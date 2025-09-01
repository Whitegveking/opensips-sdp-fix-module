/*
 * SDP Fix Module for OpenSIPS
 *
 * Copyright (C) 2024
 *
 * This file is part of opensips, a free SIP server.
 *
 * opensips is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version
 *
 * opensips is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301  USA
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <regex.h>
#include <time.h>

#include "../../sr_module.h"
#include "../../dprint.h"
#include "../../data_lump.h"
#include "../../mem/mem.h"
#include "../../mem/shm_mem.h"
#include "../../locking.h"
#include "../../parser/parse_content.h"
#include "../../parser/sdp/sdp.h"
#include "../../parser/parse_to.h"
#include "../../parser/parse_from.h"
#include "../../parser/parse_cseq.h"
#include "../../mod_fix.h"
#include "../../str.h"
#include "../../ut.h"
#include "../../trim.h"

// 模块参数
static int enable_sdp_fix = 1;
static int auto_fix_payload = 1;
static char *sdp_fix_log_prefix = "SDP_FIX";
static int session_timeout = 300;

// 编解码器信息结构
typedef struct codec_info
{
    int payload_type;
    str codec_name;
    int sample_rate;
    str fmtp_params;
    int channels;
    int is_dynamic_name; // 标记编解码器名称是否为动态分配
} codec_info_t;

// 音频媒体信息
typedef struct audio_media
{
    int port;
    str connection_ip;
    str direction;
    codec_info_t *codecs;
    int codec_count;
} audio_media_t;

// 会话上下文
typedef struct session_context
{
    str call_id;
    audio_media_t update_audio;
    audio_media_t reply_audio;
    time_t timestamp;
} session_context_t;

// 哈希表结构
struct hash_entry
{
    char *key;
    int key_len;
    void *value;
    struct hash_entry *next;
};

struct hash_table
{
    struct hash_entry **buckets;
    int size;
    gen_lock_t lock;
};

// 全局会话存储
static struct hash_table *session_table = NULL;

// 函数声明
static int mod_init(void);
static void mod_destroy(void);
static int safe_str2int(const str *s);
static int store_update_codecs(struct sip_msg *msg);
static int fix_codec_mismatch(struct sip_msg *msg);
static int check_codec_compatibility(struct sip_msg *msg);

// 内部函数声明
static int parse_audio_codecs(sdp_info_t *sdp, audio_media_t *audio);
static char *build_fixed_audio_sdp(sdp_info_t *original_sdp, session_context_t *ctx, int *new_len);
static int replace_sdp_body(struct sip_msg *msg, char *new_body, int new_len);
static struct hash_table *init_hash_table(int size);
static void *hash_get(struct hash_table *ht, const char *key, int key_len);
static int hash_set(struct hash_table *ht, const char *key, int key_len, void *value);
static void destroy_hash_table(struct hash_table *ht);
static int get_reply_code(struct sip_msg *msg);
static void cleanup_expired_sessions(void);

static cmd_export_t cmds[] = {
    {.name = "store_update_codecs",
     .function = (cmd_function)store_update_codecs,
     .params = {{0}},
     .flags = REQUEST_ROUTE},
    {.name = "fix_codec_mismatch",
     .function = (cmd_function)fix_codec_mismatch,
     .params = {{0}},
     .flags = ONREPLY_ROUTE},
    {.name = "check_codec_compatibility",
     .function = (cmd_function)check_codec_compatibility,
     .params = {{0}},
     .flags = ONREPLY_ROUTE},
    {0}};

static param_export_t params[] = {
    {"enable_sdp_fix", INT_PARAM, &enable_sdp_fix},
    {"auto_fix_payload", INT_PARAM, &auto_fix_payload},
    {"session_timeout", INT_PARAM, &session_timeout},
    {0, 0, 0}};

struct module_exports exports = {
    .name = "sdp_fix",
    .type = MOD_TYPE_DEFAULT,
    .ver_info = {.version = OPENSIPS_FULL_VERSION, .compile_flags = OPENSIPS_COMPILE_FLAGS, .scm = {VERSIONTYPE, THISREVISION}},
    .dlflags = DEFAULT_DLFLAGS,
    .load_f = 0,
    .deps = 0,
    .cmds = cmds,
    .acmds = 0,
    .params = params,
    .stats = 0,
    .mi_cmds = 0,
    .items = 0,
    .trans = 0,
    .procs = 0,
    .preinit_f = 0,
    .init_f = mod_init,
    .response_f = 0,
    .destroy_f = mod_destroy,
    .init_child_f = 0,
    .reload_ack_f = 0};

static int mod_init(void)
{
    LM_INFO("%s: Initializing SDP fix module\n", sdp_fix_log_prefix);

    session_table = init_hash_table(2048);
    if (!session_table)
    {
        LM_ERR("Failed to initialize session table\n");
        return -1;
    }

    LM_INFO("%s: SDP fix module initialized successfully with shared memory\n", sdp_fix_log_prefix);
    return 0;
}

// 安全的字符串转整数函数
static int safe_str2int(const str *s)
{
    unsigned int result;
    if (str2int(s, &result) == 0)
    {
        return (int)result;
    }
    return -1;
}
// 获取回复状态码
static int get_reply_code(struct sip_msg *msg)
{
    if (msg->first_line.type != SIP_REPLY)
    {
        return -1;
    }
    return msg->first_line.u.reply.statuscode;
}

// 存储UPDATE请求中的编解码器信息
static int store_update_codecs(struct sip_msg *msg)
{
    sdp_info_t *sdp;
    session_context_t *ctx;
    str call_id;

    if (!enable_sdp_fix)
    {
        return 1;
    }

    // 仅处理UPDATE请求
    if (msg->REQ_METHOD != METHOD_UPDATE)
    {
        return 1;
    }

    // 解析SDP
    if (parse_sdp(msg) < 0)
    {
        LM_DBG("No SDP in UPDATE request\n");
        return 1;
    }

    sdp = get_sdp(msg);
    if (!sdp)
    {
        return 1;
    }

    // 获取Call-ID
    if (msg->callid == NULL && parse_headers(msg, HDR_CALLID_F, 0) < 0)
    {
        LM_ERR("Failed to parse Call-ID header\n");
        return -1;
    }

    if (msg->callid == NULL)
    {
        LM_ERR("Call-ID header not found\n");
        return -1;
    }

    call_id = msg->callid->body;

    // 创建或获取会话上下文
    lock_get(&session_table->lock);
    ctx = hash_get(session_table, call_id.s, call_id.len);
    if (!ctx)
    {
        ctx = shm_malloc(sizeof(session_context_t));
        if (!ctx)
        {
            lock_release(&session_table->lock);
            LM_ERR("Memory allocation failed\n");
            return -1;
        }
        memset(ctx, 0, sizeof(session_context_t));

        // 复制call_id
        ctx->call_id.s = shm_malloc(call_id.len);
        if (!ctx->call_id.s)
        {
            shm_free(ctx);
            lock_release(&session_table->lock);
            return -1;
        }
        memcpy(ctx->call_id.s, call_id.s, call_id.len);
        ctx->call_id.len = call_id.len;
    }
    else
    {
        // 清理之前的UPDATE编解码器信息
        if (ctx->update_audio.codecs)
        {
            for (int i = 0; i < ctx->update_audio.codec_count; i++)
            {
                if (ctx->update_audio.codecs[i].is_dynamic_name &&
                    ctx->update_audio.codecs[i].codec_name.s)
                {
                    shm_free(ctx->update_audio.codecs[i].codec_name.s);
                }
            }
            shm_free(ctx->update_audio.codecs);
            ctx->update_audio.codecs = NULL;
            ctx->update_audio.codec_count = 0;
        }
    }

    // 解析UPDATE请求中的音频编解码器
    if (parse_audio_codecs(sdp, &ctx->update_audio) < 0)
    {
        LM_ERR("Failed to parse UPDATE audio codecs\n");
        lock_release(&session_table->lock);
        return -1;
    }

    ctx->timestamp = time(NULL);
    hash_set(session_table, call_id.s, call_id.len, ctx);

    // 清理过期会话（不要在锁内进行）
    lock_release(&session_table->lock);

    // 只在模块正常运行时清理过期会话
    if (session_table)
    {
        cleanup_expired_sessions();
    }

    LM_INFO("%s: Stored UPDATE codecs for Call-ID: %.*s, found %d codecs\n",
            sdp_fix_log_prefix, call_id.len, call_id.s,
            ctx->update_audio.codec_count);

    // 打印存储的编解码器信息
    for (int i = 0; i < ctx->update_audio.codec_count; i++)
    {
        codec_info_t *codec = &ctx->update_audio.codecs[i];
        LM_INFO("%s: UPDATE codec[%d]: PT=%d, Name=%.*s, Rate=%d, Channels=%d\n",
                sdp_fix_log_prefix, i, codec->payload_type,
                codec->codec_name.len, codec->codec_name.s,
                codec->sample_rate, codec->channels);

        if (codec->fmtp_params.s && codec->fmtp_params.len > 0)
        {
            LM_INFO("%s: UPDATE codec[%d] fmtp: %.*s\n",
                    sdp_fix_log_prefix, i, codec->fmtp_params.len, codec->fmtp_params.s);
        }
    }

    return 1;
}

// 解析音频编解码器信息 - 修复API调用
static int parse_audio_codecs(sdp_info_t *sdp, audio_media_t *audio)
{
    sdp_stream_cell_t *stream;
    sdp_payload_attr_t *payload;
    int codec_idx = 0;
    int max_codecs = 32; // 限制最大编解码器数量

    memset(audio, 0, sizeof(audio_media_t));

    // 使用正确的API获取流
    if (!sdp || sdp->streams_num == 0)
    {
        return 0;
    }

    // 遍历所有流
    stream = sdp->sessions ? sdp->sessions->streams : NULL;

    while (stream)
    {
        if (strncmp(stream->media.s, "audio", 5) != 0)
        {
            stream = stream->next;
            continue;
        }

        // 解析端口
        int port_val = safe_str2int(&stream->port);
        if (port_val > 0)
        {
            audio->port = port_val;
        }

        // 获取连接地址
        if (stream->ip_addr.s && stream->ip_addr.len > 0)
        {
            audio->connection_ip = stream->ip_addr;
        }

        // 获取媒体方向
        if (stream->sendrecv_mode.s && stream->sendrecv_mode.len > 0)
        {
            audio->direction = stream->sendrecv_mode;
        }
        else
        {
            audio->direction.s = "sendrecv";
            audio->direction.len = 8;
        }

        // 计算编解码器数量，但限制最大值
        for (payload = stream->payload_attr; payload && audio->codec_count < max_codecs; payload = payload->next)
        {
            if (payload->rtp_payload.s && payload->rtp_payload.len > 0)
            {
                audio->codec_count++;
            }
        }

        if (audio->codec_count == 0)
        {
            stream = stream->next;
            continue;
        }

        // 分配编解码器数组
        audio->codecs = shm_malloc(sizeof(codec_info_t) * audio->codec_count);
        if (!audio->codecs)
        {
            LM_ERR("Failed to allocate codec array\n");
            return -1;
        }
        memset(audio->codecs, 0, sizeof(codec_info_t) * audio->codec_count);

        // 解析每个编解码器
        codec_idx = 0; // 重置索引
        for (payload = stream->payload_attr; payload && codec_idx < audio->codec_count;
             payload = payload->next)
        {
            if (!payload->rtp_payload.s || payload->rtp_payload.len == 0)
            {
                continue;
            }

            codec_info_t *codec = &audio->codecs[codec_idx];

            // 解析负载类型
            codec->payload_type = safe_str2int(&payload->rtp_payload);

            // 设置默认值
            codec->sample_rate = 8000;
            codec->channels = 1;
            codec->codec_name.s = "unknown";
            codec->codec_name.len = 7;
            codec->is_dynamic_name = 0; // 静态字符串

            // 解析编解码器名称和采样率
            if (payload->rtp_enc.s && payload->rtp_enc.len > 0)
            {
                char *slash = memchr(payload->rtp_enc.s, '/', payload->rtp_enc.len);
                if (slash)
                {
                    // rtp_enc包含完整的格式信息 (如 "AMR-WB/16000/1")
                    int name_len = slash - payload->rtp_enc.s;

                    // 确保名称长度合理（防止异常长度）
                    if (name_len > 0 && name_len <= 64)
                    {
                        char *name_copy = shm_malloc(name_len + 1);
                        if (name_copy)
                        {
                            memcpy(name_copy, payload->rtp_enc.s, name_len);
                            name_copy[name_len] = '\0';

                            codec->codec_name.s = name_copy;
                            codec->codec_name.len = name_len;
                            codec->is_dynamic_name = 1; // 动态分配

                            str rate_str;
                            rate_str.s = slash + 1;
                            rate_str.len = payload->rtp_enc.len - name_len - 1;

                            // 查找下一个斜杠（声道数）
                            char *next_slash = memchr(rate_str.s, '/', rate_str.len);
                            if (next_slash)
                            {
                                rate_str.len = next_slash - rate_str.s;
                                // 解析声道数
                                str channels_str;
                                channels_str.s = next_slash + 1;
                                channels_str.len = payload->rtp_enc.len - name_len - rate_str.len - 2;
                                codec->channels = safe_str2int(&channels_str);
                                if (codec->channels <= 0)
                                    codec->channels = 1;
                            }

                            codec->sample_rate = safe_str2int(&rate_str);
                            if (codec->sample_rate <= 0)
                                codec->sample_rate = 8000;
                        }
                    }
                }
                else
                {
                    // rtp_enc只包含编解码器名称，需要从rtp_clock获取采样率
                    int name_len = payload->rtp_enc.len;

                    // 确保名称长度合理（防止异常长度）
                    if (name_len > 0 && name_len <= 64)
                    {
                        char *name_copy = shm_malloc(name_len + 1);
                        if (name_copy)
                        {
                            memcpy(name_copy, payload->rtp_enc.s, name_len);
                            name_copy[name_len] = '\0';

                            codec->codec_name.s = name_copy;
                            codec->codec_name.len = name_len;
                            codec->is_dynamic_name = 1; // 动态分配

                            // 尝试从rtp_clock获取采样率
                            if (payload->rtp_clock.s && payload->rtp_clock.len > 0)
                            {
                                codec->sample_rate = safe_str2int(&payload->rtp_clock);
                                if (codec->sample_rate <= 0)
                                    codec->sample_rate = 8000;
                            }
                        }
                    }
                }
            }
            else
            {
                // 为标准编解码器设置默认值
                switch (codec->payload_type)
                {
                case 0:
                {
                    char *name_copy = shm_malloc(5);
                    if (name_copy)
                    {
                        strcpy(name_copy, "PCMU");
                        codec->codec_name.s = name_copy;
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 1; // 动态分配
                    }
                    else
                    {
                        codec->codec_name.s = "PCMU";
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 0; // 静态字符串（回退）
                    }
                    codec->sample_rate = 8000;
                    codec->channels = 1;
                    break;
                }
                case 8:
                {
                    char *name_copy = shm_malloc(5);
                    if (name_copy)
                    {
                        strcpy(name_copy, "PCMA");
                        codec->codec_name.s = name_copy;
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 1; // 动态分配
                    }
                    else
                    {
                        codec->codec_name.s = "PCMA";
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 0; // 静态字符串（回退）
                    }
                    codec->sample_rate = 8000;
                    codec->channels = 1;
                    break;
                }
                case 18:
                {
                    char *name_copy = shm_malloc(5);
                    if (name_copy)
                    {
                        strcpy(name_copy, "G729");
                        codec->codec_name.s = name_copy;
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 1; // 动态分配
                    }
                    else
                    {
                        codec->codec_name.s = "G729";
                        codec->codec_name.len = 4;
                        codec->is_dynamic_name = 0; // 静态字符串（回退）
                    }
                    codec->sample_rate = 8000;
                    codec->channels = 1;
                    break;
                }
                }
            }

            // 存储fmtp参数
            if (payload->fmtp_string.s && payload->fmtp_string.len > 0)
            {
                codec->fmtp_params = payload->fmtp_string;
            }

            // 总是递增索引，确保不会无限循环
            codec_idx++;
        }

        audio->codec_count = codec_idx;
        break; // 只处理第一个音频流
    }
    return 0;
}

// 检查编解码器兼容性
static int check_codec_compatibility(struct sip_msg *msg)
{
    sdp_info_t *sdp;
    session_context_t *ctx;
    str call_id;
    audio_media_t reply_audio;

    if (!enable_sdp_fix)
    {
        return 1;
    }

    // 仅处理200 OK响应
    if (msg->first_line.type != SIP_REPLY || get_reply_code(msg) != 200)
    {
        return 1;
    }

    // 获取Call-ID
    if (msg->callid == NULL && parse_headers(msg, HDR_CALLID_F, 0) < 0)
    {
        return -1;
    }

    if (msg->callid == NULL)
    {
        return -1;
    }

    call_id = msg->callid->body;

    lock_get(&session_table->lock);
    ctx = hash_get(session_table, call_id.s, call_id.len);
    if (!ctx)
    {
        lock_release(&session_table->lock);
        LM_DBG("No stored UPDATE context for Call-ID: %.*s\n",
               call_id.len, call_id.s);
        return 1;
    }

    // 解析SDP
    if (parse_sdp(msg) < 0)
    {
        lock_release(&session_table->lock);
        return 1;
    }

    sdp = get_sdp(msg);
    if (!sdp)
    {
        lock_release(&session_table->lock);
        return 1;
    }

    // 解析200 OK中的音频编解码器
    if (parse_audio_codecs(sdp, &reply_audio) < 0)
    {
        lock_release(&session_table->lock);
        LM_ERR("Failed to parse reply audio codecs\n");
        return -1;
    }

    // 清理之前的Reply编解码器信息
    if (ctx->reply_audio.codecs)
    {
        for (int i = 0; i < ctx->reply_audio.codec_count; i++)
        {
            if (ctx->reply_audio.codecs[i].is_dynamic_name &&
                ctx->reply_audio.codecs[i].codec_name.s)
            {
                shm_free(ctx->reply_audio.codecs[i].codec_name.s);
            }
        }
        shm_free(ctx->reply_audio.codecs);
    }

    ctx->reply_audio = reply_audio;
    lock_release(&session_table->lock);

    LM_INFO("%s: Reply codecs for Call-ID: %.*s, found %d codecs\n",
            sdp_fix_log_prefix, call_id.len, call_id.s,
            reply_audio.codec_count);

    // 打印200 OK中的编解码器
    for (int i = 0; i < reply_audio.codec_count; i++)
    {
        codec_info_t *codec = &reply_audio.codecs[i];
        LM_INFO("%s: Reply codec[%d]: PT=%d, Name=%.*s, Rate=%d, Channels=%d\n",
                sdp_fix_log_prefix, i, codec->payload_type,
                codec->codec_name.len, codec->codec_name.s,
                codec->sample_rate, codec->channels);

        if (codec->fmtp_params.s && codec->fmtp_params.len > 0)
        {
            LM_INFO("%s: Reply codec[%d] fmtp: %.*s\n",
                    sdp_fix_log_prefix, i, codec->fmtp_params.len, codec->fmtp_params.s);
        }
    }

    // 检查负载类型匹配
    int mismatch_found = 0;
    for (int i = 0; i < ctx->update_audio.codec_count; i++)
    {
        codec_info_t *update_codec = &ctx->update_audio.codecs[i];

        LM_INFO("%s: Checking UPDATE codec[%d]: PT=%d, Name='%.*s', Rate=%d\n",
                sdp_fix_log_prefix, i, update_codec->payload_type,
                update_codec->codec_name.len, update_codec->codec_name.s,
                update_codec->sample_rate);

        // 在200 OK响应中查找相同的编解码器
        int found_match = 0;
        for (int j = 0; j < reply_audio.codec_count; j++)
        {
            codec_info_t *reply_codec = &reply_audio.codecs[j];

            LM_INFO("%s: Comparing with Reply codec[%d]: PT=%d, Name='%.*s', Rate=%d\n",
                    sdp_fix_log_prefix, j, reply_codec->payload_type,
                    reply_codec->codec_name.len, reply_codec->codec_name.s,
                    reply_codec->sample_rate);

            // 检查编解码器名称和采样率是否匹配
            if (update_codec->codec_name.len == reply_codec->codec_name.len &&
                strncasecmp(update_codec->codec_name.s, reply_codec->codec_name.s,
                            update_codec->codec_name.len) == 0 &&
                update_codec->sample_rate == reply_codec->sample_rate)
            {
                LM_INFO("%s: Found matching codec: %.*s/%d\n",
                        sdp_fix_log_prefix,
                        update_codec->codec_name.len, update_codec->codec_name.s,
                        update_codec->sample_rate);

                if (update_codec->payload_type != reply_codec->payload_type)
                {
                    LM_WARN("%s: Payload type mismatch for %.*s/%d: UPDATE=%d, Reply=%d\n",
                            sdp_fix_log_prefix,
                            update_codec->codec_name.len, update_codec->codec_name.s,
                            update_codec->sample_rate,
                            update_codec->payload_type, reply_codec->payload_type);
                    mismatch_found = 1;
                }
                else
                {
                    LM_INFO("%s: Payload types match for %.*s/%d: %d\n",
                            sdp_fix_log_prefix,
                            update_codec->codec_name.len, update_codec->codec_name.s,
                            update_codec->sample_rate,
                            update_codec->payload_type);
                }
                found_match = 1;
                break;
            }
        }

        if (!found_match)
        {
            LM_WARN("%s: Codec %.*s/%d from UPDATE not found in reply\n",
                    sdp_fix_log_prefix,
                    update_codec->codec_name.len, update_codec->codec_name.s,
                    update_codec->sample_rate);
        }
    }

    if (mismatch_found)
    {
        LM_INFO("%s: Codec payload type mismatch detected, auto-fix %s\n",
                sdp_fix_log_prefix,
                auto_fix_payload ? "enabled" : "disabled");
        return auto_fix_payload ? -1 : -2; // -1表示需要修复，-2表示不兼容但不修复
    }

    return 1; // 兼容
}

// 修复编解码器负载类型不匹配
static int fix_codec_mismatch(struct sip_msg *msg)
{
    session_context_t *ctx;
    str call_id;
    char *new_sdp_body;
    int new_len;

    if (!enable_sdp_fix || !auto_fix_payload)
    {
        return 1;
    }

    // 仅处理200 OK响应
    if (msg->first_line.type != SIP_REPLY || get_reply_code(msg) != 200)
    {
        return 1;
    }

    // 获取Call-ID
    if (msg->callid == NULL && parse_headers(msg, HDR_CALLID_F, 0) < 0)
    {
        return -1;
    }

    if (msg->callid == NULL)
    {
        return -1;
    }

    call_id = msg->callid->body;

    lock_get(&session_table->lock);
    ctx = hash_get(session_table, call_id.s, call_id.len);
    if (!ctx || ctx->update_audio.codec_count == 0)
    {
        lock_release(&session_table->lock);
        return 1;
    }
    lock_release(&session_table->lock);

    // 解析当前SDP
    if (parse_sdp(msg) < 0)
    {
        return 1;
    }

    sdp_info_t *sdp = get_sdp(msg);
    if (!sdp)
    {
        return 1;
    }

    // 构建修复后的SDP
    new_sdp_body = build_fixed_audio_sdp(sdp, ctx, &new_len);
    if (!new_sdp_body)
    {
        LM_ERR("Failed to build fixed SDP\n");
        return -1;
    }

    // 替换SDP内容
    if (replace_sdp_body(msg, new_sdp_body, new_len) < 0)
    {
        LM_ERR("Failed to replace SDP body\n");
        pkg_free(new_sdp_body);
        return -1;
    }

    pkg_free(new_sdp_body);

    LM_INFO("%s: Fixed codec payload types for Call-ID: %.*s\n",
            sdp_fix_log_prefix, call_id.len, call_id.s);

    return 1;
}

// 构建修复后的音频SDP - 保持原始结构
static char *build_fixed_audio_sdp(sdp_info_t *original_sdp, session_context_t *ctx, int *new_len)
{
    char *buffer;
    int buf_size = 8192;
    int pos = 0;
    sdp_stream_cell_t *stream;

    buffer = pkg_malloc(buf_size);
    if (!buffer)
    {
        LM_ERR("Memory allocation failed\n");
        return NULL;
    }

    // 复制原始SDP会话级别的信息（只到第一个m=行）
    if (original_sdp->sessions && original_sdp->sessions->body.s)
    {
        char *session_start = original_sdp->sessions->body.s;
        char *session_end = strstr(session_start, "m=");

        if (session_end)
        {
            int session_len = session_end - session_start;

            LM_INFO("SDP_FIX: Original session info (first 20 chars): '%.20s'\n", session_start);

            // 检查并修复重复的v=行
            if (session_len >= 2 && strncmp(session_start, "v=", 2) == 0)
            {
                // 跳过重复的"v="，保留"v=0"
                session_start += 2;
                session_len -= 2;
                LM_INFO("SDP_FIX: Fixed duplicate v= line in session header\n");
            }

            // 确保会话信息正确复制
            pos += snprintf(buffer + pos, buf_size - pos, "%.*s",
                            session_len, session_start);

            LM_INFO("SDP_FIX: Copied session info, buffer now (first 30 chars): '%.30s'\n", buffer);
        }
        else
        {
            // 如果没有媒体流，复制整个会话
            int total_len = strlen(session_start);
            LM_INFO("SDP_FIX: No media streams, session info (first 20 chars): '%.20s'\n", session_start);

            if (total_len >= 4 && strncmp(session_start, "v=v=", 4) == 0)
            {
                session_start += 2;
                total_len -= 2;
                LM_INFO("SDP_FIX: Fixed duplicate v= line in session-only SDP\n");
            }
            pos += snprintf(buffer + pos, buf_size - pos, "%s", session_start);
        }
    }

    // 处理每个媒体流
    stream = original_sdp->sessions ? original_sdp->sessions->streams : NULL;

    while (stream)
    {
        if (strncmp(stream->media.s, "audio", 5) == 0)
        {
            LM_INFO("SDP_FIX: Processing audio stream, UPDATE has %d codecs, Reply has %d codecs\n",
                    ctx->update_audio.codec_count, ctx->reply_audio.codec_count);

            // 构建修复后的音频流：保持200 OK的编解码器顺序，但使用UPDATE的PT
            pos += snprintf(buffer + pos, buf_size - pos,
                            "m=audio %.*s RTP/AVP",
                            stream->port.len, stream->port.s);

            // 为200 OK中的每个编解码器，找到UPDATE中对应的payload type
            for (int j = 0; j < ctx->reply_audio.codec_count; j++)
            {
                codec_info_t *reply_codec = &ctx->reply_audio.codecs[j];
                int update_pt = -1;

                LM_INFO("SDP_FIX: Processing Reply codec[%d]: PT=%d, Name='%.*s', Rate=%d\n",
                        j, reply_codec->payload_type,
                        reply_codec->codec_name.len, reply_codec->codec_name.s,
                        reply_codec->sample_rate);

                // 在UPDATE中查找匹配的编解码器
                for (int i = 0; i < ctx->update_audio.codec_count; i++)
                {
                    codec_info_t *update_codec = &ctx->update_audio.codecs[i];

                    if (update_codec->codec_name.len == reply_codec->codec_name.len &&
                        strncasecmp(update_codec->codec_name.s, reply_codec->codec_name.s,
                                    update_codec->codec_name.len) == 0 &&
                        update_codec->sample_rate == reply_codec->sample_rate)
                    {
                        update_pt = update_codec->payload_type;
                        LM_INFO("SDP_FIX: Match found! Using UPDATE PT=%d for Reply codec %.*s/%d (was PT=%d)\n",
                                update_pt,
                                reply_codec->codec_name.len, reply_codec->codec_name.s,
                                reply_codec->sample_rate, reply_codec->payload_type);
                        break;
                    }
                }

                // 添加payload type（使用UPDATE中的，如果没找到就使用原来的）
                if (update_pt != -1)
                {
                    pos += snprintf(buffer + pos, buf_size - pos, " %d", update_pt);
                }
                else
                {
                    pos += snprintf(buffer + pos, buf_size - pos, " %d", reply_codec->payload_type);
                    LM_INFO("SDP_FIX: No UPDATE match found, keeping original PT=%d for %.*s/%d\n",
                            reply_codec->payload_type,
                            reply_codec->codec_name.len, reply_codec->codec_name.s,
                            reply_codec->sample_rate);
                }
            }
            pos += snprintf(buffer + pos, buf_size - pos, "\r\n");

            // 复制连接信息
            if (stream->ip_addr.s && stream->ip_addr.len > 0)
            {
                pos += snprintf(buffer + pos, buf_size - pos,
                                "c=IN IP4 %.*s\r\n",
                                stream->ip_addr.len, stream->ip_addr.s);
            }

            // 添加rtpmap和fmtp属性（保持200 OK的顺序，但跳过telephone-event）
            for (int j = 0; j < ctx->reply_audio.codec_count; j++)
            {
                codec_info_t *reply_codec = &ctx->reply_audio.codecs[j];

                // 跳过telephone-event，会在后面单独处理
                if (strncasecmp(reply_codec->codec_name.s, "telephone-event", 15) == 0)
                {
                    continue;
                }

                int final_pt = reply_codec->payload_type;

                // 查找UPDATE中匹配的编解码器以获取正确的payload type
                for (int i = 0; i < ctx->update_audio.codec_count; i++)
                {
                    codec_info_t *update_codec = &ctx->update_audio.codecs[i];

                    if (update_codec->codec_name.len == reply_codec->codec_name.len &&
                        strncasecmp(update_codec->codec_name.s, reply_codec->codec_name.s,
                                    update_codec->codec_name.len) == 0 &&
                        update_codec->sample_rate == reply_codec->sample_rate)
                    {
                        final_pt = update_codec->payload_type;
                        break;
                    }
                }

                // 添加rtpmap - 对于AMR和AMR-WB总是包含声道数
                if (reply_codec->channels > 1 ||
                    strncasecmp(reply_codec->codec_name.s, "AMR", 3) == 0)
                {
                    pos += snprintf(buffer + pos, buf_size - pos,
                                    "a=rtpmap:%d %.*s/%d/%d\r\n",
                                    final_pt,
                                    reply_codec->codec_name.len, reply_codec->codec_name.s,
                                    reply_codec->sample_rate,
                                    reply_codec->channels);
                }
                else
                {
                    pos += snprintf(buffer + pos, buf_size - pos,
                                    "a=rtpmap:%d %.*s/%d\r\n",
                                    final_pt,
                                    reply_codec->codec_name.len, reply_codec->codec_name.s,
                                    reply_codec->sample_rate);
                }

                // 添加fmtp（如果存在）
                if (reply_codec->fmtp_params.s && reply_codec->fmtp_params.len > 0)
                {
                    pos += snprintf(buffer + pos, buf_size - pos,
                                    "a=fmtp:%d %.*s\r\n",
                                    final_pt,
                                    reply_codec->fmtp_params.len,
                                    reply_codec->fmtp_params.s);
                }
            }

            // 2. 处理telephone-event（只保留一个，优先8000Hz）
            codec_info_t *selected_event_codec = NULL;
            int selected_event_pt = -1;

            for (int j = 0; j < ctx->reply_audio.codec_count; j++)
            {
                codec_info_t *reply_codec = &ctx->reply_audio.codecs[j];

                if (strncasecmp(reply_codec->codec_name.s, "telephone-event", 15) != 0)
                {
                    continue;
                }

                // 如果还没选择或当前是8000Hz，则选择这个
                if (selected_event_codec == NULL || reply_codec->sample_rate == 8000)
                {
                    selected_event_codec = reply_codec;
                    selected_event_pt = reply_codec->payload_type;

                    // 查找UPDATE中匹配的telephone-event
                    for (int i = 0; i < ctx->update_audio.codec_count; i++)
                    {
                        codec_info_t *update_codec = &ctx->update_audio.codecs[i];

                        if (strncasecmp(update_codec->codec_name.s, "telephone-event", 15) == 0 &&
                            update_codec->sample_rate == reply_codec->sample_rate)
                        {
                            selected_event_pt = update_codec->payload_type;
                            break;
                        }
                    }
                }
            }

            // 添加选择的telephone-event
            if (selected_event_codec != NULL)
            {
                pos += snprintf(buffer + pos, buf_size - pos,
                                "a=rtpmap:%d %.*s/%d\r\n",
                                selected_event_pt,
                                selected_event_codec->codec_name.len, selected_event_codec->codec_name.s,
                                selected_event_codec->sample_rate);

                if (selected_event_codec->fmtp_params.s && selected_event_codec->fmtp_params.len > 0)
                {
                    pos += snprintf(buffer + pos, buf_size - pos,
                                    "a=fmtp:%d %.*s\r\n",
                                    selected_event_pt,
                                    selected_event_codec->fmtp_params.len,
                                    selected_event_codec->fmtp_params.s);
                }
            }

            // 添加媒体方向属性
            if (stream->sendrecv_mode.s && stream->sendrecv_mode.len > 0)
            {
                pos += snprintf(buffer + pos, buf_size - pos,
                                "a=%.*s\r\n",
                                stream->sendrecv_mode.len, stream->sendrecv_mode.s);
            }
        }
        else
        {
            // 非音频流：保持原样
            if (stream->body.s && stream->body.len > 0)
            {
                pos += snprintf(buffer + pos, buf_size - pos,
                                "%.*s", stream->body.len, stream->body.s);
                if (stream->body.s[stream->body.len - 1] != '\n')
                {
                    pos += snprintf(buffer + pos, buf_size - pos, "\r\n");
                }
            }
        }

        stream = stream->next;
    }

    *new_len = pos;
    LM_INFO("%s: Built fixed SDP with length %d\n", sdp_fix_log_prefix, pos);
    return buffer;
}

// 替换SDP消息体
static int replace_sdp_body(struct sip_msg *msg, char *new_body, int new_len)
{
    struct lump *lump;
    char *new_buf;

    // 分配新的缓冲区
    new_buf = pkg_malloc(new_len);
    if (!new_buf)
    {
        LM_ERR("Memory allocation failed\n");
        return -1;
    }

    memcpy(new_buf, new_body, new_len);

    // 删除原有的消息体
    lump = del_lump(msg, msg->eoh - msg->buf + 4,
                    msg->len - (msg->eoh - msg->buf + 4), HDR_OTHER_T);
    if (!lump)
    {
        LM_ERR("Failed to delete old body\n");
        pkg_free(new_buf);
        return -1;
    }

    // 插入新的消息体
    if (!insert_new_lump_after(lump, new_buf, new_len, HDR_OTHER_T))
    {
        LM_ERR("Failed to insert new body\n");
        pkg_free(new_buf);
        return -1;
    }

    // 更新Content-Length头
    if (msg->content_length)
    {
        char len_str[20];
        int len_str_len = snprintf(len_str, sizeof(len_str), "%d", new_len);

        struct lump *cl_lump = del_lump(msg,
                                        msg->content_length->body.s - msg->buf,
                                        msg->content_length->body.len,
                                        HDR_CONTENTLENGTH_T);
        if (cl_lump)
        {
            char *cl_buf = pkg_malloc(len_str_len);
            if (cl_buf)
            {
                memcpy(cl_buf, len_str, len_str_len);
                insert_new_lump_after(cl_lump, cl_buf, len_str_len, HDR_CONTENTLENGTH_T);
            }
        }
    }

    return 0;
}

static void mod_destroy(void)
{
    if (session_table)
    {
        destroy_hash_table(session_table);
        session_table = NULL; // 防止重复释放
    }
    LM_INFO("%s: Module destroyed\n", sdp_fix_log_prefix);
}

// 哈希表实现
static unsigned int hash_function(const char *key, int len)
{
    unsigned int hash = 5381;
    int i;
    for (i = 0; i < len; i++)
    {
        hash = ((hash << 5) + hash) + key[i];
    }

    return hash;
}

static struct hash_table *init_hash_table(int size)
{
    struct hash_table *ht;

    ht = shm_malloc(sizeof(struct hash_table));
    if (!ht)
    {
        LM_ERR("Failed to allocate hash table\n");
        return NULL;
    }

    ht->buckets = shm_malloc(sizeof(struct hash_entry *) * size);
    if (!ht->buckets)
    {
        LM_ERR("Failed to allocate hash table buckets\n");
        shm_free(ht);
        return NULL;
    }

    memset(ht->buckets, 0, sizeof(struct hash_entry *) * size);
    ht->size = size;

    // 初始化锁
    if (lock_init(&ht->lock) == 0)
    {
        LM_ERR("Failed to initialize hash table lock\n");
        shm_free(ht->buckets);
        shm_free(ht);
        return NULL;
    }

    LM_DBG("Initialized hash table with %d buckets and shared memory\n", size);
    return ht;
}

static void *hash_get(struct hash_table *ht, const char *key, int key_len)
{
    unsigned int hash_val;
    struct hash_entry *entry;

    if (!ht || !key || key_len <= 0)
    {
        return NULL;
    }

    hash_val = hash_function(key, key_len) % ht->size;
    entry = ht->buckets[hash_val];

    while (entry)
    {
        if (entry->key_len == key_len &&
            memcmp(entry->key, key, key_len) == 0)
        {
            LM_DBG("hash_get: Found entry for key (len=%d) in bucket %u\n", key_len, hash_val);
            return entry->value;
        }
        entry = entry->next;
    }

    LM_DBG("hash_get: Entry not found for key (len=%d) in bucket %u\n", key_len, hash_val);
    return NULL;
}

static int hash_set(struct hash_table *ht, const char *key, int key_len, void *value)
{
    unsigned int hash_val;
    struct hash_entry *entry;

    if (!ht || !key || key_len <= 0)
    {
        LM_ERR("Invalid parameters for hash_set\n");
        return -1;
    }

    hash_val = hash_function(key, key_len) % ht->size;
    entry = ht->buckets[hash_val];

    // 检查是否已存在，如果存在则更新值
    while (entry)
    {
        if (entry->key_len == key_len &&
            memcmp(entry->key, key, key_len) == 0)
        {
            LM_DBG("hash_set: Updating existing entry for key (len=%d) in bucket %u\n", key_len, hash_val);

            // 直接更新为新值，不释放旧值（调用者负责内存管理）
            entry->value = value;
            return 0;
        }
        entry = entry->next;
    } // 创建新条目
    entry = shm_malloc(sizeof(struct hash_entry));
    if (!entry)
    {
        LM_ERR("Failed to allocate hash entry\n");
        return -1;
    }

    entry->key = shm_malloc(key_len);
    if (!entry->key)
    {
        LM_ERR("Failed to allocate key memory\n");
        shm_free(entry);
        return -1;
    }

    memcpy(entry->key, key, key_len);
    entry->key_len = key_len;
    entry->value = value;
    entry->next = ht->buckets[hash_val];
    ht->buckets[hash_val] = entry;

    LM_DBG("hash_set: Added new entry for key (len=%d) in bucket %u\n", key_len, hash_val);
    return 0;
}

static void destroy_hash_table(struct hash_table *ht)
{
    int i;
    struct hash_entry *entry, *next;
    int total_entries = 0;

    if (!ht)
    {
        return;
    }

    LM_DBG("Destroying hash table with %d buckets\n", ht->size);

    lock_get(&ht->lock);
    for (i = 0; i < ht->size; i++)
    {
        entry = ht->buckets[i];
        while (entry)
        {
            next = entry->next;
            total_entries++;

            // 释放会话上下文中的编解码器数组
            if (entry->value)
            {
                session_context_t *ctx = (session_context_t *)entry->value;

                // 释放UPDATE音频编解码器数组
                if (ctx->update_audio.codecs)
                {
                    // 释放每个编解码器名称的内存
                    for (int j = 0; j < ctx->update_audio.codec_count; j++)
                    {
                        // 只释放动态分配的内存
                        if (ctx->update_audio.codecs[j].is_dynamic_name &&
                            ctx->update_audio.codecs[j].codec_name.s)
                        {
                            shm_free(ctx->update_audio.codecs[j].codec_name.s);
                        }
                    }
                    shm_free(ctx->update_audio.codecs);
                }

                // 释放Reply音频编解码器数组
                if (ctx->reply_audio.codecs)
                {
                    // 释放每个编解码器名称的内存
                    for (int j = 0; j < ctx->reply_audio.codec_count; j++)
                    {
                        // 只释放动态分配的内存
                        if (ctx->reply_audio.codecs[j].is_dynamic_name &&
                            ctx->reply_audio.codecs[j].codec_name.s)
                        {
                            shm_free(ctx->reply_audio.codecs[j].codec_name.s);
                        }
                    }
                    shm_free(ctx->reply_audio.codecs);
                }

                // 释放Call-ID字符串
                if (ctx->call_id.s)
                {
                    shm_free(ctx->call_id.s);
                }

                shm_free(entry->value);
            }

            if (entry->key)
            {
                shm_free(entry->key);
            }
            shm_free(entry);
            entry = next;
        }
    }
    lock_release(&ht->lock);

    lock_destroy(&ht->lock);
    shm_free(ht->buckets);
    shm_free(ht);

    LM_DBG("Destroyed hash table, freed %d entries\n", total_entries);
}

// 清理过期会话
static void cleanup_expired_sessions(void)
{
    static time_t last_cleanup = 0;
    time_t now = time(NULL);

    // 每60秒清理一次
    if (now - last_cleanup < 60)
    {
        return;
    }

    last_cleanup = now;

    if (!session_table || !session_table->buckets)
    {
        return;
    }

    int i;
    struct hash_entry *entry, *next, *prev;
    int cleaned = 0;

    lock_get(&session_table->lock);

    for (i = 0; i < session_table->size; i++)
    {
        prev = NULL;
        entry = session_table->buckets[i];

        while (entry)
        {
            next = entry->next;

            if (entry->value)
            {
                session_context_t *ctx = (session_context_t *)entry->value;

                // 清理超过session_timeout秒的会话
                if (now - ctx->timestamp > session_timeout)
                {
                    // 从链表中移除
                    if (prev)
                    {
                        prev->next = next;
                    }
                    else
                    {
                        session_table->buckets[i] = next;
                    }

                    // 释放UPDATE音频编解码器数组
                    if (ctx->update_audio.codecs)
                    {
                        for (int j = 0; j < ctx->update_audio.codec_count; j++)
                        {
                            // 只释放动态分配的内存
                            if (ctx->update_audio.codecs[j].is_dynamic_name &&
                                ctx->update_audio.codecs[j].codec_name.s)
                            {
                                shm_free(ctx->update_audio.codecs[j].codec_name.s);
                            }
                        }
                        shm_free(ctx->update_audio.codecs);
                    }

                    if (ctx->reply_audio.codecs)
                    {
                        for (int j = 0; j < ctx->reply_audio.codec_count; j++)
                        {
                            // 只释放动态分配的内存
                            if (ctx->reply_audio.codecs[j].is_dynamic_name &&
                                ctx->reply_audio.codecs[j].codec_name.s)
                            {
                                shm_free(ctx->reply_audio.codecs[j].codec_name.s);
                            }
                        }
                        shm_free(ctx->reply_audio.codecs);
                    }

                    if (ctx->call_id.s)
                    {
                        shm_free(ctx->call_id.s);
                    }

                    shm_free(ctx);
                    shm_free(entry->key);
                    shm_free(entry);

                    cleaned++;
                    entry = next;
                    continue;
                }
            }

            prev = entry;
            entry = next;
        }
    }

    lock_release(&session_table->lock);

    if (cleaned > 0)
    {
        LM_DBG("Cleaned up %d expired sessions\n", cleaned);
    }
}
