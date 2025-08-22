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

#include "../../sr_module.h"
#include "../../dprint.h"
#include "../../data_lump.h"
#include "../../mem/mem.h"
#include "../../parser/parse_content.h"
#include "../../parser/sdp/sdp.h"
#include "../../mod_fix.h"
#include "../../str.h"

static int mod_init(void);
static void mod_destroy(void);
static int fix_sdp_rtpmap(struct sip_msg *msg, char *p1, char *p2);
static int validate_and_fix_sdp(struct sip_msg *msg);

static cmd_export_t cmds[] = {
    {.name = "fix_sdp_rtpmap",
     .function = (cmd_function)fix_sdp_rtpmap,
     .params = {{0}},
     .flags = REQUEST_ROUTE | ONREPLY_ROUTE},
    {0}};

static param_export_t params[] = {
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
    LM_INFO("SDP Fix module initialized\n");
    return 0;
}

static void mod_destroy(void)
{
    LM_INFO("SDP Fix module destroyed\n");
}

/* Generic helper: extract payload number from a line like "a=rtpmap:NNN ..." or "a=fmtp:NNN ..." */
static char *extract_payload(const char *line)
{
    static char payload[10];
    const char *start = NULL;
    const char *colon;
    int i = 0;

    if (!line)
    {
        payload[0] = '\0';
        return payload;
    }

    /* find ':' and start after it */
    colon = strchr(line, ':');
    if (!colon)
    {
        payload[0] = '\0';
        return payload;
    }
    start = colon + 1;

    /* skip any spaces */
    while (*start == ' ')
        start++;

    /* Extract payload number (stop at space or non-digit) */
    while (*start && *start >= '0' && *start <= '9' && i < (int)sizeof(payload) - 1)
    {
        payload[i++] = *start++;
    }
    payload[i] = '\0';

    return payload;
}

/* Check if string starts with specific prefix */
static int starts_with(const char *str, const char *prefix)
{
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

/* Find the position of newline character */
static char *find_newline(char *str)
{
    while (*str && *str != '\n' && *str != '\r')
    {
        str++;
    }
    return str;
}

/* Fix SDP content by ensuring rtpmap and fmtp lines have matching payload numbers */
static int fix_sdp_content(struct sip_msg *msg, char *sdp_body, int sdp_len)
{
    char *line_start = sdp_body;
    char *line_end;
    char *rtpmap_lines[50];       /* Store rtpmap lines */
    char *fmtp_lines[50];         /* Store fmtp lines */
    char rtpmap_payloads[50][10]; /* Store payload numbers from rtpmap */
    char fmtp_payloads[50][10];   /* Store payload numbers from fmtp */
    int rtpmap_count = 0;
    int fmtp_count = 0;
    char rtpmap_codecs[50][32]; /* codec names from rtpmap, e.g. AMR-WB */
    char fmtp_params[50][128];  /* tail of fmtp line after payload */
    int i, j;
    int modifications_made = 0;

    LM_DBG("Starting SDP fix process\n");

    /* Parse all rtpmap and fmtp lines */
    while (line_start < sdp_body + sdp_len)
    {
        line_end = find_newline(line_start);

        if (starts_with(line_start, "a=rtpmap:") && rtpmap_count < 50)
        {
            rtpmap_lines[rtpmap_count] = line_start;
            strcpy(rtpmap_payloads[rtpmap_count], extract_payload(line_start));
            /* extract codec name (text after payload number up to '/') */
            {
                char *p = line_start;
                /* move to ':' */
                while (*p && *p != ':')
                    p++;
                if (*p)
                    p++; /* skip ':' */
                /* skip payload digits */
                while (*p && (*p >= '0' && *p <= '9'))
                    p++;
                /* skip spaces */
                while (*p == ' ')
                    p++;
                /* copy codec token until '/' or space */
                int k = 0;
                while (*p && *p != '/' && *p != ' ' && k < (int)sizeof(rtpmap_codecs[0]) - 1)
                {
                    rtpmap_codecs[rtpmap_count][k++] = *p++;
                }
                rtpmap_codecs[rtpmap_count][k] = '\0';
            }
            rtpmap_count++;
            LM_DBG("Found rtpmap line with payload %s codec='%s'\n", rtpmap_payloads[rtpmap_count - 1], rtpmap_codecs[rtpmap_count - 1]);
        }
        else if (starts_with(line_start, "a=fmtp:") && fmtp_count < 50)
        {
            fmtp_lines[fmtp_count] = line_start;
            strcpy(fmtp_payloads[fmtp_count], extract_payload(line_start));
            /* store tail of fmtp line (parameters) for heuristic checks and logging */
            {
                char *p = line_start;
                /* find ':' then skip payload */
                while (*p && *p != ':')
                    p++;
                if (*p)
                    p++;
                while (*p && *p != ' ')
                    p++;
                /* p now at space before params or at end */
                if (*p)
                {
                    int len = 0;
                    char *q = p;
                    while (*q && *q != '\r' && *q != '\n' && len < (int)sizeof(fmtp_params[0]) - 1)
                    {
                        fmtp_params[fmtp_count][len++] = *q++;
                    }
                    fmtp_params[fmtp_count][len] = '\0';
                }
                else
                {
                    fmtp_params[fmtp_count][0] = '\0';
                }
            }
            fmtp_count++;
            LM_DBG("Found fmtp line with payload %s params='%s'\n", fmtp_payloads[fmtp_count - 1], fmtp_params[fmtp_count - 1]);
        }

        if (*line_end == '\r')
            line_end++;
        if (*line_end == '\n')
            line_end++;
        line_start = line_end;
    }

    /* Check for mismatched payload numbers and fix them.
     * Additionally, if multiple rtpmap entries describe the same codec,
     * and a fmtp line belongs to that codec but is attached to a different payload,
     * move the fmtp params to the rtpmap payload we choose (prefer first matching payload).
     */
    for (i = 0; i < fmtp_count; i++)
    {
        int found_match = 0;
        int target_j = -1;

        /* Check if this fmtp payload has a corresponding rtpmap (by payload number) */
        for (j = 0; j < rtpmap_count; j++)
        {
            if (strcmp(fmtp_payloads[i], rtpmap_payloads[j]) == 0)
            {
                found_match = 1;
                /* still record target candidates when codec indicates */
                break;
            }
        }

        /* Determine codec-based target rtpmap index for this fmtp (if any) */
        for (j = 0; j < rtpmap_count; j++)
        {
            /* prefer explicit codec token matches using extracted codec names */
            if (rtpmap_codecs[j][0] != '\0')
            {
                if ((strstr(rtpmap_codecs[j], "AMR") && (strstr(fmtp_params[i], "mode-change-capability") || strstr(fmtp_params[i], "octet-align") || strstr(fmtp_params[i], "max-red"))) ||
                    (strstr(rtpmap_codecs[j], "telephone-event") && (strstr(fmtp_params[i], "0-") || strchr(fmtp_params[i], ','))) ||
                    (strstr(rtpmap_codecs[j], "H264") && strstr(fmtp_params[i], "profile-level-id")))
                {
                    target_j = j;
                    break;
                }
            }
        }

        /* fallback: if only one rtpmap, use it */
        if (target_j == -1 && rtpmap_count == 1)
            target_j = 0;

        /* If we have a codec-based target and its payload differs from the fmtp payload, replace */
        if (target_j != -1 && strcmp(rtpmap_payloads[target_j], fmtp_payloads[i]) != 0)
        {
            char *fmtp_line = fmtp_lines[i];
            struct data_lump *lump;
            char *new_fmtp;
            int new_len;
            char *payload_end;

            LM_DBG("fmtp[%d] payload %s -> move to rtpmap[%d] payload %s (codec='%s')\n",
                   i, fmtp_payloads[i], target_j, rtpmap_payloads[target_j], rtpmap_codecs[target_j]);

            /* locate payload tail */
            payload_end = fmtp_line;
            while (*payload_end && *payload_end != ':')
                payload_end++;
            if (*payload_end)
                payload_end++;
            while (*payload_end && *payload_end != ' ')
                payload_end++;

            new_len = strlen("a=fmtp:") + strlen(rtpmap_payloads[target_j]) + strlen(payload_end);
            new_fmtp = pkg_malloc(new_len + 1);
            if (!new_fmtp)
            {
                LM_ERR("Failed to allocate memory for new fmtp line\n");
                return -1;
            }
            snprintf(new_fmtp, new_len + 1, "a=fmtp:%s%s", rtpmap_payloads[target_j], payload_end);

            char *orig_end = find_newline(fmtp_line);
            int orig_len = orig_end - fmtp_line;
            lump = del_lump(msg, fmtp_line - msg->buf, orig_len, 0);
            if (!lump)
            {
                LM_ERR("Failed to create delete lump\n");
                pkg_free(new_fmtp);
                return -1;
            }
            if (insert_new_lump_after(lump, new_fmtp, new_len, 0) == 0)
            {
                LM_ERR("Failed to insert new lump\n");
                pkg_free(new_fmtp);
                return -1;
            }
            LM_INFO("Fixed SDP: Moved fmtp payload %s -> %s for codec '%s'\n", fmtp_payloads[i], rtpmap_payloads[target_j], rtpmap_codecs[target_j]);
            modifications_made = 1;
            continue;
        }

        /* If there is no payload-number match, try heuristic match (original behavior) */
        if (!found_match)
        {
            /* Find a similar codec in rtpmap lines */
            for (j = 0; j < rtpmap_count; j++)
            {
                char *rtpmap_line = rtpmap_lines[j];
                char *fmtp_line = fmtp_lines[i];

                int heuristic_match = 0;
                if (strstr(rtpmap_line, "AMR-WB") &&
                    (strstr(fmtp_line, "mode-change-capability") || strstr(fmtp_line, "octet-align") || strstr(fmtp_line, "max-red")))
                {
                    heuristic_match = 1;
                }
                else if (strstr(rtpmap_line, "telephone-event") && (strstr(fmtp_line, "0-") || strstr(fmtp_line, ",")))
                {
                    heuristic_match = 1;
                }
                else if (strstr(rtpmap_line, "H264") && strstr(fmtp_line, "profile-level-id"))
                {
                    heuristic_match = 1;
                }
                else if (rtpmap_count == 1)
                {
                    heuristic_match = 1;
                }

                if (heuristic_match)
                {
                    /* Replace the fmtp payload number with the rtpmap one */
                    struct data_lump *lump;
                    char *new_fmtp;
                    int new_len;
                    char *payload_end;

                    /* Find the end of payload number in fmtp line */
                    payload_end = fmtp_line;
                    while (*payload_end && *payload_end != ':')
                        payload_end++;
                    if (*payload_end)
                        payload_end++;
                    while (*payload_end && *payload_end != ' ')
                        payload_end++;

                    /* Calculate new line length */
                    new_len = strlen("a=fmtp:") + strlen(rtpmap_payloads[j]) + strlen(payload_end);
                    new_fmtp = pkg_malloc(new_len + 1);
                    if (!new_fmtp)
                    {
                        LM_ERR("Failed to allocate memory for new fmtp line\n");
                        return -1;
                    }

                    /* Create new fmtp line */
                    snprintf(new_fmtp, new_len + 1, "a=fmtp:%s%s", rtpmap_payloads[j], payload_end);

                    /* Find the length of original fmtp line */
                    char *orig_end = find_newline(fmtp_line);
                    int orig_len = orig_end - fmtp_line;

                    /* Create lump to replace the line */
                    lump = del_lump(msg, fmtp_line - msg->buf, orig_len, 0);
                    if (!lump)
                    {
                        LM_ERR("Failed to create delete lump\n");
                        pkg_free(new_fmtp);
                        return -1;
                    }

                    if (insert_new_lump_after(lump, new_fmtp, new_len, 0) == 0)
                    {
                        LM_ERR("Failed to insert new lump\n");
                        pkg_free(new_fmtp);
                        return -1;
                    }

                    LM_INFO("Fixed SDP: Changed fmtp payload from %s to %s\n",
                            fmtp_payloads[i], rtpmap_payloads[j]);
                    modifications_made = 1;
                    break;
                }
            }
        }
    }
    if (!modifications_made)
    {
        /* Extra debug output to help troubleshooting when nothing was changed */
        LM_DBG("SDP fix: no modifications made; rtpmap_count=%d fmtp_count=%d\n", rtpmap_count, fmtp_count);
        for (i = 0; i < rtpmap_count; i++)
        {
            LM_DBG("  rtpmap[%d] payload=%s codec='%s'\n", i, rtpmap_payloads[i], rtpmap_codecs[i]);
        }
        for (i = 0; i < fmtp_count; i++)
        {
            LM_DBG("  fmtp[%d] payload=%s params='%s'\n", i, fmtp_payloads[i], fmtp_params[i]);
        }
    }

    return modifications_made;
}

/* Main function to validate and fix SDP */
static int validate_and_fix_sdp(struct sip_msg *msg)
{
    str body;
    char *sdp_body;
    int sdp_len;

    /* Check if message has SDP content */
    if (parse_headers(msg, HDR_CONTENTTYPE_F, 0) != 0)
    {
        LM_ERR("Failed to parse Content-Type header\n");
        return -1;
    }

    if (!msg->content_type)
    {
        LM_DBG("No Content-Type header found\n");
        return 1; /* Not an error, just no SDP */
    }

    /* Check if it's SDP content */
    if (strncasecmp(msg->content_type->body.s, "application/sdp", 15) != 0)
    {
        LM_DBG("Not SDP content: %.*s\n", msg->content_type->body.len, msg->content_type->body.s);
        return 1; /* Not SDP, but not an error */
    }

    /* Get message body */
    if (get_body(msg, &body) < 0 || body.len == 0)
    {
        LM_ERR("Failed to get message body\n");
        return -1;
    }

    sdp_body = body.s;
    sdp_len = body.len;

    LM_DBG("Processing SDP body (%d bytes)\n", sdp_len);

    /* Fix SDP content */
    return fix_sdp_content(msg, sdp_body, sdp_len);
}

/* Exported function */
static int fix_sdp_rtpmap(struct sip_msg *msg, char *p1, char *p2)
{
    int result;

    LM_DBG("fix_sdp_rtpmap called\n");

    result = validate_and_fix_sdp(msg);

    if (result < 0)
    {
        LM_ERR("Failed to fix SDP\n");
        return -1;
    }
    else if (result == 0)
    {
        LM_DBG("No modifications needed\n");
        return 1;
    }
    else
    {
        LM_INFO("SDP successfully fixed\n");
        return 1;
    }
}
