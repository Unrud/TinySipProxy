#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <errno.h>
#include <sys/select.h>
#include <ctype.h>

#define USER_AGENT "TINY!SIP!PROXY"
static const size_t BUFLEN = 64 * 1024;
static const size_t BRANCHLEN = 36;

static const unsigned short SIP_PORT = 5060;
static const size_t MAX_IPV6_LEN = strlen("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff");
static const size_t NULL_BYTE_LEN = 1;
static const char IPV4_MAPPED_PREFIX_BIN[12] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xFF};
static const char SIP_BRANCH_MAGIC_COOKIE[] = "z9hG4bK";

static const char* override_strerror = NULL;
#define eprintf(level, format, ...) { \
            fprintf(stderr, "%s:%s:%d: " format, level, __FILE__, __LINE__, ##__VA_ARGS__); \
            if (override_strerror != NULL) { \
                fprintf(stderr, " (ERROR: %s)", override_strerror); \
            } else if (errno != 0) { \
                fprintf(stderr, " (ERROR: %s)", strerror(errno)); \
            } \
            fprintf(stderr, "\n"); \
        }
#define fatal(...) { \
            eprintf("FATAL", "" __VA_ARGS__); \
            exit(1); \
        }
#define error(...) eprintf("ERROR", "" __VA_ARGS__)
#define warning(...) eprintf("WARNING", "" __VA_ARGS__)
#define info(...) eprintf("INFO", "" __VA_ARGS__)
#define run_if(expr, block) { \
            override_strerror = NULL; \
            errno = 0; \
            if (expr) { \
                block; \
            } \
        }
#define fatal_if(expr, ...) run_if(expr, fatal(__VA_ARGS__))
#define error_cont_if(expr, ...) run_if(expr, error(__VA_ARGS__); continue)
#define error_ret_if(expr, ...) run_if(expr, error(__VA_ARGS__); return -1)
#define warning_ret_if(expr, ...) run_if(expr, warning(__VA_ARGS__); return -1)

#define save_errno(block) { \
            int saved_errno = errno; \
            block; \
            errno = saved_errno; \
        }

#define stack_sprintf(varname, ...) \
        int varname##_strlen; \
        fatal_if((varname##_strlen = snprintf(NULL, 0, __VA_ARGS__)) < 0); \
        char varname[varname##_strlen + NULL_BYTE_LEN]; \
        fatal_if(snprintf(varname, sizeof(varname), __VA_ARGS__) != varname##_strlen);

static void ip_to_str(struct in6_addr src, char *dst, socklen_t size) {
    int af = AF_INET6;
    int offset = 0;
    if (memcmp(src.s6_addr, IPV4_MAPPED_PREFIX_BIN, sizeof(IPV4_MAPPED_PREFIX_BIN)) == 0) {
        af = AF_INET;
        offset = sizeof(IPV4_MAPPED_PREFIX_BIN);
    }
    fatal_if(inet_ntop(af, src.s6_addr + offset, dst, size) == NULL);
}

static int get_route(struct sockaddr_in6 src, struct in6_addr *dst) {
    int s;
    fatal_if((s = socket(AF_INET6, SOCK_DGRAM, IPPROTO_UDP)) < 0);
    if (connect(s, (struct sockaddr*) &src, sizeof(src)) != 0) {
        fatal_if(close(s) != 0);
        return -1;
    }
    struct sockaddr_in6 dst_local;
    socklen_t si_len = sizeof(dst_local);
    fatal_if(getsockname(s, (struct sockaddr*) &dst_local, &si_len) != 0);
    fatal_if(close(s) != 0);
    *dst = dst_local.sin6_addr;
    return 0;
}

static int get_routable_addr(const char *src, struct sockaddr_in6 *dst, struct in6_addr *route,
                             unsigned short port) {
    int rc;
    struct addrinfo hints;
    bzero(&hints, sizeof(hints));
    hints.ai_family = AF_INET6;
    hints.ai_socktype = SOCK_DGRAM;
    hints.ai_flags = AI_ALL | AI_V4MAPPED | AI_ADDRCONFIG | AI_NUMERICSERV;
    struct addrinfo *result, *rp;
    stack_sprintf(portbuf, "%hu", port);
    if ((rc = getaddrinfo(src, portbuf, &hints, &result)) != 0) {
        override_strerror = gai_strerror(rc);
        return -1;
    }
    struct sockaddr_in6 dst_local;
    struct in6_addr route_local;
    int saved_errno = errno;
    for (rp = result; rp != NULL; rp = rp->ai_next) {
        errno = saved_errno;
        dst_local = *(struct sockaddr_in6*) rp->ai_addr;
        if (get_route(dst_local, &route_local) == 0) {
            break;
        }
    }
    freeaddrinfo(result);
    if (rp == NULL) {
        return -1;
    }
    if (dst != NULL) {
        *dst = dst_local;
    }
    if (route != NULL) {
        *route = route_local;
    }
    return 0;
}

static int str_insert(char *dst, size_t *dst_len, size_t dst_cap, char *dst_insert,
                      const char *src, ssize_t src_len) {
    size_t dst_len_local = 0;
    if (dst_len != NULL) {
        dst_len_local = *dst_len;
    } else {
        dst_len_local = strlen(dst);
    }
    if (src_len < 0) {
        src_len = strlen(src);
    }
    fatal_if(dst_insert < dst || dst + dst_len_local < dst_insert);
    size_t new_dst_len = dst_len_local + src_len;
    if (new_dst_len > dst_cap - NULL_BYTE_LEN) {
        return -1;
    }
    size_t tail_len = dst + dst_len_local - dst_insert;
    memmove(dst_insert + src_len, dst_insert, tail_len);
    memcpy(dst_insert, src, src_len);
    dst[new_dst_len] = 0;
    if (dst_len != NULL) {
        *dst_len = new_dst_len;
    }
    return 0;
}

static int parse_address(char *start_of_addr, char *end_of_addr, char **start_of_host,
                         char **end_of_host, unsigned short *port, unsigned short default_port) {
    char *start_of_port, *end_of_port;
    if (start_of_addr[0] == '[') {
        *start_of_host = start_of_addr + strlen("[");
        if ((*end_of_host = strchr(*start_of_host, ']')) == NULL ||
                *end_of_host >= end_of_addr) {
            return -1;
        }
        start_of_port = *end_of_host + strlen("]");
    } else {
        *start_of_host = start_of_addr;
        if ((*end_of_host = strchr(*start_of_host, ':')) == NULL ||
                *end_of_host >= end_of_addr) {
            *end_of_host = end_of_addr;
        }
        start_of_port = *end_of_host;
    }
    if (start_of_port == end_of_addr) {
        *port = default_port;
        return 0;
    }
    if (start_of_port[0] != ':') {
        return -1;
    }
    start_of_port += strlen(":");
    if ((*port = strtoul(start_of_port, &end_of_port, 10)) == 0 || end_of_port != end_of_addr) {
        return -1;
    }
    return 0;
}

static void random_hex_str(char *dst, size_t len) {
    FILE *dev_urandom;
    char rand;
    fatal_if((dev_urandom = fopen("/dev/urandom", "r")) == NULL, "Failed top open /dev/urandom");
    size_t i;
    for (i = 0; i < len; i += 2) {
        fatal_if(fread(&rand, 1, 1, dev_urandom) != 1);
        fatal_if(snprintf(dst + i, len - i + NULL_BYTE_LEN, "%02hhx", rand) < 0);
    }
    fatal_if(fclose(dev_urandom) != 0);
}

struct header_entry {
    char *start, *end, *column_start, *column_end;
    unsigned int column;
};

static int find_header_entry(char *start_of_header, const char *name, const char *alt_name,
                             unsigned int column, struct header_entry *result) {
    size_t i;
    char *cursor = start_of_header;
    struct header_entry local_result;
    bzero(&local_result, sizeof(local_result));
    while (1) {
        // end of header
        if (strncmp("\r\n", cursor, strlen("\r\n")) == 0) {
            return -1;
        }
        i = 0;
        if (strncasecmp(cursor, name, strlen(name)) == 0) {
            i = strlen(name);
        } else if (alt_name != NULL && strncasecmp(cursor, alt_name, strlen(alt_name)) == 0) {
            i = strlen(alt_name);
        }
        if (i != 0) {
            // find colon
            for (; isblank(cursor[i]) || cursor[i] == ':'; i++) {
                if (cursor[i] == ':') {
                    local_result.start = cursor;
                    local_result.column_start = cursor;
                    local_result.column_end = cursor + i + strlen(":");
                    break;
                }
            }
            if (local_result.start != NULL) {
                break;
            }
        }
        // jump to next line
        if ((cursor = strstr(cursor, "\r\n")) == NULL) {
            return -1;
        }
        cursor += strlen("\r\n");
    }
    while (local_result.end == NULL) {
        if ((cursor = strstr(cursor, "\r\n")) == NULL) {
            local_result.end = cursor + strlen(cursor);
            break;
        }
        cursor += strlen("\r\n");
        if (!isblank(cursor[0])) {
            local_result.end = cursor;
            break;
        }
    }
    while (local_result.column < column) {
        for (local_result.column_start = local_result.column_end;
                local_result.column_start < local_result.end &&
                isspace(local_result.column_start[0]);
                local_result.column_start++);
        if (local_result.column_start == local_result.end) {
            return -1;
        }
        int in_quoted_string = 0;
        int is_escaped = 0;
        local_result.column_end = local_result.column_start;
        do {
            if (local_result.column_end >= local_result.end || (!in_quoted_string &&
                    isspace(local_result.column_end[0]))) {
                break;
            }
            if (local_result.column_end[0] == '"') {
                in_quoted_string = !in_quoted_string || is_escaped;
            }
            is_escaped = in_quoted_string && !is_escaped && local_result.column_end[0] == '\\';
        } while (local_result.column_end++);
        local_result.column++;
    }
    if (result != NULL) {
        *result = local_result;
    }
    return 0;
}

struct attribute_entry {
    char *start, *end, *value_start, *value_end;
};

static int find_attribute(struct header_entry header_entry, const char *name,
                          struct attribute_entry *result) {
    fatal_if(header_entry.column_start == NULL || header_entry.column_end == NULL);
    size_t i;
    char *cursor = header_entry.column_start;
    struct attribute_entry local_result;
    bzero(&local_result, sizeof(local_result));
    while (local_result.start == NULL) {
        if ((cursor = strchr(cursor, ';')) == NULL || cursor >= header_entry.column_end) {
            return -1;
        }
        cursor += strlen(";");
        if (strncmp(cursor, name, strlen(name)) != 0) {
            continue;
        }
        i = strlen(name);
        if (cursor + i < header_entry.column_end &&
                !isspace(cursor[i]) && cursor[i] != ';' && cursor[i] != '=') {
            continue;
        }
        local_result.start = cursor;
        local_result.end = cursor + i;
        if (local_result.end < header_entry.column_end && local_result.end[0] == '=') {
            local_result.value_start = cursor + i + strlen("=");
            for (; cursor + i < header_entry.column_end &&
                 !isspace(cursor[i]) && cursor[i] != ';'; i++);
            local_result.end = local_result.value_end = cursor + i;
        }
    }
    fatal_if(local_result.end > header_entry.column_end);
    if (result != NULL) {
        *result = local_result;
    }
    return 0;
}

__attribute__((unused))
static int copy_header(char *buf, size_t *recvlen, size_t buflen,
                       char *start_of_header, const char *name, const char *alt_name) {
    while (1) {
        struct header_entry header_entry;
        if (find_header_entry(start_of_header, name, alt_name, 0, &header_entry) < 0) {
            return 0;
        }
        error_ret_if(str_insert(buf, recvlen, buflen, buf + *recvlen, header_entry.start,
                                header_entry.end - header_entry.start) < 0,
                     "packet too big");
        start_of_header = header_entry.end;
    }
}

static int parse_via_header(struct header_entry via_header, struct sockaddr_in6 *dst,
                            struct in6_addr *route) {
    char *start_of_addr = via_header.column_start, *end_of_addr;
    for (end_of_addr = start_of_addr; end_of_addr < via_header.column_end &&
         !isspace(end_of_addr[0]) && end_of_addr[0] != ';'; end_of_addr++);
    char *start_of_host, *end_of_host;
    unsigned short rport;
    error_ret_if(parse_address(start_of_addr, end_of_addr, &start_of_host,
                               &end_of_host, &rport, SIP_PORT) < 0, "invalid packet");
    size_t hostlen = end_of_host - start_of_host;
    char hostbuf[hostlen + NULL_BYTE_LEN];
    hostbuf[0] = '\0';
    fatal_if(str_insert(hostbuf, NULL, sizeof(hostbuf), hostbuf, start_of_host, hostlen) < 0);
    struct attribute_entry rport_attribute;
    if (find_attribute(via_header, "rport", &rport_attribute) >= 0 &&
            rport_attribute.value_start != NULL) {
        char *end_of_rport;
        error_ret_if((rport = strtoul(rport_attribute.value_start, &end_of_rport, 10)) == 0 ||
                     end_of_rport != rport_attribute.value_end, "invalid packet");
    }
    error_ret_if(get_routable_addr(hostbuf, dst, route, rport) < 0,
                 "no route to host found: %s", hostbuf);
    return 0;
}

static int handle_message(char *buf, size_t *recvlen, struct sockaddr_in6 si_client,
                          struct sockaddr_in6 *si_remote) {
    int rc;
    struct header_entry via_header;
    error_ret_if(strstr(buf, "\r\n\r\n") == NULL, "invalid packet");
    error_ret_if(find_header_entry(buf, "Via", "v", 2, &via_header) < 0, "invalid packet");
    char *start_of_sip, *end_of_sip;
    error_ret_if((start_of_sip = strchr(buf, ' ')) == NULL, "invalid packet");
    start_of_sip += strlen(" ");
    error_ret_if((end_of_sip = strchr(start_of_sip, ' ')) == NULL, "invalid packet");
    error_ret_if(strncmp(start_of_sip, "sips:", strlen("sips:")) == 0, "sips not supported");
    if (strncmp(start_of_sip, "sip:", strlen("sip:")) == 0) {
        // client message
        char *start_of_protocol = end_of_sip + strlen(" ");
        error_ret_if(strncmp(start_of_protocol, "SIP/", strlen("SIP/")) != 0, "invalid packet");
        struct header_entry max_forwards_header;
        error_ret_if(find_header_entry(buf, "Max-Forwards", NULL, 1, &max_forwards_header) < 0,
                     "invalid packet");
        unsigned long int max_forwards;
        char *end_of_max_forwards;
        error_ret_if((max_forwards = strtoul(max_forwards_header.column_start,
                                             &end_of_max_forwards, 10)) <= 1, "too many hops");
        error_ret_if(end_of_max_forwards != max_forwards_header.column_end, "invalid packet");
        max_forwards = (max_forwards <= 70) ? max_forwards - 1 : 70;
        char max_forwardsbuf[strlen("70") + NULL_BYTE_LEN];
        fatal_if((rc = snprintf(max_forwardsbuf, sizeof(max_forwardsbuf), "%lu",
                                max_forwards)) < 0 || (unsigned int) rc >= sizeof(max_forwardsbuf));
        memmove(max_forwards_header.column_start, max_forwards_header.column_end,
                buf + (*recvlen + NULL_BYTE_LEN) - max_forwards_header.column_end);
        *recvlen -= max_forwards_header.column_end - max_forwards_header.column_start;
        fatal_if(str_insert(buf, recvlen, BUFLEN, max_forwards_header.column_start,
                            max_forwardsbuf, -1), "packet too big");
        struct attribute_entry rport_attribute;
        if (find_attribute(via_header, "rport", &rport_attribute) == 0 &&
                rport_attribute.value_start == NULL) {
            stack_sprintf(portbuf, "=%hu", ntohs(si_client.sin6_port));
            error_ret_if(str_insert(buf, recvlen, BUFLEN, rport_attribute.end,
                                    portbuf, -1) < 0, "packet too big");
        }
        char *start_of_addr, *end_of_addr = end_of_sip;
        if ((start_of_addr = strchr(start_of_sip, '@')) != NULL &&
                start_of_addr < end_of_addr) {
            start_of_addr += strlen("@");
        } else {
            start_of_addr = start_of_sip + strlen("sip:");
        }
        char *start_of_host, *end_of_host;
        unsigned short port;
        error_ret_if(parse_address(start_of_addr, end_of_addr, &start_of_host,
                                   &end_of_host, &port, SIP_PORT) < 0, "invalid packet");
        size_t hostlen = end_of_host - start_of_host;
        char hostbuf[hostlen + NULL_BYTE_LEN];
        hostbuf[0] = '\0';
        fatal_if(str_insert(hostbuf, NULL, sizeof(hostbuf), hostbuf, start_of_host, hostlen) < 0);
        struct in6_addr outbound_addr;
        error_ret_if(get_routable_addr(hostbuf, si_remote, &outbound_addr, port) < 0,
                     "no route to host found: %s", hostbuf);
        char outbound_addrbuf[MAX_IPV6_LEN + NULL_BYTE_LEN], branchbuf[BRANCHLEN + NULL_BYTE_LEN];
        ip_to_str(outbound_addr, outbound_addrbuf, sizeof(outbound_addrbuf));
        random_hex_str(branchbuf, sizeof(branchbuf) - NULL_BYTE_LEN);
        char *before_addr = "", *after_addr = "";
        if (strchr(outbound_addrbuf, ':') != NULL) {
            before_addr = "[";
            after_addr = "]";
        }
        stack_sprintf(viabuf, "Via: SIP/2.0/UDP %s%s%s:%hu;branch=%s%s\r\n", before_addr,
                      outbound_addrbuf, after_addr, SIP_PORT, SIP_BRANCH_MAGIC_COOKIE, branchbuf);
        error_ret_if(str_insert(buf, recvlen, BUFLEN, via_header.start, viabuf, -1) < 0,
                     "packet too big");
    } else {
        // server message
        char *start_of_protocol = buf;
        error_ret_if(strncmp(start_of_protocol, "SIP/", strlen("SIP/")) != 0, "invalid packet");
        // remove top Via header
        memmove(via_header.start, via_header.end,
                buf + (*recvlen + NULL_BYTE_LEN) - via_header.end);
        *recvlen -= via_header.end - via_header.start;
        error_ret_if(find_header_entry(buf, "Via", "v", 2, &via_header) < 0, "invalid packet");
        if (parse_via_header(via_header, si_remote, NULL) != 0) {
            return -1;
        }
    }
    return 0;
}

int main() {
    char buf[BUFLEN];
    struct sockaddr_in6 si_server, si_client, si_remote;
    bzero(&si_server, sizeof(si_server));
    si_server.sin6_family = AF_INET6;
    si_server.sin6_port = htons(SIP_PORT);
    si_server.sin6_addr = in6addr_any;
    int sock;
    fatal_if((sock = socket(AF_INET6, SOCK_DGRAM|SOCK_CLOEXEC, IPPROTO_UDP)) < 0);
    int option_value = 0;
    fatal_if(setsockopt(sock, IPPROTO_IPV6, IPV6_V6ONLY, &option_value, sizeof(option_value)) < 0);
    fatal_if(bind(sock, (struct sockaddr*) &si_server, sizeof(si_server)) < 0,
             "can't bind to port %hu", SIP_PORT);
    fd_set rfds;
    FD_ZERO(&rfds);
    FD_SET(sock, &rfds);
    // mainloop
    while (1) {
        fatal_if(select(sock + 1, &rfds, NULL, NULL, NULL) < 0);
        ssize_t recvlen;
        socklen_t si_len = sizeof(si_client);
        fatal_if((recvlen = recvfrom(
            sock, buf, BUFLEN, 0, (struct sockaddr*) &si_client, &si_len)) < 0);
        error_cont_if((size_t) recvlen > BUFLEN - NULL_BYTE_LEN, "packet too big");
        // safe for string functions
        buf[recvlen] = '\0';
        if (handle_message(buf, (size_t *) &recvlen, si_client, &si_remote) == 0) {
            error_cont_if(sendto(sock, buf, recvlen, 0, (struct sockaddr*) &si_remote,
                                 sizeof(si_remote)) < 0, "failed to send");
        }
    }
    // unreachable
    return 0;
}
