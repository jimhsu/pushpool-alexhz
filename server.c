/*
 * Copyright 2011 Jeff Garzik
 * Copyright 2009 Red Hat, Inc.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include "autotools-config.h"

#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <locale.h>
#include <unistd.h>
#include <signal.h>
#include <syslog.h>
#include <fcntl.h>
#include <string.h>
#include <zlib.h>
#include <netdb.h>
#include <stdarg.h>

#include <openssl/sha.h>
#include <argp.h>
#include "server.h"

const char *argp_program_version = PACKAGE_VERSION;

enum {
	CLI_RD_TIMEOUT		= 30,
	CLI_MAX_MSG		= (1 * 1024 * 1024),

	SFL_FOREGROUND		= (1 << 0),	/* run in foreground */
};

static struct argp_option options[] = {
	{ "config", 'c', "FILE", 0,
	  "Read master configuration from FILE (default: server.json)" },
	{ "debug", 'D', "LEVEL", 0,
	  "Set debug output to LEVEL (0 = off, 2 = max)" },
	{ "stderr", 'E', NULL, 0,
	  "Switch the log to standard error" },
	{ "foreground", 'F', NULL, 0,
	  "Run in foreground, do not fork" },
	{ "pid", 'P', "FILE", 0,
	  "Write daemon process id to FILE" },
	{ "strict-free", 1001, NULL, 0,
	  "For memory-checker runs.  When shutting down server, free local "
	  "heap, rather than simply exit(2)ing and letting OS clean up." },
	{ }
};

static const char doc[] =
PROGRAM_NAME " - push-mining proxy daemon";


static error_t parse_opt (int key, char *arg, struct argp_state *state);


static const struct argp argp = { options, parse_opt, NULL, doc };

typedef enum lp_type {
	LP_NONE = 0,
	LP_REPLY,
	LP_KEEPALIVE,
	LP_CLOSE,
} lp_type;

static bool server_running = true;
static bool dump_stats;
static bool reopen_logs;
static lp_type initiate_lp_flush;
bool use_syslog = true;
static bool strict_free = false;
int debugging = 0;
struct timeval current_time;

struct server srv = {
	.config		= "server.json",
	.pid_fd		= -1,
	.req_fd		= -1,
	.share_fd	= -1,

#if defined(HAVE_SQLITE3)
	.db_eng		= SDB_SQLITE,
	.db_ops		= &sqlite_db_ops,
#elif defined(HAVE_MYSQL)
	.db_eng		= SDB_MYSQL,
	.db_ops		= &mysql_db_ops,
#elif defined(HAVE_POSTGRESQL)
	.db_eng		= SDB_POSTGRESQL,
	.db_ops		= &postgresql_db_ops,
#else
#error("No valid database engines defined")
#endif
	.db_port	= -1,

	.cred_expire	= 75,
	.work_expire	= 120,
};

static error_t parse_opt (int key, char *arg, struct argp_state *state)
{
	int v;

	switch(key) {
	case 'c':
		srv.config = arg;
		break;
	case 'D':
		v = atoi(arg);
		if (v < 0 || v > 2) {
			fprintf(stderr, "invalid debug level: '%s'\n", arg);
			argp_usage(state);
		}
		debugging = v;
		break;
	case 'E':
		use_syslog = false;
		break;
	case 'F':
		srv.flags |= SFL_FOREGROUND;
		break;
	case 'P':
		srv.pid_file = strdup(arg);
		break;
	case 1001:			/* --strict-free */
		strict_free = true;
		break;
	case ARGP_KEY_ARG:
		argp_usage(state);	/* too many args */
		break;
	case ARGP_KEY_END:
		break;
	default:
		return ARGP_ERR_UNKNOWN;
	}

	return 0;
}

static bool valid_auth_hdr(const char *hdr, char *username_out)
{
	char *t_type = NULL;
	char *t_b64 = NULL;
	char *t_userpass = NULL, *colon, *user, *pass;
	char *pass_db = NULL;
	bool rc = false;
	size_t hdrlen = strlen(hdr);
	size_t bin_len = 0;
	void *bin = NULL;

	t_type = calloc(1, hdrlen + 1);
	t_b64 = calloc(1, hdrlen + 1);
	t_userpass = calloc(1, hdrlen + 1);
	if (!t_type || !t_b64 || !t_userpass)
		goto out;
	if (sscanf(hdr, "%s %s", t_type, t_b64) != 2)
		goto out;

	/* auth type Basic */
	if (strcasecmp(t_type, "basic"))
		goto out;

	/* decode base64 token */
	bin = g_base64_decode(t_b64, &bin_len);
	if (!bin)
		goto out;
	if (bin_len > hdrlen)		/* impossible */
		goto out;
	memcpy(t_userpass, bin, bin_len);

	/* split user:pass */
	colon = strchr(t_userpass, ':');
	if (!colon)
		goto out;
	*colon = 0;
	user = t_userpass;
	pass = colon + 1;

	/* password database authentication check */
	pass_db = pwdb_lookup(user);
	if (!pass_db || (strcmp(pass, pass_db) && *pass_db != '\0'))
		goto out;

	rc = true;
	strncpy(username_out, user, 64);
	username_out[64] = 0;

out:
	free(pass_db);
	free(bin);
	free(t_type);
	free(t_b64);
	free(t_userpass);
	return rc;
}

static void reqlog(const char *rem_host, const char *username,
		   const char *uri)
{
	struct timeval tv = { };
	char *f;
	ssize_t wrc;
	struct tm tm;

	if (srv.req_fd < 0)
		return;

	gettimeofday(&tv, NULL);
	gmtime_r(&tv.tv_sec, &tm);

	if (asprintf(&f, "[%d-%02d-%02d %02d:%02d:%02d.%llu] %s %s \"%s\"\n",
		tm.tm_year + 1900,
		tm.tm_mon + 1,
		tm.tm_mday,
		tm.tm_hour,
		tm.tm_min,
		tm.tm_sec,
		(unsigned long long) tv.tv_usec,
	        (rem_host && *rem_host) ? rem_host : "-",
	        (username && *username) ? username : "-",
	        (uri && *uri) ? uri : "") < 0)
		return;

	wrc = write(srv.req_fd, f, strlen(f));
	if (wrc != strlen(f))
		syslogerr(srv.req_log);

	free(f);
}

void sharelog(struct server_auxchain *aux,
	      const char *rem_host, const char *username,
	      const char *our_result, const char *upstream_result,
	      const char *reason, const char *solution)
{
	struct timeval tv = { };
	char *f;
	ssize_t wrc;
	struct tm tm;

	if (srv.db_sharelog && srv.db_ops->sharelog != NULL)
		srv.db_ops->sharelog(aux, rem_host, username, our_result,
				     upstream_result, reason, solution);

	if (srv.share_fd < 0)
		return;

	gettimeofday(&tv, NULL);
	gmtime_r(&tv.tv_sec, &tm);

	if (asprintf(&f, "[%d-%02d-%02d %02d:%02d:%02.6f] %s %s %s %s %s %s%s%s\n",
		tm.tm_year + 1900,
		tm.tm_mon + 1,
		tm.tm_mday,
		tm.tm_hour,
		tm.tm_min,
		tm.tm_sec +
		tv.tv_usec/1000000.0,
	        (rem_host && *rem_host) ? rem_host : "-",
	        (username && *username) ? username : "-",
	        (our_result && *our_result) ? our_result : "-",
	        (upstream_result && *upstream_result) ? upstream_result : "-",
	        (reason && *reason) ? reason : "-",
		(solution && *solution) ? solution : "-",
		aux ? " " : "", aux ? aux->rpc_url : "") < 0)
		return;

	wrc = write(srv.share_fd, f, strlen(f));
	if (wrc != strlen(f))
		syslogerr(srv.share_log);

	free(f);
}

static bool http_get_username(struct evhttp_request *req, char *username, bool headers_sent)
{
	const char *auth;

	auth = evhttp_find_header(req->input_headers, "Authorization");
	if (!auth) {
		reqlog(req->remote_host, username, req->uri);
		if (!headers_sent) {
			evhttp_add_header(req->output_headers, "WWW-Authenticate", "Basic realm=\"pool.itzod.ru\"");
			evhttp_send_reply(req, 401, "not authorized", NULL);
		}
		return false;
	}
	if (!valid_auth_hdr(auth, username)) {
		reqlog(req->remote_host, username, req->uri);
		if (!headers_sent)
			evhttp_send_reply(req, 403, "access forbidden", NULL);
		return false;
	}

	return true;
}

static void http_set_headers(struct evhttp_request *req, struct server_socket *sock, bool longpoll)
{
	evhttp_clear_headers(req->output_headers);

	/* Add header to debug load balancing */
	if (srv.ourhost)
		evhttp_add_header(req->output_headers, "X-Server", srv.ourhost);

	/* copy X-Forwarded-For header to remote_host, if a trusted proxy provides it */
	if (sock->cfg->proxy && !strcmp(req->remote_host, sock->cfg->proxy)) {
		const char *hdr;
		hdr = evhttp_find_header(req->input_headers, "X-Forwarded-For");
		if (hdr) {
			free(req->remote_host);
			req->remote_host = strdup(hdr);
		}
	}

	evhttp_add_header(req->output_headers,
			  "Content-Type", "application/json");
	if (!longpoll && !srv.disable_lp)
		evhttp_add_header(req->output_headers, "X-Long-Polling", "/LP");
	if (!srv.disable_roll_ntime)
		evhttp_add_header(req->output_headers, "X-Roll-NTime", "Y");
}

static inline bool is_valid(bool *valid)
{
	if (valid && *valid)
		return true;
	return false;
}

static void http_handle_req(struct evhttp_request *req, lp_type longpoll, bool *req_valid)
{
	const char *clen_str;
	char *body_str;
	char username[65] = "";
	void *body, *reply = NULL;
	int clen = 0;
	unsigned int reply_len = 0;
	json_t *jreq;
	json_error_t jerr;
	bool rc;
	struct evbuffer *evbuf;

	if (!http_get_username(req, username, req->chunked))
 		return;

	if (longpoll == LP_NONE) {
		clen_str = evhttp_find_header(req->input_headers, "Content-Length");
		if (clen_str)
			clen = atoi(clen_str);
		if (clen < 1 || clen > 999999) {
			reqlog(req->remote_host, username, req->uri);
			goto err_out_bad_req;
		}

		if (EVBUFFER_LENGTH(req->input_buffer) != clen)
			goto err_out_bad_req;
		body = EVBUFFER_DATA(req->input_buffer);
		body_str = strndup(body, clen);
		if (!body_str)
			goto err_out_bad_req;
	} else if (longpoll == LP_REPLY) {
		body_str = strdup("{\"method\":\"getwork\",\"params\":[],\"id\":1}");
	} else if (longpoll == LP_KEEPALIVE || longpoll == LP_CLOSE) {
		reply = malloc(sizeof(char) * 2);
		if (!reply)
			goto err_out_bad_req;
		reply_len = snprintf(reply, 2, " ");
	}

	if (!reply) {
		jreq = JSON_LOADS(body_str, &jerr);

		free(body_str);

		if (!jreq)
			goto err_out_bad_req;

		rc = msg_json_rpc(req, jreq, username, &reply, &reply_len);

		json_decref(jreq);

		if (!rc)
			goto err_out_bad_req;
	}

	evbuf = evbuffer_new();
	if (!evbuf) {
		free(reply);
		goto err_out_bad_req;
	}
	if (evbuffer_add(evbuf, reply, reply_len)) {
		evbuffer_free(evbuf);
		free(reply);
		goto err_out_bad_req;
	}

	free(reply);

	/* req_valid is a pointer to the valid member of the list struct
	 * containing the LP request. When the connection drops and
	 * http_lp_close_cb is called, this bool is set to false. Because we
	 * have the reference, we can check before each send command if the
	 * close callback has been called or if the request is still OK.
	 *
	 * We only have to check this when sending chunked, because if we send
	 * in one go, there is nothing that could have closed the request, as
	 * we're single threaded. For now.
	 */
	if (longpoll == LP_NONE) {
		/* Send normal requests not chunked */
		evhttp_send_reply(req, HTTP_OK, "ok", evbuf);
	} else {
		if (!req->chunked && is_valid(req_valid))
			evhttp_send_reply_start(req, HTTP_OK, "ok");
		if (is_valid(req_valid))
			evhttp_send_reply_chunk(req, evbuf);
		if (longpoll != LP_KEEPALIVE && is_valid(req_valid))
			evhttp_send_reply_end(req);
	}

	evbuffer_free(evbuf);

	return;

err_out_bad_req:
	/* When we've already sent headers, we can't really give an error so
	 * we just send an empty reply...
	 */
	if (req->chunked) {
		if (is_valid(req_valid))
			evhttp_send_reply_end(req);
	} else {
		evhttp_send_reply(req, HTTP_BADREQUEST, "invalid args", NULL);
	}
}

static void lp_keepalive_reset(struct event *ev, bool new)
{
	struct timeval tv;

	if (srv.lp_keepalive_interval <= 0)
		return;

	tv.tv_sec = srv.lp_keepalive_interval;
	tv.tv_usec = 0;

	if (evtimer_pending(ev, NULL) == EV_TIMEOUT)
		evtimer_del(ev);

	if (new)
		evtimer_add(ev, &tv);
	return;
}

static void fetch_new_work_reset(struct event *ev, bool new)
{
	struct timeval tv;

	tv.tv_sec = rand() % 10 + 1;
	tv.tv_usec = 0;

	if (evtimer_pending(ev, NULL) == EV_TIMEOUT)
		evtimer_del(ev);

	if (new)
		evtimer_add(ev, &tv);
	return;
}


static void flush_lp_waiters(lp_type type)
{
	struct genlist *tmp, *iter;
	char *lp_type_str[] = {"none", "reply", "keep-alive", "close"};
 
	applog(LOG_DEBUG, "LP flush waiters: %s", lp_type_str[type]);

	elist_for_each_entry_safe(tmp, iter, &srv.lp_waiters, node) {
		struct evhttp_request *req;

		req = tmp->data;
		if (req && tmp->valid)
			http_handle_req(req, type, &tmp->valid);
		if (type != LP_KEEPALIVE) {
			if (req)
				evhttp_connection_set_closecb(req->evcon, NULL, NULL);
			elist_del(&tmp->node);
			memset(tmp, 0, sizeof(*tmp));
			free(tmp);
		}
	}
	lp_keepalive_reset(&srv.ev_lp_keepalive, (type != LP_CLOSE));
}

void http_lp_close_cb(struct evhttp_connection *evcon, void *arg)
{
	struct genlist *list = (struct genlist *)arg;

	/* We don't delete the list item in case we are iterating
	 * over it just now in flush_lp_waiters. Instead, we set
	 * the req to NULL so we know to not touch it anymore. It
	 * will get deleted on LP.
	 */
	list->data = NULL;
	list->valid = false;
}

static void __http_srv_event(struct evhttp_request *req, void *arg,
			     bool longpoll)
{
	struct server_socket *sock = arg;
	const char *auth;
	char username[65] = "";
	
	http_set_headers(req, sock, longpoll);

	if (!http_get_username(req, username, false))
		return;

	reqlog(req->remote_host, username, req->uri);

	/* if longpoll, don't respond now, queue onto list for later */
	if (longpoll) {
		struct genlist *gl = calloc(1, sizeof(*gl));
		if (!gl)
			return;

		gl->data = req;
		gl->valid = true;
		INIT_ELIST_HEAD(&gl->node);

		evhttp_connection_set_closecb(req->evcon, http_lp_close_cb, gl);
		elist_add_tail(&gl->node, &srv.lp_waiters);
	}

	/* otherwise, handle immediately */
	else
		http_handle_req(req, LP_NONE, NULL);
}

static void http_srv_event(struct evhttp_request *req, void *arg)
{
	__http_srv_event(req, arg, false);
}

static void http_srv_event_lp(struct evhttp_request *req, void *arg)
{
	__http_srv_event(req, arg, true);
}

static int net_write_port(const char *port_file, const char *port_str)
{
	FILE *portf;
	int rc;

	portf = fopen(port_file, "w");
	if (portf == NULL) {
		rc = errno;
		applog(LOG_INFO, "Cannot create port file %s: %s",
		       port_file, strerror(rc));
		return -rc;
	}
	fprintf(portf, "%s\n", port_str);
	fclose(portf);
	return 0;
}

static void net_sock_free(struct server_socket *sock)
{
	if (!sock)
		return;

	elist_del_init(&sock->sockets_node);

	if (sock->http)
		evhttp_free(sock->http);
	else
		event_del(&sock->ev);

	if (sock->fd >= 0)
		close(sock->fd);

	memset(sock, 0, sizeof(*sock));	/* poison */
	free(sock);
}

static void net_close(void)
{
	struct server_socket *sock, *iter;
	struct listen_cfg *cfg, *citer;

	elist_for_each_entry_safe(sock, iter, &srv.sockets, sockets_node) {
		net_sock_free(sock);
	}

	elist_for_each_entry_safe(cfg, citer, &srv.listeners, listeners_node) {
		elist_del_init(&cfg->listeners_node);
		free(cfg->host);
		free(cfg->port_file);
		memset(cfg, 0, sizeof(*cfg)); /* poison */
		free(cfg);
	}
}

static int net_open_socket(const struct listen_cfg *cfg,
			   int addr_fam, int sock_type, int sock_prot,
			   int addr_len, void *addr_ptr)
{
	struct server_socket *sock;
	int fd, on;
	int rc;
	bool have_http = (cfg->proto == LP_HTTP_JSON);

	fd = socket(addr_fam, sock_type, sock_prot);
	if (fd < 0) {
		rc = errno;
		syslogerr("tcp socket");
		return -rc;
	}

	on = 1;
	if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on)) < 0) {
		syslogerr("setsockopt(SO_REUSEADDR)");
		rc = -errno;
		goto err_out_fd;
	}

	if (bind(fd, addr_ptr, addr_len) < 0) {
		syslogerr("tcp bind");
		rc = -errno;
		goto err_out_fd;
	}

	if (listen(fd, 100) < 0) {
		syslogerr("tcp listen");
		rc = -errno;
		goto err_out_fd;
	}

	rc = fsetflags("tcp server", fd, O_NONBLOCK);
	if (rc)
		goto err_out_fd;

	sock = calloc(1, sizeof(*sock));
	if (!sock) {
		rc = -ENOMEM;
		goto err_out_fd;
	}

	INIT_ELIST_HEAD(&sock->sockets_node);

	sock->fd = fd;
	sock->cfg = cfg;

	sock->http = evhttp_new(srv.evbase_main);
	if (!sock->http)
		goto err_out_sock;

	if (evhttp_accept_socket(sock->http, fd) < 0) {
		evhttp_free(sock->http);
		goto err_out_sock;
	}

	evhttp_set_cb(sock->http, "/",
		      http_srv_event, sock);
	if (!srv.disable_lp)
		evhttp_set_cb(sock->http, "/LP",
		      http_srv_event_lp,sock);

	elist_add_tail(&sock->sockets_node, &srv.sockets);

	return fd;

err_out_sock:
	free(sock);
err_out_fd:
	close(fd);
	return rc;
}

static int net_open_known(const struct listen_cfg *cfg)
{
	int ipv6_found = 0;
	int rc;
	struct addrinfo hints, *res, *res0;
	char port_str[16];

	memset(&hints, 0, sizeof(hints));
	hints.ai_family = PF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_flags = AI_PASSIVE;

	sprintf(port_str, "%d", cfg->port);

	rc = getaddrinfo(cfg->host, port_str, &hints, &res0);
	if (rc) {
		applog(LOG_ERR, "getaddrinfo(%s:%s) failed: %s",
		       cfg->host ? cfg->host : "*",
		       cfg->port, gai_strerror(rc));
		return -EINVAL;
	}

#ifdef __linux__
	/*
	 * We rely on getaddrinfo to discover if the box supports IPv6.
	 * Much easier to sanitize its output than to try to figure what
	 * to put into ai_family.
	 *
	 * These acrobatics are required on Linux because we should bind
	 * to ::0 if we want to listen to both ::0 and 0.0.0.0. Else, we
	 * may bind to 0.0.0.0 by accident (depending on order getaddrinfo
	 * returns them), then bind(::0) fails and we only listen to IPv4.
	 */
	for (res = res0; res; res = res->ai_next) {
		if (res->ai_family == PF_INET6)
			ipv6_found = 1;
	}
#endif

	for (res = res0; res; res = res->ai_next) {
		char listen_host[65], listen_serv[65];

		if (ipv6_found && res->ai_family == PF_INET)
			continue;

		rc = net_open_socket(cfg, res->ai_family, res->ai_socktype,
				     res->ai_protocol,
				     res->ai_addrlen, res->ai_addr);
		if (rc < 0)
			goto err_out;

		getnameinfo(res->ai_addr, res->ai_addrlen,
			    listen_host, sizeof(listen_host),
			    listen_serv, sizeof(listen_serv),
			    NI_NUMERICHOST | NI_NUMERICSERV);

		applog(LOG_INFO, "Listening on host %s port %s",
		       listen_host, listen_serv);
	}

	freeaddrinfo(res0);

	if (cfg->port_file)
		net_write_port(cfg->port_file, port_str);
	return 0;

err_out:
	freeaddrinfo(res0);
	return rc;
}

/*
 * Find out own hostname.
 * This is needed for:
 *  - finding the local domain and its SRV records
 * Do this before our state machines start ticking, so we can quit with
 * a meaningful message easily.
 */
static char *get_hostname(void)
{
	enum { hostsz = 64 };
	char hostb[hostsz];
	char *ret;

	if (gethostname(hostb, hostsz-1) < 0) {
		applog(LOG_ERR, "get_hostname: gethostname error (%d): %s",
		       errno, strerror(errno));
		exit(1);
	}
	hostb[hostsz-1] = 0;
	if ((ret = strdup(hostb)) == NULL) {
		applog(LOG_ERR, "get_hostname: no core (%ld)",
		       (long)strlen(hostb));
		exit(1);
	}
	return ret;
}

static void term_signal(int signo)
{
	server_running = false;
	event_loopbreak();
}

static int log_reopen(int fd, const char *fn)
{
	if (!fn || !*fn)
		return -1;

	if ((fd >= 0) && (close(fd) < 0))
		syslogerr(fn);

	fd = open(fn, O_WRONLY | O_CREAT | O_APPEND, 0666);
	if (fd < 0)
		syslogerr(fn);

	return fd;
}

static void usr1_signal(int signo)
{
	if (debugging)
		applog(LOG_INFO, "USR1 signal received, flushing LP waiters");

	initiate_lp_flush = LP_REPLY;
	event_loopbreak();
}

static void hup_signal(int signo)
{
	applog(LOG_INFO, "HUP signal received, reopening logs");

	reopen_logs = true;
	event_loopbreak();
}

static void stats_signal(int signo)
{
	dump_stats = true;
	event_loopbreak();
}

#define X(stat) \
	applog(LOG_INFO, "STAT %s %lu", #stat, srv.stats.stat)

static void stats_dump(void)
{
	X(poll);
	X(event);
	X(tcp_accept);
	X(opt_write);
}

#undef X

static void lp_keepalive_cb(int fd, short what, void *arg)
{
	if (what != EV_TIMEOUT)
		return;

	applog(LOG_INFO, "Triggering LP keepalive");
	lp_keepalive_reset(&srv.ev_lp_keepalive, false);

	initiate_lp_flush = LP_KEEPALIVE;
	event_loopbreak();

	return;
}

static void fetch_new_work_cb(int fd, short what, void *arg)
{
	if (what != EV_TIMEOUT)
		return;

	applog(LOG_INFO, "Fetching new work");
	fetch_new_work();
	fetch_new_work_reset(&srv.ev_fetch_new_work, true);
	//event_loopbreak();

	return;
}

static int main_loop(void)
{
	int rc = 0;

	while (server_running) {
		event_dispatch();

		if (dump_stats) {
			dump_stats = false;
			stats_dump();
		}
		if (reopen_logs) {
			reopen_logs = false;
			srv.req_fd = log_reopen(srv.req_fd, srv.req_log);
			srv.share_fd = log_reopen(srv.share_fd, srv.share_log);
		}
		if (initiate_lp_flush != LP_NONE) {

			if(initiate_lp_flush == LP_REPLY)
			{
			    fetch_new_work();
			    fetch_new_work_reset(&srv.ev_fetch_new_work, true);
			}

			flush_lp_waiters(initiate_lp_flush);
			initiate_lp_flush = LP_NONE;
		}
	}

	return rc;
}

int main (int argc, char *argv[])
{
	error_t aprc;
	int rc = 1;
	struct elist_head *tmpl;

	INIT_ELIST_HEAD(&srv.listeners);
	INIT_ELIST_HEAD(&srv.sockets);
	INIT_ELIST_HEAD(&srv.work_log);
	INIT_ELIST_HEAD(&srv.lp_waiters);
	INIT_ELIST_HEAD(&srv.auxchains);

	/* isspace() and strcasecmp() consistency requires this */
	setlocale(LC_ALL, "C");

	/*
	 * Unfortunately, our initialization order is rather rigid.
	 *
	 * First, parse command line. This way errors in parameters can
	 * be written to stderr, where they belong.
	 */
	aprc = argp_parse(&argp, argc, argv, 0, NULL, NULL);
	if (aprc) {
		fprintf(stderr, "argp_parse failed: %s\n", strerror(aprc));
		return 1;
	}

	/*
	 * Next, open syslog. From now on, nothing goes to stderr, and
	 * we minimize (or hopefuly eliminate) opening libraries that
	 * do not have a switcheable diagnostic output.
	 */
	if (use_syslog)
		openlog(PROGRAM_NAME, LOG_PID, LOG_LOCAL3);
	if (debugging)
		applog(LOG_INFO, "Debug output enabled");

	srv.evbase_main = event_init();

	/* must initialize memcached_st obj prior to reading config */
	srv.mc = memcached_create(NULL);
	if (!srv.mc) {
		applog(LOG_ERR, "memcached init failed");
		goto err_out;
	}
	memcached_behavior_set(srv.mc, MEMCACHED_BEHAVIOR_BINARY_PROTOCOL, 1);

	/*
	 * Next, read master configuration. This should be done as
	 * early as possible, so that tunables are available.
	 */
	read_config();
	if (!srv.ourhost)
		srv.ourhost = get_hostname();
	else if (debugging)
		applog(LOG_INFO, "Forcing local hostname to %s",
		       srv.ourhost);

	/*
	 * For example, backgrounding and PID file should be done early
	 * (before we do anything that can conflict with other instance),
	 * but not before read_config().
	 */
	if (!(srv.flags & SFL_FOREGROUND) && (daemon(1, !use_syslog) < 0)) {
		syslogerr("daemon");
		goto err_out;
	}

	rc = write_pid_file(srv.pid_file);
	if (rc < 0)
		goto err_out;
	srv.pid_fd = rc;

	srv.hist = hist_alloc();
	if (!srv.hist)
		goto err_out;

	/*
	 * properly capture TERM and other signals
	 */
	signal(SIGUSR1, usr1_signal);
	signal(SIGHUP, hup_signal);
	signal(SIGPIPE, SIG_IGN);
	signal(SIGINT, term_signal);
	signal(SIGTERM, term_signal);
	signal(SIGUSR2, stats_signal);

	srv.curl = curl_easy_init();
	if (!srv.curl) {
		applog(LOG_ERR, "CURL init failed");
		goto err_out;
	}

	srv.workers = htab_str_new(false, true);
	if (!srv.workers) {
		applog(LOG_ERR, "htab init failed");
		goto err_out;
	}

	/* set up server networking */
	elist_for_each(tmpl, &srv.listeners) {
		struct listen_cfg *tmpcfg;

		tmpcfg = elist_entry(tmpl, struct listen_cfg, listeners_node);
		rc = net_open_known(tmpcfg);
		if (rc)
			goto err_out_listen;
	}

	if (!srv.db_ops->open())
		goto err_out_listen;

	applog(LOG_INFO, "initialized");

	/* set up longpolling keep-alive timer */
	if (srv.lp_keepalive_interval > 0) {
		applog(LOG_INFO, "Enabling %ds LP keep-alive", srv.lp_keepalive_interval);
		evtimer_set(&srv.ev_lp_keepalive, lp_keepalive_cb, NULL);
		lp_keepalive_reset(&srv.ev_lp_keepalive, true);
	}

	/* set up fetch_new_work timer */
	if (srv.easy_target) {
		applog(LOG_INFO, "Enabling fetch_new_work timer");
		evtimer_set(&srv.ev_fetch_new_work, fetch_new_work_cb, NULL);
		fetch_new_work_reset(&srv.ev_fetch_new_work, true);
	}

        if(!fetch_new_work() && !elist_empty(&srv.listeners)) {
		applog(LOG_ERR, "error: using aux chains but getworkex not available");
		exit(1);
	}

	rc = main_loop();

	applog(LOG_INFO, "shutting down");

	srv.db_ops->close();

err_out_listen:
	/* we ignore closing sockets, as process exit does that for us */
	unlink(srv.pid_file);
	close(srv.pid_fd);
err_out:
	closelog();

	if (strict_free) {
		flush_lp_waiters(LP_CLOSE);
		hist_free(srv.hist);
		net_close();
		curl_easy_cleanup(srv.curl);
		curl_global_cleanup();

		if (srv.req_fd >= 0)
			close(srv.req_fd);
		free(srv.req_log);

		if (srv.share_fd >= 0)
			close(srv.share_fd);
		free(srv.share_log);

		if (srv.pid_fd >= 0)
			close(srv.pid_fd);
		free(srv.pid_file);

		free(srv.ourhost);
		free(srv.rpc_url);
		free(srv.rpc_userpass);
		json_decref(srv.easy_target);

		free(srv.db_host);
		free(srv.db_name);
		free(srv.db_username);
		free(srv.db_password);
		free(srv.db_stmt_pwdb);
		free(srv.db_stmt_sharelog);

		worker_log_expire(time(NULL) + 1);
		htab_free(srv.workers);

		if (srv.mc)
			memcached_free(srv.mc);

		event_base_free(srv.evbase_main);
	}

	return rc;
}

