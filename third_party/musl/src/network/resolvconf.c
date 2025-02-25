#include "lookup.h"
#include "stdio_impl.h"
#include <ctype.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <netinet/in.h>
#if OHOS_DNS_PROXY_BY_NETSYS
#include <dlfcn.h>
#endif

int __get_resolv_conf(struct resolvconf *conf, char *search, size_t search_sz)
{
	char line[256];
	unsigned char _buf[256];
	FILE *f, _f;
	int nns = 0;

	conf->ndots = 1;
	conf->timeout = 5;
	conf->attempts = 2;
	if (search) *search = 0;

#if OHOS_DNS_PROXY_BY_NETSYS
	void *handle = dlopen(DNS_SO_PATH, RTLD_LAZY);
	if (handle == NULL) {
		DNS_CONFIG_PRINT("__get_resolv_conf dlopen err %s\n", dlerror());
		goto etc_resolv_conf;
	}

	GetConfig func = dlsym(handle, OHOS_GET_CONFIG_FUNC_NAME);
	if (func == NULL) {
		DNS_CONFIG_PRINT("__get_resolv_conf dlsym err %s\n", dlerror());
		dlclose(handle);
		goto etc_resolv_conf;
	}

	struct resolv_config config = {0};
	int ret = func(0, &config);
	dlclose(handle);
	if (ret < 0) {
		DNS_CONFIG_PRINT("__get_resolv_conf OHOS_GET_CONFIG_FUNC_NAME err %d\n", ret);
		goto etc_resolv_conf;
	}
	int32_t timeout_second = config.timeout_ms / 1000;
#endif

#if OHOS_DNS_PROXY_BY_NETSYS
netsys_conf:
	if (timeout_second > 0) {
		if (timeout_second >= 60) {
			conf->timeout = 60;
		} else {
			conf->timeout = timeout_second;
		}
	}
	if (config.retry_count > 0) {
		if (config.retry_count >= 10) {
			conf->attempts = 10;
		} else {
			conf->attempts = config.retry_count;
		}
	}
	for (int i = 0; i < MAX_SERVER_NUM; ++i) {
		if (config.nameservers[i] == NULL || config.nameservers[i][0] == 0 || nns >= MAXNS) {
			continue;
		}
		if (__lookup_ipliteral(conf->ns + nns, config.nameservers[i], AF_UNSPEC) > 0) {
			nns++;
		}
	}

etc_resolv_conf:
#endif
	f = __fopen_rb_ca("/etc/resolv.conf", &_f, _buf, sizeof _buf);
	if (!f) switch (errno) {
	case ENOENT:
	case ENOTDIR:
	case EACCES:
		goto no_resolv_conf;
	default:
		return -1;
	}

	while (fgets(line, sizeof line, f)) {
		char *p, *z;
		if (!strchr(line, '\n') && !feof(f)) {
			/* Ignore lines that get truncated rather than
			 * potentially misinterpreting them. */
			int c;
			do c = getc(f);
			while (c != '\n' && c != EOF);
			continue;
		}
		if (!strncmp(line, "options", 7) && isspace(line[7])) {
			p = strstr(line, "ndots:");
			if (p && isdigit(p[6])) {
				p += 6;
				unsigned long x = strtoul(p, &z, 10);
				if (z != p) conf->ndots = x > 15 ? 15 : x;
			}
			p = strstr(line, "attempts:");
			if (p && isdigit(p[9])) {
				p += 9;
				unsigned long x = strtoul(p, &z, 10);
				if (z != p) conf->attempts = x > 10 ? 10 : x;
			}
			p = strstr(line, "timeout:");
			if (p && (isdigit(p[8]) || p[8]=='.')) {
				p += 8;
				unsigned long x = strtoul(p, &z, 10);
				if (z != p) conf->timeout = x > 60 ? 60 : x;
			}
			continue;
		}
		if (!strncmp(line, "nameserver", 10) && isspace(line[10])) {
			if (nns >= MAXNS) continue;
			for (p=line+11; isspace(*p); p++);
			for (z=p; *z && !isspace(*z); z++);
			*z=0;
			if (__lookup_ipliteral(conf->ns+nns, p, AF_UNSPEC) > 0)
				nns++;
			continue;
		}

		if (!search) continue;
		if ((strncmp(line, "domain", 6) && strncmp(line, "search", 6))
		    || !isspace(line[6]))
			continue;
		for (p=line+7; isspace(*p); p++);
		size_t l = strlen(p);
		/* This can never happen anyway with chosen buffer sizes. */
		if (l >= search_sz) continue;
		memcpy(search, p, l+1);
	}

	__fclose_ca(f);

no_resolv_conf:
	if (!nns) {
		__lookup_ipliteral(conf->ns, "127.0.0.1", AF_UNSPEC);
		nns = 1;
	}

	conf->nns = nns;

	return 0;
}
