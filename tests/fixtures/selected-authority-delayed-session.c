#define _GNU_SOURCE

#include <dlfcn.h>
#include <stdlib.h>
#include <sys/types.h>
#include <unistd.h>

pid_t setsid(void) {
    static pid_t (*real_setsid)(void);
    if (real_setsid == NULL) {
        real_setsid = (pid_t(*)(void))dlsym(RTLD_NEXT, "setsid");
    }
    const char *delay = getenv("LEGITIMACY_SESSION_DELAY_MICROSECONDS");
    if (delay != NULL) {
        usleep((useconds_t)strtoul(delay, NULL, 10));
    }
    return real_setsid();
}
