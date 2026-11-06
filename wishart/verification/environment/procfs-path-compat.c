/* Only supplies the explicitly configured executable path for this process.
   All other readlink operations retain the operating system implementation.
   No access control, kernel checking, or compiler logic is changed. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
    char own_exe[80];
    snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
    const char *configured = getenv("WISHART_LEAN_EXECUTABLE");
    if (configured && strcmp(path, own_exe) == 0) {
        size_t n = strlen(configured);
        if (n > size) n = size;
        memcpy(buf, configured, n);
        return (ssize_t)n;
    }
    static ssize_t (*original)(const char*,char*,size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    if (!original) { errno=ENOSYS; return -1; }
    return original(path,buf,size);
}
