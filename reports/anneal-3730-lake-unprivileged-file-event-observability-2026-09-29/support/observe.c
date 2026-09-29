#define _DARWIN_C_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>

/* Private, best-effort libc boundary witness, not a syscall trace. */
static int log_fd = -2;
static const char *root;

static void init_log(void) {
    if (log_fd != -2) return;
    root = getenv("OBSERVE_ROOT");
    const char *name = getenv("OBSERVE_LOG");
    if (!root || !name || !*root || !*name) { log_fd = -1; return; }
    log_fd = (int)syscall(SYS_open, name, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (log_fd >= 0) {
        const char *prog = getprogname();
        const char *kind = prog && strcmp(prog, "lean") == 0 ? "process-lean" :
                           prog && strcmp(prog, "lake") == 0 ? "process-lake" :
                           "process-other";
        char line[PATH_MAX + 128];
        int n = snprintf(line, sizeof line, "%ld\t%s\t%ld\t0\t%s\n",
                         (long)getpid(), kind, (long)getppid(), root);
        if (n > 0 && n < (int)sizeof line) (void)syscall(SYS_write, log_fd, line, (size_t)n);
    }
}

static int selected(const char *path) {
    init_log();
    if (log_fd < 0 || !path) return 0;
    size_t n = strlen(root);
    return strncmp(path, root, n) == 0 && (path[n] == '/' || path[n] == '\0');
}

static void emit(const char *op, const char *path, long result, long arg) {
    if (!selected(path)) return;
    char buf[PATH_MAX + 128];
    int n = snprintf(buf, sizeof buf, "%ld\t%s\t%ld\t%ld\t%s\n",
                     (long)getpid(), op, result, arg, path);
    if (n > 0 && n < (int)sizeof buf) (void)syscall(SYS_write, log_fd, buf, (size_t)n);
}

static void full_path(const char *path, char out[PATH_MAX]) {
    if (!path) { out[0] = '\0'; return; }
    if (path[0] == '/') { snprintf(out, PATH_MAX, "%s", path); return; }
    if (!getcwd(out, PATH_MAX)) { out[0] = '\0'; return; }
    size_t n = strlen(out);
    snprintf(out + n, PATH_MAX - n, "/%s", path);
}

static int observed_open(const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap; va_start(ap, flags); mode = (mode_t)va_arg(ap, int); va_end(ap);
    }
    int fd = (int)syscall(SYS_open, path, flags, mode);
    char full[PATH_MAX]; full_path(path, full);
    emit("open", full, fd, flags);
    return fd;
}

static int observed_openat(int dirfd, const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap; va_start(ap, flags); mode = (mode_t)va_arg(ap, int); va_end(ap);
    }
    int fd = (int)syscall(SYS_openat, dirfd, path, flags, mode);
    /* A relative path under a non-CWD dirfd cannot be attributed by cwd. */
    if (path && (path[0] == '/' || dirfd == AT_FDCWD)) {
        char full[PATH_MAX]; full_path(path, full);
        emit("openat", full, fd, flags);
    }
    return fd;
}

static ssize_t observed_read(int fd, void *buf, size_t size) {
    ssize_t n = (ssize_t)syscall(SYS_read, fd, buf, size);
    char path[PATH_MAX];
    if (n > 0 && fcntl(fd, F_GETPATH, path) == 0) emit("read", path, n, size);
    return n;
}

static ssize_t observed_write(int fd, const void *buf, size_t size) {
    ssize_t n = (ssize_t)syscall(SYS_write, fd, buf, size);
    char path[PATH_MAX];
    if (n > 0 && fd != log_fd && fcntl(fd, F_GETPATH, path) == 0) emit("write", path, n, size);
    return n;
}

static int observed_rename(const char *oldpath, const char *newpath) {
    int rc = (int)syscall(SYS_rename, oldpath, newpath);
    char full[PATH_MAX]; full_path(oldpath, full); emit("rename-from", full, rc, 0);
    full_path(newpath, full); emit("rename-to", full, rc, 0);
    return rc;
}

static int observed_unlink(const char *path) {
    int rc = (int)syscall(SYS_unlink, path);
    char full[PATH_MAX]; full_path(path, full); emit("unlink", full, rc, 0);
    return rc;
}

struct pair { const void *replacement; const void *replacee; };
__attribute__((used, section("__DATA,__interpose")))
static const struct pair interposers[] = {
    {(const void *)observed_open, (const void *)open},
    {(const void *)observed_openat, (const void *)openat},
    {(const void *)observed_read, (const void *)read},
    {(const void *)observed_write, (const void *)write},
    {(const void *)observed_rename, (const void *)rename},
    {(const void *)observed_unlink, (const void *)unlink},
};
