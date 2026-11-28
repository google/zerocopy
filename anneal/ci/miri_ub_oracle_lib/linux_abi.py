# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Linux syscall, prctl, Landlock, namespace, mount, and seccomp constants
and allowlist tables used by confinement."""

from __future__ import annotations

import os


_PR_GET_DUMPABLE = 3
_PR_SET_DUMPABLE = 4
_PR_SET_NO_NEW_PRIVS = 38
_PR_SET_SECCOMP = 22
_SECCOMP_MODE_FILTER = 2
_BPF_LD_W_ABS = 0x20
_BPF_JMP_JEQ_K = 0x15
_BPF_JMP_JSET_K = 0x45
_BPF_RET_K = 0x06
_SECCOMP_RET_KILL_PROCESS = 0x80000000
_SECCOMP_RET_ERRNO = 0x00050000
_SECCOMP_RET_ALLOW = 0x7FFF0000
_X32_SYSCALL_BIT = 0x40000000
# Open flags requesting write access, creation, truncation, append, or
# anonymous temporary files (`__O_TMPFILE = 0x400000`, omitting `O_DIRECTORY`
# so read-only `O_RDONLY | O_DIRECTORY` opens remain permitted on both x86_64
# and aarch64).
_OPEN_WRITE_FLAGS = (
    0x000001  # O_WRONLY
    | 0x000002  # O_RDWR
    | 0x000040  # O_CREAT
    | 0x000200  # O_TRUNC
    | 0x000400  # O_APPEND
    | 0x400000  # __O_TMPFILE (without O_DIRECTORY)
)
_CONFINED_EXEC_FLAG = "--_confined-exec"
CONFINEMENT_MODES = frozenset({"eval", "capture"})

# Linux Landlock LSM syscall numbers (identical on x86_64 and aarch64) and
# ABI v1..v5 filesystem access bitmasks.
_SYS_LANDLOCK_CREATE_RULESET = 444
_SYS_LANDLOCK_ADD_RULE = 445
_SYS_LANDLOCK_RESTRICT_SELF = 446
_LANDLOCK_CREATE_RULESET_VERSION = 1
_LANDLOCK_RULE_PATH_BENEATH = 1
_LANDLOCK_ACCESS_FS_EXECUTE = 1 << 0
_LANDLOCK_ACCESS_FS_WRITE_FILE = 1 << 1
_LANDLOCK_ACCESS_FS_READ_FILE = 1 << 2
_LANDLOCK_ACCESS_FS_READ_DIR = 1 << 3
_LANDLOCK_ACCESS_FS_REMOVE_DIR = 1 << 4
_LANDLOCK_ACCESS_FS_REMOVE_FILE = 1 << 5
_LANDLOCK_ACCESS_FS_MAKE_DIR = 1 << 7
_LANDLOCK_ACCESS_FS_MAKE_REG = 1 << 8
_LANDLOCK_ACCESS_FS_ABI1_ALL = (1 << 13) - 1
_LANDLOCK_ACCESS_FS_REFER = 1 << 13
_LANDLOCK_ACCESS_FS_TRUNCATE = 1 << 14
_LANDLOCK_ACCESS_FS_IOCTL_DEV = 1 << 15
_LANDLOCK_DIR_RO_EXEC = (
    _LANDLOCK_ACCESS_FS_EXECUTE
    | _LANDLOCK_ACCESS_FS_READ_FILE
    | _LANDLOCK_ACCESS_FS_READ_DIR
)
_LANDLOCK_DIR_RO = (
    _LANDLOCK_ACCESS_FS_READ_FILE | _LANDLOCK_ACCESS_FS_READ_DIR
)
_LANDLOCK_DIR_RW_BASE = (
    _LANDLOCK_ACCESS_FS_READ_FILE
    | _LANDLOCK_ACCESS_FS_READ_DIR
    | _LANDLOCK_ACCESS_FS_WRITE_FILE
    | _LANDLOCK_ACCESS_FS_REMOVE_DIR
    | _LANDLOCK_ACCESS_FS_REMOVE_FILE
    | _LANDLOCK_ACCESS_FS_MAKE_REG
    | _LANDLOCK_ACCESS_FS_MAKE_DIR
)
_LANDLOCK_FILE_RO_EXEC = (
    _LANDLOCK_ACCESS_FS_EXECUTE | _LANDLOCK_ACCESS_FS_READ_FILE
)
_LANDLOCK_FILE_RO = _LANDLOCK_ACCESS_FS_READ_FILE
_LANDLOCK_FILE_RW_BASE = (
    _LANDLOCK_ACCESS_FS_READ_FILE | _LANDLOCK_ACCESS_FS_WRITE_FILE
)
_CLONE_NEWNS = 0x00020000
_CLONE_NEWUSER = 0x10000000
_CLONE_NEWPID = 0x20000000
_CLONE_NEWNET = 0x40000000
# All Linux namespace-creation `clone(2)` flags (identical on x86_64/aarch64):
# CLONE_NEWTIME | NEWNS | NEWCGROUP | NEWUTS | NEWIPC | NEWUSER | NEWPID |
# NEWNET.
_CLONE_FORBIDDEN_NS_FLAGS = 0x7E020080
_MS_RDONLY = 1
_MS_NOSUID = 2
_MS_NODEV = 4
_MS_NOEXEC = 8
_MS_REMOUNT = 32
_MS_NOATIME = 1024
_MS_NODIRATIME = 2048
_MS_BIND = 4096
_MS_REC = 16384
_MS_PRIVATE = 1 << 18
_MS_RELATIME = 1 << 21
_MNT_DETACH = 2
_ST_TO_MS_FLAGS = (
    (getattr(os, "ST_NOSUID", 0x2), _MS_NOSUID),
    (getattr(os, "ST_NODEV", 0x4), _MS_NODEV),
    (getattr(os, "ST_NOEXEC", 0x8), _MS_NOEXEC),
    (getattr(os, "ST_NOATIME", 0x400), _MS_NOATIME),
    (getattr(os, "ST_NODIRATIME", 0x800), _MS_NODIRATIME),
    (getattr(os, "ST_RELATIME", 0x1000), _MS_RELATIME),
)
_LANDLOCK_SYSTEM_RO_EXEC_DIRS = (
    "/usr",
    "/lib",
    "/lib64",
    "/nix/store",
    "/opt/anneal-nix/runtime-libs",
)
_LANDLOCK_SYSTEM_RO_PATHS = (
    "/etc/ld.so.cache",
    "/etc/ld.so.conf",
    "/etc/ld.so.conf.d",
    "/dev/null",
    "/dev/zero",
    "/dev/urandom",
)

# Strict default-deny seccomp allowlists for both `eval` and `capture` modes:
# every syscall outside the audited allowlist (including `socket`/`socketpair`,
# `eventfd*`, `epoll_*`, `inotify_*`, `timerfd_*`, `signalfd_*`, `memfd_*`,
# `io_uring_*`, SysV/POSIX IPC, `openat2`, `setsid`/`setpgid`, `unshare`/
# `setns`, `kill`, `ptrace`, `process_vm_*`, `pidfd_*`, `mount`/`umount2`)
# returns `EPERM`. `prlimit64` is admitted only for `pid == 0` (self) and
# `fcntl` only for `{F_DUPFD, F_GETFD, F_SETFD, F_GETFL, F_DUPFD_CLOEXEC}` plus
# `F_SETFL` with `O_ASYNC` clear (zero upper 32 bits). In `eval` mode,
# `open`/`openat` require `_OPEN_WRITE_FLAGS` clear and `ioctl` admits only
# `FIOCLEX`; all task/thread/pipe creation is denied. In `capture` mode,
# `clone3` returns `ENOSYS` so glibc falls back to `clone`, where any namespace
# flag in `_CLONE_FORBIDDEN_NS_FLAGS` (or non-zero upper 32 bits) returns
# `EPERM`; `ioctl` admits only `{FIOCLEX, FIONCLEX, FIONBIO}` and `prctl`
# admits only `{PR_SET_NAME, PR_GET_NAME}` (zero upper 32 bits).
_IOCTL_FIOCLEX = 0x5451  # identical on Linux x86_64 and aarch64
_IOCTL_CAPTURE_ALLOWED = (
    0x5451,  # FIOCLEX
    0x5450,  # FIONCLEX
    0x5421,  # FIONBIO
)
_PRCTL_CAPTURE_ALLOWED = (
    15,  # PR_SET_NAME
    16,  # PR_GET_NAME
)
_FCNTL_SAFE_CMDS = (
    0,     # F_DUPFD
    1,     # F_GETFD
    2,     # F_SETFD
    3,     # F_GETFL
    1030,  # F_DUPFD_CLOEXEC
)
_FCNTL_F_SETFL = 4
_FCNTL_O_ASYNC = 0x2000  # FASYNC on Linux x86_64 and aarch64
_X86_64_SECCOMP_SPEC: dict[str, object] = {
    "audit_arch": 0xC000003E,  # AUDIT_ARCH_X86_64
    "reject_x32": True,
    "open_nr": 2,  # open(pathname, flags, mode) -> args[1] at offset 24
    "openat_nr": 257,  # openat(dirfd, pathname, flags, mode) -> args[2] at 32
    "prlimit64_nr": 302,  # prlimit64(pid, resource, new, old) -> args[0] at 16
    "ioctl_nr": 16,  # ioctl(fd, request, ...) -> args[1] at offset 24
    "fcntl_nr": 72,  # fcntl(fd, cmd, arg) -> args[1] at 24, args[2] at 32
    "clone_nr": 56,  # clone(flags, ...) -> args[0] at offset 16
    "clone3_nr": 435,  # clone3(...) -> ENOSYS (glibc falls back to clone)
    "prctl_nr": 157,  # prctl(option, ...) -> args[0] at offset 16
    "eval_allow_nrs": (
        0,    # read
        1,    # write
        3,    # close
        4,    # stat
        5,    # fstat
        6,    # lstat
        7,    # poll
        8,    # lseek
        9,    # mmap
        10,   # mprotect
        11,   # munmap
        12,   # brk
        13,   # rt_sigaction
        14,   # rt_sigprocmask
        15,   # rt_sigreturn
        17,   # pread64
        20,   # writev
        21,   # access
        24,   # sched_yield
        25,   # mremap
        28,   # madvise
        35,   # nanosleep
        39,   # getpid
        59,   # execve
        60,   # exit
        63,   # uname
        79,   # getcwd
        89,   # readlink
        96,   # gettimeofday
        97,   # getrlimit
        99,   # sysinfo
        102,  # getuid
        104,  # getgid
        107,  # geteuid
        108,  # getegid
        110,  # getppid
        131,  # sigaltstack
        137,  # statfs
        138,  # fstatfs
        158,  # arch_prctl
        186,  # gettid
        202,  # futex
        204,  # sched_getaffinity
        217,  # getdents64
        218,  # set_tid_address
        228,  # clock_gettime
        230,  # clock_nanosleep
        231,  # exit_group
        262,  # newfstatat
        267,  # readlinkat
        269,  # faccessat
        271,  # ppoll
        273,  # set_robust_list
        318,  # getrandom
        332,  # statx
        334,  # rseq
        439,  # faccessat2
    ),
    "capture_extra_allow_nrs": (
        2,    # open (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        18,   # pwrite64
        19,   # readv
        22,   # pipe (bounded by RLIMIT_NOFILE)
        32,   # dup
        33,   # dup2
        61,   # wait4
        76,   # truncate (mediated by Landlock ABI >= 3)
        77,   # ftruncate (mediated by Landlock ABI >= 3)
        80,   # chdir
        81,   # fchdir
        82,   # rename
        83,   # mkdir
        84,   # rmdir
        87,   # unlink
        91,   # fchmod
        95,   # umask
        200,  # tkill (confined to isolated CLONE_NEWPID namespace)
        229,  # clock_getres
        234,  # tgkill (confined to isolated CLONE_NEWPID namespace)
        247,  # waitid
        257,  # openat (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        258,  # mkdirat
        263,  # unlinkat
        264,  # renameat
        292,  # dup3
        293,  # pipe2 (bounded by RLIMIT_NOFILE)
        295,  # preadv
        296,  # pwritev
        316,  # renameat2
        326,  # copy_file_range
    ),
}

_AARCH64_SECCOMP_SPEC: dict[str, object] = {
    "audit_arch": 0xC00000B7,  # AUDIT_ARCH_AARCH64
    "reject_x32": False,
    "open_nr": None,
    "openat_nr": 56,  # openat(dirfd, pathname, flags, mode) -> args[2] at 32
    "prlimit64_nr": 261,  # prlimit64(pid, resource, new, old) -> args[0] at 16
    "ioctl_nr": 29,  # ioctl(fd, request, ...) -> args[1] at offset 24
    "fcntl_nr": 25,  # fcntl(fd, cmd, arg) -> args[1] at 24, args[2] at 32
    "clone_nr": 220,  # clone(flags, ...) -> args[0] at offset 16
    "clone3_nr": 435,  # clone3(...) -> ENOSYS (glibc falls back to clone)
    "prctl_nr": 167,  # prctl(option, ...) -> args[0] at offset 16
    "eval_allow_nrs": (
        17,   # getcwd
        43,   # statfs
        44,   # fstatfs
        48,   # faccessat
        57,   # close
        61,   # getdents64
        62,   # lseek
        63,   # read
        64,   # write
        66,   # writev
        67,   # pread64
        73,   # ppoll
        78,   # readlinkat
        79,   # newfstatat
        80,   # fstat
        93,   # exit
        94,   # exit_group
        96,   # set_tid_address
        98,   # futex
        99,   # set_robust_list
        101,  # nanosleep
        113,  # clock_gettime
        115,  # clock_nanosleep
        123,  # sched_getaffinity
        124,  # sched_yield
        132,  # sigaltstack
        134,  # rt_sigaction
        135,  # rt_sigprocmask
        139,  # rt_sigreturn
        160,  # uname
        163,  # getrlimit
        169,  # gettimeofday
        172,  # getpid
        173,  # getppid
        174,  # getuid
        175,  # geteuid
        176,  # getgid
        177,  # getegid
        178,  # gettid
        179,  # sysinfo
        214,  # brk
        215,  # munmap
        216,  # mremap
        221,  # execve
        222,  # mmap
        226,  # mprotect
        233,  # madvise
        278,  # getrandom
        291,  # statx
        293,  # rseq
        439,  # faccessat2
    ),
    "capture_extra_allow_nrs": (
        23,   # dup
        24,   # dup3
        34,   # mkdirat
        35,   # unlinkat
        38,   # renameat
        45,   # truncate (mediated by Landlock ABI >= 3)
        46,   # ftruncate (mediated by Landlock ABI >= 3)
        49,   # chdir
        50,   # fchdir
        52,   # fchmod (RO bind-mounts block fchmod on sysroot/src with EROFS)
        56,   # openat (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        59,   # pipe2 (bounded by RLIMIT_NOFILE)
        65,   # readv
        68,   # pwrite64
        69,   # preadv
        70,   # pwritev
        95,   # waitid
        114,  # clock_getres
        130,  # tkill (confined to isolated CLONE_NEWPID namespace)
        131,  # tgkill (confined to isolated CLONE_NEWPID namespace)
        166,  # umask
        260,  # wait4
        276,  # renameat2
        285,  # copy_file_range
    ),
}

_SECCOMP_ARCH_TABLE: dict[str, dict[str, object]] = {
    "x86_64": _X86_64_SECCOMP_SPEC,
    "amd64": _X86_64_SECCOMP_SPEC,
    "aarch64": _AARCH64_SECCOMP_SPEC,
    "arm64": _AARCH64_SECCOMP_SPEC,
}
