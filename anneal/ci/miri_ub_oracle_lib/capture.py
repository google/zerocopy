# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Capture-mode hardening: UID checks, capability dropping, namespaces,
and file export."""

from __future__ import annotations

import ctypes
import errno
import os
from pathlib import Path
import platform
import re
import stat
import struct

from .common import (
    CAPTURE_MAX_DISK_BYTES, CAPTURE_MAX_EXPORT_BYTES, CAPTURE_MAX_INODES, OracleError,
)
from .linux_abi import (
    _CLONE_NEWNET, _CLONE_NEWNS, _CLONE_NEWPID, _CLONE_NEWUSER, _MS_BIND, _MS_NODEV, _MS_NOEXEC,
    _MS_NOSUID, _MS_PRIVATE, _MS_RDONLY, _MS_REC, _MS_REMOUNT, _PR_GET_DUMPABLE, _PR_SET_DUMPABLE,
    _ST_TO_MS_FLAGS,
)


def _harden_parent_process() -> None:
    """Mark the parent harness non-dumpable so children cannot read `/proc/$PPID/environ`.

    Linux sets `/proc/<pid>/environ` (and `mem`/`maps`/`fd`) ownership to
    `root:root` mode `0400` when `PR_SET_DUMPABLE` is `0`, preventing same-UID
    subprocesses from reading stripped GitHub Actions tokens out of the parent.
    """
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(_PR_SET_DUMPABLE, 0, 0, 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_DUMPABLE, 0) failed: errno={err}")
    if libc.prctl(_PR_GET_DUMPABLE, 0, 0, 0, 0) != 0:
        raise OracleError(
            "parent process remained dumpable after prctl(PR_SET_DUMPABLE, 0)"
        )


def _assert_capture_non_root_uid() -> None:
    """Fail closed if launched as UID 0 (`root`).

    Linux `copy_process()` exempts `INIT_USER` (UID 0) and callers holding
    `CAP_SYS_RESOURCE`/`CAP_SYS_ADMIN` from `RLIMIT_NPROC`. Refuse to run
    `capture` confinement as UID 0 so the kernel task ceiling is always
    enforced.
    """
    if os.getuid() == 0 or os.geteuid() == 0:
        raise OracleError(
            "capture confinement refuses to run as UID 0 (root) because "
            "Linux exempts root/INIT_USER from RLIMIT_NPROC; re-run as an "
            "unprivileged user"
        )


def _drop_all_capabilities(
    libc: ctypes.CDLL, *, drop_bounding: bool = True
) -> None:
    """Drop Linux capabilities before `seccomp` and `execve`.

    Always clears ambient, effective, permitted, and inheritable capability
    sets. When `drop_bounding=True` (used in `capture` mode inside its private
    user namespace), also drops the capability bounding set via
    `PR_CAPBSET_DROP` and verifies via `PR_CAPBSET_READ` that any `EPERM`
    capability is already absent (failing closed otherwise). In `eval` mode
    (`drop_bounding=False`), `execve` stays in the seccomp allowlist so the
    `--_confined-exec` re-exec trampoline can launch `anneal-mir-eval` after
    installing the filter (while `execveat` and `clone`/`fork`/`vfork` are
    denied); setting `PR_SET_NO_NEW_PRIVS` before seccomp—together with
    clearing ambient, effective, permitted, and inheritable
    capabilities—prevents `CapBnd` from elevating privileges across any
    `execve`.
    """
    pr_capbset_read = 23
    pr_capbset_drop = 24
    pr_cap_ambient = 47
    pr_cap_ambient_clear_all = 4
    if drop_bounding:
        # Clear the bounding set while CAP_SETPCAP is held in the userns.
        for cap_num in range(64):
            rc = int(libc.prctl(pr_capbset_drop, cap_num, 0, 0, 0))
            if rc == 0:
                continue
            err = ctypes.get_errno()
            if err == errno.EINVAL:
                break
            if err == errno.EPERM:
                # Caller lacks CAP_SETPCAP; only accept EPERM if
                # PR_CAPBSET_READ confirms the cap is already absent.
                present = int(libc.prctl(pr_capbset_read, cap_num, 0, 0, 0))
                if present == 0:
                    continue
                if present < 0 and ctypes.get_errno() == errno.EINVAL:
                    break
                raise OracleError(
                    f"prctl(PR_CAPBSET_DROP, {cap_num}) failed with EPERM "
                    f"while capability remains in bounding set "
                    f"(PR_CAPBSET_READ={present})"
                )
            raise OracleError(
                f"prctl(PR_CAPBSET_DROP, {cap_num}) failed: errno={err}"
            )
    # Clear ambient capabilities (ignore EINVAL if kernel lacks ambient caps).
    if int(libc.prctl(pr_cap_ambient, pr_cap_ambient_clear_all, 0, 0, 0)) != 0:
        err = ctypes.get_errno()
        if err != errno.EINVAL:
            raise OracleError(
                f"prctl(PR_CAP_AMBIENT_CLEAR_ALL) failed: errno={err}"
            )
    machine = platform.machine().lower()
    if machine in ("x86_64", "amd64"):
        sys_capset = 126
    elif machine in ("aarch64", "arm64"):
        sys_capset = 91
    else:
        raise OracleError(f"unsupported architecture for capset: {machine!r}")
    # struct __user_cap_header_struct { __u32 version; int pid; }
    # struct __user_cap_data_struct[2] { effective, permitted, inheritable }
    cap_header = ctypes.create_string_buffer(struct.pack("<Ii", 0x20080522, 0))
    cap_data = ctypes.create_string_buffer(24)
    if int(libc.syscall(sys_capset, cap_header, cap_data)) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"capset(clear all) failed: errno={err}")


def _enter_capture_namespaces(
    work_dir: Path | None,
    *,
    read_only_bind_paths: list[Path] = (),  # type: ignore[assignment]
    max_disk_bytes: int = CAPTURE_MAX_DISK_BYTES,
    max_inodes: int = CAPTURE_MAX_INODES,
) -> None:
    """Isolate the capture supervisor in private user, PID, mount, and net namespaces.

    Unshares `CLONE_NEWUSER | CLONE_NEWPID | CLONE_NEWNS | CLONE_NEWNET` with
    a 1:1 UID/GID mapping so:
    - The forked capture child runs as PID 1 in a private PID namespace: it
      cannot address or signal host/runner processes, and the kernel atomically
      kills and reaps all descendants when PID 1 exits.
    - The child receives a dedicated `ucounts` task budget (`RLIMIT_NPROC`)
      that cannot be escaped via nested namespaces (`clone`/`clone3`/`unshare`/
      `setns` namespace creation is denied by seccomp).
    - Every `read_only_bind_paths` entry (`src_dir`, `sysroot`, `target_exe`)
      is bind-mounted read-only (`MS_BIND | MS_REMOUNT | MS_RDONLY`) inside the
      private mount namespace so even non-Landlock metadata calls (`fchmod`)
      return `EROFS` on read-only inputs and toolchains.
    - If `work_dir` is provided, a private size- and inode-bounded `tmpfs`
      (`nosuid,nodev,noexec`) is mounted on `work_dir` so sequential file
      creation cannot fill the shared host filesystem.
    Fails closed with `OracleError` if namespaces, read-only bind-mounts, or
    the bounded `tmpfs` mount fail.
    """
    _assert_capture_non_root_uid()
    libc = ctypes.CDLL(None, use_errno=True)
    uid = os.getuid()
    gid = os.getgid()
    flags = _CLONE_NEWUSER | _CLONE_NEWPID | _CLONE_NEWNS | _CLONE_NEWNET
    if int(libc.unshare(flags)) != 0:
        err = ctypes.get_errno()
        raise OracleError(
            "capture confinement requires unprivileged Linux user/PID/mount/net "
            f"namespaces (unshare failed: errno={err})"
        )
    try:
        try:
            Path("/proc/self/setgroups").write_text("deny", encoding="ascii")
        except FileNotFoundError:
            pass
        Path("/proc/self/uid_map").write_text(f"{uid} {uid} 1\n", encoding="ascii")
        Path("/proc/self/gid_map").write_text(f"{gid} {gid} 1\n", encoding="ascii")
    except OSError as exc:
        raise OracleError(f"failed configuring capture user namespace maps: {exc}") from exc

    libc.mount.argtypes = [
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_ulong,
        ctypes.c_char_p,
    ]
    libc.mount.restype = ctypes.c_int
    # Sever shared mount propagation from the host namespace before creating
    # bind-mounts or tmpfs mounts so SIGKILL cannot leak host-visible mounts.
    if int(libc.mount(None, b"/", None, _MS_REC | _MS_PRIVATE, None)) != 0:
        err = ctypes.get_errno()
        raise OracleError(
            f"failed marking capture mount namespace private: errno={err}"
        )

    def _remount_ro(target_p: Path, *, bind_first: bool) -> None:
        stv = os.statvfs(target_p)
        if stv.f_flag & getattr(os, "ST_RDONLY", 1):
            return
        preserved = 0
        for st_bit, ms_bit in _ST_TO_MS_FLAGS:
            if stv.f_flag & st_bit:
                preserved |= ms_bit
        p_bytes = os.fsencode(target_p)
        if bind_first:
            bind_flags = _MS_BIND | (_MS_REC if target_p.is_dir() else 0)
            if int(libc.mount(p_bytes, p_bytes, None, bind_flags, None)) != 0:
                err = ctypes.get_errno()
                raise OracleError(
                    f"failed read-only bind-mount on '{target_p}': errno={err}"
                )
        remount_flags = _MS_BIND | _MS_REMOUNT | _MS_RDONLY | preserved
        if int(libc.mount(None, p_bytes, None, remount_flags, None)) != 0:
            err = ctypes.get_errno()
            raise OracleError(
                f"failed read-only remount on '{target_p}': errno={err}"
            )

    def _unescape_mountinfo_path(raw_mp: str) -> str:
        return re.sub(
            r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), raw_mp
        )

    work_resolved = work_dir.resolve() if work_dir is not None else None
    seen_ro: set[Path] = set()
    for raw_p in read_only_bind_paths:
        if not raw_p.exists():
            continue
        p = raw_p.resolve()
        if p in seen_ro or p == Path("/"):
            continue
        if work_resolved is not None and (
            work_resolved == p or work_resolved.is_relative_to(p)
        ):
            raise OracleError(
                f"capture work_dir '{work_resolved}' must not reside under "
                f"read-only path '{p}'"
            )
        seen_ro.add(p)
        _remount_ro(p, bind_first=True)
        if p.is_dir():
            # `MS_REMOUNT | MS_RDONLY` applies per mountpoint; also remount
            # any submounts beneath `p/` so `fchmod` fails with `EROFS` across
            # nested mounts inside readable trees.
            prefix = str(p).rstrip("/") + "/"
            for line in Path("/proc/self/mountinfo").read_text(
                encoding="utf-8", errors="replace"
            ).splitlines():
                parts = line.split()
                if len(parts) < 5:
                    continue
                mp_str = _unescape_mountinfo_path(parts[4])
                if not mp_str.startswith(prefix):
                    continue
                mp_path = Path(mp_str)
                if work_resolved is not None and (
                    work_resolved == mp_path
                    or work_resolved.is_relative_to(mp_path)
                ):
                    continue
                if mp_path.exists():
                    _remount_ro(mp_path, bind_first=False)

    if work_dir is not None:
        if max_disk_bytes <= 0 or max_inodes <= 0:
            raise OracleError(
                f"invalid capture tmpfs quota: bytes={max_disk_bytes}, inodes={max_inodes}"
            )
        mount_opts = f"size={max_disk_bytes},nr_inodes={max_inodes},mode=0700".encode(
            "ascii"
        )
        rc = int(
            libc.mount(
                b"tmpfs",
                os.fsencode(work_dir),
                b"tmpfs",
                _MS_NOSUID | _MS_NODEV | _MS_NOEXEC,
                mount_opts,
            )
        )
        if rc != 0:
            err = ctypes.get_errno()
            raise OracleError(
                f"failed mounting bounded tmpfs on '{work_dir}': errno={err}"
            )
        (work_dir / "tmp").mkdir(mode=0o700, exist_ok=True)


def _export_capture_file(src_file: Path, dst_file: Path) -> None:
    """Copy one bounded regular non-symlink file from capture tmpfs `src_file` to `dst_file`.

    Silently returns if `src_file` or its parent directory was not produced
    (e.g. when capture exited with `unsupported` or `compiler_failed`). Ignores
    sibling files/directories such as sharded `Captured/` output so multi-shard
    captures (>20 bodies) export `capture.json` cleanly while rejecting symlinks,
    non-regular entries, or oversized payloads fail-closed.
    """
    o_nofollow = getattr(os, "O_NOFOLLOW", 0)
    o_directory = getattr(os, "O_DIRECTORY", 0)
    o_nonblock = getattr(os, "O_NONBLOCK", 0)
    try:
        src_dir_fd = os.open(
            src_file.parent, os.O_RDONLY | o_directory | o_nofollow
        )
    except FileNotFoundError:
        return
    try:
        try:
            in_fd = os.open(
                src_file.name,
                os.O_RDONLY | o_nofollow | o_nonblock,
                dir_fd=src_dir_fd,
            )
        except FileNotFoundError:
            return
        try:
            in_st = os.fstat(in_fd)
            if not stat.S_ISREG(in_st.st_mode):
                raise OracleError(
                    f"capture output entry '{src_file.name}' is not a regular file"
                )
            dst_file.parent.mkdir(parents=True, exist_ok=True)
            dst_dir_fd = os.open(
                dst_file.parent, os.O_RDONLY | o_directory | o_nofollow
            )
            try:
                out_fd = os.open(
                    dst_file.name,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | o_nofollow,
                    0o600,
                    dir_fd=dst_dir_fd,
                )
                try:
                    total_bytes = 0
                    while True:
                        chunk = os.read(in_fd, 65536)
                        if not chunk:
                            break
                        total_bytes += len(chunk)
                        if total_bytes > CAPTURE_MAX_EXPORT_BYTES:
                            raise OracleError(
                                "capture exported output exceeds "
                                f"{CAPTURE_MAX_EXPORT_BYTES} bytes"
                            )
                        view = memoryview(chunk)
                        while view:
                            written = os.write(out_fd, view)
                            view = view[written:]
                finally:
                    os.close(out_fd)
            finally:
                os.close(dst_dir_fd)
        finally:
            os.close(in_fd)
    finally:
        os.close(src_dir_fd)
