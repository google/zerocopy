# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Construction and installation of the confinement seccomp filter."""

from __future__ import annotations

import ctypes
import errno
import platform
import struct

from .common import OracleError
from .linux_abi import (
    CONFINEMENT_MODES, _BPF_JMP_JEQ_K, _BPF_JMP_JSET_K, _BPF_LD_W_ABS, _BPF_RET_K,
    _CLONE_FORBIDDEN_NS_FLAGS, _FCNTL_F_SETFL, _FCNTL_O_ASYNC, _FCNTL_SAFE_CMDS,
    _IOCTL_CAPTURE_ALLOWED, _IOCTL_FIOCLEX, _OPEN_WRITE_FLAGS, _PRCTL_CAPTURE_ALLOWED,
    _PR_SET_NO_NEW_PRIVS, _PR_SET_SECCOMP, _SECCOMP_ARCH_TABLE, _SECCOMP_MODE_FILTER,
    _SECCOMP_RET_ALLOW, _SECCOMP_RET_ERRNO, _SECCOMP_RET_KILL_PROCESS, _X32_SYSCALL_BIT,
)


class _SockFprog(ctypes.Structure):
    _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.c_void_p)]


def _build_confinement_seccomp_bpf(
    machine: str, *, confinement: str = "eval"
) -> bytes:
    """Build a default-deny Linux seccomp-BPF filter for `eval` or `capture` confinement.

    Always kills non-native or x32 ABI syscalls and defaults every unlisted
    syscall to `EPERM`. Both modes share the base read/memory/signal/stat
    allowlist, `prlimit64` restricted to `pid == 0` (self), and `fcntl`
    restricted to safe descriptor/flag operations (denying `F_SETOWN`,
    `F_SETSIG`, `O_ASYNC`, pipe resizing, leases, locks, and seals).

    `eval` restricts `open`/`openat` to read-only flags and `ioctl` to
    `FIOCLEX`, denying all process/thread creation, pipes, and filesystem
    mutations. `capture` adds the audited subset required by
    `anneal-rustc-capture` and `rustc` inside its isolated `CLONE_NEWUSER |
    CLONE_NEWPID | CLONE_NEWNS | CLONE_NEWNET` sandbox: `clone3` returns
    `ENOSYS` (falling back to `clone`), `clone` denies every namespace flag in
    `_CLONE_FORBIDDEN_NS_FLAGS` and non-zero upper 32 bits, `ioctl` admits only
    `{FIOCLEX, FIONCLEX, FIONBIO}`, and `prctl` admits only `{PR_SET_NAME,
    PR_GET_NAME}`. Sockets, eventfds, memfds, io_uring, SysV/POSIX IPC,
    `setsid`/`setpgid`, `unshare`/`setns`, `kill`, `ptrace`, `process_vm_*`,
    and `mount` are denied by default.
    """
    if confinement not in CONFINEMENT_MODES:
        raise OracleError(f"unsupported confinement mode: {confinement!r}")
    spec = _SECCOMP_ARCH_TABLE.get(machine.lower())
    if spec is None:
        raise OracleError(
            f"unsupported architecture for Linux seccomp confinement: {machine!r}"
        )
    ir: list[tuple[object, ...]] = [
        ("op", _BPF_LD_W_ABS, 0, 0, 4),  # load seccomp_data.arch
        ("op", _BPF_JMP_JEQ_K, 0, "kill", spec["audit_arch"]),
        ("op", _BPF_LD_W_ABS, 0, 0, 0),  # load seccomp_data.nr
    ]
    if spec["reject_x32"]:
        ir.append(("op", _BPF_JMP_JSET_K, "kill", 0, _X32_SYSCALL_BIT))
    for nr in spec["eval_allow_nrs"]:  # type: ignore[union-attr]
        ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, nr))
    if confinement == "capture":
        for nr in spec["capture_extra_allow_nrs"]:  # type: ignore[union-attr]
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, nr))
        ir.append(("op", _BPF_JMP_JEQ_K, "enosys", 0, spec["clone3_nr"]))
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_clone", spec["clone_nr"]),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (flags)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (flags)
            ("op", _BPF_JMP_JSET_K, "eperm", "allow", _CLONE_FORBIDDEN_NS_FLAGS),
            ("label", "after_clone"),
        ])
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_prctl", spec["prctl_nr"]),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (option)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (option)
        ])
        for opt_val in _PRCTL_CAPTURE_ALLOWED:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, opt_val))
        ir.extend([
            ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
            ("label", "after_prctl"),
        ])
    else:
        openat_nr = spec["openat_nr"]
        if openat_nr is not None:
            ir.extend([
                ("op", _BPF_JMP_JEQ_K, 0, "after_openat", openat_nr),
                ("op", _BPF_LD_W_ABS, 0, 0, 32),  # args[2] low 32 bits (flags)
                ("op", _BPF_JMP_JSET_K, "eperm", "allow", _OPEN_WRITE_FLAGS),
                ("label", "after_openat"),
            ])
        open_nr = spec["open_nr"]
        if open_nr is not None:
            ir.extend([
                ("op", _BPF_JMP_JEQ_K, 0, "after_open", open_nr),
                ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (flags)
                ("op", _BPF_JMP_JSET_K, "eperm", "allow", _OPEN_WRITE_FLAGS),
                ("label", "after_open"),
            ])
    prlimit64_nr = spec["prlimit64_nr"]
    if prlimit64_nr is not None:
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_prlimit64", prlimit64_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (pid)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (pid)
            ("op", _BPF_JMP_JEQ_K, "allow", "eperm", 0),
            ("label", "after_prlimit64"),
        ])
    ioctl_nr = spec["ioctl_nr"]
    if ioctl_nr is not None:
        allowed_ioctls = (
            _IOCTL_CAPTURE_ALLOWED if confinement == "capture" else (_IOCTL_FIOCLEX,)
        )
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_ioctl", ioctl_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 28),  # args[1] high 32 bits (req)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (req)
        ])
        for req_val in allowed_ioctls:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, req_val))
        ir.extend([
            ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
            ("label", "after_ioctl"),
        ])
    fcntl_nr = spec["fcntl_nr"]
    if fcntl_nr is not None:
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_fcntl", fcntl_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 28),  # args[1] high 32 bits (cmd)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (cmd)
        ])
        for cmd_val in _FCNTL_SAFE_CMDS:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, cmd_val))
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", _FCNTL_F_SETFL),
            ("op", _BPF_LD_W_ABS, 0, 0, 36),  # args[2] high 32 bits (flags)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 32),  # args[2] low 32 bits (flags)
            ("op", _BPF_JMP_JSET_K, "eperm", "allow", _FCNTL_O_ASYNC),
            ("label", "after_fcntl"),
        ])
    ir.extend([
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
        ("label", "kill"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_KILL_PROCESS),
        ("label", "eperm"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
        ("label", "enosys"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.ENOSYS),
        ("label", "allow"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ALLOW),
    ])
    labels: dict[str, int] = {}
    ops: list[tuple[int, object, object, int]] = []
    for item in ir:
        if item[0] == "label":
            labels[str(item[1])] = len(ops)
        else:
            ops.append((int(item[1]), item[2], item[3], int(item[4])))
    out = bytearray()
    for idx, (code, jt_ref, jf_ref, k) in enumerate(ops):
        jt = (labels[jt_ref] - idx - 1) if isinstance(jt_ref, str) else int(jt_ref)
        jf = (labels[jf_ref] - idx - 1) if isinstance(jf_ref, str) else int(jf_ref)
        if not (0 <= jt <= 255 and 0 <= jf <= 255):
            raise OracleError(f"invalid BPF jump offset at {idx}: jt={jt}, jf={jf}")
        out.extend(struct.pack("HBBI", code, jt, jf, k))
    return bytes(out)


def _install_confinement_seccomp(*, confinement: str) -> None:
    """Install `PR_SET_NO_NEW_PRIVS` and the confinement seccomp filter."""
    bpf = _build_confinement_seccomp_bpf(
        platform.machine(), confinement=confinement
    )
    buf = ctypes.create_string_buffer(bpf)
    prog = _SockFprog(len(bpf) // 8, ctypes.addressof(buf))
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_NO_NEW_PRIVS) failed: errno={err}")
    if libc.prctl(_PR_SET_SECCOMP, _SECCOMP_MODE_FILTER, ctypes.byref(prog), 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_SECCOMP) failed: errno={err}")
