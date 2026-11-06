#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical verification of Linux process isolation policies for Lean 4 v4.34.1."""

import ctypes
import ctypes.util
import json
import os
import shutil
import socket
import struct
import subprocess
import sys
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
LEAN_BIN = os.path.expanduser(
    "~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
)
ANNEAL_LEAN_RUN = os.path.expanduser("~/.local/bin/anneal-lean-run")

# Linux x86_64 constants
PR_SET_NO_NEW_PRIVS = 38
PR_SET_SECCOMP = 22
SECCOMP_MODE_FILTER = 2

AUDIT_ARCH_X86_64 = 0xC000003E
SECCOMP_RET_KILL_PROCESS = 0x80000000
SECCOMP_RET_ERRNO = 0x00050000
SECCOMP_RET_ALLOW = 0x7FFF0000

ENOSYS = 38
EPERM = 1
CLONE_THREAD = 0x00010000

# x86_64 syscall numbers
SYS_socket = 41
SYS_connect = 42
SYS_sendto = 44
SYS_sendmsg = 46
SYS_bind = 49
SYS_listen = 50
SYS_socketpair = 53
SYS_clone = 56
SYS_fork = 57
SYS_vfork = 58
SYS_execve = 59
SYS_ptrace = 101
SYS_setsid = 112
SYS_process_vm_readv = 310
SYS_process_vm_writev = 311
SYS_execveat = 322
SYS_clone3 = 435

# Landlock syscall numbers and constants (x86_64)
SYS_landlock_create_ruleset = 444
SYS_landlock_add_rule = 445
SYS_landlock_restrict_self = 446
LANDLOCK_CREATE_RULESET_VERSION = 1 << 0
LANDLOCK_RULE_PATH_BENEATH = 1

# BPF instruction macros
BPF_LD = 0x00
BPF_W = 0x00
BPF_ABS = 0x20
BPF_JMP = 0x05
BPF_JEQ = 0x10
BPF_JSET = 0x40
BPF_K = 0x00
BPF_RET = 0x06


def bpf_stmt(code: int, k: int) -> bytes:
    return struct.pack("HBBI", code, 0, 0, k)


def bpf_jump(code: int, k: int, jt: int, jf: int) -> bytes:
    return struct.pack("HBBI", code, jt, jf, k)


class SockFilter(ctypes.Structure):
    _fields_ = [
        ("code", ctypes.c_ushort),
        ("jt", ctypes.c_ubyte),
        ("jf", ctypes.c_ubyte),
        ("k", ctypes.c_uint),
    ]


class SockFprog(ctypes.Structure):
    _fields_ = [
        ("len", ctypes.c_ushort),
        ("filter", ctypes.POINTER(SockFilter)),
    ]


class LandlockRulesetAttr(ctypes.Structure):
    _fields_ = [
        ("handled_access_fs", ctypes.c_uint64),
        ("handled_access_net", ctypes.c_uint64),
        ("scoped", ctypes.c_uint64),
    ]


class LandlockPathBeneathAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [
        ("allowed_access", ctypes.c_uint64),
        ("parent_fd", ctypes.c_int32),
    ]


libc = ctypes.CDLL(ctypes.util.find_library("c"), use_errno=True)


def query_landlock_abi() -> int:
    return libc.syscall(
        SYS_landlock_create_ruleset,
        None,
        0,
        LANDLOCK_CREATE_RULESET_VERSION,
    )


def apply_landlock_v9(ro_paths: list[str], rw_paths: list[str]) -> int:
    abi = query_landlock_abi()
    if abi <= 0:
        return abi
    # ABI v9 supports bits 0..16 for FS, bits 0..1 for NET, bits 0..1 for scoped
    fs_mask = (1 << 17) - 1 if abi >= 9 else (1 << 15) - 1
    net_mask = 0x3 if abi >= 4 else 0
    scoped_mask = 0x3 if abi >= 6 else 0

    attr = LandlockRulesetAttr(fs_mask, net_mask, scoped_mask)
    ruleset_fd = libc.syscall(
        SYS_landlock_create_ruleset,
        ctypes.byref(attr),
        ctypes.sizeof(attr),
        0,
    )
    if ruleset_fd < 0:
        raise OSError(ctypes.get_errno(), "landlock_create_ruleset failed")

    # Read-only + execute access mask:
    # EXECUTE (1<<0) | READ_FILE (1<<2) | READ_DIR (1<<3)
    ro_access = (1 << 0) | (1 << 2) | (1 << 3)
    # Read-write access mask (without EXECUTE or RESOLVE_UNIX):
    rw_access = (
        ro_access
        | (1 << 1)  # WRITE_FILE
        | (1 << 4)  # REMOVE_DIR
        | (1 << 5)  # REMOVE_FILE
        | (1 << 6)  # MAKE_CHAR
        | (1 << 7)  # MAKE_DIR
        | (1 << 8)  # MAKE_REG
        | (1 << 11)  # MAKE_SYM
        | (1 << 12)  # REFER
        | (1 << 13)  # TRUNCATE
    )

    O_PATH = 0o10000000
    for p in ro_paths:
        if not os.path.exists(p):
            continue
        fd = os.open(p, O_PATH | os.O_CLOEXEC)
        try:
            pb = LandlockPathBeneathAttr(ro_access & fs_mask, fd)
            libc.syscall(
                SYS_landlock_add_rule,
                ruleset_fd,
                LANDLOCK_RULE_PATH_BENEATH,
                ctypes.byref(pb),
                0,
            )
        finally:
            os.close(fd)

    for p in rw_paths:
        if not os.path.exists(p):
            continue
        fd = os.open(p, O_PATH | os.O_CLOEXEC)
        try:
            pb = LandlockPathBeneathAttr(rw_access & fs_mask, fd)
            libc.syscall(
                SYS_landlock_add_rule,
                ruleset_fd,
                LANDLOCK_RULE_PATH_BENEATH,
                ctypes.byref(pb),
                0,
            )
        finally:
            os.close(fd)

    if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        os.close(ruleset_fd)
        raise OSError(ctypes.get_errno(), "prctl(NO_NEW_PRIVS) failed")

    if libc.syscall(SYS_landlock_restrict_self, ruleset_fd, 0) != 0:
        err = ctypes.get_errno()
        os.close(ruleset_fd)
        raise OSError(err, "landlock_restrict_self failed")

    os.close(ruleset_fd)
    return abi


def build_seccomp_filter(block_execve: bool) -> bytes:
    """Constructs the seccomp-bpf program.

    - Verify arch == AUDIT_ARCH_X86_64
    - SYS_clone3 -> SECCOMP_RET_ERRNO | ENOSYS (glibc falls back to SYS_clone)
    - SYS_clone -> inspect (args[0] & CLONE_THREAD):
        if set -> SECCOMP_RET_ALLOW
        if unset -> SECCOMP_RET_ERRNO | EPERM
    - Blocked process/IPC/network/debug syscalls -> SECCOMP_RET_ERRNO | EPERM
    """
    eblock = [
        SYS_fork,
        SYS_vfork,
        SYS_setsid,
        SYS_socket,
        SYS_socketpair,
        SYS_connect,
        SYS_bind,
        SYS_listen,
        SYS_sendto,
        SYS_sendmsg,
        SYS_ptrace,
        SYS_process_vm_readv,
        SYS_process_vm_writev,
    ]
    if block_execve:
        eblock.extend([SYS_execve, SYS_execveat])

    insns: list[bytes] = []
    # [0] Load arch (offset 4 in seccomp_data)
    insns.append(bpf_stmt(BPF_LD | BPF_W | BPF_ABS, 4))
    # [1] Jump if arch == X86_64 to [3], else [2]
    insns.append(bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0))
    # [2] Kill on wrong arch
    insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS))
    # [3] Load nr (offset 0 in seccomp_data)
    insns.append(bpf_stmt(BPF_LD | BPF_W | BPF_ABS, 0))
    # [4] If nr == SYS_clone3 -> return ENOSYS
    insns.append(bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_clone3, 0, 1))
    insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ENOSYS))
    # [6] If nr == SYS_clone -> check CLONE_THREAD in args[0] (offset 16)
    insns.append(bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_clone, 0, 4))
    insns.append(bpf_stmt(BPF_LD | BPF_W | BPF_ABS, 16))
    insns.append(bpf_jump(BPF_JMP | BPF_JSET | BPF_K, CLONE_THREAD, 0, 1))
    insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_ALLOW))
    insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM))

    # Each syscall in eblock -> return EPERM
    for nr in eblock:
        insns.append(bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, nr, 0, 1))
        insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM))

    # Default allow
    insns.append(bpf_stmt(BPF_RET | BPF_K, SECCOMP_RET_ALLOW))
    return b"".join(insns)


def install_seccomp_filter(block_execve: bool) -> None:
    raw = build_seccomp_filter(block_execve=block_execve)
    count = len(raw) // 8
    arr = (SockFilter * count).from_buffer_copy(raw)
    prog = SockFprog(count, ctypes.cast(arr, ctypes.POINTER(SockFilter)))
    if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_NO_NEW_PRIVS) failed")
    if libc.prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ctypes.byref(prog), 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_SECCOMP) failed")


def build_post_exec_preload_so() -> Path:
    """Builds a minimal shared library that locks SYS_execve/SYS_execveat on startup."""
    c_src = BASE_DIR / "lock_execve.c"
    so_path = BASE_DIR / "liblock_execve.so"
    c_code = """
#include <errno.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sys/prctl.h>
#include <sys/syscall.h>

__attribute__((constructor))
static void lock_execve_init(void) {
    struct sock_filter filter[] = {
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, 4),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, 0),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_execve, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_execveat, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    };
    struct sock_fprog prog = {
        .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
        .filter = filter,
    };
    prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
    prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog, 0, 0);
}
"""
    c_src.write_text(c_code)
    subprocess.run(
        ["gcc", "-O2", "-shared", "-fPIC", str(c_src), "-o", str(so_path)],
        check=True,
    )
    return so_path


def run_lean_under_sandbox(lean_code: str, name: str, so_path: Path) -> dict:
    lean_file = BASE_DIR / f"{name}.lean"
    lean_file.write_text(lean_code)

    ro_paths = [
        "/usr",
        "/lib",
        "/lib64",
        "/bin",
        "/dev",
        "/proc",
        os.path.expanduser("~/.elan"),
        str(BASE_DIR),
    ]
    rw_paths = []

    def preexec() -> None:
        apply_landlock_v9(ro_paths=ro_paths, rw_paths=rw_paths)
        install_seccomp_filter(block_execve=False)

    env = os.environ.copy()
    env["LD_PRELOAD"] = str(so_path)
    proc = subprocess.run(
        [LEAN_BIN, str(lean_file)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        preexec_fn=preexec,
        timeout=30,
    )
    return {
        "name": name,
        "returncode": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip(),
    }


def run_direct_syscall_checks() -> dict:
    """Forks a child that enters Landlock v9 + seccomp-bpf (with block_execve=True)
    and verifies the exact errno returned for each syscall class."""
    r_fd, w_fd = os.pipe()
    parent_pid = os.getpid()
    pid = os.fork()
    if pid == 0:
        os.close(r_fd)
        results = {}
        try:
            abi = apply_landlock_v9(
                ro_paths=["/usr", "/lib", "/lib64", "/bin"],
                rw_paths=[],
            )
            install_seccomp_filter(block_execve=True)
            results["landlock_abi"] = abi

            # 1a. SYS_clone3 -> ENOSYS
            res_c3 = libc.syscall(SYS_clone3, 0, 0)
            results["sys_clone3_errno"] = ctypes.get_errno() if res_c3 < 0 else 0

            # 1b. SYS_clone without CLONE_THREAD (process fork) -> EPERM
            SIGCHLD = 17
            res_clone_proc = libc.syscall(SYS_clone, SIGCHLD, 0, 0, 0, 0)
            results["sys_clone_process_errno"] = (
                ctypes.get_errno() if res_clone_proc < 0 else 0
            )

            # 1c. SYS_fork & SYS_setsid -> EPERM
            res_fork = libc.syscall(SYS_fork)
            results["sys_fork_errno"] = ctypes.get_errno() if res_fork < 0 else 0
            res_setsid = libc.syscall(SYS_setsid)
            results["sys_setsid_errno"] = ctypes.get_errno() if res_setsid < 0 else 0

            # 2a. AF_UNIX socket -> EPERM
            res_unix = libc.syscall(SYS_socket, socket.AF_UNIX, socket.SOCK_STREAM, 0)
            results["af_unix_socket_errno"] = (
                ctypes.get_errno() if res_unix < 0 else 0
            )

            # 2b. AF_INET SOCK_DGRAM (UDP) socket -> EPERM
            res_udp = libc.syscall(SYS_socket, socket.AF_INET, socket.SOCK_DGRAM, 0)
            results["af_inet_udp_socket_errno"] = (
                ctypes.get_errno() if res_udp < 0 else 0
            )

            # 3. Direct dynamic linker invocation via SYS_execve -> EPERM
            ld_path = b"/lib64/ld-linux-x86-64.so.2"
            res_exec = libc.syscall(
                SYS_execve, ctypes.c_char_p(ld_path), 0, 0
            )
            results["sys_execve_ld_linux_errno"] = (
                ctypes.get_errno() if res_exec < 0 else 0
            )

            # 4. SYS_ptrace(PTRACE_ATTACH=16, parent_pid) -> EPERM
            res_ptrace = libc.syscall(SYS_ptrace, 16, parent_pid, 0, 0)
            results["sys_ptrace_attach_errno"] = (
                ctypes.get_errno() if res_ptrace < 0 else 0
            )

            # 5. SYS_process_vm_readv -> EPERM
            res_vm = libc.syscall(SYS_process_vm_readv, parent_pid, 0, 0, 0, 0, 0)
            results["sys_process_vm_readv_errno"] = (
                ctypes.get_errno() if res_vm < 0 else 0
            )
        except Exception as exc:
            results["error"] = str(exc)

        os.write(w_fd, json.dumps(results).encode("utf-8"))
        os.close(w_fd)
        os._exit(0)
    else:
        os.close(w_fd)
        data = os.read(r_fd, 65536)
        os.close(r_fd)
        os.waitpid(pid, 0)
        return json.loads(data.decode("utf-8"))


def test_bwrap() -> dict:
    bwrap_path = shutil.which("bwrap")
    if not bwrap_path:
        return {"installed": False}

    ver_proc = subprocess.run(
        [bwrap_path, "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    probe_lean = BASE_DIR / "bwrap_task_probe.lean"
    probe_lean.write_text(
        """
#eval show IO Unit from do
  let t1 := Task.spawn fun _ => List.range 500 |>.foldl (· + ·) 0
  let t2 := Task.spawn fun _ => List.range 500 |>.foldl (· + ·) 0
  IO.println s!"bwrap_tasks_sum={t1.get + t2.get}"
"""
    )

    cmd = [
        bwrap_path,
        "--unshare-all",
        "--die-with-parent",
        "--ro-bind",
        "/",
        "/",
        "--tmpfs",
        "/run",
        "--tmpfs",
        "/tmp",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        LEAN_BIN,
        str(probe_lean),
    ]
    run_proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
    )

    # Also test whether /run/docker.sock is masked inside bwrap --tmpfs /run
    mask_cmd = [
        bwrap_path,
        "--unshare-all",
        "--die-with-parent",
        "--ro-bind",
        "/",
        "/",
        "--tmpfs",
        "/run",
        "--tmpfs",
        "/tmp",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "/usr/bin/python3",
        "-c",
        (
            "import os, socket; "
            "s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); "
            "err = None\n"
            "try:\n"
            "  s.sendto(b'x', ('8.8.8.8', 53))\n"
            "except OSError as e:\n"
            "  err = e.errno\n"
            "print(f'run_entries={os.listdir(\"/run\")} udp_errno={err}')"
        ),
    ]
    mask_proc = subprocess.run(
        mask_cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
    )

    return {
        "installed": True,
        "path": bwrap_path,
        "version": ver_proc.stdout.strip(),
        "unprivileged_unshare_all_returncode": run_proc.returncode,
        "unprivileged_unshare_all_stdout": run_proc.stdout.strip(),
        "unprivileged_unshare_all_stderr": run_proc.stderr.strip(),
        "isolation_check_returncode": mask_proc.returncode,
        "isolation_check_stdout": mask_proc.stdout.strip(),
        "isolation_check_stderr": mask_proc.stderr.strip(),
    }


def main() -> None:
    so_path = build_post_exec_preload_so()

    # Lean Probe 1: Task.spawn / Task.get + IO.asTask parallel computation
    lean_tasks = run_lean_under_sandbox(
        """
#eval show IO Unit from do
  let tasks ← (List.range 8).mapM fun i => IO.asTask do
    let s := (List.range 1000).foldl (· + ·) i
    return s
  let mut total := 0
  for t in tasks do
    let v ← IO.ofExcept t.get
    total := total + v
  let pureTask := Task.spawn fun _ => (List.range 100).foldl (· + ·) 0
  IO.println s!"TASK_POOL_OK total={total + pureTask.get}"
""",
        "probe_1_tasks",
        so_path,
    )

    # Lean Probe 2: UDP socket bind/send via Std.Internal.UV.UDP.Socket
    lean_udp = run_lean_under_sandbox(
        """
import Std.Internal.UV.UDP
import Std.Net.Addr
#eval show IO Unit from do
  try
    let s ← Std.Internal.UV.UDP.Socket.new
    let addr := Std.Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 0
    s.bind (.v4 addr)
    IO.println "UNEXPECTED_UDP_SUCCESS"
  catch e =>
    IO.println s!"UDP_BLOCKED: {e}"
""",
        "probe_2_udp",
        so_path,
    )

    # Lean Probe 3: Dynamic linker invocation (/lib64/ld-linux-x86-64.so.2) via IO.Process.output
    lean_ld_linux = run_lean_under_sandbox(
        """
#eval show IO Unit from do
  try
    let out ← IO.Process.output {
      cmd := "/lib64/ld-linux-x86-64.so.2"
      args := #["/usr/bin/true"]
    }
    IO.println s!"UNEXPECTED_LD_SUCCESS exit={out.exitCode}"
  catch e =>
    IO.println s!"LD_LINUX_BLOCKED: {e}"
""",
        "probe_3_ld_linux",
        so_path,
    )

    # Lean Probe 4: Background process spawn via IO.Process.spawn
    lean_spawn = run_lean_under_sandbox(
        """
#eval show IO Unit from do
  try
    let _ ← IO.Process.spawn {
      cmd := "/usr/bin/true"
    }
    IO.println "UNEXPECTED_SPAWN_SUCCESS"
  catch e =>
    IO.println s!"SPAWN_BLOCKED: {e}"
""",
        "probe_4_spawn",
        so_path,
    )

    direct_syscalls = run_direct_syscall_checks()
    bwrap_info = test_bwrap()

    all_passed = (
        lean_tasks["returncode"] == 0
        and "TASK_POOL_OK total=4000978" in lean_tasks["stdout"]
        and lean_udp["returncode"] == 0
        and "UDP_BLOCKED:" in lean_udp["stdout"]
        and lean_ld_linux["returncode"] == 0
        and "LD_LINUX_BLOCKED:" in lean_ld_linux["stdout"]
        and lean_spawn["returncode"] == 0
        and "SPAWN_BLOCKED:" in lean_spawn["stdout"]
        and direct_syscalls.get("sys_clone3_errno") == ENOSYS
        and direct_syscalls.get("sys_clone_process_errno") == EPERM
        and direct_syscalls.get("sys_fork_errno") == EPERM
        and direct_syscalls.get("sys_setsid_errno") == EPERM
        and direct_syscalls.get("af_unix_socket_errno") == EPERM
        and direct_syscalls.get("af_inet_udp_socket_errno") == EPERM
        and direct_syscalls.get("sys_execve_ld_linux_errno") == EPERM
        and direct_syscalls.get("sys_ptrace_attach_errno") == EPERM
        and direct_syscalls.get("sys_process_vm_readv_errno") == EPERM
        and bwrap_info.get("installed") is True
        and bwrap_info.get("unprivileged_unshare_all_returncode") == 0
    )

    summary = {
        "kernel": os.uname().release,
        "allAssertionsPassed": all_passed,
        "leanProbes": {
            "taskPool": lean_tasks,
            "udpSocket": lean_udp,
            "ldLinuxExec": lean_ld_linux,
            "processSpawn": lean_spawn,
        },
        "directSyscallErrnoChecks": direct_syscalls,
        "bwrapChecks": bwrap_info,
    }

    out_file = BASE_DIR / "hardened_sandbox_results.json"
    out_file.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if not all_passed:
        sys.exit(1)


if __name__ == "__main__":
    main()
