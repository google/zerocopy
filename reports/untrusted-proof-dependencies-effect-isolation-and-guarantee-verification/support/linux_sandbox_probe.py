#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical evaluation of unprivileged Linux sandboxing building blocks for Lean 4.34.1.

Tests:
1. Combined EvilTheory.lean (and per-vector isolated EvilTheory variants):
   - Vector 1: `#eval IO.FS.writeFile "/tmp/pwned" "pwn"` (arbitrary file write)
   - Vector 2a: `#eval IO.FS.readFile "/etc/hostname"` (arbitrary file read via #eval)
   - Vector 2b: `include_str "../../../../../../../../../../../../etc/hostname"` (read without #eval)
   - Vector 3: `#eval IO.Process.output { cmd := "sh", args := #["-c", "id"] }` (process spawn)
   - Vector 4: `#eval IO.FS.writeFile "Trusted.olean" "corrupted"` (upstream .olean corruption)
   - Vector 5: `Std.Internal.UV.TCP.Socket.new` + `bind 127.0.0.1:0` (network socket creation)
2. Sandboxing mechanisms evaluated:
   - Landlock LSM (ABI v5) + PR_SET_NO_NEW_PRIVS + seccomp-bpf (in-process preexec_fn)
   - bubblewrap (`bwrap --unshare-all`)
   - util-linux `unshare -Urmnpf`
3. Wall-clock latency benchmark (N=20 iterations after 2 warmup runs) compiling GoodTheory.lean.
"""

import ctypes
import hashlib
import json
import os
import pathlib
import shutil
import statistics
import struct
import subprocess
import tempfile
import time

LEAN_ROOT = pathlib.Path(
    str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1")
)
LEAN_BIN = LEAN_ROOT / "bin" / "lean"
PROBES_DIR = pathlib.Path(__file__).resolve().parent

# Linux x86_64 constants
SYS_LANDLOCK_CREATE_RULESET = 444
SYS_LANDLOCK_ADD_RULE = 445
SYS_LANDLOCK_RESTRICT_SELF = 446
LANDLOCK_CREATE_RULESET_VERSION = 1 << 0
LANDLOCK_RULE_PATH_BENEATH = 1

LANDLOCK_ACCESS_FS_EXECUTE = 1 << 0
LANDLOCK_ACCESS_FS_WRITE_FILE = 1 << 1
LANDLOCK_ACCESS_FS_READ_FILE = 1 << 2
LANDLOCK_ACCESS_FS_READ_DIR = 1 << 3
LANDLOCK_ACCESS_FS_REMOVE_DIR = 1 << 4
LANDLOCK_ACCESS_FS_REMOVE_FILE = 1 << 5
LANDLOCK_ACCESS_FS_MAKE_CHAR = 1 << 6
LANDLOCK_ACCESS_FS_MAKE_DIR = 1 << 7
LANDLOCK_ACCESS_FS_MAKE_REG = 1 << 8
LANDLOCK_ACCESS_FS_MAKE_SOCK = 1 << 9
LANDLOCK_ACCESS_FS_MAKE_FIFO = 1 << 10
LANDLOCK_ACCESS_FS_MAKE_BLOCK = 1 << 11
LANDLOCK_ACCESS_FS_MAKE_SYM = 1 << 12
LANDLOCK_ACCESS_FS_REFER = 1 << 13
LANDLOCK_ACCESS_FS_TRUNCATE = 1 << 14

LANDLOCK_HANDLED_FS = (1 << 15) - 1
LANDLOCK_ACCESS_NET_BIND_TCP = 1 << 0
LANDLOCK_ACCESS_NET_CONNECT_TCP = 1 << 1
LANDLOCK_HANDLED_NET = LANDLOCK_ACCESS_NET_BIND_TCP | LANDLOCK_ACCESS_NET_CONNECT_TCP

FS_FILE_RO = LANDLOCK_ACCESS_FS_READ_FILE | LANDLOCK_ACCESS_FS_EXECUTE
FS_DIR_RO = (
    LANDLOCK_ACCESS_FS_READ_FILE
    | LANDLOCK_ACCESS_FS_READ_DIR
    | LANDLOCK_ACCESS_FS_EXECUTE
)
FS_DIR_RW = (
    FS_DIR_RO
    | LANDLOCK_ACCESS_FS_WRITE_FILE
    | LANDLOCK_ACCESS_FS_REMOVE_DIR
    | LANDLOCK_ACCESS_FS_REMOVE_FILE
    | LANDLOCK_ACCESS_FS_MAKE_DIR
    | LANDLOCK_ACCESS_FS_MAKE_REG
    | LANDLOCK_ACCESS_FS_TRUNCATE
    | LANDLOCK_ACCESS_FS_REFER
)

O_PATH = 0o10000000
O_CLOEXEC = 0o2000000

PR_SET_NO_NEW_PRIVS = 38
PR_SET_SECCOMP = 22
SECCOMP_MODE_FILTER = 2

AUDIT_ARCH_X86_64 = 0xC000003E
SECCOMP_RET_ALLOW = 0x7FFF0000
SECCOMP_RET_ERRNO = 0x00050000
EPERM = 1
ENOSYS = 38

SYS_SOCKET = 41
SYS_CONNECT = 42
SYS_BIND = 49
SYS_LISTEN = 50
SYS_SOCKETPAIR = 53
SYS_CLONE = 56
SYS_FORK = 57
SYS_VFORK = 58
SYS_CLONE3 = 435
CLONE_THREAD = 0x00010000


class LandlockRulesetAttr(ctypes.Structure):
    _fields_ = [
        ("handled_access_fs", ctypes.c_uint64),
        ("handled_access_net", ctypes.c_uint64),
    ]


class LandlockPathBeneathAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [
        ("allowed_access", ctypes.c_uint64),
        ("parent_fd", ctypes.c_int32),
    ]


class SockFilter(ctypes.Structure):
    _fields_ = [
        ("code", ctypes.c_uint16),
        ("jt", ctypes.c_uint8),
        ("jf", ctypes.c_uint8),
        ("k", ctypes.c_uint32),
    ]


class SockFprog(ctypes.Structure):
    _fields_ = [
        ("len", ctypes.c_uint16),
        ("filter", ctypes.POINTER(SockFilter)),
    ]


libc = ctypes.CDLL("libc.so.6", use_errno=True)
libc.syscall.restype = ctypes.c_long


def get_landlock_abi_version() -> int:
    ver = libc.syscall(
        ctypes.c_long(SYS_LANDLOCK_CREATE_RULESET),
        ctypes.c_void_p(None),
        ctypes.c_size_t(0),
        ctypes.c_uint32(LANDLOCK_CREATE_RULESET_VERSION),
    )
    if ver < 0:
        raise OSError(ctypes.get_errno(), "landlock_create_ruleset(VERSION) failed")
    return int(ver)


def build_seccomp_prog() -> tuple[SockFprog, ctypes.Array]:
    """Builds a classic BPF filter blocking network sockets and process forks while allowing pthreads."""
    BPF_LD = 0x00
    BPF_W = 0x00
    BPF_ABS = 0x20
    BPF_JMP = 0x05
    BPF_JEQ = 0x10
    BPF_JSET = 0x40
    BPF_K = 0x00
    BPF_RET = 0x06

    def stmt(code: int, k: int) -> SockFilter:
        return SockFilter(code, 0, 0, k)

    def jump(code: int, k: int, jt: int, jf: int) -> SockFilter:
        return SockFilter(code, jt, jf, k)

    # Offsets in struct seccomp_data:
    # nr: 0, arch: 4, instruction_pointer: 8, args[0] (low 32 bits): 16
    insns = [
        # 0: Load arch
        stmt(BPF_LD | BPF_W | BPF_ABS, 4),
        # 1: If arch != X86_64, jump to allow (or kill; allow non-matching arch untouched)
        jump(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 0, 14),
        # 2: Load syscall nr
        stmt(BPF_LD | BPF_W | BPF_ABS, 0),
        # 3..9: Block socket/connect/bind/listen/socketpair/fork/vfork -> DENY_EPERM (idx 14)
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_SOCKET, 10, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_CONNECT, 9, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_BIND, 8, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_LISTEN, 7, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_SOCKETPAIR, 6, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_FORK, 5, 0),
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_VFORK, 4, 0),
        # 10: SYS_CLONE3 -> return ENOSYS (idx 15) so glibc pthreads falls back to SYS_CLONE
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_CLONE3, 4, 0),
        # 11: SYS_CLONE -> inspect args[0] for CLONE_THREAD
        jump(BPF_JMP | BPF_JEQ | BPF_K, SYS_CLONE, 0, 4),
        # 12: Load args[0] low 32 bits (clone flags)
        stmt(BPF_LD | BPF_W | BPF_ABS, 16),
        # 13: If (flags & CLONE_THREAD) != 0 -> ALLOW (idx 16), else DENY_EPERM (idx 14)
        jump(BPF_JMP | BPF_JSET | BPF_K, CLONE_THREAD, 2, 0),
        # 14: DENY_EPERM
        stmt(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
        # 15: DENY_ENOSYS
        stmt(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ENOSYS),
        # 16: ALLOW
        stmt(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    ]
    arr_type = SockFilter * len(insns)
    arr = arr_type(*insns)
    prog = SockFprog(len(insns), ctypes.cast(arr, ctypes.POINTER(SockFilter)))
    return prog, arr


def make_landlock_seccomp_preexec(
    ro_dirs: list[pathlib.Path],
    ro_files: list[pathlib.Path],
    rw_dirs: list[pathlib.Path],
):
    """Returns a preexec_fn that applies Landlock LSM + PR_SET_NO_NEW_PRIVS + seccomp-bpf."""
    ro_dir_strs = [str(p) for p in ro_dirs if p.exists()]
    ro_file_strs = [str(p) for p in ro_files if p.exists()]
    rw_dir_strs = [str(p) for p in rw_dirs if p.exists()]

    def _preexec():
        # 1. PR_SET_NO_NEW_PRIVS = 1 (required for unprivileged Landlock & seccomp-bpf)
        res = libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)
        if res != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_SET_NO_NEW_PRIVS) failed")

        # 2. Create Landlock ruleset handling FS + NET_TCP
        attr = LandlockRulesetAttr(
            handled_access_fs=LANDLOCK_HANDLED_FS,
            handled_access_net=LANDLOCK_HANDLED_NET,
        )
        ruleset_fd = libc.syscall(
            ctypes.c_long(SYS_LANDLOCK_CREATE_RULESET),
            ctypes.byref(attr),
            ctypes.c_size_t(ctypes.sizeof(attr)),
            ctypes.c_uint32(0),
        )
        if ruleset_fd < 0:
            raise OSError(ctypes.get_errno(), "landlock_create_ruleset failed")

        def add_path_rule(path_str: str, access_mask: int):
            fd = os.open(path_str, O_PATH | O_CLOEXEC)
            try:
                rule = LandlockPathBeneathAttr(
                    allowed_access=access_mask,
                    parent_fd=fd,
                )
                r = libc.syscall(
                    ctypes.c_long(SYS_LANDLOCK_ADD_RULE),
                    ctypes.c_int(ruleset_fd),
                    ctypes.c_int(LANDLOCK_RULE_PATH_BENEATH),
                    ctypes.byref(rule),
                    ctypes.c_uint32(0),
                )
                if r < 0:
                    raise OSError(
                        ctypes.get_errno(), f"landlock_add_rule({path_str}) failed"
                    )
            finally:
                os.close(fd)

        for d in ro_dir_strs:
            add_path_rule(d, FS_DIR_RO)
        for f in ro_file_strs:
            add_path_rule(f, FS_FILE_RO)
        for d in rw_dir_strs:
            add_path_rule(d, FS_DIR_RW)

        r = libc.syscall(
            ctypes.c_long(SYS_LANDLOCK_RESTRICT_SELF),
            ctypes.c_int(ruleset_fd),
            ctypes.c_uint32(0),
        )
        os.close(ruleset_fd)
        if r < 0:
            raise OSError(ctypes.get_errno(), "landlock_restrict_self failed")

        # 3. Install seccomp-bpf filter
        prog, _arr = build_seccomp_prog()
        r = libc.prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ctypes.byref(prog), 0, 0)
        if r != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_SET_SECCOMP) failed")

    return _preexec


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_cmd_landlock(
    cmd: list[str],
    cwd: pathlib.Path,
    env: dict[str, str],
    ro_dirs: list[pathlib.Path],
    ro_files: list[pathlib.Path],
    rw_dirs: list[pathlib.Path],
) -> tuple[int, str, str, float]:
    preexec = make_landlock_seccomp_preexec(ro_dirs, ro_files, rw_dirs)
    t0 = time.perf_counter_ns()
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        preexec_fn=preexec,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    return proc.returncode, proc.stdout, proc.stderr, elapsed_ms


def run_cmd_bwrap(
    cmd: list[str],
    cwd: pathlib.Path,
    env: dict[str, str],
    ro_dirs: list[pathlib.Path],
    ro_files: list[pathlib.Path],
    rw_dirs: list[pathlib.Path],
) -> tuple[int, str, str, float]:
    bwrap_cmd = [
        "/usr/bin/bwrap",
        "--unshare-all",
        "--die-with-parent",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
    ]
    for d in ro_dirs:
        if d.exists():
            bwrap_cmd.extend(["--ro-bind", str(d), str(d)])
    for f in ro_files:
        if f.exists() and not str(f).startswith("/dev/"):
            bwrap_cmd.extend(["--ro-bind", str(f), str(f)])
    for d in rw_dirs:
        if d.exists():
            bwrap_cmd.extend(["--bind", str(d), str(d)])
    bwrap_cmd.extend(["--chdir", str(cwd), "--"])
    bwrap_cmd.extend(cmd)

    t0 = time.perf_counter_ns()
    proc = subprocess.run(
        bwrap_cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    return proc.returncode, proc.stdout, proc.stderr, elapsed_ms


def run_cmd_unshare(
    cmd: list[str],
    cwd: pathlib.Path,
    env: dict[str, str],
) -> tuple[int, str, str, float]:
    unshare_cmd = [
        "/usr/bin/unshare",
        "-Urmnpf",
        "--mount-proc",
        "--",
    ] + cmd
    t0 = time.perf_counter_ns()
    proc = subprocess.run(
        unshare_cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    return proc.returncode, proc.stdout, proc.stderr, elapsed_ms


def run_cmd_unsandboxed(
    cmd: list[str],
    cwd: pathlib.Path,
    env: dict[str, str],
) -> tuple[int, str, str, float]:
    t0 = time.perf_counter_ns()
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    return proc.returncode, proc.stdout, proc.stderr, elapsed_ms


def main() -> None:
    abi_ver = get_landlock_abi_version()
    with tempfile.TemporaryDirectory(prefix="anneal_track5_stage_") as tmp:
        stage = pathlib.Path(tmp)
        deps_dir = stage / "deps"
        src_dir = stage / "src"
        out_dir = stage / "out"
        deps_dir.mkdir()
        src_dir.mkdir()
        out_dir.mkdir()

        # Copy probe sources into stage/src
        for name in ["Trusted.lean", "GoodTheory.lean", "EvilTheory.lean"]:
            shutil.copy2(PROBES_DIR / name, src_dir / name)

        base_env = {
            "PATH": str(LEAN_ROOT / "bin"),
            "LEAN_PATH": str(deps_dir),
            "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "2"),
            "HOME": "/nonexistent",
        }

        # 1. Compile Trusted.lean -> deps/Trusted.olean
        trusted_olean = deps_dir / "Trusted.olean"
        rc, out, err, _ = run_cmd_unsandboxed(
            [
                str(LEAN_BIN),
                "-R",
                str(src_dir),
                "-o",
                str(trusted_olean),
                str(src_dir / "Trusted.lean"),
            ],
            cwd=deps_dir,
            env=base_env,
        )
        assert rc == 0, f"Trusted.lean compilation failed: {out}\n{err}"
        trusted_sha_before = sha256_file(trusted_olean)

        ro_dirs = [
            LEAN_ROOT,
            pathlib.Path("/lib"),
            pathlib.Path("/lib64"),
            pathlib.Path("/usr/lib"),
            deps_dir,
            src_dir,
        ]
        ro_files = [
            pathlib.Path("/etc/ld.so.cache"),
            pathlib.Path("/dev/urandom"),
            pathlib.Path("/dev/null"),
        ]
        rw_dirs = [
            out_dir,
        ]

        # 2. Test Combined EvilTheory.lean under Landlock+seccomp-bpf and under bwrap
        evil_lean = src_dir / "EvilTheory.lean"
        evil_olean = out_dir / "EvilTheory.olean"
        pwn_path = pathlib.Path("/tmp/pwned")
        if pwn_path.exists():
            pwn_path.unlink()

        ll_rc, ll_out, ll_err, ll_ms = run_cmd_landlock(
            [str(LEAN_BIN), "-R", str(src_dir), "-o", str(evil_olean), str(evil_lean)],
            cwd=deps_dir,
            env=base_env,
            ro_dirs=ro_dirs,
            ro_files=ro_files,
            rw_dirs=rw_dirs,
        )
        ll_trusted_sha_after = sha256_file(trusted_olean)
        ll_pwn_created = pwn_path.exists()

        bw_rc, bw_out, bw_err, bw_ms = run_cmd_bwrap(
            [str(LEAN_BIN), "-R", str(src_dir), "-o", str(evil_olean), str(evil_lean)],
            cwd=deps_dir,
            env=base_env,
            ro_dirs=ro_dirs,
            ro_files=ro_files,
            rw_dirs=rw_dirs,
        )
        bw_trusted_sha_after = sha256_file(trusted_olean)
        bw_pwn_created = pwn_path.exists()

        # 3. Also test each individual vector in isolation to record the exact per-vector diagnostic
        individual_vectors = {
            "vec1_write_tmp_pwned": 'import Trusted\n#eval IO.FS.writeFile "/tmp/pwned" "pwn"\n',
            "vec2a_read_etc_hostname_eval": 'import Trusted\n#eval IO.FS.readFile "/etc/hostname"\n',
            "vec2b_read_etc_hostname_include_str": (
                'import Trusted\ndef h : String := include_str "../../../../../../../../../../../../etc/hostname"\n'
            ),
            "vec3_spawn_process_sh": (
                'import Trusted\n#eval IO.Process.output { cmd := "sh", args := #["-c", "id"] }\n'
            ),
            "vec3b_spawn_process_abs_sh": (
                'import Trusted\n#eval IO.Process.output { cmd := "/bin/sh", args := #["-c", "id"] }\n'
            ),
            "vec4_overwrite_trusted_olean": (
                'import Trusted\n#eval IO.FS.writeFile "Trusted.olean" "corrupted"\n'
            ),
            "vec5_network_tcp_socket": (
                "import Trusted\nimport Std.Internal.UV.TCP\nimport Std.Net.Addr\n"
                "#eval do\n"
                "  let sock ← Std.Internal.UV.TCP.Socket.new\n"
                "  let addr := Std.Net.SocketAddress.v4 (Std.Net.SocketAddressV4.mk (Std.Net.IPv4Addr.ofParts 127 0 0 1) 0)\n"
                "  sock.bind addr\n"
            ),
        }

        per_vector_results = {}
        for vname, vcode in individual_vectors.items():
            vfile = src_dir / f"{vname}.lean"
            vout = out_dir / f"{vname}.olean"
            vfile.write_text(vcode)
            if vout.exists():
                vout.unlink()
            rc_l, out_l, err_l, _ = run_cmd_landlock(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(vout), str(vfile)],
                cwd=deps_dir,
                env=base_env,
                ro_dirs=ro_dirs,
                ro_files=ro_files,
                rw_dirs=rw_dirs,
            )
            l_emitted = vout.exists()
            if vout.exists():
                vout.unlink()
            rc_b, out_b, err_b, _ = run_cmd_bwrap(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(vout), str(vfile)],
                cwd=deps_dir,
                env=base_env,
                ro_dirs=ro_dirs,
                ro_files=ro_files,
                rw_dirs=rw_dirs,
            )
            b_emitted = vout.exists()
            if vout.exists():
                vout.unlink()
            per_vector_results[vname] = {
                "landlock_seccomp": {
                    "exit_code": rc_l,
                    "output": (out_l + err_l).strip(),
                    "olean_emitted": l_emitted,
                },
                "bwrap": {
                    "exit_code": rc_b,
                    "output": (out_b + err_b).strip(),
                    "olean_emitted": b_emitted,
                },
            }

        # 4. Benchmark GoodTheory.lean compilation across 4 modes (2 warmup + 20 timed runs)
        good_lean = src_dir / "GoodTheory.lean"
        good_olean = out_dir / "GoodTheory.olean"
        n_warmup = 2
        n_iters = 20

        timings: dict[str, list[float]] = {
            "unsandboxed": [],
            "landlock_seccomp": [],
            "bwrap": [],
            "unshare": [],
        }
        good_hashes: dict[str, str] = {}

        for i in range(n_warmup + n_iters):
            if good_olean.exists():
                good_olean.unlink()
            rc, out, err, ms = run_cmd_unsandboxed(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(good_olean), str(good_lean)],
                cwd=deps_dir,
                env=base_env,
            )
            assert rc == 0, f"unsandboxed GoodTheory failed: {out} {err}"
            if i >= n_warmup:
                timings["unsandboxed"].append(ms)
            if i == n_warmup:
                good_hashes["unsandboxed"] = sha256_file(good_olean)

            if good_olean.exists():
                good_olean.unlink()
            rc, out, err, ms = run_cmd_landlock(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(good_olean), str(good_lean)],
                cwd=deps_dir,
                env=base_env,
                ro_dirs=ro_dirs,
                ro_files=ro_files,
                rw_dirs=rw_dirs,
            )
            assert rc == 0, f"landlock GoodTheory failed: {out} {err}"
            if i >= n_warmup:
                timings["landlock_seccomp"].append(ms)
            if i == n_warmup:
                good_hashes["landlock_seccomp"] = sha256_file(good_olean)

            if good_olean.exists():
                good_olean.unlink()
            rc, out, err, ms = run_cmd_bwrap(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(good_olean), str(good_lean)],
                cwd=deps_dir,
                env=base_env,
                ro_dirs=ro_dirs,
                ro_files=ro_files,
                rw_dirs=rw_dirs,
            )
            assert rc == 0, f"bwrap GoodTheory failed: {out} {err}"
            if i >= n_warmup:
                timings["bwrap"].append(ms)
            if i == n_warmup:
                good_hashes["bwrap"] = sha256_file(good_olean)

            if good_olean.exists():
                good_olean.unlink()
            rc, out, err, ms = run_cmd_unshare(
                [str(LEAN_BIN), "-R", str(src_dir), "-o", str(good_olean), str(good_lean)],
                cwd=deps_dir,
                env=base_env,
            )
            assert rc == 0, f"unshare GoodTheory failed: {out} {err}"
            if i >= n_warmup:
                timings["unshare"].append(ms)
            if i == n_warmup:
                good_hashes["unshare"] = sha256_file(good_olean)

        def summarize(vals: list[float]) -> dict[str, float]:
            return {
                "mean_ms": round(statistics.mean(vals), 3),
                "median_ms": round(statistics.median(vals), 3),
                "min_ms": round(min(vals), 3),
                "max_ms": round(max(vals), 3),
                "stdev_ms": round(statistics.stdev(vals), 3),
            }

        summary = {
            "host_kernel": os.uname().release,
            "landlock_abi_version": abi_ver,
            "lean_binary": str(LEAN_BIN),
            "lean_sha256": sha256_file(LEAN_BIN),
            "trusted_olean_sha256_before": trusted_sha_before,
            "combined_evil_theory": {
                "landlock_seccomp": {
                    "exit_code": ll_rc,
                    "output": (ll_out + ll_err).strip(),
                    "trusted_olean_sha256_after": ll_trusted_sha_after,
                    "trusted_olean_intact": ll_trusted_sha_after == trusted_sha_before,
                    "tmp_pwned_created": ll_pwn_created,
                    "evil_olean_emitted": evil_olean.exists(),
                    "elapsed_ms": round(ll_ms, 3),
                },
                "bwrap": {
                    "exit_code": bw_rc,
                    "output": (bw_out + bw_err).strip(),
                    "trusted_olean_sha256_after": bw_trusted_sha_after,
                    "trusted_olean_intact": bw_trusted_sha_after == trusted_sha_before,
                    "tmp_pwned_created": bw_pwn_created,
                    "evil_olean_emitted": evil_olean.exists(),
                    "elapsed_ms": round(bw_ms, 3),
                },
            },
            "per_vector_isolated_results": per_vector_results,
            "good_theory_benchmark_n20": {
                mode: summarize(vals) for mode, vals in timings.items()
            },
            "overhead_vs_unsandboxed_ms": {
                mode: {
                    "mean_delta_ms": round(
                        statistics.mean(timings[mode])
                        - statistics.mean(timings["unsandboxed"]),
                        3,
                    ),
                    "median_delta_ms": round(
                        statistics.median(timings[mode])
                        - statistics.median(timings["unsandboxed"]),
                        3,
                    ),
                }
                for mode in ["landlock_seccomp", "bwrap", "unshare"]
            },
            "good_theory_olean_sha256_by_mode": good_hashes,
            "bit_identical_output_across_all_modes": len(set(good_hashes.values())) == 1,
        }

        out_json = json.dumps(summary, indent=2)
        (PROBES_DIR / "linux_sandbox_results.json").write_text(out_json + "\n")
        print(out_json)


if __name__ == "__main__":
    main()
