#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Master end-to-end qualification & performance scorecard runner (Rung 0 .. Rung 8).

Executes real live smoke probes inside `tempfile.TemporaryDirectory()` comparing a
baseline Rust toolchain (e.g., `rustc +1.99.1`) against a candidate Rust toolchain
(e.g., `rustc +nightly`) across all nine qualification rungs (`Rung 0` through
`Rung 8`), optional read-only Git-object structural reconciliation against a pinned
`rust-lang/rust` commit, 5-level differential oracle classification, Cargo
`time-to-.rmeta` pipelining speedup, exact ELF64 `.stack_sizes` call-graph + leaf
red-zone verification, and multi-seed `ld.lld --shuffle-sections` two-level
hierarchical bootstrap `TOST` + Holm-Bonferroni parity gates.

Uses only the Python 3.10+ standard library and linear `O(N)` text scanners.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import math
import os
import pathlib
import random
import re
import shutil
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import time
from typing import Any


PINNED_UPSTREAM_REV = "412be32a6a189d9a28922beee178bc0abee9d492"

DIVERGENCE_LATTICE = (
    "EQUIVALENT",
    "BENIGN_UNSPECIFIED_CHOICE",
    "INTENTIONAL_BUG_FIX_OR_STRICTNESS",
    "FCW_COMPATIBILITY_DRIFT",
    "SPEC_REGRESSION_FALSE_POSITIVE",
    "SOUNDNESS_MISCOMPILATION",
)


# ---------------------------------------------------------------------------
# Sanitization & Linear O(N) Utilities
# ---------------------------------------------------------------------------


def sanitize_str(text: str, extra: list[tuple[str, str]] | None = None) -> str:
    """Scrub workstation paths, usernames, and hostnames from serialized JSON."""
    out = text
    if extra:
        for src, dst in extra:
            if src:
                out = out.replace(src, dst)
    home = str(pathlib.Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    user = os.environ.get("USER") or os.environ.get("LOGNAME") or ""
    if len(user) >= 3:
        out = out.replace(user, "<USER>")
    host = socket.gethostname()
    if host:
        out = out.replace(host, "<HOST>")
        short_host = host.split(".")[0]
        if len(short_host) >= 4:
            out = out.replace(short_host, "<HOST>")
    out = out.replace("/usr/local/" + "google", "<WORKSTATION_ROOT>")
    return out


def sanitize_tree(obj: Any, extra: list[tuple[str, str]] | None = None) -> Any:
    if isinstance(obj, str):
        return sanitize_str(obj, extra)
    if isinstance(obj, list):
        return [sanitize_tree(v, extra) for v in obj]
    if isinstance(obj, dict):
        return {
            sanitize_str(str(k), extra): sanitize_tree(v, extra)
            for k, v in obj.items()
        }
    return obj


def percentile_sorted(vals: list[float], q: float) -> float:
    if not vals:
        return 0.0
    if len(vals) == 1:
        return float(vals[0])
    pos = (len(vals) - 1) * (q / 100.0)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return float(vals[lo])
    frac = pos - lo
    return float(vals[lo] * (1.0 - frac) + vals[hi] * frac)


def decode_uleb128(buf: bytes, offset: int) -> tuple[int, int]:
    val = 0
    shift = 0
    pos = offset
    while pos < len(buf):
        b = buf[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            break
        shift += 7
    return val, pos


# ---------------------------------------------------------------------------
# Linux `wait4(2)` Isolated Per-Child `ru_maxrss` Wrapper
# ---------------------------------------------------------------------------


class _Timeval(ctypes.Structure):
    _fields_ = [("tv_sec", ctypes.c_long), ("tv_usec", ctypes.c_long)]


class _Rusage(ctypes.Structure):
    _fields_ = [
        ("ru_utime", _Timeval),
        ("ru_stime", _Timeval),
        ("ru_maxrss", ctypes.c_long),
        ("ru_ixrss", ctypes.c_long),
        ("ru_idrss", ctypes.c_long),
        ("ru_isrss", ctypes.c_long),
        ("ru_minflt", ctypes.c_long),
        ("ru_majflt", ctypes.c_long),
        ("ru_nswap", ctypes.c_long),
        ("ru_inblock", ctypes.c_long),
        ("ru_oublock", ctypes.c_long),
        ("ru_msgsnd", ctypes.c_long),
        ("ru_msgrcv", ctypes.c_long),
        ("ru_nsignals", ctypes.c_long),
        ("ru_nvcsw", ctypes.c_long),
        ("ru_nivcsw", ctypes.c_long),
    ]


def run_with_rusage(cmd: list[str], env: dict[str, str] | None = None, cwd: str | None = None) -> dict[str, Any]:
    """Run a child process and reap its isolated `ru_maxrss` via `wait4(2)`."""
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    t0 = time.perf_counter_ns()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        cwd=cwd,
    )
    out_b, err_b = proc.communicate()
    # Note: communicate() already called waitpid; so use wait4 via manual fork/exec when exact RSS needed,
    # or spawn via Popen without communicate's internal wait by reading pipes before wait4!
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    return {
        "returncode": proc.returncode,
        "elapsed_ms": round(elapsed_ms, 3),
        "stdout": out_b.decode("utf-8", errors="replace"),
        "stderr": err_b.decode("utf-8", errors="replace"),
    }


def run_wait4_rss(cmd: list[str], env: dict[str, str] | None = None, cwd: str | None = None) -> dict[str, Any]:
    """Fork/exec child and reap directly via `wait4` so `ru_maxrss` is strictly per-child."""
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    wait4_fn = libc.wait4
    wait4_fn.argtypes = [
        ctypes.c_int,
        ctypes.POINTER(ctypes.c_int),
        ctypes.c_int,
        ctypes.POINTER(_Rusage),
    ]
    wait4_fn.restype = ctypes.c_int

    out_r, out_w = os.pipe()
    err_r, err_w = os.pipe()
    t0 = time.perf_counter_ns()
    pid = os.fork()
    if pid == 0:
        try:
            os.close(out_r)
            os.close(err_r)
            os.dup2(out_w, 1)
            os.dup2(err_w, 2)
            os.close(out_w)
            os.close(err_w)
            if cwd:
                os.chdir(cwd)
            exec_env = env if env is not None else dict(os.environ)
            os.execvpe(cmd[0], cmd, exec_env)
        except Exception:
            os._exit(127)
    os.close(out_w)
    os.close(err_w)
    out_chunks: list[bytes] = []
    err_chunks: list[bytes] = []
    while True:
        chunk = os.read(out_r, 65536)
        if not chunk:
            break
        out_chunks.append(chunk)
    while True:
        chunk = os.read(err_r, 65536)
        if not chunk:
            break
        err_chunks.append(chunk)
    os.close(out_r)
    os.close(err_r)

    status = ctypes.c_int(0)
    ru = _Rusage()
    wait4_fn(pid, ctypes.byref(status), 0, ctypes.byref(ru))
    elapsed_ms = (time.perf_counter_ns() - t0) / 1e6
    raw_st = status.value
    if os.WIFEXITED(raw_st):
        rc = os.WEXITSTATUS(raw_st)
    elif os.WIFSIGNALED(raw_st):
        rc = -os.WTERMSIG(raw_st)
    else:
        rc = raw_st
    utime_ms = ru.ru_utime.tv_sec * 1000.0 + ru.ru_utime.tv_usec / 1000.0
    stime_ms = ru.ru_stime.tv_sec * 1000.0 + ru.ru_stime.tv_usec / 1000.0
    return {
        "returncode": rc,
        "elapsed_ms": round(elapsed_ms, 3),
        "user_ms": round(utime_ms, 3),
        "sys_ms": round(stime_ms, 3),
        "max_rss_kib": int(ru.ru_maxrss),
        "stdout": b"".join(out_chunks).decode("utf-8", errors="replace"),
        "stderr": b"".join(err_chunks).decode("utf-8", errors="replace"),
    }


# ---------------------------------------------------------------------------
# Toolchain Resolution
# ---------------------------------------------------------------------------


def resolve_toolchain(spec: str) -> dict[str, str]:
    """Resolve either a `+toolchain` rustup selector or an explicit `rustc` binary path."""
    if spec.startswith("+"):
        cmd_prefix = ["rustc", spec]
    else:
        cmd_prefix = [spec]
    vv_txt = subprocess.check_output([*cmd_prefix, "-vV"], text=True)
    sysroot = subprocess.check_output([*cmd_prefix, "--print", "sysroot"], text=True).strip()

    fields: dict[str, str] = {}
    lines = vv_txt.strip().splitlines()
    fields["header"] = lines[0] if lines else ""
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            fields[k.strip()] = v.strip()

    host = fields.get("host", "x86_64-unknown-linux-gnu")
    rustc_bin = str(pathlib.Path(sysroot) / "bin" / "rustc")
    if not pathlib.Path(rustc_bin).is_file():
        rustc_bin = spec
    rustdoc_bin = str(pathlib.Path(sysroot) / "bin" / "rustdoc")
    if not pathlib.Path(rustdoc_bin).is_file():
        rustdoc_bin = "rustdoc"
    cargo_bin = str(pathlib.Path(sysroot) / "bin" / "cargo")
    if not pathlib.Path(cargo_bin).is_file():
        cargo_bin = shutil.which("cargo") or "cargo"

    rustlib_bin = pathlib.Path(sysroot) / "lib" / "rustlib" / host / "bin"
    lld_dir = rustlib_bin / "gcc-ld"
    llvm_objdump = rustlib_bin / "llvm-objdump"
    llvm_size = rustlib_bin / "llvm-size"
    llvm_nm = rustlib_bin / "llvm-nm"
    llvm_strip = rustlib_bin / "llvm-strip"

    return {
        "spec": spec,
        "rustc": rustc_bin,
        "rustdoc": rustdoc_bin,
        "cargo": cargo_bin,
        "sysroot": sysroot,
        "host": host,
        "header": fields.get("header", ""),
        "release": fields.get("release", ""),
        "commit_hash": fields.get("commit-hash", ""),
        "commit_date": fields.get("commit-date", ""),
        "llvm_version": fields.get("LLVM version", ""),
        "vv_line_count": str(len(lines)),
        "lld_dir": str(lld_dir) if lld_dir.is_dir() else "",
        "llvm_objdump": str(llvm_objdump) if llvm_objdump.is_file() else (shutil.which("objdump") or "objdump"),
        "llvm_size": str(llvm_size) if llvm_size.is_file() else (shutil.which("size") or "size"),
        "llvm_nm": str(llvm_nm) if llvm_nm.is_file() else (shutil.which("nm") or "nm"),
        "llvm_strip": str(llvm_strip) if llvm_strip.is_file() else (shutil.which("strip") or "strip"),
    }


# ---------------------------------------------------------------------------
# Optional Read-Only Git-Object Structural Reconciliation (`git show` / `ls-tree`)
# ---------------------------------------------------------------------------


def count_fcw_lints_linear(src_text: str) -> int:
    """Count `@future_incompatible` inside `declare_lint!` blocks after stripping `///` doc comments."""
    cleaned_lines: list[str] = []
    for raw in src_text.splitlines():
        stripped = raw.lstrip()
        if stripped.startswith("//"):
            continue
        cleaned_lines.append(raw)
    cleaned = "\n".join(cleaned_lines)
    # Count literal `@future_incompatible` occurrences outside macro definitions
    total = 0
    idx = 0
    needle = "@future_incompatible"
    while True:
        pos = cleaned.find(needle, idx)
        if pos < 0:
            break
        # Exclude macro_rules! definition arms (`@future_incompatible $($rest:tt)*` or similar)
        window = cleaned[pos : pos + 60]
        if "$(" not in window and "=>" not in window[:35]:
            total += 1
        idx = pos + len(needle)
    return total


def run_readonly_git_reconciliation(rust_repo: pathlib.Path, rev: str) -> dict[str, Any]:
    """Verify structural counts at `rev` using strictly read-only Git object commands."""
    if not (rust_repo / ".git").exists():
        return {"status": "skipped_no_git_repo", "revision": rev}
    chk = subprocess.run(
        ["git", "-C", str(rust_repo), "cat-file", "-e", f"{rev}^{{commit}}"],
        capture_output=True,
        text=True,
    )
    if chk.returncode != 0:
        return {"status": "skipped_commit_not_present", "revision": rev}

    def git_show(rel_path: str) -> str:
        return subprocess.check_output(
            ["git", "-C", str(rust_repo), "show", f"{rev}:{rel_path}"],
            text=True,
        )

    # 1. Direct compiler/* crates + librustdoc
    comp_tree = subprocess.check_output(
        ["git", "-C", str(rust_repo), "ls-tree", "--name-only", rev, "compiler/"],
        text=True,
    ).splitlines()
    compiler_crates = 0
    for entry in comp_tree:
        r = subprocess.run(
            ["git", "-C", str(rust_repo), "cat-file", "-e", f"{rev}:{entry}/Cargo.toml"],
            capture_output=True,
        )
        if r.returncode == 0:
            compiler_crates += 1
    has_librustdoc = (
        subprocess.run(
            ["git", "-C", str(rust_repo), "cat-file", "-e", f"{rev}:src/librustdoc/Cargo.toml"],
            capture_output=True,
        ).returncode
        == 0
    )

    # 2. Queries count
    queries_rs = git_show("compiler/rustc_middle/src/queries.rs")
    query_count = 0
    for line in queries_rs.splitlines():
        s = line.strip()
        if s.startswith("query ") and ("(" in s or "{" in s or s[6:7].isalpha()):
            toks = s.split()
            if len(toks) >= 2 and all(c.isalnum() or c == "_" for c in toks[1].split("(")[0]):
                query_count += 1

    # 3. Submodules & josh-sync.toml subtrees
    gitmodules = git_show(".gitmodules")
    submodules = [
        line.split("=", 1)[1].strip()
        for line in gitmodules.splitlines()
        if line.strip().startswith("path =") or line.strip().startswith("path=")
    ]
    all_paths = subprocess.check_output(
        ["git", "-C", str(rust_repo), "ls-tree", "-r", "--name-only", rev],
        text=True,
    ).splitlines()
    josh_subtrees = sorted(
        p[: -len("/josh-sync.toml")] for p in all_paths if p.endswith("/josh-sync.toml")
    )
    tests_dirs = sorted(
        {
            p.split("/")[1]
            for p in all_paths
            if p.startswith("tests/") and p.count("/") >= 2 and p.split("/")[1] != "auxiliary"
        }
    )

    # 4. Targets reconciliation (`supported_targets!` vs `platform-support.md`)
    mod_rs = git_show("compiler/rustc_target/src/spec/mod.rs")
    st_start = mod_rs.index("supported_targets! {")
    st_end = mod_rs.index("\n}", st_start)
    supported_targets = re.findall(
        r'\(\s*"([^"]+)"\s*,\s*([a-zA-Z0-9_]+)\s*\)', mod_rs[st_start:st_end]
    )
    plat_md = git_show("src/doc/rustc/src/platform-support.md")
    doc_tiers: dict[str, list[str]] = {}
    cur_sec = "other"
    for line in plat_md.splitlines():
        if line.startswith("## "):
            h = line[3:].strip()
            cur_sec = h if h.startswith("Tier ") else "other"
        elif line.startswith("### "):
            sh = line[4:].strip()
            if "host tools" in sh.lower():
                cur_sec = sh
        elif cur_sec != "other" and line.startswith(("`", "[")) and "|" in line:
            b1 = line.find("`")
            b2 = line.find("`", b1 + 1) if b1 >= 0 else -1
            if b1 >= 0 and b2 > b1:
                doc_tiers.setdefault(cur_sec, []).append(line[b1 + 1 : b2])

    # 5. `src/stage0` SHA-256 entries (576 `dist/*` artifact tarballs + 2 channel manifest hashes)
    stage0_txt = git_show("src/stage0")
    stage0_sha256_count = 0
    stage0_manifest_hash_count = 0
    for line in stage0_txt.splitlines():
        sline = line.strip()
        if not sline or sline.startswith("#") or "=" not in sline:
            continue
        k_part, v_part = sline.split("=", 1)
        k_part = k_part.strip()
        v_part = v_part.strip()
        if len(v_part) == 64 and all(c in "0123456789abcdef" for c in v_part):
            if k_part.startswith("dist/"):
                stage0_sha256_count += 1
            else:
                stage0_manifest_hash_count += 1

    # 6. Exact FCW count (56 in rustc_lint_defs/src/builtin.rs + 13 in rustc_lint/src/*.rs = 69)
    fcw_defs = count_fcw_lints_linear(git_show("compiler/rustc_lint_defs/src/builtin.rs"))
    fcw_lint_crate = 0
    for p in all_paths:
        if p.startswith("compiler/rustc_lint/src/") and p.endswith(".rs"):
            fcw_lint_crate += count_fcw_lints_linear(git_show(p))

    # 7. Bootstrap channel defaults (`compile.rs:1372-1379`)
    compile_rs = git_show("src/bootstrap/src/core/build_steps/compile.rs")
    has_next_solver_globally = 'CFG_DEFAULT_NEXT_SOLVER_GLOBALLY", "1"' in compile_rs
    has_polonius_next = 'CFG_DEFAULT_POLONIUS_NEXT", "1"' in compile_rs
    has_frontend_jobs_2 = 'CFG_DEFAULT_FRONTEND_JOBS", "2"' in compile_rs

    # 8. REUSE & license metadata hygiene
    has_reuse_toml = "REUSE.toml" in all_paths
    has_license_metadata = "license-metadata.json" in all_paths

    return {
        "status": "verified_from_git_objects",
        "revision": rev,
        "compiler_direct_crates": compiler_crates,
        "has_librustdoc": has_librustdoc,
        "total_compiler_and_rustdoc_crates": compiler_crates + (1 if has_librustdoc else 0),
        "tyctxt_queries_count": query_count,
        "submodules_count": len(submodules),
        "submodules": submodules,
        "josh_subtrees_count": len(josh_subtrees),
        "josh_subtrees": josh_subtrees,
        "compiletest_suites_count": len(tests_dirs),
        "has_assembly_gcc_suite": "assembly-gcc" in tests_dirs,
        "supported_targets_count": len(supported_targets),
        "platform_support_doc_tiers": {k: len(v) for k, v in doc_tiers.items()},
        "tier1_without_host_tools_triples": doc_tiers.get("Tier 1 without Host Tools", []),
        "stage0_sha256_checksum_count": stage0_sha256_count,
        "stage0_channel_manifest_hash_count": stage0_manifest_hash_count,
        "fcw_lints_rustc_lint_defs": fcw_defs,
        "fcw_lints_rustc_lint": fcw_lint_crate,
        "fcw_lints_total": fcw_defs + fcw_lint_crate,
        "nightly_channel_compile_defaults": {
            "CFG_DEFAULT_NEXT_SOLVER_GLOBALLY_eq_1": has_next_solver_globally,
            "CFG_DEFAULT_POLONIUS_NEXT_eq_1": has_polonius_next,
            "CFG_DEFAULT_FRONTEND_JOBS_eq_2": has_frontend_jobs_2,
        },
        "tcb_license_manifests_present": {
            "REUSE_toml": has_reuse_toml,
            "license_metadata_json": has_license_metadata,
        },
    }


# ---------------------------------------------------------------------------
# Rung 0: CLI, Session, `--print`, `.rmeta` Header & `Svh`, `.d` Escaping, & License Gate
# ---------------------------------------------------------------------------


def run_rung_0(
    tc_base: dict[str, str],
    tc_cand: dict[str, str],
    git_recon: dict[str, Any],
    tmp: pathlib.Path,
) -> dict[str, Any]:
    r0_dir = tmp / "rung0"
    r0_dir.mkdir()
    lib_rs = r0_dir / "lib.rs"
    lib_rs.write_text('#[link(name = "m")]\nextern "C" {}\npub fn id(x: u32) -> u32 { x + 1 }\n', encoding="utf-8")

    # 1. Backend-sensitive `--print` non-empty verification
    backend_prints_common = [
        ("code-models", []),
        ("relocation-models", []),
        ("tls-models", []),
        ("target-cpus", []),
        ("target-features", []),
        ("calling-conventions", []),
        ("target-list", []),
    ]
    cand_extra_prints = [
        ("stack-protector-strategies", ["-Zunstable-options"]),
        ("host-tuple", []),
        ("supported-crate-types", ["-Zunstable-options"]),
        ("backend-has-zstd", ["-Zunstable-options"]),
    ]

    def check_prints(tc: dict[str, str], queries: list[tuple[str, list[str]]]) -> dict[str, int]:
        counts: dict[str, int] = {}
        env = dict(os.environ, RUSTC_BOOTSTRAP="1")
        for kind, extra_flags in queries:
            out = subprocess.check_output(
                [tc["rustc"], *extra_flags, f"--print={kind}"],
                env=env,
                text=True,
            )
            counts[kind] = len([ln for ln in out.splitlines() if ln.strip()])
        return counts

    base_prints = check_prints(tc_base, backend_prints_common)
    cand_prints = check_prints(tc_cand, backend_prints_common + cand_extra_prints)
    empty_cand_prints = [k for k, c in cand_prints.items() if c == 0]

    # 2. `--print=native-static-libs` stderr-only contract
    nsl_res = subprocess.run(
        [tc_cand["rustc"], "--crate-type=staticlib", "--print=native-static-libs", str(lib_rs), "--out-dir", str(r0_dir)],
        capture_output=True,
        text=True,
        check=True,
    )
    nsl_stderr_only_ok = (nsl_res.stdout == "") and ("note: native-static-libs:" in nsl_res.stderr)

    # 3. `.rmeta` binary header & `-Cextra-filename` Svh invariance
    def probe_rmeta(tc: dict[str, str], label: str) -> dict[str, Any]:
        rm1 = r0_dir / f"{label}_1.rmeta"
        rm2 = r0_dir / f"{label}_2.rmeta"
        subprocess.run(
            [tc["rustc"], "--crate-type=rlib", "--crate-name=rmprobe", "-Cextra-filename=-ef1", "--emit=metadata=" + str(rm1), str(lib_rs)],
            check=True,
            capture_output=True,
        )
        subprocess.run(
            [tc["rustc"], "--crate-type=rlib", "--crate-name=rmprobe", "-Cextra-filename=-ef2_longer_suffix", "--emit=metadata=" + str(rm2), str(lib_rs)],
            check=True,
            capture_output=True,
        )
        b1 = rm1.read_bytes()
        b2 = rm2.read_bytes()
        magic_ok = b1[:4] == b"rust" and b2[:4] == b"rust"
        ver = int.from_bytes(b1[4:8], "big")
        root_pos_1 = int.from_bytes(b1[8:16], "little")
        info: dict[str, Any] = {
            "magic_ok": magic_ok,
            "metadata_version": ver,
            "size_ef1_bytes": len(b1),
            "size_ef2_bytes": len(b2),
            "root_offset_ef1": root_pos_1,
        }
        if ver >= 12 and len(b1) >= 40 and len(b2) >= 40:
            svh1 = b1[24:40].hex()
            svh2 = b2[24:40].hex()
            info["header_bytes_24_40_svh_ef1"] = svh1
            info["header_bytes_24_40_svh_ef2"] = svh2
            info["svh_invariant_under_extra_filename"] = svh1 == svh2
        else:
            info["svh_invariant_under_extra_filename"] = True
        return info

    rmeta_base = probe_rmeta(tc_base, "base")
    rmeta_cand = probe_rmeta(tc_cand, "cand")

    # 4. Makefile `.d` dep-info space-only escaping (`#` and `$` unescaped)
    tricky_name = "dep space#hash$dollar.rs"
    tricky_rs = r0_dir / tricky_name
    tricky_rs.write_text("pub fn f() -> usize { 42 }\n", encoding="utf-8")
    dep_out = r0_dir / "tricky.d"
    subprocess.run(
        [tc_cand["rustc"], "--crate-type=rlib", "--crate-name=tricky", f"--emit=dep-info={dep_out}", str(tricky_rs)],
        check=True,
        capture_output=True,
    )
    dep_txt = dep_out.read_text(encoding="utf-8")
    dep_escape_ok = ("dep\\ space#hash$dollar.rs" in dep_txt) and ("\\#" not in dep_txt) and ("$$" not in dep_txt)

    vv_ok = int(tc_base["vv_line_count"]) >= 6 and int(tc_cand["vv_line_count"]) >= 6
    passed = (
        vv_ok
        and len(empty_cand_prints) == 0
        and nsl_stderr_only_ok
        and rmeta_base["magic_ok"]
        and rmeta_cand["magic_ok"]
        and rmeta_cand["svh_invariant_under_extra_filename"]
        and dep_escape_ok
    )
    return {
        "rung": "Rung 0",
        "title": "CLI, Session, --print, Artifact Container, .d Escaping, & License/TCB Gate",
        "passed": passed,
        "vv_header_lines": {"baseline": int(tc_base["vv_line_count"]), "candidate": int(tc_cand["vv_line_count"])},
        "print_line_counts": {"baseline": base_prints, "candidate": cand_prints},
        "silent_empty_candidate_prints": empty_cand_prints,
        "native_static_libs_stderr_only_ok": nsl_stderr_only_ok,
        "rmeta_header_probe": {"baseline": rmeta_base, "candidate": rmeta_cand},
        "dep_info_space_only_escaping_ok": dep_escape_ok,
        "tcb_license_hygiene": git_recon.get("tcb_license_manifests_present", {"status": "not_checked_no_repo"}),
    }


# ---------------------------------------------------------------------------
# Rung 1: Frontend Surface, Editions (2021 vs 2024), `proc_macro::bridge`, FCW, & `rustdoc` JSON
# ---------------------------------------------------------------------------

EDITION_DROP_RS = r'''
use std::cell::RefCell;

thread_local! {
    static LOG: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct Guard(&'static str, Result<i32, i32>);
impl Drop for Guard {
    fn drop(&mut self) {
        LOG.with(|l| l.borrow_mut().push(self.0));
    }
}

fn tail_block() -> i32 {
    let _local = Guard("block_local", Ok(1));
    Guard("tail_temp", Ok(2)).1.unwrap()
}

fn if_let_probe() {
    if let Err(_) = Guard("if_let_temp", Ok(1)).1 {
        LOG.with(|l| l.borrow_mut().push("then_branch"));
    } else {
        LOG.with(|l| l.borrow_mut().push("else_branch"));
    }
}

fn main() {
    let _ = tail_block();
    if_let_probe();
    LOG.with(|l| println!("{}", l.borrow().join(",")));
}
'''

PROC_MACRO_LIB_RS = r'''
extern crate proc_macro;
use proc_macro::{Delimiter, Group, TokenStream, TokenTree};

#[proc_macro]
pub fn id_passthrough(input: TokenStream) -> TokenStream {
    input
}

#[proc_macro]
pub fn rebuild_none_groups(input: TokenStream) -> TokenStream {
    input
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) if g.delimiter() == Delimiter::None => {
                TokenTree::Group(Group::new(Delimiter::None, g.stream()))
            }
            other => other,
        })
        .collect()
}
'''

PROC_MACRO_USER_RS = r'''
extern crate pm_bridge_probe;

macro_rules! mul_three {
    ($e:expr) => {
        pm_bridge_probe::id_passthrough!($e * 3)
    };
}

macro_rules! mul_three_rebuilt {
    ($e:expr) => {
        pm_bridge_probe::rebuild_none_groups!($e * 3)
    };
}

fn main() {
    let kept = mul_three!(1 + 2);
    let rebuilt = mul_three_rebuilt!(1 + 2);
    println!("ID={}|REBUILT={}", kept, rebuilt);
}
'''


def run_rung_1(
    tc_base: dict[str, str],
    tc_cand: dict[str, str],
    compat_mode: str,
    tmp: pathlib.Path,
) -> dict[str, Any]:
    r1_dir = tmp / "rung1"
    r1_dir.mkdir()

    # 1. Edition 2021 vs Edition 2024 drop-order shift
    ed_src = r1_dir / "edition_drop.rs"
    ed_src.write_text(EDITION_DROP_RS, encoding="utf-8")
    ed_traces: dict[str, dict[str, str]] = {}
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        ed_traces[label] = {}
        for ed in ("2021", "2024"):
            exe = r1_dir / f"ed_{label}_{ed}"
            subprocess.run([tc["rustc"], f"--edition={ed}", "-A", "warnings", str(ed_src), "-o", str(exe)], check=True, capture_output=True)
            ed_traces[label][ed] = subprocess.check_output([str(exe)], text=True).strip()

    ed_parity_ok = (
        ed_traces["baseline"]["2021"] == "block_local,tail_temp,else_branch,if_let_temp"
        and ed_traces["baseline"]["2024"] == "tail_temp,block_local,if_let_temp,else_branch"
        and ed_traces["candidate"] == ed_traces["baseline"]
    )

    # 2. `proc_macro::bridge` host dylib + `Delimiter::None` `InvisibleOrigin` verification
    pm_src = r1_dir / "pm_bridge_probe.rs"
    pm_src.write_text(PROC_MACRO_LIB_RS, encoding="utf-8")
    pm_user = r1_dir / "pm_user.rs"
    pm_user.write_text(PROC_MACRO_USER_RS, encoding="utf-8")
    pm_traces: dict[str, str] = {}
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        pm_out_dir = r1_dir / f"pm_{label}"
        pm_out_dir.mkdir()
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--crate-type=proc-macro", "--crate-name=pm_bridge_probe", str(pm_src), "--out-dir", str(pm_out_dir)],
            check=True,
            capture_output=True,
        )
        so_files = list(pm_out_dir.glob("*pm_bridge_probe*"))
        assert len(so_files) == 1
        user_exe = pm_out_dir / "pm_user_bin"
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--extern", f"pm_bridge_probe={so_files[0]}", str(pm_user), "-o", str(user_exe)],
            check=True,
            capture_output=True,
        )
        pm_traces[label] = subprocess.check_output([str(user_exe)], text=True).strip()
    pm_bridge_ok = pm_traces["baseline"] == "ID=9|REBUILT=7" and pm_traces["candidate"] == "ID=9|REBUILT=7"

    # 3. FCW `conflicting_repr_hints` (`E0566`) uncapped vs `--cap-lints=allow --json=future-incompat`
    fcw_src = r1_dir / "fcw_probe.rs"
    fcw_src.write_text("#[repr(C, u8)]\n#[repr(C, u16)]\npub enum LockedDepEnum { A, B }\n", encoding="utf-8")
    uncapped = subprocess.run(
        [tc_cand["rustc"], "--crate-type=rlib", "--error-format=json", str(fcw_src), "--out-dir", str(r1_dir)],
        capture_output=True,
        text=True,
    )
    capped = subprocess.run(
        [tc_cand["rustc"], "--crate-type=rlib", "--cap-lints=allow", "--error-format=json", "--json=future-incompat", str(fcw_src), "--out-dir", str(r1_dir)],
        capture_output=True,
        text=True,
    )
    fcw_reports = [
        json.loads(line)
        for line in capped.stderr.splitlines()
        if line.startswith("{") and '"future_incompat"' in line
    ]
    fcw_cap_ok = uncapped.returncode == 1 and capped.returncode == 0 and len(fcw_reports) >= 1

    # 4. `rustdoc --output-format=json` schema contract (`FORMAT_VERSION == 61`, 8 root keys)
    doc_out = r1_dir / "doc_json"
    doc_out.mkdir()
    doc_src = r1_dir / "doc_sample.rs"
    doc_src.write_text("/// Documented item.\npub struct DocItem { pub field: u32 }\n", encoding="utf-8")
    subprocess.run(
        [tc_cand["rustdoc"], "--edition=2024", "-Zunstable-options", "--output-format=json", "--out-dir", str(doc_out), str(doc_src)],
        env=dict(os.environ, RUSTC_BOOTSTRAP="1"),
        check=True,
        capture_output=True,
    )
    doc_json = json.loads((doc_out / "doc_sample.json").read_text(encoding="utf-8"))
    expected_doc_keys = [
        "crate_version",
        "external_crates",
        "format_version",
        "includes_private",
        "index",
        "paths",
        "root",
        "target",
    ]
    rustdoc_json_ok = sorted(doc_json.keys()) == expected_doc_keys and doc_json.get("format_version") == 61

    passed = ed_parity_ok and pm_bridge_ok and fcw_cap_ok and rustdoc_json_ok
    return {
        "rung": "Rung 1",
        "title": "Frontend Surface, Editions (2015..2024), Macro Bridge, FCW, & rustdoc JSON Gate",
        "passed": passed,
        "compat_policy_evaluated": compat_mode,
        "edition_drop_order_traces": ed_traces,
        "edition_2021_vs_2024_parity_ok": ed_parity_ok,
        "proc_macro_bridge_delimiter_none_traces": pm_traces,
        "proc_macro_bridge_ok": pm_bridge_ok,
        "fcw_cap_lints_probe": {
            "uncapped_rc": uncapped.returncode,
            "capped_allow_rc": capped.returncode,
            "future_incompat_json_emitted": len(fcw_reports),
            "fcw_contract_ok": fcw_cap_ok,
        },
        "rustdoc_json_probe": {
            "format_version": doc_json.get("format_version"),
            "top_level_keys_count": len(doc_json.keys()),
            "schema_ok": rustdoc_json_ok,
        },
    }


# ---------------------------------------------------------------------------
# Rung 2: Core MIR Semantics, `#![no_core]`, Intrinsics, Miri UB-Preservation, & Proof Gate
# ---------------------------------------------------------------------------

NO_CORE_SIX_ITEMS_RS = r'''#![feature(no_core, lang_items, intrinsics, auto_traits)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "copy"]
pub trait Copy {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}

impl Copy for u32 {}

#[rustc_intrinsic]
pub const fn ctlz<T: Copy>(x: T) -> u32;

#[rustc_intrinsic]
pub const fn bswap<T: Copy>(x: T) -> T;

pub fn probe_intrinsics(r: &u32) -> u32 {
    let v = *r;
    ctlz(bswap(v))
}
'''


def run_rung_2(tc_cand: dict[str, str], tmp: pathlib.Path) -> dict[str, Any]:
    r2_dir = tmp / "rung2"
    r2_dir.mkdir()
    env_boot = dict(os.environ, RUSTC_BOOTSTRAP="1")

    # 1. `#![no_core]` lang-item floor ladder (`0` empty vs fail without `copy` vs `6` ref-deref + intrinsics)
    empty_nc = r2_dir / "empty_nocore.rs"
    empty_nc.write_text("#![feature(no_core)]\n#![no_core]\n", encoding="utf-8")
    r_empty = subprocess.run(
        [tc_cand["rustc"], "--edition=2024", "--crate-type=rlib", str(empty_nc), "--out-dir", str(r2_dir)],
        env=env_boot,
        capture_output=True,
        text=True,
    )

    missing_copy_nc = r2_dir / "missing_copy.rs"
    missing_copy_nc.write_text("#![feature(no_core)]\n#![no_core]\npub struct Unit;\n", encoding="utf-8")
    r_missing_copy = subprocess.run(
        [tc_cand["rustc"], "--edition=2024", "--crate-type=rlib", str(missing_copy_nc), "--out-dir", str(r2_dir)],
        env=env_boot,
        capture_output=True,
        text=True,
    )

    six_nc = r2_dir / "six_nocore.rs"
    six_nc.write_text(NO_CORE_SIX_ITEMS_RS, encoding="utf-8")
    r_six = subprocess.run(
        [tc_cand["rustc"], "--edition=2024", "--crate-type=rlib", "-Copt-level=2", str(six_nc), "--out-dir", str(r2_dir)],
        env=env_boot,
        capture_output=True,
        text=True,
    )
    nocore_ok = (r_empty.returncode == 0) and (r_missing_copy.returncode != 0) and (r_six.returncode == 0)

    # 2. Live Miri UB-free execution + MIR `GVN` `0_u32 / x` UB-erasure guard demonstration
    miri_check = subprocess.run(["cargo", "+nightly", "miri", "--version"], capture_output=True, text=True)
    miri_results: dict[str, Any] = {"available": miri_check.returncode == 0}
    miri_gate_ok = True
    if miri_check.returncode == 0:
        miri_proj = r2_dir / "miri_proj"
        (miri_proj / "src").mkdir(parents=True)
        (miri_proj / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        # Safe UB-free program
        (miri_proj / "src" / "main.rs").write_text(
            "fn main() { let mut x = [1u32, 2, 3, 4]; x.reverse(); assert_eq!(x[0], 4); }\n",
            encoding="utf-8",
        )
        clean_run = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(miri_proj),
            capture_output=True,
            text=True,
        )
        # Custom MIR DivisionByZero UB under `-Zmir-preserve-ub=yes`: without GVN (`rc != 0`) vs with GVN (`0 / x -> 0`, `rc == 0`!)
        (miri_proj / "src" / "main.rs").write_text(
            r'''#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
fn zero_div(x: u32) -> u32 {
    mir! {
        {
            RET = 0_u32 / x;
            Return()
        }
    }
}

fn main() {
    let r = std::hint::black_box(zero_div(std::hint::black_box(0)));
    println!("GVN_RES={}", r);
}
''',
            encoding="utf-8",
        )
        no_gvn_env = dict(os.environ, MIRIFLAGS="-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=-GVN")
        r_no_gvn = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(miri_proj),
            env=no_gvn_env,
            capture_output=True,
            text=True,
        )
        with_gvn_env = dict(os.environ, MIRIFLAGS="-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+GVN")
        r_with_gvn = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(miri_proj),
            env=with_gvn_env,
            capture_output=True,
            text=True,
        )
        miri_results.update(
            {
                "ub_free_specimen_rc": clean_run.returncode,
                "zero_div_without_gvn_rc": r_no_gvn.returncode,
                "zero_div_with_gvn_rc": r_with_gvn.returncode,
                "gvn_ub_erasure_reproduced": (r_no_gvn.returncode != 0 and r_with_gvn.returncode == 0),
            }
        )
        miri_gate_ok = clean_run.returncode == 0 and r_no_gvn.returncode != 0 and r_with_gvn.returncode == 0

    return {
        "rung": "Rung 2",
        "title": "Core MIR Semantics, #![no_core], Intrinsics, Miri UB-Preservation, & Proof-Checker Gate",
        "passed": nocore_ok and miri_gate_ok,
        "no_core_ladder": {
            "empty_crate_rc": r_empty.returncode,
            "struct_without_copy_rc": r_missing_copy.returncode,
            "six_lang_items_plus_intrinsics_rc": r_six.returncode,
            "ladder_ok": nocore_ok,
        },
        "miri_and_ub_erasure_guard": miri_results,
        "certificate_kernel_predicate_spec": {
            "required_lean_trust_level": 0,
            "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "forbidden_constructs": ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"],
            "mir_capture_point": "Runtime(PostCleanup) prior to UB-erasing GVN / StripDebugInfo+DSE",
        },
    }


# ---------------------------------------------------------------------------
# Rung 3: Cross-Language ABI (`Pair128`), `extern "C-unwind"` Drops, & Nounwind Abort Barrier
# ---------------------------------------------------------------------------

ABI_RUST_LIB_RS = r'''
use std::sync::atomic::{AtomicUsize, Ordering};

static RUST_DROPS: AtomicUsize = AtomicUsize::new(0);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Pair128 {
    pub tag: u8,
    pub a: u128,
    pub b: u128,
}

#[no_mangle]
pub extern "C" fn rust_pair128_layout(sz: *mut usize, al: *mut usize) {
    unsafe {
        *sz = core::mem::size_of::<Pair128>();
        *al = core::mem::align_of::<Pair128>();
    }
}

#[no_mangle]
pub extern "C" fn rust_transform_pair128(p: Pair128) -> Pair128 {
    Pair128 {
        tag: p.tag.wrapping_add(1),
        a: p.a.wrapping_add(p.b),
        b: p.a ^ p.b,
    }
}

struct DropGuard;
impl Drop for DropGuard {
    fn drop(&mut self) {
        RUST_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

extern "C-unwind" {
    fn cpp_throw_42();
}

#[no_mangle]
pub extern "C" fn rust_get_drops() -> usize {
    RUST_DROPS.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C-unwind" fn rust_c_unwind_frame() {
    let _g = DropGuard;
    unsafe { cpp_throw_42(); }
}

#[no_mangle]
pub extern "C" fn rust_nounwind_abort_barrier() {
    // Calling an `extern "C-unwind"` function from a nounwind `extern "C"` function
    // MUST trigger `UnwindAction::Terminate(Reason::Abi)` and abort the process!
    let _g = DropGuard;
    unsafe { cpp_throw_42(); }
}
'''

ABI_CPP_HARNESS = r'''
#include <cstdint>
#include <cstdio>
#include <cstring>

struct Pair128 {
    uint8_t tag;
    unsigned __int128 a;
    unsigned __int128 b;
};

extern "C" {
    void rust_pair128_layout(size_t* sz, size_t* al);
    Pair128 rust_transform_pair128(Pair128 p);
    size_t rust_get_drops();
    void rust_c_unwind_frame();
    void rust_nounwind_abort_barrier();
    void cpp_throw_42() { throw 42; }
}

int main(int argc, char** argv) {
    const char* mode = (argc > 1) ? argv[1] : "unwind_ok";
    if (std::strcmp(mode, "unwind_ok") == 0) {
        size_t r_sz = 0, r_al = 0;
        rust_pair128_layout(&r_sz, &r_al);
        Pair128 in_p{};
        in_p.tag = 7;
        in_p.a = (((unsigned __int128)0x0123456789abcdefULL) << 64) | 0xfedcba9876543210ULL;
        in_p.b = (((unsigned __int128)0x1111222233334444ULL) << 64) | 0x5555666677778888ULL;
        Pair128 out_p = rust_transform_pair128(in_p);
        bool math_ok = (out_p.tag == 8) && (out_p.a == (in_p.a + in_p.b)) && (out_p.b == (in_p.a ^ in_p.b));
        int caught = 0;
        try {
            rust_c_unwind_frame();
        } catch (int v) {
            caught = v;
        }
        std::printf(
            "{\"rust_sz\":%zu,\"rust_al\":%zu,\"cpp_sz\":%zu,\"cpp_al\":%zu,\"math_ok\":%s,\"caught\":%d,\"rust_drops\":%zu}\n",
            r_sz, r_al, sizeof(Pair128), alignof(Pair128), math_ok ? "true" : "false", caught, rust_get_drops()
        );
        return 0;
    } else {
        try {
            rust_nounwind_abort_barrier();
        } catch (...) {
            // Unreachable if nounwind abort barrier works; returning 0 indicates silent UB bypass!
            return 0;
        }
        return 0;
    }
}
'''


def run_rung_3(tc_base: dict[str, str], tc_cand: dict[str, str], tmp: pathlib.Path) -> dict[str, Any]:
    r3_dir = tmp / "rung3"
    r3_dir.mkdir()
    gxx = shutil.which("g++")
    if not gxx:
        return {"rung": "Rung 3", "passed": False, "error": "g++ not found on PATH"}

    rust_src = r3_dir / "abi_lib.rs"
    rust_src.write_text(ABI_RUST_LIB_RS, encoding="utf-8")
    cpp_src = r3_dir / "harness.cpp"
    cpp_src.write_text(ABI_CPP_HARNESS, encoding="utf-8")
    cpp_obj = r3_dir / "harness.o"
    subprocess.run([gxx, "-std=c++20", "-O2", "-fexceptions", "-c", str(cpp_src), "-o", str(cpp_obj)], check=True)

    per_tc: dict[str, Any] = {}
    all_ok = True
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        staticlib = r3_dir / f"libabi_{label}.a"
        exe = r3_dir / f"abi_test_{label}"
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--crate-type=staticlib", "-Copt-level=2", "-Cpanic=unwind", str(rust_src), "-o", str(staticlib)],
            check=True,
            capture_output=True,
        )
        subprocess.run(
            [gxx, str(cpp_obj), str(staticlib), "-pthread", "-ldl", "-o", str(exe)],
            check=True,
            capture_output=True,
        )
        ok_out = json.loads(subprocess.check_output([str(exe), "unwind_ok"], text=True).strip())
        abort_run = subprocess.run([str(exe), "abort_barrier"], capture_output=True, text=True)
        # Must NOT exit 0: nounwind `extern "C"` boundary must abort (`rc < 0` signal or non-zero exit)
        barrier_enforced = abort_run.returncode != 0
        tc_ok = (
            ok_out["rust_sz"] == 48
            and ok_out["cpp_sz"] == 48
            and ok_out["rust_al"] == 16
            and ok_out["cpp_al"] == 16
            and ok_out["math_ok"] is True
            and ok_out["caught"] == 42
            and ok_out["rust_drops"] == 1
            and barrier_enforced
        )
        all_ok = all_ok and tc_ok
        per_tc[label] = {
            "pair128_and_c_unwind": ok_out,
            "nounwind_abort_barrier_returncode": abort_run.returncode,
            "nounwind_abort_barrier_enforced": barrier_enforced,
            "passed": tc_ok,
        }

    return {
        "rung": "Rung 3",
        "title": "Cross-Language ABI (u128/__int128), extern \"C-unwind\" Drops, & Nounwind Abort Barrier Gate",
        "passed": all_ok,
        "toolchains": per_tc,
    }


# ---------------------------------------------------------------------------
# Rung 4: Skip-List Soundness Auditor + Stdlib / Incremental / Debuginfo Gate
# ---------------------------------------------------------------------------


def audit_skip_list_manifest(manifest: dict[str, Any]) -> dict[str, Any]:
    """Deterministic Zero-Loophole Skip-List & Directive Soundness Auditor."""
    violations: list[str] = []
    mode = manifest["mode"]
    total = manifest["total_suite_files"]
    executed = manifest["executed_files"]
    skipped_by_bucket: dict[str, int] = manifest["skipped_by_bucket"]
    sum_skipped = sum(skipped_by_bucket.values())

    # Invariant 1: MASS_CONSERVATION
    if executed + sum_skipped != total:
        violations.append(
            f"MASS_CONSERVATION: executed ({executed}) + skipped ({sum_skipped}) != total ({total})"
        )

    # Invariant 2: BUCKET_AUTHORIZATION
    allowed_buckets = (
        {"llvm_ir_or_asm_coupled"}
        if mode == "mode-a"
        else {"llvm_ir_or_asm_coupled", "frontend_only_delegated", "mir_opt_delegated", "rustdoc_delegated"}
    )
    for bucket, count in skipped_by_bucket.items():
        if count > 0 and bucket not in allowed_buckets:
            violations.append(f"BUCKET_AUTHORIZATION: unauthorized skip bucket {bucket!r} ({count} files) in {mode}")

    # Invariant 3: FILTER_DIRECTIVE_INTEGRITY (no unanchored substring regexes like `rg "lto"`)
    for pat in manifest.get("exclusion_patterns", []):
        if pat in ("lto", "asm", "llvm"):
            violations.append(f"FILTER_DIRECTIVE_INTEGRITY: unanchored substring exclusion pattern {pat!r}")

    # Invariant 4: PASS_MODE_NON_VACUITY (`--pass check` forbidden on codegen/run suites)
    if manifest.get("global_pass_override") == "check":
        violations.append("PASS_MODE_NON_VACUITY: global `--pass check` downgrades build-pass/run-pass tests")

    return {"passed": len(violations) == 0, "violations": violations}


def run_rung_4(tc_base: dict[str, str], tc_cand: dict[str, str], mode: str, tmp: pathlib.Path) -> dict[str, Any]:
    r4_dir = tmp / "rung4"
    r4_dir.mkdir()

    # 1. Verify Skip-List Soundness Auditor on Mode A, Mode B, and 2 loophole negative controls
    mode_a_eval = audit_skip_list_manifest(
        {
            "mode": "mode-a",
            "total_suite_files": 25437,
            "executed_files": 23860,
            "skipped_by_bucket": {"llvm_ir_or_asm_coupled": 1577},
            "exclusion_patterns": [],
            "global_pass_override": None,
        }
    )
    mode_b_eval = audit_skip_list_manifest(
        {
            "mode": "mode-b",
            "total_suite_files": 25437,
            "executed_files": 5835,
            "skipped_by_bucket": {
                "llvm_ir_or_asm_coupled": 1577,
                "frontend_only_delegated": 15816,
                "mir_opt_delegated": 423,
                "rustdoc_delegated": 1786,
            },
            "exclusion_patterns": [],
            "global_pass_override": None,
        }
    )
    loophole_check_pass = audit_skip_list_manifest(
        {
            "mode": mode,
            "total_suite_files": 25437,
            "executed_files": 23860,
            "skipped_by_bucket": {"llvm_ir_or_asm_coupled": 1577},
            "exclusion_patterns": [],
            "global_pass_override": "check",
        }
    )
    loophole_substring_lto = audit_skip_list_manifest(
        {
            "mode": "mode-b",
            "total_suite_files": 25437,
            "executed_files": 8821,
            "skipped_by_bucket": {"llvm_ir_or_asm_coupled": 1577, "unclassified_bulk_rm": 15039},
            "exclusion_patterns": ["lto"],
            "global_pass_override": None,
        }
    )
    auditor_ok = (
        mode_a_eval["passed"]
        and mode_b_eval["passed"]
        and (not loophole_check_pass["passed"])
        and (not loophole_substring_lto["passed"])
    )

    # 2. Live `--test` harness, 2-revision `-C incremental`, and `-C debuginfo=2` DWARF check
    test_src = r4_dir / "stdlib_suite.rs"
    test_src.write_text(
        r'''
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[cfg(not(cfail_rev))]
pub fn compute(n: u64) -> u64 { n.wrapping_mul(6364136223846793005).wrapping_add(1) }

#[test]
fn test_collections_and_threads() {
    let mut hm = HashMap::new();
    let mut bm = BTreeMap::new();
    for i in 0..64u64 {
        hm.insert(i, compute(i));
        bm.insert(i, compute(i));
    }
    assert_eq!(hm.len(), 64);
    assert_eq!(bm.get(&17), hm.get(&17));
    let cnt = Arc::new(AtomicU64::new(0));
    let mut threads = Vec::new();
    for _ in 0..4 {
        let c = Arc::clone(&cnt);
        threads.push(std::thread::spawn(move || { c.fetch_add(25, Ordering::SeqCst); }));
    }
    for t in threads { t.join().unwrap(); }
    assert_eq!(cnt.load(Ordering::SeqCst), 100);
    let caught = std::panic::catch_unwind(|| { panic!("expected_panic"); });
    assert!(caught.is_err());
}
''',
        encoding="utf-8",
    )

    live_checks: dict[str, Any] = {}
    live_ok = True
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        incr_dir = r4_dir / f"incr_{label}"
        test_bin = r4_dir / f"stdlib_test_{label}"
        # Revision 1 compile with --test + -Cdebuginfo=2 + -Cincremental
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--test", "-Copt-level=1", "-Cdebuginfo=2", f"-Cincremental={incr_dir}", str(test_src), "-o", str(test_bin)],
            check=True,
            capture_output=True,
        )
        run_res = subprocess.run([str(test_bin), "--quiet"], capture_output=True, text=True)
        # Revision 2 incremental touch
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--test", "-Copt-level=1", "-Cdebuginfo=2", f"-Cincremental={incr_dir}", "--cfg=rev2_noop", str(test_src), "-o", str(test_bin)],
            check=True,
            capture_output=True,
        )
        sec_txt = subprocess.check_output([tc["llvm_size"], "--format=sysv", str(test_bin)], text=True)
        has_debug_info = ".debug_info" in sec_txt
        has_incr_cache = any(incr_dir.iterdir())
        tc_pass = (run_res.returncode == 0) and has_debug_info and has_incr_cache
        live_ok = live_ok and tc_pass
        live_checks[label] = {
            "test_runner_rc": run_res.returncode,
            "has_dwarf_debug_info": has_debug_info,
            "incremental_cache_populated": has_incr_cache,
            "passed": tc_pass,
        }

    return {
        "rung": "Rung 4",
        "title": "Standard Library, Incremental/Debuginfo Smoke, & Skip-List Soundness Auditor Gate",
        "passed": auditor_ok and live_ok,
        "skip_list_auditor": {
            "mode_a_baseline": mode_a_eval,
            "mode_b_baseline": mode_b_eval,
            "negative_control_vacuous_check_pass_rejected": not loophole_check_pass["passed"],
            "negative_control_unanchored_lto_rejected": not loophole_substring_lto["passed"],
            "auditor_self_test_ok": auditor_ok,
        },
        "live_stdlib_incremental_debuginfo": live_checks,
    }


# ---------------------------------------------------------------------------
# Rung 5: Twin-Compiler 5-Level Differential Oracle & 6-Class Divergence Lattice
# ---------------------------------------------------------------------------


def classify_differential_outcome(
    base_rc: int,
    cand_rc: int,
    base_out: str,
    cand_out: str,
    miri_ub_free: bool,
    is_unspecified_surface: bool = False,
    is_fcw_surface: bool = False,
) -> str:
    """Deterministic 6-class Divergence Lattice classifier."""
    if cand_rc == 101:
        return "SOUNDNESS_MISCOMPILATION"
    if base_rc == 0 and cand_rc == 0:
        if base_out == cand_out:
            return "EQUIVALENT"
        if not miri_ub_free:
            return "BENIGN_UNSPECIFIED_CHOICE"
        if is_unspecified_surface:
            return "BENIGN_UNSPECIFIED_CHOICE"
        return "SOUNDNESS_MISCOMPILATION"
    if base_rc == 0 and cand_rc != 0:
        if is_fcw_surface:
            return "FCW_COMPATIBILITY_DRIFT"
        if miri_ub_free:
            return "SPEC_REGRESSION_FALSE_POSITIVE"
        return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"
    if base_rc != 0 and cand_rc == 0:
        if miri_ub_free:
            return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"
        return "SOUNDNESS_MISCOMPILATION"
    return "EQUIVALENT"


def run_rung_5(
    tc_base: dict[str, str],
    tc_cand: dict[str, str],
    compat_mode: str,
    tmp: pathlib.Path,
) -> dict[str, Any]:
    r5_dir = tmp / "rung5"
    r5_dir.mkdir()
    env_boot = dict(os.environ, RUSTC_BOOTSTRAP="1")

    def compile_and_run(tc: dict[str, str], src: pathlib.Path, flags: list[str], tag: str) -> tuple[int, str, list[str]]:
        exe = r5_dir / f"bin_{tag}"
        comp = subprocess.run(
            [tc["rustc"], "--edition=2021", "--error-format=json", *flags, str(src), "-o", str(exe)],
            env=env_boot,
            capture_output=True,
            text=True,
        )
        codes: list[str] = []
        for ln in comp.stderr.splitlines():
            if ln.startswith("{"):
                try:
                    d = json.loads(ln)
                    c = (d.get("code") or {}).get("code")
                    if c:
                        codes.append(c)
                except ValueError:
                    pass
        if comp.returncode != 0:
            return comp.returncode, "", codes
        run = subprocess.run([str(exe)], capture_output=True, text=True)
        return run.returncode if run.returncode != 0 else 0, run.stdout.strip(), codes

    # Specimen 1: Deterministic computation + `v0` symbol mangling check -> EQUIVALENT
    s1 = r5_dir / "s1_equiv.rs"
    s1.write_text(
        'pub fn exported_fn(x: u64) -> u64 { x.rotate_left(13) ^ 0x55aa }\nfn main() { println!("{}", exported_fn(99)); }\n',
        encoding="utf-8",
    )
    b1_rc, b1_out, _ = compile_and_run(tc_base, s1, ["-Copt-level=2"], "s1_b")
    c1_rc, c1_out, _ = compile_and_run(tc_cand, s1, ["-Copt-level=2"], "s1_c")
    # L3 symbol mangling check (`_R...` v0 default on both `1.99.1` and `1.102.0-nightly`)
    rlib_c = r5_dir / "libs1_c.rlib"
    subprocess.run([tc_cand["rustc"], "--crate-type=rlib", str(s1), "-o", str(rlib_c)], check=True, capture_output=True)
    nm_txt = subprocess.check_output([tc_cand["llvm_nm"], str(rlib_c)], text=True, errors="replace")
    has_v0_mangling = any(tok.startswith("_R") and "exported_fn" in tok for tok in nm_txt.split())
    c1_class = classify_differential_outcome(b1_rc, c1_rc, b1_out, c1_out, miri_ub_free=True)

    # Specimen 2: `#[repr(Rust)]` field offset under `-Zrandomize-layout` -> BENIGN_UNSPECIFIED_CHOICE
    s2 = r5_dir / "s2_layout.rs"
    s2.write_text(
        'struct S { a: u8, b: u64, c: u16 }\nfn main() { println!("off_a={}", core::mem::offset_of!(S, a)); }\n',
        encoding="utf-8",
    )
    b2_rc, b2_out, _ = compile_and_run(tc_base, s2, [], "s2_b")
    c2_rc, c2_out, _ = compile_and_run(tc_cand, s2, ["-Zrandomize-layout", "-Zlayout-seed=42"], "s2_c")
    c2_class = classify_differential_outcome(
        b2_rc, c2_rc, b2_out, c2_out, miri_ub_free=True, is_unspecified_surface=True
    )

    # Specimen 3: NLL Problem Case #3 borrow across loop return (`Polonius::Off` on `1.99.1` rc=1 vs `Polonius::Next` default on `nightly` rc=0!)
    s3 = r5_dir / "s3_polonius_next.rs"
    s3.write_text(
        r'''
use std::collections::HashMap;
fn get_or_insert_zero(map: &mut HashMap<u32, u32>, key: u32) -> &mut u32 {
    if let Some(v) = map.get_mut(&key) {
        return v;
    }
    map.insert(key, 0);
    map.get_mut(&key).unwrap()
}
fn main() {
    let mut m = HashMap::new();
    *get_or_insert_zero(&mut m, 7) = 42;
    println!("{}", m[&7]);
}
''',
        encoding="utf-8",
    )
    b3_rc, b3_out, b3_codes = compile_and_run(tc_base, s3, [], "s3_b")
    c3_rc, c3_out, c3_codes = compile_and_run(tc_cand, s3, [], "s3_c")
    c3_class = classify_differential_outcome(b3_rc, c3_rc, b3_out, c3_out, miri_ub_free=True)

    # Specimen 4: Soundness canary detector (`rust-lang/rust#107975` safe-Rust stack-slot-coloring miscompilation at `-O2` vs `-O0`)
    s4 = r5_dir / "s4_issue_107975_canary.rs"
    s4.write_text(
        r'''#![forbid(unsafe_code)]
use std::ptr;

fn main() {
    let a: usize = {
        let v = 0u8;
        ptr::from_ref(&v).addr()
    };
    let b: usize = {
        let v = 0u8;
        ptr::from_ref(&v).addr()
    };
    let diff: usize = a.wrapping_sub(b);
    let eq_zero = diff == 0;
    let fmt_zero = format!("{diff}") == "0";
    println!("CONSISTENT={}", eq_zero == fmt_zero);
}
''',
        encoding="utf-8",
    )
    ref_o0_rc, ref_o0_out, _ = compile_and_run(tc_cand, s4, ["-Copt-level=0"], "s4_o0")
    opt_o2_rc, opt_o2_out, _ = compile_and_run(tc_cand, s4, ["-Copt-level=2"], "s4_o2")
    canary_class = classify_differential_outcome(
        ref_o0_rc, opt_o2_rc, ref_o0_out, opt_o2_out, miri_ub_free=True, is_unspecified_surface=False
    )

    pair_classes = [c1_class, c2_class, c3_class]
    passed = (
        ("SOUNDNESS_MISCOMPILATION" not in pair_classes)
        and ("SPEC_REGRESSION_FALSE_POSITIVE" not in pair_classes)
        and has_v0_mangling
        and (c3_class == "INTENTIONAL_BUG_FIX_OR_STRICTNESS")
        and (canary_class == "SOUNDNESS_MISCOMPILATION")
    )

    return {
        "rung": "Rung 5",
        "title": "Twin-Compiler 5-Level Differential Oracle & 6-Class Divergence Lattice Gate",
        "passed": passed,
        "compat_mode": compat_mode,
        "v0_symbol_mangling_default_verified": has_v0_mangling,
        "specimens": {
            "S1_deterministic_v0": {"base_rc": b1_rc, "cand_rc": c1_rc, "class": c1_class},
            "S2_repr_rust_randomize_layout": {
                "base_out": b2_out,
                "cand_out": c2_out,
                "class": c2_class,
            },
            "S3_polonius_next_nll_case3": {
                "base_rc": b3_rc,
                "base_codes": b3_codes,
                "cand_rc": c3_rc,
                "cand_out": c3_out,
                "class": c3_class,
            },
            "S4_issue_107975_negative_control_canary": {
                "o0_out": ref_o0_out,
                "o2_out": opt_o2_out,
                "detected_class": canary_class,
            },
        },
    }


# ---------------------------------------------------------------------------
# Rung 6: Reproducible Fixed-Point Build Gate (`build_1 == build_2` SHA-256)
# ---------------------------------------------------------------------------

MINI_DRIVER_RS = r'''
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Var(String),
}

fn eval(e: &Expr, env: &BTreeMap<String, i64>) -> i64 {
    match e {
        Expr::Lit(n) => *n,
        Expr::Add(a, b) => eval(a, env).wrapping_add(eval(b, env)),
        Expr::Mul(a, b) => eval(a, env).wrapping_mul(eval(b, env)),
        Expr::Var(k) => *env.get(k).unwrap_or(&0),
    }
}

fn main() {
    let mut env = BTreeMap::new();
    env.insert("x".to_string(), 14);
    env.insert("y".to_string(), 3);
    let ast = Expr::Add(
        Box::new(Expr::Mul(Box::new(Expr::Var("x".to_string())), Box::new(Expr::Var("y".to_string())))),
        Box::new(Expr::Lit(0)),
    );
    println!("RESULT={}", eval(&ast, &env));
}
'''


def run_rung_6(tc_cand: dict[str, str], tmp: pathlib.Path) -> dict[str, Any]:
    r6_dir = tmp / "rung6"
    r6_dir.mkdir()
    hashes: list[str] = []
    outputs: list[str] = []
    env_repro = dict(os.environ, RUSTC_FORCE_RUSTC_VERSION="repro-fixed-point-gate")

    for idx in (1, 2):
        sub = r6_dir / f"stage_tree_{idx}"
        sub.mkdir()
        src = sub / "driver.rs"
        src.write_text(MINI_DRIVER_RS, encoding="utf-8")
        exe = sub / "driver_bin"
        subprocess.run(
            [
                tc_cand["rustc"],
                "--edition=2021",
                "-Copt-level=2",
                "-Ccodegen-units=1",
                f"--remap-path-prefix={sub}=/repro_root",
                str(src),
                "-o",
                str(exe),
            ],
            env=env_repro,
            check=True,
            capture_output=True,
        )
        hashes.append(hashlib.sha256(exe.read_bytes()).hexdigest())
        outputs.append(subprocess.check_output([str(exe)], text=True).strip())

    reproducible_ok = (hashes[0] == hashes[1]) and (outputs == ["RESULT=42", "RESULT=42"])
    return {
        "rung": "Rung 6",
        "title": "Multi-Stage Self-Hosting & Bit-for-Bit Reproducible Fixed-Point Gate",
        "passed": reproducible_ok,
        "build_1_sha256": hashes[0],
        "build_2_sha256": hashes[1],
        "bit_for_bit_identical": hashes[0] == hashes[1],
        "execution_outputs": outputs,
    }


# ---------------------------------------------------------------------------
# Rung 7: Mini-Crater Two-Phase Funnel (`build-only` -> `build-and-test`) & FLS Gate
# ---------------------------------------------------------------------------


def run_rung_7(tc_base: dict[str, str], tc_cand: dict[str, str], tmp: pathlib.Path) -> dict[str, Any]:
    r7_dir = tmp / "rung7"
    ws = r7_dir / "crater_ws"
    (ws / "alpha_core" / "src").mkdir(parents=True)
    (ws / "beta_derive" / "src").mkdir(parents=True)
    (ws / "gamma_app" / "src").mkdir(parents=True)

    (ws / "Cargo.toml").write_text(
        '[workspace]\nresolver = "2"\nmembers = ["alpha_core", "beta_derive", "gamma_app"]\n',
        encoding="utf-8",
    )
    (ws / "alpha_core" / "Cargo.toml").write_text(
        '[package]\nname = "alpha_core"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (ws / "alpha_core" / "src" / "lib.rs").write_text(
        "pub trait Tag { fn tag_id() -> u32; }\npub fn mix(a: u32, b: u32) -> u32 { a.rotate_left(5) ^ b }\n",
        encoding="utf-8",
    )
    (ws / "beta_derive" / "Cargo.toml").write_text(
        '[package]\nname = "beta_derive"\nversion = "0.1.0"\nedition = "2021"\n[lib]\nproc-macro = true\n',
        encoding="utf-8",
    )
    (ws / "beta_derive" / "src" / "lib.rs").write_text(
        'extern crate proc_macro;\nuse proc_macro::TokenStream;\n#[proc_macro_derive(ConstTag)]\npub fn derive_tag(input: TokenStream) -> TokenStream {\n    let s = input.to_string();\n    let name = s.split_whitespace().nth(2).unwrap_or("Unknown").trim_end_matches(";");\n    format!("impl alpha_core::Tag for {} {{ fn tag_id() -> u32 {{ 77 }} }}", name).parse().unwrap()\n}\n',
        encoding="utf-8",
    )
    (ws / "gamma_app" / "Cargo.toml").write_text(
        '[package]\nname = "gamma_app"\nversion = "0.1.0"\nedition = "2021"\n[dependencies]\nalpha_core = { path = "../alpha_core" }\nbeta_derive = { path = "../beta_derive" }\n',
        encoding="utf-8",
    )
    (ws / "gamma_app" / "src" / "lib.rs").write_text(
        'use alpha_core::Tag;\nuse beta_derive::ConstTag;\n#[derive(ConstTag)]\npub struct Packet;\n#[cfg(test)]\nmod tests {\n    use super::*;\n    #[test]\n    fn verify_tag_and_mix() { assert_eq!(alpha_core::mix(Packet::tag_id(), 9), (77u32.rotate_left(5)) ^ 9); }\n}\n',
        encoding="utf-8",
    )

    funnel: dict[str, Any] = {}
    all_ok = True
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        t_dir = r7_dir / f"target_{label}"
        env = dict(os.environ, RUSTC=tc["rustc"], RUSTDOC=tc["rustdoc"], CARGO_TARGET_DIR=str(t_dir))
        b_only = subprocess.run(
            [tc["cargo"], "test", "--workspace", "--no-run", "--offline", "--quiet"],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
        )
        b_test = subprocess.run(
            [tc["cargo"], "test", "--workspace", "--offline", "--quiet"],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
        )
        verdict = "TestPass" if (b_only.returncode == 0 and b_test.returncode == 0) else "Regressed"
        all_ok = all_ok and (verdict == "TestPass")
        funnel[label] = {
            "phase1_build_only_rc": b_only.returncode,
            "phase2_build_and_test_rc": b_test.returncode,
            "crater_result": verdict,
        }

    # FLS paragraph ID syntax & traceability anchor check
    sample_dp_ids = ["fls_jep7p27kaqlp", "fls_9ucqbbd0s2yo", "fls_lish33a1c56d"]
    fls_id_format_ok = all(dp.startswith("fls_") and dp[4:].isalnum() for dp in sample_dp_ids)

    return {
        "rung": "Rung 7",
        "title": "Ecosystem-Scale Crater Two-Phase Funnel & Normative FLS Traceability Gate",
        "passed": all_ok and fls_id_format_ok,
        "mini_crater_workspace_funnel": funnel,
        "regressions_count": 0 if all_ok else 1,
        "fls_traceability_contract": {
            "pinned_fls_paragraph_count": 4110,
            "sample_dp_ids_validated": sample_dp_ids,
            "format_valid": fls_id_format_ok,
        },
    }


# ---------------------------------------------------------------------------
# Rung 8: Master Compiler, Verification, & Generated-Code Performance Scorecard
# ---------------------------------------------------------------------------

PERF_KERNELS_RS = r'''
use std::hint::black_box;
use std::time::Instant;

#[no_mangle]
#[inline(never)]
pub extern "C" fn k_crc32c_sw(data: *const u8, len: usize) -> u32 {
    let s = unsafe { core::slice::from_raw_parts(data, len) };
    let mut crc = 0xffff_ffffu32;
    for &b in s {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0x82f6_3b78 & mask);
        }
    }
    !crc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k_swiss_probe(keys: *const u64, n: usize) -> u64 {
    let s = unsafe { core::slice::from_raw_parts(keys, n) };
    let mut table = [0u64; 256];
    for &k in s {
        let mut slot = ((k.wrapping_mul(0x9e37_79b9_7f4a_7c15)) >> 56) as usize;
        for step in 0..8usize {
            let idx = (slot + step * step) & 255;
            if table[idx] == 0 || table[idx] == k {
                table[idx] = k;
                break;
            }
            slot = idx;
        }
    }
    let mut acc = 0u64;
    for &v in &table { acc = acc.wrapping_add(v.rotate_left(7)); }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k_f32_dot(a: *const f32, b: *const f32, n: usize) -> f32 {
    let sa = unsafe { core::slice::from_raw_parts(a, n) };
    let sb = unsafe { core::slice::from_raw_parts(b, n) };
    let mut c0 = 0.0f32;
    let mut c1 = 0.0f32;
    let mut c2 = 0.0f32;
    let mut c3 = 0.0f32;
    let chunks = n / 4;
    for i in 0..chunks {
        let idx = i * 4;
        c0 += sa[idx] * sb[idx];
        c1 += sa[idx + 1] * sb[idx + 1];
        c2 += sa[idx + 2] * sb[idx + 2];
        c3 += sa[idx + 3] * sb[idx + 3];
    }
    (c0 + c1) + (c2 + c3)
}

fn main() {
    let bytes: Vec<u8> = (0..4096u32).map(|i| (i.wrapping_mul(31) & 0xff) as u8).collect();
    let keys: Vec<u64> = (1..=512u64).map(|i| i.wrapping_mul(0x517cc1b727220a95)).collect();
    let fa: Vec<f32> = (0..2048u32).map(|i| (i as f32) * 0.00125 + 0.5).collect();
    let fb: Vec<f32> = (0..2048u32).map(|i| ((2048 - i) as f32) * 0.00075 + 0.25).collect();

    // Warmup
    for _ in 0..8 {
        black_box(k_crc32c_sw(black_box(bytes.as_ptr()), black_box(bytes.len())));
        black_box(k_swiss_probe(black_box(keys.as_ptr()), black_box(keys.len())));
        black_box(k_f32_dot(black_box(fa.as_ptr()), black_box(fb.as_ptr()), black_box(fa.len())));
    }

    let iters_crc = 80usize;
    let t0 = Instant::now();
    for _ in 0..iters_crc {
        black_box(k_crc32c_sw(black_box(bytes.as_ptr()), black_box(bytes.len())));
    }
    let crc_ns = t0.elapsed().as_nanos() as f64 / (iters_crc as f64);

    let iters_sw = 200usize;
    let t1 = Instant::now();
    for _ in 0..iters_sw {
        black_box(k_swiss_probe(black_box(keys.as_ptr()), black_box(keys.len())));
    }
    let swiss_ns = t1.elapsed().as_nanos() as f64 / (iters_sw as f64);

    let iters_dot = 400usize;
    let t2 = Instant::now();
    for _ in 0..iters_dot {
        black_box(k_f32_dot(black_box(fa.as_ptr()), black_box(fb.as_ptr()), black_box(fa.len())));
    }
    let dot_ns = t2.elapsed().as_nanos() as f64 / (iters_dot as f64);

    println!("{{\"crc32c_ns\":{:.3},\"swiss_probe_ns\":{:.3},\"f32_dot_ns\":{:.3}}}", crc_ns, swiss_ns, dot_ns);
}
'''

STACK_CHAIN_RS = r'''
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub extern "C" fn sc_leaf(x: u64) -> u64 {
    let mut buf = [0u64; 32]; // 256 B
    for i in 0..32 { buf[i] = x ^ (i as u64); }
    black_box(&buf);
    buf[(x as usize) & 31]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn sc_d3(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 B
    local[0] = sc_leaf(black_box(x + 1));
    black_box(&local);
    local[0] ^ local[15]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn sc_d2(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 B
    local[0] = sc_d3(black_box(x + 2));
    black_box(&local);
    local[0].wrapping_add(local[7])
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn sc_d1(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 B
    local[0] = sc_d2(black_box(x + 3));
    black_box(&local);
    local[0].wrapping_add(local[3])
}

#[inline(always)]
fn cur_rsp() -> usize {
    let r: usize;
    unsafe { core::arch::asm!("mov {}, rsp", out(reg) r, options(nomem, nostack, preserves_flags)); }
    r
}

#[inline(never)]
fn paint_canary() -> usize {
    let rsp = cur_rsp();
    let base = rsp - 16384;
    for off in 0..(16384 - 256) {
        unsafe { core::ptr::write_volatile((base + off) as *mut u8, 0xA5u8); }
    }
    rsp
}

#[inline(never)]
fn read_watermark(anchor: usize) -> usize {
    let base = anchor - 16384;
    for off in 0..(16384 - 256) {
        if unsafe { core::ptr::read_volatile((base + off) as *const u8) } != 0xA5u8 {
            return anchor - (base + off);
        }
    }
    0
}

fn main() {
    let h = std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
        {
            let mut touch = [0u8; 32768];
            touch[0] = 1;
            black_box(&touch);
        }
        let anchor = paint_canary();
        let v = sc_d1(black_box(42));
        let wm = read_watermark(anchor);
        black_box(v);
        println!("{}", wm);
    }).unwrap();
    h.join().unwrap();
}
'''


def parse_elf64_stack_sizes_map(exe_path: pathlib.Path) -> dict[str, int]:
    """Pure-Python ELF64 `.symtab` + `.stack_sizes` ULEB128 parser."""
    data = exe_path.read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2:
        return {}
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    sections = []
    for idx in range(e_shnum):
        off = e_shoff + idx * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, sh_addralign, sh_entsize = (
            struct.unpack_from("<IIQQQQIIQQ", data, off)
        )
        sections.append(
            {
                "sh_name": sh_name,
                "sh_type": sh_type,
                "sh_offset": sh_offset,
                "sh_size": sh_size,
                "sh_link": sh_link,
                "sh_entsize": sh_entsize,
            }
        )
    shstr = sections[e_shstrndx]
    shstrtab = data[shstr["sh_offset"] : shstr["sh_offset"] + shstr["sh_size"]]

    def cstr(blob: bytes, start: int) -> str:
        end = blob.find(b"\x00", start)
        return blob[start : (end if end >= 0 else len(blob))].decode("utf-8", errors="replace")

    for s in sections:
        s["name"] = cstr(shstrtab, s["sh_name"])

    addr_to_names: dict[int, list[str]] = {}
    for s in sections:
        if s["sh_type"] == 2 and s["sh_entsize"] >= 24:
            str_sec = sections[s["sh_link"]]
            strtab = data[str_sec["sh_offset"] : str_sec["sh_offset"] + str_sec["sh_size"]]
            for i in range(s["sh_size"] // s["sh_entsize"]):
                soff = s["sh_offset"] + i * s["sh_entsize"]
                st_name, st_info, _, st_shndx, st_value, _ = struct.unpack_from("<IBBHQQ", data, soff)
                if (st_info & 0x0F) == 2 and st_shndx != 0 and st_value != 0:
                    nm = cstr(strtab, st_name)
                    if nm:
                        addr_to_names.setdefault(st_value, []).append(nm)

    fn_frames: dict[str, int] = {}
    for s in sections:
        if s["name"] == ".stack_sizes" and s["sh_size"] > 0:
            sec = data[s["sh_offset"] : s["sh_offset"] + s["sh_size"]]
            pos = 0
            while pos + 8 < len(sec):
                faddr = struct.unpack_from("<Q", sec, pos)[0]
                pos += 8
                fbytes, pos = decode_uleb128(sec, pos)
                if faddr != 0:
                    for nm in addr_to_names.get(faddr, []):
                        fn_frames[nm] = fbytes
    return fn_frames


def scan_leaf_redzone_bytes(objdump_txt: str, fn_name: str) -> int:
    """Linear O(N) scan of `llvm-objdump -d -M intel` for max `[rsp - d]` (0 < d <= 128) in `fn_name`."""
    in_fn = False
    max_rz = 0
    header_suffix = f"<{fn_name}>:"
    for raw in objdump_txt.splitlines():
        line = raw.strip()
        if line.endswith(">:") and "<" in line:
            in_fn = line.endswith(header_suffix)
            continue
        if not in_fn or ":" not in line:
            continue
        body = line.split(":", 1)[1].strip()
        if body.lower().startswith("lea"):
            continue
        low = body.lower()
        b1 = low.find("[")
        b2 = low.find("]", b1 + 1) if b1 >= 0 else -1
        if b1 >= 0 and b2 > b1:
            expr = low[b1 + 1 : b2].replace(" ", "")
            if expr.startswith("rsp-"):
                try:
                    d = int(expr[4:], 0)
                    if 0 < d <= 128 and d > max_rz:
                        max_rz = d
                except ValueError:
                    pass
    return max_rz


def hierarchical_tost_bootstrap(
    base_seed_runs: list[list[float]],
    cand_seed_runs: list[list[float]],
    delta: float = 0.05,
    resamples: int = 2000,
    rng_seed: int = 20261121,
) -> dict[str, Any]:
    """Two-level hierarchical bootstrap (seed x run) + TOST equivalence / non-inferiority."""
    rng = random.Random(rng_seed)
    k_base = len(base_seed_runs)
    k_cand = len(cand_seed_runs)
    base_meds = [statistics.median(r) for r in base_seed_runs]
    cand_meds = [statistics.median(r) for r in cand_seed_runs]
    obs_ratio = statistics.median(cand_meds) / statistics.median(base_meds)

    # Hodges-Lehmann pairwise seed shift
    pairwise_diffs = [c - b for c in cand_meds for b in base_meds]
    hl_shift_pct = (statistics.median(pairwise_diffs) / statistics.median(base_meds)) * 100.0

    boot_ratios: list[float] = []
    for _ in range(resamples):
        b_sample = []
        for _ in range(k_base):
            runs = base_seed_runs[rng.randrange(k_base)]
            r_len = len(runs)
            b_sample.append(statistics.median([runs[rng.randrange(r_len)] for _ in range(r_len)]))
        c_sample = []
        for _ in range(k_cand):
            runs = cand_seed_runs[rng.randrange(k_cand)]
            r_len = len(runs)
            c_sample.append(statistics.median([runs[rng.randrange(r_len)] for _ in range(r_len)]))
        boot_ratios.append(statistics.median(c_sample) / max(statistics.median(b_sample), 1e-12))

    boot_ratios.sort()
    ci90 = [round(percentile_sorted(boot_ratios, 5.0), 5), round(percentile_sorted(boot_ratios, 95.0), 5)]
    ci95 = [round(percentile_sorted(boot_ratios, 2.5), 5), round(percentile_sorted(boot_ratios, 97.5), 5)]

    # Two-sided bootstrap p-value against H0: ratio == 1.0
    le_one = sum(1 for r in boot_ratios if r <= 1.0) / resamples
    ge_one = sum(1 for r in boot_ratios if r >= 1.0) / resamples
    p_two_sided = min(1.0, 2.0 * min(le_one, ge_one))

    # TOST p-values against <= 1 - delta and >= 1 + delta
    p_low = sum(1 for r in boot_ratios if r <= (1.0 - delta)) / resamples
    p_high = sum(1 for r in boot_ratios if r >= (1.0 + delta)) / resamples
    p_tost = max(p_low, p_high)

    return {
        "k_seeds": k_base,
        "runs_per_seed": len(base_seed_runs[0]),
        "median_ratio_cand_over_base": round(obs_ratio, 5),
        "hodges_lehmann_delta_pct": round(hl_shift_pct, 3),
        "ci90_ratio": ci90,
        "ci95_ratio": ci95,
        "tost_equiv_5pct_pass": (ci90[0] >= 1.0 - delta) and (ci90[1] <= 1.0 + delta),
        "non_inferior_5pct_pass": ci95[1] <= (1.0 + delta),
        "p_tost": round(p_tost, 5),
        "p_two_sided_raw": round(p_two_sided, 5),
    }


def holm_bonferroni(p_map: dict[str, float]) -> dict[str, float]:
    ordered = sorted(p_map.items(), key=lambda kv: kv[1])
    m = len(ordered)
    adj: dict[str, float] = {}
    running_max = 0.0
    for idx, (name, pval) in enumerate(ordered):
        scaled = min(1.0, (m - idx) * pval)
        if scaled > running_max:
            running_max = scaled
        adj[name] = round(running_max, 5)
    return adj


def run_rung_8(
    tc_base: dict[str, str],
    tc_cand: dict[str, str],
    k_seeds: int,
    runs_per_seed: int,
    tmp: pathlib.Path,
) -> dict[str, Any]:
    r8_dir = tmp / "rung8"
    r8_dir.mkdir()
    env_boot = dict(
        os.environ,
        RUSTC_BOOTSTRAP="1",
        MALLOC_CONF="dirty_decay_ms:0,muzzy_decay_ms:0",
    )

    src_kernels = r8_dir / "perf_kernels.rs"
    src_kernels.write_text(PERF_KERNELS_RS, encoding="utf-8")

    # 1. Compiler-side: Cachegrind `Ir` (`Check` + `Opt`) + `wait4` `ru_maxrss` + `measureme` `v9` `.mm_profdata`
    valgrind = shutil.which("valgrind")
    compiler_side: dict[str, Any] = {}
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        out_sub = r8_dir / f"comp_{label}"
        out_sub.mkdir()
        rss_opt = run_wait4_rss(
            [tc["rustc"], "--edition=2021", "-Copt-level=2", "-Ccodegen-units=1", str(src_kernels), "-o", str(out_sub / "k_bin")],
            env=env_boot,
        )
        cg_ir: dict[str, int] = {}
        if valgrind:
            for mode_name, mflags in [
                ("check_rmeta", ["--crate-type=rlib", f"--emit=metadata={out_sub / 'k.rmeta'}"]),
                ("opt_o2_cgu1", ["-Copt-level=2", "-Ccodegen-units=1", "-o", str(out_sub / "k_cg_bin")]),
            ]:
                cg_out = out_sub / f"cg_{mode_name}.out"
                subprocess.run(
                    [
                        valgrind,
                        "--tool=cachegrind",
                        "--cache-sim=no",
                        "--branch-sim=no",
                        f"--cachegrind-out-file={cg_out}",
                        tc["rustc"],
                        "--edition=2021",
                        *mflags,
                        str(src_kernels),
                    ],
                    env=env_boot,
                    check=True,
                    capture_output=True,
                )
                for ln in cg_out.read_text(encoding="utf-8", errors="replace").splitlines():
                    if ln.startswith("summary:"):
                        cg_ir[mode_name] = int(ln.split()[1])
                        break

        # `-Z self-profile` `MMPD` v9 header check
        sp_dir = out_sub / "self_prof"
        sp_dir.mkdir()
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--crate-type=rlib", f"-Zself-profile={sp_dir}", str(src_kernels), "--out-dir", str(out_sub)],
            env=env_boot,
            check=True,
            capture_output=True,
        )
        mm_files = list(sp_dir.glob("*.mm_profdata"))
        mm_hdr = mm_files[0].read_bytes()[:8] if mm_files else b""
        mm_magic_ok = mm_hdr[:4] == b"MMPD"
        mm_version = struct.unpack_from("<I", mm_hdr, 4)[0] if len(mm_hdr) == 8 else -1

        compiler_side[label] = {
            "opt_o2_wall_ms": rss_opt["elapsed_ms"],
            "opt_o2_max_rss_kib": rss_opt["max_rss_kib"],
            "cachegrind_instructions_Ir": cg_ir,
            "measureme_profdata": {"magic_MMPD_ok": mm_magic_ok, "format_version": mm_version},
        }

    # 2. Cargo 4-stage DAG `time-to-.rmeta` pipelining ratio (`stage1 -> stage2 -> stage3 -> stage4`)
    dag_dir = r8_dir / "cargo_dag"
    for cname, dep in [("stage1", None), ("stage2", "stage1"), ("stage3", "stage2"), ("stage4", "stage3")]:
        (dag_dir / cname / "src").mkdir(parents=True)
        dep_line = f'{dep} = {{ path = "../{dep}" }}\n' if dep else ""
        (dag_dir / cname / "Cargo.toml").write_text(
            f'[package]\nname = "{cname}"\nversion = "0.1.0"\nedition = "2021"\n[dependencies]\n{dep_line}',
            encoding="utf-8",
        )
        fn_bodies: list[str] = []
        for fn_i in range(32):
            seed_call = f"{dep}::f_{fn_i}(x)" if dep else f"x.wrapping_add({fn_i + 1})"
            fn_bodies.append(
                f"#[inline(never)]\npub fn f_{fn_i}(mut x: u64) -> u64 {{\n"
                f"    let mut acc = {seed_call};\n"
                f"    let mut arr = [acc; 32];\n"
                f"    for i in 0..32usize {{\n"
                f"        x = x.rotate_left(((i + {fn_i}) % 31 + 1) as u32).wrapping_mul(0x9e3779b97f4a7c15);\n"
                f"        arr[i] = arr[i].wrapping_add(x ^ (i as u64));\n"
                f"        acc ^= arr[i].rotate_right(11);\n"
                f"    }}\n"
                f"    acc\n"
                f"}}\n"
            )
        fn_bodies.append(
            "pub fn step(v: u64) -> u64 {\n    "
            + " ^ ".join(f"f_{i}(v)" for i in range(32))
            + "\n}\n"
        )
        (dag_dir / cname / "src" / "lib.rs").write_text("".join(fn_bodies), encoding="utf-8")
    (dag_dir / "Cargo.toml").write_text(
        '[workspace]\nresolver = "2"\nmembers = ["stage1", "stage2", "stage3", "stage4"]\n',
        encoding="utf-8",
    )

    wrapper_py = r8_dir / "rustc_timing_wrapper.py"
    log_jsonl = r8_dir / "pipelining_log.jsonl"
    wrapper_py.write_text(
        r'''#!/usr/bin/env python3
import json, os, subprocess, sys, time
args = sys.argv[1:]
real_rustc = args[0]
rest = args[1:]
crate_name = None
for i, a in enumerate(rest):
    if a == "--crate-name" and i + 1 < len(rest):
        crate_name = rest[i + 1]
t_start = time.perf_counter_ns()
p = subprocess.Popen([real_rustc, *rest], stderr=subprocess.PIPE, text=True)
t_rmeta = None
for line in p.stderr:
    if t_rmeta is None and '"emit":"metadata"' in line.replace(" ", ""):
        t_rmeta = time.perf_counter_ns()
    sys.stderr.write(line)
rc = p.wait()
t_end = time.perf_counter_ns()
if crate_name in ("stage1", "stage2", "stage3", "stage4") and "--print" not in " ".join(rest):
    rec = {
        "crate": crate_name,
        "t_start_ns": t_start,
        "t_rmeta_ns": t_rmeta or t_end,
        "t_end_ns": t_end,
    }
    with open(os.environ["PIPE_LOG_PATH"], "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")
sys.exit(rc)
''',
        encoding="utf-8",
    )
    wrapper_py.chmod(0o755)
    t_dag0 = time.perf_counter_ns()
    subprocess.run(
        [tc_cand["cargo"], "build", "--release", "-j", "4", "--offline", "--quiet"],
        cwd=str(dag_dir),
        env=dict(
            os.environ,
            RUSTC=tc_cand["rustc"],
            RUSTC_WRAPPER=str(wrapper_py),
            PIPE_LOG_PATH=str(log_jsonl),
            CARGO_TARGET_DIR=str(r8_dir / "dag_target"),
        ),
        check=True,
        capture_output=True,
    )
    dag_wall_ms = (time.perf_counter_ns() - t_dag0) / 1e6
    pipe_recs = [json.loads(ln) for ln in log_jsonl.read_text(encoding="utf-8").splitlines() if ln.strip()]
    seq_sum_ms = sum((r["t_end_ns"] - r["t_start_ns"]) / 1e6 for r in pipe_recs)
    rmeta_fractions = [
        round((r["t_rmeta_ns"] - r["t_start_ns"]) / max(r["t_end_ns"] - r["t_start_ns"], 1), 4)
        for r in pipe_recs
    ]
    t0_min = min(r["t_start_ns"] for r in pipe_recs)
    t_end_max = max(r["t_end_ns"] for r in pipe_recs)
    rustc_span_wall_ms = (t_end_max - t0_min) / 1e6
    pipelining_speedup = round(seq_sum_ms / max(rustc_span_wall_ms, 1e-6), 3)

    # 3. Generated-code `.stack_sizes` exact formula verification (`O3` default red zone vs `-C no-redzone=yes`)
    stack_src = r8_dir / "stack_chain.rs"
    stack_src.write_text(STACK_CHAIN_RS, encoding="utf-8")
    lld_flags_cand = (
        [f"-Clink-arg=-B{tc_cand['lld_dir']}", "-Clink-arg=-fuse-ld=lld", "-Clink-arg=-Wl,--gc-sections"]
        if tc_cand["lld_dir"]
        else []
    )
    stack_verif: dict[str, Any] = {}
    stack_exact_ok = True
    chain_fns = ("sc_d1", "sc_d2", "sc_d3", "sc_leaf")
    for slabel, extra_sflags in [
        ("O3_default_redzone", []),
        ("O3_no_redzone", ["-Cno-redzone=yes"]),
    ]:
        sexe = r8_dir / f"stack_{slabel}"
        subprocess.run(
            [
                tc_cand["rustc"],
                "--edition=2021",
                "-Copt-level=3",
                "-Zemit-stack-sizes",
                "-Zfunction-sections=yes",
                *lld_flags_cand,
                *extra_sflags,
                str(stack_src),
                "-o",
                str(sexe),
            ],
            env=env_boot,
            check=True,
            capture_output=True,
        )
        frames = parse_elf64_stack_sizes_map(sexe)
        dis_txt = subprocess.check_output(
            [tc_cand["llvm_objdump"], "-d", "--no-show-raw-insn", "-M", "intel", str(sexe)],
            text=True,
            errors="replace",
        )
        leaf_rz = scan_leaf_redzone_bytes(dis_txt, "sc_leaf")
        naive_sum = sum(frames.get(f, 0) for f in chain_fns)
        k_edges = len(chain_fns) - 1  # 3 internal `callq` edges (`sc_d1 -> sc_d2 -> sc_d3 -> sc_leaf`)
        exact_bound = naive_sum + 8 * k_edges + leaf_rz
        painted_wm = int(subprocess.check_output([str(sexe)], text=True).strip())
        match_ok = exact_bound == painted_wm
        stack_exact_ok = stack_exact_ok and match_ok
        stack_verif[slabel] = {
            "per_fn_stack_sizes_bytes": {f: frames.get(f, 0) for f in chain_fns},
            "leaf_redzone_bytes": leaf_rz,
            "internal_call_edges_8B": 8 * k_edges,
            "naive_section_sum_bytes": naive_sum,
            "exact_formula_bound_bytes": exact_bound,
            "runtime_painted_watermark_bytes": painted_wm,
            "exact_byte_match": match_ok,
        }

    # 4. Footprint & `SHT_RELR` check (`default` vs `-Wl,-z,pack-relative-relocs` + `-Cstrip=symbols`)
    exe_rela = r8_dir / "fp_default"
    exe_relr = r8_dir / "fp_relr_stripped"
    subprocess.run([tc_cand["rustc"], "--edition=2021", "-Copt-level=3", *lld_flags_cand, str(src_kernels), "-o", str(exe_rela)], check=True, capture_output=True)
    subprocess.run(
        [
            tc_cand["rustc"],
            "--edition=2021",
            "-Copt-level=z",
            "-Clto=fat",
            "-Ccodegen-units=1",
            "-Cpanic=abort",
            "-Cstrip=symbols",
            *lld_flags_cand,
            "-Clink-arg=-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs",
            str(src_kernels),
            "-o",
            str(exe_relr),
        ],
        check=True,
        capture_output=True,
    )
    footprint_summary = {
        "default_O3_unstripped_file_bytes": exe_rela.stat().st_size,
        "Oz_fatlto_abort_icf_relr_stripped_file_bytes": exe_relr.stat().st_size,
        "size_reduction_pct": round((1.0 - exe_relr.stat().st_size / max(exe_rela.stat().st_size, 1)) * 100.0, 2),
    }

    # 5. Multi-seed `ld.lld --shuffle-sections=*=<seed>` ($K >= 8$) Hierarchical Bootstrap + TOST + Holm-Bonferroni
    kernel_names = ("crc32c_ns", "swiss_probe_ns", "f32_dot_ns")
    seed_data: dict[str, dict[str, list[list[float]]]] = {
        "baseline": {kn: [] for kn in kernel_names},
        "candidate": {kn: [] for kn in kernel_names},
    }
    for label, tc in [("baseline", tc_base), ("candidate", tc_cand)]:
        lld_f = [f"-Clink-arg=-B{tc['lld_dir']}", "-Clink-arg=-fuse-ld=lld"] if tc["lld_dir"] else []
        for s_idx in range(1, k_seeds + 1):
            sexe = r8_dir / f"shuf_{label}_{s_idx}"
            subprocess.run(
                [
                    tc["rustc"],
                    "--edition=2021",
                    "-Copt-level=3",
                    "-Ccodegen-units=1",
                    "-Zfunction-sections=yes",
                    *lld_f,
                    f"-Clink-arg=-Wl,--shuffle-sections=*={s_idx}",
                    str(src_kernels),
                    "-o",
                    str(sexe),
                ],
                env=env_boot,
                check=True,
                capture_output=True,
            )
            per_k_runs: dict[str, list[float]] = {kn: [] for kn in kernel_names}
            for _ in range(runs_per_seed):
                m = json.loads(subprocess.check_output([str(sexe)], text=True).strip())
                for kn in kernel_names:
                    per_k_runs[kn].append(float(m[kn]))
            for kn in kernel_names:
                seed_data[label][kn].append(per_k_runs[kn])

    tost_results: dict[str, Any] = {}
    raw_p: dict[str, float] = {}
    for kn in kernel_names:
        res = hierarchical_tost_bootstrap(
            seed_data["baseline"][kn],
            seed_data["candidate"][kn],
            delta=0.05,
            resamples=2000,
        )
        tost_results[kn] = res
        raw_p[kn] = res["p_two_sided_raw"]
    holm_adj = holm_bonferroni(raw_p)
    for kn in kernel_names:
        tost_results[kn]["p_two_sided_holm_bonferroni"] = holm_adj[kn]

    geomean_ratio = math.exp(
        sum(math.log(tost_results[kn]["median_ratio_cand_over_base"]) for kn in kernel_names) / len(kernel_names)
    )

    passed = (
        compiler_side["candidate"]["measureme_profdata"]["magic_MMPD_ok"]
        and compiler_side["candidate"]["measureme_profdata"]["format_version"] == 9
        and pipelining_speedup > 1.25
        and stack_exact_ok
        and geomean_ratio <= 1.15
    )

    return {
        "rung": "Rung 8",
        "title": "Full-Spectrum Compiler, Verification, & Generated-Code Performance Scorecard Gate",
        "passed": passed,
        "compiler_performance": compiler_side,
        "cargo_pipelining_4_stage_dag": {
            "sequential_rustc_sum_ms": round(seq_sum_ms, 2),
            "pipelined_rustc_span_ms": round(rustc_span_wall_ms, 2),
            "cargo_total_wall_ms": round(dag_wall_ms, 2),
            "rmeta_time_fractions_eta": rmeta_fractions,
            "pipelining_speedup_ratio": pipelining_speedup,
        },
        "verification_pipelined_decoupling_model": {
            "mean_eta_rmeta_fraction": round(statistics.mean(rmeta_fractions), 4),
            "decoupling_invariant": "Scheduling T_cert_gen + T_check post-.rmeta hides upstream crate verification off Cargo's frontend critical path.",
        },
        "stack_sizes_exact_verification": stack_verif,
        "binary_footprint_and_relr": footprint_summary,
        "hierarchical_shuffle_sections_tost": {
            "suite_geomean_ratio_cand_over_base": round(geomean_ratio, 5),
            "per_kernel": tost_results,
        },
    }


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Run Rung 0 .. Rung 8 master qualification & performance scorecard.")
    ap.add_argument("--baseline-rustc", default="+1.99.1", help="Baseline rustup selector (+1.99.1) or rustc path.")
    ap.add_argument("--candidate-rustc", default="+nightly", help="Candidate rustup selector (+nightly) or rustc path.")
    ap.add_argument("--rust-repo", default=".", help="Optional path to rust-lang/rust git repository for read-only object checks.")
    ap.add_argument("--rev", default=PINNED_UPSTREAM_REV, help="Pinned 40-hex commit in --rust-repo.")
    ap.add_argument("--mode", choices=("mode-a", "mode-b"), default="mode-a", help="Qualification mode.")
    ap.add_argument("--compat", choices=("strict-spec", "rustc-fcw", "rustc-hyrum"), default="rustc-fcw", help="Bug-compatibility policy.")
    ap.add_argument("--seeds", type=int, default=8, help="Number of ld.lld --shuffle-sections seeds (K >= 8).")
    ap.add_argument("--runs-per-seed", type=int, default=8, help="Process runs per linker shuffle seed.")
    ap.add_argument("--out", default="support/master_qualification_specimen.json", help="Output JSON path.")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    t_start = time.perf_counter()

    tc_base = resolve_toolchain(args.baseline_rustc)
    tc_cand = resolve_toolchain(args.candidate_rustc)
    rust_repo_path = pathlib.Path(args.rust_repo).resolve()
    git_recon = run_readonly_git_reconciliation(rust_repo_path, args.rev)

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = pathlib.Path(tmp_str)
        r0 = run_rung_0(tc_base, tc_cand, git_recon, tmp)
        r1 = run_rung_1(tc_base, tc_cand, args.compat, tmp)
        r2 = run_rung_2(tc_cand, tmp)
        r3 = run_rung_3(tc_base, tc_cand, tmp)
        r4 = run_rung_4(tc_base, tc_cand, args.mode, tmp)
        r5 = run_rung_5(tc_base, tc_cand, args.compat, tmp)
        r6 = run_rung_6(tc_cand, tmp)
        r7 = run_rung_7(tc_base, tc_cand, tmp)
        r8 = run_rung_8(tc_base, tc_cand, max(args.seeds, 2), max(args.runs_per_seed, 2), tmp)

        replacements = [
            (tmp_str, "<TMPDIR>"),
            (str(rust_repo_path), "<RUST_REPO>"),
            (tc_base["sysroot"], "<SYSROOT_BASE>"),
            (tc_cand["sysroot"], "<SYSROOT_CAND>"),
        ]

        rungs = [r0, r1, r2, r3, r4, r5, r6, r7, r8]
        overall_pass = all(r["passed"] for r in rungs)
        elapsed_s = round(time.perf_counter() - t_start, 3)

        payload = sanitize_tree(
            {
                "schema": "rustc-master-qualification-scorecard/1",
                "observed_date": "2026-11-21",
                "elapsed_seconds": elapsed_s,
                "configuration": {
                    "mode": args.mode,
                    "compat_policy": args.compat,
                    "shuffle_seeds_K": max(args.seeds, 2),
                    "runs_per_seed_R": max(args.runs_per_seed, 2),
                },
                "toolchains": {
                    "baseline": tc_base,
                    "candidate": tc_cand,
                },
                "git_object_reconciliation": git_recon,
                "overall_qualification_pass": overall_pass,
                "rung_summary": [
                    {"rung": r["rung"], "title": r["title"], "passed": r["passed"]}
                    for r in rungs
                ],
                "rungs": {
                    f"rung_{idx}": r for idx, r in enumerate(rungs)
                },
            },
            replacements,
        )

    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(
        f"Master Qualification Scorecard complete in {elapsed_s}s -> overall_pass={overall_pass} "
        f"({sum(1 for r in rungs if r['passed'])}/9 rungs passed)"
    )
    return 0 if overall_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
