#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Empirical compiler performance metric probe for rustc +1.99.1 and +nightly.

Executes inside temporary directories using only the Python 3.11+ standard
library, Linux perf_event_open (syscall 298 on x86_64), wait4(2) per-child
resource accounting, valgrind (cachegrind and dhat), direct measureme v9
.mm_profdata binary wire-format decoding, -Z time-passes JSON parsing, Cargo
pipelined time-to-.rmeta instrumentation, parallel scaling sweeps, and
asymptotic stress microbenchmarks.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
import ctypes
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import struct
import subprocess
import sys
import tempfile
import time
from typing import Any


# ---------------------------------------------------------------------------
# Sanitization helpers (prevent workstation paths from entering JSON output)
# ---------------------------------------------------------------------------


def sanitize_text(text: str, extra_replacements: list[tuple[str, str]] | None = None) -> str:
    out = text
    if extra_replacements:
        for src, dst in extra_replacements:
            if src:
                out = out.replace(src, dst)
    home = os.path.expanduser("~")
    if home and home != "/":
        out = out.replace(home, "$HOME")
    return out


def sanitize_obj(obj: Any, extra_replacements: list[tuple[str, str]] | None = None) -> Any:
    if isinstance(obj, str):
        return sanitize_text(obj, extra_replacements)
    if isinstance(obj, list):
        return [sanitize_obj(v, extra_replacements) for v in obj]
    if isinstance(obj, dict):
        return {
            sanitize_text(str(k), extra_replacements): sanitize_obj(v, extra_replacements)
            for k, v in obj.items()
        }
    return obj


# ---------------------------------------------------------------------------
# Toolchain resolution and wait4(2) per-process RSS / CPU timing
# ---------------------------------------------------------------------------


def resolve_toolchain(selector: str) -> dict[str, str]:
    vv = subprocess.check_output(["rustc", selector, "-vV"], text=True)
    sysroot = subprocess.check_output(
        ["rustc", selector, "--print", "sysroot"], text=True
    ).strip()
    cargo_bin = str(Path(sysroot) / "bin" / "cargo")
    if not Path(cargo_bin).is_file():
        cargo_bin = shutil.which("cargo") or "cargo"
    rustc_bin = str(Path(sysroot) / "bin" / "rustc")
    info: dict[str, str] = {
        "selector": selector,
        "sysroot": sysroot,
        "rustc_bin": rustc_bin,
        "cargo_bin": cargo_bin,
    }
    for line in vv.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
        elif line.startswith("rustc "):
            info["headline"] = line.strip()
    return info


def run_measured(
    argv: list[str],
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
) -> dict[str, Any]:
    """Spawn a child process and reap it with os.wait4 to capture isolated ru_maxrss."""
    merged_env = dict(os.environ)
    if env:
        merged_env.update(env)
    with tempfile.TemporaryFile() as out_f, tempfile.TemporaryFile() as err_f:
        t0 = time.monotonic_ns()
        proc = subprocess.Popen(
            argv,
            stdout=out_f,
            stderr=err_f,
            env=merged_env,
            cwd=str(cwd) if cwd else None,
        )
        _, status, rusage = os.wait4(proc.pid, 0)
        t1 = time.monotonic_ns()
        rc = os.waitstatus_to_exitcode(status)
        out_f.seek(0)
        err_f.seek(0)
        stdout_text = out_f.read().decode("utf-8", errors="replace")
        stderr_text = err_f.read().decode("utf-8", errors="replace")
    return {
        "returncode": rc,
        "wall_ns": t1 - t0,
        "wall_ms": (t1 - t0) / 1e6,
        "user_sec": rusage.ru_utime,
        "sys_sec": rusage.ru_stime,
        "max_rss_kib": rusage.ru_maxrss,
        "minflt": rusage.ru_minflt,
        "majflt": rusage.ru_majflt,
        "nvcsw": rusage.ru_nvcsw,
        "nivcsw": rusage.ru_nivcsw,
        "stdout": stdout_text,
        "stderr": stderr_text,
    }


# ---------------------------------------------------------------------------
# Linux perf_event_open (syscall 298 on x86_64)
# ---------------------------------------------------------------------------


class PerfEventAttr(ctypes.Structure):
    _fields_ = [
        ("type", ctypes.c_uint32),
        ("size", ctypes.c_uint32),
        ("config", ctypes.c_uint64),
        ("sample_period", ctypes.c_uint64),
        ("sample_type", ctypes.c_uint64),
        ("read_format", ctypes.c_uint64),
        ("flags", ctypes.c_uint64),
        ("wakeup_events", ctypes.c_uint32),
        ("bp_type", ctypes.c_uint32),
        ("config1", ctypes.c_uint64),
        ("config2", ctypes.c_uint64),
        ("branch_sample_type", ctypes.c_uint64),
        ("sample_regs_user", ctypes.c_uint64),
        ("sample_stack_user", ctypes.c_uint32),
        ("clockid", ctypes.c_int32),
        ("sample_regs_intr", ctypes.c_uint64),
        ("aux_watermark", ctypes.c_uint32),
        ("sample_max_stack", ctypes.c_uint16),
        ("reserved_2", ctypes.c_uint16),
        ("aux_sample_size", ctypes.c_uint32),
        ("reserved_3", ctypes.c_uint32),
        ("sig_data", ctypes.c_uint64),
    ]


PERF_TYPE_HARDWARE = 0
PERF_TYPE_SOFTWARE = 1

PERF_EVENTS_SPEC = [
    ("instructions:u", PERF_TYPE_HARDWARE, 1),
    ("cycles:u", PERF_TYPE_HARDWARE, 0),
    ("cache-references:u", PERF_TYPE_HARDWARE, 2),
    ("cache-misses:u", PERF_TYPE_HARDWARE, 3),
    ("branches:u", PERF_TYPE_HARDWARE, 4),
    ("branch-misses:u", PERF_TYPE_HARDWARE, 5),
    ("cpu-clock:u", PERF_TYPE_SOFTWARE, 0),
    ("task-clock:u", PERF_TYPE_SOFTWARE, 1),
    ("page-faults:u", PERF_TYPE_SOFTWARE, 2),
    ("context-switches:u", PERF_TYPE_SOFTWARE, 3),
    ("cpu-migrations:u", PERF_TYPE_SOFTWARE, 4),
    ("minor-faults:u", PERF_TYPE_SOFTWARE, 5),
    ("major-faults:u", PERF_TYPE_SOFTWARE, 6),
]

# x86_64 little-endian bitfield positions in perf_event_attr.flags:
# disabled=bit0, inherit=bit1, exclude_kernel=bit5, exclude_hv=bit6, enable_on_exec=bit12
PERF_FLAGS_INHERIT_EXEC_USER = (1 << 0) | (1 << 1) | (1 << 5) | (1 << 6) | (1 << 12)
PERF_EVENT_IOC_DISABLE = 0x2401


def run_with_perf_event_open(argv: list[str], env: dict[str, str]) -> dict[str, Any]:
    """Measure a subprocess with perf_event_open inherited across child threads."""
    if platform.machine() != "x86_64" or sys.platform != "linux":
        return {"supported": False, "reason": "non-x86_64-linux"}

    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    sys_perf_event_open = 298

    # Fork a tiny Python-controlled child that opens perf fds on pid=0 with
    # disabled=1 | inherit=1 | exclude_kernel=1 | exclude_hv=1 | enable_on_exec=1,
    # sends fd readiness/errors over a pipe, and execs rustc!
    # Wait: if the child opens fds on pid=0 before execve, how does the parent read them?
    # Even simpler and cleaner: parent spawns child paused on a synchronization pipe,
    # opens perf_event_open(attr, pid=child_pid, cpu=-1, group_fd=-1, flags=0) from the
    # PARENT before unblocking child's execve! That way all perf fds live in the parent!
    r_sync, w_sync = os.pipe()
    t0_wall = 0
    pid = os.fork()
    if pid == 0:
        os.close(w_sync)
        _ = os.read(r_sync, 1)
        os.close(r_sync)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        os.execvpe(argv[0], argv, env)
        os._exit(127)

    os.close(r_sync)
    opened: dict[str, int] = {}
    errors: dict[str, dict[str, Any]] = {}
    for name, etype, ecfg in PERF_EVENTS_SPEC:
        attr = PerfEventAttr()
        attr.type = etype
        attr.size = ctypes.sizeof(PerfEventAttr)
        attr.config = ecfg
        attr.flags = PERF_FLAGS_INHERIT_EXEC_USER
        ctypes.set_errno(0)
        fd = libc.syscall(sys_perf_event_open, ctypes.byref(attr), pid, -1, -1, 0)
        err = ctypes.get_errno()
        if fd >= 0:
            opened[name] = int(fd)
        else:
            errors[name] = {"errno": err, "strerror": os.strerror(err)}

    t0_wall = time.monotonic_ns()
    os.write(w_sync, b"1")
    os.close(w_sync)

    _, status, rusage = os.wait4(pid, 0)
    t1_wall = time.monotonic_ns()
    rc = os.waitstatus_to_exitcode(status)

    counts: dict[str, int] = {}
    for name, fd in opened.items():
        libc.ioctl(fd, PERF_EVENT_IOC_DISABLE, 0)
        raw = os.read(fd, 8)
        counts[name] = struct.unpack("<Q", raw)[0]
        os.close(fd)

    return {
        "returncode": rc,
        "wall_ms": (t1_wall - t0_wall) / 1e6,
        "max_rss_kib": rusage.ru_maxrss,
        "user_sec": rusage.ru_utime,
        "sys_sec": rusage.ru_stime,
        "counts": counts,
        "unavailable_events": errors,
    }


# ---------------------------------------------------------------------------
# Pure-Python measureme v9 .mm_profdata binary wire-format decoder
# ---------------------------------------------------------------------------


def decode_mm_profdata(data: bytes) -> dict[str, Any]:
    if len(data) < 8 or data[:4] != b"MMPD":
        raise ValueError(f"Invalid .mm_profdata top-level magic: {data[:8]!r}")
    ver = struct.unpack_from("<I", data, 4)[0]
    if ver != 9:
        raise ValueError(f"Unsupported .mm_profdata format version: {ver}")

    streams: dict[int, bytearray] = {0: bytearray(), 1: bytearray(), 2: bytearray()}
    page_counts: dict[str, int] = {"events": 0, "string_data": 0, "string_index": 0}
    tag_names = {0: "events", 1: "string_data", 2: "string_index"}

    pos = 8
    total_len = len(data)
    while pos < total_len:
        tag = data[pos]
        page_size = struct.unpack_from("<I", data, pos + 1)[0]
        streams[tag].extend(data[pos + 5 : pos + 5 + page_size])
        page_counts[tag_names[tag]] += 1
        pos += 5 + page_size

    ev_buf = bytes(streams[0])
    sd_buf = bytes(streams[1])
    si_buf = bytes(streams[2])

    assert ev_buf[:4] == b"MMES" and struct.unpack_from("<I", ev_buf, 4)[0] == 9
    assert sd_buf[:4] == b"MMSD" and struct.unpack_from("<I", sd_buf, 4)[0] == 9
    assert si_buf[:4] == b"MMSI" and struct.unpack_from("<I", si_buf, 4)[0] == 9

    metadata_id = 100_000_001
    invalid_id = 100_000_002
    first_regular_id = 100_000_003

    vmap: dict[int, int] = {}
    for off in range(8, len(si_buf), 16):
        vid, addr = struct.unpack_from("<QQ", si_buf, off)
        vmap[vid] = addr

    str_cache: dict[int, str] = {}

    def resolve_str(sid: int) -> str:
        cached = str_cache.get(sid)
        if cached is not None:
            return cached
        if sid == invalid_id:
            return "<invalid>"
        if sid <= metadata_id:
            addr = vmap.get(sid)
            if addr is None:
                return "<unknown>"
        else:
            addr = sid - first_regular_id

        parts: list[str] = []
        p = addr
        sd_len = len(sd_buf)
        while p < sd_len:
            b = sd_buf[p]
            if b == 0xFF:
                break
            if b == 0xFE:
                ref_id = struct.unpack_from("<Q", sd_buf, p + 1)[0]
                parts.append(resolve_str(ref_id))
                p += 9
            else:
                start = p
                while p < sd_len and sd_buf[p] < 0xFE:
                    p += 1
                parts.append(sd_buf[start:p].decode("utf-8", errors="replace"))
        val = "".join(parts)
        str_cache[sid] = val
        return val

    meta_obj = json.loads(resolve_str(metadata_id))
    instant_marker = 0xFFFF_FFFF_FFFF
    integer_marker = 0xFFFF_FFFF_FFFE

    num_raw_events = (len(ev_buf) - 8) // 32
    per_thread_stacks: dict[int, list[tuple[int, int, str, str]]] = defaultdict(list)
    query_stats: dict[str, dict[str, int]] = defaultdict(
        lambda: {
            "time_ns": 0,
            "self_time_ns": 0,
            "invocations": 0,
            "cache_hits": 0,
            "blocked_ns": 0,
            "incr_load_ns": 0,
            "incr_hash_ns": 0,
        }
    )
    artifact_sizes: dict[str, int] = {}
    kind_counts: dict[str, int] = defaultdict(int)
    hit_count_labels: set[str] = set()
    threads_seen: set[int] = set()

    for idx in range(num_raw_events - 1, -1, -1):
        off = 8 + idx * 32
        ekind_id, eid_id, tid, p1_lo, p2_lo, p_up = struct.unpack_from(
            "<QQIIII", ev_buf, off
        )
        threads_seen.add(tid)
        ekind = resolve_str(ekind_id)
        full_eid = resolve_str(eid_id)
        sep_idx = full_eid.find("\x1e")
        label = full_eid[:sep_idx] if sep_idx >= 0 else full_eid
        kind_counts[ekind] += 1

        val1 = p1_lo | ((p_up & 0xFFFF_0000) << 16)
        val2 = p2_lo | ((p_up & 0x0000_FFFF) << 32)
        if val2 == integer_marker:
            if ekind == "ArtifactSize":
                artifact_sizes[label] = artifact_sizes.get(label, 0) + val1
            elif ekind == "QueryCacheHitCount":
                query_stats[label]["cache_hits"] += val1
                hit_count_labels.add(label)
        elif val2 == instant_marker:
            if ekind == "QueryCacheHit" and label not in hit_count_labels:
                query_stats[label]["cache_hits"] += 1
        else:
            start, end = val1, val2
            dur = end - start
            st = per_thread_stacks[tid]
            while st and not (st[-1][0] <= start and end <= st[-1][1]):
                st.pop()
            if st:
                _, _, p_kind, p_label = st[-1]
                query_stats[p_label]["self_time_ns"] -= dur
                if p_kind == "IncrementalResultHashing":
                    query_stats[p_label]["incr_hash_ns"] -= dur
                elif p_kind == "IncrementalLoadResult":
                    query_stats[p_label]["incr_load_ns"] -= dur
            qs = query_stats[label]
            if ekind in ("Query", "GenericActivity"):
                qs["self_time_ns"] += dur
                qs["time_ns"] += dur
                qs["invocations"] += 1
            elif ekind == "QueryBlocked":
                qs["self_time_ns"] += dur
                qs["time_ns"] += dur
                qs["blocked_ns"] += dur
            elif ekind == "IncrementalLoadResult":
                qs["self_time_ns"] += dur
                qs["time_ns"] += dur
                qs["incr_load_ns"] += dur
            elif ekind == "IncrementalResultHashing":
                qs["self_time_ns"] += dur
                qs["incr_hash_ns"] += dur
            else:
                qs["self_time_ns"] += dur
                qs["time_ns"] += dur
                qs["invocations"] += 1
            st.append((start, end, ekind, label))

    top_self = sorted(
        query_stats.items(), key=lambda kv: kv[1]["self_time_ns"], reverse=True
    )[:12]
    total_self_ns = sum(v["self_time_ns"] for v in query_stats.values())
    total_cache_hits = sum(v["cache_hits"] for v in query_stats.values())
    total_incr_load_ns = sum(v["incr_load_ns"] for v in query_stats.values())
    total_incr_hash_ns = sum(v["incr_hash_ns"] for v in query_stats.values())

    return {
        "format_version": ver,
        "file_bytes": len(data),
        "stream_bytes": {
            "events": len(ev_buf),
            "string_data": len(sd_buf),
            "string_index": len(si_buf),
        },
        "page_counts": page_counts,
        "num_raw_events": num_raw_events,
        "num_virtual_index_entries": (len(si_buf) - 8) // 16,
        "distinct_threads": len(threads_seen),
        "counter": meta_obj.get("counter"),
        "event_kind_counts": dict(kind_counts),
        "artifact_sizes_bytes": artifact_sizes,
        "totals": {
            "total_self_time_ms": round(total_self_ns / 1e6, 3),
            "total_query_cache_hits": total_cache_hits,
            "total_incr_load_ms": round(total_incr_load_ns / 1e6, 3),
            "total_incr_hash_ms": round(total_incr_hash_ns / 1e6, 3),
            "distinct_labels": len(query_stats),
        },
        "top_12_by_self_time": [
            {
                "label": k,
                "self_time_ms": round(v["self_time_ns"] / 1e6, 3),
                "total_time_ms": round(v["time_ns"] / 1e6, 3),
                "invocations": v["invocations"],
                "cache_hits": v["cache_hits"],
                "incr_load_ms": round(v["incr_load_ns"] / 1e6, 3),
                "incr_hash_ms": round(v["incr_hash_ns"] / 1e6, 3),
            }
            for k, v in top_self
        ],
    }


# ---------------------------------------------------------------------------
# Workload source generators
# ---------------------------------------------------------------------------


SUBJECT_CRATE_LIB = """\
#![allow(dead_code)]

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpCode {
    Const(i64),
    Add,
    Sub,
    Mul,
    BitXor,
    Dup,
    Swap,
    JumpIfNonZero(usize),
}

pub struct VmState {
    pub stack: Vec<i64>,
    pub regs: [i64; 16],
    pub steps: u64,
}

impl VmState {
    pub fn new(seed: i64) -> Self {
        let mut regs = [0i64; 16];
        let mut i = 0;
        while i < 16 {
            regs[i] = seed.wrapping_mul((i as i64) + 3).wrapping_add(0x9e37_79b9);
            i += 1;
        }
        Self { stack: Vec::with_capacity(64), regs, steps: 0 }
    }

    pub fn execute(&mut self, prog: &[OpCode], budget: u64) -> i64 {
        let mut pc = 0usize;
        while pc < prog.len() && self.steps < budget {
            self.steps += 1;
            match prog[pc] {
                OpCode::Const(v) => self.stack.push(v),
                OpCode::Add => {
                    if let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) {
                        self.stack.push(a.wrapping_add(b));
                    }
                }
                OpCode::Sub => {
                    if let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) {
                        self.stack.push(a.wrapping_sub(b));
                    }
                }
                OpCode::Mul => {
                    if let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) {
                        self.stack.push(a.wrapping_mul(b));
                    }
                }
                OpCode::BitXor => {
                    if let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) {
                        self.stack.push(a ^ b);
                    }
                }
                OpCode::Dup => {
                    if let Some(&top) = self.stack.last() {
                        self.stack.push(top);
                    }
                }
                OpCode::Swap => {
                    let n = self.stack.len();
                    if n >= 2 {
                        self.stack.swap(n - 1, n - 2);
                    }
                }
                OpCode::JumpIfNonZero(target) => {
                    if let Some(cond) = self.stack.pop() {
                        if cond != 0 && target < prog.len() {
                            pc = target;
                            continue;
                        }
                    }
                }
            }
            pc += 1;
        }
        self.stack.last().copied().unwrap_or(self.regs[0])
    }
}

pub trait HashFold {
    fn fold_into(&self, acc: u64) -> u64;
}

impl HashFold for u64 {
    #[inline]
    fn fold_into(&self, acc: u64) -> u64 {
        acc.wrapping_mul(0x1000_0000_01b3) ^ (*self)
    }
}

impl<T: HashFold, const N: usize> HashFold for [T; N] {
    fn fold_into(&self, mut acc: u64) -> u64 {
        for item in self {
            acc = item.fold_into(acc);
        }
        acc
    }
}

pub struct DenseMatrix<const R: usize, const C: usize> {
    pub cells: [[f64; C]; R],
}

impl<const N: usize> DenseMatrix<N, N> {
    pub fn matmul(&self, rhs: &Self) -> Self {
        let mut out = Self { cells: [[0.0; N]; N] };
        let mut i = 0;
        while i < N {
            let mut k = 0;
            while k < N {
                let a = self.cells[i][k];
                let mut j = 0;
                while j < N {
                    out.cells[i][j] += a * rhs.cells[k][j];
                    j += 1;
                }
                k += 1;
            }
            i += 1;
        }
        out
    }
}

#[inline(never)]
pub fn leaf_checksum(values: &[u64]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for &v in values {
        h = v.fold_into(h);
    }
    h
}

pub fn run_kernel(seed: i64) -> (i64, f64, u64) {
    let prog = [
        OpCode::Const(seed),
        OpCode::Const(7),
        OpCode::Mul,
        OpCode::Const(13),
        OpCode::Add,
        OpCode::Dup,
        OpCode::BitXor,
    ];
    let mut vm = VmState::new(seed);
    let vm_res = vm.execute(&prog, 128);
    let m4 = DenseMatrix { cells: [[1.5; 4]; 4] };
    let m8 = DenseMatrix { cells: [[0.75; 8]; 8] };
    let r4 = m4.matmul(&m4).cells[0][0];
    let r8 = m8.matmul(&m8).cells[7][7];
    let chk = leaf_checksum(&[seed as u64, vm_res as u64, 42]);
    (vm_res, r4 + r8, chk)
}
"""


def patched_subject_lib() -> str:
    return SUBJECT_CRATE_LIB.replace(
        "let mut h = 0xcbf2_9ce4_8422_2325u64;",
        "let mut h = 0xcbf2_9ce4_8422_2325u64 ^ 0x55;",
    )


# ---------------------------------------------------------------------------
# Probe 1: Deterministic Cachegrind + perf_event_open Userspace Counters
# ---------------------------------------------------------------------------


def parse_cachegrind_out(cgout_path: Path) -> dict[str, Any]:
    descs: list[str] = []
    events: list[str] = []
    summary: list[int] = []
    for line in cgout_path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("desc:"):
            descs.append(line[5:].strip())
        elif line.startswith("events:"):
            events = line[7:].split()
        elif line.startswith("summary:"):
            summary = [int(x) for x in line[8:].split()]
    ev_map = dict(zip(events, summary))
    ir = ev_map.get("Ir", 0)
    l1m = ev_map.get("I1mr", 0) + ev_map.get("D1mr", 0) + ev_map.get("D1mw", 0)
    llm = ev_map.get("ILmr", 0) + ev_map.get("DLmr", 0) + ev_map.get("DLmw", 0)
    bm = ev_map.get("Bcm", 0) + ev_map.get("Bim", 0)
    cest = ir + 10 * bm + 10 * l1m + 100 * llm
    return {
        "cache_geometry": descs,
        "events": ev_map,
        "derived": {
            "L1_misses_total": l1m,
            "LL_misses_total": llm,
            "branch_mispredicts_total": bm,
            "cycle_estimate_CEst": cest,
            "l1_miss_rate_per_1k_insns": round(1000.0 * l1m / max(ir, 1), 4),
            "ll_miss_rate_per_1k_insns": round(1000.0 * llm / max(ir, 1), 4),
            "branch_mispredict_pct": round(
                100.0 * bm / max(ev_map.get("Bc", 0) + ev_map.get("Bi", 0), 1), 4
            ),
        },
    }


def cv_pct(vals: list[float]) -> float:
    if len(vals) < 2:
        return 0.0
    mean = statistics.fmean(vals)
    if mean == 0:
        return 0.0
    return 100.0 * statistics.stdev(vals) / mean


def probe_determinism(toolchains: dict[str, dict[str, str]]) -> dict[str, Any]:
    paranoid_path = Path("/proc/sys/kernel/perf_event_paranoid")
    paranoid = (
        int(paranoid_path.read_text(encoding="utf-8").strip())
        if paranoid_path.is_file()
        else None
    )
    det_env = {
        **os.environ,
        "MALLOC_CONF": "dirty_decay_ms:0,muzzy_decay_ms:0",
        "RUSTC_FORCE_RUSTC_VERSION": "rustc-perf",
        "RUSTC_FORCE_INCR_COMP_ARTIFACT_HEADER": "rustc-perf",
    }

    results: dict[str, Any] = {"perf_event_paranoid": paranoid, "toolchains": {}}
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        src = t / "lib.rs"
        src.write_text(SUBJECT_CRATE_LIB, encoding="utf-8")

        # 1) Run native perf_event_open + wall-clock strictly serially across toolchains
        perf_by_label: dict[str, list[dict[str, Any]]] = {}
        cg_jobs: list[tuple[str, int, Path, list[str]]] = []
        for label, tc in toolchains.items():
            rustc = tc["rustc_bin"]
            perf_runs = []
            for i in range(5):
                out_rlib = t / f"perf_{label}_{i}.rlib"
                argv = [
                    "setarch",
                    "x86_64",
                    "-R",
                    rustc,
                    "--crate-name",
                    "perf_subject",
                    "--crate-type=rlib",
                    "--edition=2021",
                    "-C",
                    "opt-level=2",
                    str(src),
                    "-o",
                    str(out_rlib),
                ]
                perf_runs.append(run_with_perf_event_open(argv, det_env))
            perf_by_label[label] = perf_runs

            for i in range(3):
                cgout = t / f"cgout_{label}_{i}"
                out_rlib = t / f"cg_{label}_{i}.rlib"
                cmd = [
                    "setarch",
                    "x86_64",
                    "-R",
                    "valgrind",
                    "--tool=cachegrind",
                    "--cache-sim=yes",
                    "--branch-sim=yes",
                    f"--cachegrind-out-file={cgout}",
                    rustc,
                    "--crate-name",
                    "perf_subject",
                    "--crate-type=rlib",
                    "--edition=2021",
                    "-C",
                    "opt-level=2",
                    str(src),
                    "-o",
                    str(out_rlib),
                ]
                cg_jobs.append((label, i, cgout, cmd))

        # 2) Execute the 6 deterministic Cachegrind runs concurrently across 6 cores
        def _run_cg_det(job: tuple[str, int, Path, list[str]]) -> tuple[str, int, dict[str, Any], list[str]]:
            lbl, idx, cgout, cmd = job
            m = run_measured(cmd, env=det_env)
            assert m["returncode"] == 0, m["stderr"]
            parsed_cg = parse_cachegrind_out(cgout)
            parsed_cg["valgrind_wall_ms"] = round(m["wall_ms"], 3)
            preview: list[str] = []
            if idx == 0 and shutil.which("cg_annotate"):
                ann = subprocess.check_output(
                    [
                        "cg_annotate",
                        "--auto=no",
                        "--show-percs=yes",
                        "--threshold=2.0",
                        str(cgout),
                    ],
                    text=True,
                )
                for ln in ann.splitlines():
                    if ln.strip() and not ln.startswith(("-", "I1 ", "D1 ", "LL ")):
                        preview.append(ln)
                    if len(preview) >= 18:
                        break
            return lbl, idx, parsed_cg, preview

        cg_by_label: dict[str, list[dict[str, Any]]] = defaultdict(list)
        preview_by_label: dict[str, list[str]] = {}
        with ThreadPoolExecutor(max_workers=6) as pool:
            for lbl, idx, parsed_cg, preview in pool.map(_run_cg_det, cg_jobs):
                cg_by_label[lbl].append(parsed_cg)
                if idx == 0:
                    preview_by_label[lbl] = preview

        for label in toolchains:
            perf_runs = perf_by_label[label]
            cg_runs = cg_by_label[label]
            cgann_top_lines = preview_by_label.get(label, [])

            wall_vals = [r["wall_ms"] for r in perf_runs]
            tclock_vals = [
                r["counts"].get("task-clock:u", 0) / 1e6 for r in perf_runs
            ]
            pf_vals = [float(r["counts"].get("page-faults:u", 0)) for r in perf_runs]
            ir_vals = [float(r["events"]["Ir"]) for r in cg_runs]
            cest_vals = [
                float(r["derived"]["cycle_estimate_CEst"]) for r in cg_runs
            ]

            results["toolchains"][label] = {
                "perf_event_open_5_runs": {
                    "wall_ms_runs": [round(x, 3) for x in wall_vals],
                    "wall_ms_median": round(statistics.median(wall_vals), 3),
                    "wall_ms_cv_pct": round(cv_pct(wall_vals), 4),
                    "task_clock_ms_runs": [round(x, 3) for x in tclock_vals],
                    "task_clock_ms_median": round(statistics.median(tclock_vals), 3),
                    "task_clock_ms_cv_pct": round(cv_pct(tclock_vals), 4),
                    "page_faults_runs": [int(x) for x in pf_vals],
                    "page_faults_cv_pct": round(cv_pct(pf_vals), 4),
                    "max_rss_kib_median": int(
                        statistics.median([r["max_rss_kib"] for r in perf_runs])
                    ),
                    "sample_counts_run0": perf_runs[0]["counts"],
                    "unavailable_pmu_events": perf_runs[0]["unavailable_events"],
                },
                "cachegrind_3_runs": {
                    "cache_geometry": cg_runs[0]["cache_geometry"],
                    "Ir_runs": [int(x) for x in ir_vals],
                    "Ir_median": int(statistics.median(ir_vals)),
                    "Ir_cv_pct": round(cv_pct(ir_vals), 6),
                    "Ir_max_min_ppm": round(
                        1e6 * (max(ir_vals) - min(ir_vals)) / max(ir_vals[0], 1.0), 3
                    ),
                    "CEst_runs": [int(x) for x in cest_vals],
                    "CEst_median": int(statistics.median(cest_vals)),
                    "CEst_cv_pct": round(cv_pct(cest_vals), 6),
                    "events_run0": cg_runs[0]["events"],
                    "derived_run0": cg_runs[0]["derived"],
                    "valgrind_slowdown_vs_native_wall": round(
                        cg_runs[0]["valgrind_wall_ms"] / max(statistics.median(wall_vals), 0.1),
                        2,
                    ),
                    "cg_annotate_preview": cgann_top_lines[:14],
                },
            }
    return results


# ---------------------------------------------------------------------------
# Probe 2: -Z time-passes JSON, -Z self-profile .mm_profdata, & IR volume
# ---------------------------------------------------------------------------


def parse_time_passes_json(stderr_text: str) -> list[dict[str, Any]]:
    passes = []
    prefix = "time: "
    for line in stderr_text.splitlines():
        if line.startswith(prefix):
            payload = line[len(prefix) :].strip()
            if payload.startswith("{"):
                passes.append(json.loads(payload))
    return passes


def parse_incremental_info(stderr_text: str) -> dict[str, Any]:
    total_nodes = 0
    total_edges = 0
    red_nodes = 0
    reused_cgus: str | None = None
    for line in stderr_text.splitlines():
        s = line.strip()
        if not s.startswith("[incremental]"):
            continue
        body = s[len("[incremental]") :].strip()
        if body.startswith("Total Node Count:"):
            total_nodes = int(body.split(":", 1)[1].strip())
        elif body.startswith("Total Edge Count:"):
            total_edges = int(body.split(":", 1)[1].strip())
        elif body.startswith("Red ") or body.startswith("Red|"):
            parts = [p.strip() for p in body.split("|")]
            if len(parts) >= 3 and parts[0] == "Red":
                red_nodes = int(parts[2])
        elif "re-using" in body:
            reused_cgus = body
    return {
        "total_dep_nodes": total_nodes,
        "total_dep_edges": total_edges,
        "red_nodes": red_nodes,
        "reused_cgu_summary": reused_cgus,
    }


def probe_self_profile_and_phases(
    toolchains: dict[str, dict[str, str]],
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    boot_env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}

    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        for label, tc in toolchains.items():
            rustc = tc["rustc_bin"]
            tc_res: dict[str, Any] = {"time_passes_profiles": {}, "self_profile_scenarios": {}}

            # 1) -Z time-passes -Z time-passes-format=json across Check, Debug (-O0), Opt (-O3)
            src_tp = t / f"tp_{label}.rs"
            src_tp.write_text(SUBJECT_CRATE_LIB, encoding="utf-8")
            for prof_name, extra_args in [
                ("Check", ["--emit=metadata"]),
                ("Debug_O0", ["-C", "opt-level=0", "--emit=dep-info,metadata,link"]),
                ("Opt_O3", ["-C", "opt-level=3", "--emit=dep-info,metadata,link"]),
            ]:
                odir = t / f"tp_out_{label}_{prof_name}"
                odir.mkdir(parents=True, exist_ok=True)
                m = run_measured(
                    [
                        rustc,
                        "--crate-name",
                        "perf_subject",
                        "--crate-type=rlib",
                        "--edition=2021",
                        "-Z",
                        "time-passes",
                        "-Z",
                        "time-passes-format=json",
                        *extra_args,
                        str(src_tp),
                        "--out-dir",
                        str(odir),
                    ],
                    env=boot_env,
                )
                assert m["returncode"] == 0, m["stderr"]
                entries = parse_time_passes_json(m["stderr"])
                by_pass = {e["pass"]: e for e in entries}
                tc_res["time_passes_profiles"][prof_name] = {
                    "wall_ms": round(m["wall_ms"], 3),
                    "max_rss_kib": m["max_rss_kib"],
                    "pass_count": len(entries),
                    "key_passes_ms": {
                        k: round(by_pass[k]["time"] * 1000.0, 3)
                        for k in [
                            "parse_crate",
                            "macro_expand_crate",
                            " late_resolve_crate",
                            "late_resolve_crate",
                            "type_check_crate",
                            "MIR_borrow_checking",
                            "monomorphization_collector_graph_walk",
                            "partition_and_assert_distinct_symbols",
                            "write_crate_metadata",
                            "codegen_crate",
                            "LLVM_passes",
                            "finish_ongoing_codegen",
                            "link",
                            "total",
                        ]
                        if k in by_pass
                    },
                    "peak_rss_end_bytes": max(
                        (e["rss_end"] or 0 for e in entries), default=0
                    ),
                }

            # 2) -Z self-profile across Full, IncrFull, IncrUnchanged, IncrPatched
            src_sp = t / f"sp_{label}.rs"
            incr_dir = t / f"incr_{label}"
            odir_sp = t / f"sp_out_{label}"
            odir_sp.mkdir(parents=True, exist_ok=True)

            scenarios = [
                ("Full", SUBJECT_CRATE_LIB, False),
                ("IncrFull", SUBJECT_CRATE_LIB, True),
                ("IncrUnchanged", SUBJECT_CRATE_LIB, True),
                ("IncrPatched", patched_subject_lib(), True),
            ]
            for scen_name, code_text, use_incr in scenarios:
                src_sp.write_text(code_text, encoding="utf-8")
                prof_dir = t / f"mm_{label}_{scen_name}"
                prof_dir.mkdir(parents=True, exist_ok=True)
                args = [
                    rustc,
                    "--crate-name",
                    "perf_subject",
                    "--crate-type=rlib",
                    "--edition=2021",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "codegen-units=4",
                    "--emit=dep-info,metadata,link",
                    f"-Zself-profile={prof_dir}",
                    "-Zself-profile-events=default,args,llvm",
                ]
                if use_incr:
                    args.extend(
                        [
                            f"-Cincremental={incr_dir}",
                            "-Zincremental-verify-ich",
                            "-Zincremental-info",
                        ]
                    )
                args.extend([str(src_sp), "--out-dir", str(odir_sp)])
                m = run_measured(args, env=boot_env)
                assert m["returncode"] == 0, m["stderr"]
                mm_file = next(prof_dir.glob("*.mm_profdata"))
                decoded = decode_mm_profdata(mm_file.read_bytes())
                decoded["wall_ms"] = round(m["wall_ms"], 3)
                decoded["max_rss_kib"] = m["max_rss_kib"]
                if use_incr:
                    decoded["incremental_info"] = parse_incremental_info(m["stderr"])
                tc_res["self_profile_scenarios"][scen_name] = decoded

            # 3) IR volume, mono-items, and -Z print-type-sizes
            vol_dir = t / f"vol_{label}"
            vol_dir.mkdir(parents=True, exist_ok=True)
            m_vol = run_measured(
                [
                    rustc,
                    "--crate-name",
                    "perf_subject",
                    "--crate-type=rlib",
                    "--edition=2021",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "codegen-units=1",
                    "--emit=mir,llvm-ir,llvm-bc,obj,metadata,link,dep-info",
                    "-Z",
                    "print-type-sizes",
                    "-Z",
                    "print-mono-items",
                    str(src_tp),
                    "--out-dir",
                    str(vol_dir),
                ],
                env=boot_env,
            )
            assert m_vol["returncode"] == 0, m_vol["stderr"]
            type_size_lines = [
                ln
                for ln in m_vol["stdout"].splitlines()
                if ln.startswith("print-type-size type:")
            ]
            mono_item_lines = [
                ln
                for ln in m_vol["stdout"].splitlines()
                if ln.startswith("MONO_ITEM ")
            ]
            mir_file = next(vol_dir.glob("*.mir"))
            ll_file = next(vol_dir.glob("*.ll"))
            bc_file = next(vol_dir.glob("*.bc"))
            obj_file = next(vol_dir.glob("*.o"))
            rmeta_file = next(vol_dir.glob("*.rmeta"))
            rlib_file = next(vol_dir.glob("*.rlib"))
            dep_file = next(vol_dir.glob("*.d"))
            mir_lines = mir_file.read_text(encoding="utf-8", errors="replace").splitlines()
            ll_lines = ll_file.read_text(encoding="utf-8", errors="replace").splitlines()
            mir_bbs = sum(
                1
                for ln in mir_lines
                if ln.lstrip().startswith("bb") and ln.rstrip().endswith("{")
            )
            ll_defines = sum(1 for ln in ll_lines if ln.startswith("define "))

            # Incremental cache on-disk breakdown from incr_dir
            incr_session_files: dict[str, int] = {}
            for p in incr_dir.rglob("*"):
                if p.is_file():
                    incr_session_files[p.name] = p.stat().st_size

            tc_res["ir_volume_and_artifact_footprint"] = {
                "mono_items_count": len(mono_item_lines),
                "type_size_records_count": len(type_size_lines),
                "top_5_types": type_size_lines[:5],
                "mir_file_bytes": mir_file.stat().st_size,
                "mir_line_count": len(mir_lines),
                "mir_basic_blocks": mir_bbs,
                "llvm_ir_file_bytes": ll_file.stat().st_size,
                "llvm_ir_line_count": len(ll_lines),
                "llvm_ir_define_count": ll_defines,
                "llvm_bc_bytes": bc_file.stat().st_size,
                "object_file_bytes": obj_file.stat().st_size,
                "rmeta_bytes": rmeta_file.stat().st_size,
                "rlib_bytes": rlib_file.stat().st_size,
                "dep_info_bytes": dep_file.stat().st_size,
                "incremental_session_files_bytes": incr_session_files,
            }

            out[label] = tc_res
    return out


# ---------------------------------------------------------------------------
# Probe 3: Cargo Pipelining Critical-Path Latency & Parallel Scaling
# ---------------------------------------------------------------------------


def make_heavy_stage_crate(crate_dir: Path, name: str, dep_name: str | None) -> None:
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    deps_toml = f'{dep_name} = {{ path = "../{dep_name}" }}\n' if dep_name else ""
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\n{deps_toml}',
        encoding="utf-8",
    )
    dep_call = f"{dep_name}::exported_api(seed)" if dep_name else "seed as u64"
    # Generate 24 distinct non-inlined instantiated kernels so LLVM optimization/codegen
    # takes ~150-300 ms AFTER .rmeta is already emitted!
    fns = [
        f"pub fn exported_api(seed: usize) -> u64 {{ let base = {dep_call}; compute_all(base) }}",
        "fn step_mix<const K: u64>(mut x: u64, n: usize) -> [u64; 32] {",
        "    let mut arr = [0u64; 32];",
        "    let mut i = 0usize;",
        "    while i < n {",
        "        x = x.wrapping_mul(0x9e37_79b9_7f4a_7c15 ^ K).rotate_left(((i & 31) as u32) + 1);",
        "        arr[i & 31] = arr[i & 31].wrapping_add(x ^ (i as u64));",
        "        i += 1;",
        "    }",
        "    arr",
        "}",
    ]
    calls = []
    for k in range(1, 33):
        fns.append(
            f"#[inline(never)] pub fn kernel_{k}(x: u64) -> u64 {{ "
            f"let a = step_mix::<{k * 1315423911}>(x, 64); "
            f"a.iter().fold(0u64, |acc, &v| acc.rotate_left(7) ^ v.wrapping_mul({k * 17 + 3})) }}"
        )
        calls.append(f"kernel_{k}(base.wrapping_add({k}))")
    fns.append(
        "pub fn compute_all(base: u64) -> u64 {\n    "
        + "\n    ^ ".join(calls)
        + "\n}"
    )
    (crate_dir / "src" / "lib.rs").write_text("\n".join(fns) + "\n", encoding="utf-8")


WRAPPER_SCRIPT = """\
#!/usr/bin/env python3
import json, os, subprocess, sys, time

log_dir = os.environ["PIPE_PROBE_LOG_DIR"]
real_rustc = sys.argv[1]
rustc_args = sys.argv[2:]

crate_name = None
for i, a in enumerate(rustc_args):
    if a == "--crate-name" and i + 1 < len(rustc_args):
        crate_name = rustc_args[i + 1]
        break

t_start = time.monotonic_ns()
proc = subprocess.Popen([real_rustc, *rustc_args], stderr=subprocess.PIPE)
t_rmeta = None
t_link = None
chunks = []
assert proc.stderr is not None
while True:
    line = proc.stderr.readline()
    if not line:
        break
    now = time.monotonic_ns()
    sys.stderr.buffer.write(line)
    sys.stderr.buffer.flush()
    if line.startswith(b"{"):
        try:
            msg = json.loads(line.decode("utf-8", errors="replace"))
            if msg.get("$message_type") == "artifact":
                if msg.get("emit") == "metadata" and t_rmeta is None:
                    t_rmeta = now
                elif msg.get("emit") == "link" and t_link is None:
                    t_link = now
        except Exception:
            pass
rc = proc.wait()
t_end = time.monotonic_ns()

if crate_name and crate_name.startswith("stage_"):
    rec = {
        "crate": crate_name,
        "t_start_ns": t_start,
        "t_rmeta_ns": t_rmeta,
        "t_link_ns": t_link,
        "t_end_ns": t_end,
    }
    out_p = os.path.join(log_dir, f"{crate_name}_{os.getpid()}.json")
    with open(out_p, "w", encoding="utf-8") as f:
        json.dump(rec, f)
sys.exit(rc)
"""


def probe_pipelining_and_parallel_scaling(
    toolchains: dict[str, dict[str, str]],
) -> dict[str, Any]:
    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        ws = t / "ws"
        ws.mkdir()
        stages = ["stage_a", "stage_b", "stage_c", "stage_d"]
        (ws / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["stage_a", "stage_b", "stage_c", "stage_d"]\nresolver = "2"\n',
            encoding="utf-8",
        )
        prev = None
        for s in stages:
            make_heavy_stage_crate(ws / s, s, prev)
            prev = s

        wrapper = t / "rustc_pipe_wrapper.py"
        wrapper.write_text(WRAPPER_SCRIPT, encoding="utf-8")
        wrapper.chmod(0o755)

        for label, tc in toolchains.items():
            rustc = tc["rustc_bin"]
            cargo = tc["cargo_bin"]

            # 1) Cargo pipelined build (-j 4 --release) vs -j 1 sequential
            log_j4 = t / f"logs_j4_{label}"
            log_j4.mkdir()
            tgt_j4 = t / f"target_j4_{label}"
            m_j4 = run_measured(
                [cargo, "build", "--release", "-j", "4", "--target-dir", str(tgt_j4)],
                env={
                    **os.environ,
                    "RUSTC": rustc,
                    "RUSTC_WRAPPER": str(wrapper),
                    "PIPE_PROBE_LOG_DIR": str(log_j4),
                },
                cwd=ws,
            )
            assert m_j4["returncode"] == 0, m_j4["stderr"]

            stage_records = []
            for p in sorted(log_j4.glob("stage_*.json")):
                stage_records.append(json.loads(p.read_text(encoding="utf-8")))
            stage_records.sort(key=lambda r: r["crate"])
            origin_ns = min(r["t_start_ns"] for r in stage_records)
            end_all_ns = max(r["t_end_ns"] for r in stage_records)
            dag_wall_ms = (end_all_ns - origin_ns) / 1e6

            per_crate_timeline = []
            sum_total_ms = 0.0
            for r in stage_records:
                tot_ms = (r["t_end_ns"] - r["t_start_ns"]) / 1e6
                rmeta_ms = (
                    (r["t_rmeta_ns"] - r["t_start_ns"]) / 1e6
                    if r["t_rmeta_ns"]
                    else tot_ms
                )
                sum_total_ms += tot_ms
                per_crate_timeline.append(
                    {
                        "crate": r["crate"],
                        "start_offset_ms": round((r["t_start_ns"] - origin_ns) / 1e6, 2),
                        "rmeta_ready_offset_ms": round(
                            (r["t_rmeta_ns"] - origin_ns) / 1e6, 2
                        )
                        if r["t_rmeta_ns"]
                        else None,
                        "end_offset_ms": round((r["t_end_ns"] - origin_ns) / 1e6, 2),
                        "t_rmeta_ms": round(rmeta_ms, 2),
                        "t_total_ms": round(tot_ms, 2),
                        "rmeta_fraction_of_total": round(rmeta_ms / max(tot_ms, 0.001), 4),
                    }
                )

            crit_path_lower_bound_ms = sum(
                c["t_rmeta_ms"] for c in per_crate_timeline[:-1]
            ) + per_crate_timeline[-1]["t_total_ms"]

            # 2) Parallel frontend (-Z threads=1,2,4,8) & CGU scaling (-C codegen-units=1,4,16)
            # Build a multi-module single crate with 64 functions to stress frontend + backend
            big_src = t / f"big_{label}.rs"
            big_lines = ["#![allow(dead_code)]"]
            for m_idx in range(8):
                big_lines.append(f"pub mod mod_{m_idx} {{")
                for f_idx in range(12):
                    seed_c = (m_idx * 31 + f_idx * 17 + 1) * 2654435761
                    big_lines.append(
                        f"    #[inline(never)] pub fn work_{f_idx}(mut x: u64) -> u64 {{"
                        f"        let mut acc = {seed_c}u64;"
                        f"        let mut i = 0u64;"
                        f"        while i < 96 {{"
                        f"            x = x.wrapping_mul(6364136223846793005).wrapping_add(i ^ acc);"
                        f"            acc ^= x.rotate_right(((i & 31) as u32) + 1);"
                        f"            i += 1;"
                        f"        }}"
                        f"        acc"
                        f"    }}"
                    )
                big_lines.append("}")
            big_src.write_text("\n".join(big_lines) + "\n", encoding="utf-8")

            boot_env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
            cgu_scaling = {}
            for cgu in (1, 4, 16):
                med_runs = []
                rss_runs = []
                for r_i in range(3):
                    od = t / f"cgu_{label}_{cgu}_{r_i}"
                    od.mkdir()
                    m = run_measured(
                        [
                            rustc,
                            "--crate-name",
                            "big_cgu",
                            "--crate-type=rlib",
                            "--edition=2021",
                            "-C",
                            "opt-level=3",
                            "-C",
                            "lto=off",
                            "-C",
                            f"codegen-units={cgu}",
                            str(big_src),
                            "--out-dir",
                            str(od),
                        ],
                        env=boot_env,
                    )
                    assert m["returncode"] == 0, m["stderr"]
                    med_runs.append(m["wall_ms"])
                    rss_runs.append(m["max_rss_kib"])
                cgu_scaling[f"cgu_{cgu}"] = {
                    "wall_ms_median": round(statistics.median(med_runs), 2),
                    "max_rss_kib_median": int(statistics.median(rss_runs)),
                }
            base_cgu1 = cgu_scaling["cgu_1"]["wall_ms_median"]
            for k, v in cgu_scaling.items():
                v["speedup_vs_cgu_1"] = round(base_cgu1 / max(v["wall_ms_median"], 0.01), 3)

            frontend_threads_scaling = {}
            for zt in (1, 2, 4, 8):
                med_runs = []
                rss_runs = []
                for r_i in range(3):
                    od = t / f"zt_{label}_{zt}_{r_i}"
                    od.mkdir()
                    m = run_measured(
                        [
                            rustc,
                            "--crate-name",
                            "big_zt",
                            "--crate-type=rlib",
                            "--edition=2021",
                            "--emit=metadata",
                            f"-Zthreads={zt}",
                            str(big_src),
                            "--out-dir",
                            str(od),
                        ],
                        env=boot_env,
                    )
                    assert m["returncode"] == 0, m["stderr"]
                    med_runs.append(m["wall_ms"])
                    rss_runs.append(m["max_rss_kib"])
                frontend_threads_scaling[f"threads_{zt}"] = {
                    "check_wall_ms_median": round(statistics.median(med_runs), 2),
                    "max_rss_kib_median": int(statistics.median(rss_runs)),
                }
            base_t1 = frontend_threads_scaling["threads_1"]["check_wall_ms_median"]
            for k, v in frontend_threads_scaling.items():
                v["speedup_vs_threads_1"] = round(
                    base_t1 / max(v["check_wall_ms_median"], 0.01), 3
                )

            results[label] = {
                "cargo_4_stage_dag_pipelining": {
                    "non_pipelined_sum_of_crates_ms": round(sum_total_ms, 2),
                    "theoretical_rmeta_critical_path_ms": round(
                        crit_path_lower_bound_ms, 2
                    ),
                    "measured_pipelined_dag_wall_ms": round(dag_wall_ms, 2),
                    "pipelining_speedup_vs_sequential_sum": round(
                        sum_total_ms / max(dag_wall_ms, 0.01), 3
                    ),
                    "per_crate_timeline": per_crate_timeline,
                },
                "cgu_partition_scaling_O3_no_lto": cgu_scaling,
                "frontend_threads_check_scaling": frontend_threads_scaling,
            }
    return results


# ---------------------------------------------------------------------------
# Probe 4: Dynamic Heap Allocation Churn (Valgrind DHAT heap + copy modes)
# ---------------------------------------------------------------------------


def summarize_dhat_json(dh_path: Path) -> dict[str, Any]:
    dh = json.loads(dh_path.read_text(encoding="utf-8"))
    pps = dh.get("pps", [])
    total_bytes = sum(p.get("tb", 0) for p in pps)
    total_blocks = sum(p.get("tbk", 0) for p in pps)
    gmax_bytes = sum(p.get("mb", 0) for p in pps)
    gmax_blocks = sum(p.get("mbk", 0) for p in pps)
    end_bytes = sum(p.get("eb", 0) for p in pps)
    end_blocks = sum(p.get("ebk", 0) for p in pps)
    total_reads = sum(p.get("rb", 0) for p in pps)
    total_writes = sum(p.get("wb", 0) for p in pps)
    ftbl = dh.get("ftbl", [])

    top_pps = sorted(pps, key=lambda p: p.get("tb", 0), reverse=True)[:5]
    top_sites = []
    for p in top_pps:
        frames = [
            ftbl[idx] for idx in p.get("fs", [])[:3] if 0 <= idx < len(ftbl)
        ]
        top_sites.append(
            {
                "total_bytes": p.get("tb", 0),
                "total_blocks": p.get("tbk", 0),
                "at_tgmax_bytes": p.get("mb", 0),
                "top_frames": frames,
            }
        )

    return {
        "dhat_file_version": dh.get("dhatFileVersion"),
        "mode": dh.get("mode"),
        "time_unit": dh.get("tu"),
        "t_gmax_instrs": dh.get("tg"),
        "t_end_instrs": dh.get("te"),
        "total_bytes": total_bytes,
        "total_blocks": total_blocks,
        "at_t_gmax_bytes": gmax_bytes,
        "at_t_gmax_blocks": gmax_blocks,
        "at_t_end_bytes": end_bytes,
        "at_t_end_blocks": end_blocks,
        "total_bytes_read": total_reads,
        "total_bytes_written": total_writes,
        "churn_ratio_total_over_gmax": round(
            total_bytes / max(gmax_bytes, 1), 3
        ),
        "mean_block_size_bytes": round(total_bytes / max(total_blocks, 1), 2),
        "top_5_allocation_sites": top_sites,
    }


def probe_memory_and_dhat(toolchains: dict[str, dict[str, str]]) -> dict[str, Any]:
    out: dict[str, Any] = {label: {} for label in toolchains}
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        src = t / "lib.rs"
        src.write_text(SUBJECT_CRATE_LIB, encoding="utf-8")

        jobs: list[tuple[str, str, list[str], Path]] = []
        for label, tc in toolchains.items():
            rustc = tc["rustc_bin"]
            for mode_name, extra_rustc in [
                ("Check", ["--emit=metadata"]),
                ("Opt_O2", ["-C", "opt-level=2", "--emit=dep-info,metadata,link"]),
            ]:
                dh_heap = t / f"dhat_heap_{label}_{mode_name}.json"
                od = t / f"dh_out_{label}_{mode_name}"
                od.mkdir()
                jobs.append(
                    (
                        label,
                        mode_name,
                        [
                            "valgrind",
                            "--tool=dhat",
                            "--num-callers=6",
                            f"--dhat-out-file={dh_heap}",
                            rustc,
                            "--crate-name",
                            "perf_subject",
                            "--crate-type=rlib",
                            "--edition=2021",
                            *extra_rustc,
                            str(src),
                            "--out-dir",
                            str(od),
                        ],
                        dh_heap,
                    )
                )

            dh_copy = t / f"dhat_copy_{label}.json"
            od_c = t / f"dh_copy_out_{label}"
            od_c.mkdir()
            jobs.append(
                (
                    label,
                    "Check_copy_mode",
                    [
                        "valgrind",
                        "--tool=dhat",
                        "--mode=copy",
                        "--num-callers=6",
                        f"--dhat-out-file={dh_copy}",
                        rustc,
                        "--crate-name",
                        "perf_subject",
                        "--crate-type=rlib",
                        "--edition=2021",
                        "--emit=metadata",
                        str(src),
                        "--out-dir",
                        str(od_c),
                    ],
                    dh_copy,
                )
            )

        def _run_dhat_job(job: tuple[str, str, list[str], Path]) -> tuple[str, str, dict[str, Any]]:
            lbl, mname, cmd, dh_file = job
            m = run_measured(cmd)
            assert m["returncode"] == 0, m["stderr"]
            return lbl, mname, summarize_dhat_json(dh_file)

        with ThreadPoolExecutor(max_workers=6) as pool:
            for lbl, mname, summary in pool.map(_run_dhat_job, jobs):
                out[lbl][mname] = summary
    return out


# ---------------------------------------------------------------------------
# Probe 5: Asymptotic Pathological Scaling Sweeps
# ---------------------------------------------------------------------------


def gen_projection_nesting(depth: int) -> str:
    lines = [
        "pub trait Assoc { type Out; fn step(self) -> Self::Out; }",
        "pub struct Base(pub u64);",
        "impl Assoc for Base { type Out = u64; fn step(self) -> u64 { self.0 + 1 } }",
        "pub struct Wrap<T>(pub T);",
        "impl<T: Assoc> Assoc for Wrap<T> { type Out = T::Out; fn step(self) -> Self::Out { self.0.step() } }",
    ]
    ty = "Base"
    val = "Base(x)"
    for _ in range(depth):
        ty = f"Wrap<{ty}>"
        val = f"Wrap({val})"
    lines.append(f"pub fn normalize(x: u64) -> <{ty} as Assoc>::Out {{ ({val}).step() }}")
    return "\n".join(lines) + "\n"


def gen_match_matrix(cols: int) -> str:
    # Diagonal boolean matrix of size cols x cols: forces 2^cols or quadratic specialization
    arms = []
    for r in range(cols):
        cells = ["true" if c == r else "_" for c in range(cols)]
        arms.append(f"        ({', '.join(cells)}) => {r + 1},")
    arms.append(f"        ({', '.join(['false'] * cols)}) => 0,")
    arms.append("        _ => 999,")
    params = ", ".join(f"b{i}: bool" for i in range(cols))
    tup = ", ".join(f"b{i}" for i in range(cols))
    return f"pub fn check_exhaustiveness({params}) -> u32 {{\n    match ({tup}) {{\n" + "\n".join(arms) + "\n    }\n}\n"


def gen_mono_fanout(count: int) -> str:
    lines = [
        "pub trait Tag { const ID: u64; }",
        "#[inline(never)] pub fn generic_pipeline<T: Tag>(mut x: u64) -> u64 {",
        "    let mut i = 0u64;",
        "    while i < 8 { x = x.wrapping_mul(0x517cc1b727220a95) ^ T::ID ^ i; i += 1; }",
        "    x",
        "}",
    ]
    calls = []
    for i in range(count):
        lines.append(f"pub struct S{i}; impl Tag for S{i} {{ const ID: u64 = {i * 97 + 13}; }}")
        calls.append(f"generic_pipeline::<S{i}>(x)")
    lines.append("pub fn entry(x: u64) -> u64 {\n    " + "\n    ^ ".join(calls) + "\n}")
    return "\n".join(lines) + "\n"


def gen_large_fn_blocks(blocks: int) -> str:
    lines = ["pub fn giant_cfg(mut x: u64) -> u64 {"]
    for i in range(blocks):
        lines.append(
            f"    if (x.wrapping_add({i})) & 3 == 0 {{ x = x.rotate_left(5) ^ {i * 31 + 7}; }} else {{ x = x.wrapping_add({i * 13 + 1}); }}"
        )
    lines.append("    x\n}")
    return "\n".join(lines) + "\n"


def gen_tt_muncher(tokens: int) -> str:
    lines = [
        "#![recursion_limit = \"512\"]",
        "macro_rules! munch {",
        "    () => { 0u64 };",
        "    ($head:tt $($tail:tt)*) => { ($head as u64).wrapping_add(munch!($($tail)*)) };",
        "}",
        "pub fn expanded() -> u64 { munch!(" + " ".join("1" for _ in range(tokens)) + ") }",
    ]
    return "\n".join(lines) + "\n"


def fit_power_law_exponent(xs: list[int], ys: list[float]) -> float:
    lx = [math.log(float(x)) for x in xs]
    ly = [math.log(max(float(y), 1e-9)) for y in ys]
    mx = statistics.fmean(lx)
    my = statistics.fmean(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) ** 2 for a in lx)
    return round(num / den, 4) if den > 0 else 0.0


def probe_asymptotic_scaling(rustc_bin: str) -> dict[str, Any]:
    det_env = {
        **os.environ,
        "MALLOC_CONF": "dirty_decay_ms:0,muzzy_decay_ms:0",
        "RUSTC_FORCE_RUSTC_VERSION": "rustc-perf",
        "RUSTC_FORCE_INCR_COMP_ARTIFACT_HEADER": "rustc-perf",
    }
    dimensions = [
        ("projection_normalization_depth", [8, 16, 32, 64], gen_projection_nesting, ["--emit=metadata"]),
        ("match_exhaustiveness_arity", [4, 8, 12, 16], gen_match_matrix, ["--emit=metadata"]),
        ("monomorphization_fanout", [16, 64, 256], gen_mono_fanout, ["-C", "opt-level=2", "-C", "codegen-units=1"]),
        ("single_fn_cfg_branches", [64, 256, 1024], gen_large_fn_blocks, ["-C", "opt-level=2", "-C", "codegen-units=1"]),
        ("tt_muncher_macro_tokens", [16, 32, 64, 112], gen_tt_muncher, ["--emit=metadata"]),
    ]

    out: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        # Measure empty crate baseline Ir so we also compute marginal delta_Ir(N) = Ir(N) - Ir(0)!
        empty_src = t / "empty.rs"
        empty_src.write_text("pub fn noop() {}\n", encoding="utf-8")
        base_ir: dict[str, int] = {}
        for mode_key, flags in [
            ("check", ["--emit=metadata"]),
            ("opt", ["-C", "opt-level=2", "-C", "codegen-units=1"]),
        ]:
            cg_base = t / f"cg_base_{mode_key}"
            m_b = run_measured(
                [
                    "valgrind",
                    "--tool=cachegrind",
                    "--cache-sim=no",
                    "--branch-sim=no",
                    f"--cachegrind-out-file={cg_base}",
                    rustc_bin,
                    "--crate-name",
                    "empty_base",
                    "--crate-type=rlib",
                    "--edition=2021",
                    *flags,
                    str(empty_src),
                    "-o",
                    str(t / f"libempty_{mode_key}.rlib"),
                ],
                env=det_env,
            )
            assert m_b["returncode"] == 0, m_b["stderr"]
            base_ir[mode_key] = parse_cachegrind_out(cg_base)["events"]["Ir"]

        out["empty_crate_baseline_Ir"] = base_ir

        # First run all native timing/RSS measurements strictly serially on an uncontended host,
        # then execute the deterministic Cachegrind Ir runs across 6 workers!
        staged_cases: list[dict[str, Any]] = []
        for dim_name, sizes, gen_fn, extra_flags in dimensions:
            mode_key = "check" if "--emit=metadata" in extra_flags else "opt"
            for sz in sizes:
                sfile = t / f"{dim_name}_{sz}.rs"
                sfile.write_text(gen_fn(sz), encoding="utf-8")
                out_nat = t / f"lib_nat_{dim_name}_{sz}.rlib"
                m_nat = run_measured(
                    [
                        rustc_bin,
                        "--crate-name",
                        "stress_case",
                        "--crate-type=rlib",
                        "--edition=2021",
                        *extra_flags,
                        str(sfile),
                        "-o",
                        str(out_nat),
                    ],
                    env=det_env,
                )
                assert m_nat["returncode"] == 0, m_nat["stderr"]
                staged_cases.append(
                    {
                        "dim_name": dim_name,
                        "mode_key": mode_key,
                        "extra_flags": extra_flags,
                        "N": sz,
                        "sfile": sfile,
                        "source_bytes": sfile.stat().st_size,
                        "native_wall_ms": round(m_nat["wall_ms"], 3),
                        "max_rss_kib": m_nat["max_rss_kib"],
                    }
                )

        def _run_cg_case(c: dict[str, Any]) -> dict[str, Any]:
            dim_name = c["dim_name"]
            sz = c["N"]
            cg_p = t / f"cg_{dim_name}_{sz}"
            out_cg = t / f"lib_cg_{dim_name}_{sz}.rlib"
            m_cg = run_measured(
                [
                    "valgrind",
                    "--tool=cachegrind",
                    "--cache-sim=no",
                    "--branch-sim=no",
                    f"--cachegrind-out-file={cg_p}",
                    rustc_bin,
                    "--crate-name",
                    "stress_case",
                    "--crate-type=rlib",
                    "--edition=2021",
                    *c["extra_flags"],
                    str(c["sfile"]),
                    "-o",
                    str(out_cg),
                ],
                env=det_env,
            )
            assert m_cg["returncode"] == 0, m_cg["stderr"]
            ir_val = parse_cachegrind_out(cg_p)["events"]["Ir"]
            b_ir = base_ir[c["mode_key"]]
            delta_ir = max(ir_val - b_ir, 1)
            return {
                "dim_name": dim_name,
                "point": {
                    "N": sz,
                    "source_bytes": c["source_bytes"],
                    "native_wall_ms": c["native_wall_ms"],
                    "max_rss_kib": c["max_rss_kib"],
                    "total_Ir": ir_val,
                    "marginal_Ir_above_empty": delta_ir,
                    "marginal_Ir_per_unit_N": round(delta_ir / sz, 1),
                },
            }

        by_dim: dict[str, list[dict[str, Any]]] = defaultdict(list)
        with ThreadPoolExecutor(max_workers=6) as pool:
            for res in pool.map(_run_cg_case, staged_cases):
                by_dim[res["dim_name"]].append(res["point"])

        for dim_name, _, _, extra_flags in dimensions:
            points = sorted(by_dim[dim_name], key=lambda p: p["N"])
            out[dim_name] = {
                "extra_flags": extra_flags,
                "points": points,
                "marginal_Ir_power_law_exponent": fit_power_law_exponent(
                    [p["N"] for p in points],
                    [float(p["marginal_Ir_above_empty"]) for p in points],
                ),
            }
    return out


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------


def collect_host_metadata() -> dict[str, Any]:
    cpu_model = "unknown"
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for ln in cpuinfo.read_text(encoding="utf-8", errors="replace").splitlines():
            if ln.startswith("model name"):
                cpu_model = ln.split(":", 1)[1].strip()
                break
    valgrind_ver = (
        subprocess.check_output(["valgrind", "--version"], text=True).strip()
        if shutil.which("valgrind")
        else "unavailable"
    )
    return {
        "os": platform.system(),
        "kernel_release": platform.release(),
        "arch": platform.machine(),
        "logical_cpus": os.cpu_count(),
        "cpu_model": cpu_model,
        "valgrind_version": valgrind_ver,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Path to write compiler_perf_specimen.json",
    )
    ap.add_argument("--stable-selector", default="+1.99.1")
    ap.add_argument("--nightly-selector", default="+nightly")
    args = ap.parse_args()

    tc_stable = resolve_toolchain(args.stable_selector)
    tc_nightly = resolve_toolchain(args.nightly_selector)
    toolchains = {
        "stable_1_99_1": tc_stable,
        "nightly_1_102_0": tc_nightly,
    }

    replacements = [
        (tc_stable["sysroot"], "<SYSROOT_STABLE>"),
        (tc_nightly["sysroot"], "<SYSROOT_NIGHTLY>"),
    ]

    print("[1/5] Probing perf_event_open and Cachegrind determinism...", file=sys.stderr)
    det = probe_determinism(toolchains)

    print("[2/5] Probing -Z time-passes JSON and measureme v9 .mm_profdata...", file=sys.stderr)
    sp = probe_self_profile_and_phases(toolchains)

    print("[3/5] Probing Cargo time-to-.rmeta pipelining and parallel scaling...", file=sys.stderr)
    pipe = probe_pipelining_and_parallel_scaling(toolchains)

    print("[4/5] Probing Valgrind DHAT heap churn and copy modes...", file=sys.stderr)
    mem = probe_memory_and_dhat(toolchains)

    print("[5/5] Probing 5 asymptotic pathological scaling dimensions...", file=sys.stderr)
    asym = probe_asymptotic_scaling(tc_stable["rustc_bin"])

    specimen = {
        "schema": "rustc-compiler-perf-metrics-specimen/1",
        "observed_at": "2026-11-21",
        "host": collect_host_metadata(),
        "toolchains": toolchains,
        "probe_1_determinism_perf_and_cachegrind": det,
        "probe_2_internal_phases_and_self_profile": sp,
        "probe_3_cargo_pipelining_and_parallel_scaling": pipe,
        "probe_4_memory_footprint_and_dhat_churn": mem,
        "probe_5_asymptotic_scaling_sweeps": asym,
    }

    clean_specimen = sanitize_obj(specimen, replacements)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(clean_specimen, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {args.out} ({args.out.stat().st_size} bytes)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
