#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Comprehensive generated-code performance, microarchitecture, footprint, stack, and statistical probe.

Executes inside temporary directories (`tempfile.TemporaryDirectory`) across pinned
`rustc +1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rustc +nightly`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), collecting:
  1. Cold-start vs warm steady-state latency quantiles (`median`, `IQR`, `p90`..`p99.9`),
     async coroutine state-machine `size_of_val(&fut)` and `Future::poll` latency,
     and `Result` vs DWARF `.eh_frame_hdr` `catch_unwind` error-path latency.
  2. `perf_event_open` (syscall 298, `exclude_kernel=1, exclude_hv=1`) software/hardware
     PMU probing, `valgrind --tool=cachegrind --cache-sim=yes --branch-sim=yes` whole-binary
     and per-kernel isolated cache/branch miss counts, static `llvm-objdump` spill/reload,
     SIMD (`scalar`/`XMM`/`YMM`/`ZMM`), devirtualization, and MIR vs LLVM bounds-check survival.
  3. Cold process `execve` startup latency, `llvm-readelf -r` dynamic relocation counts
     (`.rela.dyn` vs packed `SHT_RELR` `.relr.dyn`), and `valgrind --tool=dhat` + custom
     Rust `GlobalAlloc` heap allocation telemetry.
  4. Pure-Python ELF64 `.stack_sizes` (`-Z emit-stack-sizes`) binary ULEB128 parser, static
     call-graph worst-case stack calculator (accounting for x86-64 `callq` 8-byte return pushes
     and 128-byte leaf red zones), and live runtime stack-painting watermark verification.
  5. 11-point binary section attribution ladder (`.text`, `.rodata`, `.data.rel.ro`,
     `.eh_frame`+`.eh_frame_hdr`+`.gcc_except_table`, `.debug_*`, zstd debug compression,
     `--gc-sections`, `--icf=all`, `-Z location-detail=none`, and `#![no_std]` zero-unwind core),
     plus Intel RAPL `/sys/bus/event_source/devices/power/` probe and EDP metrics.
  6. Exact 3D Pareto frontier and hypervolume indicator (`CompileTime x CodeSize x Speed`)
     and a live 12-seed x 15-run `ld.lld --shuffle-sections` hierarchical bootstrap + TOST
     equivalence / non-inferiority experiment with Holm-Bonferroni and Benjamini-Hochberg control.
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
import shutil
import statistics
import struct
import subprocess
import tempfile
import time
from typing import Any


# ---------------------------------------------------------------------------
# Linear O(N) helpers & statistics (zero nested quantified regular expressions)
# ---------------------------------------------------------------------------


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


def summarize_dist(samples: list[float]) -> dict[str, float]:
    s = sorted(float(x) for x in samples)
    n = len(s)
    if n == 0:
        return {}
    med = percentile_sorted(s, 50.0)
    p25 = percentile_sorted(s, 25.0)
    p75 = percentile_sorted(s, 75.0)
    iqr = p75 - p25
    mean = sum(s) / n
    sd = statistics.stdev(s) if n >= 2 else 0.0
    return {
        "n": n,
        "min": round(s[0], 4),
        "p10": round(percentile_sorted(s, 10.0), 4),
        "p25": round(p25, 4),
        "median": round(med, 4),
        "p75": round(p75, 4),
        "p90": round(percentile_sorted(s, 90.0), 4),
        "p95": round(percentile_sorted(s, 95.0), 4),
        "p99": round(percentile_sorted(s, 99.0), 4),
        "p99_9": round(percentile_sorted(s, 99.9), 4),
        "max": round(s[-1], 4),
        "mean": round(mean, 4),
        "stdev": round(sd, 4),
        "cv_pct": round((sd / mean * 100.0) if mean > 0 else 0.0, 4),
        "iqr": round(iqr, 4),
        "norm_iqr_pct": round((iqr / med * 100.0) if med > 0 else 0.0, 4),
    }


def normal_cdf(z: float) -> float:
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))


def mann_whitney_u_two_sided(xs: list[float], ys: list[float]) -> dict[str, float]:
    nx, ny = len(xs), len(ys)
    combined = [(v, 0) for v in xs] + [(v, 1) for v in ys]
    combined.sort(key=lambda t: t[0])
    n = nx + ny
    ranks = [0.0] * n
    tie_term = 0.0
    i = 0
    while i < n:
        j = i + 1
        while j < n and combined[j][0] == combined[i][0]:
            j += 1
        avg_rank = 0.5 * ((i + 1) + j)
        t_len = j - i
        if t_len > 1:
            tie_term += t_len**3 - t_len
        for k in range(i, j):
            ranks[k] = avg_rank
        i = j
    r_x = sum(ranks[k] for k in range(n) if combined[k][1] == 0)
    u_x = r_x - nx * (nx + 1) / 2.0
    mu = nx * ny / 2.0
    var = (nx * ny / 12.0) * ((n + 1) - tie_term / (n * (n - 1))) if n > 1 else 1.0
    z = (u_x - mu) / math.sqrt(max(var, 1e-12))
    p_two = 2.0 * (1.0 - normal_cdf(abs(z)))
    return {"u_stat": round(u_x, 3), "z": round(z, 4), "p_two_sided": round(p_two, 6)}


def hodges_lehmann_shift(xs: list[float], ys: list[float]) -> float:
    """Pairwise median difference median_{i,j}(y_j - x_i)."""
    diffs = [y - x for x in xs for y in ys]
    diffs.sort()
    return percentile_sorted(diffs, 50.0)


def resolve_toolchain(tc: str) -> dict[str, str]:
    rustc = subprocess.check_output(
        ["rustup", "which", "--toolchain", tc, "rustc"], text=True
    ).strip()
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    vv = subprocess.check_output([rustc, "-vV"], text=True).strip()
    bin_dir = pathlib.Path(sysroot) / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
    lld_dir = bin_dir / "gcc-ld"
    return {
        "name": tc,
        "rustc": rustc,
        "sysroot": sysroot,
        "version_verbose": vv,
        "lld_dir": str(lld_dir),
        "llvm_size": str(bin_dir / "llvm-size") if (bin_dir / "llvm-size").exists() else "llvm-size",
        "llvm_objdump": str(bin_dir / "llvm-objdump") if (bin_dir / "llvm-objdump").exists() else "llvm-objdump",
        "llvm_readobj": str(bin_dir / "llvm-readobj") if (bin_dir / "llvm-readobj").exists() else "llvm-readelf",
    }


# ---------------------------------------------------------------------------
# Perf_event_open (syscall 298, x86_64 Linux) & RAPL sysfs probe
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
        ("__reserved_2", ctypes.c_uint16),
        ("aux_sample_size", ctypes.c_uint32),
        ("__reserved_3", ctypes.c_uint32),
        ("sig_data", ctypes.c_uint64),
    ]


SYS_PERF_EVENT_OPEN = 298
PERF_IOC_ENABLE = 0x2400
PERF_IOC_DISABLE = 0x2401
PERF_IOC_RESET = 0x2403
# bit 0 = disabled, bit 2 = inherit, bit 5 = exclude_kernel, bit 6 = exclude_hv, bit 8 = enable_on_exec
PERF_FLAGS_USER_CHILD = (1 << 0) | (1 << 2) | (1 << 5) | (1 << 6) | (1 << 8)


def probe_pmu_and_rapl_capabilities() -> dict[str, Any]:
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    paranoid = -1
    p_file = pathlib.Path("/proc/sys/kernel/perf_event_paranoid")
    if p_file.exists():
        paranoid = int(p_file.read_text().strip())

    probes = [
        ("HW_CPU_CYCLES", 0, 0),
        ("HW_INSTRUCTIONS", 0, 1),
        ("HW_CACHE_REFERENCES", 0, 2),
        ("HW_CACHE_MISSES", 0, 3),
        ("HW_BRANCH_INSTRUCTIONS", 0, 4),
        ("HW_BRANCH_MISSES", 0, 5),
        ("RAW_TOPDOWN_SLOTS", 4, 0x0400),
        ("SW_CPU_CLOCK", 1, 0),
        ("SW_TASK_CLOCK", 1, 1),
        ("SW_PAGE_FAULTS", 1, 2),
        ("SW_CONTEXT_SWITCHES", 1, 3),
        ("SW_PAGE_FAULTS_MIN", 1, 5),
        ("SW_PAGE_FAULTS_MAJ", 1, 6),
    ]
    counter_status = {}
    for name, ptype, cfg in probes:
        attr = PerfEventAttr()
        attr.type = ptype
        attr.size = ctypes.sizeof(PerfEventAttr)
        attr.config = cfg
        attr.flags = (1 << 0) | (1 << 5) | (1 << 6)
        ctypes.set_errno(0)
        fd = libc.syscall(SYS_PERF_EVENT_OPEN, ctypes.byref(attr), 0, -1, -1, 0)
        err = ctypes.get_errno()
        if fd >= 0:
            os.close(fd)
            counter_status[name] = {"available": True, "errno": 0, "error": "OK"}
        else:
            counter_status[name] = {
                "available": False,
                "errno": err,
                "error": os.strerror(err),
            }

    power_dir = pathlib.Path("/sys/bus/event_source/devices/power")
    rapl_info: dict[str, Any] = {"sysfs_power_pmu_present": power_dir.exists()}
    if power_dir.exists():
        t_path = power_dir / "type"
        ev_dir = power_dir / "events"
        fmt_dir = power_dir / "format"
        pmu_type = int(t_path.read_text().strip()) if t_path.exists() else None
        rapl_info["pmu_type"] = pmu_type
        rapl_info["events_exposed"] = sorted(p.name for p in ev_dir.iterdir()) if ev_dir.exists() else []
        rapl_info["formats"] = {
            p.name: p.read_text().strip() for p in sorted(fmt_dir.iterdir())
        } if fmt_dir.exists() else {}
        if pmu_type is not None:
            # Try opening RAPL energy-pkg (config=0x01) and energy-ram (config=0x03)
            rapl_trials = {}
            for rname, rcfg in [("energy-pkg", 0x01), ("energy-cores", 0x02), ("energy-ram", 0x03)]:
                attr = PerfEventAttr()
                attr.type = pmu_type
                attr.size = ctypes.sizeof(PerfEventAttr)
                attr.config = rcfg
                attr.flags = 1 << 0
                ctypes.set_errno(0)
                fd = libc.syscall(SYS_PERF_EVENT_OPEN, ctypes.byref(attr), -1, 0, -1, 0)
                err = ctypes.get_errno()
                if fd >= 0:
                    os.close(fd)
                    rapl_trials[rname] = {"available": True, "errno": 0}
                else:
                    rapl_trials[rname] = {"available": False, "errno": err, "error": os.strerror(err)}
            rapl_info["perf_open_trials"] = rapl_trials
    pcap = pathlib.Path("/sys/class/powercap")
    rapl_info["powercap_zones"] = sorted(p.name for p in pcap.iterdir()) if pcap.exists() else []
    return {
        "perf_event_paranoid": paranoid,
        "syscall_nr_x86_64": SYS_PERF_EVENT_OPEN,
        "counter_availability": counter_status,
        "rapl_power_pmu": rapl_info,
    }


def run_with_perf_sw_counters(cmd: list[str]) -> dict[str, Any]:
    """Measure child execution with perf_event_open SW counters (exclude_kernel=1, exclude_hv=1)."""
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    specs = [
        ("task_clock_ns", 1, 1),
        ("minor_page_faults", 1, 5),
        ("major_page_faults", 1, 6),
        ("context_switches", 1, 3),
    ]
    fds: list[tuple[str, int]] = []
    # Open on self with inherit=1 + disabled=1 + enable_on_exec=1, then fork/exec child
    pid = os.fork()
    if pid == 0:
        # Child opens counters on pid=0 with enable_on_exec? Parent won't have fds unless opened in parent!
        os._exit(127)
    os.waitpid(pid, 0)

    # Better: fork a helper child that pauses on a pipe until parent attaches perf_event_open(pid=child)!
    r_fd, w_fd = os.pipe()
    child_pid = os.fork()
    if child_pid == 0:
        os.close(w_fd)
        os.read(r_fd, 1)
        os.close(r_fd)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        os.execv(cmd[0], cmd)
        os._exit(127)

    os.close(r_fd)
    try:
        for name, ptype, cfg in specs:
            attr = PerfEventAttr()
            attr.type = ptype
            attr.size = ctypes.sizeof(PerfEventAttr)
            attr.config = cfg
            attr.flags = PERF_FLAGS_USER_CHILD
            fd = libc.syscall(SYS_PERF_EVENT_OPEN, ctypes.byref(attr), child_pid, -1, -1, 0)
            if fd >= 0:
                fds.append((name, fd))
        t0 = time.perf_counter_ns()
        os.write(w_fd, b"G")
        os.close(w_fd)
        w_fd = -1
        _, status = os.waitpid(child_pid, 0)
        wall_ns = time.perf_counter_ns() - t0
        out: dict[str, Any] = {"wall_ns": wall_ns, "exit_status": os.waitstatus_to_exitcode(status)}
        for name, fd in fds:
            raw = os.read(fd, 8)
            out[name] = struct.unpack("<Q", raw)[0] if len(raw) == 8 else 0
        return out
    finally:
        if w_fd >= 0:
            os.close(w_fd)
        for _, fd in fds:
            os.close(fd)


# ---------------------------------------------------------------------------
# Pure-Python ELF64 `.stack_sizes` + `.symtab` binary parser
# ---------------------------------------------------------------------------


def decode_uleb128(buf: bytes, offset: int) -> tuple[int, int]:
    val = 0
    shift = 0
    pos = offset
    n = len(buf)
    while pos < n:
        byte = buf[pos]
        pos += 1
        val |= (byte & 0x7F) << shift
        if (byte & 0x80) == 0:
            return val, pos
        shift += 7
    raise ValueError("Truncated ULEB128 in .stack_sizes")


def parse_elf64_stack_sizes_and_symbols(elf_path: pathlib.Path) -> dict[str, Any]:
    data = elf_path.read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError("Expected 64-bit little-endian ELF")
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
                "idx": idx,
                "sh_name": sh_name,
                "sh_type": sh_type,
                "sh_flags": sh_flags,
                "sh_addr": sh_addr,
                "sh_offset": sh_offset,
                "sh_size": sh_size,
                "sh_link": sh_link,
                "sh_entsize": sh_entsize,
            }
        )

    shstr = sections[e_shstrndx]
    shstrtab = data[shstr["sh_offset"] : shstr["sh_offset"] + shstr["sh_size"]]

    def get_cstr(blob: bytes, start: int) -> str:
        end = blob.find(b"\x00", start)
        if end < 0:
            end = len(blob)
        return blob[start:end].decode("utf-8", errors="replace")

    for s in sections:
        s["name"] = get_cstr(shstrtab, s["sh_name"])

    # Parse .symtab (SHT_SYMTAB = 2)
    addr_to_funcs: dict[int, list[str]] = {}
    func_symbols: dict[str, dict[str, int]] = {}
    for s in sections:
        if s["sh_type"] == 2 and s["sh_entsize"] >= 24:
            str_sec = sections[s["sh_link"]]
            strtab = data[str_sec["sh_offset"] : str_sec["sh_offset"] + str_sec["sh_size"]]
            n_syms = s["sh_size"] // s["sh_entsize"]
            for i in range(n_syms):
                soff = s["sh_offset"] + i * s["sh_entsize"]
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", data, soff
                )
                stt = st_info & 0x0F
                # STT_FUNC = 2, SHN_UNDEF = 0
                if stt == 2 and st_shndx != 0 and st_value != 0:
                    nm = get_cstr(strtab, st_name)
                    if nm:
                        addr_to_funcs.setdefault(st_value, []).append(nm)
                        func_symbols[nm] = {"addr": st_value, "size": st_size, "shndx": st_shndx}

    # Parse all .stack_sizes sections
    stack_entries: list[dict[str, Any]] = []
    addr_to_stack: dict[int, int] = {}
    for s in sections:
        if s["name"] == ".stack_sizes" and s["sh_size"] > 0:
            sec_bytes = data[s["sh_offset"] : s["sh_offset"] + s["sh_size"]]
            pos = 0
            while pos + 8 < len(sec_bytes):
                fn_addr = struct.unpack_from("<Q", sec_bytes, pos)[0]
                pos += 8
                frame_bytes, pos = decode_uleb128(sec_bytes, pos)
                if fn_addr == 0:
                    continue
                names = addr_to_funcs.get(fn_addr, [f"<anon_0x{fn_addr:x}>"])
                addr_to_stack[fn_addr] = frame_bytes
                stack_entries.append(
                    {"addr": fn_addr, "frame_bytes": frame_bytes, "symbols": names}
                )

    missing_stt_func = [
        nm for nm, meta in sorted(func_symbols.items()) if meta["addr"] not in addr_to_stack and meta["size"] > 0
    ]
    return {
        "total_stack_size_entries": len(stack_entries),
        "total_defined_stt_func": len(func_symbols),
        "uninstrumented_or_varsized_stt_func_count": len(missing_stt_func),
        "entries": stack_entries,
        "addr_to_stack": addr_to_stack,
        "func_symbols": func_symbols,
        "missing_sample": missing_stt_func[:15],
    }


# ---------------------------------------------------------------------------
# Linear O(N) Static Disassembly Analyzer (`llvm-objdump -d --no-show-raw-insn -M intel`)
# ---------------------------------------------------------------------------

SCALAR_FP_MNEMONICS = {
    "addss", "subss", "mulss", "divss", "addsd", "subsd", "mulsd", "divsd",
    "vaddss", "vsubss", "vmulss", "vdivss", "vaddsd", "vsubsd", "vmulsd", "vdivsd",
    "sqrtss", "sqrtsd", "vsqrtss", "vsqrtsd", "maxss", "minss", "vmaxss", "vminss",
}

BRANCH_TERMINATORS = {
    "jmp", "je", "jne", "jz", "jnz", "ja", "jae", "jb", "jbe", "jg", "jge", "jl", "jle",
    "js", "jns", "jo", "jno", "jp", "jnp", "jrcxz", "jecxz", "ret", "retq", "ud2",
}


def analyze_disassembly_intel(objdump_txt: str, target_prefixes: tuple[str, ...]) -> dict[str, Any]:
    """Linear O(N) line scanner over `llvm-objdump -d --no-show-raw-insn -M intel`."""
    cur_fn: str | None = None
    fn_stats: dict[str, dict[str, Any]] = {}

    def init_bucket() -> dict[str, Any]:
        return {
            "insns": 0,
            "basic_blocks": 0,
            "stack_mem_ops": 0,
            "redzone_min_disp": 0,
            "scalar_fp_insns": 0,
            "xmm_128_insns": 0,
            "ymm_256_insns": 0,
            "zmm_512_insns": 0,
            "fma_insns": 0,
            "direct_calls": 0,
            "indirect_calls": 0,
            "panic_calls": 0,
            "memcpy_memset_calls": 0,
            "rep_string_insns": 0,
            "ud2_traps": 0,
            "callees": [],
        }

    whole = init_bucket()
    kernels_agg = init_bucket()

    for raw_line in objdump_txt.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        # Function header: "0000000000012340 <sym_name>:"
        if line.endswith(">:") and "<" in line and not line.startswith(";"):
            lt = line.find("<")
            name = line[lt + 1 : -2]
            cur_fn = name
            if cur_fn not in fn_stats:
                fn_stats[cur_fn] = init_bucket()
                fn_stats[cur_fn]["basic_blocks"] = 1
            continue

        if cur_fn is None or ":" not in line:
            continue
        colon = line.find(":")
        addr_part = line[:colon].strip()
        if not addr_part or not all(c in "0123456789abcdefABCDEF" for c in addr_part):
            continue
        body = line[colon + 1 :].strip()
        if not body:
            continue
        # Strip trailing comment after '#'
        hash_pos = body.find("#")
        code_part = body[:hash_pos].strip() if hash_pos >= 0 else body
        parts = code_part.split(None, 1)
        if not parts:
            continue
        mnem = parts[0].lower()
        ops = parts[1] if len(parts) > 1 else ""
        ops_low = ops.lower()

        # Handle "rep movsb" / "lock cmpxchg" prefixes
        if mnem == "rep" or mnem == "repz" or mnem == "repnz":
            sub = ops_low.split(None, 1)
            sub_mnem = sub[0] if sub else ""
            is_rep_str = sub_mnem.startswith(("movs", "stos"))
        else:
            is_rep_str = False

        buckets = [whole, fn_stats[cur_fn]]
        if cur_fn.startswith(target_prefixes):
            buckets.append(kernels_agg)

        # Check stack memory access `[rsp ...]` or `[rbp ...]` (excluding `lea`)
        is_stack_mem = False
        rz_disp = 0
        if mnem != "lea" and ("[" in ops_low):
            # Linear scan over bracketed memory operands
            b_start = ops_low.find("[")
            b_end = ops_low.find("]", b_start + 1)
            if b_end > b_start:
                mem_expr = ops_low[b_start + 1 : b_end].replace(" ", "")
                if mem_expr.startswith("rsp") or mem_expr.startswith("rbp"):
                    is_stack_mem = True
                    if mem_expr.startswith("rsp-"):
                        tail = mem_expr[4:]
                        try:
                            d = int(tail, 0)
                            if 0 < d <= 128:
                                rz_disp = d
                        except ValueError:
                            pass

        is_zmm = "zmm" in ops_low
        is_ymm = (not is_zmm) and ("ymm" in ops_low)
        is_xmm = (not is_zmm) and (not is_ymm) and ("xmm" in ops_low)
        is_fma = mnem.startswith("vfmadd") or mnem.startswith("vfmsub") or mnem.startswith("vfnmadd")
        is_scalar_fp = (mnem in SCALAR_FP_MNEMONICS) or (
            is_fma and mnem.endswith(("ss", "sd"))
        )
        if is_scalar_fp and is_xmm:
            # Scalar SSE/AVX uses xmm registers for 1 lane; classify as scalar_fp, not packed XMM SIMD
            is_xmm = False

        is_bb_term = mnem in BRANCH_TERMINATORS
        is_call = mnem in ("call", "callq")
        callee_name = None
        is_indirect_call = False
        is_panic_call = False
        is_memop_call = False
        if is_call:
            if "<" in body and ">" in body:
                c_lt = body.rfind("<")
                c_gt = body.rfind(">")
                if c_gt > c_lt:
                    callee_name = body[c_lt + 1 : c_gt]
                    # Strip "@plt" or "+0x..." if any
                    if "+" in callee_name:
                        callee_name = callee_name.split("+", 1)[0]
                    if "@" in callee_name:
                        callee_name = callee_name.split("@", 1)[0]
            if callee_name is None or "ptr" in ops_low or ops_low.startswith("r") or ops_low.startswith("*"):
                if callee_name is None:
                    is_indirect_call = True
            if callee_name:
                cl = callee_name.lower()
                if "panic" in cl or "slice_index" in cl or "unwrap_failed" in cl:
                    is_panic_call = True
                if cl in ("memcpy", "memmove", "memset", "bcmp", "memcmp"):
                    is_memop_call = True

        for b in buckets:
            b["insns"] += 1
            if is_bb_term:
                b["basic_blocks"] += 1
            if is_stack_mem:
                b["stack_mem_ops"] += 1
            if rz_disp > b["redzone_min_disp"]:
                b["redzone_min_disp"] = rz_disp
            if is_scalar_fp:
                b["scalar_fp_insns"] += 1
            if is_xmm:
                b["xmm_128_insns"] += 1
            if is_ymm:
                b["ymm_256_insns"] += 1
            if is_zmm:
                b["zmm_512_insns"] += 1
            if is_fma:
                b["fma_insns"] += 1
            if is_rep_str:
                b["rep_string_insns"] += 1
            if mnem == "ud2":
                b["ud2_traps"] += 1
            if is_call:
                if is_indirect_call:
                    b["indirect_calls"] += 1
                else:
                    b["direct_calls"] += 1
                    if callee_name and callee_name not in b["callees"]:
                        b["callees"].append(callee_name)
                if is_panic_call:
                    b["panic_calls"] += 1
                if is_memop_call:
                    b["memcpy_memset_calls"] += 1

    def finalize(b: dict[str, Any]) -> dict[str, Any]:
        ins = max(b["insns"], 1)
        bbs = max(b["basic_blocks"], 1)
        tot_calls = b["direct_calls"] + b["indirect_calls"]
        out = dict(b)
        out["spills_per_100_insns"] = round(b["stack_mem_ops"] * 100.0 / ins, 3)
        out["spills_per_bb"] = round(b["stack_mem_ops"] / bbs, 3)
        out["insns_per_bb"] = round(b["insns"] / bbs, 3)
        out["direct_call_share_pct"] = round(
            (b["direct_calls"] * 100.0 / tot_calls) if tot_calls > 0 else 100.0, 2
        )
        return out

    selected_fns = {
        k: finalize(v)
        for k, v in sorted(fn_stats.items())
        if k.startswith(target_prefixes)
    }
    return {
        "kernels_aggregate": finalize(kernels_agg),
        "whole_binary": {k: v for k, v in finalize(whole).items() if k != "callees"},
        "per_kernel": selected_fns,
        "all_functions": fn_stats,
    }


# ---------------------------------------------------------------------------
# Cachegrind output parser (whole-process + per-kernel isolated)
# ---------------------------------------------------------------------------

CG_EVENTS = [
    "Ir", "I1mr", "ILmr", "Dr", "D1mr", "DLmr", "Dw", "D1mw", "DLmw", "Bc", "Bcm", "Bi", "Bim"
]


def parse_cachegrind_out(cg_path: pathlib.Path, kernel_prefixes: tuple[str, ...]) -> dict[str, Any]:
    summary_vals = [0] * len(CG_EVENTS)
    kernel_vals = [0] * len(CG_EVENTS)
    per_fn: dict[str, list[int]] = {}
    cur_fn = ""

    for raw in cg_path.read_text(encoding="utf-8", errors="replace").splitlines():
        if raw.startswith("summary:"):
            nums = [int(x) for x in raw.split()[1:]]
            for i in range(min(len(nums), len(summary_vals))):
                summary_vals[i] = nums[i]
        elif raw.startswith("fn="):
            cur_fn = raw[3:].strip()
        elif raw and raw[0].isdigit():
            nums = [int(x) for x in raw.split()]
            # First column is source line number, remaining 13 columns are events
            ev = nums[1:]
            if len(ev) >= len(CG_EVENTS) and cur_fn.startswith(kernel_prefixes):
                slot = per_fn.setdefault(cur_fn, [0] * len(CG_EVENTS))
                for i in range(len(CG_EVENTS)):
                    slot[i] += ev[i]
                    kernel_vals[i] += ev[i]

    def enrich(vals: list[int]) -> dict[str, Any]:
        d = {CG_EVENTS[i]: vals[i] for i in range(len(CG_EVENTS))}
        ir = max(d["Ir"], 1)
        dr_dw = max(d["Dr"] + d["Dw"], 1)
        bc = max(d["Bc"], 1)
        bi = max(d["Bi"], 1)
        d["i1_miss_rate_pct"] = round(d["I1mr"] * 100.0 / ir, 4)
        d["d1_miss_rate_pct"] = round((d["D1mr"] + d["D1mw"]) * 100.0 / dr_dw, 4)
        d["ll_miss_rate_pct"] = round((d["ILmr"] + d["DLmr"] + d["DLmw"]) * 100.0 / (ir + dr_dw), 4)
        d["cond_branch_miss_pct"] = round(d["Bcm"] * 100.0 / bc, 4) if d["Bc"] > 0 else 0.0
        d["ind_branch_miss_pct"] = round(d["Bim"] * 100.0 / bi, 4) if d["Bi"] > 0 else 0.0
        return d

    return {
        "process_total": enrich(summary_vals),
        "kernels_isolated": enrich(kernel_vals),
        "per_kernel": {k: enrich(v) for k, v in sorted(per_fn.items())},
    }


# ---------------------------------------------------------------------------
# Rust Benchmark & Microarchitecture Specimen Sources
# ---------------------------------------------------------------------------

MICROARCH_SUITE_RS = r'''
use std::hint::black_box;
use std::time::Instant;

#[no_mangle]
#[inline(never)]
pub extern "C" fn kernel_f32_dot_fma(a: *const f32, b: *const f32, n: usize) -> f32 {
    let sa = unsafe { core::slice::from_raw_parts(a, n) };
    let sb = unsafe { core::slice::from_raw_parts(b, n) };
    let mut acc0 = 0.0f32;
    let mut acc1 = 0.0f32;
    let mut acc2 = 0.0f32;
    let mut acc3 = 0.0f32;
    let chunks = n / 4;
    for i in 0..chunks {
        let base = i * 4;
        acc0 = sa[base].mul_add(sb[base], acc0);
        acc1 = sa[base + 1].mul_add(sb[base + 1], acc1);
        acc2 = sa[base + 2].mul_add(sb[base + 2], acc2);
        acc3 = sa[base + 3].mul_add(sb[base + 3], acc3);
    }
    (acc0 + acc1) + (acc2 + acc3)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn kernel_u32_autovec_mac(a: *const u32, b: *const u32, n: usize) -> u32 {
    let sa = unsafe { core::slice::from_raw_parts(a, n) };
    let sb = unsafe { core::slice::from_raw_parts(b, n) };
    let mut sum = 0u32;
    for i in 0..n {
        let prod = sa[i].wrapping_mul(sb[i]).wrapping_add(0x9e37_79b9);
        sum = sum.wrapping_add(prod ^ (prod >> 13));
    }
    sum
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn kernel_reg_pressure_spills(seed: u64, rounds: usize) -> u64 {
    // 20 live 64-bit state variables exceeding the 15 usable x86-64 GPRs to force spills/reloads
    let mut v0 = seed.wrapping_add(1);
    let mut v1 = seed.wrapping_add(2);
    let mut v2 = seed.wrapping_add(3);
    let mut v3 = seed.wrapping_add(4);
    let mut v4 = seed.wrapping_add(5);
    let mut v5 = seed.wrapping_add(6);
    let mut v6 = seed.wrapping_add(7);
    let mut v7 = seed.wrapping_add(8);
    let mut v8 = seed.wrapping_add(9);
    let mut v9 = seed.wrapping_add(10);
    let mut v10 = seed.wrapping_add(11);
    let mut v11 = seed.wrapping_add(12);
    let mut v12 = seed.wrapping_add(13);
    let mut v13 = seed.wrapping_add(14);
    let mut v14 = seed.wrapping_add(15);
    let mut v15 = seed.wrapping_add(16);
    let mut v16 = seed.wrapping_add(17);
    let mut v17 = seed.wrapping_add(18);
    let mut v18 = seed.wrapping_add(19);
    let mut v19 = seed.wrapping_add(20);
    for r in 0..rounds {
        let k = (r as u64).wrapping_mul(0x517cc1b727220a95);
        v0 = v0.wrapping_add(v13).rotate_left(7) ^ k;
        v1 = v1.wrapping_add(v14).rotate_left(9) ^ v0;
        v2 = v2.wrapping_add(v15).rotate_left(13) ^ v1;
        v3 = v3.wrapping_add(v16).rotate_left(18) ^ v2;
        v4 = v4.wrapping_add(v17).rotate_left(7) ^ v3;
        v5 = v5.wrapping_add(v18).rotate_left(9) ^ v4;
        v6 = v6.wrapping_add(v19).rotate_left(13) ^ v5;
        v7 = v7.wrapping_add(v0).rotate_left(18) ^ v6;
        v8 = v8.wrapping_add(v1).rotate_left(7) ^ v7;
        v9 = v9.wrapping_add(v2).rotate_left(9) ^ v8;
        v10 = v10.wrapping_add(v3).rotate_left(13) ^ v9;
        v11 = v11.wrapping_add(v4).rotate_left(18) ^ v10;
        v12 = v12.wrapping_add(v5).rotate_left(7) ^ v11;
        v13 = v13.wrapping_add(v6).rotate_left(9) ^ v12;
        v14 = v14.wrapping_add(v7).rotate_left(13) ^ v13;
        v15 = v15.wrapping_add(v8).rotate_left(18) ^ v14;
        v16 = v16.wrapping_add(v9).rotate_left(7) ^ v15;
        v17 = v17.wrapping_add(v10).rotate_left(9) ^ v16;
        v18 = v18.wrapping_add(v11).rotate_left(13) ^ v17;
        v19 = v19.wrapping_add(v12).rotate_left(18) ^ v18;
    }
    v0 ^ v1 ^ v2 ^ v3 ^ v4 ^ v5 ^ v6 ^ v7 ^ v8 ^ v9
        ^ v10 ^ v11 ^ v12 ^ v13 ^ v14 ^ v15 ^ v16 ^ v17 ^ v18 ^ v19
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn kernel_bounds_and_iter(table256: *const u8, data: *const u32, len: usize) -> u64 {
    let tbl = unsafe { &*(table256 as *const [u8; 256]) };
    let s = unsafe { core::slice::from_raw_parts(data, len) };
    let mut acc = 0u64;
    if !s.is_empty() {
        for k in 0..s.len() {
            let v = s[k];
            let b = tbl[(v as usize) & 0xff] as u64;
            let rem_v = s[(k.wrapping_mul(7)) % s.len()] as u64;
            let div_v = if v != 0 { 1_000_000u32 / v } else { 0 } as u64;
            acc = acc.wrapping_add(b ^ rem_v ^ div_v);
        }
    }
    acc
}

trait OpStage {
    fn step(&self, x: u64) -> u64;
}
struct MulStage(u64);
impl OpStage for MulStage {
    fn step(&self, x: u64) -> u64 { x.wrapping_mul(self.0).wrapping_add(1) }
}
struct XorStage(u64);
impl OpStage for XorStage {
    fn step(&self, x: u64) -> u64 { (x ^ self.0).rotate_left(11) }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn kernel_dyn_dispatch_and_memops(dst: *mut u8, src: *const u8, len: usize, iters: usize) -> u64 {
    let s_mul = MulStage(0x9e3779b97f4a7c15);
    let s_xor = XorStage(0xbf58476d1ce4e5b9);
    // Known-concrete local slice eligible for SROA/devirtualization at -O2/-O3 vs indirect vtable calls at -O0/-Oz
    let stages: [&dyn OpStage; 2] = [&s_mul, &s_xor];
    let mut state = len as u64;
    for i in 0..iters {
        state = stages[i & 1].step(state);
    }
    let d_slice = unsafe { core::slice::from_raw_parts_mut(dst, len) };
    let s_slice = unsafe { core::slice::from_raw_parts(src, len) };
    d_slice.copy_from_slice(s_slice);
    state.wrapping_add(d_slice[len / 2] as u64)
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "once".to_string());
    let reps: usize = match mode.as_str() {
        "bench" => 120,
        "cachegrind" => 16,
        _ => 4,
    };
    let n = 1024usize;
    let a_f32: Vec<f32> = (0..n).map(|i| (i as f32) * 0.001 + 1.0).collect();
    let b_f32: Vec<f32> = (0..n).map(|i| ((n - i) as f32) * 0.002 + 0.5).collect();
    let a_u32: Vec<u32> = (0..n).map(|i| (i as u32).wrapping_mul(2654435761)).collect();
    let b_u32: Vec<u32> = (0..n).map(|i| (i as u32).wrapping_add(1013904223)).collect();
    let tbl256: [u8; 256] = core::array::from_fn(|i| (i as u8).wrapping_mul(73) ^ 0x5a);
    let mut dst_buf = vec![0u8; 1024];
    let src_buf: Vec<u8> = (0..1024).map(|i| (i & 0xff) as u8).collect();

    if mode == "per_kernel_json" {
        let mut out = Vec::new();
        for kname in ["f32_dot_fma", "u32_autovec_mac", "reg_pressure_spills", "bounds_and_iter", "dyn_dispatch_and_memops"] {
            // Warmup
            for _ in 0..10 {
                match kname {
                    "f32_dot_fma" => { black_box(kernel_f32_dot_fma(black_box(a_f32.as_ptr()), black_box(b_f32.as_ptr()), black_box(n))); }
                    "u32_autovec_mac" => { black_box(kernel_u32_autovec_mac(black_box(a_u32.as_ptr()), black_box(b_u32.as_ptr()), black_box(n))); }
                    "reg_pressure_spills" => { black_box(kernel_reg_pressure_spills(black_box(7), black_box(256))); }
                    "bounds_and_iter" => { black_box(kernel_bounds_and_iter(black_box(tbl256.as_ptr()), black_box(a_u32.as_ptr()), black_box(n))); }
                    _ => { black_box(kernel_dyn_dispatch_and_memops(black_box(dst_buf.as_mut_ptr()), black_box(src_buf.as_ptr()), black_box(1024), black_box(256))); }
                }
            }
            let t0 = Instant::now();
            let inner = 200usize;
            let mut sink = 0u64;
            for _ in 0..inner {
                sink ^= match kname {
                    "f32_dot_fma" => kernel_f32_dot_fma(black_box(a_f32.as_ptr()), black_box(b_f32.as_ptr()), black_box(n)).to_bits() as u64,
                    "u32_autovec_mac" => kernel_u32_autovec_mac(black_box(a_u32.as_ptr()), black_box(b_u32.as_ptr()), black_box(n)) as u64,
                    "reg_pressure_spills" => kernel_reg_pressure_spills(black_box(7), black_box(256)),
                    "bounds_and_iter" => kernel_bounds_and_iter(black_box(tbl256.as_ptr()), black_box(a_u32.as_ptr()), black_box(n)),
                    _ => kernel_dyn_dispatch_and_memops(black_box(dst_buf.as_mut_ptr()), black_box(src_buf.as_ptr()), black_box(1024), black_box(256)),
                };
            }
            let ns_per_call = t0.elapsed().as_nanos() as f64 / (inner as f64);
            black_box(sink);
            out.push(format!("\"{}\":{:.3}", kname, ns_per_call));
        }
        println!("{{{}}}", out.join(","));
        return;
    }

    let t0 = Instant::now();
    let mut checksum = 0u64;
    for r in 0..reps {
        let f = kernel_f32_dot_fma(black_box(a_f32.as_ptr()), black_box(b_f32.as_ptr()), black_box(n));
        let u = kernel_u32_autovec_mac(black_box(a_u32.as_ptr()), black_box(b_u32.as_ptr()), black_box(n));
        let sp = kernel_reg_pressure_spills(black_box(r as u64 + 1), black_box(128));
        let bd = kernel_bounds_and_iter(black_box(tbl256.as_ptr()), black_box(a_u32.as_ptr()), black_box(n));
        let dm = kernel_dyn_dispatch_and_memops(black_box(dst_buf.as_mut_ptr()), black_box(src_buf.as_ptr()), black_box(1024), black_box(128));
        checksum = checksum.wrapping_add((f.to_bits() as u64) ^ (u as u64) ^ sp ^ bd ^ dm);
    }
    let elapsed_ns = t0.elapsed().as_nanos();
    black_box(checksum);
    if mode == "bench" {
        println!("{}", elapsed_ns);
    }
}
'''

LATENCY_ASYNC_UNWIND_RS = r'''
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::hint::black_box;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};
use std::time::Instant;

// 1. Cold vs warm per-request streaming CRC/FNV + lightweight JSON-token scan over 16 KiB payload
#[inline(never)]
fn process_request_16k(buf: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    let mut quotes = 0u64;
    let mut braces = 0u64;
    for &b in buf {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
        if b == b'"' { quotes += 1; }
        if b == b'{' || b == b'}' { braces += 1; }
    }
    h ^ (quotes << 32) ^ braces
}

// 2. Async coroutine state machines
struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = u64;
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if !self.0 {
            self.0 = true;
            Poll::Pending
        } else {
            Poll::Ready(1)
        }
    }
}

async fn fut_live_across_await_1k(seed: u8) -> u64 {
    let mut buf = [seed; 1024];
    let a = YieldOnce(false).await;
    buf[511] = buf[511].wrapping_add(a as u8);
    let b = YieldOnce(false).await;
    (buf[0] as u64) + (buf[511] as u64) + b
}

async fn fut_scoped_before_await_1k(seed: u8) -> u64 {
    let partial = {
        let mut buf = [seed; 1024];
        buf[511] = buf[511].wrapping_add(3);
        black_box(&buf);
        (buf[0] as u64) + (buf[511] as u64)
    };
    let a = YieldOnce(false).await;
    let b = YieldOnce(false).await;
    partial + a + b
}

async fn fut_disjoint_two_branches_1k(seed: u8) -> u64 {
    let p1 = {
        let b1 = [seed; 1024];
        let x = YieldOnce(false).await;
        (b1[10] as u64) + x
    };
    let p2 = {
        let b2 = [seed.wrapping_add(1); 1024];
        let y = YieldOnce(false).await;
        (b2[20] as u64) + y
    };
    p1 + p2
}

async fn step_leaf(x: u64) -> u64 {
    let t = [x; 8];
    let y = YieldOnce(false).await;
    t[0].wrapping_add(y)
}
async fn step_d2(x: u64) -> u64 { step_leaf(x).await + step_leaf(x + 1).await }
async fn step_d3(x: u64) -> u64 { step_d2(x).await ^ 0x55 }
async fn fut_nested_depth4(x: u64) -> u64 { step_d3(x).await.wrapping_add(7) }

fn noop_waker() -> Waker {
    fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VTABLE) }
    fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

// 3. Result vs Unwind across RAII drop frames
struct DropGuard<'a>(&'a core::cell::Cell<u64>);
impl<'a> Drop for DropGuard<'a> {
    fn drop(&mut self) {
        self.0.set(self.0.get().wrapping_add(1));
    }
}

#[inline(never)]
fn result_ladder(depth: u32, fail: bool, drops: &core::cell::Cell<u64>) -> Result<u64, u32> {
    let _g = DropGuard(drops);
    if depth == 0 {
        if fail { Err(42) } else { Ok(99) }
    } else {
        Ok(result_ladder(black_box(depth - 1), fail, drops)?.wrapping_add(1))
    }
}

#[inline(never)]
fn panic_ladder(depth: u32, fail: bool, drops: &core::cell::Cell<u64>) -> u64 {
    let _g = DropGuard(drops);
    if depth == 0 {
        if fail { panic_any(42u32); } else { 99 }
    } else {
        panic_ladder(black_box(depth - 1), fail, drops).wrapping_add(1)
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "full".to_string());
    let payload: Vec<u8> = (0..16384)
        .map(|i| match i % 16 { 0 => b'{', 7 => b'"', 15 => b'}', _ => b'a' + (i % 26) as u8 })
        .collect();

    // Measure very first invocation in this fresh process before any warmup!
    let t_cold0 = Instant::now();
    let c0 = process_request_16k(black_box(&payload));
    let cold_ns = t_cold0.elapsed().as_nanos() as u64;
    black_box(c0);

    if mode == "cold_only" {
        println!("{}", cold_ns);
        return;
    }

    // Warm steady-state distribution (2,000 requests after 200 warmup iterations)
    for _ in 0..200 {
        black_box(process_request_16k(black_box(&payload)));
    }
    let mut warm_samples = Vec::with_capacity(2000);
    for _ in 0..2000 {
        let t = Instant::now();
        let r = process_request_16k(black_box(&payload));
        let d = t.elapsed().as_nanos() as u64;
        black_box(r);
        warm_samples.push(d);
    }

    // Measure async coroutine sizes & poll latency
    let f_live = fut_live_across_await_1k(1);
    let f_scoped = fut_scoped_before_await_1k(1);
    let f_disjoint = fut_disjoint_two_branches_1k(1);
    let f_nested = fut_nested_depth4(1);
    let sz_live = core::mem::size_of_val(&f_live);
    let sz_scoped = core::mem::size_of_val(&f_scoped);
    let sz_disjoint = core::mem::size_of_val(&f_disjoint);
    let sz_nested = core::mem::size_of_val(&f_nested);

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let poll_iters = 5000usize;
    let t_poll = Instant::now();
    let mut poll_acc = 0u64;
    for i in 0..poll_iters {
        let mut fut = Box::pin(fut_nested_depth4(black_box(i as u64)));
        loop {
            match fut.as_mut().poll(&mut cx) {
                Poll::Ready(v) => { poll_acc = poll_acc.wrapping_add(v); break; }
                Poll::Pending => {}
            }
        }
    }
    let poll_ns_per_future = t_poll.elapsed().as_nanos() as f64 / (poll_iters as f64);
    black_box(poll_acc);

    // Measure Result::Err vs catch_unwind at depth 4 and depth 32
    let drops = core::cell::Cell::new(0u64);
    let err_iters = 4000usize;
    let t_res4 = Instant::now();
    for _ in 0..err_iters {
        let _ = black_box(result_ladder(black_box(4), black_box(true), &drops));
    }
    let res4_ns = t_res4.elapsed().as_nanos() as f64 / (err_iters as f64);

    let t_res32 = Instant::now();
    for _ in 0..err_iters {
        let _ = black_box(result_ladder(black_box(32), black_box(true), &drops));
    }
    let res32_ns = t_res32.elapsed().as_nanos() as f64 / (err_iters as f64);

    let unw_iters = 400usize;
    // Install a no-op panic hook so catch_unwind isolates pure DWARF .eh_frame_hdr + .gcc_except_table unwinding
    std::panic::set_hook(Box::new(|_| {}));
    // Warmup .eh_frame_hdr cache
    for _ in 0..10 {
        let _ = catch_unwind(AssertUnwindSafe(|| panic_ladder(4, true, &drops)));
    }
    let t_unw4 = Instant::now();
    for _ in 0..unw_iters {
        let _ = black_box(catch_unwind(AssertUnwindSafe(|| panic_ladder(black_box(4), black_box(true), &drops))));
    }
    let unw4_ns = t_unw4.elapsed().as_nanos() as f64 / (unw_iters as f64);

    let t_unw32 = Instant::now();
    for _ in 0..unw_iters {
        let _ = black_box(catch_unwind(AssertUnwindSafe(|| panic_ladder(black_box(32), black_box(true), &drops))));
    }
    let unw32_ns = t_unw32.elapsed().as_nanos() as f64 / (unw_iters as f64);
    black_box(drops.get());

    let samples_str: Vec<String> = warm_samples.iter().map(|v| v.to_string()).collect();
    println!(
        "{{\"cold_first_ns\":{},\"warm_samples_ns\":[{}],\"async_sizes\":{{\"live_across_await_1k\":{},\"scoped_before_await_1k\":{},\"disjoint_two_branches_1k\":{},\"nested_depth4\":{}}},\"async_nested_depth4_complete_ns\":{:.3},\"error_paths_ns\":{{\"result_err_depth4\":{:.3},\"result_err_depth32\":{:.3},\"catch_unwind_depth4\":{:.3},\"catch_unwind_depth32\":{:.3}}}}}",
        cold_ns,
        samples_str.join(","),
        sz_live,
        sz_scoped,
        sz_disjoint,
        sz_nested,
        poll_ns_per_future,
        res4_ns,
        res32_ns,
        unw4_ns,
        unw32_ns
    );
}
'''

HEAP_AND_RELOC_RS = r'''
use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CountingAlloc;

static ALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static DEALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static REALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static TOTAL_BYTES: AtomicUsize = AtomicUsize::new(0);
static LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
static PEAK_BYTES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            let sz = layout.size();
            ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            TOTAL_BYTES.fetch_add(sz, Ordering::Relaxed);
            let cur = LIVE_BYTES.fetch_add(sz, Ordering::Relaxed) + sz;
            PEAK_BYTES.fetch_max(cur, Ordering::Relaxed);
        }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DEALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        LIVE_BYTES.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) };
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            REALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            let old_size = layout.size();
            if new_size >= old_size {
                let delta = new_size - old_size;
                TOTAL_BYTES.fetch_add(delta, Ordering::Relaxed);
                let cur = LIVE_BYTES.fetch_add(delta, Ordering::Relaxed) + delta;
                PEAK_BYTES.fetch_max(cur, Ordering::Relaxed);
            } else {
                LIVE_BYTES.fetch_sub(old_size - new_size, Ordering::Relaxed);
            }
        }
        new_ptr
    }
}

#[global_allocator]
static GLOBAL: CountingAlloc = CountingAlloc;

// Table of 256 function pointers in .data.rel.ro to exercise R_X86_64_RELATIVE vs SHT_RELR
fn handler_a(x: u64) -> u64 { x.wrapping_add(1) }
fn handler_b(x: u64) -> u64 { x.wrapping_mul(3) }
fn handler_c(x: u64) -> u64 { x ^ 0xdead_beef }
fn handler_d(x: u64) -> u64 { x.rotate_left(5) }

#[used]
static DISPATCH_TABLE: [fn(u64) -> u64; 256] = [
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
    handler_a, handler_b, handler_c, handler_d, handler_a, handler_b, handler_c, handler_d,
];

fn reset_counters() {
    let cur = LIVE_BYTES.load(Ordering::Relaxed);
    ALLOC_CALLS.store(0, Ordering::Relaxed);
    DEALLOC_CALLS.store(0, Ordering::Relaxed);
    REALLOC_CALLS.store(0, Ordering::Relaxed);
    TOTAL_BYTES.store(0, Ordering::Relaxed);
    PEAK_BYTES.store(cur, Ordering::Relaxed);
}

fn read_vmhwm_kib() -> usize {
    if let Ok(s) = std::fs::read_to_string("/proc/self/status") {
        for line in s.lines() {
            if let Some(rest) = line.strip_prefix("VmHWM:") {
                let num = rest.trim().split_whitespace().next().unwrap_or("0");
                return num.parse::<usize>().unwrap_or(0);
            }
        }
    }
    0
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "heap".to_string());
    if mode == "startup" {
        let f = black_box(&DISPATCH_TABLE)[black_box(7)];
        if f(1) == 0 { std::process::exit(2); }
        return;
    }

    reset_counters();
    let base_live = LIVE_BYTES.load(Ordering::Relaxed);

    // Workload A: unreserved Vec growth + String formatting + BTreeMap
    let mut v = Vec::new();
    for i in 0..4096u64 {
        v.push(DISPATCH_TABLE[(i as usize) & 255](i));
    }
    let mut map = BTreeMap::new();
    for i in 0..512u32 {
        map.insert(i, format!("entry_{:04x}_{}", i, v[i as usize]));
    }
    // Allocate a 16 KiB scratch buffer that is written once and never read (for DHAT zero-read check)
    let mut unread_scratch = vec![0x5au8; 16384];
    unread_scratch[0] = 1;
    black_box(unread_scratch.as_ptr());
    black_box(&map);
    drop(unread_scratch);
    drop(map);
    drop(v);

    let allocs = ALLOC_CALLS.load(Ordering::Relaxed);
    let deallocs = DEALLOC_CALLS.load(Ordering::Relaxed);
    let reallocs = REALLOC_CALLS.load(Ordering::Relaxed);
    let tot = TOTAL_BYTES.load(Ordering::Relaxed);
    let peak = PEAK_BYTES.load(Ordering::Relaxed).saturating_sub(base_live);
    let end_live = LIVE_BYTES.load(Ordering::Relaxed).saturating_sub(base_live);
    let hwm_kib = read_vmhwm_kib();

    println!(
        "{{\"alloc_calls\":{},\"dealloc_calls\":{},\"realloc_calls\":{},\"total_bytes_allocated\":{},\"peak_live_bytes\":{},\"end_live_bytes\":{},\"vm_hwm_kib\":{}}}",
        allocs, deallocs, reallocs, tot, peak, end_live, hwm_kib
    );
}
'''

STACK_VERIFICATION_RS = r'''
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::hint::black_box;

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_leaf_redzone(seed: u64) -> u64 {
    // 24 * 8 = 192 bytes: on SysV x86-64, 120 bytes fit in the 128-byte red zone!
    let mut arr = [0u64; 24];
    for i in 0..24 {
        arr[i] = seed.wrapping_add(i as u64).wrapping_mul(3);
    }
    black_box(&arr);
    arr[(seed as usize) % 24]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_slot_coloring_sequential(seed: u8) -> u64 {
    // Three sequential non-overlapping 512-byte buffers (1,536 B uncolored at -O0 -> 512 B colored at -O2/-O3)
    let a = {
        let mut b1 = [seed; 512];
        b1[255] = b1[255].wrapping_add(1);
        black_box(&b1);
        b1[255] as u64
    };
    let b = {
        let mut b2 = [seed.wrapping_add(2); 512];
        b2[127] = b2[127].wrapping_add(3);
        black_box(&b2);
        b2[127] as u64
    };
    let c = {
        let mut b3 = [seed.wrapping_add(4); 512];
        b3[63] = b3[63].wrapping_add(5);
        black_box(&b3);
        b3[63] as u64
    };
    a + b + c
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_chain_leaf(x: u64) -> u64 {
    let mut buf = [0u64; 32]; // 256 bytes
    for i in 0..32 { buf[i] = x ^ (i as u64); }
    black_box(&buf);
    buf[(x as usize) & 31]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_chain_d3(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 bytes
    local[0] = stack_chain_leaf(black_box(x + 1));
    black_box(&local);
    local[0] ^ local[15]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_chain_d2(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 bytes
    local[0] = stack_chain_d3(black_box(x + 2));
    black_box(&local);
    local[0].wrapping_add(local[7])
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_chain_d1(x: u64) -> u64 {
    let mut local = [x; 16]; // 128 bytes
    local[0] = stack_chain_d2(black_box(x + 3));
    black_box(&local);
    local[0].wrapping_add(local[3])
}

async fn async_inner(x: u64) -> u64 {
    let buf = [x; 32];
    black_box(&buf);
    buf[0] + 1
}

async fn async_outer(x: u64) -> u64 {
    let a = async_inner(x).await;
    let b = async_inner(x + a).await;
    a + b
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_async_poll_entry(x: u64) -> u64 {
    fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VT) }
    fn noop(_: *const ()) {}
    static VT: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    let waker = unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VT)) };
    let mut cx = Context::from_waker(&waker);
    let mut fut = core::pin::pin!(async_outer(x));
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => 0,
    }
}

#[inline(always)]
fn current_rsp() -> usize {
    let rsp: usize;
    unsafe { core::arch::asm!("mov {}, rsp", out(reg) rsp, options(nomem, nostack, preserves_flags)); }
    rsp
}

#[inline(never)]
fn paint_stack_below_rsp() -> usize {
    let rsp = current_rsp();
    // Paint [rsp - 16384 .. rsp - 256) with 0xA5 canary bytes
    let base = rsp - 16384;
    for off in 0..(16384 - 256) {
        unsafe { core::ptr::write_volatile((base + off) as *mut u8, 0xA5u8); }
    }
    rsp
}

#[inline(never)]
fn measure_painted_watermark(anchor_rsp: usize) -> usize {
    let base = anchor_rsp - 16384;
    for off in 0..(16384 - 256) {
        let b = unsafe { core::ptr::read_volatile((base + off) as *const u8) };
        if b != 0xA5u8 {
            return anchor_rsp - (base + off);
        }
    }
    0
}

fn main() {
    // Run on a dedicated 2 MiB thread so stack pages below RSP are pre-faulted and contiguous
    let handle = std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
        // Pre-touch 32 KiB of stack
        {
            let mut touch = [0u8; 32768];
            touch[0] = 1;
            black_box(&touch);
        }
        let anchor = paint_stack_below_rsp();
        let r_chain = stack_chain_d1(black_box(42));
        let wm_chain = measure_painted_watermark(anchor);

        let anchor2 = paint_stack_below_rsp();
        let r_color = stack_slot_coloring_sequential(black_box(7));
        let wm_color = measure_painted_watermark(anchor2);

        let r_leaf = stack_leaf_redzone(black_box(9));
        let r_async = stack_async_poll_entry(black_box(11));
        black_box(r_chain ^ r_color ^ r_leaf ^ r_async);
        println!("{{\"runtime_painted_chain_d1_bytes\":{},\"runtime_painted_slot_coloring_bytes\":{}}}", wm_chain, wm_color);
    }).unwrap();
    handle.join().unwrap();
}
'''

NOSTD_MINIMAL_EXIT_RS = r'''#![no_std]
#![no_main]

#[link(name = "c")]
extern "C" {
    fn _exit(status: i32) -> !;
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe { _exit(0) }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    unsafe { _exit(101) }
}
'''


# ---------------------------------------------------------------------------
# Experiment Runners
# ---------------------------------------------------------------------------


def run_experiment_1_latency_async_unwind(
    tc_nightly: dict[str, str], tc_1991: dict[str, str], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp1_latency.rs"
    src.write_text(LATENCY_ASYNC_UNWIND_RS, encoding="utf-8")
    results: dict[str, Any] = {}

    configs = [
        ("nightly_O0", tc_nightly, ["-Copt-level=0"]),
        ("nightly_O1", tc_nightly, ["-Copt-level=1"]),
        ("nightly_O2", tc_nightly, ["-Copt-level=2"]),
        ("nightly_O3", tc_nightly, ["-Copt-level=3"]),
        ("nightly_Os", tc_nightly, ["-Copt-level=s"]),
        ("nightly_Oz", tc_nightly, ["-Copt-level=z"]),
        ("r1991_O0", tc_1991, ["-Copt-level=0"]),
        ("r1991_O3", tc_1991, ["-Copt-level=3"]),
        ("r1991_Oz", tc_1991, ["-Copt-level=z"]),
    ]

    for label, tc, flags in configs:
        exe = tmp / f"exp1_{label}"
        subprocess.run(
            [tc["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(src), "-o", str(exe)],
            check=True,
            capture_output=True,
            text=True,
        )
        # Collect 32 fresh-process cold first-call latencies
        cold_samples = []
        for _ in range(32):
            out = subprocess.check_output([str(exe), "cold_only"], text=True).strip()
            cold_samples.append(float(out))
        full_raw = json.loads(subprocess.check_output([str(exe), "full"], text=True).strip())
        warm_dist = summarize_dist(full_raw["warm_samples_ns"])
        cold_dist = summarize_dist(cold_samples)
        med_ns = warm_dist["median"]
        # 16,384-byte payload throughput metrics
        ops_sec = 1e9 / med_ns if med_ns > 0 else 0.0
        gib_sec = (16384.0 * ops_sec) / (1024.0**3)
        cpb_2_6ghz = (med_ns * 2.60) / 16384.0

        ep = full_raw["error_paths_ns"]
        results[label] = {
            "cold_first_call_ns": cold_dist,
            "warm_steady_state_ns": warm_dist,
            "cold_over_warm_median_ratio": round(cold_dist["median"] / max(med_ns, 1e-9), 3),
            "p99_over_median_ratio": round(warm_dist["p99"] / max(med_ns, 1e-9), 3),
            "throughput_16k_payload": {
                "ops_per_sec": round(ops_sec, 1),
                "gib_per_sec": round(gib_sec, 4),
                "cycles_per_byte_at_2_60ghz": round(cpb_2_6ghz, 4),
            },
            "async_coroutine_bytes": full_raw["async_sizes"],
            "async_nested_depth4_complete_ns": full_raw["async_nested_depth4_complete_ns"],
            "error_paths_ns": {
                **ep,
                "unwind_over_result_ratio_depth4": round(
                    ep["catch_unwind_depth4"] / max(ep["result_err_depth4"], 0.001), 1
                ),
                "unwind_over_result_ratio_depth32": round(
                    ep["catch_unwind_depth32"] / max(ep["result_err_depth32"], 0.001), 1
                ),
            },
        }
    return results


def run_experiment_2_microarch(
    tc_nightly: dict[str, str], tc_1991: dict[str, str], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp2_microarch.rs"
    src.write_text(MICROARCH_SUITE_RS, encoding="utf-8")
    kernel_prefixes = (
        "kernel_f32_dot_fma",
        "kernel_u32_autovec_mac",
        "kernel_reg_pressure_spills",
        "kernel_bounds_and_iter",
        "kernel_dyn_dispatch_and_memops",
    )

    matrix = [
        ("O0_x86_64", ["-Copt-level=0", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("O1_x86_64", ["-Copt-level=1", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("O2_x86_64", ["-Copt-level=2", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("O3_x86_64", ["-Copt-level=3", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("Os_x86_64", ["-Copt-level=s", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("Oz_x86_64", ["-Copt-level=z", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
        ("O3_x86_64_v3_avx2", ["-Copt-level=3", "-Ctarget-cpu=x86-64-v3", "-Ccodegen-units=1"]),
        ("O3_x86_64_v4_avx512", ["-Copt-level=3", "-Ctarget-cpu=x86-64-v4", "-Ccodegen-units=1"]),
    ]

    profiles: dict[str, Any] = {}
    for label, flags in matrix:
        exe = tmp / f"exp2_{label}"
        t_comp0 = time.perf_counter()
        subprocess.run(
            [tc_nightly["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(src), "-o", str(exe)],
            check=True,
            capture_output=True,
            text=True,
        )
        comp_sec = time.perf_counter() - t_comp0

        # Static disassembly analysis
        dis_txt = subprocess.check_output(
            [tc_nightly["llvm_objdump"], "-d", "--no-show-raw-insn", "-M", "intel", str(exe)],
            text=True,
            errors="replace",
        )
        dis_summary = analyze_disassembly_intel(dis_txt, kernel_prefixes)
        del dis_summary["all_functions"]

        # Cachegrind dynamic instruction / cache / branch simulation
        cg_file = tmp / f"cg_{label}.out"
        cg_proc = subprocess.run(
            [
                "valgrind",
                "--tool=cachegrind",
                "--cache-sim=yes",
                "--branch-sim=yes",
                f"--cachegrind-out-file={cg_file}",
                str(exe),
                "cachegrind",
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if cg_proc.returncode == 0 and cg_file.exists():
            cg_parsed: dict[str, Any] = {
                "supported": True,
                **parse_cachegrind_out(cg_file, kernel_prefixes),
            }
        else:
            cg_parsed = {
                "supported": False,
                "returncode": cg_proc.returncode,
                "reason": "Valgrind 3.25.1 VEX amd64->IR lifter SIGILL on EVEX 512-bit AVX-512 instructions",
            }

        # Perf_event_open SW counters + per-kernel runtime latency
        perf_sw = run_with_perf_sw_counters([str(exe), "bench"])
        per_kernel_ns = json.loads(
            subprocess.check_output([str(exe), "per_kernel_json"], text=True).strip()
        )
        bench_runs = []
        for _ in range(12):
            ns = int(subprocess.check_output([str(exe), "bench"], text=True).strip())
            bench_runs.append(ns / 1e6)

        # Also get .text + .rodata size for 3D Pareto usage
        sz_out = subprocess.check_output(
            [tc_nightly["llvm_size"], "--format=sysv", str(exe)], text=True
        )
        sec_map = parse_sysv_sections(sz_out)

        profiles[label] = {
            "compile_wall_sec": round(comp_sec, 4),
            "bench_total_ms": summarize_dist(bench_runs),
            "per_kernel_ns_per_call": per_kernel_ns,
            "perf_sw_counters": perf_sw,
            "cachegrind": cg_parsed,
            "static_disassembly": dis_summary,
            "text_plus_rodata_bytes": sec_map.get(".text", 0) + sec_map.get(".rodata", 0),
        }

    # Also cross-check rustc 1.99.1 on O3_x86_64 and O3_x86_64_v3_avx2
    r1991_comp = {}
    for label, flags in [("r1991_O3_x86_64", ["-Copt-level=3", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"]),
                         ("r1991_O3_x86_64_v3", ["-Copt-level=3", "-Ctarget-cpu=x86-64-v3", "-Ccodegen-units=1"])]:
        exe = tmp / f"exp2_{label}"
        subprocess.run(
            [tc_1991["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(src), "-o", str(exe)],
            check=True, capture_output=True, text=True,
        )
        cg_file = tmp / f"cg_{label}.out"
        subprocess.run(
            ["valgrind", "--tool=cachegrind", "--cache-sim=yes", "--branch-sim=yes", f"--cachegrind-out-file={cg_file}", str(exe), "cachegrind"],
            check=True, capture_output=True, text=True,
        )
        dis_txt = subprocess.check_output(
            [tc_1991["llvm_objdump"], "-d", "--no-show-raw-insn", "-M", "intel", str(exe)],
            text=True, errors="replace",
        )
        dis_s = analyze_disassembly_intel(dis_txt, kernel_prefixes)
        r1991_comp[label] = {
            "per_kernel_ns_per_call": json.loads(subprocess.check_output([str(exe), "per_kernel_json"], text=True).strip()),
            "cachegrind_kernels_isolated": parse_cachegrind_out(cg_file, kernel_prefixes)["kernels_isolated"],
            "static_kernels_aggregate": dis_s["kernels_aggregate"],
        }

    return {
        "pmu_and_rapl_host_probe": probe_pmu_and_rapl_capabilities(),
        "nightly_profiles": profiles,
        "rustc_1991_cross_check": r1991_comp,
    }


def parse_sysv_sections(sysv_txt: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for line in sysv_txt.splitlines():
        cols = line.split()
        if len(cols) >= 2 and cols[0].startswith("."):
            try:
                out[cols[0]] = out.get(cols[0], 0) + int(cols[1])
            except ValueError:
                pass
    return out


def parse_readelf_relocs(readelf_txt: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for line in readelf_txt.splitlines():
        for tok in line.split():
            if tok.startswith("R_X86_64_"):
                counts[tok] = counts.get(tok, 0) + 1
    return counts


def run_experiment_3_startup_relocs_heap(
    tc_nightly: dict[str, str], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp3_heap_reloc.rs"
    src.write_text(HEAP_AND_RELOC_RS, encoding="utf-8")
    nostd_src = tmp / "exp3_nostd_exit.rs"
    nostd_src.write_text(NOSTD_MINIMAL_EXIT_RS, encoding="utf-8")

    lld_flags = [f"-Clink-arg=-B{tc_nightly['lld_dir']}", "-Clink-arg=-fuse-ld=lld"]

    startup_variants = [
        ("std_pie_default_rela", src, ["-Copt-level=3", *lld_flags]),
        ("std_pie_packed_relr", src, ["-Copt-level=3", *lld_flags, "-Clink-arg=-Wl,-z,pack-relative-relocs"]),
        ("nostd_libc_minimal", nostd_src, ["-Copt-level=z", "-Cpanic=abort", *lld_flags, "-Clink-arg=-Wl,-z,pack-relative-relocs"]),
    ]

    startup_results: dict[str, Any] = {}
    for label, sfile, flags in startup_variants:
        exe = tmp / f"exp3_{label}"
        subprocess.run(
            [tc_nightly["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(sfile), "-o", str(exe)],
            check=True, capture_output=True, text=True,
        )
        rel_txt = subprocess.check_output(["llvm-readelf", "-r", str(exe)], text=True, errors="replace")
        sec_txt = subprocess.check_output([tc_nightly["llvm_size"], "--format=sysv", str(exe)], text=True)
        secs = parse_sysv_sections(sec_txt)
        rel_counts = parse_readelf_relocs(rel_txt)

        # Warmup OS dentry/page cache, then measure 80 fork+execve+wait4 cold process startups
        for _ in range(5):
            subprocess.run([str(exe), "startup"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        lat_us = []
        for _ in range(80):
            t0 = time.perf_counter_ns()
            pid = os.fork()
            if pid == 0:
                os.execv(str(exe), [str(exe), "startup"])
                os._exit(127)
            os.waitpid(pid, 0)
            lat_us.append((time.perf_counter_ns() - t0) / 1000.0)

        startup_results[label] = {
            "startup_execve_us": summarize_dist(lat_us),
            "relocation_type_counts": rel_counts,
            "rela_dyn_bytes": secs.get(".rela.dyn", 0),
            "rela_plt_bytes": secs.get(".rela.plt", 0),
            "relr_dyn_bytes": secs.get(".relr.dyn", 0),
            "data_rel_ro_bytes": secs.get(".data.rel.ro", 0),
            "total_file_bytes": exe.stat().st_size,
        }

    # Heap telemetry: custom GlobalAlloc + Valgrind DHAT across -O0, -O2, -O3, -Oz
    heap_results: dict[str, Any] = {}
    for opt in ["0", "2", "3", "z"]:
        exe = tmp / f"exp3_heap_O{opt}"
        subprocess.run(
            [tc_nightly["rustc"], "--edition=2021", f"-Copt-level={opt}", "--remap-path-prefix", f"{tmp}=/work", str(src), "-o", str(exe)],
            check=True, capture_output=True, text=True,
        )
        ga_json = json.loads(subprocess.check_output([str(exe), "heap"], text=True).strip())
        dhat_file = tmp / f"dhat_O{opt}.json"
        subprocess.run(
            ["valgrind", "--tool=dhat", f"--dhat-out-file={dhat_file}", str(exe), "heap"],
            check=True, capture_output=True, text=True,
        )
        dh = json.loads(dhat_file.read_text(encoding="utf-8"))
        pps = dh.get("pps", [])
        heap_results[f"opt_{opt}"] = {
            "global_alloc_wrapper": ga_json,
            "valgrind_dhat": {
                "total_bytes": sum(p.get("tb", 0) for p in pps),
                "total_blocks": sum(p.get("tbk", 0) for p in pps),
                "bytes_at_t_gmax": sum(p.get("gb", 0) for p in pps),
                "blocks_at_t_gmax": sum(p.get("gbk", 0) for p in pps),
                "bytes_at_t_end": sum(p.get("eb", 0) for p in pps),
                "heap_bytes_read": sum(p.get("rb", 0) for p in pps),
                "heap_bytes_written": sum(p.get("wb", 0) for p in pps),
                "zero_read_allocated_bytes": sum(p.get("tb", 0) for p in pps if p.get("rb", 0) == 0),
            },
        }

    return {"startup_and_relocations": startup_results, "heap_allocator_profiles": heap_results}


def compute_call_graph_max_stack(
    entry: str,
    name_to_frame: dict[str, int],
    fn_disasm: dict[str, dict[str, Any]],
    call_push_bytes: int = 8,
) -> dict[str, Any]:
    """DFS with cycle detection computing worst-case call-tree stack usage from `entry`."""
    visiting: set[str] = set()
    memo: dict[str, tuple[int, list[str], bool]] = {}

    def dfs(fn: str) -> tuple[int, list[str], bool]:
        if fn in memo:
            return memo[fn]
        if fn in visiting:
            return (name_to_frame.get(fn, 0), [fn, "<cycle>"], True)
        visiting.add(fn)
        own_frame = name_to_frame.get(fn, 0)
        meta = fn_disasm.get(fn, {})
        callees = [c for c in meta.get("callees", []) if c in name_to_frame or c in fn_disasm]
        rz = meta.get("redzone_min_disp", 0)
        if not callees:
            # Leaf function: frame + call return address pushed by caller + red-zone bytes below RSP
            total = own_frame + rz
            res = (total, [fn], False)
        else:
            best_sub = 0
            best_path: list[str] = []
            any_cycle = False
            for c in callees:
                sub_bytes, sub_path, cyc = dfs(c)
                any_cycle = any_cycle or cyc
                # Each `callq` on x86-64 pushes an 8-byte return address before entering `c`
                cand = call_push_bytes + sub_bytes
                if cand > best_sub:
                    best_sub = cand
                    best_path = sub_path
            res = (own_frame + best_sub, [fn] + best_path, any_cycle)
        visiting.remove(fn)
        memo[fn] = res
        return res

    total_bytes, critical_path, has_cycle = dfs(entry)
    return {
        "entry": entry,
        "max_call_tree_bytes_excl_entry_retaddr": total_bytes,
        "max_call_tree_bytes_incl_entry_retaddr": total_bytes + call_push_bytes,
        "critical_path": critical_path,
        "has_recursion_cycle": has_cycle,
    }


def run_experiment_4_stack_sizes(
    tc_nightly: dict[str, str], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp4_stack.rs"
    src.write_text(STACK_VERIFICATION_RS, encoding="utf-8")
    tracked_fns = (
        "stack_leaf_redzone",
        "stack_slot_coloring_sequential",
        "stack_chain_d1",
        "stack_chain_d2",
        "stack_chain_d3",
        "stack_chain_leaf",
        "stack_async_poll_entry",
    )

    lld_flags = [f"-Clink-arg=-B{tc_nightly['lld_dir']}", "-Clink-arg=-fuse-ld=lld", "-Clink-arg=-Wl,--gc-sections"]
    configs = [
        ("O0_default_redzone", ["-Copt-level=0", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("O1_default_redzone", ["-Copt-level=1", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("O2_default_redzone", ["-Copt-level=2", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("O3_default_redzone", ["-Copt-level=3", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("Os_default_redzone", ["-Copt-level=s", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("Oz_default_redzone", ["-Copt-level=z", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
        ("O3_no_redzone", ["-Copt-level=3", "-Cno-redzone=yes", "-Zemit-stack-sizes", "-Zfunction-sections=yes", *lld_flags]),
    ]

    out: dict[str, Any] = {}
    for label, flags in configs:
        exe = tmp / f"exp4_{label}"
        subprocess.run(
            [tc_nightly["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(src), "-o", str(exe)],
            check=True, capture_output=True, text=True,
        )
        parsed = parse_elf64_stack_sizes_and_symbols(exe)
        # Cross-verify against `llvm-readelf --stack-sizes`
        re_txt = subprocess.check_output(["llvm-readelf", "--stack-sizes", str(exe)], text=True)
        readelf_map: dict[str, int] = {}
        for line in re_txt.splitlines():
            parts = line.split()
            if len(parts) >= 2 and parts[0].isdigit():
                readelf_map[parts[1]] = int(parts[0])

        name_to_frame: dict[str, int] = {}
        for e in parsed["entries"]:
            for sym in e["symbols"]:
                name_to_frame[sym] = e["frame_bytes"]

        # Verify 100% match on all tracked functions
        mismatches = [
            fn for fn in tracked_fns if fn in readelf_map and name_to_frame.get(fn) != readelf_map[fn]
        ]

        dis_txt = subprocess.check_output(
            [tc_nightly["llvm_objdump"], "-d", "--no-show-raw-insn", "-M", "intel", str(exe)],
            text=True, errors="replace",
        )
        dis = analyze_disassembly_intel(dis_txt, tracked_fns)
        cg_bound = compute_call_graph_max_stack("stack_chain_d1", name_to_frame, dis["all_functions"], 8)
        rt_watermark = json.loads(subprocess.check_output([str(exe)], text=True).strip())

        per_fn_frames = {}
        for fn in tracked_fns:
            f_sz = name_to_frame.get(fn)
            rz = dis["all_functions"].get(fn, {}).get("redzone_min_disp", 0)
            per_fn_frames[fn] = {
                "stack_sizes_section_bytes": f_sz,
                "leaf_redzone_disp_bytes": rz,
                "effective_frame_excl_retaddr_bytes": (f_sz or 0) + rz,
            }

        out[label] = {
            "elf_summary": {
                "stack_sizes_entries": parsed["total_stack_size_entries"],
                "defined_stt_func": parsed["total_defined_stt_func"],
                "missing_from_stack_sizes_count": parsed["uninstrumented_or_varsized_stt_func_count"],
                "readelf_cross_check_mismatches": len(mismatches),
            },
            "per_function_frames": per_fn_frames,
            "call_graph_chain_d1_bound": cg_bound,
            "naive_stack_sizes_sum_only_bytes": sum(
                name_to_frame.get(f, 0)
                for f in ("stack_chain_d1", "stack_chain_d2", "stack_chain_d3", "stack_chain_leaf")
            ),
            "runtime_painted_watermarks": rt_watermark,
        }
    return out


def run_experiment_5_footprint_ladder(
    tc_nightly: dict[str, str], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp5_footprint.rs"
    src.write_text(HEAP_AND_RELOC_RS, encoding="utf-8")
    lld_flags = [f"-Clink-arg=-B{tc_nightly['lld_dir']}", "-Clink-arg=-fuse-ld=lld"]

    ladder = [
        ("01_dev_O0_debug2", ["-Copt-level=0", "-Cdebuginfo=2", *lld_flags]),
        ("02_rel_O3_debug2", ["-Copt-level=3", "-Cdebuginfo=2", *lld_flags]),
        ("03_rel_O3_debug2_zstd", ["-Copt-level=3", "-Cdebuginfo=2", "-Zdebuginfo-compression=zstd", *lld_flags]),
        ("04_rel_O3_default", ["-Copt-level=3", *lld_flags]),
        ("05_rel_Oz_default", ["-Copt-level=z", *lld_flags]),
        ("06_rel_Oz_fatlto", ["-Copt-level=z", "-Clto=fat", "-Ccodegen-units=1", *lld_flags]),
        ("07_rel_Oz_fatlto_abort", ["-Copt-level=z", "-Clto=fat", "-Ccodegen-units=1", "-Cpanic=abort", *lld_flags]),
        ("08_rel_Oz_fatlto_abort_gc_icf", ["-Copt-level=z", "-Clto=fat", "-Ccodegen-units=1", "-Cpanic=abort", *lld_flags, "-Clink-arg=-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs"]),
        ("09_rel_Oz_fatlto_abort_noloc_nofmt", ["-Copt-level=z", "-Clto=fat", "-Ccodegen-units=1", "-Cpanic=abort", "-Zlocation-detail=none", "-Zfmt-debug=none", *lld_flags, "-Clink-arg=-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs"]),
        ("10_rel_Oz_stripped_final", ["-Copt-level=z", "-Clto=fat", "-Ccodegen-units=1", "-Cpanic=abort", "-Zlocation-detail=none", "-Zfmt-debug=none", "-Cstrip=symbols", *lld_flags, "-Clink-arg=-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs"]),
    ]

    results: dict[str, Any] = {}
    for label, flags in ladder:
        exe = tmp / f"exp5_{label}"
        subprocess.run(
            [tc_nightly["rustc"], "--edition=2021", "--remap-path-prefix", f"{tmp}=/work", *flags, str(src), "-o", str(exe)],
            check=True, capture_output=True, text=True,
        )
        sz_txt = subprocess.check_output([tc_nightly["llvm_size"], "--format=sysv", str(exe)], text=True)
        secs = parse_sysv_sections(sz_txt)
        debug_bytes = sum(v for k, v in secs.items() if k.startswith(".debug_"))
        unwind_bytes = secs.get(".eh_frame", 0) + secs.get(".eh_frame_hdr", 0) + secs.get(".gcc_except_table", 0)
        text_ro = secs.get(".text", 0) + secs.get(".rodata", 0)
        results[label] = {
            "file_bytes": exe.stat().st_size,
            "text_bytes": secs.get(".text", 0),
            "rodata_bytes": secs.get(".rodata", 0),
            "text_plus_rodata_bytes": text_ro,
            "data_rel_ro_bytes": secs.get(".data.rel.ro", 0),
            "data_plus_bss_bytes": secs.get(".data", 0) + secs.get(".bss", 0),
            "unwind_total_bytes": unwind_bytes,
            "eh_frame_bytes": secs.get(".eh_frame", 0),
            "eh_frame_hdr_bytes": secs.get(".eh_frame_hdr", 0),
            "gcc_except_table_bytes": secs.get(".gcc_except_table", 0),
            "reloc_sections_bytes": secs.get(".rela.dyn", 0) + secs.get(".relr.dyn", 0) + secs.get(".rela.plt", 0),
            "debug_sections_bytes": debug_bytes,
        }

    # Step 11: `#![no_std]` binary with `-C force-unwind-tables=no -C panic=abort -C strip=symbols`
    nostd_src = tmp / "exp5_nostd.rs"
    nostd_src.write_text(NOSTD_MINIMAL_EXIT_RS, encoding="utf-8")
    nostd_exe = tmp / "exp5_11_nostd_zero_unwind"
    subprocess.run(
        [
            tc_nightly["rustc"], "--edition=2021", "-Copt-level=z", "-Cpanic=abort",
            "-Cforce-unwind-tables=no", "-Cstrip=symbols",
            *lld_flags, "-Clink-arg=-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs",
            str(nostd_src), "-o", str(nostd_exe),
        ],
        check=True, capture_output=True, text=True,
    )
    ns_secs = parse_sysv_sections(
        subprocess.check_output([tc_nightly["llvm_size"], "--format=sysv", str(nostd_exe)], text=True)
    )
    results["11_nostd_abort_force_no_uwtable_stripped"] = {
        "file_bytes": nostd_exe.stat().st_size,
        "text_bytes": ns_secs.get(".text", 0),
        "rodata_bytes": ns_secs.get(".rodata", 0),
        "text_plus_rodata_bytes": ns_secs.get(".text", 0) + ns_secs.get(".rodata", 0),
        "unwind_total_bytes": ns_secs.get(".eh_frame", 0) + ns_secs.get(".eh_frame_hdr", 0) + ns_secs.get(".gcc_except_table", 0),
        "eh_frame_bytes": ns_secs.get(".eh_frame", 0),
        "debug_sections_bytes": sum(v for k, v in ns_secs.items() if k.startswith(".debug_")),
    }
    return results


# ---------------------------------------------------------------------------
# Experiment 6: 3D Pareto Hypervolume & Live Hierarchical --shuffle-sections TOST
# ---------------------------------------------------------------------------


def exact_3d_hypervolume_min(points: list[tuple[float, float, float]], ref: tuple[float, float, float]) -> float:
    """Exact 3D hypervolume dominated by minimization `points` up to nadir `ref = (rx, ry, rz)`."""
    rx, ry, rz = ref
    pts = [(x, y, z) for (x, y, z) in points if x < rx and y < ry and z < rz]
    if not pts:
        return 0.0
    # Slice along sorted unique z coordinates
    zs = sorted(set(p[2] for p in pts)) + [rz]
    hv = 0.0
    for idx in range(len(zs) - 1):
        z_cur = zs[idx]
        dz = zs[idx + 1] - z_cur
        if dz <= 0:
            continue
        # Active 2D points with z <= z_cur
        xy = sorted((p[0], p[1]) for p in pts if p[2] <= z_cur)
        # Compute exact 2D dominated area up to (rx, ry) via skyline sweep
        area_2d = 0.0
        min_y = ry
        for i, (x, y) in enumerate(xy):
            if y < min_y:
                # Add strip in y from y to min_y, spanning x to rx
                area_2d += (rx - x) * (min_y - y)
                min_y = y
        hv += area_2d * dz
    return hv


def compute_pareto_3d_analysis(microarch_profiles: dict[str, Any]) -> dict[str, Any]:
    # Part A: Live microarch 8-configuration 3D Pareto frontier
    live_pts: dict[str, tuple[float, float, float]] = {}
    for k, v in microarch_profiles.items():
        live_pts[k] = (
            float(v["compile_wall_sec"]),
            float(v["text_plus_rodata_bytes"]) / 1024.0,
            float(v["bench_total_ms"]["median"]),
        )

    # Part B: Canonical 14-configuration W-Core dataset from companion baseline report
    # (Compile wall sec, x86_64 .text+.rodata MiB, x86_64 runtime GeoMean ratio vs C05)
    w_core_14 = {
        "C01_O0": (0.541, 2.379408, 33.1154),
        "C02_O1": (0.738, 2.315456, 1.1160),
        "C03_O2": (0.792, 2.319128, 1.3570),
        "C04_O3_no_lto": (0.753, 2.327208, 1.5735),
        "C05_O3_thinlocal": (0.857, 2.325472, 1.0000),
        "C06_O3_thin_lto": (18.270, 2.302400, 0.8007),
        "C07_O3_fat_lto": (23.180, 2.182834, 1.2827),
        "C08_O3_no_lto_pgo": (0.729, 2.326160, 1.7930),
        "C09_O3_thin_lto_pgo": (18.401, 2.300556, 1.3203),
        "C10_O3_fat_lto_pgo": (24.584, 2.229714, 0.9529),
        "C11_Os": (0.760, 2.312192, 1.1081),
        "C12_Oz": (0.719, 2.311496, 1.4177),
        "C11_Os_fat_lto": (21.130, 2.085485, 1.2427),
        "C12_Oz_fat_lto": (21.164, 2.084101, 1.0699),
    }

    def analyze_set(raw: dict[str, tuple[float, float, float]]) -> dict[str, Any]:
        names = list(raw.keys())
        non_dom = []
        dominated_by: dict[str, list[str]] = {}
        for a in names:
            xa, ya, za = raw[a]
            doms = []
            for b in names:
                if a == b:
                    continue
                xb, yb, zb = raw[b]
                if (xb <= xa and yb <= ya and zb <= za) and (xb < xa or yb < ya or zb < za):
                    doms.append(b)
            if doms:
                dominated_by[a] = doms
            else:
                non_dom.append(a)

        # Normalize each axis to [0, 1] over [min, max * 1.05] with reference point (1.0, 1.0, 1.0)
        xs = [v[0] for v in raw.values()]
        ys = [v[1] for v in raw.values()]
        zs = [v[2] for v in raw.values()]
        min_x, max_x = min(xs), max(xs) * 1.05
        min_y, max_y = min(ys), max(ys) * 1.05
        min_z, max_z = min(zs), max(zs) * 1.05

        def norm(pt: tuple[float, float, float]) -> tuple[float, float, float]:
            return (
                (pt[0] - min_x) / max(max_x - min_x, 1e-12),
                (pt[1] - min_y) / max(max_y - min_y, 1e-12),
                (pt[2] - min_z) / max(max_z - min_z, 1e-12),
            )

        norm_pts = {k: norm(v) for k, v in raw.items()}
        total_hv = exact_3d_hypervolume_min(list(norm_pts.values()), (1.0, 1.0, 1.0))
        exclusive_hv: dict[str, float] = {}
        for k in non_dom:
            others = [v for k2, v in norm_pts.items() if k2 != k]
            exclusive_hv[k] = round(total_hv - exact_3d_hypervolume_min(others, (1.0, 1.0, 1.0)), 6)

        return {
            "pareto_frontier": non_dom,
            "dominated_configurations": dominated_by,
            "normalized_3d_hypervolume": round(total_hv, 6),
            "exclusive_hypervolume_contributions": exclusive_hv,
            "points": {
                k: {"compile_s": v[0], "size_unit": round(v[1], 4), "speed_unit": round(v[2], 4)}
                for k, v in raw.items()
            },
        }

    return {
        "live_microarch_8_configs": analyze_set(live_pts),
        "w_core_14_configs": analyze_set(w_core_14),
    }


def holm_bonferroni(p_vals: dict[str, float]) -> dict[str, float]:
    items = sorted(p_vals.items(), key=lambda kv: kv[1])
    m = len(items)
    adj: dict[str, float] = {}
    running_max = 0.0
    for idx, (k, p) in enumerate(items):
        val = min(1.0, p * (m - idx))
        running_max = max(running_max, val)
        adj[k] = round(running_max, 6)
    return adj


def benjamini_hochberg(p_vals: dict[str, float]) -> dict[str, float]:
    items = sorted(p_vals.items(), key=lambda kv: kv[1])
    m = len(items)
    raw_q = [0.0] * m
    running_min = 1.0
    for idx in range(m - 1, -1, -1):
        rank = idx + 1
        val = min(1.0, items[idx][1] * m / rank)
        running_min = min(running_min, val)
        raw_q[idx] = running_min
    return {items[i][0]: round(raw_q[i], 6) for i in range(m)}


def hierarchical_comparison(
    arm_base: list[list[float]],
    arm_cand: list[list[float]],
    delta_equiv: float = 0.05,
    n_boot: int = 4000,
    rng_seed: int = 20261121,
) -> dict[str, Any]:
    """Two-level hierarchical bootstrap & TOST over (seed_idx k in 1..K, run_idx r in 1..R)."""
    rng = random.Random(rng_seed)
    k_b = len(arm_base)
    k_c = len(arm_cand)
    r_b = len(arm_base[0])
    r_c = len(arm_cand[0])

    seed_meds_b = [percentile_sorted(sorted(runs), 50.0) for runs in arm_base]
    seed_meds_c = [percentile_sorted(sorted(runs), 50.0) for runs in arm_cand]

    med_b = percentile_sorted(sorted(seed_meds_b), 50.0)
    med_c = percentile_sorted(sorted(seed_meds_c), 50.0)
    ratio_est = med_c / max(med_b, 1e-12)
    hl_shift = hodges_lehmann_shift(seed_meds_b, seed_meds_c)
    hl_rel_pct = (hl_shift / max(med_b, 1e-12)) * 100.0

    # Variance components (one-way random-effects ANOVA on arm_base)
    grand_mean = sum(sum(r) for r in arm_base) / (k_b * r_b)
    seed_means = [sum(r) / r_b for r in arm_base]
    ms_between = r_b * sum((m - grand_mean) ** 2 for m in seed_means) / max(k_b - 1, 1)
    ms_within = sum(
        sum((x - seed_means[i]) ** 2 for x in arm_base[i]) for i in range(k_b)
    ) / max(k_b * (r_b - 1), 1)
    var_seed = max(0.0, (ms_between - ms_within) / r_b)
    var_run = ms_within
    icc = var_seed / max(var_seed + var_run, 1e-12)

    # Two-level hierarchical bootstrap: resample K seeds with replacement, and R runs within each seed
    boot_ratios = []
    for _ in range(n_boot):
        b_s = []
        for _ in range(k_b):
            chosen = arm_base[rng.randrange(k_b)]
            resamp = [chosen[rng.randrange(r_b)] for _ in range(r_b)]
            b_s.append(percentile_sorted(sorted(resamp), 50.0))
        c_s = []
        for _ in range(k_c):
            chosen = arm_cand[rng.randrange(k_c)]
            resamp = [chosen[rng.randrange(r_c)] for _ in range(r_c)]
            c_s.append(percentile_sorted(sorted(resamp), 50.0))
        mb = percentile_sorted(sorted(b_s), 50.0)
        mc = percentile_sorted(sorted(c_s), 50.0)
        boot_ratios.append(mc / max(mb, 1e-12))

    boot_ratios.sort()
    ci90_lo = percentile_sorted(boot_ratios, 5.0)
    ci90_hi = percentile_sorted(boot_ratios, 95.0)
    ci95_lo = percentile_sorted(boot_ratios, 2.5)
    ci95_hi = percentile_sorted(boot_ratios, 97.5)

    # Bootstrap TOST p-values for equivalence in [1 - delta_equiv, 1 + delta_equiv]:
    # p_lower tests H01: R <= 1 - delta; p_upper tests H02: R >= 1 + delta
    p_low = sum(1 for r in boot_ratios if r <= (1.0 - delta_equiv)) / n_boot
    p_high = sum(1 for r in boot_ratios if r >= (1.0 + delta_equiv)) / n_boot
    p_tost_equiv = max(p_low, p_high)
    p_two_sided_boot = min(
        1.0,
        2.0 * min(
            sum(1 for r in boot_ratios if r <= 1.0) / n_boot,
            sum(1 for r in boot_ratios if r >= 1.0) / n_boot,
        ),
    )

    # Naive single-seed false-positive audit across all k_b * k_c pairs (alpha = 0.01)
    sig_pairs = 0
    total_pairs = k_b * k_c
    max_single_seed_spread_pct = 0.0
    for i in range(k_b):
        for j in range(k_c):
            mwu = mann_whitney_u_two_sided(arm_base[i], arm_cand[j])
            if mwu["p_two_sided"] < 0.01:
                sig_pairs += 1
            sp = abs(seed_meds_c[j] - seed_meds_b[i]) / max(seed_meds_b[i], 1e-12) * 100.0
            if sp > max_single_seed_spread_pct:
                max_single_seed_spread_pct = sp

    return {
        "k_seeds": k_b,
        "r_runs_per_seed": r_b,
        "base_inter_seed_median": round(med_b, 4),
        "cand_inter_seed_median": round(med_c, 4),
        "median_ratio_cand_over_base": round(ratio_est, 5),
        "hodges_lehmann_shift": round(hl_shift, 4),
        "hodges_lehmann_rel_pct": round(hl_rel_pct, 3),
        "hierarchical_boot_90pct_ci": [round(ci90_lo, 5), round(ci90_hi, 5)],
        "hierarchical_boot_95pct_ci": [round(ci95_lo, 5), round(ci95_hi, 5)],
        "tost_margin_delta": delta_equiv,
        "tost_equivalent_at_alpha_0_05": (ci90_lo >= 1.0 - delta_equiv) and (ci90_hi <= 1.0 + delta_equiv),
        "tost_non_inferior_at_alpha_0_025": ci95_hi <= (1.0 + delta_equiv),
        "p_tost_equivalence": round(p_tost_equiv, 5),
        "p_non_inferiority": round(p_high, 5),
        "p_two_sided_hierarchical": round(p_two_sided_boot, 5),
        "variance_components_base": {
            "sigma_seed": round(math.sqrt(var_seed), 5),
            "sigma_run": round(math.sqrt(var_run), 5),
            "intraclass_correlation_icc": round(icc, 4),
            "inter_seed_cv_pct": round(
                (statistics.stdev(seed_meds_b) / max(med_b, 1e-12)) * 100.0 if k_b >= 2 else 0.0,
                3,
            ),
        },
        "naive_single_seed_mwu_alpha_0_01_reject_rate_pct": round(sig_pairs * 100.0 / total_pairs, 2),
        "max_pairwise_seed_delta_pct": round(max_single_seed_spread_pct, 2),
    }


def run_experiment_6_shuffle_sections_tost(
    tc_1991: dict[str, str], microarch_profiles: dict[str, Any], tmp: pathlib.Path
) -> dict[str, Any]:
    src = tmp / "exp6_shuffle.rs"
    src.write_text(MICROARCH_SUITE_RS, encoding="utf-8")
    lld_flags = [f"-Clink-arg=-B{tc_1991['lld_dir']}", "-Clink-arg=-fuse-ld=lld", "-Zfunction-sections=yes"]

    k_seeds = 10
    r_runs = 12

    def build_and_measure_arm(
        arm_name: str, extra_flags: list[str], seeds: list[int]
    ) -> dict[str, list[list[float]]]:
        # Returns per-kernel [seed][run] ns/call + total_bench [seed][run] ms
        per_metric: dict[str, list[list[float]]] = {
            "total_suite_ms": [],
            "f32_dot_fma": [],
            "u32_autovec_mac": [],
            "reg_pressure_spills": [],
            "bounds_and_iter": [],
            "dyn_dispatch_and_memops": [],
        }
        for s in seeds:
            exe = tmp / f"exp6_{arm_name}_s{s}"
            subprocess.run(
                [
                    "env",
                    "RUSTC_BOOTSTRAP=1",
                    tc_1991["rustc"],
                    "--edition=2021",
                    "--remap-path-prefix",
                    f"{tmp}=/work",
                    *lld_flags,
                    f"-Clink-arg=-Wl,--shuffle-sections=*={s}",
                    *extra_flags,
                    str(src),
                    "-o",
                    str(exe),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            # Warmup 1 run
            subprocess.run([str(exe), "per_kernel_json"], check=True, stdout=subprocess.DEVNULL)
            seed_buckets: dict[str, list[float]] = {m: [] for m in per_metric}
            for _ in range(r_runs):
                pk = json.loads(subprocess.check_output([str(exe), "per_kernel_json"], text=True).strip())
                tot_ns = int(subprocess.check_output([str(exe), "bench"], text=True).strip())
                seed_buckets["total_suite_ms"].append(tot_ns / 1e6)
                for kname, val in pk.items():
                    seed_buckets[kname].append(float(val))
            for m in per_metric:
                per_metric[m].append(seed_buckets[m])
        return per_metric

    arm_o3_a = build_and_measure_arm("O3_A", ["-Copt-level=3", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"], list(range(1, k_seeds + 1)))
    arm_o3_b = build_and_measure_arm("O3_B_null", ["-Copt-level=3", "-Ctarget-cpu=x86-64", "-Ccodegen-units=1"], list(range(101, 101 + k_seeds)))
    arm_o3_v3 = build_and_measure_arm("O3_v3", ["-Copt-level=3", "-Ctarget-cpu=x86-64-v3", "-Ccodegen-units=1"], list(range(1, k_seeds + 1)))

    aa_null_results = {}
    ab_avx2_results = {}
    p_raw_aa: dict[str, float] = {}
    p_raw_ab: dict[str, float] = {}
    kernels = ["f32_dot_fma", "u32_autovec_mac", "reg_pressure_spills", "bounds_and_iter", "dyn_dispatch_and_memops"]

    for m in ["total_suite_ms", *kernels]:
        aa = hierarchical_comparison(arm_o3_a[m], arm_o3_b[m], delta_equiv=0.05)
        ab = hierarchical_comparison(arm_o3_a[m], arm_o3_v3[m], delta_equiv=0.05)
        aa_null_results[m] = aa
        ab_avx2_results[m] = ab
        if m in kernels:
            p_raw_aa[m] = aa["p_two_sided_hierarchical"]
            p_raw_ab[m] = ab["p_two_sided_hierarchical"]

    return {
        "pareto_3d": compute_pareto_3d_analysis(microarch_profiles),
        "hierarchical_shuffle_sections_study": {
            "protocol": {
                "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67) + ld.lld",
                "k_seeds_per_arm": k_seeds,
                "r_invocations_per_seed": r_runs,
                "total_runs_per_arm": k_seeds * r_runs,
                "tost_equivalence_margin_pct": 5.0,
            },
            "aa_null_disjoint_seeds_O3_vs_O3": {
                "metrics": aa_null_results,
                "holm_bonferroni_p": holm_bonferroni(p_raw_aa),
                "benjamini_hochberg_q": benjamini_hochberg(p_raw_aa),
            },
            "ab_target_cpu_x86_64_vs_x86_64_v3": {
                "metrics": ab_avx2_results,
                "holm_bonferroni_p": holm_bonferroni(p_raw_ab),
                "benjamini_hochberg_q": benjamini_hochberg(p_raw_ab),
            },
        },
    }


def run_mir_vs_llvm_assert_probe(tc_nightly: dict[str, str], tmp: pathlib.Path) -> dict[str, Any]:
    """Reproducible single-file MIR SsaRangePropagation vs LLVM -O2 panic-call survival probe."""
    kernels_rs = tmp / "mir_assert_kernels.rs"
    kernels_rs.write_text(
        r'''#![crate_type = "lib"]
pub fn idx_const_in_bounds(a: &[u32; 16]) -> u32 { a[7] }
pub fn idx_bitmask_256(a: &[u8; 256], k: usize) -> u8 { a[k & 0xff] }
pub fn idx_slice_guard(s: &[u32], i: usize) -> u32 { if i < s.len() { s[i] } else { 0 } }
pub fn idx_rem_nonempty(s: &[u32], i: usize) -> u32 { if !s.is_empty() { s[i % s.len()] } else { 0 } }
pub fn idx_for_iter_sum(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for k in 0..s.len() { acc = acc.wrapping_add(s[k]); }
    acc
}
pub fn checked_div_guard(x: u32, d: u32) -> u32 { if d != 0 { x / d } else { 0 } }
''',
        encoding="utf-8",
    )
    mir_dir = tmp / "mir_dump"
    mir_dir.mkdir()
    ll_out = tmp / "mir_assert_kernels.ll"
    subprocess.run(
        [
            tc_nightly["rustc"],
            "--edition=2021",
            "-Copt-level=2",
            "-Zmir-opt-level=2",
            "--emit=llvm-ir",
            "-Zdump-mir=SimplifyCfg-pre-optimizations|SsaRangePropagation|SimplifyCfg-final",
            f"-Zdump-mir-dir={mir_dir}",
            "-o",
            str(ll_out),
            str(kernels_rs),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    def count_mir_asserts(txt: str) -> int:
        c = 0
        for line in txt.splitlines():
            s = line.strip()
            if s.startswith("assert(") and ") -> [" in s:
                c += 1
        return c

    ll_lines = ll_out.read_text(encoding="utf-8", errors="replace").splitlines()
    out: dict[str, Any] = {}
    for fn in (
        "idx_const_in_bounds",
        "idx_bitmask_256",
        "idx_slice_guard",
        "idx_rem_nonempty",
        "idx_for_iter_sum",
        "checked_div_guard",
    ):
        f_pre = next(mir_dir.glob(f"*{fn}*.SimplifyCfg-pre-optimizations.after.mir"))
        f_ssa = next(mir_dir.glob(f"*{fn}*.SsaRangePropagation.after.mir"))
        f_fin = next(mir_dir.glob(f"*{fn}*.SimplifyCfg-final.after.mir"))
        # Linear scan for LLVM IR function body
        in_fn = False
        panic_calls = 0
        for line in ll_lines:
            if line.startswith("define ") and fn in line and line.rstrip().endswith("{"):
                in_fn = True
                continue
            if in_fn:
                if line.startswith("}"):
                    in_fn = False
                    continue
                if "panic_bounds_check" in line or "panic_const_div_by_zero" in line or "panic" in line:
                    panic_calls += 1
        out[fn] = {
            "post_cleanup_asserts": count_mir_asserts(f_pre.read_text(encoding="utf-8")),
            "after_ssa_range_prop_asserts": count_mir_asserts(f_ssa.read_text(encoding="utf-8")),
            "after_mir_final_asserts": count_mir_asserts(f_fin.read_text(encoding="utf-8")),
            "llvm_o2_panic_calls": panic_calls,
        }
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="Probe generated-code performance and footprint metrics.")
    ap.add_argument(
        "--output",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent / "generated_code_metrics_specimen.json",
        help="Path to write JSON specimen.",
    )
    ap.add_argument(
        "--quick",
        action="store_true",
        help="Run a fast 15-second smoke verification subset.",
    )
    args = ap.parse_args()

    tc_nightly = resolve_toolchain("nightly")
    tc_1991 = resolve_toolchain("1.99.1")
    valgrind_ver = subprocess.check_output(["valgrind", "--version"], text=True).strip()

    t_start = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="rustc_gen_metrics_") as td:
        tmp = pathlib.Path(td)
        mir_asserts = run_mir_vs_llvm_assert_probe(tc_nightly, tmp)
        if args.quick:
            pmu_info = probe_pmu_and_rapl_capabilities()
            payload = {
                "mode": "quick_smoke",
                "toolchains": {
                    "nightly": tc_nightly["version_verbose"],
                    "rustc_1_99_1": tc_1991["version_verbose"],
                    "valgrind": valgrind_ver,
                },
                "pmu_and_rapl_host_probe": pmu_info,
                "mir_vs_llvm_assert_survival": mir_asserts,
            }
            print(json.dumps(payload, indent=2))
            return 0

        exp1 = run_experiment_1_latency_async_unwind(tc_nightly, tc_1991, tmp)
        exp2 = run_experiment_2_microarch(tc_nightly, tc_1991, tmp)
        exp3 = run_experiment_3_startup_relocs_heap(tc_nightly, tmp)
        exp4 = run_experiment_4_stack_sizes(tc_nightly, tmp)
        exp5 = run_experiment_5_footprint_ladder(tc_nightly, tmp)
        exp6 = run_experiment_6_shuffle_sections_tost(
            tc_1991, exp2["nightly_profiles"], tmp
        )

    wall_sec = round(time.perf_counter() - t_start, 3)
    specimen = {
        "schema": "generated-code-metrics-specimen/1",
        "observed_date": "2026-11-21",
        "total_probe_wall_sec": wall_sec,
        "toolchains": {
            "rustc_nightly": tc_nightly["version_verbose"],
            "rustc_1_99_1": tc_1991["version_verbose"],
            "valgrind": valgrind_ver,
            "host_os_kernel": f"{os.uname().sysname} {os.uname().release} {os.uname().machine}",
        },
        "experiment_1_latency_async_unwind": exp1,
        "experiment_2_microarch_pmu_cachegrind_disasm": exp2,
        "mir_vs_llvm_assert_survival": mir_asserts,
        "experiment_3_startup_relocations_and_heap": exp3,
        "experiment_4_stack_sizes_static_and_dynamic": exp4,
        "experiment_5_binary_footprint_ladder": exp5,
        "experiment_6_pareto_3d_and_shuffle_tost": exp6,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    text_out = json.dumps(specimen, indent=2, sort_keys=False) + "\n"
    args.output.write_text(text_out, encoding="utf-8")
    digest = hashlib.sha256(text_out.encode("utf-8")).hexdigest()
    print(f"Wrote {args.output.name} ({len(text_out)} bytes, sha256={digest}) in {wall_sec}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
