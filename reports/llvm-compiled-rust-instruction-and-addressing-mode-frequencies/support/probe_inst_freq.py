#!/usr/bin/env python3
"""M10 Probe: Measure instruction mnemonic and operand/addressing-mode frequencies in LLVM-compiled Rust 1.99.1 sysroot (all 8 Tier 1 targets) and multi-domain benchmark workloads across opt-levels (0,1,2,3,s,z) and CPU microarchitecture levels (x86-64-v1..v4, apple-m1..m4, neoverse-n1/v1/v2)."""

import json
import os
import re
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = TC_ROOT / "bin" / "rustc"
LLVM_OBJDUMP = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "llvm-objdump"
WORK_DIR = Path("/tmp/probe_out")
DATA_DIR = Path("/tmp/probe_out")
WORK_DIR.mkdir(parents=True, exist_ok=True)
DATA_DIR.mkdir(parents=True, exist_ok=True)

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-pc-windows-msvc",
    "i686-pc-windows-msvc",
]

INST_LINE_RE = re.compile(r"^\s*[0-9a-fA-F]+:\s+([a-zA-Z0-9_.]+)(?:\s+(.*))?$")


def classify_operand_form(arch: str, mnemonic: str, ops: str) -> str:
    if not ops:
        return "no_operands"
    ops = ops.split("#")[0].split("//")[0].split(";")[0].strip()
    if not ops:
        return "no_operands"
    if arch in {"x86_64", "i686"}:
        if "(%rip)" in ops or "(%eip)" in ops:
            return "rip_relative_mem"
        if re.search(r"\([^)]*,[^)]*\)", ops):
            return "sib_indexed_mem"
        if "(" in ops and ")" in ops:
            return "base_disp_mem"
        if "$" in ops:
            return "reg_imm"
        if any(r in ops for r in ["%xmm", "%ymm", "%zmm"]):
            return "simd_reg_to_reg"
        if mnemonic.startswith("j") or mnemonic.startswith("call"):
            return "branch_or_call_target"
        return "gpr_reg_to_reg"
    else:
        # AArch64
        if "]!" in ops or re.search(r"\],\s*#", ops):
            return "pre_or_post_indexed_mem"
        if "[" in ops and "]" in ops:
            if re.search(r",\s*[wx]\d+", ops) or "lsl" in ops or "sxtw" in ops or "uxtw" in ops:
                return "reg_offset_scaled_mem"
            return "base_imm_offset_mem"
        if re.search(r"\bv\d+\.(?:16b|8b|8h|4h|4s|2s|2d|1d|b|h|s|d|q)\b", ops) or re.search(r"\bz\d+\.", ops):
            return "neon_or_sve_vector_arrangement"
        if "#" in ops:
            return "reg_imm"
        if mnemonic.startswith("b") or mnemonic in {"cbz", "cbnz", "tbz", "tbnz", "adr", "adrp"}:
            return "pc_rel_branch_or_adrp"
        return "scalar_reg_to_reg"


def parse_objdump_output(text: str, arch: str):
    mnemonics = Counter()
    operand_forms = Counter()
    total = 0
    for line in text.splitlines():
        m = INST_LINE_RE.match(line)
        if not m:
            continue
        mnem = m.group(1).lower()
        ops = (m.group(2) or "").strip()
        # Handle x86 prefixes like lock / rep / data16
        if mnem in {"lock", "rep", "repe", "repz", "repne", "repnz", "data16", "cs", "ds", "es", "fs", "gs", "ss"} and ops:
            parts = ops.split(None, 1)
            mnem = f"{mnem}_{parts[0].lower()}"
            ops = parts[1] if len(parts) > 1 else ""
        mnemonics[mnem] += 1
        operand_forms[classify_operand_form(arch, mnem, ops)] += 1
        total += 1
    return total, mnemonics, operand_forms


def summarize_counter(total: int, mnemonics: Counter, operand_forms: Counter, top_n: int = 40):
    if total == 0:
        return {}
    sorted_m = mnemonics.most_common()
    cum = 0
    thresholds = {}
    top_cov = {}
    for idx, (_m, c) in enumerate(sorted_m, 1):
        cum += c
        frac = cum / total
        if idx in {10, 25, 50, 100}:
            top_cov[f"top_{idx}_pct"] = round(frac * 100.0, 2)
        for pct_label, target_frac in [("p90", 0.90), ("p95", 0.95), ("p99", 0.99), ("p99_9", 0.999)]:
            if pct_label not in thresholds and frac >= target_frac:
                thresholds[pct_label] = idx
    for idx in [10, 25, 50, 100]:
        if f"top_{idx}_pct" not in top_cov:
            top_cov[f"top_{idx}_pct"] = 100.0

    return {
        "total_instructions": total,
        "unique_mnemonics": len(mnemonics),
        "mnemonics_for_coverage": thresholds,
        "cumulative_coverage_pct": top_cov,
        "operand_form_distribution": dict(operand_forms.most_common()),
        "operand_form_pct": {k: round(v * 100.0 / total, 2) for k, v in operand_forms.most_common()},
        "top_mnemonics": dict(sorted_m[:top_n]),
    }


def disassemble_file(path: Path, arch: str):
    proc = subprocess.run(
        [str(LLVM_OBJDUMP), "-d", "--no-show-raw-insn", str(path)],
        capture_output=True, text=True, check=True,
    )
    return parse_objdump_output(proc.stdout, arch)


def analyze_sysroot_target(target: str):
    arch = "x86_64" if target.startswith("x86_64") else ("i686" if target.startswith("i686") else "aarch64")
    lib_dir = TC_ROOT / "lib" / "rustlib" / target / "lib"
    crates = {}
    agg_mnem = Counter()
    agg_ops = Counter()
    agg_total = 0

    for prefix in ["libcore-", "liballoc-", "libstd-", "libcompiler_builtins-"]:
        matches = list(lib_dir.glob(f"{prefix}*.rlib"))
        if not matches:
            continue
        rlib = matches[0]
        tot, mnem, ops = disassemble_file(rlib, arch)
        cname = prefix.rstrip("-")[3:]
        crates[cname] = summarize_counter(tot, mnem, ops, top_n=25)
        agg_total += tot
        agg_mnem.update(mnem)
        agg_ops.update(ops)

    return target, {
        "arch": arch,
        "aggregate_sysroot": summarize_counter(agg_total, agg_mnem, agg_ops, top_n=40),
        "per_crate": crates,
    }


BENCH_WORKLOAD_RS = """#![no_std]
#![crate_type = "rlib"]

use core::sync::atomic::{AtomicUsize, Ordering};

// 1. Hash table quadratic/SwissTable-style probing & FNV/FX hashing
#[unsafe(no_mangle)]
pub fn workload_hash_probe(keys: &[u64], values: &[u64], query: u64) -> u64 {
    let n = keys.len().min(values.len());
    if n == 0 { return 0; }
    let mut h = query.wrapping_mul(0x517cc1b727220a95);
    h ^= h >> 32;
    let mut idx = (h as usize) % n;
    for step in 0..n {
        let k = keys[idx];
        if k == query {
            return values[idx];
        }
        if k == u64::MAX {
            break;
        }
        idx = (idx + step + 1) % n;
    }
    0
}

// 2. UTF-8 validation & byte-class state machine (regex/lexer style)
#[unsafe(no_mangle)]
pub fn workload_utf8_and_lexer(bytes: &[u8]) -> (usize, usize, u32) {
    let mut i = 0;
    let mut tokens = 0usize;
    let mut lines = 0usize;
    let mut crc = 0xFFFF_FFFFu32;
    while i < bytes.len() {
        let b = bytes[i];
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
        if b == b'\\n' {
            lines += 1;
            i += 1;
        } else if b.is_ascii_whitespace() {
            i += 1;
        } else if b < 0x80 {
            tokens += 1;
            i += 1;
        } else if b < 0xE0 && i + 1 < bytes.len() {
            tokens += 1;
            i += 2;
        } else if b < 0xF0 && i + 2 < bytes.len() {
            tokens += 1;
            i += 3;
        } else if i + 3 < bytes.len() {
            tokens += 1;
            i += 4;
        } else {
            break;
        }
    }
    (tokens, lines, !crc)
}

// 3. Dense numerical / auto-vectorizable dot product, matrix-vector, and saturating clamp
#[unsafe(no_mangle)]
pub fn workload_numeric_kernels(a: &[i32], b: &[i32], out: &mut [i32]) -> i64 {
    let n = a.len().min(b.len()).min(out.len());
    let mut acc: i64 = 0;
    for i in 0..n {
        let prod = (a[i] as i64).wrapping_mul(b[i] as i64);
        acc = acc.wrapping_add(prod);
        out[i] = a[i].saturating_add(b[i]).clamp(-1_000_000, 1_000_000);
    }
    acc
}

// 4. Floating-point polynomial evaluation (Horner + FMA/sqrt/min/max)
#[unsafe(no_mangle)]
pub fn workload_fp64_horner(xs: &[f64], coeffs: &[f64], out: &mut [f64]) -> f64 {
    let n = xs.len().min(out.len());
    let mut total = 0.0f64;
    for i in 0..n {
        let x = xs[i];
        let mut p = 0.0f64;
        for &c in coeffs.iter().rev() {
            p = p * x + c;
        }
        let clamped = p.max(-1.0e6).min(1.0e6);
        out[i] = clamped;
        total += clamped;
    }
    total
}

// 5. 128-bit integer decimal formatting (itoa style)
#[unsafe(no_mangle)]
pub fn workload_format_u128(mut v: u128, buf: &mut [u8; 40]) -> usize {
    let mut idx = 40usize;
    if v == 0 {
        buf[39] = b'0';
        return 39;
    }
    while v > 0 && idx > 0 {
        idx -= 1;
        let rem = (v % 10) as u8;
        buf[idx] = b'0' + rem;
        v /= 10;
    }
    idx
}

// 6. Atomic ticket lock / reference count state transition
#[unsafe(no_mangle)]
pub fn workload_atomic_CAS_loop(counter: &AtomicUsize, limit: usize) -> bool {
    let mut cur = counter.load(Ordering::Relaxed);
    loop {
        if cur >= limit {
            return false;
        }
        match counter.compare_exchange_weak(cur, cur + 1, Ordering::AcqRel, Ordering::Relaxed) {
            Ok(_) => return true,
            Err(actual) => cur = actual,
        }
    }
}
"""


def run_opt_and_cpu_matrix():
    src = WORK_DIR / "bench_workload.rs"
    src.write_text(BENCH_WORKLOAD_RS, encoding="utf-8")

    opt_levels = ["0", "1", "2", "3", "s", "z"]
    opt_matrix = {}
    for target in ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
        arch = "x86_64" if target.startswith("x86_64") else ("i686" if target.startswith("i686") else "aarch64")
        opt_matrix[target] = {}
        for opt in opt_levels:
            obj = WORK_DIR / f"workload_{target}_opt{opt}.o"
            subprocess.run(
                [str(RUSTC), "--edition=2021", "--target", target, f"-Copt-level={opt}", "--emit=obj", str(src), "-o", str(obj)],
                capture_output=True, text=True, check=True,
            )
            tot, mnem, ops = disassemble_file(obj, arch)
            opt_matrix[target][f"opt_{opt}"] = summarize_counter(tot, mnem, ops, top_n=25)

    cpu_configs = [
        ("x86_64", "x86_64-unknown-linux-gnu", "x86-64"),
        ("x86_64", "x86_64-unknown-linux-gnu", "x86-64-v2"),
        ("x86_64", "x86_64-unknown-linux-gnu", "x86-64-v3"),
        ("x86_64", "x86_64-unknown-linux-gnu", "x86-64-v4"),
        ("aarch64", "aarch64-unknown-linux-gnu", "generic"),
        ("aarch64", "aarch64-apple-darwin", "apple-m1"),
        ("aarch64", "aarch64-apple-darwin", "apple-m3"),
        ("aarch64", "aarch64-apple-darwin", "apple-m4"),
        ("aarch64", "aarch64-unknown-linux-gnu", "neoverse-n1"),
        ("aarch64", "aarch64-unknown-linux-gnu", "neoverse-v1"),
        ("aarch64", "aarch64-unknown-linux-gnu", "neoverse-v2"),
    ]
    cpu_matrix = {}
    for arch, target, cpu in cpu_configs:
        obj = WORK_DIR / f"workload_{cpu}.o"
        subprocess.run(
            [str(RUSTC), "--edition=2021", "--target", target, "-Copt-level=3", f"-Ctarget-cpu={cpu}", "--emit=obj", str(src), "-o", str(obj)],
            capture_output=True, text=True, check=True,
        )
        tot, mnem, ops = disassemble_file(obj, arch)
        cpu_matrix[cpu] = {
            "target": target,
            "arch": arch,
            "summary": summarize_counter(tot, mnem, ops, top_n=25),
        }

    return opt_matrix, cpu_matrix


def main():
    sysroot_results = {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        for target, data in ex.map(analyze_sysroot_target, TIER1_TARGETS):
            sysroot_results[target] = data

    opt_matrix, cpu_matrix = run_opt_and_cpu_matrix()

    out = {
        "tier1_sysroot_instruction_census": sysroot_results,
        "opt_level_matrix": opt_matrix,
        "cpu_level_matrix_opt3": cpu_matrix,
    }
    (DATA_DIR / "m10_instruction_frequencies.json").write_text(json.dumps(out, indent=2), encoding="utf-8")

    print("=== Tier 1 Sysroot Aggregate Instruction Census ===")
    for t in TIER1_TARGETS:
        s = sysroot_results[t]["aggregate_sysroot"]
        print(f"  {t}: total={s['total_instructions']:,} unique_mnemonics={s['unique_mnemonics']} p90={s['mnemonics_for_coverage'].get('p90')} p99={s['mnemonics_for_coverage'].get('p99')} top10={s['cumulative_coverage_pct']['top_10_pct']}% top25={s['cumulative_coverage_pct']['top_25_pct']}%")

    print("=== CPU Microarchitecture Matrix (opt-level=3) ===")
    for cpu, info in cpu_matrix.items():
        s = info["summary"]
        print(f"  {cpu} ({info['target']}): total={s['total_instructions']} unique={s['unique_mnemonics']} top5={list(s['top_mnemonics'].items())[:5]}")


if __name__ == "__main__":
    main()
