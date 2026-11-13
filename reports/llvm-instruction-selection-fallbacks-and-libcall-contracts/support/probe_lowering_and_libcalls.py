#!/usr/bin/env python3
"""M3 Probe: LLVM 23.1.1 instruction selection fallbacks across feature sets and RuntimeLibcalls / compiler_builtins inventory across all 8 Tier 1 targets."""

import json
import os
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = TC_ROOT / "bin" / "rustc"
LLVM_NM = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "llvm-nm"
LLVM_DIR = Path("/tmp/probe_out")
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


def parse_runtime_libcalls_td():
    td_path = LLVM_DIR / "llvm__include__llvm__IR__RuntimeLibcalls.td"
    text = td_path.read_text(encoding="utf-8")
    # Match `def <ID> : RuntimeLibcallImpl<"<sym_name>"` or `def <ID> : RuntimeLibcall;`
    abstract_calls = re.findall(r"def\s+([A-Z0-9_]+)\s*:\s*RuntimeLibcall\b", text)
    impls = re.findall(r'def\s+([A-Za-z0-9_]+)\s*:\s*RuntimeLibcallImpl<\s*"([^"]+)"', text)
    return {
        "td_size_bytes": td_path.stat().st_size,
        "td_lines": len(text.splitlines()),
        "total_abstract_runtime_libcalls": len(abstract_calls),
        "total_runtime_libcall_impls": len(impls),
        "sample_impls": dict(impls[:40]),
    }


def categorize_symbol(sym: str) -> str:
    s = sym.lstrip("_")
    if s.startswith("aarch64_cas") or s.startswith("aarch64_ld") or s.startswith("aarch64_swp") or s.startswith("aarch64_st"):
        return "outline_atomics_aarch64"
    if "probestack" in s or "chkstk" in s:
        return "stack_probes"
    if s in {"memcpy", "memmove", "memset", "memcmp", "bcmp", "strlen"}:
        return "memory_primitives"
    if any(s.startswith(p) for p in ["addtf", "subtf", "multf", "divtf", "negtf", "eqtf", "netf", "getf", "gttf", "letf", "lttf", "unordtf", "trunctf", "extend", "trunc", "floatti", "floatunti", "floatdi", "floatundi", " floatsi", "floatunsi", "fixtf", "fixunstf", "fixdf", "fixunsdf", "fixsf", "fixunssf", "powi"]):
        return "soft_float_and_fp_conversions"
    if any(k in s for k in ["ti3", "ti4", "ti2"]):
        return "int128_arithmetic"
    if any(k in s for k in ["di3", "di4", "di2", "si3", "si4"]):
        return "int64_and_int32_arithmetic"
    if s.startswith("sync_") or s.startswith("atomic_"):
        return "sync_and_atomic_builtins"
    if "eh_personality" in s or "Unwind" in sym or " __gcc_personality" in sym:
        return "unwind_and_eh"
    return "other_builtins"


def scan_compiler_builtins_rlibs():
    per_target = {}
    for target in TIER1_TARGETS:
        lib_dir = TC_ROOT / "lib" / "rustlib" / target / "lib"
        rlibs = list(lib_dir.glob("libcompiler_builtins-*.rlib"))
        if not rlibs:
            continue
        rlib = rlibs[0]
        proc = subprocess.run(
            [str(LLVM_NM), "--defined-only", str(rlib)],
            capture_output=True, text=True, check=True,
        )
        defined_syms = set()
        for line in proc.stdout.splitlines():
            parts = line.strip().split()
            if len(parts) >= 3 and parts[1] in {"T", "W", "t", "w"}:
                sym = parts[2]
                if not sym.startswith("_ZN") and not sym.startswith("__RN") and not sym.startswith(".L"):
                    defined_syms.add(sym)

        cats = Counter(categorize_symbol(s) for s in defined_syms)
        key_families = {}
        for fam, pat in [
            ("int128_div_rem_mul_ovf", r"^_?_?(u?divti3|u?modti3|multi3|muloti4)$"),
            ("int64_32bit_div_rem_shift", r"^_?_?(u?divdi3|u?moddi3|mulodi4|ashldi3|lshrdi3|ashrdi3|_aulldiv|_aulldiv|_alldiv|_allrem|_aullrem|_allmul|_allshl|_allshr|_aullshr)$"),
            ("f16_f128_softfloat", r"^_?_?(addtf3|subtf3|multf3|divtf3|extendhfsf2|truncsfhf2|extendhfdf2|truncdfhf2|extendsftf2|extenddftf2|trunctfdf2|trunctfsf2|floattitf|floatuntitf|fixtfti|fixunstfti)$"),
            ("int128_float_conv", r"^_?_?(floattisf|floatuntisf|floattidf|floatuntidf|fixsfti|fixunssfti|fixdfti|fixunsdfti)$"),
            ("powi_builtins", r"^_?_?powi[sdt]f2$"),
            ("memory_builtins", r"^_?_?(memcpy|memmove|memset|memcmp|bcmp|strlen)$"),
            ("stack_probes", r"^_?_?(rust_probestack|chkstk|_chkstk|__chkstk|___chkstk_ms)$"),
            ("aarch64_outline_atomics", r"^_?_?aarch64_(cas|ldadd|ldclr|ldeor|ldset|swp)(1|2|4|8|16)_(relax|acq|rel|acq_rel)$"),
        ]:
            matched = sorted(s for s in defined_syms if re.match(pat, s))
            key_families[fam] = matched

        per_target[target] = {
            "rlib_name": rlib.name,
            "rlib_size_bytes": rlib.stat().st_size,
            "total_non_mangled_defined_symbols": len(defined_syms),
            "by_category": dict(cats),
            "key_symbol_families": key_families,
        }
    return per_target


ISEL_PROBE_RS = """#![feature(f16, f128, core_intrinsics)]
#![no_std]
#![crate_type = "rlib"]

use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

#[unsafe(no_mangle)]
pub fn probe_ctlz_u64(x: u64) -> u32 { x.leading_zeros() }

#[unsafe(no_mangle)]
pub fn probe_cttz_u64(x: u64) -> u32 { x.trailing_zeros() }

#[unsafe(no_mangle)]
pub fn probe_ctpop_u64(x: u64) -> u32 { x.count_ones() }

#[unsafe(no_mangle)]
pub fn probe_bitreverse_u64(x: u64) -> u64 { x.reverse_bits() }

#[unsafe(no_mangle)]
pub fn probe_bswap_u64(x: u64) -> u64 { x.swap_bytes() }

#[unsafe(no_mangle)]
pub fn probe_rotl_u64(x: u64, n: u32) -> u64 { x.rotate_left(n) }

#[unsafe(no_mangle)]
pub fn probe_sat_add_u32(a: u32, b: u32) -> u32 { a.saturating_add(b) }

#[unsafe(no_mangle)]
pub fn probe_sat_sub_i32(a: i32, b: i32) -> i32 { a.saturating_sub(b) }

#[unsafe(no_mangle)]
pub fn probe_u64_div_rem(a: u64, b: u64) -> (u64, u64) {
    if b == 0 { (0, 0) } else { (a / b, a % b) }
}

#[unsafe(no_mangle)]
pub fn probe_u128_add(a: u128, b: u128) -> u128 { a.wrapping_add(b) }

#[unsafe(no_mangle)]
pub fn probe_u128_mul(a: u128, b: u128) -> u128 { a.wrapping_mul(b) }

#[unsafe(no_mangle)]
pub fn probe_i128_mul_overflow(a: i128, b: i128) -> (i128, bool) { a.overflowing_mul(b) }

#[unsafe(no_mangle)]
pub fn probe_u128_div_rem(a: u128, b: u128) -> (u128, u128) {
    unsafe { (core::intrinsics::unchecked_div(a, b), core::intrinsics::unchecked_rem(a, b)) }
}

#[unsafe(no_mangle)]
pub fn probe_f64_fma(a: f64, b: f64, c: f64) -> f64 {
    core::intrinsics::fmaf64(a, b, c)
}

#[unsafe(no_mangle)]
pub fn probe_f64_round_ties_even(a: f64) -> f64 {
    core::intrinsics::round_ties_even_f64(a)
}

#[unsafe(no_mangle)]
pub fn probe_f64_rem(a: f64, b: f64) -> f64 { a % b }

#[unsafe(no_mangle)]
pub fn probe_f64_powi(a: f64, n: i32) -> f64 {
    core::intrinsics::powif64(a, n)
}

#[unsafe(no_mangle)]
pub fn probe_f64_to_i64_sat(a: f64) -> i64 { a as i64 }

#[unsafe(no_mangle)]
pub fn probe_f16_add(a: f16, b: f16) -> f16 { a + b }

#[unsafe(no_mangle)]
pub fn probe_f128_add(a: f128, b: f128) -> f128 { a + b }

#[unsafe(no_mangle)]
pub fn probe_f128_mul(a: f128, b: f128) -> f128 { a * b }

#[unsafe(no_mangle)]
pub fn probe_atomic_fetch_add_u64(p: &AtomicU64, v: u64) -> u64 {
    p.fetch_add(v, Ordering::AcqRel)
}

#[unsafe(no_mangle)]
pub fn probe_atomic_cas_usize(p: &AtomicUsize, old: usize, new: usize) -> Result<usize, usize> {
    p.compare_exchange(old, new, Ordering::SeqCst, Ordering::Acquire)
}
"""


def extract_fn_bodies_from_asm(asm_text: str):
    """Extract instructions per probe_* function from assembly text."""
    funcs = {}
    cur_fn = None
    cur_insts = []
    for raw_line in asm_text.splitlines():
        line = raw_line.strip()
        m_lbl = re.match(r"^_?(probe_[a-zA-Z0-9_]+):$", line)
        if m_lbl:
            if cur_fn:
                funcs[cur_fn] = cur_insts
            cur_fn = m_lbl.group(1)
            cur_insts = []
            continue
        if cur_fn is not None:
            if line.startswith(".Lfunc_end") or line.startswith(".seh_endproc") or line == ".cfi_endproc":
                funcs[cur_fn] = cur_insts
                cur_fn = None
                cur_insts = []
                continue
            if not line or line.startswith(".") or line.startswith("#") or line.startswith("//") or line.startswith(";"):
                continue
            if line.endswith(":"):
                continue
            # Keep compact instruction line
            cur_insts.append(re.sub(r"\s+", " ", line))
    if cur_fn and cur_fn not in funcs:
        funcs[cur_fn] = cur_insts
    return funcs


def run_isel_probes():
    probe_rs = WORK_DIR / "isel_probe.rs"
    probe_rs.write_text(ISEL_PROBE_RS, encoding="utf-8")

    configs = [
        ("x86_64_v1_baseline", "x86_64-unknown-linux-gnu", ["-Ctarget-cpu=x86-64"]),
        ("x86_64_v2_popcnt_sse42", "x86_64-unknown-linux-gnu", ["-Ctarget-cpu=x86-64-v2"]),
        ("x86_64_v3_avx2_bmi2_lzcnt_fma", "x86_64-unknown-linux-gnu", ["-Ctarget-cpu=x86-64-v3"]),
        ("x86_64_v4_avx512", "x86_64-unknown-linux-gnu", ["-Ctarget-cpu=x86-64-v4"]),
        ("i686_baseline", "i686-unknown-linux-gnu", ["-Ctarget-cpu=pentium4"]),
        ("i686_popcnt_lzcnt_bmi", "i686-unknown-linux-gnu", ["-Ctarget-feature=+popcnt,+lzcnt,+bmi1,+bmi2"]),
        ("aarch64_armv8a_baseline", "aarch64-unknown-linux-gnu", ["-Ctarget-feature=-outline-atomics"]),
        ("aarch64_outline_atomics_default", "aarch64-unknown-linux-gnu", []),
        ("aarch64_lse_fp16", "aarch64-unknown-linux-gnu", ["-Ctarget-feature=+lse,+fp16"]),
        ("aarch64_apple_darwin_m1", "aarch64-apple-darwin", []),
        ("x86_64_windows_msvc", "x86_64-pc-windows-msvc", []),
        ("i686_windows_msvc", "i686-pc-windows-msvc", []),
    ]

    results = {}
    for label, target, extra_flags in configs:
        out_s = WORK_DIR / f"isel_{label}.s"
        cmd = [
            str(RUSTC), "--edition=2021", "--target", target,
            "-Copt-level=2", "--emit=asm",
            *extra_flags,
            str(probe_rs), "-o", str(out_s),
        ]
        subprocess.run(cmd, env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, capture_output=True, text=True, check=True)
        asm_text = out_s.read_text(encoding="utf-8")
        funcs = extract_fn_bodies_from_asm(asm_text)
        results[label] = {
            "target": target,
            "flags": extra_flags,
            "functions": funcs,
        }
    return results


def main():
    td_info = parse_runtime_libcalls_td()
    rlib_info = scan_compiler_builtins_rlibs()
    isel_info = run_isel_probes()

    summary = {
        "llvm_runtime_libcalls_td": td_info,
        "tier1_compiler_builtins_rlibs": rlib_info,
        "instruction_selection_probes": isel_info,
    }
    (DATA_DIR / "m3_lowering_and_libcalls.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print("RuntimeLibcalls.td:", json.dumps(td_info, indent=2))
    for t, info in rlib_info.items():
        print(f"{t}: {info['total_non_mangled_defined_symbols']} syms | categories={info['by_category']}")
    print("Sample x86_64_v1 vs v3 ctlz/ctpop/fma:")
    for fn in ["probe_ctlz_u64", "probe_ctpop_u64", "probe_bitreverse_u64", "probe_f64_fma", "probe_u128_div_rem", "probe_f16_add", "probe_f128_add", "probe_atomic_fetch_add_u64"]:
        print(f"=== {fn} ===")
        for cfg in ["x86_64_v1_baseline", "x86_64_v3_avx2_bmi2_lzcnt_fma", "i686_baseline", "aarch64_armv8a_baseline", "aarch64_outline_atomics_default", "aarch64_lse_fp16"]:
            print(f"  {cfg}: {isel_info[cfg]['functions'].get(fn, [])[:8]}")


if __name__ == "__main__":
    main()
