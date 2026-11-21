#!/usr/bin/env python3
"""Self-contained empirical probe for rustc c_variadic, VaList ABIs, Miri UB, and #[unsafe(naked)].

Writes durable specimens under support/specimens/ and compiles/executes them inside a
temporary working directory, recording MIR, LLVM IR, assembly, native execution outputs,
GCC <-> Rust FFI interop, GCC SysV __int128 va_arg behavior, Miri diagnostics, 8-target
cross-compilation metadata, and compile-rejection checks into support/probe_results.json
with all temporary/host paths scrubbed.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

SUPPORT_DIR = Path(__file__).resolve().parent
SPECIMENS_DIR = SUPPORT_DIR / "specimens"
RESULTS_PATH = SUPPORT_DIR / "probe_results.json"

SPECIMENS: dict[str, str] = {
    "variadic_sysv_probe.rs": r'''#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_vsum_indirect_valist(tag_count: usize, mut ap: VaList<'_>) -> u64 {
    let kind = tag_count & 0xff;
    match kind {
        0 => {
            let a = unsafe { ap.next_arg::<u64>() };
            let b = unsafe { ap.next_arg::<u64>() };
            a + b
        }
        1 => {
            // Reads 6 GP arguments (including fixed `tag_count` => 5 variadic GP args in regs
            // plus 1 variadic GP overflow slot on stack) and 2 XMM f64 arguments.
            let mut sum: u64 = 0;
            sum += unsafe { ap.next_arg::<i32>() } as u64;
            sum += (unsafe { ap.next_arg::<f64>() }) as u64;
            sum += unsafe { ap.next_arg::<i32>() } as u64;
            sum += unsafe { ap.next_arg::<u64>() };
            sum += (unsafe { ap.next_arg::<f64>() }) as u64;
            sum += unsafe { ap.next_arg::<u64>() };
            sum += unsafe { ap.next_arg::<u64>() };
            sum += unsafe { ap.next_arg::<u64>() };
            sum
        }
        2 => {
            let mut sum: u64 = 0;
            for _ in 0..9 {
                sum += (unsafe { ap.next_arg::<f64>() }) as u64;
            }
            sum
        }
        _ => 0,
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_variadic_mixed(tag_count: usize, ap: ...) -> u64 {
    unsafe { rust_vsum_indirect_valist(tag_count, ap) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_zero_floats() -> u64 {
    unsafe { rust_variadic_mixed(0, 100u64, 100u64) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_two_floats_and_overflow() -> u64 {
    // 1 fixed GP + 6 variadic GP args => 7th GP arg (1000u64) overflows to caller stack!
    // Plus 2 variadic f64 args => caller sets %al = 2 (`movb $2, %al`).
    unsafe { rust_variadic_mixed(1, 10i32, 20.0f64, 30i32, 40u64, 50.0f64, 60u64, 10u64, 1000u64) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_nine_floats() -> u64 {
    // 9 variadic f64 args => %xmm0..%xmm7 filled (%al = 8) + 9th f64 pushed onto stack.
    unsafe { rust_variadic_mixed(2, 1.0f64, 2.0f64, 3.0f64, 4.0f64, 5.0f64, 6.0f64, 7.0f64, 8.0f64, 9.0f64) }
}

fn main() {
    let z = call_zero_floats();
    let m = call_two_floats_and_overflow();
    let nf = call_nine_floats();
    let sz = core::mem::size_of::<VaList<'_>>();
    let al = core::mem::align_of::<VaList<'_>>();
    println!("ZERO_FP={z} MIXED_OVERFLOW={m} NINE_FP={nf} VALIST_SZ={sz} VALIST_ALIGN={al}");
}
''',
    "variadic_clone_fork_probe.rs": r'''#![allow(stable_features)]
#![feature(c_variadic)]

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_variadic_clone_fork(count: usize, mut ap: ...) -> u64 {
    let mut ap_fork = ap.clone();
    let mut fork_sum: u64 = 0;
    for _ in 0..count {
        fork_sum += unsafe { ap_fork.next_arg::<u64>() };
    }
    drop(ap_fork);
    let mut orig_sum: u64 = 0;
    for _ in 0..count {
        orig_sum += unsafe { ap.next_arg::<u64>() };
    }
    if fork_sum == orig_sum { orig_sum } else { u64::MAX }
}

fn main() {
    let cf = unsafe { rust_variadic_clone_fork(4, 11u64, 22u64, 33u64, 44u64) };
    println!("CLONE_FORK={cf}");
}
''',
    "rust_c_interop_lib.rs": r'''#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

unsafe extern "C" {
    fn c_vsum_takes_valist(count: usize, ap: VaList<'_>) -> u64;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_vsum_indirect_valist(tag_count: usize, mut ap: VaList<'_>) -> u64 {
    let kind = tag_count & 0xff;
    if kind == 1 {
        let mut sum: u64 = 0;
        sum += unsafe { ap.next_arg::<i32>() } as u64;
        sum += (unsafe { ap.next_arg::<f64>() }) as u64;
        sum += unsafe { ap.next_arg::<i32>() } as u64;
        sum += unsafe { ap.next_arg::<u64>() };
        sum += (unsafe { ap.next_arg::<f64>() }) as u64;
        sum += unsafe { ap.next_arg::<u64>() };
        sum += unsafe { ap.next_arg::<u64>() };
        sum += unsafe { ap.next_arg::<u64>() };
        sum
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_variadic_mixed(tag_count: usize, ap: ...) -> u64 {
    unsafe { rust_vsum_indirect_valist(tag_count, ap) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_calls_c_valist_twice(count: usize, mut ap: ...) -> u64 {
    let c_sum = unsafe { c_vsum_takes_valist(count, ap.clone()) };
    let r_first = unsafe { ap.next_arg::<u64>() };
    c_sum * 1000 + r_first
}
''',
    "c_rust_interop.c": r'''#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t rust_variadic_mixed(size_t tag_count, ...);
extern uint64_t rust_vsum_indirect_valist(size_t tag_count, va_list ap);
extern uint64_t rust_calls_c_valist_twice(size_t count, ...);

uint64_t c_vsum_takes_valist(size_t count, va_list ap) {
    uint64_t s = 0;
    for (size_t i = 0; i < count; i++) {
        s += va_arg(ap, uint64_t);
    }
    return s;
}

static uint64_t forward_va_list(size_t tag_count, ...) {
    va_list ap;
    va_start(ap, tag_count);
    uint64_t r = rust_vsum_indirect_valist(tag_count, ap);
    va_end(ap);
    return r;
}

int main(void) {
    uint64_t direct = rust_variadic_mixed(
        1, (int32_t)10, 20.0, (int32_t)30, (uint64_t)40, 50.0, (uint64_t)60, (uint64_t)10, (uint64_t)1000
    );
    uint64_t decay = forward_va_list(
        1, (int32_t)10, 20.0, (int32_t)30, (uint64_t)40, 50.0, (uint64_t)60, (uint64_t)10, (uint64_t)1000
    );
    uint64_t r2c = rust_calls_c_valist_twice(3, (uint64_t)100, (uint64_t)200, (uint64_t)300);
    printf("C_TO_RUST_VA=%llu C_VA_LIST_DECAY=%llu RUST_TO_C_VA_DECAY=%llu\n",
           (unsigned long long)direct,
           (unsigned long long)decay,
           (unsigned long long)r2c);
    return 0;
}
''',
    "c_u128_sysv_probe.c": r'''#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

typedef unsigned __int128 u128;

__attribute__((noinline))
u128 read_1gp_then_u128_then_u64(uint64_t a0, ...) {
    va_list ap;
    va_start(ap, a0);
    u128 x = va_arg(ap, u128);
    uint64_t tail = va_arg(ap, uint64_t);
    va_end(ap);
    return x + tail;
}

__attribute__((noinline))
u128 read_5gp_then_u128_then_u64(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, ...) {
    va_list ap;
    va_start(ap, a4);
    u128 x = va_arg(ap, u128);
    uint64_t tail = va_arg(ap, uint64_t);
    va_end(ap);
    return x + tail;
}

__attribute__((noinline))
u128 read_7gp_then_u128(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5, ...) {
    va_list ap;
    va_start(ap, a5);
    uint64_t s0 = va_arg(ap, uint64_t);
    u128 x = va_arg(ap, u128);
    va_end(ap);
    return x + s0;
}

int main(void) {
    u128 v = (((u128)0x1122334455667788ULL) << 64) | 0x99AABBCCDDEEFF00ULL;
    u128 r1 = read_1gp_then_u128_then_u64(1, v, (uint64_t)7);
    u128 r2 = read_5gp_then_u128_then_u64(1, 2, 3, 4, 5, v, (uint64_t)9);
    u128 r3 = read_7gp_then_u128(1, 2, 3, 4, 5, 6, (uint64_t)11, v);
    printf("U128_ODD_GP_OK=%d U128_SPILL_R9_BACKFILL_OK=%d U128_OVERFLOW_ALIGN16_OK=%d\n",
           r1 == v + 7, r2 == v + 9, r3 == v + 11);
    return 0;
}
''',
    "cross_target_valist_matrix.rs": r'''#![no_std]
#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

#[unsafe(no_mangle)]
pub extern "C" fn valist_size() -> usize {
    core::mem::size_of::<VaList<'_>>()
}

#[unsafe(no_mangle)]
pub extern "C" fn valist_align() -> usize {
    core::mem::align_of::<VaList<'_>>()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn takes_valist_reads_i32_f64(mut ap: VaList<'_>) -> u64 {
    let a = unsafe { ap.next_arg::<i32>() } as u64;
    let b = (unsafe { ap.next_arg::<f64>() }) as u64;
    a + b
}
''',
    "naked_ok.rs": r'''use core::arch::naked_asm;

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub extern "C" fn naked_add_mul(a: u64, b: u64, c: u64) -> u64 {
    naked_asm!(
        "lea rax, [rdi + rsi]",
        "imul rax, rdx",
        "ret",
    )
}

fn main() {
    let v1 = naked_add_mul(3, 4, 5);
    println!("NAKED_OK={v1}");
}
''',
    "naked_aarch64_bti_compare.rs": r'''#![no_std]
use core::arch::naked_asm;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn normal_add1(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub extern "C" fn naked_add1(_x: u64) -> u64 {
    naked_asm!("add x0, x0, #1", "ret")
}
''',
}

MIRI_TESTS: dict[str, tuple[str, int]] = {
    "miri_type_mismatch_ub": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
unsafe extern "C" fn read_u64(_n: usize, mut ap: ...) -> u64 {
    unsafe { ap.next_arg::<u64>() }
}
fn main() {
    let _ = unsafe { read_u64(1, 3.5f64) };
}
""",
        1,
    ),
    "miri_signed_value_mismatch_ub": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
unsafe extern "C" fn read_u32(_n: usize, mut ap: ...) -> u32 {
    unsafe { ap.next_arg::<u32>() }
}
fn main() {
    let _ = unsafe { read_u32(1, -1i32) };
}
""",
        1,
    ),
    "miri_signed_nonneg_compatible_ok": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
unsafe extern "C" fn read_u32(_n: usize, mut ap: ...) -> u32 {
    unsafe { ap.next_arg::<u32>() }
}
fn main() {
    let v = unsafe { read_u32(1, 42i32) };
    println!("COMPAT_I32_AS_U32={v}");
}
""",
        0,
    ),
    "miri_out_of_bounds_ub": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
unsafe extern "C" fn read_two(_n: usize, mut ap: ...) -> u64 {
    let a = unsafe { ap.next_arg::<u64>() };
    let b = unsafe { ap.next_arg::<u64>() };
    a + b
}
fn main() {
    let _ = unsafe { read_two(1, 7u64) };
}
""",
        1,
    ),
    "miri_raw_memcpy_after_step_ub": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
use core::ffi::VaList;
unsafe extern "C" fn raw_copy_bypass(_n: usize, mut ap: ...) -> u64 {
    let mut raw_copy: VaList<'_> = unsafe { core::ptr::read(&ap) };
    let a = unsafe { ap.next_arg::<u64>() };
    let b = unsafe { raw_copy.next_arg::<u64>() };
    core::mem::forget(raw_copy);
    a + b
}
fn main() {
    let _ = unsafe { raw_copy_bypass(2, 10u64, 20u64) };
}
""",
        1,
    ),
    "miri_use_after_va_end_ub": (
        """#![allow(stable_features)]
#![feature(c_variadic)]
use core::mem::ManuallyDrop;
unsafe extern "C" fn use_after_drop(_n: usize, ap: ...) -> u64 {
    let mut md = ManuallyDrop::new(ap);
    unsafe { ManuallyDrop::drop(&mut md) };
    unsafe { md.next_arg::<u64>() }
}
fn main() {
    let _ = unsafe { use_after_drop(1, 99u64) };
}
""",
        1,
    ),
    "miri_va_copy_fork_probe": (
        SPECIMENS["variadic_clone_fork_probe.rs"],
        0,
    ),
}

COMPILE_REJECTION_TESTS: dict[str, str] = {
    "naked_non_asm_and_param_ref": r'''#[unsafe(naked)]
pub extern "C" fn bad_naked(x: u64) -> u64 {
    x + 1
}
''',
    "naked_uses_asm_instead_of_naked_asm": r'''use core::arch::asm;
#[unsafe(naked)]
pub extern "C" fn bad_asm_macro(_x: u64) -> u64 {
    asm!("ret", options(noreturn))
}
''',
    "naked_pattern_param": r'''use core::arch::naked_asm;
#[unsafe(naked)]
pub extern "C" fn bad_pattern((a, _b): (u64, u64)) -> u64 {
    naked_asm!("mov rax, 0", "ret")
}
''',
    "naked_with_in_operand": r'''use core::arch::naked_asm;
#[unsafe(naked)]
pub extern "C" fn bad_operand(x: u64) -> u64 {
    naked_asm!("ret", in("rdi") x)
}
''',
    "naked_with_nostack_option": r'''use core::arch::naked_asm;
#[unsafe(naked)]
pub extern "C" fn bad_option() {
    naked_asm!("ret", options(nostack))
}
''',
    "extern_custom_without_naked": r'''pub unsafe extern "custom" fn needs_naked() {}
''',
    "extern_custom_with_feature_without_naked": r'''#![feature(abi_custom)]
pub unsafe extern "custom" fn needs_naked() {}
''',
    "naked_incompatible_inline_e0736": r'''use core::arch::naked_asm;
#[unsafe(naked)]
#[inline(never)]
pub extern "C" fn bad_inline() {
    naked_asm!("ret")
}
''',
    "variadic_call_promoted_f32_e0617": r'''unsafe extern "C" { fn cv(n: i32, ...); }
pub fn bad_f32() { unsafe { cv(1, 1.5f32); } }
''',
    "variadic_call_promoted_i8_e0617": r'''unsafe extern "C" { fn cv(n: i32, ...); }
pub fn bad_i8() { unsafe { cv(1, 5i8); } }
''',
    "variadic_call_promoted_bool_e0617": r'''unsafe extern "C" { fn cv(n: i32, ...); }
pub fn bad_bool() { unsafe { cv(1, true); } }
''',
    "variadic_call_fndef_e0617": r'''unsafe extern "C" { fn cv(n: i32, ...); }
fn target_fn() {}
pub fn bad_fndef() { unsafe { cv(1, target_fn); } }
''',
    "variadic_call_char_allowed_by_hir_check": r'''unsafe extern "C" { fn cv(n: i32, ...); }
pub fn allows_char() { unsafe { cv(1, 'A'); } }
''',
    "variadic_without_feature_gate_probe": r'''pub unsafe extern "C" fn vfn(_n: usize, mut ap: ...) -> i32 {
    unsafe { ap.next_arg::<i32>() }
}
''',
    "variadic_int128_probe": r'''#![allow(stable_features)]
#![feature(c_variadic)]
pub unsafe extern "C" fn vfn_u128(_n: usize, mut ap: ...) -> u128 {
    unsafe { ap.next_arg::<u128>() }
}
''',
    "naked_c_variadic_with_wild_probe": r'''#![allow(stable_features)]
#![feature(c_variadic)]
use core::arch::naked_asm;
#[unsafe(naked)]
pub unsafe extern "C" fn naked_var(_tag: u64, _: ...) -> u64 {
    naked_asm!("mov rax, rdi", "ret")
}
''',
    "naked_c_variadic_sysv64_probe": r'''#![allow(stable_features)]
#![feature(c_variadic)]
use core::arch::naked_asm;
#[unsafe(naked)]
pub unsafe extern "sysv64" fn naked_var_sysv64(_tag: u64, _: ...) -> u64 {
    naked_asm!("mov rax, rdi", "ret")
}
''',
    "naked_c_variadic_rust_abi_rejected": r'''#![allow(stable_features)]
#![feature(c_variadic)]
use core::arch::naked_asm;
#[unsafe(naked)]
pub unsafe extern "Rust" fn naked_var_rust(_tag: u64, _: ...) -> u64 {
    naked_asm!("mov rax, rdi", "ret")
}
''',
}

TARGETS_TO_PROBE = [
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "i686-unknown-linux-gnu",
    "powerpc64-unknown-linux-gnu",
    "riscv64gc-unknown-none-elf",
]


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False)


def scrub_text(s: str, tmpdir: Path) -> str:
    s = s.replace(str(tmpdir), "<TMP>")
    s = s.replace(str(SPECIMENS_DIR), "<SPECIMENS>")
    home = os.environ.get("HOME", "")
    if home:
        s = s.replace(home, "<HOME>")
    s = re.sub(r"/tmp/[A-Za-z0-9_.-]+", "<TMP>", s)
    return s


def extract_symbol_asm(asm_text: str, sym_fragment: str) -> str:
    lines = asm_text.splitlines()
    out: list[str] = []
    capturing = False
    for line in lines:
        stripped = line.strip()
        if sym_fragment in stripped and stripped.endswith(":") and not stripped.startswith("."):
            capturing = True
        if capturing:
            out.append(line)
            if ".cfi_endproc" in line or ".size" in line:
                if ".size" in line:
                    break
                if "naked" not in sym_fragment:
                    break
            elif stripped == ".text" or stripped.startswith(".section"):
                if len(out) > 2:
                    out.pop()
                    break
    return "\n".join(out)


def extract_llvm_fn(ll_text: str, fn_fragment: str) -> str:
    lines = ll_text.splitlines()
    out: list[str] = []
    capturing = False
    for line in lines:
        if f"@{fn_fragment}(" in line and line.startswith("define "):
            capturing = True
        if capturing:
            out.append(line)
            if line == "}":
                break
    return "\n".join(out)


def run_miri_crate(tmpdir: Path, name: str, source: str, env: dict[str, str]) -> dict[str, object]:
    crate_dir = tmpdir / f"miri_{name}"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "miri_{name}"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (crate_dir / "src" / "main.rs").write_text(source, encoding="utf-8")
    proc = run_cmd(["cargo", "miri", "run", "--offline", "-q"], cwd=crate_dir, env=env)
    return {
        "rc": proc.returncode,
        "stdout": scrub_text(proc.stdout.strip(), tmpdir),
        "stderr": scrub_text(proc.stderr.strip(), tmpdir),
    }


def main() -> int:
    SPECIMENS_DIR.mkdir(parents=True, exist_ok=True)
    for fname, content in SPECIMENS.items():
        (SPECIMENS_DIR / fname).write_text(content, encoding="utf-8")

    env = os.environ.copy()
    home = os.environ.get("HOME", "")
    extra_bins = [f"{home}/.cargo/bin", f"{home}/.elan/bin", f"{home}/.local/bin"]
    env["PATH"] = ":".join(extra_bins + [env.get("PATH", "")])

    rustc_ver = run_cmd(["rustc", "--version", "-v"], env=env).stdout.strip()
    miri_ver = run_cmd(["cargo", "miri", "--version"], env=env).stdout.strip()
    gcc_ver = run_cmd(["gcc", "--version"], env=env).stdout.splitlines()[0].strip()

    results: dict[str, object] = {
        "rustc_version": rustc_ver,
        "miri_version": miri_ver,
        "gcc_version": gcc_ver,
    }

    with tempfile.TemporaryDirectory(prefix="cvar_probe_") as raw_tmp:
        tmpdir = Path(raw_tmp)
        remap = f"{SPECIMENS_DIR}=<SPECIMENS>"

        # 1. Variadic SysV probe: native, asm, LLVM IR, MIR, and Miri (+ separate clone fork probe).
        vp_src = SPECIMENS_DIR / "variadic_sysv_probe.rs"
        vp_bin = tmpdir / "variadic_sysv_probe"
        c_bin = run_cmd(
            ["rustc", "--edition=2021", "-C", "opt-level=2", "--remap-path-prefix", remap, str(vp_src), "-o", str(vp_bin)],
            env=env,
        )
        assert c_bin.returncode == 0, c_bin.stderr
        native_run = run_cmd([str(vp_bin)], env=env)
        assert native_run.returncode == 0, native_run.stderr

        cf_bin = tmpdir / "variadic_clone_fork_probe"
        c_cf = run_cmd(
            ["rustc", "--edition=2021", "-C", "opt-level=2", "--remap-path-prefix", remap, str(SPECIMENS_DIR / "variadic_clone_fork_probe.rs"), "-o", str(cf_bin)],
            env=env,
        )
        assert c_cf.returncode == 0, c_cf.stderr
        cf_run = run_cmd([str(cf_bin)], env=env)
        assert cf_run.returncode == 0, cf_run.stderr

        vp_asm = tmpdir / "variadic_sysv_probe.s"
        c_asm = run_cmd(
            [
                "rustc", "--edition=2021", "-C", "opt-level=2", "-C", "codegen-units=1",
                "-C", "symbol-mangling-version=v0", "--emit=asm", "--remap-path-prefix", remap,
                str(vp_src), "-o", str(vp_asm),
            ],
            env=env,
        )
        assert c_asm.returncode == 0, c_asm.stderr
        asm_text = vp_asm.read_text(encoding="utf-8")
        (SPECIMENS_DIR / "variadic_sysv_probe.s").write_text(asm_text, encoding="utf-8")

        vp_ll = tmpdir / "variadic_sysv_probe.ll"
        c_ll = run_cmd(
            [
                "rustc", "--edition=2021", "-C", "opt-level=2", "-C", "codegen-units=1",
                "-C", "symbol-mangling-version=v0", "--emit=llvm-ir", "--remap-path-prefix", remap,
                str(vp_src), "-o", str(vp_ll),
            ],
            env=env,
        )
        assert c_ll.returncode == 0, c_ll.stderr
        ll_text = vp_ll.read_text(encoding="utf-8")

        vp_mir = tmpdir / "variadic_sysv_probe.mir"
        c_mir = run_cmd(
            [
                "rustc", "--edition=2021", "-C", "opt-level=2", "--emit=mir",
                "--remap-path-prefix", remap, str(vp_src), "-o", str(vp_mir),
            ],
            env=env,
        )
        assert c_mir.returncode == 0, c_mir.stderr
        mir_text = vp_mir.read_text(encoding="utf-8")
        mir_excerpt: list[str] = []
        cap = False
        for line in mir_text.splitlines():
            if line.startswith("fn rust_variadic_mixed("):
                cap = True
            if cap:
                mir_excerpt.append(line)
                if line == "}" and len(mir_excerpt) > 3:
                    break

        miri_ok = run_miri_crate(tmpdir, "variadic_sysv_ok", SPECIMENS["variadic_sysv_probe.rs"], env)

        results["part_a_c_variadic_sysv"] = {
            "native_stdout": native_run.stdout.strip(),
            "clone_fork_native_stdout": cf_run.stdout.strip(),
            "miri_rc": miri_ok["rc"],
            "miri_stdout": miri_ok["stdout"],
            "miri_stderr": miri_ok["stderr"],
            "call_zero_floats_asm": extract_symbol_asm(asm_text, "call_zero_floats"),
            "call_two_floats_and_overflow_asm": extract_symbol_asm(asm_text, "call_two_floats_and_overflow"),
            "call_nine_floats_asm": extract_symbol_asm(asm_text, "call_nine_floats"),
            "rust_variadic_mixed_mir": "\n".join(mir_excerpt),
            "rust_variadic_mixed_llvm_ir": extract_llvm_fn(ll_text, "rust_variadic_mixed"),
            "rust_vsum_indirect_valist_llvm_ir_head": "\n".join(
                extract_llvm_fn(ll_text, "rust_vsum_indirect_valist").splitlines()[:45]
            ),
        }

        # 2. Bidirectional GCC <-> Rust FFI interop & GCC u128 SysV probe.
        lib_obj = tmpdir / "librust_c_interop.a"
        c_lib = run_cmd(
            [
                "rustc", "--edition=2021", "--crate-type=staticlib", "-C", "opt-level=2",
                "--remap-path-prefix", remap, str(SPECIMENS_DIR / "rust_c_interop_lib.rs"), "-o", str(lib_obj),
            ],
            env=env,
        )
        assert c_lib.returncode == 0, c_lib.stderr
        interop_bin = tmpdir / "c_rust_interop"
        c_cc = run_cmd(
            ["gcc", "-O2", str(SPECIMENS_DIR / "c_rust_interop.c"), str(lib_obj), "-lpthread", "-ldl", "-lm", "-o", str(interop_bin)],
            env=env,
        )
        assert c_cc.returncode == 0, c_cc.stderr
        interop_run = run_cmd([str(interop_bin)], env=env)
        assert interop_run.returncode == 0, interop_run.stderr

        u128_asm = tmpdir / "c_u128_sysv_probe.s"
        u128_bin = tmpdir / "c_u128_sysv_probe"
        c_u128_s = run_cmd(["gcc", "-O2", "-S", str(SPECIMENS_DIR / "c_u128_sysv_probe.c"), "-o", str(u128_asm)], env=env)
        c_u128_b = run_cmd(["gcc", "-O2", str(SPECIMENS_DIR / "c_u128_sysv_probe.c"), "-o", str(u128_bin)], env=env)
        assert c_u128_s.returncode == 0 and c_u128_b.returncode == 0, c_u128_b.stderr
        u128_run = run_cmd([str(u128_bin)], env=env)
        assert u128_run.returncode == 0, u128_run.stderr
        u128_asm_txt = u128_asm.read_text(encoding="utf-8")
        (SPECIMENS_DIR / "c_u128_sysv_probe.s").write_text(u128_asm_txt, encoding="utf-8")

        results["part_b_gcc_rust_interop_and_u128"] = {
            "c_rust_interop_stdout": interop_run.stdout.strip(),
            "c_u128_sysv_stdout": u128_run.stdout.strip(),
            "read_5gp_then_u128_then_u64_gcc_asm": extract_symbol_asm(u128_asm_txt, "read_5gp_then_u128_then_u64"),
            "read_7gp_then_u128_gcc_asm": extract_symbol_asm(u128_asm_txt, "read_7gp_then_u128"),
        }

        # 3. Miri UB discrimination suite.
        miri_suite: dict[str, object] = {}
        for mname, (msrc, expected_rc) in MIRI_TESTS.items():
            res = run_miri_crate(tmpdir, mname, msrc, env)
            res["expected_rc_on_1_99_plus"] = expected_rc
            miri_suite[mname] = res
        results["part_c_miri_ub_suite"] = miri_suite

        # 4. 8-target VaList & emit_va_arg cross-compilation matrix.
        cross_matrix: dict[str, object] = {}
        matrix_src = SPECIMENS_DIR / "cross_target_valist_matrix.rs"
        for tgt in TARGETS_TO_PROBE:
            out_ll = tmpdir / f"matrix_{tgt}.ll"
            p = run_cmd(
                [
                    "rustc", "--edition=2021", "--crate-type=lib", "--target", tgt,
                    "-C", "opt-level=2", "-Z", "merge-functions=disabled",
                    "--emit=llvm-ir", "--remap-path-prefix", remap,
                    str(matrix_src), "-o", str(out_ll),
                ],
                env=env,
            )
            entry: dict[str, object] = {"rc": p.returncode}
            if p.returncode == 0:
                ir = out_ll.read_text(encoding="utf-8")
                sz_ir = extract_llvm_fn(ir, "valist_size")
                al_ir = extract_llvm_fn(ir, "valist_align")
                m_sz = re.search(r"ret i\d+ (\d+)", sz_ir)
                m_al = re.search(r"ret i\d+ (\d+)", al_ir)
                fn_ir = extract_llvm_fn(ir, "takes_valist_reads_i32_f64")
                sig_line = fn_ir.splitlines()[0] if fn_ir else ""
                entry.update({
                    "valist_size_bytes": int(m_sz.group(1)) if m_sz else None,
                    "valist_align_bytes": int(m_al.group(1)) if m_al else None,
                    "takes_valist_ir_signature": sig_line,
                    "uses_byval": "byval" in sig_line,
                    "uses_llvm_va_arg_instruction": "va_arg " in fn_ir,
                    "ir_line_count": len(fn_ir.splitlines()),
                    "ir_head": "\n".join(fn_ir.splitlines()[:28]),
                })
            else:
                entry["stderr"] = scrub_text(p.stderr.strip(), tmpdir)
            cross_matrix[tgt] = entry
        results["part_d_cross_target_valist_matrix"] = cross_matrix

        # 5. #[unsafe(naked)] execution, assembly, LLVM IR, AArch64 BTI/PAC, and compile rejections.
        naked_src = SPECIMENS_DIR / "naked_ok.rs"
        naked_bin = tmpdir / "naked_ok"
        c_nk = run_cmd(
            ["rustc", "--edition=2021", "-C", "opt-level=2", "--remap-path-prefix", remap, str(naked_src), "-o", str(naked_bin)],
            env=env,
        )
        assert c_nk.returncode == 0, c_nk.stderr
        nk_run = run_cmd([str(naked_bin)], env=env)
        assert nk_run.returncode == 0, nk_run.stderr

        nk_asm = tmpdir / "naked_ok.s"
        nk_ll = tmpdir / "naked_ok.ll"
        run_cmd(
            [
                "rustc", "--edition=2021", "-C", "opt-level=2", "-C", "codegen-units=1",
                "--emit=asm", "--remap-path-prefix", remap, str(naked_src), "-o", str(nk_asm),
            ],
            env=env,
        )
        run_cmd(
            [
                "rustc", "--edition=2021", "-C", "opt-level=2", "-C", "codegen-units=1",
                "--emit=llvm-ir", "--remap-path-prefix", remap, str(naked_src), "-o", str(nk_ll),
            ],
            env=env,
        )
        nk_asm_txt = nk_asm.read_text(encoding="utf-8")
        nk_ll_txt = nk_ll.read_text(encoding="utf-8")
        (SPECIMENS_DIR / "naked_ok.s").write_text(nk_asm_txt, encoding="utf-8")

        bti_s = tmpdir / "naked_aarch64_bti.s"
        bti_ll = tmpdir / "naked_aarch64_bti.ll"
        c_bti_s = run_cmd(
            [
                "rustc", "--edition=2021", "--crate-type=lib", "--target", "aarch64-unknown-linux-gnu",
                "-C", "opt-level=2", "-Z", "branch-protection=bti,pac-ret",
                "-C", "unsafe-allow-abi-mismatch=branch-protection", "--emit=asm",
                "--remap-path-prefix", remap, str(SPECIMENS_DIR / "naked_aarch64_bti_compare.rs"), "-o", str(bti_s),
            ],
            env=env,
        )
        c_bti_ll = run_cmd(
            [
                "rustc", "--edition=2021", "--crate-type=lib", "--target", "aarch64-unknown-linux-gnu",
                "-C", "opt-level=2", "-Z", "branch-protection=bti,pac-ret",
                "-C", "unsafe-allow-abi-mismatch=branch-protection", "--emit=llvm-ir",
                "--remap-path-prefix", remap, str(SPECIMENS_DIR / "naked_aarch64_bti_compare.rs"), "-o", str(bti_ll),
            ],
            env=env,
        )
        bti_s_txt = bti_s.read_text(encoding="utf-8") if c_bti_s.returncode == 0 else ""
        bti_ll_txt = bti_ll.read_text(encoding="utf-8") if c_bti_ll.returncode == 0 else ""

        rejects: dict[str, object] = {}
        for rname, rsrc in COMPILE_REJECTION_TESTS.items():
            rf = tmpdir / f"{rname}.rs"
            rf.write_text(rsrc, encoding="utf-8")
            ro = tmpdir / f"{rname}.rlib"
            rp = run_cmd(
                [
                    "rustc", "--edition=2021", "--crate-type=lib",
                    "--remap-path-prefix", f"{tmpdir}=<TMP>", str(rf), "-o", str(ro),
                ],
                env=env,
            )
            rejects[rname] = {
                "rc": rp.returncode,
                "stderr": scrub_text(rp.stderr.strip(), tmpdir),
            }

        results["part_e_unsafe_naked_and_rejections"] = {
            "naked_ok_stdout": nk_run.stdout.strip(),
            "naked_add_mul_asm": extract_symbol_asm(nk_asm_txt, "naked_add_mul"),
            "naked_ok_module_asm_lines": [l for l in nk_ll_txt.splitlines() if l.startswith("module asm") or "naked_add_mul" in l],
            "aarch64_bti_rc": c_bti_s.returncode,
            "aarch64_bti_normal_add1_asm": extract_symbol_asm(bti_s_txt, "normal_add1"),
            "aarch64_bti_naked_add1_asm": extract_symbol_asm(bti_s_txt, "naked_add1"),
            "aarch64_bti_llvm_attrs": [l for l in bti_ll_txt.splitlines() if "branch-target-enforcement" in l or "sign-return-address" in l or l.startswith("module asm")],
            "compile_rejections": rejects,
        }

    RESULTS_PATH.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {RESULTS_PATH} ({RESULTS_PATH.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
