#!/usr/bin/env python3
"""
Empirically probe and classify C3: Backend-dependent observable behavior across LLVM, Cranelift, and GCC backends.
"""
import json
import os
import subprocess
import tempfile
from pathlib import Path

OUT_DIR = Path("/tmp/reval")
OUT_DIR.mkdir(parents=True, exist_ok=True)
TMP_DIR = Path("/tmp/reval")
os.environ["TMPDIR"] = str(TMP_DIR)

PROBE_RS = r'''
#![allow(internal_features, unsafe_op_in_unsafe_fn, function_item_references)]
#![feature(intrinsics, rustc_attrs, used_with_arg)]

use std::hint::black_box;
use std::sync::atomic::{AtomicU64, Ordering};



pub fn generic_id<T: Copy>(x: T) -> T { x }

pub trait MyTrait { fn act(&self) -> u64; }
impl MyTrait for u64 { fn act(&self) -> u64 { *self } }

pub const CONST_ARR: [u8; 16] = *b"0123456789abcdef";
pub static STATIC_A: [u8; 16] = *b"0123456789abcdef";
pub static STATIC_B: [u8; 16] = *b"0123456789abcdef";

#[used]
static KEEP_USED_DEFAULT: u64 = 0x1122334455667788;

#[used(linker)]
static KEEP_USED_LINKER: u64 = 0x8877665544332211;

#[link_section = ".custom_sec"]
#[used(linker)]
pub static SEC_ITEM_1: u64 = 0xAAAABBBBCCCCDDDD;

#[link_section = ".custom_sec"]
#[used(linker)]
pub static SEC_ITEM_2: u64 = 0x1111222233334444;

#[inline(never)]
#[cold]
#[no_mangle]
pub extern "C" fn cold_never_inline(x: u64) -> u64 {
    black_box(x).wrapping_add(7)
}

#[no_mangle]
pub unsafe extern "C" fn probe_volatile_u64(p: *mut u64) -> u64 {
    let v = core::ptr::read_volatile(p);
    core::ptr::write_volatile(p, v + 1);
    v
}

#[no_mangle]
pub extern "C" fn probe_atomic_seqcst(a: &AtomicU64, v: u64) -> u64 {
    a.store(v, Ordering::SeqCst);
    a.load(Ordering::SeqCst) + a.fetch_add(1, Ordering::AcqRel)
}

#[no_mangle]
pub extern "C" fn probe_abort_intrinsic() {
    // Triggers UnwindTerminate(Abi) — identical MIR terminator to intrinsics::abort()
    panic!("abort via nounwind extern C");
}

#[no_mangle]
pub extern "C" fn probe_process_abort() -> ! {
    std::process::abort()
}

#[no_mangle]
pub unsafe extern "C" fn probe_unreachable_unchecked() -> ! {
    core::hint::unreachable_unchecked()
}

#[inline(never)]
pub fn measure_frame_step(depth: usize, prev_sp: usize) -> isize {
    let local: [u8; 64] = black_box([depth as u8; 64]);
    let cur_sp = &local as *const _ as usize;
    if depth == 0 {
        (prev_sp as isize) - (cur_sp as isize)
    } else {
        measure_frame_step(depth - 1, cur_sp)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        match args[1].as_str() {
            "abort_intrinsic" => probe_abort_intrinsic(),
            "process_abort" => probe_process_abort(),
            "unreachable" => unsafe { probe_unreachable_unchecked() },
            _ => {}
        }
    }

    // Keep references so linker --gc-sections retains the probe functions
    black_box(probe_volatile_u64 as usize);
    black_box(probe_atomic_seqcst as usize);
    black_box(probe_abort_intrinsic as usize);
    black_box(probe_process_abort as usize);
    black_box(probe_unreachable_unchecked as usize);
    black_box(cold_never_inline(1));

    let f_u32 = generic_id::<u32> as fn(u32) -> u32 as usize;
    let f_i32 = generic_id::<i32> as fn(i32) -> i32 as usize;

    let v1: &dyn MyTrait = &10u64;
    let v2: &dyn MyTrait = &20u64;
    let vt1 = unsafe { core::mem::transmute::<&dyn MyTrait, [usize; 2]>(v1)[1] };
    let vt2 = unsafe { core::mem::transmute::<&dyn MyTrait, [usize; 2]>(v2)[1] };

    let c_ptr1 = &CONST_ARR as *const _ as usize;
    let c_ptr2 = &CONST_ARR as *const _ as usize;
    let s_ptr1 = "hello_literal".as_ptr() as usize;
    let s_ptr2 = "hello_literal".as_ptr() as usize;
    let st_a = &STATIC_A as *const _ as usize;
    let st_b = &STATIC_B as *const _ as usize;

    let const_powi = (2.5f64).powi(3).to_bits();
    let rt_powi = black_box(2.5f64).powi(black_box(3)).to_bits();
    let qnan_neg = f64::from_bits(0xfff8_0000_0000_0001);
    let nan_add_const = (f64::from_bits(0xfff8_0000_0000_0001) + 0.0).to_bits();
    let nan_add_rt = (black_box(qnan_neg) + black_box(0.0)).to_bits();

    let frame_delta = measure_frame_step(1, 0);

    let bt = std::backtrace::Backtrace::force_capture().to_string();
    let has_main_sym = bt.contains("main");

    println!(
        "{}",
        format!(
            "{{\"fn_u32_eq_i32\":{},\"vtable_eq\":{},\"const_addr_eq\":{},\"str_lit_eq\":{},\"static_ab_eq\":{},\"const_powi\":\"0x{:016x}\",\"rt_powi\":\"0x{:016x}\",\"nan_add_const\":\"0x{:016x}\",\"nan_add_rt\":\"0x{:016x}\",\"frame_delta_bytes\":{},\"bt_has_main\":{}}}",
            str_bool(f_u32 == f_i32),
            str_bool(vt1 == vt2),
            str_bool(c_ptr1 == c_ptr2),
            str_bool(s_ptr1 == s_ptr2),
            str_bool(st_a == st_b),
            const_powi,
            rt_powi,
            nan_add_const,
            nan_add_rt,
            frame_delta,
            str_bool(has_main_sym),
        )
    );
}

fn str_bool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}
'''

def run_probes():
    results = {}
    with tempfile.TemporaryDirectory(dir=TMP_DIR) as wd:
        wd_p = Path(wd)
        src = wd_p / "probe.rs"
        src.write_text(PROBE_RS)

        configs = [
            ("baseline_1991_opt0", ["rustc", "+1.99.1", "-Copt-level=0", "-Cdebuginfo=2"]),
            ("baseline_1991_opt3", ["rustc", "+1.99.1", "-Copt-level=3", "-Cdebuginfo=2"]),
            ("baseline_1991_opt3_mergefn", ["rustc", "+1.99.1", "-Copt-level=3", "-Zmerge-functions=aliases"]),
            ("llvm_opt0", ["rustc", "+nightly-2026-11-12", "-Zcodegen-backend=llvm", "-Copt-level=0", "-Cdebuginfo=2"]),
            ("llvm_opt3", ["rustc", "+nightly-2026-11-12", "-Zcodegen-backend=llvm", "-Copt-level=3", "-Cdebuginfo=2"]),
            ("clif_opt0", ["rustc", "+nightly-2026-11-12", "-Zcodegen-backend=cranelift", "-Copt-level=0", "-Cdebuginfo=2"]),
            ("clif_opt3", ["rustc", "+nightly-2026-11-12", "-Zcodegen-backend=cranelift", "-Copt-level=3", "-Cdebuginfo=2"]),
        ]

        for name, base_cmd in configs:
            bin_path = wd_p / f"probe_{name}"
            env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
            p_build = subprocess.run(base_cmd + ["-o", str(bin_path), str(src)], cwd=wd, env=env, capture_output=True, text=True)
            entry = {"build_rc": p_build.returncode, "build_stderr": p_build.stderr.strip()[:500]}
            if p_build.returncode == 0 and bin_path.exists():
                p_run = subprocess.run([str(bin_path)], cwd=wd, capture_output=True, text=True)
                try:
                    entry["runtime"] = json.loads(p_run.stdout.strip())
                except Exception:
                    entry["runtime_raw"] = p_run.stdout.strip()

                # Test termination signals
                signals = {}
                for mode in ["abort_intrinsic", "process_abort", "unreachable"]:
                    try:
                        p_sig = subprocess.run([str(bin_path), mode], cwd=wd, capture_output=True, timeout=3)
                        signals[mode] = p_sig.returncode
                    except subprocess.TimeoutExpired:
                        signals[mode] = "timeout"
                entry["termination_rc"] = signals

                # Disassemble key functions
                p_obj = subprocess.run(
                    ["objdump", "-d",
                     "--disassemble=probe_volatile_u64",
                     "--disassemble=probe_atomic_seqcst",
                     "--disassemble=probe_abort_intrinsic",
                     "--disassemble=probe_process_abort",
                     "--disassemble=probe_unreachable_unchecked",
                     "--disassemble=cold_never_inline",
                     str(bin_path)],
                    capture_output=True, text=True
                )
                entry["disasm"] = p_obj.stdout.strip()
                # Check custom_sec and used symbols
                p_nm = subprocess.run(["nm", "-n", str(bin_path)], capture_output=True, text=True)
                entry["symbols"] = [
                    l for l in p_nm.stdout.splitlines()
                    if any(k in l for k in ["SEC_ITEM", "KEEP_USED", "STATIC_A", "STATIC_B", "cold_never_inline"])
                ]
            results[name] = entry

        # Also probe i686 vs x86_64 vs aarch64 assembly on 1.99.1
        lib_src = wd_p / "arch_probe.rs"
        lib_src.write_text(
            '#![no_std]\n#![feature(intrinsics, rustc_attrs)]\n'
            'use core::sync::atomic::{AtomicU64, Ordering};\n'
            '#[rustc_intrinsic] pub fn abort() -> !;\n'
            '#[no_mangle] pub extern "C" fn id_f32(x: f32) -> f32 { x }\n'
            '#[no_mangle] pub extern "C" fn atomic_seqcst(a: &AtomicU64, v: u64) -> u64 { a.store(v, Ordering::SeqCst); a.load(Ordering::SeqCst) }\n'
            '#[no_mangle] pub extern "C" fn do_abort() -> ! { abort() }\n'
            '#[no_mangle] pub unsafe extern "C" fn do_unreach() -> ! { core::hint::unreachable_unchecked() }\n'
        )
        arch_asm = {}
        for tgt in ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
            asm_out = wd_p / f"arch_{tgt}.s"
            subprocess.run(
                ["rustc", "+1.99.1", "--crate-type=rlib", "-Copt-level=2", f"--target={tgt}", "--emit=asm", "-o", str(asm_out), str(lib_src)],
                env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, capture_output=True, text=True
            )
            if asm_out.exists():
                arch_asm[tgt] = asm_out.read_text()
        results["arch_asm"] = arch_asm

    return results

if __name__ == "__main__":
    res = run_probes()
    (OUT_DIR / "c3_extracted.json").write_text(json.dumps(res, indent=2))
    for k, v in res.items():
        if k != "arch_asm":
            print(k, "rc:", v["build_rc"], "runtime:", v.get("runtime"), "signals:", v.get("termination_rc"))
