#!/usr/bin/env python3
import json, os, re, shutil, subprocess
from pathlib import Path

SYSROOT = Path("/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu")
BIN_DIR = SYSROOT / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
LLVM_AR = str(BIN_DIR / "llvm-ar")
LLVM_READOBJ = str(BIN_DIR / "llvm-readobj")
LLVM_OBJDUMP = str(BIN_DIR / "llvm-objdump")
RUSTC = "rustc"
OUT_DIR = Path(".")

TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

PROBE_RS = r"""
#![feature(thread_local, used_with_arg, linkage, rustc_attrs)]
#![allow(dead_code, non_upper_case_globals, internal_features)]

use std::sync::atomic::{AtomicUsize, Ordering};

#[used(compiler)]
static USED_COMPILER_ITEM: u64 = 0x1122_3344_5566_7788;

#[used(linker)]
static USED_LINKER_ITEM: u64 = 0x8877_6655_4433_2211;

#[cfg_attr(target_os = "linux", link_section = ".init_array")]
#[cfg_attr(target_os = "macos", link_section = "__DATA,__mod_init_func,mod_init_funcs")]
#[cfg_attr(target_os = "windows", link_section = ".CRT$XCU")]
#[used(linker)]
pub static CTOR_ENTRY: unsafe extern "C" fn() = my_init_ctor;

pub unsafe extern "C" fn my_init_ctor() {}

// Distributed slice simulation
#[cfg_attr(target_os = "linux", link_section = "linkme_ITEMS")]
#[cfg_attr(target_os = "macos", link_section = "__DATA,__linkme_items,regular,no_dead_strip")]
#[cfg_attr(target_os = "windows", link_section = ".linkme$b")]
#[used(linker)]
pub static SLICE_ELEM: u64 = 42;

#[cfg(target_os = "macos")]
#[link_section = "__DATA,__objc_classlist,regular,no_dead_strip"]
#[used(linker)]
pub static OBJC_CLASS_ENTRY: u64 = 0xABCD;

#[cfg(target_os = "macos")]
extern "C" {
    #[rustc_objc_class = "NSObject"]
    static NS_OBJECT_CLASS: *const u8;
    #[rustc_objc_selector = "init"]
    static INIT_SEL: *const u8;
}

#[thread_local]
pub static mut TLS_COUNTER: u64 = 12345;

#[thread_local]
pub static mut TLS_ZERO: u64 = 0;

pub static GLOBAL_ATOMIC: AtomicUsize = AtomicUsize::new(7);

pub trait Op {
    fn run(&self, x: usize) -> usize;
}

pub struct Adder(pub usize);
impl Op for Adder {
    #[inline(never)]
    fn run(&self, x: usize) -> usize {
        x.wrapping_add(self.0)
    }
}

#[inline(never)]
pub fn generic_comdat<T: Copy>(x: T) -> T {
    std::hint::black_box(x)
}

#[no_mangle]
pub extern "C" fn probe_entry(op: &dyn Op, v: usize) -> usize {
    let a = GLOBAL_ATOMIC.fetch_add(v, Ordering::SeqCst);
    let t = unsafe {
        TLS_COUNTER = TLS_COUNTER.wrapping_add(1);
        TLS_ZERO = TLS_ZERO.wrapping_add(2);
        TLS_COUNTER ^ TLS_ZERO
    };
    #[cfg(target_os = "macos")]
    let objc_bits = unsafe { (NS_OBJECT_CLASS as usize) ^ (INIT_SEL as usize) };
    #[cfg(not(target_os = "macos"))]
    let objc_bits = 0usize;
    let g = generic_comdat(v);
    op.run(a ^ (t as usize) ^ g ^ objc_bits)
}
"""

def run_probe():
    work = OUT_DIR / "tmp" / "t8_work"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    src = work / "probe.rs"
    src.write_text(PROBE_RS)

    results = {}
    for t in TARGETS:
        t_dir = work / t
        t_dir.mkdir()
        obj_path = t_dir / "probe.o"
        cmd = [
            RUSTC, "+1.99.1", "--target", t, "--crate-type=rlib",
            "--emit=obj,link,asm", "-C", "opt-level=2", "-C", "debuginfo=2",
            "-C", "embed-bitcode=yes", "-C", "codegen-units=1",
            str(src), "--out-dir", str(t_dir)
        ]
        env = os.environ.copy()
        env["RUSTC_BOOTSTRAP"] = "1"
        subprocess.run(cmd, env=env, check=True)

        # Also compile security-note variants
        extra_objs = {}
        if t in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
            cet_obj = t_dir / "probe_cet.o"
            subprocess.run([
                RUSTC, "+1.99.1", "--target", t, "--crate-type=lib",
                "--emit=obj", "-Z", "cf-protection=full", str(src), "-o", str(cet_obj)
            ], env=env, check=True)
            extra_objs["cet"] = cet_obj
        elif t == "aarch64-unknown-linux-gnu":
            bti_obj = t_dir / "probe_bti_pac.o"
            subprocess.run([
                RUSTC, "+1.99.1", "--target", t, "--crate-type=lib",
                "--emit=obj", "-Z", "branch-protection=bti,pac-ret,leaf", "-C", "unsafe-allow-abi-mismatch=branch-protection", str(src), "-o", str(bti_obj)
            ], env=env, check=True)
            extra_objs["bti_pac"] = bti_obj
        elif "windows-msvc" in t:
            cfg_obj = t_dir / "probe_cfg.o"
            cmd_cfg = [
                RUSTC, "+1.99.1", "--target", t, "--crate-type=lib",
                "--emit=obj", "-C", "control-flow-guard=checks", str(src), "-o", str(cfg_obj)
            ]
            if t == "x86_64-pc-windows-msvc":
                cmd_cfg.extend(["-Z", "ehcont-guard"])
            subprocess.run(cmd_cfg, env=env, check=True)
            extra_objs["cfguard"] = cfg_obj

        rlib_members = subprocess.check_output([LLVM_AR, "t", str(t_dir / "libprobe.rlib")], text=True).splitlines()
        extract_dir = t_dir / "rlib_extracted"
        extract_dir.mkdir()
        subprocess.run([LLVM_AR, "x", str(t_dir / "libprobe.rlib")], cwd=str(extract_dir), check=True)

        ro_out = subprocess.check_output([
            LLVM_READOBJ, "--file-headers", "--sections", "--symbols", "--relocations",
            "--elf-section-groups", "--coff-directives", "--addrsig", "--notes", str(obj_path)
        ], text=True, errors="replace")

        rmeta_out = ""
        if (extract_dir / "lib.rmeta").exists():
            rmeta_out = subprocess.check_output([
                LLVM_READOBJ, "--file-headers", "--sections", "--symbols", "--notes", str(extract_dir / "lib.rmeta")
            ], text=True, errors="replace")

        extra_notes = {}
        for k, p in extra_objs.items():
            extra_notes[k] = subprocess.check_output([
                LLVM_READOBJ, "--sections", "--symbols", "--notes", "--coff-directives", str(p)
            ], text=True, errors="replace")

        asm_txt = (t_dir / "probe.s").read_text(errors="replace")

        results[t] = {
            "rlib_members": rlib_members,
            "probe_readobj": ro_out,
            "rmeta_readobj": rmeta_out,
            "extra_readobj": extra_notes,
            "asm_lines": len(asm_txt.splitlines()),
            "asm_tail": "\n".join(asm_txt.splitlines()[-80:]),
        }

    (OUT_DIR / "t8_probe_raw.json").write_text(json.dumps(results, indent=2))
    print("Saved t8_probe_raw.json successfully!")

if __name__ == "__main__":
    run_probe()
