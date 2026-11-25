#!/usr/bin/env python3
"""Revalidate target-specific repr(C) divergences: AIX f64, Win64 ZST, i686 Empty, and AArch64 bool/HVA."""
import os
import shutil
import subprocess
import sys
import tempfile

NO_CORE = r"""
#![feature(no_core, rustc_attrs, lang_items, auto_traits, repr_simd)]
#![no_core]
#![allow(unused, improper_ctypes_definitions, internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "drop_glue"] fn drop_glue<T: ?Sized>(_: *mut T) {}
impl Copy for u8 {} impl Copy for i32 {} impl Copy for u32 {} impl Copy for u64 {} impl Copy for f32 {} impl Copy for f64 {} impl Copy for bool {}
impl<T: Copy, const N: usize> Copy for [T; N] {}
"""


def main() -> int:
    tc = os.environ.get("RUSTC_TOOLCHAIN", "nightly")
    clang = shutil.which("clang-19") or shutil.which("clang")
    clangxx = shutil.which("clang++-19") or shutil.which("clang++")
    gcc = shutil.which("gcc")
    gxx = shutil.which("g++")

    with tempfile.TemporaryDirectory() as tmp:
        aix_src = NO_CORE + """
#[rustc_dump_layout(size, align)] #[repr(C)] pub struct Struct { a1: f64, a2: u8 }
#[rustc_dump_layout(size, align)] #[repr(C)] pub struct Floats { a: f64, b: u8, c: f64 }
#[rustc_dump_layout(size, align)] #[repr(C)] pub struct LaterF64 { b: u8, a: f64 }
"""
        pa = os.path.join(tmp, "aix.rs")
        with open(pa, "w") as f:
            f.write(aix_src)
        r = subprocess.run(["rustc", f"+{tc}", "--crate-type=lib", "--emit=metadata", "--target=powerpc64-ibm-aix", pa, "-o", os.path.join(tmp, "a.rmeta")], capture_output=True, text=True)
        print("=== AIX rustc layout ===")
        for l in r.stderr.splitlines():
            if "size:" in l or "align:" in l:
                print(" ", l.strip())

        zst_src = NO_CORE + """
pub struct RZero;
#[repr(C)] pub struct CZero {}
#[repr(C)] pub struct CArr0([i32; 0]);
#[repr(transparent)] pub struct WrapUnit(());
#[repr(transparent)] pub struct WrapCZero(CZero);
#[no_mangle] pub extern "C" fn ret_unit() {}
#[no_mangle] pub extern "C" fn ret_rust_zst() -> RZero { RZero }
#[no_mangle] pub extern "C" fn ret_c_empty() -> CZero { CZero {} }
#[no_mangle] pub extern "C" fn ret_c_arr0() -> CArr0 { CArr0([]) }
#[no_mangle] pub extern "C" fn arg_c_empty(_: CZero, x: i32) -> i32 { x }
#[no_mangle] pub extern "C" fn arg_wrap_czero(_: WrapCZero, x: i32) -> i32 { x }
"""
        pz = os.path.join(tmp, "zst.rs")
        with open(pz, "w") as f:
            f.write(zst_src)
        for tgt in ["x86_64-pc-windows-msvc", "i686-unknown-linux-gnu"]:
            ll = os.path.join(tmp, f"{tgt}.ll")
            subprocess.run(["rustc", f"+{tc}", "--crate-type=lib", "--emit=llvm-ir", f"--target={tgt}", pz, "-o", ll], check=True)
            print(f"\n=== rustc {tgt} ZST IR ===")
            for l in open(ll):
                if l.startswith("define "):
                    print(" ", l.strip())

        aarch_src = NO_CORE + """
#[repr(simd)] pub struct F64x2([f64; 2]);
impl Copy for F64x2 {}
#[repr(C)] pub struct HVA { pub a: F64x2, pub b: F64x2 }
#[no_mangle] pub extern "C" fn ret_bool(x: bool) -> bool { x }
#[no_mangle] pub extern "C" fn ret_hva(x: HVA) -> HVA { x }
"""
        paa = os.path.join(tmp, "aarch.rs")
        with open(paa, "w") as f:
            f.write(aarch_src)
        lla = os.path.join(tmp, "aarch.ll")
        subprocess.run(["rustc", f"+{tc}", "--crate-type=lib", "--emit=llvm-ir", "--target=aarch64-unknown-linux-gnu", paa, "-o", lla], check=True)
        print("\n=== rustc aarch64 bool & HVA IR ===")
        for l in open(lla):
            if l.startswith("define "):
                print(" ", l.strip())

        c_src = """
#include <stdint.h>
struct Struct { double a1; uint8_t a2; };
struct Floats { double a; uint8_t b; double c; };
struct LaterF64 { uint8_t b; double a; };
struct Empty {};
int sz_struct(void) { return sizeof(struct Struct); }
int al_struct(void) { return _Alignof(struct Struct); }
int sz_floats(void) { return sizeof(struct Floats); }
int sz_later(void) { return sizeof(struct LaterF64); }
int al_later(void) { return _Alignof(struct LaterF64); }
struct Empty ret_empty(void) { struct Empty e = {}; return e; }
int arg_empty(struct Empty e, int x) { return x; }
"""
        pc = os.path.join(tmp, "c_check.c")
        with open(pc, "w") as f:
            f.write(c_src)
        if clang:
            for tgt in ["powerpc64-ibm-aix", "i686-unknown-linux-gnu", "x86_64-pc-windows-msvc"]:
                ll = os.path.join(tmp, f"clang_{tgt}.ll")
                subprocess.run([clang, f"--target={tgt}", "-O1", "-S", "-emit-llvm", pc, "-o", ll], check=True)
                print(f"\n=== {clang} {tgt} ===")
                for l in open(ll):
                    if l.startswith("define ") or "ret i32 " in l:
                        print(" ", l.strip())
        if clangxx and gcc and gxx:
            cpp = os.path.join(tmp, "e.cpp")
            with open(cpp, "w") as f:
                f.write('struct Empty {};\nextern "C" Empty ret_empty() { return {}; }\nextern "C" int arg_empty(Empty e, int x) { return x; }\n')
            for label, cmd in [
                ("gcc -m32 C", [gcc, "-m32", "-O1", "-S", "-xc", cpp]),
                ("g++ -m32 C++", [gxx, "-m32", "-O1", "-S"]),
                ("clang++ -m32 C++", [clangxx, "--target=i686-unknown-linux-gnu", "-O1", "-S"]),
            ]:
                s = os.path.join(tmp, label.replace(" ", "_") + ".s")
                rc = subprocess.run([*cmd, cpp, "-o", s], capture_output=True, text=True)
                print(f"\n=== {label} (rc={rc.returncode}) ===")
                if rc.returncode == 0:
                    for l in open(s):
                        if any(k in l for k in ("arg_empty:", "ret_empty:", "esp", "ret")):
                            print(" ", l.strip())
    return 0


if __name__ == "__main__":
    sys.exit(main())
