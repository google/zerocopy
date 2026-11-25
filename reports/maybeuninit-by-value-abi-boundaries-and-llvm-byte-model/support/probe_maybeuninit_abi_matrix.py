#!/usr/bin/env python3
"""Revalidate T vs MaybeUninit<T> ABI compatibility across 8 targets, MSan TLS asm, and Miri padding UB."""
import os
import subprocess
import sys
import tempfile

CORE = r"""
#![feature(no_core, rustc_attrs, lang_items, f16, f128, transparent_unions, auto_traits)]
#![no_core]
#![allow(unused, improper_ctypes_definitions, internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "drop_glue"] fn drop_glue<T: ?Sized>(_: *mut T) {}
#[lang = "bikeshed_guaranteed_no_drop"] pub trait BikeshedGuaranteedNoDrop {}
#[lang = "manually_drop"] #[repr(transparent)] pub struct ManuallyDrop<T: ?Sized> { value: T }
impl<T: ?Sized + Copy> Copy for ManuallyDrop<T> {}
#[lang = "maybe_uninit"] #[repr(transparent)] pub union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }
impl Copy for bool {} impl Copy for u8 {} impl Copy for u16 {} impl Copy for u32 {} impl Copy for i32 {}
impl Copy for f32 {} impl Copy for f64 {}
impl<T: ?Sized> Copy for *const T {}
#[repr(u8)] pub enum E2U8 { A = 0, B = 1 } impl Copy for E2U8 {}
#[repr(u8)] pub enum E3U8 { A = 0, B = 1, C = 2 } impl Copy for E3U8 {}
#[repr(C)] pub enum E2C { A = 0, B = 1 } impl Copy for E2C {}
pub enum OptU8 { None, Some(u8) } impl Copy for OptU8 {}
pub enum E2Rust { A, B } impl Copy for E2Rust {}
pub enum OptBool { None, Some(bool) } impl Copy for OptBool {}
pub enum OptF32 { None, Some(f32) } impl Copy for OptF32 {}
#[repr(transparent)] pub struct BoolWrap(bool); impl Copy for BoolWrap {}
#[repr(C)] pub struct F32x2(pub f32, pub f32); impl Copy for F32x2 {}
#[repr(C)] pub struct F64x3(pub f64, pub f64, pub f64); impl Copy for F64x3 {}
#[repr(C)] pub struct Padded(pub u16, pub u8); impl Copy for Padded {}
"""

CASES = [
    ("c_i32", "i32"), ("c_u8", "u8"), ("c_ptr", "*const ()"), ("c_f64", "f64"),
    ("c_bool", "bool"), ("c_bool_wrap", "BoolWrap"), ("c_e2_rust", "E2Rust"),
    ("c_e2_u8", "E2U8"), ("c_e3_u8", "E3U8"), ("c_e2_c", "E2C"),
    ("c_opt_u8", "OptU8"), ("c_opt_bool", "OptBool"), ("c_pair_bool_u8", "(bool, u8)"),
    ("c_opt_f32", "OptF32"), ("c_f32x2", "F32x2"), ("c_f64x3", "F64x3"),
    ("c_padded_c", "Padded"), ("c_padded_rust", "(u16, u8)"),
]
TARGETS = [
    "x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc", "aarch64-unknown-linux-gnu",
    "thumbv8m.main-none-eabi", "m68k-unknown-linux-gnu", "mips64-unknown-linux-gnuabi64",
    "bpfeb-unknown-none", "wasm32-unknown-unknown",
]


def main() -> int:
    tc = os.environ.get("RUSTC_TOOLCHAIN", "nightly")
    with tempfile.TemporaryDirectory() as tmp:
        print(f"Toolchain: rustc +{tc}")
        for abi_kind, sig in [("Rust", "fn({}) -> {}"), ("C", 'extern "C" fn({}) -> {}')]:
            print(f"\n=== ABI: {abi_kind} ===")
            for tgt in TARGETS:
                fails = []
                for name, ty in CASES:
                    s1 = sig.format(ty, ty)
                    s2 = sig.format(f"MaybeUninit<{ty}>", f"MaybeUninit<{ty}>")
                    p = os.path.join(tmp, f"{name}.rs")
                    with open(p, "w") as f:
                        f.write(CORE + f"#[rustc_abi(assert_eq)] type T = ({s1}, {s2});\n")
                    r = subprocess.run(
                        ["rustc", f"+{tc}", "--crate-name=t", "--crate-type=lib", "--emit=metadata", f"--target={tgt}", p, "-o", os.path.join(tmp, "o.rmeta")],
                        capture_output=True, text=True,
                    )
                    if r.returncode != 0:
                        fails.append(name)
                print(f"{tgt}: fail({len(fails)})={fails}")

        msan_src = CORE + """
#[no_mangle] pub extern "C" fn take_i32(x: i32) -> i32 { x }
#[no_mangle] pub extern "C" fn take_mu_i32(x: MaybeUninit<i32>) -> MaybeUninit<i32> { x }
"""
        pm = os.path.join(tmp, "msan.rs")
        with open(pm, "w") as f:
            f.write(msan_src)
        sm = os.path.join(tmp, "msan.s")
        rm = subprocess.run(
            ["rustc", f"+{tc}", "-Copt-level=1", "-Zsanitizer=memory", "--crate-type=lib", "--emit=asm", pm, "-o", sm],
            capture_output=True, text=True,
        )
        print(f"\n=== MSan ASM rc={rm.returncode} ===")
        if rm.returncode == 0:
            asm = open(sm).read()
            for fn in ["take_i32:", "take_mu_i32:"]:
                idx = asm.find(fn)
                if idx != -1:
                    print("\n".join(asm[idx:idx + 280].splitlines()[:8]))

        pad_src = """
use std::mem::MaybeUninit;
#[inline(never)]
unsafe fn id(x: MaybeUninit<{TY}>) -> MaybeUninit<{TY}> { x }
fn main() {
    let mut x = MaybeUninit::<{TY}>::uninit();
    unsafe {
        x.as_mut_ptr().cast::<u32>().write_unaligned(0xaabbccdd);
        let y = id(x);
        let v: u32 = std::mem::transmute(y);
        println!("0x{v:08x}");
    }
}
"""
        pp = os.path.join(tmp, "pad.rs")
        with open(pp, "w") as f:
            f.write(pad_src.replace("{TY}", "(u16, u8)"))
        bp = os.path.join(tmp, "pad_bin")
        subprocess.run(["rustc", f"+{tc}", "-O", pp, "-o", bp], check=True)
        rp = subprocess.run([bp], capture_output=True, text=True, check=True)
        print("\n=== Padding Test ===")
        print("Compiled rustc -O:", rp.stdout.strip())
        for label, ty in [("padded_(u16,u8)", "(u16, u8)"), ("unpadded_(u16,u16)", "(u16, u16)")]:
            cdir = os.path.join(tmp, f"miri_{label}")
            os.makedirs(os.path.join(cdir, "src"))
            with open(os.path.join(cdir, "Cargo.toml"), "w") as f:
                f.write('[package]\nname = "miri_pad"\nversion = "0.1.0"\nedition = "2021"\n')
            with open(os.path.join(cdir, "src", "main.rs"), "w") as f:
                f.write(pad_src.replace("{TY}", ty))
            rmiri = subprocess.run(["cargo", f"+{tc}", "miri", "run"], cwd=cdir, capture_output=True, text=True)
            print(f"Miri {label}: rc={rmiri.returncode} out={rmiri.stdout.strip()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
