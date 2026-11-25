#!/usr/bin/env python3
"""Revalidate wasm32 C ABI parity, i686 byval vs scalar IR, -Zregparm=3 u64 omission, and modifier flags."""
import os
import shutil
import subprocess
import sys
import tempfile

NO_CORE = r"""
#![feature(no_core, lang_items, auto_traits, rustc_attrs)]
#![no_core]
#![allow(unused, improper_ctypes_definitions, internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "drop_glue"] fn drop_glue<T: ?Sized>(_: *mut T) {}
impl Copy for u8 {} impl Copy for i32 {} impl Copy for u32 {} impl Copy for u64 {} impl Copy for f64 {}
impl<T: ?Sized> Copy for *const T {}
"""


def main() -> int:
    tc = os.environ.get("RUSTC_TOOLCHAIN", "nightly")
    clang = shutil.which("clang-19") or shutil.which("clang")

    with tempfile.TemporaryDirectory() as tmp:
        wasm_std = """
#![crate_type = "lib"]
#![no_std]
#![allow(unused, improper_ctypes_definitions)]
#[repr(C)] pub struct Empty {}
impl Copy for Empty {}
impl Clone for Empty { fn clone(&self) -> Self { *self } }
#[repr(C)] #[derive(Copy, Clone)] pub struct SingleU32(pub u32);
#[repr(C)] #[derive(Copy, Clone)] pub union SingleUnion { pub a: u32, pub b: u32 }
#[repr(C)] #[derive(Copy, Clone)] pub union SingleUnionMixed { pub a: u32, pub b: *const u8 }
#[repr(C)] #[derive(Copy, Clone)] pub union SingleUnionWithEmpty { pub e: Empty, pub a: u32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct WithEmpty { pub e: Empty, pub a: u32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct Pair(pub u32, pub u32);
#[repr(u8)] pub enum EnumZstField { A(()), B }
#[no_mangle] pub extern "C" fn ret_single_struct(x: SingleU32) -> SingleU32 { x }
#[no_mangle] pub extern "C" fn ret_single_union(x: SingleUnion) -> SingleUnion { x }
#[no_mangle] pub extern "C" fn ret_single_union_mixed(x: SingleUnionMixed) -> SingleUnionMixed { x }
#[no_mangle] pub extern "C" fn ret_union_empty(x: SingleUnionWithEmpty) -> SingleUnionWithEmpty { x }
#[no_mangle] pub extern "C" fn ret_with_empty(x: WithEmpty) -> WithEmpty { x }
#[no_mangle] pub extern "C" fn ret_pair(x: Pair) -> Pair { x }
#[no_mangle] pub extern "C" fn ret_enum_zst(x: EnumZstField) -> EnumZstField { x }
"""
        pw = os.path.join(tmp, "w.rs")
        with open(pw, "w") as f:
            f.write(wasm_std)
        llw = os.path.join(tmp, "w.ll")
        subprocess.run(["rustc", f"+{tc}", "-Copt-level=1", "--emit=llvm-ir", "--target=wasm32-unknown-unknown", pw, "-o", llw], check=True)
        print("=== rustc wasm32-unknown-unknown IR ===")
        for l in open(llw):
            if l.startswith("define "):
                print(" ", l.strip())
        rl = subprocess.run(["rustc", f"+{tc}", "-Z", "wasm-c-abi=legacy", "--crate-type=lib", "--emit=metadata", "--target=wasm32-unknown-unknown", pw, "-o", os.path.join(tmp, "w.rmeta")], capture_output=True, text=True)
        print(f"wasm-c-abi=legacy check rc={rl.returncode}: {rl.stderr.strip().splitlines()[0]}")

        i686_src = NO_CORE + """
#[repr(C)] pub struct TwoI32(pub i32, pub i32);
#[repr(C)] pub struct ThreeI32(pub i32, pub i32, pub i32);
#[no_mangle] pub extern "C" fn take_two(x: TwoI32) -> i32 { x.0 }
#[no_mangle] pub extern "C" fn take_three(x: ThreeI32) -> i32 { x.0 }
#[no_mangle] pub extern "C" fn take_u64_u32(a: u64, b: u32) -> u32 { b }
"""
        pi = os.path.join(tmp, "i686.rs")
        with open(pi, "w") as f:
            f.write(i686_src)
        for label, extra in [("default", []), ("regparm3", ["-Z", "regparm=3"])]:
            ll = os.path.join(tmp, f"i_{label}.ll")
            s = os.path.join(tmp, f"i_{label}.s")
            subprocess.run(["rustc", f"+{tc}", *extra, "-Copt-level=1", "--crate-type=lib", "--emit=llvm-ir", "--target=i686-unknown-linux-gnu", pi, "-o", ll], check=True)
            subprocess.run(["rustc", f"+{tc}", *extra, "-Copt-level=1", "--crate-type=lib", "--emit=asm", "--target=i686-unknown-linux-gnu", pi, "-o", s], check=True)
            print(f"\n=== rustc i686 {label} ===")
            for l in open(ll):
                if l.startswith("define "):
                    print(" ", l.strip())
            asm = open(s).read()
            idx = asm.find("take_u64_u32:")
            if idx != -1:
                print("  ASM:", " | ".join(asm[idx:idx + 160].splitlines()[:4]))

        if clang:
            cw = """
typedef struct {} Empty;
typedef struct { unsigned a; } SingleU32;
typedef union { unsigned a; unsigned b; } SingleUnion;
typedef union { unsigned a; const unsigned char *b; } SingleUnionMixed;
typedef union { Empty e; unsigned a; } SingleUnionWithEmpty;
typedef struct { Empty e; unsigned a; } WithEmpty;
typedef struct { unsigned a; unsigned b; } Pair;
SingleU32 ret_single_struct(SingleU32 x) { return x; }
SingleUnion ret_single_union(SingleUnion x) { return x; }
SingleUnionMixed ret_single_union_mixed(SingleUnionMixed x) { return x; }
SingleUnionWithEmpty ret_union_empty(SingleUnionWithEmpty x) { return x; }
WithEmpty ret_with_empty(WithEmpty x) { return x; }
Pair ret_pair(Pair x) { return x; }
"""
            pcw = os.path.join(tmp, "cw.c")
            with open(pcw, "w") as f:
                f.write(cw)
            llcw = os.path.join(tmp, "cw.ll")
            subprocess.run([clang, "--target=wasm32-unknown-unknown", "-O1", "-S", "-emit-llvm", pcw, "-o", llcw], check=True)
            print(f"\n=== {clang} wasm32 IR ===")
            for l in open(llcw):
                if l.startswith("define "):
                    print(" ", l.strip())

            ci = """
typedef struct { int a, b; } TwoI32;
typedef struct { int a, b, c; } ThreeI32;
int take_two(TwoI32 x) { return x.a; }
int take_three(ThreeI32 x) { return x.a; }
unsigned take_u64_u32(unsigned long long a, unsigned b) { return b; }
"""
            pci = os.path.join(tmp, "ci.c")
            with open(pci, "w") as f:
                f.write(ci)
            for label, extra in [("default", []), ("mregparm3", ["-mregparm=3"])]:
                ll = os.path.join(tmp, f"ci_{label}.ll")
                s = os.path.join(tmp, f"ci_{label}.s")
                subprocess.run([clang, "--target=i686-unknown-linux-gnu", *extra, "-O1", "-S", "-emit-llvm", pci, "-o", ll], check=True)
                subprocess.run([clang, "--target=i686-unknown-linux-gnu", *extra, "-O1", "-S", pci, "-o", s], check=True)
                print(f"\n=== {clang} i686 {label} ===")
                for l in open(ll):
                    if l.startswith("define "):
                        print(" ", l.strip())
                asm = open(s).read()
                idx = asm.find("take_u64_u32:")
                if idx != -1:
                    print("  ASM:", " | ".join(asm[idx:idx + 160].splitlines()[:5]))

        mod_src = NO_CORE + """
#[repr(C)] pub struct WrapC(pub u32);
#[repr(transparent)] pub struct WrapT(pub u32);
#[no_mangle] pub fn f64_rust(x: f64) -> f64 { x }
#[no_mangle] pub extern "C" fn fp_c(x: f64) -> f64 { x }
#[no_mangle] pub extern "C" fn u32_fn(x: u32) -> u32 { x }
#[no_mangle] pub extern "C" fn wrap_c_fn(x: WrapC) -> WrapC { x }
#[no_mangle] pub extern "C" fn wrap_t_fn(x: WrapT) -> WrapT { x }
"""
        pmod = os.path.join(tmp, "mod.rs")
        with open(pmod, "w") as f:
            f.write(mod_src)
        rsse = subprocess.run(
            ["rustc", f"+{tc}", "--crate-type=lib", "--emit=metadata", "--target=i686-unknown-linux-gnu", "-Ctarget-feature=-sse,-sse2", pmod, "-o", os.path.join(tmp, "nosse.rmeta")],
            capture_output=True, text=True,
        )
        print(f"\n=== rustc i686 -sse,-sse2 rc={rsse.returncode}: {rsse.stderr.strip().splitlines()[0] if rsse.stderr.strip() else ''} ===")
        for label, tgt, flags in [
            ("i686-sse2", "i686-unknown-linux-gnu", []),
            ("x86_64-kcfi", "x86_64-unknown-linux-gnu", ["-Cpanic=abort", "-Z", "sanitizer=kcfi"]),
            ("aarch64-pauth", "aarch64-unknown-linux-gnu", ["-Z", "branch-protection=pac-ret"]),
        ]:
            ll = os.path.join(tmp, f"{label}.ll")
            subprocess.run(["rustc", f"+{tc}", *flags, "-Copt-level=1", "--crate-type=lib", "--emit=llvm-ir", f"--target={tgt}", pmod, "-o", ll], check=True)
            print(f"\n=== rustc {label} IR ===")
            for l in open(ll):
                if l.startswith("define ") or "sign-return-address" in l or ("= !{i32 -" in l) or ("= !{i32 " in l and label == "x86_64-kcfi"):
                    print(" ", l.strip())
    return 0


if __name__ == "__main__":
    sys.exit(main())
