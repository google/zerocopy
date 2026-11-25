#!/usr/bin/env python3
"""Revalidate C++ dsize/POD tail-padding reuse, bitfield units, non-trivial-for-calls, and SVE vscale IR."""
import os
import shutil
import subprocess
import sys
import tempfile

CPP_SRC = r"""
#include <cstddef>
#include <cstdio>

struct Empty {};
struct BaseWithTailPad { int a; char b; };
struct DerivedNonPod : BaseWithTailPad {
    virtual ~DerivedNonPod() {}
    char c;
};
struct PodSubobj { int a; char b; };
struct NonPodSubobj { int a; char b; ~NonPodSubobj() {} };
struct DerivedFromNonPod : NonPodSubobj { char c; };
struct ComposedPodNoUniq { [[no_unique_address]] PodSubobj p; char c; };
struct ComposedNonPodNoUniq { [[no_unique_address]] NonPodSubobj p; char c; };
struct WithEmptyNoAttr { int a; Empty e; int b; };
struct WithEmptyNoUniq { int a; [[no_unique_address]] Empty e; int b; };

struct BfContig { unsigned a : 8; unsigned b : 8; };
struct BfSplit { unsigned a : 17; unsigned b : 16; };
struct BfZeroBreak { unsigned a : 8; unsigned : 0; unsigned b : 8; };
struct BfBool { bool a : 1; bool b : 1; };

struct NonTrivialCopy {
    long x;
    NonTrivialCopy(long v) : x(v) {}
    NonTrivialCopy(const NonTrivialCopy& o) : x(o.x) {}
    NonTrivialCopy(NonTrivialCopy&&) = default;
    ~NonTrivialCopy() = default;
};
extern "C" long pass_ntc(NonTrivialCopy v) { return v.x + 1; }

struct Base1 { int x; virtual void f() {} };
struct Base2 { int y; virtual void g() {} };
struct Multi : Base1, Base2 { int z; };

int main() {
    std::printf("Empty sizeof=%zu alignof=%zu\n", sizeof(Empty), alignof(Empty));
    std::printf("DerivedNonPod sizeof=%zu c_off=%zu\n", sizeof(DerivedNonPod), offsetof(DerivedNonPod, c));
    std::printf("DerivedFromNonPod sizeof=%zu c_off=%zu\n", sizeof(DerivedFromNonPod), offsetof(DerivedFromNonPod, c));
    std::printf("ComposedPodNoUniq sizeof=%zu c_off=%zu\n", sizeof(ComposedPodNoUniq), offsetof(ComposedPodNoUniq, c));
    std::printf("ComposedNonPodNoUniq sizeof=%zu c_off=%zu\n", sizeof(ComposedNonPodNoUniq), offsetof(ComposedNonPodNoUniq, c));
    std::printf("WithEmptyNoAttr sizeof=%zu b_off=%zu\n", sizeof(WithEmptyNoAttr), offsetof(WithEmptyNoAttr, b));
    std::printf("WithEmptyNoUniq sizeof=%zu b_off=%zu\n", sizeof(WithEmptyNoUniq), offsetof(WithEmptyNoUniq, b));
    std::printf("BfContig sizeof=%zu BfSplit sizeof=%zu BfZeroBreak sizeof=%zu BfBool sizeof=%zu\n",
                sizeof(BfContig), sizeof(BfSplit), sizeof(BfZeroBreak), sizeof(BfBool));
    std::printf("Multi sizeof=%zu Base2_ptr_off=%zu\n", sizeof(Multi),
                (size_t)(reinterpret_cast<char*>(static_cast<Base2*>(reinterpret_cast<Multi*>(0x1000))) - reinterpret_cast<char*>(0x1000)));
    return 0;
}
"""

SVE_SRC = r"""
#![crate_type = "lib"]
#![feature(no_core, rustc_attrs, lang_items, auto_traits)]
#![no_core]
#![allow(internal_features, unused)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "drop_glue"] fn drop_glue<T: ?Sized>(_: *mut T) {}
impl Copy for i32 {}
#[rustc_scalable_vector(4)]
pub struct SvI32(i32);
#[no_mangle] pub fn id_sv(x: SvI32) -> SvI32 { x }
"""


def main() -> int:
    tc = os.environ.get("RUSTC_TOOLCHAIN", "nightly")
    with tempfile.TemporaryDirectory() as tmp:
        pcpp = os.path.join(tmp, "geom.cpp")
        with open(pcpp, "w") as f:
            f.write(CPP_SRC)
        for cxx in ["g++", "clang++-19", "clang++"]:
            b = shutil.which(cxx)
            if not b:
                continue
            exe = os.path.join(tmp, f"geom_{os.path.basename(b)}")
            subprocess.run([b, "-std=c++23", "-O1", pcpp, "-o", exe], check=True)
            out = subprocess.run([exe], capture_output=True, text=True, check=True)
            print(f"=== {b} -std=c++23 ===")
            print(out.stdout.strip())
            if "clang" in b:
                ll = os.path.join(tmp, "geom_clang.ll")
                subprocess.run([b, "-std=c++23", "-O1", "-S", "-emit-llvm", pcpp, "-o", ll], check=True)
                for l in open(ll):
                    if "pass_ntc" in l and l.startswith("define "):
                        print("  IR:", l.strip())

        psve = os.path.join(tmp, "sve.rs")
        with open(psve, "w") as f:
            f.write(SVE_SRC)
        ll_sve = os.path.join(tmp, "sve.ll")
        subprocess.run(["rustc", f"+{tc}", "-Copt-level=1", "--target=aarch64-unknown-linux-gnu", "-Ctarget-feature=+sve", "--emit=llvm-ir", psve, "-o", ll_sve], check=True)
        print("\n=== rustc aarch64 +sve IR ===")
        for l in open(ll_sve):
            if l.startswith("define "):
                print(" ", l.strip())
    return 0


if __name__ == "__main__":
    sys.exit(main())
