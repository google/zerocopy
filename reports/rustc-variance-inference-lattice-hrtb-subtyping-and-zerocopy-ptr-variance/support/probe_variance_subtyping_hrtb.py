#!/usr/bin/env python3
"""Live rustc probe for variance inference, HRTB subtyping, and zerocopy Ptr variance."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path


def sanitize_output(text: str, tmpdir: str, extra_paths: list[str] | None = None) -> str:
    text = text.replace(tmpdir, "<tmp>")
    for p in extra_paths or []:
        if p:
            text = text.replace(p, "<external>")
    return text.strip()


def run_rustc_probe(
    name: str,
    code: str,
    *,
    edition: str = "2024",
    extra_args: list[str] | None = None,
    run_binary: bool = False,
    crate_type: str | None = None,
    sanitize_paths: list[str] | None = None,
) -> dict:
    extra_args = list(extra_args or [])
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        src_path = tmp_path / "probe.rs"
        bin_path = tmp_path / "probe_bin"
        src_path.write_text(code, encoding="utf-8")

        cmd = ["rustc", f"--edition={edition}"]
        if crate_type is not None:
            cmd.append(f"--crate-type={crate_type}")
        cmd.extend(extra_args)
        cmd.extend([str(src_path), "-o", str(bin_path)])

        proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
        res: dict = {
            "name": name,
            "edition": edition,
            "extra_args": [
                sanitize_output(a, tmpdir, sanitize_paths) for a in extra_args
            ],
            "compile_returncode": proc.returncode,
            "compile_stdout": sanitize_output(proc.stdout, tmpdir, sanitize_paths),
            "compile_stderr": sanitize_output(proc.stderr, tmpdir, sanitize_paths),
        }
        if run_binary and proc.returncode == 0 and bin_path.exists():
            run_proc = subprocess.run([str(bin_path)], capture_output=True, text=True, check=False)
            res["run_returncode"] = run_proc.returncode
            res["run_stdout"] = sanitize_output(run_proc.stdout, tmpdir, sanitize_paths)
            res["run_stderr"] = sanitize_output(run_proc.stderr, tmpdir, sanitize_paths)
        return res


def run_zerocopy_crate_probes(zerocopy_lib: Path) -> dict:
    """Compile real zerocopy crate in a TemporaryDirectory and test Ptr<'a, T, I> variance."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        rlib_path = tmp_path / "libzerocopy.rlib"
        build_cmd = [
            "rustc",
            "--edition=2021",
            "--crate-name=zerocopy",
            "--crate-type=lib",
            "--cfg",
            "no_zerocopy_allocator_api_1_100_0",
            str(zerocopy_lib),
            "-o",
            str(rlib_path),
        ]
        zc_root = str(zerocopy_lib.parent.parent)
        env = dict(os.environ)
        env["CARGO_PKG_VERSION"] = "0.8.64"
        build_proc = subprocess.run(build_cmd, capture_output=True, text=True, env=env, check=False)
        if build_proc.returncode != 0:
            return {
                "crate_build_returncode": build_proc.returncode,
                "crate_build_stderr": sanitize_output(build_proc.stderr, tmpdir, [zc_root]),
            }

        extern_args = ["--extern", f"zerocopy={rlib_path}"]
        pos_code = """\
use zerocopy::pointer::{
    invariant::{Aligned, Exclusive, Safe, Shared},
    Ptr,
};

pub fn shorten_ptr_lt<'big: 'small, 'small>(
    p: Ptr<'big, u8, (Shared, Aligned, Safe)>,
) -> Ptr<'small, u8, (Shared, Aligned, Safe)> {
    p
}

pub fn shorten_exclusive_ptr_lt<'big: 'small, 'small>(
    p: Ptr<'big, u8, (Exclusive, Aligned, Safe)>,
) -> Ptr<'small, u8, (Exclusive, Aligned, Safe)> {
    p
}

fn main() {
    let x: u8 = 91;
    let p = Ptr::from_ref(&x);
    let q = shorten_ptr_lt::<'_, '_>(p);
    let mut y: u8 = 7;
    let pe = Ptr::from_mut(&mut y);
    let qe = shorten_exclusive_ptr_lt::<'_, '_>(pe);
    println!("REAL_ZC_SHARED={} REAL_ZC_EXCL={}", *q.as_ref(), *qe.as_ref());
}
"""
        neg_code = """\
use zerocopy::pointer::{
    invariant::{Aligned, Exclusive, Safe, Shared},
    Ptr,
};

pub fn _when_exclusive<'big: 'small, 'small>(
    big: Ptr<'small, &'big u32, (Exclusive, Aligned, Safe)>,
    mut _small: Ptr<'small, &'small u32, (Exclusive, Aligned, Safe)>,
) {
    _small = big;
}

pub fn _when_shared<'big: 'small, 'small>(
    big: Ptr<'small, &'big u32, (Shared, Aligned, Safe)>,
    mut _small: Ptr<'small, &'small u32, (Shared, Aligned, Safe)>,
) {
    _small = big;
}

fn main() {}
"""
        pos_res = run_rustc_probe(
            "real_zerocopy_lifetime_covariant_ok",
            pos_code,
            edition="2021",
            extra_args=extern_args,
            run_binary=True,
            sanitize_paths=[zc_root, tmpdir],
        )
        neg_res = run_rustc_probe(
            "real_zerocopy_referent_invariant_rejected",
            neg_code,
            edition="2021",
            extra_args=extern_args,
            run_binary=False,
            sanitize_paths=[zc_root, tmpdir],
        )
        return {
            "crate_build_returncode": build_proc.returncode,
            "crate_build_stderr": sanitize_output(build_proc.stderr, tmpdir, [zc_root]),
            "real_zerocopy_lifetime_covariant_ok": pos_res,
            "real_zerocopy_referent_invariant_rejected": neg_res,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Path to write JSON probe results.",
    )
    parser.add_argument(
        "--zerocopy-lib",
        type=Path,
        default=None,
        help="Optional path to real zerocopy/src/lib.rs to compile and probe directly.",
    )
    args = parser.parse_args()

    rustc_ver = subprocess.run(
        ["rustc", "--version", "--verbose"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()

    # Group A: Variance dump & subtyping matrix
    dump_code = """\
#![feature(rustc_attrs)]
use core::cell::UnsafeCell;
use core::marker::PhantomData;

#[rustc_dump_variances]
pub struct CovPtr<T>(*const T);

#[rustc_dump_variances]
pub struct InvPtr<T>(*mut T);

#[rustc_dump_variances]
pub struct FnVar<T, U>(PhantomData<fn(T) -> U>);

#[rustc_dump_variances]
pub struct FnInv<T>(PhantomData<fn(T) -> T>);

#[rustc_dump_variances]
pub struct CellWrap<T>(UnsafeCell<T>);

#[rustc_dump_variances]
pub struct SharedRef<'a, T>(&'a T);

#[rustc_dump_variances]
pub struct MutRef<'a, T>(&'a mut T);

#[rustc_dump_variances]
pub struct UnusedParam<T>(u8, PhantomData<fn() -> ()>, [T; 0]);

#[rustc_dump_variances]
pub struct TrueUnused<T>(u8);

#[rustc_dump_variances]
pub struct BoundUnused<T: Copy>(u8);

#[rustc_dump_variances]
pub struct ConstParam<const N: usize>(u8);

#[rustc_dump_variances]
pub fn fn_unused<T>(_x: u8) {}

#[rustc_dump_variances]
pub struct MutualA<T>(*const MutualB<T>);

#[rustc_dump_variances]
pub struct MutualB<T>(*const MutualA<T>, PhantomData<fn(T)>);

#[rustc_dump_variances]
pub struct MutualCycleInvA<T>(PhantomData<fn(MutualCycleInvB<T>)>);

#[rustc_dump_variances]
pub struct MutualCycleInvB<T>(PhantomData<fn(MutualCycleInvA<T>)>, *const T);

#[rustc_dump_variances]
pub struct SelfCycleOddInv<T>(PhantomData<fn(SelfCycleOddInv<T>)>, *const T);

fn main() {}
"""

    cov_unsafe_cell_probe_code = """\
#![feature(covariant_unsafe_cell)]
use core::cell::CovariantUnsafeCell;

pub fn check<'big: 'small, 'small>(
    x: CovariantUnsafeCell<&'big u8>,
) -> CovariantUnsafeCell<&'small u8> {
    x
}

fn main() {}
"""

    positive_coercions_code = """\
pub fn shorten_ref<'a>(x: &'static u8) -> &'a u8 { x }
pub fn widen_fn_arg<'a>(f: fn(&'a u8) -> u8) -> fn(&'static u8) -> u8 { f }
pub fn shorten_const_ptr<'a>(p: *const &'static u8) -> *const &'a u8 { p }

fn take_any_ref(x: &u8) -> u8 { *x }

fn main() {
    static STATIC_VAL: u8 = 42;
    let r: &u8 = shorten_ref(&STATIC_VAL);
    let f: fn(&'static u8) -> u8 = widen_fn_arg(take_any_ref);
    let p_src: *const &'static u8 = &(&STATIC_VAL);
    let p_dst: *const &u8 = shorten_const_ptr(p_src);
    let local_val: u8 = 9;
    let local_res = take_any_ref(&local_val);
    println!(
        "COV_REF={} FN_CONTRA={} CONST_PTR={} LOCAL={}",
        *r,
        f(&STATIC_VAL),
        unsafe { **p_dst },
        local_res
    );
}
"""

    inv_mut_ref_code = """\
pub fn inv_mut_ref<'a, 'b>(x: &'a mut &'static u8) -> &'a mut &'b u8 { x }
fn main() {}
"""

    inv_unsafe_cell_code = """\
use core::cell::UnsafeCell;
pub fn inv_cell<'a>(x: UnsafeCell<&'static u8>) -> UnsafeCell<&'a u8> { x }
fn main() {}
"""

    contra_fn_rev_code = """\
pub fn bad_fn_arg<'a>(f: fn(&'static u8)) -> fn(&'a u8) { f }
fn main() {}
"""

    inv_phantom_fn_code = """\
use core::marker::PhantomData;
pub fn bad_phantom_inv<'a>(
    p: PhantomData<fn(&'static u8) -> &'static u8>,
) -> PhantomData<fn(&'a u8) -> &'a u8> { p }
fn main() {}
"""

    inv_phantom_mut_ptr_code = """\
use core::marker::PhantomData;
pub fn bad_phantom_mut<'a>(
    p: PhantomData<*mut &'static u8>,
) -> PhantomData<*mut &'a u8> { p }
fn main() {}
"""

    # Group B: HRTB subtyping & double-contravariant flip
    hrtb_ok_code = """\
pub fn hrtb_to_static(f: for<'a> fn(&'a u8) -> u8) -> fn(&'static u8) -> u8 {
    f
}

pub fn double_contravariant_flip(
    hof: fn(fn(&'static u8) -> u8) -> u8,
) -> fn(for<'a> fn(&'a u8) -> u8) -> u8 {
    hof
}

fn id_ref(x: &u8) -> u8 { *x }
fn call_with_static(g: fn(&'static u8) -> u8) -> u8 { g(&55) }

fn main() {
    let f_static = hrtb_to_static(id_ref);
    let hof_hrtb = double_contravariant_flip(call_with_static);
    println!("HRTB_TO_STATIC={} DOUBLE_FLIP={}", f_static(&77), hof_hrtb(id_ref));
}
"""

    static_to_hrtb_code = """\
pub fn static_to_hrtb(f: fn(&'static u8) -> u8) -> for<'a> fn(&'a u8) -> u8 { f }
fn main() {}
"""

    double_flip_rev_code = """\
pub fn bad_double_flip(
    hof: fn(for<'a> fn(&'a u8) -> u8) -> u8,
) -> fn(fn(&'static u8) -> u8) -> u8 { hof }
fn main() {}
"""

    # Group C: Standalone zerocopy PtrInner / Ptr mirror
    zc_dump_code = """\
#![feature(rustc_attrs)]
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr::NonNull;

#[rustc_dump_variances]
pub struct ZcPtrInner<'a, T: ?Sized> {
    ptr: NonNull<T>,
    _marker: PhantomData<&'a UnsafeCell<T>>,
}

#[rustc_dump_variances]
pub struct ZcPtr<'a, T: ?Sized, I> {
    ptr: ZcPtrInner<'a, T>,
    _invariants: PhantomData<I>,
}

fn main() {}
"""

    zc_cov_lt_code = """\
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr::NonNull;

pub enum Shared {}

pub struct ZcPtrInner<'a, T: ?Sized> {
    ptr: NonNull<T>,
    _marker: PhantomData<&'a UnsafeCell<T>>,
}

pub struct ZcPtr<'a, T: ?Sized, I> {
    ptr: ZcPtrInner<'a, T>,
    _invariants: PhantomData<I>,
}

pub fn shorten_ptr_lt<'a>(p: ZcPtr<'static, u8, Shared>) -> ZcPtr<'a, u8, Shared> {
    p
}

fn main() {
    static X: u8 = 91;
    let p = ZcPtr {
        ptr: ZcPtrInner { ptr: NonNull::from(&X), _marker: PhantomData },
        _invariants: PhantomData::<Shared>,
    };
    let q: ZcPtr<'_, u8, Shared> = shorten_ptr_lt(p);
    println!("ZC_PTR_COVARIANT_LT={}", unsafe { *q.ptr.ptr.as_ref() });
}
"""

    zc_t_inv_code = """\
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr::NonNull;

pub enum Shared {}

pub struct ZcPtrInner<'a, T: ?Sized> {
    ptr: NonNull<T>,
    _marker: PhantomData<&'a UnsafeCell<T>>,
}

pub struct ZcPtr<'a, T: ?Sized, I> {
    ptr: ZcPtrInner<'a, T>,
    _invariants: PhantomData<I>,
}

pub fn cannot_shorten_t_even_for_shared<'a, 'b>(
    p: ZcPtr<'a, &'static u8, Shared>,
) -> ZcPtr<'a, &'b u8, Shared> {
    p
}

fn main() {}
"""

    results: dict = {
        "rustc_version": rustc_ver,
        "experiments": {
            "a_variance_dump_and_subtyping_matrix": {
                "rustc_dump_variances_output": run_rustc_probe(
                    "rustc_dump_variances_output", dump_code
                ),
                "covariant_unsafe_cell_availability": run_rustc_probe(
                    "covariant_unsafe_cell_availability", cov_unsafe_cell_probe_code
                ),
                "subtyping_positive_coercions": run_rustc_probe(
                    "subtyping_positive_coercions", positive_coercions_code, run_binary=True
                ),
                "invariant_mut_ref_rejected": run_rustc_probe(
                    "invariant_mut_ref_rejected", inv_mut_ref_code
                ),
                "invariant_unsafe_cell_rejected": run_rustc_probe(
                    "invariant_unsafe_cell_rejected", inv_unsafe_cell_code
                ),
                "contravariant_fn_reverse_rejected": run_rustc_probe(
                    "contravariant_fn_reverse_rejected", contra_fn_rev_code
                ),
                "invariant_phantom_fn_t_to_t_rejected": run_rustc_probe(
                    "invariant_phantom_fn_t_to_t_rejected", inv_phantom_fn_code
                ),
                "invariant_phantom_mut_ptr_rejected": run_rustc_probe(
                    "invariant_phantom_mut_ptr_rejected", inv_phantom_mut_ptr_code
                ),
            },
            "b_hrtb_subtyping_and_polarity_flip": {
                "hrtb_and_double_contravariant_flip_ok": run_rustc_probe(
                    "hrtb_and_double_contravariant_flip_ok", hrtb_ok_code, run_binary=True
                ),
                "static_to_hrtb_rejected": run_rustc_probe(
                    "static_to_hrtb_rejected", static_to_hrtb_code
                ),
                "static_to_hrtb_no_leak_check_rejected": run_rustc_probe(
                    "static_to_hrtb_no_leak_check_rejected",
                    static_to_hrtb_code,
                    extra_args=["-Zno-leak-check"],
                ),
                "double_flip_reverse_rejected": run_rustc_probe(
                    "double_flip_reverse_rejected", double_flip_rev_code
                ),
            },
            "c_zerocopy_ptr_variance": {
                "zerocopy_ptr_dump_variances": run_rustc_probe(
                    "zerocopy_ptr_dump_variances", zc_dump_code
                ),
                "zerocopy_ptr_lifetime_covariant_ok": run_rustc_probe(
                    "zerocopy_ptr_lifetime_covariant_ok", zc_cov_lt_code, run_binary=True
                ),
                "zerocopy_ptr_shared_referent_t_invariant_rejected": run_rustc_probe(
                    "zerocopy_ptr_shared_referent_t_invariant_rejected", zc_t_inv_code
                ),
            },
        },
    }

    if args.zerocopy_lib is not None:
        results["experiments"]["c_zerocopy_ptr_variance"]["real_zerocopy_crate"] = (
            run_zerocopy_crate_probes(args.zerocopy_lib)
        )

    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
