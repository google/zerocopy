#!/usr/bin/env python3
"""Empirical rustc + Miri probe for:
  Part A: Subtyping variance lattice (12 constructors, lifetime variance,
          #[rustc_variance] dump, and E0392 bivariant parameter rejection)
  Part B: Two-axis dropck / #[may_dangle] / PhantomData<T> soundness & Miri UAF
  Part C: Edition 2021 vs 2024 RPIT default lifetime capturing and use<...>
  Part D: CoerceUnsized vs DispatchFromDyn ABI-preserving field/alignment rules

Outputs scrubbed JSON (zero host-local absolute paths, usernames, or temp dirs).
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env_with_cargo() -> dict[str, str]:
    env = os.environ.copy()
    home = os.path.expanduser("~")
    extra = [os.path.join(home, ".cargo", "bin")]
    cur = env.get("PATH", "")
    parts = [p for p in extra if os.path.isdir(p) and p not in cur.split(":")]
    if parts:
        env["PATH"] = ":".join(parts + ([cur] if cur else []))
    return env


def scrub_text(text: str, tmpdir: Path, sysroot: str) -> str:
    """Remove any absolute host, user-directory, sysroot, or temporary directory paths."""
    out = text
    user_dir = os.path.expanduser("~")
    user_parent = os.path.dirname(user_dir)
    replacements = [
        (str(tmpdir), "<tmpdir>"),
        (sysroot, "<sysroot>"),
        (user_dir, "<userdir>"),
    ]
    for src, dst in replacements:
        if src:
            out = out.replace(src, dst)
    if user_parent and user_parent != os.sep:
        out = re.sub(re.escape(user_parent) + r"/[^/\s:]+", "<userdir>", out)
    out = re.sub(r"/tmp/tmp[a-zA-Z0-9_]+", "<tmpdir>", out)
    return out


def run_cmd(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str],
    tmpdir: Path,
    sysroot: str,
    timeout: int = 120,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return {
        "rc": proc.returncode,
        "stdout": scrub_text(proc.stdout.strip(), tmpdir, sysroot),
        "stderr": scrub_text(proc.stderr.strip(), tmpdir, sysroot),
    }


def compile_rs(
    tmpdir: Path,
    name: str,
    src: str,
    env: dict[str, str],
    sysroot: str,
    edition: str = "2024",
    crate_type: str = "lib",
    extra_flags: list[str] | None = None,
    run_bin: bool = False,
) -> dict[str, Any]:
    rs_path = tmpdir / f"{name}.rs"
    out_path = tmpdir / (f"{name}.bin" if crate_type == "bin" else f"lib{name}.rlib")
    rs_path.write_text(src, encoding="utf-8")
    cmd = [
        "rustc",
        f"--edition={edition}",
        f"--crate-type={crate_type}",
        "-o",
        str(out_path),
        str(rs_path),
    ]
    if extra_flags:
        cmd.extend(extra_flags)
    res = run_cmd(cmd, tmpdir, env, tmpdir, sysroot)
    record: dict[str, Any] = {
        "compile_rc": res["rc"],
        "stderr_head": "\n".join(res["stderr"].splitlines()[:28]),
    }
    if run_bin and res["rc"] == 0:
        run_res = run_cmd([str(out_path)], tmpdir, env, tmpdir, sysroot)
        record["run_rc"] = run_res["rc"]
        record["stdout"] = run_res["stdout"]
        if run_res["stderr"]:
            record["run_stderr_head"] = "\n".join(run_res["stderr"].splitlines()[:15])
    return record


def run_miri_crate(
    miri_proj: Path,
    tmpdir: Path,
    src: str,
    env: dict[str, str],
    sysroot: str,
    edition: str = "2024",
) -> dict[str, Any]:
    (miri_proj / "Cargo.toml").write_text(
        f'[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "{edition}"\n',
        encoding="utf-8",
    )
    src_dir = miri_proj / "src"
    src_dir.mkdir(parents=True, exist_ok=True)
    (src_dir / "main.rs").write_text(src, encoding="utf-8")
    res = run_cmd(
        ["cargo", "miri", "run", "--quiet"],
        miri_proj,
        env,
        tmpdir,
        sysroot,
        timeout=180,
    )
    return {
        "rc": res["rc"],
        "stdout": res["stdout"],
        "stderr_head": "\n".join(res["stderr"].splitlines()[:28]),
    }


def part_a_variance(tmpdir: Path, env: dict[str, str], sysroot: str) -> dict[str, Any]:
    cases = [
        ("shared_ref_T", "&'b T", True),
        ("mut_ref_T", "&'b mut T", True),
        ("raw_const_T", "*const T", False),
        ("raw_mut_T", "*mut T", False),
        ("fn_arg_T", "fn(T)", False),
        ("fn_ret_T", "fn() -> T", False),
        ("fn_double_contra_T", "fn(fn(T))", False),
        ("unsafe_cell_T", "core::cell::UnsafeCell<T>", False),
        ("phantom_T", "core::marker::PhantomData<T>", False),
        ("phantom_fn_arg_T", "core::marker::PhantomData<fn(T)>", False),
        ("phantom_fn_ret_T", "core::marker::PhantomData<fn() -> T>", False),
        ("phantom_inv_T", "core::marker::PhantomData<fn(T) -> T>", False),
    ]
    out: dict[str, Any] = {}
    for key, ty_expr, has_b in cases:
        if has_b:
            struct_def = f"struct Wrap<'b, T>({ty_expr});"
            cov_fn = "pub fn cov<'a, 'b>(x: Wrap<'b, &'static u8>) -> Wrap<'b, &'a u8> { x }"
            contra_fn = "pub fn contra<'a, 'b>(x: Wrap<'b, &'a u8>) -> Wrap<'b, &'static u8> { x }"
        else:
            struct_def = f"struct Wrap<T>({ty_expr});"
            cov_fn = "pub fn cov<'a>(x: Wrap<&'static u8>) -> Wrap<&'a u8> { x }"
            contra_fn = "pub fn contra<'a>(x: Wrap<&'a u8>) -> Wrap<&'static u8> { x }"
        cov_res = compile_rs(tmpdir, f"a_{key}_cov", f"{struct_def}\n{cov_fn}\n", env, sysroot)
        contra_res = compile_rs(tmpdir, f"a_{key}_contra", f"{struct_def}\n{contra_fn}\n", env, sysroot)
        cov_ok = cov_res["compile_rc"] == 0
        contra_ok = contra_res["compile_rc"] == 0
        if cov_ok and contra_ok:
            inferred = "Bivariant"
        elif cov_ok:
            inferred = "Covariant"
        elif contra_ok:
            inferred = "Contravariant"
        else:
            inferred = "Invariant"
        out[key] = {
            "ty": ty_expr,
            "cov_ok": cov_ok,
            "contra_ok": contra_ok,
            "inferred_variance": inferred,
        }

    # Lifetime-parameter variance checks for &'a T, &'a mut T, fn(&'a u8), fn(fn(&'a u8))
    lt_cases = [
        ("lt_shared_ref", "&'a u8"),
        ("lt_mut_ref", "&'a mut u8"),
        ("lt_fn_arg_ref", "fn(&'a u8)"),
        ("lt_fn_double_contra_ref", "fn(fn(&'a u8))"),
        ("lt_mut_ref_to_ref_inner", "&'static mut &'a u8"),
    ]
    lt_out: dict[str, Any] = {}
    for key, ty_expr in lt_cases:
        struct_def = f"struct LtWrap<'a>({ty_expr});"
        cov_fn = "pub fn cov<'a>(x: LtWrap<'static>) -> LtWrap<'a> { x }"
        contra_fn = "pub fn contra<'a>(x: LtWrap<'a>) -> LtWrap<'static> { x }"
        cov_ok = compile_rs(tmpdir, f"a_{key}_cov", f"{struct_def}\n{cov_fn}\n", env, sysroot)["compile_rc"] == 0
        contra_ok = compile_rs(tmpdir, f"a_{key}_contra", f"{struct_def}\n{contra_fn}\n", env, sysroot)["compile_rc"] == 0
        if cov_ok and contra_ok:
            inferred = "Bivariant"
        elif cov_ok:
            inferred = "Covariant"
        elif contra_ok:
            inferred = "Contravariant"
        else:
            inferred = "Invariant"
        lt_out[key] = {
            "ty": ty_expr,
            "cov_ok": cov_ok,
            "contra_ok": contra_ok,
            "inferred_variance": inferred,
        }
    out["lifetime_parameter_variance"] = lt_out

    # E0392 unconstrained bivariant type & lifetime params
    out["unused_type_param_bivariant_rejected_e0392"] = compile_rs(
        tmpdir, "a_e0392_ty", "pub struct Unused<T>(u8);\n", env, sysroot
    )
    out["unused_lifetime_param_bivariant_rejected_e0392"] = compile_rs(
        tmpdir, "a_e0392_lt", "pub struct UnusedLt<'a>(u8);\n", env, sysroot
    )

    # Direct rustc internal #[rustc_dump_variances] attribute dump
    rustc_var_src = """#![feature(rustc_attrs)]
use core::cell::UnsafeCell;
use core::marker::PhantomData;

#[rustc_dump_variances]
pub struct Showcase<'a, 'b, A, B, C, D, E, F>(
    &'a A,
    &'b mut B,
    fn(C) -> D,
    fn(fn(E)),
    UnsafeCell<F>,
    PhantomData<fn(C) -> A>,
);
"""
    out["rustc_dump_variances_internal"] = compile_rs(
        tmpdir, "a_rustc_variance_dump", rustc_var_src, env, sysroot
    )
    return out


def part_b_dropck(
    tmpdir: Path, miri_proj: Path, env: dict[str, str], sysroot: str
) -> dict[str, Any]:
    out: dict[str, Any] = {}

    b1_none = """#![feature(dropck_eyepatch)]
struct PrintOnDrop<'a>(&'a String);
impl<'a> Drop for PrintOnDrop<'a> {
    fn drop(&mut self) { let _ = self.0.len(); }
}

struct MyBox<T>(*mut T);
impl<T> MyBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v))) }
}
unsafe impl<#[may_dangle] T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("dropped_first");
    _guard = MyBox::new(PrintOnDrop(&s));
}
"""
    out["axis1_no_phantom_uaf_compile"] = compile_rs(
        tmpdir, "b1_none", b1_none, env, sysroot, crate_type="bin"
    )
    out["axis1_no_phantom_uaf_miri"] = run_miri_crate(
        miri_proj, tmpdir, b1_none, env, sysroot
    )

    b2_pht = """#![feature(dropck_eyepatch)]
use core::marker::PhantomData;

struct PrintOnDrop<'a>(&'a String);
impl<'a> Drop for PrintOnDrop<'a> {
    fn drop(&mut self) { let _ = self.0.len(); }
}

struct MyBox<T>(*mut T, PhantomData<T>);
impl<T> MyBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
unsafe impl<#[may_dangle] T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("dropped_first");
    _guard = MyBox::new(PrintOnDrop(&s));
}
"""
    out["axis1_phantom_t_blocks_e0597"] = compile_rs(
        tmpdir, "b2_pht", b2_pht, env, sysroot, crate_type="bin"
    )

    b2_pht_safe_order = """#![feature(dropck_eyepatch)]
use core::marker::PhantomData;

struct PrintOnDrop<'a>(&'a String);
impl<'a> Drop for PrintOnDrop<'a> {
    fn drop(&mut self) {
        println!("SAFE_DROP_LEN={}", self.0.len());
    }
}

struct MyBox<T>(*mut T, PhantomData<T>);
impl<T> MyBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
unsafe impl<#[may_dangle] T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let (s, _guard);
    s = String::from("dropped_second");
    _guard = MyBox::new(PrintOnDrop(&s));
}
"""
    out["axis1_phantom_t_safe_order_miri"] = run_miri_crate(
        miri_proj, tmpdir, b2_pht_safe_order, env, sysroot
    )

    b3_phfn = """#![feature(dropck_eyepatch)]
use core::marker::PhantomData;

struct PrintOnDrop<'a>(&'a String);
impl<'a> Drop for PrintOnDrop<'a> {
    fn drop(&mut self) { let _ = self.0.len(); }
}

struct MyBox<T>(*mut T, PhantomData<fn() -> T>);
impl<T> MyBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
unsafe impl<#[may_dangle] T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("dropped_first");
    _guard = MyBox::new(PrintOnDrop(&s));
}
"""
    out["axis1_phantom_fn_uaf_compile"] = compile_rs(
        tmpdir, "b3_phfn", b3_phfn, env, sysroot, crate_type="bin"
    )
    out["axis1_phantom_fn_uaf_miri"] = run_miri_crate(
        miri_proj, tmpdir, b3_phfn, env, sysroot
    )

    b4_axis2 = """#![feature(dropck_eyepatch)]
use core::fmt::Display;
use core::marker::PhantomData;

struct InspectBox<T: Display>(*mut T, PhantomData<T>);
impl<T: Display> InspectBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
unsafe impl<#[may_dangle] T: Display> Drop for InspectBox<T> {
    fn drop(&mut self) {
        unsafe {
            let b = Box::from_raw(self.0);
            let _ = format!("{}", b);
        }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("dangling_copy_ref");
    _guard = InspectBox::new(&s);
}
"""
    out["axis2_direct_read_copy_t_even_with_phantom_t_compile"] = compile_rs(
        tmpdir, "b4_axis2", b4_axis2, env, sysroot, crate_type="bin"
    )
    out["axis2_direct_read_copy_t_even_with_phantom_t_miri"] = run_miri_crate(
        miri_proj, tmpdir, b4_axis2, env, sysroot
    )

    b5_no_may_dangle = """use core::fmt::Display;
use core::marker::PhantomData;

struct InspectBox<T: Display>(*mut T, PhantomData<T>);
impl<T: Display> InspectBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
impl<T: Display> Drop for InspectBox<T> {
    fn drop(&mut self) {
        unsafe {
            let b = Box::from_raw(self.0);
            let _ = format!("{}", b);
        }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("dangling_copy_ref");
    _guard = InspectBox::new(&s);
}
"""
    out["axis2_without_may_dangle_blocks_copy_t_e0597"] = compile_rs(
        tmpdir, "b5_no_may_dangle", b5_no_may_dangle, env, sysroot, crate_type="bin"
    )

    b6_sound_copy = """#![feature(dropck_eyepatch)]
use core::marker::PhantomData;

struct SoundBox<T>(*mut T, PhantomData<T>);
impl<T> SoundBox<T> {
    fn new(v: T) -> Self { Self(Box::into_raw(Box::new(v)), PhantomData) }
}
unsafe impl<#[may_dangle] T> Drop for SoundBox<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let (_guard, s);
    s = String::from("copy_ref_dropped_first");
    _guard = SoundBox::new(&s);
    println!("SOUND_MAY_DANGLE_COPY_OK");
}
"""
    out["sound_may_dangle_copy_t_miri"] = run_miri_crate(
        miri_proj, tmpdir, b6_sound_copy, env, sysroot
    )
    return out


def part_c_rpit(tmpdir: Path, env: dict[str, str], sysroot: str) -> dict[str, Any]:
    out: dict[str, Any] = {}

    c_free = """fn make_opaque<'a>(_x: &'a i32) -> impl Sized {
    42u8
}
fn main() {
    let mut x = 1;
    let tok = make_opaque(&x);
    x += 1;
    drop(tok);
    println!("RPIT_NO_CAPTURE_X={}", x);
}
"""
    out["ed2021_rpit_free_does_not_capture_a"] = compile_rs(
        tmpdir, "c0_2021", c_free, env, sysroot, edition="2021", crate_type="bin", run_bin=True
    )
    out["ed2024_rpit_free_captures_a_by_default"] = compile_rs(
        tmpdir, "c1_2024", c_free, env, sysroot, edition="2024", crate_type="bin", run_bin=True
    )

    c_use_empty = """fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<> {
    42u8
}
fn main() {
    let mut x = 1;
    let tok = make_opaque(&x);
    x += 1;
    drop(tok);
    println!("RPIT_USE_EMPTY_X={}", x);
}
"""
    out["ed2024_rpit_use_empty_opts_out"] = compile_rs(
        tmpdir, "c2_2024_use_empty", c_use_empty, env, sysroot, edition="2024", crate_type="bin", run_bin=True
    )
    out["ed2021_rpit_use_empty_ok"] = compile_rs(
        tmpdir, "c2_2021_use_empty", c_use_empty, env, sysroot, edition="2021", crate_type="bin", run_bin=True
    )

    c_use_a = """fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<'a> {
    42u8
}
fn main() {
    let mut x = 1;
    let tok = make_opaque(&x);
    x += 1;
    drop(tok);
    let _ = x;
}
"""
    out["ed2024_rpit_use_a_captures_a"] = compile_rs(
        tmpdir, "c3_2024_use_a", c_use_a, env, sysroot, edition="2024", crate_type="bin"
    )
    out["ed2021_rpit_use_a_captures_a"] = compile_rs(
        tmpdir, "c3_2021_use_a", c_use_a, env, sysroot, edition="2021", crate_type="bin"
    )

    # Inherent method RPIT vs Trait method RPITIT in 2021 vs 2024
    c_method = """struct S(i32);
impl S {
    fn make(&self) -> impl Sized { 42u8 }
}
fn main() {
    let mut s = S(1);
    let tok = s.make();
    s.0 += 1;
    drop(tok);
    println!("INHERENT_METHOD_X={}", s.0);
}
"""
    out["ed2021_inherent_method_rpit_does_not_capture_self"] = compile_rs(
        tmpdir, "c4_2021_method", c_method, env, sysroot, edition="2021", crate_type="bin", run_bin=True
    )
    out["ed2024_inherent_method_rpit_captures_self"] = compile_rs(
        tmpdir, "c4_2024_method", c_method, env, sysroot, edition="2024", crate_type="bin"
    )

    c_rpitit = """trait Maker {
    fn make(&self) -> impl Sized;
}
struct S(i32);
impl Maker for S {
    fn make(&self) -> impl Sized { 42u8 }
}
fn main() {
    let mut s = S(1);
    let tok = s.make();
    s.0 += 1;
    drop(tok);
    let _ = s.0;
}
"""
    out["ed2021_rpitit_trait_method_already_captures_self"] = compile_rs(
        tmpdir, "c5_2021_rpitit", c_rpitit, env, sysroot, edition="2021", crate_type="bin"
    )
    out["ed2024_rpitit_trait_method_captures_self"] = compile_rs(
        tmpdir, "c5_2024_rpitit", c_rpitit, env, sysroot, edition="2024", crate_type="bin"
    )
    return out


def part_d_dispatch_from_dyn(
    tmpdir: Path, miri_proj: Path, env: dict[str, str], sysroot: str
) -> dict[str, Any]:
    out: dict[str, Any] = {}

    d1_ok = """#![feature(unsize, coerce_unsized, dispatch_from_dyn, arbitrary_self_types)]
use core::marker::Unsize;
use core::ops::{CoerceUnsized, Deref, DispatchFromDyn};

struct MyPtr<T: ?Sized>(*const T);
impl<T: ?Sized> Deref for MyPtr<T> {
    type Target = T;
    fn deref(&self) -> &T { unsafe { &*self.0 } }
}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<U>> for MyPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<MyPtr<U>> for MyPtr<T> {}

trait Foo {
    fn val(self: MyPtr<Self>) -> u32;
}
struct Bar(u32);
impl Foo for Bar {
    fn val(self: MyPtr<Self>) -> u32 { (*self).0 }
}

fn main() {
    let b = Bar(123);
    let p: MyPtr<dyn Foo> = MyPtr(&b as *const Bar);
    println!("CUSTOM_DISPATCH={}", p.val());
}
"""
    out["custom_dispatch_from_dyn_ok"] = compile_rs(
        tmpdir, "d1_ok", d1_ok, env, sysroot, crate_type="bin", run_bin=True
    )
    out["custom_dispatch_from_dyn_miri"] = run_miri_crate(
        miri_proj, tmpdir, d1_ok, env, sysroot
    )

    d2_extra = """#![feature(unsize, coerce_unsized, dispatch_from_dyn)]
use core::marker::Unsize;
use core::ops::{CoerceUnsized, DispatchFromDyn};

struct BadPtr<T: ?Sized>(*const T, u64);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadPtr<U>> for BadPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadPtr<U>> for BadPtr<T> {}
"""
    out["dispatch_from_dyn_extra_non_zst_rejected_e0378"] = compile_rs(
        tmpdir, "d2_extra", d2_extra, env, sysroot
    )

    d2_coerce_only = """#![feature(unsize, coerce_unsized)]
use core::marker::Unsize;
use core::ops::CoerceUnsized;

pub struct CoerceWithMeta<T: ?Sized>(pub *const T, pub u64);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<CoerceWithMeta<U>> for CoerceWithMeta<T> {}

pub fn coerce_slice(arr: &[u8; 4]) -> CoerceWithMeta<[u8]> {
    CoerceWithMeta(arr as *const [u8; 4], 99)
}
"""
    out["coerce_unsized_extra_non_zst_allowed"] = compile_rs(
        tmpdir, "d2_coerce_only", d2_coerce_only, env, sysroot
    )

    d3_azst = """#![feature(unsize, coerce_unsized, dispatch_from_dyn)]
use core::marker::Unsize;
use core::ops::{CoerceUnsized, DispatchFromDyn};

#[repr(align(16))]
struct Align16Zst;

struct BadAlignedPtr<T: ?Sized>(*const T, Align16Zst);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadAlignedPtr<U>> for BadAlignedPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadAlignedPtr<U>> for BadAlignedPtr<T> {}
"""
    out["dispatch_from_dyn_align16_zst_rejected_e0378"] = compile_rs(
        tmpdir, "d3_azst", d3_azst, env, sysroot
    )

    d3b_1byte_zst = """#![feature(unsize, coerce_unsized, dispatch_from_dyn, arbitrary_self_types)]
use core::marker::Unsize;
use core::ops::{CoerceUnsized, Deref, DispatchFromDyn};

struct UnitZst;
struct GoodZstPtr<T: ?Sized>(*const T, UnitZst);
impl<T: ?Sized> Deref for GoodZstPtr<T> {
    type Target = T;
    fn deref(&self) -> &T { unsafe { &*self.0 } }
}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<GoodZstPtr<U>> for GoodZstPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<GoodZstPtr<U>> for GoodZstPtr<T> {}

trait Foo {
    fn val(self: GoodZstPtr<Self>) -> u32;
}
struct Bar(u32);
impl Foo for Bar {
    fn val(self: GoodZstPtr<Self>) -> u32 { (*self).0 }
}

fn main() {
    let b = Bar(456);
    let p: GoodZstPtr<dyn Foo> = GoodZstPtr(&b as *const Bar, UnitZst);
    println!("ZST_DISPATCH={}", p.val());
}
"""
    out["dispatch_from_dyn_1byte_nongeneric_zst_miri"] = run_miri_crate(
        miri_proj, tmpdir, d3b_1byte_zst, env, sysroot
    )

    d4_pht = """#![feature(unsize, coerce_unsized, dispatch_from_dyn, arbitrary_self_types)]
use core::marker::{PhantomData, Unsize};
use core::ops::{CoerceUnsized, Deref, DispatchFromDyn};

struct PhantomTPtr<T: ?Sized>(*const T, PhantomData<T>);
impl<T: ?Sized> Deref for PhantomTPtr<T> {
    type Target = T;
    fn deref(&self) -> &T { unsafe { &*self.0 } }
}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<PhantomTPtr<U>> for PhantomTPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<PhantomTPtr<U>> for PhantomTPtr<T> {}

trait Foo {
    fn val(self: PhantomTPtr<Self>) -> u32;
}
struct Bar(u32);
impl Foo for Bar {
    fn val(self: PhantomTPtr<Self>) -> u32 { (*self).0 }
}

fn main() {
    let b = Bar(789);
    let p: PhantomTPtr<dyn Foo> = PhantomTPtr(&b as *const Bar, PhantomData);
    println!("PHANTOM_DISPATCH={}", p.val());
}
"""
    out["dispatch_from_dyn_phantom_t_whitelisted_compile"] = compile_rs(
        tmpdir, "d4_pht", d4_pht, env, sysroot, crate_type="bin", run_bin=True
    )
    out["dispatch_from_dyn_phantom_t_whitelisted_miri"] = run_miri_crate(
        miri_proj, tmpdir, d4_pht, env, sysroot
    )

    d5_myzst_coerce = """#![feature(unsize, coerce_unsized, dispatch_from_dyn)]
use core::marker::{PhantomData, Unsize};
use core::ops::{CoerceUnsized, DispatchFromDyn};

struct MyZst<T: ?Sized>(PhantomData<T>);
struct BadCustomGenZstPtr<T: ?Sized>(*const T, MyZst<T>);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadCustomGenZstPtr<U>> for BadCustomGenZstPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadCustomGenZstPtr<U>> for BadCustomGenZstPtr<T> {}
"""
    out["dispatch_from_dyn_custom_generic_zst_with_coerce_e0375"] = compile_rs(
        tmpdir, "d5_myzst_coerce", d5_myzst_coerce, env, sysroot
    )

    d6_myzst_dispatch_only = """#![feature(unsize, dispatch_from_dyn)]
use core::marker::{PhantomData, Unsize};
use core::ops::DispatchFromDyn;

struct MyZst<T: ?Sized>(PhantomData<T>);
struct BadCustomGenZstPtr<T: ?Sized>(*const T, MyZst<T>);
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadCustomGenZstPtr<U>> for BadCustomGenZstPtr<T> {}
"""
    out["dispatch_from_dyn_custom_generic_zst_alone_e0375"] = compile_rs(
        tmpdir, "d6_myzst_dispatch_only", d6_myzst_dispatch_only, env, sysroot
    )

    d6b_other_type_generic_zst = """#![feature(unsize, dispatch_from_dyn)]
use core::marker::{PhantomData, Unsize};
use core::ops::DispatchFromDyn;

struct OtherGenZst<X>(PhantomData<X>);
struct BadOtherGenZstPtr<T: ?Sized, X>(*const T, OtherGenZst<X>);
impl<T: ?Sized + Unsize<U>, U: ?Sized, X>
    DispatchFromDyn<BadOtherGenZstPtr<U, X>> for BadOtherGenZstPtr<T, X> {}
"""
    out["dispatch_from_dyn_unchanged_type_generic_zst_e0378"] = compile_rs(
        tmpdir, "d6b_other_gen_zst", d6b_other_type_generic_zst, env, sysroot
    )

    d7_phantom_const_generic = """#![feature(unsize, dispatch_from_dyn)]
use core::marker::Unsize;
use core::ops::DispatchFromDyn;

struct ConstZst<const N: usize>;
struct BadConstZstPtr<T: ?Sized, const N: usize>(*const T, ConstZst<N>);
impl<T: ?Sized + Unsize<U>, U: ?Sized, const N: usize>
    DispatchFromDyn<BadConstZstPtr<U, N>> for BadConstZstPtr<T, N> {}
"""
    out["dispatch_from_dyn_const_generic_zst_rejected_e0378"] = compile_rs(
        tmpdir, "d7_const_zst", d7_phantom_const_generic, env, sysroot
    )

    d8_repr_c = """#![feature(unsize, dispatch_from_dyn)]
use core::marker::Unsize;
use core::ops::DispatchFromDyn;

#[repr(C)]
struct ReprCPtr<T: ?Sized>(*const T);
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<ReprCPtr<U>> for ReprCPtr<T> {}
"""
    out["dispatch_from_dyn_repr_c_rejected"] = compile_rs(
        tmpdir, "d8_repr_c", d8_repr_c, env, sysroot
    )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional path to write JSON output (defaults to stdout).",
    )
    args = parser.parse_args()

    env = _env_with_cargo()
    rustc_v = subprocess.check_output(["rustc", "-vV"], env=env, text=True).strip()
    miri_v = subprocess.check_output(["cargo", "miri", "--version"], env=env, text=True).strip()
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"], env=env, text=True).strip()

    with tempfile.TemporaryDirectory(prefix="rustc_var_dropck_probe_") as td:
        tmpdir = Path(td)
        miri_proj = tmpdir / "miri_proj"
        miri_proj.mkdir()

        results = {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime(
                "%Y-%m-%dT%H:%M:%SZ"
            ),
            "rustc_version": rustc_v,
            "miri_version": miri_v,
            "part_a_variance_lattice": part_a_variance(tmpdir, env, sysroot),
            "part_b_dropck_may_dangle_phantomdata": part_b_dropck(
                tmpdir, miri_proj, env, sysroot
            ),
            "part_c_edition2021_vs_2024_rpit_use_capture": part_c_rpit(
                tmpdir, env, sysroot
            ),
            "part_d_coerce_unsized_and_dispatch_from_dyn": part_d_dispatch_from_dyn(
                tmpdir, miri_proj, env, sysroot
            ),
        }

    payload = json.dumps(results, indent=2, ensure_ascii=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
