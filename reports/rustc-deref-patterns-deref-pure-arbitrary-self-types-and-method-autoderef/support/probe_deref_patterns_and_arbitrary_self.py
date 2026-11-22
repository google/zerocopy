#!/usr/bin/env python3
"""Empirical rustc + Miri probe for deref_patterns, arbitrary_self_types v2,
DispatchFromDyn, and method-call autoderef/autoref resolution order.

All compilation, execution, MIR inspection, and Miri checks are executed live
against the active nightly rustc/Miri toolchain with zero hardcoded outputs.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def _sanitize(text: str, tmp_dir: Path) -> str:
    return text.replace(str(tmp_dir), "<TMP>")


def _compile_only(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    crate_type: str = "lib",
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    out = tmp_dir / f"{name}.out"
    src.write_text(code, encoding="utf-8")
    cmd = [rustc, "--edition=2024", f"--crate-type={crate_type}", str(src), "-o", str(out)]
    if extra_args:
        cmd.extend(extra_args)
    res = _run(cmd, cwd=tmp_dir)
    return {
        "rc": res.returncode,
        "stdout": _sanitize(res.stdout, tmp_dir).strip(),
        "stderr": _sanitize(res.stderr, tmp_dir).strip(),
    }


def _compile_and_run_native(
    rustc: str, tmp_dir: Path, name: str, code: str
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    exe = tmp_dir / f"{name}_bin"
    src.write_text(code, encoding="utf-8")
    comp = _run([rustc, "--edition=2024", str(src), "-o", str(exe)], cwd=tmp_dir)
    if comp.returncode != 0:
        return {
            "compile_rc": comp.returncode,
            "run_rc": None,
            "stdout": "",
            "stderr": _sanitize(comp.stderr, tmp_dir).strip(),
        }
    run = _run([str(exe)], cwd=tmp_dir)
    return {
        "compile_rc": 0,
        "run_rc": run.returncode,
        "stdout": run.stdout.strip(),
        "stderr": _sanitize(run.stderr, tmp_dir).strip(),
    }


def _run_miri(
    cargo: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    miri_env: dict[str, str],
    miri_flags: str | None = None,
) -> dict[str, Any]:
    proj = tmp_dir / f"miri_{name}"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        f'[package]\nname = "miri_{name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(code, encoding="utf-8")
    env = dict(miri_env)
    if miri_flags:
        existing = env.get("MIRIFLAGS", "").strip()
        env["MIRIFLAGS"] = f"{existing} {miri_flags}".strip()
    res = _run([cargo, "miri", "run", "-q"], cwd=proj, env=env)
    return {
        "rc": res.returncode,
        "stdout": res.stdout.strip(),
        "stderr": _sanitize(res.stderr, proj).strip(),
    }


def _prepare_miri_env(cargo: str, tmp_dir: Path, explicit_sysroot: str | None) -> dict[str, str]:
    env = dict(os.environ)
    if explicit_sysroot:
        env["MIRI_SYSROOT"] = explicit_sysroot
        return env
    if env.get("MIRI_SYSROOT"):
        return env
    # Ensure Miri sysroot builds cleanly even in offline environments with a vendored
    # ~/.cargo/config.toml whose vendor versions differ from rust-src's locked std deps.
    probe_dir = tmp_dir / "_miri_setup_probe"
    (probe_dir / "src").mkdir(parents=True, exist_ok=True)
    (probe_dir / "Cargo.toml").write_text(
        '[package]\nname = "miri_setup_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (probe_dir / "src" / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
    test = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=240)
    if test.returncode == 0:
        return env

    home_cargo = Path.home() / ".cargo"
    if (home_cargo / "registry").is_dir():
        alt_home = tmp_dir / "_alt_cargo_home"
        alt_home.mkdir(parents=True, exist_ok=True)
        os.symlink(home_cargo / "registry", alt_home / "registry")
        if (home_cargo / "bin").is_dir():
            os.symlink(home_cargo / "bin", alt_home / "bin")
        (alt_home / "config.toml").write_text("[net]\noffline = true\n", encoding="utf-8")
        sysroot = tmp_dir / "_miri_sysroot"
        sysroot.mkdir(parents=True, exist_ok=True)
        env["CARGO_HOME"] = str(alt_home)
        env["MIRI_SYSROOT"] = str(sysroot)
        setup = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=300)
        if setup.returncode != 0:
            raise RuntimeError(f"cargo miri setup failed:\n{setup.stderr}")
        return env
    raise RuntimeError(f"cargo miri setup failed:\n{test.stderr}")


# ---------------------------------------------------------------------------
# Rust probe programs
# ---------------------------------------------------------------------------

PART_A_IMPURE_DEREF = r"""
#![feature(deref_patterns)]
use core::ops::Deref;

pub struct ImpureWrapper(pub u32);

impl Deref for ImpureWrapper {
    type Target = u32;
    fn deref(&self) -> &u32 { &self.0 }
}

pub fn test_impure(w: ImpureWrapper) -> u32 {
    match w {
        deref!(0) => 1,
        _ => 2,
    }
}
"""

PART_A_STD_AND_CUSTOM_DEREF_PURE = r"""
#![feature(deref_patterns, deref_pure_trait)]
use std::borrow::Cow;
use std::ops::{Deref, DerefMut, DerefPure};
use std::rc::Rc;
use std::sync::Arc;

struct PureWrap<T>(T);

impl<T> Deref for PureWrap<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

impl<T> DerefMut for PureWrap<T> {
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}

unsafe impl<T> DerefPure for PureWrap<T> {}

fn main() {
    let b: Box<u32> = Box::new(10);
    let r: Rc<u32> = Rc::new(20);
    let a: Arc<u32> = Arc::new(30);
    let s: String = String::from("hello");
    let v: Vec<u32> = vec![1, 2, 3];
    let c: Cow<'_, str> = Cow::Owned(String::from("cow"));
    let mut p: PureWrap<u32> = PureWrap(40);

    let v_box = match b { deref!(10) => 10, deref!(x) => x };
    let v_rc = match r { deref!(20) => 20, deref!(x) => x };
    let v_arc = match a { deref!(30) => 30, deref!(x) => x };
    let v_str = match s { deref!("hello") => 50, _ => 0 };
    let v_vec = match v { deref!([1, x, 3]) => x * 10, _ => 0 };
    let v_cow = match c { deref!("cow") => 35, _ => 0 };
    let v_custom = match p {
        deref!(ref mut x) => {
            *x += 5;
            *x
        }
    };
    let total = v_box + v_rc + v_arc + v_str + v_vec + v_cow + v_custom;
    assert_eq!(p.0, 45);
    assert_eq!(total, 210);
    println!("DEREF_PAT_OK={total} MUT_CUSTOM={}", p.0);
}
"""

PART_A_DEEP_FAKE_BORROW_GUARD = r"""
#![feature(deref_patterns)]

pub fn bad_guard(mut b: Box<bool>) -> u32 {
    match b {
        deref!(true) => 1,
        _ if { *b = true; false } => 2,
        deref!(false) => 3,
    }
}
"""

PART_A_MIXED_CTORS = r"""
#![feature(deref_patterns, deref_pure_trait)]
use core::ops::{Deref, DerefPure};

pub struct PureWrap(pub u32);
impl Deref for PureWrap {
    type Target = u32;
    fn deref(&self) -> &u32 { &self.0 }
}
unsafe impl DerefPure for PureWrap {}

pub fn mixed(w: PureWrap) -> u32 {
    match w {
        deref!(0) => 1,
        PureWrap(1) => 2,
        _ => 3,
    }
}
"""

PART_A_MULTI_ARM_MIR = r"""
#![feature(deref_patterns, deref_pure_trait)]
use core::ops::{Deref, DerefPure};

pub struct PureBool(pub bool);

impl Deref for PureBool {
    type Target = bool;
    #[inline(never)]
    fn deref(&self) -> &bool { &self.0 }
}

unsafe impl DerefPure for PureBool {}

pub fn classify_pure(w: PureBool) -> u32 {
    match w {
        deref!(true) => 10,
        deref!(false) => 20,
    }
}
"""

PART_A_LYING_DEREF_PURE_UB = r"""
#![feature(deref_patterns, deref_pure_trait)]
use std::cell::Cell;
use std::ops::{Deref, DerefPure};

static FALSE_VAL: bool = false;
static TRUE_VAL: bool = true;

struct LyingToggle(Cell<bool>);

impl Deref for LyingToggle {
    type Target = bool;
    fn deref(&self) -> &bool {
        let prev = self.0.get();
        self.0.set(!prev);
        if prev { &TRUE_VAL } else { &FALSE_VAL }
    }
}

// DELIBERATELY UNSOUND: violates DerefPure idempotence to test exhaustiveness UB.
unsafe impl DerefPure for LyingToggle {}

fn main() {
    let w = LyingToggle(Cell::new(false));
    let out = match w {
        deref!(true) => 1,
        deref!(false) => 2,
    };
    println!("UNEXPECTED_OUT={out}");
}
"""

PART_B_NON_DEREF_RECEIVER_AND_RAW_PTR = r"""
#![feature(arbitrary_self_types, arbitrary_self_types_pointers)]
use std::ops::Receiver;

struct Handle<T: ?Sized> {
    ptr: *const T,
    tag: u32,
}

impl<T: ?Sized> Receiver for Handle<T> {
    type Target = T;
}

struct Target {
    val: u32,
}

impl Target {
    fn via_handle(self: Handle<Self>) -> u32 {
        let v = unsafe { (*self.ptr).val };
        v + self.tag
    }

    fn via_const_ptr(self: *const Self) -> u32 {
        unsafe { (*self).val * 2 }
    }

    fn bump_mut_ptr(self: *mut Self, delta: u32) -> u32 {
        unsafe {
            (*self).val += delta;
            (*self).val
        }
    }
}

fn main() {
    let mut t = Target { val: 20 };
    let h = Handle { ptr: &t as *const Target, tag: 11 };
    let r_handle = h.via_handle();
    let p_const: *const Target = &t;
    let r_const = p_const.via_const_ptr();
    let p_mut: *mut Target = &mut t;
    let r_mut = p_mut.bump_mut_ptr(7);
    assert_eq!(r_handle, 31);
    assert_eq!(r_const, 40);
    assert_eq!(r_mut, 27);
    println!("HANDLE={r_handle} RAW_PTR={r_const} RAW_MUT={r_mut}");
}
"""

PART_B_RAW_PTR_WITHOUT_POINTERS_FEATURE = r"""
#![feature(arbitrary_self_types)]

pub struct S(pub u32);
impl S {
    pub fn raw_self(self: *const Self) -> u32 { 0 }
}
"""

PART_B_RECEIVER_WITHOUT_DISPATCH_FROM_DYN = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct NonDynHandle<T: ?Sized> {
    pub ptr: *const T,
    pub tag: u32,
}

impl<T: ?Sized> Receiver for NonDynHandle<T> {
    type Target = T;
}

pub trait DynAttempt {
    fn ping(self: NonDynHandle<Self>) -> u32;
}

pub fn use_dyn(d: &dyn DynAttempt) -> usize {
    core::mem::size_of_val(&d)
}
"""

PART_B_DISPATCH_FROM_DYN_TWO_FIELD_REJECTED = r"""
#![feature(arbitrary_self_types, dispatch_from_dyn, unsize)]
use core::marker::Unsize;
use core::ops::DispatchFromDyn;

pub struct TwoField<T: ?Sized> {
    pub ptr: *const T,
    pub extra: u32,
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<TwoField<U>> for TwoField<T> {}
"""

PART_B_DISPATCH_FROM_DYN_REPR_C_REJECTED = r"""
#![feature(arbitrary_self_types, dispatch_from_dyn, unsize)]
use core::marker::Unsize;
use core::ops::DispatchFromDyn;

#[repr(C)]
pub struct ReprCHandle<T: ?Sized>(pub *const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<ReprCHandle<U>> for ReprCHandle<T> {}
"""

PART_B_DISPATCH_FROM_DYN_VALID_CUSTOM_HANDLE = r"""
#![feature(arbitrary_self_types, coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::{PhantomData, Unsize};
use std::ops::{CoerceUnsized, DispatchFromDyn, Receiver};

struct DynHandle<T: ?Sized> {
    ptr: *const T,
    _zst: PhantomData<u8>,
}

impl<T: ?Sized> Receiver for DynHandle<T> {
    type Target = T;
}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<DynHandle<U>> for DynHandle<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<DynHandle<U>> for DynHandle<T> {}

trait DynOk {
    fn ping(self: DynHandle<Self>) -> u32;
}

struct Concrete(u32);
impl DynOk for Concrete {
    fn ping(self: DynHandle<Self>) -> u32 {
        unsafe { (*self.ptr).0 + 100 }
    }
}

fn call_dyn(h: DynHandle<dyn DynOk>) -> u32 {
    h.ping()
}

fn main() {
    let c = Concrete(42);
    let h: DynHandle<Concrete> = DynHandle { ptr: &c, _zst: PhantomData };
    let dyn_h: DynHandle<dyn DynOk> = h;
    let out = call_dyn(dyn_h);
    assert_eq!(out, 142);
    println!("DYN_HANDLE_OK={out}");
}
"""

PART_B_SHADOWING_DEREF_DEPTH0_WINS = r"""
#![feature(arbitrary_self_types)]
use std::ops::Deref;

struct SmartPtr<T>(T);

impl<T> Deref for SmartPtr<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

impl<T> SmartPtr<T> {
    fn tag(&self) -> u32 { 222 }
}

struct Inner;

impl Inner {
    fn tag(&self) -> u32 { 111 }
}

fn main() {
    let p = SmartPtr(Inner);
    let chosen = p.tag();
    let explicit_inner = Inner::tag(&*p);
    assert_eq!(chosen, 222);
    assert_eq!(explicit_inner, 111);
    println!("SHADOW_TAG={chosen} EXPLICIT_INNER={explicit_inner}");
}
"""

PART_B_SHADOWING_INH_VS_TRAIT_EXT = r"""
#![feature(arbitrary_self_types)]
use std::ops::Receiver;

struct SmartPtr<T>(T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    fn tag(&self) -> u32 { 222 }
}

struct Inner;
trait ExtTag: Sized {
    fn tag(self: &SmartPtr<Self>) -> u32;
}
impl ExtTag for Inner {
    fn tag(self: &SmartPtr<Self>) -> u32 { 111 }
}

fn main() {
    let p = SmartPtr(Inner);
    let chosen = p.tag();
    let explicit_ext = <Inner as ExtTag>::tag(&p);
    assert_eq!(chosen, 222);
    assert_eq!(explicit_ext, 111);
    println!("INH_OVER_EXT_TAG={chosen} EXPLICIT_EXT={explicit_ext}");
}
"""

PART_B_SHADOWING_ASYMMETRY_INNER_BY_VAL_WINS = r"""
#![feature(arbitrary_self_types)]
use std::ops::Receiver;

struct SmartPtr<T>(T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    #[allow(dead_code)]
    fn asym(&self) -> u32 { 222 }
}

struct Inner;
impl Inner {
    fn asym(self: SmartPtr<Self>) -> u32 { 111 }
}

fn main() {
    let p = SmartPtr(Inner);
    let chosen = p.asym();
    assert_eq!(chosen, 111);
    println!("ASYM_INNER_WINS={chosen}");
}
"""

PART_B_BOTH_INH_SAME_REF_AMBIGUITY = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartPtr<T>(pub T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    pub fn same_ref(&self) -> u32 { 222 }
}

pub struct Inner;
impl Inner {
    pub fn same_ref(self: &SmartPtr<Self>) -> u32 { 111 }
}

pub fn trigger(p: SmartPtr<Inner>) -> u32 {
    p.same_ref()
}
"""

PART_B_ANTI_SHADOWING_BY_VAL_VS_BY_REF = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartPtr<T>(pub T);

impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}

impl<T> SmartPtr<T> {
    pub fn collide(self) -> u32 { 222 }
}

pub struct Inner;

impl Inner {
    pub fn collide(self: &SmartPtr<Self>) -> u32 { 111 }
}

pub fn trigger(p: SmartPtr<Inner>) -> u32 {
    p.collide()
}
"""

PART_B_ANTI_SHADOWING_REF_VS_MUT_REF = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartPtr<T>(pub T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    pub fn collide_ref(&self) -> u32 { 222 }
}

pub struct Inner;
impl Inner {
    pub fn collide_ref(self: &mut SmartPtr<Self>) -> u32 { 111 }
}

pub fn trigger(mut p: SmartPtr<Inner>) -> u32 {
    p.collide_ref()
}
"""

PART_C_METHOD_AUTODEREF_PRECEDENCE = r"""
#![feature(arbitrary_self_types, arbitrary_self_types_pointers)]
#![allow(dead_code)]
use std::ops::Deref;

// 1. (depth=0, ByVal) vs (depth=0, &self) vs (depth=1, ByVal)
struct Inner;
struct Outer(Inner);
impl Deref for Outer {
    type Target = Inner;
    fn deref(&self) -> &Inner { &self.0 }
}

trait ExtByVal { fn m_val(self) -> u32; }
trait ExtRef { fn m_ref(&self) -> u32; }
trait ExtMut { fn m_mut(&mut self) -> u32; }
trait ExtDepth0RefVsDepth1Val { fn m_d0r_d1v(&self) -> u32; }
trait ExtDepth0MutVsDepth1Ref { fn m_d0m_d1r(&mut self) -> u32; }

impl ExtByVal for Outer { fn m_val(self) -> u32 { 10 } }
impl ExtRef for Outer { fn m_ref(&self) -> u32 { 11 } }
impl ExtMut for Outer { fn m_mut(&mut self) -> u32 { 12 } }

impl ExtDepth0RefVsDepth1Val for Outer { fn m_d0r_d1v(&self) -> u32 { 20 } }
impl Inner {
    fn m_d0r_d1v(self) -> u32 { 21 }
    fn m_d0m_d1r(&self) -> u32 { 31 }
}
impl ExtDepth0MutVsDepth1Ref for Outer { fn m_d0m_d1r(&mut self) -> u32 { 30 } }

// 2. Inherent vs trait extension at same (depth=0, &self), and (depth=0, &self) trait vs (depth=1, &self) inherent
trait ExtSame { fn m_inh_vs_ext(&self) -> u32; }
impl Outer { fn m_inh_vs_ext(&self) -> u32 { 40 } }
impl ExtSame for Outer { fn m_inh_vs_ext(&self) -> u32 { 41 } }

// 3. Array [u32; 4] exact vs unsized [u32] slice step (after Deref)
struct ArrWrap([u32; 4]);
impl Deref for ArrWrap {
    type Target = [u32; 4];
    fn deref(&self) -> &[u32; 4] { &self.0 }
}

trait ExactArr { fn m_arr(&self) -> u32; }
trait SliceOnly { fn m_slice(&self) -> u32; }
trait BothArrAndSlice { fn m_both(&self) -> u32; }

impl ExactArr for [u32; 4] { fn m_arr(&self) -> u32 { 50 } }
impl SliceOnly for [u32] { fn m_slice(&self) -> u32 { 60 } }
impl BothArrAndSlice for [u32; 4] { fn m_both(&self) -> u32 { 70 } }
impl BothArrAndSlice for [u32] { fn m_both(&self) -> u32 { 71 } }

// 4. Raw pointer *mut S -> *const S via pick_const_ptr_method vs &(*mut S)
struct RawItem(u32);
impl RawItem {
    fn only_const(self: *const Self) -> u32 { unsafe { (*self).0 + 80 } }
}
trait RefOnMutPtr { fn ptr_ref_vs_const(&self) -> u32; }
impl RefOnMutPtr for *mut RawItem { fn ptr_ref_vs_const(&self) -> u32 { 90 } }
impl RawItem {
    fn ptr_ref_vs_const(self: *const Self) -> u32 { 91 }
}

fn main() {
    let mut o1 = Outer(Inner);
    let r_d0r_d1v = o1.m_d0r_d1v(); // depth=0 &self (trait) beats depth=1 by-val (inherent)
    let r_d0m_d1r = o1.m_d0m_d1r(); // depth=0 &mut self (trait) beats depth=1 &self (inherent)
    let r_inh_vs_ext = o1.m_inh_vs_ext(); // inherent beats trait at same (0, &self)
    let r_val = o1.m_val(); // depth=0 by-val

    let aw = ArrWrap([1, 2, 3, 4]);
    let r_arr = aw.m_arr();     // deref depth=1 exact [u32; 4]
    let r_slice = aw.m_slice(); // deref depth=1 + unsize [u32]
    let r_both = aw.m_both();   // exact [u32; 4] beats unsized [u32]

    let mut ri = RawItem(5);
    let pm: *mut RawItem = &mut ri;
    let r_const_coerced = pm.only_const(); // *mut -> *const via pick_const_ptr_method
    let r_ref_before_const = pm.ptr_ref_vs_const(); // &(*mut T) beats *mut -> *const

    assert_eq!(r_val, 10);
    assert_eq!(r_d0r_d1v, 20);
    assert_eq!(r_d0m_d1r, 30);
    assert_eq!(r_inh_vs_ext, 40);
    assert_eq!(r_arr, 50);
    assert_eq!(r_slice, 60);
    assert_eq!(r_both, 70);
    assert_eq!(r_const_coerced, 85);
    assert_eq!(r_ref_before_const, 90);
    println!(
        "PICK_VAL={r_val} D0R_VS_D1V={r_d0r_d1v} D0M_VS_D1R={r_d0m_d1r} INH_VS_EXT={r_inh_vs_ext} ARR={r_arr} SLICE={r_slice} BOTH={r_both} CONST_PTR={r_const_coerced} REF_BEFORE_CONST={r_ref_before_const}"
    );
}
"""

PART_C_RAW_PTR_NO_AUTODEREF = r"""
#![feature(arbitrary_self_types, arbitrary_self_types_pointers)]

pub struct Target(pub u32);
impl Target {
    pub fn by_ref(&self) -> u32 { self.0 }
}

pub fn illegal_raw_autoderef(p: *const Target) -> u32 {
    p.by_ref()
}
"""


def run_all(rustc: str, cargo: str, miri_sysroot: str | None) -> dict[str, Any]:
    rustc_ver = _run([rustc, "--version", "--verbose"])
    miri_ver = _run([cargo, "miri", "--version"])
    if rustc_ver.returncode != 0:
        raise RuntimeError(f"rustc --version failed: {rustc_ver.stderr}")
    if miri_ver.returncode != 0:
        raise RuntimeError(f"cargo miri --version failed: {miri_ver.stderr}")

    with tempfile.TemporaryDirectory(prefix="probe_deref_self_") as td:
        tmp = Path(td)
        miri_env = _prepare_miri_env(cargo, tmp, miri_sysroot)

        # Part A
        a_impure = _compile_only(rustc, tmp, "a_impure", PART_A_IMPURE_DEREF)
        a_native = _compile_and_run_native(rustc, tmp, "a_std_custom", PART_A_STD_AND_CUSTOM_DEREF_PURE)
        a_miri_sb = _run_miri(cargo, tmp, "a_std_custom_sb", PART_A_STD_AND_CUSTOM_DEREF_PURE, miri_env=miri_env)
        a_miri_tb = _run_miri(
            cargo, tmp, "a_std_custom_tb", PART_A_STD_AND_CUSTOM_DEREF_PURE,
            miri_env=miri_env, miri_flags="-Zmiri-tree-borrows",
        )
        a_guard = _compile_only(rustc, tmp, "a_guard", PART_A_DEEP_FAKE_BORROW_GUARD)
        a_mixed = _compile_only(rustc, tmp, "a_mixed", PART_A_MIXED_CTORS)

        # MIR inspection of multi-arm deref!()
        mir_src = tmp / "a_mir.rs"
        mir_out = tmp / "a_mir.mir"
        mir_src.write_text(PART_A_MULTI_ARM_MIR, encoding="utf-8")
        mir_res = _run(
            [rustc, "--edition=2024", "--crate-type=lib", "--emit=mir", str(mir_src), "-o", str(mir_out)],
            cwd=tmp,
        )
        mir_text = mir_out.read_text(encoding="utf-8") if mir_out.exists() else ""
        # Extract classify_pure MIR block
        m_fn = re.search(r"fn classify_pure\([^\n]*\n(?:[ \t].*\n|\n)*^\}", mir_text, flags=re.M)
        classify_mir = m_fn.group(0) if m_fn else ""
        deref_call_count = len(re.findall(r"as (?:core::ops::)?Deref>::deref\(", classify_mir))
        has_unreachable = "unreachable;" in classify_mir
        has_fake_borrow = "Fake(" in classify_mir or "FakeRead" in classify_mir
        a_mir = {
            "rc": mir_res.returncode,
            "classify_pure_found": bool(m_fn),
            "deref_call_count_in_post_cleanup_mir": deref_call_count,
            "has_unreachable_terminator": has_unreachable,
            "has_residual_fake_borrow_or_fake_read": has_fake_borrow,
            "classify_pure_mir_excerpt": classify_mir.strip(),
        }

        a_lying_miri = _run_miri(
            cargo, tmp, "a_lying_deref_pure", PART_A_LYING_DEREF_PURE_UB, miri_env=miri_env
        )

        # Part B
        b_native = _compile_and_run_native(rustc, tmp, "b_handle_raw", PART_B_NON_DEREF_RECEIVER_AND_RAW_PTR)
        b_miri_sb = _run_miri(cargo, tmp, "b_handle_raw_sb", PART_B_NON_DEREF_RECEIVER_AND_RAW_PTR, miri_env=miri_env)
        b_miri_tb = _run_miri(
            cargo, tmp, "b_handle_raw_tb", PART_B_NON_DEREF_RECEIVER_AND_RAW_PTR,
            miri_env=miri_env, miri_flags="-Zmiri-tree-borrows",
        )
        b_no_ptrs = _compile_only(rustc, tmp, "b_no_ptrs", PART_B_RAW_PTR_WITHOUT_POINTERS_FEATURE)
        b_no_dyn = _compile_only(rustc, tmp, "b_no_dyn", PART_B_RECEIVER_WITHOUT_DISPATCH_FROM_DYN)
        b_dfd_two = _compile_only(rustc, tmp, "b_dfd_two", PART_B_DISPATCH_FROM_DYN_TWO_FIELD_REJECTED)
        b_dfd_reprc = _compile_only(rustc, tmp, "b_dfd_reprc", PART_B_DISPATCH_FROM_DYN_REPR_C_REJECTED)
        b_dfd_ok_native = _compile_and_run_native(rustc, tmp, "b_dfd_ok", PART_B_DISPATCH_FROM_DYN_VALID_CUSTOM_HANDLE)
        b_dfd_ok_miri = _run_miri(cargo, tmp, "b_dfd_ok_miri", PART_B_DISPATCH_FROM_DYN_VALID_CUSTOM_HANDLE, miri_env=miri_env)
        b_shadow_deref_native = _compile_and_run_native(rustc, tmp, "b_shadow_deref", PART_B_SHADOWING_DEREF_DEPTH0_WINS)
        b_shadow_deref_miri = _run_miri(cargo, tmp, "b_shadow_deref_miri", PART_B_SHADOWING_DEREF_DEPTH0_WINS, miri_env=miri_env)
        b_shadow_ext_native = _compile_and_run_native(rustc, tmp, "b_shadow_ext", PART_B_SHADOWING_INH_VS_TRAIT_EXT)
        b_shadow_ext_miri = _run_miri(cargo, tmp, "b_shadow_ext_miri", PART_B_SHADOWING_INH_VS_TRAIT_EXT, miri_env=miri_env)
        b_shadow_asym_native = _compile_and_run_native(rustc, tmp, "b_shadow_asym", PART_B_SHADOWING_ASYMMETRY_INNER_BY_VAL_WINS)
        b_shadow_asym_miri = _run_miri(cargo, tmp, "b_shadow_asym_miri", PART_B_SHADOWING_ASYMMETRY_INNER_BY_VAL_WINS, miri_env=miri_env)
        b_shadow_same_ref_err = _compile_only(rustc, tmp, "b_shadow_same_ref", PART_B_BOTH_INH_SAME_REF_AMBIGUITY)
        b_shadow_err = _compile_only(rustc, tmp, "b_shadow_err", PART_B_ANTI_SHADOWING_BY_VAL_VS_BY_REF)
        b_shadow_ref_mut_err = _compile_only(rustc, tmp, "b_shadow_ref_mut", PART_B_ANTI_SHADOWING_REF_VS_MUT_REF)

        # Part C
        c_native = _compile_and_run_native(rustc, tmp, "c_precedence", PART_C_METHOD_AUTODEREF_PRECEDENCE)
        c_miri_sb = _run_miri(cargo, tmp, "c_precedence_sb", PART_C_METHOD_AUTODEREF_PRECEDENCE, miri_env=miri_env)
        c_miri_tb = _run_miri(
            cargo, tmp, "c_precedence_tb", PART_C_METHOD_AUTODEREF_PRECEDENCE,
            miri_env=miri_env, miri_flags="-Zmiri-tree-borrows",
        )
        c_raw_no_deref = _compile_only(rustc, tmp, "c_raw_no_deref", PART_C_RAW_PTR_NO_AUTODEREF)

        # Strict assertions that every probe actually executed and produced expected verdicts
        checks = {
            "part_a_impure_rejected_E0277": a_impure["rc"] != 0 and "E0277" in a_impure["stderr"] and "DerefPure" in a_impure["stderr"],
            "part_a_std_custom_native_miri_agree": (
                a_native["compile_rc"] == 0
                and a_native["run_rc"] == 0
                and a_miri_sb["rc"] == 0
                and a_miri_tb["rc"] == 0
                and a_native["stdout"] == a_miri_sb["stdout"] == a_miri_tb["stdout"]
                and "DEREF_PAT_OK=210" in a_native["stdout"]
            ),
            "part_a_deep_fake_borrow_blocks_guard_E0510": a_guard["rc"] != 0 and "E0510" in a_guard["stderr"],
            "part_a_mixed_ctors_rejected": a_mixed["rc"] != 0 and "deref" in a_mixed["stderr"].lower(),
            "part_a_mir_emits_two_derefs_and_unreachable_no_fake_borrow": (
                a_mir["rc"] == 0
                and a_mir["classify_pure_found"]
                and a_mir["deref_call_count_in_post_cleanup_mir"] == 2
                and a_mir["has_unreachable_terminator"]
                and not a_mir["has_residual_fake_borrow_or_fake_read"]
            ),
            "part_a_lying_deref_pure_miri_catches_unreachable_ub": (
                a_lying_miri["rc"] != 0
                and "Undefined Behavior" in a_lying_miri["stderr"]
                and "unreachable" in a_lying_miri["stderr"]
            ),
            "part_b_non_deref_receiver_native_miri_agree": (
                b_native["compile_rc"] == 0
                and b_native["run_rc"] == 0
                and b_miri_sb["rc"] == 0
                and b_miri_tb["rc"] == 0
                and b_native["stdout"] == b_miri_sb["stdout"] == b_miri_tb["stdout"]
                and "HANDLE=31 RAW_PTR=40 RAW_MUT=27" in b_native["stdout"]
            ),
            "part_b_raw_ptr_gate_E0658": b_no_ptrs["rc"] != 0 and "E0658" in b_no_ptrs["stderr"],
            "part_b_dyn_compat_split_E0038": b_no_dyn["rc"] != 0 and "E0038" in b_no_dyn["stderr"],
            "part_b_dispatch_from_dyn_rejects_two_field_and_repr_c": (
                b_dfd_two["rc"] != 0 and "E0378" in b_dfd_two["stderr"]
                and b_dfd_reprc["rc"] != 0 and "E0378" in b_dfd_reprc["stderr"]
            ),
            "part_b_dispatch_from_dyn_valid_custom_handle_native_miri_agree": (
                b_dfd_ok_native["compile_rc"] == 0
                and b_dfd_ok_native["run_rc"] == 0
                and b_dfd_ok_miri["rc"] == 0
                and b_dfd_ok_native["stdout"] == b_dfd_ok_miri["stdout"] == "DYN_HANDLE_OK=142"
            ),
            "part_b_shadowing_deref_depth0_wins_native_miri_agree": (
                b_shadow_deref_native["compile_rc"] == 0
                and b_shadow_deref_native["run_rc"] == 0
                and b_shadow_deref_miri["rc"] == 0
                and b_shadow_deref_native["stdout"] == b_shadow_deref_miri["stdout"]
                and "SHADOW_TAG=222" in b_shadow_deref_native["stdout"]
            ),
            "part_b_shadowing_inh_over_ext_native_miri_agree": (
                b_shadow_ext_native["compile_rc"] == 0
                and b_shadow_ext_native["run_rc"] == 0
                and b_shadow_ext_miri["rc"] == 0
                and b_shadow_ext_native["stdout"] == b_shadow_ext_miri["stdout"]
                and "INH_OVER_EXT_TAG=222" in b_shadow_ext_native["stdout"]
            ),
            "part_b_shadowing_asymmetry_inner_by_val_wins_native_miri_agree": (
                b_shadow_asym_native["compile_rc"] == 0
                and b_shadow_asym_native["run_rc"] == 0
                and b_shadow_asym_miri["rc"] == 0
                and b_shadow_asym_native["stdout"] == b_shadow_asym_miri["stdout"]
                and "ASYM_INNER_WINS=111" in b_shadow_asym_native["stdout"]
            ),
            "part_b_both_inh_same_ref_E0034": (
                b_shadow_same_ref_err["rc"] != 0 and "E0034" in b_shadow_same_ref_err["stderr"]
            ),
            "part_b_anti_shadowing_by_val_vs_by_ref_E0034": (
                b_shadow_err["rc"] != 0 and "E0034" in b_shadow_err["stderr"]
            ),
            "part_b_anti_shadowing_ref_vs_mut_ref_E0034": (
                b_shadow_ref_mut_err["rc"] != 0 and "E0034" in b_shadow_ref_mut_err["stderr"]
            ),
            "part_c_precedence_native_miri_agree": (
                c_native["compile_rc"] == 0
                and c_native["run_rc"] == 0
                and c_miri_sb["rc"] == 0
                and c_miri_tb["rc"] == 0
                and c_native["stdout"] == c_miri_sb["stdout"] == c_miri_tb["stdout"]
                and "PICK_VAL=10" in c_native["stdout"]
            ),
            "part_c_raw_ptr_never_autoderefs_E0599": (
                c_raw_no_deref["rc"] != 0 and "E0599" in c_raw_no_deref["stderr"]
            ),
        }

        return {
            "timestamp_utc": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": rustc_ver.stdout.strip(),
            "miri_version": miri_ver.stdout.strip(),
            "part_a_deref_patterns_box_rc_string_vec_and_deref_pure_gate": {
                "impure_deref_rejected_without_deref_pure": a_impure,
                "std_and_custom_deref_pure_native": a_native,
                "std_and_custom_deref_pure_miri_stacked_borrows": a_miri_sb,
                "std_and_custom_deref_pure_miri_tree_borrows": a_miri_tb,
                "deep_fake_borrow_blocks_guard_mutation": a_guard,
                "mixed_deref_and_adt_ctors_rejected": a_mixed,
                "multi_arm_deref_pat_post_cleanup_mir": a_mir,
                "lying_deref_pure_triggers_miri_ub": a_lying_miri,
            },
            "part_b_arbitrary_self_types_receiver_vs_dyn_dispatch": {
                "non_deref_receiver_and_raw_ptr_native": b_native,
                "non_deref_receiver_and_raw_ptr_miri_stacked_borrows": b_miri_sb,
                "non_deref_receiver_and_raw_ptr_miri_tree_borrows": b_miri_tb,
                "raw_ptr_self_rejected_without_arbitrary_self_types_pointers": b_no_ptrs,
                "receiver_without_dispatch_from_dyn_breaks_dyn_trait": b_no_dyn,
                "dispatch_from_dyn_two_field_rejected": b_dfd_two,
                "dispatch_from_dyn_repr_c_rejected": b_dfd_reprc,
                "dispatch_from_dyn_valid_custom_handle_native": b_dfd_ok_native,
                "dispatch_from_dyn_valid_custom_handle_miri": b_dfd_ok_miri,
                "shadowing_deref_depth0_wins_native": b_shadow_deref_native,
                "shadowing_deref_depth0_wins_miri": b_shadow_deref_miri,
                "shadowing_inh_over_ext_native": b_shadow_ext_native,
                "shadowing_inh_over_ext_miri": b_shadow_ext_miri,
                "shadowing_asymmetry_inner_by_val_wins_native": b_shadow_asym_native,
                "shadowing_asymmetry_inner_by_val_wins_miri": b_shadow_asym_miri,
                "both_inh_same_ref_ambiguity": b_shadow_same_ref_err,
                "anti_shadowing_by_val_vs_by_ref_error": b_shadow_err,
                "anti_shadowing_ref_vs_mut_ref_error": b_shadow_ref_mut_err,
            },
            "part_c_method_autoderef_autoref_precedence_and_raw_ptr": {
                "method_probe_full_precedence_native": c_native,
                "method_probe_full_precedence_miri_stacked_borrows": c_miri_sb,
                "method_probe_full_precedence_miri_tree_borrows": c_miri_tb,
                "raw_ptr_never_autoderefs_in_method_call": c_raw_no_deref,
            },
            "summary_checks": checks,
            "all_checks_passed": all(checks.values()),
        }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=shutil.which("rustc") or "rustc")
    parser.add_argument("--cargo", default=shutil.which("cargo") or "cargo")
    parser.add_argument("--miri-sysroot", default=None)
    parser.add_argument("--out", default=None, help="Optional JSON output path")
    args = parser.parse_args(argv)

    result = run_all(args.rustc, args.cargo, args.miri_sysroot)
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0 if result["all_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
