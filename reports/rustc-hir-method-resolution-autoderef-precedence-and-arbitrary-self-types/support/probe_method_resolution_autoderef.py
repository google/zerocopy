#!/usr/bin/env python3
"""Empirical rustc + MIR + Miri probe suite for HIR method resolution,
autoderef-step-first precedence, E0034 ambiguity vs. cross-step shadowing,
arbitrary_self_types Receiver dispatch, and zerocopy receiver patterns.

Every compilation, MIR emission, native execution, and Miri execution is run
live inside a temporary directory with zero hardcoded compiler outputs.
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


def _find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / name
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError(f"required tool {name!r} not found in PATH or ~/.cargo/bin")


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
    out = text.replace(str(tmp_dir), "<TMP>")
    home = str(Path.home())
    if home:
        out = out.replace(home, "<HOME>")
    return out


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
        "edition": "2024",
        "crate_type": crate_type,
        "extra_args": extra_args or [],
        "compile_returncode": res.returncode,
        "compile_stdout": _sanitize(res.stdout, tmp_dir).strip(),
        "compile_stderr": _sanitize(res.stderr, tmp_dir).strip(),
    }


def _compile_and_run(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    exe = tmp_dir / f"{name}_bin"
    src.write_text(code, encoding="utf-8")
    cmd = [rustc, "--edition=2024", str(src), "-o", str(exe)]
    if extra_args:
        cmd.extend(extra_args)
    comp = _run(cmd, cwd=tmp_dir)
    if comp.returncode != 0:
        return {
            "edition": "2024",
            "extra_args": extra_args or [],
            "compile_returncode": comp.returncode,
            "compile_stdout": _sanitize(comp.stdout, tmp_dir).strip(),
            "compile_stderr": _sanitize(comp.stderr, tmp_dir).strip(),
            "run_returncode": None,
            "run_stdout": "",
            "run_stderr": "",
        }
    run = _run([str(exe)], cwd=tmp_dir)
    return {
        "edition": "2024",
        "extra_args": extra_args or [],
        "compile_returncode": 0,
        "compile_stdout": _sanitize(comp.stdout, tmp_dir).strip(),
        "compile_stderr": _sanitize(comp.stderr, tmp_dir).strip(),
        "run_returncode": run.returncode,
        "run_stdout": _sanitize(run.stdout, tmp_dir).strip(),
        "run_stderr": _sanitize(run.stderr, tmp_dir).strip(),
    }


def _emit_mir_excerpt(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    fn_markers: list[str],
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    mir_path = tmp_dir / f"{name}.mir"
    src.write_text(code, encoding="utf-8")
    comp = _run(
        [
            rustc,
            "--edition=2024",
            "--crate-type=lib",
            "--emit=mir",
            "-C",
            "opt-level=0",
            str(src),
            "-o",
            str(mir_path),
        ],
        cwd=tmp_dir,
    )
    if comp.returncode != 0:
        return {
            "compile_returncode": comp.returncode,
            "compile_stderr": _sanitize(comp.stderr, tmp_dir).strip(),
            "mir_excerpts": {},
        }
    mir_text = _sanitize(mir_path.read_text(encoding="utf-8"), tmp_dir)
    excerpts: dict[str, str] = {}
    for marker in fn_markers:
        # Bounded per-function block scan
        blocks = mir_text.split("\n\nfn ")
        matched = ""
        for idx, blk in enumerate(blocks):
            text_blk = blk if idx == 0 else "fn " + blk
            if f"fn {marker}(" in text_blk or f"fn {marker}::" in text_blk:
                end_pos = text_blk.find("\n}\n")
                matched = text_blk[: end_pos + 3] if end_pos != -1 else text_blk
                break
        excerpts[marker] = matched.strip()
    return {
        "compile_returncode": 0,
        "compile_stderr": _sanitize(comp.stderr, tmp_dir).strip(),
        "mir_excerpts": excerpts,
    }


def _prepare_miri_env(cargo: str, tmp_dir: Path) -> dict[str, str] | None:
    env = dict(os.environ)
    if env.get("MIRI_SYSROOT"):
        return env
    probe_dir = tmp_dir / "_miri_setup_probe"
    (probe_dir / "src").mkdir(parents=True, exist_ok=True)
    (probe_dir / "Cargo.toml").write_text(
        '[package]\nname = "miri_setup_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (probe_dir / "src" / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
    test = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=180)
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
        setup = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=240)
        if setup.returncode == 0:
            return env
    return None


def _run_miri(
    cargo: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    miri_env: dict[str, str],
    miri_flags: str = "",
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
    res = _run([cargo, "miri", "run", "-q"], cwd=proj, env=env, timeout=180)
    return {
        "rc": res.returncode,
        "stdout": _sanitize(res.stdout, proj).strip(),
        "stderr": _sanitize(res.stderr, proj).strip(),
    }


# ---------------------------------------------------------------------------
# Probe programs: Group A — Autoderef-Step-First & Per-Step Adjustment Order
# ---------------------------------------------------------------------------

PROBE_A_PRECEDENCE_MATRIX = r"""
use std::ops::{Deref, DerefMut};

struct Inner(u32);
impl Inner {
    fn trait_vs_inherent(&self) -> &'static str { "Inner::inherent(&self)" }
    fn only_inner_mut(&mut self) -> &'static str { "Inner::mut(&mut self)" }
    fn val_vs_ref(self) -> &'static str { "Inner::inherent(self)" }
}

struct Outer(Inner);
impl Deref for Outer {
    type Target = Inner;
    fn deref(&self) -> &Inner { &self.0 }
}
impl DerefMut for Outer {
    fn deref_mut(&mut self) -> &mut Inner { &mut self.0 }
}

trait OuterTrait {
    fn trait_vs_inherent(&self) -> &'static str;
    fn ref_vs_mut(&self) -> &'static str;
}
impl OuterTrait for Outer {
    fn trait_vs_inherent(&self) -> &'static str { "OuterTrait::trait(&self)" }
    fn ref_vs_mut(&self) -> &'static str { "OuterTrait::trait(&self)" }
}

trait OuterByVal {
    fn val_vs_inherent_ref(self) -> &'static str;
}
impl OuterByVal for Outer {
    fn val_vs_inherent_ref(self) -> &'static str { "OuterByVal::trait(self)" }
}

impl Outer {
    fn val_vs_ref(&self) -> &'static str { "Outer::inherent(&self)" }
    fn val_vs_inherent_ref(&self) -> &'static str { "Outer::inherent(&self)" }
    fn ref_vs_mut(&mut self) -> &'static str { "Outer::inherent(&mut self)" }
    fn only_mut(&mut self) -> &'static str { "Outer::only_mut(&mut self)" }
}

#[derive(Clone, Copy)]
struct RefStep(u32);
impl RefStep {
    fn by_val(self) -> &'static str { "RefStep::by_val(self)" }
    fn m_val_or_ref(self) -> &'static str { "RefStep::by_val(self)" }
}
trait RefStepRef {
    fn by_val(&self) -> &'static str;
    fn m_val_or_ref(&self) -> &'static str;
    fn reborrow_or_ref(&self) -> &'static str;
}
impl RefStepRef for RefStep {
    fn by_val(&self) -> &'static str { "RefStepRef::&self" }
    fn m_val_or_ref(&self) -> &'static str { "RefStepRef::&self" }
    fn reborrow_or_ref(&self) -> &'static str { "RefStepRef::&self" }
}
trait RefStepMut {
    fn reborrow_or_ref(&mut self) -> &'static str;
}
impl RefStepMut for RefStep {
    fn reborrow_or_ref(&mut self) -> &'static str { "RefStepMut::&mut self" }
}

struct OwnedArr([u8; 4]);
impl Deref for OwnedArr {
    type Target = [u8; 4];
    fn deref(&self) -> &[u8; 4] { &self.0 }
}

trait ArrayOverride {
    fn len(&self) -> usize;
    fn custom_arr(&self) -> &'static str;
}
impl ArrayOverride for [u8; 4] {
    fn len(&self) -> usize { 404 }
    fn custom_arr(&self) -> &'static str { "ArrayOverride::[u8;4]" }
}
trait SliceFallback {
    fn custom_arr(&self) -> &'static str;
}
impl SliceFallback for [u8] {
    fn custom_arr(&self) -> &'static str { "SliceFallback::[u8]" }
}

trait WhereBound {
    fn where_vs_ext(&self) -> &'static str;
}
impl WhereBound for Inner {
    fn where_vs_ext(&self) -> &'static str { "WhereBound::inherent_priority" }
}
trait BlanketExt {
    fn where_vs_ext(&self) -> &'static str;
}
impl<T> BlanketExt for T {
    fn where_vs_ext(&self) -> &'static str { "BlanketExt::extension" }
}
fn check_where_beats_ext<T: WhereBound>(x: &T) -> &'static str {
    // `WhereClauseCandidate` is assembled in `inherent_candidates` (`probe.rs:1080`),
    // beating `BlanketExt` in `extension_candidates` at the same `(step, adjustment)`.
    x.where_vs_ext()
}

fn main() {
    let mut o1 = Outer(Inner(7));
    // Step 0 extension &self beats Step 1 inherent &self
    let c_step0_trait_vs_step1_inh = o1.trait_vs_inherent();
    // Step 0 inherent &self beats Step 1 inherent self
    let c_step0_inh_vs_step1_val = o1.val_vs_ref();
    // Step 0 extension by-value beats Step 0 inherent &self
    let c_step0_val_trait_vs_inh_ref = Outer(Inner(8)).val_vs_inherent_ref();
    // Step 0 extension &self beats Step 0 inherent &mut self
    let mut o2 = Outer(Inner(9));
    let c_step0_ref_trait_vs_mut_inh = o2.ref_vs_mut();
    // Step 0 inherent &mut self
    let c_step0_mut = o2.only_mut();
    // Step 1 inherent &mut self via DerefMut
    let c_step1_mut = o2.only_inner_mut();

    // Owned RefStep: step 0 by_val beats step 0 &self
    let rs_owned = RefStep(1);
    let c_owned_val = rs_owned.by_val();
    // Owned mut RefStep: step 0 &self beats step 0 &mut self
    let mut rs_owned2 = RefStep(2);
    let c_owned_ref_vs_mut = rs_owned2.reborrow_or_ref();
    // &mut RefStep: step 0 by-value (&mut RefStep) matches &mut self (reborrow!), beating step 1 &self
    let mut rs_val = RefStep(3);
    let r_mut: &mut RefStep = &mut rs_val;
    let c_mutref_reborrow = r_mut.reborrow_or_ref();
    // Confirm `r_mut` was reborrowed rather than moved (still usable after method call):
    let c_mutref_still_usable = r_mut.reborrow_or_ref();
    // &mut RefStep (Copy) with `self` vs `&self`: step 0 (&mut RefStep) fails both, step 1 (RefStep) picks `by_val(self)` over `&self`
    let c_mutref_step1_val_beats_ref = r_mut.m_val_or_ref();
    // &RefStep: step 0 by-value (&RefStep) matches &self
    let r_imm: &RefStep = &rs_owned;
    let c_immref = r_imm.reborrow_or_ref();

    // Array vs slice unsizing:
    // OwnedArr -> Deref [u8;4] -> trailing unsize [u8], trait ArrayOverride wins at step 1 before unsize step 2
    let oa = OwnedArr([1, 2, 3, 4]);
    let oa_slice_len = <[u8]>::len(&*oa);
    let oa_trait_len = oa.len();
    let oa_arr_override = oa.custom_arr();
    // [u8; 5] has no ArrayOverride impl, so falls through step 0 to trailing unsize step 1 (`[u8]::len`)
    let box_len = Box::new([1u8, 2, 3, 4, 5]).len();
    let where_beats_ext = check_where_beats_ext(&Inner(1));

    println!(
        "A1={} | A2={} | A3={} | A4={} | A5={} | A6={} | V1={} | V2={} | V3={} | V3B={} | V4={} | V5={} | OA_SLICE={} | OA_TRAIT={} | OA_OVR={} | BOX_LEN={} | W={}",
        c_step0_trait_vs_step1_inh,
        c_step0_inh_vs_step1_val,
        c_step0_val_trait_vs_inh_ref,
        c_step0_ref_trait_vs_mut_inh,
        c_step0_mut,
        c_step1_mut,
        c_owned_val,
        c_owned_ref_vs_mut,
        c_mutref_reborrow,
        c_mutref_still_usable,
        c_mutref_step1_val_beats_ref,
        c_immref,
        oa_slice_len,
        oa_trait_len,
        oa_arr_override,
        box_len,
        where_beats_ext
    );
}
"""

PROBE_A_PROBE_IGNORES_PLACE_MUTABILITY_E0596 = r"""
use core::ops::Deref;

pub struct Inner;
impl Inner {
    pub fn m(&self) -> u32 { 1 }
}

pub struct Outer(pub Inner);
impl Deref for Outer {
    type Target = Inner;
    fn deref(&self) -> &Inner { &self.0 }
}
impl Outer {
    pub fn m(&mut self) -> u32 { 2 }
}

pub fn call_on_immutable() -> u32 {
    let o = Outer(Inner);
    // Probe selects step-0 `Outer::m(&mut self)` without checking place mutability,
    // failing later with E0596 instead of falling back to step-1 `Inner::m(&self)`.
    o.m()
}
"""

PROBE_A_RAW_PTR_NO_AUTODEREF_E0599 = r"""
pub struct Pointee;
impl Pointee {
    pub fn m(&self) -> u32 { 42 }
}

pub fn test_raw(p: *const Pointee) -> u32 {
    p.m()
}
"""

PROBE_A_RAW_PTR_CONST_COERCION_AND_NO_CHAINED_AUTOREF = r"""
#![feature(arbitrary_self_types_pointers)]

pub struct Target(pub u32);
impl Target {
    pub fn only_const(self: *const Self) -> u32 {
        unsafe { (*self).0 }
    }
    pub fn mut_or_const(self: *mut Self) -> &'static str { "by_mut_ptr" }
}
trait ConstPtrTrait {
    fn on_const_ptr_ref(&self) -> u32;
}
impl ConstPtrTrait for *const Target {
    fn on_const_ptr_ref(&self) -> u32 { 99 }
}

pub fn call_negative(mut t: Target) -> u32 {
    let p: *mut Target = &mut t;
    // Probe checks EITHER ToConstPtr OR Autoref at a step, never both chained:
    // `*mut Target` converts to `*const Target` via ToConstPtr, NOT `&*const Target`.
    p.on_const_ptr_ref()
}
"""

PROBE_A_RAW_PTR_CONST_COERCION_POSITIVE = r"""
#![feature(arbitrary_self_types_pointers)]

struct Target(u32);
impl Target {
    fn only_const(self: *const Self) -> u32 {
        unsafe { (*self).0 }
    }
    fn prefer_mut(self: *mut Self) -> &'static str { "mut_ptr_by_val" }
}
trait FallbackConst {
    fn prefer_mut(self: *const Self) -> &'static str;
}
impl FallbackConst for Target {
    fn prefer_mut(self: *const Self) -> &'static str { "const_ptr_trait" }
}

fn main() {
    let mut t = Target(77);
    let p: *mut Target = &mut t;
    // ToConstPtr: *mut Target -> *const Target
    let c = p.only_const();
    // by_value (*mut Self) beats ToConstPtr (*const Self)
    let w = p.prefer_mut();
    // Standard inherent raw-ptr methods without arbitrary_self_types_pointers:
    let nonnull_cast = p.cast::<u8>();
    assert!(!nonnull_cast.is_null());
    println!("TO_CONST_PTR={} PREFER_MUT={}", c, w);
}
"""

PROBE_A_UNSIZE_SKIPS_BY_VALUE_AND_CONST_PTR = r"""
#![feature(arbitrary_self_types_pointers)]

pub trait SlicePtr {
    fn slice_const_ptr(self: *const Self) -> usize;
}
impl SlicePtr for [u8] {
    fn slice_const_ptr(self: *const Self) -> usize { 123 }
}

pub fn test_array_to_slice_const_ptr() -> usize {
    let mut arr = [1u8, 2, 3, 4];
    let p: *mut [u8; 4] = &mut arr;
    // `step.unsize` skips both `pick_by_value_method` and `pick_const_ptr_method`,
    // and array-to-slice unsizing requires Autoref (`&[u8]` / `&mut [u8]`).
    p.slice_const_ptr()
}
"""

PROBE_A_PIN_REBORROW = r"""
#![feature(pin_ergonomics)]
use core::pin::Pin;

struct Pinned(u32);
impl Pinned {
    fn get_imm(self: Pin<&Self>) -> u32 { self.0 }
}

fn main() {
    let mut val = Pinned(55);
    let mut p: Pin<&mut Pinned> = Pin::new(&mut val);
    // `pick_reborrow_pin_method` reborrows `Pin<&mut Pinned>` -> `Pin<&Pinned>`
    let a = p.get_imm();
    let b = p.get_imm();
    println!("PIN_REBORROW={}", a + b);
}
"""

# ---------------------------------------------------------------------------
# Probe programs: Group B — E0034 Ambiguity, Collapsing, Cross-Step Shadowing,
# and arbitrary_self_types (Receiver + Anti-Shadowing)
# ---------------------------------------------------------------------------

PROBE_B_SAME_STEP_TRAIT_AMBIGUITY_E0034 = r"""
pub struct S;
pub trait T1 { fn collide(&self) -> u32 { 1 } }
pub trait T2 { fn collide(&self) -> u32 { 2 } }
impl T1 for S {}
impl T2 for S {}

pub fn run(s: S) -> u32 {
    s.collide()
}
"""

PROBE_B_SAME_STEP_INHERENT_AMBIGUITY_E0034 = r"""
pub struct Gen<A, B>(pub A, pub B);
impl<T> Gen<T, u32> { pub fn dup(&self) -> u32 { 1 } }
impl<U> Gen<u32, U> { pub fn dup(&self) -> u32 { 2 } }
// Extension trait in scope must NOT suppress or participate in inherent ambiguity:
pub trait ExtDup { fn dup(&self) -> u32 { 3 } }
impl ExtDup for Gen<u32, u32> {}

pub fn run(g: Gen<u32, u32>) -> u32 {
    g.dup()
}
"""

PROBE_B_WHERE_CLAUSE_AMBIGUITY_E0034 = r"""
pub trait T1 { fn ambig(&self) -> u32 { 1 } }
pub trait T2 { fn ambig(&self) -> u32 { 2 } }
// `WhereClauseCandidate`s are placed in `inherent_candidates` (`probe.rs:1080`),
// triggering `E0034` cleanly with zero `E0592` coherence error.
pub fn run<T: T1 + T2>(x: &T) -> u32 {
    x.ambig()
}
"""

PROBE_B_OBJECT_CANDIDATE_AMBIGUITY_E0034 = r"""
pub trait T1 { fn ambig(&self) -> u32 { 1 } }
pub trait T2 { fn ambig(&self) -> u32 { 2 } }
pub trait Combined: T1 + T2 {}
// `ObjectCandidate`s for supertraits are placed in `inherent_candidates` (`probe.rs:1053`),
// triggering `E0034` cleanly with zero `E0592` coherence error.
pub fn run(x: &dyn Combined) -> u32 {
    x.ambig()
}
"""

PROBE_B_CROSS_STEP_TRAIT_SHADOWS_INNER_INHERENT = r"""
use core::ops::Deref;

struct Inner;
impl Inner {
    fn sh(&self) -> &'static str { "Inner_inherent_step1" }
}

struct Outer(Inner);
impl Deref for Outer {
    type Target = Inner;
    fn deref(&self) -> &Inner { &self.0 }
}
trait TOuter {
    fn sh(&self) -> &'static str { "TOuter_step0" }
}
impl TOuter for Outer {}

fn main() {
    let o = Outer(Inner);
    println!("CROSS_STEP={}", o.sh());
}
"""

PROBE_B_INFERENCE_DEFERRED_TRAIT_COLLAPSE = r"""
trait Convert {
    fn extract(&self) -> u64;
}
struct Wrap<T>(T);
impl Convert for Wrap<i32> {
    fn extract(&self) -> u64 { self.0 as u64 }
}
impl Convert for Wrap<u64> {
    fn extract(&self) -> u64 { self.0 }
}

fn make<T>(x: T) -> Wrap<T> { Wrap(x) }
fn expect_i32(_: &Wrap<i32>) {}

fn main() {
    // At the method-call site, `w` has type `Wrap<?0>` matching two `TraitCandidate`s
    // of the SAME trait `Convert`, so `collapse_candidates_to_trait_pick` collapses
    // them into a single `TraitPick` rather than emitting E0034.
    let w = make(Default::default());
    let val = w.extract();
    expect_i32(&w);
    println!("COLLAPSE_SAME_TRAIT={}", val);
}
"""

PROBE_B_SUPERTRAIT_WITHOUT_FEATURE_E0034 = r"""
pub trait Super { fn item(&self) -> u32 { 1 } }
pub trait Sub: Super { fn item(&self) -> u32 { 2 } }
pub struct Impl;
impl Super for Impl {}
impl Sub for Impl {}

pub fn call_sub(x: &Impl) -> u32 {
    x.item()
}
"""

PROBE_B_SUPERTRAIT_WITH_FEATURE = r"""
#![feature(supertrait_item_shadowing)]
#![warn(resolving_to_items_shadowing_supertrait_items)]
trait Super { fn item(&self) -> u32 { 1 } }
trait Sub: Super { fn item(&self) -> u32 { 2 } }
struct Impl;
impl Super for Impl {}
impl Sub for Impl {}

fn main() {
    let x = Impl;
    println!("SUPERTRAIT_SHADOW={}", x.item());
}
"""

PROBE_B_ARBITRARY_SELF_RECEIVER_VS_DEREF = r"""
#![feature(arbitrary_self_types)]
use core::ops::{Deref, Receiver};

struct SmartOnly<T>(T);
impl<T> Receiver for SmartOnly<T> {
    type Target = T;
}

struct SmartDeref<T>(T);
impl<T> Deref for SmartDeref<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

struct Inner(u32);
impl Inner {
    fn via_smart(self: &SmartOnly<Self>) -> u32 { self.0.0 + 7 }
    fn via_smart_val(self: SmartOnly<Self>) -> u32 { self.0.0 + 17 }
    fn via_deref(&self) -> u32 { self.0 + 9 }
}

fn main() {
    let a = SmartOnly(Inner(100));
    let b = SmartDeref(Inner(200));
    let r1 = a.via_smart();
    let r2 = a.via_smart_val();
    let r3 = b.via_deref();
    println!("SMART_REF={} SMART_VAL={} DEREF_FALLBACK={}", r1, r2, r3);
}
"""

PROBE_B_RECEIVER_ONLY_CANNOT_AUTOREF_TARGET_E0599 = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartOnly<T>(pub T);
impl<T> Receiver for SmartOnly<T> {
    type Target = T;
}
pub struct TargetVal(pub u32);
impl TargetVal {
    pub fn needs_deref(&self) -> u32 { self.0 }
}

pub fn call_missing(s: SmartOnly<TargetVal>) -> u32 {
    s.needs_deref()
}
"""

PROBE_B_ANTI_SHADOWING_VAL_VS_REF_E0034 = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartPtr<T>(pub T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    pub fn collide(self) -> u32 { 1 }
}

pub struct Target;
impl Target {
    pub fn collide(self: &SmartPtr<Self>) -> u32 { 2 }
}

pub fn run(p: SmartPtr<Target>) -> u32 {
    p.collide()
}
"""

PROBE_B_ANTI_SHADOWING_REF_VS_MUT_E0034 = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

pub struct SmartPtr<T>(pub T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    pub fn collide(&self) -> u32 { 1 }
}

pub struct Target;
impl Target {
    pub fn collide(self: &mut SmartPtr<Self>) -> u32 { 2 }
}

pub fn run(mut p: SmartPtr<Target>) -> u32 {
    p.collide()
}
"""

PROBE_B_ANTI_SHADOWING_ASYMMETRY_POINTEE_SHADOWS_SMART = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

struct SmartPtr<T>(T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    fn asym(&self) -> &'static str { "SmartPtr::&self" }
}

struct Target;
impl Target {
    // receiver_steps = 1 (pointee) shadows receiver_steps = 0 (SmartPtr) silently!
    fn asym(self: SmartPtr<Self>) -> &'static str { "Target::SmartPtr<Self>" }
}

fn main() {
    let p = SmartPtr(Target);
    println!("ASYM_POINTEE_WINS={}", p.asym());
}
"""

PROBE_B_ANTI_SHADOWING_DOUBLE_REF_NICHE_BYPASS = r"""
#![feature(arbitrary_self_types)]
use core::ops::Receiver;

struct SmartPtr<T>(T);
impl<T> Receiver for SmartPtr<T> {
    type Target = T;
}
impl<T> SmartPtr<T> {
    // At receiver `&SmartPtr<Target>`, `pick_by_value_method` matches `&self` and increments
    // `pick.autoderefs` from 0 to 1, while passing `step` (`step.autoderefs == 0`) to
    // `check_for_shadowed_autorefd_method`, so `0 == 1` is false and Target is NOT flagged.
    fn niche(&self) -> &'static str { "SmartPtr::&self" }
}

struct Target;
impl Target {
    fn niche(self: &&SmartPtr<Self>) -> &'static str { "Target::&&SmartPtr<Self>" }
}

fn main() {
    let inner = SmartPtr(Target);
    let r: &SmartPtr<Target> = &inner;
    println!("DOUBLE_REF_NICHE={}", r.niche());
}
"""

PROBE_B_ANTI_SHADOWING_MUT_PTR_EXEMPTION = r"""
#![feature(arbitrary_self_types, arbitrary_self_types_pointers)]
use core::ops::Receiver;

struct RawWrap<T>(*mut T);
impl<T> Receiver for RawWrap<T> {
    type Target = T;
}
impl<T> RawWrap<T> {
    // `pick_const_ptr_method` does not invoke `check_for_shadowed_autorefd_method`,
    // and `check_for_shadowed_autorefd_method` checks only `[Not, Mut]` autorefs, not `ToConstPtr`.
    fn ptr_shadow(self: *mut Self) -> &'static str { "RawWrap::*mut" }
}

struct Target;
impl Target {
    fn ptr_shadow(self: *const RawWrap<Self>) -> &'static str { "Target::*const_RawWrap" }
}

fn main() {
    let mut t = Target;
    let mut w = RawWrap(&mut t as *mut Target);
    let p: *mut RawWrap<Target> = &mut w;
    println!("MUT_PTR_EXEMPT={}", p.ptr_shadow());
}
"""

# ---------------------------------------------------------------------------
# Probe programs: Group C — zerocopy First-Customer Patterns + MIR Inspection
# ---------------------------------------------------------------------------

PROBE_C_ZEROCOPY_PATTERNS = r"""
use core::cell::Cell;
use core::marker::PhantomData;
use core::ops::Deref;

// 1. Minimal standalone replica of zerocopy's `Ptr<'a, T, I>` (no `Deref` impl):
struct Shared;
struct Exclusive;
struct Ptr<'a, T: ?Sized, I> {
    raw: *mut T,
    _marker: PhantomData<(&'a T, I)>,
}
impl<'a, T: ?Sized> Copy for Ptr<'a, T, Shared> {}
impl<'a, T: ?Sized> Clone for Ptr<'a, T, Shared> {
    fn clone(&self) -> Self { *self }
}
impl<'a, T: ?Sized> Ptr<'a, T, Shared> {
    fn from_ref(r: &'a T) -> Self {
        Self { raw: r as *const T as *mut T, _marker: PhantomData }
    }
}
impl<'a, T: ?Sized> Ptr<'a, T, Exclusive> {
    fn from_mut(r: &'a mut T) -> Self {
        Self { raw: r as *mut T, _marker: PhantomData }
    }
}
impl<'a, T: ?Sized, I> Ptr<'a, T, I> {
    // Intentionally takes `self` by value, never implementing `Deref`
    fn as_ref(self) -> &'a T {
        unsafe { &*self.raw }
    }
    fn reborrow(&mut self) -> Ptr<'_, T, I> {
        Ptr { raw: self.raw, _marker: PhantomData }
    }
}
// Even if an extension trait defines `as_ref(&self)` on `Ptr`, `Ptr::as_ref(self)`
// wins unambiguously at step 0 `by_value` before `Autoref(Not)`:
trait InnerConflict {
    fn as_ref(&self) -> &'static [u8];
}
impl<'a, T: ?Sized, I> InnerConflict for Ptr<'a, T, I> {
    fn as_ref(&self) -> &'static [u8] { b"trait_conflict" }
}

// 2. Minimal standalone replica of zerocopy's `Unalign<T>`:
trait Unaligned {}
impl<const N: usize> Unaligned for [u8; N] {}

#[repr(C, packed)]
struct Unalign<T>(T);
impl<T: Copy> Unalign<T> {
    fn get(&self) -> T {
        let Unalign(v) = *self;
        v
    }
}
impl<T: Unaligned> Deref for Unalign<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*(&raw const self.0) }
    }
}
// Demonstrate that `Unalign::get(&self)` at step 0 shadows any trait/referent method at step >= 1
trait ReferentGet {
    fn get(&self) -> [u8; 4];
}
impl ReferentGet for [u8; 4] {
    fn get(&self) -> [u8; 4] { [99, 99, 99, 99] }
}

// 3. Minimal standalone replica of zerocopy's `ReadOnly<T>`:
trait Immutable {}
impl<const N: usize> Immutable for [u8; N] {}

#[repr(transparent)]
struct ReadOnly<T: ?Sized>(T);
impl<T> ReadOnly<T> {
    const fn new(t: T) -> Self { Self(t) }
    fn into_inner(r: Self) -> T { r.0 }
}
impl<T: ?Sized + Immutable> Deref for ReadOnly<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}
impl<T: ?Sized + Immutable> AsRef<T> for ReadOnly<T> {
    fn as_ref(&self) -> &T { self.deref() }
}

fn main() {
    let arr = [1u8, 2, 3, 4];
    let p_shared = Ptr::from_ref(&arr);
    // `Ptr<Shared>` is Copy, so `as_ref(self)` copies it and keeps `p_shared` usable:
    let s1 = p_shared.as_ref();
    let s2 = p_shared.as_ref();
    assert_eq!(s1, s2);

    let mut mut_arr = [1u8, 2, 3, 4];
    let mut p_excl = Ptr::from_mut(&mut mut_arr);
    // `reborrow(&mut self)` resolves at step 0 Autoref(Mut), leaving `p_excl` usable after rb dies:
    let rb = p_excl.reborrow().as_ref()[0];
    let consumed = p_excl.as_ref();

    let u = Unalign([10u8, 20, 30, 40]);
    let u_get = u.get();
    // Step 0 (`Unalign`) -> Step 1 (`[u8; 4]` via Deref) -> Step 2 (`[u8]` via unsize:true)
    let u_len = u.len();

    let ro = ReadOnly::new([5u8, 6, 7, 8]);
    // Step 0 extension `AsRef::as_ref(&self)` (no `&self` inherent method on ReadOnly!)
    let ro_as_ref_copy: [u8; 4] = *ro.as_ref();
    // Step 0 (`ReadOnly`) -> Step 1 (`[u8; 4]` via Deref) -> Step 2 (`[u8]` via unsize:true)
    let ro_len = ro.len();
    let ro_inner = ReadOnly::into_inner(ro);

    // Ensure Cell isn't dropped unused
    let _c = ReadOnly::new(Cell::new(0u8));

    println!(
        "PTR={:?} RB={} CONSUMED={:?} UNALIGN_GET={:?} UNALIGN_LEN={} RO_AS_REF={:?} RO_LEN={} RO_INNER={:?}",
        s1, rb, consumed, u_get, u_len, ro_as_ref_copy, ro_len, ro_inner
    );
}
"""

PROBE_C_ZEROCOPY_CONDITIONAL_DEREF_UNALIGNED_E0599 = r"""
use core::ops::Deref;

pub trait Unaligned {}
#[repr(C, packed)]
pub struct Unalign<T>(pub T);
impl<T: Copy> Unalign<T> {
    pub fn get(&self) -> T {
        let Unalign(v) = *self;
        v
    }
}
impl<T: Unaligned> Deref for Unalign<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*(&raw const self.0) }
    }
}

pub fn fail_unaligned_deref(u: &Unalign<[u32; 4]>) -> usize {
    let _ok = u.get();
    // `[u32; 4]: !Unaligned`, so `Unalign<[u32; 4]>` stops at step 0 and cannot unsize-call `.len()`
    u.len()
}
"""

PROBE_C_ZEROCOPY_CONDITIONAL_DEREF_IMMUTABLE_E0599 = r"""
use core::cell::Cell;
use core::ops::Deref;

pub trait Immutable {}
#[repr(transparent)]
pub struct ReadOnly<T: ?Sized>(pub T);
impl<T: ?Sized + Immutable> Deref for ReadOnly<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

pub fn fail_interior_mut_deref(r: &ReadOnly<Cell<u8>>) -> u8 {
    // `Cell<u8>: !Immutable`, so `ReadOnly<Cell<u8>>` cannot autoderef to `Cell::get(&self)`
    r.get()
}
"""

PROBE_C_ZEROCOPY_PTR_NO_DEREF_TO_REFERENT_E0599 = r"""
use core::marker::PhantomData;
pub struct Ptr<'a, T: ?Sized> {
    raw: *const T,
    _marker: PhantomData<&'a T>,
}
impl<'a, T: ?Sized> Ptr<'a, T> {
    pub fn as_ref(self) -> &'a T { unsafe { &*self.raw } }
}

pub fn fail_ptr_len(p: Ptr<'_, [u8; 4]>) -> usize {
    // `Ptr` intentionally does NOT implement `Deref`, so referent `.len()` does not resolve
    p.len()
}
"""

PROBE_C_MIR_INSPECTION = r"""
use core::ops::Deref;

pub struct UnalignLike(pub [u8; 4]);
impl Deref for UnalignLike {
    type Target = [u8; 4];
    fn deref(&self) -> &[u8; 4] { &self.0 }
}

pub fn mir_array_unsize_len(a: &[u8; 4]) -> usize {
    a.len()
}

pub fn mir_deref_then_unsize_len(u: &UnalignLike) -> usize {
    u.len()
}

pub struct PtrLike<'a, T: ?Sized>(pub *const T, pub core::marker::PhantomData<&'a T>);
impl<'a, T: ?Sized> PtrLike<'a, T> {
    pub fn as_ref(self) -> &'a T { unsafe { &*self.0 } }
    pub fn reborrow(&mut self) -> PtrLike<'_, T> {
        PtrLike(self.0, core::marker::PhantomData)
    }
}

pub fn mir_ptr_reborrow_and_as_ref(mut p: PtrLike<'_, [u8; 4]>) -> usize {
    p.reborrow().as_ref().len()
}
"""


def run_all(output_path: Path, *, with_miri: bool = True) -> dict[str, Any]:
    rustc = _find_tool("rustc")
    cargo = _find_tool("cargo")

    rustc_ver = _run([rustc, "--version", "--verbose"]).stdout.strip()
    commit_hash = ""
    for line in rustc_ver.splitlines():
        if line.startswith("commit-hash:"):
            commit_hash = line.split(":", 1)[1].strip()

    with tempfile.TemporaryDirectory() as td:
        tmp_dir = Path(td)

        # Group A
        a_matrix = _compile_and_run(rustc, tmp_dir, "a_matrix", PROBE_A_PRECEDENCE_MATRIX)
        a_mut_e0596 = _compile_only(
            rustc, tmp_dir, "a_mut_e0596", PROBE_A_PROBE_IGNORES_PLACE_MUTABILITY_E0596
        )
        a_raw_e0599 = _compile_only(
            rustc, tmp_dir, "a_raw_e0599", PROBE_A_RAW_PTR_NO_AUTODEREF_E0599
        )
        a_raw_const_neg = _compile_only(
            rustc,
            tmp_dir,
            "a_raw_const_neg",
            PROBE_A_RAW_PTR_CONST_COERCION_AND_NO_CHAINED_AUTOREF,
        )
        a_raw_const_pos = _compile_and_run(
            rustc, tmp_dir, "a_raw_const_pos", PROBE_A_RAW_PTR_CONST_COERCION_POSITIVE
        )
        a_unsize_skip = _compile_only(
            rustc, tmp_dir, "a_unsize_skip", PROBE_A_UNSIZE_SKIPS_BY_VALUE_AND_CONST_PTR
        )
        a_pin_reborrow = _compile_and_run(rustc, tmp_dir, "a_pin_reborrow", PROBE_A_PIN_REBORROW)

        # Group B
        b_trait_e0034 = _compile_only(
            rustc, tmp_dir, "b_trait_e0034", PROBE_B_SAME_STEP_TRAIT_AMBIGUITY_E0034
        )
        b_inh_e0034 = _compile_only(
            rustc, tmp_dir, "b_inh_e0034", PROBE_B_SAME_STEP_INHERENT_AMBIGUITY_E0034
        )
        b_where_e0034 = _compile_only(
            rustc, tmp_dir, "b_where_e0034", PROBE_B_WHERE_CLAUSE_AMBIGUITY_E0034
        )
        b_obj_e0034 = _compile_only(
            rustc, tmp_dir, "b_obj_e0034", PROBE_B_OBJECT_CANDIDATE_AMBIGUITY_E0034
        )
        b_cross_step = _compile_and_run(
            rustc, tmp_dir, "b_cross_step", PROBE_B_CROSS_STEP_TRAIT_SHADOWS_INNER_INHERENT
        )
        b_trait_collapse = _compile_and_run(
            rustc, tmp_dir, "b_trait_collapse", PROBE_B_INFERENCE_DEFERRED_TRAIT_COLLAPSE
        )
        b_super_e0034 = _compile_only(
            rustc, tmp_dir, "b_super_e0034", PROBE_B_SUPERTRAIT_WITHOUT_FEATURE_E0034
        )
        b_super_feat = _compile_and_run(
            rustc, tmp_dir, "b_super_feat", PROBE_B_SUPERTRAIT_WITH_FEATURE
        )
        b_arb_pos = _compile_and_run(
            rustc, tmp_dir, "b_arb_pos", PROBE_B_ARBITRARY_SELF_RECEIVER_VS_DEREF
        )
        b_arb_no_deref = _compile_only(
            rustc,
            tmp_dir,
            "b_arb_no_deref",
            PROBE_B_RECEIVER_ONLY_CANNOT_AUTOREF_TARGET_E0599,
        )
        b_anti_val_ref = _compile_only(
            rustc, tmp_dir, "b_anti_val_ref", PROBE_B_ANTI_SHADOWING_VAL_VS_REF_E0034
        )
        b_anti_ref_mut = _compile_only(
            rustc, tmp_dir, "b_anti_ref_mut", PROBE_B_ANTI_SHADOWING_REF_VS_MUT_E0034
        )
        b_anti_asym = _compile_and_run(
            rustc,
            tmp_dir,
            "b_anti_asym",
            PROBE_B_ANTI_SHADOWING_ASYMMETRY_POINTEE_SHADOWS_SMART,
        )
        b_anti_double_ref = _compile_and_run(
            rustc,
            tmp_dir,
            "b_anti_double_ref",
            PROBE_B_ANTI_SHADOWING_DOUBLE_REF_NICHE_BYPASS,
        )
        b_anti_mut_ptr_exempt = _compile_and_run(
            rustc,
            tmp_dir,
            "b_anti_mut_ptr_exempt",
            PROBE_B_ANTI_SHADOWING_MUT_PTR_EXEMPTION,
        )

        # Group C
        c_zerocopy_pos = _compile_and_run(
            rustc, tmp_dir, "c_zerocopy_pos", PROBE_C_ZEROCOPY_PATTERNS
        )
        c_zc_unaligned_e0599 = _compile_only(
            rustc,
            tmp_dir,
            "c_zc_unaligned_e0599",
            PROBE_C_ZEROCOPY_CONDITIONAL_DEREF_UNALIGNED_E0599,
        )
        c_zc_immutable_e0599 = _compile_only(
            rustc,
            tmp_dir,
            "c_zc_immutable_e0599",
            PROBE_C_ZEROCOPY_CONDITIONAL_DEREF_IMMUTABLE_E0599,
        )
        c_zc_ptr_no_deref_e0599 = _compile_only(
            rustc,
            tmp_dir,
            "c_zc_ptr_no_deref_e0599",
            PROBE_C_ZEROCOPY_PTR_NO_DEREF_TO_REFERENT_E0599,
        )
        c_mir = _emit_mir_excerpt(
            rustc,
            tmp_dir,
            "c_mir",
            PROBE_C_MIR_INSPECTION,
            fn_markers=[
                "mir_array_unsize_len",
                "mir_deref_then_unsize_len",
                "mir_ptr_reborrow_and_as_ref",
            ],
        )

        # Group D: Miri Stacked Borrows + Tree Borrows on positive probes
        miri_results: dict[str, Any] = {"available": False}
        if with_miri:
            miri_env = _prepare_miri_env(cargo, tmp_dir)
            if miri_env is not None:
                miri_ver = _run([cargo, "miri", "--version"]).stdout.strip()
                miri_results = {
                    "available": True,
                    "miri_version": miri_ver,
                    "a_matrix_stacked": _run_miri(
                        cargo, tmp_dir, "a_sb", PROBE_A_PRECEDENCE_MATRIX, miri_env=miri_env
                    ),
                    "a_matrix_tree_borrows": _run_miri(
                        cargo,
                        tmp_dir,
                        "a_tb",
                        PROBE_A_PRECEDENCE_MATRIX,
                        miri_env=miri_env,
                        miri_flags="-Zmiri-tree-borrows",
                    ),
                    "c_zerocopy_stacked": _run_miri(
                        cargo, tmp_dir, "c_sb", PROBE_C_ZEROCOPY_PATTERNS, miri_env=miri_env
                    ),
                    "c_zerocopy_tree_borrows": _run_miri(
                        cargo,
                        tmp_dir,
                        "c_tb",
                        PROBE_C_ZEROCOPY_PATTERNS,
                        miri_env=miri_env,
                        miri_flags="-Zmiri-tree-borrows",
                    ),
                }

    results = {
        "observed_at": _dt.date.today().isoformat(),
        "rustc_version": rustc_ver,
        "rustc_commit_hash": commit_hash,
        "group_a_autoderef_and_adjustment_precedence": {
            "a_matrix": a_matrix,
            "a_probe_ignores_place_mutability_e0596": a_mut_e0596,
            "a_raw_ptr_no_autoderef_e0599": a_raw_e0599,
            "a_raw_ptr_to_const_no_chained_autoref_e0599": a_raw_const_neg,
            "a_raw_ptr_to_const_positive": a_raw_const_pos,
            "a_unsize_skips_by_value_and_const_ptr_e0599": a_unsize_skip,
            "a_pin_reborrow_positive": a_pin_reborrow,
        },
        "group_b_ambiguity_shadowing_and_arbitrary_self_types": {
            "same_step_trait_ambiguity_e0034": b_trait_e0034,
            "same_step_inherent_ambiguity_e0034": b_inh_e0034,
            "same_step_where_clause_ambiguity_e0034": b_where_e0034,
            "same_step_object_candidate_ambiguity_e0034": b_obj_e0034,
            "cross_step_trait_shadows_inner_inherent": b_cross_step,
            "inference_deferred_same_trait_collapse": b_trait_collapse,
            "supertrait_collision_without_feature_e0034": b_super_e0034,
            "supertrait_shadowing_with_feature": b_super_feat,
            "arbitrary_self_receiver_vs_deref_positive": b_arb_pos,
            "arbitrary_self_receiver_without_deref_e0599": b_arb_no_deref,
            "anti_shadowing_by_val_over_ref_e0034": b_anti_val_ref,
            "anti_shadowing_shared_ref_over_mut_ref_e0034": b_anti_ref_mut,
            "anti_shadowing_asymmetry_pointee_shadows_smart": b_anti_asym,
            "anti_shadowing_double_ref_niche_bypass": b_anti_double_ref,
            "anti_shadowing_mut_ptr_exemption": b_anti_mut_ptr_exempt,
        },
        "group_c_zerocopy_first_customer_patterns": {
            "zerocopy_patterns_positive": c_zerocopy_pos,
            "zerocopy_unalign_missing_unaligned_e0599": c_zc_unaligned_e0599,
            "zerocopy_readonly_missing_immutable_e0599": c_zc_immutable_e0599,
            "zerocopy_ptr_no_deref_to_referent_e0599": c_zc_ptr_no_deref_e0599,
            "mir_lowering_excerpts": c_mir,
        },
        "group_d_miri_execution": miri_results,
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Path to write JSON probe results.",
    )
    parser.add_argument(
        "--no-miri",
        action="store_true",
        help="Skip Miri checks.",
    )
    args = parser.parse_args(argv)
    results = run_all(args.out, with_miri=not args.no_miri)

    # Assertions verifying expected compiler outcomes (no silent failures)
    ga = results["group_a_autoderef_and_adjustment_precedence"]
    assert ga["a_matrix"]["run_returncode"] == 0, ga["a_matrix"]
    assert ga["a_probe_ignores_place_mutability_e0596"]["compile_returncode"] != 0
    assert "E0596" in ga["a_probe_ignores_place_mutability_e0596"]["compile_stderr"]
    assert "E0599" in ga["a_raw_ptr_no_autoderef_e0599"]["compile_stderr"]
    assert "E0599" in ga["a_raw_ptr_to_const_no_chained_autoref_e0599"]["compile_stderr"]
    assert ga["a_raw_ptr_to_const_positive"]["run_returncode"] == 0
    assert "E0599" in ga["a_unsize_skips_by_value_and_const_ptr_e0599"]["compile_stderr"]
    assert ga["a_pin_reborrow_positive"]["run_returncode"] == 0

    gb = results["group_b_ambiguity_shadowing_and_arbitrary_self_types"]
    assert "E0034" in gb["same_step_trait_ambiguity_e0034"]["compile_stderr"]
    assert "E0034" in gb["same_step_inherent_ambiguity_e0034"]["compile_stderr"]
    assert "E0592" in gb["same_step_inherent_ambiguity_e0034"]["compile_stderr"]
    assert "ExtDup" not in gb["same_step_inherent_ambiguity_e0034"]["compile_stderr"]
    assert "E0034" in gb["same_step_where_clause_ambiguity_e0034"]["compile_stderr"]
    assert "E0592" not in gb["same_step_where_clause_ambiguity_e0034"]["compile_stderr"]
    assert "E0034" in gb["same_step_object_candidate_ambiguity_e0034"]["compile_stderr"]
    assert "E0592" not in gb["same_step_object_candidate_ambiguity_e0034"]["compile_stderr"]
    assert gb["cross_step_trait_shadows_inner_inherent"]["run_returncode"] == 0
    assert gb["inference_deferred_same_trait_collapse"]["run_returncode"] == 0
    assert "E0034" in gb["supertrait_collision_without_feature_e0034"]["compile_stderr"]
    assert gb["supertrait_shadowing_with_feature"]["run_returncode"] == 0
    assert gb["arbitrary_self_receiver_vs_deref_positive"]["run_returncode"] == 0
    assert "E0599" in gb["arbitrary_self_receiver_without_deref_e0599"]["compile_stderr"]
    assert "E0034" in gb["anti_shadowing_by_val_over_ref_e0034"]["compile_stderr"]
    assert "E0034" in gb["anti_shadowing_shared_ref_over_mut_ref_e0034"]["compile_stderr"]
    assert gb["anti_shadowing_asymmetry_pointee_shadows_smart"]["run_returncode"] == 0
    assert gb["anti_shadowing_double_ref_niche_bypass"]["run_returncode"] == 0
    assert gb["anti_shadowing_mut_ptr_exemption"]["run_returncode"] == 0

    gc = results["group_c_zerocopy_first_customer_patterns"]
    assert gc["zerocopy_patterns_positive"]["run_returncode"] == 0
    assert "E0599" in gc["zerocopy_unalign_missing_unaligned_e0599"]["compile_stderr"]
    assert "E0599" in gc["zerocopy_readonly_missing_immutable_e0599"]["compile_stderr"]
    assert "E0599" in gc["zerocopy_ptr_no_deref_to_referent_e0599"]["compile_stderr"]
    assert gc["mir_lowering_excerpts"]["compile_returncode"] == 0

    gd = results["group_d_miri_execution"]
    if gd.get("available"):
        assert gd["a_matrix_stacked"]["rc"] == 0, gd["a_matrix_stacked"]
        assert gd["a_matrix_tree_borrows"]["rc"] == 0, gd["a_matrix_tree_borrows"]
        assert gd["c_zerocopy_stacked"]["rc"] == 0, gd["c_zerocopy_stacked"]
        assert gd["c_zerocopy_tree_borrows"]["rc"] == 0, gd["c_zerocopy_tree_borrows"]

    print(f"All empirical probes passed and wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
