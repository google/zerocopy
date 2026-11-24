#!/usr/bin/env python3
"""Live rustc probe for min_specialization soundness, always-applicable traits,
Copy rejection vs Sized/TrustedStep/TrustedLen/TrivialClone admission,
lifetime-equality / 'static / duplicate-param rejections, and default type
separation between min_specialization and full specialization.

Run standalone:
  python3 support/probe_min_specialization_soundness.py --out support/probe_results.json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and shutil.which(env_rustc):
        return env_rustc
    direct = shutil.which("rustc")
    if direct:
        return direct
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.is_file():
        return str(cargo_rustc)
    raise FileNotFoundError("rustc binary not found in PATH or ~/.cargo/bin/rustc")


def _scrub(text: str, tmp_dir: Path) -> str:
    """Scrub host-specific temp paths, home dirs, and compiler source hashes."""
    out = text.replace(str(tmp_dir), "<WORKDIR>")
    out = re.sub(r"/(?:[^\s/]+/)*\.rustup/toolchains/[^/\s]+", "<RUST_SYSROOT>", out)
    home_str = str(Path.home())
    if home_str and home_str != "/":
        out = out.replace(home_str, "<USER_DIR>")
    out = re.sub(r"/rustc/[0-9a-f]{40}", "<RUSTC_SRC>", out)
    return out


def _extract_error_codes(stderr: str) -> list[str]:
    return sorted(set(re.findall(r"error\[(E\d{4})\]", stderr)))


def _run_case(
    rustc: str,
    tmp_dir: Path,
    stem: str,
    source: str,
    extra_args: list[str] | None = None,
    expect_run: bool = True,
    crate_type: str = "bin",
) -> dict[str, Any]:
    src_path = tmp_dir / f"{stem}.rs"
    out_path = tmp_dir / (f"{stem}.bin" if crate_type == "bin" else f"lib{stem}.rlib")
    src_path.write_text(source, encoding="utf-8")

    cmd = [
        rustc,
        "--edition=2024",
        f"--crate-type={crate_type}",
        str(src_path),
        "-o",
        str(out_path),
    ]
    if extra_args:
        cmd.extend(extra_args)

    comp = subprocess.run(cmd, capture_output=True, text=True, check=False)
    stderr_clean = _scrub(comp.stderr.strip(), tmp_dir)
    stderr_lines = stderr_clean.splitlines()
    result: dict[str, Any] = {
        "compile_rc": comp.returncode,
        "error_codes": _extract_error_codes(stderr_clean),
        "stderr_head": "\n".join(stderr_lines[:35]),
    }
    if comp.returncode == 0 and expect_run and crate_type == "bin":
        run = subprocess.run([str(out_path)], capture_output=True, text=True, check=False)
        result["run_rc"] = run.returncode
        result["stdout"] = run.stdout.strip()
        if run.stderr.strip():
            result["run_stderr"] = _scrub(run.stderr.strip(), tmp_dir)
    return result


def run_probe() -> dict[str, Any]:
    rustc = _find_rustc()
    rustc_ver_raw = subprocess.run(
        [rustc, "-vV"], capture_output=True, text=True, check=True
    ).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="probe_min_spec_") as td:
        tmp = Path(td)

        # Build an auxiliary crate exporting a #[rustc_specialization_trait] trait
        # to verify cross-crate feature gating on manual impls.
        aux_rs = tmp / "aux_spec_trait.rs"
        aux_rlib = tmp / "libaux_spec_trait.rlib"
        aux_rs.write_text(
            """
#![feature(min_specialization)]
#![feature(rustc_attrs)]

#[rustc_specialization_trait]
pub trait AuxSpecTrait {
    fn tag(&self) -> u32;
}

impl AuxSpecTrait for u32 {
    fn tag(&self) -> u32 { 77 }
}
""",
            encoding="utf-8",
        )
        aux_comp = subprocess.run(
            [
                rustc,
                "--edition=2024",
                "--crate-type=rlib",
                "--crate-name=aux_spec_trait",
                str(aux_rs),
                "-o",
                str(aux_rlib),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        assert aux_comp.returncode == 0
        extern_aux = ["--extern", f"aux_spec_trait={aux_rlib}"]

        part_a: dict[str, Any] = {
            "a01_valid_min_specialization_u32_and_vec": _run_case(
                rustc,
                tmp,
                "a01_valid_u32_vec",
                """
#![feature(min_specialization)]

trait Tag {
    fn tag(&self) -> &'static str;
}

impl<T> Tag for T {
    default fn tag(&self) -> &'static str { "generic" }
}

impl Tag for u32 {
    fn tag(&self) -> &'static str { "u32" }
}

impl<T> Tag for Vec<T> {
    fn tag(&self) -> &'static str { "vec" }
}

fn call_generic<T>(x: &T) -> &'static str { x.tag() }

fn main() {
    let x = true;
    let y = 42u32;
    let z = vec![1u8, 2u8];
    println!(
        "SPEC_GEN={} SPEC_U32={} SPEC_VEC={} MONO_GEN={} MONO_U32={}",
        x.tag(),
        y.tag(),
        z.tag(),
        call_generic(&x),
        call_generic(&y),
    );
}
""",
            ),
            "a02_valid_constrained_projection_spec_extend": _run_case(
                rustc,
                tmp,
                "a02_constrained_proj",
                """
#![feature(min_specialization)]

trait SpecCollect<T> {
    fn kind(&self) -> &'static str;
}

impl<T, I: Iterator<Item = T>> SpecCollect<T> for I {
    default fn kind(&self) -> &'static str { "iter" }
}

// `T` appears in both `SpecCollect<T>` and `IntoIter<T>`, yet passes
// `check_duplicate_params` because `I: Iterator<Item = T>` constrains `T`
// in the parent impl (`unconstrained_parent_impl_args`).
impl<T> SpecCollect<T> for std::vec::IntoIter<T> {
    fn kind(&self) -> &'static str { "into_iter" }
}

fn main() {
    let a = [1u32, 2].into_iter();
    let b = vec![1u32, 2].into_iter();
    println!("SPEC_EXTEND={},{}", a.kind(), b.kind());
}
""",
            ),
            "a03_valid_always_applicable_sized_trusted_step_and_marker_trusted_len_fused": _run_case(
                rustc,
                tmp,
                "a03_core_markers",
                """
#![feature(min_specialization)]
#![feature(trusted_len)]
#![feature(trusted_step)]

use std::iter::{FusedIterator, TrustedLen, TrustedStep};

trait SizeTag {
    fn size_kind(&self) -> u32;
}
impl<T: ?Sized> SizeTag for T {
    default fn size_kind(&self) -> u32 { 1 }
}
impl<T: Sized> SizeTag for T {
    fn size_kind(&self) -> u32 { 2 }
}

trait StepTag {
    fn step_kind(&self) -> &'static str;
}
impl<T> StepTag for T {
    default fn step_kind(&self) -> &'static str { "any" }
}
// `TrustedStep: Step + Copy` is `#[rustc_specialization_trait]`, so its
// supertraits (`Step`, `Copy`, `Clone`) are elaborated into parent clauses.
impl<T: TrustedStep> StepTag for T {
    fn step_kind(&self) -> &'static str { "trusted_step" }
}

trait IterTag {
    fn iter_kind(&self) -> &'static str;
}
// Note: `Iterator` is already in the base impl, so `TrustedLen` (a Marker
// specialization trait whose supertraits are NOT elaborated) succeeds.
impl<I: Iterator> IterTag for I {
    default fn iter_kind(&self) -> &'static str { "iter" }
}
impl<I: TrustedLen> IterTag for I {
    fn iter_kind(&self) -> &'static str { "trusted_len" }
}

trait FusedTag {
    fn fused_kind(&self) -> &'static str;
}
impl<I: Iterator> FusedTag for I {
    default fn fused_kind(&self) -> &'static str { "iter" }
}
impl<I: FusedIterator> FusedTag for I {
    fn fused_kind(&self) -> &'static str { "fused" }
}

fn main() {
    let slice: &[u8] = &[1, 2, 3];
    let gen_iter = [1u32, 2, 3].into_iter().filter(|x| *x > 1);
    let tl_iter = 0u32..3u32;
    println!(
        "GEN_ITER={} TL_ITER={} FUSED={} BOOL_STEP={} U32_STEP={} UNSIZED={} SIZED={}",
        gen_iter.iter_kind(),
        tl_iter.iter_kind(),
        tl_iter.fused_kind(),
        false.step_kind(),
        7u32.step_kind(),
        slice.size_kind(),
        7u32.size_kind(),
    );
}
""",
            ),
            "a04_valid_user_rustc_specialization_trait_and_supertrait_elaboration": _run_case(
                rustc,
                tmp,
                "a04_user_spec_trait",
                """
#![feature(min_specialization)]
#![feature(rustc_attrs)]

trait MySup {
    fn sup_val(&self) -> u32;
}
impl MySup for u32 {
    fn sup_val(&self) -> u32 { *self + 10 }
}

#[rustc_specialization_trait]
trait AlwaysSpec: MySup {}

// Valid because `u32: MySup` is global (`clause.is_global()`).
impl AlwaysSpec for u32 {}

trait Consumer {
    fn compute(&self) -> u32;
}
impl<T> Consumer for T {
    default fn compute(&self) -> u32 { 0 }
}
// Valid: `AlwaysSpec` is AlwaysApplicable, so its supertrait `MySup`
// is elaborated into `impl2_clauses` and can even be invoked here.
impl<T: AlwaysSpec> Consumer for T {
    fn compute(&self) -> u32 { self.sup_val() }
}

fn main() {
    println!("ALWAYS_SUP={},{}", "abc".compute(), 5u32.compute());
}
""",
            ),
            "a05_valid_bytewise_eq_distinct_rhs_avoids_duplicate_param": _run_case(
                rustc,
                tmp,
                "a05_bytewise_rhs",
                """
#![feature(min_specialization)]
#![feature(rustc_attrs)]

#[rustc_specialization_trait]
trait FastEq<Rhs = Self>: PartialEq<Rhs> {}
impl FastEq for u32 {}

trait SliceEq<B> {
    fn fast_path(&self, other: &B) -> bool;
}
impl<A: PartialEq<B>, B> SliceEq<B> for A {
    default fn fast_path(&self, other: &B) -> bool { *self == *other }
}
impl<A, B> SliceEq<B> for A
where
    A: FastEq<B>,
{
    fn fast_path(&self, other: &B) -> bool { *self == *other }
}

fn main() {
    println!("BYTEWISE={}", 9u32.fast_path(&9u32));
}
""",
            ),
            "a06_valid_const_arg_has_type_chain": _run_case(
                rustc,
                tmp,
                "a06_const_arg",
                """
#![feature(min_specialization)]

trait ArrTag {
    fn arr_kind(&self) -> &'static str;
}
impl<T, const N: usize> ArrTag for [T; N] {
    default fn arr_kind(&self) -> &'static str { "generic_arr" }
}
impl<const N: usize> ArrTag for [u8; N] {
    default fn arr_kind(&self) -> &'static str { "u8_arr" }
}
impl ArrTag for [u8; 4] {
    fn arr_kind(&self) -> &'static str { "u8_len4_arr" }
}

fn main() {
    let a = [1u32; 2];
    let b = [1u8; 3];
    let c = [1u8; 4];
    println!("CONST_ARR={},{},{}", a.arr_kind(), b.arr_kind(), c.arr_kind());
}
""",
            ),
            "a07_valid_trivial_clone_marker_with_base_clone": _run_case(
                rustc,
                tmp,
                "a07_trivial_clone",
                """
#![feature(min_specialization)]
#![feature(trivial_clone)]

use std::clone::TrivialClone;

trait FastClone {
    fn clone_kind(&self) -> &'static str;
}
// `Clone` is present in the base impl, matching core/alloc `RcFromSlice`!
impl<T: Clone> FastClone for T {
    default fn clone_kind(&self) -> &'static str { "clone" }
}
impl<T: TrivialClone> FastClone for T {
    fn clone_kind(&self) -> &'static str { "trivial_clone" }
}

fn main() {
    let s = String::from("hi");
    let n = 42u32;
    println!("TRIVIAL_CLONE={},{}", s.clone_kind(), n.clone_kind());
}
""",
            ),
        }

        part_b: dict[str, Any] = {
            "b01_reject_lifetime_eq_layer1_e0119": _run_case(
                rustc,
                tmp,
                "b01_lt_eq_e0119",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<'a, 'b> Tr for (&'a u8, &'b u8) { default fn id(&self) -> u32 { 1 } }
impl<'a> Tr for (&'a u8, &'a u8) { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b02_reject_static_bound_layer1_e0119": _run_case(
                rustc,
                tmp,
                "b02_static_bound_e0119",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
impl<T: 'static> Tr for T { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b03_reject_static_lifetime_header_layer2": _run_case(
                rustc,
                tmp,
                "b03_static_header",
                """
#![feature(min_specialization)]
trait Tr { fn f(&self) -> u32; }
impl<T> Tr for T { default fn f(&self) -> u32 { 1 } }
impl Tr for &'static i32 { fn f(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b04_reject_lifetime_generalize_79457_region_error": _run_case(
                rustc,
                tmp,
                "b04_generalize_79457",
                """
#![feature(min_specialization)]
trait Tr { fn other(self); }
impl<T: 'static> Tr for T { default fn other(self) {} }
impl<'a> Tr for &'a i32 { fn other(self) {} }
fn main() {}
""",
                expect_run=False,
            ),
            "b05_reject_copy_and_clone_elaboration": _run_case(
                rustc,
                tmp,
                "b05_reject_copy",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
impl<T: Copy> Tr for T { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b05b_witness_copy_can_be_lifetime_dependent_in_safe_rust": _run_case(
                rustc,
                tmp,
                "b05b_copy_static_ok",
                """
// Safe Rust allows a type to implement Copy ONLY for `'static`, proving why
// `Copy` cannot soundly carry `#[rustc_specialization_trait]`.
struct OnlyStaticCopy<'a>(&'a u8);
impl Clone for OnlyStaticCopy<'static> {
    fn clone(&self) -> Self { *self }
}
impl Copy for OnlyStaticCopy<'static> {}

fn main() {
    static BYTE: u8 = 9;
    let a = OnlyStaticCopy(&BYTE);
    let b = a;
    println!("STATIC_COPY={},{}", a.0, b.0);
}
""",
            ),
            "b06_reject_clone_alone": _run_case(
                rustc,
                tmp,
                "b06_reject_clone",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
impl<T: Clone> Tr for T { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b07_reject_trusted_len_supertrait_iterator_when_absent_from_base": _run_case(
                rustc,
                tmp,
                "b07_trusted_len_no_base_iter",
                """
#![feature(min_specialization)]
#![feature(trusted_len)]
use std::iter::TrustedLen;

trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
// `TrustedLen` is Marker (`TraitSpecializationKind::Marker`), NOT AlwaysApplicable,
// so its supertrait `Iterator` is NOT elaborated into base clauses!
impl<T: TrustedLen> Tr for T { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b08_reject_always_applicable_impl_with_non_spec_bound": _run_case(
                rustc,
                tmp,
                "b08_spec_trait_super_bound",
                """
#![feature(min_specialization)]
#![feature(rustc_attrs)]

#[rustc_specialization_trait]
trait SpecMarker: Default {
    fn f();
}

impl<T: Default> SpecMarker for T {
    fn f() {}
}
fn main() {}
""",
                expect_run=False,
            ),
            "b08b_reject_manual_impl_of_spec_trait_without_feature": _run_case(
                rustc,
                tmp,
                "b08b_manual_spec_trait_no_feat",
                """
extern crate aux_spec_trait;
struct Local(u32);
impl aux_spec_trait::AuxSpecTrait for Local {
    fn tag(&self) -> u32 { self.0 }
}
fn main() {}
""",
                extra_args=extern_aux,
                expect_run=False,
            ),
            "b09_reject_duplicate_type_param_tuple": _run_case(
                rustc,
                tmp,
                "b09_dup_ty_param",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
impl<T> Tr for (T, T) { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b10_reject_duplicate_lifetime_param": _run_case(
                rustc,
                tmp,
                "b10_dup_lt_param",
                """
#![feature(min_specialization)]
trait Tr { fn f(&self) -> u32; }
impl<T> Tr for T { default fn f(&self) -> u32 { 1 } }
impl<'a> Tr for (&'a u8, &'a u8) { fn f(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b11_reject_projection_bound": _run_case(
                rustc,
                tmp,
                "b11_proj_bound",
                """
#![feature(min_specialization)]
trait Id { type This; }
impl<T> Id for T { type This = T; }
trait X { fn f(); }
impl<T: Id> X for T { default fn f() {} }
impl<I, V: Id<This = (I,)>> X for V { fn f() {} }
fn main() {}
""",
                expect_run=False,
            ),
            "b12_reject_empty_specialization": _run_case(
                rustc,
                tmp,
                "b12_empty_spec",
                """
#![feature(min_specialization)]
trait Tr { fn f(&self) -> u32; }
impl<T> Tr for T { default fn f(&self) -> u32 { 1 } }
impl Tr for u32 {}
fn main() {}
""",
                expect_run=False,
            ),
            "b13_reject_non_default_parent_item": _run_case(
                rustc,
                tmp,
                "b13_non_default_parent",
                """
#![feature(min_specialization)]
trait Tr { fn f(&self) -> u32; }
impl<T> Tr for T { fn f(&self) -> u32 { 1 } }
impl Tr for u32 { fn f(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b14_reject_async_rpitit_specialization": _run_case(
                rustc,
                tmp,
                "b14_async_spec",
                """
#![feature(min_specialization)]
trait AsyncTr {
    async fn f(&self) -> u32;
}
impl<T> AsyncTr for T {
    default async fn f(&self) -> u32 { 1 }
}
impl AsyncTr for u32 {
    async fn f(&self) -> u32 { 2 }
}
fn main() {}
""",
                expect_run=False,
            ),
            "b15_reject_non_chain_diamond_overlap_e0119": _run_case(
                rustc,
                tmp,
                "b15_diamond_e0119",
                """
#![feature(min_specialization)]
trait ArrTag { fn arr_kind(&self) -> u32; }
impl<T, const N: usize> ArrTag for [T; N] { default fn arr_kind(&self) -> u32 { 1 } }
impl<const N: usize> ArrTag for [u8; N] { default fn arr_kind(&self) -> u32 { 2 } }
impl<T> ArrTag for [T; 4] { fn arr_kind(&self) -> u32 { 3 } }
fn main() {}
""",
                expect_run=False,
            ),
        }

        part_c: dict[str, Any] = {
            "c01_reject_default_type_assoc_min_specialization_e0658_e0308": _run_case(
                rustc,
                tmp,
                "c01_default_type_min_spec",
                """
#![feature(min_specialization)]
trait Tr { type Assoc; fn get(&self) -> Self::Assoc; }
impl<T> Tr for T { default type Assoc = (); default fn get(&self) -> Self::Assoc {} }
fn main() {}
""",
                expect_run=False,
            ),
            "c02_reject_default_impl_min_specialization_e0658": _run_case(
                rustc,
                tmp,
                "c02_default_impl_min_spec",
                """
#![feature(min_specialization)]
trait Tr { fn f(&self) -> u32; }
default impl<T> Tr for T { fn f(&self) -> u32 { 1 } }
impl Tr for u32 { fn f(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "c03_accept_default_type_assoc_full_specialization": _run_case(
                rustc,
                tmp,
                "c03_default_type_full_spec",
                """
#![feature(specialization)]
trait Tr { type Assoc; fn tag(&self) -> u32; }
impl<T> Tr for T { default type Assoc = u16; default fn tag(&self) -> u32 { 1 } }
impl Tr for u32 { type Assoc = u64; fn tag(&self) -> u32 { 42 } }
fn main() {
    let x = 0u32;
    println!(
        "FULL_SPEC_ASSOC={},{}",
        x.tag(),
        std::mem::size_of::<<u32 as Tr>::Assoc>(),
    );
}
""",
            ),
            "c04_full_specialization_still_hides_default_type_in_typeck_e0308": _run_case(
                rustc,
                tmp,
                "c04_full_spec_opaque_typeck",
                """
#![feature(specialization)]
trait Tr { type Assoc; fn get(&self) -> Self::Assoc; }
impl<T> Tr for T { default type Assoc = (); default fn get(&self) -> Self::Assoc {} }
fn main() {}
""",
                expect_run=False,
            ),
            "c05a_full_specialization_direct_non_copy_call_rejected_e0597": _run_case(
                rustc,
                tmp,
                "c05a_full_spec_direct_e0597",
                """
#![feature(specialization)]
#![allow(incomplete_features)]

trait Tag { fn kind(&self) -> &'static str; }
impl<T> Tag for T { default fn kind(&self) -> &'static str { "generic" } }
impl<T: Copy> Tag for T { fn kind(&self) -> &'static str { "copy" } }

struct OnlyStaticCopy<'a>(&'a u8);
impl Clone for OnlyStaticCopy<'static> {
    fn clone(&self) -> Self { *self }
}
impl Copy for OnlyStaticCopy<'static> {}

fn main() {
    let local: u8 = 2;
    let l_ref = OnlyStaticCopy(&local);
    // Direct call sees concrete `OnlyStaticCopy<'local>`, picks `Copy` modulo regions,
    // and fails borrowck with E0597 because `local` is not `'static`.
    println!("{}", l_ref.kind());
}
""",
                expect_run=False,
            ),
            "c05b_full_specialization_generic_bypass_dispatches_copy_on_non_copy": _run_case(
                rustc,
                tmp,
                "c05b_full_spec_generic_bypass",
                """
#![feature(specialization)]
#![allow(incomplete_features)]

trait Tag { fn kind(&self) -> &'static str; }
impl<T> Tag for T { default fn kind(&self) -> &'static str { "generic" } }
impl<T: Copy> Tag for T { fn kind(&self) -> &'static str { "copy" } }

struct OnlyStaticCopy<'a>(&'a u8);
impl Clone for OnlyStaticCopy<'static> {
    fn clone(&self) -> Self { *self }
}
impl Copy for OnlyStaticCopy<'static> {}

fn dispatch_generic<T>(x: &T) -> &'static str {
    x.kind()
}

fn main() {
    static S: u8 = 1;
    let local: u8 = 2;
    let s_ref = OnlyStaticCopy(&S);
    let l_ref = OnlyStaticCopy(&local);
    // Through generic `T`, typeck checks only `T: Tag` (satisfied by blanket impl),
    // borrowck succeeds, and post-erasure monomorphization dispatches `Copy` impl ("copy")!
    println!(
        "FULL_SPEC_BYPASS=static:{},local:{}",
        dispatch_generic(&s_ref),
        dispatch_generic(&l_ref),
    );
}
""",
            ),
            "c06_full_specialization_default_type_monomorphizes_via_erased_copy": _run_case(
                rustc,
                tmp,
                "c06_full_spec_assoc_bypass",
                """
#![feature(specialization)]
#![allow(incomplete_features)]

trait AssocTag {
    type Assoc;
    fn size() -> usize;
}
impl<T> AssocTag for T {
    default type Assoc = u16;
    default fn size() -> usize { std::mem::size_of::<u16>() }
}
impl<T: Copy> AssocTag for T {
    type Assoc = [u64; 4];
    fn size() -> usize { std::mem::size_of::<Self::Assoc>() }
}

struct OnlyStaticCopy<'a>(&'a u8);
impl Clone for OnlyStaticCopy<'static> {
    fn clone(&self) -> Self { *self }
}
impl Copy for OnlyStaticCopy<'static> {}

fn assoc_size_generic<T>(_: &T) -> usize {
    std::mem::size_of::<<T as AssocTag>::Assoc>()
}

fn main() {
    let local: u8 = 2;
    let l_ref = OnlyStaticCopy(&local);
    println!("FULL_SPEC_ASSOC_BYPASS={}", assoc_size_generic(&l_ref));
}
""",
            ),
        }

        part_d: dict[str, Any] = {
            "d01_next_solver_valid_u32_vec": _run_case(
                rustc,
                tmp,
                "d01_ns_valid",
                """
#![feature(min_specialization)]
trait Tag { fn tag(&self) -> &'static str; }
impl<T> Tag for T { default fn tag(&self) -> &'static str { "generic" } }
impl Tag for u32 { fn tag(&self) -> &'static str { "u32" } }
fn main() { println!("NS_VALID={},{}", true.tag(), 42u32.tag()); }
""",
                extra_args=["-Znext-solver=globally"],
            ),
            "d02_next_solver_reject_copy": _run_case(
                rustc,
                tmp,
                "d02_ns_reject_copy",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<T> Tr for T { default fn id(&self) -> u32 { 1 } }
impl<T: Copy> Tr for T { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                extra_args=["-Znext-solver=globally"],
                expect_run=False,
            ),
            "d03_next_solver_reject_lifetime_eq_e0119": _run_case(
                rustc,
                tmp,
                "d03_ns_lt_eq",
                """
#![feature(min_specialization)]
trait Tr { fn id(&self) -> u32; }
impl<'a, 'b> Tr for (&'a u8, &'b u8) { default fn id(&self) -> u32 { 1 } }
impl<'a> Tr for (&'a u8, &'a u8) { fn id(&self) -> u32 { 2 } }
fn main() {}
""",
                extra_args=["-Znext-solver=globally"],
                expect_run=False,
            ),
            "d04_next_solver_reject_default_type_e0658": _run_case(
                rustc,
                tmp,
                "d04_ns_default_type",
                """
#![feature(min_specialization)]
trait Tr { type Assoc; fn get(&self) -> Self::Assoc; }
impl<T> Tr for T { default type Assoc = (); default fn get(&self) -> Self::Assoc {} }
fn main() {}
""",
                extra_args=["-Znext-solver=globally"],
                expect_run=False,
            ),
        }

    total = len(part_a) + len(part_b) + len(part_c) + len(part_d)
    return {
        "schema_version": 1,
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_ver_raw,
        "total_cases": total,
        "part_a_valid_min_specialization": part_a,
        "part_b_soundness_rejections": part_b,
        "part_c_default_type_and_full_specialization": part_c,
        "part_d_next_solver_comparison": part_d,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Write JSON results to path")
    args = parser.parse_args(argv)

    data = run_probe()
    rendered = json.dumps(data, indent=2, ensure_ascii=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.out} ({len(rendered)} bytes, {data['total_cases']} cases)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
