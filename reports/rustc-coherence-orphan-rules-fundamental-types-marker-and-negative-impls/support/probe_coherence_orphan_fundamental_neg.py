#!/usr/bin/env python3
"""Live multi-crate rustc probe for coherence, covered-type orphan checking,
#[fundamental] types/traits, #[marker] impls, negative coherence, and
zerocopy-style disjoint blanket reason markers.

Run standalone:
  python3 support/probe_coherence_orphan_fundamental_neg.py --out support/probe_results.json
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
    home_str = str(Path.home())
    out = re.sub(r"/(?:[^\s/]+/)*\.rustup/toolchains/[^/\s]+", "<RUST_SYSROOT>", out)
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

    cmd = [rustc, "--edition=2024", f"--crate-type={crate_type}", str(src_path), "-o", str(out_path)]
    if extra_args:
        cmd.extend(extra_args)

    comp = subprocess.run(cmd, capture_output=True, text=True, check=False)
    stderr_clean = _scrub(comp.stderr.strip(), tmp_dir)
    stderr_lines = stderr_clean.splitlines()
    result: dict[str, Any] = {
        "compile_rc": comp.returncode,
        "error_codes": _extract_error_codes(stderr_clean),
        "stderr_head": "\n".join(stderr_lines[:24]),
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
    rustc_ver = subprocess.run([rustc, "-vV"], capture_output=True, text=True, check=True).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="probe_coherence_orphan_") as td:
        tmp = Path(td)

        # Build independent upstream crate `up` (`libup.rlib`) with foreign traits and structs.
        up_rs = tmp / "up.rs"
        up_rlib = tmp / "libup.rlib"
        up_rs.write_text(
            """
pub trait ForeignTrait<Rhs = ()> {
    fn kind(&self) -> &'static str;
}

pub trait ForeignBlanketTrait {
    fn tag(&self) -> u32;
}

pub struct ForeignType(pub u32);
pub struct ForeignWrapper<T>(pub T);

pub trait ZcMarkerLike {
    fn zc_tag(&self) -> &'static str;
}

pub unsafe trait ZcImmutable {}
unsafe impl ZcImmutable for u32 {}
unsafe impl<T: ?Sized> ZcImmutable for &T {}
unsafe impl<T: ?Sized> ZcImmutable for &mut T {}
unsafe impl<T> ZcImmutable for Box<T> {}
""",
            encoding="utf-8",
        )
        up_comp = subprocess.run(
            [rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=up", str(up_rs), "-o", str(up_rlib)],
            capture_output=True,
            text=True,
            check=True,
        )
        assert up_comp.returncode == 0
        extern_up = ["--extern", f"up={up_rlib}"]

        # Build nightly upstream crate `up_neg` testing cross-crate negative impls.
        up_neg_rs = tmp / "up_neg.rs"
        up_neg_rlib = tmp / "libup_neg.rlib"
        up_neg_rs.write_text(
            """
#![feature(negative_impls)]
pub struct UpNoSend(pub u32);
impl !Send for UpNoSend {}
pub trait UpNegTrait {}
pub struct UpNegStruct(pub u32);
impl !UpNegTrait for UpNegStruct {}
""",
            encoding="utf-8",
        )
        up_neg_comp = subprocess.run(
            [rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=up_neg", str(up_neg_rs), "-o", str(up_neg_rlib)],
            capture_output=True,
            text=True,
            check=True,
        )
        assert up_neg_comp.returncode == 0
        extern_up_neg = ["--extern", f"up_neg={up_neg_rlib}"]

        # ------------------------------------------------------------------
        # Part A: Covered-Type Orphan Rules & #[fundamental] Types/Traits
        # ------------------------------------------------------------------
        part_a = {
            "a01_local_type_for_foreign_trait_ok": _run_case(
                rustc,
                tmp,
                "a01_local_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for LocalType {
    fn kind(&self) -> &'static str { "local" }
}
fn main() {
    println!("A01={}", LocalType(1).kind());
}
""",
                extra_args=extern_up,
            ),
            "a02_fundamental_box_local_type_ok": _run_case(
                rustc,
                tmp,
                "a02_box_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for Box<LocalType> {
    fn kind(&self) -> &'static str { "box_local" }
}
fn main() {
    let b = Box::new(LocalType(1));
    println!("A02={}", b.kind());
}
""",
                extra_args=extern_up,
            ),
            "a03_fundamental_shared_ref_local_type_ok": _run_case(
                rustc,
                tmp,
                "a03_ref_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for &LocalType {
    fn kind(&self) -> &'static str { "ref_local" }
}
fn main() {
    let x = LocalType(1);
    let r: &LocalType = &x;
    println!("A03={}", r.kind());
}
""",
                extra_args=extern_up,
            ),
            "a04_fundamental_mut_ref_local_type_ok": _run_case(
                rustc,
                tmp,
                "a04_mut_ref_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for &mut LocalType {
    fn kind(&self) -> &'static str { "mut_ref_local" }
}
fn main() {
    let mut x = LocalType(1);
    let r: &mut LocalType = &mut x;
    println!("A04={}", r.kind());
}
""",
                extra_args=extern_up,
            ),
            "a05_nested_fundamental_pin_ref_and_pin_box_ok": _run_case(
                rustc,
                tmp,
                "a05_pin_nested_ok",
                """
use std::pin::Pin;
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for Pin<&LocalType> {
    fn kind(&self) -> &'static str { "pin_ref_local" }
}
impl ForeignTrait for Pin<Box<LocalType>> {
    fn kind(&self) -> &'static str { "pin_box_local" }
}
fn main() {
    let x = LocalType(1);
    let pr = Pin::new(&x);
    let pb = Box::pin(LocalType(2));
    println!("A05={},{}", pr.kind(), pb.kind());
}
""",
                extra_args=extern_up,
            ),
            "a06_non_fundamental_vec_local_type_e0117": _run_case(
                rustc,
                tmp,
                "a06_vec_e0117",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for Vec<LocalType> {
    fn kind(&self) -> &'static str { "vec_local" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a07_non_fundamental_foreign_wrapper_local_type_e0117": _run_case(
                rustc,
                tmp,
                "a07_wrap_e0117",
                """
use up::{ForeignTrait, ForeignWrapper};
struct LocalType(u32);
impl ForeignTrait for ForeignWrapper<LocalType> {
    fn kind(&self) -> &'static str { "wrap_local" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a08_foreign_trait_local_arg_for_u32_ok": _run_case(
                rustc,
                tmp,
                "a08_arg_u32_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait<LocalType> for u32 {
    fn kind(&self) -> &'static str { "u32_local_arg" }
}
fn main() {
    println!("A08={}", <u32 as ForeignTrait<LocalType>>::kind(&7u32));
}
""",
                extra_args=extern_up,
            ),
            "a09_rfc2451_covered_t_in_vec_before_local_arg_ok": _run_case(
                rustc,
                tmp,
                "a09_rfc2451_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl<T> ForeignTrait<LocalType> for Vec<T> {
    fn kind(&self) -> &'static str { "vec_t_local_arg" }
}
fn main() {
    let v: Vec<u32> = vec![1, 2];
    println!("A09={}", <Vec<u32> as ForeignTrait<LocalType>>::kind(&v));
}
""",
                extra_args=extern_up,
            ),
            "a10_uncovered_t_before_local_type_arg_e0210": _run_case(
                rustc,
                tmp,
                "a10_uncovered_e0210",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl<T> ForeignTrait<LocalType> for T {
    fn kind(&self) -> &'static str { "uncovered" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a11_uncovered_t_in_fundamental_box_before_local_arg_e0210": _run_case(
                rustc,
                tmp,
                "a11_box_t_e0210",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl<T> ForeignTrait<LocalType> for Box<T> {
    fn kind(&self) -> &'static str { "box_uncovered" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a12_covered_t_after_local_self_ok": _run_case(
                rustc,
                tmp,
                "a12_after_local_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
struct LocalGen<T>(T);
impl<T> ForeignTrait<T> for LocalType {
    fn kind(&self) -> &'static str { "local_self_then_t" }
}
impl<T> ForeignTrait<T> for LocalGen<T> {
    fn kind(&self) -> &'static str { "local_gen_then_t" }
}
fn main() {
    let a = LocalType(1);
    let b = LocalGen(9u32);
    println!("A12={},{}", <LocalType as ForeignTrait<u64>>::kind(&a), <LocalGen<u32> as ForeignTrait<u32>>::kind(&b));
}
""",
                extra_args=extern_up,
            ),
            "a13_fully_foreign_with_type_param_e0210": _run_case(
                rustc,
                tmp,
                "a13_foreign_t_e0210",
                """
use up::{ForeignTrait, ForeignType};
impl<T> ForeignTrait<T> for ForeignType {
    fn kind(&self) -> &'static str { "bad" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a14_fully_foreign_concrete_e0117": _run_case(
                rustc,
                tmp,
                "a14_foreign_e0117",
                """
use up::{ForeignTrait, ForeignType};
impl ForeignTrait for ForeignType {
    fn kind(&self) -> &'static str { "bad" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a15_box_allocator_param_unwrapped_in_1_98": _run_case(
                rustc,
                tmp,
                "a15_box_alloc_param",
                """
#![feature(allocator_api)]
use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;
use up::ForeignTrait;

#[derive(Clone, Copy)]
struct LocalAlloc;
unsafe impl Allocator for LocalAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        std::alloc::Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { std::alloc::Global.deallocate(ptr, layout) }
    }
}

impl ForeignTrait for Box<u32, LocalAlloc> {
    fn kind(&self) -> &'static str { "box_u32_local_alloc" }
}

fn main() {
    let b = Box::new_in(42u32, LocalAlloc);
    println!("A15={}", b.kind());
}
""",
                extra_args=extern_up,
            ),
            "a16_auto_trait_bypasses_fundamental_e0321": _run_case(
                rustc,
                tmp,
                "a16_auto_e0321",
                """
struct LocalType(u32);
unsafe impl Send for Box<LocalType> {}
fn main() {}
""",
                expect_run=False,
            ),
            "a17_fundamental_fnmut_trait_knowable_ok": _run_case(
                rustc,
                tmp,
                "a17_fnmut_fundamental_ok",
                """
trait Pattern { fn pat_kind(&self) -> &'static str; }
impl<F: FnMut(char) -> bool> Pattern for F {
    fn pat_kind(&self) -> &'static str { "fnmut" }
}
impl Pattern for &str {
    fn pat_kind(&self) -> &'static str { "str_ref" }
}
fn main() {
    let pred = |c: char| c == 'a';
    let s: &str = "hi";
    println!("A17={},{}", pred.pat_kind(), s.pat_kind());
}
""",
            ),
            "a18_non_fundamental_foreign_trait_knowability_e0119": _run_case(
                rustc,
                tmp,
                "a18_non_fund_trait_e0119",
                """
use up::ForeignBlanketTrait;
trait Pattern { fn pat_kind(&self) -> &'static str; }
impl<T: ForeignBlanketTrait> Pattern for T {
    fn pat_kind(&self) -> &'static str { "foreign_bound" }
}
impl Pattern for &str {
    fn pat_kind(&self) -> &'static str { "str_ref" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a19_tuple_containing_local_type_rejected_e0117": _run_case(
                rustc,
                tmp,
                "a19_tuple_e0117",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl ForeignTrait for (LocalType, u32) {
    fn kind(&self) -> &'static str { "tuple_local" }
}
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "a20_box_local_before_uncovered_trait_arg_ok": _run_case(
                rustc,
                tmp,
                "a20_box_local_before_t_ok",
                """
use up::ForeignTrait;
struct LocalType(u32);
impl<T> ForeignTrait<T> for Box<LocalType> {
    fn kind(&self) -> &'static str { "box_local_before_t" }
}
fn main() {
    let b = Box::new(LocalType(9));
    println!("A20={}", <Box<LocalType> as ForeignTrait<u8>>::kind(&b));
}
""",
                extra_args=extern_up,
            ),
        }

        # ------------------------------------------------------------------
        # Part B: Overlap, Inherent Overlap, Object Overlap, and #[marker]
        # ------------------------------------------------------------------
        part_b = {
            "b01_conflicting_trait_impls_e0119": _run_case(
                rustc,
                tmp,
                "b01_e0119",
                """
trait Tr { fn f(&self) -> u32; }
struct Wrapper<T>(T);
impl<T> Tr for Wrapper<T> { fn f(&self) -> u32 { 1 } }
impl Tr for Wrapper<u32> { fn f(&self) -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "b02_inherent_impls_disjoint_ok": _run_case(
                rustc,
                tmp,
                "b02_inh_ok",
                """
struct Wrap<T>(T);
impl Wrap<u32> { fn get(&self) -> u32 { self.0 } }
impl Wrap<i32> { fn get(&self) -> i32 { self.0 } }
fn main() {
    println!("B02={},{}", Wrap(10u32).get(), Wrap(-3i32).get());
}
""",
            ),
            "b03_inherent_impls_overlap_e0592": _run_case(
                rustc,
                tmp,
                "b03_inh_e0592",
                """
struct Wrap<T>(T);
impl<T> Wrap<T> { fn dup(&self) {} }
impl Wrap<u32> { fn dup(&self) {} }
fn main() {}
""",
                expect_run=False,
            ),
            "b04_inherent_impl_foreign_type_e0116": _run_case(
                rustc,
                tmp,
                "b04_inh_e0116",
                """
use up::ForeignType;
impl ForeignType { fn bad(&self) {} }
fn main() {}
""",
                extra_args=extern_up,
                expect_run=False,
            ),
            "b05_object_overlap_supertrait_e0371": _run_case(
                rustc,
                tmp,
                "b05_obj_e0371",
                """
trait Sup {}
trait Sub: Sup {}
impl Sup for dyn Sub {}
fn main() {}
""",
                expect_run=False,
            ),
            "b06_marker_trait_overlap_allowed_ok": _run_case(
                rustc,
                tmp,
                "b06_marker_ok",
                """
#![feature(marker_trait_attr)]
#[marker]
trait Mark {}
impl<T: Copy> Mark for T {}
impl<T: Clone> Mark for T {}
fn check<T: Mark>(_: T) {}
fn main() {
    check(42u32);
    check(String::from("ok"));
    println!("B06=marker_ok");
}
""",
            ),
            "b07_marker_trait_with_item_and_impl_e0714_e0715": _run_case(
                rustc,
                tmp,
                "b07_marker_e0714_e0715",
                """
#![feature(marker_trait_attr)]
#[marker]
pub trait M { fn bad(&self) {} }
impl M for u32 {}
fn main() {}
""",
                expect_run=False,
            ),
            "b08_marker_trait_impl_explicit_item_e0714_e0715": _run_case(
                rustc,
                tmp,
                "b08_marker_item_e0715",
                """
#![feature(marker_trait_attr)]
#[marker]
pub trait M { const X: u32 = 1; }
impl M for u32 { const X: u32 = 2; }
fn main() {}
""",
                expect_run=False,
            ),
        }

        # ------------------------------------------------------------------
        # Part C: Negative Impls & with_negative_coherence
        # ------------------------------------------------------------------
        part_c = {
            "c01_overlap_without_negative_impl_e0119": _run_case(
                rustc,
                tmp,
                "c01_no_neg_e0119",
                """
trait Marker { fn tag() -> u32; }
struct Local(u32);
impl<T: Send> Marker for T { fn tag() -> u32 { 1 } }
impl Marker for Local { fn tag() -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "c02_local_negative_impl_send_without_with_negative_coherence_ok": _run_case(
                rustc,
                tmp,
                "c02_stable_local_ok",
                """
#![feature(negative_impls)]
trait Marker { fn tag() -> u32; }
struct Local(u32);
impl !Send for Local {}
impl<T: Send> Marker for T { fn tag() -> u32 { 1 } }
impl Marker for Local { fn tag() -> u32 { 2 } }
fn main() {
    let _ = Local(0).0;
    println!("C02={},{}", <u32 as Marker>::tag(), <Local as Marker>::tag());
}
""",
            ),
            "c03_negative_impl_send_with_negative_coherence_ok": _run_case(
                rustc,
                tmp,
                "c03_neg_send_ok",
                """
#![feature(negative_impls, with_negative_coherence)]
trait Marker { fn tag() -> u32; }
struct Local(u32);
impl !Send for Local {}
impl<T: Send> Marker for T { fn tag() -> u32 { 1 } }
impl Marker for Local { fn tag() -> u32 { 2 } }
fn main() {
    let _ = Local(0).0;
    println!("C03={},{}", <u32 as Marker>::tag(), <Local as Marker>::tag());
}
""",
            ),
            "c04_negative_impl_custom_trait_with_negative_coherence_ok": _run_case(
                rustc,
                tmp,
                "c04_neg_custom_ok",
                """
#![feature(negative_impls, with_negative_coherence)]
trait CustomBound {}
impl CustomBound for u32 {}
struct Local(u32);
impl !CustomBound for Local {}
trait Classify { fn cls() -> u32; }
impl<T: CustomBound> Classify for T { fn cls() -> u32 { 10 } }
impl Classify for Local { fn cls() -> u32 { 20 } }
fn main() {
    let _ = Local(0).0;
    println!("C04={},{}", <u32 as Classify>::cls(), <Local as Classify>::cls());
}
""",
            ),
            "c05_negative_impl_foreign_trait_for_local_and_overlap_ok": _run_case(
                rustc,
                tmp,
                "c05_neg_foreign_ok",
                """
#![feature(negative_impls, with_negative_coherence)]
use up::ForeignBlanketTrait;
struct Local(u32);
impl !ForeignBlanketTrait for Local {}
trait Classify { fn cls() -> u32; }
impl<T: ForeignBlanketTrait> Classify for T { fn cls() -> u32 { 100 } }
impl Classify for Local { fn cls() -> u32 { 200 } }
fn main() {
    let _ = Local(0).0;
    println!("C05={}", <Local as Classify>::cls());
}
""",
                extra_args=extern_up,
            ),
            "c06a_cross_crate_negative_impl_without_with_negative_coherence_e0119": _run_case(
                rustc,
                tmp,
                "c06a_cross_crate_stable_e0119",
                """
use up_neg::{UpNegStruct, UpNegTrait};
trait CrossClassify { fn kind() -> &'static str; }
impl<T: UpNegTrait> CrossClassify for T { fn kind() -> &'static str { "pos" } }
impl CrossClassify for UpNegStruct { fn kind() -> &'static str { "up_negstruct" } }
fn main() {}
""",
                extra_args=extern_up_neg,
                expect_run=False,
            ),
            "c06b_cross_crate_negative_impl_with_negative_coherence_ok": _run_case(
                rustc,
                tmp,
                "c06b_cross_crate_neg_ok",
                """
#![feature(with_negative_coherence)]
use up_neg::{UpNegStruct, UpNegTrait, UpNoSend};
trait CrossClassify { fn kind() -> &'static str; }
impl<T: Send + UpNegTrait> CrossClassify for T { fn kind() -> &'static str { "pos" } }
impl CrossClassify for UpNoSend { fn kind() -> &'static str { "up_nosend" } }
impl CrossClassify for UpNegStruct { fn kind() -> &'static str { "up_negstruct" } }
fn main() {
    println!("C06B={},{}", <UpNoSend as CrossClassify>::kind(), <UpNegStruct as CrossClassify>::kind());
}
""",
                extra_args=extern_up_neg,
            ),
            "c07_foreign_rc_without_negative_coherence_e0119": _run_case(
                rustc,
                tmp,
                "c07_rc_stable_e0119",
                """
use std::rc::Rc;
trait Classify { fn cls() -> u32; }
impl<T: Send> Classify for T { fn cls() -> u32 { 1 } }
impl<T> Classify for Rc<T> { fn cls() -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "c08_foreign_rc_with_negative_coherence_ok": _run_case(
                rustc,
                tmp,
                "c08_rc_neg_coh_ok",
                """
#![feature(with_negative_coherence)]
use std::rc::Rc;
trait Classify { fn cls() -> u32; }
impl<T: Send> Classify for T { fn cls() -> u32 { 1 } }
impl<T> Classify for Rc<T> { fn cls() -> u32 { 2 } }
fn main() {
    println!("C08={},{}", <u32 as Classify>::cls(), <Rc<u32> as Classify>::cls());
}
""",
            ),
            "c09_negative_impl_with_items_rejected_e0749": _run_case(
                rustc,
                tmp,
                "c09_neg_items_e0749",
                """
#![feature(negative_impls)]
trait Foo { fn bar(&self); }
struct Local(u32);
impl !Foo for Local { fn bar(&self) {} }
fn main() {}
""",
                expect_run=False,
            ),
            "c10_negative_positive_conflict_e0751": _run_case(
                rustc,
                tmp,
                "c10_neg_pos_e0751",
                """
#![feature(negative_impls)]
trait Foo {}
struct Local(u32);
impl Foo for Local {}
impl !Foo for Local {}
fn main() {}
""",
                expect_run=False,
            ),
            "c11_negative_auto_trait_specialized_rejected_e0366": _run_case(
                rustc,
                tmp,
                "c11_neg_spec_e0366",
                """
#![feature(negative_impls)]
struct Wrap<T>(T);
impl !Send for Wrap<u32> {}
fn main() {}
""",
                expect_run=False,
            ),
        }

        # ------------------------------------------------------------------
        # Part D: Real zerocopy-Style Coherence Patterns
        # ------------------------------------------------------------------
        part_d = {
            "d01_zerocopy_style_disjoint_reason_markers_and_occurs_check_ok": _run_case(
                rustc,
                tmp,
                "d01_zc_coherence_ok",
                """
use core::mem::ManuallyDrop;

pub trait Aliasing {}
pub enum Shared {}
pub enum Exclusive {}
impl Aliasing for Shared {}
impl Aliasing for Exclusive {}

pub trait Validity {}
pub enum Safe {}
pub enum Initialized {}
impl Validity for Safe {}
impl Validity for Initialized {}

pub unsafe trait Immutable {}
unsafe impl Immutable for u32 {}
unsafe impl<T: ?Sized + Immutable> Immutable for ManuallyDrop<T> {}

pub enum BecauseImmutable {}
pub enum BecauseExclusive {}
pub trait Read<A: Aliasing, R> {}
impl<A: Aliasing, T: ?Sized + Immutable> Read<A, BecauseImmutable> for T {}
impl<T: ?Sized> Read<Exclusive, BecauseExclusive> for T {}

pub unsafe trait TransmuteFrom<Src: ?Sized, SV: Validity, DV: Validity> {}
unsafe impl<T: ?Sized, V: Validity> TransmuteFrom<T, V, V> for T {}
unsafe impl<T: ?Sized, V: Validity> TransmuteFrom<T, V, V> for ManuallyDrop<T> {}
unsafe impl<T: ?Sized, V: Validity> TransmuteFrom<ManuallyDrop<T>, V, V> for T {}

pub unsafe trait SharedCompatible<T: ?Sized> {}
unsafe impl<T: ?Sized> SharedCompatible<T> for T {}
unsafe impl<T: ?Sized> SharedCompatible<T> for ManuallyDrop<T> {}
unsafe impl<T: ?Sized> SharedCompatible<ManuallyDrop<T>> for T {}

pub enum BecauseRead {}
pub enum BecauseSharedCompatible {}
pub unsafe trait MutationCompatible<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R> {}
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>
    MutationCompatible<Src, A, SV, DV, (BecauseRead, R)> for Dst
where
    Src: Read<A, R>,
    Dst: Read<A, R>,
{}
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity>
    MutationCompatible<Src, A, SV, DV, BecauseSharedCompatible> for Dst
where
    Src: TransmuteFrom<Dst, DV, SV>,
    Dst: TransmuteFrom<Src, SV, DV> + SharedCompatible<Src>,
{}

pub enum BecauseMutationCompatible {}
pub unsafe trait TryTransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R> {}
unsafe impl<Src: ?Sized, Dst: ?Sized, SV: Validity, DV: Validity, A: Aliasing, R>
    TryTransmuteFromPtr<Src, A, SV, DV, (BecauseMutationCompatible, R)> for Dst
where
    Src: TransmuteFrom<Dst, DV, SV>,
    Dst: MutationCompatible<Src, A, SV, DV, R>,
{}
unsafe impl<Src: ?Sized, Dst: ?Sized, SV: Validity, DV: Validity>
    TryTransmuteFromPtr<Src, Shared, SV, DV, BecauseImmutable> for Dst
where
    Src: Immutable,
    Dst: Immutable,
{}

fn check_ptr<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>() -> &'static str
where
    Dst: TryTransmuteFromPtr<Src, A, SV, DV, R>,
{
    "ok"
}

fn main() {
    let r1 = check_ptr::<u32, ManuallyDrop<u32>, Shared, Safe, Safe, (BecauseMutationCompatible, BecauseSharedCompatible)>();
    let r2 = check_ptr::<u32, u32, Shared, Safe, Safe, BecauseImmutable>();
    let r3 = check_ptr::<u32, u32, Exclusive, Safe, Safe, (BecauseMutationCompatible, (BecauseRead, BecauseExclusive))>();
    println!("D01={},{},{}", r1, r2, r3);
}
""",
            ),
            "d02_zerocopy_style_omitting_reason_param_triggers_e0119": _run_case(
                rustc,
                tmp,
                "d02_zc_no_reason_e0119",
                """
pub trait Aliasing {}
pub enum Shared {}
impl Aliasing for Shared {}
pub trait Read<A: Aliasing> {}
pub unsafe trait SharedCompatible<T: ?Sized> {}
pub unsafe trait MutationCompatible<Src: ?Sized, A: Aliasing> {}

unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing> MutationCompatible<Src, A> for Dst
where
    Src: Read<A>,
    Dst: Read<A>,
{}
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing> MutationCompatible<Src, A> for Dst
where
    Dst: SharedCompatible<Src>,
{}
fn main() {}
""",
                expect_run=False,
            ),
            "d03_zerocopy_style_downstream_fundamental_ok_vs_vec_e0117": {
                "fundamental_ok": _run_case(
                    rustc,
                    tmp,
                    "d03a_zc_fund_ok",
                    """
use std::pin::Pin;
use up::{ZcImmutable, ZcMarkerLike};

struct UserStruct(u32);
impl ZcMarkerLike for UserStruct {
    fn zc_tag(&self) -> &'static str { "user" }
}
impl ZcMarkerLike for Box<UserStruct> {
    fn zc_tag(&self) -> &'static str { "box_user" }
}
impl ZcMarkerLike for &UserStruct {
    fn zc_tag(&self) -> &'static str { "ref_user" }
}
impl ZcMarkerLike for Pin<&UserStruct> {
    fn zc_tag(&self) -> &'static str { "pin_ref_user" }
}

fn require_imm<T: ZcImmutable>() -> bool { true }

fn main() {
    let u = UserStruct(5);
    let b = Box::new(UserStruct(6));
    let r: &UserStruct = &u;
    let p = Pin::new(&u);
    println!(
        "D03={},{},{},{}",
        u.zc_tag(),
        b.zc_tag(),
        <&UserStruct as ZcMarkerLike>::zc_tag(&r),
        p.zc_tag()
    );
    assert!(require_imm::<Box<u32>>());
    assert!(require_imm::<&u32>());
}
""",
                    extra_args=extern_up,
                ),
                "vec_rejected_e0117": _run_case(
                    rustc,
                    tmp,
                    "d03b_zc_vec_e0117",
                    """
use up::ZcMarkerLike;
struct UserStruct(u32);
impl ZcMarkerLike for Vec<UserStruct> {
    fn zc_tag(&self) -> &'static str { "vec_user" }
}
fn main() {}
""",
                    extra_args=extern_up,
                    expect_run=False,
                ),
            },
        }

    return {
        "schema_version": 1,
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_ver,
        "total_cases": (
            len(part_a)
            + len(part_b)
            + len(part_c)
            + sum(1 if "compile_rc" in v else len(v) for v in part_d.values())
        ),
        "part_a_orphan_and_fundamental": part_a,
        "part_b_overlap_inherent_and_marker": part_b,
        "part_c_negative_impls_and_coherence": part_c,
        "part_d_zerocopy_coherence_patterns": part_d,
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
