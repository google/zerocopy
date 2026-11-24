#!/usr/bin/env python3
"""Standalone empirical probe suite for rustc implied bounds, RFC 2093 outlives
inference, WF checking asymmetries, supertrait elaboration, and associated-type
projection normalization.

Executes every test case in an isolated `with tempfile.TemporaryDirectory():`
environment using Python 3.10+ standard library only and records verbatim
compiler exit codes, sanitized stderr diagnostics, runtime outputs, and
`#[rustc_dump_inferred_outlives]` dumps.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class ProbeCase:
    group: str
    case_id: str
    description: str
    expect_compile_rc: int
    expect_stdout: str | None
    expect_error_codes: tuple[str, ...]
    extra_flags: tuple[str, ...]
    source: str


PROBE_CASES: tuple[ProbeCase, ...] = (
    # Group A: Implied bounds & RFC 2093 outlives inference boundaries
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="fn_implied_ref_ok",
        description="Function input &'a T supplies implied bound T: 'a via assumed_wf_types.",
        expect_compile_rc=0,
        expect_stdout="IMPLIED_FN_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
fn need<'a, T: 'a>() {}
fn f<'a, T>(_r: &'a T) {
    need::<'a, T>();
}
fn main() {
    let x = 1u32;
    f(&x);
    println!("IMPLIED_FN_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="fn_implied_return_ok",
        description="Function return type Option<&'a T> is in assumed_wf_types (inputs_and_output) and implies T: 'a.",
        expect_compile_rc=0,
        expect_stdout="IMPLIED_RET_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
fn need<'a, T: 'a>() {}
fn f<'a, T>() -> Option<&'a T> {
    need::<'a, T>();
    None
}
fn main() {
    let _r: Option<&u32> = f::<u32>();
    println!("IMPLIED_RET_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_ref_rfc2093_ok",
        description="RFC 2093 infers T: 'a on struct Ref<'a, T>(&'a T) without explicit where clause.",
        expect_compile_rc=0,
        expect_stdout="RFC2093_STRUCT_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
struct Ref<'a, T>(&'a T);
fn main() {
    let x = 1u32;
    let _r = Ref(&x);
    println!("RFC2093_STRUCT_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_mutual_rec_fixpoint_ok",
        description="Fixed-point inferred_outlives_of propagates T: 'a across Inner -> Outer <-> Either.",
        expect_compile_rc=0,
        expect_stdout="MUTUAL_FIXPOINT_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
struct Inner<'b, U>(&'b U);
#[allow(dead_code)]
enum Either<'a, T> {
    Empty,
    Next(Box<Outer<'a, T>>),
}
#[allow(dead_code)]
struct Outer<'a, T> {
    inner: Inner<'a, T>,
    next: Either<'a, T>,
}
fn need<'a, T: 'a>() {}
fn check<'a, T>(_: Outer<'a, T>) {
    need::<'a, T>();
}
fn main() {
    let x = 7u32;
    let o = Outer { inner: Inner(&x), next: Either::Empty };
    check(o);
    println!("MUTUAL_FIXPOINT_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_union_enum_rfc2093_ok",
        description="RFC 2093 infers T: 'a for Struct, Enum, and Union definitions.",
        expect_compile_rc=0,
        expect_stdout="UNION_ENUM_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
union U<'a, T: Copy> {
    r: &'a T,
    tag: u8,
}
#[allow(dead_code)]
enum E<'a, T> {
    Ref(&'a T),
    None,
}
fn need<'a, T: 'a>() {}
fn check_u<'a, T: Copy>(_: U<'a, T>) {
    need::<'a, T>();
}
fn check_e<'a, T>(_: E<'a, T>) {
    need::<'a, T>();
}
fn main() {
    let v = 3u32;
    check_u(U { r: &v });
    check_e(E::Ref(&v));
    println!("UNION_ENUM_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_ref_impl_inherits_rfc2093_ok",
        description="Inherent impl<'a, T> Ref<'a, T> inherits RFC 2093 T: 'a bound via assumed_wf_types(Impl).",
        expect_compile_rc=0,
        expect_stdout="IMPL_INHERIT_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
struct Ref<'a, T>(&'a T);
fn need<'a, T: 'a>() {}
impl<'a, T> Ref<'a, T> {
    fn check(&self) {
        need::<'a, T>();
    }
}
fn main() {
    let x = 1u32;
    Ref(&x).check();
    println!("IMPL_INHERIT_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_static_ref_no_outlives_e0310",
        description="is_free_region(ReStatic) == false prevents inferring T: 'static on StaticRef<T>(&'static T), causing E0310.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0310",),
        extra_flags=(),
        source="""\
struct StaticRef<T>(&'static T);
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="fn_implied_static_ref_ok",
        description="Function input &'static T implies T: 'static (implied_outlives_bounds keeps ReStatic, unlike RFC 2093).",
        expect_compile_rc=0,
        expect_stdout="FN_STATIC_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
fn need_static<T: 'static>() {}
fn fn_takes_static<T>(_x: &'static T) {
    need_static::<T>();
}
fn main() {
    fn_takes_static(&42u32);
    println!("FN_STATIC_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="impl_for_static_ref_ok",
        description="impl<T> StaticTr for &'static T assumes &'static T is WF, implying T: 'static inside impl body.",
        expect_compile_rc=0,
        expect_stdout="IMPL_STATIC_OK=7",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait StaticTr {
    fn check(&self) -> u32;
}
fn need_static<T: 'static>() {}
impl<T> StaticTr for &'static T {
    fn check(&self) -> u32 {
        need_static::<T>();
        7
    }
}
fn main() {
    let r: &'static u32 = &42;
    println!("IMPL_STATIC_OK={}", r.check());
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_static_ref_explicit_ok",
        description="Explicit T: 'static satisfies WF on StaticRef<T: 'static>(&'static T).",
        expect_compile_rc=0,
        expect_stdout="STATIC_EXPLICIT_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
struct StaticRef<T: 'static>(&'static T);
static VAL: u32 = 9;
fn main() {
    let _s = StaticRef(&VAL);
    println!("STATIC_EXPLICIT_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_nested_static_ref_e0310",
        description="Wrapping StaticRef<U: 'static> in Wrapper<U> does not propagate T: 'static via inferred_outlives_of (E0310).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0310",),
        extra_flags=(),
        source="""\
struct StaticRef<T: 'static>(&'static T);
struct Wrapper<U>(StaticRef<U>);
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_for_binder_late_bound_ok",
        description="Late-bound region 'b in for<'b> fn(&'b T) is excluded by is_free_region(ReBound) == false.",
        expect_compile_rc=0,
        expect_stdout="LATE_BOUND_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#[allow(dead_code)]
struct FnHolder<T>(for<'b> fn(&'b T));
fn take_u32(_: &u32) {}
fn main() {
    let local = 5u32;
    let _h1 = FnHolder::<&u32>(|_: &&u32| {});
    let _h2 = FnHolder::<u32>(take_u32);
    let _ = &local;
    println!("LATE_BOUND_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_proj_allows_assoc_outlives_ok",
        description="Component::Alias infers <T as Id>::Out: 'a on Wrap<'a, T: Id>(&'a <T as Id>::Out).",
        expect_compile_rc=0,
        expect_stdout="PROJ_ASSOC_OUTLIVES_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Id {
    type Out;
}
#[allow(dead_code)]
struct Wrap<'a, T: Id>(&'a <T as Id>::Out);
fn req_outlives<'a, U: 'a>() {}
fn check_assoc<'a, T: Id>(_: Wrap<'a, T>) {
    req_outlives::<'a, <T as Id>::Out>();
}
struct Unit;
impl Id for Unit {
    type Out = u32;
}
fn main() {
    let v = 3u32;
    check_assoc(Wrap::<Unit>(&v));
    println!("PROJ_ASSOC_OUTLIVES_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_proj_rejects_param_outlives_e0309",
        description="Wrap<'a, T: Id>(&'a <T as Id>::Out) infers <T as Id>::Out: 'a, NOT T: 'a (E0309).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=(),
        source="""\
trait Id {
    type Out;
}
struct Wrap<'a, T: Id>(&'a <T as Id>::Out);
fn req_outlives<'a, U: 'a>() {}
fn check_param<'a, T: Id>(_: Wrap<'a, T>) {
    req_outlives::<'a, T>();
}
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="struct_proj_unnormalized_impl_e0309",
        description="RFC 2093 walks unnormalized projections and ignores impl where bounds, causing E0309 on struct Holder.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=(),
        source="""\
trait MakeRef<'a> {
    type Type;
}
impl<'a, T: 'a> MakeRef<'a> for Vec<T> {
    type Type = &'a T;
}
struct Holder<'a, T> {
    field: <Vec<T> as MakeRef<'a>>::Type,
}
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="type_alias_unchecked_ok",
        description="Default (non-lazy/unchecked) type alias &'a T skips inferred_outlives_of and WF checking.",
        expect_compile_rc=0,
        expect_stdout="LAZY_ALIAS_OK=11",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
type UncheckedAlias<'a, T> = &'a T;
fn main() {
    let x = 11u32;
    let r: UncheckedAlias<'_, u32> = &x;
    println!("LAZY_ALIAS_OK={}", *r);
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="type_alias_unchecked_static_ok",
        description="Default unchecked type alias &'static T is accepted without T: 'static until instantiated.",
        expect_compile_rc=0,
        expect_stdout="STATIC_ALIAS_UNCHECKED=42",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
type StaticAlias<T> = &'static T;
static V: u32 = 42;
fn main() {
    let r: StaticAlias<u32> = &V;
    println!("STATIC_ALIAS_UNCHECKED={}", *r);
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="type_alias_lazy_checked_static_e0310",
        description="With #![feature(lazy_type_alias)], StaticAlias<T> = &'static T undergoes WF check and fails E0310.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0310",),
        extra_flags=(),
        source="""\
#![feature(lazy_type_alias)]
type StaticAlias<T> = &'static T;
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="type_alias_lazy_checked_early_ok",
        description="With #![feature(lazy_type_alias)], CheckedAlias<'a, T> = &'a T infers T: 'a and succeeds.",
        expect_compile_rc=0,
        expect_stdout="CHECKED_ALIAS_OK=12",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#![feature(lazy_type_alias)]
type CheckedAlias<'a, T> = &'a T;
fn main() {
    let x = 12u32;
    let r: CheckedAlias<'_, u32> = &x;
    println!("CHECKED_ALIAS_OK={}", *r);
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="trait_impl_for_ref_requires_wf_ok",
        description="impl<'a, T> MyTrait for &'a T assumes &'a T is WF, implying T: 'a inside impl methods.",
        expect_compile_rc=0,
        expect_stdout="IMPL_FOR_REF_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait MyTrait {
    fn ping(&self) -> u32;
}
fn need<'a, T: 'a>() {}
impl<'a, T> MyTrait for &'a T {
    fn ping(&self) -> u32 {
        need::<'a, T>();
        1
    }
}
fn main() {
    let x = 1u32;
    let r = &x;
    println!("IMPL_FOR_REF_OK={}", r.ping());
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="trait_method_caller_missing_implied_e0309",
        description="Trait header Tr<'a, T> does not imply T: 'a at caller site (assumed_wf_types(Trait) is empty -> E0309).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=(),
        source="""\
trait Tr<'a, T> {}
fn need<'a, T: 'a>() {}
fn caller<'a, T, X: Tr<'a, T>>(_x: X) {
    need::<'a, T>();
}
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="assoc_type_ref_missing_outlives_e0309",
        description="Associated type RHS &'a T in impl<'a, T> Assoc<'a, T> for S does not imply T: 'a (E0309).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=(),
        source="""\
trait Assoc<'a, T> {
    type Out;
}
struct S;
impl<'a, T> Assoc<'a, T> for S {
    type Out = &'a T;
}
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="rfc2093_runs_after_default_object_bound",
        description="RFC 599/1156 default object lifetime runs before RFC 2093, defaulting InferredRef<'a, dyn Dummy> to +'static.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Dummy {}
struct InferredRef<'a, T: ?Sized>(&'a T);
fn default_obj<'a>(x: &'a dyn Dummy) -> InferredRef<'a, dyn Dummy> {
    InferredRef(x)
}
fn main() {}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="explicit_outlives_changes_default_object_bound_ok",
        description="Explicit where T: 'a changes trait object default in ExplicitRef<'a, dyn Dummy> to +'a.",
        expect_compile_rc=0,
        expect_stdout="OBJ_DEFAULT_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Dummy {}
#[allow(dead_code)]
struct ExplicitRef<'a, T: 'a + ?Sized>(&'a T);
fn default_obj<'a>(x: &'a dyn Dummy) -> ExplicitRef<'a, dyn Dummy> {
    ExplicitRef(x)
}
impl Dummy for u32 {}
fn main() {
    let x = 1u32;
    let _r = default_obj(&x);
    println!("OBJ_DEFAULT_OK=1");
}
""",
    ),
    ProbeCase(
        group="a_implied_bounds_and_rfc2093_boundaries",
        case_id="rustc_dump_inferred_outlives_oracle",
        description="Direct compiler dump via #[rustc_dump_inferred_outlives] confirming exact inferred_outlives_of sets.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#![feature(rustc_attrs, lazy_type_alias)]
trait Id {
    type Out;
}
#[rustc_dump_inferred_outlives]
struct Ref<'a, T>(&'a T);
#[rustc_dump_inferred_outlives]
struct StaticRef<T: 'static>(&'static T);
#[rustc_dump_inferred_outlives]
struct Wrap<'a, T: Id>(&'a <T as Id>::Out);
#[rustc_dump_inferred_outlives]
struct FnHolder<T>(for<'b> fn(&'b T));
#[rustc_dump_inferred_outlives]
struct Outer<'a, T> {
    inner: Ref<'a, T>,
    next: Box<Either<'a, T>>,
}
#[rustc_dump_inferred_outlives]
enum Either<'a, T> {
    Empty,
    Next(Box<Outer<'a, T>>),
}
#[rustc_dump_inferred_outlives]
struct NestedStatic<U: 'static>(StaticRef<U>);
#[rustc_dump_inferred_outlives]
type CheckedAlias<'a, T> = &'a T;
fn main() {}
""",
    ),
    # Group B: Supertrait elaboration, PredicateFilter asymmetry, projection normalization, and struct where-bounds
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="supertrait_elaboration_and_norm_ok",
        description="Supertrait bound Sub: Base<Item = u32> elaborates into T: Base and <T as Base>::Item == u32.",
        expect_compile_rc=0,
        expect_stdout="SUPERTRAIT_NORM=42",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Base {
    type Item;
    fn get() -> Self::Item;
}
trait Sub: Base<Item = u32> {}
fn take<T: Sub>() -> u32 {
    T::get()
}
struct Impl;
impl Base for Impl {
    type Item = u32;
    fn get() -> u32 {
        42
    }
}
impl Sub for Impl {}
fn main() {
    println!("SUPERTRAIT_NORM={}", take::<Impl>());
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="trait_param_bound_not_implied_by_filter_e0309",
        description="PredicateFilter::SelfAndAssociatedTypeBounds excludes non-Self param bound T: 'a on trait Tr<'a, T: 'a> (E0309).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=(),
        source="""\
trait Tr<'a, T: 'a> {}
fn need<'a, T: 'a>() {}
fn caller<'a, T, X: Tr<'a, T>>(_x: X) {
    need::<'a, T>();
}
fn main() {}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="trait_self_outlives_elaborates_ok",
        description="PredicateFilter::SelfAndAssociatedTypeBounds elaborates Self: 'a from trait Tr<'a>: 'a into caller ParamEnv.",
        expect_compile_rc=0,
        expect_stdout="SELF_ELAB_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Tr<'a>: 'a {}
fn need<'a, X: 'a>() {}
fn caller<'a, X: Tr<'a>>(_x: X) {
    need::<'a, X>();
}
struct S;
impl<'a> Tr<'a> for S {}
fn main() {
    caller(S);
    println!("SELF_ELAB_OK=1");
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="trait_assoc_outlives_elaborates_ok",
        description="PredicateFilter::SelfAndAssociatedTypeBounds elaborates Self::Assoc: 'a from trait Tr<'a> { type Assoc: 'a; }.",
        expect_compile_rc=0,
        expect_stdout="ASSOC_ELAB_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Tr<'a> {
    type Assoc: 'a;
}
fn need<'a, U: 'a>() {}
fn caller<'a, X: Tr<'a>>() {
    need::<'a, X::Assoc>();
}
struct S;
impl<'a> Tr<'a> for S {
    type Assoc = u32;
}
fn main() {
    caller::<S>();
    println!("ASSOC_ELAB_OK=1");
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="trait_alias_all_filter_elaborates_ok",
        description="Trait aliases use PredicateFilter::All, elaborating non-Self T: 'a in caller<'a, T, X: Alias<'a, T>>.",
        expect_compile_rc=0,
        expect_stdout="TRAIT_ALIAS_ELAB_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
#![feature(trait_alias)]
trait Base<'a, T: 'a> {}
trait Alias<'a, T: 'a> = Base<'a, T>;
fn need<'a, T: 'a>() {}
fn caller<'a, T, X: Alias<'a, T>>(_x: X) {
    need::<'a, T>();
}
struct S;
impl<'a, T: 'a> Base<'a, T> for S {}
fn main() {
    caller::<u32, S>(S);
    println!("TRAIT_ALIAS_ELAB_OK=1");
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="diamond_consistent_supertrait_proj_ok",
        description="Consistent diamond supertraits (Left: Base<Item=u32>, Right: Base<Item=u32>) deduplicate in ProjectionCandidateSet.",
        expect_compile_rc=0,
        expect_stdout="DIAMOND_NORM=99",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Base {
    type Item;
}
trait Left: Base<Item = u32> {}
trait Right: Base<Item = u32> {}
trait Both: Left + Right {}
fn take<T: Both>(x: <T as Base>::Item) -> u32 {
    x
}
struct Impl;
impl Base for Impl {
    type Item = u32;
}
impl Left for Impl {}
impl Right for Impl {}
impl Both for Impl {}
fn main() {
    println!("DIAMOND_NORM={}", take::<Impl>(99));
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="diamond_conflicting_supertrait_proj_e0284",
        description="Conflicting diamond supertrait projections produce ProjectionCandidateSet::Ambiguous -> E0284.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0284",),
        extra_flags=(),
        source="""\
trait Base {
    type Item;
}
trait Left: Base<Item = u32> {}
trait Right: Base<Item = i32> {}
trait Both: Left + Right {}
fn take<T: Both>(x: <T as Base>::Item) -> u32 {
    x
}
fn main() {}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="normalized_sig_implies_inner_outlives_ok",
        description="deeply_normalize before compute_implied_outlives_bounds extracts U: 'a from T: Id<Out = &'a U> input T::Out.",
        expect_compile_rc=0,
        expect_stdout="NORM_IMPLIED_OK=1",
        expect_error_codes=(),
        extra_flags=(),
        source="""\
trait Id {
    type Out;
}
fn need<'a, T: 'a>() {}
fn f<'a, U, T: Id<Out = &'a U>>(_x: T::Out) {
    need::<'a, U>();
}
struct S;
impl Id for S {
    type Out = &'static u32;
}
fn main() {
    f::<u32, S>(&1);
    println!("NORM_IMPLIED_OK=1");
}
""",
    ),
    ProbeCase(
        group="b_supertrait_elaboration_and_projection_norm",
        case_id="struct_where_not_implied_in_impl_e0277",
        description="Struct trait where-bound NeedEq<T: PartialEq> is not implied into impl<T> NeedEq<T> (E0277 + E0369).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0277", "E0369"),
        extra_flags=(),
        source="""\
struct NeedEq<T: PartialEq>(T);
impl<T> NeedEq<T> {
    fn same(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
fn main() {}
""",
    ),
    # Group C: -Znext-solver differential spot checks on key boundaries
    ProbeCase(
        group="c_next_solver_differential",
        case_id="next_solver_fn_implied_ref_ok",
        description="With -Znext-solver: fn f<'a, T>(&'a T) still implies T: 'a.",
        expect_compile_rc=0,
        expect_stdout="NEXT_FN_OK=1",
        expect_error_codes=(),
        extra_flags=("-Znext-solver",),
        source="""\
fn need<'a, T: 'a>() {}
fn f<'a, T>(_r: &'a T) {
    need::<'a, T>();
}
fn main() {
    let x = 1u32;
    f(&x);
    println!("NEXT_FN_OK=1");
}
""",
    ),
    ProbeCase(
        group="c_next_solver_differential",
        case_id="next_solver_static_ref_e0310",
        description="With -Znext-solver: StaticRef<T>(&'static T) still rejects with E0310.",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0310",),
        extra_flags=("-Znext-solver",),
        source="""\
struct StaticRef<T>(&'static T);
fn main() {}
""",
    ),
    ProbeCase(
        group="c_next_solver_differential",
        case_id="next_solver_trait_param_bound_e0309",
        description="With -Znext-solver: trait Tr<'a, T: 'a> still rejects caller without T: 'a (E0309).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0309",),
        extra_flags=("-Znext-solver",),
        source="""\
trait Tr<'a, T: 'a> {}
fn need<'a, T: 'a>() {}
fn caller<'a, T, X: Tr<'a, T>>(_x: X) {
    need::<'a, T>();
}
fn main() {}
""",
    ),
    ProbeCase(
        group="c_next_solver_differential",
        case_id="next_solver_supertrait_norm_ok",
        description="With -Znext-solver: supertrait elaboration and projection normalization succeed.",
        expect_compile_rc=0,
        expect_stdout="NEXT_SUPERTRAIT_NORM=42",
        expect_error_codes=(),
        extra_flags=("-Znext-solver",),
        source="""\
trait Base {
    type Item;
    fn get() -> Self::Item;
}
trait Sub: Base<Item = u32> {}
fn take<T: Sub>() -> u32 {
    T::get()
}
struct Impl;
impl Base for Impl {
    type Item = u32;
    fn get() -> u32 {
        42
    }
}
impl Sub for Impl {}
fn main() {
    println!("NEXT_SUPERTRAIT_NORM={}", take::<Impl>());
}
""",
    ),
    ProbeCase(
        group="c_next_solver_differential",
        case_id="next_solver_struct_where_not_implied_e0277",
        description="With -Znext-solver: struct where NeedEq<T: PartialEq> is still not implied in impl<T> NeedEq<T> (E0277).",
        expect_compile_rc=1,
        expect_stdout=None,
        expect_error_codes=("E0277", "E0369"),
        extra_flags=("-Znext-solver",),
        source="""\
struct NeedEq<T: PartialEq>(T);
impl<T> NeedEq<T> {
    fn same(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
fn main() {}
""",
    ),
)


def sanitize_output(text: str, tmp_dir: Path) -> str:
    return text.replace(str(tmp_dir), "<tmp>")


def extract_rustc_metadata(rustc_bin: str) -> dict[str, str]:
    proc = subprocess.run([rustc_bin, "-Vv"], capture_output=True, text=True, check=True)
    meta: dict[str, str] = {"raw": proc.stdout.strip()}
    for line in proc.stdout.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip()
        elif line.startswith("rustc "):
            meta["version_line"] = line.strip()
    return meta


def run_case(case: ProbeCase, rustc_bin: str, tmp_dir: Path) -> tuple[dict[str, Any], bool]:
    src_path = tmp_dir / f"{case.case_id}.rs"
    exe_path = tmp_dir / case.case_id
    src_path.write_text(case.source, encoding="utf-8")

    cmd = [rustc_bin, "--edition=2021", *case.extra_flags, str(src_path), "-o", str(exe_path)]
    comp = subprocess.run(cmd, capture_output=True, text=True, check=False)

    entry: dict[str, Any] = {
        "description": case.description,
        "extra_flags": list(case.extra_flags),
        "source_sha256": hashlib.sha256(case.source.encode("utf-8")).hexdigest(),
        "compile_returncode": comp.returncode,
        "compile_stderr": sanitize_output(comp.stderr.strip(), tmp_dir),
    }

    ok = comp.returncode == case.expect_compile_rc
    for code in case.expect_error_codes:
        if f"error[{code}]" not in comp.stderr:
            ok = False

    if comp.returncode == 0 and exe_path.exists():
        run_proc = subprocess.run([str(exe_path)], capture_output=True, text=True, check=False)
        entry["run_returncode"] = run_proc.returncode
        entry["run_stdout"] = run_proc.stdout.strip()
        entry["run_stderr"] = sanitize_output(run_proc.stderr.strip(), tmp_dir)
        if run_proc.returncode != 0:
            ok = False
        if case.expect_stdout is not None and entry["run_stdout"] != case.expect_stdout:
            ok = False

    if case.case_id == "rustc_dump_inferred_outlives_oracle":
        # Verify exact compiler dump notes appear cleanly.
        required_notes = ("note: T: 'a", "note: <T as Id>::Out: 'a")
        if not all(note in comp.stderr for note in required_notes):
            ok = False

    entry["passed"] = ok
    return entry, ok


def render_summary(results: dict[str, Any]) -> str:
    lines = [
        "# Probe Summary: Implied Bounds, RFC 2093, Projection Normalization, and Supertraits",
        "",
        f"- Compiler: `{results['rustc_version'].get('version_line', 'unknown')}` (`commit-hash: {results['rustc_version'].get('commit-hash', 'unknown')}`)",
        f"- Total checks: `{results['summary']['passed']}/{results['summary']['total']}` passed",
        "",
        "| Group | Case ID | Compile RC | Result | Key Diagnostic / Stdout |",
        "| :--- | :--- | :---: | :---: | :--- |",
    ]
    for group_name, cases in results["experiments"].items():
        for cid, info in cases.items():
            rc = info["compile_returncode"]
            status = "PASS" if info["passed"] else "FAIL"
            if rc == 0:
                detail = f"`{info.get('run_stdout', '')}`"
            else:
                first_err = next(
                    (ln for ln in info["compile_stderr"].splitlines() if ln.startswith("error")),
                    "(no error line)",
                )
                detail = f"`{first_err}`"
            lines.append(f"| `{group_name}` | `{cid}` | `{rc}` | `{status}` | {detail} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rustc",
        default=os.environ.get("RUSTC", "rustc"),
        help="Path to rustc executable (default: rustc)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Output JSON path (default: support/probe_results.json)",
    )
    parser.add_argument(
        "--summary-md",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_summary.md",
        help="Output Markdown summary path (default: support/probe_summary.md)",
    )
    args = parser.parse_args()

    rustc_meta = extract_rustc_metadata(args.rustc)
    experiments: dict[str, dict[str, Any]] = {}
    total = 0
    passed = 0

    with tempfile.TemporaryDirectory(prefix="rustc_implied_bounds_probe_") as tmp:
        tmp_dir = Path(tmp)
        for case in PROBE_CASES:
            total += 1
            entry, ok = run_case(case, args.rustc, tmp_dir)
            if ok:
                passed += 1
            experiments.setdefault(case.group, {})[case.case_id] = entry

    payload: dict[str, Any] = {
        "rustc_version": rustc_meta,
        "summary": {
            "total": total,
            "passed": passed,
            "failed": total - passed,
        },
        "experiments": experiments,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.summary_md.write_text(render_summary(payload), encoding="utf-8")
    print(f"probe_implied_bounds_and_supertraits: {passed}/{total} checks passed")
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
