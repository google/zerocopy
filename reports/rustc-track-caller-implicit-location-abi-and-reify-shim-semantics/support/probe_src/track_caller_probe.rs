// `Location::caller()` regime matrix for `#[track_caller]`.
//
// Lines carrying an `@NAME` marker are located by the harness
// (`probe_track_caller_abi_and_shims.py`), which derives every expected line number from the
// marker positions; nothing below depends on absolute line numbers.
#![allow(dead_code)]
use std::hint::black_box;
use std::panic::Location;

type Pos = (u32, u32);

fn pos(l: &Location<'_>) -> Pos {
    (l.line(), l.column())
}

// ---- Regime 0: `Location::caller()` in an untracked function ----------------------------------
#[inline(never)]
fn untracked_self() -> Pos {
    pos(Location::caller()) // @UNTRACKED_SELF
}

// ---- Regime 1: direct call through a three-level tracked chain --------------------------------
#[track_caller]
#[inline(always)]
fn leaf_tracked() -> Pos {
    pos(Location::caller())
}

#[track_caller]
#[inline(always)]
fn mid_tracked() -> Pos {
    leaf_tracked() // @MID_BODY (never reported: `mid_tracked` is tracked)
}

#[track_caller]
#[inline(always)]
fn top_tracked() -> Pos {
    mid_tracked() // @TOP_BODY (never reported: `top_tracked` is tracked)
}

#[inline(never)]
fn direct_site() -> Pos {
    top_tracked() // @DIRECT_SITE
}

// ---- Regime 2: the same chain behind an untracked wrapper -------------------------------------
#[inline(always)]
fn untracked_wrapper() -> Pos {
    top_tracked() // @WRAPPER_DEF_SITE
}

#[inline(never)]
fn wrapper_site() -> Pos {
    untracked_wrapper() // @WRAPPER_CALL_SITE (never reported: the wrapper is untracked)
}

// ---- Regime 2b: a tracked function that reaches the chain through the untracked wrapper -------
#[track_caller]
#[inline(always)]
fn tracked_outer_via_wrapper() -> Pos {
    untracked_wrapper() // @TRACKED_OUTER_BODY (never reported)
}

#[inline(never)]
fn tracked_outer_site() -> Pos {
    tracked_outer_via_wrapper() // @TRACKED_OUTER_CALL_SITE (never reported)
}

// ---- Regime 3: reification to a function pointer ----------------------------------------------
#[track_caller]
#[inline(never)]
fn leaf_tracked_noinline() -> Pos { // @FNPTR_DEF
    pos(Location::caller())
}

#[inline(never)]
fn fp_sites() -> [Pos; 3] {
    let fp: fn() -> Pos = leaf_tracked_noinline; // @FNPTR_COERCE (never reported)
    let fp1 = fp(); // @FP1_CALL (never reported)
    let fp2 = black_box(fp)(); // @FP2_CALL (never reported)
    let direct = leaf_tracked_noinline(); // @FNPTR_DIRECT_CALL
    [fp1, fp2, direct]
}

// ---- Regime 4: the trait method declaration is `#[track_caller]`; impls inherit ---------------
trait DeclTracked {
    #[track_caller]
    fn m(&self) -> Pos;
    #[track_caller]
    fn provided(&self) -> Pos {
        pos(Location::caller())
    }
}
struct A;
impl DeclTracked for A {
    fn m(&self) -> Pos { // @DECL_TRACKED_IMPL_DEF (never reported)
        pos(Location::caller())
    }
}

// ---- Regime 5: only the impl method is `#[track_caller]` --------------------------------------
trait DeclUntracked {
    fn m(&self) -> Pos;
}
struct B;
impl DeclUntracked for B {
    #[track_caller]
    fn m(&self) -> Pos { // @IMPL_ONLY_DEF
        pos(Location::caller())
    }
}

#[inline(never)]
fn generic_site<T: DeclUntracked + ?Sized>(t: &T) -> Pos {
    t.m() // @GENERIC_SITE
}

#[inline(never)]
fn dyn_sites() -> [Pos; 6] {
    let a: &dyn DeclTracked = black_box(&A);
    let dyn_decl = a.m(); // @DYN_DECL_TRACKED_CALL
    let dyn_provided = a.provided(); // @DYN_PROVIDED_CALL
    let b: &dyn DeclUntracked = black_box(&B);
    let dyn_impl_only = b.m(); // @DYN_IMPL_ONLY_CALL (never reported)
    let static_impl_only = B.m(); // @STATIC_IMPL_ONLY_CALL
    let generic_static = generic_site(&B);
    let generic_dyn = generic_site(b);
    [dyn_decl, dyn_provided, dyn_impl_only, static_impl_only, generic_static, generic_dyn]
}

fn main() {
    let show = |name: &str, v: Pos| println!("{name}={}:{}", v.0, v.1);
    show("UNTRACKED_SELF", untracked_self());
    show("DIRECT", direct_site());
    show("WRAPPER", wrapper_site());
    show("TRACKED_OUTER_WRAPPER", tracked_outer_site());
    let [fp1, fp2, direct] = fp_sites();
    show("FP1", fp1);
    show("FP2", fp2);
    show("FNPTR_DIRECT", direct);
    let d = dyn_sites();
    show("DYN_DECL_TRACKED", d[0]);
    show("DYN_PROVIDED", d[1]);
    show("DYN_IMPL_ONLY", d[2]);
    show("STATIC_IMPL_ONLY", d[3]);
    show("GENERIC_STATIC", d[4]);
    show("GENERIC_DYN", d[5]);
}
