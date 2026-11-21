// Library crate whose public items pin down where the implicit `&'static Location<'static>`
// argument of a `#[track_caller]` function travels on x86-64. Public linkage keeps LLVM from
// specialising a callee on a constant argument, so every body below has to honour its full ABI.
// The method bodies differ on purpose so that identical-function merging cannot alias them.
#![crate_type = "lib"]
use std::panic::Location;

// ---- tracked callees with 0, 1, 2 and 6 explicit integer arguments ----------------------------
#[track_caller]
#[inline(never)]
pub fn abi_tracked0() -> u32 { // @ABI0_DEF
    Location::caller().line()
}

#[track_caller]
#[inline(never)]
pub fn abi_tracked1(a: u64) -> u32 { // @ABI1_DEF
    Location::caller().line().wrapping_add(a as u32)
}

#[track_caller]
#[inline(never)]
pub fn abi_tracked2(a: u64, b: u64) -> u32 { // @ABI2_DEF
    Location::caller().line().wrapping_add(a as u32).wrapping_add(b as u32)
}

#[track_caller]
#[inline(never)]
pub fn abi_tracked6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u32 {
    Location::caller().line().wrapping_add((a ^ b ^ c ^ d ^ e ^ f) as u32)
}

// Untracked twin of `abi_tracked1`, for contrast: no implicit argument.
#[inline(never)]
pub fn abi_untracked1(a: u64) -> u32 {
    Location::caller().line().wrapping_add(a as u32) // @UNTRACKED1_SELF
}

// ---- direct call sites: an untracked caller materialises a constant `&Location` ----------------
#[inline(never)]
pub fn call_tracked0() -> u32 {
    abi_tracked0() // @CALL0_SITE
}

#[inline(never)]
pub fn call_tracked1(a: u64) -> u32 {
    abi_tracked1(a) // @CALL1_SITE
}

#[inline(never)]
pub fn call_tracked2(a: u64, b: u64) -> u32 {
    abi_tracked2(a, b) // @CALL2_SITE
}

// A tracked caller forwards its own implicit argument instead of materialising a constant.
#[track_caller]
#[inline(never)]
pub fn forward_tracked1(a: u64) -> u32 {
    abi_tracked1(a)
}

// ---- function-pointer reification: `fn` item -> `fn` pointer ----------------------------------
#[inline(never)]
pub fn reify0() -> fn() -> u32 {
    abi_tracked0
}

#[inline(never)]
pub fn reify1() -> fn(u64) -> u32 {
    abi_tracked1
}

#[inline(never)]
pub fn reify2() -> fn(u64, u64) -> u32 {
    abi_tracked2
}

#[inline(never)]
pub fn reify_untracked1() -> fn(u64) -> u32 {
    abi_untracked1
}

#[inline(never)]
pub fn call_through_pointer(fp: fn(u64) -> u32, a: u64) -> u32 {
    fp(a)
}

// ---- trait objects ---------------------------------------------------------------------------
pub trait DeclTracked {
    #[track_caller]
    fn m(&self, a: u64) -> u32;
}
pub struct A;
impl DeclTracked for A {
    #[inline(never)]
    fn m(&self, a: u64) -> u32 {
        Location::caller().line().wrapping_add(a as u32).wrapping_mul(3)
    }
}

pub trait DeclUntracked {
    fn m(&self, a: u64) -> u32;
}
pub struct B;
impl DeclUntracked for B {
    #[track_caller]
    #[inline(never)]
    fn m(&self, a: u64) -> u32 { // @IMPL_ONLY_DEF
        Location::caller().line().wrapping_add(a as u32).wrapping_mul(5)
    }
}

#[inline(never)]
pub fn virtual_call_decl_tracked(x: &dyn DeclTracked, a: u64) -> u32 {
    x.m(a) // @VCALL_TRACKED_SITE
}

#[inline(never)]
pub fn virtual_call_decl_untracked(x: &dyn DeclUntracked, a: u64) -> u32 {
    x.m(a)
}

#[inline(never)]
pub fn make_dyn_decl_tracked() -> &'static dyn DeclTracked {
    &A
}

#[inline(never)]
pub fn make_dyn_decl_untracked() -> &'static dyn DeclUntracked {
    &B
}
