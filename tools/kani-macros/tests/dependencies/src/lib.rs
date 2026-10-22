// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r == x),
))]
fn leaf(x: u8) -> u8 {
    x
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r),
))]
fn pre_leaf(x: u8) -> bool {
    true
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r == x),
))]
fn post_leaf(x: u8) -> u8 {
    x
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r),
))]
fn gate(x: u8) -> bool {
    true
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX && pre_leaf(x)), ensures(|r| *r == x),
    stub_verified(leaf),
))]
fn left(x: u8) -> u8 {
    leaf(x)
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r == post_leaf(x)),
    stub_verified(leaf),
))]
fn right(x: u8) -> u8 {
    leaf(x)
}

#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX), ensures(|r| *r == x),
))]
fn join_post(x: u8) -> u8 {
    x
}

// Diamond top -> {left, right} -> leaf. Gate/join_post appear only in
// top's conditions. pre_leaf/post_leaf appear inside replacement conditions.
#[cfg(feature = "positive")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    requires(x < u8::MAX && gate(x)), ensures(|r| *r == join_post(x)),
    stub_verified(left), stub_verified(right), stub_verified(gate),
    stub_verified(join_post), stub_verified(pre_leaf), stub_verified(post_leaf),
))]
fn top(x: u8) -> u8 {
    let callback: fn(u8) -> u8 = right;
    let _ = callback(x);
    left(x)
}

#[cfg(all(kani, feature = "missing_provider"))]
#[kani::ensures(|r| *r == x)]
fn unproved(x: u8) -> u8 {
    x
}

#[cfg(all(kani, feature = "missing_provider"))]
#[zerocopy_kani_macros::contract(ensures(|r| *r == x), stub_verified(unproved))]
fn missing_caller(x: u8) -> u8 {
    unproved(x)
}

#[cfg(feature = "wrong_instance")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    instances(byte(T = u8)), ensures(|r| *r == core::mem::size_of::<T>()),
))]
fn generic_leaf<T>() -> usize {
    core::mem::size_of::<T>()
}

#[cfg(feature = "wrong_instance")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == 2), stub_verified(generic_leaf::<u16>),
))]
fn wrong_instance() -> usize {
    generic_leaf::<u16>()
}

// These generators cover every input and call nonrecursive real functions in
// ordinary Rust. The two proof models nevertheless have a replacement cycle.
#[cfg(all(kani, feature = "mutual_cycle"))]
struct CycleA(u8);
#[cfg(all(kani, feature = "mutual_cycle"))]
struct CycleB(u8);
#[cfg(all(kani, feature = "mutual_cycle"))]
impl kani::Arbitrary for CycleA {
    fn any() -> Self {
        let _ = cycle_b(CycleB(0));
        Self(kani::any())
    }
}
#[cfg(all(kani, feature = "mutual_cycle"))]
impl kani::Arbitrary for CycleB {
    fn any() -> Self {
        let _ = cycle_a(CycleA(0));
        Self(kani::any())
    }
}
#[cfg(all(kani, feature = "mutual_cycle"))]
#[zerocopy_kani_macros::contract(ensures(|r| *r == x.0), stub_verified(cycle_b))]
fn cycle_a(x: CycleA) -> u8 {
    x.0
}
#[cfg(all(kani, feature = "mutual_cycle"))]
#[zerocopy_kani_macros::contract(ensures(|r| *r == x.0), stub_verified(cycle_a))]
fn cycle_b(x: CycleB) -> u8 {
    x.0
}

#[cfg(all(kani, feature = "generator_reentry"))]
struct Reentry(u8);
#[cfg(all(kani, feature = "generator_reentry"))]
impl kani::Arbitrary for Reentry {
    fn any() -> Self {
        let _ = generator_target(Self(2));
        Self(kani::any())
    }
}
#[cfg(all(kani, feature = "generator_reentry"))]
#[zerocopy_kani_macros::contract(requires(x.0 <= 1), ensures(|r| *r == 1))]
fn generator_target(x: Reentry) -> u8 {
    x.0
}

#[cfg(feature = "stub_requires")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == x), stub_verified(leaf),
))]
fn violates_requires(x: u8) -> u8 {
    leaf(x)
}

#[cfg(feature = "false_callee")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r == 0)))]
fn false_leaf() -> u8 {
    1
}
#[cfg(feature = "false_callee")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == 0), stub_verified(false_leaf),
))]
fn false_leaf_caller() -> u8 {
    false_leaf()
}

// The narrow model intentionally violates the documented substituted-output
// Arbitrary obligation. Graph validation cannot infer generator completeness.
// Switching to full_output must expose the same false caller contract.
#[cfg(any(feature = "narrow_output", feature = "full_output"))]
struct Output(u8);
#[cfg(all(kani, feature = "narrow_output"))]
impl kani::Arbitrary for Output {
    fn any() -> Self {
        Self(0)
    }
}
#[cfg(all(kani, feature = "full_output"))]
impl kani::Arbitrary for Output {
    fn any() -> Self {
        Self(kani::any())
    }
}
#[cfg(any(feature = "narrow_output", feature = "full_output"))]
#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|_| true)))]
fn output_leaf() -> Output {
    Output(1)
}
#[cfg(any(feature = "narrow_output", feature = "full_output"))]
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == 0), stub_verified(output_leaf),
))]
fn output_caller() -> u8 {
    output_leaf().0
}
