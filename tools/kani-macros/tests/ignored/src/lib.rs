// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r == x)))]
fn enabled(x: u8) -> u8 { x }

#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == x), stub_verified(enabled),
))]
fn enabled_caller(x: u8) -> u8 { enabled(x) }

#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == x), ignore = "Manual λ", 
))]
fn ignored_leaf(x: u8) -> u8 { x }

// The boundary counterexample must remain discoverable in every manual mode.
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r < u8::MAX), ignore = "Known failure",
))]
fn broken(x: u8) -> u8 { x }

#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r < u8::MAX), ignore = "Requires broken provider",
    stub_verified(broken), stub_verified(enabled),
))]
fn ignored_caller(x: u8) -> u8 { broken(enabled(x)) }

#[cfg(kani)]
#[kani::proof]
#[kani::stub_verified(enabled)]
fn handwritten_enabled() { let x: u8 = kani::any(); assert_eq!(enabled(x), x); }

#[cfg(all(kani, feature = "enabled_depends_ignored"))]
#[zerocopy_kani_macros::contract(ensures(|r| *r == x), stub_verified(ignored_leaf))]
fn forbidden_caller(x: u8) -> u8 { ignored_leaf(x) }

#[cfg(all(kani, feature = "handwritten_depends_ignored"))]
#[kani::proof]
#[kani::stub_verified(ignored_leaf)]
fn forbidden_handwritten() { let x: u8 = kani::any(); assert_eq!(ignored_leaf(x), x); }

#[cfg_attr(kani, derive(kani::Arbitrary))]
struct Generic<T>(T);

#[cfg_attr(kani, zerocopy_kani_macros::contracts(
    instances(byte(T = u8), word(T = u16)),
))]
impl<T: Copy + PartialEq> Generic<T> {
    #[cfg_attr(kani, contract(ensures(|r| *r == self.0), ignore = "Generic λ"))]
    fn get(&self) -> T { self.0 }
}

// Kani substitutes by definition: naming u8 can replace a reached u16 call.
#[cfg(all(kani, feature = "generic_handwritten"))]
#[kani::proof]
#[kani::stub_verified(Generic::<u8>::get)]
fn generic_handwritten() {
    let word: Generic<u16> = kani::any();
    assert_eq!(word.get(), word.0);
}

// Ignoring a callee proof must not suppress execution of its original body.
#[cfg(all(kani, feature = "original_body"))]
#[zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX))]
fn original_body(x: u8) -> u8 { ignored_leaf(x) }
