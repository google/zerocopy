// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.
#![allow(dead_code)]

#[cfg_attr(kani, zerocopy_kani_macros::contract(
    target = increment,
    requires(x < u8::MAX),
    ensures(|r| *r == x + 1),
))]
fn increment(x: u8) -> u8 { x + 1 }

#[cfg_attr(kani, derive(kani::Arbitrary))]
struct Example(u8);
impl Example {
    #[cfg_attr(kani, zerocopy_kani_macros::contract(
        method, target = Example::get,
        ensures(|r| *r == self.0),
    ))]
    fn get(&self) -> u8 { self.0 }

    #[cfg_attr(kani, zerocopy_kani_macros::contract(
        method, target = Example::width,
        instances(unit(T = ()), word(T = u16)),
        ensures(|r| *r == core::mem::size_of::<T>()),
    ))]
    fn width<T>() -> usize { core::mem::size_of::<T>() }
}

#[cfg_attr(kani, derive(kani::Arbitrary))]
struct Generic<E>(E);
#[cfg_attr(kani, zerocopy_kani_macros::contracts(
    instances(byte(E = u8), word(E = u16))
))]
impl<E: Copy> Generic<E> {
    #[cfg_attr(kani, contract(ensures(|r| *r == core::mem::size_of::<E>())))]
    fn width(&self) -> usize { core::mem::size_of::<E>() }
}

#[cfg(feature = "false_contract")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(target = broken, ensures(|r| *r < u8::MAX)))]
fn broken(x: u8) -> u8 { x }

#[cfg(feature = "unsupported_slice")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(target = slice_len, ensures(|_| true)))]
fn slice_len(x: &[u8]) -> usize { x.len() }

#[cfg(all(kani, feature = "wrong_owner"))]
impl<E: Copy + kani::Arbitrary> Generic<E> {
    #[zerocopy_kani_macros::contract(
        method, target = Generic::<u8>::wrong, ensures(|r| *r == 1),
    )]
    fn wrong(&self) -> u8 { 1 }
}
