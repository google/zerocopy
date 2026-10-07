// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.
#![allow(dead_code)]

#[cfg_attr(kani, zerocopy_kani_macros::contract(
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

    #[cfg_attr(kani, contract(
        instances(byte(T = u8), word(T = u16)),
        ensures(|r| r.0 == core::mem::size_of::<E>() + core::mem::size_of::<T>()
            && r.1 == x),
    ))]
    fn pair<T: Copy + PartialEq + Into<u16>>(&self, x: T) -> (usize, T) {
        let width = core::mem::size_of::<E>() + core::mem::size_of::<T>();
        // Only one concrete pair fails, and only at its input-domain boundary.
        #[cfg(feature = "false_generic_pair")]
        let width = if core::mem::size_of::<E>() == 2
            && core::mem::size_of::<T>() == 1
            && x.into() == u16::from(u8::MAX)
        {
            width + 1
        } else {
            width
        };
        (width, x)
    }
}

#[cfg(feature = "false_contract")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX)))]
fn broken(x: u8) -> u8 { x }

#[cfg(feature = "unsupported_slice")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|_| true)))]
fn slice_len(x: &[u8]) -> usize { x.len() }

#[cfg(all(kani, feature = "wrong_owner"))]
impl<E: Copy + kani::Arbitrary> Generic<E> {
    #[zerocopy_kani_macros::contract(
        method, target = Generic::<u8>::wrong, ensures(|r| *r == 1),
    )]
    fn wrong(&self) -> u8 { 1 }
}

#[cfg(all(kani, feature = "wrong_generic_owner"))]
impl<E: Copy + kani::Arbitrary> Generic<E> {
    #[zerocopy_kani_macros::contract(
        method, target = Generic::<E>::wrong_generic, ensures(|r| *r == 1),
    )]
    fn wrong_generic(&self) -> u8 { 1 }
}

// A generated module importing super would bind these local names to the
// module-level increment instead, successfully proving the wrong contract.
#[cfg(feature = "local_homonym")]
fn local_outer() {
    #[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX)))]
    fn increment(x: u8) -> u8 { x }
}

#[cfg(feature = "generic_local_homonym")]
fn generic_local_outer<T>() {
    #[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX)))]
    fn increment(x: u8) -> u8 { x }
}

#[cfg(feature = "contracted_local_homonym")]
#[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r == 1)))]
fn contracted_local_outer() -> u8 {
    #[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX)))]
    fn increment(x: u8) -> u8 { x }
    1
}

#[cfg(feature = "free_method")]
impl Example {
    // Omitting method must not generate a proof for the module-level homonym.
    #[cfg_attr(kani, zerocopy_kani_macros::contract(ensures(|r| *r < u8::MAX)))]
    fn increment(x: u8) -> u8 { x }
}
