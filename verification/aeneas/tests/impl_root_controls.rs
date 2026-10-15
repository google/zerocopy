// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(auto_traits, negative_impls)]
#![allow(dead_code, unused_macros)]
trait Unused {
    fn unused(&self);
}
unsafe trait IntoBytes {
    fn marker()
    where
        Self: Sized;
    fn provided<T: Unused>(value: T)
    where
        Self: Sized,
    {
        value.unused();
    }
}
const _: () = {
    /// Ordinary impl documentation is outside the selected owner span.
    /*é*/
    unsafe impl<T: IntoBytes, const N: usize> IntoBytes for [T; N] {
        fn marker() {}
    }
};
unsafe impl IntoBytes for u8 {
    fn marker() {}
}
fn ignored_pointer(value: &u8) -> *const u8 {
    &raw const *value
}
struct Inherent;
impl Inherent {
    fn method() {}
}
auto trait Auto {}
struct Neg;
impl !Auto for Neg {}
trait MacroTrait {}
struct MacroType;
macro_rules! generated {
    () => {
        impl MacroTrait for MacroType {}
    };
}
generated!();
trait MacroA {}
trait MacroB {}
struct Both;
macro_rules! two {
    () => {
        impl MacroA for Both {}
        impl MacroB for Both {}
    };
}
two!();
