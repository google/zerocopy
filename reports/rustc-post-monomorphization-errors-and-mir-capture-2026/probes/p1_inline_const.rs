// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]

pub fn concrete_ok() {
    const {
        assert!(1 + 1 == 2);
    }
}

pub fn generic_const_assert<T>() {
    const {
        assert!(core::mem::size_of::<T>() == 4);
    }
}

#[cfg(instantiate_ok)]
pub fn call_ok() {
    generic_const_assert::<u32>();
}

#[cfg(instantiate_fail)]
pub fn call_fail() {
    generic_const_assert::<u64>();
}

#[cfg(concrete_fail)]
pub fn concrete_bad() {
    const {
        assert!(1 == 2);
    }
}
