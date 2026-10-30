// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]

pub struct AssertSize4<T>(core::marker::PhantomData<T>);

impl<T> AssertSize4<T> {
    pub const OK: usize = {
        assert!(core::mem::size_of::<T>() == 4);
        4
    };
}

pub fn let_underscore<T>() {
    let _ = AssertSize4::<T>::OK;
}

pub fn let_binding<T>() -> usize {
    let x = AssertSize4::<T>::OK;
    x
}

pub fn operand_use<T>() -> usize {
    10 + AssertSize4::<T>::OK
}

pub fn zerocopy_static_assert<T: ?Sized>() {
    trait StaticAssert {
        const ASSERT: bool;
    }
    impl<U: ?Sized> StaticAssert for (core::marker::PhantomData<U>,) {
        const ASSERT: bool = {
            assert!(core::mem::size_of::<*const U>() == 8);
            core::mem::size_of::<*const U>() == 8
        };
    }
    assert!(<(core::marker::PhantomData<T>,) as StaticAssert>::ASSERT);
}

#[cfg(instantiate_ok)]
pub fn call_all_ok() -> usize {
    let_underscore::<u32>();
    zerocopy_static_assert::<u32>();
    let_binding::<u32>() + operand_use::<u32>()
}

#[cfg(instantiate_fail_let_underscore)]
pub fn call_fail_let_underscore() {
    let_underscore::<u64>();
}

#[cfg(instantiate_fail_zerocopy)]
pub fn call_fail_zerocopy() {
    zerocopy_static_assert::<[u8]>();
}
