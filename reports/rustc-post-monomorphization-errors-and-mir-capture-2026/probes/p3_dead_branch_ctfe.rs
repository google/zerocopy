// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
#![allow(unreachable_code)]

pub struct Fail<T>(core::marker::PhantomData<T>);
impl<T> Fail<T> {
    pub const C: () = assert!(core::mem::size_of::<T>() == 0);
}

pub fn inner_fail<T>() {
    const {
        assert!(core::mem::size_of::<T>() == 0);
    }
}

pub fn generic_if_false_const<T>() {
    if false {
        const {
            assert!(core::mem::size_of::<T>() == 0);
        }
    }
}

pub fn generic_if_false_assoc<T>() {
    if false {
        let _ = Fail::<T>::C;
    }
}

pub fn generic_if_false_call<T>() {
    if false {
        inner_fail::<T>();
    }
}

pub fn generic_after_return_const<T>() {
    return;
    const {
        assert!(core::mem::size_of::<T>() == 0);
    }
}

pub fn generic_after_return_assoc<T>() {
    return;
    let _ = Fail::<T>::C;
}

#[cfg(concrete_if_false_const)]
pub fn concrete_dead_const() {
    if false {
        const {
            panic!("dead concrete const block");
        }
    }
}

#[cfg(concrete_after_return_const)]
pub fn concrete_after_ret() {
    return;
    const {
        panic!("after return concrete const block");
    }
}

#[cfg(call_if_false_const)]
pub fn trigger_if_false_const() {
    generic_if_false_const::<u32>();
}

#[cfg(call_if_false_assoc)]
pub fn trigger_if_false_assoc() {
    generic_if_false_assoc::<u32>();
}

#[cfg(call_if_false_call)]
pub fn trigger_if_false_call() {
    generic_if_false_call::<u32>();
}

#[cfg(call_after_return_const)]
pub fn trigger_after_return_const() {
    generic_after_return_const::<u32>();
}

#[cfg(call_after_return_assoc)]
pub fn trigger_after_return_assoc() {
    generic_after_return_assoc::<u32>();
}
