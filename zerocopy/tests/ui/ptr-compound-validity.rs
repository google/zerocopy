// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use zerocopy::{
    pointer::{
        invariant::{Aligned, Exclusive, Safe, Shared, Uninit},
        Ptr,
    },
    project_clients::TryFromBytesDerive,
    ReadOnly, Unalign,
};

fn _wrong_arity(ptr: Ptr<'_, (u8, u8), (Shared, Aligned, (Safe,))>) {
    let _ = ptr.project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 0>();
    //~^ ERROR: the method `project` exists
}

fn _uninitialized_field(ptr: Ptr<'_, (u8, bool), (Shared, Aligned, (Safe, Uninit))>) {
    let field = ptr.project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 1>().unwrap();
    let _ = field.as_ref();
    //~^ ERROR: the method `as_ref` exists
}

fn _wrapped_uninitialized_field(ptr: Ptr<'_, (u8, bool), (Shared, Aligned, (Safe, Uninit))>) {
    let field = ptr
        .into_unalign()
        .project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 1>()
        .unwrap();
    let _ = field.as_ref();
    //~^ ERROR: the method `as_ref` exists
}

fn _wrapped_extra_level(ptr: Ptr<'_, Unalign<(u8, u8)>, (Shared, Aligned, ((Safe, Safe),))>) {
    let _ = ptr.project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 0>();
    //~^ ERROR: the method `project` exists
}

fn _unwrap_shared_cell(
    ptr: Ptr<'_, core::cell::UnsafeCell<(u8, bool)>, (Shared, Aligned, (Safe, Uninit))>,
) {
    let _ = ptr.get_mut();
    //~^ ERROR: the method `get_mut` exists
}

fn _unwrapped_uninitialized_field(
    ptr: Ptr<'_, core::cell::UnsafeCell<(u8, bool)>, (Exclusive, Aligned, (Safe, Uninit))>,
) {
    let field = ptr
        .get_mut()
        .project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 1>()
        .unwrap();
    let _ = field.as_ref();
    //~^ ERROR: the method `as_ref` exists
}

fn _readonly(ptr: Ptr<'_, ReadOnly<(core::cell::Cell<u8>, u8)>, (Shared, Aligned, (Safe, Safe))>) {
    let field = ptr.project::<TryFromBytesDerive, _, { zerocopy::STRUCT_VARIANT_ID }, 0>().unwrap();
    field.as_ref().set(1);
    //~^ ERROR: no method named `set` found
}

fn main() {}
