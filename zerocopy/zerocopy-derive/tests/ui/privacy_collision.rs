// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Soundness regression test: generic type parameters named after generated
// `___ZcField_*` markers must not shadow those markers in `HasField` /
// `ProjectField` and expose private fields to callers outside the defining
// module. Unlike `privacy.rs`, this file supplies explicit `VARIANT_ID`
// constants so MSRV (1.56.0) also reaches the privacy pass.

#![allow(non_camel_case_types, unused_braces)]

#[macro_use]
extern crate zerocopy_renamed;

fn main() {}

mod private {
    #[derive(TryFromBytes, Project)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct CollisionStruct<___ZcField_b, ___ZcField__b> {
        pub a: u8,
        pub(self) b: u16,
        pub(self) b_: u16,
        _marker: core::marker::PhantomData<(___ZcField_b, ___ZcField__b)>,
    }

    impl<T, U> CollisionStruct<T, U> {
        pub fn new() -> Self {
            Self { a: 0, b: 0, b_: 0, _marker: core::marker::PhantomData }
        }
    }

    #[derive(TryFromBytes, Project)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct CollisionTuple<r#___ZcField_1>(
        pub u8,
        pub(self) u16,
        pub core::marker::PhantomData<r#___ZcField_1>,
    );

    #[derive(TryFromBytes, Project)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub union CollisionUnion<___ZcField_b> {
        pub a: u8,
        pub(self) b: u16,
        _marker: core::marker::PhantomData<___ZcField_b>,
    }
}

use private::*;

const _: () = {
    let _: <CollisionStruct<(), ()> as zerocopy_renamed::HasField<
        zerocopy_renamed::project_clients::TryFromBytesDerive,
        _,
        { zerocopy_renamed::STRUCT_VARIANT_ID },
        { zerocopy_renamed::ident_id!(a) },
    >>::Type = 0u8;
    let _: <CollisionStruct<(), ()> as zerocopy_renamed::HasField<
        zerocopy_renamed::project_clients::TryFromBytesDerive,
        _,
        //~[msrv, stable, nightly]^ ERROR: type `private::_::_::_::___ZcField___b` is private
        { zerocopy_renamed::STRUCT_VARIANT_ID },
        { zerocopy_renamed::ident_id!(b) },
    >>::Type = 0u16;
    let _: <CollisionStruct<(), ()> as zerocopy_renamed::HasField<
        zerocopy_renamed::project_clients::ProjectDerive,
        _,
        //~[msrv, stable, nightly]^ ERROR: type `private::_::_::___ZcField___b_` is private
        { zerocopy_renamed::STRUCT_VARIANT_ID },
        { zerocopy_renamed::ident_id!(b_) },
    >>::Type = 0u16;
    let _: <CollisionTuple<()> as zerocopy_renamed::HasField<
        zerocopy_renamed::project_clients::TryFromBytesDerive,
        _,
        //~[msrv, stable, nightly]^ ERROR: type `private::_::_::_::___ZcField__1` is private
        { zerocopy_renamed::STRUCT_VARIANT_ID },
        { zerocopy_renamed::ident_id!(1) },
    >>::Type = 0u16;
    let _: <CollisionUnion<()> as zerocopy_renamed::HasField<
        zerocopy_renamed::project_clients::TryFromBytesDerive,
        _,
        //~[msrv, stable, nightly]^ ERROR: type `private::_::_::_::___ZcField__b` is private
        { zerocopy_renamed::REPR_C_UNION_VARIANT_ID },
        { zerocopy_renamed::ident_id!(b) },
    >>::Type = 0u16;
};

pub fn attempt_safe_ptr_project_via_colliding_type_param() {
    use zerocopy_renamed::{
        ident_id as id,
        pointer::Ptr,
        project_clients::{ProjectDerive as PD, TryFromBytesDerive as TFBD},
        STRUCT_VARIANT_ID as S,
    };
    let mut s = CollisionStruct::<(), ()>::new();
    let _ = Ptr::from_mut(&mut s).project::<TFBD, _, { S }, { id!(b) }>();
    //~[msrv, stable, nightly]^ ERROR: type `private::_::_::_::___ZcField___b` is private
    let _ = Ptr::from_mut(&mut s).project::<PD, _, { S }, { id!(b_) }>();
    //~[msrv, stable, nightly]^ ERROR: type `private::_::_::___ZcField___b_` is private
}
