// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::KnownLayout, imp::Immutable, imp::FromBytes, imp::IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct Byte(u8);

// Exported macros must not resolve this instead of Result::Ok.
fn Ok(_: ()) {}

#[test]
fn fallible_transmutes_ignore_caller_ok() {
    let value: imp::Result<Byte, _> = imp::try_transmute!(1u8);
    imp::assert_eq!(value.unwrap().0, 1);

    let input = 2u8;
    let value: imp::Result<&Byte, _> = imp::try_transmute_ref!(&input);
    imp::assert_eq!(value.unwrap().0, 2);

    let mut input = 3u8;
    let value: imp::Result<&mut Byte, _> = imp::try_transmute_mut!(&mut input);
    value.unwrap().0 = 4;
    imp::assert_eq!(input, 4);
}

#[test]
fn raw_and_ordinary_field_names_have_the_same_id() {
    imp::assert_eq!(imp::ident_id!(field), imp::ident_id!(r#field));
    imp::assert_eq!(imp::ident_id!(東京), imp::ident_id!(r#東京));
    imp::assert_eq!(imp::ident_id!(0), 0);
}

#[test]
fn direct_core_dependencies_use_the_reexport() {
    let input = Byte(5);
    let output: &u8 = imp::transmute_ref!(&input);
    imp::assert_eq!(*output, 5);

    let output: [u8; 4] = imp::include_value!("../../testdata/include_value/data");
    imp::assert_eq!(output, [b'a', b'b', b'c', b'd']);
}

#[derive(imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
struct RawField {
    r#field: u8,
}

#[test]
fn derived_projection_accepts_ordinary_spelling_for_raw_field() {
    let value = RawField { r#field: 6 };
    let field = imp::Ptr::from_ref(&value)
        .project::<
            imp::project_clients::ProjectDerive,
            _,
            { imp::STRUCT_VARIANT_ID },
            { imp::ident_id!(field) },
        >()
        .unwrap();
    imp::assert_eq!(*field.as_ref(), 6);
}
