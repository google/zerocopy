// Copyright 2022 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use util::*;
use zerocopy::transmute_mut;

fn main() {
    const ARRAY_OF_U8S: [u8; 2] = [0u8; 2];

    // `transmute_mut!` cannot, generally speaking, be used in const contexts.
    //@[msrv]~ ERROR: mutable references are not allowed in constants
    //@[msrv]~ ERROR: calls in constants are limited to constant functions, tuple structs and tuple variants
    //@[msrv]~ ERROR: temporary value dropped while borrowed
    //@[stable]~ ERROR: cannot call non-const method `Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut_inference_helper` in constants
    //@[stable]~ ERROR: cannot call non-const method `Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut` in constants
    //@[nightly]~ ERROR: cannot call non-const method `zerocopy::util::macro_util::Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut_inference_helper` in constants
    //@[nightly]~ ERROR: cannot call non-const method `zerocopy::util::macro_util::Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut` in constants
    const CONST_CONTEXT: &mut [u8; 2] = transmute_mut!(&mut ARRAY_OF_U8S);

    // `transmute_mut!` does not support transmuting into a non-reference
    // destination type.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const DST_NOT_A_REFERENCE: usize = transmute_mut!(&mut 0u8);

    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Src;

    #[derive(zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Dst;

    // `transmute_mut` requires that the destination type implements `FromBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Dst: FromBytes` is not satisfied
    const DST_NOT_FROM_BYTES: &mut Dst = transmute_mut!(&mut Src);

    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Src;

    #[derive(zerocopy::FromBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Dst;

    // `transmute_mut` requires that the destination type implements `IntoBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Dst: IntoBytes` is not satisfied
    const DST_NOT_AS_BYTES: &mut Dst = transmute_mut!(&mut Src);

    let mut x = 0u64;
    // It is illegal to increase the lifetime scope.
    //@[msrv, stable, nightly]~ ERROR: `x` does not live long enough
    let _: &'static mut u64 = zerocopy::transmute_mut!(&mut x);

    // `transmute_mut!` does not support transmuting between non-reference source
    // and destination types.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const SRC_DST_NOT_REFERENCES: &mut usize = transmute_mut!(0usize);

    // `transmute_mut!` requires that its source type be a mutable reference.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    let _: &mut u8 = transmute_mut!(&0u8);

    // `transmute_mut!` does not support transmuting from a non-reference source
    // type.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const SRC_NOT_A_REFERENCE: &mut u8 = transmute_mut!(0usize);

    #[derive(zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Src;

    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Dst;

    // `transmute_mut` requires that the source type implements `FromBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Src: FromBytes` is not satisfied
    const SRC_NOT_FROM_BYTES: &mut Dst = transmute_mut!(&mut Src);

    #[derive(zerocopy::FromBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Src;

    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    #[repr(C)]
    struct Dst;

    // `transmute_mut` requires that the source type implements `IntoBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Src: IntoBytes` is not satisfied
    const SRC_NOT_AS_BYTES: &mut Dst = transmute_mut!(&mut Src);

    // `transmute_mut!` does not support transmuting from an unsized source type to
    // a sized destination type.
    //@[msrv, stable]~ ERROR: the method `transmute_mut` exists for struct `Wrap<&mut [u8], &mut [u8; 1]>`, but its trait bounds were not satisfied
    //@[nightly]~ ERROR: the method `transmute_mut` exists for struct `zerocopy::util::macro_util::Wrap<&mut [u8], &mut [u8; 1]>`, but its trait bounds were not satisfied
    const SRC_UNSIZED: &mut [u8; 1] = transmute_mut!(&mut [0u8][..]);
}
