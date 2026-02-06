// Copyright 2022 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use util::*;
use zerocopy::transmute_ref;

fn main() {}

fn dst_mutable() {}

fn ref_dst_mutable() {
    // `transmute_ref!` requires that its destination type be an immutable
    // reference.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    let _: &mut u8 = transmute_ref!(&0u8);
}

fn dst_not_a_reference() {
    // `transmute_ref!` does not support transmuting into a non-reference
    // destination type.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const DST_NOT_A_REFERENCE: usize = transmute_ref!(&0u8);
}

fn dst_not_frombytes() {
    #[derive(zerocopy::Immutable)]
    #[repr(transparent)]
    struct Dst(AU16);

    // `transmute_ref` requires that the destination type implements `FromBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Dst: FromBytes` is not satisfied
    const DST_NOT_FROM_BYTES: &Dst = transmute_ref!(&AU16(0));
}

fn dst_not_nocell() {
    #[derive(zerocopy::FromBytes)]
    #[repr(transparent)]
    struct Dst(AU16);

    // `transmute_ref` requires that the destination type implements `Immutable`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Dst: Immutable` is not satisfied
    const DST_NOT_IMMUTABLE: &Dst = transmute_ref!(&AU16(0));
}

fn illegal_lifetime() {}

fn increase_lifetime() {
    let x = 0u64;
    // It is illegal to increase the lifetime scope.
    //@[msrv, stable, nightly]~ ERROR: `x` does not live long enough
    let _: &'static u64 = zerocopy::transmute_ref!(&x);
}

fn src_dst_not_references() {
    // `transmute_ref!` does not support transmuting between non-reference source
    // and destination types.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const SRC_DST_NOT_REFERENCES: usize = transmute_ref!(0usize);
}

fn src_not_a_reference() {
    // `transmute_ref!` does not support transmuting from a non-reference source
    // type.
    //@[msrv, stable, nightly]~ ERROR: mismatched types
    const SRC_NOT_A_REFERENCE: &u8 = transmute_ref!(0usize);
}

fn src_not_intobytes() {
    #[derive(zerocopy::Immutable)]
    #[repr(transparent)]
    struct Src(AU16);

    // `transmute_ref` requires that the source type implements `IntoBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Src: IntoBytes` is not satisfied
    const SRC_NOT_AS_BYTES: &AU16 = transmute_ref!(&Src(AU16(0)));
}

fn src_not_nocell() {
    #[derive(zerocopy::IntoBytes)]
    #[repr(transparent)]
    struct Src(AU16);

    // `transmute_ref` requires that the source type implements `Immutable`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `Src: Immutable` is not satisfied
    const SRC_NOT_IMMUTABLE: &AU16 = transmute_ref!(&Src(AU16(0)));
}

fn src_unsized() {
    // `transmute_ref!` does not support transmuting from an unsized source type.
    //@[msrv, stable]~ ERROR: the method `transmute_ref` exists for struct `Wrap<&[u8], &[u8; 1]>`, but its trait bounds were not satisfied
    //@[nightly]~ ERROR: the method `transmute_ref` exists for struct `zerocopy::util::macro_util::Wrap<&[u8], &[u8; 1]>`, but its trait bounds were not satisfied
    const SRC_UNSIZED: &[u8; 1] = transmute_ref!(&[0u8][..]);
}
