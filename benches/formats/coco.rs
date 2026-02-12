// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! This modules defines two formats similar to the one used to illustrate the
//! examples of [`zerocopy::TryFromBytes`]. The basic structure of these formats
//! is a [`Packet`], which has a parameterizable leading field, followed by
//! two-fixed byte fields, followed by a dynamically sized field. This format is
//! consumed by our benchmarks either as a [`CocoPacket`] (which begins with the
//! leading bytes `0xC0C0`), or a [`LocoPacket`] (which begins two bytes of any
//! value). Both formats share the following qualities which stress-test our
//! benchmarks:
//!
//! - They have a minimum alignment of two.
//! - They have a minimum size of four bytes.
//! - They have an even size.

use zerocopy_derive::*;

// The only valid value of this type are the bytes `0xC0C0`.
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(u16)]
pub enum C0C0 {
    _XC0C0 = 0xC0C0,
}

#[derive(FromBytes, KnownLayout, Immutable)]
#[repr(C, align(2))]
pub struct Packet<Magic> {
    magic_number: Magic,
    mug_size: u8,
    temperature: u8,
    marshmallows: [[u8; 2]],
}

/// A packet begining with the magic number `0xC0C0`.
pub type CocoPacket = Packet<C0C0>;

/// A packet beginning with any two initialized bytes.
pub type LocoPacket = Packet<[u8; 2]>;
