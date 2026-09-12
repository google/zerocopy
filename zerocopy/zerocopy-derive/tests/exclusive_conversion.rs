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

#[derive(imp::KnownLayout, imp::FromBytes, imp::IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct Packet {
    header: imp::core::cell::Cell<u8>,
    body: [imp::core::cell::Cell<u8>],
}

util_assert_impl_all!(Packet: imp::KnownLayout, imp::FromBytes, imp::IntoBytes);
util_assert_not_impl_any!(Packet: imp::Immutable);

#[test]
fn explicit_count_mutable_conversion_does_not_require_immutable() {
    use imp::FromBytes as _;

    let mut bytes = [1u8, 2, 3];
    let packet = Packet::mut_from_bytes_with_elems(&mut bytes[..], 2).unwrap();
    imp::assert_eq!(packet.header.get(), 1);
    imp::assert_eq!(packet.body.len(), 2);
    packet.header.set(4);
    packet.body[1].set(5);
    imp::assert_eq!(bytes, [4, 2, 5]);
}

#[test]
fn explicit_count_mutable_affixes_preserve_the_other_bytes() {
    use imp::FromBytes as _;

    let mut bytes = [1u8, 2, 3, 4];
    let (packet, suffix) =
        Packet::mut_from_prefix_with_elems(&mut bytes[..], 2).unwrap();
    packet.header.set(5);
    packet.body[1].set(6);
    suffix[0] = 7;
    imp::assert_eq!(bytes, [5, 2, 6, 7]);

    let (prefix, packet) =
        Packet::mut_from_suffix_with_elems(&mut bytes[..], 2).unwrap();
    prefix[0] = 8;
    packet.header.set(9);
    packet.body[1].set(10);
    imp::assert_eq!(bytes, [8, 9, 6, 10]);
}
