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

#[derive(imp::KnownLayout, imp::Immutable, imp::FromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct Byte(u8);

#[test]
fn pointer_iterator_tracks_both_ends() {
    use imp::{DoubleEndedIterator as _, ExactSizeIterator as _, Iterator as _};

    let values = [Byte(1), Byte(2), Byte(3)];
    let mut iter = imp::Ptr::from_ref(&values[..]).iter();
    imp::assert_eq!(iter.len(), 3);
    imp::assert_eq!(iter.next_back().unwrap().as_ref().0, 3);
    imp::assert_eq!(iter.len(), 2);
    imp::assert_eq!(iter.next().unwrap().as_ref().0, 1);
    imp::assert_eq!(iter.len(), 1);
    imp::assert_eq!(iter.next_back().unwrap().as_ref().0, 2);
    imp::assert_eq!(iter.len(), 0);
    imp::assert_eq!(iter.next().is_none(), true);
    imp::assert_eq!(iter.next_back().is_none(), true);
}

#[test]
fn inner_pointer_iterator_tracks_both_ends() {
    use imp::{DoubleEndedIterator as _, ExactSizeIterator as _, Iterator as _};

    let values = [Byte(1), Byte(2), Byte(3)];
    let inner = imp::Ptr::from_ref(&values[..]).as_inner();
    let mut iter = inner.iter();
    imp::assert_eq!(iter.len(), 3);
    let _ = iter.next_back().unwrap();
    imp::assert_eq!(iter.len(), 2);
    let _ = iter.next().unwrap();
    imp::assert_eq!(iter.len(), 1);
    let _ = iter.next_back().unwrap();
    imp::assert_eq!(iter.len(), 0);
    imp::assert_eq!(iter.next().is_none(), true);
}

#[test]
fn empty_and_zero_sized_pointer_iterators_keep_their_lengths() {
    use imp::{DoubleEndedIterator as _, ExactSizeIterator as _, Iterator as _};

    let empty: [Byte; 0] = [];
    let mut iter = imp::Ptr::from_ref(&empty[..]).iter();
    imp::assert_eq!(iter.len(), 0);
    imp::assert_eq!(iter.next().is_none(), true);
    imp::assert_eq!(iter.next_back().is_none(), true);

    let values = [(); 3];
    let mut iter = imp::Ptr::from_ref(&values[..]).iter();
    imp::assert_eq!(iter.len(), 3);
    let _ = iter.next_back().unwrap();
    imp::assert_eq!(iter.len(), 2);
    let _ = iter.next().unwrap();
    imp::assert_eq!(iter.len(), 1);
    let _ = iter.next_back().unwrap();
    imp::assert_eq!(iter.len(), 0);
}
