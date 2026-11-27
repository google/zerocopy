// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The attributes accept well-formed specifications and leave the annotated
//! items unchanged.

pub trait PointerMetadata {
    fn from_elem_count(elems: usize) -> Self;
    fn to_elem_count(self) -> usize;
}

impl PointerMetadata for usize {
    #[anneal::spec(total, ensures(|ret| ret == elems))]
    fn from_elem_count(elems: usize) -> usize {
        elems
    }

    #[anneal::spec(total, ensures(|count| count == self))]
    fn to_elem_count(self) -> usize {
        self
    }
}

#[anneal::pure]
fn nonzero(x: u32) -> bool {
    x != 0u32
}

#[anneal::spec(
    safety_requires(nonzero(d)),
    requires(n < 100u32),
    ensures(|q| math(q) * math(d) <= math(n)),
    no_panic,
)]
unsafe fn div(n: u32, d: u32) -> u32 {
    n / d
}

#[anneal::spec(terminates, no_panic, max_steps = 34 * len + 540, ensures(|r| r == len))]
fn bounded_id(len: usize) -> usize {
    len
}

#[anneal::vacuous_ok(reason = "exercises the waiver")]
#[anneal::spec(requires(false), may_diverge, may_unwind)]
fn never_called() {}

#[allow(dead_code)]
#[anneal::spec(may_panic)]
fn panic_sink() -> ! {
    panic!("sink")
}

anneal::external_spec! {
    mod util::macros {
        #[anneal::spec(total, ensures(|ret| ret == ()))]
        unsafe fn __unsafe();
    }
}

#[test]
fn annotated_items_keep_their_behavior() {
    assert_eq!(<usize as PointerMetadata>::from_elem_count(7), 7);
    assert_eq!(7usize.to_elem_count(), 7);
    assert!(nonzero(3));
    // SAFETY: `d` is nonzero.
    assert_eq!(unsafe { div(9, 4) }, 2);
    assert_eq!(bounded_id(12), 12);
    never_called();
}
