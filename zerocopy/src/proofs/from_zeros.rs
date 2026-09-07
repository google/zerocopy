// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bounded Kani regression proofs for [`FromZeros::insert_vec_zeroed`].

use alloc::{boxed::Box, vec};
use core::cell::Cell;

use crate::FromZeros;

const INITIAL_LEN: usize = 2;
const OUTPUT_LEN: usize = INITIAL_LEN + 1;

struct DropTracked<'a> {
    value: u8,
    dropped: &'a Cell<bool>,
}

impl Drop for DropTracked<'_> {
    fn drop(&mut self) {
        assert!(!self.dropped.replace(true));
    }
}

#[derive(Copy, Clone)]
enum ExpectedSlot {
    First,
    Second,
    Inserted,
}

// A value-level specification for this proof's deliberately fixed
// two-to-three-element domain, using safe slice semantics as the oracle for an
// overlapping move.
fn expected_after_single_insert(position: usize) -> [ExpectedSlot; 3] {
    let mut expected = [ExpectedSlot::First, ExpectedSlot::Second, ExpectedSlot::Inserted];
    expected.copy_within(position..2, position + 1);
    expected[position] = ExpectedSlot::Inserted;
    expected
}

// Configuration: Uses the common Kani CI configuration documented in
// `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
// x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
// `-Zfunction-contracts`, and one layout selected by `--randomize-layout` per
// invocation. All three explicit loops execute exactly `OUTPUT_LEN == 3`
// iterations. The concrete unwind bound is four, with unwinding assertions
// enabled.
//
// Domain: this fixed two-to-three-element growth, every valid insertion
// position `0..=INITIAL_LEN`, and every initial and replacement `u8` payload on
// Kani's target. Positions greater than the vector length and their documented
// panic are not covered.
//
// Establishes: the inserted all-zero representation is safely observed as
// `None`; the original boxes' recorded raw pointer values compare equal and
// their values and order match a safe fixed-array model; all resulting slots
// are usable; and each referent's observable `Drop` implementation runs exactly
// once.
//
// Oracle basis: Rust guarantees that, for sized `U`, transmuting an all-zero byte
// array to `Option<Box<U>>` is sound and produces `None` [1]. The safely
// constructed `None` below is the expected value connected to the
// implementation's zero bytes by that language guarantee. The proof consumes
// this guarantee; it does not independently prove the null-pointer optimization
// or rely on Kani to diagnose an invalid `Option<Box<U>>`.
//
// Safe `copy_within` permits overlapping source and destination ranges [2], so
// `expected_after_single_insert` independently models the value-level shift
// without calling `insert_vec_zeroed`; the chosen ranges and inserted position
// are the target API's insertion-policy oracle. On success, `Vec::try_reserve`
// guarantees capacity of at least `len + additional` [3]. Safe assignment
// replaces the selected place [4]. `Box` uniquely owns its allocation and drops
// its contents when it leaves scope [5]. `core::mem::drop` moves its argument
// and drops it before returning [6]; the `Vec` guarantees explicitly discuss
// its elements being dropped while leaving their order unspecified [7], and the
// Reference defines recursive destructor execution for initialized values [8].
// For each referent, an independent `Cell<bool>` records whether its destructor
// ran: `Cell::replace` installs `true` and returns the old value [9], while
// `Cell::get` returns a copy [10]. Thus the assertion inside `Drop::drop` rejects
// a second call and the final `get` assertion rejects no call. Raw-pointer
// equality compares addresses [11]; those observations establish neither
// allocation identity nor provenance. These premises specify normal-path value
// and ownership behavior, not aliasing or provenance.
//
// [1]: https://doc.rust-lang.org/1.93.0/core/option/index.html#representation
// [2]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_within
// [3]: https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.try_reserve
// [4]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#assignment-expressions
// [5]: https://doc.rust-lang.org/1.93.0/alloc/boxed/index.html
// [6]: https://doc.rust-lang.org/1.93.0/core/mem/fn.drop.html
// [7]: https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#guarantees
// [8]: https://doc.rust-lang.org/1.93.0/reference/destructors.html
// [9]: https://doc.rust-lang.org/1.93.0/core/cell/struct.Cell.html#method.replace
// [10]: https://doc.rust-lang.org/1.93.0/core/cell/struct.Cell.html#method.get
// [11]: https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*const+T
//
// Allocation-failure premise: Kani 0.67 invokes CBMC with
// `--no-malloc-may-fail` [12], and the recorded bundled CBMC 6.8.0 help text
// defines that option as disabling potential allocation failure [13]. The
// harness therefore requires this fixed operation to return `Ok`; the explicit
// assertion fails rather than skips the remaining properties if another error
// appears. This is conditional on that exact model, not a claim that production
// allocation cannot fail.
//
// [12]: https://github.com/model-checking/kani/blob/kani-0.67.0/kani-driver/src/call_cbmc.rs#L195-L200
// [13]: `agent_docs/validation.md`
//
// Allocation characterization: the successful modeled path creates two
// initial `Box<DropTracked>` allocations, requests one vector buffer, grows
// that vector enough to hold three slots, and later creates one replacement
// box. The persistent ownership graph therefore peaks at three boxes plus one
// vector buffer. The proof asserts only the `try_reserve` lower bound; it does
// not use the implementation's chosen post-growth capacity as an oracle or
// claim a maximum vector allocation size. This does not bound allocator
// over-allocation or transient implementation allocations, and it does not
// establish deallocation behavior.
//
// This is not a generic theorem over `T`, vector length/capacity, insertion
// count, ZSTs, allocation failure, deallocation, or real allocator behavior.
// Kani does not completely check reference aliasing, pointer provenance,
// invalid values, or uninitialized memory, so this harness does not discharge
// those UB obligations for `copy_to`, `write_bytes`, or `Vec::set_len`.
#[kani::proof]
#[kani::unwind(4)]
fn prove_insert_vec_zeroed_grows_and_preserves_owned_values() {
    let initial: [u8; INITIAL_LEN] = kani::any();
    let position = core::cmp::min(usize::from(kani::any::<u8>()), INITIAL_LEN);
    let additional = 1;
    let first_dropped = Cell::new(false);
    let second_dropped = Cell::new(false);
    let inserted_dropped = Cell::new(false);
    let zero_witness: Option<Box<DropTracked<'_>>> = None;
    let first = Box::new(DropTracked { value: initial[0], dropped: &first_dropped });
    let second = Box::new(DropTracked { value: initial[1], dropped: &second_dropped });
    let first_ptr: *const DropTracked<'_> = &*first;
    let second_ptr: *const DropTracked<'_> = &*second;
    let expected = expected_after_single_insert(position);
    let mut v = vec![Some(first), Some(second)];
    let modeled_initial_capacity = v.capacity();
    // This fail-closed guard selects a modeled path on which adding one element
    // requires growth. If Kani's allocator model changes, the proof fails here;
    // the equality is not a general guarantee of `vec!` or `Vec`.
    assert_eq!(modeled_initial_capacity, INITIAL_LEN);

    let result = <Option<Box<DropTracked<'_>>>>::insert_vec_zeroed(&mut v, position, additional);

    kani::cover!(result.is_ok() && position == 0 && additional == 1);
    kani::cover!(result.is_ok() && position == 1 && additional == 1);
    kani::cover!(result.is_ok() && position == INITIAL_LEN && additional == 1);
    kani::cover!(result.is_ok() && initial[0] != initial[1]);
    assert!(result.is_ok());

    let new_len = OUTPUT_LEN;
    assert_eq!(v.len(), new_len);
    assert!(v.capacity() >= new_len);
    for idx in 0..new_len {
        match expected[idx] {
            ExpectedSlot::First => {
                let boxed = v[idx].as_ref().unwrap();
                let ptr: *const DropTracked<'_> = &**boxed;
                assert_eq!(ptr, first_ptr);
                assert_eq!(boxed.value, initial[0]);
            }
            ExpectedSlot::Second => {
                let boxed = v[idx].as_ref().unwrap();
                let ptr: *const DropTracked<'_> = &**boxed;
                assert_eq!(ptr, second_ptr);
                assert_eq!(boxed.value, initial[1]);
            }
            ExpectedSlot::Inserted => assert_eq!(v[idx].is_none(), zero_witness.is_none()),
        }
    }

    let replacements: [u8; OUTPUT_LEN] = kani::any();
    kani::cover!(replacements[0] != replacements[1] && replacements[1] != replacements[2]);
    for idx in 0..new_len {
        let slot = &mut v[idx];
        match slot {
            Some(boxed) => boxed.value = replacements[idx],
            None => {
                *slot = Some(Box::new(DropTracked {
                    value: replacements[idx],
                    dropped: &inserted_dropped,
                }))
            }
        }
    }
    for idx in 0..new_len {
        assert_eq!(v[idx].as_ref().unwrap().value, replacements[idx]);
    }
    assert!(!first_dropped.get());
    assert!(!second_dropped.get());
    assert!(!inserted_dropped.get());
    drop(v);
    assert!(first_dropped.get());
    assert!(second_dropped.get());
    assert!(inserted_dropped.get());
}
