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
const MAX_MODELED_VEC_CAPACITY: usize = 4;

struct DropTracked<'a> {
    value: u8,
    drops: &'a Cell<usize>,
}

impl Drop for DropTracked<'_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
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
// `None`; the original boxes retain their address, value, and order against a
// safe fixed-array value model; all resulting slots are usable; and each
// referent's observable `Drop` implementation runs exactly once.
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
// its contents when it leaves scope [5], while the Reference defines recursive
// destructor execution for initialized values [6]. Independent `Cell` counters
// observe those drops. These premises specify normal-path value and ownership
// behavior, not aliasing or provenance.
//
// [1]: https://doc.rust-lang.org/1.93.0/core/option/index.html#representation
// [2]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_within
// [3]: https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.try_reserve
// [4]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#assignment-expressions
// [5]: https://doc.rust-lang.org/1.93.0/alloc/boxed/index.html
// [6]: https://doc.rust-lang.org/1.93.0/reference/destructors.html
//
// Allocation bound: the successful modeled path creates two initial
// `Box<DropTracked>` allocations, requests a two-slot vector buffer, grows that
// vector to exactly `MAX_MODELED_VEC_CAPACITY == 4` slots, and later creates one
// replacement box. The persistent ownership graph therefore peaks at three
// boxes plus one vector buffer. The nominal box layout is
// `Layout::new::<DropTracked>()`; the maximum modeled vector layout is
// `Layout::array::<Option<Box<DropTracked>>>(4)`. This does not bound allocator
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
    let first_drops = Cell::new(0);
    let second_drops = Cell::new(0);
    let inserted_drops = Cell::new(0);
    let zero_witness: Option<Box<DropTracked<'_>>> = None;
    let first = Box::new(DropTracked { value: initial[0], drops: &first_drops });
    let second = Box::new(DropTracked { value: initial[1], drops: &second_drops });
    let first_ptr: *const DropTracked<'_> = &*first;
    let second_ptr: *const DropTracked<'_> = &*second;
    let expected = expected_after_single_insert(position);
    let mut v = vec![Some(first), Some(second)];
    let old_capacity = v.capacity();
    // This intentionally forces the reallocation path in Kani's current
    // allocator model; it is not a general guarantee of `vec!` or `Vec`.
    assert_eq!(old_capacity, INITIAL_LEN);

    let result = <Option<Box<DropTracked<'_>>>>::insert_vec_zeroed(&mut v, position, additional);

    kani::cover!(result.is_ok() && position == 0 && additional == 1);
    kani::cover!(result.is_ok() && position == 1 && additional == 1);
    kani::cover!(result.is_ok() && position == INITIAL_LEN && additional == 1);
    kani::cover!(result.is_ok() && initial[0] != initial[1]);
    assert!(result.is_ok());

    let new_len = OUTPUT_LEN;
    assert_eq!(v.len(), new_len);
    assert!(v.capacity() >= new_len);
    assert!(v.capacity() > old_capacity);
    assert_eq!(v.capacity(), MAX_MODELED_VEC_CAPACITY);
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
                *slot =
                    Some(Box::new(DropTracked { value: replacements[idx], drops: &inserted_drops }))
            }
        }
    }
    for idx in 0..new_len {
        assert_eq!(v[idx].as_ref().unwrap().value, replacements[idx]);
    }
    assert_eq!(first_drops.get(), 0);
    assert_eq!(second_drops.get(), 0);
    assert_eq!(inserted_drops.get(), 0);
    drop(v);
    assert_eq!(first_drops.get(), 1);
    assert_eq!(second_drops.get(), 1);
    assert_eq!(inserted_drops.get(), 1);
}
