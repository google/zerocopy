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
// two-to-three-element domain, using safe slice rotation as the oracle for the
// insertion shift.
fn expected_after_single_insert(position: usize) -> [ExpectedSlot; 3] {
    let mut expected = [ExpectedSlot::First, ExpectedSlot::Second, ExpectedSlot::Inserted];
    expected[position..].rotate_right(1);
    expected
}

// A safe standard-library oracle for the length effect of this proof's fixed
// single-element insertion. Unit elements keep the oracle allocation-free.
fn vec_insert_len_oracle(initial_len: usize, position: usize) -> usize {
    let mut oracle = vec![(); initial_len];
    oracle.insert(position, ());
    oracle.len()
}

// Configuration: Uses the common Kani CI configuration documented in
// `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
// x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
// `-Zfunction-contracts`, and one layout selected by `--randomize-layout` per
// invocation. Before any harness-written loop executes, an assertion requires
// the safe `Vec<()>` length oracle's result to equal the fixed model length of
// three.
//
// Concrete loop audit: each of the three harness `for` loops below ranges over
// `0..OUTPUT_LEN` and therefore executes exactly three iterations. On the
// normal path, the pinned standard library's slice-drop loop visits exactly the
// three resulting vector slots. The rotation oracle receives a suffix of one,
// two, or three elements and rotates it right by one; in this configuration the
// pinned implementation selects its buffered memmove path (or the one-element
// no-op), so its linked GCD and swap loops execute zero iterations. The unit
// vector length oracle has no element-drop loop, and its pinned ZST insertion
// path contains no loop. The target performs one fixed zero-fill and an
// overlapping move of zero, one, or two vector slots, modeled as memory
// operations rather than source loops. The buffered rotation similarly moves
// at most two one-byte `ExpectedSlot` values.
//
// `goto-instrument --show-loops` reports 21 static loop IDs in the exact
// harness-restricted GOTO binary. Four are the feasible iterative Rust loops
// just described: the three harness loops and the slice-drop loop. Seven linked
// rotation GCD, swap, and chunk loops are infeasible in this domain. Nine are
// allocator-model C
// `do { assertion } while (0)` wrappers. Of those, the two `__rust_alloc` IDs
// execute one body iteration per call for three calls (the three boxes), the
// three `__rust_realloc` IDs execute once in its single call, and the two
// `__rust_dealloc` IDs execute once per call for four calls (the three boxes and
// final vector buffer). Every such wrapper traverses zero back edges. The two
// linked `__rust_alloc_zeroed` IDs are infeasible. The remaining linked
// infinite fallback in `kani_intrinsic::<usize>` is also infeasible. The
// initial vector buffer is a direct modeled `malloc` in this exact GOTO codegen,
// so it remains an allocation event in the accounting below but invokes no
// allocator-shim loop; `__rust_realloc` frees that old buffer. These are pinned
// compiler/Kani facts, not source-level API guarantees. The listing establishes
// the inventory; fixed-input path analysis and per-loop unwind checks establish
// the reachability and iteration counts rather than inferring them from the
// listing alone.
//
// `#[kani::unwind(4)]` is deliberately one greater than the maximum concrete
// three-iteration loop. It applies to every reachable generated loop, including
// any in the target and standard-library oracles, with unwinding assertions
// enabled; a bound of three fails at the first harness loop, while four proves
// every unwinding assertion. Four lets CBMC check the terminating guard after
// three body iterations. The attribute is verifier configuration, distinct
// from the domain-specific iteration counts above.
//
// Domain: this fixed two-to-three-element growth, every valid insertion
// position `0..=INITIAL_LEN`, and every initial and replacement `u8` payload on
// Kani's target. The harness uses no `kani::assume`; taking the minimum of an
// arbitrary `u8` converted to `usize` and `INITIAL_LEN` reaches all three valid
// positions. Positions greater than the vector length and their documented
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
// Safe `rotate_right` moves the final element of the selected suffix to its
// front while preserving the order of the other elements [2], so
// `expected_after_single_insert` models the value-level shift without manually
// reconstructing overlapping move endpoints or calling `insert_vec_zeroed`.
// Selecting the suffix at `position` remains the target API's insertion-policy
// oracle. Safe `vec!` constructs a separate length oracle with `initial_len`
// unit elements [17]. Safe `Vec::insert` inserts one unit element at `position`
// [18], and `Vec::len` reports the resulting number of elements [19]. Thus
// `vec_insert_len_oracle(v.len(), position)` supplies this harness's expected
// post-call length without restating `initial_len + additional`. Using the same
// `position` remains the zerocopy API's insertion-position policy; this oracle
// does not cover other insertion counts. Unit is zero-sized [20], and `Vec`
// allocates no storage for zero-sized elements [7], so the oracle adds no heap
// allocation to the accounting below. `OUTPUT_LEN` sizes fixed-domain arrays
// and their fixed iteration ranges; it is not the target-length oracle. On
// success, `Vec::try_reserve` guarantees
// capacity of at least `len + additional` [3]. Safe assignment
// replaces the selected place [4]. `Box` uniquely owns its allocation and drops
// its contents when it leaves scope [5]. The Reference guarantees that the heap
// allocation remains at one location for its whole lifetime and expressly says
// it "will never be relocated as a result of moving a box value" [21]. The
// raw-pointer assertions consume that guarantee to observe
// whether moving the two original boxes between vector slots and buffers
// preserves their pointee addresses. `core::mem::drop` moves its argument and
// drops it before returning [6]; the `Vec` guarantees explicitly discuss its
// elements being dropped while leaving their order unspecified [7], and the
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
// [2]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.rotate_right
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
// Modeled heap-allocation bound (TOOL/TCB, not a `Vec` contract): for the
// compiler bundled with Kani 0.67 on the documented x86_64 target, inspection
// of exact-harness codegen gives 16-byte `DropTracked` allocations and 8-byte
// `Option<Box<DropTracked>>` vector slots. The pinned `RawVec`
// `grow_amortized` path [14] grows the guarded capacity-two buffer to capacity
// four, so the vector requests 16 bytes initially and 32 bytes during growth.
// Equal old/new alignment selects `Global::grow`'s reallocation path [15];
// Kani models that path by allocating the new 32-byte object, copying 16 bytes,
// and then freeing the old 16-byte object [16].
//
// The successful modeled trace therefore has five allocation events: four
// 16-byte requests (three boxes and the initial vector storage) and one 32-byte
// request. It requests 96 bytes cumulatively, at most 32 bytes in one request,
// and has at most four live objects totaling 80 requested bytes. During
// growth, exactly one additional buffer is temporarily live: the old and new
// vector buffers coexist (two objects totaling 48 bytes) with the two original
// boxes. The replacement box is allocated only after the old buffer is freed;
// at that point three boxes and the new vector buffer again total four objects
// and 80 requested bytes.
//
// These numbers are pinned compiler/Kani implementation facts. The proof keeps
// only the public `try_reserve` lower-bound assertion and deliberately does not
// assert capacity four as a `Vec` guarantee. CBMC gives modeled dynamic objects
// their requested extents; real allocator rounding, metadata, overcommit,
// in-place reallocation, and Kani's incomplete alignment model remain TOOL/TCB
// exclusions. Stack storage (including safe-oracle implementation scratch) is
// outside this dynamic-allocation accounting. A compiler, Kani, target,
// type-layout, or harness-allocation change requires this accounting and the
// generated control flow to be re-audited.
//
// [14]: https://github.com/rust-lang/rust/blob/53732d5e076329a62f71d3c6901886ce8a71e812/library/alloc/src/raw_vec/mod.rs
// [15]: https://github.com/rust-lang/rust/blob/53732d5e076329a62f71d3c6901886ce8a71e812/library/alloc/src/alloc.rs
// [16]: https://github.com/model-checking/kani/blob/kani-0.67.0/library/kani/kani_lib.c#L99-L119
// [17]: https://doc.rust-lang.org/1.93.0/alloc/macro.vec.html
// [18]: https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.insert
// [19]: https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.len
// [20]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#tuple-layout
// [21]: https://doc.rust-lang.org/1.93.0/reference/memory-allocation-and-lifetime.html#dynamic-memory-allocation
// [22]: https://model-checking.github.io/kani/rust-feature-support.html
//
// This is not a generic theorem over `T`, vector length/capacity, insertion
// count, ZSTs, allocation failure, deallocation, or real allocator behavior.
// Kani does not completely check reference aliasing, pointer provenance,
// invalid values, or uninitialized memory, so this harness does not discharge
// those UB obligations for `copy_to`, `write_bytes`, or `Vec::set_len`. Kani's
// feature table also marks destructors and `Drop` as only partially supported
// [22]. The exactly-once normal-path destructor result is therefore conditional
// on Kani 0.67's lowering and execution model for the particular drops reached
// here; this harness does not independently establish that model and does not
// cover panic unwinding.
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
    let expected_len = vec_insert_len_oracle(v.len(), position);
    assert_eq!(expected_len, OUTPUT_LEN);

    let result = <Option<Box<DropTracked<'_>>>>::insert_vec_zeroed(&mut v, position, additional);

    kani::cover!(result.is_ok() && position == 0 && additional == 1);
    kani::cover!(result.is_ok() && position == 1 && additional == 1);
    kani::cover!(result.is_ok() && position == INITIAL_LEN && additional == 1);
    kani::cover!(result.is_ok() && initial[0] != initial[1]);
    assert!(result.is_ok());

    assert_eq!(v.len(), expected_len);
    assert!(v.capacity() >= expected_len);
    for idx in 0..OUTPUT_LEN {
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
    for idx in 0..OUTPUT_LEN {
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
    for idx in 0..OUTPUT_LEN {
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
