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

//! Bounded Kani regression proofs for five [`IntoBytes`] byte-view and
//! slice-write methods.
//!
//! Configuration: Uses the common Kani CI configuration documented in
//! `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
//! x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
//! `-Zfunction-contracts`, and one layout selected by `--randomize-layout` per
//! invocation.
//!
//! API surface: this family directly invokes exactly [`IntoBytes::as_bytes`],
//! [`IntoBytes::as_mut_bytes`], [`IntoBytes::write_to`],
//! [`IntoBytes::write_to_prefix`], and [`IntoBytes::write_to_suffix`]. The
//! common feature bundle enables `std`, so it also compiles
//! [`IntoBytes::write_to_io`]. It also compiles the deprecated, doc-hidden
//! `as_bytes_mut` forwarding method and the hidden required implementor
//! function `only_derive_is_allowed_to_implement_this_trait`. No harness
//! invokes those three items, and this module directly establishes no behavior
//! for them.
//!
//! Storage domain: the shared-view harness and each of the three slice-write
//! harnesses separately cover every `u32`. The mutable-view harness covers the
//! full Cartesian product of every `[u32; 3]` and every four-byte replacement.
//! It owns that backing value (12 bytes on Kani's target), a same-shaped
//! snapshot, and four-byte initial/replacement representations; it exposes only
//! the middle `u32` as a four-byte view. Each slice-write harness owns a
//! six-byte destination and snapshot and covers the full product of every
//! destination value and logical length from zero through six.
//! It passes exactly the offset-zero prefix `&mut destination[..len]`; no
//! harness varies the start index. The family does not cover nonzero-start
//! subslices (including same-length subslices of a six-byte or larger object),
//! exact-sized backing objects of lengths zero through five, or any other
//! backing size or shape. At length zero, the target is the empty prefix; this
//! does not claim a Rust-specified raw address for that empty slice. The
//! expected passed-slice result and the separately observed caller-backing
//! frame both come from six-byte values. No harness dynamically allocates,
//! contains a source-level loop, or uses `kani::assume`. Each
//! symbolic scalar, array, and replacement is unconstrained; the logical
//! destination length is an arbitrary `u8` reduced modulo seven and converted
//! to `usize`, which reaches every value `0..=6`.
//!
//! Unwind domain: every harness has bound seven with unwinding assertions. The
//! maximum fixed bytewise extent that can drive a reachable elementwise
//! operation is six: arbitrary destination generation and the separated frame
//! comparisons cover `[u8; 6]`; each successful target or oracle byte copy is
//! exactly `size_of::<u32>() == 4` bytes. Operations on `[u32; 3]` cover three
//! elements, and its 12-byte storage size is not used as a loop bound. The
//! proof assumes no particular compiler or Kani lowering; successful unwinding
//! assertions establish that seven suffices for every reachable translated loop
//! in the exact modeled run.
//!
//! The harnesses check documented `IntoBytes` value/length behavior and the
//! three slice-write methods' success, placement, and passed-slice frames. Safe
//! standard-library byte conversion and slice copying independently specify the
//! values written; they do not independently establish that the API's policy is
//! the right one. Returned-view raw-address identity and preservation of the
//! unpassed `destination[len..6]` caller-backing suffix are additional
//! implementation-regression assertions, not documented API postconditions.
//! The outer-frame assertion establishes only final-value preservation for
//! this exact backing object under Kani's model. In particular, Kani does not
//! completely check reference aliasing, pointer provenance, reference
//! lifetimes, uninitialized memory, or other properties absent from its model.
//! Each slice-write result is consumed only by variant, so the proofs do not
//! observe the `SizeError` payload or reference-recovery identity. Each view
//! target's referent is snapshotted before the call and the returned view is
//! observed afterward. The slice-write frames are likewise observed only after
//! the call, so neither observation detects a transient mutation restored
//! before return.
//! These proofs do not cover larger backing arrays or copy lengths,
//! nonzero-start destination subslices, zero-sized or padded types, other sized
//! types, any unsized input type, `write_to_io` writer interaction (including
//! partial writes, `write_all` retries, writer errors, and writer panics), the
//! deprecated `as_bytes_mut` forwarding entry point, or the hidden implementor
//! function. The unsized exclusion includes ordinary slice and `str` DSTs as
//! well as custom and nested DST layouts (see #3630). Bound seven is a
//! translated-loop bound for this fixed family, not Rust panic-unwind coverage
//! or a general bound derived from object-allocation sizes.
//!
//! Language/library oracle basis: `VALUE_SIZE` is not reconstructed from
//! [`IntoBytes`]. Rust says "all values of a `Sized` type share the same size
//! and alignment" [1]. `size_of` states, "Returns the size of a type in bytes"
//! [2]; `size_of_val` states, "Returns the size of the pointed-to value in
//! bytes" [3]. Thus
//! `size_of::<u32>()` independently specifies the `size_of_val(self)` length in
//! the target APIs' contracts for this sized monomorphization. Safe
//! `u32::to_ne_bytes` "Returns the memory representation of this integer" in
//! native byte order [4], while `u32::from_ne_bytes` "Creates a native endian
//! integer value from its memory representation" [5]. `copy_from_slice`
//! "Copies all elements from `src` into `self`" for an equal-length receiver
//! [6]. These operations do not call zerocopy; their independence is from the
//! implementation under proof, not from the pinned compiler, standard library,
//! or Kani translation/model.
//!
//! API-policy basis: The success predicates, prefix/suffix placement, and
//! error-path passed-slice frames below restate the public documentation of
//! [`IntoBytes::write_to`], [`IntoBytes::write_to_prefix`], and
//! [`IntoBytes::write_to_suffix`]. Returned-view address identity and the
//! unpassed caller-backing frame are explicitly separate regression properties.
//! These policy and regression assertions are intentionally separate from the
//! safe language/library oracles that construct expected bytes and frame
//! values. The conclusions remain specific to `u32`, the configured target's
//! native byte order, and exactly the bounded buffers described above.
//!
//! [1]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#r-layout.properties.sized
//! [2]: https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of.html
//! [3]: https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of_val.html
//! [4]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.to_ne_bytes
//! [5]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes
//! [6]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_from_slice
//!
//! Snapshot and observation basis: every pre-call array snapshot uses the
//! shared `copy_snapshot`, whose own documentation applies Rust's
//! dereference-result, block-value-context, and copied-place rules [10]. Every
//! asserted byte view and slice-write frame uses the
//! shared `assert_same_u8_elements`, which separately checks length and then
//! compares all ordered bytes through safe slice iteration [11], copied
//! iteration, iterator equality [12], and `u8` equality [13]. Thus no proof
//! assertion silently treats array or slice `PartialEq` as its oracle; array
//! equality remains only in reachability covers. These helpers establish
//! values, not allocation identity.
//!
//! Address oracle basis: the Reference permits `&T` to `*const T` and `&mut T`
//! to `*mut T` coercions [7]. Its sized pointer-to-pointer cast rule says the
//! pointer is "returned unchanged" [8]. Slice `as_ptr` and `as_mut_ptr` return
//! raw pointers to their buffers [14][15]. `ptr::addr_eq` compares pointer
//! addresses while ignoring metadata [16]. Thus the pre-call source pointer and
//! its cast to `u8` independently compute the expected address, while the slice
//! accessors supply the returned-view address being tested. Address identity is
//! an additional regression assertion, and address equality neither checks
//! aliasing nor establishes a provenance theorem.
//!
//! Placement oracle basis: the Reference defines `start..end` as a half-open
//! `Range` containing exactly `start <= x < end` [17]. Rust maps mutable
//! indexing to `IndexMut`; arrays accept any slice index, and
//! `Range<usize>: SliceIndex<[T], Output = [T]>` returns the selected mutable
//! slice. Its documented panic conditions are `start > end` or `end` beyond
//! the array bound [18]. The shared expected-range helper accepts the
//! policy-selected `Range` directly, asserts the opposite conditions before
//! indexing, and then checks the selected slice's length before copying. Exact
//! and prefix copies pass `0..4`. The suffix helper instead indexes the
//! modeled logical `expected[..len]` destination and calls safe
//! `slice::last_chunk_mut::<4>`, whose contract directly selects its last four
//! elements or returns `None` when fewer exist [20]. It is reached only on the
//! `len >= 4` policy branch and fails closed if that safe oracle nevertheless
//! returns `None`. Thus suffix placement uses no reconstructed subtraction.
//! These operations are the Rust/library placement oracles; the target API
//! policy still decides whether a write is supposed to succeed.
//!
//! Passed-slice and caller-backing observation are deliberately separate.
//! After the target borrow ends, safe `slice::split_at(len)` partitions the
//! actual, expected, and pre-call arrays into the passed prefix and unpassed
//! suffix [21]. The passed prefix is compared with the policy-selected safe
//! copy. Separately, the unpassed suffix is compared directly with its pre-call
//! snapshot as the additional regression frame described above. Kani's
//! incomplete aliasing, provenance, and reference-lifetime checks remain
//! TOOL/TCB premises for this outer-frame observation [22].
//!
//! Result-classification basis: `classify_write_result` exhaustively matches
//! the target `Result` together with the API-policy success Boolean. Rust match
//! expressions select the first matching arm, tuple patterns match each field,
//! tuple-struct patterns select the `Ok`/`Err` variant, and literal patterns
//! match the Boolean value [19]. The two disagreement arms panic, so successful
//! verification establishes target/policy agreement without reducing the
//! target result through `Result::is_ok` or Boolean equality.
//!
//! [7]: https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#coercion-types
//! [8]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast
//! [9]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#primitive-data-layout
//! [10]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.result
//!       https://doc.rust-lang.org/1.93.0/reference/expressions/block-expr.html#r-expr.block.value
//!       https://doc.rust-lang.org/1.93.0/reference/expressions.html#moved-and-copied-types
//! [11]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
//! [12]: https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
//!       https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
//! [13]: https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
//! [14]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
//! [15]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_mut_ptr
//! [16]: https://doc.rust-lang.org/1.93.0/std/ptr/fn.addr_eq.html
//! [17]: https://doc.rust-lang.org/1.93.0/reference/expressions/range-expr.html
//! [18]: https://doc.rust-lang.org/1.93.0/reference/expressions/array-expr.html#r-expr.array.index.trait
//!       https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-IndexMut%3CI%3E-for-%5BT%3B+N%5D
//!       https://doc.rust-lang.org/1.93.0/std/ops/struct.Range.html#impl-SliceIndex%3C%5BT%5D%3E-for-Range%3Cusize%3E
//! [19]: https://doc.rust-lang.org/1.93.0/reference/expressions/match-expr.html
//!       https://doc.rust-lang.org/1.93.0/reference/patterns.html#tuple-patterns
//!       https://doc.rust-lang.org/1.93.0/reference/patterns.html#tuple-struct-patterns
//!       https://doc.rust-lang.org/1.93.0/reference/patterns.html#literal-patterns
//! [20]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.last_chunk_mut
//! [21]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at
//! [22]: https://model-checking.github.io/kani/undefined-behaviour.html

use crate::{
    proof_support::{assert_same_u8_elements, copy_snapshot},
    IntoBytes,
};

const VALUE_SIZE: usize = core::mem::size_of::<u32>();
const MAX_DST_LEN: usize = 6;

// Rust's primitive layout table fixes `u32` at four bytes [9]. Assert that
// concrete language premise in every independently selectable harness rather
// than letting array lengths and covers silently depend on it.
fn assert_modeled_u32_size() {
    assert_eq!(VALUE_SIZE, 4);
}

fn destination_len() -> usize {
    usize::from(kani::any::<u8>() % ((MAX_DST_LEN + 1) as u8))
}

// Factor the initial view's size and contents together; pointer identity stays
// local because shared and mutable views expose different pointer types.
fn assert_initial_u32_byte_view(bytes: &[u8], before: &[u8; VALUE_SIZE]) {
    assert_eq!(bytes.len(), VALUE_SIZE);
    assert_same_u8_elements(bytes, before);
}

fn expected_after_range_copy(
    destination: &[u8; MAX_DST_LEN],
    source: &[u8; VALUE_SIZE],
    range: core::ops::Range<usize>,
) -> [u8; MAX_DST_LEN] {
    let mut expected = copy_snapshot(destination);
    assert!(range.start <= range.end);
    assert!(range.end <= expected.len());
    let selected = &mut expected[range];
    assert_eq!(selected.len(), source.len());
    selected.copy_from_slice(source);
    expected
}

fn expected_after_suffix_copy(
    destination: &[u8; MAX_DST_LEN],
    source: &[u8; VALUE_SIZE],
    len: usize,
) -> [u8; MAX_DST_LEN] {
    let mut expected = copy_snapshot(destination);
    assert!(len <= expected.len());
    let logical_destination = &mut expected[..len];
    let suffix = match logical_destination.last_chunk_mut::<VALUE_SIZE>() {
        Some(suffix) => suffix,
        None => panic!("successful suffix policy requires enough destination bytes"),
    };
    assert_eq!(suffix.len(), source.len());
    suffix.copy_from_slice(source);
    expected
}

fn assert_passed_slice_result(
    actual: &[u8; MAX_DST_LEN],
    expected: &[u8; MAX_DST_LEN],
    len: usize,
) {
    assert!(len <= actual.len());
    let (actual_passed, _) = actual.split_at(len);
    let (expected_passed, _) = expected.split_at(len);
    assert_same_u8_elements(actual_passed, expected_passed);
}

fn assert_unpassed_backing_frame(
    actual: &[u8; MAX_DST_LEN],
    before: &[u8; MAX_DST_LEN],
    len: usize,
) {
    assert!(len <= actual.len());
    let (_, actual_unpassed) = actual.split_at(len);
    let (_, before_unpassed) = before.split_at(len);
    assert_same_u8_elements(actual_unpassed, before_unpassed);
}

fn classify_write_result<T, E>(result: Result<T, E>, expected_success: bool) -> bool {
    match (result, expected_success) {
        (Ok(_), true) => true,
        (Err(_), false) => false,
        (Ok(_), false) => panic!("write unexpectedly succeeded"),
        (Err(_), true) => panic!("write unexpectedly failed"),
    }
}

#[kani::proof]
#[kani::unwind(7)]
fn prove_into_bytes_as_bytes() {
    assert_modeled_u32_size();
    let value = kani::any::<u32>();
    // Snapshot both contents and length before invoking the target, so a
    // target-induced value change still present at return cannot redefine its
    // own expected result.
    let expected = value.to_ne_bytes();
    let value_address = (&value as *const u32) as *const u8;
    let bytes = value.as_bytes();

    // Domain: every `u32` on Kani's target. Establishes exact length, address,
    // initial contents, and absence of target-induced net value mutation still
    // observable at return. The
    // pre-call `u32::to_ne_bytes` snapshot is the independent safe value and
    // length oracle; pointer equality remains subject to Kani's provenance
    // model limits.
    kani::cover!(value == 0);
    kani::cover!(value == u32::MAX);
    kani::cover!(value == 0x01020304);
    assert_initial_u32_byte_view(bytes, &expected);
    assert!(core::ptr::addr_eq(bytes.as_ptr(), value_address));
    assert_same_u8_elements(&value.to_ne_bytes(), &expected);
}

#[kani::proof]
#[kani::unwind(7)]
fn prove_into_bytes_as_mut_bytes() {
    assert_modeled_u32_size();
    let mut values = kani::any::<[u32; 3]>();
    let before = copy_snapshot(&values);
    let initial_bytes = before[1].to_ne_bytes();
    let replacement = kani::any::<[u8; VALUE_SIZE]>();
    let value_address = (&mut values[1] as *mut u32) as *mut u8;

    {
        let bytes = values[1].as_mut_bytes();
        assert_initial_u32_byte_view(bytes, &initial_bytes);
        assert!(core::ptr::addr_eq(bytes.as_mut_ptr(), value_address));
        // The shared helper observes the view before this overwrite, so a
        // target-induced mutation still present at return is not erased by the
        // replacement write.
        bytes.copy_from_slice(&replacement);
        assert_same_u8_elements(bytes, &replacement);
    }

    // Domain: every three-`u32` input and replacement representation.
    // Establishes initial contents, exact address/length, and write propagation
    // for the middle element, plus a frame for both neighbors. Pre-call native
    // bytes, safe slice copying, and `u32::from_ne_bytes` are the oracles; this
    // is not an aliasing theorem.
    kani::cover!(replacement != initial_bytes);
    kani::cover!(replacement == [0; VALUE_SIZE]);
    kani::cover!(replacement == [u8::MAX; VALUE_SIZE]);
    kani::cover!(before[0] != before[2]);
    assert_eq!(values[0], before[0]);
    assert_eq!(values[1], u32::from_ne_bytes(replacement));
    assert_eq!(values[2], before[2]);
}

#[kani::proof]
#[kani::unwind(7)]
fn prove_into_bytes_write_to() {
    assert_modeled_u32_size();
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = copy_snapshot(&destination);
    let len = destination_len();

    let expected_success = len == source_len;
    let succeeded =
        classify_write_result(value.write_to(&mut destination[..len]), expected_success);

    // Domain: every `u32`, destination value, and destination length 0..=6 in
    // the module-level offset-zero prefix destination family.
    // Establishes the exact-length success condition and passed-slice result,
    // plus the separate unpassed caller-backing frame. Success and the
    // passed-slice error frame are API-policy assertions; once the successful
    // branch and offset are selected, safe `copy_from_slice` constructs the
    // independent expected contents. The outer frame is only the additional
    // exact-harness regression property documented above.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(!succeeded && len == source_len + 1);
    kani::cover!(!succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && destination != before);

    assert_same_u8_elements(&value.to_ne_bytes(), &source);
    let expected = if expected_success {
        expected_after_range_copy(&before, &source, 0..source_len)
    } else {
        copy_snapshot(&before)
    };
    assert_passed_slice_result(&destination, &expected, len);
    assert_unpassed_backing_frame(&destination, &before, len);
}

#[kani::proof]
#[kani::unwind(7)]
fn prove_into_bytes_write_to_prefix() {
    assert_modeled_u32_size();
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = copy_snapshot(&destination);
    let len = destination_len();

    let expected_success = len >= source_len;
    let succeeded =
        classify_write_result(value.write_to_prefix(&mut destination[..len]), expected_success);

    // Domain: every `u32`, destination value, and destination length 0..=6 in
    // the module-level offset-zero prefix destination family.
    // Establishes the minimum-length success condition, exact prefix write,
    // and preservation of the passed slice's suffix, plus the separate
    // unpassed caller-backing frame. Success, placement, and the passed-slice
    // error frame are API-policy assertions; safe `copy_from_slice`
    // independently constructs the expected contents for the selected prefix.
    // The outer frame is only the additional exact-harness regression property
    // documented above.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(succeeded && len == source_len + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_same_u8_elements(&value.to_ne_bytes(), &source);
    let expected = if expected_success {
        expected_after_range_copy(&before, &source, 0..source_len)
    } else {
        copy_snapshot(&before)
    };
    assert_passed_slice_result(&destination, &expected, len);
    assert_unpassed_backing_frame(&destination, &before, len);
}

#[kani::proof]
#[kani::unwind(7)]
fn prove_into_bytes_write_to_suffix() {
    assert_modeled_u32_size();
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = copy_snapshot(&destination);
    let len = destination_len();

    let expected_success = len >= VALUE_SIZE;
    let succeeded =
        classify_write_result(value.write_to_suffix(&mut destination[..len]), expected_success);

    // Domain: every `u32`, destination value, and destination length 0..=6 in
    // the module-level offset-zero prefix destination family.
    // Establishes the minimum-length success condition, exact suffix write,
    // and preservation of the passed slice's prefix, plus the separate
    // unpassed caller-backing frame. Success, placement, and the passed-slice
    // error frame are API-policy assertions. Safe `last_chunk_mut` selects the
    // suffix without arithmetic, and `copy_from_slice` independently
    // constructs its expected contents. The outer frame is only the additional
    // exact-harness regression property documented above.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(succeeded && len == source_len + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_same_u8_elements(&value.to_ne_bytes(), &source);
    let expected = if expected_success {
        expected_after_suffix_copy(&before, &source, len)
    } else {
        copy_snapshot(&before)
    };
    assert_passed_slice_result(&destination, &expected, len);
    assert_unpassed_backing_frame(&destination, &before, len);
}
