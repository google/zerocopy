// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Traits for types that encapsulate a `[u8]`.
//!
//! These traits are used to bound the `B` parameter of [`Ref`].

use core::{
    cell,
    ops::{Deref, DerefMut},
};

// For each trait polyfill, as soon as the corresponding feature is stable, the
// polyfill import will be unused because method/function resolution will prefer
// the inherent method/function over a trait method/function. Thus, we suppress
// the `unused_imports` warning.
//
// See the documentation on `util::polyfills` for more information.
#[allow(unused_imports)]
use crate::util::polyfills::{self, NonNullExt as _, NumExt as _};
#[cfg(doc)]
use crate::Ref;

/// A mutable or immutable reference to a byte slice.
///
/// `ByteSlice` abstracts over the mutability of a byte slice reference, and is
/// implemented for various special reference types such as
/// [`Ref<[u8]>`](core::cell::Ref) and [`RefMut<[u8]>`](core::cell::RefMut).
///
/// # Safety
///
/// Implementations of `ByteSlice` must promise that their implementations of
/// [`Deref`] and [`DerefMut`] are "stable". In particular, given `B: ByteSlice`
/// and `b: B`, two calls, each to either `b.deref()` or `b.deref_mut()`, must
/// return a byte slice with the same address and length. This must hold even if
/// the two calls are separated by an arbitrary sequence of calls to methods on
/// `ByteSlice`, [`ByteSliceMut`], [`IntoByteSlice`], or [`IntoByteSliceMut`],
/// or on their super-traits. This does *not* need to hold if the two calls are
/// separated by any method calls, field accesses, or field modifications *other
/// than* those from these traits.
///
/// Note that this also implies that, given `b: B`, the address and length
/// cannot be modified via objects other than `b`, either on the same thread or
/// on another thread.
pub unsafe trait ByteSlice: Deref<Target = [u8]> + Sized {}

/// A mutable reference to a byte slice.
///
/// `ByteSliceMut` abstracts over various ways of storing a mutable reference to
/// a byte slice, and is implemented for various special reference types such as
/// `RefMut<[u8]>`.
///
/// `ByteSliceMut` is a shorthand for [`ByteSlice`] and [`DerefMut`].
pub trait ByteSliceMut: ByteSlice + DerefMut {}
impl<B: ByteSlice + DerefMut> ByteSliceMut for B {}

/// A [`ByteSlice`] which can be copied without violating dereference stability.
///
/// # Safety
///
/// If `B: CopyableByteSlice`, then the dereference stability properties
/// required by [`ByteSlice`] (see that trait's safety documentation) do not
/// only hold regarding two calls to `b.deref()` or `b.deref_mut()`, but also
/// hold regarding `c.deref()` or `c.deref_mut()`, where `c` is produced by
/// copying `b`.
pub unsafe trait CopyableByteSlice: ByteSlice + Copy + CloneableByteSlice {}

/// A [`ByteSlice`] which can be cloned without violating dereference stability.
///
/// # Safety
///
/// If `B: CloneableByteSlice`, then the dereference stability properties
/// required by [`ByteSlice`] (see that trait's safety documentation) do not
/// only hold regarding two calls to `b.deref()` or `b.deref_mut()`, but also
/// hold regarding `c.deref()` or `c.deref_mut()`, where `c` is produced by
/// `b.clone()`, `b.clone().clone()`, etc.
pub unsafe trait CloneableByteSlice: ByteSlice + Clone {}

/// A [`ByteSlice`] that can be split in two.
///
/// # Safety
///
/// Unsafe code may depend for its soundness on the assumption that `split_at`
/// and `split_at_unchecked` are implemented correctly. In particular, given `B:
/// SplitByteSlice` and `b: B`, if `b.deref()` returns a byte slice with address
/// `addr` and length `len`, then if `split <= len`, both of these
/// invocations:
/// - `b.split_at(split)`
/// - `b.split_at_unchecked(split)`
///
/// ...will return `(first, second)` such that:
/// - `first`'s address is `addr` and its length is `split`
/// - `second`'s address is `addr + split` and its length is `len - split`
pub unsafe trait SplitByteSlice: ByteSlice {
    /// Attempts to split `self` at the midpoint.
    ///
    /// `s.split_at(mid)` returns `Ok((s[..mid], s[mid..]))` if `mid <=
    /// s.deref().len()` and otherwise returns `Err(s)`.
    ///
    /// # Safety
    ///
    /// Unsafe code may rely on this function correctly implementing the above
    /// functionality.
    #[inline]
    fn split_at(self, mid: usize) -> Result<(Self, Self), Self> {
        if mid <= self.deref().len() {
            // SAFETY: Above, we ensure that `mid <= self.deref().len()`. By
            // invariant on `ByteSlice`, a supertrait of `SplitByteSlice`,
            // `.deref()` is guaranteed to be "stable"; i.e., it will always
            // dereference to a byte slice of the same address and length. Thus,
            // we can be sure that the above precondition remains satisfied
            // through the call to `split_at_unchecked`.
            unsafe { Ok(self.split_at_unchecked(mid)) }
        } else {
            Err(self)
        }
    }

    /// Splits the slice at the midpoint, possibly omitting bounds checks.
    ///
    /// `s.split_at_unchecked(mid)` returns `s[..mid]` and `s[mid..]`.
    ///
    /// # Safety
    ///
    /// `mid` must not be greater than `self.deref().len()`.
    ///
    /// # Panics
    ///
    /// Implementations of this method may choose to perform a bounds check and
    /// panic if `mid > self.deref().len()`. They may also panic for any other
    /// reason. Since it is optional, callers must not rely on this behavior for
    /// soundness.
    #[must_use]
    unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self);
}

/// A shorthand for [`SplitByteSlice`] and [`ByteSliceMut`].
pub trait SplitByteSliceMut: SplitByteSlice + ByteSliceMut {}
impl<B: SplitByteSlice + ByteSliceMut> SplitByteSliceMut for B {}

#[allow(clippy::missing_safety_doc)] // There's a `Safety` section on `into_byte_slice`.
/// A [`ByteSlice`] that conveys no ownership, and so can be converted into a
/// byte slice.
///
/// Some `ByteSlice` types (notably, the standard library's [`Ref`] type) convey
/// ownership, and so they cannot soundly be moved by-value into a byte slice
/// type (`&[u8]`). Some methods in this crate's API (such as [`Ref::into_ref`])
/// are only compatible with `ByteSlice` types without these ownership
/// semantics.
///
/// [`Ref`]: core::cell::Ref
pub unsafe trait IntoByteSlice<'a>: ByteSlice {
    /// Coverts `self` into a `&[u8]`.
    ///
    /// # Safety
    ///
    /// The returned reference has the same address and length as `self.deref()`
    /// and `self.deref_mut()`.
    ///
    /// Note that, combined with the safety invariant on [`ByteSlice`], this
    /// safety invariant implies that the returned reference is "stable" in the
    /// sense described in the `ByteSlice` docs.
    fn into_byte_slice(self) -> &'a [u8];
}

#[allow(clippy::missing_safety_doc)] // There's a `Safety` section on `into_byte_slice_mut`.
/// A [`ByteSliceMut`] that conveys no ownership, and so can be converted into a
/// mutable byte slice.
///
/// Some `ByteSliceMut` types (notably, the standard library's [`RefMut`] type)
/// convey ownership, and so they cannot soundly be moved by-value into a byte
/// slice type (`&mut [u8]`). Some methods in this crate's API (such as
/// [`Ref::into_mut`]) are only compatible with `ByteSliceMut` types without
/// these ownership semantics.
///
/// [`RefMut`]: core::cell::RefMut
pub unsafe trait IntoByteSliceMut<'a>: IntoByteSlice<'a> + ByteSliceMut {
    /// Coverts `self` into a `&mut [u8]`.
    ///
    /// # Safety
    ///
    /// The returned reference has the same address and length as `self.deref()`
    /// and `self.deref_mut()`.
    ///
    /// Note that, combined with the safety invariant on [`ByteSlice`], this
    /// safety invariant implies that the returned reference is "stable" in the
    /// sense described in the `ByteSlice` docs.
    fn into_byte_slice_mut(self) -> &'a mut [u8];
}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl ByteSlice for &[u8] {}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl CopyableByteSlice for &[u8] {}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl CloneableByteSlice for &[u8] {}

// SAFETY: This delegates to `polyfills:split_at_unchecked`, which is documented
// to correctly split `self` into two slices at the given `mid` point.
unsafe impl SplitByteSlice for &[u8] {
    #[inline]
    unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self) {
        // SAFETY: By contract on caller, `mid` is not greater than
        // `self.len()`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        unsafe {
            (<[u8]>::get_unchecked(self, ..mid), <[u8]>::get_unchecked(self, mid..))
        }
    }
}

// SAFETY: See inline.
unsafe impl<'a> IntoByteSlice<'a> for &'a [u8] {
    #[inline(always)]
    fn into_byte_slice(self) -> &'a [u8] {
        // SAFETY: It would be patently insane to implement `<Deref for
        // &[u8]>::deref` as anything other than `fn deref(&self) -> &[u8] {
        // *self }`. Assuming this holds, then `self` is stable as required by
        // `into_byte_slice`.
        self
    }
}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl ByteSlice for &mut [u8] {}

// SAFETY: This delegates to `polyfills:split_at_mut_unchecked`, which is
// documented to correctly split `self` into two slices at the given `mid`
// point.
unsafe impl SplitByteSlice for &mut [u8] {
    #[inline]
    unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self) {
        use core::slice::from_raw_parts_mut;

        // `l_ptr` is non-null, because `self` is non-null, by invariant on
        // `&mut [u8]`.
        let l_ptr = self.as_mut_ptr();

        // SAFETY: By contract on caller, `mid` is not greater than
        // `self.len()`.
        let r_ptr = unsafe { l_ptr.add(mid) };

        let l_len = mid;

        // SAFETY: By contract on caller, `mid` is not greater than
        // `self.len()`.
        //
        // FIXME(#67): Remove this allow. See NumExt for more details.
        #[allow(unstable_name_collisions)]
        let r_len = unsafe { self.len().unchecked_sub(mid) };

        // SAFETY: These invocations of `from_raw_parts_mut` satisfy its
        // documented safety preconditions [1]:
        // - The data `l_ptr` and `r_ptr` are valid for both reads and writes of
        //   `l_len` and `r_len` bytes, respectively, and they are trivially
        //   aligned. In particular:
        //   - The entire memory range of each slice is contained within a
        //     single allocated object, since `l_ptr` and `r_ptr` are both
        //     derived from within the address range of `self`.
        //   - Both `l_ptr` and `r_ptr` are non-null and trivially aligned.
        //     `self` is non-null by invariant on `&mut [u8]`, and the
        //     operations that derive `l_ptr` and `r_ptr` from `self` do not
        //     nullify either pointer.
        // - The data `l_ptr` and `r_ptr` point to `l_len` and `r_len`,
        //   respectively, consecutive properly initialized values of type `u8`.
        //   This is true for `self` by invariant on `&mut [u8]`, and remains
        //   true for these two sub-slices of `self`.
        // - The memory referenced by the returned slice cannot be accessed
        //   through any other pointer (not derived from the return value) for
        //   the duration of lifetime `'a``, because:
        //   - `split_at_unchecked` consumes `self` (which is not `Copy`),
        //   - `split_at_unchecked` does not exfiltrate any references to this
        //     memory, besides those references returned below,
        //   - the returned slices are non-overlapping.
        // - The individual sizes of the sub-slices of `self` are no larger than
        //   `isize::MAX`, because their combined sizes are no larger than
        //   `isize::MAX`, by invariant on `self`.
        //
        // [1] https://doc.rust-lang.org/std/slice/fn.from_raw_parts_mut.html#safety
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        unsafe {
            (from_raw_parts_mut(l_ptr, l_len), from_raw_parts_mut(r_ptr, r_len))
        }
    }
}

// SAFETY: See inline.
unsafe impl<'a> IntoByteSlice<'a> for &'a mut [u8] {
    #[inline(always)]
    fn into_byte_slice(self) -> &'a [u8] {
        // SAFETY: It would be patently insane to implement `<Deref for &mut
        // [u8]>::deref` as anything other than `fn deref(&self) -> &[u8] {
        // *self }`. Assuming this holds, then `self` is stable as required by
        // `into_byte_slice`.
        self
    }
}

// SAFETY: See inline.
unsafe impl<'a> IntoByteSliceMut<'a> for &'a mut [u8] {
    #[inline(always)]
    fn into_byte_slice_mut(self) -> &'a mut [u8] {
        // SAFETY: It would be patently insane to implement `<DerefMut for &mut
        // [u8]>::deref` as anything other than `fn deref_mut(&mut self) -> &mut
        // [u8] { *self }`. Assuming this holds, then `self` is stable as
        // required by `into_byte_slice_mut`.
        self
    }
}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl ByteSlice for cell::Ref<'_, [u8]> {}

// SAFETY: This delegates to stdlib implementation of `Ref::map_split`, which is
// assumed to be correct, and `SplitByteSlice::split_at_unchecked`, which is
// documented to correctly split `self` into two slices at the given `mid`
// point.
unsafe impl SplitByteSlice for cell::Ref<'_, [u8]> {
    #[inline]
    unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self) {
        cell::Ref::map_split(self, |slice|
            // SAFETY: By precondition on caller, `mid` is not greater than
            // `slice.len()`.
            unsafe {
                SplitByteSlice::split_at_unchecked(slice, mid)
            })
    }
}

// FIXME(#429): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl ByteSlice for cell::RefMut<'_, [u8]> {}

// SAFETY: This delegates to stdlib implementation of `RefMut::map_split`, which
// is assumed to be correct, and `SplitByteSlice::split_at_unchecked`, which is
// documented to correctly split `self` into two slices at the given `mid`
// point.
unsafe impl SplitByteSlice for cell::RefMut<'_, [u8]> {
    #[inline]
    unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self) {
        cell::RefMut::map_split(self, |slice|
            // SAFETY: By precondition on caller, `mid` is not greater than
            // `slice.len()`
            unsafe {
                SplitByteSlice::split_at_unchecked(slice, mid)
            })
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    // Configuration: Uses the common Kani CI configuration documented in
    // `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
    // x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
    // `-Zfunction-contracts`, and one layout selected by `--randomize-layout`
    // per invocation.
    //
    // Domain: Every four-byte array value, every view `start..end` satisfying
    // `0 <= start <= end <= 4` (including every empty, prefix, interior, and
    // suffix view), and every `usize` midpoint for the safe operation or every
    // midpoint satisfying `mid <= end - start` for the unchecked operation,
    // for `&[u8]`, `&mut [u8]`, `Ref<[u8]>`, and `RefMut<[u8]>`. The mutable
    // harnesses also quantify over every `usize` index and `u8` value for one
    // attempted write in each returned half.
    // Every harness uses one fixed four-byte stack backing array and fixed-size
    // snapshots; none performs a dynamic allocation. There is no explicit
    // proof loop. The unwind bound is five for every harness and applies to
    // any loop reached in zerocopy or a standard-library oracle, with Kani's
    // unwinding assertions enabled.
    //
    // Establishes: Exact success/failure classification and returned lengths
    // and ordered contents, including for empty partitions. For nonempty
    // partitions, it also establishes start addresses; when both partitions
    // are nonempty, their contiguity; and the source endpoint through whichever
    // terminal partition is nonempty. Shared forms preserve the backing array;
    // mutable forms perform at most one symbolic in-bounds write in each half
    // and establish the frame condition for the entire backing array, including
    // bytes outside the view. Failure preserves exact length and contents and,
    // only for a nonempty input, its start address.
    //
    // Oracle: Safe `slice::split_at_checked` independently supplies result
    // classification [1]; safe `slice::split_at` supplies expected partitions
    // over the documented `[0, mid)` and `[mid, len)` ranges [2]; and safe
    // `slice::split_at_mut` independently supplies expected mutations over the
    // same ranges [3]. For nonempty slices only, safe `slice::as_ptr` identifies
    // the buffer start [4], while `slice::as_ptr_range` identifies the
    // half-open address range and one-past-the-end pointer [5]. Safe
    // `slice::get_mut` makes each symbolic write conditional on its index being
    // in bounds [6]. Safe shared and mutable `Range<usize>` indexing selects
    // the half-open `view.start..view.end` subslice for each target input and,
    // independently, from the pre-target copy used to compute the mutation
    // frame [7]. Thus the expected values, nonempty address partition, and
    // mutation frame come only from safe standard-library operations which do
    // not call `SplitByteSlice`.
    // `any_view` keeps `start <= end <= BUFFER_LEN`, excluding [7]'s panic
    // cases. Because target setup uses the same safe indexing contract as the
    // expected-value oracle, these proofs trust Rust's documented range mapping
    // and Kani's model of it; they do not prove range indexing itself.
    //
    // Contents and whole-array frames use `assert_same_u8_elements`, not slice
    // or array `PartialEq`. Safe `slice::iter` returns an iterator which “yields
    // all items from start to end” [8]; `Iterator::copied` “copies all of its
    // elements,” and `Iterator::eq` determines whether one iterator's elements
    // equal another's [9]. `u8::eq` tests two `u8` values for equality [10].
    // The helper separately checks equal lengths, so these operations establish
    // the same ordered bytes. Whole arrays reach the helper through the
    // Reference's `[T; n]` to `[T]` unsizing coercion [11]. These safe
    // operations do not call zerocopy and establish neither allocation identity
    // nor aliasing or provenance. The remaining array `PartialEq` uses occur
    // only in `kani::cover!` reachability witnesses; no proof assertion depends
    // on them.
    //
    // No cited address contract selects a unique buffer address for an empty
    // slice. `expected_split` therefore records expected pointers only for
    // nonempty partitions, and the assertion helpers gate every returned or
    // failed-input pointer observation accordingly. Empty cases still establish
    // exact lengths and ordered contents.
    //
    // Excludes: Larger backing storage, other implementations, uninitialized
    // storage, program panic-unwind semantics, exact pointer identity for empty
    // inputs or returned partitions, and aliasing, provenance, and borrow-model
    // obligations that Kani does not fully model. Pointer equality checks only
    // Kani's modeled addresses, not provenance. In particular, these harnesses
    // exercise one split and optional writes; they do not prove `ByteSlice`'s
    // full address-and-length stability theorem across arbitrary method
    // sequences. These are not generic `SplitByteSlice` implementation proofs.
    //
    // [1] Rust 1.93 specifies that `mid <= len` returns the two documented
    // index ranges, and says “`mid > len`, returns `None`”:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_checked
    //
    // [2] Rust 1.93 specifies the shared results as `[0, mid)` and
    // `[mid, len)`:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at
    //
    // [3] Rust 1.93 specifies the mutable results using the same ranges:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_mut
    //
    // [4] Rust 1.93 says `as_ptr` returns a “raw pointer to the slice’s
    // buffer”:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
    //
    // [5] Rust 1.93 says the “returned range is half-open”; its end points one
    // past the final element:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr_range
    //
    // [6] Rust 1.93 says `get_mut` returns `None` “if the index is out of
    // bounds”:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.get_mut
    //
    // [7] Rust 1.93 says, “A (half-open) range bounded inclusively below and
    // exclusively above (`start..end`).” It further says, “The range
    // `start..end` contains all values with `start <= x < end`.” For
    // `SliceIndex<[T]> for Range<usize>`, `Output = [T]`; `index` says, “Returns
    // a shared reference to the output at this location, panicking if out of
    // bounds.” `index_mut` says, “Returns a mutable reference to the output at
    // this location, panicking if out of bounds.” The implementation documents
    // those panic cases as `start > end` or `end` out of bounds:
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.Range.html
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.Range.html#impl-SliceIndex%3C%5BT%5D%3E-for-Range%3Cusize%3E
    //
    // [8] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    //
    // [9] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
    // and https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
    //
    // [10] https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
    //
    // [11] https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.unsize.slice
    const BUFFER_LEN: usize = 4;

    #[derive(Copy, Clone)]
    struct View {
        start: usize,
        end: usize,
    }

    impl View {
        fn range(self) -> core::ops::Range<usize> {
            self.start..self.end
        }
    }

    struct ExpectedSplit {
        left_len: usize,
        right_len: usize,
        left_start: Option<*const u8>,
        right_start: Option<*const u8>,
        source_end: Option<*const u8>,
    }

    struct Writes {
        left_index: usize,
        left_value: u8,
        right_index: usize,
        right_value: u8,
    }

    fn any_view() -> View {
        let first = kani::any::<usize>() % (BUFFER_LEN + 1);
        let second = kani::any::<usize>() % (BUFFER_LEN + 1);
        let view =
            View { start: core::cmp::min(first, second), end: core::cmp::max(first, second) };

        kani::cover!(view.start == 0 && view.end == 0);
        kani::cover!(view.start == 0 && 0 < view.end && view.end < BUFFER_LEN);
        kani::cover!(view.start == 0 && view.end == BUFFER_LEN);
        kani::cover!(0 < view.start && view.start == view.end && view.end < BUFFER_LEN);
        kani::cover!(0 < view.start && view.start < view.end && view.end < BUFFER_LEN);
        kani::cover!(0 < view.start && view.start < view.end && view.end == BUFFER_LEN);
        kani::cover!(view.start == BUFFER_LEN && view.end == BUFFER_LEN);
        view
    }

    fn any_valid_mid(len: usize) -> usize {
        // `len <= BUFFER_LEN`, so `len + 1` cannot overflow.
        kani::any::<usize>() % (len + 1)
    }

    fn expected_split(left: &[u8], right: &[u8]) -> ExpectedSplit {
        let left_len = left.len();
        let right_len = right.len();
        let left_start = if left.is_empty() { None } else { Some(left.as_ptr()) };
        let right_start = if right.is_empty() { None } else { Some(right.as_ptr()) };
        let source_end = if !right.is_empty() {
            Some(right.as_ptr_range().end)
        } else if !left.is_empty() {
            Some(left.as_ptr_range().end)
        } else {
            None
        };
        ExpectedSplit { left_len, right_len, left_start, right_start, source_end }
    }

    fn assert_same_u8_elements(actual: &[u8], expected: &[u8]) {
        assert_eq!(actual.len(), expected.len());
        assert!(actual.iter().copied().eq(expected.iter().copied()));
    }

    fn assert_split<B: ByteSlice>(
        left: &B,
        right: &B,
        shape: ExpectedSplit,
        mid: usize,
        expected: &[u8],
    ) {
        let left = <B as Deref>::deref(left);
        let right = <B as Deref>::deref(right);
        let (expected_left, expected_right) = expected.split_at(mid);
        assert_same_u8_elements(left, expected_left);
        assert_same_u8_elements(right, expected_right);
        assert_eq!(left.len(), shape.left_len);
        assert_eq!(right.len(), shape.right_len);
        if !left.is_empty() {
            assert_eq!(Some(left.as_ptr()), shape.left_start);
        }
        if !right.is_empty() {
            assert_eq!(Some(right.as_ptr()), shape.right_start);
            assert_eq!(Some(right.as_ptr_range().end), shape.source_end);
        } else if !left.is_empty() {
            assert_eq!(Some(left.as_ptr_range().end), shape.source_end);
        }
        if !left.is_empty() && !right.is_empty() {
            assert_eq!(left.as_ptr_range().end, right.as_ptr());
        }
    }

    fn assert_unsplit<B: ByteSlice>(bytes: &B, base: Option<*const u8>, expected: &[u8]) {
        let bytes = <B as Deref>::deref(bytes);

        assert_same_u8_elements(bytes, expected);
        if !bytes.is_empty() {
            assert_eq!(Some(bytes.as_ptr()), base);
        }
    }

    fn check_split_at<B: SplitByteSlice>(
        bytes: B,
        mid: usize,
        expected: &[u8],
    ) -> Result<(B, B), B> {
        let (base, oracle, len) = {
            let bytes = <B as Deref>::deref(&bytes);
            let len = bytes.len();
            let oracle =
                bytes.split_at_checked(mid).map(|(left, right)| expected_split(left, right));
            let base = if bytes.is_empty() { None } else { Some(bytes.as_ptr()) };
            (base, oracle, len)
        };

        let result = match (SplitByteSlice::split_at(bytes, mid), oracle) {
            (Ok((left, right)), Some(shape)) => {
                assert_split(&left, &right, shape, mid, expected);
                Ok((left, right))
            }
            (Err(bytes), None) => {
                assert_unsplit(&bytes, base, expected);
                Err(bytes)
            }
            (Ok(_), None) => panic!("split succeeded when the std oracle rejected the midpoint"),
            (Err(_), Some(_)) => panic!("split failed when the std oracle accepted the midpoint"),
        };

        // Ensure that bounds and result assertions are not proved vacuously.
        kani::cover!(len == 0 && mid == 0);
        kani::cover!(len > 0 && mid == 0);
        kani::cover!(0 < mid && mid < len);
        kani::cover!(len > 0 && mid == len);
        kani::cover!(mid > len);
        result
    }

    fn check_split_at_unchecked<B: SplitByteSlice>(
        bytes: B,
        mid: usize,
        expected: &[u8],
    ) -> (B, B) {
        let (shape, len) = {
            let bytes = <B as Deref>::deref(&bytes);
            let len = bytes.len();
            assert!(mid <= len);
            let (left, right) = bytes.split_at(mid);
            (expected_split(left, right), len)
        };

        // SAFETY: The preceding dereference yielded `len`, and the assertion
        // establishes `mid <= len`. `ByteSlice` guarantees length-stable
        // dereferencing through this call, so
        // `mid <= bytes.deref().len()` at invocation. This is the same bound
        // required by the standard slice operation [1].
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_unchecked:
        //
        //     Calling this method with an out-of-bounds index is undefined
        //     behavior even if the resulting reference is not used. The caller
        //     has to ensure that `0 <= mid <= self.len()`.
        let (left, right) = unsafe { SplitByteSlice::split_at_unchecked(bytes, mid) };
        assert_split(&left, &right, shape, mid, expected);

        kani::cover!(len == 0 && mid == 0);
        kani::cover!(len > 0 && mid == 0);
        kani::cover!(0 < mid && mid < len);
        kani::cover!(len > 0 && mid == len);
        (left, right)
    }

    fn mutate_split<B: ByteSliceMut>(left: &mut B, right: &mut B, writes: &Writes) {
        if let Some(byte) = <B as DerefMut>::deref_mut(left).get_mut(writes.left_index) {
            kani::cover!(*byte != writes.left_value);
            *byte = writes.left_value;
        }
        if let Some(byte) = <B as DerefMut>::deref_mut(right).get_mut(writes.right_index) {
            kani::cover!(*byte != writes.right_value);
            *byte = writes.right_value;
        }
    }

    fn expected_after_writes(
        original: &[u8; BUFFER_LEN],
        view: View,
        mid: Option<usize>,
        writes: &Writes,
    ) -> [u8; BUFFER_LEN] {
        let mut expected = *original;
        if let Some(mid) = mid {
            let (left, right) = expected[view.range()].split_at_mut(mid);
            if let Some(byte) = left.get_mut(writes.left_index) {
                *byte = writes.left_value;
            }
            if let Some(byte) = right.get_mut(writes.right_index) {
                *byte = writes.right_value;
            }
        }
        expected
    }

    fn assert_write_frame(
        actual: &[u8; BUFFER_LEN],
        original: &[u8; BUFFER_LEN],
        view: View,
        mid: Option<usize>,
        writes: &Writes,
    ) {
        let expected = expected_after_writes(original, view, mid, writes);
        kani::cover!(view.start > 0 && expected != *original);
        kani::cover!(view.end < BUFFER_LEN && expected != *original);
        assert_same_u8_elements(actual, &expected);
    }

    fn any_writes() -> Writes {
        Writes {
            left_index: kani::any(),
            left_value: kani::any(),
            right_index: kani::any(),
            right_value: kani::any(),
        }
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_shared_slice_split_at() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let _ = check_split_at(&bytes[view.range()], kani::any(), &original[view.range()]);
        assert_same_u8_elements(&bytes, &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_shared_slice_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let _ = check_split_at_unchecked(&bytes[view.range()], mid, &original[view.range()]);
        assert_same_u8_elements(&bytes, &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_mut_slice_split_at() {
        let mut bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let mid = kani::any();
        let writes = any_writes();
        let split_mid = match check_split_at(&mut bytes[view.range()], mid, &original[view.range()])
        {
            Ok((mut left, mut right)) => {
                mutate_split(&mut left, &mut right, &writes);
                Some(mid)
            }
            Err(_) => None,
        };
        assert_write_frame(&bytes, &original, view, split_mid, &writes);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_mut_slice_split_at_unchecked() {
        let mut bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let writes = any_writes();
        {
            let (mut left, mut right) =
                check_split_at_unchecked(&mut bytes[view.range()], mid, &original[view.range()]);
            mutate_split(&mut left, &mut right, &writes);
        }
        assert_write_frame(&bytes, &original, view, Some(mid), &writes);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_split_at() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::Ref::map(cell.borrow(), |bytes| &bytes[view.range()]);
        let _ = check_split_at(bytes, kani::any(), &original[view.range()]);
        assert_same_u8_elements(&cell.into_inner(), &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::Ref::map(cell.borrow(), |bytes| &bytes[view.range()]);
        let _ = check_split_at_unchecked(bytes, mid, &original[view.range()]);
        assert_same_u8_elements(&cell.into_inner(), &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_mut_split_at() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let mid = kani::any();
        let writes = any_writes();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::RefMut::map(cell.borrow_mut(), |bytes| &mut bytes[view.range()]);
        let split_mid = match check_split_at(bytes, mid, &original[view.range()]) {
            Ok((mut left, mut right)) => {
                mutate_split(&mut left, &mut right, &writes);
                Some(mid)
            }
            Err(_) => None,
        };
        let bytes = cell.into_inner();
        assert_write_frame(&bytes, &original, view, split_mid, &writes);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_mut_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = bytes;
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let writes = any_writes();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::RefMut::map(cell.borrow_mut(), |bytes| &mut bytes[view.range()]);
        let (mut left, mut right) = check_split_at_unchecked(bytes, mid, &original[view.range()]);
        mutate_split(&mut left, &mut right, &writes);
        drop(left);
        drop(right);
        let bytes = cell.into_inner();
        assert_write_frame(&bytes, &original, view, Some(mid), &writes);
    }
}

#[cfg(test)]
mod tests {
    use core::cell::RefCell;

    use super::*;

    #[test]
    fn test_ref_split_at_unchecked() {
        let cell = RefCell::new([1, 2, 3, 4]);
        let borrow = cell.borrow();
        let slice_ref: cell::Ref<'_, [u8]> = cell::Ref::map(borrow, |a| &a[..]);
        // SAFETY: 2 is within bounds of [1, 2, 3, 4]
        let (l, r) = unsafe { slice_ref.split_at_unchecked(2) };
        assert_eq!(*l, [1, 2]);
        assert_eq!(*r, [3, 4]);
    }

    #[test]
    fn test_ref_mut_split_at_unchecked() {
        let cell = RefCell::new([1, 2, 3, 4]);
        let borrow_mut = cell.borrow_mut();
        let slice_ref_mut: cell::RefMut<'_, [u8]> = cell::RefMut::map(borrow_mut, |a| &mut a[..]);
        // SAFETY: 2 is within bounds of [1, 2, 3, 4]
        let (l, r) = unsafe { slice_ref_mut.split_at_unchecked(2) };
        assert_eq!(*l, [1, 2]);
        assert_eq!(*r, [3, 4]);
    }
}
