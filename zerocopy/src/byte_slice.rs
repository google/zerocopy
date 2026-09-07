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
    use crate::proof_support::{
        any_usize_inclusive, assert_same_u8_elements, assert_same_usize, copy_snapshot,
    };

    // Configuration: Uses the common Kani CI configuration documented in
    // `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
    // x86_64-unknown-linux-gnu compiler and CBMC, the stable-compatible feature
    // bundle, `-Zfunction-contracts`, and one layout selected by
    // `--randomize-layout` per invocation. Every harness uses unwind bound five
    // with unwinding assertions enabled.
    //
    // Fixed-content domain: Eight harnesses quantify over every four-byte array
    // value; every view `start..end` satisfying
    // `0 <= start <= end <= BUFFER_LEN`; and every `usize` midpoint for the
    // safe operation or every valid midpoint for the unchecked operation, for
    // `&[u8]`, `&mut [u8]`, `Ref<[u8]>`, and `RefMut<[u8]>`. The mutable
    // harnesses additionally quantify over every `usize` index and `u8` value
    // for one attempted write in each result. Each harness owns one fixed
    // four-byte stack array and fixed-size copies; it performs no allocation.
    // The shared `any_usize_inclusive` generator supplies every endpoint and
    // every valid midpoint with checked domain-size arithmetic and a central
    // executable bound. Safe `core::cmp::{min,max}` then order the two
    // independently generated endpoints according to `Ord` [22]. These are
    // proof-domain construction mechanics, not split-result oracles.
    //
    // Symbolic-shape domain: Two separate allocation-backed harnesses exercise
    // the unchecked implementation for `&[u8]` and `&mut [u8]`. Each quantifies
    // over every zero-filled `Vec<u8>` length in
    // `0..=DstLayout::MAX_SIZE` and every `mid <= len`. This includes lengths
    // beyond `BUFFER_LEN`, and the start, interior, and end partitions at
    // `DstLayout::MAX_SIZE`. These two harnesses inspect only lengths and
    // addresses, not contents or writes. They require the `alloc` feature.
    //
    // Allocation and loop bounds: The repeated `vec!` form safely constructs
    // exactly the requested number of zero-valued elements [23], and `Vec::len`
    // reports that count [24]. A fail-closed equality check first connects the
    // requested symbolic length to that vector length. `Vec::as_slice` and
    // `Vec::as_mut_slice` then extract, respectively, a shared slice containing
    // the entire vector and a mutable slice of the entire vector [29]. Together
    // with `slice::len` [21], those safe adapters bridge the requested count to
    // the slice length observed inside `check_split_at_unchecked_shape`. They
    // call no zerocopy target and do not reconstruct an expected split; they
    // establish the input domain rather than a result oracle. The bridge trusts
    // the cited `Vec` contracts and Kani's model of them, and does not establish
    // real allocation availability, backing-allocation identity, provenance,
    // or aliasing. Zero contents are setup for the shape-only proof, not a
    // conclusion.
    //
    // Allocation-model bridge (TOOL/TCB premise): In the pinned Rust library,
    // `vec![0u8; len]` selects the `u8` zero-element specialization [25], which
    // requests zeroed `RawVec` storage [26]. Exact linked GOTO inspection after
    // Function Pointer Removal shows that, for `len > 0`, this reaches
    // `Global::allocate_zeroed`, `std::alloc::alloc_zeroed`, Kani's
    // `__rust_alloc_zeroed(len, 1)`, and finally `calloc(1, len)` [27]. Length
    // zero uses the standard library's dangling zero-size path and makes no C
    // allocator call. Because both the Rust element size and C element count
    // are one, `len <= DstLayout::MAX_SIZE == isize::MAX` avoids Rust layout
    // multiplication overflow and `calloc` multiplication overflow.
    //
    // Kani 0.67 invokes bundled CBMC with `--no-malloc-may-fail` [14]. Exact
    // GOTO/VCC inspection shows that this fixes the allocation-failure mode to
    // zero and bypasses both the nondeterministic-failure and configured
    // maximum-allocation-size null branches. Consequently the satisfied
    // maximum-length cover obtains an abstract dynamic object at `isize::MAX`,
    // even though that is not a realizable production allocation and exceeds
    // CBMC's reported representable allocation size. CBMC documents always-
    // successful allocation as its default model and separately describes the
    // optional too-large failure configuration [28]. The Rust specialization
    // and lowering, Kani shim, CBMC flag/model behavior, and huge-object
    // representation are manually audited TOOL/TCB premises, not theorems of
    // these harnesses; changes to any of them require a repeat audit.
    //
    // There is no explicit proof loop. The unwind bound applies to every loop
    // reachable in zerocopy, allocation setup, destruction, or an oracle.
    // Successful unwinding assertions establish that five is sufficient for
    // this exact translation; the proof does not assume a lowering or claim a
    // minimum.
    //
    // Establishes: In the fixed-content domain, exact success/failure
    // classification and exact returned lengths and ordered contents. Shared
    // forms preserve the backing array. Mutable forms perform at most one
    // symbolic in-bounds write in each result and establish the frame condition
    // for the entire backing array, including bytes outside the view. Failure
    // preserves exact length, contents, and modeled start address. In both
    // domains, successful splits satisfy the `SplitByteSlice` address policy:
    // the first result starts at the source address and the second at the
    // source address plus `mid`, including when the source or either result is
    // empty. The symbolic-shape harnesses additionally establish the two
    // result lengths across the full stated length domain. Whenever a result
    // is nonempty, its start address also agrees with the corresponding result
    // returned directly by Rust's safe split oracle; empty-result addresses
    // remain solely zerocopy policy checks.
    //
    // Rust-level oracles: Safe `slice::split_at_checked` independently supplies
    // result classification [1]; safe `slice::split_at` supplies expected
    // lengths, contents, and direct nonempty-result pointer observations over
    // `[0, mid)` and `[mid, len)` [2][4]; and safe `slice::split_at_mut`
    // supplies expected mutations over those ranges [3].
    // `std_nonempty_start` factors the direct pointer gate through safe
    // `slice::first`, which returns the first element or `None` when empty [18];
    // `Option::map` transforms only the `Some` case [19], and `ptr::from_ref`
    // obtains that element reference's raw pointer [20]. The helper calls no
    // zerocopy target and supplies a pointer exactly when the safe split result
    // has a first element; it intentionally supplies no empty-result address.
    // Safe `slice::get_mut` makes each symbolic write conditional on its index
    // being in bounds [6]. Safe shared and mutable `Range<usize>` indexing
    // selects the half-open `view.start..view.end` target input and,
    // independently, the corresponding pre-target copy used for the frame [7].
    // `any_view` excludes [7]'s panic cases. These proofs trust the documented
    // range mapping and Kani's model of it; they do not prove indexing itself.
    // For the guard-backed harnesses, safe `RefCell::new` creates a cell
    // containing the generated array, while `borrow` and `borrow_mut` borrow
    // that wrapped value shared or mutably [33]. Safe `Ref::map` and
    // `RefMut::map` then create a new guard for the component returned by the
    // mapping closure [30][31]; the closure returns exactly the range-selected
    // slice just described. After the target returns, each harness moves every
    // returned guard into `mem::forget`, which takes ownership without running
    // its destructor [34]. This excludes guard destruction from the frame
    // observation. Safe `RefCell::into_inner` then consumes the cell and returns
    // its wrapped array [32], which supplies the whole backing-array observation
    // used by the preservation or write-frame assertion. None of these adapters
    // invokes a zerocopy target. They are nevertheless not independent
    // implementations of `RefCell` mechanics: `Ref::{map,map_split}`,
    // `RefMut::{map,map_split}`, cell construction and borrowing, and
    // `into_inner` may share standard-library representation and Kani lowering.
    // Accordingly, this adapter chain does not prove dynamic borrow enforcement,
    // guard lifetimes, aliasing, or provenance, and a common defect in that
    // trusted machinery could affect both setup and the target execution.
    // Calls to standard slice oracles and calls to the target trait use
    // explicit UFCS so method lookup cannot exchange them.
    //
    // Contents and frames use the shared `assert_same_u8_elements`, not slice
    // or array `PartialEq`. It obtains element counts through `slice::len` and
    // the shared `assert_same_usize`; direct result-shape checks use that same
    // equality helper [21]. Safe iteration and byte equality compare ordered
    // values [8]-[10]. Whole arrays reach the byte helper through `[T; N]`-to-
    // `[T]` unsizing [11]. Array snapshots use the shared `copy_snapshot`:
    // evaluating a place of a `Copy` type copies rather than moves it [12], and
    // `[u8; BUFFER_LEN]` is `Copy` because arrays are `Copy` when their element
    // type is, and `u8` is `Copy` [13]. These are value oracles; they do not
    // establish distinct storage or allocation identity. Array `PartialEq`
    // remains only in `kani::cover!` reachability witnesses.
    //
    // Zerocopy policy oracle: The local `SplitByteSlice` safety contract, not a
    // Rust slice contract, requires exact result addresses even for empty
    // partitions. `split_address_policy` deliberately restates that API policy
    // from the pre-call source pointer: first starts at `source.as_ptr()` and
    // second at `source.as_ptr().wrapping_add(mid)`. `as_ptr` identifies the
    // buffer pointer [4]; `wrapping_add` is always safe and advances by `mid`
    // elements [5]; and `u8` has size and alignment one [15]. Since a valid
    // slice allocation cannot wrap the address space [16], the wrapping
    // operation expresses the contract's `addr + mid` without an unsafe oracle
    // operation. `ptr::addr_eq` compares addresses while ignoring metadata
    // [17]. The failed-split base-address check likewise restates
    // `ByteSlice`'s stable-address policy together with `split_at` returning
    // the original value in `Err`. Consequently these unconditional assertions
    // check Kani's modeled addresses only; they are policy-regression evidence,
    // not independent Rust-level evidence for the empty-slice address choice,
    // provenance, or allocation identity. For nonempty results, the safe
    // split's direct pointer observations independently corroborate the same
    // addresses. No cited Rust contract selects an exact address for an empty
    // result, so those cases deliberately remain policy-only.
    //
    // Trust boundary: The proofs trust Kani, CBMC, the bundled compiler and
    // standard-library model, the cited language/library rules, and the manual
    // compatibility proposition in `agent_docs/validation.md` between those
    // Rust 1.93 contracts and Kani's bundled nightly. The unconditional address
    // oracle also trusts the stated zerocopy target policy; it detects
    // implementation drift but cannot validate the policy itself. Nonempty
    // addresses additionally have the direct std observation above. The
    // allocation-backed results trust Kani's forced-success allocation model.
    // The `Vec` and `RefCell` adapter bridges additionally trust Kani's model of
    // the cited standard-library operations; in particular, the guard-backed
    // observations are not structurally independent of `map_split`'s internal
    // `RefCell` machinery. Forgetting the returned guards deliberately excludes
    // their destruction and release behavior; the harnesses immediately consume
    // the cell and do not establish that it can be borrowed again afterward.
    //
    // Excludes: Content and mutation properties above four bytes, nonzero
    // contents in the symbolic-shape harnesses, other implementations,
    // uninitialized storage, configurations without `alloc`, real allocation
    // availability, program panic-unwind behavior, and aliasing, provenance,
    // and borrow-model obligations that Kani does not fully model. The
    // harnesses exercise one split and optional writes; they do not prove
    // `ByteSlice`'s stability theorem across arbitrary method sequences. These
    // are concrete implementation checks, not a generic `SplitByteSlice`
    // theorem.
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
    // [5] Rust 1.93 says `wrapping_add` is always safe and computes
    // `self.wrapping_offset(count as isize)`:
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.wrapping_add
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
    //
    // [12] https://doc.rust-lang.org/1.93.0/reference/expressions.html#moved-and-copied-types
    //
    // [13] https://doc.rust-lang.org/1.93.0/std/primitive.array.html#trait-implementations-1
    // and https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-Copy-for-u8
    //
    // [14] https://github.com/model-checking/kani/blob/kani-0.67.0/kani-driver/src/call_cbmc.rs#L213-L219
    //
    // [15] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#primitive-data-layout
    //
    // [16] https://doc.rust-lang.org/1.93.0/std/ptr/index.html#allocated-object
    //
    // [17] https://doc.rust-lang.org/1.93.0/std/ptr/fn.addr_eq.html
    // [18] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.first
    // [19] https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.map
    // [20] https://doc.rust-lang.org/1.93.0/std/ptr/fn.from_ref.html
    // [21] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    // [22] https://doc.rust-lang.org/1.93.0/core/cmp/fn.min.html
    // https://doc.rust-lang.org/1.93.0/core/cmp/fn.max.html
    // [23] https://doc.rust-lang.org/1.93.0/alloc/macro.vec.html
    // [24] https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.len
    // [25] https://github.com/rust-lang/rust/blob/53732d5e076329a62f71d3c6901886ce8a71e812/library/alloc/src/vec/spec_from_elem.rs#L48-L59
    // [26] https://github.com/rust-lang/rust/blob/53732d5e076329a62f71d3c6901886ce8a71e812/library/alloc/src/raw_vec/mod.rs#L437-L475
    // https://github.com/rust-lang/rust/blob/53732d5e076329a62f71d3c6901886ce8a71e812/library/alloc/src/alloc.rs#L185-L195
    // [27] https://github.com/model-checking/kani/blob/kani-0.67.0/library/kani/kani_lib.c#L50-L67
    // [28] https://diffblue.github.io/cbmc/cprover-manual/md_memory-primitives.html#malloc-modelling
    // [29] https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.as_slice
    // https://doc.rust-lang.org/1.93.0/alloc/vec/struct.Vec.html#method.as_mut_slice
    // [30] https://doc.rust-lang.org/1.93.0/std/cell/struct.Ref.html#method.map
    // [31] https://doc.rust-lang.org/1.93.0/std/cell/struct.RefMut.html#method.map
    // [32] https://doc.rust-lang.org/1.93.0/std/cell/struct.RefCell.html#method.into_inner
    // [33] https://doc.rust-lang.org/1.93.0/std/cell/struct.RefCell.html#method.new
    // https://doc.rust-lang.org/1.93.0/std/cell/struct.RefCell.html#method.borrow
    // https://doc.rust-lang.org/1.93.0/std/cell/struct.RefCell.html#method.borrow_mut
    // [34] https://doc.rust-lang.org/1.93.0/core/mem/fn.forget.html
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

    struct SplitShape {
        left_len: usize,
        right_len: usize,
    }

    struct SplitAddressPolicy {
        left_start: *const u8,
        right_start: *const u8,
    }

    struct StdSplitAddressOracle {
        left_start: Option<*const u8>,
        right_start: Option<*const u8>,
    }

    struct ExpectedSplit {
        shape: SplitShape,
        policy_addresses: SplitAddressPolicy,
        std_addresses: StdSplitAddressOracle,
    }

    struct Writes {
        left_index: usize,
        left_value: u8,
        right_index: usize,
        right_value: u8,
    }

    fn any_view() -> View {
        let first = any_usize_inclusive(BUFFER_LEN);
        let second = any_usize_inclusive(BUFFER_LEN);
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
        any_usize_inclusive(len)
    }

    fn split_address_policy(source: &[u8], mid: usize) -> SplitAddressPolicy {
        assert!(mid <= source.len());
        let left_start = source.as_ptr();
        let right_start = left_start.wrapping_add(mid);
        SplitAddressPolicy { left_start, right_start }
    }

    fn std_nonempty_start(slice: &[u8]) -> Option<*const u8> {
        slice.first().map(core::ptr::from_ref)
    }

    fn expected_split(source: &[u8], mid: usize, left: &[u8], right: &[u8]) -> ExpectedSplit {
        ExpectedSplit {
            shape: SplitShape { left_len: left.len(), right_len: right.len() },
            policy_addresses: split_address_policy(source, mid),
            std_addresses: StdSplitAddressOracle {
                left_start: std_nonempty_start(left),
                right_start: std_nonempty_start(right),
            },
        }
    }

    fn assert_split_shape<B: ByteSlice>(left: &B, right: &B, expected: ExpectedSplit) {
        let left = <B as Deref>::deref(left);
        let right = <B as Deref>::deref(right);

        assert_same_usize(left.len(), expected.shape.left_len);
        assert_same_usize(right.len(), expected.shape.right_len);
        assert!(core::ptr::addr_eq(left.as_ptr(), expected.policy_addresses.left_start));
        assert!(core::ptr::addr_eq(right.as_ptr(), expected.policy_addresses.right_start));
        if let Some(std_left_start) = expected.std_addresses.left_start {
            assert!(core::ptr::addr_eq(left.as_ptr(), std_left_start));
        }
        if let Some(std_right_start) = expected.std_addresses.right_start {
            assert!(core::ptr::addr_eq(right.as_ptr(), std_right_start));
        }
    }

    fn assert_split_contents<B: ByteSlice>(left: &B, right: &B, mid: usize, expected: &[u8]) {
        let left = <B as Deref>::deref(left);
        let right = <B as Deref>::deref(right);
        let (expected_left, expected_right) = <[u8]>::split_at(expected, mid);
        assert_same_u8_elements(left, expected_left);
        assert_same_u8_elements(right, expected_right);
    }

    fn assert_split<B: ByteSlice>(
        left: &B,
        right: &B,
        oracle: ExpectedSplit,
        mid: usize,
        expected: &[u8],
    ) {
        assert_split_shape(left, right, oracle);
        assert_split_contents(left, right, mid, expected);
    }

    fn assert_unsplit<B: ByteSlice>(bytes: &B, base: *const u8, expected: &[u8]) {
        let bytes = <B as Deref>::deref(bytes);

        assert_same_u8_elements(bytes, expected);
        assert!(core::ptr::addr_eq(bytes.as_ptr(), base));
    }

    fn check_split_at<B: SplitByteSlice>(
        bytes: B,
        mid: usize,
        expected: &[u8],
    ) -> Result<(B, B), B> {
        let (base, oracle, len) = {
            let bytes = <B as Deref>::deref(&bytes);
            let len = bytes.len();
            let oracle = <[u8]>::split_at_checked(bytes, mid)
                .map(|(left, right)| expected_split(bytes, mid, left, right));
            let base = bytes.as_ptr();
            (base, oracle, len)
        };

        let result = match (<B as SplitByteSlice>::split_at(bytes, mid), oracle) {
            (Ok((left, right)), Some(oracle)) => {
                assert_split(&left, &right, oracle, mid, expected);
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

    fn check_split_at_unchecked_shape<B: SplitByteSlice>(bytes: B, mid: usize) -> (B, B) {
        let (oracle, len) = {
            let bytes = <B as Deref>::deref(&bytes);
            let len = bytes.len();
            assert!(mid <= len);
            let (left, right) = <[u8]>::split_at(bytes, mid);
            (expected_split(bytes, mid, left, right), len)
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
        let (left, right) = unsafe { <B as SplitByteSlice>::split_at_unchecked(bytes, mid) };
        assert_split_shape(&left, &right, oracle);

        kani::cover!(len == 0 && mid == 0);
        kani::cover!(len > 0 && mid == 0);
        kani::cover!(0 < mid && mid < len);
        kani::cover!(len > 0 && mid == len);
        (left, right)
    }

    fn check_split_at_unchecked<B: SplitByteSlice>(
        bytes: B,
        mid: usize,
        expected: &[u8],
    ) -> (B, B) {
        let (left, right) = check_split_at_unchecked_shape(bytes, mid);
        assert_split_contents(&left, &right, mid, expected);
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
        let mut expected = copy_snapshot(original);
        if let Some(mid) = mid {
            let (left, right) = <[u8]>::split_at_mut(&mut expected[view.range()], mid);
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
        kani::cover!(view.start > 0 && expected != copy_snapshot(original));
        kani::cover!(view.end < BUFFER_LEN && expected != copy_snapshot(original));
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

    #[cfg(feature = "alloc")]
    fn any_symbolic_length_storage() -> alloc::vec::Vec<u8> {
        let requested_len = kani::any();
        kani::assume(requested_len <= crate::DstLayout::MAX_SIZE);
        let storage = alloc::vec![0u8; requested_len];
        assert_same_usize(storage.len(), requested_len);
        storage
    }

    #[cfg(feature = "alloc")]
    fn cover_symbolic_shape_domain(len: usize, mid: usize) {
        kani::cover!(len == 0 && mid == 0);
        kani::cover!(len == BUFFER_LEN + 1);
        kani::cover!(len == crate::DstLayout::MAX_SIZE && mid == 0);
        kani::cover!(len == crate::DstLayout::MAX_SIZE && 0 < mid && mid < len);
        kani::cover!(len == crate::DstLayout::MAX_SIZE && mid == len);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_shared_slice_split_at_unchecked_shape_all_lengths() {
        let bytes = any_symbolic_length_storage();
        let len = bytes.len();
        let mid = kani::any();
        kani::assume(mid <= len);

        let _ = check_split_at_unchecked_shape::<&[u8]>(bytes.as_slice(), mid);
        cover_symbolic_shape_domain(len, mid);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_mut_slice_split_at_unchecked_shape_all_lengths() {
        let mut bytes = any_symbolic_length_storage();
        let len = bytes.len();
        let mid = kani::any();
        kani::assume(mid <= len);

        let _ = check_split_at_unchecked_shape::<&mut [u8]>(bytes.as_mut_slice(), mid);
        cover_symbolic_shape_domain(len, mid);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_shared_slice_split_at() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = copy_snapshot(&bytes);
        let view = any_view();
        let _ = check_split_at(&bytes[view.range()], kani::any(), &original[view.range()]);
        assert_same_u8_elements(&bytes, &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_shared_slice_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = copy_snapshot(&bytes);
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
        let original = copy_snapshot(&bytes);
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
        let original = copy_snapshot(&bytes);
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
        let original = copy_snapshot(&bytes);
        let view = any_view();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::Ref::map(cell.borrow(), |bytes| &bytes[view.range()]);
        match check_split_at(bytes, kani::any(), &original[view.range()]) {
            Ok((left, right)) => {
                core::mem::forget(left);
                core::mem::forget(right);
            }
            Err(bytes) => core::mem::forget(bytes),
        }
        assert_same_u8_elements(&cell.into_inner(), &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = copy_snapshot(&bytes);
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::Ref::map(cell.borrow(), |bytes| &bytes[view.range()]);
        let (left, right) = check_split_at_unchecked(bytes, mid, &original[view.range()]);
        core::mem::forget(left);
        core::mem::forget(right);
        assert_same_u8_elements(&cell.into_inner(), &original);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_mut_split_at() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = copy_snapshot(&bytes);
        let view = any_view();
        let mid = kani::any();
        let writes = any_writes();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::RefMut::map(cell.borrow_mut(), |bytes| &mut bytes[view.range()]);
        let split_mid = match check_split_at(bytes, mid, &original[view.range()]) {
            Ok((mut left, mut right)) => {
                mutate_split(&mut left, &mut right, &writes);
                core::mem::forget(left);
                core::mem::forget(right);
                Some(mid)
            }
            Err(bytes) => {
                core::mem::forget(bytes);
                None
            }
        };
        let bytes = cell.into_inner();
        assert_write_frame(&bytes, &original, view, split_mid, &writes);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_ref_mut_split_at_unchecked() {
        let bytes = kani::any::<[u8; BUFFER_LEN]>();
        let original = copy_snapshot(&bytes);
        let view = any_view();
        let len = original[view.range()].len();
        let mid = any_valid_mid(len);
        let writes = any_writes();
        let cell = cell::RefCell::new(bytes);
        let bytes = cell::RefMut::map(cell.borrow_mut(), |bytes| &mut bytes[view.range()]);
        let (mut left, mut right) = check_split_at_unchecked(bytes, mid, &original[view.range()]);
        mutate_split(&mut left, &mut right, &writes);
        core::mem::forget(left);
        core::mem::forget(right);
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
