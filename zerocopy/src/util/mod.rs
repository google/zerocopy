// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[macro_use]
pub(crate) mod macros;

#[doc(hidden)]
pub mod macro_util;

use core::{
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    num::NonZeroUsize,
    ptr::NonNull,
};

use super::*;
use crate::pointer::{
    invariant::{Exclusive, Shared, Valid},
    SizeEq, TransmuteFromPtr,
};

/// Like [`PhantomData`], but [`Send`] and [`Sync`] regardless of whether the
/// wrapped `T` is.
pub(crate) struct SendSyncPhantomData<T: ?Sized>(PhantomData<T>);

// SAFETY: `SendSyncPhantomData` does not enable any behavior which isn't sound
// to be called from multiple threads.
unsafe impl<T: ?Sized> Send for SendSyncPhantomData<T> {}
// SAFETY: `SendSyncPhantomData` does not enable any behavior which isn't sound
// to be called from multiple threads.
unsafe impl<T: ?Sized> Sync for SendSyncPhantomData<T> {}

impl<T: ?Sized> Default for SendSyncPhantomData<T> {
    fn default() -> SendSyncPhantomData<T> {
        SendSyncPhantomData(PhantomData)
    }
}

impl<T: ?Sized> PartialEq for SendSyncPhantomData<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<T: ?Sized> Eq for SendSyncPhantomData<T> {}

impl<T: ?Sized> Clone for SendSyncPhantomData<T> {
    fn clone(&self) -> Self {
        SendSyncPhantomData(PhantomData)
    }
}

#[cfg(miri)]
extern "Rust" {
    /// Miri-provided intrinsic that marks the pointer `ptr` as aligned to
    /// `align`.
    ///
    /// This intrinsic is used to inform Miri's symbolic alignment checker that
    /// a pointer is aligned, even if Miri cannot statically deduce that fact.
    /// This is often required when performing raw pointer arithmetic or casts
    /// where the alignment is guaranteed by runtime checks or invariants that
    /// Miri is not aware of.
    pub(crate) fn miri_promise_symbolic_alignment(ptr: *const (), align: usize);
}

pub(crate) trait AsAddress {
    fn addr(self) -> usize;
}

impl<T: ?Sized> AsAddress for &T {
    #[inline(always)]
    fn addr(self) -> usize {
        let ptr: *const T = self;
        AsAddress::addr(ptr)
    }
}

impl<T: ?Sized> AsAddress for &mut T {
    #[inline(always)]
    fn addr(self) -> usize {
        let ptr: *const T = self;
        AsAddress::addr(ptr)
    }
}

impl<T: ?Sized> AsAddress for NonNull<T> {
    #[inline(always)]
    fn addr(self) -> usize {
        AsAddress::addr(self.as_ptr())
    }
}

impl<T: ?Sized> AsAddress for *const T {
    #[inline(always)]
    fn addr(self) -> usize {
        // FIXME(#181), FIXME(https://github.com/rust-lang/rust/issues/95228):
        // Use `.addr()` instead of `as usize` once it's stable, and get rid of
        // this `allow`. Currently, `as usize` is the only way to accomplish
        // this.
        #[allow(clippy::as_conversions)]
        #[cfg_attr(
            __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS,
            allow(lossy_provenance_casts)
        )]
        return self.cast::<()>() as usize;
    }
}

impl<T: ?Sized> AsAddress for *mut T {
    #[inline(always)]
    fn addr(self) -> usize {
        let ptr: *const T = self;
        AsAddress::addr(ptr)
    }
}

/// Validates that `t` is aligned to `align_of::<U>()`.
#[inline(always)]
pub(crate) fn validate_aligned_to<T: AsAddress, U>(t: T) -> Result<(), AlignmentError<(), U>> {
    // `mem::align_of::<U>()` is guaranteed to return a non-zero value, which in
    // turn guarantees that this mod operation will not panic.
    #[allow(clippy::arithmetic_side_effects)]
    let remainder = t.addr() % mem::align_of::<U>();
    if remainder == 0 {
        Ok(())
    } else {
        // SAFETY: We just confirmed that `t.addr() % align_of::<U>() != 0`.
        // That's only possible if `align_of::<U>() > 1`.
        Err(unsafe { AlignmentError::new_unchecked(()) })
    }
}

/// Returns the bytes needed to pad `len` to the next multiple of `align`.
///
/// This function assumes that align is a power of two; there are no guarantees
/// on the answer it gives if this is not the case.
#[cfg_attr(
    kani,
    kani::requires(len <= DstLayout::MAX_SIZE),
    kani::requires(align.is_power_of_two()),
    kani::ensures(|&p| (len + p) % align.get() == 0),
    // Ensures that we add the minimum required padding.
    kani::ensures(|&p| p < align.get()),
)]
#[cfg_attr(not(zerocopy_inline_always), inline)]
#[cfg_attr(zerocopy_inline_always, inline(always))]
pub(crate) const fn padding_needed_for(len: usize, align: NonZeroUsize) -> usize {
    #[cfg(kani)]
    #[kani::proof_for_contract(padding_needed_for)]
    fn proof() {
        padding_needed_for(kani::any(), kani::any());
    }

    // Abstractly, we want to compute:
    //   align - (len % align).
    // Handling the case where len%align is 0.
    // Because align is a power of two, len % align = len & (align-1).
    // Guaranteed not to underflow as align is nonzero.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = align.get() - 1;

    // To efficiently subtract this value from align, we can use the bitwise
    // complement.
    // Note that ((!len) & (align-1)) gives us a number that with (len &
    // (align-1)) sums to align-1. So subtracting 1 from x before taking the
    // complement subtracts `len` from `align`. Some quick inspection of
    // cases shows that this also handles the case where `len % align = 0`
    // correctly too: len-1 % align then equals align-1, so the complement mod
    // align will be 0, as desired.
    //
    // The following reasoning can be verified quickly by an SMT solver
    // supporting the theory of bitvectors:
    // ```smtlib
    // ; Naive implementation of padding
    // (define-fun padding1 (
    //     (len (_ BitVec 32))
    //     (align (_ BitVec 32))) (_ BitVec 32)
    //    (ite
    //      (= (_ bv0 32) (bvand len (bvsub align (_ bv1 32))))
    //      (_ bv0 32)
    //      (bvsub align (bvand len (bvsub align (_ bv1 32))))))
    //
    // ; The implementation below
    // (define-fun padding2 (
    //     (len (_ BitVec 32))
    //     (align (_ BitVec 32))) (_ BitVec 32)
    // (bvand (bvnot (bvsub len (_ bv1 32))) (bvsub align (_ bv1 32))))
    //
    // (define-fun is-power-of-two ((x (_ BitVec 32))) Bool
    //   (= (_ bv0 32) (bvand x (bvsub x (_ bv1 32)))))
    //
    // (declare-const len (_ BitVec 32))
    // (declare-const align (_ BitVec 32))
    // ; Search for a case where align is a power of two and padding2 disagrees
    // ; with padding1
    // (assert (and (is-power-of-two align)
    //              (not (= (padding1 len align) (padding2 len align)))))
    // (simplify (padding1 (_ bv300 32) (_ bv32 32))) ; 20
    // (simplify (padding2 (_ bv300 32) (_ bv32 32))) ; 20
    // (simplify (padding1 (_ bv322 32) (_ bv32 32))) ; 30
    // (simplify (padding2 (_ bv322 32) (_ bv32 32))) ; 30
    // (simplify (padding1 (_ bv8 32) (_ bv8 32)))    ; 0
    // (simplify (padding2 (_ bv8 32) (_ bv8 32)))    ; 0
    // (check-sat) ; unsat, also works for 64-bit bitvectors
    // ```
    !(len.wrapping_sub(1)) & mask
}

/// Rounds `n` down to the largest value `m` such that `m <= n` and `m % align
/// == 0`.
///
/// # Panics
///
/// May panic if `align` is not a power of two. Even if it doesn't panic in this
/// case, it will produce nonsense results.
#[inline(always)]
#[cfg_attr(
    kani,
    kani::requires(align.is_power_of_two()),
    kani::ensures(|&m| m <= n && m % align.get() == 0),
    // Guarantees that `m` is the *largest* value such that `m % align == 0`.
    kani::ensures(|&m| {
        // If this `checked_add` fails, then the next multiple would wrap
        // around, which trivially satisfies the "largest value" requirement.
        m.checked_add(align.get()).map(|next_mul| next_mul > n).unwrap_or(true)
    })
)]
pub(crate) const fn round_down_to_next_multiple_of_alignment(
    n: usize,
    align: NonZeroUsize,
) -> usize {
    #[cfg(kani)]
    #[kani::proof_for_contract(round_down_to_next_multiple_of_alignment)]
    fn proof() {
        round_down_to_next_multiple_of_alignment(kani::any(), kani::any());
    }

    let align = align.get();
    #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
    debug_assert!(align.is_power_of_two());

    // Subtraction can't underflow because `align.get() >= 1`.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = !(align - 1);
    n & mask
}

#[cfg_attr(not(zerocopy_inline_always), inline)]
#[cfg_attr(zerocopy_inline_always, inline(always))]
pub(crate) const fn max(a: NonZeroUsize, b: NonZeroUsize) -> NonZeroUsize {
    if a.get() < b.get() {
        b
    } else {
        a
    }
}

#[cfg_attr(not(zerocopy_inline_always), inline)]
#[cfg_attr(zerocopy_inline_always, inline(always))]
pub(crate) const fn min(a: NonZeroUsize, b: NonZeroUsize) -> NonZeroUsize {
    if a.get() > b.get() {
        b
    } else {
        a
    }
}

/// Copies `src` into the prefix of `dst`.
///
/// Callers must ensure that `src.len() <= dst.len()`.
#[inline(always)]
pub(crate) fn copy_prefix(src: &[u8], dst: &mut [u8]) {
    debug_assert!(src.len() <= dst.len());
    dst.iter_mut().zip(src.iter()).for_each(|(dst, src)| *dst = *src);
}

/// Unsafely transmutes the given `src` into a type `Dst`.
///
/// # Safety
///
/// The value `src` must be a valid instance of `Dst`.
#[inline(always)]
pub(crate) const unsafe fn transmute_unchecked<Src, Dst>(src: Src) -> Dst {
    static_assert!(Src, Dst => core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());

    #[repr(C)]
    union Transmute<Src, Dst> {
        src: ManuallyDrop<Src>,
        dst: ManuallyDrop<Dst>,
    }

    // SAFETY: Since `Transmute<Src, Dst>` is `#[repr(C)]`, its `src` and `dst`
    // fields both start at the same offset and the types of those fields are
    // transparent wrappers around `Src` and `Dst` [1]. Consequently,
    // initializing `Transmute` with with `src` and then reading out `dst` is
    // equivalent to transmuting from `Src` to `Dst` [2]. Transmuting from `src`
    // to `Dst` is valid because — by contract on the caller — `src` is a valid
    // instance of `Dst`.
    //
    // [1] Per https://doc.rust-lang.org/1.82.0/std/mem/struct.ManuallyDrop.html:
    //
    //     `ManuallyDrop<T>` is guaranteed to have the same layout and bit
    //     validity as `T`, and is subject to the same layout optimizations as
    //     `T`.
    //
    // [2] Per https://doc.rust-lang.org/1.82.0/reference/items/unions.html#reading-and-writing-union-fields:
    //
    //     Effectively, writing to and then reading from a union with the C
    //     representation is analogous to a transmute from the type used for
    //     writing to the type used for reading.
    unsafe { ManuallyDrop::into_inner(Transmute { src: ManuallyDrop::new(src) }.dst) }
}

/// # Safety
///
/// `Src` must have a greater or equal alignment to `Dst`.
pub(crate) unsafe fn transmute_ref<Src, Dst, R>(src: &Src) -> &Dst
where
    Src: ?Sized,
    Dst: SizeEq<Src>
        + TransmuteFromPtr<Src, Shared, Valid, Valid, <Dst as SizeEq<Src>>::CastFrom, R>
        + ?Sized,
{
    let dst = Ptr::from_ref(src).transmute();
    // SAFETY: The caller promises that `Src`'s alignment is at least as large
    // as `Dst`'s alignment.
    let dst = unsafe { dst.assume_alignment() };
    dst.as_ref()
}

/// # Safety
///
/// `Src` must have a greater or equal alignment to `Dst`.
pub(crate) unsafe fn transmute_mut<Src, Dst, R>(src: &mut Src) -> &mut Dst
where
    Src: ?Sized,
    Dst: SizeEq<Src>
        + TransmuteFromPtr<Src, Exclusive, Valid, Valid, <Dst as SizeEq<Src>>::CastFrom, R>
        + ?Sized,
{
    let dst = Ptr::from_mut(src).transmute();
    // SAFETY: The caller promises that `Src`'s alignment is at least as large
    // as `Dst`'s alignment.
    let dst = unsafe { dst.assume_alignment() };
    dst.as_mut()
}

/// Uses `allocate` to create a `Box<T>`.
///
/// # Errors
///
/// Returns an error on allocation failure. Allocation failure is guaranteed
/// never to cause a panic or an abort.
///
/// # Safety
///
/// `allocate` must be either `alloc::alloc::alloc` or
/// `alloc::alloc::alloc_zeroed`. Any `Box<T>` returned by this function must
/// have a bit-valid referent with metadata `meta`. Thus `T` must permit the
/// corresponding initial memory state: its zero-byte representation for a
/// zero-sized instance, uninitialized bytes from `alloc`, or initialized
/// all-zero bytes from `alloc_zeroed`.
#[must_use = "has no side effects (other than allocation)"]
#[cfg(feature = "alloc")]
#[inline]
pub(crate) unsafe fn new_box<T>(
    meta: T::PointerMetadata,
    allocate: unsafe fn(core::alloc::Layout) -> *mut u8,
) -> Result<alloc::boxed::Box<T>, AllocError>
where
    T: ?Sized + crate::KnownLayout,
{
    let align = T::LAYOUT.align.get();
    if !T::is_valid_metadata(meta) {
        return Err(AllocError);
    }
    let size = match T::size_for_metadata(meta) {
        Some(size) => size,
        // Thanks to the `!T::is_valid_metadata(meta)` check
        // above, this branch is unreachable. Fortunately, the
        // optimizer recognizes this, so replacing this branch
        // with `unreachable_unchecked` produces no codegen
        // improvements.
        None => return Err(AllocError),
    };
    let ptr = if size != 0 {
        // SAFETY:
        // - `align` is derived from a `NonZeroUsize` and is thus non-zero.
        // - `align` is a power of two because, by invariant on
        //   `KnownLayout::LAYOUT` `<T as KnownLayout>::LAYOUT` accurately
        //   reflects the layout of `T`.
        // - `size`, by invariant on `size_for_metadata` is well-aligned for
        //   `align` and, by the check on `T::is_valid_metadata(meta)`, is less
        //   than `isize::MAX`.
        let layout: Layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        // SAFETY: By contract on the caller, `allocate` is either
        // `alloc::alloc::alloc` or `alloc::alloc::alloc_zeroed`. The above
        // check ensures their shared safety precondition: that the supplied
        // layout is not zero-sized type [1].
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/std/alloc/trait.GlobalAlloc.html#tymethod.alloc:
        //
        //     This function is unsafe because undefined behavior can result if
        //     the caller does not ensure that layout has non-zero size.
        let ptr = unsafe { allocate(layout) };
        match NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => return Err(AllocError),
        }
    } else {
        // We use `transmute` instead of an `as` cast since Miri (with strict
        // provenance enabled) notices and complains that an `as` cast creates a
        // pointer with no provenance. Miri isn't smart enough to realize that
        // we're only executing this branch when we're constructing a zero-sized
        // `Box`, which doesn't require provenance.
        //
        // SAFETY: any initialized bit sequence is a bit-valid `*mut u8`. All
        // bits of a `usize` are initialized.
        //
        // `#[allow(unknown_lints)]` is for `integer_to_ptr_transmutes`
        #[allow(unknown_lints)]
        #[allow(clippy::useless_transmute, integer_to_ptr_transmutes)]
        let dangling = unsafe { mem::transmute::<usize, *mut u8>(align) };
        // SAFETY: `dangling` is constructed from `align`, which is derived from
        // a `NonZeroUsize`, which is guaranteed to be non-zero.
        //
        // `Box<[T]>` does not allocate when `T` is zero-sized or when `len` is
        // zero, but it does require a non-null dangling pointer for its
        // allocation.
        //
        // FIXME(https://github.com/rust-lang/rust/issues/95228): Use
        // `std::ptr::without_provenance` once it's stable. That may optimize
        // better. As written, Rust may assume that this consumes "exposed"
        // provenance, and thus Rust may have to assume that this may consume
        // provenance from any pointer whose provenance has been exposed.
        unsafe { NonNull::new_unchecked(dangling) }
    };

    let ptr = T::raw_from_ptr_len(ptr, meta);

    // FIXME(#429): Add a "SAFETY" comment and remove this `allow`. Make sure to
    // include a justification that `ptr.as_ptr()` is validly-aligned in the ZST
    // case (in which we manually construct a dangling pointer) and to justify
    // why `Box` is safe to drop (it's because `allocate` uses the system
    // allocator).
    #[allow(clippy::undocumented_unsafe_blocks)]
    Ok(unsafe { alloc::boxed::Box::from_raw(ptr.as_ptr()) })
}

#[cfg(kani)]
mod proofs {
    use core::{convert::TryFrom as _, num::Wrapping};

    use super::*;
    use crate::{
        pointer::{BecauseImmutable, BecauseInvariantsEq, BecauseMutationCompatible},
        proof_support::{assert_same_u8_elements, assert_same_usize, copy_snapshot},
    };

    // Configuration: The harnesses below use the common Kani CI configuration
    // documented in `agent_docs/validation.md`: the CI-pinned Kani release and
    // its bundled x86_64-unknown-linux-gnu compiler, the stable-compatible
    // feature bundle, `-Zfunction-contracts`, and one layout selected by
    // `--randomize-layout` per invocation.
    //
    // `copy_prefix` proof scope:
    //
    // Domain: Every source `[u8; 8]`, destination `[u8; 12]`, source length
    // from 0 through 8, and destination length from the source length through
    // 12. Both target slices and both safe-oracle slices are offset-zero
    // prefixes of those fixed backing arrays. The proof uses only those arrays
    // and fixed source and destination snapshots; it performs no dynamic
    // allocation and has no explicit proof loop. Its unwind bound is 13, one
    // more than the largest modeled slice, and applies to all target and oracle
    // loops Kani reaches, with unwinding assertions enabled.
    // Establishes: The copied prefix and every destination frame byte exactly
    // match a safe copy, and the entire source equals its pre-call snapshot.
    // Target mechanics: `copy_prefix` contains no unsafe operation. Safe
    // `slice::iter_mut` visits the destination elements mutably while
    // `slice::iter` visits the source elements by shared reference [26], `zip`
    // pairs them until either iterator ends [27], and `for_each` applies the
    // byte assignment to every pair [28].
    // The caller condition `src.len() <= dst.len()` therefore makes every
    // source element participate. This safe iterator path is the target, not
    // the expected-result oracle.
    // Oracle: Safe `slice::copy_from_slice`, whose Rust 1.93 contract copies
    // every element from an equal-length source [1], is applied to a separate
    // destination copy. Shared and mutable `RangeTo<usize>` indexing selects
    // the exact `..src_len` and `..dst_len` prefixes for the oracle and target
    // inputs [12]; the domain bounds exclude its documented panic cases. Both
    // paths trust that same Rust indexing contract, which this proof does not
    // itself establish. Before the call, ordinary `Copy` semantics for the
    // fixed `[u8; 8]` source [19] create a separate snapshot through the shared
    // `copy_snapshot`; comparing the source against it after the call
    // independently supplies the source-frame oracle.
    // Excludes: Inputs with `src.len() > dst.len()` (the debug assertion panics
    // and the iterator body otherwise copies only the shorter length), larger
    // fixed arrays, nonzero-offset or interior source and destination slices,
    // preservation of frame bytes preceding such a destination slice,
    // overlapping regions (which safe input references preclude), and aliasing
    // or provenance properties outside Kani's model. This is not a generic
    // contract proof.
    //
    // [1] Rust 1.93 specifies that `copy_from_slice` copies every element from
    // `src` into the equal-length receiver:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_from_slice
    //
    // Transmutation proof scope:
    //
    // Domain: The value-to-bytes and shared-reference harnesses each cover
    // every independently generated `u32`; the bytes-to-value harness covers
    // every independently generated `[u8; 4]`; and the mutable-reference
    // harness covers the full Cartesian product of every initial `u32` and
    // every independently generated replacement `u32`. The reference
    // harnesses view their respective source values as `Wrapping<u32>`. Each
    // proof uses only fixed-size stack values, uses no `kani::assume`, performs
    // no dynamic allocation, and has no explicit proof loop. The mutable
    // harness's unequal-value `kani::cover!` is a reachability diagnostic and
    // does not constrain that Cartesian domain. Primitive `u32` inequality
    // classifies only this diagnostic [32]; expected-value assertions use the
    // native-byte oracle instead. Every harness has unwind bound five, which
    // also bounds any target or oracle loop Kani reaches, with unwinding
    // assertions enabled.
    // Establishes: Independently seeded value-to-bytes and bytes-to-value
    // native representation contracts, modeled address preservation, and
    // mutation propagation. Neither value transmutation is used to construct
    // the other's input.
    // Oracle: Safe `u32::to_ne_bytes` and `u32::from_ne_bytes` directly map
    // between a value and its native-endian memory representation [2][3]; safe
    // an explicit numbered-field `Wrapping { 0: replacement }` struct
    // expression, its documented transparent layout, and Rust's tuple-field
    // projection rule supply the reference expectations [25]. The shared
    // `assert_same_u32_value` oracle applies `u32::to_ne_bytes` [2] to each
    // observed public field or scalar and compares the resulting ordered bytes
    // through `assert_same_u8_elements`; it therefore avoids relying on
    // `Wrapping<u32>::PartialEq` or an undocumented scalar equality. Rust's
    // listed reference-to-raw-pointer coercions supply pointers to the source
    // and returned referents [4]. The raw-pointer `cast` methods are documented
    // as casts to another pointer type [5], and the Reference says a sized-to-
    // sized pointer cast returns the pointer unchanged [6]. Raw-pointer
    // equality is documented as address equality [5], so those operations
    // provide an independent observer of the modeled addresses. Requiring the
    // two observed addresses to match is an explicit zerocopy same-address
    // policy oracle under test, not an independent Rust-language oracle: Rust
    // does not require this target to return a view at the source address.
    //
    // For mutation, dereferencing the local `dst: &mut Wrapping<u32>` denotes
    // its pointed-to location and makes that location assignable [7]. Ordinary
    // assignment then copies or moves the explicit
    // `Wrapping { 0: replacement }` value into that place [8]. These are safe
    // Rust language operations independent of `transmute_mut`: they define the
    // write through the returned reference. After that borrow ends,
    // `assert_same_u32_value(src, replacement)` checks whether the target
    // returned a view of the source storage. It does not derive the expected
    // mutation from `transmute_mut` itself.
    // TOOL/TCB boundary: Each harness reads, and the mutable harness writes,
    // through the reference returned by the unsafe target. Rust's reference
    // safety requirements include alignment, non-nullness, dereferenceability,
    // valid representation, and a referent that remains live for the reference
    // lifetime [33]. Kani does not completely check these properties [34]. The
    // observations can test values and modeled addresses only under that
    // premise; they cannot discharge it, because an invalid returned reference
    // could make the observing Rust execution itself invalid.
    // Excludes: Other source/destination types, invalid representations, and
    // returned-reference lifetime, dereferenceability, provenance, or aliasing
    // guarantees. In particular, the address operation used to define pointer
    // equality discards provenance [5]; equal raw pointer addresses therefore
    // do not establish equal provenance. These are not generic transmutation
    // contract proofs.
    //
    // [2] Rust 1.93 specifies that `to_ne_bytes` returns the integer's memory
    // representation as a native-byte-order array:
    // https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.to_ne_bytes
    //
    // [3] Rust 1.93 specifies that `from_ne_bytes` creates the native-endian
    // integer value from its memory-representation array:
    // https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes
    //
    // [4] Rust 1.93 lists the coercions “`&T` to `*const T`” and “`&mut T` to
    // `*mut T`”:
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#coercion-types
    //
    // [5] Rust 1.93 says `cast`: “Casts to a pointer of another type.” Raw
    // pointer `PartialEq` says: “Pointer equality is by address.” The `addr`
    // documentation says “the provenance of the pointer is discarded” by that
    // address operation:
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.cast
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.cast-1
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*const+T
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*mut+T
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.addr
    //
    // [6] For sized source and destination types, Rust 1.93 says “the pointer
    // is returned unchanged” by a pointer-to-pointer cast:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast
    //
    // [7] For a dereference, Rust 1.93 specifies:
    //
    //     When applied to a pointer it denotes the pointed-to location.
    //
    // It further specifies:
    //
    //     If the expression is of type `&mut T` or `*mut T`, and is either a
    //     local variable, a (nested) field of a local variable or is a mutable
    //     place expression, then the resulting memory location can be assigned
    //     to.
    //
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.result
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.mut
    //
    // [8] For assignment, Rust 1.93 specifies:
    //
    //     Next it either copies or moves the assigned value to the assigned
    //     place.
    //
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.assign.behavior
    //
    // Allocation proof scope:
    //
    // Domain: Three fixed calls: `new_box::<u32>((), alloc_zeroed)`,
    // `new_box::<[u8]>(4, alloc_zeroed)`, and `new_box::<()>((), alloc)`. The
    // first two select the nonzero-size branch; the unit call selects the
    // zero-size dangling-pointer branch. In the inspected source, each selected
    // nonzero-size path reaches the single call through `allocate`, while the
    // unit path bypasses it; the harnesses do not instrument allocator-call
    // counts. Kani 0.67's tagged C runtime states that Rust's `__rust_alloc`
    // and `__rust_alloc_zeroed` shims call `malloc` and `calloc` respectively
    // [29]. We manually inspected the exact linked GOTO programs emitted for
    // both nonzero-size harnesses after Function Pointer Removal: each indirect
    // `allocate` parameter resolves to `std::alloc::alloc_zeroed`, then
    // `__rust_alloc_zeroed`, then `calloc`; the unit harness's zero-size branch
    // bypasses `allocate`. Kani 0.67 invokes CBMC with
    // `--no-malloc-may-fail` [9], and the bundled CBMC 6.8.0's own `--help`
    // defines that flag as "disable potential malloc failure" [10]. Inspecting
    // CBMC's GOTO functions with that flag shows the built-in `calloc` model's
    // nondeterministic may-fail mode fixed to zero. For these two calls, the
    // asserted metadata policy supplies size four, so `calloc(1, 4)` also
    // avoids the model's separate multiplication-overflow and maximum-size
    // null returns. The link from the Rust calls through compiler/Kani lowering
    // and those flag/model semantics is an audited TOOL/TCB premise, not a
    // theorem of these harnesses. Under that premise, they do not model
    // allocation failure. A Kani, compiler, linker, or allocation-model change
    // requires repeating the call-graph and flag audit.
    //
    // The `u32` harness additionally quantifies over every replacement `u32`
    // used by its post-allocation safe write/read check. Its equal-to and
    // distinct-from the independently constructed initial-zero expectation
    // covers witness the no-op and value-changing partitions; they are
    // reachability diagnostics and do not constrain the every-`u32` domain.
    // Primitive `u32` equality and inequality classify only those diagnostics
    // [32]. Call metadata, allocated type and length, and the other oracle
    // shapes are fixed. The first two target calls exercise Kani's allocation
    // and normal deallocation models. There is no explicit proof loop. Each
    // harness sets the loop-unwinding bound to five; common CI retains
    // unwinding assertions for every translated reachable loop. This is not
    // Rust panic-unwind coverage.
    // Establishes: Under the metadata-policy and no-allocation-failure premises
    // below, all three fixed calls return `Ok`. Every harness unconditionally
    // asserts `result.is_ok()` before unwrapping. Rust specifies that `is_ok`
    // is true for `Ok`, while `unwrap` returns an `Ok` value and panics for
    // `Err` [11]. Thus an unexpected metadata, size, or allocation `Err` fails
    // that assertion instead of silently skipping the content checks. On the
    // proved `Ok` path, `unwrap` supplies the value they inspect. The `u32`
    // call returns zeroed storage and, for every replacement `u32`, a safe
    // `Box` write is read back exactly. The `[u8]` call returns four zero bytes
    // with length four; the unit call returns a zero-sized referent.
    // Metadata-policy oracle: before each target call,
    // `assert_new_box_metadata_policy` receives a byte size computed by Rust's
    // `size_of` or `size_of_val` operations [18][20]. For `[u8]`, the
    // `size_of_val` input is a safely constructed four-element slice rather
    // than a manual reconstruction of slice layout. The helper checks that the
    // independent size is representable as `isize` using safe `TryFrom` [23],
    // then checks the `KnownLayout::is_valid_metadata` and `size_for_metadata`
    // results used by `new_box`. `Option::is_some` and `unwrap` [31] make a
    // missing size fail before the contained `usize` is compared through the
    // equality chain in [30]. The `KnownLayout` contracts require acceptance
    // and that exact size for these fixed `u32`, `[u8]`, and unit inputs.
    // Because these checks consume zerocopy's own `KnownLayout` contract, they
    // are explicitly policy premises, not independent evidence that its
    // implementations are correct.
    // They do establish, before the target call, that neither metadata check is
    // an expected source of `Err`.
    //
    // Value oracle: Rust's repeat-array expression constructs the expected
    // fixed arrays with the stated number of copies of zero [24]. Primitive
    // `u32::from_ne_bytes` [3] independently maps four such bytes to the
    // expected integer value. The shared `assert_same_u8_elements` [13]-[17],
    // [30] supplies the expected slice length and ordered zero bytes, and
    // `size_of_val` [18] observes the unit referent's size. The direct unit-size
    // assertion also uses the documented `assert_eq!`/`usize::PartialEq`
    // equality chain [30].
    //
    // Box observation oracle: `Box<T>` implements `Deref<Target = T>` and
    // `DerefMut` [21]. Rust's dereference and assignment rules [7][8] specify
    // the `*boxed` reads and write, while dereference coercion [22] supplies
    // the `&Box<[u8]>` to `&[u8]` observation. These safe operations are
    // independent of `new_box` and specify observations of a valid returned
    // box. They cannot establish that `new_box` constructed a valid `Box`: if
    // its raw-pointer, allocation, or referent obligations were already
    // violated, these observations could themselves be outside Rust's valid
    // execution model.
    // Excludes: Configurations which permit modeled allocation failure, real
    // resource exhaustion, and validation of the expected allocation-failure
    // `Err` path. The required `Ok` result is conditional on the manually
    // audited Rust-to-Kani-to-CBMC allocation bridge and Kani 0.67's CBMC model,
    // not a claim that production allocation cannot fail. The harnesses do not
    // prove that bridge, Kani's allocation shims, or the CBMC flag semantics.
    // Also excluded are uninitialized non-ZST referents, arbitrary
    // types/metadata, and nested slice DSTs (see
    // https://github.com/google/zerocopy/pull/3630). In particular, these are
    // behavioral smoke regressions, not proofs of the `Box::from_raw`
    // provenance, alignment, ownership, or allocator/deallocator obligations
    // called out by FIXME #429 above, nor of `new_box`'s overall soundness.
    //
    // [9] https://github.com/model-checking/kani/blob/kani-0.67.0/kani-driver/src/call_cbmc.rs#L213-L219
    //
    // [10] `agent_docs/validation.md` records the exact bundled CBMC version and
    // its inspected `--no-malloc-may-fail` / `--malloc-may-fail` help text.
    //
    // [11] Rust 1.93's `Result` contracts state:
    //
    //     Returns `true` if the result is `Ok`.
    //
    //     Returns the contained `Ok` value, consuming the `self` value.
    //
    //     Panics if the value is an `Err`, with a panic message provided by the
    //     `Err`’s value.
    //
    // https://doc.rust-lang.org/1.93.0/std/result/enum.Result.html#method.is_ok
    // https://doc.rust-lang.org/1.93.0/std/result/enum.Result.html#method.unwrap

    // Shared observation oracle: `assert_same_u8_elements` obtains both element
    // counts through `slice::len` [13]; `assert_eq!` compares those counts using
    // `usize::PartialEq` [30]. Safe `slice::iter` then yields every item in
    // order [14], `Iterator::copied` copies those items, and `Iterator::eq`
    // compares the two sequences [15] using primitive `u8` equality [16].
    // Fixed arrays reach this helper through the Reference's array-to-slice
    // unsizing coercion [17]. These operations are independent of the zerocopy
    // target, but not of the compiler, standard library, or Kani model. They
    // observe element counts and ordered values, not storage identity or
    // provenance.
    //
    // [12] Rust 1.93 defines `RangeTo` as including values below `end`, and its
    // `SliceIndex<[T]>` implementation returns that prefix for shared and
    // mutable indexing, panicking when `end` is out of bounds:
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.RangeTo.html
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.RangeTo.html#impl-SliceIndex%3C%5BT%5D%3E-for-RangeTo%3Cusize%3E
    //
    // [13] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // [14] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    // [15] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
    // and https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
    // [16] https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
    // [17] Rust 1.93 permits references to unsize at a coercion site and lists
    // `[T; n]` to `[T]` as an unsized coercion:
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.types.unsize
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.unsize.slice
    //
    // Rust 1.93 specifies that `size_of_val` returns the size of the pointed-to
    // value in bytes [18]. The unit allocation harness uses this only to
    // observe the target referent's dynamic size.
    //
    // [18] https://doc.rust-lang.org/1.93.0/core/mem/fn.size_of_val.html

    // [19] Rust 1.93 implements `Copy` for `[T; N]` when `T: Copy`, and for
    // `u8`, establishing that the complete `[u8; 8]` place is copied by value:
    // https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-Copy-for-%5BT;+N%5D
    // https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-Copy-for-u8
    //
    // [20] Rust 1.93 specifies that `size_of` returns a type's size in bytes:
    // https://doc.rust-lang.org/1.93.0/core/mem/fn.size_of.html
    //
    // [21] Rust 1.93's `Box` implementations dereference to `T` and permit
    // mutable dereference:
    // https://doc.rust-lang.org/1.93.0/alloc/boxed/struct.Box.html#impl-Deref-for-Box%3CT,+A%3E
    // https://doc.rust-lang.org/1.93.0/alloc/boxed/struct.Box.html#impl-DerefMut-for-Box%3CT,+A%3E
    //
    // [22] Rust 1.93 permits `&T` to coerce to `&U` when
    // `T: Deref<Target = U>`:
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.types.deref
    //
    // [23] Rust 1.93's `TryFrom<usize> for isize` performs the checked integer
    // conversion used by the metadata policy precheck:
    // https://doc.rust-lang.org/1.93.0/std/primitive.isize.html#impl-TryFrom%3Cusize%3E-for-isize

    // [24] Rust 1.93 specifies: “`[a; b]` creates an array containing `b`
    // copies of the value of `a`”:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/array-expr.html#array-expressions

    // [25] Rust 1.93 specifies explicit struct expressions, including numeric
    // fields for tuple structs, and that tuple and tuple-struct fields are
    // accessed with the number corresponding to the field's position:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/struct-expr.html#r-expr.struct.intro
    // https://doc.rust-lang.org/1.93.0/reference/expressions/struct-expr.html#r-expr.struct.tuple-field
    // https://doc.rust-lang.org/1.93.0/reference/expressions/tuple-expr.html#tuple-indexing-expressions

    // [26] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter_mut
    // [27] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.zip
    // [28] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.for_each

    // [29] Kani 0.67's tagged runtime implements `__rust_alloc` using `malloc`
    // and `__rust_alloc_zeroed` using `calloc`:
    // https://github.com/model-checking/kani/blob/kani-0.67.0/library/kani/kani_lib.c#L31-L67

    // [30] Rust 1.93 specifies that `slice::len` returns the number of elements,
    // `assert_eq!` compares operands using `PartialEq`, and `usize` equality
    // tests its two values for equality:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize

    // [31] Rust 1.93 specifies that `Option::is_some` is true for `Some` and
    // `Option::unwrap` returns the contained `Some` value or panics for `None`:
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.is_some
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.unwrap

    // [32] Rust 1.93 specifies `PartialEq::eq` and `PartialEq::ne`, and provides
    // that implementation for `u32`:
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#method.ne
    // https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#impl-PartialEq-for-u32

    // [33] Rust 1.93 lists the safety requirements for references:
    // https://doc.rust-lang.org/1.93.0/std/primitive.reference.html#safety

    // [34] Kani documents the undefined-behavior checks it does and does not
    // support; `agent_docs/validation.md` records the exact pinned-tool audit:
    // https://model-checking.github.io/kani/undefined-behaviour.html

    fn assert_same_u32_value(actual: u32, expected: u32) {
        assert_same_u8_elements(&actual.to_ne_bytes(), &expected.to_ne_bytes());
    }

    #[cfg(feature = "alloc")]
    fn assert_new_box_metadata_policy<T>(meta: T::PointerMetadata, expected_size: usize)
    where
        T: ?Sized + KnownLayout,
    {
        assert!(isize::try_from(expected_size).is_ok());
        assert!(T::is_valid_metadata(meta));
        let actual_size = T::size_for_metadata(meta);
        assert!(actual_size.is_some());
        assert_same_usize(actual_size.unwrap(), expected_size);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn prove_copy_prefix_copies_prefix_and_preserves_frame() {
        const SRC_CAPACITY: usize = 8;
        const DST_CAPACITY: usize = 12;

        let src: [u8; SRC_CAPACITY] = kani::any();
        let original_src = copy_snapshot(&src);
        let mut dst: [u8; DST_CAPACITY] = kani::any();
        let src_len: usize = kani::any();
        let dst_len: usize = kani::any();

        kani::assume(src_len <= SRC_CAPACITY);
        kani::assume(dst_len <= DST_CAPACITY);
        kani::assume(src_len <= dst_len);

        kani::cover!(src_len == 0 && dst_len == 0);
        kani::cover!(src_len == SRC_CAPACITY && src_len == dst_len);
        kani::cover!(0 < src_len && src_len < dst_len && dst_len < DST_CAPACITY);
        kani::cover!(src_len > 0 && src[0] != dst[0]);

        let mut expected_dst = copy_snapshot(&dst);
        expected_dst[..src_len].copy_from_slice(&original_src[..src_len]);

        copy_prefix(&src[..src_len], &mut dst[..dst_len]);

        assert_same_u8_elements(&src, &original_src);
        assert_same_u8_elements(&dst, &expected_dst);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_transmute_unchecked_u32_to_bytes() {
        let src: u32 = kani::any();

        // SAFETY: `transmute_unchecked` statically checks that `[u8; 4]` and
        // `u32` have the same size. `src` is initialized, and numeric bit
        // validity is exactly that of an initialized byte array [1], so its
        // representation is valid for `[u8; 4]`.
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/reference/types/numeric.html#bit-validity:
        //
        //     For every numeric type, `T`, the bit validity of `T` is
        //     equivalent to the bit validity of `[u8; size_of::<T>()]`. An
        //     uninitialized byte is not a valid `u8`.
        let bytes: [u8; 4] = unsafe { transmute_unchecked(src) };
        assert_same_u8_elements(&bytes, &src.to_ne_bytes());
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_transmute_unchecked_bytes_to_u32() {
        // This consumer receives a fresh arbitrary representation, not the
        // output of the opposite target transmutation.
        let bytes: [u8; 4] = kani::any();

        // SAFETY: `transmute_unchecked` statically checks that `[u8; 4]` and
        // `u32` have the same size. Every byte in `bytes` is initialized, and
        // numeric bit validity is exactly that of an initialized byte array
        // [1], so its representation is valid for `u32`.
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/reference/types/numeric.html#bit-validity:
        //
        //     For every numeric type, `T`, the bit validity of `T` is
        //     equivalent to the bit validity of `[u8; size_of::<T>()]`. An
        //     uninitialized byte is not a valid `u8`.
        let roundtrip: u32 = unsafe { transmute_unchecked(bytes) };
        assert_same_u32_value(roundtrip, u32::from_ne_bytes(bytes));
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_transmute_ref_preserves_address_and_value() {
        let src: u32 = kani::any();
        let src_ptr: *const u32 = &src;

        // SAFETY: A type's layout includes its alignment [1], and
        // `Wrapping<u32>` has the same layout as `u32` [2]. Their alignments
        // are therefore equal, satisfying `transmute_ref`'s sole caller
        // precondition.
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html:
        //
        //     The layout of a type is its size, alignment, and the relative
        //     offsets of its fields.
        //
        // [2] Per https://doc.rust-lang.org/1.93.0/std/num/struct.Wrapping.html#layout-1:
        //
        //     `Wrapping<T>` is guaranteed to have the same layout and ABI as
        //     `T`.
        let dst: &Wrapping<u32> = unsafe { transmute_ref::<_, _, BecauseImmutable>(&src) };
        let dst_ptr: *const Wrapping<u32> = dst;

        assert_eq!(src_ptr.cast::<u8>(), dst_ptr.cast::<u8>());
        assert_same_u32_value(dst.0, src);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_transmute_mut_preserves_address_and_mutates_source() {
        let mut src: u32 = kani::any();
        let original = copy_snapshot(&src);
        let replacement: u32 = kani::any();
        let src_ptr: *mut u32 = &mut src;

        {
            // SAFETY: A type's layout includes its alignment [1], and
            // `Wrapping<u32>` has the same layout as `u32` [2]. Their
            // alignments are therefore equal, satisfying `transmute_mut`'s
            // sole caller precondition.
            //
            // [1] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html:
            //
            //     The layout of a type is its size, alignment, and the
            //     relative offsets of its fields.
            //
            // [2] Per https://doc.rust-lang.org/1.93.0/std/num/struct.Wrapping.html#layout-1:
            //
            //     `Wrapping<T>` is guaranteed to have the same layout and ABI
            //     as `T`.
            let dst: &mut Wrapping<u32> = unsafe {
                transmute_mut::<_, _, (BecauseMutationCompatible, BecauseInvariantsEq)>(&mut src)
            };
            let dst_ptr: *mut Wrapping<u32> = dst;

            assert_eq!(src_ptr.cast::<u8>(), dst_ptr.cast::<u8>());
            assert_same_u32_value(dst.0, original);
            *dst = Wrapping { 0: replacement };
            assert_same_u32_value(dst.0, replacement);
        }

        kani::cover!(replacement != original);
        assert_same_u32_value(src, replacement);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zeroed_u32() {
        let meta = ();
        assert_new_box_metadata_policy::<u32>(meta, mem::size_of::<u32>());

        // SAFETY: This passes `alloc_zeroed` directly, one of the two allocator
        // functions permitted by `new_box`. It returns initialized zeroed
        // memory [1], and every initialized representation is valid for a
        // numeric type such as `u32` [2].
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/std/alloc/fn.alloc_zeroed.html:
        //
        //     Allocates zero-initialized memory with the global allocator.
        //
        // [2] Per https://doc.rust-lang.org/1.93.0/reference/types/numeric.html#bit-validity:
        //
        //     For every numeric type, `T`, the bit validity of `T` is
        //     equivalent to the bit validity of `[u8; size_of::<T>()]`. An
        //     uninitialized byte is not a valid `u8`.
        //
        // [3] Per https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes:
        //
        //     Creates a native endian integer value from its memory
        //     representation as a byte array in native endianness.
        let result = unsafe { new_box::<u32>(meta, alloc::alloc::alloc_zeroed) };
        assert!(result.is_ok());

        let mut boxed = result.unwrap();
        let expected = u32::from_ne_bytes([0; mem::size_of::<u32>()]);
        assert_same_u32_value(*boxed, expected);

        let replacement: u32 = kani::any();
        kani::cover!(replacement == expected);
        kani::cover!(replacement != expected);
        *boxed = replacement;
        assert_same_u32_value(*boxed, replacement);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zst() {
        let meta = ();
        assert_new_box_metadata_policy::<()>(meta, mem::size_of::<()>());

        // SAFETY: This passes `alloc` directly, one of the two allocator
        // functions permitted by `new_box`. The unit type has exactly one
        // value [1] and occupies no bytes [2], so the resulting referent must
        // be that valid value regardless of the allocator's byte contents.
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/reference/types/tuple.html#unit:
        //
        //     Its one value is also called unit or the unit value.
        //
        // [2] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#tuple-layout:
        //
        //     The exception to this is the unit tuple (`()`), which is
        //     guaranteed as a zero-sized type to have a size of 0 and an
        //     alignment of 1.
        //
        // The family-level `size_of_val` oracle [18] observes that size through
        // the returned `Box`.
        let result = unsafe { new_box::<()>(meta, alloc::alloc::alloc) };
        assert!(result.is_ok());

        let boxed = result.unwrap();
        assert_same_usize(mem::size_of_val(&*boxed), 0);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zeroed_byte_slice() {
        const LEN: usize = 4;

        let meta = LEN;
        let expected = [0u8; LEN];
        // The explicit type invokes the documented array-to-slice coercion
        // [17], avoiding `RangeFull` indexing as an unlisted oracle step.
        let expected_slice: &[u8] = &expected;
        let expected_size = mem::size_of_val(expected_slice);
        assert_new_box_metadata_policy::<[u8]>(meta, expected_size);

        // SAFETY: This passes `alloc_zeroed` directly, one of the two allocator
        // functions permitted by `new_box`. It returns initialized zeroed
        // memory [1]. Numeric bit validity is exactly the validity of an
        // initialized byte array [2], so every element is a valid `u8`; slices
        // have the layout of their array section [3].
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/std/alloc/fn.alloc_zeroed.html:
        //
        //     Allocates zero-initialized memory with the global allocator.
        //
        // [2] Per https://doc.rust-lang.org/1.93.0/reference/types/numeric.html#bit-validity:
        //
        //     For every numeric type, `T`, the bit validity of `T` is
        //     equivalent to the bit validity of `[u8; size_of::<T>()]`. An
        //     uninitialized byte is not a valid `u8`.
        //
        // [3] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#slice-layout:
        //
        //     Slices have the same layout as the section of the array they
        //     slice.
        let result = unsafe { new_box::<[u8]>(meta, alloc::alloc::alloc_zeroed) };
        assert!(result.is_ok());

        let boxed = result.unwrap();
        assert_same_u8_elements(&boxed, &expected);
    }
}

mod len_of {
    use super::*;

    /// A witness type for metadata of a valid instance of `&T`.
    pub struct MetadataOf<T: ?Sized + KnownLayout> {
        /// # Safety
        ///
        /// The size of an instance of `&T` with the given metadata is not
        /// larger than `isize::MAX`.
        meta: T::PointerMetadata,
        _p: PhantomData<T>,
    }

    impl<T: ?Sized + KnownLayout> Copy for MetadataOf<T> {}
    impl<T: ?Sized + KnownLayout> Clone for MetadataOf<T> {
        #[inline]
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T: ?Sized + KnownLayout> core::fmt::Debug for MetadataOf<T>
    where
        T::PointerMetadata: core::fmt::Debug,
    {
        #[inline]
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("MetadataOf").field("meta", &self.meta).finish()
        }
    }

    impl<T: ?Sized> MetadataOf<T>
    where
        T: KnownLayout,
    {
        /// Returns `None` if `meta` is greater than `t`'s metadata.
        #[inline(always)]
        pub(crate) fn new_in_bounds(t: &T, meta: usize) -> Option<Self>
        where
            T: KnownLayout<PointerMetadata = usize>,
        {
            if meta <= Ptr::from_ref(t).len() {
                // SAFETY: We have checked that `meta` is not greater than `t`'s
                // metadata, which, by invariant on `&T`, addresses no more than
                // `isize::MAX` bytes [1][2].
                //
                // [1] Per https://doc.rust-lang.org/1.85.0/std/primitive.reference.html#safety:
                //
                //    For all types, `T: ?Sized`, and for all `t: &T` or `t:
                //    &mut T`, when such values cross an API boundary, the
                //    following invariants must generally be upheld:
                //
                //    * `t` is non-null
                //    * `t` is aligned to `align_of_val(t)`
                //    * if `size_of_val(t) > 0`, then `t` is dereferenceable for
                //      `size_of_val(t)` many bytes
                //
                //    If `t` points at address `a`, being "dereferenceable" for
                //    N bytes means that the memory range `[a, a + N)` is all
                //    contained within a single allocated object.
                //
                // [2] Per https://doc.rust-lang.org/1.85.0/std/ptr/index.html#allocated-object:
                //
                //    For any allocated object with `base` address, `size`, and
                //    a set of `addresses`, the following are guaranteed:
                //    - For all addresses `a` in `addresses`, `a` is in the
                //      range `base .. (base + size)` (note that this requires
                //      `a < base + size`, not `a <= base + size`)
                //    - `base` is not equal to [`null()`] (i.e., the address
                //      with the numerical value 0)
                //    - `base + size <= usize::MAX`
                //    - `size <= isize::MAX`
                Some(unsafe { Self::new_unchecked(meta) })
            } else {
                None
            }
        }

        /// # Safety
        ///
        /// The size of an instance of `&T` with the given metadata is not
        /// larger than `isize::MAX`.
        pub(crate) unsafe fn new_unchecked(meta: T::PointerMetadata) -> Self {
            // SAFETY: The caller has promised that the size of an instance of
            // `&T` with the given metadata is not larger than `isize::MAX`.
            Self { meta, _p: PhantomData }
        }

        pub(crate) fn get(&self) -> T::PointerMetadata
        where
            T::PointerMetadata: Copy,
        {
            self.meta
        }

        #[inline]
        pub(crate) fn padding_needed_for(&self) -> usize
        where
            T: KnownLayout<PointerMetadata = usize>,
        {
            let trailing_slice_layout = crate::trailing_slice_layout::<T>();

            // FIXME(#67): Remove this allow. See NumExt for more details.
            #[allow(
                unstable_name_collisions,
                clippy::incompatible_msrv,
                clippy::multiple_unsafe_ops_per_block
            )]
            // SAFETY: By invariant on `self`, a `&T` with metadata `self.meta`
            // describes an object of size `<= isize::MAX`. This computes the
            // size of such a `&T` without any trailing padding, and so neither
            // the multiplication nor the addition will overflow.
            let unpadded_size = unsafe {
                let trailing_size = self.meta.unchecked_mul(trailing_slice_layout.elem_size);
                trailing_size.unchecked_add(trailing_slice_layout.offset)
            };

            util::padding_needed_for(unpadded_size, T::LAYOUT.align)
        }

        #[inline(always)]
        pub(crate) fn validate_cast_and_convert_metadata(
            addr: usize,
            bytes_len: MetadataOf<[u8]>,
            cast_type: CastType,
            meta: Option<T::PointerMetadata>,
        ) -> Result<(MetadataOf<T>, MetadataOf<[u8]>), MetadataCastError> {
            let layout = match meta {
                None => T::LAYOUT,
                // This can return `Err(MetadataCastError::Size)` if the
                // metadata describes an object which can't fit in an `isize`.
                Some(meta) => {
                    if !T::is_valid_metadata(meta) {
                        return Err(MetadataCastError::Size);
                    }
                    let size = match T::size_for_metadata(meta) {
                        Some(size) => size,
                        // Thanks to the `!T::is_valid_metadata(meta)` check
                        // above, this branch is unreachable. Fortunately, the
                        // optimizer recognizes this, so replacing this branch
                        // with `unreachable_unchecked` produces no codegen
                        // improvements.
                        None => return Err(MetadataCastError::Size),
                    };
                    DstLayout {
                        align: T::LAYOUT.align,
                        size_info: crate::SizeInfo::Sized { size },
                        statically_shallow_unpadded: false,
                    }
                }
            };
            // Lemma 0: By contract on `validate_cast_and_convert_metadata`, if
            // the result is `Ok(..)`, then a `&T` with `elems` trailing slice
            // elements is no larger in size than `bytes_len.get()`.
            let (elems, split_at) =
                layout.validate_cast_and_convert_metadata(addr, bytes_len.get(), cast_type)?;
            let elems = T::PointerMetadata::from_elem_count(elems);

            // For a slice DST type, if `meta` is `Some(elems)`, then we
            // synthesize `layout` to describe a sized type whose size is equal
            // to the size of the instance that we are asked to cast. For sized
            // types, `validate_cast_and_convert_metadata` returns `elems == 0`.
            // Thus, in this case, we need to use the `elems` passed by the
            // caller, not the one returned by
            // `validate_cast_and_convert_metadata`.
            //
            // Lemma 1: A `&T` with `elems` trailing slice elements is no larger
            // in size than `bytes_len.get()`. Proof:
            // - If `meta` is `None`, then `elems` satisfies this condition by
            //   Lemma 0.
            // - If `meta` is `Some(meta)`, then `layout` describes an object
            //   whose size is equal to the size of an `&T` with `meta`
            //   metadata. By Lemma 0, that size is not larger than
            //   `bytes_len.get()`.
            //
            // Lemma 2: A `&T` with `elems` trailing slice elements is no larger
            // than `isize::MAX` bytes. Proof: By Lemma 1, a `&T` with metadata
            // `elems` is not larger in size than `bytes_len.get()`. By
            // invariant on `MetadataOf<[u8]>`, a `&[u8]` with metadata
            // `bytes_len` is not larger than `isize::MAX`. Because
            // `size_of::<u8>()` is `1`, a `&[u8]` with metadata `bytes_len` has
            // size `bytes_len.get()` bytes. Therefore, a `&T` with metadata
            // `elems` has size not larger than `isize::MAX`.
            let elems = meta.unwrap_or(elems);

            // SAFETY: See Lemma 2.
            let elems = unsafe { MetadataOf::new_unchecked(elems) };

            // SAFETY: Let `size` be the size of a `&T` with metadata `elems`.
            // By post-condition on `validate_cast_and_convert_metadata`, one of
            // the following conditions holds:
            // - `split_at == size`, in which case, by Lemma 2, `split_at <=
            //   isize::MAX`. Since `size_of::<u8>() == 1`, a `[u8]` with
            //   `split_at` elems has size not larger than `isize::MAX`.
            // - `split_at == bytes_len - size`. Since `bytes_len:
            //   MetadataOf<u8>`, and since `size` is non-negative, `split_at`
            //   addresses no more bytes than `bytes_len` does. Since
            //   `bytes_len: MetadataOf<u8>`, `bytes_len` describes a `[u8]`
            //   which has no more than `isize::MAX` bytes, and thus so does
            //   `split_at`.
            let split_at = unsafe { MetadataOf::<[u8]>::new_unchecked(split_at) };
            Ok((elems, split_at))
        }
    }
}

pub use len_of::MetadataOf;

/// Since we support multiple versions of Rust, there are often features which
/// have been stabilized in the most recent stable release which do not yet
/// exist (stably) on our MSRV. This module provides polyfills for those
/// features so that we can write more "modern" code, and just remove the
/// polyfill once our MSRV supports the corresponding feature. Without this,
/// we'd have to write worse/more verbose code and leave FIXME comments
/// sprinkled throughout the codebase to update to the new pattern once it's
/// stabilized.
///
/// Each trait is imported as `_` at the crate root; each polyfill should "just
/// work" at usage sites.
pub(crate) mod polyfills {
    use core::ptr::{self, NonNull};

    // A polyfill for `NonNull::slice_from_raw_parts` that we can use before our
    // MSRV is 1.70, when that function was stabilized.
    //
    // The `#[allow(unused)]` is necessary because, on sufficiently recent
    // toolchain versions, `ptr.slice_from_raw_parts()` resolves to the inherent
    // method rather than to this trait, and so this trait is considered unused.
    //
    // FIXME(#67): Once our MSRV is 1.70, remove this.
    #[allow(unused)]
    pub(crate) trait NonNullExt<T> {
        fn slice_from_raw_parts(data: Self, len: usize) -> NonNull<[T]>;
    }

    impl<T> NonNullExt<T> for NonNull<T> {
        // NOTE on coverage: this will never be tested in nightly since it's a
        // polyfill for a feature which has been stabilized on our nightly
        // toolchain.
        #[cfg_attr(
            all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS),
            coverage(off)
        )]
        #[inline(always)]
        fn slice_from_raw_parts(data: Self, len: usize) -> NonNull<[T]> {
            let ptr = ptr::slice_from_raw_parts_mut(data.as_ptr(), len);
            // SAFETY: `ptr` is converted from `data`, which is non-null.
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    // A polyfill for `Self::unchecked_sub` that we can use until methods like
    // `usize::unchecked_sub` is stabilized.
    //
    // The `#[allow(unused)]` is necessary because, on sufficiently recent
    // toolchain versions, `ptr.slice_from_raw_parts()` resolves to the inherent
    // method rather than to this trait, and so this trait is considered unused.
    //
    // FIXME(#67): Once our MSRV is high enough, remove this.
    #[allow(unused)]
    pub(crate) trait NumExt {
        /// Add without checking for overflow.
        ///
        /// # Safety
        ///
        /// The caller promises that the addition will not overflow.
        unsafe fn unchecked_add(self, rhs: Self) -> Self;

        /// Subtract without checking for underflow.
        ///
        /// # Safety
        ///
        /// The caller promises that the subtraction will not underflow.
        unsafe fn unchecked_sub(self, rhs: Self) -> Self;

        /// Multiply without checking for overflow.
        ///
        /// # Safety
        ///
        /// The caller promises that the multiplication will not overflow.
        unsafe fn unchecked_mul(self, rhs: Self) -> Self;
    }

    // NOTE on coverage: these will never be tested in nightly since they're
    // polyfills for a feature which has been stabilized on our nightly
    // toolchain.
    impl NumExt for usize {
        #[cfg_attr(
            all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS),
            coverage(off)
        )]
        #[inline(always)]
        unsafe fn unchecked_add(self, rhs: usize) -> usize {
            match self.checked_add(rhs) {
                Some(x) => x,
                None => {
                    // SAFETY: The caller promises that the addition will not
                    // underflow.
                    unsafe { core::hint::unreachable_unchecked() }
                }
            }
        }

        #[cfg_attr(
            all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS),
            coverage(off)
        )]
        #[inline(always)]
        unsafe fn unchecked_sub(self, rhs: usize) -> usize {
            match self.checked_sub(rhs) {
                Some(x) => x,
                None => {
                    // SAFETY: The caller promises that the subtraction will not
                    // underflow.
                    unsafe { core::hint::unreachable_unchecked() }
                }
            }
        }

        #[cfg_attr(
            all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS),
            coverage(off)
        )]
        #[inline(always)]
        unsafe fn unchecked_mul(self, rhs: usize) -> usize {
            match self.checked_mul(rhs) {
                Some(x) => x,
                None => {
                    // SAFETY: The caller promises that the multiplication will
                    // not overflow.
                    unsafe { core::hint::unreachable_unchecked() }
                }
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod testutil {
    use crate::*;

    /// A `T` which is aligned to at least `align_of::<A>()`.
    #[derive(Default)]
    pub(crate) struct Align<T, A> {
        pub(crate) t: T,
        _a: [A; 0],
    }

    impl<T: Default, A> Align<T, A> {
        pub(crate) fn set_default(&mut self) {
            self.t = T::default();
        }
    }

    impl<T, A> Align<T, A> {
        pub(crate) const fn new(t: T) -> Align<T, A> {
            Align { t, _a: [] }
        }
    }

    /// A `T` which is guaranteed not to satisfy `align_of::<A>()`.
    ///
    /// It must be the case that `align_of::<T>() < align_of::<A>()` in order
    /// for this type to work properly.
    #[repr(C)]
    pub(crate) struct ForceUnalign<T: Unaligned, A> {
        // The outer struct is aligned to `A`, and, thanks to `repr(C)`, `t` is
        // placed at the minimum offset that guarantees its alignment. If
        // `align_of::<T>() < align_of::<A>()`, then that offset will be
        // guaranteed *not* to satisfy `align_of::<A>()`.
        //
        // Note that we need `T: Unaligned` in order to guarantee that there is
        // no padding between `_u` and `t`.
        _u: u8,
        pub(crate) t: T,
        _a: [A; 0],
    }

    impl<T: Unaligned, A> ForceUnalign<T, A> {
        pub(crate) fn new(t: T) -> ForceUnalign<T, A> {
            ForceUnalign { _u: 0, t, _a: [] }
        }
    }
    // A `u64` with alignment 8.
    //
    // Though `u64` has alignment 8 on some platforms, it's not guaranteed. By
    // contrast, `AU64` is guaranteed to have alignment 8 on all platforms.
    #[derive(
        KnownLayout,
        Immutable,
        FromBytes,
        IntoBytes,
        Eq,
        PartialEq,
        Ord,
        PartialOrd,
        Default,
        Debug,
        Copy,
        Clone,
    )]
    #[repr(C, align(8))]
    pub(crate) struct AU64(pub(crate) u64);

    impl AU64 {
        // Converts this `AU64` to bytes using this platform's endianness.
        pub(crate) fn to_bytes(self) -> [u8; 8] {
            crate::transmute!(self)
        }
    }

    impl Display for AU64 {
        #[cfg_attr(
            all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS),
            coverage(off)
        )]
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_down_to_next_multiple_of_alignment() {
        fn alt_impl(n: usize, align: NonZeroUsize) -> usize {
            let mul = n / align.get();
            mul * align.get()
        }

        for align in [1, 2, 4, 8, 16] {
            for n in 0..256 {
                let align = NonZeroUsize::new(align).unwrap();
                let want = alt_impl(n, align);
                let got = round_down_to_next_multiple_of_alignment(n, align);
                assert_eq!(got, want, "round_down_to_next_multiple_of_alignment({}, {})", n, align);
            }
        }
    }

    #[rustversion::since(1.57.0)]
    #[test]
    #[should_panic]
    fn test_round_down_to_next_multiple_of_alignment_zerocopy_panic_in_const_and_vec_try_reserve() {
        round_down_to_next_multiple_of_alignment(0, NonZeroUsize::new(3).unwrap());
    }
    #[test]
    fn test_send_sync_phantom_data() {
        let x = SendSyncPhantomData::<u8>::default();
        let y = x.clone();
        assert!(x == y);
        assert!(x == SendSyncPhantomData::<u8>::default());
    }

    #[test]
    #[allow(clippy::as_conversions)]
    fn test_as_address() {
        let x = 0u8;
        let r = &x;
        let mut x_mut = 0u8;
        let rm = &mut x_mut;
        let p = r as *const u8;
        let pm = rm as *mut u8;
        let nn = NonNull::new(p as *mut u8).unwrap();

        assert_eq!(AsAddress::addr(r), p as usize);
        assert_eq!(AsAddress::addr(rm), pm as usize);
        assert_eq!(AsAddress::addr(p), p as usize);
        assert_eq!(AsAddress::addr(pm), pm as usize);
        assert_eq!(AsAddress::addr(nn), p as usize);
    }
}
