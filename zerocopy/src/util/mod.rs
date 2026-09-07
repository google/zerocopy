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
/// # Safety
///
/// The caller guarantees that `src.len() <= dst.len()`.
#[inline(always)]
pub(crate) unsafe fn copy_unchecked(src: &[u8], dst: &mut [u8]) {
    debug_assert!(src.len() <= dst.len());
    // SAFETY: This invocation satisfies the safety contract of
    // copy_nonoverlapping [1]:
    // - `src.as_ptr()` is trivially valid for reads of `src.len()` bytes
    // - `dst.as_mut_ptr()` is valid for writes of `src.len()` bytes because
    //   the caller has promised that `src.len() <= dst.len()`
    // - `src` and `dst` are, trivially, properly aligned
    // - the region of memory beginning at `src` with a size of `src.len()`
    //   bytes does not overlap with the region of memory beginning at `dst`
    //   with the same size, because `dst` is derived from an exclusive
    //   reference which coexists with `src` [2].
    //
    // [1] Per https://doc.rust-lang.org/1.56.0/std/ptr/fn.copy_nonoverlapping.html#safety:
    //
    //     Behavior is undefined if any of the following conditions are
    //     violated:
    //
    //     - `src` must be valid for reads of `count * size_of::<T>()` bytes.
    //     - `dst` must be valid for writes of `count * size_of::<T>()` bytes.
    //     - Both `src` and `dst` must be properly aligned.
    //     - The region of memory beginning at `src` with a size of
    //       `count * size_of::<T>()` bytes must not overlap with the region of
    //       memory beginning at `dst` with the same size.
    //
    //     Note that even if the effectively copied size
    //     (`count * size_of::<T>()`) is 0, the pointers must be non-null and
    //     properly aligned.
    //
    // [2] Per https://doc.rust-lang.org/1.56.0/reference/types/pointer.html#mutable-references-mut:
    //
    //     A mutable reference (that hasn't been borrowed) is the only way to
    //     access the value it points to.
    unsafe {
        core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    };
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
    use core::num::Wrapping;

    use super::*;
    use crate::pointer::{BecauseImmutable, BecauseInvariantsEq, BecauseMutationCompatible};

    // Configuration: The harnesses below use the common Kani CI configuration
    // documented in `agent_docs/validation.md`: the CI-pinned Kani release and
    // its bundled x86_64-unknown-linux-gnu compiler, the stable-compatible
    // feature bundle, `-Zfunction-contracts`, and one layout selected by
    // `--randomize-layout` per invocation.
    //
    // `copy_unchecked` proof scope:
    //
    // Domain: Every source `[u8; 8]`, destination `[u8; 12]`, source length
    // from 0 through 8, and destination length from the source length through
    // 12. The proof uses only those fixed stack arrays and one fixed
    // destination snapshot; it performs no dynamic allocation and has no
    // explicit proof loop. Its unwind bound is 13, one more than the largest
    // modeled slice, and applies to all target and oracle loops Kani reaches,
    // with unwinding assertions enabled.
    // Establishes: The copied prefix and every destination frame byte exactly
    // match a safe copy.
    // Oracle: Safe `slice::copy_from_slice`, whose Rust 1.93 contract copies
    // every element from an equal-length source [1], is applied to a separate
    // destination copy.
    // Excludes: Larger fixed arrays, overlapping regions (which safe input
    // references preclude), and aliasing or provenance properties outside
    // Kani's model. This is not a generic contract proof.
    //
    // [1] Rust 1.93 specifies that `copy_from_slice` copies every element from
    // `src` into the equal-length receiver:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_from_slice
    //
    // Transmutation proof scope:
    //
    // Domain: Every `u32`, every independently generated `[u8; 4]`, and shared
    // and mutable `u32` views as `Wrapping<u32>`. Each proof uses only fixed
    // scalar values, performs no dynamic allocation, and has no explicit proof
    // loop. Every harness has unwind bound five, which also bounds any target
    // or oracle loop Kani reaches, with unwinding assertions enabled.
    // Establishes: Independently seeded value-to-bytes and bytes-to-value
    // native representation contracts, modeled address preservation, and
    // mutation propagation. Neither value transmutation is used to construct
    // the other's input.
    // Oracle: Safe `u32::to_ne_bytes` and `u32::from_ne_bytes` directly map
    // between a value and its native-endian memory representation [2][3]; safe
    // `Wrapping` construction and its documented transparent layout supply
    // the reference expectations. Rust's listed reference-to-raw-pointer
    // coercions supply pointers to the source and returned referents [4]. The
    // raw-pointer `cast` methods are documented as casts to another pointer
    // type [5], and the Reference says a sized-to-sized pointer cast returns
    // the pointer unchanged [6]. Raw-pointer equality is documented as address
    // equality [5], so the equality assertions independently observe whether
    // the target preserved the referent's modeled address.
    // Excludes: Other source/destination types, invalid representations, and
    // provenance or aliasing guarantees. In particular, the address operation
    // used to define pointer equality discards provenance [5]; equal raw
    // pointer addresses therefore do not establish equal provenance. These
    // are not generic transmutation contract proofs.
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
    // Allocation proof scope:
    //
    // Domain: Three fixed calls: `new_box::<u32>((), alloc_zeroed)`,
    // `new_box::<[u8]>(4, alloc_zeroed)`, and `new_box::<()>((), alloc)`. The
    // first two select the nonzero-size branch; the unit call selects the
    // zero-size dangling-pointer branch. In the inspected source, each selected
    // nonzero-size path reaches the single call through `allocate`, while the
    // unit path bypasses it; the harnesses do not instrument allocator-call
    // counts. Kani 0.67 invokes CBMC with `--no-malloc-may-fail` [7], and the
    // bundled CBMC 6.8.0's own `--help` defines that flag as "disable potential
    // malloc failure" [8], so these harnesses do not model allocation failure.
    // Harness-owned inputs and oracles have fixed shape; the first two target
    // calls exercise Kani's allocation and normal deallocation models. There
    // is no explicit proof loop. Each harness sets the loop-unwinding bound to
    // five; common CI retains unwinding assertions for every translated
    // reachable loop. This is not Rust panic-unwind coverage.
    // Establishes: Within Kani's model, if the `u32` call succeeds, it returns
    // zeroed storage which accepts a symbolic write; if the `[u8]` call
    // succeeds, it returns four zero bytes with length four; and the unit call
    // returns `Ok` with a zero-sized referent.
    // Oracle: Safe value construction supplies the expected contents and
    // length. Dereferencing the returned `Box` only observes the target; it is
    // not independent evidence that constructing that `Box` was sound.
    // Excludes: Every allocation-failure and `Err` path, uninitialized non-ZST
    // referents, arbitrary types/metadata, and nested slice DSTs (see
    // https://github.com/google/zerocopy/pull/3630). In particular, these are
    // behavioral smoke regressions, not proofs of the `Box::from_raw`
    // provenance, alignment, ownership, or allocator/deallocator obligations
    // called out by FIXME #429 above, nor of `new_box`'s overall soundness.
    //
    // [7] https://github.com/model-checking/kani/blob/kani-0.67.0/kani-driver/src/call_cbmc.rs#L195-L200
    //
    // [8] `agent_docs/validation.md` records the exact bundled CBMC version and
    // its inspected `--no-malloc-may-fail` / `--malloc-may-fail` help text.

    #[kani::proof]
    #[kani::unwind(13)]
    fn prove_copy_unchecked_copies_prefix_and_preserves_frame() {
        const SRC_CAPACITY: usize = 8;
        const DST_CAPACITY: usize = 12;

        let src: [u8; SRC_CAPACITY] = kani::any();
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

        let mut expected_dst = dst;
        expected_dst[..src_len].copy_from_slice(&src[..src_len]);

        // SAFETY: The assumptions above establish `src_len <= dst_len`, the
        // sole caller precondition of `copy_unchecked`. More concretely, the
        // reference arguments are aligned, non-null, and point to valid slice
        // values [2]. Their pointer accessors point to the corresponding slice
        // buffers [3], so `src` supplies `src_len` readable bytes and the
        // length inequality makes at least that many bytes writable through
        // `dst`. The shared source and exclusive destination references
        // coexist through the call; the exclusive-reference rule [4]
        // therefore prevents their accessed regions from overlapping. These
        // facts satisfy the wrapped operation's requirements [1].
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/std/ptr/fn.copy_nonoverlapping.html#safety:
        //
        //     `src` must be valid for reads of `count * size_of::<T>()` bytes.
        //
        //     `dst` must be valid for writes of `count * size_of::<T>()` bytes.
        //
        //     Both `src` and `dst` must be properly aligned.
        //
        //     The region of memory beginning at `src` with a size of
        //     `count * size_of::<T>()` bytes must not overlap with the region
        //     of memory beginning at `dst` with the same size.
        //
        //     Note that even if the effectively copied size
        //     (`count * size_of::<T>()`) is 0, the pointers must be non-null
        //     and properly aligned.
        //
        // [2] Per https://doc.rust-lang.org/1.93.0/std/primitive.reference.html:
        //
        //     a reference is just a pointer that is assumed to be aligned, not
        //     null, and pointing to memory containing a valid value of `T`
        //
        // [3] Per https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
        // and https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_mut_ptr:
        //
        //     Returns a raw pointer to the slice's buffer.
        //
        //     Returns an unsafe mutable pointer to the slice's buffer.
        //
        // [4] Per https://doc.rust-lang.org/1.93.0/reference/behavior-considered-undefined.html#r-undefined.alias:
        //
        //     `&mut T` must point to memory that is not read or written by any
        //     pointer not derived from the reference
        unsafe { copy_unchecked(&src[..src_len], &mut dst[..dst_len]) };

        assert_eq!(dst, expected_dst);
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
        assert_eq!(bytes, src.to_ne_bytes());
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
        assert_eq!(roundtrip, u32::from_ne_bytes(bytes));
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
        assert_eq!(*dst, Wrapping(src));
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_transmute_mut_preserves_address_and_mutates_source() {
        let mut src: u32 = kani::any();
        let original = src;
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
            assert_eq!(*dst, Wrapping(original));
            *dst = Wrapping(replacement);
            assert_eq!(*dst, Wrapping(replacement));
        }

        kani::cover!(replacement != original);
        assert_eq!(src, replacement);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zeroed_u32_on_success() {
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
        let result = unsafe { new_box::<u32>((), alloc::alloc::alloc_zeroed) };
        kani::cover!(result.is_ok());

        if let Ok(mut boxed) = result {
            assert_eq!(*boxed, 0);

            let replacement: u32 = kani::any();
            *boxed = replacement;
            assert_eq!(*boxed, replacement);
        }
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zst() {
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
        let result = unsafe { new_box::<()>((), alloc::alloc::alloc) };
        assert!(result.is_ok());

        let boxed = result.unwrap();
        assert_eq!(mem::size_of_val(&*boxed), 0);
    }

    #[cfg(feature = "alloc")]
    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_new_box_zeroed_byte_slice_on_success() {
        const LEN: usize = 4;

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
        let result = unsafe { new_box::<[u8]>(LEN, alloc::alloc::alloc_zeroed) };
        kani::cover!(result.is_ok());

        if let Ok(boxed) = result {
            let expected = [0u8; LEN];
            assert_eq!(&*boxed, &expected[..]);
        }
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
