// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{
    cell::{Cell, UnsafeCell},
    mem::{ManuallyDrop, MaybeUninit},
    num::Wrapping,
};

use crate::{
    pointer::{inner::PtrInner, invariant::*},
    FromBytes, Immutable, IntoBytes, Unalign,
};

/// Transmutations which are sound to attempt, conditional on validating the bit
/// validity of the destination type.
///
/// If a `Ptr` transmutation is `TryTransmuteFromPtr`, then it is sound to
/// perform that transmutation so long as some additional mechanism is used to
/// validate that the referent is bit-valid for the destination type. That
/// validation mechanism could be a type bound (such as `TransmuteFrom`) or a
/// runtime validity check.
///
/// # Safety
///
/// ## Post-conditions
///
/// Given `Dst: TryTransmuteFromPtr<Src, A, SV, DV, _>`, callers may assume the
/// following:
///
/// Given `src: Ptr<'a, Src, (A, _, SV)>` and `dst_inner =
/// SizeCompat::cast_from_raw(src.into_inner())`, if the referent of `dst_inner`
/// is `DV`-valid for `Dst`, then it is sound to construct `dst: Ptr<'a, Dst,
/// (A, Unaligned, DV)>` from `dst_inner`. Equivalently, it is sound to
/// transmute `src` into `dst` using [`SizeCompat::cast_from_raw`].
///
/// ## Pre-conditions
///
/// Given `src: Ptr<Src, (A, _, SV)>` and `dst: Ptr<Dst, (A, Unaligned, DV)>`
/// constructed from `SizeCompat::cast_from_raw(src.into_inner())`, `Dst:
/// TryTransmuteFromPtr<Src, A, SV, DV, _>` is sound if all of the following
/// hold:
/// - Forwards transmutation: Either of the following hold:
///   - So long as `dst` is active, no mutation of `dst`'s referent is allowed
///     except via `dst` itself
///   - `Dst: TransmuteFrom<Src, SV, DV>`
/// - Reverse transmutation: Either of the following hold:
///   - `dst` does not permit mutation of its referent
///   - `Src: TransmuteFrom<Dst, DV, SV>`
/// - No safe code, given access to `src` and `dst`, can cause undefined
///   behavior: Any of the following hold:
///   - `A` is `Exclusive`
///   - `Src: Immutable` and `Dst: Immutable`
///   - It is sound for safe code to operate on `src.as_ref(): &Src` and
///     `dst.as_ref(): &Dst` at the same time
///
/// ## Proof
///
/// Given:
/// - `src: Ptr<'a, Src, (A, _, SV)>`
/// - The leading `N` bytes of `src`'s referent are a `DV`-valid `Dst`, where
///   `N` is the referent size of `SizeCompat::cast_from_raw(src)`
///
/// We are trying to prove that it is sound to use `SizeCompat::cast_from_raw`
/// to transmute from `src` to a `dst: Ptr<'a, Dst, (A, Unaligned, DV)>`. We
/// need to prove that such a transmute does not violate any of `src`'s
/// invariants, and that it satisfies all invariants of the destination `Ptr`
/// type.
///
/// First, all of `src`'s `PtrInner` invariants are upheld. `src`'s address and
/// metadata are unchanged, so:
/// - If its referent is not zero sized, then it still has valid provenance for
///   its referent, which is still entirely contained in some Rust allocation,
///   `A`
/// - If its referent is not zero sized, `A` is guaranteed to live for at least
///   `'a`
///
/// By post-condition on `SizeCompat::cast_from_raw`, `dst` addresses a prefix
/// of the bytes addressed by `src`. `dst` also has the same lifetime as `src`.
/// Therefore, all of the `PtrInner` invariants mentioned above also hold for
/// `dst`.
///
/// Second, since `src`'s address is unchanged, it still satisfies its
/// alignment. Since `dst`'s alignment is `Unaligned`, it trivially satisfies
/// its alignment.
///
/// Third, aliasing (`A`) is either `Exclusive` or `Shared`:
/// - If it is `Exclusive`, then both `src` and `dst` satisfy `Exclusive`
///   aliasing trivially: since `src` and `dst` have the same lifetime, `src` is
///   inaccessible so long as `dst` is alive, and no other live `Ptr`s or
///   references may reference the same referent.
/// - If it is `Shared`, then either:
///   - `Src: Immutable` and `Dst: Immutable`, and so `UnsafeCell`s trivially
///     cover the same byte ranges in both types.
///   - It is sound for safe code to operate on a `src.as_ref()` and
///     `dst.as_ref()` at the same time.
///
/// Fourth, `src`'s validity is satisfied. By invariant, `src`'s referent began
/// as an `SV`-valid `Src`. It is guaranteed to remain so, as either of the
/// following hold:
/// - `dst` does not permit mutation of its referent.
/// - `Src: TransmuteFrom<Dst, DV, SV>`. Since `Dst: SizeCompat<Src>`, and since
///   `dst` is produced using `SizeCompat::cast_from_raw`, given `src'` composed
///   by concatenating any `DV`-valid `Dst` of size `size_of_val(dst)` with the
///   trailing `size_of_val(src) - size_of_val(dst)` bytes of `src`, `src'` is
///   an `SV`-valid `Src`. Thus, any value written to `dst` is guaranteed not to
///   violate the `SV`-validity of `Src`.
///
/// Fifth, `dst`'s validity is satisfied. It is a given of this proof that the
/// leading bytes of the referent are `DV`-valid for `Dst`. It is guaranteed to
/// remain so, as either of the following hold:
/// - So long as `dst` is active, no mutation of the referent is allowed except
///   via `dst` itself.
/// - `Dst: TransmuteFrom<Src, SV, DV>`. Since `Dst: SizeCompat<Src>`, and since
///   `dst` is produced using `SizeCompat::cast_from_raw`, the leading
///   `size_of_val(dst)` bytes of any `SV`-valid `Src` constitute a `DV`-valid
///   `Dst`. Thus, any value written via `src` is guaranteed not to violate the
///   `DV`-validity of `Dst`.
pub unsafe trait TryTransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>:
    SizeCompat<Src>
{
}

#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum BecauseMutationCompatible {}

// SAFETY:
// - Forwards transmutation: By `Dst: MutationCompatible<Src, A, SV, DV, _>`, we
//   know that at least one of the following holds:
//   - So long as `dst: Ptr<Dst>` is active, no mutation of its referent is
//     allowed except via `dst` itself if either of the following hold:
//     - Aliasing is `Exclusive`, in which case, so long as the `Dst` `Ptr`
//       exists, no mutation is permitted except via that `Ptr`
//     - Aliasing is `Shared`, `Src: Immutable`, and `Dst: Immutable`, in which
//       case no mutation is possible via either `Ptr`
//   - `Dst: TransmuteFrom<Src, SV, DV>`
// - Reverse transmutation: `Src: TransmuteFrom<Dst, DV, SV>`, and so the set of
//   `DV`-valid `Dst`s is a subset of the set of `SV`-valid `Src`s
// - No safe code, given access to `src` and `dst`, can cause undefined
//   behavior: By `Dst: MutationCompatible<Src, A, SV, DV, _>`, at least one of
//   the following holds:
//   - `A` is `Exclusive`
//   - `Src: Immutable` and `Dst: Immutable`
//   - `Dst: InvariantsEq<Src>`, which guarantees that `Src` and `Dst` have the
//     same invariants, and have `UnsafeCell`s covering the same byte ranges
unsafe impl<Src, Dst, SV, DV, A, R>
    TryTransmuteFromPtr<Src, A, SV, DV, (BecauseMutationCompatible, R)> for Dst
where
    A: Aliasing,
    SV: Validity,
    DV: Validity,
    Src: TransmuteFrom<Dst, DV, SV> + ?Sized,
    Dst: MutationCompatible<Src, A, SV, DV, R> + SizeCompat<Src> + ?Sized,
{
}

// SAFETY:
// - Forwards transmutation: Since aliasing is `Shared` and `Src: Immutable`,
//   `src` does not permit mutation of its referent.
// - Reverse transmutation: Since aliasing is `Shared` and `Dst: Immutable`,
//   `dst` does not permit mutation of its referent.
// - No safe code, given access to `src` and `dst`, can cause undefined
//   behavior: `Src: Immutable` and `Dst: Immutable`
unsafe impl<Src, Dst, SV, DV> TryTransmuteFromPtr<Src, Shared, SV, DV, BecauseImmutable> for Dst
where
    SV: Validity,
    DV: Validity,
    Src: Immutable + ?Sized,
    Dst: Immutable + SizeCompat<Src> + ?Sized,
{
}

/// Denotes that `src: Ptr<Src, (A, _, SV)>` and `dst: Ptr<Self, (A, _, DV)>`,
/// referencing the same referent at the same time, cannot be used by safe code
/// to break library safety invariants of `Src` or `Self`.
///
/// # Safety
///
/// At least one of the following must hold:
/// - `Src: Read<A, _>` and `Self: Read<A, _>`
/// - `Self: InvariantsEq<Src>` and:
///   - `Dst: TransmuteFrom<Src, SV, DV>`
///   - `Src: TransmuteFrom<Dst, DV, SV>`
pub unsafe trait MutationCompatible<Src: ?Sized, A: Aliasing, SV, DV, R> {}

#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum BecauseRead {}

// SAFETY: `Src: Read<A, _>` and `Dst: Read<A, _>`.
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R, S>
    MutationCompatible<Src, A, SV, DV, (BecauseRead, (R, S))> for Dst
where
    Src: Read<A, R>,
    Dst: Read<A, S>,
{
}

/// Denotes that two types have the same invariants.
///
/// # Safety
///
/// It is sound for safe code to operate on a `&T` and a `&Self` pointing to the
/// same referent at the same time - no such safe code can cause undefined
/// behavior.
pub unsafe trait InvariantsEq<T: ?Sized> {}

// SAFETY: Trivially sound to have multiple `&T` pointing to the same referent.
unsafe impl<T: ?Sized> InvariantsEq<T> for T {}

// SAFETY: `Dst: InvariantsEq<Src> + TransmuteFrom<Src, SV, DV>`, and `Src:
// TransmuteFrom<Dst, DV, SV>`.
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity>
    MutationCompatible<Src, A, SV, DV, BecauseInvariantsEq> for Dst
where
    Src: TransmuteFrom<Dst, DV, SV>,
    Dst: TransmuteFrom<Src, SV, DV> + InvariantsEq<Src>,
{
}

pub(crate) enum BecauseInvariantsEq {}

macro_rules! unsafe_impl_invariants_eq {
    ($tyvar:ident => $t:ty, $u:ty) => {{
        crate::util::macros::__unsafe();
        // SAFETY: The caller promises that this is sound.
        unsafe impl<$tyvar> InvariantsEq<$t> for $u {}
        // SAFETY: The caller promises that this is sound.
        unsafe impl<$tyvar> InvariantsEq<$u> for $t {}
    }};
}

impl_transitive_transmute_from!(T => MaybeUninit<T> => T => Wrapping<T>);
impl_transitive_transmute_from!(T => Wrapping<T> => T => MaybeUninit<T>);

// SAFETY: `ManuallyDrop<T>` has the same size and bit validity as `T` [1], and
// implements `Deref<Target = T>` [2]. Thus, it is already possible for safe
// code to obtain a `&T` and a `&ManuallyDrop<T>` to the same referent at the
// same time.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
//   validity as `T`
//
// [2] https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html#impl-Deref-for-ManuallyDrop%3CT%3E
unsafe impl<T: ?Sized> InvariantsEq<T> for ManuallyDrop<T> {}
// SAFETY: See previous safety comment.
unsafe impl<T: ?Sized> InvariantsEq<ManuallyDrop<T>> for T {}

/// Transmutations which are always sound.
///
/// `TransmuteFromPtr` is a shorthand for the conjuction of
/// [`TryTransmuteFromPtr`] and [`TransmuteFrom`].
///
/// # Safety
///
/// `Dst: TransmuteFromPtr<Src, A, SV, DV, _>` is equivalent to `Dst:
/// TryTransmuteFromPtr<Src, A, SV, DV, _> + TransmuteFrom<Src, SV, DV>`.
///
/// Further, if `Dst: TransmuteFromPtr<Src, A, SV, DV>`, then given `src:
/// Ptr<'_, (A, _, SV)>`, it is sound to transmute `src` to `dst: Ptr<'_, (A, _,
/// DV)>` using [`SizeCompat::cast_from_raw`] to perform the raw pointer
/// transmute.
///
/// ## Proof
///
/// TODO
pub unsafe trait TransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>:
    TryTransmuteFromPtr<Src, A, SV, DV, R> + TransmuteFrom<Src, SV, DV>
{
}

// SAFETY: The `where` bounds are equivalent to the safety invariant on
// `TransmuteFromPtr`.
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>
    TransmuteFromPtr<Src, A, SV, DV, R> for Dst
where
    Dst: TransmuteFrom<Src, SV, DV> + TryTransmuteFromPtr<Src, A, SV, DV, R>,
{
}

/// Denotes that any `SV`-valid `Src` may soundly be transmuted into a
/// `DV`-valid `Self`.
///
/// # Safety
///
/// *In this section, we refer to `Self` as `Dst`.*
///
/// If `Src` is an inhabited type, then `Dst` must also be an inhabited type.
///
/// ## By-value transmutation
///
/// If `Src: Sized` and `Dst: Sized`, then it must be sound to transmute an
/// `SV`-valid `Src` into a `DV`-valid `Dst` by value via union transmute. In
/// particular:
/// - If `size_of::<Src>() >= size_of::<Dst>()`, then the first
///   `size_of::<Dst>()` bytes of any `SV`-valid `Src` must be a `DV`-valid
///   `Dst`.
/// - If `size_of::<Src>() < size_of::<Dst>()`, then any `SV`-valid `Src`
///   followed by `size_of::<Dst>() - size_of::<Src>()` uninitialized bytes must
///   be a `DV`-valid `Dst`.
///
/// If either `Src: !Sized` or `Dst: !Sized`, then this condition does not need
/// to hold.
///
/// ## By-reference transmutation
///
/// If `Dst: SizeCompat<Src>`, then the following must hold: For all [valid
/// sizes] of `Src`, `ssize` let `s: PtrInner<'_, Src>` with referent size
/// `ssize`. Let `dsize` be the referent size of `SizeCompat::cast_from_raw(s)`.
/// Note that, by invariant on `cast_from_raw`, `ssize >= dsize`. For all
/// `SV`-valid values of `Src` with size `ssize`, `src`, it must be the case
/// that the leading `dsize` bytes of `src` constitute a `DV`-valid `Dst`.
///
/// *This case corresponds to a `&Src` to `&Dst` transmute.*
///
/// If `Src: SizeCompat<Dst>`, then the following must hold: For all [valid
/// sizes] of `Dst`, `dsize`, let `d: PtrInner<'_, Dst>` with referent size
/// `dsize`. Let `ssize` be the referent size of `SizeCompat::cast_from_raw(d)`.
/// Note that, by invariant on `cast_from_raw`, `dsize >= ssize`. For all
/// `DV`-valid values of `Dst` with size `dsize`, `dst`, and for all `SV`-valid
/// values of `Src` with size `ssize`, `src`, let `dst'` be constructed by
/// concatenating `src` with the trailing `dsize - ssize` bytes of `dst`. It
/// must be the case that `dst'` is a `DV`-valid `Dst`.
///
/// *This case corresponds to a `&Dst` to `&Src` transmute where `Src` and `Dst`
/// permit interior mutation, or to a `&mut Dst` to `&mut Src` transmute. In
/// particular, it ensures that, once values have been written to the `&Src` or
/// `&mut Src` and the `&Src` or `&mut Src` have been dropped, the original
/// `&Src` or `&mut Src` still refer to an `SV`-valid `Src`.*
///
/// Note that, if `<Dst as SizeCompat<Src>>::cast_from_raw` and `<Src as
/// SizeCompat<Dst>>::cast_from_raw` both preserve referent size exactly, then
/// the conditions in this section are a logical consequence of the conditions
/// in the "By-value transmutation" section.
///
/// [valid sizes]: crate::KnownLayout#what-is-a-valid-size
pub unsafe trait TransmuteFrom<Src: ?Sized, SV, DV> {}

/// # Safety
///
/// Implementations of `cast_from_raw` must satisfy that method's safety
/// post-condition.
pub unsafe trait SizeCompat<Src: ?Sized> {
    /// # Safety
    ///
    /// Given `src: PtrInner<'_, Src>`, `let dst = Self::cast_from_raw(src)`
    /// produces a pointer with the same address as `src`, and referring to at
    /// most as many bytes. If `src` has valid provenance for its referent, then
    /// `dst` has valid provenance for *its* referent.
    ///
    /// The size of `dst` must only be a function of the size of `src`. It must
    /// not be a function of `src`'s address.
    ///
    /// `<Self as SizeCompat<Self>>::cast_from_raw` is guaranteed to be the
    /// identity function.
    fn cast_from_raw(src: PtrInner<'_, Src>) -> PtrInner<'_, Self>;
}

// SAFETY: `T` trivially has the same size and vtable kind as `T`, and since
// pointer `*mut T -> *mut T` pointer casts are no-ops, this cast trivially
// preserves referent size (when `T: ?Sized`).
unsafe impl<T: ?Sized> SizeCompat<T> for T {
    #[inline(always)]
    fn cast_from_raw<'a>(t: PtrInner<'a, T>) -> PtrInner<'a, T> {
        t
    }
}

// TODO: Update all `TransmuteFrom` safety proofs.

/// `Valid<Src: IntoBytes> → Initialized<Dst>`
// SAFETY: Since `Src: IntoBytes`, the set of valid `Src`'s is the set of
// initialized bit patterns, which is exactly the set allowed in the referent of
// any `Initialized` `Ptr`.
unsafe impl<Src, Dst> TransmuteFrom<Src, Valid, Initialized> for Dst
where
    Src: IntoBytes + ?Sized,
    Dst: ?Sized,
{
}

/// `Initialized<Src> → Valid<Dst: FromBytes>`
// SAFETY: Since `Dst: FromBytes`, any initialized bit pattern may appear in the
// referent of a `Ptr<Dst, (_, _, Valid)>`. This is exactly equal to the set of
// bit patterns which may appear in the referent of any `Initialized` `Ptr`.
unsafe impl<Src, Dst> TransmuteFrom<Src, Initialized, Valid> for Dst
where
    Src: ?Sized,
    Dst: FromBytes + ?Sized,
{
}

// FIXME(#2354): This seems like a smell - the soundness of this bound has
// nothing to do with `Src` or `Dst` - we're basically just saying `[u8; N]` is
// transmutable into `[u8; N]`.

/// `Initialized<Src> → Initialized<Dst>`
// SAFETY: The set of allowed bit patterns in the referent of any `Initialized`
// `Ptr` is the same regardless of referent type.
unsafe impl<Src, Dst> TransmuteFrom<Src, Initialized, Initialized> for Dst
where
    Src: ?Sized,
    Dst: ?Sized,
{
}

// FIXME(#2354): This seems like a smell - the soundness of this bound has
// nothing to do with `Dst` - we're basically just saying that any type is
// transmutable into `MaybeUninit<[u8; N]>`.

/// `V<Src> → Uninit<Dst>`
// SAFETY: A `Dst` with validity `Uninit` permits any byte sequence, and
// therefore can be transmuted from any value.
unsafe impl<Src, Dst, V> TransmuteFrom<Src, V, Uninit> for Dst
where
    Src: ?Sized,
    Dst: ?Sized,
    V: Validity,
{
}

// SAFETY:
// - `ManuallyDrop<T>` has the same size as `T` [1]
// - `ManuallyDrop<T>` has the same validity as `T` [1]
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`
const _: () = unsafe { unsafe_impl_for_transparent_wrapper!(T: ?Sized => ManuallyDrop<T>) };

// SAFETY:
// - `Unalign<T>` promises to have the same size as `T`.
// - `Unalign<T>` promises to have the same validity as `T`.
const _: () = unsafe { unsafe_impl_for_transparent_wrapper!(T => Unalign<T>) };
// SAFETY: `Unalign<T>` promises to have the same size and validity as `T`.
// Given `u: &Unalign<T>`, it is already possible to obtain `let t =
// u.try_deref().unwrap()`. Because `Unalign<T>` has the same size as `T`, the
// returned `&T` must point to the same referent as `u`, and thus it must be
// sound for these two references to exist at the same time since it's already
// possible for safe code to get into this state.
const _: () = unsafe { unsafe_impl_invariants_eq!(T => T, Unalign<T>) };

// SAFETY:
// - `Wrapping<T>` has the same size as `T` [1].
// - `Wrapping<T>` has only one field, which is `pub` [2]. We are also
//   guaranteed per that `Wrapping<T>` has the same layout as `T` [1]. The only
//   way for both of these to be true simultaneously is for `Wrapping<T>` to
//   have the same bit validity as `T`. In particular, in order to change the
//   bit validity, one of the following would need to happen:
//   - `Wrapping` could change its `repr`, but this would violate the layout
//     guarantee.
//   - `Wrapping` could add or change its fields, but this would be a
//     stability-breaking change.
//
// [1] Per https://doc.rust-lang.org/1.85.0/core/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
//
// [2] Definition from https://doc.rust-lang.org/1.85.0/core/num/struct.Wrapping.html:
//
//   ```
//   #[repr(transparent)]
//   pub struct Wrapping<T>(pub T);
//   ```
const _: () = unsafe { unsafe_impl_for_transparent_wrapper!(T => Wrapping<T>) };

// SAFETY: By the preceding safety proof, `Wrapping<T>` and `T` have the same
// layout and bit validity. Since a `Wrapping<T>`'s `T` field is `pub`, given
// `w: &Wrapping<T>`, it's possible to do `let t = &w.t`, which means that it's
// already possible for safe code to obtain a `&Wrapping<T>` and a `&T` pointing
// to the same referent at the same time. Thus, this must be sound.
const _: () = unsafe { unsafe_impl_invariants_eq!(T => T, Wrapping<T>) };

// SAFETY:
// - `UnsafeCell<T>` has the same size as `T` [1].
// - Per [1], `UnsafeCell<T>` has the same bit validity as `T`. Technically the
//   term "representation" doesn't guarantee this, but the subsequent sentence
//   in the documentation makes it clear that this is the intention.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`. A consequence of this guarantee is that it is possible to convert
//   between `T` and `UnsafeCell<T>`.
const _: () = unsafe { unsafe_impl_for_transparent_wrapper!(T: ?Sized => UnsafeCell<T>) };

// SAFETY:
// - `Cell<T>` has the same size as `T` [1].
// - Per [1], `Cell<T>` has the same bit validity as `T`. Technically the term
//   "representation" doesn't guarantee this, but it does promise to have the
//   "same memory layout and caveats as `UnsafeCell<T>`." The `UnsafeCell` docs
//   [2] make it clear that bit validity is the intention even if that phrase
//   isn't used.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/cell/struct.Cell.html#memory-layout:
//
//   `Cell<T>` has the same memory layout and caveats as `UnsafeCell<T>`. In
//   particular, this means that `Cell<T>` has the same in-memory representation
//   as its inner type `T`.
//
// [2] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`. A consequence of this guarantee is that it is possible to convert
//   between `T` and `UnsafeCell<T>`.
const _: () = unsafe { unsafe_impl_for_transparent_wrapper!(T: ?Sized => Cell<T>) };

impl_transitive_transmute_from!(T: ?Sized => Cell<T> => T => UnsafeCell<T>);
impl_transitive_transmute_from!(T: ?Sized => UnsafeCell<T> => T => Cell<T>);

/// `Uninit<Src> → Valid<MaybeUninit<Dst>>`
// SAFETY: `MaybeUninit<T>` has no validity requirements. Currently this is not
// explicitly guaranteed, but it's obvious from `MaybeUninit`'s documentation
// that this is the intention:
// https://doc.rust-lang.org/1.85.0/core/mem/union.MaybeUninit.html
unsafe impl<Src, Dst> TransmuteFrom<Src, Uninit, Valid> for MaybeUninit<Dst> {}

// SAFETY: `MaybeUninit<T>` has the same size as `T` [1]. Thus, a pointer cast
// preserves address and referent size.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
//   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
//   `T`
unsafe impl<T> SizeCompat<T> for MaybeUninit<T> {
    #[inline(always)]
    fn cast_from_raw(t: PtrInner<'_, T>) -> PtrInner<'_, MaybeUninit<T>> {
        // SAFETY: Per preceding safety comment, `MaybeUninit<T>` and `T` have
        // the same size, and so this cast preserves referent size.
        unsafe { cast!(t) }
    }
}

// SAFETY: See previous safety comment.
unsafe impl<T> SizeCompat<MaybeUninit<T>> for T {
    #[inline(always)]
    fn cast_from_raw(t: PtrInner<'_, MaybeUninit<T>>) -> PtrInner<'_, T> {
        // SAFETY: Per preceding safety comment, `MaybeUninit<T>` and `T` have
        // the same size, and so this cast preserves referent size.
        unsafe { cast!(t) }
    }
}
