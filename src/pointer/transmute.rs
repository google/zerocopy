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
/// SizeFrom::cast_from_raw(src.into_inner())`, if the referent of `dst_inner`
/// is `DV`-valid for `Dst`, then it is sound to construct `dst: Ptr<'a, Dst,
/// (A, Unaligned, DV)>` from `dst_inner`. Equivalently, it is sound to
/// transmute `src` into `dst` using [`SizeFrom::cast_from_raw`].
///
/// ## Pre-conditions
///
/// Given `src: Ptr<Src, (A, _, SV)>` and `dst: Ptr<Dst, (A, Unaligned, DV)>`
/// constructed from `SizeFrom::cast_from_raw(src.into_inner())`, `Dst:
/// TryTransmuteFromPtr<Src, A, SV, DV, _>` is sound if all of the following
/// hold:
/// - Forwards transmutation: Either of the following hold:
///   - So long as `dst` is active, no mutation of `dst`'s referent is allowed
///     except via `dst` itself
///   - `Dst: TransmuteFrom<Src, SV, DV>`
/// - Reverse transmutation: Either of the following hold:
///   - `dst` does not permit mutation of its referent
///   - `Src: TransmuteFromOverwrite<Dst, DV, SV>`
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
///   `N` is the referent size of `SizeFrom::cast_from_raw(src)`
///
/// We are trying to prove that it is sound to use `SizeFrom::cast_from_raw` to
/// transmute from `src` to a `dst: Ptr<'a, Dst, (A, Unaligned, DV)>`. We need
/// to prove that such a transmute does not violate any of `src`'s invariants,
/// and that it satisfies all invariants of the destination `Ptr` type.
///
/// First, all of `src`'s `PtrInner` invariants are upheld. `src`'s address and
/// metadata are unchanged, so:
/// - If its referent is not zero sized, then it still has valid provenance for
///   its referent, which is still entirely contained in some Rust allocation,
///   `A`
/// - If its referent is not zero sized, `A` is guaranteed to live for at least
///   `'a`
///
/// By post-condition on `SizeFrom::cast_from_raw`, `dst` addresses a prefix of
/// the bytes addressed by `src`. `dst` also has the same lifetime as `src`.
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
/// - `Src: TransmuteFromOverwrite<Dst, DV, SV>`. Since `Dst: SizeFrom<Src>`,
///   and since `dst` is produced using `SizeFrom::cast_from_raw`, given `src'`
///   composed by concatenating any `DV`-valid `Dst` of size `size_of_val(dst)`
///   with the trailing `size_of_val(src) - size_of_val(dst)` bytes of `src`,
///   `src'` is an `SV`-valid `Src`. Thus, any value written to `dst` is
///   guaranteed not to violate the `SV`-validity of `Src`.
///
/// Fifth, `dst`'s validity is satisfied. It is a given of this proof that the
/// leading bytes of the referent are `DV`-valid for `Dst`. It is guaranteed to
/// remain so, as either of the following hold:
/// - So long as `dst` is active, no mutation of the referent is allowed except
///   via `dst` itself.
/// - `Dst: TransmuteFrom<Src, SV, DV>`. Since `Dst: SizeFrom<Src>`, and since
///   `dst` is produced using `SizeFrom::cast_from_raw`, the leading
///   `size_of_val(dst)` bytes of any `SV`-valid `Src` constitute a `DV`-valid
///   `Dst`. Thus, any value written via `src` is guaranteed not to violate the
///   `DV`-validity of `Dst`.
pub unsafe trait TryTransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>:
    SizeFrom<Src>
{
}

// SAFETY:
// - Forwards transmutation: By `Dst: MutationCompatible<Src, A, SV, DV>`, one
//   of the following holds:
//   - So long as `dst` is active, no mutation of `dst`'s referent is allowed
//     except via `dst` itself because:
//     - `A = Exclusive`, or
//     - `A = Shared`, `Src: Immutable`, and `Dst: Immutable`, in which case no
//       mutation is permitted whatsoever.
//   - `Dst: TransmuteFrom<Src, SV, DV>`
// - Reverse transmutation: By `Dst: MutationCompatible<Src, A, SV, DV>`, one of
//   the following holds:
//   - `dst` does not permit mutation of its referent because `A = Shared`,
//     `Src: Immutable`, and `Dst: Immutable`
//   - `Src: TransmuteFromOverwrite<Dst, DV, SV>`
// - No safe code, given access to `src` and `dst`, can cause undefined
//   behavior: By `Dst: MutationCompatible<Src, A, SV, DV>`, one of the
//   following holds:
//   - `A` is `Exclusive`
//   - `Src: Immutable` and `Dst: Immutable`
//   - `Dst: InvariantsEq<Src>`, in which case it is sound for safe code to
//     operate on `src.as_ref(): &Src` and `dst.as_ref(): &Dst` at the same time
unsafe impl<Src, Dst, A, SV, DV, R> TryTransmuteFromPtr<Src, A, SV, DV, R> for Dst
where
    A: Aliasing,
    SV: Validity,
    DV: Validity,
    Src: ?Sized,
    Dst: MutationCompatible<Src, A, SV, DV, R> + SizeFrom<Src> + ?Sized,
{
}

/// Denotes that `src: Ptr<Src, (A, _, SV)>` and `dst: Ptr<Self, (A, _, DV)>`,
/// referencing the same referent at the same time, cannot be used by safe code
/// to break library safety invariants of `Src` or `Self`.
///
/// # Safety
///
/// At least one of the following must hold:
/// - `A = Exclusive` and `Src: TransmuteOverwrite<Dst, DV, SV>`
/// - `A = Shared`, `Src: Immutable`, and `Dst: Immutable`
/// - `Dst: TransmuteFrom<Src, SV, DV>`, `Src: TransmuteOverwrite<Dst, DV, SV>`,
///   and `Dst: InvariantsEq<Src>`
pub unsafe trait MutationCompatible<Src: ?Sized, A: Aliasing, SV, DV, R> {}

#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum BecauseReversible {}

#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum BecauseBidirectional {}

// SAFETY: Aliasing is `Exclusive` and `Src: TransmuteOverwrite<Dst, DV, SV>`.
unsafe impl<Src: ?Sized, Dst: ?Sized, SV: Validity, DV: Validity>
    MutationCompatible<Src, Exclusive, SV, DV, BecauseReversible> for Dst
where
    Src: TransmuteOverwrite<Dst, DV, SV>,
{
}

// SAFETY: Aliasing is `Shared`, `Src: Immutable`, and `Dst: Immutable`.
unsafe impl<Src: ?Sized, Dst: ?Sized, SV: Validity, DV: Validity>
    MutationCompatible<Src, Shared, SV, DV, BecauseImmutable> for Dst
where
    Src: Immutable,
    Dst: Immutable,
{
}

// SAFETY: `Dst: TransmuteFrom<Src, SV, DV>`, `Src: TransmuteFromOverwrite<Dst,
// DV, SV>`, and `Dst: InvariantsEq<Src>`.
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Reference, SV: Validity, DV: Validity>
    MutationCompatible<Src, A, SV, DV, BecauseBidirectional> for Dst
where
    Dst: TransmuteFrom<Src, SV, DV> + InvariantsEq<Src>,
    Src: TransmuteOverwrite<Dst, DV, SV>,
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
/// DV)>` using [`SizeFrom::cast_from_raw`] to perform the raw pointer
/// transmute.
///
/// ## Proof
///
/// By `Dst: TryTransmuteFromPtr<Src, A, SV, DV>`:
///
/// > Given `src: Ptr<'a, Src, (A, _, SV)>` and `dst_inner =
/// > SizeFrom::cast_from_raw(src.into_inner())`, if the referent of `dst_inner`
/// > is `DV`-valid for `Dst`, then it is sound to construct `dst: Ptr<'a, Dst,
/// > (A, Unaligned, DV)>` from `dst_inner`. Equivalently, it is sound to
/// > transmute `src` into `dst` using [`SizeFrom::cast_from_raw`].
///
/// Thus, we just need to prove that `dst_inner`'s referent is `DV`-valid for
/// `Dst`.
///
/// By `Dst: TransmuteFrom<Src, SV, DV>`:
///
/// > If `Dst: SizeFrom<Src>`, then the following must hold: For all [valid
/// > sizes] of `Src`, `ssize`, let `s: PtrInner<'_, Src>` with referent size
/// > `ssize`. Let `dsize` be the referent size of `SizeFrom::cast_from_raw(s)`.
/// > Note that, by invariant on `cast_from_raw`, `ssize >= dsize`. For all
/// > `SV`-valid values of `Src` with size `ssize`, `src`, it must be the case
/// > that the leading `dsize` bytes of `src` constitute a `DV`-valid `Dst`.
///
/// `dst_inner = SizeFrom::cast_from_raw(src.into_inner())`, and so its referent
/// size is equal to `dsize` in the `TransmuteFrom` safety invariant. Thus, for
/// all possible referents of `src`, `dst_inner`'s referent constitutes a
/// `DV`-valid `Dst`.
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
/// If `Dst: SizeFrom<Src>` (or `Dst: Sized` and `Src: Sized` where
/// `size_of::<Dst>() <= size_of::<Src>()`), then the following must hold: For
/// all [valid sizes] of `Src` (or for `size_of::<Src>()`), `ssize`, let `s:
/// PtrInner<'_, Src>` with referent size `ssize`. Let `dsize` be the referent
/// size of `SizeFrom::cast_from_raw(s)` (or `size_of::<Dst>()`). Note that, by
/// invariant on `cast_from_raw` (or by `size_of::<Dst>() <= size_of::<Src>()`),
/// `ssize >= dsize`. For all `SV`-valid values of `Src` with size `ssize`,
/// `src`, it must be the case that the leading `dsize` bytes of `src`
/// constitute a `DV`-valid `Dst`.
///
/// [valid sizes]: crate::KnownLayout#what-is-a-valid-size
pub unsafe trait TransmuteFrom<Src: ?Sized, SV, DV> {}

/// Denotes that any `BV`-valid `Self` may have its prefix overwritten with any
/// `OV`-valid `Overlay` and remain `BV`-valid.
///
/// # Safety
///
/// *In this section, we refer to `Self` as `Base`.*
///
/// If `Overlay: SizeFrom<Base>` (or `Overlay: Sized` and `Base: Sized` where
/// `size_of::<Overlay>() <= size_of::<Base>()`), then the following must hold:
/// For all [valid sizes] of `Base` (or for `size_of::<Base>()`), `bsize`, let
/// `b: PtrInner<'_, Base>` with referent size `bsize`. Let `osize` be the
/// referent size of `SizeFrom::cast_from_raw(b)` (or `size_of::<Overlay>()`).
/// Note that, by invariant on `cast_from_raw` (or by `size_of::<Overlay>() <=
/// size_of::<Base>()`), `bsize >= osize`. For all `BV`-valid values of `Base`
/// with size `bsize`, `base`, and for all `OV`-valid values of `Overlay` with
/// size `osize`, `overlay`, let `base'` be constructed by concatenating
/// `overlay` with the trailing `bsize - osize` bytes of `base`. It must be the
/// case that `base'` is a `BV`-valid `Base`.
///
/// [valid sizes]: crate::KnownLayout#what-is-a-valid-size
pub unsafe trait TransmuteOverwrite<Overlay: ?Sized, OV, BV> {}

/// # Safety
///
/// Implementations of `cast_from_raw` must satisfy that method's safety
/// post-condition.
pub unsafe trait SizeFrom<Src: ?Sized> {
    /// # Safety
    ///
    /// Given `src: PtrInner<'_, Src>`, `let dst = Self::cast_from_raw(src)`
    /// produces a pointer with the same address as `src`, and referring to at
    /// most as many bytes.
    ///
    /// The size of `dst` must only be a function of the size of `src`. It must
    /// not be a function of `src`'s address.
    ///
    /// `<Self as SizeFrom<Self>>::cast_from_raw` is guaranteed to be the
    /// identity function.
    fn cast_from_raw(src: PtrInner<'_, Src>) -> PtrInner<'_, Self>;
}

// SAFETY: `T` trivially has the same size and vtable kind as `T`, and since
// pointer `*mut T -> *mut T` pointer casts are no-ops, this cast trivially
// preserves referent size (when `T: ?Sized`).
unsafe impl<T: ?Sized> SizeFrom<T> for T {
    #[inline(always)]
    fn cast_from_raw<'a>(t: PtrInner<'a, T>) -> PtrInner<'a, T> {
        t
    }
}

/// `Valid<Src: IntoBytes> → Initialized<Dst>`
// SAFETY: Since `Src: IntoBytes`, the set of valid `Src`'s is the set of
// initialized bit patterns, which is exactly the set allowed in the referent of
// any `Initialized` `Ptr`. This holds even for shrinking transmutes.
unsafe impl<Src, Dst> TransmuteFrom<Src, Valid, Initialized> for Dst
where
    Src: IntoBytes + ?Sized,
    Dst: ?Sized,
{
}

/// `Valid<Overlay: IntoBytes> → Initialized<Base>`
// SAFETY: Let `overlay` be a `Valid` `Overlay` and `base` be an `Initialized`
// `Base`. The trailing bytes of `base` have bit validity `[u8; N]`. By
// `Overlay: IntoBytes`, `overlay`'s bit validity is at least as restrictive as
// `[u8; M]` (some `[u8; M]` values may not be valid `Overlay` values). Thus,
// `base' = overlay + trailing_bytes_of(base)` is a valid `[u8; N + M]`, which
// is a valid `Initialized` value.
unsafe impl<Overlay, Base> TransmuteOverwrite<Overlay, Valid, Initialized> for Base
where
    Overlay: IntoBytes + ?Sized,
    Base: ?Sized,
{
}

/// `Initialized<Src> → Valid<Dst: FromBytes>`
// SAFETY: Since `Dst: FromBytes`, any initialized bit pattern is a valid `Dst`.
// An `Initialized<Src>` is guaranteed to have all its bytes initialized, so any
// (prefix of an) `Initialized<Src>` is a valid `Dst`.
unsafe impl<Src, Dst> TransmuteFrom<Src, Initialized, Valid> for Dst
where
    Src: ?Sized,
    Dst: FromBytes + ?Sized,
{
}

/// `Initialized<Overlay> → Valid<Base: FromBytes + IntoBytes>`
// SAFETY: The bit validity of `Initialized<Overlay>` is equivalent to that of
// `[u8]`. By `Base: FromBytes + IntoBytes`, the validity of `Valid<Base>` is
// also equivalent to that of `[u8]`. Any two `[u8]`s concatenated together are
// a valid `[u8]`.
//
// It might be tempting to remove the `Base: IntoBytes` bound. Unfortunately,
// that would be unsound. Consider the following type:
//
//   #[repr(u8)]
//   enum Base {
//       V0(u8),
//       V1(MaybeUninit<u8>),
//       ...
//       V255(MaybeUninit<u8>),
//   }
//
// Consider combining this with `Overlay` type `u8`. Now consider the following
// sequence:
// - Start with `base = Base::V1(MaybeUninit::uninit())`
// - Overwrite with overlay `0`
// - This results in the bit pattern `0x00` followed by an uninit byte, which is
//   invalid for `Base`
unsafe impl<Overlay, Base> TransmuteOverwrite<Overlay, Initialized, Valid> for Base
where
    Overlay: ?Sized,
    Base: FromBytes + IntoBytes + ?Sized,
{
}

// FIXME(#2354): This seems like a smell - the soundness of this bound has
// nothing to do with `Src` or `Dst` - we're basically just saying `[u8; N]` is
// transmutable into `[u8; N]`.

/// `Initialized<Src> → Initialized<Dst>`
// SAFETY: The validity of `Initialized<T>` is equal to that of `[u8]`. `[u8]`'s
// validity does not depend on a value's length, so any prefix of an
// `Initialized<Src>` is a valid `Initialized<Dst>`.
unsafe impl<Src, Dst> TransmuteFrom<Src, Initialized, Initialized> for Dst
where
    Src: ?Sized,
    Dst: ?Sized,
{
}

/// `Initialized<Overlay> → Initialized<Base>`
// SAFETY: The validity of `Initialized<T>` is equal to that of `[u8]`. `[u8]`'s
// validity does not depend on a value's length, so two `[u8]`s concatenated
// together are also a valid `[u8]`. Thus, an `Initialized<Overlay>`
// concatenated with the `[u8]` suffix of an `Initialized<Base>` is a valid
// `Initialized<Base>`.
unsafe impl<Overlay, Base> TransmuteOverwrite<Overlay, Initialized, Initialized> for Base
where
    Overlay: ?Sized,
    Base: ?Sized,
{
}

// FIXME(#2354): This seems like a smell - the soundness of this bound has
// nothing to do with `Dst` - we're basically just saying that any type is
// transmutable into `MaybeUninit<[u8; N]>`.

/// `V<Src> → Uninit<Dst>`
// SAFETY: A `Dst` with validity `Uninit` permits any byte sequence.
unsafe impl<Src, Dst, V> TransmuteFrom<Src, V, Uninit> for Dst
where
    Src: ?Sized,
    Dst: ?Sized,
    V: Validity,
{
}

/// `V<Overlay> → Uninit<Base>`
// SAFETY: A `Base` with validity `Uninit` permits any byte sequence.
unsafe impl<Overlay, Base, V> TransmuteOverwrite<Overlay, V, Uninit> for Base
where
    Overlay: ?Sized,
    Base: ?Sized,
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

/// `Uninit<Overlay> → Valid<MaybeUninit<Base>>`
// SAFETY: See previous safety comment.
unsafe impl<Overlay, Base> TransmuteOverwrite<Overlay, Uninit, Valid> for MaybeUninit<Base> {}

// SAFETY: `MaybeUninit<T>` has the same size as `T` [1]. Thus, a pointer cast
// preserves address and referent size.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
//   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
//   `T`
unsafe impl<T> SizeFrom<T> for MaybeUninit<T> {
    #[inline(always)]
    fn cast_from_raw(t: PtrInner<'_, T>) -> PtrInner<'_, MaybeUninit<T>> {
        // SAFETY: Per preceding safety comment, `MaybeUninit<T>` and `T` have
        // the same size, and so this cast preserves referent size.
        unsafe { cast!(t) }
    }
}

// SAFETY: See previous safety comment.
unsafe impl<T> SizeFrom<MaybeUninit<T>> for T {
    #[inline(always)]
    fn cast_from_raw(t: PtrInner<'_, MaybeUninit<T>>) -> PtrInner<'_, T> {
        // SAFETY: Per preceding safety comment, `MaybeUninit<T>` and `T` have
        // the same size, and so this cast preserves referent size.
        unsafe { cast!(t) }
    }
}
