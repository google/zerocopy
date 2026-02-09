// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{borrow::Borrow, fmt, hash::Hash};

use super::*;
use crate::pointer::{invariant::Safe, SizeEq, TransmuteFrom};

/// A type with no alignment requirement.
///
/// An `Unalign` wraps a `T`, removing any alignment requirement. `Unalign<T>`
/// has the same size and bit validity as `T`, but not necessarily the same
/// alignment [or ABI]. This is useful if a type with an alignment requirement
/// needs to be read from a chunk of memory which provides no alignment
/// guarantees.
///
/// Since `Unalign` has no alignment requirement, the inner `T` may not be
/// properly aligned in memory. There are five ways to access the inner `T`:
/// - by value, using [`get`] or [`into_inner`]
/// - by reference inside of a callback, using [`update`]
/// - fallibly by reference, using [`try_deref`] or [`try_deref_mut`]; these can
///   fail if the `Unalign` does not satisfy `T`'s alignment requirement at
///   runtime
/// - unsafely by reference, using [`deref_unchecked`] or
///   [`deref_mut_unchecked`]; it is the caller's responsibility to ensure that
///   the `Unalign` satisfies `T`'s alignment requirement
/// - (where `T: Unaligned`) infallibly by reference, using [`Deref::deref`] or
///   [`DerefMut::deref_mut`]
///
/// [or ABI]: https://github.com/google/zerocopy/issues/164
/// [`get`]: Unalign::get
/// [`into_inner`]: Unalign::into_inner
/// [`update`]: Unalign::update
/// [`try_deref`]: Unalign::try_deref
/// [`try_deref_mut`]: Unalign::try_deref_mut
/// [`deref_unchecked`]: Unalign::deref_unchecked
/// [`deref_mut_unchecked`]: Unalign::deref_mut_unchecked
///
/// # Example
///
/// In this example, we need `EthernetFrame` to have no alignment requirement -
/// and thus implement [`Unaligned`]. `EtherType` is `#[repr(u16)]` and so
/// cannot implement `Unaligned`. We use `Unalign` to relax `EtherType`'s
/// alignment requirement so that `EthernetFrame` has no alignment requirement
/// and can implement `Unaligned`.
///
/// ```rust
/// use zerocopy::*;
/// # use zerocopy_derive::*;
/// # #[derive(FromBytes, KnownLayout, Immutable, Unaligned)] #[repr(C)] struct Mac([u8; 6]);
///
/// # #[derive(PartialEq, Copy, Clone, Debug)]
/// #[derive(TryFromBytes, KnownLayout, Immutable)]
/// #[repr(u16)]
/// enum EtherType {
///     Ipv4 = 0x0800u16.to_be(),
///     Arp = 0x0806u16.to_be(),
///     Ipv6 = 0x86DDu16.to_be(),
///     # /*
///     ...
///     # */
/// }
///
/// #[derive(TryFromBytes, KnownLayout, Immutable, Unaligned)]
/// #[repr(C)]
/// struct EthernetFrame {
///     src: Mac,
///     dst: Mac,
///     ethertype: Unalign<EtherType>,
///     payload: [u8],
/// }
///
/// let bytes = &[
///     # 0, 1, 2, 3, 4, 5,
///     # 6, 7, 8, 9, 10, 11,
///     # /*
///     ...
///     # */
///     0x86, 0xDD,            // EtherType
///     0xDE, 0xAD, 0xBE, 0xEF // Payload
/// ][..];
///
/// // PANICS: Guaranteed not to panic because `bytes` is of the right
/// // length, has the right contents, and `EthernetFrame` has no
/// // alignment requirement.
/// let packet = EthernetFrame::try_ref_from_bytes(&bytes).unwrap();
///
/// assert_eq!(packet.ethertype.get(), EtherType::Ipv6);
/// assert_eq!(packet.payload, [0xDE, 0xAD, 0xBE, 0xEF]);
/// ```
///
/// # Safety
///
/// `Unalign<T>` is guaranteed to have the same size and bit validity as `T`,
/// and to have [`UnsafeCell`]s covering the same byte ranges as `T`.
/// It has the same library safety invariants as `T` and alignment 1.
// NOTE: This type is sound to use with types that need to be dropped. The
// reason is that the compiler-generated drop code automatically moves all
// values to aligned memory slots before dropping them in-place. This is not
// well-documented, but it's hinted at in places like [1] and [2]. However, this
// also means that `T` must be `Sized`; unless something changes, we can never
// support unsized `T`. [3]
//
// [1] https://github.com/rust-lang/rust/issues/54148#issuecomment-420529646
// [2] https://github.com/google/zerocopy/pull/126#discussion_r1018512323
// [3] https://github.com/google/zerocopy/issues/209
#[allow(missing_debug_implementations)]
#[derive(Default, Copy)]
#[cfg_attr(any(feature = "derive", test), derive(Immutable, IntoBytes, Unaligned))]
#[repr(C, packed)]
pub struct Unalign<T>(T);

// We do not use `derive(KnownLayout)` on `Unalign`, because the derive is not
// smart enough to realize that `Unalign<T>` is always sized and thus emits a
// `KnownLayout` impl bounded on `T: KnownLayout.` This is overly restrictive.
impl_known_layout!(T => Unalign<T>);

// SAFETY:
// - `Unalign<T>` promises to have alignment 1, and so we don't require that `T:
//   Unaligned`.
// - `Unalign<T>` preserves `T`'s byte range, bit validity and library safety
//   invariants. Thus, zeroed or arbitrary initialized bytes are safe for the
//   wrapper whenever they are safe for `T`, establishing `FromZeros` and
//   `FromBytes`. Its bytes, including padding, are initialized whenever `T`'s
//   are, establishing `IntoBytes`.
// - `Immutable`: `Unalign<T>` has `UnsafeCell`s covering the same byte ranges
//   as `T`, so it permits interior mutation exactly when `T` does.
// - `TryFromBytes`: The candidate cast preserves the byte range and its
//   `Initialized` validity. Both candidate types are wrapped in `ReadOnly`,
//   so the cast's `BecauseImmutable` bound excludes mutation. The cast
//   conservatively supplies `Unaligned` to `T::is_safe`. If that validator
//   returns true, the bytes satisfy `T`'s bit validity and library safety
//   invariants, which are also those of `Unalign<T>`. If it returns false or
//   panics, no referent is moved or dropped and no validity is strengthened.
//
// `FromBytes` and its supertraits are implemented manually in all
// configurations: their derives would generate projections of the wrapper's
// physical field, whereas `Unalign` forwards projections through `T`.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    impl_or_verify!(T => Unaligned for Unalign<T>);
    impl_or_verify!(T: Immutable => Immutable for Unalign<T>);
    unsafe_impl!(
        T: TryFromBytes => TryFromBytes for Unalign<T>;
        // FIXME(#2749): Justify this `Uninit`.
        type Uninit = crate::invariant::Uninit;
        |c| T::is_safe(c.transmute::<_, _, BecauseImmutable>())
    );
    unsafe_impl!(T: FromZeros => FromZeros for Unalign<T>);
    unsafe_impl!(T: FromBytes => FromBytes for Unalign<T>);
    impl_or_verify!(T: IntoBytes => IntoBytes for Unalign<T>);
};

// SAFETY: See the safety comment on `ProjectToTag`.
unsafe impl<T: HasTag<Client, V>, Client, V: invariant::Validity> HasTag<Client, V> for Unalign<T> {
    #[inline]
    fn only_derive_is_allowed_to_implement_this_trait() {}

    type Tag = Unalign<T::Tag>;
    type TagValidity = T::TagValidity;

    // SAFETY: `Unalign<T>` occupies the same bytes as `T`, with the same
    // `UnsafeCell` coverage and library safety invariants. Simple validity
    // therefore agrees, and compound validity agrees by `Validity`'s explicit
    // wrapper rule. The initial cast preserves shared aliasing and validity,
    // while supplying only `Unaligned` for `T`. Its tag projection then
    // supplies a shared, unaligned tag with `T::TagValidity`. Wrapping that
    // tag preserves its byte range and validity by the same argument. The
    // wrapped tag is `Immutable` because `T::Tag` is, and has alignment 1,
    // satisfying either source alignment invariant. These equal validity
    // requirements are preserved by any permitted mutation of the source.
    type ProjectToTag = crate::pointer::cast::TransitiveProject<
        T,
        crate::pointer::cast::CastSized,
        crate::pointer::cast::TransitiveProject<
            T::Tag,
            T::ProjectToTag,
            crate::pointer::cast::CastSized,
        >,
    >;
}

// SAFETY: `HasField` defines `Unalign<T>`'s fields to be the projections of
// `T`, wrapped in `Unalign`. The identifiers and visibility are inherited
// through the bound on `T`. Both casts preserve address, byte range, and
// provenance; the intervening field projection preserves provenance and
// selects a subset of the source bytes by `T: HasField`.
unsafe impl<T, Client, Field, const VARIANT_ID: i128, const FIELD_ID: i128>
    HasField<Client, Field, VARIANT_ID, FIELD_ID> for Unalign<T>
where
    T: HasField<Client, Field, VARIANT_ID, FIELD_ID>,
    T::Type: Sized,
{
    #[inline]
    fn only_derive_is_allowed_to_implement_this_trait() {}

    type Type = Unalign<T::Type>;

    #[inline(always)]
    fn project(slf: PtrInner<'_, Self>) -> *mut Self::Type {
        use crate::pointer::cast::{CastSized, Projection};

        slf.project::<T, CastSized>()
            .project::<_, Projection<Client, Field, VARIANT_ID, FIELD_ID>>()
            .project::<_, CastSized>()
            .as_ptr()
    }
}

// SAFETY: The wrapper preserves the inner type's byte range, `UnsafeCell`
// coverage, and validity requirements, including compound validity. Treating
// the source as an unaligned `T` therefore preserves aliasing and validity.
// The delegated tag check establishes the precondition of `T: ProjectField`,
// which supplies the field's aliasing and validity, including preservation
// under mutation. Wrapping that field preserves both, and alignment 1 makes
// the resulting pointer `Aligned` regardless of the inner field's alignment.
unsafe impl<T, Client, Field, I, const VARIANT_ID: i128, const FIELD_ID: i128>
    ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID> for Unalign<T>
where
    I: invariant::Invariants,
    T: ProjectField<
        Client,
        Field,
        (I::Aliasing, invariant::Unaligned, I::Validity),
        VARIANT_ID,
        FIELD_ID,
    >,
    T::Type: Sized,
{
    #[inline]
    fn only_derive_is_allowed_to_implement_this_trait() {}

    type Invariants =
        (I::Aliasing, invariant::Aligned, <T::Invariants as invariant::Invariants>::Validity);

    type Error = T::Error;

    #[inline(always)]
    fn is_projectable<'a>(
        ptr: Ptr<
            'a,
            <Self as HasTag<Client, I::Validity>>::Tag,
            (invariant::Shared, I::Alignment, <Self as HasTag<Client, I::Validity>>::TagValidity),
        >,
    ) -> Result<(), Self::Error> {
        // SAFETY: Removing `Unalign` preserves the tag's byte range and
        // validity. Both tag types are `Immutable`, so shared access permits
        // no mutation. The cast returns an `Unaligned` pointer as required by
        // the underlying projection; it does not assume the tag is aligned.
        let ptr =
            unsafe { ptr.project_transmute_unchecked::<_, _, crate::pointer::cast::CastSized>() };
        T::is_projectable(ptr)
    }
}

// Note that `Unalign: Clone` only if `T: Copy`. Since the inner `T` may not be
// aligned, there's no way to safely call `T::clone`, and so a `T: Clone` bound
// is not sufficient to implement `Clone` for `Unalign`.
impl<T: Copy> Clone for Unalign<T> {
    #[inline(always)]
    fn clone(&self) -> Unalign<T> {
        *self
    }
}

impl<T> Unalign<T> {
    /// Constructs a new `Unalign`.
    #[inline(always)]
    pub const fn new(val: T) -> Unalign<T> {
        Unalign(val)
    }

    /// Consumes `self`, returning the inner `T`.
    #[inline(always)]
    pub const fn into_inner(self) -> T {
        // SAFETY: Since `Unalign` is `#[repr(C, packed)]`, it has the same size
        // and bit validity as `T`.
        //
        // We do this instead of just destructuring in order to prevent
        // `Unalign`'s `Drop::drop` from being run, since dropping is not
        // supported in `const fn`s.
        //
        // FIXME(https://github.com/rust-lang/rust/issues/73255): Destructure
        // instead of using unsafe.
        unsafe { crate::util::transmute_unchecked(self) }
    }

    /// Attempts to return a reference to the wrapped `T`, failing if `self` is
    /// not properly aligned.
    ///
    /// If `self` does not satisfy `align_of::<T>()`, then `try_deref` returns
    /// `Err`.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements [`Deref`], and callers
    /// may prefer [`Deref::deref`], which is infallible.
    #[inline(always)]
    pub fn try_deref(&self) -> Result<&T, AlignmentError<&Self, T>> {
        let inner = Ptr::from_ref(self).transmute();
        match inner.try_into_aligned() {
            Ok(aligned) => Ok(aligned.as_ref()),
            Err(err) => Err(err.map_src(
                #[inline(always)]
                |src| src.into_unalign().as_ref(),
            )),
        }
    }

    /// Attempts to return a mutable reference to the wrapped `T`, failing if
    /// `self` is not properly aligned.
    ///
    /// If `self` does not satisfy `align_of::<T>()`, then `try_deref` returns
    /// `Err`.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements [`DerefMut`], and
    /// callers may prefer [`DerefMut::deref_mut`], which is infallible.
    #[inline(always)]
    pub fn try_deref_mut(&mut self) -> Result<&mut T, AlignmentError<&mut Self, T>> {
        let inner = Ptr::from_mut(self).transmute::<_, _, (_, (_, _))>();
        match inner.try_into_aligned() {
            Ok(aligned) => Ok(aligned.as_mut()),
            Err(err) => Err(err.map_src(|src| src.into_unalign().as_mut())),
        }
    }

    /// Returns a reference to the wrapped `T` without checking alignment.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements[ `Deref`], and callers
    /// may prefer [`Deref::deref`], which is safe.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `self` satisfies `align_of::<T>()`.
    #[inline(always)]
    pub const unsafe fn deref_unchecked(&self) -> &T {
        // SAFETY: `Unalign<T>` is `repr(transparent)`, so there is a valid `T`
        // at the same memory location as `self`. It has no alignment guarantee,
        // but the caller has promised that `self` is properly aligned, so we
        // know that it is sound to create a reference to `T` at this memory
        // location.
        //
        // We use `mem::transmute` instead of `&*self.get_ptr()` because
        // dereferencing pointers is not stable in `const` on our current MSRV
        // (1.56 as of this writing).
        unsafe { mem::transmute(self) }
    }

    /// Returns a mutable reference to the wrapped `T` without checking
    /// alignment.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements[ `DerefMut`], and
    /// callers may prefer [`DerefMut::deref_mut`], which is safe.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `self` satisfies `align_of::<T>()`.
    #[inline(always)]
    pub unsafe fn deref_mut_unchecked(&mut self) -> &mut T {
        // SAFETY: `self.get_mut_ptr()` returns a raw pointer to a valid `T` at
        // the same memory location as `self`. It has no alignment guarantee,
        // but the caller has promised that `self` is properly aligned, so we
        // know that the pointer itself is aligned, and thus that it is sound to
        // create a reference to a `T` at this memory location.
        unsafe { &mut *self.get_mut_ptr() }
    }

    /// Gets an unaligned raw pointer to the inner `T`.
    ///
    /// # Safety
    ///
    /// The returned raw pointer is not necessarily aligned to
    /// `align_of::<T>()`. Most functions which operate on raw pointers require
    /// those pointers to be aligned, so calling those functions with the result
    /// of `get_ptr` will result in undefined behavior if alignment is not
    /// guaranteed using some out-of-band mechanism. In general, the only
    /// functions which are safe to call with this pointer are those which are
    /// explicitly documented as being sound to use with an unaligned pointer,
    /// such as [`read_unaligned`].
    ///
    /// Even if the caller is permitted to mutate `self` (e.g. they have
    /// ownership or a mutable borrow), it is not guaranteed to be sound to
    /// write through the returned pointer. If writing is required, prefer
    /// [`get_mut_ptr`] instead.
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
    /// [`get_mut_ptr`]: Unalign::get_mut_ptr
    #[inline(always)]
    pub const fn get_ptr(&self) -> *const T {
        ptr::addr_of!(self.0)
    }

    /// Gets an unaligned mutable raw pointer to the inner `T`.
    ///
    /// # Safety
    ///
    /// The returned raw pointer is not necessarily aligned to
    /// `align_of::<T>()`. Most functions which operate on raw pointers require
    /// those pointers to be aligned, so calling those functions with the result
    /// of `get_ptr` will result in undefined behavior if alignment is not
    /// guaranteed using some out-of-band mechanism. In general, the only
    /// functions which are safe to call with this pointer are those which are
    /// explicitly documented as being sound to use with an unaligned pointer,
    /// such as [`read_unaligned`].
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
    // FIXME(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
    #[inline(always)]
    pub fn get_mut_ptr(&mut self) -> *mut T {
        ptr::addr_of_mut!(self.0)
    }

    /// Sets the inner `T`, dropping the previous value.
    // FIXME(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
    #[inline(always)]
    pub fn set(&mut self, t: T) {
        *self = Unalign::new(t);
    }

    /// Updates the inner `T` by calling a function on it.
    ///
    /// If [`T: Unaligned`], then `Unalign<T>` implements [`DerefMut`], and that
    /// impl should be preferred over this method when performing updates, as it
    /// will usually be faster and more ergonomic.
    ///
    /// For large types, this method may be expensive, as it requires copying
    /// `2 * size_of::<T>()` bytes. \[1\]
    ///
    /// \[1\] Since the inner `T` may not be aligned, it would not be sound to
    /// invoke `f` on it directly. Instead, `update` moves it into a
    /// properly-aligned location in the local stack frame, calls `f` on it, and
    /// then moves it back to its original location in `self`.
    ///
    /// [`T: Unaligned`]: Unaligned
    #[inline]
    pub fn update<O, F: FnOnce(&mut T) -> O>(&mut self, f: F) -> O {
        if mem::align_of::<T>() == 1 {
            // While we advise callers to use `DerefMut` when `T: Unaligned`,
            // not all callers will be able to guarantee `T: Unaligned` in all
            // cases. In particular, callers who are themselves providing an API
            // which is generic over `T` may sometimes be called by *their*
            // callers with `T` such that `align_of::<T>() == 1`, but cannot
            // guarantee this in the general case. Thus, this optimization may
            // sometimes be helpful.

            // SAFETY: Since `T`'s alignment is 1, `self` satisfies its
            // alignment by definition.
            let t = unsafe { self.deref_mut_unchecked() };
            return f(t);
        }

        // On drop, this moves `copy` out of itself and uses `ptr::write` to
        // overwrite `slf`.
        struct WriteBackOnDrop<T> {
            copy: ManuallyDrop<T>,
            slf: *mut Unalign<T>,
        }

        impl<T> Drop for WriteBackOnDrop<T> {
            fn drop(&mut self) {
                // SAFETY: We never use `copy` again as required by
                // `ManuallyDrop::take`.
                let copy = unsafe { ManuallyDrop::take(&mut self.copy) };
                // SAFETY: `slf` is the raw pointer value of `self`. We know it
                // is valid for writes and properly aligned because `self` is a
                // mutable reference, which guarantees both of these properties.
                unsafe { ptr::write(self.slf, Unalign::new(copy)) };
            }
        }

        // SAFETY: We know that `self` is valid for reads, properly aligned, and
        // points to an initialized `Unalign<T>` because it is a mutable
        // reference, which guarantees all of these properties.
        //
        // Since `T: !Copy`, it would be unsound in the general case to allow
        // both the original `Unalign<T>` and the copy to be used by safe code.
        // We guarantee that the copy is used to overwrite the original in the
        // `Drop::drop` impl of `WriteBackOnDrop`. So long as this `drop` is
        // called before any other safe code executes, soundness is upheld.
        // While this method can terminate in two ways (by returning normally or
        // by unwinding due to a panic in `f`), in both cases, `write_back` is
        // dropped - and its `drop` called - before any other safe code can
        // execute.
        let copy = unsafe { ptr::read(self) }.into_inner();
        let mut write_back = WriteBackOnDrop { copy: ManuallyDrop::new(copy), slf: self };

        let ret = f(&mut write_back.copy);

        drop(write_back);
        ret
    }
}

impl<T: Copy> Unalign<T> {
    /// Gets a copy of the inner `T`.
    // FIXME(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
    #[inline(always)]
    pub fn get(&self) -> T {
        let Unalign(val) = *self;
        val
    }
}

impl<T: Unaligned> Deref for Unalign<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        Ptr::from_ref(self).transmute().bikeshed_recall_aligned().as_ref()
    }
}

impl<T: Unaligned> DerefMut for Unalign<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        Ptr::from_mut(self).transmute::<_, _, (_, (_, _))>().bikeshed_recall_aligned().as_mut()
    }
}

impl<T: Unaligned + PartialOrd> PartialOrd<Unalign<T>> for Unalign<T> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Unalign<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(self.deref(), other.deref())
    }
}

impl<T: Unaligned + Ord> Ord for Unalign<T> {
    #[inline(always)]
    fn cmp(&self, other: &Unalign<T>) -> Ordering {
        Ord::cmp(self.deref(), other.deref())
    }
}

impl<T: Unaligned + PartialEq> PartialEq<Unalign<T>> for Unalign<T> {
    #[inline(always)]
    fn eq(&self, other: &Unalign<T>) -> bool {
        PartialEq::eq(self.deref(), other.deref())
    }
}

impl<T: Unaligned + Eq> Eq for Unalign<T> {}

impl<T: Unaligned + Hash> Hash for Unalign<T> {
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.deref().hash(state);
    }
}

impl<T: Unaligned + Debug> Debug for Unalign<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.deref(), f)
    }
}

impl<T: Unaligned + Display> Display for Unalign<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

/// A wrapper type to construct uninitialized instances of `T`.
///
/// `MaybeUninit` is identical to the [standard library
/// `MaybeUninit`][core-maybe-uninit] type except that it supports unsized
/// types.
///
/// # Layout
///
/// The same layout guarantees and caveats apply to `MaybeUninit<T>` as apply to
/// the [standard library `MaybeUninit`][core-maybe-uninit] with one exception:
/// for `T: !Sized`, there is no single value for `T`'s size. Instead, for such
/// types, the following are guaranteed:
/// - Every [valid size][valid-size] for `T` is a valid size for
///   `MaybeUninit<T>` and vice versa
/// - Given `t: *const T` and `m: *const MaybeUninit<T>` with identical fat
///   pointer metadata, `t` and `m` address the same number of bytes (and
///   likewise for `*mut`)
///
/// [core-maybe-uninit]: core::mem::MaybeUninit
/// [valid-size]: crate::KnownLayout#what-is-a-valid-size
#[repr(transparent)]
#[doc(hidden)]
pub struct MaybeUninit<T: ?Sized + KnownLayout>(
    // SAFETY: `MaybeUninit<T>` has the same size as `T`, because (by invariant
    // on `T::MaybeUninit`) `T::MaybeUninit` has `T::LAYOUT` identical to `T`,
    // and because (invariant on `T::LAYOUT`) we can trust that `LAYOUT`
    // accurately reflects the layout of `T`. By invariant on `T::MaybeUninit`,
    // it admits uninitialized bytes in all positions. Because `MaybeUninit` is
    // marked `repr(transparent)`, these properties additionally hold true for
    // `Self`.
    T::MaybeUninit,
);

#[doc(hidden)]
impl<T: ?Sized + KnownLayout> MaybeUninit<T> {
    /// Constructs a `MaybeUninit<T>` initialized with the given value.
    #[inline(always)]
    pub fn new(val: T) -> Self
    where
        T: Sized,
        Self: Sized,
    {
        // SAFETY: It is valid to transmute `val` to `MaybeUninit<T>` because it
        // is both valid to transmute `val` to `T::MaybeUninit`, and it is valid
        // to transmute from `T::MaybeUninit` to `MaybeUninit<T>`.
        //
        // First, it is valid to transmute `val` to `T::MaybeUninit` because, by
        // invariant on `T::MaybeUninit`:
        // - For `T: Sized`, `T` and `T::MaybeUninit` have the same size.
        // - All byte sequences of the correct size are valid values of
        //   `T::MaybeUninit`.
        //
        // Second, it is additionally valid to transmute from `T::MaybeUninit`
        // to `MaybeUninit<T>`, because `MaybeUninit<T>` is a
        // `repr(transparent)` wrapper around `T::MaybeUninit`.
        //
        // These two transmutes are collapsed into one so we don't need to add a
        // `T::MaybeUninit: Sized` bound to this function's `where` clause.
        unsafe { crate::util::transmute_unchecked(val) }
    }

    /// Constructs an uninitialized `MaybeUninit<T>`.
    #[must_use]
    #[inline(always)]
    pub fn uninit() -> Self
    where
        T: Sized,
        Self: Sized,
    {
        let uninit = CoreMaybeUninit::<T>::uninit();
        // SAFETY: It is valid to transmute from `CoreMaybeUninit<T>` to
        // `MaybeUninit<T>` since they both admit uninitialized bytes in all
        // positions, and they have the same size (i.e., that of `T`).
        //
        // `MaybeUninit<T>` has the same size as `T`, because (by invariant on
        // `T::MaybeUninit`) `T::MaybeUninit` has `T::LAYOUT` identical to `T`,
        // and because (invariant on `T::LAYOUT`) we can trust that `LAYOUT`
        // accurately reflects the layout of `T`.
        //
        // `CoreMaybeUninit<T>` has the same size as `T` [1] and admits
        // uninitialized bytes in all positions.
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
        //
        //   `MaybeUninit<T>` is guaranteed to have the same size, alignment,
        //   and ABI as `T`
        unsafe { crate::util::transmute_unchecked(uninit) }
    }

    /// Creates a `Box<MaybeUninit<T>>`.
    ///
    /// This function is useful for allocating large, uninit values on the heap
    /// without ever creating a temporary instance of `Self` on the stack.
    ///
    /// # Errors
    ///
    /// Returns an error on allocation failure. Allocation failure is guaranteed
    /// never to cause a panic or an abort.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn new_boxed_uninit(meta: T::PointerMetadata) -> Result<Box<Self>, AllocError> {
        // SAFETY: `alloc::alloc::alloc_zeroed` is a valid argument of
        // `new_box`. The referent of the pointer returned by `alloc` (and,
        // consequently, the `Box` derived from it) is a valid instance of
        // `Self`, because `Self` is `MaybeUninit` and thus admits arbitrary
        // (un)initialized bytes.
        unsafe { crate::util::new_box(meta, alloc::alloc::alloc) }
    }

    /// Extracts the value from the `MaybeUninit<T>` container.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `self` is in an bit-valid state. Depending
    /// on subsequent use, it may also need to be in a library-valid state.
    #[inline(always)]
    pub unsafe fn assume_init(self) -> T
    where
        T: Sized,
        Self: Sized,
    {
        // SAFETY: The caller guarantees that `self` is in an bit-valid state.
        unsafe { crate::util::transmute_unchecked(self) }
    }
}

impl<T: ?Sized + KnownLayout> fmt::Debug for MaybeUninit<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad(core::any::type_name::<Self>())
    }
}

#[allow(unreachable_pub)] // False positive on MSRV
#[doc(hidden)]
pub use read_only_def::*;
mod read_only_def {
    /// A read-only wrapper.
    ///
    /// A `ReadOnly<T>` disables any interior mutability in `T`, ensuring that
    /// a `&ReadOnly<T>` is genuinely read-only. Thus, `ReadOnly<T>` is
    /// [`Immutable`] regardless of whether `T` is.
    ///
    /// Note that `&mut ReadOnly<T>` still permits mutation – the read-only
    /// property only applies to shared references.
    ///
    /// `ReadOnly<T>` implements [`Copy`] and [`Clone`] when `T: Copy`. Cloning
    /// copies the value without calling `T::clone`. Trait implementations that
    /// expose or operate on a shared reference to `T` require `T: Immutable`.
    /// Constructing a wrapper or accessing its contents through [`AsMut`]
    /// does not require `T: Immutable`.
    ///
    /// [`Immutable`]: crate::Immutable
    #[derive(Copy)]
    #[repr(transparent)]
    pub struct ReadOnly<T: ?Sized> {
        // INVARIANT: `inner` is never mutated through a `&ReadOnly<T>`
        // reference.
        inner: T,
    }

    impl<T> ReadOnly<T> {
        /// Creates a new `ReadOnly`.
        #[must_use]
        #[inline(always)]
        pub const fn new(t: T) -> ReadOnly<T> {
            ReadOnly { inner: t }
        }

        /// Returns the inner value.
        #[must_use]
        #[inline(always)]
        pub fn into_inner(r: ReadOnly<T>) -> T {
            r.inner
        }
    }

    impl<T: ?Sized> ReadOnly<T> {
        #[inline(always)]
        pub(crate) fn as_mut(r: &mut ReadOnly<T>) -> &mut T {
            // SAFETY: `r: &mut ReadOnly`, so this doesn't violate the invariant
            // that `inner` is never mutated through a `&ReadOnly<T>` reference.
            &mut r.inner
        }

        /// # Safety
        ///
        /// The caller promises not to mutate the referent (i.e., via interior
        /// mutation).
        pub(crate) const unsafe fn as_ref_unchecked(r: &ReadOnly<T>) -> &T {
            // SAFETY: The caller promises not to mutate the referent.
            &r.inner
        }
    }
}

// SAFETY: `ReadOnly<T>` is a `#[repr(transparent)` wrapper around `T`.
const _: () = unsafe {
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(T)] ReadOnly<T>);
};

#[allow(clippy::multiple_unsafe_ops_per_block)]
// SAFETY:
// - `ReadOnly<T>` has the same alignment as `T`, and so it is `Unaligned`
//   exactly when `T` is as well.
// - `ReadOnly<T>` has the same bit validity as `T`, and so this `is_safe`
//   implementation is correct, and thus the `TryFromBytes` impl is sound.
// - `ReadOnly<T>` has the same bit validity as `T`, and so it is `FromZeros`,
//   `FromBytes`, and `IntoBytes` exactly when `T` is as well.
const _: () = unsafe {
    unsafe_impl!(T: ?Sized + Unaligned => Unaligned for ReadOnly<T>);
    unsafe_impl!(
        T: ?Sized + TryFromBytes => TryFromBytes for ReadOnly<T>;
        // FIXME(#2749): Justify this `Uninit`.
        type Uninit = crate::invariant::Uninit;
        |c| T::is_safe(c.cast::<_, <ReadOnly<T> as SizeEq<ReadOnly<ReadOnly<T>>>>::CastFrom, _>())
    );
    unsafe_impl!(T: ?Sized + FromZeros => FromZeros for ReadOnly<T>);
    unsafe_impl!(T: ?Sized + FromBytes => FromBytes for ReadOnly<T>);
    unsafe_impl!(T: ?Sized + IntoBytes => IntoBytes for ReadOnly<T>);
};

// SAFETY: By invariant, `inner` is never mutated through a `&ReadOnly<T>`
// reference.
const _: () = unsafe {
    unsafe_impl!(T: ?Sized => Immutable for ReadOnly<T>);
};

const _: () = {
    use crate::pointer::cast::CastExact;

    // SAFETY: `ReadOnly<T>` has the same layout as `T`.
    define_cast!(unsafe { pub CastFromReadOnly<T: ?Sized> = ReadOnly<T> => T});
    // SAFETY: `ReadOnly<T>` has the same layout as `T`.
    unsafe impl<T: ?Sized> CastExact<ReadOnly<T>, T> for CastFromReadOnly {}
    // SAFETY: `ReadOnly<T>` has the same layout as `T`.
    define_cast!(unsafe { pub CastToReadOnly<T: ?Sized> = T => ReadOnly<T>});
    // SAFETY: `ReadOnly<T>` has the same layout as `T`.
    unsafe impl<T: ?Sized> CastExact<T, ReadOnly<T>> for CastToReadOnly {}

    impl<T: ?Sized> SizeEq<ReadOnly<T>> for T {
        type CastFrom = CastFromReadOnly;
    }

    impl<T: ?Sized> SizeEq<T> for ReadOnly<T> {
        type CastFrom = CastToReadOnly;
    }
};

// SAFETY: `ReadOnly<T>` has only its `T` field, with the same layout and bit
// validity. Its value must satisfy `T`'s library safety invariants, since safe
// exclusive access exposes that field. Conversely, exclusive access permits
// any mutation preserving those invariants. The wrapper's additional invariant
// forbids mutation through shared access; it does not constrain the value.
// `TransmuteFrom` establishes only validity, leaving that access restriction
// to the pointer conversion's separate aliasing proof.
unsafe impl<T: ?Sized> TransmuteFrom<T, Safe, Safe> for ReadOnly<T> {}

// SAFETY: The preceding argument establishes equal validity requirements in
// both directions.
unsafe impl<T: ?Sized> TransmuteFrom<ReadOnly<T>, Safe, Safe> for T {}

impl<T: Default> Default for ReadOnly<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

// Copying avoids calling `T::clone`, which could mutate through a shared
// reference to `T` and violate `ReadOnly`'s invariant.
impl<T: Copy> Clone for ReadOnly<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> From<T> for ReadOnly<T> {
    #[inline(always)]
    fn from(t: T) -> Self {
        Self::new(t)
    }
}

impl<'a, T: ?Sized + Immutable> From<&'a T> for &'a ReadOnly<T> {
    #[inline(always)]
    fn from(t: &'a T) -> &'a ReadOnly<T> {
        let ro = Ptr::from_ref(t).transmute::<_, _, (_, _)>();
        // SAFETY: `ReadOnly<T>` has the same alignment as `T`, and
        // `Ptr::from_ref` produces an aligned `Ptr`.
        let ro = unsafe { ro.assume_alignment() };
        ro.as_ref()
    }
}

impl<T: ?Sized + Immutable> Deref for ReadOnly<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        // SAFETY: By `T: Immutable`, `&T` doesn't permit interior mutation.
        unsafe { ReadOnly::as_ref_unchecked(self) }
    }
}

impl<T: ?Sized + Immutable> DerefMut for ReadOnly<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        ReadOnly::as_mut(self)
    }
}

impl<T: ?Sized + Immutable> AsRef<T> for ReadOnly<T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized + Immutable> Borrow<T> for ReadOnly<T> {
    #[inline(always)]
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T: ?Sized> AsMut<T> for ReadOnly<T> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        ReadOnly::as_mut(self)
    }
}

// Delegate shared access through `Deref`, which requires `T: Immutable` and
// thus prevents interior mutation of the wrapped value by these trait methods.
impl<T: ?Sized + Immutable + PartialEq> PartialEq for ReadOnly<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T: ?Sized + Immutable + Eq> Eq for ReadOnly<T> {}

impl<T: ?Sized + Immutable + PartialOrd> PartialOrd for ReadOnly<T> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

impl<T: ?Sized + Immutable + Ord> Ord for ReadOnly<T> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<T: ?Sized + Immutable + Hash> Hash for ReadOnly<T> {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

macro_rules! impl_read_only_fmt {
    ($($trait:ident),* $(,)?) => {$(
        impl<T: ?Sized + Immutable + fmt::$trait> fmt::$trait for ReadOnly<T> {
            #[inline(always)]
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                fmt::$trait::fmt(self.deref(), f)
            }
        }
    )*};
}

impl_read_only_fmt!(Debug, Display, Binary, Octal, LowerHex, UpperHex, LowerExp, UpperExp);

// SAFETY: See safety comment on `ProjectToTag`.
unsafe impl<T: HasTag<Client, V> + ?Sized, Client, V: invariant::Validity> HasTag<Client, V>
    for ReadOnly<T>
{
    #[allow(clippy::missing_inline_in_public_items)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }

    type Tag = <T as HasTag<Client, V>>::Tag;
    type TagValidity = <T as HasTag<Client, V>>::TagValidity;

    // SAFETY: `ReadOnly<T>` has the same layout as `T`. Simple validity has
    // the same initialization and bit-validity requirements; `Safe` also
    // retains `T`'s library safety invariants. Compound validity is inherited
    // from `T` by `Validity`'s explicit wrapper rule. Shared access through
    // the wrapper prohibits mutation, so the no-op `CastFrom` preserves
    // alignment, shared aliasing, and `V` for the inner `T`. Its tag-projection
    // guarantee supplies `Tag` and `TagValidity`. The tag is `Immutable`, so
    // projecting it does not grant mutation of the shared `ReadOnly` source.
    type ProjectToTag = crate::pointer::cast::TransitiveProject<
        T,
        <T as SizeEq<ReadOnly<T>>>::CastFrom,
        <T as HasTag<Client, V>>::ProjectToTag,
    >;
}

// SAFETY: `HasField` defines `ReadOnly<T>`'s fields to be the projections of
// `T`, wrapped in `ReadOnly`. The identifiers and visibility are inherited
// through the bound on `T`. Both casts preserve address, metadata, byte range,
// and provenance; the intervening field projection preserves provenance and
// selects a subset of the source bytes by `T: HasField`.
unsafe impl<T, Client, Field, const VARIANT_ID: i128, const FIELD_ID: i128>
    HasField<Client, Field, VARIANT_ID, FIELD_ID> for ReadOnly<T>
where
    T: HasField<Client, Field, VARIANT_ID, FIELD_ID> + ?Sized,
{
    #[allow(clippy::missing_inline_in_public_items)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }

    type Type = ReadOnly<T::Type>;

    #[inline(always)]
    fn project(slf: PtrInner<'_, Self>) -> *mut ReadOnly<T::Type> {
        slf.project::<_, <T as SizeEq<ReadOnly<T>>>::CastFrom>()
            .project::<_, crate::pointer::cast::Projection<Client, Field, VARIANT_ID, FIELD_ID>>()
            .project::<_, <ReadOnly<T::Type> as SizeEq<T::Type>>::CastFrom>()
            .as_non_null()
            .as_ptr()
    }
}

// SAFETY: `ReadOnly<T>` has the same layout as `T`. Simple validity preserves
// the inner type's initialization, bit validity, and library safety
// requirements; compound validity is inherited from `T` by `Validity`'s
// wrapper rule. The tag check is delegated unchanged, so `T: ProjectField`
// supplies the projected field's alignment, aliasing, and validity. Wrapping
// that field preserves alignment and validity and prevents shared mutation,
// retaining the source wrapper's restriction. Exclusive mutation is allowed
// and preserves source validity by `T`'s projection guarantee. This reasoning
// applies recursively when either validity is compound.
unsafe impl<T, Client, Field, I, const VARIANT_ID: i128, const FIELD_ID: i128>
    ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID> for ReadOnly<T>
where
    T: ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID> + ?Sized,
    I: invariant::Invariants,
{
    #[allow(clippy::missing_inline_in_public_items)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }

    type Invariants = <T as ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID>>::Invariants;

    type Error = <T as ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID>>::Error;

    #[inline(always)]
    fn is_projectable<'a>(
        ptr: Ptr<
            'a,
            <Self as HasTag<Client, I::Validity>>::Tag,
            (invariant::Shared, I::Alignment, <Self as HasTag<Client, I::Validity>>::TagValidity),
        >,
    ) -> Result<(), Self::Error> {
        <T as ProjectField<Client, Field, I, VARIANT_ID, FIELD_ID>>::is_projectable(ptr)
    }
}

#[cfg(test)]
mod tests {
    use core::panic::AssertUnwindSafe;

    use super::*;
    use crate::util::testutil::*;

    #[test]
    #[allow(clippy::clone_on_copy, clippy::non_canonical_clone_impl)]
    fn test_read_only_copy_clone() {
        // This type deliberately does not implement `Immutable`. Copying the
        // wrapper must not require it or invoke the inner `Clone` impl.
        #[derive(Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        struct PanickingClone(u16);

        impl Clone for PanickingClone {
            fn clone(&self) -> Self {
                panic!("ReadOnly must not call the inner Clone implementation")
            }
        }

        static_assertions::assert_not_impl_any!(
            ReadOnly<PanickingClone>: Debug, PartialEq, Eq, PartialOrd, Ord,
            Hash, AsRef<PanickingClone>, Borrow<PanickingClone>
        );
        static_assertions::assert_not_impl_any!(
            ReadOnly<Cell<u8>>: Copy, Clone, Deref, AsRef<Cell<u8>>, Borrow<Cell<u8>>
        );

        let value = ReadOnly::new(PanickingClone(42));
        let copy = value;
        let clone = value.clone();
        assert_eq!(ReadOnly::into_inner(copy).0, 42);
        assert_eq!(ReadOnly::into_inner(clone).0, 42);
    }

    #[test]
    fn test_read_only_mutable_access() {
        // Construction and exclusive access also support interior mutability.
        let mut value = ReadOnly::<Cell<u8>>::default();
        let inner: &mut Cell<u8> = value.as_mut();
        inner.set(42);
        assert_eq!(ReadOnly::into_inner(value).get(), 42);

        let value = ReadOnly::from(Cell::new(7));
        assert_eq!(ReadOnly::into_inner(value).get(), 7);
    }

    #[test]
    fn test_read_only_borrowed_lookup() {
        // Borrowed lookups require equality, hashing, and ordering to agree
        // between the wrapper and the inner value.
        let mut hash_map = std::collections::HashMap::new();
        hash_map.insert(ReadOnly::new(42u16), true);
        assert_eq!(hash_map.get(&42u16), Some(&true));
        assert_eq!(hash_map.get(&43u16), None);

        let mut tree = std::collections::BTreeMap::new();
        tree.insert(ReadOnly::new(42u16), true);
        assert_eq!(tree.get(&42u16), Some(&true));
        assert_eq!(tree.get(&43u16), None);

        // Preserve partial orders, including incomparable values.
        let nan = ReadOnly::new(f32::NAN);
        assert_eq!(nan.partial_cmp(&nan), None);
        assert_ne!(nan, nan);
    }

    #[test]
    fn test_read_only_unsized() {
        let bytes = [1u8, 2];
        let value: &ReadOnly<[u8]> = (&bytes[..]).into();
        let as_ref: &[u8] = value.as_ref();
        let borrowed: &[u8] = value.borrow();
        assert_eq!(as_ref, bytes);
        assert_eq!(borrowed, bytes);
        assert_eq!(value, value);
        assert_eq!(value.cmp(value), Ordering::Equal);

        let text: &ReadOnly<str> = "hello".into();
        assert_eq!(format!("{:.3}", text), "hel");
    }

    #[test]
    fn test_read_only_formatting() {
        let value = ReadOnly::new(42u16);
        // Check that formatting flags are forwarded as well as the value.
        assert_eq!(format!("{:04?}", value), "0042");
        assert_eq!(format!("{:04}", value), "0042");
        assert_eq!(format!("{:#010b}", value), "0b00101010");
        assert_eq!(format!("{:#06o}", value), "0o0052");
        assert_eq!(format!("{:#06x}", value), "0x002a");
        assert_eq!(format!("{:#06X}", value), "0x002A");
        assert_eq!(format!("{:.2e}", value), "4.20e1");
        assert_eq!(format!("{:.2E}", value), "4.20E1");
    }

    #[test]
    fn test_unalign() {
        // Test methods that don't depend on alignment.
        let mut u = Unalign::new(AU64(123));
        assert_eq!(u.get(), AU64(123));
        assert_eq!(u.into_inner(), AU64(123));
        assert_eq!(u.get_ptr(), <*const _>::cast::<AU64>(&u));
        assert_eq!(u.get_mut_ptr(), <*mut _>::cast::<AU64>(&mut u));
        u.set(AU64(321));
        assert_eq!(u.get(), AU64(321));

        // Test methods that depend on alignment (when alignment is satisfied).
        let mut u: Align<_, AU64> = Align::new(Unalign::new(AU64(123)));
        assert_eq!(u.t.try_deref().unwrap(), &AU64(123));
        assert_eq!(u.t.try_deref_mut().unwrap(), &mut AU64(123));
        // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
        assert_eq!(unsafe { u.t.deref_unchecked() }, &AU64(123));
        // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
        assert_eq!(unsafe { u.t.deref_mut_unchecked() }, &mut AU64(123));
        *u.t.try_deref_mut().unwrap() = AU64(321);
        assert_eq!(u.t.get(), AU64(321));

        // Test methods that depend on alignment (when alignment is not
        // satisfied).
        let mut u: ForceUnalign<_, AU64> = ForceUnalign::new(Unalign::new(AU64(123)));
        assert!(matches!(u.t.try_deref(), Err(AlignmentError { .. })));
        assert!(matches!(u.t.try_deref_mut(), Err(AlignmentError { .. })));

        // Test methods that depend on `T: Unaligned`.
        let mut u = Unalign::new(123u8);
        assert_eq!(u.try_deref(), Ok(&123));
        assert_eq!(u.try_deref_mut(), Ok(&mut 123));
        assert_eq!(u.deref(), &123);
        assert_eq!(u.deref_mut(), &mut 123);
        *u = 21;
        assert_eq!(u.get(), 21);

        // Test that some `Unalign` functions and methods are `const`.
        const _UNALIGN: Unalign<u64> = Unalign::new(0);
        const _UNALIGN_PTR: *const u64 = _UNALIGN.get_ptr();
        const _U64: u64 = _UNALIGN.into_inner();
        // Make sure all code is considered "used".
        //
        // FIXME(https://github.com/rust-lang/rust/issues/104084): Remove this
        // attribute.
        #[allow(dead_code)]
        const _: () = {
            let x: Align<_, AU64> = Align::new(Unalign::new(AU64(123)));
            // Make sure that `deref_unchecked` is `const`.
            //
            // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
            let au64 = unsafe { x.t.deref_unchecked() };
            match au64 {
                AU64(123) => {}
                _ => const_unreachable!(),
            }
        };
    }

    #[test]
    fn test_unalign_update() {
        let mut u = Unalign::new(AU64(123));
        u.update(|a| a.0 += 1);
        assert_eq!(u.get(), AU64(124));

        // Test that, even if the callback panics, the original is still
        // correctly overwritten. Use a `Box` so that Miri is more likely to
        // catch any unsoundness (which would likely result in two `Box`es for
        // the same heap object, which is the sort of thing that Miri would
        // probably catch).
        let mut u = Unalign::new(Box::new(AU64(123)));
        let res = std::panic::catch_unwind(AssertUnwindSafe(|| {
            u.update(|a| {
                a.0 += 1;
                panic!();
            })
        }));
        assert!(res.is_err());
        assert_eq!(u.into_inner(), Box::new(AU64(124)));

        // Test the align_of::<T>() == 1 optimization.
        let mut u = Unalign::new([0u8, 1]);
        u.update(|a| a[0] += 1);
        assert_eq!(u.get(), [1u8, 1]);
    }

    #[test]
    fn test_unalign_copy_clone() {
        // Test that `Copy` and `Clone` do not cause soundness issues. This test
        // is mainly meant to exercise UB that would be caught by Miri.

        // `u.t` is definitely not validly-aligned for `AU64`'s alignment of 8.
        let u = ForceUnalign::<_, AU64>::new(Unalign::new(AU64(123)));
        #[allow(clippy::clone_on_copy)]
        let v = u.t.clone();
        let w = u.t;
        assert_eq!(u.t.get(), v.get());
        assert_eq!(u.t.get(), w.get());
        assert_eq!(v.get(), w.get());
    }

    #[test]
    fn test_unalign_trait_impls() {
        let zero = Unalign::new(0u8);
        let one = Unalign::new(1u8);

        assert!(zero < one);
        assert_eq!(PartialOrd::partial_cmp(&zero, &one), Some(Ordering::Less));
        assert_eq!(Ord::cmp(&zero, &one), Ordering::Less);

        assert_ne!(zero, one);
        assert_eq!(zero, zero);
        assert!(!PartialEq::eq(&zero, &one));
        assert!(PartialEq::eq(&zero, &zero));

        fn hash<T: Hash>(t: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }

        assert_eq!(hash(&zero), hash(&0u8));
        assert_eq!(hash(&one), hash(&1u8));

        assert_eq!(format!("{:?}", zero), format!("{:?}", 0u8));
        assert_eq!(format!("{:?}", one), format!("{:?}", 1u8));
        assert_eq!(format!("{}", zero), format!("{}", 0u8));
        assert_eq!(format!("{}", one), format!("{}", 1u8));
    }

    #[test]
    #[allow(clippy::as_conversions)]
    fn test_maybe_uninit() {
        // int
        {
            let input = 42;
            let uninit = MaybeUninit::new(input);
            // SAFETY: `uninit` is in an initialized state
            let output = unsafe { uninit.assume_init() };
            assert_eq!(input, output);
        }

        // thin ref
        {
            let input = 42;
            let uninit = MaybeUninit::new(&input);
            // SAFETY: `uninit` is in an initialized state
            let output = unsafe { uninit.assume_init() };
            assert_eq!(&input as *const _, output as *const _);
            assert_eq!(input, *output);
        }

        // wide ref
        {
            let input = [1, 2, 3, 4];
            let uninit = MaybeUninit::new(&input[..]);
            // SAFETY: `uninit` is in an initialized state
            let output = unsafe { uninit.assume_init() };
            assert_eq!(&input[..] as *const _, output as *const _);
            assert_eq!(input, *output);
        }
    }
    #[test]
    fn test_maybe_uninit_uninit() {
        let _uninit = MaybeUninit::<u8>::uninit();
        // Cannot check value, but can check it compiles and runs
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_maybe_uninit_new_boxed_uninit() {
        let _boxed = MaybeUninit::<u8>::new_boxed_uninit(()).unwrap();
    }

    #[test]
    fn test_maybe_uninit_debug() {
        let uninit = MaybeUninit::<u8>::uninit();
        assert!(format!("{:?}", uninit).contains("MaybeUninit"));
    }
}
