// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(missing_copy_implementations, missing_debug_implementations)]

//! The parameterized invariants of a [`Ptr`][super::Ptr].
//!
//! A `Ptr<V, I>` has the following invariants:
//! - [`V: Validity`][validity-trait] encodes the bit validity of `Ptr`'s
//!   referent, which is of type [`V::Inner`][validity-inner]
//! - [`I: Invariants`][invariants-trait], where
//!   [`I::Aliasing`][invariants-aliasing] and
//!   [`I::Alignment`][invariants-alignment] encode the `Ptr`'s aliasing and
//!   alignment invariants respectively
//!
//! [validity-trait]: Validity
//! [validity-inner]: Validity::Inner
//! [invariants-trait]: Invariants
//! [invariants-aliasing]: Invariants::Aliasing
//! [invariants-alignment]: Invariants::Alignment

use core::marker::PhantomData;

/// The aliasing and alignment invariants of a [`Ptr`][super::Ptr].
pub trait Invariants: Sealed {
    type Aliasing: Aliasing;
    type Alignment: Alignment;

    /// Invariants identical to `Self` except with a different aliasing
    /// invariant.
    type WithAliasing<A: Aliasing>: Invariants<Aliasing = A, Alignment = Self::Alignment>;

    /// Invariants identical to `Self` except with a different alignment
    /// invariant.
    type WithAlignment<A: Alignment>: Invariants<Aliasing = Self::Aliasing, Alignment = A>;
}

impl<A: Aliasing, AA: Alignment> Invariants for (A, AA) {
    type Aliasing = A;
    type Alignment = AA;

    type WithAliasing<AB: Aliasing> = (AB, AA);
    type WithAlignment<AB: Alignment> = (A, AB);
}

/// The aliasing invariant of a [`Ptr`][super::Ptr].
///
/// All aliasing invariants must permit reading from the bytes of a pointer's
/// referent which are not covered by [`UnsafeCell`]s.
///
/// [`UnsafeCell`]: core::cell::UnsafeCell
pub trait Aliasing: Sealed {
    /// Is `Self` [`Exclusive`]?
    #[doc(hidden)]
    const IS_EXCLUSIVE: bool;
}

/// The alignment invariant of a [`Ptr`][super::Ptr].
pub trait Alignment: Sealed {
    #[doc(hidden)]
    type MappedTo<M: AlignmentMapping>: Alignment;
}

/// The validity invariant of a [`Ptr`][super::Ptr].
///
/// A `V: Validity` defines both the referent type of a `Ptr<V>`
/// ([`V::Inner`](Validity::Inner)) and the bit validity of the referent value.
/// Bit validity specifies a set, `S`, of possible values which may exist at the
/// `Ptr`'s referent. Code operating on a `Ptr` may assume that bit validity
/// holds - namely, that it will only observe referent values in `S`. It must
/// also uphold bit validity - namely, it must only write values in `S` to the
/// referent.
///
/// The specific definition of `S` for a given validity type (i.e., `V:
/// Validity`) is documented on that type.
///
/// The available validities are [`Uninit`], [`AsInitialized`], [`Initialized`],
/// and [`Valid`].
pub trait Validity: Sealed {
    type Inner: ?Sized;
    type WithInner<T: ?Sized>: Validity<Inner = T>;

    #[doc(hidden)]
    type MappedTo<M: ValidityMapping>: Validity;
}

/// An [`Aliasing`] invariant which is either [`Shared`] or [`Exclusive`].
///
/// # Safety
///
/// Given `A: Reference`, callers may assume that either `A = Shared` or `A =
/// Exclusive`.
pub trait Reference: Aliasing + Sealed {}

/// It is unknown whether any invariant holds.
pub enum Unknown {}

impl Alignment for Unknown {
    type MappedTo<M: AlignmentMapping> = M::FromUnknown;
}

/// A validity which permits arbitrary bytes - including uninitialized bytes -
/// at any byte offset.
pub struct Uninit<T: ?Sized = ()>(PhantomData<T>);

impl<T: ?Sized> Validity for Uninit<T> {
    type Inner = T;
    type WithInner<U: ?Sized> = Uninit<U>;

    type MappedTo<M: ValidityMapping> = M::FromUninit<T>;
}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a T`.
///
/// The referent of a shared-aliased `Ptr` may be concurrently referenced by any
/// number of shared-aliased `Ptr` or `&T` references, and may not be
/// concurrently referenced by any exclusively-aliased `Ptr`s or `&mut T`
/// references. The referent must not be mutated, except via [`UnsafeCell`]s.
///
/// [`UnsafeCell`]: core::cell::UnsafeCell
pub enum Shared {}
impl Aliasing for Shared {
    const IS_EXCLUSIVE: bool = false;
}
impl Reference for Shared {}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a mut T`.
///
/// The referent of an exclusively-aliased `Ptr` may not be concurrently
/// referenced by any other `Ptr`s or references, and may not be accessed (read
/// or written) other than via this `Ptr`.
pub enum Exclusive {}
impl Aliasing for Exclusive {
    const IS_EXCLUSIVE: bool = true;
}
impl Reference for Exclusive {}

/// The referent is aligned: for `Ptr<T>`, the referent's address is a
/// multiple of the `T`'s alignment.
pub enum Aligned {}
impl Alignment for Aligned {
    type MappedTo<M: AlignmentMapping> = M::FromAligned;
}

/// The byte ranges initialized in `T` are also initialized in the referent.
///
/// Formally: uninitialized bytes may only be present in
/// `Ptr<AsInitialized<T>>`'s referent where they are guaranteed to be present
/// in `T`. This is a dynamic property: if, at a particular byte offset, a valid
/// enum discriminant is set, the subsequent bytes may only have uninitialized
/// bytes as specificed by the corresponding enum.
///
/// Formally, given `len = size_of_val_raw(ptr)`, at every byte offset, `b`, in
/// the range `[0, len)`:
/// - If, in any instance `t: T` of length `len`, the byte at offset `b` in `t`
///   is initialized, then the byte at offset `b` within `*ptr` must be
///   initialized.
/// - Let `c` be the contents of the byte range `[0, b)` in `*ptr`. Let `S` be
///   the subset of valid instances of `T` of length `len` which contain `c` in
///   the offset range `[0, b)`. If, in any instance of `t: T` in `S`, the byte
///   at offset `b` in `t` is initialized, then the byte at offset `b` in `*ptr`
///   must be initialized.
///
///   Pragmatically, this means that if `*ptr` is guaranteed to contain an enum
///   type at a particular offset, and the enum discriminant stored in `*ptr`
///   corresponds to a valid variant of that enum type, then it is guaranteed
///   that the appropriate bytes of `*ptr` are initialized as defined by that
///   variant's bit validity (although note that the variant may contain another
///   enum type, in which case the same rules apply depending on the state of
///   its discriminant, and so on recursively).
pub struct AsInitialized<T: ?Sized = ()>(PhantomData<T>);
impl<T: ?Sized> Validity for AsInitialized<T> {
    type Inner = T;
    type WithInner<U: ?Sized> = AsInitialized<U>;
    type MappedTo<M: ValidityMapping> = M::FromAsInitialized<T>;
}

/// The byte ranges in the referent are fully initialized. In other words, if
/// the referent is `N` bytes long, then it contains a bit-valid `[u8; N]`.
pub struct Initialized<T: ?Sized = ()>(PhantomData<T>);
impl<T: ?Sized> Validity for Initialized<T> {
    type Inner = T;
    type WithInner<U: ?Sized> = Initialized<U>;
    type MappedTo<M: ValidityMapping> = M::FromInitialized<T>;
}

/// The referent is bit-valid for `T`.
pub struct Valid<T: ?Sized = ()>(PhantomData<T>);
impl<T: ?Sized> Validity for Valid<T> {
    type Inner = T;
    type WithInner<U: ?Sized> = Valid<U>;
    type MappedTo<M: ValidityMapping> = M::FromValid<T>;
}

/// [`Ptr`](crate::Ptr) referents that permit unsynchronized read operations.
///
/// `T: Read<A, R>` implies that a pointer to `T` with aliasing `A` permits
/// unsynchronized read oeprations. This can be because `A` is [`Exclusive`] or
/// because `T` does not permit interior mutation.
///
/// # Safety
///
/// `T: Read<A, R>` if either of the following conditions holds:
/// - `A` is [`Exclusive`]
/// - `T` implements [`Immutable`](crate::Immutable)
///
/// As a consequence, if `T: Read<A, R>`, then any `Ptr<T, (A, ...)>` is
/// permitted to perform unsynchronized reads from its referent.
#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub unsafe trait Read<A: Aliasing, R> {}

define_because!(
    /// Unsynchronized reads are permitted because only one live
    /// [`Ptr`](crate::Ptr) or reference may exist to the referent bytes at a
    /// time.
    #[doc(hidden)]
    pub BecauseExclusive
);
// SAFETY: The aliasing parameter is `Exclusive`.
unsafe impl<T: ?Sized> Read<Exclusive, BecauseExclusive> for T {}

define_because!(
    /// Unsynchronized reads are permitted because no live [`Ptr`](crate::Ptr)s
    /// or references permit interior mutation.
    #[doc(hidden)]
    pub BecauseImmutable
);
// SAFETY: `T: Immutable`.
unsafe impl<A: Aliasing, T: ?Sized + crate::Immutable> Read<A, BecauseImmutable> for T {}

use sealed::Sealed;
mod sealed {
    use super::*;

    pub trait Sealed {}

    impl Sealed for Unknown {}

    impl<T: ?Sized> Sealed for Uninit<T> {}

    impl Sealed for Shared {}
    impl Sealed for Exclusive {}

    impl Sealed for Aligned {}

    impl<T: ?Sized> Sealed for AsInitialized<T> {}
    impl<T: ?Sized> Sealed for Initialized<T> {}
    impl<T: ?Sized> Sealed for Valid<T> {}

    impl<A: Sealed, AA: Sealed> Sealed for (A, AA) {}
}

pub use mapping::*;
mod mapping {
    use super::*;

    /// A mapping from one [`Alignment`] type to another.
    ///
    /// An `AlignmentMapping` is a type-level map which maps one `Alignment`
    /// type to another. It is always "total" in the sense of having a mapping
    /// for any `A: Alignment`.
    ///
    /// Given `A: Alignment` and `M: AlignmentMapping`, `M` can be applied to
    /// `A` as [`MappedAlignment<A, M>`](MappedAlignment).
    ///
    /// Mappings are used by [`Ptr`](crate::Ptr) conversion methods to preserve
    /// or modify invariants as required by each method's semantics.
    pub trait AlignmentMapping {
        type FromUnknown: Alignment;
        type FromAligned: Alignment;
    }

    /// A mapping from one [`Validity`] type to another.
    ///
    /// An `ValidityMapping` is a type-level map which maps one `Validity` type
    /// to another. It is always "total" in the sense of having a mapping for
    /// any `A: Validity`.
    ///
    /// Given `V: Validity` and `M: ValidityMapping`, `M` can be applied to `V`
    /// as [`MappedValidity<A, M>`](MappedValidity).
    ///
    /// Mappings are used by [`Ptr`](crate::Ptr) conversion methods to preserve
    /// or modify invariants as required by each method's semantics.
    pub trait ValidityMapping {
        type FromUninit<T: ?Sized>: Validity;
        type FromAsInitialized<T: ?Sized>: Validity;
        type FromInitialized<T: ?Sized>: Validity;
        type FromValid<T: ?Sized>: Validity;
    }

    /// The application of the [`AlignmentMapping`] `M` to the [`Alignment`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedAlignment<A: Alignment, M: AlignmentMapping> = A::MappedTo<M>;

    /// The application of the [`ValidityMapping`] `M` to the [`Validity`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedValidity<V: Validity, U: ?Sized, M: ValidityMapping> =
        <V::MappedTo<M> as Validity>::WithInner<U>;

    impl<FromUnknown: Alignment, FromAligned: Alignment> AlignmentMapping
        for ((Unknown, FromUnknown), (Shared, FromAligned))
    {
        type FromUnknown = FromUnknown;
        type FromAligned = FromAligned;
    }

    impl<
            FromUninit: Validity,
            FromAsInitialized: Validity,
            FromInitialized: Validity,
            FromValid: Validity,
        > ValidityMapping
        for (
            (Unknown, FromUninit),
            (AsInitialized, FromAsInitialized),
            (Initialized, FromInitialized),
            (Valid, FromValid),
        )
    {
        type FromUninit<T: ?Sized> = FromUninit::WithInner<T>;
        type FromAsInitialized<T: ?Sized> = FromAsInitialized::WithInner<T>;
        type FromInitialized<T: ?Sized> = FromInitialized::WithInner<T>;
        type FromValid<T: ?Sized> = FromValid::WithInner<T>;
    }

    impl<FromInitialized: Validity> ValidityMapping for (Initialized, FromInitialized) {
        type FromUninit<T: ?Sized> = Uninit<T>;
        type FromAsInitialized<T: ?Sized> = Uninit<T>;
        type FromInitialized<T: ?Sized> = FromInitialized::WithInner<T>;
        type FromValid<T: ?Sized> = Uninit<T>;
    }
}
