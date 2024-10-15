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
//! Invariants are encoded as ([`Aliasing`], [`Alignment`], [`Validity`])
//! triples implementing the [`Invariants`] trait.

/// The invariants of a [`Ptr`][super::Ptr].
pub trait Invariants: Sealed {
    type Aliasing: Aliasing;
    type Alignment: Alignment;
    type Validity: Validity;

    /// Invariants identical to `Self` except with a different aliasing
    /// invariant.
    type WithAliasing<A: Aliasing>: Invariants<
        Aliasing = A,
        Alignment = Self::Alignment,
        Validity = Self::Validity,
    >;

    /// Invariants identical to `Self` except with a different alignment
    /// invariant.
    type WithAlignment<A: Alignment>: Invariants<
        Aliasing = Self::Aliasing,
        Alignment = A,
        Validity = Self::Validity,
    >;

    /// Invariants identical to `Self` except with a different validity
    /// invariant.
    type WithValidity<V: Validity>: Invariants<
        Aliasing = Self::Aliasing,
        Alignment = Self::Alignment,
        Validity = V,
    >;

    /// Invariants identical to `Self` except with a different alignment
    /// invariant, produced by applying the mapping `M` to `Self`'s alignment
    /// invariant.
    type WithMappedAlignment<M: AlignmentMapping>: Invariants<
        Aliasing = Self::Aliasing,
        Alignment = MappedAlignment<Self::Alignment, M>,
        Validity = Self::Validity,
    >;

    /// Invariants identical to `Self` except with a different validity
    /// invariant, produced by applying the mapping `M` to `Self`'s validity
    /// invariant.
    type WithMappedValidity<M: ValidityMapping>: Invariants<
        Aliasing = Self::Aliasing,
        Alignment = Self::Alignment,
        Validity = MappedValidity<Self::Validity, M>,
    >;
}

impl<A: Aliasing, AA: Alignment, V: Validity> Invariants for (A, AA, V) {
    type Aliasing = A;
    type Alignment = AA;
    type Validity = V;

    type WithAliasing<AB: Aliasing> = (AB, AA, V);
    type WithAlignment<AB: Alignment> = (A, AB, V);
    type WithValidity<VB: Validity> = (A, AA, VB);

    type WithMappedAlignment<M: AlignmentMapping> = (A, MappedAlignment<AA, M>, V);
    type WithMappedValidity<M: ValidityMapping> = (A, AA, MappedValidity<V, M>);
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

    /// A type which has the correct variance over `'a` and `T` for this
    /// aliasing invariant. `Ptr` stores a `<I::Aliasing as
    /// Aliasing>::Variance<'a, T>` to inherit this variance.
    #[doc(hidden)]
    type Variance<'a, T: 'a + ?Sized>;

    // #[doc(hidden)]
    // type Applied<'a, T: 'a + ?Sized>;

    // #[doc(hidden)]
    // fn into_ptr<'a, T: 'a + ?Sized>(ptr: Self::Applied<'a, T>) -> PtrInner<'a, T>;

    // #[doc(hidden)]
    // unsafe fn from_ptr<'a, T: 'a + ?Sized>(ptr: PtrInner<'a, T>) -> Self::Applied<'a, T>;
}

// NOTE: The `AlignmentInner`/`Alignment` distinction is required so that we can
// add a `MappedTo<Preserved> = Self` bound. For an explanation of the design
// space (and prior attempts), see:
// https://users.rust-lang.org/t/how-to-implement-a-type-level-map-with-an-identity-function/119745
#[doc(hidden)]
pub trait AlignmentInner: Sealed {
    type MappedTo<M: AlignmentMapping>: Alignment;
}

/// The alignment invariant of a [`Ptr`][super::Ptr].
pub trait Alignment:
    AlignmentInner<MappedTo<Preserved> = Self>
    + AlignmentInner<MappedTo<Unknown> = Unknown>
    + AlignmentInner<MappedTo<Aligned> = Aligned>
    + Sealed
{
}
impl<
        A: AlignmentInner<MappedTo<Preserved> = Self>
            + AlignmentInner<MappedTo<Unknown> = Unknown>
            + AlignmentInner<MappedTo<Aligned> = Aligned>,
    > Alignment for A
{
}

#[doc(hidden)]
pub trait ValidityInner: Sealed {
    type MappedTo<M: ValidityMapping>: Validity;
}

/// The validity invariant of a [`Ptr`][super::Ptr].
pub trait Validity:
    ValidityInner<MappedTo<Preserved> = Self>
    + ValidityInner<MappedTo<Unknown> = Unknown>
    + ValidityInner<MappedTo<AsInitialized> = AsInitialized>
    + ValidityInner<MappedTo<Initialized> = Initialized>
    + ValidityInner<MappedTo<Valid> = Valid>
    + Sealed
{
}
impl<
        V: ValidityInner<MappedTo<Preserved> = Self>
            + ValidityInner<MappedTo<Unknown> = Unknown>
            + ValidityInner<MappedTo<AsInitialized> = AsInitialized>
            + ValidityInner<MappedTo<Initialized> = Initialized>
            + ValidityInner<MappedTo<Valid> = Valid>,
    > Validity for V
{
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

impl AlignmentInner for Unknown {
    type MappedTo<M: AlignmentMapping> = M::FromUnknown;
}
impl ValidityInner for Unknown {
    type MappedTo<M: ValidityMapping> = M::FromUnknown;
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
    type Variance<'a, T: 'a + ?Sized> = &'a T;
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
    type Variance<'a, T: 'a + ?Sized> = &'a mut T;
}
impl Reference for Exclusive {}

#[cfg(feature = "alloc")]
mod _alloc {
    use alloc::boxed::Box as Bx;

    use super::*;

    pub enum Box {}
    impl Aliasing for Box {
        const IS_EXCLUSIVE: bool = false;
        type Variance<'a, T: 'a + ?Sized> = Bx<T>;
    }
}

#[cfg(feature = "std")]
pub use _std::*;
#[cfg(feature = "std")]
mod _std {
    use std::sync::Arc as Ac;

    use super::*;

    pub enum Arc {}
    impl Aliasing for Arc {
        const IS_EXCLUSIVE: bool = false;
        type Variance<'a, T: 'a + ?Sized> = Ac<T>;
    }
}

/// The referent is aligned: for `Ptr<T>`, the referent's address is a multiple
/// of the `T`'s alignment.
pub enum Aligned {}
impl AlignmentInner for Aligned {
    type MappedTo<M: AlignmentMapping> = M::FromAligned;
}

/// The byte ranges initialized in `T` are also initialized in the referent.
///
/// Formally: uninitialized bytes may only be present in `Ptr<T>`'s referent
/// where they are guaranteed to be present in `T`. This is a dynamic property:
/// if, at a particular byte offset, a valid enum discriminant is set, the
/// subsequent bytes may only have uninitialized bytes as specificed by the
/// corresponding enum.
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
pub enum AsInitialized {}
impl ValidityInner for AsInitialized {
    type MappedTo<M: ValidityMapping> = M::FromAsInitialized;
}

/// The byte ranges in the referent are fully initialized. In other words,
/// if the referent is `N` bytes long, then it contains a bit-valid `[u8; N]`.
pub enum Initialized {}
impl ValidityInner for Initialized {
    type MappedTo<M: ValidityMapping> = M::FromInitialized;
}

/// The referent is bit-valid for `T`.
pub enum Valid {}
impl ValidityInner for Valid {
    type MappedTo<M: ValidityMapping> = M::FromValid;
}

// Shared, Arc, etc
pub trait SharedFoo: Aliasing {}
impl SharedFoo for Shared {}
#[cfg(feature = "std")]
impl SharedFoo for Arc {}

// Exclusive, Box, etc
pub trait ExclusiveFoo: Aliasing {}
impl ExclusiveFoo for Exclusive {}
#[cfg(feature = "alloc")]
impl ExclusiveFoo for Box {}

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
unsafe impl<A: ExclusiveFoo, T: ?Sized> Read<A, BecauseExclusive> for T {}

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

    impl Sealed for Shared {}
    impl Sealed for Exclusive {}
    #[cfg(feature = "alloc")]
    impl Sealed for Box {}
    #[cfg(feature = "std")]
    impl Sealed for Arc {}

    impl Sealed for Aligned {}

    impl Sealed for AsInitialized {}
    impl Sealed for Initialized {}
    impl Sealed for Valid {}

    impl<A: Sealed, AA: Sealed, V: Sealed> Sealed for (A, AA, V) {}
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
        type FromUnknown: Validity;
        type FromAsInitialized: Validity;
        type FromInitialized: Validity;
        type FromValid: Validity;
    }

    /// A mapping which preserves all invariants as-is.
    ///
    /// `Preserved` is a valid type for any mapping trait ([`AlignmentMapping`]
    /// and [`ValidityMapping`]).
    pub enum Preserved {}

    /// The application of the [`AlignmentMapping`] `M` to the [`Alignment`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedAlignment<A: Alignment, M: AlignmentMapping> = A::MappedTo<M>;

    /// The application of the [`ValidityMapping`] `M` to the [`Validity`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedValidity<V: Validity, M: ValidityMapping> = V::MappedTo<M>;

    impl<FromUnknown: Alignment, FromAligned: Alignment> AlignmentMapping
        for ((Unknown, FromUnknown), (Aligned, FromAligned))
    {
        type FromUnknown = FromUnknown;
        type FromAligned = FromAligned;
    }

    impl AlignmentMapping for Unknown {
        type FromUnknown = Unknown;
        type FromAligned = Unknown;
    }

    impl AlignmentMapping for Preserved {
        type FromUnknown = Unknown;
        type FromAligned = Aligned;
    }

    impl AlignmentMapping for Aligned {
        type FromUnknown = Aligned;
        type FromAligned = Aligned;
    }

    impl<
            FromUnknown: Validity,
            FromAsInitialized: Validity,
            FromInitialized: Validity,
            FromValid: Validity,
        > ValidityMapping
        for (
            (Unknown, FromUnknown),
            (AsInitialized, FromAsInitialized),
            (Initialized, FromInitialized),
            (Valid, FromValid),
        )
    {
        type FromUnknown = FromUnknown;
        type FromAsInitialized = FromAsInitialized;
        type FromInitialized = FromInitialized;
        type FromValid = FromValid;
    }

    impl<FromInitialized: Validity> ValidityMapping for (Initialized, FromInitialized) {
        type FromUnknown = Unknown;
        type FromAsInitialized = Unknown;
        type FromInitialized = FromInitialized;
        type FromValid = Unknown;
    }

    impl ValidityMapping for Unknown {
        type FromUnknown = Unknown;
        type FromAsInitialized = Unknown;
        type FromInitialized = Unknown;
        type FromValid = Unknown;
    }

    impl ValidityMapping for Preserved {
        type FromUnknown = Unknown;
        type FromAsInitialized = AsInitialized;
        type FromInitialized = Initialized;
        type FromValid = Valid;
    }

    impl ValidityMapping for AsInitialized {
        type FromUnknown = AsInitialized;
        type FromAsInitialized = AsInitialized;
        type FromInitialized = AsInitialized;
        type FromValid = AsInitialized;
    }

    impl ValidityMapping for Initialized {
        type FromUnknown = Initialized;
        type FromAsInitialized = Initialized;
        type FromInitialized = Initialized;
        type FromValid = Initialized;
    }

    impl ValidityMapping for Valid {
        type FromUnknown = Valid;
        type FromAsInitialized = Valid;
        type FromInitialized = Valid;
        type FromValid = Valid;
    }
}
