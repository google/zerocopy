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

use super::*;

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
}

impl<A: Aliasing, AA: Alignment, V: Validity> Invariants for (A, AA, V) {
    type Aliasing = A;
    type Alignment = AA;
    type Validity = V;

    type WithAliasing<AB: Aliasing> = (AB, AA, V);
    type WithAlignment<AB: Alignment> = (A, AB, V);
    type WithValidity<VB: Validity> = (A, AA, VB);
}

// NOTE: The `AliasingInner`/`Aliasing` distinction is required so that we can
// add a `MappedTo<Preserved> = Self` bound. For an explanation of the design
// space (and prior attempts), see:
// https://users.rust-lang.org/t/how-to-implement-a-type-level-map-with-an-identity-function/119745
#[doc(hidden)]
pub trait AliasingInner: Sealed {
    type MappedTo<M: AliasingMapping>: Aliasing;
}

/// The aliasing invariant of a [`Ptr`][super::Ptr].
pub trait Aliasing:
    AliasingInner<MappedTo<Preserved> = Self>
    + AliasingInner<MappedTo<Inaccessible> = Inaccessible>
    + AliasingInner<MappedTo<Shared> = Shared>
    + AliasingInner<MappedTo<Exclusive> = Exclusive>
    + Sealed
{
    /// Is `Self` [`Exclusive`]?
    #[doc(hidden)]
    const IS_EXCLUSIVE: bool;

    /// A type which has the correct variance over `'a` and `T` for this
    /// aliasing invariant. `Ptr` stores a `<I::Aliasing as
    /// Aliasing>::Variance<'a, T>` to inherit this variance.
    #[doc(hidden)]
    type Variance<'a, T: 'a + ?Sized>;
}

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
pub trait Reference: Aliasing + Sealed {
    fn with<'a, T, I, S, E, O>(ptr: Ptr<'a, T, I>, shared: S, exclusive: E) -> O
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = Self>,
        S: FnOnce(Ptr<'a, T, I::WithAliasing<Shared>>) -> O,
        E: FnOnce(Ptr<'a, T, I::WithAliasing<Exclusive>>) -> O;
}

/// It is unknown whether any invariant holds.
pub enum Unknown {}

impl AlignmentInner for Unknown {
    type MappedTo<M: AlignmentMapping> = M::FromUnknown;
}
impl ValidityInner for Unknown {
    type MappedTo<M: ValidityMapping> = M::FromUnknown;
}

/// The `Ptr<'a, T>` does not permit any reads or writes from or to its referent.
pub enum Inaccessible {}

impl AliasingInner for Inaccessible {
    type MappedTo<M: AliasingMapping> = M::FromInaccessible;
}
impl Aliasing for Inaccessible {
    const IS_EXCLUSIVE: bool = false;

    // SAFETY: Inaccessible `Ptr`s permit neither reads nor writes, and so it
    // doesn't matter how long the referent actually lives. Thus, covariance is
    // fine (and is chosen because it is maximally permissive). Shared
    // references are covariant [1].
    //
    // [1] https://doc.rust-lang.org/1.81.0/reference/subtyping.html#variance
    type Variance<'a, T: 'a + ?Sized> = &'a T;
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
impl AliasingInner for Shared {
    type MappedTo<M: AliasingMapping> = M::FromShared;
}
impl Aliasing for Shared {
    const IS_EXCLUSIVE: bool = false;
    type Variance<'a, T: 'a + ?Sized> = &'a T;
}
impl Reference for Shared {
    #[inline(always)]
    fn with<'a, T, I, S, E, O>(ptr: Ptr<'a, T, I>, shared: S, _exclusive: E) -> O
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = Shared>,
        S: FnOnce(Ptr<'a, T, I::WithAliasing<Shared>>) -> O,
        E: FnOnce(Ptr<'a, T, I::WithAliasing<Exclusive>>) -> O,
    {
        shared(ptr.unify_invariants())
    }
}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a mut T`.
///
/// The referent of an exclusively-aliased `Ptr` may not be concurrently
/// referenced by any other `Ptr`s or references, and may not be accessed (read
/// or written) other than via this `Ptr`.
pub enum Exclusive {}
impl AliasingInner for Exclusive {
    type MappedTo<M: AliasingMapping> = M::FromExclusive;
}
impl Aliasing for Exclusive {
    const IS_EXCLUSIVE: bool = true;
    type Variance<'a, T: 'a + ?Sized> = &'a mut T;
}
impl Reference for Exclusive {
    #[inline(always)]
    fn with<'a, T, I, S, E, O>(ptr: Ptr<'a, T, I>, _shared: S, exclusive: E) -> O
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = Exclusive>,
        S: FnOnce(Ptr<'a, T, I::WithAliasing<Shared>>) -> O,
        E: FnOnce(Ptr<'a, T, I::WithAliasing<Exclusive>>) -> O,
    {
        exclusive(ptr.unify_invariants())
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
pub trait Read<A: Aliasing, R: ?Sized> {}

/// Unsynchronized reads are permitted because only one live [`Ptr`](crate::Ptr)
/// or reference may exist to the referent bytes at a time.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum BecauseExclusive {}
impl<T: ?Sized> Read<Exclusive, BecauseExclusive> for T {}

/// Unsynchronized reads are permitted because no live [`Ptr`](crate::Ptr)s or
/// references permit interior mutation.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum BecauseImmutable {}
impl<A: Reference, T: ?Sized + crate::Immutable> Read<A, BecauseImmutable> for T {}

macro_rules! declare_because {
    ($($name:ident),*) => {$(
        #[doc(hidden)]
        pub struct $name<R: ?Sized>(core::marker::PhantomData<R>);
    )*};
}

declare_because!(
    BecauseSliceElem,
    BecauseArrayElem,
    BecauseSlice // BecauseArray
);

#[doc(hidden)]
pub struct BecauseArray<R: ?Sized, const N: usize>(core::marker::PhantomData<([(); N], R)>);

impl<A: Reference, T, R: ?Sized> Read<A, BecauseSliceElem<R>> for [T] where T: Read<A, R> {}
impl<A: Reference, T, R: ?Sized> Read<A, BecauseArrayElem<R>> for T where [T]: Read<A, R> {}
impl<A: Reference, T, R: ?Sized, const N: usize> Read<A, BecauseSlice<R>> for [T; N] where
    T: Read<A, R>
{
}
impl<A: Reference, T, R: ?Sized, const N: usize> Read<A, BecauseArray<R, N>> for T where
    [T; N]: Read<A, R>
{
}

use sealed::Sealed;
mod sealed {
    use super::*;

    pub trait Sealed {}

    impl Sealed for Unknown {}

    impl Sealed for Inaccessible {}
    impl Sealed for Shared {}
    impl Sealed for Exclusive {}

    impl Sealed for Aligned {}

    impl Sealed for AsInitialized {}
    impl Sealed for Initialized {}
    impl Sealed for Valid {}

    impl<A: Sealed, AA: Sealed, V: Sealed> Sealed for (A, AA, V) {}

    impl Sealed for BecauseImmutable {}
    impl Sealed for BecauseExclusive {}
}

pub use mapping::*;
mod mapping {
    use super::*;

    /// A mapping from one set of [`Invariants`] to another.
    ///
    /// A `Mapping` is a set of an [`AliasingMapping`], an [`AlignmentMapping`],
    /// and a [`ValidityMapping`]. Given `I: Invariants` and `M: Mapping`, `M`
    /// can be applied to `I` as [`Mapped<I, M>`](Mapped).
    pub trait Mapping {
        type Aliasing: AliasingMapping;
        type Alignment: AlignmentMapping;
        type Validity: ValidityMapping;
    }

    // TODO: How to make this less error prone? Right now, e.g.,
    // `(Preserved, Unknown, Preserved)` and `(Unknown, Preserved, Preserved)` both
    // implement `Mapping`, and it's not clear from the definition which
    // order the invariants come in.
    //
    // First attempt was to do `Mapping for ((Aliasing, A), (Alignment, AA),
    // (Validity, V))`, but not all of `Aliasing`, `Alignment`, and
    // `Validity` are object safe.
    impl<A: AliasingMapping, AA: AlignmentMapping, V: ValidityMapping> Mapping for (A, AA, V) {
        type Aliasing = A;
        type Alignment = AA;
        type Validity = V;
    }

    impl Mapping for Preserved {
        type Aliasing = Preserved;
        type Alignment = Preserved;
        type Validity = Preserved;
    }

    /// A mapping from one [`Aliasing`] type to another.
    ///
    /// An `AliasingMapping` is a type-level map which maps one `Aliasing` type
    /// to another. It is always "total" in the sense of having a mapping for
    /// any `A: Aliasing`.
    ///
    /// Given `A: Aliasing` and `M: AliasingMapping`, `M` can be applied to `A`
    /// as [`MappedAliasing<A, M>`](MappedAliasing).
    ///
    /// Mappings are used by [`Ptr`](crate::Ptr) conversion methods to preserve
    /// or modify invariants as required by each method's semantics.
    pub trait AliasingMapping {
        type FromInaccessible: Aliasing;
        type FromShared: Aliasing;
        type FromExclusive: Aliasing;
    }

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
    /// `Preserved` is a valid type for any mapping trait ([`Mapping`],
    /// [`AliasingMapping`], [`AlignmentMapping`], and [`ValidityMapping`]).
    pub enum Preserved {}

    /// The application of the [`Mapping`] `M` to the [`Invariants`] `I`.
    #[allow(type_alias_bounds)]
    pub type Mapped<I: Invariants, M: Mapping> = (
        MappedAliasing<I::Aliasing, M::Aliasing>,
        MappedAlignment<I::Alignment, M::Alignment>,
        MappedValidity<I::Validity, M::Validity>,
    );

    /// The application of the [`AliasingMapping`] `M` to the [`Aliasing`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedAliasing<A: Aliasing, M: AliasingMapping> = A::MappedTo<M>;

    /// The application of the [`AlignmentMapping`] `M` to the [`Alignment`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedAlignment<A: Alignment, M: AlignmentMapping> = A::MappedTo<M>;

    /// The application of the [`ValidityMapping`] `M` to the [`Validity`] `A`.
    #[allow(type_alias_bounds)]
    pub type MappedValidity<V: Validity, M: ValidityMapping> = V::MappedTo<M>;

    impl<FromInaccessible: Aliasing, FromShared: Aliasing, FromExclusive: Aliasing> AliasingMapping
        for ((Inaccessible, FromInaccessible), (Shared, FromShared), (Exclusive, FromExclusive))
    {
        type FromInaccessible = FromInaccessible;
        type FromShared = FromShared;
        type FromExclusive = FromExclusive;
    }

    impl AliasingMapping for Inaccessible {
        type FromInaccessible = Inaccessible;
        type FromShared = Inaccessible;
        type FromExclusive = Inaccessible;
    }

    pub enum UnsafeCellMismatch {}

    impl AliasingMapping for UnsafeCellMismatch {
        type FromInaccessible = Inaccessible;
        type FromShared = Inaccessible;
        type FromExclusive = Exclusive;
    }

    impl AliasingMapping for Preserved {
        type FromInaccessible = Inaccessible;
        type FromShared = Shared;
        type FromExclusive = Exclusive;
    }

    impl AliasingMapping for Shared {
        type FromInaccessible = Shared;
        type FromShared = Shared;
        type FromExclusive = Shared;
    }

    impl AliasingMapping for Exclusive {
        type FromInaccessible = Exclusive;
        type FromShared = Exclusive;
        type FromExclusive = Exclusive;
    }

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
