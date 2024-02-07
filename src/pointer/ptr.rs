// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::ptr::NonNull;

use crate::{util::AsAddress, KnownLayout, _CastType};

/// Module used to gate access to [`Ptr`]'s fields.
mod def {
    #[cfg(doc)]
    use super::invariant;
    use super::Invariants;
    use core::{marker::PhantomData, ptr::NonNull};

    /// A raw pointer with more restrictions.
    ///
    /// `Ptr<T>` is similar to [`NonNull<T>`], but it is more restrictive in the
    /// following ways:
    /// - It must derive from a valid allocation.
    /// - It must reference a byte range which is contained inside the
    ///   allocation from which it derives.
    ///   - As a consequence, the byte range it references must have a size
    ///     which does not overflow `isize`.
    ///
    /// Depending on how `Ptr` is parameterized, it may have additional
    /// invariants:
    /// - `ptr` conforms to the aliasing invariant of
    ///   [`ALIASING_INVARIANT`](invariant::Aliasing).
    /// - `ptr` conforms to the alignment invariant of
    ///   [`ALIGNMENT_INVARIANT`](invariant::Alignment).
    /// - `ptr` conforms to the validity invariant of
    ///   [`VALIDITY_INVARIANT`](invariant::Validity).
    ///
    /// `Ptr<'a, T>` is [covariant] in `'a` and `T`.
    ///
    /// [covariant]: https://doc.rust-lang.org/reference/subtyping.html
    pub struct Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// # Invariants
        ///
        /// 0. `ptr` is derived from some valid Rust allocation, `A`.
        /// 1. `ptr` has valid provenance for `A`.
        /// 2. `ptr` addresses a byte range which is entirely contained in `A`.
        /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
        /// 4. `ptr` addresses a byte range which does not wrap around the
        ///     address space.
        /// 5. `A` is guaranteed to live for at least `'a`.
        /// 6. `T: 'a`.
        /// 7. `ptr` conforms to the aliasing invariant of
        ///    [`ALIASING_INVARIANT`](invariant::Aliasing); namely:
        ///    - If [`invariant::Shared`], the pointer confoms to the aliasing
        ///      rules of a shared reference.
        ///    - If [`invariant::Exclusive`], the pointer conforms to the
        ///      aliasing rules of an exclusive reference.
        /// 8. `ptr` conforms to the alignment invariant of
        ///    [`ALIGNMENT_INVARIANT`](invariant::Alignment); namely:
        ///    - If [`invariant::Aligned`], the pointer's referent is
        ///      well-aligned.
        /// 9. `ptr` conforms to the validity invariant of
        ///    [`VALIDITY_INVARIANT`](invariant::Validity); namely:
        ///    - If [`invariant::AsInitialized`], the pointer's referent is
        ///      initialized (but not necessarily validly so) in all of the
        ///      initialized ranges of `T`.
        ///    - If [`invariant::Valid`], the pointer's referent is bit-valid.
        // SAFETY: `NonNull<T>` is covariant over `T` [1].
        //
        // [1]: https://doc.rust-lang.org/std/ptr/struct.NonNull.html
        ptr: NonNull<T>,
        // SAFETY: `&'a ()` is covariant over `'a` [1].
        //
        // [1]: https://doc.rust-lang.org/reference/subtyping.html#variance
        _invariants: PhantomData<&'a I>,
    }

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// Constructs a `Ptr` from a [`NonNull`].
        ///
        /// # Safety
        ///
        /// The caller promises that:
        ///
        /// 0. `ptr` is derived from some valid Rust allocation, `A`.
        /// 1. `ptr` has valid provenance for `A`.
        /// 2. `ptr` addresses a byte range which is entirely contained in `A`.
        /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
        /// 4. `ptr` addresses a byte range which does not wrap around the
        ///    address space.
        /// 5. `A` is guaranteed to live for at least `'a`.
        /// 6. `ptr` conforms to the aliasing invariant of
        ///   [`ALIASING_INVARIANT`](invariant::Aliasing).
        /// 7. `ptr` conforms to the alignment invariant of
        ///   [`ALIGNMENT_INVARIANT`](invariant::Alignment).
        /// 8. `ptr` conforms to the validity invariant of
        ///   [`VALIDITY_INVARIANT`](invariant::Validity).
        pub(super) unsafe fn new(ptr: NonNull<T>) -> Ptr<'a, T, I> {
            // SAFETY: The caller has promised to satisfy all safety invariants
            // of `Ptr`.
            Self { ptr, _invariants: PhantomData }
        }

        /// Constructs a `Ptr` from another `Ptr`, possibly with different
        /// parameterized safety invariants.
        ///
        /// # Safety
        ///
        /// The caller promises that `ptr` conforms to the invariants of `I`.
        pub(super) unsafe fn from_ptr<H>(ptr: Ptr<'a, T, H>) -> Self
        where
            H: Invariants,
        {
            // SAFETY: The caller has promised to satisfy all parameterized
            // invariants of `Ptr`. `Ptr`'s other invariants are satisfied
            // by-contract by the source `Ptr`.
            unsafe { Self::new(ptr.as_non_null()) }
        }

        /// Converts this `Ptr<T>` to a [`NonNull<T>`].
        ///
        /// Note that this method does not consume `self`. The caller should
        /// watch out for `unsafe` code which uses the returned `NonNull` in a
        /// way that violates the safety invariants of `self`.
        pub(crate) fn as_non_null(&self) -> NonNull<T> {
            self.ptr
        }
    }
}

#[allow(unreachable_pub)] // This is a false positive on our MSRV toolchain.
pub use def::Ptr;

/// Used to define the system of [invariants][invariant] of `Ptr`.
macro_rules! define_system {
    ($(#[$system_attr:meta])* $system:ident {
        $($(#[$set_attr:meta])* $set:ident {
            $( $(#[$elem_attr:meta])* $elem:ident,)*
        })*
    }) => {
        mod sealed {
            pub trait Sealed {}

            impl<$($set,)*> Sealed for ($($set,)*)
            where
                $($set: super::$set,)*
            {}

            $($(
                impl Sealed for super::$elem {}
            )*)*
        }

        $(#[$system_attr])*
        ///
        #[doc = concat!(
            stringify!($system),
            " are encoded as tuples of (",
        )]
        $(#[doc = concat!(
            "[`",
            stringify!($set),
            "`],"
        )])*
        #[doc = concat!(
            ").",
        )]
        /// This trait is implemented for such tuples, and can be used to
        /// project out the components of these tuples via its associated types.
        pub trait $system: sealed::Sealed {
            $(
                $(#[$set_attr])*
                type $set: $set;
            )*
        }

        impl<$($set,)*> $system for ($($set,)*)
        where
            $($set: self::$set,)*
        {
            $(type $set = $set;)*
        }

        $(
            $(#[$set_attr])*
            pub trait $set: sealed::Sealed {}

            $(
                $(#[$elem_attr])*
                #[allow(missing_copy_implementations, missing_debug_implementations)]
                pub enum $elem {}

                $(#[$elem_attr])*
                impl $set for $elem {}
            )*
        )*

        /// Groupings of invariants at least as strict as the given invariant.
        pub mod at_least {
            $(define_system!(@at_least $set, $($elem,)*);)*
        }
    };

    (@at_least $set:ident, $first:ident, $($rest:ident,)*) => {
        define_system!(@at_least_helper $set, $($rest,)*);
    };
    (@at_least_helper $set:ident, $($first:ident,)?) => {};
    (@at_least_helper $set:ident, $first:ident, $($rest:ident,)+) => {
        #[doc = concat!(
            "[",
            stringify!($set),
            "][super::",
            stringify!($set),
            "] at least as strict as [`",
            stringify!($first),
            "`][super::",
            stringify!($first),
            "]."
        )]
        pub trait $first: super::$set {}
        impl $first for super::$first {}
        $(impl $first for super::$rest {})*
        define_system!(@at_least_helper $set, $($rest,)*);
    };


}

/// The parameterized invariants of a [`Ptr`].
///
/// Invariants are encoded as ([`Aliasing`][invariant::Aliasing],
/// [`Alignment`][invariant::Alignment], [`Validity`][invariant::Validity])
/// triples implementing the [`Invariants`] trait.
pub mod invariant {
    define_system! {
        /// The invariants of a [`Ptr`][super::Ptr].
        Invariants {
            /// The aliasing invariant of a [`Ptr`][super::Ptr].
            Aliasing {
                /// No aliasing invariant.
                AnyAliasing,

                /// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a T`.
                ///
                /// The referent of a shared-aliased `Ptr` may be concurrently
                /// referenced by any number of shared-aliased `Ptr` or `&T`
                /// references, and may not be concurrently referenced by any
                /// exclusively-aliased `Ptr`s or `&mut T` references.
                ///
                /// Unsafe code must assume that safe code will assume that the
                /// referent of such a `Ptr` will not be mutated, except through
                /// interior [`UnsafeCell`]s (if any).
                ///
                /// [`UnsafeCell`]: core::cell::UnsafeCell
                Shared,

                /// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a mut T`.
                ///
                /// The referent of an exclusively-aliased `Ptr` may not be
                /// concurrently referenced by any other `Ptr`s or references.
                /// Owners of an exclusively-aliased `Ptr` may safely (contigent on
                /// upholding the referent's original validity invariants) mutate
                /// its referent.
                Exclusive,
            }

            /// The alignment invariant of a [`Ptr`][super::Ptr].
            Alignment {
                /// The referent is not necessarily aligned.
                AnyAlignment,
                /// The referent is aligned.
                Aligned,
            }

            /// The validity invariant of a [`Ptr`][super::Ptr].
            Validity {
                /// The referent is not necessarily initialized.
                AnyValidity,

                /// The byte ranges initialized in `T` are also initialized in
                /// the referent.
                ///
                /// Formally: uninitialized bytes may only be present in
                /// `Ptr<T>`'s referent where they are guaranteed to be present
                /// in `T`. This is a dynamic property: if, at a particular byte
                /// offset, a valid enum discriminant is set, the subsequent
                /// bytes may only have uninitialized bytes as specificed by the
                /// corresponding enum.
                ///
                /// Formally, given `len = size_of_val_raw(ptr)`, at every byte
                /// offset, `b`, in the range `[0, len)`:
                /// - If, in any instance `t: T` of length `len`, the byte at
                ///   offset `b` in `t` is initialized, then the byte at offset
                ///   `b` within `*ptr` must be initialized.
                /// - Let `c` be the contents of the byte range `[0, b)` in
                ///   `*ptr`. Let `S` be the subset of valid instances of `T` of
                ///   length `len` which contain `c` in the offset range `[0,
                ///   b)`. If, in any instance of `t: T` in `S`, the byte at
                ///   offset `b` in `t` is initialized, then the byte at offset
                ///   `b` in `*ptr` must be initialized.
                ///
                ///   Pragmatically, this means that if `*ptr` is guaranteed to
                ///   contain an enum type at a particular offset, and the enum
                ///   discriminant stored in `*ptr` corresponds to a valid
                ///   variant of that enum type, then it is guaranteed that the
                ///   appropriate bytes of `*ptr` are initialized as defined by
                ///   that variant's bit validity (although note that the
                ///   variant may contain another enum type, in which case the
                ///   same rules apply depending on the state of its
                ///   discriminant, and so on recursively).
                AsInitialized,

                /// The referent is bit-valid for `T`.
                Valid,
            }
        }
    }
}

pub(crate) use invariant::Invariants;

/// External trait implementations on [`Ptr`].
mod _external {
    use super::*;
    use core::fmt::{Debug, Formatter};

    /// SAFETY: Shared pointers are safely `Copy`. We do not implement `Copy`
    /// for exclusive pointers, since at most one may exist at a time. `Ptr`'s
    /// other invariants are unaffected by the number of references that exist
    /// to `Ptr`'s referent.
    impl<'a, T, I> Copy for Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = invariant::Shared>,
    {
    }

    /// SAFETY: Shared pointers are safely `Clone`. We do not implement `Clone`
    /// for exclusive pointers, since at most one may exist at a time. `Ptr`'s
    /// other invariants are unaffected by the number of references that exist
    /// to `Ptr`'s referent.
    impl<'a, T, I> Clone for Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = invariant::Shared>,
    {
        #[inline]
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'a, T, I> Debug for Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        #[inline]
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            self.as_non_null().fmt(f)
        }
    }
}

/// Methods for converting to and from `Ptr` and Rust's safe reference types.
mod _conversions {
    use core::mem::MaybeUninit;

    use super::*;

    /// `&'a T` → `Ptr<'a, T>`
    impl<'a, T> Ptr<'a, T, (invariant::Shared, invariant::Aligned, invariant::Valid)>
    where
        T: 'a + ?Sized,
    {
        /// Constructs a `Ptr` from a shared reference.
        #[doc(hidden)]
        #[inline]
        pub fn from_ref(ptr: &'a T) -> Self {
            let ptr = core::ptr::NonNull::from(ptr);
            // SAFETY:
            // 0. `ptr`, by invariant on `&'a T`, is derived from some valid
            //    Rust allocation, `A`.
            // 1. `ptr`, by invariant on `&'a T`, has valid provenance for `A`.
            // 2. `ptr`, by invariant on `&'a T`, addresses a byte range which
            //    is entirely contained in `A`.
            // 3. `ptr`, by invariant on `&'a T`, addresses a byte range whose
            //    length fits in an `isize`.
            // 4. `ptr`, by invariant on `&'a T`, addresses a byte range which
            //     does not wrap around the address space.
            // 5. `A`, by invariant on `&'a T`, is guaranteed to live for at
            //    least `'a`.
            // 6. `ptr`, by invariant on `&'a T`, conforms to the aliasing
            //    invariant of `invariant::Shared`.
            // 7. `ptr`, by invariant on `&'a T`, conforms to the alignment
            //    invariant of `invariant::Aligned`.
            // 8. `ptr`, by invariant on `&'a T`, conforms to the validity
            //    invariant of `invariant::Valid`.
            unsafe { Self::new(ptr) }
        }
    }

    /// `Ptr<'a, T>` → `&'a T`
    impl<'a, T> Ptr<'a, T, (invariant::Shared, invariant::Aligned, invariant::Valid)>
    where
        T: 'a + ?Sized,
    {
        /// Converts the `Ptr` to a shared reference.
        // This consumes `self`, not `&self`, because `self` is, logically, a
        // pointer. Since this method is only available for `invariant::Shared`,
        // `Self: Copy`, and so this doesn't prevent the caller from still
        // using the pointer after calling `as_ref`.
        #[allow(clippy::wrong_self_convention)]
        pub(crate) fn as_ref(self) -> &'a T {
            let raw = self.as_non_null();
            // SAFETY: This invocation of `NonNull::as_ref` satisfies its
            // documented safety preconditions:
            //
            // 1. The pointer is properly aligned. This is ensured by-contract
            //    on `Ptr`, because the `ALIGNMENT_INVARIANT` is `Aligned`.
            //
            // 2. It must be “dereferenceable” in the sense defined in the
            //    module documentation; i.e.:
            //
            //    > The memory range of the given size starting at the pointer
            //    > must all be within the bounds of a single allocated object.
            //    > [2]
            //
            //   This is ensured by contract on all `Ptr`s.
            //
            // 3. The pointer must point to an initialized instance of `T`. This
            //    is ensured by-contract on `Ptr`, because the
            //    `VALIDITY_INVARIANT` is `Valid`.
            //
            // 4. You must enforce Rust’s aliasing rules. This is ensured by
            //    contract on `Ptr`, because the `ALIASING_INVARIANT` is
            //    `Shared`.
            //
            // [1]: https://doc.rust-lang.org/std/ptr/struct.NonNull.html#method.as_ref
            // [2]: https://doc.rust-lang.org/std/ptr/index.html#safety
            unsafe { raw.as_ref() }
        }
    }

    /// `&'a MaybeUninit<T>` → `Ptr<'a, T>`
    impl<'a, T> Ptr<'a, T, (invariant::Shared, invariant::Aligned, invariant::AnyValidity)>
    where
        T: 'a,
    {
        /// Constructs a `Ptr` from a shared reference to a [`MaybeUninit<T>`].
        ///
        /// [`MaybeUninit<T>`]: MaybeUninit
        #[doc(hidden)]
        #[inline]
        pub fn from_maybe_uninit_ref(ptr: &'a MaybeUninit<T>) -> Self {
            let mu_ptr = core::ptr::NonNull::from(ptr);
            let t_ptr = mu_ptr.cast::<T>();
            // SAFETY:
            // 0. `mu_ptr`, by invariant on `&'a T`, is derived from some valid
            //    Rust allocation, `A`. `t_ptr` is as well because `.cast()`
            //    conserves this property.
            // 1. `mu_ptr`, by invariant on `&'a T`, has valid provenance for
            //    `A`. `t_ptr` does as well because `.cast()` conserves this
            //    property.
            // 2. `mu_ptr`, by invariant on `&'a T`, addresses a byte range
            //    which is entirely contained in `A`. `t_ptr` does as well
            //    because `.cast()` conserves this property. This relies on the
            //    fact that `t_ptr` addresses the same number of bytes as
            //    `mu_ptr`, which is guaranteed because `MaybeUninit<T>` has the
            //    same size as `T` [1].
            // 3. `mu_ptr`, by invariant on `&'a T`, addresses a byte range
            //    whose length fits in an `isize`. `t_ptr` does as well because
            //    `.cast()` conserves this property. This relies on the fact
            //    that `t_ptr` addresses the same number of bytes as `mu_ptr`,
            //    which is guaranteed because `MaybeUninit<T>` has the same size
            //    as `T` [1].
            // 4. `mu_ptr`, by invariant on `&'a T`, addresses a byte range
            //     which does not wrap around the address space. `t_ptr` does as
            //    well because `.cast()` conserves this property. This relies on
            //    the fact that `t_ptr` addresses the same number of bytes as
            //    `mu_ptr`, which is guaranteed because `MaybeUninit<T>` has the
            //    same size as `T` [1].
            // 5. `A`, by invariant on `&'a T`, is guaranteed to live for at
            //    least `'a`.
            // 6. `mu_ptr`, by invariant on `&'a T`, conforms to the aliasing
            //    invariant of `invariant::Shared`. `t_ptr` does as well because
            //    `.cast()` conserves this property.
            // 7. `mu_ptr`, by invariant on `&'a T`, conforms to the alignment
            //    invariant of `invariant::Aligned`. `t_ptr` does as well
            //    because `.cast()` conserves alignment, and `MaybeUninit<T>`
            //    has the same alignment as `T` [1].
            // 8. The returned `Ptr` has validity `invariant::AnyValidity`,
            //    which is always upheld regardless of the contents of its
            //    referent.
            //
            // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
            //
            //   `MaybeUninit<T>` is guaranteed to have the same size,
            //   alignment, and ABI as `T`
            unsafe { Self::new(t_ptr) }
        }
    }
}

/// State transitions between invariants.
mod _transitions {
    use super::*;

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// Assumes that `Ptr`'s referent is validly-aligned for `T` if required
        /// by `A`.
        ///
        /// # Safety
        ///
        /// The caller promises that `Ptr`'s referent conforms to the alignment
        /// invariant of `T` if required by `A`.
        #[inline]
        pub(crate) unsafe fn assume_alignment<A: invariant::Alignment>(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, A, I::Validity)> {
            // SAFETY: The caller promises that `self`'s referent is
            // well-aligned for `T` if required by `A` .
            unsafe { Ptr::from_ptr(self) }
        }

        /// Assumes that `Ptr`'s referent conforms to the validity requirement
        /// of `V`.
        ///
        /// # Safety
        ///
        /// The caller promises that `Ptr`'s referent conforms to the validity
        /// requirement of `V`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn assume_validity<V: invariant::Validity>(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, V)> {
            // SAFETY: The caller promises that `self`'s referent conforms to
            // the validity requirement of `V`.
            unsafe { Ptr::from_ptr(self) }
        }

        /// A shorthand for `self.assume_validity<invariant::AsInitialized>()`.
        ///
        /// # Safety
        ///
        /// The caller promises to uphold the safety preconditions of
        /// `self.assume_validity<invariant::AsInitialized>()`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn assume_as_initialized(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, invariant::AsInitialized)> {
            // SAFETY: The caller has promised to uphold the safety
            // preconditions.
            unsafe { self.assume_validity::<invariant::AsInitialized>() }
        }

        /// A shorthand for `self.assume_validity<invariant::Valid>()`.
        ///
        /// # Safety
        ///
        /// The caller promises to uphold the safety preconditions of
        /// `self.assume_validity<invariant::Valid>()`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn assume_valid(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, invariant::Valid)> {
            // SAFETY: The caller has promised to uphold the safety
            // preconditions.
            unsafe { self.assume_validity::<invariant::Valid>() }
        }

        /// Forgets that `Ptr`'s referent is validly-aligned for `T`.
        #[doc(hidden)]
        #[inline]
        pub fn forget_aligned(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, invariant::AnyAlignment, I::Validity)> {
            // SAFETY: `AnyAlignment` is less restrictive than `Aligned`.
            unsafe { Ptr::from_ptr(self) }
        }

        /// Forgets that `Ptr`'s referent is bit-valid for `T`.
        #[doc(hidden)]
        #[inline]
        pub fn forget_valid(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, invariant::AsInitialized)> {
            // SAFETY: `AnyValidity` is less restrictive than `Valid`.
            unsafe { Ptr::from_ptr(self) }
        }
    }
}

/// Casts of the referent type.
mod _casts {
    use super::*;

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// Casts to a different (unsized) target type.
        ///
        /// # Safety
        ///
        /// The caller promises that
        /// - `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
        ///   *mut U`.
        /// - The size of the object referenced by the resulting pointer is less
        ///   than or equal to the size of the object referenced by `self`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn cast_unsized<U: 'a + ?Sized, F: FnOnce(*mut T) -> *mut U>(
            self,
            cast: F,
        ) -> Ptr<'a, U, (I::Aliasing, invariant::AnyAlignment, invariant::AnyValidity)>
        where
            U: 'a,
        {
            let ptr = cast(self.as_non_null().as_ptr());

            // SAFETY: Caller promises that `cast` is just an `as` cast. We call
            // `cast` on `self.ptr.as_non_null().as_ptr()`, which is non-null by
            // construction.
            let ptr = unsafe { NonNull::new_unchecked(ptr) };

            // SAFETY: Lemma: In the following safety arguments, note that
            // the caller promises that `cast` produces a pointer which
            // addresses no more bytes than those addressed by its input
            // pointer. As a result, the bytes addressed by `ptr` are a subset
            // of the bytes addressed by `self`.
            //
            // 0. By invariant on `self` and contract on `cast`, `ptr` is
            //    derived from some valid Rust allocation, `A`.
            // 1. By invariant on `self` and contract on `cast` (its
            //    implementation is provenance-preserving), `ptr` has valid
            //    provenance for `A`.
            // 2. By the above lemma, `ptr` addresses a byte range which is
            //    entirely contained in `A`.
            // 3. By the above lemma, `ptr` addresses a byte range whose
            //    length fits in an `isize`.
            // 4. By the above lemma, `ptr` addresses a byte range which
            //    does not wrap around the address space.
            // 5. By invariant on `self` and contract on `cast`, `A` is
            //    guaranteed to live for at least `'a`.
            // 6. `ptr` conforms to the aliasing invariant of
            //    `ALIASING_INVARIANT` because casting does not impact the
            //    aliasing invariant.
            // 7. `ptr`, trivially, conforms to the alignment invariant of
            //    `AnyAlignment`.
            // 8. `ptr`, trivially, conforms to the validity invariant of
            //   `AnyValidity`.
            unsafe { Ptr::new(ptr) }
        }
    }

    impl<'a, T, I, const N: usize> Ptr<'a, [T; N], I>
    where
        T: 'a,
        I: Invariants,
    {
        /// Casts this pointer-to-array into a slice.
        #[allow(clippy::wrong_self_convention)]
        pub(crate) fn as_slice(self) -> Ptr<'a, [T], I> {
            let start = self.as_non_null().cast::<T>().as_ptr();
            let slice = core::ptr::slice_from_raw_parts_mut(start, N);
            // SAFETY: `slice` is not null, because it is derived from `start`
            // which is non-null.
            let slice = unsafe { NonNull::new_unchecked(slice) };
            // SAFETY: Lemma: In the following safety arguments, note that
            // `slice` is derived from `self` in two steps: first, by casting
            // `self: [T; N]` to `start: T`, then by constructing a pointer to a
            // slice starting at `start` of length `N`. As a result, `slice`
            // references exactly the same allocation as `self.`
            //
            // 0. By the above lemma, `slice` is derived from the same
            //    allocation as `self`, which, by invariant on `Ptr`, is valid.
            // 1. By the above lemma, `slice` has valid provenance for `A`,
            //    since it is derived from the pointer `self`, which, by
            //    invariant on `Ptr`, has valid provenance for `A`.
            // 2. By the above lemma, `slice` addresses a byte range which is
            //    entirely contained in `A`, because it references exactly the
            //    same byte range as `self`, which, by invariant on `Ptr`, is
            //    entirely contained in `A`.
            // 3. By the above lemma, `slice` addresses a byte range whose
            //    length fits in an `isize`, since it addresses exactly the same
            //    byte range as `self`, which, by invariant on `Ptr`, has a
            //    length that fits in an `isize`.
            // 4. By the above lemma, `slice` addresses a byte range which does
            //    not wrap around the address space, since it addresses exactly
            //    the same byte range as `self`, which, by invariant on `Ptr`,
            //    does not wrap around the address space.
            // 5. By the above lemma, `A` is guaranteed to live for at least
            //    `'a`, because it is derived from the same allocation as
            //    `self`, which, by invariant on `Ptr`, lives for at least `'a`.
            // 6. By the above lemma, `slice` conforms to the aliasing invariant
            //    of `I::Aliasing`, because the operations that produced `slice`
            //    from `self` do not impact aliasing.
            // 7. By the above lemma, `slice` conforms to the alignment
            //    invariant of `I::Alignment`, because the operations that
            //    produced `slice` from `self` do not impact alignment.
            // 8. By the above lemma, `slice` conforms to the validity invariant
            //    of `I::Validity`, because the operations that produced `slice`
            //    from `self` do not impact validity.
            unsafe { Ptr::new(slice) }
        }
    }

    /// For caller convenience, these methods are generic over alignment
    /// invariant. In practice, the referent is always well-aligned, because the
    /// alignment of `[u8]` is 1.
    impl<'a, I> Ptr<'a, [u8], I>
    where
        I: Invariants,
    {
        /// Attempts to cast `self` to a `U` using the given cast type.
        ///
        /// Returns `None` if the resulting `U` would be invalidly-aligned or if
        /// no `U` can fit in `self`. On success, returns a pointer to the
        /// largest-possible `U` which fits in `self`.
        ///
        /// # Safety
        ///
        /// The caller may assume that this implementation is correct, and may
        /// rely on that assumption for the soundness of their code. In
        /// particular, the caller may assume that, if `try_cast_into` returns
        /// `Some((ptr, split_at))`, then:
        /// - If this is a prefix cast, `ptr` refers to the byte range `[0,
        ///   split_at)` in `self`.
        /// - If this is a suffix cast, `ptr` refers to the byte range
        ///   `[split_at, self.len())` in `self`.
        ///
        /// # Panics
        ///
        /// Panics if `U` is a DST whose trailing slice element is zero-sized.
        pub(crate) fn try_cast_into<U: 'a + ?Sized + KnownLayout>(
            &self,
            cast_type: _CastType,
        ) -> Option<(Ptr<'a, U, (I::Aliasing, invariant::Aligned, invariant::AnyValidity)>, usize)>
        {
            // PANICS: By invariant, the byte range addressed by `self.ptr` does
            // not wrap around the address space. This implies that the sum of
            // the address (represented as a `usize`) and length do not overflow
            // `usize`, as required by `validate_cast_and_convert_metadata`.
            // Thus, this call to `validate_cast_and_convert_metadata` will only
            // panic if `U` is a DST whose trailing slice element is zero-sized.
            let (elems, split_at) = U::LAYOUT.validate_cast_and_convert_metadata(
                AsAddress::addr(self.as_non_null().as_ptr()),
                self.len(),
                cast_type,
            )?;

            let offset = match cast_type {
                _CastType::_Prefix => 0,
                _CastType::_Suffix => split_at,
            };

            let ptr = self.as_non_null().cast::<u8>().as_ptr();

            // SAFETY: `offset` is either `0` or `split_at`.
            // `validate_cast_and_convert_metadata` promises that `split_at` is
            // in the range `[0, self.len()]`. Thus, in both cases, `offset` is
            // in `[0, self.len()]`. Thus:
            // - The resulting pointer is in or one byte past the end of the
            //   same byte range as `self.ptr`. Since, by invariant, `self.ptr`
            //   addresses a byte range entirely contained within a single
            //   allocation, the pointer resulting from this operation is within
            //   or one byte past the end of that same allocation.
            // - By invariant, `self.len() <= isize::MAX`. Since `offset <=
            //   self.len()`, `offset <= isize::MAX`.
            // - By invariant, `self.ptr` addresses a byte range which does not
            //   wrap around the address space. This means that the base pointer
            //   plus the `self.len()` does not overflow `usize`. Since `offset
            //   <= self.len()`, this addition does not overflow `usize`.
            let base = unsafe { ptr.add(offset) };

            // SAFETY: Since `add` is not allowed to wrap around, the preceding line
            // produces a pointer whose address is greater than or equal to that of
            // `ptr`. Since `ptr` is a `NonNull`, `base` is also non-null.
            let base = unsafe { NonNull::new_unchecked(base) };
            let ptr = U::raw_from_ptr_len(base, elems);

            // SAFETY:
            // 0. By invariant, `self.ptr` is derived from some valid Rust
            //    allocation, `A`. By contract on `cast`, `ptr` is derived from
            //    `self`, and thus from the same valid Rust allocation, `A`.
            // 1. By invariant, `self.ptr` has provenance valid for some Rust
            //    allocation, `A`. By contract on `cast`, and because `ptr` is
            //    derived from `self` via provenance-preserving operations,
            //    `ptr` will also have provenance valid for `A`.
            // 2. By invariant, `self.ptr` addresses a byte range which is
            //    entirely contained in `A`. By contract on `cast`, `ptr`
            //    addresses a subset of the bytes referenced by `self.ptr`,
            //    which is itself entirely contained by `A`.
            // -  `validate_cast_and_convert_metadata` promises that the object
            //    described by `elems` and `split_at` lives at a byte range
            //    which is a subset of the input byte range. Thus:
            //    3. Since, by invariant, `self.ptr` addresses a byte range
            //       entirely contained in `A`, so does `ptr`.
            //    4. Since, by invariant, `self.ptr` addresses a range whose
            //       length is not longer than `isize::MAX` bytes, so does
            //       `ptr`.
            //    5. Since, by invariant, `self.ptr` addresses a range which
            //       does not wrap around the address space, so does `ptr`.
            // 6. `ptr` conforms to the aliasing invariant of
            //    `ALIASING_INVARIANT` because casting does not impact the
            //    aliasing invariant.
            // 7. `ptr` conforms to the alignment invariant of `Aligned` because
            //    it is derived from `validate_cast_and_convert_metadata`
            //    promises that the object described by `split_at` is validly
            //    aligned for `U`.
            // 8. `ptr`, trivially, conforms to the validity invariant of
            //    `AnyValidity`.
            Some((unsafe { Ptr::new(ptr) }, split_at))
        }

        /// Attempts to cast `self` into a `U`, failing if all of the bytes of
        /// `self` cannot be treated as a `U`.
        ///
        /// In particular, this method fails if `self` is not validly-aligned
        /// for `U` or if `self`'s size is not a valid size for `U`.
        ///
        /// # Safety
        ///
        /// On success, the caller may assume that the returned pointer
        /// references the same byte range as `self`.
        #[allow(unused)]
        #[inline(always)]
        pub(crate) fn try_cast_into_no_leftover<U: 'a + ?Sized + KnownLayout>(
            &self,
        ) -> Option<Ptr<'a, U, (I::Aliasing, invariant::Aligned, invariant::AnyValidity)>> {
            // TODO(#67): Remove this allow. See NonNulSlicelExt for more
            // details.
            #[allow(unstable_name_collisions)]
            match self.try_cast_into(_CastType::_Prefix) {
                Some((slf, split_at)) if split_at == self.len() => Some(slf),
                Some(_) | None => None,
            }
        }
    }
}

/// Projections through the referent.
mod _project {
    use super::*;

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
        I::Validity: invariant::at_least::AsInitialized,
    {
        /// Projects a field from `self`.
        ///
        /// # Safety
        ///
        /// ## Preconditions
        ///
        /// The caller promises that `projector` projects a field of its
        /// argument. Its argument will be `self` casted to a raw pointer. The
        /// pointer it returns must reference only a subset of `self`'s bytes.
        ///
        /// The caller also promises that `T` is a struct or union type.
        ///
        /// ## Postconditions
        ///
        /// If the preconditions of this function are met, this function will
        /// return a `Ptr` to the field projected from `self` by `projector`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn project<U: 'a + ?Sized>(
            self,
            projector: impl FnOnce(*mut T) -> *mut U,
        ) -> Ptr<'a, U, (I::Aliasing, invariant::AnyAlignment, invariant::AsInitialized)> {
            // SAFETY: `projector` is provided with `self` casted to a raw
            // pointer.
            let field = projector(self.as_non_null().as_ptr());

            // SAFETY: We promise that `projector` is provided with `self`
            // casted to a raw pointer, and the caller promises that `projector`
            // is a field projection of its argument. By invariant on `Ptr`,
            // `self` is non-null, and by contract on `projector`, so too will
            // its return value.
            //
            // Note that field projection cannot wrap around the address space
            // to null.
            //
            // TODO(https://github.com/rust-lang/rust/pull/116675): Cite
            // documentation that allocated objects do not wrap around the
            // address space.
            let field = unsafe { NonNull::new_unchecked(field) };

            // SAFETY: The safety invariants of `Ptr::new` (see definition) are
            // satisfied:
            // 0. `field` is derived from a valid Rust allocation, because
            //    `self` is derived from a valid Rust allocation, by invariant
            //    on `Ptr`, and `projector` (by contract) is a field projection
            //    through `self`.
            // 1. `field` has valid provenance for `self`, because it derived
            //    from `self` using a series of provenance-preserving
            //    operations.
            // 2. `field` is entirely contained in the allocation of `self`,
            //    because it is derived by `projector`, which is (by contract) a
            //    field projection through `self`.
            // 3. `field` addresses a byte range whose length fits in an
            //    `isize`, because it is a field projection through `self` and
            //    thus is entirely contained by `self`, which satisfies this
            //    invariant.
            // 4. `field` addresses a byte range which does not wrap around the
            //    address space (see above).
            // 5. The allocation of `field` is guaranteed to live for at least
            //    `'a`, because `field` is entirely contained in `self`, which
            //    lives for at least `'a` by invariant on `Ptr`.
            // 6. `field` conforms to the aliasing invariant of
            //    `ALIASING_INVARIANT` because projection does not impact the
            //    aliasing invariant.
            // 7. `field`, trivially, conforms to the alignment invariant of
            //    `AnyAlignment`.
            // 8. By type bound on `I::Validity`, `self` satisfies the
            //    "as-initialized" property relative to `T`. The returned `Ptr`
            //    has the validity `AsInitialized`. The caller promises that `T`
            //    is either a struct type or a union type. Returning a `Ptr`
            //    with the validity `AsInitialized` is valid in both cases. The
            //    struct case is self-explanatory, but the union case bears
            //    explanation. The "as-initialized" property says that a byte
            //    must be initialized if it is initialized in *any* instance of
            //    the type. Thus, if `self`'s referent is as-initialized as `T`,
            //    then it is at least as-initialized as each of its fields.
            unsafe { Ptr::new(field) }
        }
    }

    impl<'a, T, I> Ptr<'a, [T], I>
    where
        T: 'a,
        I: Invariants,
    {
        /// The number of slice elements referenced by `self`.
        ///
        /// # Safety
        ///
        /// Unsafe code my rely on `len` satisfying the above contract.
        pub(super) fn len(&self) -> usize {
            #[allow(clippy::as_conversions)]
            let slc = self.as_non_null().as_ptr() as *const [()];

            // SAFETY:
            // - `()` has alignment 1, so `slc` is trivially aligned.
            // - `slc` was derived from a non-null pointer.
            // - The size is 0 regardless of the length, so it is sound to
            //   materialize a reference regardless of location.
            // - By invariant, `self.ptr` has valid provenance.
            let slc = unsafe { &*slc };

            // This is correct because the preceding `as` cast preserves the
            // number of slice elements. Per
            // https://doc.rust-lang.org/nightly/reference/expressions/operator-expr.html#slice-dst-pointer-to-pointer-cast:
            //
            //   For slice types like `[T]` and `[U]`, the raw pointer types
            //   `*const [T]`, `*mut [T]`, `*const [U]`, and `*mut [U]` encode
            //   the number of elements in this slice. Casts between these raw
            //   pointer types preserve the number of elements. Note that, as a
            //   consequence, such casts do *not* necessarily preserve the size
            //   of the pointer's referent (e.g., casting `*const [u16]` to
            //   `*const [u8]` will result in a raw pointer which refers to an
            //   object of half the size of the original). The same holds for
            //   `str` and any compound type whose unsized tail is a slice type,
            //   such as struct `Foo(i32, [u8])` or `(u64, Foo)`.
            //
            // TODO(#429),
            // TODO(https://github.com/rust-lang/reference/pull/1417): Once this
            // text is available on the Stable docs, cite those instead of the
            // Nightly docs.
            slc.len()
        }

        /// Iteratively projects the elements `Ptr<T>` from `Ptr<[T]>`.
        pub(crate) fn iter(&self) -> impl Iterator<Item = Ptr<'a, T, I>> {
            // TODO(#429): Once `NonNull::cast` documents that it preserves
            // provenance, cite those docs.
            let base = self.as_non_null().cast::<T>().as_ptr();
            (0..self.len()).map(move |i| {
                // TODO(https://github.com/rust-lang/rust/issues/74265): Use
                // `NonNull::get_unchecked_mut`.

                // SAFETY: If the following conditions are not satisfied
                // `pointer::cast` may induce Undefined Behavior [1]:
                // > 1. Both the starting and resulting pointer must be either
                // >    in bounds or one byte past the end of the same allocated
                // >    object.
                // > 2. The computed offset, in bytes, cannot overflow an
                // >    `isize`.
                // > 3. The offset being in bounds cannot rely on “wrapping
                // >    around” the address space. That is, the
                // >    infinite-precision sum must fit in a `usize`.
                //
                // [1] https://doc.rust-lang.org/std/primitive.pointer.html#method.add
                //
                // We satisfy all three of these conditions here:
                // 1. `base` (by invariant on `self`) points to an allocated
                //    object. By contract, `self.len()` accurately reflects the
                //    number of elements in the slice. `i` is in bounds of
                //   `c.len()` by construction, and so the result of this
                //   addition cannot overflow past the end of the allocation
                //   referred to by `c`.
                // 2. By invariant on `Ptr`, `self` addresses a byte range whose
                //    length fits in an `isize`. Since `elem` is contained in
                //    `self`, the computed offset of `elem` must fit within
                //    `isize.`
                // 3. By invariant on `Ptr`, `self` addresses a byte range which
                //    does not wrap around the address space. Since `elem` is
                //    contained in `self`, the computed offset of `elem` must
                //    wrap around the address space.
                //
                // TODO(#429): Once `pointer::add` documents that it preserves
                // provenance, cite those docs.
                let elem = unsafe { base.add(i) };

                // SAFETY:
                //  - `elem` must not be null. `base` is constructed from a
                //    `NonNull` pointer, and the addition that produces `elem`
                //    must not overflow or wrap around, so `elem >= base > 0`.
                //
                // TODO(#429): Once `NonNull::new_unchecked` documents that it
                // preserves provenance, cite those docs.
                let elem = unsafe { NonNull::new_unchecked(elem) };

                // SAFETY: The safety invariants of `Ptr::new` (see definition)
                // are satisfied:
                // 0. `elem` is derived from a valid Rust allocation, because
                //    `self` is derived from a valid Rust allocation, by
                //    invariant on `Ptr`.
                // 1. `elem` has valid provenance for `self`, because it
                //    derived from `self` using a series of
                //    provenance-preserving operations.
                // 2. `elem` is entirely contained in the allocation of `self`
                //    (see above).
                // 3. `elem` addresses a byte range whose length fits in an
                //    `isize` (see above).
                // 4. `elem` addresses a byte range which does not wrap around
                //    the address space (see above).
                // 5. The allocation of `elem` is guaranteed to live for at
                //    least `'a`, because `elem` is entirely contained in
                //    `self`, which lives for at least `'a` by invariant on
                //    `Ptr`.
                // 6. `elem` conforms to the aliasing invariant of
                //    `ALIASING_INVARIANT` because projection does not impact
                //    the aliasing invariant.
                // 7. `elem`, conditionally, conforms to the validity invariant
                //    of `ALIGNMENT_INVARIANT`. If `elem` is projected from data
                //    well-aligned for `[T]`, `elem` will be valid for `T`.
                // 8. `elem`, conditionally, conforms to the validity invariant of
                //    `VALIDITY_INVARIANT`. If `elem` is projected from data valid
                //    for `[T]`, `elem` will be valid for `T`.
                unsafe { Ptr::new(elem) }
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use core::mem::{self, MaybeUninit};

    use super::*;
    use crate::{util::testutil::AU64, FromBytes};

    #[test]
    fn test_ptr_try_cast_into_soundness() {
        // This test is designed so that if `Ptr::try_cast_into_xxx` are
        // buggy, it will manifest as unsoundness that Miri can detect.

        // - If `size_of::<T>() == 0`, `N == 4`
        // - Else, `N == 4 * size_of::<T>()`
        fn test<T: ?Sized + KnownLayout + FromBytes, const N: usize>() {
            let mut bytes = [MaybeUninit::<u8>::uninit(); N];
            let initialized = [MaybeUninit::new(0u8); N];
            for start in 0..=bytes.len() {
                for end in start..=bytes.len() {
                    // Set all bytes to uninitialized other than those in
                    // the range we're going to pass to `try_cast_from`.
                    // This allows Miri to detect out-of-bounds reads
                    // because they read uninitialized memory. Without this,
                    // some out-of-bounds reads would still be in-bounds of
                    // `bytes`, and so might spuriously be accepted.
                    bytes = [MaybeUninit::<u8>::uninit(); N];
                    let bytes = &mut bytes[start..end];
                    // Initialize only the byte range we're going to pass to
                    // `try_cast_from`.
                    bytes.copy_from_slice(&initialized[start..end]);

                    let bytes = {
                        let bytes: *const [MaybeUninit<u8>] = bytes;
                        #[allow(clippy::as_conversions)]
                        let bytes = bytes as *const [u8];
                        // SAFETY: We just initialized these bytes to valid
                        // `u8`s.
                        unsafe { &*bytes }
                    };

                    // SAFETY: The bytes in `slf` must be initialized.
                    unsafe fn validate_and_get_len<T: ?Sized + KnownLayout + FromBytes>(
                        slf: Ptr<
                            '_,
                            T,
                            (invariant::Shared, invariant::Aligned, invariant::AnyValidity),
                        >,
                    ) -> usize {
                        // SAFETY:
                        // - Since all bytes in `slf` are initialized and
                        //   `T: FromBytes`, `slf` contains a valid `T`.
                        let t = unsafe { slf.as_non_null().as_ref() };

                        let bytes = {
                            let len = mem::size_of_val(t);
                            let t: *const T = t;
                            // SAFETY:
                            // - We know `t`'s bytes are all initialized
                            //   because we just read it from `slf`, which
                            //   points to an initialized range of bytes. If
                            //   there's a bug and this doesn't hold, then
                            //   that's exactly what we're hoping Miri will
                            //   catch!
                            // - Since `T: FromBytes`, `T` doesn't contain
                            //   any `UnsafeCell`s, so it's okay for `t: T`
                            //   and a `&[u8]` to the same memory to be
                            //   alive concurrently.
                            unsafe { core::slice::from_raw_parts(t.cast::<u8>(), len) }
                        };

                        // This assertion ensures that `t`'s bytes are read
                        // and compared to another value, which in turn
                        // ensures that Miri gets a chance to notice if any
                        // of `t`'s bytes are uninitialized, which they
                        // shouldn't be (see the comment above).
                        assert_eq!(bytes, vec![0u8; bytes.len()]);

                        mem::size_of_val(t)
                    }

                    for cast_type in [_CastType::_Prefix, _CastType::_Suffix] {
                        if let Some((slf, split_at)) =
                            Ptr::from_ref(bytes).try_cast_into::<T>(cast_type)
                        {
                            // SAFETY: All bytes in `bytes` have been
                            // initialized.
                            let len = unsafe { validate_and_get_len(slf) };
                            match cast_type {
                                _CastType::_Prefix => assert_eq!(split_at, len),
                                _CastType::_Suffix => assert_eq!(split_at, bytes.len() - len),
                            }
                        }
                    }

                    if let Some(slf) = Ptr::from_ref(bytes).try_cast_into_no_leftover::<T>() {
                        // SAFETY: All bytes in `bytes` have been
                        // initialized.
                        let len = unsafe { validate_and_get_len(slf) };
                        assert_eq!(len, bytes.len());
                    }
                }
            }
        }

        macro_rules! test {
        ($($ty:ty),*) => {
            $({
                const S: usize = core::mem::size_of::<$ty>();
                const N: usize = if S == 0 { 4 } else { S * 4 };
                test::<$ty, N>();
                // We don't support casting into DSTs whose trailing slice
                // element is a ZST.
                if S > 0 {
                    test::<[$ty], N>();
                }
                // TODO: Test with a slice DST once we have any that
                // implement `KnownLayout + FromBytes`.
            })*
        };
    }

        test!(());
        test!(u8, u16, u32, u64, u128, usize, AU64);
        test!(i8, i16, i32, i64, i128, isize);
        test!(f32, f64);
    }
}
