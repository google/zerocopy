// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::ptr::NonNull;

use crate::{util::AsAddress, CastType, KnownLayout};

/// Module used to gate access to [`Ptr`]'s fields.
mod def {
    #[cfg(doc)]
    use super::invariant;
    use super::Invariants;
    use core::{marker::PhantomData, ptr::NonNull};

    /// A raw pointer with more restrictions.
    ///
    /// `Ptr<T>` is similar to [`NonNull<T>`], but it is more restrictive in the
    /// following ways (note that these requirements only hold of non-zero-sized
    /// referents):
    /// - It must derive from a valid allocation.
    /// - It must reference a byte range which is contained inside the
    ///   allocation from which it derives.
    ///   - As a consequence, the byte range it references must have a size
    ///     which does not overflow `isize`.
    ///
    /// Depending on how `Ptr` is parameterized, it may have additional
    /// invariants:
    /// - `ptr` conforms to the aliasing invariant of
    ///   [`I::Aliasing`](invariant::Aliasing).
    /// - `ptr` conforms to the alignment invariant of
    ///   [`I::Alignment`](invariant::Alignment).
    /// - `ptr` conforms to the validity invariant of
    ///   [`I::Validity`](invariant::Validity).
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
        /// 0. If `ptr`'s referent is not zero sized, then `ptr` is derived from
        ///    some valid Rust allocation, `A`.
        /// 1. If `ptr`'s referent is not zero sized, then `ptr` has valid
        ///    provenance for `A`.
        /// 2. If `ptr`'s referent is not zero sized, then `ptr` addresses a
        ///    byte range which is entirely contained in `A`.
        /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
        /// 4. `ptr` addresses a byte range which does not wrap around the
        ///     address space.
        /// 5. If `ptr`'s referent is not zero sized,`A` is guaranteed to live
        ///    for at least `'a`.
        /// 6. `T: 'a`.
        /// 7. `ptr` conforms to the aliasing invariant of
        ///    [`I::Aliasing`](invariant::Aliasing).
        /// 8. `ptr` conforms to the alignment invariant of
        ///    [`I::Alignment`](invariant::Alignment).
        /// 9. `ptr` conforms to the validity invariant of
        ///    [`I::Validity`](invariant::Validity).
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
        /// 0. If `ptr`'s referent is not zero sized, then `ptr` is derived from
        ///    some valid Rust allocation, `A`.
        /// 1. If `ptr`'s referent is not zero sized, then `ptr` has valid
        ///    provenance for `A`.
        /// 2. If `ptr`'s referent is not zero sized, then `ptr` addresses a
        ///    byte range which is entirely contained in `A`.
        /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
        /// 4. `ptr` addresses a byte range which does not wrap around the
        ///    address space.
        /// 5. If `ptr`'s referent is not zero sized, then `A` is guaranteed to
        ///    live for at least `'a`.
        /// 6. `ptr` conforms to the aliasing invariant of
        ///    [`I::Aliasing`](invariant::Aliasing).
        /// 7. `ptr` conforms to the alignment invariant of
        ///    [`I::Alignment`](invariant::Alignment).
        /// 8. `ptr` conforms to the validity invariant of
        ///    [`I::Validity`](invariant::Validity).
        pub(super) unsafe fn new(ptr: NonNull<T>) -> Ptr<'a, T, I> {
            // SAFETY: The caller has promised to satisfy all safety invariants
            // of `Ptr`.
            Self { ptr, _invariants: PhantomData }
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
            $( $(#[$elem_attr:meta])* $elem:ident $(< $($stronger_elem:ident)|*)?,)*
        })*
    }) => {
        /// No requirement - any invariant is allowed.
        #[allow(missing_copy_implementations, missing_debug_implementations)]
        pub enum Any {}

        /// `Self` imposes a requirement at least as strict as `I`.
        pub trait AtLeast<I> {}

        mod sealed {
            pub trait Sealed {}

            impl<$($set,)*> Sealed for ($($set,)*)
            where
                $($set: super::$set,)*
            {}

            impl Sealed for super::Any {}

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
            pub trait $set: 'static + sealed::Sealed {
                // This only exists for use in
                // `into_exclusive_or_post_monomorphization_error`.
                #[doc(hidden)]
                const NAME: &'static str;
            }

            impl $set for Any {
                const NAME: &'static str = stringify!(Any);
            }

            $(
                $(#[$elem_attr])*
                #[allow(missing_copy_implementations, missing_debug_implementations)]
                pub enum $elem {}

                $(#[$elem_attr])*
                impl $set for $elem {
                    const NAME: &'static str = stringify!($elem);
                }
            )*
        )*

        $($(
            impl AtLeast<Any> for $elem {}
            impl AtLeast<$elem> for $elem {}

            $($(impl AtLeast<$elem> for $stronger_elem {})*)?
        )*)*
    };
}

/// The parameterized invariants of a [`Ptr`].
///
/// Invariants are encoded as ([`Aliasing`], [`Alignment`], [`Validity`])
/// triples implementing the [`Invariants`] trait.
#[doc(hidden)]
pub mod invariant {
    define_system! {
        /// The invariants of a [`Ptr`][super::Ptr].
        Invariants {
            /// The aliasing invariant of a [`Ptr`][super::Ptr].
            Aliasing {
                /// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a T`.
                ///
                /// The referent of a shared-aliased `Ptr` may be concurrently
                /// referenced by any number of shared-aliased `Ptr` or `&T`
                /// references, and may not be concurrently referenced by any
                /// exclusively-aliased `Ptr`s or `&mut T` references. The
                /// referent must not be mutated, except via [`UnsafeCell`]s.
                ///
                /// [`UnsafeCell`]: core::cell::UnsafeCell
                Shared < Exclusive,

                /// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a mut
                /// T`.
                ///
                /// The referent of an exclusively-aliased `Ptr` may not be
                /// concurrently referenced by any other `Ptr`s or references,
                /// and may not be accessed (read or written) other than via
                /// this `Ptr`.
                Exclusive,
            }

            /// The alignment invariant of a [`Ptr`][super::Ptr].
            Alignment {
                /// The referent is aligned: for `Ptr<T>`, the referent's
                /// address is a multiple of the `T`'s alignment.
                Aligned,
            }

            /// The validity invariant of a [`Ptr`][super::Ptr].
            Validity {
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
                AsInitialized < Initialized | Valid,

                /// The byte ranges in the referent are fully initialized. In
                /// other words, if the referent is `N` bytes long, then it
                /// contains a bit-valid `[u8; N]`.
                Initialized,

                /// The referent is bit-valid for `T`.
                Valid,
            }
        }
    }
}

pub(crate) use invariant::*;

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
        I: Invariants,
        Shared: AtLeast<I::Aliasing>,
    {
    }

    /// SAFETY: Shared pointers are safely `Clone`. We do not implement `Clone`
    /// for exclusive pointers, since at most one may exist at a time. `Ptr`'s
    /// other invariants are unaffected by the number of references that exist
    /// to `Ptr`'s referent.
    impl<'a, T, I> Clone for Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
        Shared: AtLeast<I::Aliasing>,
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
    use super::*;
    use crate::util::{AlignmentVariance, Covariant, TransparentWrapper, ValidityVariance};

    /// `&'a T` → `Ptr<'a, T>`
    impl<'a, T> Ptr<'a, T, (Shared, Aligned, Valid)>
    where
        T: 'a + ?Sized,
    {
        /// Constructs a `Ptr` from a shared reference.
        #[doc(hidden)]
        #[inline]
        pub fn from_ref(ptr: &'a T) -> Self {
            let ptr = NonNull::from(ptr);
            // SAFETY:
            // 0.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //    invariant on `&'a T`, is derived from some valid Rust
            //    allocation, `A`.
            // 1.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //     invariant on `&'a T`, has valid provenance for `A`.
            // 2.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //    invariant on `&'a T`, addresses a byte range which is entirely
            //    contained in `A`.
            // 3. `ptr`, by invariant on `&'a T`, addresses a byte range whose
            //    length fits in an `isize`.
            // 4. `ptr`, by invariant on `&'a T`, addresses a byte range which
            //     does not wrap around the address space.
            // 5.  If `ptr`'s referent is not zero sized, then `A`, by invariant
            //    on `&'a T`, is guaranteed to live for at least `'a`.
            // 6. `T: 'a`.
            // 7. `ptr`, by invariant on `&'a T`, conforms to the aliasing
            //    invariant of `Shared`.
            // 8. `ptr`, by invariant on `&'a T`, conforms to the alignment
            //    invariant of `Aligned`.
            // 9. `ptr`, by invariant on `&'a T`, conforms to the validity
            //    invariant of `Valid`.
            unsafe { Self::new(ptr) }
        }
    }

    /// `&'a mut T` → `Ptr<'a, T>`
    impl<'a, T> Ptr<'a, T, (Exclusive, Aligned, Valid)>
    where
        T: 'a + ?Sized,
    {
        /// Constructs a `Ptr` from an exclusive reference.
        #[inline]
        pub(crate) fn from_mut(ptr: &'a mut T) -> Self {
            let ptr = NonNull::from(ptr);
            // SAFETY:
            // 0.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //    invariant on `&'a mut T`, is derived from some valid Rust
            //    allocation, `A`.
            // 1.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //    invariant on `&'a mut T`, has valid provenance for `A`.
            // 2.  If `ptr`'s referent is not zero sized, then `ptr`, by
            //    invariant on `&'a mut T`, addresses a byte range which is
            //    entirely contained in `A`.
            // 3. `ptr`, by invariant on `&'a mut T`, addresses a byte range
            //    whose length fits in an `isize`.
            // 4. `ptr`, by invariant on `&'a mut T`, addresses a byte range
            //     which does not wrap around the address space.
            // 5.  If `ptr`'s referent is not zero sized, then `A`, by invariant
            //    on `&'a mut T`, is guaranteed to live for at least `'a`.
            // 6. `ptr`, by invariant on `&'a mut T`, conforms to the aliasing
            //    invariant of `Exclusive`.
            // 7. `ptr`, by invariant on `&'a mut T`, conforms to the alignment
            //    invariant of `Aligned`.
            // 8. `ptr`, by invariant on `&'a mut T`, conforms to the validity
            //    invariant of `Valid`.
            unsafe { Self::new(ptr) }
        }
    }

    /// `Ptr<'a, T>` → `&'a T`
    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants<Alignment = Aligned, Validity = Valid>,
        I::Aliasing: AtLeast<Shared>,
    {
        /// Converts `self` to a shared reference.
        // This consumes `self`, not `&self`, because `self` is, logically, a
        // pointer. For `I::Aliasing = invariant::Shared`, `Self: Copy`, and so
        // this doesn't prevent the caller from still using the pointer after
        // calling `as_ref`.
        #[allow(clippy::wrong_self_convention)]
        pub(crate) fn as_ref(self) -> &'a T {
            let raw = self.as_non_null();
            // SAFETY: This invocation of `NonNull::as_ref` satisfies its
            // documented safety preconditions:
            //
            // 1. The pointer is properly aligned. This is ensured by-contract
            //    on `Ptr`, because the `I::Alignment` is `Aligned`.
            //
            // 2. If the pointer's referent is not zero-sized, then the pointer
            //    must be “dereferenceable” in the sense defined in the module
            //    documentation; i.e.:
            //
            //    > The memory range of the given size starting at the pointer
            //    > must all be within the bounds of a single allocated object.
            //    > [2]
            //
            //   This is ensured by contract on all `Ptr`s.
            //
            // 3. The pointer must point to an initialized instance of `T`. This
            //    is ensured by-contract on `Ptr`, because the `I::Validity` is
            //    `Valid`.
            //
            // 4. You must enforce Rust’s aliasing rules. This is ensured by
            //    contract on `Ptr`, because the `I::Aliasing` is
            //    `AtLeast<Shared>`. Either it is `Shared` or `Exclusive`. If it
            //    is `Shared`, other references may not mutate the referent
            //    outside of `UnsafeCell`s.
            //
            // [1]: https://doc.rust-lang.org/std/ptr/struct.NonNull.html#method.as_ref
            // [2]: https://doc.rust-lang.org/std/ptr/index.html#safety
            unsafe { raw.as_ref() }
        }
    }

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
        I::Aliasing: AtLeast<Shared>,
    {
        /// Reborrows `self`, producing another `Ptr`.
        ///
        /// Since `self` is borrowed immutably, this prevents any mutable
        /// methods from being called on `self` as long as the returned `Ptr`
        /// exists.
        #[doc(hidden)]
        #[inline]
        #[allow(clippy::needless_lifetimes)] // Allows us to name the lifetime in the safety comment below.
        pub fn reborrow<'b>(&'b mut self) -> Ptr<'b, T, I>
        where
            'a: 'b,
        {
            // SAFETY: The following all hold by invariant on `self`, and thus
            // hold of `ptr = self.as_non_null()`:
            // 0.  If `ptr`'s referent is not zero sized, then `ptr` is derived
            //     from some valid Rust allocation, `A`.
            // 1.  If `ptr`'s referent is not zero sized, then `ptr` has valid
            //     provenance for `A`.
            // 2.  If `ptr`'s referent is not zero sized, then `ptr` addresses a
            //    byte range which is entirely contained in `A`.
            // 3. `ptr` addresses a byte range whose length fits in an `isize`.
            // 4. `ptr` addresses a byte range which does not wrap around the
            //    address space.
            // 5.  If `ptr`'s referent is not zero sized, then `A` is guaranteed
            //     to live for at least `'a`.
            // 6. SEE BELOW.
            // 7. `ptr` conforms to the alignment invariant of
            //   [`I::Alignment`](invariant::Alignment).
            // 8. `ptr` conforms to the validity invariant of
            //   [`I::Validity`](invariant::Validity).
            //
            // For aliasing (6 above), since `I::Aliasing: AtLeast<Shared>`,
            // there are two cases for `I::Aliasing`:
            // - For `invariant::Shared`: `'a` outlives `'b`, and so the
            //   returned `Ptr` does not permit accessing the referent any
            //   longer than is possible via `self`. For shared aliasing, it is
            //   sound for multiple `Ptr`s to exist simultaneously which
            //   reference the same memory, so creating a new one is not
            //   problematic.
            // - For `invariant::Exclusive`: Since `self` is `&'b mut` and we
            //   return a `Ptr` with lifetime `'b`, `self` is inaccessible to
            //   the caller for the lifetime `'b` - in other words, `self` is
            //   inaccessible to the caller as long as the returned `Ptr`
            //   exists. Since `self` is an exclusive `Ptr`, no other live
            //   references or `Ptr`s may exist which refer to the same memory
            //   while `self` is live. Thus, as long as the returned `Ptr`
            //   exists, no other references or `Ptr`s which refer to the same
            //   memory may be live.
            unsafe { Ptr::new(self.as_non_null()) }
        }
    }

    /// `Ptr<'a, T>` → `&'a mut T`
    impl<'a, T> Ptr<'a, T, (Exclusive, Aligned, Valid)>
    where
        T: 'a + ?Sized,
    {
        /// Converts `self` to a mutable reference.
        #[allow(clippy::wrong_self_convention)]
        pub(crate) fn as_mut(self) -> &'a mut T {
            let mut raw = self.as_non_null();
            // SAFETY: This invocation of `NonNull::as_mut` satisfies its
            // documented safety preconditions:
            //
            // 1. The pointer is properly aligned. This is ensured by-contract
            //    on `Ptr`, because the `ALIGNMENT_INVARIANT` is `Aligned`.
            //
            // 2. If the pointer's referent is not zero-sized, then the pointer
            //    must be “dereferenceable” in the sense defined in the module
            //    documentation; i.e.:
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
            //    `Exclusive`.
            //
            // [1]: https://doc.rust-lang.org/std/ptr/struct.NonNull.html#method.as_mut
            // [2]: https://doc.rust-lang.org/std/ptr/index.html#safety
            unsafe { raw.as_mut() }
        }
    }

    /// `Ptr<'a, T = Wrapper<U>>` → `Ptr<'a, U>`
    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + TransparentWrapper<I, UnsafeCellVariance = Covariant> + ?Sized,
        I: Invariants,
    {
        /// Converts `self` to a transparent wrapper type into a `Ptr` to the
        /// wrapped inner type.
        pub(crate) fn transparent_wrapper_into_inner(
            self,
        ) -> Ptr<
            'a,
            T::Inner,
            (
                I::Aliasing,
                <T::AlignmentVariance as AlignmentVariance<I::Alignment>>::Applied,
                <T::ValidityVariance as ValidityVariance<I::Validity>>::Applied,
            ),
        > {
            // SAFETY:
            // - By invariant on `TransparentWrapper::cast_into_inner`:
            //   - This cast preserves address and referent size, and thus the
            //     returned pointer addresses the same bytes as `p`
            //   - This cast preserves provenance
            // - By invariant on `TransparentWrapper<UnsafeCellVariance =
            //   Covariant>`, `T` and `T::Inner` have `UnsafeCell`s at the same
            //   byte ranges. Since `p` and the returned pointer address the
            //   same byte range, they refer to `UnsafeCell`s at the same byte
            //   ranges.
            let c = unsafe { self.cast_unsized(|p| T::cast_into_inner(p)) };
            // SAFETY: By invariant on `TransparentWrapper`, since `self`
            // satisfies the alignment invariant `I::Alignment`, `c` (of type
            // `T::Inner`) satisfies the given "applied" alignment invariant.
            let c = unsafe {
                c.assume_alignment::<<T::AlignmentVariance as AlignmentVariance<I::Alignment>>::Applied>()
            };
            // SAFETY: By invariant on `TransparentWrapper`, since `self`
            // satisfies the validity invariant `I::Validity`, `c` (of type
            // `T::Inner`) satisfies the given "applied" validity invariant.
            let c = unsafe {
                c.assume_validity::<<T::ValidityVariance as ValidityVariance<I::Validity>>::Applied>()
            };
            c
        }
    }

    /// `Ptr<'a, T, (_, _, _)>` → `Ptr<'a, Unalign<T>, (_, Aligned, _)>`
    impl<'a, T, I> Ptr<'a, T, I>
    where
        I: Invariants,
    {
        /// Converts a `Ptr` an unaligned `T` into a `Ptr` to an aligned
        /// `Unalign<T>`.
        pub(crate) fn into_unalign(
            self,
        ) -> Ptr<'a, crate::Unalign<T>, (I::Aliasing, Aligned, I::Validity)> {
            // SAFETY:
            // - This cast preserves provenance.
            // - This cast preserves address. `Unalign<T>` promises to have the
            //   same size as `T`, and so the cast returns a pointer addressing
            //   the same byte range as `p`.
            // - By the same argument, the returned pointer refers to
            //   `UnsafeCell`s at the same locations as `p`.
            let ptr = unsafe {
                #[allow(clippy::as_conversions)]
                self.cast_unsized(|p: *mut T| p as *mut crate::Unalign<T>)
            };
            // SAFETY: `Unalign<T>` promises to have the same bit validity as
            // `T`.
            let ptr = unsafe { ptr.assume_validity::<I::Validity>() };
            // SAFETY: `Unalign<T>` promises to have alignment 1, and so it is
            // trivially aligned.
            let ptr = unsafe { ptr.assume_alignment::<Aligned>() };
            ptr
        }
    }
}

/// State transitions between invariants.
mod _transitions {
    use super::*;
    use crate::{AlignmentError, TryFromBytes, ValidityError};

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// Returns a `Ptr` with [`Exclusive`] aliasing if `self` already has
        /// `Exclusive` aliasing.
        ///
        /// This allows code which is generic over aliasing to down-cast to a
        /// concrete aliasing.
        ///
        /// [`Exclusive`]: invariant::Exclusive
        #[inline]
        pub(crate) fn into_exclusive_or_post_monomorphization_error(
            self,
        ) -> Ptr<'a, T, (Exclusive, I::Alignment, I::Validity)> {
            trait AliasingExt: Aliasing {
                const IS_EXCLUSIVE: bool;
            }

            impl<A: Aliasing> AliasingExt for A {
                const IS_EXCLUSIVE: bool = {
                    let is_exclusive =
                        strs_are_equal(<Self as Aliasing>::NAME, <Exclusive as Aliasing>::NAME);
                    const_assert!(is_exclusive);
                    true
                };
            }

            const fn strs_are_equal(s: &str, t: &str) -> bool {
                if s.len() != t.len() {
                    return false;
                }

                let s = s.as_bytes();
                let t = t.as_bytes();

                let mut i = 0;
                #[allow(clippy::arithmetic_side_effects)]
                while i < s.len() {
                    #[allow(clippy::indexing_slicing)]
                    if s[i] != t[i] {
                        return false;
                    }

                    i += 1;
                }

                true
            }

            assert!(I::Aliasing::IS_EXCLUSIVE);

            // SAFETY: We've confirmed that `self` already has the aliasing
            // `Exclusive`. If it didn't, either the preceding assert would fail
            // or evaluating `I::Aliasing::IS_EXCLUSIVE` would fail. We're
            // *pretty* sure that it's guaranteed to fail const eval, but the
            // `assert!` provides a backstop in case that doesn't work.
            unsafe { self.assume_exclusive() }
        }

        /// Assumes that `self` satisfies the invariants `H`.
        ///
        /// # Safety
        ///
        /// The caller promises that `self` satisfies the invariants `H`.
        unsafe fn assume_invariants<H: Invariants>(self) -> Ptr<'a, T, H> {
            // SAFETY: The caller has promised to satisfy all parameterized
            // invariants of `Ptr`. `Ptr`'s other invariants are satisfied
            // by-contract by the source `Ptr`.
            unsafe { Ptr::new(self.as_non_null()) }
        }

        /// Helps the type system unify two distinct invariant types which are
        /// actually the same.
        pub(crate) fn unify_invariants<
            H: Invariants<Aliasing = I::Aliasing, Alignment = I::Alignment, Validity = I::Validity>,
        >(
            self,
        ) -> Ptr<'a, T, H> {
            // SAFETY: The associated type bounds on `H` ensure that the
            // invariants are unchanged.
            unsafe { self.assume_invariants::<H>() }
        }

        /// Assumes that `self` satisfies the aliasing requirement of `A`.
        ///
        /// # Safety
        ///
        /// The caller promises that `self` satisfies the aliasing requirement
        /// of `A`.
        #[inline]
        pub(crate) unsafe fn assume_aliasing<A: Aliasing>(
            self,
        ) -> Ptr<'a, T, (A, I::Alignment, I::Validity)> {
            // SAFETY: The caller promises that `self` satisfies the aliasing
            // requirements of `A`.
            unsafe { self.assume_invariants() }
        }

        /// Assumes `self` satisfies the aliasing requirement of [`Exclusive`].
        ///
        /// # Safety
        ///
        /// The caller promises that `self` satisfies the aliasing requirement
        /// of `Exclusive`.
        ///
        /// [`Exclusive`]: invariant::Exclusive
        #[inline]
        pub(crate) unsafe fn assume_exclusive(
            self,
        ) -> Ptr<'a, T, (Exclusive, I::Alignment, I::Validity)> {
            // SAFETY: The caller promises that `self` satisfies the aliasing
            // requirements of `Exclusive`.
            unsafe { self.assume_aliasing::<Exclusive>() }
        }

        /// Assumes that `self`'s referent is validly-aligned for `T` if
        /// required by `A`.
        ///
        /// # Safety
        ///
        /// The caller promises that `self`'s referent conforms to the alignment
        /// invariant of `T` if required by `A`.
        #[inline]
        pub(crate) unsafe fn assume_alignment<A: Alignment>(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, A, I::Validity)> {
            // SAFETY: The caller promises that `self`'s referent is
            // well-aligned for `T` if required by `A` .
            unsafe { self.assume_invariants() }
        }

        /// Checks the `self`'s alignment at runtime, returning an aligned `Ptr`
        /// on success.
        pub(crate) fn bikeshed_try_into_aligned(
            self,
        ) -> Result<Ptr<'a, T, (I::Aliasing, Aligned, I::Validity)>, AlignmentError<Self, T>>
        where
            T: Sized,
        {
            if let Err(err) = crate::util::validate_aligned_to::<_, T>(self.as_non_null()) {
                return Err(err.with_src(self));
            }

            // SAFETY: We just checked the alignment.
            Ok(unsafe { self.assume_alignment::<Aligned>() })
        }

        /// Recalls that `self`'s referent is validly-aligned for `T`.
        #[inline]
        // TODO(#859): Reconsider the name of this method before making it
        // public.
        pub(crate) fn bikeshed_recall_aligned(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, Aligned, I::Validity)>
        where
            T: crate::Unaligned,
        {
            // SAFETY: The bound `T: Unaligned` ensures that `T` has no
            // non-trivial alignment requirement.
            unsafe { self.assume_alignment::<Aligned>() }
        }

        /// Assumes that `self`'s referent conforms to the validity requirement
        /// of `V`.
        ///
        /// # Safety
        ///
        /// The caller promises that `self`'s referent conforms to the validity
        /// requirement of `V`.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        pub unsafe fn assume_validity<V: Validity>(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, V)> {
            // SAFETY: The caller promises that `self`'s referent conforms to
            // the validity requirement of `V`.
            unsafe { self.assume_invariants() }
        }

        /// A shorthand for `self.assume_validity<invariant::Initialized>()`.
        ///
        /// # Safety
        ///
        /// The caller promises to uphold the safety preconditions of
        /// `self.assume_validity<invariant::Initialized>()`.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        pub unsafe fn assume_initialized(
            self,
        ) -> Ptr<'a, T, (I::Aliasing, I::Alignment, Initialized)> {
            // SAFETY: The caller has promised to uphold the safety
            // preconditions.
            unsafe { self.assume_validity::<Initialized>() }
        }

        /// A shorthand for `self.assume_validity<Valid>()`.
        ///
        /// # Safety
        ///
        /// The caller promises to uphold the safety preconditions of
        /// `self.assume_validity<Valid>()`.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        pub unsafe fn assume_valid(self) -> Ptr<'a, T, (I::Aliasing, I::Alignment, Valid)> {
            // SAFETY: The caller has promised to uphold the safety
            // preconditions.
            unsafe { self.assume_validity::<Valid>() }
        }

        /// Recalls that `self`'s referent is bit-valid for `T`.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        // TODO(#859): Reconsider the name of this method before making it
        // public.
        pub fn bikeshed_recall_valid(self) -> Ptr<'a, T, (I::Aliasing, I::Alignment, Valid)>
        where
            T: crate::FromBytes,
            I: Invariants<Validity = Initialized>,
        {
            // SAFETY: The bound `T: FromBytes` ensures that any initialized
            // sequence of bytes is bit-valid for `T`. `I: Invariants<Validity =
            // invariant::Initialized>` ensures that all of the referent bytes
            // are initialized.
            unsafe { self.assume_valid() }
        }

        /// Checks that `self`'s referent is validly initialized for `T`,
        /// returning a `Ptr` with `Valid` on success.
        ///
        /// # Panics
        ///
        /// This method will panic if
        /// [`T::is_bit_valid`][TryFromBytes::is_bit_valid] panics.
        ///
        /// # Safety
        ///
        /// On error, unsafe code may rely on this method's returned
        /// `ValidityError` containing `self`.
        #[inline]
        pub(crate) fn try_into_valid(
            mut self,
        ) -> Result<Ptr<'a, T, (I::Aliasing, I::Alignment, Valid)>, ValidityError<Self, T>>
        where
            T: TryFromBytes,
            I::Aliasing: AtLeast<Shared>,
            I: Invariants<Validity = Initialized>,
        {
            // This call may panic. If that happens, it doesn't cause any soundness
            // issues, as we have not generated any invalid state which we need to
            // fix before returning.
            if T::is_bit_valid(self.reborrow().forget_aligned()) {
                // SAFETY: If `T::is_bit_valid`, code may assume that `self`
                // contains a bit-valid instance of `Self`.
                Ok(unsafe { self.assume_valid() })
            } else {
                Err(ValidityError::new(self))
            }
        }

        /// Forgets that `self`'s referent exclusively references `T`,
        /// downgrading to a shared reference.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        pub fn forget_exclusive(self) -> Ptr<'a, T, (Shared, I::Alignment, I::Validity)>
        where
            I::Aliasing: AtLeast<Shared>,
        {
            // SAFETY: `I::Aliasing` is at least as restrictive as `Shared`.
            unsafe { self.assume_invariants() }
        }

        /// Forgets that `self`'s referent is validly-aligned for `T`.
        #[doc(hidden)]
        #[must_use]
        #[inline]
        pub fn forget_aligned(self) -> Ptr<'a, T, (I::Aliasing, Any, I::Validity)> {
            // SAFETY: `Any` is less restrictive than `Aligned`.
            unsafe { self.assume_invariants() }
        }
    }
}

/// Casts of the referent type.
mod _casts {
    use super::*;
    use crate::{
        layout::{DstLayout, MetadataCastError},
        pointer::aliasing_safety::*,
        AlignmentError, CastError, PointerMetadata, SizeError,
    };

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants,
    {
        /// Casts to a different (unsized) target type.
        ///
        /// # Safety
        ///
        /// The caller promises that `u = cast(p)` is a pointer cast with the
        /// following properties:
        /// - `u` addresses a subset of the bytes addressed by `p`
        /// - `u` has the same provenance as `p`
        /// - If `I::Aliasing` is [`Any`] or [`Shared`], `UnsafeCell`s in `*u`
        ///   must exist at ranges identical to those at which `UnsafeCell`s
        ///   exist in `*p`
        #[doc(hidden)]
        #[inline]
        pub unsafe fn cast_unsized<U: 'a + ?Sized, F: FnOnce(*mut T) -> *mut U>(
            self,
            cast: F,
        ) -> Ptr<'a, U, (I::Aliasing, Any, Any)> {
            let ptr = cast(self.as_non_null().as_ptr());

            // SAFETY: Caller promises that `cast` returns a pointer whose
            // address is in the range of `self.as_non_null()`'s referent. By
            // invariant, none of these addresses are null.
            let ptr = unsafe { NonNull::new_unchecked(ptr) };

            // SAFETY:
            //
            // Lemma 1: `ptr` has the same provenance as `self`. The caller
            // promises that `cast` preserves provenance, and we call it with
            // `self.as_non_null()`.
            //
            // 0. By invariant,  if `self`'s referent is not zero sized, then
            //    `self` is derived from some valid Rust allocation, `A`. By
            //    Lemma 1, `ptr` has the same provenance as `self`. Thus, `ptr`
            //    is derived from `A`.
            // 1. By invariant, if `self`'s referent is not zero sized, then
            //    `self` has valid provenance for `A`. By Lemma 1, so does
            //    `ptr`.
            // 2. By invariant on `self` and caller precondition, if `ptr`'s
            //    referent is not zero sized, then `ptr` addresses a byte range
            //    which is entirely contained in `A`.
            // 3. By invariant on `self` and caller precondition, `ptr`
            //    addresses a byte range whose length fits in an `isize`.
            // 4. By invariant on `self` and caller precondition, `ptr`
            //    addresses a byte range which does not wrap around the address
            //    space.
            // 5. By invariant on `self`, if `self`'s referent is not zero
            //    sized, then `A` is guaranteed to live for at least `'a`.
            // 6. `ptr` conforms to the aliasing invariant of `I::Aliasing`:
            //    - `Exclusive`: `self` is the only `Ptr` or reference which is
            //      permitted to read or modify the referent for the lifetime
            //      `'a`. Since we consume `self` by value, the returned pointer
            //      remains the only `Ptr` or reference which is permitted to
            //      read or modify the referent for the lifetime `'a`.
            //    - `Shared`: Since `self` has aliasing `Shared`, we know that
            //      no other code may mutate the referent during the lifetime
            //      `'a`, except via `UnsafeCell`s. The caller promises that
            //      `UnsafeCell`s cover the same byte ranges in `*self` and
            //      `*ptr`. For each byte in the referent, there are two cases:
            //      - If the byte is not covered by an `UnsafeCell` in `*ptr`,
            //        then it is not covered in `*self`. By invariant on `self`,
            //        it will not be mutated during `'a`, as required by the
            //        constructed pointer. Similarly, the returned pointer will
            //        not permit any mutations to these locations, as required
            //        by the invariant on `self`.
            //      - If the byte is covered by an `UnsafeCell` in `*ptr`, then
            //        the returned pointer's invariants do not assume that the
            //        byte will not be mutated during `'a`. While the returned
            //        pointer will permit mutation of this byte during `'a`, by
            //        invariant on `self`, no other code assumes that this will
            //        not happen.
            // 7. `ptr`, trivially, conforms to the alignment invariant of
            //    `Any`.
            // 8. `ptr`, trivially, conforms to the validity invariant of `Any`.
            unsafe { Ptr::new(ptr) }
        }
    }

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + KnownLayout + ?Sized,
        I: Invariants<Validity = Initialized>,
    {
        /// Casts this pointer-to-initialized into a pointer-to-bytes.
        #[allow(clippy::wrong_self_convention)]
        pub(crate) fn as_bytes<R>(self) -> Ptr<'a, [u8], (I::Aliasing, Aligned, Valid)>
        where
            [u8]: AliasingSafe<T, I::Aliasing, R>,
            R: AliasingSafeReason,
        {
            let bytes = match T::size_of_val_raw(self.as_non_null()) {
                Some(bytes) => bytes,
                // SAFETY: `KnownLayout::size_of_val_raw` promises to always
                // return `Some` so long as the resulting size fits in a
                // `usize`. By invariant on `Ptr`, `self` refers to a range of
                // bytes whose size fits in an `isize`, which implies that it
                // also fits in a `usize`.
                None => unsafe { core::hint::unreachable_unchecked() },
            };

            // SAFETY:
            // - `slice_from_raw_parts_mut` and `.cast` both preserve the
            //   pointer's address, and `bytes` is the length of `p`, so the
            //   returned pointer addresses the same bytes as `p`
            // - `slice_from_raw_parts_mut` and `.cast` both preserve provenance
            // - Because `[u8]: AliasingSafe<T, I::Aliasing, _>`, either:
            //   - `I::Aliasing` is `Exclusive`
            //   - `T` and `[u8]` are both `Immutable`, in which case they
            //     trivially contain `UnsafeCell`s at identical locations
            let ptr: Ptr<'a, [u8], _> = unsafe {
                self.cast_unsized(|p: *mut T| {
                    #[allow(clippy::as_conversions)]
                    core::ptr::slice_from_raw_parts_mut(p.cast::<u8>(), bytes)
                })
            };

            let ptr = ptr.bikeshed_recall_aligned();

            // SAFETY: `ptr`'s referent begins as `Initialized`, denoting that
            // all bytes of the referent are initialized bytes. The referent
            // type is then casted to `[u8]`, whose only validity invariant is
            // that its bytes are initialized. This validity invariant is
            // satisfied by the `Initialized` invariant on the starting `ptr`.
            unsafe { ptr.assume_validity::<Valid>() }
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
            // references exactly the same allocation as `self`, if any.
            //
            // 0. By the above lemma, if `slice`'s referent is not zero sized,
            //    then `slice` is derived from the same allocation as `self`,
            //    which, by invariant on `Ptr`, is valid.
            // 1. By the above lemma, if `slice`'s referent is not zero sized,
            //    then , `slice` has valid provenance for `A`, since it is
            //    derived from the pointer `self`, which, by invariant on `Ptr`,
            //    has valid provenance for `A`.
            // 2. By the above lemma, if `slice`'s referent is not zero sized,
            //    then `slice` addresses a byte range which is entirely
            //    contained in `A`, because it references exactly the same byte
            //    range as `self`, which, by invariant on `Ptr`, is entirely
            //    contained in `A`.
            // 3. By the above lemma, `slice` addresses a byte range whose
            //    length fits in an `isize`, since it addresses exactly the same
            //    byte range as `self`, which, by invariant on `Ptr`, has a
            //    length that fits in an `isize`.
            // 4. By the above lemma, `slice` addresses a byte range which does
            //    not wrap around the address space, since it addresses exactly
            //    the same byte range as `self`, which, by invariant on `Ptr`,
            //    does not wrap around the address space.
            // 5. By the above lemma, if `slice`'s referent is not zero sized,
            //    then `A` is guaranteed to live for at least `'a`, because it
            //    is derived from the same allocation as `self`, which, by
            //    invariant on `Ptr`, lives for at least `'a`.
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
        I: Invariants<Validity = Valid>,
    {
        /// Attempts to cast `self` to a `U` using the given cast type.
        ///
        /// If `U` is a slice DST and pointer metadata (`meta`) is provided,
        /// then the cast will only succeed if it would produce an object with
        /// the given metadata.
        ///
        /// Returns `None` if the resulting `U` would be invalidly-aligned, if
        /// no `U` can fit in `self`, or if the provided pointer metadata
        /// describes an invalid instance of `U`. On success, returns a pointer
        /// to the largest-possible `U` which fits in `self`.
        ///
        /// # Safety
        ///
        /// The caller may assume that this implementation is correct, and may
        /// rely on that assumption for the soundness of their code. In
        /// particular, the caller may assume that, if `try_cast_into` returns
        /// `Some((ptr, remainder))`, then `ptr` and `remainder` refer to
        /// non-overlapping byte ranges within `self`, and that `ptr` and
        /// `remainder` entirely cover `self`. Finally:
        /// - If this is a prefix cast, `ptr` has the same address as `self`.
        /// - If this is a suffix cast, `remainder` has the same address as
        ///   `self`.
        #[inline(always)]
        pub(crate) fn try_cast_into<U, R>(
            self,
            cast_type: CastType,
            meta: Option<U::PointerMetadata>,
        ) -> Result<
            (Ptr<'a, U, (I::Aliasing, Aligned, Initialized)>, Ptr<'a, [u8], I>),
            CastError<Self, U>,
        >
        where
            R: AliasingSafeReason,
            U: 'a + ?Sized + KnownLayout + AliasingSafe<[u8], I::Aliasing, R>,
        {
            let layout = match meta {
                None => U::LAYOUT,
                // This can return `None` if the metadata describes an object
                // which can't fit in an `isize`.
                Some(meta) => {
                    let size = match meta.size_for_metadata(U::LAYOUT) {
                        Some(size) => size,
                        None => return Err(CastError::Size(SizeError::new(self))),
                    };
                    DstLayout { align: U::LAYOUT.align, size_info: crate::SizeInfo::Sized { size } }
                }
            };
            // PANICS: By invariant, the byte range addressed by `self.ptr` does
            // not wrap around the address space. This implies that the sum of
            // the address (represented as a `usize`) and length do not overflow
            // `usize`, as required by `validate_cast_and_convert_metadata`.
            // Thus, this call to `validate_cast_and_convert_metadata` will only
            // panic if `U` is a DST whose trailing slice element is zero-sized.
            let maybe_metadata = layout.validate_cast_and_convert_metadata(
                AsAddress::addr(self.as_non_null().as_ptr()),
                self.len(),
                cast_type,
            );

            let (elems, split_at) = match maybe_metadata {
                Ok((elems, split_at)) => (elems, split_at),
                Err(MetadataCastError::Alignment) => {
                    // SAFETY: Since `validate_cast_and_convert_metadata`
                    // returned an alignment error, `U` must have an alignment
                    // requirement greater than one.
                    let err = unsafe { AlignmentError::<_, U>::new_unchecked(self) };
                    return Err(CastError::Alignment(err));
                }
                Err(MetadataCastError::Size) => return Err(CastError::Size(SizeError::new(self))),
            };

            // SAFETY: `validate_cast_and_convert_metadata` promises to return
            // `split_at <= self.len()`.
            let (l_slice, r_slice) = unsafe { self.split_at(split_at) };

            let (target, remainder) = match cast_type {
                CastType::Prefix => (l_slice, r_slice),
                CastType::Suffix => (r_slice, l_slice),
            };

            let base = target.as_non_null().cast::<u8>();

            let elems = <U as KnownLayout>::PointerMetadata::from_elem_count(elems);
            // For a slice DST type, if `meta` is `Some(elems)`, then we
            // synthesize `layout` to describe a sized type whose size is equal
            // to the size of the instance that we are asked to cast. For sized
            // types, `validate_cast_and_convert_metadata` returns `elems == 0`.
            // Thus, in this case, we need to use the `elems` passed by the
            // caller, not the one returned by
            // `validate_cast_and_convert_metadata`.
            let elems = meta.unwrap_or(elems);

            let ptr = U::raw_from_ptr_len(base, elems);

            // SAFETY:
            // 0. By invariant, if `target`'s referent is not zero sized, then
            //    `target` is derived from some valid Rust allocation, `A`. By
            //    contract on `cast`, `ptr` is derived from `self`, and thus
            //    from the same valid Rust allocation, `A`.
            // 1. By invariant, if `target`'s referent is not zero sized, then
            //    `target` has provenance valid for some Rust allocation, `A`.
            //    Because `ptr` is derived from `target` via
            //    provenance-preserving operations, `ptr` will also have
            //    provenance valid for `A`.
            // -  `validate_cast_and_convert_metadata` promises that the object
            //    described by `elems` and `split_at` lives at a byte range
            //    which is a subset of the input byte range. Thus:
            //    2. Since, by invariant, if `target`'s referent is not zero
            //       sized, then `target` addresses a byte range which is
            //       entirely contained in `A`, so does `ptr`.
            //    3. Since, by invariant, `target` addresses a byte range whose
            //       length fits in an `isize`, so does `ptr`.
            //    4. Since, by invariant, `target` addresses a byte range which
            //       does not wrap around the address space, so does `ptr`.
            //    5. Since, by invariant, if `target`'s referent is not zero
            //       sized, then `target` refers to an allocation which is
            //       guaranteed to live for at least `'a`, so does `ptr`.
            //    6. Since `U: AliasingSafe<[u8], I::Aliasing, _>`, either:
            //       - `I::Aliasing` is `Exclusive`, in which case both `src`
            //         and `ptr` conform to `Exclusive`
            //       - `I::Aliasing` is `Shared` or `Any` and both `U` and
            //         `[u8]` are `Immutable`. In this case, neither pointer
            //         permits mutation, and so `Shared` aliasing is satisfied.
            // 7. `ptr` conforms to the alignment invariant of `Aligned` because
            //    it is derived from `validate_cast_and_convert_metadata`, which
            //    promises that the object described by `target` is validly
            //    aligned for `U`.
            // 8. By trait bound, `self` - and thus `target` - is a bit-valid
            //    `[u8]`. All bit-valid `[u8]`s have all of their bytes
            //    initialized, so `ptr` conforms to the validity invariant of
            //    `Initialized`.
            Ok((unsafe { Ptr::new(ptr) }, remainder))
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
        pub(crate) fn try_cast_into_no_leftover<U, R>(
            self,
            meta: Option<U::PointerMetadata>,
        ) -> Result<Ptr<'a, U, (I::Aliasing, Aligned, Initialized)>, CastError<Self, U>>
        where
            U: 'a + ?Sized + KnownLayout + AliasingSafe<[u8], I::Aliasing, R>,
            R: AliasingSafeReason,
        {
            // TODO(#67): Remove this allow. See NonNulSlicelExt for more
            // details.
            #[allow(unstable_name_collisions)]
            match self.try_cast_into(CastType::Prefix, meta) {
                Ok((slf, remainder)) => {
                    if remainder.len() == 0 {
                        Ok(slf)
                    } else {
                        // Undo the cast so we can return the original bytes.
                        let slf = slf.as_bytes();
                        // Restore the initial alignment invariant of `self`.
                        //
                        // SAFETY: The referent type of `slf` is now equal to
                        // that of `self`, but the alignment invariants
                        // nominally differ. Since `slf` and `self` refer to the
                        // same memory and no actions have been taken that would
                        // violate the original invariants on `self`, it is
                        // sound to apply the alignment invariant of `self` onto
                        // `slf`.
                        let slf = unsafe { slf.assume_alignment::<I::Alignment>() };
                        let slf = slf.unify_invariants();
                        Err(CastError::Size(SizeError::<_, U>::new(slf)))
                    }
                }
                Err(err) => Err(err),
            }
        }
    }

    impl<'a, T, I> Ptr<'a, core::cell::UnsafeCell<T>, I>
    where
        T: 'a + ?Sized,
        I: Invariants<Aliasing = Exclusive>,
    {
        /// Converts this `Ptr` into a pointer to the underlying data.
        ///
        /// This call borrows the `UnsafeCell` mutably (at compile-time) which
        /// guarantees that we possess the only reference.
        ///
        /// This is like [`UnsafeCell::get_mut`], but for `Ptr`.
        ///
        /// [`UnsafeCell::get_mut`]: core::cell::UnsafeCell::get_mut
        #[must_use]
        #[inline(always)]
        pub fn get_mut(self) -> Ptr<'a, T, I> {
            // SAFETY:
            // - The closure uses an `as` cast, which preserves address range
            //   and provenance.
            // - We require `I: Invariants<Aliasing = Exclusive>`, so we are not
            //   required to uphold `UnsafeCell` equality.
            #[allow(clippy::as_conversions)]
            let ptr = unsafe { self.cast_unsized(|p| p as *mut T) };

            // SAFETY: `UnsafeCell<T>` has the same alignment as `T` [1],
            // and so if `self` is guaranteed to be aligned, then so is the
            // returned `Ptr`.
            //
            // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
            //
            //   `UnsafeCell<T>` has the same in-memory representation as
            //   its inner type `T`. A consequence of this guarantee is that
            //   it is possible to convert between `T` and `UnsafeCell<T>`.
            let ptr = unsafe { ptr.assume_alignment::<I::Alignment>() };

            // SAFETY: `UnsafeCell<T>` has the same bit validity as `T` [1], and
            // so if `self` has a particular validity invariant, then the same
            // holds of the returned `Ptr`. Technically the term
            // "representation" doesn't guarantee this, but the subsequent
            // sentence in the documentation makes it clear that this is the
            // intention.
            //
            // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
            //
            //   `UnsafeCell<T>` has the same in-memory representation as its
            //   inner type `T`. A consequence of this guarantee is that it is
            //   possible to convert between `T` and `UnsafeCell<T>`.
            let ptr = unsafe { ptr.assume_validity::<I::Validity>() };
            ptr.unify_invariants()
        }
    }
}

/// Projections through the referent.
mod _project {
    use core::ops::Range;

    #[allow(unused_imports)]
    use crate::util::polyfills::NumExt as _;

    use super::*;

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + ?Sized,
        I: Invariants<Validity = Initialized>,
    {
        /// Projects a field from `self`.
        ///
        /// # Safety
        ///
        /// `project` has the same safety preconditions as `cast_unsized`.
        #[doc(hidden)]
        #[inline]
        pub unsafe fn project<U: 'a + ?Sized>(
            self,
            projector: impl FnOnce(*mut T) -> *mut U,
        ) -> Ptr<'a, U, (I::Aliasing, Any, Initialized)> {
            // TODO(#1122): If `cast_unsized` were able to reason that, when
            // casting from an `Initialized` pointer, the result is another
            // `Initialized` pointer, we could remove this method entirely.

            // SAFETY: This method has the same safety preconditions as
            // `cast_unsized`.
            let ptr = unsafe { self.cast_unsized(projector) };

            // SAFETY: If all of the bytes of `self` are initialized (as
            // promised by `I: Invariants<Validity = Initialized>`), then any
            // subset of those bytes are also all initialized.
            unsafe { ptr.assume_validity::<Initialized>() }
        }
    }

    impl<'a, T, I> Ptr<'a, T, I>
    where
        T: 'a + KnownLayout<PointerMetadata = usize> + ?Sized,
        I: Invariants,
    {
        /// The number of trailing slice elements in the object referenced by
        /// `self`.
        ///
        /// # Safety
        ///
        /// Unsafe code my rely on `trailing_slice_len` satisfying the above
        /// contract.
        pub(super) fn trailing_slice_len(&self) -> usize {
            T::pointer_to_metadata(self.as_non_null().as_ptr())
        }
    }

    impl<'a, T, I> Ptr<'a, [T], I>
    where
        T: 'a,
        I: Invariants,
    {
        /// The number of slice elements in the object referenced by `self`.
        ///
        /// # Safety
        ///
        /// Unsafe code my rely on `len` satisfying the above contract.
        pub(crate) fn len(&self) -> usize {
            self.trailing_slice_len()
        }

        /// Creates a pointer which addresses the given `range` of self.
        ///
        /// # Safety
        ///
        /// `range` is a valid range (`start <= end`) and `end <= self.len()`.
        pub(crate) unsafe fn slice_unchecked(self, range: Range<usize>) -> Self {
            let base = self.as_non_null().cast::<T>().as_ptr();

            // SAFETY: The caller promises that `start <= end <= self.len()`. By
            // invariant, if `self`'s referent is not zero-sized, then `self`
            // refers to a byte range which is contained within a single
            // allocation, which is no more than `isize::MAX` bytes long, and
            // which does not wrap around the address space. Thus, this pointer
            // arithmetic remains in-bounds of the same allocation, and does not
            // wrap around the address space. The offset (in bytes) does not
            // overflow `isize`.
            //
            // If `self`'s referent is zero-sized, then these conditions are
            // trivially satisfied.
            let base = unsafe { base.add(range.start) };

            // SAFETY: The caller promises that `start <= end`, and so this will
            // not underflow.
            #[allow(unstable_name_collisions, clippy::incompatible_msrv)]
            let len = unsafe { range.end.unchecked_sub(range.start) };

            let ptr = core::ptr::slice_from_raw_parts_mut(base, len);

            // SAFETY: By invariant, `self`'s address is non-null and its range
            // does not wrap around the address space. Since, by the preceding
            // lemma, `ptr` addresses a range within that addressed by `self`,
            // `ptr` is non-null.
            let ptr = unsafe { NonNull::new_unchecked(ptr) };

            // SAFETY:
            //
            // Lemma 0: `ptr` addresses a subset of the bytes addressed by
            //          `self`, and has the same provenance.
            // Proof: The caller guarantees that `start <= end <= self.len()`.
            //        Thus, `base` is in-bounds of `self`, and `base + (end -
            //        start)` is also in-bounds of self. Finally, `ptr` is
            //        constructed using provenance-preserving operations.
            //
            // 0. Per Lemma 0 and by invariant on `self`, if `ptr`'s referent is
            //    not zero sized, then `ptr` is derived from some valid Rust
            //    allocation, `A`.
            // 1. Per Lemma 0 and by invariant on `self`, if `ptr`'s referent is
            //    not zero sized, then `ptr` has valid provenance for `A`.
            // 2. Per Lemma 0 and by invariant on `self`, if `ptr`'s referent is
            //    not zero sized, then `ptr` addresses a byte range which is
            //    entirely contained in `A`.
            // 3. Per Lemma 0 and by invariant on `self`, `ptr` addresses a byte
            //    range whose length fits in an `isize`.
            // 4. Per Lemma 0 and by invariant on `self`, `ptr` addresses a byte
            //    range which does not wrap around the address space.
            // 5. Per Lemma 0 and by invariant on `self`, if `ptr`'s referent is
            //    not zero sized, then `A` is guaranteed to live for at least
            //    `'a`.
            // 6. Per Lemma 0 and by invariant on `self`, `ptr` conforms to the
            //    aliasing invariant of [`I::Aliasing`](invariant::Aliasing).
            // 7. Per Lemma 0 and by invariant on `self`, `ptr` conforms to the
            //    alignment invariant of [`I::Alignment`](invariant::Alignment).
            // 8. Per Lemma 0 and by invariant on `self`, `ptr` conforms to the
            //    validity invariant of [`I::Validity`](invariant::Validity).
            unsafe { Ptr::new(ptr) }
        }

        /// Splits the slice in two.
        ///
        /// # Safety
        ///
        /// The caller promises that `l_len <= self.len()`.
        pub(crate) unsafe fn split_at(self, l_len: usize) -> (Self, Self) {
            // SAFETY: `Any` imposes no invariants, and so this is always sound.
            let slf = unsafe { self.assume_aliasing::<Any>() };

            // SAFETY: The caller promises that `l_len <= self.len()`.
            // Trivially, `0 <= l_len`.
            let left = unsafe { slf.slice_unchecked(0..l_len) };

            // SAFETY: The caller promises that `l_len <= self.len() =
            // slf.len()`. Trivially, `slf.len() <= slf.len()`.
            let right = unsafe { slf.slice_unchecked(l_len..slf.len()) };

            // LEMMA: `left` and `right` are non-overlapping. Proof: `left` is
            // constructed from `slf` with `l_len` as its (exclusive) upper
            // bound, while `right` is constructed from `slf` with `l_len` as
            // its (inclusive) lower bound. Thus, no index is a member of both
            // ranges.

            // SAFETY: By the preceding lemma, `left` and `right` do not alias.
            // We do not construct any other `Ptr`s or references which alias
            // `left` or `right`. Thus, the only `Ptr`s or references which
            // alias `left` or `right` are outside of this method. By invariant,
            // `self` obeys the aliasing invariant `I::Aliasing` with respect to
            // those other `Ptr`s or references, and so `left` and `right` do as
            // well.
            let (left, right) = unsafe {
                (left.assume_aliasing::<I::Aliasing>(), right.assume_aliasing::<I::Aliasing>())
            };
            (left.unify_invariants(), right.unify_invariants())
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
                //
                // > - The computed offset, `count * size_of::<T>()` bytes, must
                // >   not overflow `isize``.
                // > - If the computed offset is non-zero, then `self` must be
                // >   derived from a pointer to some allocated object, and the
                // >   entire memory range between `self` and the result must be
                // >   in bounds of that allocated object. In particular, this
                // >   range must not “wrap around” the edge of the address
                // >   space.
                //
                // [1] https://doc.rust-lang.org/std/primitive.pointer.html#method.add
                //
                // We satisfy both of these conditions here:
                // - By invariant on `Ptr`, `self` addresses a byte range whose
                //   length fits in an `isize`. Since `elem` is contained in
                //   `self`, the computed offset of `elem` must fit within
                //   `isize.`
                // - If the computed offset is non-zero, then this means that
                //   the referent is not zero-sized. In this case, `base` points
                //   to an allocated object (by invariant on `self`). Thus:
                //   - By contract, `self.len()` accurately reflects the number
                //     of elements in the slice. `i` is in bounds of `c.len()`
                //     by construction, and so the result of this addition
                //     cannot overflow past the end of the allocation referred
                //     to by `c`.
                //   - By invariant on `Ptr`, `self` addresses a byte range
                //     which does not wrap around the address space. Since
                //     `elem` is contained in `self`, the computed offset of
                //     `elem` must wrap around the address space.
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
                // 0. If `elem`'s referent is not zero sized, then `elem` is
                //    derived from a valid Rust allocation, because `self` is
                //    derived from a valid Rust allocation, by invariant on
                //    `Ptr`.
                // 1. If `elem`'s referent is not zero sized, then `elem` has
                //    valid provenance for `self`, because it derived from
                //    `self` using a series of provenance-preserving operations.
                // 2. If `elem`'s referent is not zero sized, then `elem` is
                //    entirely contained in the allocation of `self` (see
                //    above).
                // 3. `elem` addresses a byte range whose length fits in an
                //    `isize` (see above).
                // 4. `elem` addresses a byte range which does not wrap around
                //    the address space (see above).
                // 5. If `elem`'s referent is not zero sized, then the
                //    allocation of `elem` is guaranteed to live for at least
                //    `'a`, because `elem` is entirely contained in `self`,
                //    which lives for at least `'a` by invariant on `Ptr`.
                // 6. `elem` conforms to the aliasing invariant of `I::Aliasing`
                //    because projection does not impact the aliasing invariant.
                // 7. `elem`, conditionally, conforms to the validity invariant
                //    of `I::Alignment`. If `elem` is projected from data
                //    well-aligned for `[T]`, `elem` will be valid for `T`.
                // 8. `elem`, conditionally, conforms to the validity invariant
                //    of `I::Validity`. If `elem` is projected from data valid
                //    for `[T]`, `elem` will be valid for `T`.
                unsafe { Ptr::new(elem) }
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use core::mem::{self, MaybeUninit};

    use static_assertions::{assert_impl_all, assert_not_impl_any};

    use super::*;
    use crate::{pointer::BecauseImmutable, util::testutil::AU64, FromBytes, Immutable};

    #[test]
    fn test_split_at() {
        const N: usize = 16;
        let mut arr = [1; N];
        let mut ptr = Ptr::from_mut(&mut arr).as_slice();
        for i in 0..=N {
            assert_eq!(ptr.len(), N);
            // SAFETY: `i` is in bounds by construction.
            let (l, r) = unsafe { ptr.reborrow().split_at(i) };
            let l_sum: usize = l.iter().map(Ptr::read_unaligned::<BecauseImmutable>).sum();
            let r_sum: usize = r.iter().map(Ptr::read_unaligned::<BecauseImmutable>).sum();
            assert_eq!(l_sum, i);
            assert_eq!(r_sum, N - i);
            assert_eq!(l_sum + r_sum, N);
        }
    }

    mod test_ptr_try_cast_into_soundness {
        use super::*;

        // This test is designed so that if `Ptr::try_cast_into_xxx` are
        // buggy, it will manifest as unsoundness that Miri can detect.

        // - If `size_of::<T>() == 0`, `N == 4`
        // - Else, `N == 4 * size_of::<T>()`
        //
        // Each test will be run for each metadata in `metas`.
        fn test<T, I, const N: usize>(metas: I)
        where
            T: ?Sized + KnownLayout + Immutable + FromBytes,
            I: IntoIterator<Item = Option<T::PointerMetadata>> + Clone,
        {
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
                        slf: Ptr<'_, T, (Shared, Aligned, Initialized)>,
                    ) -> usize {
                        let t = slf.bikeshed_recall_valid().as_ref();

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

                    for meta in metas.clone().into_iter() {
                        for cast_type in [CastType::Prefix, CastType::Suffix] {
                            if let Ok((slf, remaining)) = Ptr::from_ref(bytes)
                                .try_cast_into::<T, BecauseImmutable>(cast_type, meta)
                            {
                                // SAFETY: All bytes in `bytes` have been
                                // initialized.
                                let len = unsafe { validate_and_get_len(slf) };
                                assert_eq!(remaining.len(), bytes.len() - len);
                                #[allow(unstable_name_collisions)]
                                let bytes_addr = bytes.as_ptr().addr();
                                #[allow(unstable_name_collisions)]
                                let remaining_addr = remaining.as_non_null().as_ptr().addr();
                                match cast_type {
                                    CastType::Prefix => {
                                        assert_eq!(remaining_addr, bytes_addr + len)
                                    }
                                    CastType::Suffix => assert_eq!(remaining_addr, bytes_addr),
                                }

                                if let Some(want) = meta {
                                    let got = KnownLayout::pointer_to_metadata(
                                        slf.as_non_null().as_ptr(),
                                    );
                                    assert_eq!(got, want);
                                }
                            }
                        }

                        if let Ok(slf) = Ptr::from_ref(bytes)
                            .try_cast_into_no_leftover::<T, BecauseImmutable>(meta)
                        {
                            // SAFETY: All bytes in `bytes` have been
                            // initialized.
                            let len = unsafe { validate_and_get_len(slf) };
                            assert_eq!(len, bytes.len());

                            if let Some(want) = meta {
                                let got =
                                    KnownLayout::pointer_to_metadata(slf.as_non_null().as_ptr());
                                assert_eq!(got, want);
                            }
                        }
                    }
                }
            }
        }

        #[derive(FromBytes, KnownLayout, Immutable)]
        #[repr(C)]
        struct SliceDst<T> {
            a: u8,
            trailing: [T],
        }

        // Each test case becomes its own `#[test]` function. We do this because
        // this test in particular takes far, far longer to execute under Miri
        // than all of our other tests combined. Previously, we had these
        // execute sequentially in a single test function. We run Miri tests in
        // parallel in CI, but this test being sequential meant that most of
        // that parallelism was wasted, as all other tests would finish in a
        // fraction of the total execution time, leaving this test to execute on
        // a single thread for the remainder of the test. By putting each test
        // case in its own function, we permit better use of available
        // parallelism.
        macro_rules! test {
            ($test_name:ident: $ty:ty) => {
                #[test]
                #[allow(non_snake_case)]
                fn $test_name() {
                    const S: usize = core::mem::size_of::<$ty>();
                    const N: usize = if S == 0 { 4 } else { S * 4 };
                    test::<$ty, _, N>([None]);

                    // If `$ty` is a ZST, then we can't pass `None` as the
                    // pointer metadata, or else computing the correct trailing
                    // slice length will panic.
                    if S == 0 {
                        test::<[$ty], _, N>([Some(0), Some(1), Some(2), Some(3)]);
                        test::<SliceDst<$ty>, _, N>([Some(0), Some(1), Some(2), Some(3)]);
                    } else {
                        test::<[$ty], _, N>([None, Some(0), Some(1), Some(2), Some(3)]);
                        test::<SliceDst<$ty>, _, N>([None, Some(0), Some(1), Some(2), Some(3)]);
                    }
                }
            };
            ($ty:ident) => {
                test!($ty: $ty);
            };
            ($($ty:ident),*) => { $(test!($ty);)* }
        }

        test!(empty_tuple: ());
        test!(u8, u16, u32, u64, u128, usize, AU64);
        test!(i8, i16, i32, i64, i128, isize);
        test!(f32, f64);
    }

    #[test]
    fn test_invariants() {
        // Test that the correct invariant relationships hold.
        use super::invariant::*;

        assert_not_impl_any!(Any: AtLeast<Shared>);
        assert_impl_all!(Shared: AtLeast<Shared>);
        assert_impl_all!(Exclusive: AtLeast<Shared>);

        assert_not_impl_any!(Any: AtLeast<AsInitialized>);
        assert_impl_all!(AsInitialized: AtLeast<AsInitialized>);
        assert_impl_all!(Initialized: AtLeast<AsInitialized>);
        assert_impl_all!(Valid: AtLeast<AsInitialized>);
    }

    #[test]
    fn test_try_cast_into_explicit_count() {
        macro_rules! test {
            ($ty:ty, $bytes:expr, $elems:expr, $expect:expr) => {{
                let bytes = [0u8; $bytes];
                let ptr = Ptr::from_ref(&bytes[..]);
                let res =
                    ptr.try_cast_into::<$ty, BecauseImmutable>(CastType::Prefix, Some($elems));
                if let Some(expect) = $expect {
                    let (ptr, _) = res.unwrap();
                    assert_eq!(
                        KnownLayout::pointer_to_metadata(ptr.as_non_null().as_ptr()),
                        expect
                    );
                } else {
                    let _ = res.unwrap_err();
                }
            }};
        }

        #[derive(KnownLayout, Immutable)]
        #[repr(C)]
        struct ZstDst {
            u: [u8; 8],
            slc: [()],
        }

        test!(ZstDst, 8, 0, Some(0));
        test!(ZstDst, 7, 0, None);

        test!(ZstDst, 8, usize::MAX, Some(usize::MAX));
        test!(ZstDst, 7, usize::MAX, None);

        #[derive(KnownLayout, Immutable)]
        #[repr(C)]
        struct Dst {
            u: [u8; 8],
            slc: [u8],
        }

        test!(Dst, 8, 0, Some(0));
        test!(Dst, 7, 0, None);

        test!(Dst, 9, 1, Some(1));
        test!(Dst, 8, 1, None);

        // If we didn't properly check for overflow, this would cause the
        // metadata to overflow to 0, and thus the cast would spuriously
        // succeed.
        test!(Dst, 8, usize::MAX - 8 + 1, None);
    }
}
