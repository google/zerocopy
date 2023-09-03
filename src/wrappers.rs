// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use core::{
    cmp::Ordering,
    fmt::{self, Debug, Display, Formatter},
    hash::Hash,
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr,
};

use super::*;

/// An alternative to the standard library's [`MaybeUninit`] that supports
/// unsized types.
///
/// `MaybeUninit<T>` is identical to the standard library's `MaybeUninit` type
/// with the exception that it supports wrapping unsized types. Namely,
/// `MaybeUninit<T>` has the same layout as `T`, but it has no bit validity
/// constraints - any byte of a `MaybeUninit<T>` may have any value, including
/// uninitialized.
///
/// [`MaybeUninit`]: core::mem::MaybeUninit
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct MaybeUninit<T: KnownLayout + ?Sized> {
    inner: T::MaybeUninit,
}

safety_comment! {
    /// SAFETY:
    /// Since `MaybeUninit<T>` is a `repr(transparent)` wrapper around
    /// `T::MaybeUninit`:
    /// - They have the same prefix size, alignment, and trailing slice element
    ///   size
    /// - It is valid to perform an `as` cast in either direction, and this
    ///   operation preserves referent size
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(T::MaybeUninit)] MaybeUninit<T>);
}

impl<T: KnownLayout + ?Sized> Debug for MaybeUninit<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.pad(core::any::type_name::<Self>())
    }
}

impl<T: KnownLayout + ?Sized> MaybeUninit<T> {
    /// Gets a shared reference to the contained value.
    ///
    /// # Safety
    ///
    /// `self` must contain a validly-initialized `T`.
    pub unsafe fn assume_init_ref(&self) -> &T {
        let ptr = T::cast_from_maybe_uninit(NonNull::from(&self.inner));
        // SAFETY: The caller has promised that `self` contains an initialized
        // `T`. Since `Self` is `repr(transparent)`, it has the same layout as
        // `T::MaybeUninit`, which in turn is guaranteed (by safety invariant)
        // to have the same layout as `T`. Thus, it is sound to treat `ptr` as
        // pointing to a valid `T` of the correct size and alignment.
        //
        // Further, thanks to the safety requirements on `T::MaybeUninit`, we
        // know that there are `UnsafeCell`s at the same byte ranges in both
        // types.  See [1] for a discussion of why this is a required safety
        // condition.
        //
        // [1] https://github.com/rust-lang/unsafe-code-guidelines/issues/455
        unsafe { &*ptr.as_ptr() }
    }

    /// Gets a mutable reference to the contained value.
    ///
    /// # Safety
    ///
    /// `self` must contain a validly-initialized `T`.
    pub unsafe fn assume_init_mut(&mut self) -> &mut T {
        let ptr = T::cast_from_maybe_uninit(NonNull::from(&mut self.inner));
        // SAFETY: The caller has promised that `self` contains an initialized
        // `T`. Since `Self` is `repr(transparent)`, it has the same layout as
        // `T::MaybeUninit`, which in turn is guaranteed (by safety invariant)
        // to have the same layout as `T`. Thus, it is sound to treat `ptr` as
        // pointing to a valid `T` of the correct size and alignment.
        //
        // Further, thanks to the safety requirements on `T::MaybeUninit`, we
        // know that there are `UnsafeCell`s at the same byte ranges in both
        // types.  See [1] for a discussion of why this is a required safety
        // condition.
        //
        // [1] https://github.com/rust-lang/unsafe-code-guidelines/issues/455
        unsafe { &mut *ptr.as_ptr() }
    }

    /// Gets a pointer to the contained value.
    ///
    /// Reading from this pointer or turning it into a reference is undefined
    /// behavior unless `self` is initialized. Writing to memory that this
    /// pointer (non-transitively) points to is undefined behavior (except
    /// inside an `UnsafeCell<T>`).
    pub fn as_ptr(&self) -> *const T {
        T::cast_from_maybe_uninit(NonNull::from(&self.inner)).as_ptr().cast_const()
    }

    /// Gets a mutable pointer to the contained value.
    ///
    /// Reading from this pointer or turning it into a reference is undefined
    /// behavior unless `self` is initialized.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        T::cast_from_maybe_uninit(NonNull::from(&mut self.inner)).as_ptr()
    }

    /// Gets a view of this `&T` as a `&MaybeUninit<T>`.
    ///
    /// There is no mutable equivalent to this function, as producing a `&mut
    /// MaybeUninit<T>` from a `&mut T` would allow safe code to write invalid
    /// values which would be accessible through `&mut T`.
    pub fn from_ref(r: &T) -> &MaybeUninit<T> {
        let ptr = T::cast_to_maybe_uninit(NonNull::from(r));
        #[allow(clippy::as_conversions)]
        let ptr = ptr.as_ptr() as *const MaybeUninit<T>;
        // SAFETY: Since `Self` is `repr(transparent)`, it has the same layout
        // as `T::MaybeUninit`, so the size and alignment here are valid.
        //
        // `MaybeUninit<T>` has no bit validity constraints, so this is
        // guaranteed not to produce in invalid `MaybeUninit<T>`. If it were
        // possible to write a different value for `MaybeUninit<T>` through the
        // returned reference, it could result in an invalid value being exposed
        // via the `&T`. Luckily, the only way for mutation to happen is if `T`
        // contains an `UnsafeCell` and the caller uses it to perform interior
        // mutation. Importantly, `T` containing an `UnsafeCell` does not permit
        // interior mutation through `MaybeUninit<T>`, so it doesn't permit
        // writing uninitialized or otherwise invalid values which would be
        // visible through the original `&T`.
        unsafe { &*ptr }
    }
}

impl<T: KnownLayout<MaybeUninit = mem::MaybeUninit<T>> + Sized> MaybeUninit<T> {
    /// Creates a new `MaybeUninit<T>` with the given value.
    pub const fn new(val: T) -> MaybeUninit<T> {
        MaybeUninit { inner: mem::MaybeUninit::new(val) }
    }

    /// Creates a new `MaybeUninit<T>` in an uninitialized state.
    pub const fn uninit() -> MaybeUninit<T> {
        MaybeUninit { inner: mem::MaybeUninit::uninit() }
    }

    /// Creates a new `MaybeUninit<T>` whose bytes are initialized to 0.
    // TODO(https://github.com/rust-lang/rust/issues/91850): Make this const
    // once `MaybeUninit::zeroed` is const.
    pub fn zeroed() -> MaybeUninit<T> {
        MaybeUninit { inner: mem::MaybeUninit::zeroed() }
    }

    /// Extracts the value from the `MaybeUninit<T>` container.
    ///
    /// # Safety
    ///
    /// `assume_init` has the same safety requirements and guarantees as the
    /// standard library's [`MaybeUninit::assume_init`] method.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    pub const unsafe fn assume_init(self) -> T {
        // SAFETY: The caller has promised to uphold the safety invariants of
        // the exact function we're calling here. Since, for `T: Sized`,
        // `MaybeUninit<T>` is a `repr(transparent)` wrapper around
        // `mem::MaybeUninit<T>`, it is sound to treat `Self` as equivalent to a
        // `mem::MaybeUninit<T>` for the purposes of
        // `mem::MaybeUninit::assume_init`'s safety invariants.
        unsafe { self.inner.assume_init() }
    }
}

safety_comment! {
    // `MaybeUninit<T>` is `FromZeroes` and `FromBytes`, but never `AsBytes`
    // since it may contain uninitialized bytes.
    //
    /// SAFETY:
    /// - `FromZeroes`, `FromBytes`: `MaybeUninit<T>` has no restrictions on its
    ///   contents. Unfortunately, in addition to bit validity, `FromZeroes` and
    ///   `FromBytes` also require that implementers contain no `UnsafeCell`s.
    ///   Thus, we require `T: FromZeroes` and `T: FromBytes` in order to ensure
    ///   that `T` - and thus `MaybeUninit<T>` - contains to `UnsafeCell`s.
    ///   Thus, requiring that `T` implement each of these traits is sufficient
    /// - `Unaligned`: `MaybeUninit<T>` is guaranteed by its documentation [1]
    ///   to have the same alignment as `T`.
    ///
    /// [1] https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#layout-1
    ///
    /// TODO(https://github.com/google/zerocopy/issues/251): If we split
    /// `FromBytes` and `RefFromBytes`, or if we introduce a separate
    /// `NoCell`/`Freeze` trait, we can relax the trait bounds for `FromZeroes`
    /// and `FromBytes`.
    unsafe_impl!(T: ?Sized + KnownLayout + FromZeroes => FromZeroes for MaybeUninit<T>);
    unsafe_impl!(T: ?Sized + KnownLayout + FromBytes => FromBytes for MaybeUninit<T>);
    unsafe_impl!(T: ?Sized + KnownLayout + Unaligned => Unaligned for MaybeUninit<T>);
    assert_unaligned!(mem::MaybeUninit<()>, MaybeUninit<u8>);
}

/// A value which might or might not constitute a valid instance of `T`.
///
/// `MaybeValid<T>` has the same layout (size and alignment) and field offsets
/// as `T`. Unlike `T`, it may contain any bit pattern, except that
/// uninitialized bytes may only appear in `MaybeValid<T>` at byte offsets where
/// they may appear in `T`. This is a dynamic property: if, at a particular byte
/// offset, a valid enum discriminant is set, the subsequent bytes may only have
/// uninitialized bytes as specified by the corresponding enum variant.
///
/// Formally, given `m: MaybeValid<T>` and a byte offset, `b` in the range `[0,
/// size_of_val(m))`:
/// - If, in all valid instances `t: T`, the byte at offset `b` in `t` is
///   initialized, then the byte at offset `b` within `m` is guaranteed to be
///   initialized.
/// - Let `c` be the contents of the byte range `[0, b)` in `m`. Let `TT` be the
///   subset of valid instances of `T` which contain `c` in the offset range
///   `[0, b)`. If, for all instances of `t: T` in `TT`, the byte at offset `b`
///   in `t` is initialized, then the byte at offset `b` in `m` is guaranteed to
///   be initialized.
///
///   Pragmatically, this means that if `m` is guaranteed to contain an enum
///   type at a particular offset, and the enum discriminant stored in `m`
///   corresponds to a valid variant of that enum type, then it is guaranteed
///   that the appropriate bytes of `m` are initialized as defined by that
///   variant's bit validity (although note that the variant may contain another
///   enum type, in which case the same rules apply depending on the state of
///   its discriminant, and so on recursively).
///
/// # Safety
///
/// Unsafe code may assume that an instance of `MaybeValid` satisfies the
/// constraints described above. Unsafe code may produce a `MaybeValid` or
/// modify the bytes of an existing `MaybeValid` so long as these constraints
/// are upheld. It is unsound to produce a `MaybeValid` which fails to uphold
/// these constraints.
#[repr(transparent)]
pub struct MaybeValid<T: ?Sized + KnownLayout> {
    inner: MaybeUninit<T>,
}

safety_comment! {
    /// SAFETY:
    /// - `AsBytes`: `MaybeValid` requires that, if a byte in `T` is always
    ///   initialized, the equivalent byte in `MaybeValid<T>` must be
    ///   initialized. `T: AsBytes` implies that all bytes in `T` must always be
    ///   initialized, and so all bytes in `MaybeValid<T>` must always be
    ///   initialized, and so `MaybeValid<T>` satisfies `AsBytes`.
    /// - `Unaligned`: `MaybeValid<T>` has the same alignment as `T`.
    /// - `KnownLayout`: Since `MaybeUninit<T>` is a `repr(transparent)` wrapper
    ///   around `T::MaybeUninit`:
    ///   - They have the same prefix size, alignment, and trailing slice
    ///     element size
    ///   - It is valid to perform an `as` cast in either direction, and this
    ///     operation preserves referent size
    ///
    /// TODO(#5): Implement `FromZeroes` and `FromBytes` for `MaybeValid<T>` and
    /// `MaybeValid<[T]>`.
    unsafe_impl!(T: ?Sized + KnownLayout + AsBytes => AsBytes for MaybeValid<T>);
    unsafe_impl!(T: ?Sized + KnownLayout + Unaligned => Unaligned for MaybeValid<T>);
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(MaybeUninit<T>)] MaybeValid<T>);
}

impl<T: KnownLayout<MaybeUninit = mem::MaybeUninit<T>>> Default for MaybeValid<T> {
    fn default() -> MaybeValid<T> {
        // SAFETY: All of the bytes of `inner` are initialized to 0, and so the
        // safety invariant on `MaybeValid` is upheld.
        MaybeValid { inner: MaybeUninit::zeroed() }
    }
}

impl<T: KnownLayout + ?Sized> MaybeValid<T> {
    /// Converts this `&MaybeValid<T>` to a `&T`.
    ///
    /// # Safety
    ///
    /// `self` must contain a valid `T`.
    pub unsafe fn assume_valid_ref(&self) -> &T {
        // SAFETY: The caller has promised that `self` contains a valid `T`.
        // Since `Self` is `repr(transparent)`, it has the same layout as
        // `MaybeUninit<T>`, which in turn is guaranteed to have the same layout
        // as `T`. Thus, it is sound to treat `self.inner` as containing a valid
        // `T`.
        unsafe { self.inner.assume_init_ref() }
    }

    /// Converts this `&mut MaybeValid<T>` to a `&mut T`.
    ///
    /// # Safety
    ///
    /// `self` must contain a valid `T`.
    pub unsafe fn assume_valid_mut(&mut self) -> &mut T {
        // SAFETY: The caller has promised that `self` contains a valid `T`.
        // Since `Self` is `repr(transparent)`, it has the same layout as
        // `MaybeUninit<T>`, which in turn is guaranteed to have the same layout
        // as `T`. Thus, it is sound to treat `self.inner` as containing a valid
        // `T`.
        unsafe { self.inner.assume_init_mut() }
    }

    /// Gets a view of this `&T` as a `&MaybeValid<T>`.
    ///
    /// There is no mutable equivalent to this function, as producing a `&mut
    /// MaybeValid<T>` from a `&mut T` would allow safe code to write invalid
    /// values which would be accessible through `&mut T`.
    pub fn from_ref(r: &T) -> &MaybeValid<T> {
        let m: *const MaybeUninit<T> = MaybeUninit::from_ref(r);
        #[allow(clippy::as_conversions)]
        let ptr = m as *const MaybeValid<T>;
        // SAFETY: Since `Self` is `repr(transparent)`, it has the same layout
        // as `MaybeUninit<T>`, so the size and alignment here are valid.
        //
        // `MaybeValid<T>`'s bit validity constraints are weaker than those of
        // `T`, so this is guaranteed not to produce an invalid `MaybeValid<T>`.
        // If it were possible to write a different value for `MaybeValid<T>`
        // through the returned reference, it could result in an invalid value
        // being exposed via the `&T`. Luckily, the only way for mutation to
        // happen is if `T` contains an `UnsafeCell` and the caller uses it to
        // perform interior mutation. Importantly, `T` containing an
        // `UnsafeCell` does not permit interior mutation through
        // `MaybeValid<T>`, so it doesn't permit writing uninitialized or
        // otherwise invalid values which would be visible through the original
        // `&T`.
        unsafe { &*ptr }
    }
}

impl<T: KnownLayout<MaybeUninit = mem::MaybeUninit<T>>> MaybeValid<T> {
    /// Converts this `MaybeValid<T>` to a `T`.
    ///
    /// # Safety
    ///
    /// `self` must contain a valid `T`.
    pub const unsafe fn assume_valid(self) -> T {
        // SAFETY: The caller has promised that `self` contains a valid `T`.
        // Since `Self` is `repr(transparent)`, it has the same layout as
        // `MaybeUninit<T>`, which in turn is guaranteed to have the same layout
        // as `T`. Thus, it is sound to treat `self.inner` as containing a valid
        // `T`.
        unsafe { self.inner.assume_init() }
    }
}

impl<T: KnownLayout<MaybeUninit = mem::MaybeUninit<T>>> MaybeValid<[T]> {
    /// Converts a `MaybeValid<[T]>` to a `[MaybeValid<T>]`.
    ///
    /// `MaybeValid<T>` has the same layout as `T`, so these layouts are
    /// equivalent.
    pub const fn as_slice_of_maybe_valids(&self) -> &[MaybeValid<T>] {
        let inner: &[<T as KnownLayout>::MaybeUninit] = &self.inner.inner;
        let inner_ptr: *const [<T as KnownLayout>::MaybeUninit] = inner;
        // Note: this Clippy warning is only emitted on our MSRV (1.61), but not
        // on later versions of Clippy. Thus, we consider it spurious.
        #[allow(clippy::as_conversions)]
        let ret_ptr = inner_ptr as *const [MaybeValid<T>];
        // SAFETY: Since `inner` is a `&[MaybeUninit<T>]`, and `MaybeValid<T>`
        // is a `repr(transparent)` struct around `MaybeUninit<T>`, `inner` has
        // the same layout as `&[MaybeValid<T>]`.
        unsafe { &*ret_ptr }
    }
}

impl<const N: usize, T: KnownLayout> MaybeValid<[T; N]> {
    /// Converts a `MaybeValid<[T; N]>` to a `MaybeValid<[T]>`.
    // TODO(#64): Make this `const` once our MSRV is >= 1.64.0 (when
    // `slice_from_raw_parts` was stabilized as `const`).
    pub fn as_slice(&self) -> &MaybeValid<[T]> {
        let base: *const MaybeValid<[T; N]> = self;
        let slice_of_t: *const [T] = ptr::slice_from_raw_parts(base.cast::<T>(), N);
        // Note: this Clippy warning is only emitted on our MSRV (1.61), but not
        // on later versions of Clippy. Thus, we consider it spurious.
        #[allow(clippy::as_conversions)]
        let mv_of_slice = slice_of_t as *const MaybeValid<[T]>;
        // SAFETY: `MaybeValid<T>` is a `repr(transparent)` wrapper around
        // `MaybeUninit<T>`, which in turn has the same layout as `T`. Thus, the
        // trailing slices of `[T]` and of `MaybeValid<[T]>` both have element
        // type `T`. Since the number of elements is preserved during an `as`
        // cast of slice/DST pointers, the resulting `*const MaybeValid<[T]>`
        // has the same number of elements - and thus the same length - as the
        // original `*const [T]`.
        //
        // Thanks to their layouts, `MaybeValid<[T; N]>` and `MaybeValid<[T]>`
        // have the same alignment, so `mv_of_slice` is guaranteed to be
        // aligned.
        unsafe { &*mv_of_slice }
    }
}

impl<T: ?Sized + KnownLayout> Debug for MaybeValid<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.pad(core::any::type_name::<Self>())
    }
}

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
#[cfg_attr(any(feature = "derive", test), derive(FromZeroes, FromBytes, AsBytes, Unaligned))]
#[repr(C, packed)]
pub struct Unalign<T>(T);

safety_comment! {
    /// SAFETY:
    /// - `Unalign<T>` is `repr(packed)`, so it is unaligned regardless of the
    ///   alignment of `T`, and so we don't require that `T: Unaligned`
    /// - `Unalign<T>` has the same bit validity as `T`, and so it is
    ///   `FromZeroes`, `FromBytes`, or `AsBytes` exactly when `T` is as well.
    impl_or_verify!(T => Unaligned for Unalign<T>);
    impl_or_verify!(T: FromZeroes => FromZeroes for Unalign<T>);
    impl_or_verify!(T: FromBytes => FromBytes for Unalign<T>);
    impl_or_verify!(T: AsBytes => AsBytes for Unalign<T>);
}

// Note that `Unalign: Clone` only if `T: Copy`. Since the inner `T` may not be
// aligned, there's no way to safely call `T::clone`, and so a `T: Clone` bound
// is not sufficient to implement `Clone` for `Unalign`.
impl<T: Copy> Clone for Unalign<T> {
    fn clone(&self) -> Unalign<T> {
        *self
    }
}

impl<T> Unalign<T> {
    /// Constructs a new `Unalign`.
    pub const fn new(val: T) -> Unalign<T> {
        Unalign(val)
    }

    /// Consumes `self`, returning the inner `T`.
    pub const fn into_inner(self) -> T {
        // Use this instead of `mem::transmute` since the latter can't tell
        // that `Unalign<T>` and `T` have the same size.
        #[repr(C)]
        union Transmute<T> {
            u: ManuallyDrop<Unalign<T>>,
            t: ManuallyDrop<T>,
        }

        // SAFETY: Since `Unalign` is `#[repr(C, packed)]`, it has the same
        // layout as `T`. `ManuallyDrop<U>` is guaranteed to have the same
        // layout as `U`, and so `ManuallyDrop<Unalign<T>>` has the same layout
        // as `ManuallyDrop<T>`. Since `Transmute<T>` is `#[repr(C)]`, its `t`
        // and `u` fields both start at the same offset (namely, 0) within the
        // union.
        //
        // We do this instead of just destructuring in order to prevent
        // `Unalign`'s `Drop::drop` from being run, since dropping is not
        // supported in `const fn`s.
        //
        // TODO(https://github.com/rust-lang/rust/issues/73255): Destructure
        // instead of using unsafe.
        unsafe { ManuallyDrop::into_inner(Transmute { u: ManuallyDrop::new(self) }.t) }
    }

    /// Attempts to return a reference to the wrapped `T`, failing if `self` is
    /// not properly aligned.
    ///
    /// If `self` does not satisfy `mem::align_of::<T>()`, then it is unsound to
    /// return a reference to the wrapped `T`, and `try_deref` returns `None`.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements [`Deref`], and callers
    /// may prefer [`Deref::deref`], which is infallible.
    pub fn try_deref(&self) -> Option<&T> {
        if !crate::util::aligned_to::<_, T>(self) {
            return None;
        }

        // SAFETY: `deref_unchecked`'s safety requirement is that `self` is
        // aligned to `align_of::<T>()`, which we just checked.
        unsafe { Some(self.deref_unchecked()) }
    }

    /// Attempts to return a mutable reference to the wrapped `T`, failing if
    /// `self` is not properly aligned.
    ///
    /// If `self` does not satisfy `mem::align_of::<T>()`, then it is unsound to
    /// return a reference to the wrapped `T`, and `try_deref_mut` returns
    /// `None`.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements [`DerefMut`], and
    /// callers may prefer [`DerefMut::deref_mut`], which is infallible.
    pub fn try_deref_mut(&mut self) -> Option<&mut T> {
        if !crate::util::aligned_to::<_, T>(&*self) {
            return None;
        }

        // SAFETY: `deref_mut_unchecked`'s safety requirement is that `self` is
        // aligned to `align_of::<T>()`, which we just checked.
        unsafe { Some(self.deref_mut_unchecked()) }
    }

    /// Returns a reference to the wrapped `T` without checking alignment.
    ///
    /// If `T: Unaligned`, then `Unalign<T>` implements[ `Deref`], and callers
    /// may prefer [`Deref::deref`], which is safe.
    ///
    /// # Safety
    ///
    /// If `self` does not satisfy `mem::align_of::<T>()`, then
    /// `self.deref_unchecked()` may cause undefined behavior.
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
    /// If `self` does not satisfy `mem::align_of::<T>()`, then
    /// `self.deref_mut_unchecked()` may cause undefined behavior.
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
    /// of `get_ptr` will be undefined behavior if alignment is not guaranteed
    /// using some out-of-band mechanism. In general, the only functions which
    /// are safe to call with this pointer are those which are explicitly
    /// documented as being sound to use with an unaligned pointer, such as
    /// [`read_unaligned`].
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
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
    /// of `get_ptr` will be undefined behavior if alignment is not guaranteed
    /// using some out-of-band mechanism. In general, the only functions which
    /// are safe to call with this pointer are those which are explicitly
    /// documented as being sound to use with an unaligned pointer, such as
    /// [`read_unaligned`].
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
    // TODO(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
    pub fn get_mut_ptr(&mut self) -> *mut T {
        ptr::addr_of_mut!(self.0)
    }

    /// Sets the inner `T`, dropping the previous value.
    // TODO(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
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
    pub fn update<O, F: FnOnce(&mut T) -> O>(&mut self, f: F) -> O {
        // On drop, this moves `copy` out of itself and uses `ptr::write` to
        // overwrite `slf`.
        struct WriteBackOnDrop<T> {
            copy: ManuallyDrop<T>,
            slf: *mut Unalign<T>,
        }

        impl<T> Drop for WriteBackOnDrop<T> {
            fn drop(&mut self) {
                // SAFETY: See inline comments.
                unsafe {
                    // SAFETY: We never use `copy` again as required by
                    // `ManuallyDrop::take`.
                    let copy = ManuallyDrop::take(&mut self.copy);
                    // SAFETY: `slf` is the raw pointer value of `self`. We know
                    // it is valid for writes and properly aligned because
                    // `self` is a mutable reference, which guarantees both of
                    // these properties.
                    ptr::write(self.slf, Unalign::new(copy));
                }
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
    // TODO(https://github.com/rust-lang/rust/issues/57349): Make this `const`.
    pub fn get(&self) -> T {
        let Unalign(val) = *self;
        val
    }
}

impl<T: Unaligned> Deref for Unalign<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: `deref_unchecked`'s safety requirement is that `self` is
        // aligned to `align_of::<T>()`. `T: Unaligned` guarantees that
        // `align_of::<T>() == 1`, and all pointers are one-aligned because all
        // addresses are divisible by 1.
        unsafe { self.deref_unchecked() }
    }
}

impl<T: Unaligned> DerefMut for Unalign<T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: `deref_mut_unchecked`'s safety requirement is that `self` is
        // aligned to `align_of::<T>()`. `T: Unaligned` guarantees that
        // `align_of::<T>() == 1`, and all pointers are one-aligned because all
        // addresses are divisible by 1.
        unsafe { self.deref_mut_unchecked() }
    }
}

impl<T: Unaligned + PartialOrd> PartialOrd<Unalign<T>> for Unalign<T> {
    fn partial_cmp(&self, other: &Unalign<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(self.deref(), other.deref())
    }
}

impl<T: Unaligned + Ord> Ord for Unalign<T> {
    fn cmp(&self, other: &Unalign<T>) -> Ordering {
        Ord::cmp(self.deref(), other.deref())
    }
}

impl<T: Unaligned + PartialEq> PartialEq<Unalign<T>> for Unalign<T> {
    fn eq(&self, other: &Unalign<T>) -> bool {
        PartialEq::eq(self.deref(), other.deref())
    }
}

impl<T: Unaligned + Eq> Eq for Unalign<T> {}

impl<T: Unaligned + Hash> Hash for Unalign<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.deref().hash(state);
    }
}

impl<T: Unaligned + Debug> Debug for Unalign<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.deref(), f)
    }
}

impl<T: Unaligned + Display> Display for Unalign<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

#[cfg(test)]
mod tests {
    use core::panic::AssertUnwindSafe;

    use super::*;
    use crate::util::testutil::*;

    /// A `T` which is guaranteed not to satisfy `align_of::<A>()`.
    ///
    /// It must be the case that `align_of::<T>() < align_of::<A>()` in order
    /// fot this type to work properly.
    #[repr(C)]
    struct ForceUnalign<T, A> {
        // The outer struct is aligned to `A`, and, thanks to `repr(C)`, `t` is
        // placed at the minimum offset that guarantees its alignment. If
        // `align_of::<T>() < align_of::<A>()`, then that offset will be
        // guaranteed *not* to satisfy `align_of::<A>()`.
        _u: u8,
        t: T,
        _a: [A; 0],
    }

    impl<T, A> ForceUnalign<T, A> {
        const fn new(t: T) -> ForceUnalign<T, A> {
            ForceUnalign { _u: 0, t, _a: [] }
        }
    }

    #[test]
    fn test_maybe_uninit() {
        let m = MaybeUninit::new(1usize);
        // SAFETY: `m` was initialized with a valid `usize`.
        assert_eq!(unsafe { m.assume_init() }, 1);

        let mut m = MaybeUninit::<usize>::uninit();
        // SAFETY: Writing a valid `usize`.
        unsafe { core::ptr::write(m.as_mut_ptr(), 1) };
        // SAFETY: We just initialized `m`.
        assert_eq!(unsafe { m.assume_init_ref() }, &1);
        // SAFETY: We just initialized `m`.
        assert_eq!(unsafe { m.assume_init_mut() }, &mut 1);
        // SAFETY: We just initialized `m`.
        assert_eq!(unsafe { m.assume_init() }, 1);

        let mut bytes = [0u8, 1, 2];
        let bytes_mut = &mut bytes[..];

        // SAFETY: `MaybeUninit<[u8]>` has the same layout as `[u8]`.
        let m = unsafe {
            // Assign to `m` rather than leaving as a trailing expression
            // because annotations on expressions are unstable.
            #[allow(clippy::as_conversions)]
            let m = &mut *(bytes_mut as *mut [u8] as *mut MaybeUninit<[u8]>);
            m
        };

        // // SAFETY: `m` was created from an initialized value.
        // let r = unsafe { m.assume_init_ref() };
        // assert_eq!(r.len(), 3);
        // assert_eq!(r, [0, 1, 2]);

        // SAFETY: `m` was created from an initialized value.
        let r = unsafe { m.assume_init_mut() };
        assert_eq!(r.len(), 3);
        assert_eq!(r, [0, 1, 2]);

        r[0] = 1;
        assert_eq!(bytes, [1, 1, 2]);
    }

    #[test]
    fn test_maybe_uninit_zeroed() {
        let m = MaybeUninit::<usize>::zeroed();
        // SAFETY: `m` was initialized with zeroes, which constitute a valid
        // instance of `usize`.
        assert_eq!(unsafe { m.assume_init() }, 0);
    }

    #[test]
    fn test_maybe_uninit_from_ref() {
        use core::cell::Cell;

        let u = 1usize;
        let m = MaybeUninit::from_ref(&u);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_init_ref() }, &1usize);

        // Test that interior mutability doesn't affect correctness or
        // soundness.

        let c = Cell::new(1usize);
        let m = MaybeUninit::from_ref(&c);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_init_ref() }, &Cell::new(1));

        c.set(2);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_init_ref() }, &Cell::new(2));
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
        assert_eq!(u.t.try_deref(), Some(&AU64(123)));
        assert_eq!(u.t.try_deref_mut(), Some(&mut AU64(123)));
        // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
        assert_eq!(unsafe { u.t.deref_unchecked() }, &AU64(123));
        // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
        assert_eq!(unsafe { u.t.deref_mut_unchecked() }, &mut AU64(123));
        *u.t.try_deref_mut().unwrap() = AU64(321);
        assert_eq!(u.t.get(), AU64(321));

        // Test methods that depend on alignment (when alignment is not
        // satisfied).
        let mut u: ForceUnalign<_, AU64> = ForceUnalign::new(Unalign::new(AU64(123)));
        assert_eq!(u.t.try_deref(), None);
        assert_eq!(u.t.try_deref_mut(), None);

        // Test methods that depend on `T: Unaligned`.
        let mut u = Unalign::new(123u8);
        assert_eq!(u.try_deref(), Some(&123));
        assert_eq!(u.try_deref_mut(), Some(&mut 123));
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
        // TODO(https://github.com/rust-lang/rust/issues/104084): Remove this
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
                _ => unreachable!(),
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
    }
}
