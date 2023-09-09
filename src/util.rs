// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[path = "third_party/rust/layout.rs"]
pub(crate) mod core_layout;

use core::{
    fmt::{Debug, Formatter},
    marker::PhantomData,
    mem,
    num::NonZeroUsize,
    ptr::NonNull,
};

use crate::{CastType, KnownLayout};

// For each polyfill, as soon as the corresponding feature is stable, the
// polyfill import will be unused because method/function resolution will prefer
// the inherent method/function over a trait method/function. Thus, we suppress
// the `unused_imports` warning.
//
// See the documentation on `util::polyfills` for more information.
#[allow(unused_imports)]
use crate::util::polyfills::NonNullSliceExt as _;

/// A raw pointer with more restrictions.
///
/// `Ptr<T>` is similar to `NonNull<T>`, but it is more restrictive in the
/// following ways:
/// - It must derive from a valid allocation
/// - It must reference a byte range which is contained inside the allocation
///   from which it derives
///   - As a consequence, the byte range it references must have a size which
///     does not overflow `isize`
/// - It must satisfy `T`'s alignment requirement
///
/// Thanks to these restrictions, it is easier to prove the soundness of some
/// operations using `Ptr`s.
///
/// `Ptr<'a, T>` is [covariant] in `'a` and `T`.
///
/// [covariant]: https://doc.rust-lang.org/reference/subtyping.html
#[doc(hidden)]
pub struct Ptr<'a, T: 'a + ?Sized> {
    // INVARIANTS:
    // - `ptr` is derived from some valid Rust allocation, `A`
    // - `ptr` has the same provenance as `A`
    // - `ptr` addresses a byte range which is entirely contained in `A`
    // - `ptr` addresses a byte range which is not longer than `isize::MAX`
    // - `ptr` addresses a byte range which does not wrap around the address
    //   space
    // - `ptr` is validly-aligned for `T`
    // - `A` is guaranteed to live for at least `'a`
    // - `T: 'a`
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, T: ?Sized> Copy for Ptr<'a, T> {}
impl<'a, T: ?Sized> Clone for Ptr<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: ?Sized> Ptr<'a, T> {
    /// Returns a shared reference to the value.
    ///
    /// # Safety
    ///
    /// TODO(#29), TODO(#429): What is the right way to articulate the safety
    /// invariant here? I can see two possible approaches:
    /// - Mimic the invariants on [`NonNull::as_ref`] so that it's easy to write
    ///   the safety comment on the inner call to `self.ptr.as_ref()`.
    /// - Simply say that it's the caller's responsibility to ensure that the
    ///   resulting reference is valid.
    ///
    /// These two approaches should in principle be equivalent, but since our
    /// memory model is undefined, there are some subtleties here. See, e.g.:
    /// <https://github.com/rust-lang/unsafe-code-guidelines/issues/463#issuecomment-1736771593>
    ///
    /// # Old draft of Safety section
    ///
    /// - The referenced memory must contain a validly-initialized `T` for the
    ///   duration of `'a`. Note that this requires that any interior mutation
    ///   (i.e. via [`UnsafeCell`]) performed after this method call leave the
    ///   memory region always containing a valid `T`.
    /// - The referenced memory must not also by referenced by any mutable
    ///   references during the lifetime `'a`.
    /// - There must not exist any references to the same memory region which
    ///   contain `UnsafeCell`s at byte ranges which are not identical to the
    ///   byte ranges at which `T` contains `UnsafeCell`s.
    ///
    /// TODO: What about reads/mutation via raw pointers? Presumably these can
    /// happen under the following conditions:
    /// - Mutation only occurs inside `UnsafeCell`s
    /// - Reads only happen using `UnsafeCell`s in places where there are
    ///   `UnsafeCell`s in `T` (otherwise, those reads could be unsound due to
    ///   assuming no concurrent mutation)
    ///
    /// [`UnsafeCell`]: core::cell::UnsafeCell
    pub(crate) unsafe fn as_ref(&self) -> &'a T {
        // TODO(#429): Add a safety comment. This will depend on how we resolve
        // the question about how to define the safety invariants on this
        // method.
        //
        // Old draft of safety comment:
        // - By invariant, `self.ptr` is properly-aligned for `T`.
        // - By invariant, `self.ptr` is "dereferenceable" in that it points to
        //   a single allocation
        // - By invariant, the allocation is live for `'a`
        // - The caller promises that no mutable references exist to this region
        //   during `'a`
        // - The caller promises that `UnsafeCell`s match exactly
        // - The caller promises that the memory region contains a
        //   validly-intialized `T`
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            self.ptr.as_ref()
        }
    }

    /// Returns a unique reference to the value.
    ///
    /// # Safety
    ///
    /// - The referenced memory must contain a validly-initialized `T`.
    /// - The referenced memory must not also be referenced by any other
    ///   references during the lifetime `'a`.
    ///
    /// [`UnsafeCell`]: core::cell::UnsafeCell
    pub(crate) unsafe fn as_mut(&mut self) -> &'a mut T {
        // SAFETY:
        // - By invariant, `self.ptr` is properly-aligned for `T`.
        // - By invariant, `self.ptr` is "dereferenceable" in that it points to
        //   a single allocation
        // - By invariant, the allocation is live for `'a`
        // - The caller promises that no other references exist to this memory
        //   region for `'a`
        // - The caller promises that the memory region contains a
        //   validly-intialized `T`
        unsafe { self.ptr.as_mut() }
    }

    /// TODO
    ///
    /// # Safety
    ///
    /// The caller promises that, given `t: *mut T` and `u: *mut U` with the
    /// same pointer metadata, `u` references an object which is less than or
    /// equal to the size of the object referenced by `t`.
    pub(crate) unsafe fn cast<U>(self) -> Ptr<'a, U> {
        // SAFETY: We pass a vanilla `as` cast for the `cast` argument as
        // required. The caller is responsible for guaranteeing the size
        // relationship.
        unsafe { self.cast_unsized(|p| p as *mut _) }
    }

    /// TODO
    ///
    /// # Safety
    ///
    /// The caller promises that
    /// - `cast(p)` is implemented exactly as follows: `|p: *mut T| p as *mut U`
    /// - The size of the object referenced by the resulting pointer is less
    ///   than or equal to the size of the object referenced by `self`
    pub(crate) unsafe fn cast_unsized<U: 'a + ?Sized>(
        self,
        cast: impl FnOnce(*mut T) -> *mut U,
    ) -> Ptr<'a, U> {
        let ptr = cast(self.ptr.as_ptr());
        // SAFETY: Caller promises that `cast` is just an `as` cast. We call
        // `cast` on `self.ptr.as_ptr()`, which is non-null by construction.
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        // SAFETY: TODO
        Ptr { ptr, _lifetime: PhantomData }
    }

    /// TODO
    ///
    /// # Safety
    ///
    /// TODO
    #[doc(hidden)]
    pub unsafe fn project<U: 'a + ?Sized>(
        self,
        project: impl FnOnce(*mut T) -> *mut U,
    ) -> Ptr<'a, U> {
        let field = project(self.ptr.as_ptr());
        // SAFETY: TODO
        let field = unsafe { NonNull::new_unchecked(field) };
        // SAFETY: TODO
        Ptr { ptr: field, _lifetime: PhantomData }
    }
}

impl<'a, T: 'a> Ptr<'a, [T]> {
    pub(crate) fn len(&self) -> usize {
        // TODO(#67): Remove this allow. See NonNullSliceExt for more details.
        #[allow(unstable_name_collisions)]
        self.ptr.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Ptr<'a, T>> {
        let base = self.ptr.cast::<T>().as_ptr();
        (0..self.len()).map(move |i| {
            // TODO(https://github.com/rust-lang/rust/issues/74265): Use
            // `NonNull::get_unchecked_mut`.

            // SAFETY: TODO
            //
            // Old safety comment:
            //
            // SAFETY:
            // - `i` is in bounds of `c.len()` by construction, and so the
            //   result of this addition cannot overflow past the end of the
            //   allocation referred to by `c`.
            // - It is a precondition of `is_bit_valid` that the total length
            //   encoded by `c` doesn't overflow `isize`.
            // - Since `c` must point to a valid allocation, and valid
            //   allocations cannot wrap around the address space, we know that
            //   this addition will not wrap around either.
            let elem = unsafe { base.add(i) };
            // SAFETY: TODO
            //
            // Old safety comment:
            //
            // SAFETY: `base` is constructed from a `NonNull` pointer, and the
            // addition that produces `elem` is guaranteed not to wrap
            // around/overflow, so `elem >= base > 0`.
            let elem = unsafe { NonNull::new_unchecked(elem) };
            // SAFETY: TODO
            Ptr { ptr: elem, _lifetime: PhantomData }
        })
    }
}

impl<'a, const N: usize, T: 'a> Ptr<'a, [T; N]> {
    pub(crate) fn as_slice(&self) -> Ptr<'a, [T]> {
        let ptr = NonNull::slice_from_raw_parts(self.ptr.cast::<T>(), N);
        // SAFETY: TODO
        Ptr { ptr, _lifetime: PhantomData }
    }
}

impl<'a> Ptr<'a, [u8]> {
    /// Attempts to cast `self` to a `U` using the given cast type.
    ///
    /// Returns `None` if the resulting `U` would be invalidly-aligned or if no
    /// `U` can fit in `self`. On success, returns a pointer to the
    /// largest-possible `U` which fits in `self`.
    ///
    /// # Safety
    ///
    /// The caller may assume that this implementation is correct, and may rely
    /// on that assumption for the soundness of their code. In particular, the
    /// caller may assume that, if `try_cast_into` returns `Some((ptr,
    /// split_at))`, then:
    /// - If this is a prefix cast, `ptr` refers to the byte range `[0,
    ///   split_at)` in `self`.
    /// - If this is a suffix cast, `ptr` refers to the byte range `[split_at,
    ///   self.len())` in `self`.
    ///
    /// # Panics
    ///
    /// Panics if `U` is a DST whose trailing slice element is zero-sized.
    pub(crate) fn try_cast_into<U: 'a + ?Sized + KnownLayout>(
        &self,
        cast_type: CastType,
    ) -> Option<(Ptr<'a, U>, usize)> {
        // PANICS: By invariant, the byte range addressed by `self.ptr` does not
        // wrap around the address space. This implies that the sum of the
        // address (represented as a `usize`) and length do not overflow
        // `usize`, as required by `validate_cast_and_convert_metadata`. Thus,
        // this call to `validate_cast_and_convert_metadata` won't panic.
        let (elems, split_at) = U::LAYOUT.validate_cast_and_convert_metadata(
            AsAddress::addr(self.ptr.as_ptr()),
            self.len(),
            cast_type,
        )?;
        let offset = match cast_type {
            CastType::Prefix => 0,
            CastType::_Suffix => split_at,
        };

        let ptr = self.ptr.cast::<u8>().as_ptr();
        // SAFETY: `offset` is either `0` or `split_at`.
        // `validate_cast_and_convert_metadata` promises that `split_at` is in
        // the range `[0, bytes_len)`, where `bytes_len` is the length argument
        // to `validate_cast_and_convert_metadata`. Thus, in both cases,
        // `offset` is in `[0, bytes_len)`. For `bytes_len`, we pass the length
        // of `self`. Thus:
        // - The resulting pointer is in or one byte past the end of the same
        //   byte range as `self.ptr`. Since, by invariant, `self.ptr` addresses
        //   a byte range entirely contained within a single allocation, the
        //   pointer resulting from this operation is within or one byte past
        //   the end of that same allocation.
        // - By invariant, `bytes_len <= isize::MAX`. Since `offset <=
        //   bytes_len`, `offset <= isize::MAX`.
        // - By invariant, `self.ptr` addresses a byte range which does not wrap
        //   around the address space. This means that the base pointer plus the
        //   `bytes_len` does not overflow `usize`. Since `offset <= bytes_len`,
        //   this addition does not overflow `usize`.
        let base = unsafe { ptr.add(offset) };
        // SAFETY: Since `add` is not allowed to wrap around, the preceding line
        // produces a pointer whose address is greater than or equal to that of
        // `ptr`. Since `ptr` is a `NonNull`, `base` is also non-null.
        let base = unsafe { NonNull::new_unchecked(base) };
        let ptr = U::raw_from_ptr_len(base, elems);
        // SAFETY:
        // - By invariant, `self.ptr` is derived from some valid Rust
        //   allocation, `A`, and has the same provenance as `A`. All operations
        //   performed on `self.ptr` and values derived from it in this method
        //   preserve provenance, so:
        //   - `ptr` is derived from a valid Rust allocation, `A`.
        //   - `ptr` has the same provenance as `A`.
        // - `validate_cast_and_convert_metadata` promises that the object
        //   described by `elems` and `split_at` lives at a byte range which is
        //   a subset of the input byte range. Thus:
        //   - Since, by invariant, `self.ptr` addresses a byte range entirely
        //     contained in `A`, so does `ptr`.
        //   - Since, by invariant, `self.ptr` addresses a range not longer than
        //     `isize::MAX` bytes, so does `ptr`.
        //   - Since, by invariant, `self.ptr` addresses a range which does not
        //     wrap around the address space, so does `ptr`.
        // - `validate_cast_and_convert_metadata` promises that the object
        //   described by `split_at` is validly-aligned for `U`.
        // - By invariant on `self`, `A` is guaranteed to live for at least
        //   `'a`.
        // - `U: 'a` by trait bound.
        Some((Ptr { ptr, _lifetime: PhantomData }, split_at))
    }

    /// Attempts to cast `self` into a `U`, failing if all of the bytes of
    /// `self` cannot be treated as a `U`.
    ///
    /// In particular, this method fails if `self` is not validly-aligned for
    /// `U` or if `self`'s size is not a valid size for `U`.
    ///
    /// # Safety
    ///
    /// On success, the caller may assume that the returned pointer references
    /// the same byte range as `self`.
    #[doc(hidden)]
    #[inline(always)]
    pub(crate) fn try_cast_into_no_leftover<U: 'a + ?Sized + KnownLayout>(
        &self,
    ) -> Option<Ptr<'a, U>> {
        // TODO(#67): Remove this allow. See NonNulSlicelExt for more details.
        #[allow(unstable_name_collisions)]
        match self.try_cast_into(CastType::Prefix) {
            Some((slf, split_at)) if split_at == self.len() => Some(slf),
            Some(_) | None => None,
        }
    }
}

impl<'a, T: 'a + ?Sized> From<&'a T> for Ptr<'a, T> {
    #[inline(always)]
    fn from(t: &'a T) -> Ptr<'a, T> {
        // SAFETY: `t` points to a valid Rust allocation, `A`, by construction.
        // Thus:
        // - `ptr` is derived from `A`
        // - Since we use `NonNull::from`, which preserves provenance, `ptr` has
        //   the same provenance as `A`
        // - Since `NonNull::from` creates a pointer which addresses the same
        //   bytes as `t`, `ptr` addresses a byte range entirely contained in
        //   (in this case, identical to) `A`
        // - Since `t: &T`, it addresses no more than `isize::MAX` bytes. [1]
        // - Since `t: &T`, it addresses a byte range which does not wrap around
        //   the address space. [2]
        // - Since it is constructed from a valid `&T`, `ptr` is validly-aligned
        //   for `T`
        // - Since `t: &'a T`, the allocation `A` is guaranteed to live for at
        //   least `'a`
        // - `T: 'a` by trait bound
        //
        // TODO(#429), TODO(https://github.com/rust-lang/rust/issues/116181):
        // Once it's documented, reference the guarantee that `NonNull::from`
        // preserves provenance.
        //
        // TODO(#429),
        // TODO(https://github.com/rust-lang/unsafe-code-guidelines/issues/465):
        // - [1] Where does the reference document that allocations fit in
        //   `isize`?
        // - [2] Where does the reference document that allocations don't wrap
        //   around the address space?
        Ptr { ptr: NonNull::from(t), _lifetime: PhantomData }
    }
}

impl<'a, T: 'a + ?Sized> From<&'a mut T> for Ptr<'a, T> {
    #[inline(always)]
    fn from(t: &'a mut T) -> Ptr<'a, T> {
        Ptr::from(&*t)
    }
}

impl<'a, T: 'a + ?Sized> Debug for Ptr<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.ptr.fmt(f)
    }
}

pub(crate) trait AsAddress {
    fn addr(self) -> usize;
}

impl<'a, T: ?Sized> AsAddress for &'a T {
    #[inline(always)]
    fn addr(self) -> usize {
        let ptr: *const T = self;
        AsAddress::addr(ptr)
    }
}

impl<'a, T: ?Sized> AsAddress for &'a mut T {
    #[inline(always)]
    fn addr(self) -> usize {
        let ptr: *const T = self;
        AsAddress::addr(ptr)
    }
}

impl<T: ?Sized> AsAddress for *const T {
    #[inline(always)]
    fn addr(self) -> usize {
        // TODO(https://github.com/rust-lang/rust/issues/95228): Use `.addr()`
        // instead of `as usize` once it's stable, and get rid of this `allow`.
        // Currently, `as usize` is the only way to accomplish this.
        #[allow(clippy::as_conversions)]
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

/// Is `t` aligned to `mem::align_of::<U>()`?
#[inline(always)]
pub(crate) fn aligned_to<T: AsAddress, U>(t: T) -> bool {
    // `mem::align_of::<U>()` is guaranteed to return a non-zero value, which in
    // turn guarantees that this mod operation will not panic.
    #[allow(clippy::arithmetic_side_effects)]
    let remainder = t.addr() % mem::align_of::<U>();
    remainder == 0
}

/// Round `n` down to the largest value `m` such that `m <= n` and `m % align ==
/// 0`.
///
/// # Panics
///
/// May panic if `align` is not a power of two. Even if it doesn't panic in this
/// case, it will produce nonsense results.
#[inline(always)]
pub(crate) const fn round_down_to_next_multiple_of_alignment(
    n: usize,
    align: NonZeroUsize,
) -> usize {
    let align = align.get();
    debug_assert!(align.is_power_of_two());

    // Subtraction can't underflow because `align.get() >= 1`.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = !(align - 1);
    n & mask
}

/// Since we support multiple versions of Rust, there are often features which
/// have been stabilized in the most recent stable release which do not yet
/// exist (stably) on our MSRV. This module provides polyfills for those
/// features so that we can write more "modern" code, and just remove the
/// polyfill once our MSRV supports the corresponding feature. Without this,
/// we'd have to write worse/more verbose code and leave TODO comments sprinkled
/// throughout the codebase to update to the new pattern once it's stabilized.
///
/// Each trait is imported as `_` at the crate root; each polyfill should "just
/// work" at usage sites.
pub(crate) mod polyfills {
    use core::ptr::{self, NonNull};

    // A polyfill for `NonNull::slice_from_raw_parts` that we can use before our
    // MSRV is 1.70, when that function was stabilized.
    //
    // TODO(#67): Once our MSRV is 1.70, remove this.
    pub(crate) trait NonNullExt<T> {
        fn slice_from_raw_parts(data: Self, len: usize) -> NonNull<[T]>;
    }

    impl<T> NonNullExt<T> for NonNull<T> {
        #[inline(always)]
        fn slice_from_raw_parts(data: Self, len: usize) -> NonNull<[T]> {
            let ptr = ptr::slice_from_raw_parts_mut(data.as_ptr(), len);
            // SAFETY: `ptr` is converted from `data`, which is non-null.
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    // A polyfill for `NonNull::len` that we can use before our MSRV is 1.63,
    // when that function was stabilized.
    //
    // TODO(#67): Once our MSRV is 1.63, remove this.
    pub(crate) trait NonNullSliceExt<T> {
        fn len(&self) -> usize;
    }

    impl<T> NonNullSliceExt<T> for NonNull<[T]> {
        #[inline(always)]
        fn len(&self) -> usize {
            #[allow(clippy::as_conversions)]
            let slc = self.as_ptr() as *const [()];
            // SAFETY:
            // - `()` has alignment 1, so `slc` is trivially aligned
            // - `slc` was derived from a non-null pointer
            // - the size is 0 regardless of the length, so it is sound to
            //   materialize a reference regardless of location
            // - pointer provenance may be an issue, but we never dereference
            let slc = unsafe { &*slc };
            slc.len()
        }
    }
}

#[cfg(test)]
pub(crate) mod testutil {
    use core::fmt::{self, Display, Formatter};

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

    // A `u64` with alignment 8.
    //
    // Though `u64` has alignment 8 on some platforms, it's not guaranteed.
    // By contrast, `AU64` is guaranteed to have alignment 8.
    #[derive(
        FromZeroes, FromBytes, AsBytes, Eq, PartialEq, Ord, PartialOrd, Default, Debug, Copy, Clone,
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
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }

    impl_known_layout!(AU64);
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;
    use crate::{util::testutil::AU64, FromBytes};

    #[test]
    fn test_ptrtry_cast_into_soundness() {
        // This test is designed so that if `Ptr::try_cast_into_xxx` are buggy,
        // it will manifest as unsoundness that Miri can detect.

        // - If `size_of::<T>() == 0`, `N == 4`
        // - Else, `N == 4 * size_of::<T>()`
        fn test<const N: usize, T: ?Sized + KnownLayout + FromBytes>() {
            let mut bytes = [MaybeUninit::<u8>::uninit(); N];
            let initialized = [MaybeUninit::new(0u8); N];
            for start in 0..=bytes.len() {
                for end in start..=bytes.len() {
                    // Set all bytes to uninitialized other than those in the
                    // range we're going to pass to `try_cast_from`. This allows
                    // Miri to detect out-of-bounds reads because they read
                    // uninitialized memory. Without this, some out-of-bounds
                    // reads would still be in-bounds of `bytes`, and so might
                    // spuriously be accepted.
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

                    /// # Safety
                    ///
                    /// - `slf` must reference a byte range which is entirely
                    ///   initialized.
                    /// - `slf` must reference a byte range which is only
                    ///   referenced by shared references which do not contain
                    ///   `UnsafeCell`s during its lifetime.
                    unsafe fn validate_and_get_len<T: ?Sized + KnownLayout + FromBytes>(
                        slf: Ptr<'_, T>,
                    ) -> usize {
                        // TODO(#429): Update this safety comment once
                        // `as_ref`'s safety invariants are well-defined.
                        //
                        // Old draft safety comment:
                        // - The caller has promised that all bytes referenced
                        //   by `slf` are initialized. Since `T: FromBytes`,
                        //   those bytes constitute a valid `T`.
                        // - The caller has promised that no mutable references
                        //   exist to the same memory during the duration of
                        //   this function call.
                        // - The caller has promised that no `UnsafeCell`
                        //   references exist to the same memory during the
                        //   duration of this function call.
                        #[allow(clippy::undocumented_unsafe_blocks)]
                        let t = unsafe { slf.as_ref() };

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

                    for cast_type in [CastType::Prefix, CastType::_Suffix] {
                        if let Some((slf, split_at)) =
                            Ptr::from(bytes).try_cast_into::<T>(cast_type)
                        {
                            // SAFETY: All bytes in `bytes` have been
                            // initialized.
                            let len = unsafe { validate_and_get_len(slf) };
                            match cast_type {
                                CastType::Prefix => assert_eq!(split_at, len),
                                CastType::_Suffix => assert_eq!(split_at, bytes.len() - len),
                            }
                        }
                    }

                    if let Some(slf) = Ptr::from(bytes).try_cast_into_no_leftover::<T>() {
                        // SAFETY: All bytes in `bytes` have been initialized.
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
                    test::<N, $ty>();
                    // We don't support casting into DSTs whose trailing slice
                    // element is a ZST.
                    if S > 0 {
                        test::<N, [$ty]>();
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
                assert_eq!(got, want, "round_down_to_next_multiple_of_alignment({n}, {align})");
            }
        }
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    #[kani::proof]
    fn prove_round_down_to_next_multiple_of_alignment() {
        fn model_impl(n: usize, align: NonZeroUsize) -> usize {
            assert!(align.get().is_power_of_two());
            let mul = n / align.get();
            mul * align.get()
        }

        let align: NonZeroUsize = kani::any();
        kani::assume(align.get().is_power_of_two());
        let n: usize = kani::any();

        let expected = model_impl(n, align);
        let actual = round_down_to_next_multiple_of_alignment(n, align);
        assert_eq!(expected, actual, "round_down_to_next_multiple_of_alignment({n}, {align})");
    }

    // Restricted to nightly since we use the unstable `usize::next_multiple_of`
    // in our model implementation.
    #[cfg(__INTERNAL_USE_ONLY_NIGHLTY_FEATURES_IN_TESTS)]
    #[kani::proof]
    fn prove_padding_needed_for() {
        fn model_impl(len: usize, align: NonZeroUsize) -> usize {
            let padded = len.next_multiple_of(align.get());
            let padding = padded - len;
            padding
        }

        let align: NonZeroUsize = kani::any();
        kani::assume(align.get().is_power_of_two());
        let len: usize = kani::any();
        // Constrain `len` to valid Rust lengths, since our model implementation
        // isn't robust to overflow.
        kani::assume(len <= isize::MAX as usize);
        kani::assume(align.get() < 1 << 29);

        let expected = model_impl(len, align);
        let actual = core_layout::_padding_needed_for(len, align);
        assert_eq!(expected, actual, "padding_needed_for({len}, {align})");

        let padded_len = actual + len;
        assert_eq!(padded_len % align, 0);
        assert!(padded_len / align >= len / align);
    }
}
