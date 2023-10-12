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
pub(crate) struct Ptr<'a, T: 'a + ?Sized> {
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
    pub(crate) unsafe fn _as_ref(&self) -> &'a T {
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
pub(crate) const fn _round_down_to_next_multiple_of_alignment(
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
    use super::*;

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
                let got = _round_down_to_next_multiple_of_alignment(n, align);
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
        let actual = _round_down_to_next_multiple_of_alignment(n, align);
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
