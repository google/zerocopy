// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{mem, num::NonZeroUsize};

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
        // TODO(#181), TODO(https://github.com/rust-lang/rust/issues/95228): Use
        // `.addr()` instead of `as usize` once it's stable, and get rid of this
        // `allow`. Currently, `as usize` is the only way to accomplish this.
        #[allow(clippy::as_conversions)]
        #[cfg_attr(__INTERNAL_USE_ONLY_NIGHLTY_FEATURES_IN_TESTS, allow(lossy_provenance_casts))]
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

/// Returns the bytes needed to pad `len` to the next multiple of `align`.
///
/// This function assumes that align is a power of two; there are no guarantees
/// on the answer it gives if this is not the case.
pub(crate) const fn padding_needed_for(len: usize, align: NonZeroUsize) -> usize {
    // Abstractly, we want to compute:
    //   align - (len % align).
    // Handling the case where len%align is 0.
    // Because align is a power of two, len % align = len & (align-1).
    // Guaranteed not to underflow as align is nonzero.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = align.get() - 1;

    // To efficiently subtract this value from align, we can use the bitwise complement.
    // Note that ((!len) & (align-1)) gives us a number that with (len &
    // (align-1)) sums to align-1. So subtracting 1 from x before taking the
    // complement subtracts `len` from `align`. Some quick inspection of
    // cases shows that this also handles the case where `len % align = 0`
    // correctly too: len-1 % align then equals align-1, so the complement mod
    // align will be 0, as desired.
    //
    // The following reasoning can be verified quickly by an SMT solver
    // supporting the theory of bitvectors:
    // ```smtlib
    // ; Naive implementation of padding
    // (define-fun padding1 (
    //     (len (_ BitVec 32))
    //     (align (_ BitVec 32))) (_ BitVec 32)
    //    (ite
    //      (= (_ bv0 32) (bvand len (bvsub align (_ bv1 32))))
    //      (_ bv0 32)
    //      (bvsub align (bvand len (bvsub align (_ bv1 32))))))
    //
    // ; The implementation below
    // (define-fun padding2 (
    //     (len (_ BitVec 32))
    //     (align (_ BitVec 32))) (_ BitVec 32)
    // (bvand (bvnot (bvsub len (_ bv1 32))) (bvsub align (_ bv1 32))))
    //
    // (define-fun is-power-of-two ((x (_ BitVec 32))) Bool
    //   (= (_ bv0 32) (bvand x (bvsub x (_ bv1 32)))))
    //
    // (declare-const len (_ BitVec 32))
    // (declare-const align (_ BitVec 32))
    // ; Search for a case where align is a power of two and padding2 disagrees with padding1
    // (assert (and (is-power-of-two align)
    //              (not (= (padding1 len align) (padding2 len align)))))
    // (simplify (padding1 (_ bv300 32) (_ bv32 32))) ; 20
    // (simplify (padding2 (_ bv300 32) (_ bv32 32))) ; 20
    // (simplify (padding1 (_ bv322 32) (_ bv32 32))) ; 30
    // (simplify (padding2 (_ bv322 32) (_ bv32 32))) ; 30
    // (simplify (padding1 (_ bv8 32) (_ bv8 32)))    ; 0
    // (simplify (padding2 (_ bv8 32) (_ bv8 32)))    ; 0
    // (check-sat) ; unsat, also works for 64-bit bitvectors
    // ```
    !(len.wrapping_sub(1)) & mask
}

/// Rounds `n` down to the largest value `m` such that `m <= n` and `m % align
/// == 0`.
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
    #[cfg(zerocopy_panic_in_const)]
    debug_assert!(align.is_power_of_two());

    // Subtraction can't underflow because `align.get() >= 1`.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = !(align - 1);
    n & mask
}

pub(crate) const fn max(a: NonZeroUsize, b: NonZeroUsize) -> NonZeroUsize {
    if a.get() < b.get() {
        b
    } else {
        a
    }
}

pub(crate) const fn min(a: NonZeroUsize, b: NonZeroUsize) -> NonZeroUsize {
    if a.get() > b.get() {
        b
    } else {
        a
    }
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
    // The `#[allow(unused)]` is necessary because, on sufficiently recent
    // toolchain versions, `ptr.slice_from_raw_parts()` resolves to the inherent
    // method rather than to this trait, and so this trait is considered unused.
    //
    // TODO(#67): Once our MSRV is 1.70, remove this.
    #[allow(unused)]
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
        KnownLayout,
        NoCell,
        TryFromBytes,
        FromZeros,
        FromBytes,
        IntoBytes,
        Eq,
        PartialEq,
        Ord,
        PartialOrd,
        Default,
        Debug,
        Copy,
        Clone,
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

    #[derive(
        NoCell, FromZeros, FromBytes, Eq, PartialEq, Ord, PartialOrd, Default, Debug, Copy, Clone,
    )]
    #[repr(C)]
    pub(crate) struct Nested<T, U: ?Sized> {
        _t: T,
        _u: U,
    }
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
                let got = round_down_to_next_multiple_of_alignment(n, align);
                assert_eq!(got, want, "round_down_to_next_multiple_of_alignment({}, {})", n, align);
            }
        }
    }

    #[rustversion::since(1.57.0)]
    #[test]
    #[should_panic]
    fn test_round_down_to_next_multiple_of_alignment_panic_in_const() {
        round_down_to_next_multiple_of_alignment(0, NonZeroUsize::new(3).unwrap());
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
        assert_eq!(expected, actual, "round_down_to_next_multiple_of_alignment({}, {})", n, align);
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
        let actual = padding_needed_for(len, align);
        assert_eq!(expected, actual, "padding_needed_for({}, {})", len, align);

        let padded_len = actual + len;
        assert_eq!(padded_len % align, 0);
        assert!(padded_len / align >= len / align);
    }
}
