// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[path = "third_party/rust/layout.rs"]
pub(crate) mod core_layout;

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
