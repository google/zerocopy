// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Generic owned conversions through the bounded standard-primitive helper.
//!
//! The independent generic caller keeps both trait bounds in the checked
//! execution closure rather than specializing the conversion to fixture types.

use crate::{FromBytes, IntoBytes};

/// ```aeneas
/// spec transmute_copy_caller_spec
///   requires(raw) same_size : AeneasSpecs.RustModel.sameSize Src Dst
///   ensures(raw) result => AeneasSpecs.RustModel.byteCast src result
/// ```
const fn transmute_copy_caller<Src: IntoBytes, Dst: FromBytes>(src: Src) -> Dst {
    super::macro_util::transmute_copy(src)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(IntoBytes)]
    #[repr(transparent)]
    struct PanicsOnDrop(u8);

    impl Drop for PanicsOnDrop {
        fn drop(&mut self) {
            panic!("the consumed source must not be dropped");
        }
    }

    #[test]
    fn source_is_not_dropped() {
        assert_eq!(transmute_copy_caller::<_, u8>(PanicsOnDrop(42)), 42);
    }

    #[test]
    fn const_and_runtime_conversions() {
        const BYTES: [u8; 4] = transmute_copy_caller(0x1234_5678u32);
        const VALUE: u32 = transmute_copy_caller(BYTES);
        const EMPTY_BYTES: [u8; 0] = transmute_copy_caller(());
        const EMPTY_ALIGNED: [u64; 0] = transmute_copy_caller(EMPTY_BYTES);
        const _: () = transmute_copy_caller(EMPTY_ALIGNED);

        assert_eq!(BYTES, 0x1234_5678u32.to_ne_bytes());
        assert_eq!(VALUE, 0x1234_5678);
        assert_eq!(EMPTY_BYTES, []);
        assert_eq!(EMPTY_ALIGNED, []);

        for value in [0, 1, 0x1234_5678, u32::MAX] {
            let bytes: [u8; 4] = transmute_copy_caller(value);
            assert_eq!(bytes, value.to_ne_bytes());
            assert_eq!(transmute_copy_caller::<_, u32>(bytes), value);
        }
        assert_eq!(transmute_copy_caller::<_, [u8; 0]>(()), []);
        assert_eq!(transmute_copy_caller::<[u8; 0], [u64; 0]>([]), []);
        transmute_copy_caller::<[u64; 0], ()>([]);
    }
}
