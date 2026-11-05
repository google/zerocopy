// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Empirical probe of `-Z randomize-layout` in `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`
// across `-Z layout-seed=<seed>` values.

#![allow(dead_code)]

use core::mem::{align_of, offset_of, size_of};
use core::num::NonZeroU8;

// 1. Single-field structs under repr(Rust), repr(transparent), and repr(C)
struct SingleRust(u64);

#[repr(transparent)]
struct SingleTrans(u64);

#[repr(C)]
struct SingleC(u64);

// 2. Single non-ZST field + 1-ZST field under repr(Rust), repr(transparent), and repr(C)
struct RustWithZst((), u64);

#[repr(transparent)]
struct TransWithZst((), u64);

#[repr(C)]
struct CWithZst((), u64);

// 3. Multi-field structs where field order changes total size due to inter-field padding:
//    Ordered (u8, u16, u8) -> offsets 0, 2, 4 -> size 6, align 2
//    Ordered (u16, u8, u8) or (u8, u8, u16) -> offsets 0, 2, 3 -> size 4, align 2
struct MultiPaddedRust(u8, u16, u8);

#[repr(C)]
struct MultiPaddedC(u8, u16, u8);

// 4. Multi-field struct with equal-alignment fields
struct PairRust(u64, u32);

// 5. Generic struct with `?Sized` tail field (`StructKind::MaybeUnsized` in rustc_ty_utils):
//    The tail field `2` is excluded from shuffling even when instantiated with a Sized type!
struct WithUnsizableTail<T: ?Sized>(u8, u16, T);

// 6. Tuple `(u8, u16, u8)`: has default Rust representation per [r-layout.tuple.def],
//    but rustc_ty_utils uses `ReprOptions::default()` (without RANDOMIZE_LAYOUT) and
//    `StructKind::MaybeUnsized`, so `-Z randomize-layout` never shuffles tuple fields!
type TuplePadded = (u8, u16, u8);

// 7. Niche selection under `-Z randomize-layout`:
//    `univariant_biased` selects the LAST field with maximum niche size (`>=`).
//    Here field `0` (`bool`, 254 niche values) and field `1` (`NonZeroU8`, 1 niche value)
//    have different niche sizes, so `largest_niche` always picks `bool`, while its offset
//    inside `NicheStructDiff` (and therefore the discriminant offset of `Option<NicheStructDiff>`)
//    moves with `bool`!
struct NicheStructDiff(bool, NonZeroU8);

//    When two fields have EQUAL niche capacities (e.g., two `NonZeroU8` fields), shuffling changes
//    which field is visited last in `univariant_biased` (`>=`), changing which field carries the
//    `Option` niche!
struct NicheStructEqual(NonZeroU8, NonZeroU8);

// 8. Multi-variant enum with multi-field variants
enum MultiEnum {
    A(u8, u16, u8),
    B(u32, u8),
}

fn main() {
    let seed = std::env::args().nth(1).unwrap_or_else(|| "none".to_string());

    let mut buf = [0xFFu8; 2];
    unsafe {
        core::ptr::write(buf.as_mut_ptr() as *mut Option<NicheStructEqual>, None);
    }
    let none_equal_bytes = buf;

    let mut buf_diff = [0xFFu8; 2];
    unsafe {
        core::ptr::write(buf_diff.as_mut_ptr() as *mut Option<NicheStructDiff>, None);
    }
    let none_diff_bytes = buf_diff;

    println!(
        "{{\"seed\":\"{}\",\
        \"SingleRust\":{{\"size\":{},\"align\":{},\"off0\":{}}},\
        \"SingleTrans\":{{\"size\":{},\"align\":{},\"off0\":{}}},\
        \"SingleC\":{{\"size\":{},\"align\":{},\"off0\":{}}},\
        \"RustWithZst\":{{\"size\":{},\"align\":{},\"off0_zst\":{},\"off1_u64\":{}}},\
        \"TransWithZst\":{{\"size\":{},\"align\":{},\"off0_zst\":{},\"off1_u64\":{}}},\
        \"CWithZst\":{{\"size\":{},\"align\":{},\"off0_zst\":{},\"off1_u64\":{}}},\
        \"MultiPaddedRust\":{{\"size\":{},\"align\":{},\"off0_u8\":{},\"off1_u16\":{},\"off2_u8\":{}}},\
        \"MultiPaddedC\":{{\"size\":{},\"align\":{},\"off0_u8\":{},\"off1_u16\":{},\"off2_u8\":{}}},\
        \"PairRust\":{{\"size\":{},\"align\":{},\"off0_u64\":{},\"off1_u32\":{}}},\
        \"WithUnsizableTail_u8\":{{\"size\":{},\"align\":{},\"off0_u8\":{},\"off1_u16\":{},\"off2_tail_u8\":{}}},\
        \"TuplePadded\":{{\"size\":{},\"align\":{},\"off0_u8\":{},\"off1_u16\":{},\"off2_u8\":{}}},\
        \"NicheStructDiff\":{{\"size\":{},\"opt_size\":{},\"off0_bool\":{},\"off1_nz\":{},\"none_bytes\":[{},{}]}},\
        \"NicheStructEqual\":{{\"size\":{},\"opt_size\":{},\"off0_nz0\":{},\"off1_nz1\":{},\"none_bytes\":[{},{}]}},\
        \"MultiEnum\":{{\"size\":{},\"align\":{},\"opt_size\":{}}}\
        }}",
        seed,
        size_of::<SingleRust>(), align_of::<SingleRust>(), offset_of!(SingleRust, 0),
        size_of::<SingleTrans>(), align_of::<SingleTrans>(), offset_of!(SingleTrans, 0),
        size_of::<SingleC>(), align_of::<SingleC>(), offset_of!(SingleC, 0),
        size_of::<RustWithZst>(), align_of::<RustWithZst>(), offset_of!(RustWithZst, 0), offset_of!(RustWithZst, 1),
        size_of::<TransWithZst>(), align_of::<TransWithZst>(), offset_of!(TransWithZst, 0), offset_of!(TransWithZst, 1),
        size_of::<CWithZst>(), align_of::<CWithZst>(), offset_of!(CWithZst, 0), offset_of!(CWithZst, 1),
        size_of::<MultiPaddedRust>(), align_of::<MultiPaddedRust>(), offset_of!(MultiPaddedRust, 0), offset_of!(MultiPaddedRust, 1), offset_of!(MultiPaddedRust, 2),
        size_of::<MultiPaddedC>(), align_of::<MultiPaddedC>(), offset_of!(MultiPaddedC, 0), offset_of!(MultiPaddedC, 1), offset_of!(MultiPaddedC, 2),
        size_of::<PairRust>(), align_of::<PairRust>(), offset_of!(PairRust, 0), offset_of!(PairRust, 1),
        size_of::<WithUnsizableTail<u8>>(), align_of::<WithUnsizableTail<u8>>(), offset_of!(WithUnsizableTail<u8>, 0), offset_of!(WithUnsizableTail<u8>, 1), offset_of!(WithUnsizableTail<u8>, 2),
        size_of::<TuplePadded>(), align_of::<TuplePadded>(), offset_of!(TuplePadded, 0), offset_of!(TuplePadded, 1), offset_of!(TuplePadded, 2),
        size_of::<NicheStructDiff>(), size_of::<Option<NicheStructDiff>>(), offset_of!(NicheStructDiff, 0), offset_of!(NicheStructDiff, 1), none_diff_bytes[0], none_diff_bytes[1],
        size_of::<NicheStructEqual>(), size_of::<Option<NicheStructEqual>>(), offset_of!(NicheStructEqual, 0), offset_of!(NicheStructEqual, 1), none_equal_bytes[0], none_equal_bytes[1],
        size_of::<MultiEnum>(), align_of::<MultiEnum>(), size_of::<Option<MultiEnum>>()
    );
}
