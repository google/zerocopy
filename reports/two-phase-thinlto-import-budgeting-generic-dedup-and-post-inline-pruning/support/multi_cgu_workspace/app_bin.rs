#![crate_name = "app_bin"]
extern crate core_bytes;
extern crate zerocopy_layout;
extern crate codec_generic;

use std::hint::black_box;
use std::time::Instant;

pub mod mod_cgu_00 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_00(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(0), y)
    }

    #[inline(never)]
    pub fn entry_stage_00(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1000>(words);
        let b = generic_read_le(words, 0, 0u64);
        internal_stage_helper_00(a, b)
    }
}


pub mod mod_cgu_01 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_01(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(1), y)
    }

    #[inline(never)]
    pub fn entry_stage_01(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1001>(words);
        let b = generic_read_le(words, 1, 1u64);
        internal_stage_helper_01(a, b)
    }
}


pub mod mod_cgu_02 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_02(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(2), y)
    }

    #[inline(never)]
    pub fn entry_stage_02(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1002>(words);
        let b = generic_read_le(words, 2, 2u64);
        internal_stage_helper_02(a, b)
    }
}


pub mod mod_cgu_03 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_03(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(3), y)
    }

    #[inline(never)]
    pub fn entry_stage_03(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1003>(words);
        let b = generic_read_le(words, 0, 3u64);
        internal_stage_helper_03(a, b)
    }
}


pub mod mod_cgu_04 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_04(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(4), y)
    }

    #[inline(never)]
    pub fn entry_stage_04(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1000>(words);
        let b = generic_read_le(words, 1, 4u64);
        internal_stage_helper_04(a, b)
    }
}


pub mod mod_cgu_05 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_05(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(5), y)
    }

    #[inline(never)]
    pub fn entry_stage_05(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1001>(words);
        let b = generic_read_le(words, 2, 5u64);
        internal_stage_helper_05(a, b)
    }
}


pub mod mod_cgu_06 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_06(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(6), y)
    }

    #[inline(never)]
    pub fn entry_stage_06(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1002>(words);
        let b = generic_read_le(words, 0, 6u64);
        internal_stage_helper_06(a, b)
    }
}


pub mod mod_cgu_07 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_07(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(7), y)
    }

    #[inline(never)]
    pub fn entry_stage_07(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1003>(words);
        let b = generic_read_le(words, 1, 7u64);
        internal_stage_helper_07(a, b)
    }
}


pub mod mod_cgu_08 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_08(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(8), y)
    }

    #[inline(never)]
    pub fn entry_stage_08(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1000>(words);
        let b = generic_read_le(words, 2, 8u64);
        internal_stage_helper_08(a, b)
    }
}


pub mod mod_cgu_09 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_09(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(9), y)
    }

    #[inline(never)]
    pub fn entry_stage_09(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1001>(words);
        let b = generic_read_le(words, 0, 9u64);
        internal_stage_helper_09(a, b)
    }
}


pub mod mod_cgu_10 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_10(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(10), y)
    }

    #[inline(never)]
    pub fn entry_stage_10(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1002>(words);
        let b = generic_read_le(words, 1, 10u64);
        internal_stage_helper_10(a, b)
    }
}


pub mod mod_cgu_11 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_11(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(11), y)
    }

    #[inline(never)]
    pub fn entry_stage_11(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1003>(words);
        let b = generic_read_le(words, 2, 11u64);
        internal_stage_helper_11(a, b)
    }
}


pub mod mod_cgu_12 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_12(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(12), y)
    }

    #[inline(never)]
    pub fn entry_stage_12(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1000>(words);
        let b = generic_read_le(words, 0, 12u64);
        internal_stage_helper_12(a, b)
    }
}


pub mod mod_cgu_13 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_13(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(13), y)
    }

    #[inline(never)]
    pub fn entry_stage_13(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1001>(words);
        let b = generic_read_le(words, 1, 13u64);
        internal_stage_helper_13(a, b)
    }
}


pub mod mod_cgu_14 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_14(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(14), y)
    }

    #[inline(never)]
    pub fn entry_stage_14(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1002>(words);
        let b = generic_read_le(words, 2, 14u64);
        internal_stage_helper_14(a, b)
    }
}


pub mod mod_cgu_15 {
    use codec_generic::decode_frame_generic;
    use core_bytes::{generic_mix_lane, generic_read_le};

    #[inline]
    fn internal_stage_helper_15(x: u64, y: u64) -> u64 {
        generic_mix_lane::<0x517C_C1B7_2722_0A95>(x.wrapping_add(15), y)
    }

    #[inline(never)]
    pub fn entry_stage_15(words: &[u64]) -> u64 {
        let a = decode_frame_generic::<0x1003>(words);
        let b = generic_read_le(words, 0, 15u64);
        internal_stage_helper_15(a, b)
    }
}

fn main() {
    let words = [0xABCD_0123_4567_89EFu64, 64, 99, 12345];
    for _ in 0..10 {
        let mut acc = 0u64;
        acc = acc.wrapping_add(mod_cgu_00::entry_stage_00(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_01::entry_stage_01(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_02::entry_stage_02(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_03::entry_stage_03(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_04::entry_stage_04(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_05::entry_stage_05(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_06::entry_stage_06(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_07::entry_stage_07(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_08::entry_stage_08(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_09::entry_stage_09(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_10::entry_stage_10(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_11::entry_stage_11(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_12::entry_stage_12(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_13::entry_stage_13(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_14::entry_stage_14(black_box(&words)));
        acc = acc.wrapping_add(mod_cgu_15::entry_stage_15(black_box(&words)));
        black_box(acc);
    }
    let mut times = Vec::with_capacity(25);
    for _ in 0..25 {
        let t0 = Instant::now();
        let mut acc = 0u64;
        for _ in 0..2_000 {
            acc = acc.wrapping_add(mod_cgu_00::entry_stage_00(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_01::entry_stage_01(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_02::entry_stage_02(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_03::entry_stage_03(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_04::entry_stage_04(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_05::entry_stage_05(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_06::entry_stage_06(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_07::entry_stage_07(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_08::entry_stage_08(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_09::entry_stage_09(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_10::entry_stage_10(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_11::entry_stage_11(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_12::entry_stage_12(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_13::entry_stage_13(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_14::entry_stage_14(black_box(&words)));
            acc = acc.wrapping_add(mod_cgu_15::entry_stage_15(black_box(&words)));
        }
        black_box(acc);
        times.push(t0.elapsed().as_nanos() as f64 / 1000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{{\"median_us\": {:.2}}}", times[times.len() / 2]);
}
