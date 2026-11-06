use crate::Harness;
use std::hint::black_box;

pub fn run(h: &mut Harness) {
    let x = black_box(0x0123_4567_89ab_cdef_u64);
    let little = [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];
    let big = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
    let native = x.to_ne_bytes();
    println!("OBS integer.u64.native_bytes={:?}", native);
    println!("OBS integer.u64.little_bytes={:?}", x.to_le_bytes());
    println!("OBS integer.u64.big_bytes={:?}", x.to_be_bytes());
    h.check("integer.explicit_byte_orders", x.to_le_bytes() == little && x.to_be_bytes() == big);
    h.check("integer.native_byte_order", native == if cfg!(target_endian = "big") { big } else { little });
    h.check("integer.native_roundtrip", u64::from_ne_bytes(native) == x);
    h.check("control.native_bytes_need_endian", native != if cfg!(target_endian = "big") { little } else { big });

    let umax = black_box(u32::MAX);
    let imin = black_box(i32::MIN);
    h.check("integer.wrapping_add", umax.wrapping_add(1) == 0);
    h.check("integer.checked_add", umax.checked_add(1).is_none());
    h.check("integer.wrapping_signed_sub", imin.wrapping_sub(1) == i32::MAX);
    h.check("integer.checked_signed_sub", imin.checked_sub(1).is_none());
    h.check("integer.checked_div_overflow", imin.checked_div(-1).is_none());
    h.check("integer.wrapping_div_overflow", imin.wrapping_div(-1) == i32::MIN);
    h.check("integer.checked_div_zero", 7_u32.checked_div(0).is_none());
    h.check("integer.checked_shift_in_range", 1_u32.checked_shl(31) == Some(0x8000_0000));
    h.check("integer.checked_shift_out_of_range", 1_u32.checked_shl(32).is_none());
    h.check("integer.wrapping_shift_masks_count", 1_u32.wrapping_shl(32) == 1 && 0x8000_0000_u32.wrapping_shr(33) == 0x4000_0000);
    h.check("integer.signed_right_shift", black_box(-8_i32) >> 2 == -2);
    h.check("integer.narrowing_cast", black_box(0x1234_u16) as u8 == 0x34 && black_box(300_u16) as u8 == 44);
    h.check("integer.signed_unsigned_cast", black_box(-1_i8) as u16 == u16::MAX && black_box(255_u8) as i8 == -1);
    h.check("control.checked_is_not_wrapping", umax.checked_add(1) != Some(umax.wrapping_add(1)));

    // Bit conversions preserve the given bits; no arithmetic NaN payload is fixed.
    for bits in [0_u32, 0x8000_0000, 1, 0x3fc0_0000, 0x7f80_0000, 0xff80_0000, 0x7fc0_1234, 0x7f80_1234] {
        let f = f32::from_bits(black_box(bits));
        println!("OBS float.f32.input={:08x} roundtrip={:08x} nan={}", bits, f.to_bits(), f.is_nan());
        h.check(&format!("float.f32.bit_roundtrip.{:08x}", bits), f.to_bits() == bits);
    }
    for bits in [0_u64, 0x8000_0000_0000_0000, 1, 0x3ff8_0000_0000_0000, 0x7ff0_0000_0000_0000, 0x7ff8_0000_0000_1234] {
        let f = f64::from_bits(black_box(bits));
        println!("OBS float.f64.input={:016x} roundtrip={:016x} nan={}", bits, f.to_bits(), f.is_nan());
        h.check(&format!("float.f64.bit_roundtrip.{:016x}", bits), f.to_bits() == bits);
    }
    h.check("float.exact_binary_arithmetic", black_box(1.5_f32) + black_box(2.25_f32) == 3.75_f32);
    h.check("float.exact_cross_width_cast", black_box(1.5_f64) as f32 == 1.5_f32);
    h.check("float.subnormal_bit_value", f32::from_bits(black_box(1)) > 0.0 && f32::from_bits(1).is_finite());
    h.check("float.finite_cast_truncates", black_box(3.875_f32) as i32 == 3 && black_box(-3.875_f32) as i32 == -3);
    h.check("float.cast_saturates_unsigned", black_box(300.0_f32) as u8 == 255 && black_box(-1.0_f32) as u8 == 0);
    h.check("float.cast_nan_zero", black_box(f32::NAN) as i32 == 0);
    h.check("float.cast_infinities_saturate", black_box(f32::INFINITY) as i32 == i32::MAX && black_box(f32::NEG_INFINITY) as i32 == i32::MIN);
    let plus_zero = black_box(0.0_f64);
    let minus_zero = black_box(-0.0_f64);
    h.check("control.float_equality_is_not_bit_equality", plus_zero == minus_zero && plus_zero.to_bits() != minus_zero.to_bits());

    let nan32 = black_box(f32::from_bits(0x7fc0_1234)) + black_box(1.0_f32);
    let nan64 = black_box(f64::from_bits(0x7ff8_0000_0000_1234)) * black_box(2.0_f64);
    let cast_nan = black_box(f64::from_bits(0x7ff8_0000_0000_1234)) as f32;
    println!("CHOICE float.f32.arithmetic_nan_bits={:08x}", nan32.to_bits());
    println!("CHOICE float.f64.arithmetic_nan_bits={:016x}", nan64.to_bits());
    println!("CHOICE float.f64_to_f32.nan_bits={:08x}", cast_nan.to_bits());
    h.check("float.arithmetic_nan_class", nan32.is_nan() && nan64.is_nan());
    h.check("float.nan_cast_class", cast_nan.is_nan());
    h.check("control.nan_not_reflexively_equal", nan32 != nan32 && nan64 != nan64);
}
