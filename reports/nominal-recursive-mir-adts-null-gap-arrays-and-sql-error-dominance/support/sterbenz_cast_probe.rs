// Empirical x86-64 IEEE-754 probe comparing naive `(x + 0.5).floor()` double-rounding,
// `f64::round()` (`libm` foreign call), and branchless Sterbenz-exact `libm`-free
// `round_halfway_away_from_zero_to_i64` for SQL `CAST(DOUBLE AS INT64)`.

#[inline(never)]
pub fn buggy_floor_plus_half_to_i64(x: f64) -> Option<i64> {
    if !x.is_finite() {
        return None;
    }
    let y = if x >= 0.0 {
        (x + 0.5_f64).trunc()
    } else {
        (x - 0.5_f64).trunc()
    };
    if y < -9_223_372_036_854_775_808.0_f64 || y >= 9_223_372_036_854_775_808.0_f64 {
        return None;
    }
    Some(y as i64)
}

#[inline(never)]
pub fn sterbenz_round_away_from_zero_to_i64(x: f64) -> Option<i64> {
    if !x.is_finite() {
        return None;
    }
    // Note: `9_223_372_036_854_775_808.0_f64` (`2^63`) is exact in binary64, whereas
    // every finite `f64` strictly below `2^63` has `|x| <= 2^63 - 1024`, whose
    // integer part and +/-1 adjustment cannot overflow `i64` (`[-2^63, 2^63 - 1]`).
    if x < -9_223_372_036_854_775_808.0_f64 || x >= 9_223_372_036_854_775_808.0_f64 {
        return None;
    }
    // For `|x| >= 2^52`, every binary64 value is already an exact integer (`frac == 0`).
    let trunc_i64 = x as i64;
    let trunc_f64 = trunc_i64 as f64;
    // By Sterbenz's Lemma (when `0.5 <= |x| < 2^52`, `trunc_f64` is either `0.0` or within
    // `[|x|/2, |x|]`), `rem = x - trunc_f64` is computed with ZERO rounding error in IEEE-754!
    let rem = x - trunc_f64;
    let adj = (rem >= 0.5_f64) as i64 - (rem <= -0.5_f64) as i64;
    // Edge case: `x == -2^63` (`-9223372036854775808.0`): `trunc_i64 == i64::MIN`,
    // `rem == 0.0`, `adj == 0`, so `wrapping_add` is exact and never overflows.
    Some(trunc_i64.wrapping_add(adj))
}

fn main() {
    let pos_pred = f64::from_bits(0x3fdf_ffff_ffff_ffff); // +(0.5 - 2^-54)
    let neg_pred_exact = f64::from_bits(0xbfdf_ffff_ffff_ffff); // -(0.5 - 2^-54)
    assert_eq!(neg_pred_exact, -pos_pred);

    // 1. Show naive `(x +/- 0.5).trunc()` double-rounds `+/- (0.5 - 2^-54)` to `+/- 1`!
    assert_eq!(buggy_floor_plus_half_to_i64(pos_pred), Some(1));
    assert_eq!(buggy_floor_plus_half_to_i64(neg_pred_exact), Some(-1));

    // 2. Show Sterbenz `libm`-free rounding matches `f64::round()` across all critical boundaries!
    let cases: &[(f64, Option<i64>)] = &[
        (0.0, Some(0)),
        (-0.0, Some(0)),
        (pos_pred, Some(0)),
        (neg_pred_exact, Some(0)),
        (0.5, Some(1)),
        (-0.5, Some(-1)),
        (1.5, Some(2)),
        (-1.5, Some(-2)),
        (2.5, Some(3)),
        (-2.5, Some(-3)),
        (4503599627370495.5, Some(4503599627370496)),   // 2^52 - 0.5 (last fractional binary64)
        (-4503599627370495.5, Some(-4503599627370496)), // -(2^52 - 0.5)
        (4503599627370497.0, Some(4503599627370497)),   // 2^52 + 1 (odd integer > 2^52)
        (-9_223_372_036_854_775_808.0, Some(i64::MIN)), // -2^63 exact
        (f64::from_bits(0x43df_ffff_ffff_ffff), Some(9_223_372_036_854_774_784)), // max f64 < 2^63 (`2^63 - 1024`)
        (9_223_372_036_854_775_808.0, None),            // +2^63 overflows i64::MAX
        (f64::from_bits(0xc3e0_0000_0000_0001), None),  // next f64 below -2^63 (`-2^63 - 2048`)
        (f64::NAN, None),
        (f64::INFINITY, None),
        (f64::NEG_INFINITY, None),
    ];

    for &(x, expected) in cases {
        let got = sterbenz_round_away_from_zero_to_i64(x);
        assert_eq!(
            got, expected,
            "mismatch for x={x} (bits=0x{:016x})",
            x.to_bits()
        );
        if let Some(exp_i64) = expected {
            assert_eq!(x.round() as i64, exp_i64);
        }
    }

    println!(
        "STERBENZ_PROBE_OK: pos_pred(0x{:016x}) buggy={:?} sterbenz={:?} max_lt_2p63={:?}",
        pos_pred.to_bits(),
        buggy_floor_plus_half_to_i64(pos_pred),
        sterbenz_round_away_from_zero_to_i64(pos_pred),
        sterbenz_round_away_from_zero_to_i64(f64::from_bits(0x43df_ffff_ffff_ffff)),
    );
}
