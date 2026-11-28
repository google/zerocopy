// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifications whose generated `Spec.lean` must compile against
// `prelude` + `Trusted.MirSemantics` alone, exercising every lowering that
// names a library function. `Check.lean` pins what each helper means, so a
// lowering that compiles but means something else still fails.
// `anneal/ci/verify_anneal_spec_zerocopy.py` compiles both.

anneal::external_spec! {
    #[anneal::pure]
    fn one() -> u8 {
        1u8
    }

    #[anneal::pure]
    fn tdiv_is(a: i32, b: i32, q: i32) -> bool {
        b != 0i32 && math(a / b) == math(q)
    }

    #[anneal::pure]
    fn tmod_is(a: i32, b: i32, r: i32) -> bool {
        b != 0i32 && math(a % b) == math(r)
    }

    #[anneal::pure]
    fn wadd_is(a: u8, b: u8, r: u8) -> bool {
        wrapping_add(a, b) == r
    }

    #[anneal::pure]
    fn wsub_is(a: i8, b: i8, r: i8) -> bool {
        wrapping_sub(a, b) == r
    }

    #[anneal::pure]
    fn wmul_is(a: u16, b: u16, r: u16) -> bool {
        wrapping_mul(a, b) == r
    }

    // Each parameter is named like something the generated Lean references
    // in qualified form; none of them may capture that reference.
    #[anneal::pure]
    fn no_capture(pure_one: u8, intTdiv: i32, intTmod: i32, intEmod: u8, Val: u8, neg: i32) -> bool {
        pure_one == one()
            && math(intTdiv / 2) == math(intTmod % 3)
            && wrapping_add(intEmod, Val) == intEmod
            && -1i32 < neg
    }

    #[anneal::pure]
    fn unit_eq(Val: u8) -> bool {
        Val == Val && () == ()
    }

    // Integer constants lower to their values on the profile v1 target,
    // where `usize` and `isize` are 64 bits wide.
    #[anneal::pure]
    fn consts_are(umax: usize, imin: isize, i8min: i8, u128max: u128, bits: u32) -> bool {
        umax == usize::MAX
            && imin == isize::MIN
            && i8min == i8::MIN
            && u128max == u128::MAX
            && bits == usize::BITS
            && u32::MIN == 0u32
    }

    // An `if` that chooses a value lowers to Lean's `if`, so its condition
    // must be decidable. A `bool`-valued `if` lowers to two implications,
    // which also admit a `bool` helper parameter as the condition.
    #[anneal::pure]
    fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
        if x < lo { lo } else if x > hi { hi } else { x }
    }

    #[anneal::pure]
    fn sign_is(x: i8, s: i8) -> bool {
        s == if x < 0 { -1 } else if x == 0 { 0 } else { 1 }
    }

    #[anneal::pure]
    fn div_or_zero_is(n: u32, d: u32, r: u32) -> bool {
        if d == 0u32 { r == 0u32 } else { math(r) == math(n / d) }
    }

    #[anneal::pure]
    fn flag_is(b: bool, r: u8) -> bool {
        if b { r == 1u8 } else { r == 0u8 }
    }

    #[anneal::spec(
        requires(div_or_zero_is(n, n, 1u32) && flag_is(flag, 1u8) && sign_is(0i8, 0i8)),
        max_steps = if n > 100 { n } else { 100 },
        ensures(|r| (r == if flag { n } else { 0u32 }) && clamp(0i32, 1i32, 2i32) == 1i32),
    )]
    fn piecewise(n: u32, flag: bool) -> u32;

    // A `let` binding lowers to a Lean `let` with its value's type.
    #[anneal::pure]
    fn let_sum_is(a: i32, b: i32, r: i32) -> bool {
        let s = math(a) + math(b);
        let t: i32 = r;
        math(t) == s
    }

    #[anneal::pure]
    fn let_pick(x: u8) -> u8 {
        let big = x > 9u8;
        if big { let y: u8 = 9; y } else { x }
    }

    #[anneal::pure]
    fn let_div_is(n: u32, d: u32, r: u32) -> bool {
        let ok = d != 0u32;
        if ok { math(r) == math(n / d) } else { r == 0u32 }
    }

    // Lean decides an `if` condition through a block's bindings.
    #[anneal::pure]
    fn let_guarded_pick(n: u8, d: u8) -> u8 {
        if d != 0u8 { if ({ let p = n > 1u8 && math(n / d) > 0; p }) { 1u8 } else { 0u8 } } else { 2u8 }
    }

    #[anneal::pure]
    fn let_math_cond_is(n: u8, r: u8) -> bool {
        math(r) == math(if ({ let k = 1; n > 1u8 && k > 0 }) { 1 } else { 0 })
    }

    #[anneal::spec(
        requires(let_sum_is(1i32, 2i32, 3i32) && let_div_is(n, 2u32, 1u32) && let_pick(b) == 9u8),
        max_steps = { let base: u32 = 7; let twice = n * 2; if twice > base { twice } else { base } },
        ensures(|r| { let m = math(n) + 1; math(r) == m }),
    )]
    fn stepped(n: u32, b: u8) -> u32;

    // A `match` choosing a value lowers to Lean's `if` over equalities with
    // the bound scrutinee, and one choosing a `bool` to implications.
    #[anneal::pure]
    fn match_bucket(x: u8) -> u8 {
        match x { 0 => 0, 1 | 2 => 1, u8::MAX => 3, _ => 2 }
    }

    #[anneal::pure]
    fn match_flag_is(b: bool, r: u8) -> bool {
        match b { true => r == 1u8, false => r == 0u8 }
    }

    #[anneal::pure]
    fn match_div_is(n: u32, d: u32, r: u32) -> bool {
        match d { 0 => r == 0u32, k => { let s = math(n / k); math(r) == s } }
    }

    #[anneal::spec(
        requires(match_bucket(n8) == 1u8 && match_flag_is(true, 1u8) && match_div_is(7u32, 2u32, 3u32)),
        max_steps = match n { 0 => 1, m => m * 2 },
        ensures(|r| match n { 0 => r == 0u32, _ => math(r) >= 0 }),
    )]
    fn tiered(n: u32, n8: u8) -> u32;

    // Saturating arithmetic clamps the exact result to the type's range,
    // negation wraps or overflows only at the type's edge, and `abs_diff` is
    // the exact distance, in the unsigned type of the operands' width.
    #[anneal::pure]
    fn sadd_is(a: u8, b: u8, r: u8) -> bool {
        saturating_add(a, b) == r
    }

    #[anneal::pure]
    fn ssub_is(a: i8, b: i8, r: i8) -> bool {
        saturating_sub(a, b) == r
    }

    #[anneal::pure]
    fn smul_is(a: i16, b: i16, r: i16) -> bool {
        saturating_mul(a, b) == r
    }

    #[anneal::pure]
    fn sneg_is(a: i8, r: i8) -> bool {
        saturating_neg(a) == r
    }

    #[anneal::pure]
    fn wneg_u_is(a: u8, r: u8) -> bool {
        wrapping_neg(a) == r
    }

    #[anneal::pure]
    fn wneg_i_is(a: i8, r: i8) -> bool {
        wrapping_neg(a) == r
    }

    #[anneal::pure]
    fn neg_ok_u(a: u8) -> bool {
        no_overflow_neg(a)
    }

    #[anneal::pure]
    fn neg_ok_i(a: i8) -> bool {
        no_overflow_neg(a)
    }

    #[anneal::pure]
    fn diff_i_is(a: i8, b: i8, r: u8) -> bool {
        abs_diff(a, b) == r
    }

    #[anneal::pure]
    fn diff_u_is(a: u32, b: u32, r: u32) -> bool {
        abs_diff(a, b) == r
    }

    // The parameter is named like the binder of a saturating result, which
    // must not capture it.
    #[anneal::pure]
    fn sat_nested(saturating: u8) -> u8 {
        saturating_add(saturating_add(saturating, 1u8), saturating)
    }

    // Bitwise operators act on the two's-complement bits of their machine
    // operands, and shifts by a constant drop the bits shifted past the
    // width (`<<`) or shift arithmetically (`>>` on a signed type).
    #[anneal::pure]
    fn bits_u_is(a: u8, b: u8, and: u8, or: u8, xor: u8, not: u8) -> bool {
        a & b == and && a | b == or && a ^ b == xor && (!a) == not
    }

    #[anneal::pure]
    fn bits_i_is(a: i8, b: i8, and: i8, or: i8, xor: i8, not: i8) -> bool {
        a & b == and && a | b == or && a ^ b == xor && (!a) == not
    }

    #[anneal::pure]
    fn shifts_u(a: u8) -> u8 {
        (a << 3) | (a >> 5)
    }

    #[anneal::pure]
    fn shifts_i(a: i8) -> i8 {
        (a << 1) ^ (a >> 7)
    }

    #[anneal::pure]
    fn shl_i(a: i8) -> i8 {
        a << 1
    }

    // A `let`-bound amount is a constant too.
    #[anneal::pure]
    fn shifts_let(a: i16) -> i16 {
        let k: u8 = 3;
        let m: u32 = 4;
        (a >> k) << m
    }

    // `as` keeps a value that fits in the target type and otherwise
    // reduces it modulo `2^bits`; a decidable `bool` casts to `1` or `0`.
    #[anneal::pure]
    fn cast_u8(a: i32) -> u8 {
        a as u8
    }

    #[anneal::pure]
    fn cast_i8(a: u16) -> i8 {
        a as i8
    }

    #[anneal::pure]
    fn cast_u32(a: i8) -> u32 {
        a as u32
    }

    #[anneal::pure]
    fn cast_chain(a: i16) -> u32 {
        a as u8 as u32
    }

    #[anneal::pure]
    fn cast_widen(a: i8) -> i64 {
        a as i64
    }

    #[anneal::pure]
    fn cast_lt(a: u8, b: u8) -> u8 {
        (a < b) as u8
    }

    #[anneal::pure]
    fn cast_math(a: u8, b: u8) -> u8 {
        math(a + b) as u8
    }

    // Integer methods: intrinsics with the receiver first, Lean's `min` and
    // `max`, `clamp` to constant bounds, and `is_power_of_two`.
    #[anneal::pure]
    fn wadd_method(a: i8, b: i8) -> i8 {
        a.wrapping_add(b)
    }

    #[anneal::pure]
    fn min_max(a: u8, b: u8) -> u8 {
        a.min(b).max(3)
    }

    #[anneal::pure]
    fn clamp_i(a: i8) -> i8 {
        a.clamp(-5, 5)
    }

    #[anneal::pure]
    fn pow2(a: u32) -> bool {
        a.is_power_of_two()
    }

    // `div_ceil` rounds up, `is_multiple_of(0)` holds of `0`, and rotations
    // wrap the bits around, sign-extending a signed result.
    #[anneal::pure]
    fn dceil(a: u8, b: u8) -> u8 {
        if b == 0 { 0 } else { a.div_ceil(b) }
    }

    #[anneal::pure]
    fn multiple(a: u16, b: u16) -> bool {
        a.is_multiple_of(b)
    }

    #[anneal::pure]
    fn rotl(a: u8, n: u32) -> u8 {
        a.rotate_left(n)
    }

    #[anneal::pure]
    fn rotr_i(a: i8, n: u32) -> i8 {
        a.rotate_right(n)
    }

    #[anneal::pure]
    fn rotl64(a: u64) -> u64 {
        a.rotate_left(63)
    }

    // Sign tests, `signum`, magnitudes, and same-width bit casts.
    #[anneal::pure]
    fn sig(a: i8) -> i8 {
        a.signum()
    }

    #[anneal::pure]
    fn nonzero(a: i16) -> bool {
        a.is_positive() || a.is_negative()
    }

    #[anneal::pure]
    fn negative(a: i16) -> bool {
        a.is_negative()
    }

    #[anneal::pure]
    fn uabs(a: i8) -> u8 {
        a.unsigned_abs()
    }

    #[anneal::pure]
    fn sabs(a: i8) -> i8 {
        a.saturating_abs()
    }

    #[anneal::pure]
    fn wabs(a: i8) -> i8 {
        a.wrapping_abs()
    }

    #[anneal::pure]
    fn to_signed(a: u8) -> i8 {
        a.cast_signed()
    }

    #[anneal::pure]
    fn to_unsigned(a: i8) -> u8 {
        a.cast_unsigned()
    }

    // Mixed-signedness arithmetic wraps or saturates into the receiver's
    // type.
    #[anneal::pure]
    fn wadd_signed(a: u8, b: i8) -> u8 {
        a.wrapping_add_signed(b)
    }

    #[anneal::pure]
    fn sadd_signed(a: u8, b: i8) -> u8 {
        a.saturating_add_signed(b)
    }

    #[anneal::pure]
    fn wsub_signed(a: u8, b: i8) -> u8 {
        a.wrapping_sub_signed(b)
    }

    #[anneal::pure]
    fn ssub_signed(a: u8, b: i8) -> u8 {
        a.saturating_sub_signed(b)
    }

    #[anneal::pure]
    fn wadd_unsigned(a: i8, b: u8) -> i8 {
        a.wrapping_add_unsigned(b)
    }

    #[anneal::pure]
    fn wsub_unsigned(a: i8, b: u8) -> i8 {
        a.wrapping_sub_unsigned(b)
    }

    #[anneal::pure]
    fn sadd_unsigned(a: i8, b: u8) -> i8 {
        a.saturating_add_unsigned(b)
    }

    #[anneal::pure]
    fn ssub_unsigned(a: i8, b: u8) -> i8 {
        a.saturating_sub_unsigned(b)
    }

    // Unbounded shifts shift every bit out by an amount not below the
    // width, and `midpoint` rounds toward zero.
    #[anneal::pure]
    fn ushl(a: u8, n: u32) -> u8 {
        a.unbounded_shl(n)
    }

    #[anneal::pure]
    fn ishl(a: i8, n: u32) -> i8 {
        a.unbounded_shl(n)
    }

    #[anneal::pure]
    fn ushr(a: u32, n: u32) -> u32 {
        a.unbounded_shr(n)
    }

    #[anneal::pure]
    fn ishr(a: i8, n: u32) -> i8 {
        a.unbounded_shr(n)
    }

    #[anneal::pure]
    fn mid_u(a: u8, b: u8) -> u8 {
        a.midpoint(b)
    }

    #[anneal::pure]
    fn mid_i(a: i8, b: i8) -> i8 {
        a.midpoint(b)
    }

    // Division methods, each guarded against a zero divisor.
    #[anneal::pure]
    fn wdiv(a: i8, b: i8) -> i8 {
        if b == 0 { 0 } else { a.wrapping_div(b) }
    }

    #[anneal::pure]
    fn wrem(a: i8, b: i8) -> i8 {
        if b == 0 { 0 } else { a.wrapping_rem(b) }
    }

    #[anneal::pure]
    fn wdive(a: i8, b: i8) -> i8 {
        if b == 0 { 0 } else { a.wrapping_div_euclid(b) }
    }

    #[anneal::pure]
    fn wreme(a: i8, b: i8) -> i8 {
        if b == 0 { 0 } else { a.wrapping_rem_euclid(b) }
    }

    #[anneal::pure]
    fn dive(a: u8, b: u8) -> u8 {
        if b == 0 { 0 } else { a.div_euclid(b) }
    }

    #[anneal::pure]
    fn reme(a: u8, b: u8) -> u8 {
        if b == 0 { 0 } else { a.rem_euclid(b) }
    }

    // `saturating_div` saturates only `MIN / -1`, which is also the only
    // quotient that `no_overflow_div` rules out.
    #[anneal::pure]
    fn sdiv(a: i8, b: i8) -> i8 {
        if b == 0 { 0 } else { a.saturating_div(b) }
    }

    #[anneal::pure]
    fn sdiv_u(a: u8, b: u8) -> u8 {
        if b == 0 { 0 } else { saturating_div(a, b) }
    }

    #[anneal::pure]
    fn nodiv(a: i8, b: i8) -> bool {
        if b == 0 { true } else { no_overflow_div(a, b) }
    }

    #[anneal::pure]
    fn wshl_is(a: u16, n: u32, r: u16) -> bool {
        wrapping_shl(a, n) == r
    }

    #[anneal::pure]
    fn wshr_is(a: i16, n: u32, r: i16) -> bool {
        wrapping_shr(a, n) == r
    }

    #[anneal::spec(
        requires(diff_u_is(n, n, 0u32) && sadd_is(a, 255u8, 255u8)),
        max_steps = {
            let k: u32 = 31;
            abs_diff(a, b) + saturating_add(n, 1u32) + (n & 15u32) + (n >> 30) + (n >> k)
                + n as u8 as u32
                + a.max(b) as u32
                + n.div_ceil(8)
                + a.cast_signed().unsigned_abs() as u32
                + b.saturating_add_signed(-1) as u32
                + n.unbounded_shr(31)
                + n.div_euclid(16)
                + n.saturating_div(1024)
        },
        ensures(|r| r == saturating_sub(n, 1u32)),
    )]
    fn usat(a: u8, b: u8, n: u32) -> u32;

    #[anneal::spec(
        requires(math(n) + 1 <= math(usize::MAX)),
        max_steps = u8::MAX + u32::BITS * 2 + n / u16::MAX,
        ensures(|r| math(r) == math(n) + 1),
    )]
    fn consts(n: usize) -> usize;

    #[anneal::spec(
        requires(d != 0u32),
        ensures(|r| math(r) == math(n / d) && math(n % d) < math(d)),
    )]
    fn div(n: u32, d: u32) -> u32;

    // `syntax` is a Lean keyword, which the claim's module namespace must
    // escape.
    #[anneal::spec(
        claim = "syntax",
        ensures(|r| r == wrapping_mul(wrapping_sub(wrapping_add(a, b), b), 1i64)),
    )]
    fn wrap(a: i64, b: i64) -> i64;

    #[anneal::spec(requires(tdiv_is(a, b, q) && no_capture(1u8, a, b, 0u8, 0u8, q) && unit_eq(0u8)))]
    fn helpers(a: i32, b: i32, q: i32);

    #[anneal::spec(
        requires(d != 0usize),
        terminates,
        no_panic,
        max_steps = 34 * n + n / d + n % 2 + wrapping_add(one(), 1u8) + 540,
        ensures(|r| r == n),
    )]
    fn bounded(n: usize, d: usize) -> usize;
}
