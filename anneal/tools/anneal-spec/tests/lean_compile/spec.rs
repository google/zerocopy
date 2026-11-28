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
