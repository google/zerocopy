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

    #[anneal::spec(
        requires(d != 0u32),
        ensures(|r| math(r) == math(n / d) && math(n % d) < math(d)),
    )]
    fn div(n: u32, d: u32) -> u32;

    #[anneal::spec(ensures(|r| r == wrapping_mul(wrapping_sub(wrapping_add(a, b), b), 1i64)))]
    fn wrap(a: i64, b: i64) -> i64;

    #[anneal::spec(requires(tdiv_is(a, b, q) && no_capture(1u8, a, b, 0u8, 0u8, q) && unit_eq(0u8)))]
    fn helpers(a: i32, b: i32, q: i32);
}
