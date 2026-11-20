// Cross-check of the Rust integer-semantics claims in REPORT.md against rustc (execution evidence only).
#![feature(exact_bitshifts)]
use std::hint::black_box as bb;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn try_<T: std::fmt::Debug>(f: impl FnOnce() -> T) -> String {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => format!("ok({:?})", v),
        Err(_) => "PANIC".to_string(),
    }
}

#[allow(overflowing_literals)]
fn trunc_lit() -> i8 { 128_i8 }

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let oc = try_(|| bb(u8::MAX) + bb(1u8));
    println!("overflow_checks_behavioral: {}", if oc == "PANIC" { "on" } else { "off" });
    // literals / unary minus
    let a: i8 = -128_i8;
    let b: i8 = -(128_i8);
    let c: i8 = -(128);
    println!("lit -128_i8 = {a}; -(128_i8) = {b}; -(128) = {c}");
    println!("allow(overflowing_literals) 128_i8 = {}", trunc_lit());
    println!("runtime -(MIN) via black_box = {}", try_(|| -bb(i8::MIN)));
    // shifts
    println!("128u8.checked_shl(1) = {:?}", 128u8.checked_shl(1));
    println!("64i8.checked_shl(1) = {:?}", 64i8.checked_shl(1));
    println!("128u8.checked_mul(2) = {:?}; 64i8.checked_mul(2) = {:?}", 128u8.checked_mul(2), 64i8.checked_mul(2));
    println!("128u8 << 1 (bb) = {}", try_(|| bb(128u8) << bb(1u32)));
    println!("64i8 << 1 (bb) = {}", try_(|| bb(64i8) << bb(1u32)));
    println!("1u8 << 8 (bb) = {}", try_(|| bb(1u8) << bb(8u32)));
    println!("1u8.checked_shl(8) = {:?}", 1u8.checked_shl(8));
    println!("wrapping_shl: 1u8,8 -> {}; 5u8,9 -> {}; -1i8,8 -> {}", 1u8.wrapping_shl(8), 5u8.wrapping_shl(9), (-1i8).wrapping_shl(8));
    println!("unbounded_shl: 1u8,8 -> {}", 1u8.unbounded_shl(8));
    println!("shl_exact(nightly): 128u8,1 -> {:?}; 64i8,1 -> {:?}; 1u8,3 -> {:?}", 128u8.shl_exact(1), 64i8.shl_exact(1), 1u8.shl_exact(3));
    println!("wrapping_shr: 128u8,8 -> {}; -128i8,8 -> {}; (-1i8)>>1 -> {}; (-1i8)/2 -> {}", 128u8.wrapping_shr(8), (-128i8).wrapping_shr(8), (-1i8) >> 1, (-1i8) / 2);
    println!("-7i8 >> 2 = {}", (-7i8) >> 2);
    // division
    println!("MIN / -1 (bb) = {}", try_(|| bb(i8::MIN) / bb(-1i8)));
    println!("MIN % -1 (bb) = {}", try_(|| bb(i8::MIN) % bb(-1i8)));
    println!("7 / 0 (bb) = {}", try_(|| bb(7i8) / bb(0i8)));
    println!("MIN.checked_div(-1) = {:?}; MIN.checked_rem(-1) = {:?}; MIN.checked_rem_euclid(-1) = {:?}; MIN.checked_div_euclid(-1) = {:?}",
        i8::MIN.checked_div(-1), i8::MIN.checked_rem(-1), i8::MIN.checked_rem_euclid(-1), i8::MIN.checked_div_euclid(-1));
    println!("MIN.wrapping_rem(-1) = {}; MIN.wrapping_div(-1) = {}", i8::MIN.wrapping_rem(-1), i8::MIN.wrapping_div(-1));
    println!("-7/4 = {}; -7%4 = {}; div_euclid = {}; rem_euclid = {}", (-7i8) / 4, (-7i8) % 4, (-7i8).div_euclid(4), (-7i8).rem_euclid(4));
    println!("7/-4 = {}; 7%-4 = {}; div_euclid = {}; rem_euclid = {}", 7i8 / -4, 7i8 % -4, 7i8.div_euclid(-4), 7i8.rem_euclid(-4));
    println!("(-1i8).rem_euclid(-128) = {}; (-1i8).div_euclid(-128) = {}", (-1i8).rem_euclid(-128), (-1i8).div_euclid(-128));
    // exhaustive i8 check of div_euclid/rem_euclid vs Euclidean definition and tdiv
    let mut bad = 0;
    for x in i8::MIN..=i8::MAX { for y in i8::MIN..=i8::MAX {
        if y == 0 || (x == i8::MIN && y == -1) { continue; }
        let (xi, yi) = (x as i32, y as i32);
        let r = xi.rem_euclid(yi); let q = (xi - r) / yi;
        if x.div_euclid(y) as i32 != q || x.rem_euclid(y) as i32 != r { bad += 1; }
        if (x / y) as i32 != xi / yi || (x % y) as i32 != xi % yi { bad += 1; }
    }}
    println!("exhaustive i8 euclid/trunc mismatches = {bad}");
    // add-sub intermediate overflow
    println!("(200u8+100)-100 (bb) = {}", try_(|| (bb(200u8) + bb(100u8)) - bb(100u8)));
    println!("(100i8+50)-50 (bb) = {}", try_(|| (bb(100i8) + bb(50i8)) - bb(50i8)));
    println!("200u8.checked_add(100) = {:?}; 100i8.checked_add(50) = {:?}", 200u8.checked_add(100), 100i8.checked_add(50));
    // order
    println!("u8::MAX.wrapping_add(1) = {}; i8::MAX.wrapping_add(1) = {}", u8::MAX.wrapping_add(1), i8::MAX.wrapping_add(1));
    println!("both-wrap u: {} < {}; s: {} < {}", 200u8.wrapping_add(100), 250u8.wrapping_add(100), 100i8.wrapping_add(100), 120i8.wrapping_add(100));
    // ring non-identities
    let mut ok1 = true; let mut ok2 = true;
    for x in 0..=255u8 { if 64u8.wrapping_mul(4u8.wrapping_mul(x)) != 0 { ok1 = false; } if 128u8.wrapping_mul(x.wrapping_add(x)) != 0 { ok2 = false; } }
    let mut ok3 = true; for x in i8::MIN..=i8::MAX { if 64i8.wrapping_mul(4i8.wrapping_mul(x)) != 0 { ok3 = false; } }
    println!("64*(4*x)==0 u8:{ok1} i8:{ok3}; 128*(x+x)==0 u8:{ok2}");
    // casts
    println!("(256u16 as u8) as u16 = {}; (128i16 as i8) as i16 = {}; (-1i8) as u16 = {}; ((-1i8) as u8) as u16 = {}",
        (bb(256u16) as u8) as u16, (bb(128i16) as i8) as i16, bb(-1i8) as u16, (bb(-1i8) as u8) as u16);
    println!("(0x12345678u32 as u8) as u32 = {:#x}; -17i8 as i16 = {}; -17i8 as u8 = {}; 255u8 as i8 = {}; (256u32 as u16) as u8 = {}",
        (bb(0x12345678u32) as u8) as u32, bb(-17i8) as i16, bb(-17i8) as u8, bb(255u8) as i8, (bb(256u32) as u16) as u8);
    println!("(x as i8) as u32 for x=0x80u32: {}", (bb(0x80u32) as i8) as u32);
    let mut ok4 = true; for x in 0..=255u8 { if (bb(x) as u32) as u16 != x as u16 { ok4 = false; } }
    println!("u8 -> u32 -> u16 preserves every x (target narrower than intermediate): {ok4}");
    println!("f64 casts: 300.7 as u8 = {}; NaN as u8 = {}; -5.5 as u8 = {}", bb(300.7f64) as u8, bb(f64::NAN) as u8, bb(-5.5f64) as u8);
    // neg
    println!("0u8.checked_neg = {:?}; 1u8.checked_neg = {:?}; MIN.checked_neg = {:?}", 0u8.checked_neg(), 1u8.checked_neg(), i8::MIN.checked_neg());
}
