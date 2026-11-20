// Rust numeric-conversion probe.
//
// Part A (compiles): `as` cast semantics and checked conversions.
//   rustc --edition 2021 -O rust_casts_probe.rs -o rust_probe && ./rust_probe
// Part B (must NOT compile): implicit mixing of integer and float; see
//   rust_mixed_e0277.rs. Part C: clippy lints on explicit casts; see
//   clippy_casts_probe/ (run `cargo clippy` with the pedantic cast lints).

use std::convert::TryFrom;

fn main() {
    // Float -> int `as` saturates and maps NaN to 0 (observed on the toolchain recorded in the report).
    println!("300.7f64 as u8 = {}", 300.7f64 as u8);
    println!("-1.5f64 as u8 = {}", -1.5f64 as u8);
    println!("f64::NAN as i32 = {}", f64::NAN as i32);
    println!("1e20f64 as i64 = {}", 1e20f64 as i64);
    println!("-2.9f64 as i32 = {}", -2.9f64 as i32);

    // Int -> int `as` truncates / reinterprets bits.
    println!("300i32 as u8 = {}", 300i32 as u8);
    println!("-1i32 as u32 = {}", -1i32 as u32);
    println!("u32::MAX as i32 = {}", u32::MAX as i32);

    // Int -> float `as` rounds to nearest.
    println!("16777217i32 as f32 = {:.1}", 16777217i32 as f32);
    println!("(i64::MAX as f64) as i64 == i64::MAX: {}", (i64::MAX as f64) as i64 == i64::MAX);

    // Checked conversions.
    println!("u8::try_from(300i32) = {:?}", u8::try_from(300i32));
    println!("i64::from(7i32) = {}", i64::from(7i32));
    println!("f64::from(7i32) = {}", f64::from(7i32));

    // Integer division truncates toward zero; there is no implicit float result.
    println!("7 / 2 = {}, -7 / 2 = {}, (-7i32).div_euclid(2) = {}", 7 / 2, -7 / 2, (-7i32).div_euclid(2));
    println!("7.0 / 2.0 = {}", 7.0f64 / 2.0);

    // Overflow: wrapping_* is explicit; checked_* returns None.
    println!("200u8.checked_add(100) = {:?}", 200u8.checked_add(100));
    println!("200u8.wrapping_add(100) = {}", 200u8.wrapping_add(100));
}
