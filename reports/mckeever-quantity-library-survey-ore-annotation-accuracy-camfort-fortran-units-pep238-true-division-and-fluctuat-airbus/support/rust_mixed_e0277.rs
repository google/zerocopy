// Expected to FAIL to compile: Rust has no implicit numeric promotion.
// rustc --edition 2021 rust_mixed_e0277.rs
fn mean(sum: u32, n: u32) -> f64 {
    sum / n            // error[E0308]: mismatched types (expected f64, found u32)
}
fn main() {
    let a = 1u32 + 1.0f64;   // error[E0277]: cannot add `f64` to `u32`
    let b: u64 = 1u32;       // error[E0308]: mismatched types (no implicit widening)
    println!("{} {} {}", mean(7, 2), a, b);
}
