// Integer overflow behavior depends on build profile (overflow checks).
// rustc --edition 2021 rust_overflow_probe.rs -o ovf_debug            (debug: checks on)
// rustc --edition 2021 -O rust_overflow_probe.rs -o ovf_release       (release: checks off)
fn main() {
    let x: u8 = std::env::args().count() as u8 + 199; // 200 at run time, opaque to const-eval
    let y = x + 100;
    println!("200u8 + 100 = {}", y);
}
