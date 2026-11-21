#![allow(dead_code)]
extern "Rust" {
    #[track_caller]
    fn g() -> u32;
}
fn main() {}
