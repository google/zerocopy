#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]
fn target() -> u32 {
    0
}
#[track_caller]
fn tracked_caller() -> u32 {
    become target();
}
fn main() {
    let _ = tracked_caller();
}
