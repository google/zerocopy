// `become` is unstable (`explicit_tail_calls`); this file needs a nightly.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]
use std::panic::Location;

#[track_caller]
#[inline(never)]
fn tracked_target() -> u32 { // @TAIL_TARGET_DEF
    Location::caller().line()
}

#[inline(never)]
fn tail_caller() -> u32 {
    become tracked_target(); // @TAIL_CALL_SITE
}

#[inline(never)]
fn plain_caller() -> u32 {
    tracked_target() // @PLAIN_CALL_SITE
}

fn main() {
    println!("TAIL_CALL={}", tail_caller()); // @TAIL_CALLER_CALL_SITE
    println!("PLAIN_CALL={}", plain_caller());
}
