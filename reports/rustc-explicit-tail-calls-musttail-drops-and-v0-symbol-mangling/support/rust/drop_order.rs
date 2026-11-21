// Destructor ordering around `become`, compared against an ordinary `return call(..)`.
//
// Every `Guard(d)` appends the decimal digit `d` to a global log when its
// destructor runs; callee bodies append `9`. Each scenario prints the log as one
// decimal number, so the digit sequence is the order of events.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

use std::sync::atomic::{AtomicU64, Ordering};

static LOG: AtomicU64 = AtomicU64::new(0);

fn log(digit: u64) {
    LOG.store(LOG.load(Ordering::Relaxed) * 10 + digit, Ordering::Relaxed);
}

fn take_log() -> u64 {
    LOG.swap(0, Ordering::Relaxed)
}

struct Guard(u64);

impl Drop for Guard {
    fn drop(&mut self) {
        log(self.0);
    }
}

// ---- scenario 1: one parameter guard, one local guard, one fresh argument ----

#[inline(never)]
fn callee(_callee_guard: Guard, x: u64) -> u64 {
    log(9);
    x + 100
}

#[inline(never)]
fn tail_caller(param_guard: Guard, x: u64) -> u64 {
    let _local_guard = Guard(2);
    let _ = &param_guard;
    become callee(Guard(3), x)
}

#[inline(never)]
fn plain_caller(param_guard: Guard, x: u64) -> u64 {
    let _local_guard = Guard(2);
    let _ = &param_guard;
    return callee(Guard(3), x);
}

// ---- scenario 2: two parameters, three locals across nested scopes ----

#[inline(never)]
fn callee2(_g1: Guard, _g2: Guard, x: u64) -> u64 {
    log(9);
    x
}

#[inline(never)]
fn tail_caller2(p1: Guard, p2: Guard, x: u64) -> u64 {
    let _ = (&p1, &p2);
    let _a = Guard(3);
    {
        let _b = Guard(4);
        let _c = Guard(5);
        become callee2(Guard(6), Guard(7), x)
    }
}

#[inline(never)]
fn plain_caller2(p1: Guard, p2: Guard, x: u64) -> u64 {
    let _ = (&p1, &p2);
    let _a = Guard(3);
    {
        let _b = Guard(4);
        let _c = Guard(5);
        return callee2(Guard(6), Guard(7), x);
    }
}

// ---- scenario 3: the caller forwards its own parameter (a move, not a drop) ----

#[inline(never)]
fn tail_forward(param_guard: Guard, x: u64) -> u64 {
    let _local_guard = Guard(2);
    become callee(param_guard, x)
}

fn main() {
    let r = tail_caller(Guard(1), 42);
    println!("S1_BECOME R={r} DROP_ORDER_LOG={}", take_log());
    let r = plain_caller(Guard(1), 42);
    println!("S1_PLAIN R={r} DROP_ORDER_LOG={}", take_log());

    let r = tail_caller2(Guard(1), Guard(2), 7);
    println!("S2_BECOME R={r} DROP_ORDER_LOG={}", take_log());
    let r = plain_caller2(Guard(1), Guard(2), 7);
    println!("S2_PLAIN R={r} DROP_ORDER_LOG={}", take_log());

    let r = tail_forward(Guard(1), 5);
    println!("S3_BECOME_FORWARD R={r} DROP_ORDER_LOG={}", take_log());
}
