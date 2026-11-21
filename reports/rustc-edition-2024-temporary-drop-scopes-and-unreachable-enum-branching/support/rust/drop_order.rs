//! Edition-sensitive temporary drop-order probe.
//!
//! Every `Guard(n)` pushes the decimal digit `n` onto a global log when it is
//! dropped; `push(8)` / `push(9)` mark that a `then` / `else` (or match arm)
//! body ran. Reading the log left to right gives the runtime order.
//! Compile once with `--edition 2021` and once with `--edition 2024`.

use std::sync::atomic::{AtomicU64, Ordering};

static LOG: AtomicU64 = AtomicU64::new(0);

#[inline(never)]
fn push(d: u64) {
    let cur = LOG.load(Ordering::Relaxed);
    LOG.store(cur * 10 + d, Ordering::Relaxed);
}

#[inline(never)]
fn take_log() -> u64 {
    LOG.swap(0, Ordering::Relaxed)
}

struct Guard(u64);

impl Drop for Guard {
    fn drop(&mut self) {
        push(self.0)
    }
}

impl Guard {
    #[inline(never)]
    fn val(&self) -> u32 {
        self.0 as u32
    }

    #[inline(never)]
    fn some(&self) -> Option<u32> {
        Some(self.0 as u32)
    }
}

#[inline(never)]
fn id(x: u32) -> u32 {
    x
}

/// Block with one `let` local (`Guard(1)`) and a tail expression that creates
/// a temporary (`Guard(2)`).
#[inline(never)]
fn run_tail_expr() -> (u32, u64) {
    let out = {
        let _local = Guard(1);
        id(Guard(2).val())
    };
    (out, take_log())
}

/// Same shape, but the block is the function body itself.
#[inline(never)]
fn fn_body_tail() -> u32 {
    let _local = Guard(1);
    id(Guard(2).val())
}

/// `if let` whose pattern fails, so the `else` block runs while (2021) or
/// after (2024) the scrutinee temporary `Guard(1)` is alive.
#[inline(never)]
fn run_if_let_else() -> u64 {
    if let None = Guard(1).some() {
        push(8);
    } else {
        push(9);
    }
    take_log()
}

/// `if let` whose pattern succeeds: the `then` block runs with the scrutinee
/// temporary alive in both editions.
#[inline(never)]
fn run_if_let_then() -> u64 {
    if let Some(_) = Guard(1).some() {
        push(8);
    } else {
        push(9);
    }
    take_log()
}

/// `match` with the same scrutinee: the temporary outlives every arm in both
/// editions.
#[inline(never)]
fn run_match() -> u64 {
    match Guard(1).some() {
        None => push(8),
        _ => push(9),
    }
    take_log()
}

/// `match` whose scrutinee is wrapped in a block, making the scrutinee
/// expression a block tail expression.
#[inline(never)]
fn run_match_block_scrutinee() -> u64 {
    match { Guard(1).some() } {
        None => push(8),
        _ => push(9),
    }
    take_log()
}

fn main() {
    let (out, tail) = run_tail_expr();
    let if_let = run_if_let_else();
    let matched = run_match();
    println!("TAIL={} IF_LET={} MATCH={}", tail, if_let, matched);
    let fn_tail_out = fn_body_tail();
    let fn_tail = take_log();
    println!(
        "FN_TAIL={} IF_LET_THEN={} MATCH_BLOCK_SCRUTINEE={}",
        fn_tail,
        run_if_let_then(),
        run_match_block_scrutinee()
    );
    assert_eq!((out, fn_tail_out), (2, 2));
}
