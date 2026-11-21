// Mutual recursion between `even_step` and `odd_step`.
//
// Built two ways from the same source:
//   * default:            the transfer is `become callee(..)` (explicit tail call);
//   * `--cfg plain_call`: the transfer is `return callee(..)`  (ordinary call).
//
// Each activation records a "depth witness" so the run reports how far apart the
// shallowest and deepest activations were:
//   * native: the address of a stack local (bytes of stack between activations);
//   * Miri:   `miri_backtrace_size`, i.e. the number of frames on Miri's call stack.
//
// The recursion runs on a spawned thread with an explicit stack size so the
// ordinary-call build overflows deterministically instead of depending on the
// process stack limit.
//
// usage: tail_recursion <steps> <thread_stack_bytes>
#![cfg_attr(not(plain_call), feature(explicit_tail_calls))]
#![cfg_attr(not(plain_call), allow(incomplete_features))]

use std::sync::atomic::{AtomicUsize, Ordering};

static MIN_WITNESS: AtomicUsize = AtomicUsize::new(usize::MAX);
static MAX_WITNESS: AtomicUsize = AtomicUsize::new(0);

#[cfg(miri)]
unsafe extern "Rust" {
    fn miri_backtrace_size(flags: u64) -> usize;
}

#[inline(never)]
fn note_activation() {
    #[cfg(miri)]
    let witness = unsafe { miri_backtrace_size(0) };
    #[cfg(not(miri))]
    let witness = {
        let marker = 0u8;
        std::hint::black_box(&marker as *const u8 as usize)
    };
    MIN_WITNESS.fetch_min(witness, Ordering::Relaxed);
    MAX_WITNESS.fetch_max(witness, Ordering::Relaxed);
}

#[cfg(not(plain_call))]
macro_rules! transfer {
    ($e:expr) => {
        become $e
    };
}
#[cfg(plain_call)]
macro_rules! transfer {
    ($e:expr) => {
        return $e
    };
}

#[inline(never)]
fn even_step(n: u64, acc: u64) -> u64 {
    note_activation();
    if n == 0 {
        return acc;
    }
    transfer!(odd_step(n - 1, acc + 1))
}

#[inline(never)]
fn odd_step(n: u64, acc: u64) -> u64 {
    note_activation();
    if n == 0 {
        return acc;
    }
    transfer!(even_step(n - 1, acc + 1))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let steps: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(250_000);
    let stack_bytes: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(1 << 20);

    let handle = std::thread::Builder::new()
        .stack_size(stack_bytes)
        .spawn(move || even_step(steps, 0))
        .expect("spawn");
    let result = handle.join().expect("join");

    let min = MIN_WITNESS.load(Ordering::Relaxed);
    let max = MAX_WITNESS.load(Ordering::Relaxed);
    let mode = if cfg!(plain_call) { "plain_call" } else { "become" };
    let witness = if cfg!(miri) { "miri_frames" } else { "stack_bytes" };
    println!(
        "MODE={mode} STEPS={steps} RESULT={result} WITNESS={witness} WITNESS_SPAN={}",
        max - min
    );
}
