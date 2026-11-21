//! Bounded-coverage probe for Loom's preemption bound.
//!
//! Thread A performs two stores (x=1, x=2); thread B performs two loads.
//! The assertion fails only for the interleaving in which B's first load
//! falls between A's two stores and B's second load follows A's second
//! store. Running with LOOM_MAX_PREEMPTIONS=k shows for which k the
//! failing interleaving is inside the explored schedule set.
use loom::sync::atomic::{AtomicUsize, Ordering::SeqCst};
use loom::sync::Arc;
use loom::thread;
use std::sync::atomic::{AtomicUsize as StdAtomic, Ordering};

static ITERS: StdAtomic = StdAtomic::new(0);

fn main() {
    // With PROBE_NOASSERT set, the assertion is disabled so that the run
    // reports the total number of executions explored under the bound.
    let check = std::env::var("PROBE_NOASSERT").is_err();
    let found = std::panic::catch_unwind(|| {
        loom::model(move || {
            ITERS.fetch_add(1, Ordering::Relaxed);
            let x = Arc::new(AtomicUsize::new(0));
            let xa = x.clone();
            let a = thread::spawn(move || {
                xa.store(1, SeqCst);
                xa.store(2, SeqCst);
            });
            let xb = x.clone();
            let b = thread::spawn(move || {
                let r1 = xb.load(SeqCst);
                let r2 = xb.load(SeqCst);
                if check {
                    assert!(!(r1 == 1 && r2 == 2), "interleaving A1 B1 A2 B2 reached");
                }
            });
            a.join().unwrap();
            b.join().unwrap();
        });
    })
    .is_err();
    println!(
        "LOOM_MAX_PREEMPTIONS={} assertion={} failure_found={} executions_explored={}",
        std::env::var("LOOM_MAX_PREEMPTIONS").unwrap_or_else(|_| "unset".into()),
        if check { "on" } else { "off" },
        found,
        ITERS.load(Ordering::Relaxed)
    );
}
