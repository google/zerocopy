//! A field is moved out of a box and a panic unwinds through the frame. Expected: no error and
//! no leak; every destructor runs exactly once.
#![allow(dead_code)]
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

static DROPS: [AtomicUsize; 2] = [AtomicUsize::new(0), AtomicUsize::new(0)];

struct Counted(usize, Box<u64>);

impl Drop for Counted {
    fn drop(&mut self) {
        DROPS[self.0].fetch_add(1, SeqCst);
    }
}

struct Pair {
    first: Counted,
    second: Counted,
}

fn main() {
    let r = catch_unwind(AssertUnwindSafe(|| {
        let b = Box::new(Pair { first: Counted(0, Box::new(10)), second: Counted(1, Box::new(11)) });
        let first = b.first;
        if std::hint::black_box(true) {
            panic!("deliberate panic");
        }
        drop(first);
    }));
    assert!(r.is_err());
    assert_eq!(DROPS[0].load(SeqCst), 1);
    assert_eq!(DROPS[1].load(SeqCst), 1);
    println!("ok");
}
