use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

fn main() {
    let x = Arc::new(AtomicUsize::new(0));
    let y = Arc::new(AtomicUsize::new(0));
    let x1 = Arc::clone(&x);
    let y1 = Arc::clone(&y);
    let t1 = thread::spawn(move || {
        x1.store(1, Ordering::Release);
        y1.load(Ordering::Acquire)
    });
    let t2 = thread::spawn(move || {
        y.store(1, Ordering::Release);
        x.load(Ordering::Acquire)
    });
    let r1 = t1.join().unwrap();
    let r2 = t2.join().unwrap();
    assert!(r1 <= 1 && r2 <= 1);
}
