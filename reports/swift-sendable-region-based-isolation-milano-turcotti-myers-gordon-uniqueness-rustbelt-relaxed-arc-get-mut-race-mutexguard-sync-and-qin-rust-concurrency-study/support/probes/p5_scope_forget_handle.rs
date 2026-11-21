// Run: leak (mem::forget) a ScopedJoinHandle. Question: can scope() return
// while the child may still run, or does it wait? A detached watchdog thread
// reports if scope() has not returned 2 s after the child finished.
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Duration;
fn main() {
    std::thread::spawn(|| {
        std::thread::sleep(Duration::from_millis(2300));
        println!("watchdog: scope() still blocked ~2 s after the child finished");
        std::process::exit(3);
    });
    let done = AtomicU32::new(0);
    std::thread::scope(|s| {
        let h = s.spawn(|| {
            std::thread::sleep(Duration::from_millis(300));
            done.store(1, Ordering::Relaxed);
            println!("child: finished");
        });
        std::mem::forget(h);
    });
    println!("after scope: done = {}", done.load(Ordering::Relaxed));
}
