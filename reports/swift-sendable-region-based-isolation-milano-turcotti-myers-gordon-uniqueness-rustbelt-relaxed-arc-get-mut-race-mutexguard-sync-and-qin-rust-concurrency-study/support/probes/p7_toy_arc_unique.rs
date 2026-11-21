// TOY MODEL (not the standard library): the synchronization pattern of a
// reference-count uniqueness check, reduced to one counter and one payload.
// Thread A writes the payload non-atomically, then decrements the counter with
// Release. Thread B spins until it observes count == 1 using ORDER, then
// writes the payload non-atomically. With ORDER = Relaxed there is no
// happens-before edge from A's write to B's write; with Acquire there is.
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicUsize, Ordering};
struct Shared { count: AtomicUsize, payload: UnsafeCell<u64> }
unsafe impl Sync for Shared {}
#[cfg(relaxed)] const ORDER: Ordering = Ordering::Relaxed;
#[cfg(not(relaxed))] const ORDER: Ordering = Ordering::Acquire;
fn main() {
    let sh = Shared { count: AtomicUsize::new(2), payload: UnsafeCell::new(0) };
    let shr = &sh; // move closures below capture this &Shared (Shared: Sync)
    std::thread::scope(|s| {
        s.spawn(move || {
            unsafe { *shr.payload.get() += 1 };       // A: non-atomic write
            shr.count.fetch_sub(1, Ordering::Release); // A: drop its reference
        });
        s.spawn(move || {
            while shr.count.load(ORDER) != 1 { std::thread::yield_now(); }
            unsafe { *shr.payload.get() += 1 };       // B: "unique" access
        });
    });
    println!("payload = {}", unsafe { *sh.payload.get() });
}
