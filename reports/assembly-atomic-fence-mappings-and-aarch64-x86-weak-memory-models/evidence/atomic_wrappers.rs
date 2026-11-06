#![crate_type = "lib"]
use std::sync::atomic::{AtomicU32, Ordering, fence};

#[no_mangle]
pub extern "C" fn publish_relaxed(data: &AtomicU32, flag: &AtomicU32) {
    data.store(1, Ordering::Relaxed);
    flag.store(1, Ordering::Relaxed);
}
#[no_mangle]
pub extern "C" fn publish_release(data: &AtomicU32, flag: &AtomicU32) {
    data.store(1, Ordering::Relaxed);
    flag.store(1, Ordering::Release);
}
#[no_mangle]
pub extern "C" fn observe_relaxed(data: &AtomicU32, flag: &AtomicU32) -> u64 {
    let f = flag.load(Ordering::Relaxed);
    let d = data.load(Ordering::Relaxed);
    ((f as u64) << 32) | (d as u64)
}
#[no_mangle]
pub extern "C" fn observe_acquire(data: &AtomicU32, flag: &AtomicU32) -> u64 {
    let f = flag.load(Ordering::Acquire);
    let d = data.load(Ordering::Relaxed);
    ((f as u64) << 32) | (d as u64)
}
#[no_mangle]
pub extern "C" fn store_then_load_relaxed(own: &AtomicU32, peer: &AtomicU32) -> u32 {
    own.store(1, Ordering::Relaxed);
    peer.load(Ordering::Relaxed)
}
#[no_mangle]
pub extern "C" fn store_then_load_fenced(own: &AtomicU32, peer: &AtomicU32) -> u32 {
    own.store(1, Ordering::Relaxed);
    fence(Ordering::SeqCst);
    peer.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn store_then_load_release_acquire(own: &AtomicU32, peer: &AtomicU32) -> u32 {
    own.store(1, Ordering::Release);
    peer.load(Ordering::Acquire)
}
#[no_mangle]
pub extern "C" fn store_then_load_seqcst(own: &AtomicU32, peer: &AtomicU32) -> u32 {
    own.store(1, Ordering::SeqCst);
    peer.load(Ordering::SeqCst)
}
