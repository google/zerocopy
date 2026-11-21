//! Allocation-failure specimen. The global allocator refuses every request of at least 2^40
//! bytes by returning a null pointer, which makes the failure deterministic.
//!
//! The first command-line argument selects the operation:
//!
//! * `box`          `Box::<[u8; 1 << 41]>::new_uninit()`   (infallible API)
//! * `vec`          `Vec::<u8>::with_capacity(1 << 41)`    (infallible API)
//! * `try_reserve`  `Vec::<u8>::try_reserve_exact(1 << 41)` (fallible API; exits normally)
//! * `raw`          `std::alloc::alloc` with a 2^41-byte layout (returns null; exits normally)
//! * `overflow`     `Vec::<u8>::with_capacity(usize::MAX)` (capacity overflow: a panic, and the
//!                  allocator is never called)

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

const REFUSE_FROM: usize = 1 << 40;
const BIG: usize = 1 << 41;

static REFUSED: AtomicUsize = AtomicUsize::new(0);

struct Refusing;

unsafe impl GlobalAlloc for Refusing {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() >= REFUSE_FROM {
            REFUSED.fetch_add(1, SeqCst);
            return std::ptr::null_mut();
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Refusing = Refusing;

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "box" => {
            let b = Box::<[u8; BIG]>::new_uninit();
            std::hint::black_box(b);
            println!("unreachable: box returned");
        }
        "vec" => {
            let v = Vec::<u8>::with_capacity(std::hint::black_box(BIG));
            std::hint::black_box(v);
            println!("unreachable: vec returned");
        }
        "try_reserve" => {
            let mut v = Vec::<u8>::new();
            let r = v.try_reserve_exact(std::hint::black_box(BIG));
            println!("try_reserve_exact is_err={} refused_calls={}", r.is_err(), REFUSED.load(SeqCst));
        }
        "raw" => {
            let p = unsafe { std::alloc::alloc(Layout::from_size_align(BIG, 1).unwrap()) };
            println!("raw alloc is_null={} refused_calls={}", p.is_null(), REFUSED.load(SeqCst));
        }
        "overflow" => {
            let v = Vec::<u8>::with_capacity(std::hint::black_box(usize::MAX));
            std::hint::black_box(v);
            println!("unreachable: vec returned");
        }
        other => {
            eprintln!("unknown mode {other:?}");
            std::process::exit(2);
        }
    }
}
