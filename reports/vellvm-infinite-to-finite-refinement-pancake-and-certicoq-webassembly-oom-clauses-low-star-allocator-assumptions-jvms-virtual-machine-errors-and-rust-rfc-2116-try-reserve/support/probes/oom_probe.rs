// Bounded probe: a global allocator that refuses to exceed a fixed byte budget,
// comparing infallible collection growth with fallible reservation.
// Modes: push | try | overflow | hook | vecmacro
#![feature(alloc_error_hook)]
#![feature(try_reserve_kind)]
use std::alloc::{set_alloc_error_hook, GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

const CAP: usize = 1 << 20; // 1 MiB budget for all live heap bytes

struct Capped;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static REFUSED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Capped {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let prev = LIVE.fetch_add(l.size(), Relaxed);
        if prev + l.size() > CAP {
            LIVE.fetch_sub(l.size(), Relaxed);
            REFUSED.fetch_add(1, Relaxed);
            return std::ptr::null_mut();
        }
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Relaxed);
        unsafe { System.dealloc(p, l) }
    }
    // realloc is not overridden: the default implementation calls alloc,
    // copies, then calls dealloc, so the budget sees old+new during growth.
}

#[global_allocator]
static A: Capped = Capped;

fn main() {
    let mode = std::env::args().nth(1).expect("mode");
    match mode.as_str() {
        "push" => {
            let mut v: Vec<u64> = Vec::new();
            let mut last_cap = 0;
            loop {
                v.push(1);
                if v.capacity() != last_cap {
                    last_cap = v.capacity();
                    eprintln!("cap_bytes={} live={}", last_cap * 8, LIVE.load(Relaxed));
                }
            }
        }
        "try" => {
            let mut v: Vec<u64> = Vec::new();
            loop {
                let want = v.capacity().max(1);
                match v.try_reserve(want) {
                    Ok(()) => {
                        while v.len() < v.capacity() {
                            v.push(1);
                        }
                    }
                    Err(e) => {
                        println!(
                            "try_reserve Err: {e} kind={:?} len_bytes={} live={} refused={}",
                            e.kind(),
                            v.len() * 8,
                            LIVE.load(Relaxed),
                            REFUSED.load(Relaxed)
                        );
                        break;
                    }
                }
            }
            println!("CONTINUED len={}", v.len());
        }
        "overflow" => {
            let mut v: Vec<u64> = Vec::new();
            match v.try_reserve(usize::MAX) {
                Ok(()) => println!("unexpected Ok"),
                Err(e) => println!("try_reserve(usize::MAX) Err: {e} kind={:?}", e.kind()),
            }
            println!("CONTINUED refused={}", REFUSED.load(Relaxed));
        }
        "hook" => {
            set_alloc_error_hook(|l: Layout| panic!("alloc error hook: {} bytes", l.size()));
            let r = std::panic::catch_unwind(|| {
                let mut v: Vec<u64> = Vec::new();
                loop {
                    v.push(1);
                }
            });
            println!("catch_unwind returned is_err={} live={}", r.is_err(), LIVE.load(Relaxed));
            println!("CONTINUED");
        }
        "vecmacro" => {
            let v = vec![0u8; 2 * CAP];
            println!("unexpected len={}", v.len());
        }
        _ => panic!("unknown mode"),
    }
}
