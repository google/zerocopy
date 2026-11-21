//! Compile-fail borrowck witnesses vs native `extern "C"` abort execution.

#[allow(dead_code)]
#[cfg(case = "borrowck_guard_mutates_scrutinee")]
fn main() {
    let mut x = Some(0u32);
    let _ = match x {
        None => 0,
        Some(_) if { x = None; false } => 1,
        Some(_) => 2,
    };
}

#[allow(dead_code)]
#[cfg(case = "borrowck_empty_match_uninit_void")]
fn main() {
    enum Void {}
    let x: Void;
    match x {}
}

#[cfg(case = "native_extern_c_unwind_aborts_after_drop")]
mod native_abort {
    use std::sync::atomic::{AtomicU32, Ordering};

    static DROPPED: AtomicU32 = AtomicU32::new(0);

    struct Marker;
    impl Drop for Marker {
        fn drop(&mut self) {
            DROPPED.fetch_add(1, Ordering::SeqCst);
            eprintln!("NATIVE_CLEANUP_DROP_EXECUTED={}", DROPPED.load(Ordering::SeqCst));
        }
    }

    #[inline(never)]
    fn do_panic() {
        panic!("boom across extern C");
    }

    #[inline(never)]
    extern "C" fn c_boundary() {
        let _m = Marker;
        do_panic();
    }

    pub fn run() {
        c_boundary();
    }
}

#[cfg(case = "native_extern_c_unwind_aborts_after_drop")]
fn main() {
    native_abort::run();
}
