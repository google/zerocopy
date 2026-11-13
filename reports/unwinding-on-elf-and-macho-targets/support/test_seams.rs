use std::sync::atomic::{AtomicU32, Ordering};

pub static DROP_LOG: AtomicU32 = AtomicU32::new(0);

pub struct Guard(pub u32);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        let prev = DROP_LOG.load(Ordering::SeqCst);
        DROP_LOG.store(prev * 10 + self.0, Ordering::SeqCst);
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C-unwind" fn rust_inner_with_drop(f: extern "C-unwind" fn()) {
    let _g = Guard(1);
    f();
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn c_boundary_no_drop(f: extern "C-unwind" fn()) {
    rust_inner_with_drop(f);
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn c_boundary_with_drop(f: extern "C-unwind" fn()) {
    let _g = Guard(2);
    rust_inner_with_drop(f);
}

#[no_mangle]
pub extern "C" fn get_drop_log() -> u32 {
    DROP_LOG.load(Ordering::SeqCst)
}

#[no_mangle]
#[inline(never)]
pub extern "C-unwind" fn rust_c_unwind_nested(f: extern "C-unwind" fn()) {
    let _g1 = Guard(3);
    {
        let _g2 = Guard(4);
        rust_inner_with_drop(f);
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_catch_foreign(f: extern "C-unwind" fn()) -> i32 {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rust_inner_with_drop(f);
    })) {
        Ok(()) => 0,
        Err(_) => 1,
    }
}
