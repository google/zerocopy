#![allow(unused)]

pub struct DropTracker(pub *mut u32, pub u32);
impl Drop for DropTracker {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { *self.0 = (*self.0) * 10 + self.1; }
    }
}

#[no_mangle]
#[inline(never)]
pub fn frameless_leaf(x: u64) -> u64 {
    x.wrapping_add(42)
}

#[no_mangle]
#[inline(never)]
pub fn passthrough_no_cleanup(f: extern "C-unwind" fn()) {
    f();
}

#[no_mangle]
#[inline(never)]
pub fn nested_cleanups(state: *mut u32, f: extern "C-unwind" fn()) {
    let _d1 = DropTracker(state, 1);
    {
        let _d2 = DropTracker(state, 2);
        f();
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn nounwind_c_boundary(state: *mut u32, f: extern "C-unwind" fn()) {
    let _d1 = DropTracker(state, 9);
    f();
}

#[no_mangle]
#[inline(never)]
pub fn catch_unwind_entry(state: *mut u32, f: extern "C-unwind" fn()) -> i32 {
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        nested_cleanups(state, f);
    }));
    match res {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

#[no_mangle]
#[inline(never)]
pub fn passthrough_with_frame(x: u64, f: extern "C-unwind" fn(u64) -> u64) -> u64 {
    f(x).wrapping_add(x)
}

#[no_mangle]
#[inline(never)]
pub fn simple_nonleaf_call(f: extern "C-unwind" fn() -> u64) -> u64 {
    f().wrapping_add(1)
}
