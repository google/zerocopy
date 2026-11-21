#![crate_type = "staticlib"]

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

unsafe extern "C-unwind" {
    fn cpp_throw_nocatch() -> !;
}

struct StaticlibGuard;
impl Drop for StaticlibGuard {
    fn drop(&mut self) {
        let msg = b"[TRACE] staticlib_guard_drop\n";
        unsafe {
            let _ = write(2, msg.as_ptr(), msg.len());
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn rust_staticlib_c_unwind_with_guard() -> ! {
    let _g = StaticlibGuard;
    unsafe { cpp_throw_nocatch() }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn rust_staticlib_c_unwind_no_guard() -> ! {
    unsafe { cpp_throw_nocatch() }
}
