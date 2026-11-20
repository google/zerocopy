// Auto-trait change detected by the 2021 migration lint (compile with --edition 2018).
use std::thread;
pub struct Pointer(*mut i32);
unsafe impl Send for Pointer {}
pub fn f() {
    let mut f = 10;
    let fptr = Pointer(&mut f as *mut i32);
    let _ = thread::spawn(move || unsafe { *fptr.0 = 20; });
}
