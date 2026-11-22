#![allow(unused)]

unsafe extern "C" {
    fn ext_c(x: u32) -> u32;
    fn ext_abort() -> !;
}

unsafe extern "C-unwind" {
    fn ext_c_unwind(x: u32) -> u32;
}

pub fn call_ext_c(x: u32) -> u32 {
    unsafe { ext_c(x) }
}

pub fn call_ext_c_unwind(x: u32) -> u32 {
    unsafe { ext_c_unwind(x) }
}

pub fn call_ext_abort() -> ! {
    unsafe { ext_abort() }
}

pub extern "C" fn rust_ext_c(x: u32) -> u32 {
    if x == 0 {
        panic!("boom");
    }
    x
}

pub extern "C-unwind" fn rust_ext_c_unwind(x: u32) -> u32 {
    if x == 0 {
        panic!("boom");
    }
    x
}

pub fn rust_never() -> ! {
    loop {}
}
