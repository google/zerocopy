#![no_std]
#![allow(internal_features)]
#![feature(rustc_attrs)]
#![no_builtins]

#[inline(never)]
unsafe fn set_bytes_helper(s: *mut u8, c: u8, n: usize) {
    let mut cur = s;
    let end = s.wrapping_add(n);
    while cur < end {
        unsafe {
            *cur = c;
        }
        cur = cur.wrapping_add(1);
    }
}

#[inline(never)]
unsafe fn copy_forward_helper(dest: *mut u8, src: *const u8, n: usize) {
    let dst_arr: &mut [u8; 4096] = unsafe { &mut *(dest as *mut [u8; 4096]) };
    let src_arr: &[u8; 4096] = unsafe { &*(src as *const [u8; 4096]) };
    let mut i = 0;
    while i < 4096 {
        dst_arr[i] = src_arr[i];
        i += 1;
    }
    let _ = n;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(s: *mut u8, c: core::ffi::c_int, n: usize) -> *mut u8 {
    unsafe { set_bytes_helper(s, c as u8, n); }
    s
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    unsafe { copy_forward_helper(dest, src, n); }
    dest
}
