#![allow(dead_code)]

pub fn advance_marker() -> *const [u8; 0] {
    unsafe { core::ptr::null::<[u8; 0]>().add(1) }
}
