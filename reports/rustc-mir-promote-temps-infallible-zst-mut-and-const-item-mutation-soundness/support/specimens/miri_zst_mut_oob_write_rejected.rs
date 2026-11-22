#![allow(unused_mut)]

fn main() {
    let a: &'static mut [u32] = &mut [];
    unsafe {
        *a.as_mut_ptr() = 1;
    }
}
