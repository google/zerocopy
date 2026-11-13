#![allow(unused)]

#[no_mangle]
#[inline(never)]
pub fn redzone_leaf(a: u64, b: u64, c: u64, d: u64) -> u64 {
    let mut arr = [a, b, c, d, a ^ b, c ^ d, a.wrapping_add(c), b.wrapping_add(d)];
    std::hint::black_box(&mut arr[0]);
    arr[0].wrapping_add(arr[7])
}

#[no_mangle]
#[inline(never)]
pub fn frame_3k(x: u8) -> u8 {
    let mut buf = [x; 3072];
    std::hint::black_box(&mut buf);
    buf[1024]
}

#[no_mangle]
#[inline(never)]
pub fn frame_8k(x: u8) -> u8 {
    let mut buf = [x; 8192];
    std::hint::black_box(&mut buf);
    buf[4096]
}

#[no_mangle]
#[inline(never)]
pub fn frame_70k(x: u8) -> u8 {
    let mut buf = [x; 71680];
    std::hint::black_box(&mut buf);
    buf[65536]
}

#[repr(align(64))]
pub struct Align64(pub [u8; 64]);

#[no_mangle]
#[inline(never)]
pub fn overaligned_frame(x: u8, f: extern "C" fn(*mut Align64)) -> u8 {
    let mut a = Align64([x; 64]);
    f(&mut a);
    a.0[0]
}
