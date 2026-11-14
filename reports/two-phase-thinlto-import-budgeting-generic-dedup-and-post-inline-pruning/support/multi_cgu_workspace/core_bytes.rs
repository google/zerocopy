#![crate_name = "core_bytes"]
#![crate_type = "rlib"]

#[inline]
pub fn generic_read_le<T: Copy>(slice: &[T], idx: usize, default: T) -> T {
    if idx < slice.len() {
        slice[idx]
    } else {
        default
    }
}

#[inline]
pub fn generic_mix_lane<const K: u64>(x: u64, y: u64) -> u64 {
    x.wrapping_mul(K).wrapping_add(y.rotate_left(13))
}

#[inline(never)]
pub fn cold_diagnostic_format_dump(code: u64, len: usize) -> u64 {
    let mut h = code ^ (len as u64);
    for step in 0..32 {
        h = h.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(step);
    }
    h
}
