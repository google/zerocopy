#![allow(dead_code)]

/// Has no additional safety requirements.
pub unsafe fn acknowledge() {}

/// Stores `value` at `dst` without reading or dropping the old `u16`.
///
/// # Safety
///
/// `dst` must be properly aligned and valid for writes of one `u16`.
pub unsafe fn store_word(dst: *mut u16, value: u16) {
    // SAFETY: The caller guarantees exactly the preconditions of `ptr::write`.
    unsafe { std::ptr::write(dst, value) }
}

/// Copies the byte at `src` to `dst` and preserves the source byte.
///
/// # Safety
///
/// `src` must be properly aligned, valid for reads of one `u8`, and point to an
/// initialized `u8`; `dst` must be properly aligned and valid for writes of one
/// `u8`; and the two one-byte regions must not overlap.
pub unsafe fn copy_byte(src: *const u8, dst: *mut u8) {
    // SAFETY: The caller guarantees every precondition for a one-element copy.
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) }
}

/// Reads and returns the initialized `u32` at `src` without changing it.
///
/// # Safety
///
/// `src` must be properly aligned, valid for reads of one `u32`, and point to
/// a properly initialized `u32`.
pub unsafe fn load_word(src: *const u32) -> u32 {
    // SAFETY: The caller guarantees exactly the preconditions of `ptr::read`.
    unsafe { std::ptr::read(src) }
}
