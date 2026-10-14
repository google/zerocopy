// A complete small safe API over one unsafe representation operation.
pub fn checked_bool(byte: u8) -> Option<bool> {
    if byte < 2 {
        // Rust bool and u8 have size one; exactly 0 and 1 are valid bool bytes.
        Some(unsafe { core::mem::transmute::<u8, bool>(byte) })
    } else {
        None
    }
}
