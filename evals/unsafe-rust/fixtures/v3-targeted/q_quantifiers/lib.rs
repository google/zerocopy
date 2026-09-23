#![allow(dead_code)]

/// Transfers control to a site declared unreachable.
pub fn force_unreachable() {
    // SAFETY: This site is assumed to be unreachable.
    unsafe { std::hint::unreachable_unchecked() }
}

/// Delegates a nonzero value to the selected peer implementation.
///
/// # Safety
///
/// `value` must not equal zero.
pub unsafe fn delegated_nonzero(value: u8) -> u8 {
    // SAFETY: The caller guarantees that `value` is nonzero, which is the
    // dependency API's documented caller-side precondition.
    unsafe { peer_unsafe_dep::duplicate_nonzero(value) }
}
