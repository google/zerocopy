use std::ptr::NonNull;

pub struct Pointers {
    pub a: *const u8,
    pub b: *mut u8,
    pub c: NonNull<u8>,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn ptr_arg(p: *const u8) -> *const u8 {
    p
}
