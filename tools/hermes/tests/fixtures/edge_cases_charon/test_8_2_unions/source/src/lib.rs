
pub union U {
    pub f1: u32,
    pub f2: f32,
}

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn access(u: U) -> u32 {
    unsafe { u.f1 }
}
