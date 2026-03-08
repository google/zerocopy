
pub union U {
    pub f1: u32,
    pub f2: f32,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold access at *
///   simp_all
/// ```
pub fn access(u: U) -> u32 {
    unsafe { u.f1 }
}
