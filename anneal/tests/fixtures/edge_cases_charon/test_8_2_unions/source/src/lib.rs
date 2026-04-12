
pub union U {
    pub f1: u32,
    pub f2: f32,
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn access(u: U) -> u32 {
    unsafe { u.f1 }
}
