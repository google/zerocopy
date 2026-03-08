pub enum E {
    A(u32),
    B(u32),
}

/// @spec
/// isValid self := match self.e with | .A x => x > 0 | .B y => y > 10
pub struct S {
    pub e: E,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
