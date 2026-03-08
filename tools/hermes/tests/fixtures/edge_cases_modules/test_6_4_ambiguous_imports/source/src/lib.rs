pub mod a {
    pub struct S;
}

pub mod b {
    pub struct S;
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold func at *
///   simp_all
/// ```
pub fn func(x: a::S, y: b::S) {}
