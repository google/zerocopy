pub mod a {
    pub struct S;
}

pub mod b {
    pub struct S;
}

/// ```lean, hermes
/// proof context:
///   unfold func
///   simp_all
/// ```
pub fn func(x: a::S, y: b::S) {}
