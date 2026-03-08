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
///   have h_foo : True := True.intro
/// ```
pub fn func(x: a::S, y: b::S) {}
