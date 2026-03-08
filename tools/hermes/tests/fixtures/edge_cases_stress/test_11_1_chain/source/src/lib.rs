
pub mod a {
    pub fn f() -> u32 { 1 }
}
pub mod b {
    pub fn f() -> u32 { crate::a::f() + 1 }
}
pub mod c {
    pub fn f() -> u32 { crate::b::f() + 1 }
}
pub mod d {
    pub fn f() -> u32 { crate::c::f() + 1 }
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
