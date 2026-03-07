
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
/// proof context:
///   unfold dummy_hermes_padding
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
