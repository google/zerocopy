
/// ```lean, hermes
/// proof context:
///   unfold one_tuple
///   simp_all
/// ```
pub fn one_tuple(x: (u32,)) -> (u32,) {
    x
}

pub fn long_tuple() -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0)
}
