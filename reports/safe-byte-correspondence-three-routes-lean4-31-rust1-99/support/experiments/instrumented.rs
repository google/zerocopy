fn scale(v: u8) -> u8 { v.wrapping_mul(5) }
pub fn subject(x: u8) -> u8 {
    let a = x.wrapping_add(3);
    let b = scale(a);
    b.wrapping_add(7)
}
pub fn subject_trace(x: u8) -> (u8,u8,u8) {
    let a = x.wrapping_add(3);
    let b = scale(a);
    (a,b,b.wrapping_add(7))
}
