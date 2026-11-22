pub struct Big(pub [u8; 256]);
#[inline(never)]
pub fn sink(b: Big) -> u8 {
    b.0[0]
}
pub fn pass_by_move(b: Big) -> u8 {
    sink(b)
}
