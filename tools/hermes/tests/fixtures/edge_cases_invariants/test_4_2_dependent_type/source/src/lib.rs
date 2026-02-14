
/// @spec
/// isValid self := self.a.len = N
pub struct ArrayPair<const N: usize> {
    pub a: [u8; N],
    pub b: [u8; N],
}
