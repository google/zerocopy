
/// @spec
/// isValid self := self.a.len = N
pub struct ArrayPair<const N: usize> {
    pub a: [u8; N],
    pub b: [u8; N],
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
