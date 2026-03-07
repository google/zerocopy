
/// @spec
/// isValid self := let y := self.x + 1; y > 10
pub struct Wrapper {
    pub x: u32,
}


/// ```lean, hermes
/// proof context:
///   unfold dummy_hermes_padding
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
