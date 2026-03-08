
pub mod inner {
    /// @spec
    /// isValid self := self.private_field > 0
    pub struct S {
        private_field: u32,
    }
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
