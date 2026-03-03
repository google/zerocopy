
pub mod inner {
    /// @spec
    /// isValid self := self.private_field > 0
    pub struct S {
        private_field: u32,
    }
}


/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn dummy_hermes_padding() {}
