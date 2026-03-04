
pub mod inner {
    pub(crate) fn helper() -> u32 { 42 }
    
    /// @spec
    /// ensures ret = helper()
    pub fn public_api() -> u32 {
        helper()
    }
}


/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn dummy_hermes_padding() {}
