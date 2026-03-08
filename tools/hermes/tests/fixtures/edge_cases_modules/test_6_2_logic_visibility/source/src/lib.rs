
pub mod inner {
    pub(crate) fn helper() -> u32 { 42 }
    
    /// @spec
    /// ensures:
///   ///   ///   ret = helper()
    pub fn public_api() -> u32 {
        helper()
    }
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
