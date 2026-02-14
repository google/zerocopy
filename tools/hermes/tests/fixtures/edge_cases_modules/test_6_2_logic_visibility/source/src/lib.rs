
pub mod inner {
    pub(crate) fn helper() -> u32 { 42 }
    
    /// @spec
    /// ensures result = helper()
    pub fn public_api() -> u32 {
        helper()
    }
}
