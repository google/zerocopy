pub struct NamedStruct {
    pub a: u8,
    pub b: u16,
}

/// ```lean, hermes
/// context:
/// derive_sized sizedness_pass.NamedStruct
/// ```
pub fn foo(_f: &NamedStruct) {}
