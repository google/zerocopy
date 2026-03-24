pub struct NamedDst {
    pub a: u8,
    pub b: [u16],
}

/// ```lean, hermes
/// context:
/// derive_sized sizedness_reject.NamedDst
/// ```
pub fn foo(_f: &NamedDst) {}
