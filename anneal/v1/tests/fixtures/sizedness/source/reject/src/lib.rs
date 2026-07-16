pub struct NamedDst {
    pub a: u8,
    pub b: [u16],
}

/// ```lean, anneal
/// context:
/// derive_sized sizedness_reject.NamedDst
/// ```
pub fn foo(_f: &NamedDst) {}
