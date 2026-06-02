pub struct NamedStruct {
    pub a: u8,
    pub b: u16,
}

/// ```lean, anneal
/// derive_sized sizedness_pass.NamedStruct
/// ```
pub fn foo(_f: &NamedStruct) {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (dummy_force_compile) (fun ret_ => True) := by
///   unfold dummy_force_compile
///   simp_all
/// ```
pub fn dummy_force_compile() {}
