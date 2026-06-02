pub struct Arrays {
    pub empty: [u8; 0],
    pub singleton: [u8; 1],
    pub large: [u8; 1024],
}

/// ```lean, anneal, spec
/// theorem spec (x : _) :
///   Aeneas.Std.WP.spec (slice_of_slices x) (fun ret_ => True) := by
///   sorry
/// ```
pub fn slice_of_slices(x: &[&[u8]]) -> usize {
    x.len()
}
