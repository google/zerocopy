pub struct Arrays {
    pub empty: [u8; 0],
    pub singleton: [u8; 1],
    pub large: [u8; 1024],
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold slice_of_slices at *
///   simp_all
/// ```
pub fn slice_of_slices(x: &[&[u8]]) -> usize {
    x.len()
}
