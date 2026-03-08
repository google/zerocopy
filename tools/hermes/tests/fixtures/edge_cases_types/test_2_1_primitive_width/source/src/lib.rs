
pub struct Widths {
    pub a: isize,
    pub b: usize,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold check_widths at *
///   simp_all
/// ```
pub fn check_widths(x: isize, y: usize) -> (isize, usize) {
    (x, y)
}
