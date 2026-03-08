
pub struct Widths {
    pub a: isize,
    pub b: usize,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn check_widths(x: isize, y: usize) -> (isize, usize) {
    (x, y)
}
