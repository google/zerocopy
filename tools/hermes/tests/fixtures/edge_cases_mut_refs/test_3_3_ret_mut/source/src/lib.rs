
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold pop at *
///   simp_all
/// ```
pub fn pop(v: &mut Vec<u32>) -> Option<u32> {
    v.pop()
}

pub fn inc(x: &mut u32) {
    *x += 1;
}
