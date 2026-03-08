/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold swap at *
///   simp_all
/// ```
pub fn swap(a: &mut u32, b: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

pub fn swap_reordered(b: &mut u32, a: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}
