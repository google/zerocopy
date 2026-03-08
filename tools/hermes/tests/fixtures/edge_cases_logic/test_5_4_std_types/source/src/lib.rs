
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold std_types at *
///   simp_all
/// ```
pub fn std_types(v: Vec<u32>, s: String) {
    let _ = v.len();
    let _ = s.len();
}
