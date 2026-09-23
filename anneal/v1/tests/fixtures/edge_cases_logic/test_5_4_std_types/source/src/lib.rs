
/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn std_types(v: Vec<u32>, s: String) {
    let _ = v.len();
    let _ = s.len();
}
