/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold nested at *
///   simp_all
/// ```
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
