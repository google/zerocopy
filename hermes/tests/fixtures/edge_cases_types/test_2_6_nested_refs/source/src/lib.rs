/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
