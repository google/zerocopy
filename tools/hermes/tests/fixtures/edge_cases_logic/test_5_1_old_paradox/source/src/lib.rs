
/// @spec
/// ensures:
///   ret = x
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold foo at *
///   try simp_all
/// ```
pub fn foo(x: u32) -> u32 {
    x
}
