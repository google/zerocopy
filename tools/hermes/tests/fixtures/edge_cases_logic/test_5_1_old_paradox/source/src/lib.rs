
/// @spec
/// ensures:
///   ret = x
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn foo(x: u32) -> u32 {
    x
}
