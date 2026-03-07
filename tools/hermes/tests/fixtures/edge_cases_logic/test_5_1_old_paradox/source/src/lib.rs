
/// @spec
/// ensures:
///   ret = x
/// ```lean, hermes
/// proof context:
///   unfold foo
///   try simp_all
/// ```
pub fn foo(x: u32) -> u32 {
    x
}
