/// ```lean, hermes, unsafe(axiom)
/// ensures:
///   ///   ///   ret.val = 0
/// ```
pub fn test_ptr(p: *const u32) -> u32 {
    unsafe { *p }
}
