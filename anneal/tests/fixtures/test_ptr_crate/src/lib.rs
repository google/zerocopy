/// ```lean, anneal, unsafe(axiom)
/// axiom spec (p : ConstRawPtr Std.U32) :
///   Aeneas.Std.WP.spec (test_ptr p) (fun ret_ => ret_.val = 0)
/// ```
pub fn test_ptr(p: *const u32) -> u32 {
    unsafe { *p }
}
