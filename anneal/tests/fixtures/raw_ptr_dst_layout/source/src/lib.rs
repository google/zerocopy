/// ```lean, anneal, unsafe(axiom)
/// axiom spec {T : Type} (val : ConstRawPtr T) :
///   Aeneas.Std.WP.spec (size_of_val_raw val) (fun ret_ => True)
/// ```
#[allow(unused_variables)]
pub const unsafe fn size_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```lean, anneal, unsafe(axiom)
/// axiom spec {T : Type} (val : ConstRawPtr T) :
///   Aeneas.Std.WP.spec (align_of_val_raw val) (fun ret_ => True)
/// ```
#[allow(unused_variables)]
pub const unsafe fn align_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```lean, anneal, spec
/// theorem spec (slice : ConstRawPtr (Slice Std.U8)) :
///   Aeneas.Std.WP.spec (test_slice slice) (fun ret_ => ret_.2.val ∣ ret_.1.val) := by
///   rfl
/// ```
pub fn test_slice(slice: *const [u8]) -> (usize, usize) {
    unsafe { (size_of_val_raw(slice), align_of_val_raw(slice)) }
}
