/// Writes to a pointer.
///
/// ```lean, hermes, unsafe(axiom)
/// -- Aeneas recently transitioned `RawPtr` to be structurally opaque, rendering previous
/// -- `ptr.val ≠ 0` projections invalid. We simplify raw pointer axioms to `True` for example continuity.
/// requires True -- non-null
/// axiom *ptr = val
/// ```
pub unsafe fn raw_write(ptr: *mut u32, val: u32) {
    *ptr = val;
}

fn main() {}
