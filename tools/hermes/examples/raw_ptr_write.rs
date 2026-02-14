/// Writes to a pointer.
///
/// ```lean, hermes, unsafe(axiom)
/// requires ptr.val ≠ 0 -- non-null
/// axiom *ptr = val
/// ```
pub unsafe fn raw_write(ptr: *mut u32, val: u32) {
    *ptr = val;
}

fn main() {}
