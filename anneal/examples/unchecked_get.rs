/// Returns the element at index `i`.
///
/// ```lean, anneal, unsafe(axiom)
/// axiom spec (s : Slice Std.U32) (i : Std.Usize) (h_bound : i.val < s.len) :
///   Aeneas.Std.WP.spec (get_unchecked s i) (fun ret_ => ret_ = s[i.val])
/// ```
pub unsafe fn get_unchecked(s: &[u32], i: usize) -> u32 {
    unsafe { *s.get_unchecked(i) }
}

fn main() {}
