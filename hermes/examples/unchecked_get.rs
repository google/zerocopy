/// Returns the element at index `i`.
///
/// ```lean, hermes, unsafe(axiom)
/// requires (h_bound): i < s.len
/// ensures: ret = s[i]'h_bound
/// ```
pub unsafe fn get_unchecked(s: &[u32], i: usize) -> u32 {
    unsafe { *s.get_unchecked(i) }
}

fn main() {}
