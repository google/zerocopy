/// Returns the element at index `i`.
///
/// ```lean, hermes, unsafe(axiom)
/// requires i < s.len
/// axiom result = s[i]
/// ```
pub unsafe fn get_unchecked(s: &[u32], i: usize) -> u32 {
    *s.get_unchecked(i)
}

fn main() {}
