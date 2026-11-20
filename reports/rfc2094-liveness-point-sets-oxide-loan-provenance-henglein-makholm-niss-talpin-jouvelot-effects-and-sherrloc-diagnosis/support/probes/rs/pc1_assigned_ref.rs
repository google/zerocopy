// RFC 2094 problem case #1: a reference assigned into a variable.
fn capitalize(s: &mut [char]) { for c in s.iter_mut() { *c = c.to_ascii_uppercase(); } }
pub fn bar() {
    let mut data = vec!['a', 'b', 'c'];
    let slice = &mut data[..];
    capitalize(slice);
    data.push('d');
    data.push('e');
    data.push('f');
}
