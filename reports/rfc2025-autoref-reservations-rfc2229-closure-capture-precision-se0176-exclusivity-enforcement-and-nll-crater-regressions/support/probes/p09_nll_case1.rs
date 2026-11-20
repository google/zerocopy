// RFC 2094 problem case #1. Expect: accepted under NLL.
fn capitalize(_data: &mut [char]) {}
pub fn bar() {
    let mut data = vec!['a', 'b', 'c'];
    let slice = &mut data[..];
    capitalize(slice);
    data.push('d');
    data.push('e');
    data.push('f');
}
