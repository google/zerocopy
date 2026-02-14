
pub fn nested_mut(x: &mut (u32, u32)) {
    x.0 += 1;
    x.1 += 1;
}
