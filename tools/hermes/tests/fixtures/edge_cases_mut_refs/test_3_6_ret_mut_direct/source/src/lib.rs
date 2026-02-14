
pub fn mut_passthrough(x: &mut u32) -> &mut u32 {
    *x += 1;
    x
}
