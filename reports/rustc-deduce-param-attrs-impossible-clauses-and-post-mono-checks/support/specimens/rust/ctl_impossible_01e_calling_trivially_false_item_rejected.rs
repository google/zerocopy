#![feature(trivial_bounds)]
pub fn impossible_string_copy(x: u32) -> u32
where
    String: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
pub fn caller() -> u32 {
    impossible_string_copy(1)
}
