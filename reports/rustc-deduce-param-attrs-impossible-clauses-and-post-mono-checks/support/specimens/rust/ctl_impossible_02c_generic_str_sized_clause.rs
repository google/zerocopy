#![feature(trivial_bounds)]
pub fn impossible_str_sized<T>(x: u32) -> u32
where
    str: Sized,
{
    x.wrapping_mul(3).wrapping_add(1)
}
