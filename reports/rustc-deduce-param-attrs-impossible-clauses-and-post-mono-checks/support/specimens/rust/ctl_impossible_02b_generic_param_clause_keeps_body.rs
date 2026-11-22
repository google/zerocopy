pub fn possible_for_some_t<T>(x: u32) -> u32
where
    T: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
