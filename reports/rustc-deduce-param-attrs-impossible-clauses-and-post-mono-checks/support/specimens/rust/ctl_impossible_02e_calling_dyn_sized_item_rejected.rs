pub trait MyTrait<T> {}
pub fn impossible_dyn_sized<T>(x: u32) -> u32
where
    dyn MyTrait<T>: Sized,
{
    x.wrapping_mul(3).wrapping_add(1)
}
pub fn caller() -> u32 {
    impossible_dyn_sized::<u8>(1)
}
