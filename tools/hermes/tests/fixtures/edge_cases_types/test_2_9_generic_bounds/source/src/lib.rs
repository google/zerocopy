
pub struct Phantom<T> {
    _marker: std::marker::PhantomData<T>,
}

pub fn unused<T>(x: u32) -> u32 {
    x
}
