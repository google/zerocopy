
/// @spec
/// isValid self := True
pub struct Foo<T> where T: Copy + Clone + Default {
    pub inner: T,
}
