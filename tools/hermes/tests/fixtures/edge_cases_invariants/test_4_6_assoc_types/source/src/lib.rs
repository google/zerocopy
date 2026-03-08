
pub trait Iter {
    type Item: Default;
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold check_item at *
///   simp_all
/// ```
pub fn check_item<T: Iter>(x: T::Item) -> T::Item {
    x
}

/// @spec
/// isValid self := self.val == T::Item::default()
pub struct Wrapper<T: Iter> where T::Item: PartialEq {
    pub val: T::Item,
}
