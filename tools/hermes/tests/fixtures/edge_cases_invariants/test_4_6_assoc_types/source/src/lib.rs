
pub trait Iter {
    type Item: Default;
}

/// ```hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn check_item<T: Iter>(x: T::Item) -> T::Item {
    x
}

/// ```hermes
/// isValid self := self.val == T::Item::default()
/// ```
pub struct Wrapper<T: Iter> where T::Item: PartialEq {
    pub val: T::Item,
}
