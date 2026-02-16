
pub trait Trait {
    type Assoc;
}

pub struct Wrapper<T: Trait> {
    pub val: T::Assoc,
}

/// ```lean, hermes
/// isSafe : ...
/// ```
pub unsafe trait SafeTrait<T: Trait> {
    fn get_assoc(x: T::Assoc) -> T::Assoc;
}
