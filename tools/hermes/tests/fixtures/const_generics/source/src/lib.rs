
pub struct Foo<const N: usize> {
    pub data: [u8; N],
}

/// ```lean, hermes
/// isSafe Self := fun _ => True
/// ```
pub unsafe trait Bar<const N: usize> {}
