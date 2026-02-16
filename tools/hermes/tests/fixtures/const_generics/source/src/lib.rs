
pub struct Foo<const N: usize> {
    pub data: [u8; N],
}

/// ```lean, hermes
/// isSafe : ...
/// ```
pub unsafe trait Bar<const N: usize> {}
