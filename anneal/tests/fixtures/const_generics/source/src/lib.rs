
pub struct Foo<const N: usize> {
    pub data: [u8; N],
}

/// ```lean, anneal
/// def isSafe (Self : Type) (N : Std.Usize) : Prop := True
/// ```
pub unsafe trait Bar<const N: usize> {}
