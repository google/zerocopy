
pub enum Enum {
    A(u32),
    B(bool),
}

/// ```lean, anneal
/// instance : Anneal.IsValid Wrapper where
///   isValid self := match self.inner with
///    | Enum.A x => x.val > 10
///    | Enum.B b => b = true
/// ```
pub struct Wrapper {
    pub inner: Enum,
}
