
pub enum Enum {
    A(u32),
    B(bool),
}

/// ```lean, hermes
/// isValid self := match self with
///   | Enum.A x => x > 10
///   | Enum.B b => b
/// ```
pub struct Wrapper {
    pub inner: Enum,
}
