
pub enum Void {}

/// ```lean, hermes
/// isValid self := nomatch self
/// ```
pub struct Wrapper {
    pub v: Void,
}
