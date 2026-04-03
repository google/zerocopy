
pub union MyUnion {
    pub f1: u32,
    pub f2: f32,
}

/// ```lean, hermes
/// isValid self := true
/// ```
pub struct Wrapper {
    pub u: MyUnion,
}
