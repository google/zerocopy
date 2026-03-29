/// ```hermes
/// isValid self := True
/// ```
pub struct Empty {}

/// ```hermes
/// isValid self := True
/// ```
pub struct WrapUnit {
    pub f: (),
}

/// ```hermes
/// ensures: True
/// ```
pub fn unit_arg(_: ()) {}

/// ```hermes
/// ensures: True
/// ```
pub fn unit_ret() -> () {}
