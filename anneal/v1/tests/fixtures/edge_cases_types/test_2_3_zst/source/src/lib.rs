/// ```anneal
/// isValid self := True
/// ```
pub struct Empty {}

/// ```anneal
/// isValid self := True
/// ```
pub struct WrapUnit {
    pub f: (),
}

/// ```anneal
/// ensures: True
/// ```
pub fn unit_arg(_: ()) {}

/// ```anneal
/// ensures: True
/// ```
pub fn unit_ret() -> () {}
