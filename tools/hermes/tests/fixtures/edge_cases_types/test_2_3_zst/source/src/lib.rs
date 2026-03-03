
pub struct Empty {}

pub struct WrapUnit {
    pub f: (),
}

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn unit_arg(_: ()) {}

pub fn unit_ret() -> () {}
