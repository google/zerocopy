
pub struct Empty {}

pub struct WrapUnit {
    pub f: (),
}

/// ```lean, hermes
/// proof context:
///   unfold unit_arg
///   simp_all
/// ```
pub fn unit_arg(_: ()) {}

pub fn unit_ret() -> () {}
