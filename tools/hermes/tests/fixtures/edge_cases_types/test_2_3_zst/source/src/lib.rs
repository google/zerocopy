
pub struct Empty {}

pub struct WrapUnit {
    pub f: (),
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn unit_arg(_: ()) {}

pub fn unit_ret() -> () {}
