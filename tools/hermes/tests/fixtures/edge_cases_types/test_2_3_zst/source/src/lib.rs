
pub struct Empty {}

pub struct WrapUnit {
    pub f: (),
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold unit_arg at *
///   simp_all
/// ```
pub fn unit_arg(_: ()) {}

pub fn unit_ret() -> () {}
