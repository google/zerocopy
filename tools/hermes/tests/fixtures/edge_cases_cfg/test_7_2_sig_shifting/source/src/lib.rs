pub struct Config {
    #[cfg(target_os = "linux")]
    pub fd: i32,
    #[cfg(target_os = "windows")]
    pub handle: i32,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
