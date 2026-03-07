#[cfg(target_os = "windows")]
/// ```lean, hermes
/// proof context:
///   unfold windows_only
///   simp_all
/// ```
pub fn windows_only() {
    panic!("This should not exist on Linux");
}

#[cfg(target_os = "linux")]
pub fn linux_only() {}
