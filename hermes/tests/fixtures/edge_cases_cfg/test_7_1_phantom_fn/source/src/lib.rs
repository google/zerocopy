#[cfg(target_os = "windows")]
/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn windows_only() {
    panic!("This should not exist on Linux");
}

#[cfg(target_os = "linux")]
pub fn linux_only() {}
