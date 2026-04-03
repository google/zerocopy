
#[cfg(target_os = "windows")]
/// ```lean, hermes
/// ensures:
///   ret = 42
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn windows_only() -> u32 { 42 }

#[cfg(target_os = "linux")]
/// ```hermes
/// ensures:
///   ret = 100
/// ```
pub fn linux_only() -> u32 { 100 }
