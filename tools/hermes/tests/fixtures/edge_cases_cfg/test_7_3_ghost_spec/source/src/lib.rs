
#[cfg(target_os = "windows")]
/// @spec
/// ensures:
///   ///   ///   ret = 42
/// ```lean, hermes
/// proof context:
///   unfold windows_only
///   simp_all
/// ```
pub fn windows_only() -> u32 { 42 }

#[cfg(target_os = "linux")]
/// @spec
/// ensures:
///   ///   ///   ret = 100
pub fn linux_only() -> u32 { 100 }
