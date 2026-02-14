
#[cfg(target_os = "windows")]
/// @spec
/// ensures result = 42
pub fn windows_only() -> u32 { 42 }

#[cfg(target_os = "linux")]
/// @spec
/// ensures result = 100
pub fn linux_only() -> u32 { 100 }
