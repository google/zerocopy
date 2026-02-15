#[cfg(target_os = "windows")]
mod windows_sys; // This file will intentionally not exist

/// ```lean, hermes
/// context
/// theorem demo : True := trivial
/// ```
pub fn demo() {}
