
#[cfg(target_os = "windows")]
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (windows_only) (fun ret_ => ret_.val = 42) := by
///   sorry
/// ```
pub fn windows_only() -> u32 { 42 }

#[cfg(target_os = "linux")]
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (linux_only) (fun ret_ => ret_.val = 100) := by
///   sorry
/// ```
pub fn linux_only() -> u32 { 100 }
