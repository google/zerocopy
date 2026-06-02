#[cfg(target_os = "windows")]
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (windows_only) (fun ret_ => True) := by
///   sorry
/// ```
pub fn windows_only() {
    panic!("This should not exist on Linux");
}

#[cfg(target_os = "linux")]
pub fn linux_only() {}
