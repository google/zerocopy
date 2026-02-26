#[cfg_attr(unix, path = "sys_unix.rs")]
mod sys; // This triggers the warning

/// ```lean, hermes
/// context
/// theorem my_demo : True := trivial
/// ```
pub fn demo() {} // Included so the overall verification command succeeds
