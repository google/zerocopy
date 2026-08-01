#![allow(dead_code)]

/// Panics when `input == 0`.
///
/// On normal return, returns `input`.
pub fn classify(input: u8) -> u8 {
    match input {
        0 => unsafe { core::hint::unreachable_unchecked() },
        1 => 2,
        _ => input,
    }
}
