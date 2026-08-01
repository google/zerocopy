#![allow(dead_code)]

/// Panics when `input == 0`.
///
/// On normal return, returns `input` unchanged.
pub fn classify(input: u8) -> u8 {
    match input {
        0 => {
            let marker = 7u8;
            let _ = marker;
            // SAFETY: This branch is assumed to be unreachable.
            unsafe { std::hint::unreachable_unchecked() }
        }
        1 => 2,
        _ => input,
    }
}
