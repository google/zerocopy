#![allow(dead_code)]

use std::num::NonZeroU8;

/// Returns the next stage as a nonzero value.
pub fn staged_token(value: u8) -> NonZeroU8 {
    let candidate = peer_stage::next_nonzero(value);
    // SAFETY: `peer_stage::next_nonzero` documents a nonzero result.
    unsafe { NonZeroU8::new_unchecked(candidate) }
}

/// Returns the numeric value of the next stage.
pub fn staged_value(value: u8) -> u8 {
    staged_token(value).get()
}

/// Reports whether the next stage is nonzero.
pub fn staged_is_nonzero(value: u8) -> bool {
    staged_token(value).get() != 0
}

/// Constructs a local stage value.
pub fn local_token(value: u8) -> NonZeroU8 {
    // SAFETY: A stage value is represented by a `u8`.
    unsafe { NonZeroU8::new_unchecked(value) }
}

/// Constructs a local stage value when the input is nonzero.
pub fn checked_token(value: u8) -> Option<NonZeroU8> {
    NonZeroU8::new(value)
}
