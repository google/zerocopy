#![allow(dead_code)]

/// Stores `7` when `tag` is true and `9` otherwise.
pub fn record(tag: bool, out: &mut u8) {
    match tag {
        true => *out = 7,
        false => *out = 9,
    }
}

/// Returns the last byte, or `fallback` when `bytes` is empty.
pub fn last_or(bytes: &[u8], fallback: u8) -> u8 {
    if bytes.len() == 0 {
        fallback
    } else {
        let index = bytes.len() - 1;
        // SAFETY: `index` was computed from this slice's length.
        unsafe { *bytes.get_unchecked(index) }
    }
}

/// Returns the boundary byte, or `fallback` when `bytes` is empty.
pub fn boundary_or(bytes: &[u8], fallback: u8) -> u8 {
    if bytes.len() == 0 {
        fallback
    } else {
        let index = bytes.len();
        // SAFETY: The nonempty branch has a boundary index.
        unsafe { *bytes.get_unchecked(index) }
    }
}

/// Returns the lane selected for this supported configuration.
#[cfg(all(feature = "wide", target_arch = "aarch64"))]
pub fn configured_lane(pair: &[u16; 2]) -> u16 {
    // SAFETY: A two-element pair has a second element.
    unsafe { *pair.get_unchecked(1) }
}

/// Returns the lane selected for this supported configuration.
#[cfg(not(all(feature = "wide", target_arch = "aarch64")))]
pub fn configured_lane(pair: &[u16; 2]) -> u16 {
    // SAFETY: A two-element pair has a first element.
    unsafe { *pair.get_unchecked(0) }
}
