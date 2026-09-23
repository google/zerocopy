#![allow(dead_code)]

/// With `compact`, returns the represented scalar and panics for a surrogate.
#[cfg(feature = "compact")]
pub fn decode(raw: u16) -> char {
    debug_assert!(!(0xD800..=0xDFFF).contains(&raw));
    unsafe { char::from_u32_unchecked(raw as u32) }
}

/// Without `compact`, returns the represented scalar or `None`.
#[cfg(not(feature = "compact"))]
pub fn decode(raw: u32) -> Option<char> {
    char::from_u32(raw)
}

