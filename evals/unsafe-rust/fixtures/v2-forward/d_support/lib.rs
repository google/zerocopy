#![allow(dead_code)]

#[cfg(not(feature = "fast"))]
pub fn first(bytes: &[u8]) -> Option<u8> {
    bytes.first().copied()
}

#[cfg(feature = "fast")]
pub fn first(bytes: &[u8]) -> Option<u8> {
    if bytes.is_empty() {
        None
    } else {
        Some(unsafe { *bytes.get_unchecked(0) })
    }
}
