#![allow(dead_code)]

pub fn last(bytes: &[u8]) -> Option<&u8> {
    if bytes.len() == 0 {
        None
    } else {
        let index = bytes.len() - 1;
        // SAFETY: The returned reference cannot outlive `bytes`.
        Some(unsafe { bytes.get_unchecked(index) })
    }
}
