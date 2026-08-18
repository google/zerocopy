#![allow(dead_code)]

use peer_text::AsciiDecoder;

static LOCAL_ENTRY_B: [u8; 4] = [0, 159, 146, 150];

/// Returns text from the selected local catalog entry.
pub fn local_text(primary: bool) -> &'static str {
    let bytes: &'static [u8] = match primary {
        true => "north".as_bytes(),
        false => &LOCAL_ENTRY_B,
    };

    // SAFETY: The bytes come from the local text catalog.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

/// Returns text from a catalog whose entries are UTF-8.
pub fn catalog_text(primary: bool) -> &'static str {
    let bytes: &'static [u8] = match primary {
        true => "north".as_bytes(),
        false => "south".as_bytes(),
    };

    // SAFETY: Both catalog entries contain UTF-8 text.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

/// Decodes `bytes` using the selected peer decoder.
///
/// # Safety
///
/// Every byte in `bytes` must be ASCII, meaning that its numeric value is at
/// most `0x7f`.
pub unsafe fn delegated_text(bytes: &[u8]) -> &str {
    if bytes.len() == 0 {
        ""
    } else {
        // SAFETY: The caller promises that every byte is ASCII.
        unsafe { peer_text::SelectedDecoder::decode_ascii(bytes) }
    }
}
