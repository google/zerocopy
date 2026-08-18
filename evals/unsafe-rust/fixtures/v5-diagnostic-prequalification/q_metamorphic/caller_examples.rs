use metamorphic_target::{delegated_text, local_text};

static INVALID_UTF8: [u8; 4] = [0, 159, 146, 150];
static ASCII_NUL: [u8; 1] = [0];

pub fn example_local() -> &'static str {
    local_text(false)
}

pub fn example_peer_bytes() -> &'static str {
    // SAFETY: This example supplies the bytes shown here.
    unsafe { delegated_text(&INVALID_UTF8) }
}

pub fn example_peer_ascii() -> &'static str {
    // SAFETY: The only byte in this input is at most 0x7f.
    unsafe { delegated_text(&ASCII_NUL) }
}
