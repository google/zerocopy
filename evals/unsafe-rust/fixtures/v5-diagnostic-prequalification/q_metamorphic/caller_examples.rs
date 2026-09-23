use metamorphic_target::{delegated_text, local_text};

static PEER_INPUT_A: [u8; 4] = [0, 159, 146, 150];
static PEER_INPUT_B: [u8; 1] = [0];

pub fn example_local() -> &'static str {
    local_text(false)
}

pub fn example_peer_a() -> &'static str {
    // SAFETY: This example supplies the bytes shown here.
    unsafe { delegated_text(&PEER_INPUT_A) }
}

pub fn example_peer_b() -> &'static str {
    // SAFETY: The only byte in this input is at most 0x7f.
    unsafe { delegated_text(&PEER_INPUT_B) }
}
