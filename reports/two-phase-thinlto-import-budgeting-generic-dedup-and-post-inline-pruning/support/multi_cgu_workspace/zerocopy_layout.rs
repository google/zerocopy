#![crate_name = "zerocopy_layout"]
#![crate_type = "rlib"]

extern crate core_bytes;
use core_bytes::{generic_mix_lane, generic_read_le};

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PacketHeader {
    pub magic: u64,
    pub payload_len: u64,
}

#[inline]
pub fn validate_and_extract_header(words: &[u64]) -> Option<PacketHeader> {
    if words.len() < 2 {
        return None;
    }
    let m = generic_read_le(words, 0, 0);
    let l = generic_read_le(words, 1, 0);
    Some(PacketHeader {
        magic: generic_mix_lane::<0x517C_C1B7_2722_0A95>(m, 1),
        payload_len: l,
    })
}
