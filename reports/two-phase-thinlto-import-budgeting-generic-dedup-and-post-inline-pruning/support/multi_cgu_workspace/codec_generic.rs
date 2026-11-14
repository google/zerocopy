#![crate_name = "codec_generic"]
#![crate_type = "rlib"]

extern crate core_bytes;
extern crate zerocopy_layout;

use core_bytes::{cold_diagnostic_format_dump, generic_mix_lane, generic_read_le};
use zerocopy_layout::validate_and_extract_header;

#[inline]
pub fn decode_frame_generic<const SALT: u64>(words: &[u64]) -> u64 {
    if let Some(hdr) = validate_and_extract_header(words) {
        let w2 = generic_read_le(words, 2, SALT);
        generic_mix_lane::<SALT>(hdr.magic ^ hdr.payload_len, w2)
    } else {
        cold_diagnostic_format_dump(SALT, words.len())
    }
}
