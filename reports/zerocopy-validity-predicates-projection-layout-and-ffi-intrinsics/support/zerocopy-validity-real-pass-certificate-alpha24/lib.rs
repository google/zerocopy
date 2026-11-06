pub mod util;
pub fn bool_api(byte: u8) -> bool { util::validity::bool_encoding(byte) }
pub fn nonzero_api(n: usize) -> bool { util::validity::nonzero_encoding(n) }
pub fn byte_api(bytes: &[u8], index: usize) -> u8 { util::validity::read_byte(bytes, index) }
