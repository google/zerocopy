pub const EMOJI: &str = "😀"; pub fn after_emoji(x: u32) -> u32 { x + 1 }
pub const COMBINING: &str = "é"; pub fn after_combining(x: u32) -> u32 { x + 2 }
pub fn unicode_body() -> usize { "😀é".len() }
