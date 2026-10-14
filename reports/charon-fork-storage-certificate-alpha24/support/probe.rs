pub fn choose(b: bool, x: u8, y: u8) -> u8 { if b { x } else { y } }
pub fn update_second(p: &mut (u8, u8), x: u8) { p.1 = x; }
