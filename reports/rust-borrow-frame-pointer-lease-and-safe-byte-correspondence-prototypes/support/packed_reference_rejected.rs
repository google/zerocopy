#[repr(C, packed)]
struct Packed { byte: u8, word: u32 }
fn project(p: &Packed) -> &u32 { &p.word }
fn main() {}
