use std::mem::{align_of, offset_of, size_of};

#[repr(C)]
struct PacketRecord {
    word: usize,
    flags: [bool; 4],
    header: [u8; 2],
}

#[unsafe(no_mangle)]
pub extern "C" fn aggregate_layout(field: u32) -> u32 {
    match field {
        0 => size_of::<PacketRecord>() as u32,
        1 => align_of::<PacketRecord>() as u32,
        2 => offset_of!(PacketRecord, flags) as u32,
        3 => offset_of!(PacketRecord, header) as u32,
        4 => size_of::<bool>() as u32,
        5 => align_of::<bool>() as u32,
        6 => size_of::<[bool; 4]>() as u32,
        7 => align_of::<[bool; 4]>() as u32,
        8 => size_of::<[u8; 2]>() as u32,
        9 => align_of::<[u8; 2]>() as u32,
        10 => size_of::<usize>() as u32,
        11 => align_of::<usize>() as u32,
        _ => 99,
    }
}

fn main() {
    println!("aggregate={:?}", (0..12).map(|field| aggregate_layout(field)).collect::<Vec<_>>());
}
