//! A safe observation of one configured Rust compilation's layout.
//! This neither reads padding nor observes pointer provenance/representation.
use std::mem::{align_of, offset_of, size_of};

#[repr(C)]
struct Packet {
    tag: u8,
    ptr: *const u8,
}

fn main() {
    println!(
        "{{\"pointer_bytes\":{},\"pointer_alignment\":{},\"tag_offset\":{},\"pointer_offset\":{},\"packet_size\":{},\"packet_alignment\":{},\"little_endian\":{}}}",
        size_of::<*const u8>(),
        align_of::<*const u8>(),
        offset_of!(Packet, tag),
        offset_of!(Packet, ptr),
        size_of::<Packet>(),
        align_of::<Packet>(),
        cfg!(target_endian = "little"),
    );
}
