use zerocopy::{TryFromBytes, try_transmute_ref};
use zerocopy_derive::*;

#[path = "formats/coco.rs"]
mod coco;

#[derive(IntoBytes, Unaligned, KnownLayout, Immutable)]
#[repr(C)]
struct MinimialViableSource {
    header: [u8; 4],
    trailer: [[u8; 2]]
}

#[unsafe(no_mangle)]
fn codegen_test(source: &MinimialViableSource) -> Option<&coco::Packet> {
    try_transmute_ref!(source).ok()
}