use zerocopy::try_transmute_ref;
use zerocopy_derive::*;

#[path = "formats/coco.rs"]
mod coco;

#[derive(IntoBytes, Unaligned, KnownLayout, Immutable)]
#[repr(C)]
struct MinimalViableSource {
    header: [u8; 4],
    trailer: [[u8; 2]],
}

#[unsafe(no_mangle)]
fn codegen_test(source: &MinimalViableSource) -> Option<&coco::Packet> {
    try_transmute_ref!(source).ok()
}
