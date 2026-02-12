use zerocopy::{TryFromBytes, try_transmute_ref};
use zerocopy_derive::*;

#[path = "formats/coco.rs"]
mod coco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8]) -> Option<&coco::Packet> {
    TryFromBytes::try_ref_from_bytes(source).ok()
}