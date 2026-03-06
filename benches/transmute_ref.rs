use zerocopy_derive::*;

#[path = "formats/coco.rs"]
mod format;

#[derive(IntoBytes, KnownLayout, Immutable)]
#[repr(C, align(2))]
struct MinimalViableSource {
    header: [u8; 4],
    trailer: [[u8; 2]],
}

#[unsafe(no_mangle)]
fn bench_transmute_ref(source: &MinimalViableSource) -> &format::LocoPacket {
    zerocopy::transmute_ref!(source)
}
