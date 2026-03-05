#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_ref_from_bytes(source: &[u8]) -> Option<&format::LocoPacket> {
    zerocopy::FromBytes::ref_from_bytes(source).ok()
}
