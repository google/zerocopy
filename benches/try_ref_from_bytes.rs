#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_ref_from_bytes(source: &[u8]) -> Option<&format::CocoPacket> {
    zerocopy::TryFromBytes::try_ref_from_bytes(source).ok()
}
