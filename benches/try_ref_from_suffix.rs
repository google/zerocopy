#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_ref_from_suffix(source: &[u8]) -> Option<&format::CocoPacket> {
    match zerocopy::TryFromBytes::try_ref_from_suffix(source) {
        Ok((_rest, packet)) => Some(packet),
        _ => None,
    }
}
