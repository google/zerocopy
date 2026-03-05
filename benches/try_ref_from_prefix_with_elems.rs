#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_try_ref_from_prefix_with_elems(
    source: &[u8],
    count: usize,
) -> Option<&format::CocoPacket> {
    match zerocopy::TryFromBytes::try_ref_from_prefix_with_elems(source, count) {
        Ok((packet, _rest)) => Some(packet),
        _ => None,
    }
}
