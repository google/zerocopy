#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn bench_ref_from_prefix_with_elems(source: &[u8], count: usize) -> Option<&format::LocoPacket> {
    match zerocopy::FromBytes::ref_from_prefix_with_elems(source, count) {
        Ok((packet, _rest)) => Some(packet),
        _ => None,
    }
}
