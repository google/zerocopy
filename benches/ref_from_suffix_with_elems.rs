#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8], count: usize) -> Option<&format::LocoPacket> {
    match zerocopy::FromBytes::ref_from_suffix_with_elems(source, count) {
        Ok((_rest, packet)) => Some(packet),
        _ => None,
    }
}
