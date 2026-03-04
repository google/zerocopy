#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8]) -> Option<&format::LocoPacket> {
    match zerocopy::FromBytes::ref_from_prefix(source) {
        Ok((packet, _rest)) => Some(packet),
        _ => None,
    }
}
