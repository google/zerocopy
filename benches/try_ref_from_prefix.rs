use zerocopy::TryFromBytes;

#[path = "formats/coco.rs"]
mod coco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8]) -> Option<&coco::Packet> {
    match TryFromBytes::try_ref_from_prefix(source) {
        Ok((packet, _rest)) => Some(packet),
        _ => None,
    }
}
