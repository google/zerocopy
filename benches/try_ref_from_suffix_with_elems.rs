use zerocopy::TryFromBytes;

#[path = "formats/coco.rs"]
mod coco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8], count: usize) -> Option<&coco::Packet> {
    match TryFromBytes::try_ref_from_suffix_with_elems(source, count) {
        Ok((rest, packet)) => Some(packet),
        _ => None,
    }
}
