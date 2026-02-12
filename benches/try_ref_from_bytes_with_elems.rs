use zerocopy::TryFromBytes;

#[path = "formats/coco.rs"]
mod coco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8], count: usize) -> Option<&coco::Packet> {
    TryFromBytes::try_ref_from_bytes_with_elems(source, count).ok()
}
