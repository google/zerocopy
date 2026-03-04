#[path = "formats/coco.rs"]
mod format;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8]) -> Option<&format::CocoPacket> {
    zerocopy::TryFromBytes::try_ref_from_bytes(source).ok()
}
