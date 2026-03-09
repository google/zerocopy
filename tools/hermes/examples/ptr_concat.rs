//! This example exists as a test for agents to see how well they can
//! automatically write and prove Hermes specifications.

/// ```lean, hermes, unsafe(axiom)
/// ensures: ret = Hermes.HasMetadata.metadata data
/// ```
pub const unsafe fn slice_len(data: *const [u8]) -> usize {
    data.len()
}

/// ```lean, hermes, unsafe(axiom)
/// ensures: (Hermes.HasReferent.referent ret).address = (Hermes.HasReferent.referent data).address
/// ```
pub const unsafe fn cast_slice_to_u8(data: *const [u8]) -> *const u8 {
    data.cast::<u8>()
}

/// ```lean, hermes, unsafe(axiom)
/// requires (h_isize): len.val ≤ Isize.max
/// ensures (h_addr): (Hermes.HasReferent.referent ret).address = (Hermes.HasReferent.referent data).address
/// ensures (h_len): Hermes.HasMetadata.metadata ret = len
/// ensures (h_size): (Hermes.HasReferent.referent ret).size = len
/// ```
pub const unsafe fn slice_from_slice_parts(data: *const u8, len: usize) -> *const [u8] {
    core::ptr::slice_from_raw_parts(data, len)
}

/// TODO:
/// - Require that both referents live in the same allocation
/// - Require that both referents are contiguous and non-overlapping
/// - Ensure that the returned referent is the concatenation of the two input referents
/// - Ensure that the returned referent lives in the same allocation as the input referents
///
/// ```lean, hermes, spec
/// ```
pub unsafe fn concat_slices(a: *const [u8], b: *const [u8]) -> *const [u8] {
    // TODO: Fill me in.
}

fn main() {}
