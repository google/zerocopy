//! This example exists as a test for agents to see how well they can
//! automatically write and prove Anneal specifications.

/// ```lean, anneal, unsafe(axiom)
/// axiom spec (data : ConstRawPtr (Slice Std.U8)) :
///   Aeneas.Std.WP.spec (slice_len data) (fun ret_ => ret_ = Anneal.HasMetadata.metadata data)
/// ```
pub const unsafe fn slice_len(data: *const [u8]) -> usize {
    data.len()
}

/// ```lean, anneal, unsafe(axiom)
/// axiom spec (data : ConstRawPtr (Slice Std.U8)) :
///   Aeneas.Std.WP.spec (cast_slice_to_u8 data) (fun ret_ =>
///     (Anneal.HasReferent.referent ret_).address = (Anneal.HasReferent.referent data).address)
/// ```
pub const unsafe fn cast_slice_to_u8(data: *const [u8]) -> *const u8 {
    data.cast::<u8>()
}

/// ```lean, anneal, unsafe(axiom)
/// axiom spec (data : ConstRawPtr Std.U8) (len : Std.Usize) (h_isize : len.val ≤ Isize.max) :
///   Aeneas.Std.WP.spec (slice_from_slice_parts data len) (fun ret_ =>
///     (Anneal.HasReferent.referent ret_).address = (Anneal.HasReferent.referent data).address ∧
///     Anneal.HasMetadata.metadata ret_ = len ∧
///     (Anneal.HasReferent.referent ret_).size = len)
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
/// ```lean, anneal, spec
/// ```
#[allow(unused)]
pub unsafe fn concat_slices(a: *const [u8], b: *const [u8]) -> *const [u8] {
    // TODO: Fill me in.
    todo!()
}

fn main() {}
