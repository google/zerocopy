/// `isValid` defines a structural invariant for a type.
///
/// Under the hood, Anneal will automatically generate a `Anneal.IsValid` instance
/// for this type mapping to the expression below. You can apply it in proofs
/// using `simp_all [Anneal.IsValid.isValid]`.
///
/// ```lean, anneal
/// def isValid (self : PositiveUsize) : Prop := self.val.val > 0
/// ```
pub struct PositiveUsize {
    #[allow(unused)]
    val: usize,
}

/// `isSafe` defines an invariant for an unsafe trait.
///
/// In this trait, we enforce that `Self` has an alignment of exactly 1.
///
/// ```lean, anneal
/// def isSafe (Self : Type) [Anneal.core.marker.Sized Self] [Anneal.HasStaticLayout Self] : Prop :=
///   (Anneal.HasStaticLayout.layout Self).align.val.val = 1
/// ```
pub unsafe trait Unaligned: Sized {}

/// An optimized implementation of addition.
///
/// `unsafe(axiom)` marks this function as an axiom, meaning Aeneas will skip
/// analyzing the body of this function, and Anneal will accept the spec
/// without proof.
///
/// ```lean, anneal, unsafe(axiom)
/// axiom spec (a b : Std.Usize) (h_req : a.val + b.val ≤ Usize.max) :
///   Aeneas.Std.WP.spec (fast_add a b) (fun ret_ => ret_.val = a.val + b.val)
/// ```
#[allow(unused)]
pub unsafe fn fast_add(a: usize, b: usize) -> usize {
    todo!()
}

/// The `requires` block defines a pre-condition named `h_is_safe`.
///
/// Notice the type `Unaligned.Safe T Inst`. When you define an `isSafe` block
/// on a trait, Anneal generates a `.Safe` predicate parameterized by the type `T`
/// and the specific trait implementation `Inst`.
///
/// ```lean, anneal, spec
/// theorem spec {T : Type} (UnalignedInst : Unaligned T) (sized_inst : Anneal.core.marker.Sized T) (layout_inst : Anneal.HasStaticLayout T)
///   (h_req : Unaligned.isSafe T) :
///   Aeneas.Std.WP.spec (get_unaligned_fast_pad (T := T) (UnalignedInst := UnalignedInst)) (fun ret_ => ret_.val.val = 1) := by
///   sorry
/// ```
pub unsafe fn get_unaligned_fast_pad<T: Unaligned>() -> PositiveUsize {
    let align = core::mem::align_of::<T>();
    let padded = unsafe { fast_add(align, 0) };
    PositiveUsize { val: padded }
}

fn main() {}
