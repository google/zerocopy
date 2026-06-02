/// ```lean, anneal
/// def isValid (N : Std.Usize) : Prop := N.val > 0
/// ```
pub struct ConstGen<const N: usize>;

/// ```lean, anneal
/// def isSafe (N : Std.Usize) : Prop := N.val > 0
/// ```
pub unsafe trait ConstTrait<const N: usize> {}

/// ```lean, anneal, spec
/// theorem spec {N : Std.Usize} (arr : Array Std.U8 N) :
///   Aeneas.Std.WP.spec (use_const arr) (fun ret_ =>
///     if N.val = 0 then ret_.val = 0 else True) := by
///   unfold use_const
///   split <;> (try unfold Array.index_usize) <;> (try split) <;> simp_all <;> scalar_tac
/// ```
pub fn use_const<const N: usize>(arr: [u8; N]) -> u8 {
    if N > 0 { arr[0] } else { 0 }
}

fn main() {}
