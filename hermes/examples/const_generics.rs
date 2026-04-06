/// ```hermes
/// isValid self := N > 0
/// ```
pub struct ConstGen<const N: usize>;

/// ```hermes
/// isSafe : N > 0
/// ```
pub unsafe trait ConstTrait<const N: usize> {}

/// ```hermes
/// ensures: if N.val = 0 then ret.val = 0 else True
/// proof:
///   unfold use_const at h_returns
///   split at h_returns <;> (try unfold Array.index_usize at h_returns) <;> (try split at h_returns) <;> simp_all <;> scalar_tac
/// proof (h_progress):
///   unfold use_const
///   split <;> (try unfold Array.index_usize) <;> (try split) <;> simp_all <;> scalar_tac
/// ```
pub fn use_const<const N: usize>(arr: [u8; N]) -> u8 {
    if N > 0 { arr[0] } else { 0 }
}

fn main() {}
