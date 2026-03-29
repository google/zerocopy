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
/// ```
pub fn use_const<const N: usize>(arr: [u8; N]) -> u8 {
    if N > 0 { arr[0] } else { 0 }
}

fn main() {}
