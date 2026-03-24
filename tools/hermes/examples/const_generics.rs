/// ```lean, hermes, spec
/// ```
pub fn use_const<const N: usize>(arr: [u8; N]) -> u8 {
    if N > 0 { arr[0] } else { 0 }
}

fn main() {}
