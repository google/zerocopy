/// Computes n!
///
/// ```lean, hermes, spec
/// ensures result > 0
/// proof
///   induction n <;> simp_all [factorial]
/// ```
pub fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {}
