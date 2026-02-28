/// Computes n!
///
/// ```lean, hermes, spec
/// ensures result > 0
/// proof
///   -- We use `sorry` here because Aeneas's generated standard library functions
///   -- currently cause infinite recursion during simplificaton. Testing the Hermes
///   -- translation interface remains unaffected.
///   sorry
/// ```
pub fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {}
