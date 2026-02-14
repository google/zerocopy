
/// @spec
/// ensures result = 42
/// decreases by sorry
pub fn unknown_decrease(n: u32) -> u32 {
    if n > 0 {
        unknown_decrease(n - 1)
    } else {
        42
    }
}
