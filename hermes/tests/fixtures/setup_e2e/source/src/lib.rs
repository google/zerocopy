/// ```anneal
/// ensures:
///   if x >= 0 then ret = x else ret = -x
/// proof (h_progress):
///   sorry
/// ```
pub fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}
