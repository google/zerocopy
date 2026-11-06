/// ```lean, anneal, spec
/// requires: False
/// ensures (h0): ret < 0
/// proof (h_progress):
///   cases h_req.h_anon
/// proof (h0):
///   cases h_anon
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {}
