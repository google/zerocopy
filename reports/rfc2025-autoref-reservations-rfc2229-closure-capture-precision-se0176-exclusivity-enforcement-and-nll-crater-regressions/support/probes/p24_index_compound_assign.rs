// Rust analogue of SE-0176's `array[0] += array[1]` NOT-A-CONFLICT example.
pub fn f() -> Vec<i32> { let mut v = vec![1, 2]; v[0] += v[1]; v }
