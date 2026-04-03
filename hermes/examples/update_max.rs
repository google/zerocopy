/// Sets `acc` to `val` if `val` is larger.
///
/// ```lean, hermes, spec
/// -- Note: We use the natively supported `acc'` notation instead of `old(acc)`
/// -- to succinctly refer to the post-state value of the mutable reference.
/// ensures acc' = max acc val
/// proof
///   unfold update_max
///   split <;> simp_all
///   simp [max]
///   split <;> simp_all
/// ```
pub fn update_max(acc: &mut u32, val: u32) {
    if val > *acc {
        *acc = val;
    }
}

fn main() {}
