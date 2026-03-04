
// Helper for Aeneas/Hermes
/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn old<T>(x: T) -> T { x }

// 1. Legacy/Result Shadowing
// 'ret' is often used by Aeneas as the return variable name in specs.
pub fn result_shadow(ret: u32) -> u32 {
    ret
}

// 2. Old/New Shadowing
// 'old_x' effectively shadows the concept of 'old(x)'.
pub fn old_shadow(old_x: &mut u32) {
    *old_x += 1;
}

// 3. Internal Shadowing
pub fn internal_shadow(ret: u32, x_new: u32) -> u32 {
    ret + x_new
}
