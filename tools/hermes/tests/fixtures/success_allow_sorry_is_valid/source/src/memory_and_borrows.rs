//! Tests for memory safety, borrowing patterns, and lifetime management.

/// Test for swapping two mutable references.
/// ```lean, hermes, spec
/// proof:
///   sorry
/// ```
pub fn swap(a: &mut u32, b: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

/// Swapping with different parameter order.
pub fn swap_reordered(b: &mut u32, a: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

/// A "sandwich" borrow where an immutable borrow is taken between mutable operations.
/// ```lean, hermes, spec
/// proof:
///   sorry
/// ```
pub fn sandwich_borrow(a: &mut u32, b: &u32, c: &mut u32) {
    *a += *b;
    *c += *b;
}

/// Destructuring a mutable reference to a tuple.
/// ```lean, hermes, spec
/// proof:
///   sorry
/// ```
pub fn deep_destruct(x: &mut (u32, u32)) {
    x.0 += 1;
    x.1 += 1;
}

/// Explicit lifetime splitting with disjoint mutable borrows.
/// ```lean, hermes, spec
/// proof:
///   sorry
/// ```
pub fn partial_mut<'a, 'b>(x: &'a mut u32, y: &'b mut u32) {
    if *x > 10 {
        *y += 1;
    } else {
        *x += 1;
    }
}

/// Simple mutable reference passthrough.
/// ```lean, hermes, spec
/// proof:
///   sorry
/// ```
pub fn mut_passthrough(x: &mut u32) {
    *x += 1;
}

/// Verifying that `isValid` on mutable references is correctly handled in proofs.
/// ```lean, hermes, spec
/// proof (h_x'_is_valid):
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn target_mut_ref_is_valid(x: &mut u32) {}

/// ```lean, hermes
/// requires: a.len = b.len
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub unsafe fn zip(a: &[u8], b: &[u8]) {}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn mix(a: &mut u32, b: &u32, c: &mut u32) {
    *a += *b;
    *c += *b;
}


// --- Restored from missing tests ---
// Restored fn nested_mut from test_3_4_deep_destruct
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn nested_mut(x: &mut (u32, u32)) {
    x.0 += 1;
    x.1 += 1;
}

