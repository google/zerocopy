/// ```anneal
/// isValid self := self.val.val > 0
/// ```
pub struct PositiveUsize {
    val: usize,
}

impl PositiveUsize {
    /// Creates a new `PositiveUsize` if `x > 0`.
    ///
    /// ```anneal
    /// ensures:
    ///   match ret with
    ///   | none => x.val = 0
    ///   | some r => r.val.val = x.val
    /// ```
    pub fn new(x: usize) -> Option<PositiveUsize> {
        if x > 0 { Some(Self { val: x }) } else { None }
    }
}

/// Polyfill for unchecked division.
///
/// ```anneal, unsafe(axiom)
/// requires: b.val > 0
/// ensures: ret.val = a.val / b.val
/// ```
pub unsafe fn unchecked_div(a: usize, b: usize) -> usize {
    todo!()
}

/// ```anneal
/// proof (h_progress):
///   unfold div_positive
///   rcases h_req with ⟨h_self_val_is_valid, h_rhs_is_valid⟩
///   have ho := unchecked_div.spec self_val rhs.val {
///     h_a_is_valid := h_self_val_is_valid
///     h_b_is_valid := by verify_is_valid h_b_is_valid _root_.positive_usize.div_positive
///     h_anon := by simp_all [Anneal.IsValid.isValid]
///   }
///   rcases Aeneas.Std.WP.spec_imp_exists ho with ⟨y, h_eq, _⟩
///   exact ⟨y, h_eq⟩
/// ```
fn div_positive(self_val: usize, rhs: PositiveUsize) -> usize {
    // SAFETY: The type invariant of `PositiveUsize` guarantees that `rhs.val > 0`.
    unsafe { unchecked_div(self_val, rhs.val) }
}

impl std::ops::Div<PositiveUsize> for usize {
    type Output = usize;

    fn div(self, rhs: PositiveUsize) -> usize {
        unsafe { unchecked_div(self, rhs.val) }
    }
}

fn main() {
    if let Some(p) = PositiveUsize::new(2) {
        let _ = 4 / p;
    }
}
