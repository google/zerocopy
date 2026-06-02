/// ```lean, anneal
/// def isValid (self : PositiveUsize) : Prop := self.val.val > 0
/// ```
pub struct PositiveUsize {
    val: usize,
}

impl PositiveUsize {
    /// Creates a new `PositiveUsize` if `x > 0`.
    ///
    /// ```lean, anneal, spec
    /// theorem spec (x : Std.Usize) :
    ///   Aeneas.Std.WP.spec (PositiveUsize.new x) (fun ret_ =>
    ///     match ret_ with
    ///     | none => x.val = 0
    ///     | some r => r.val.val = x.val) := by
    ///   sorry
    /// ```
    pub fn new(x: usize) -> Option<PositiveUsize> {
        if x > 0 { Some(Self { val: x }) } else { None }
    }
}

/// Polyfill for unchecked division.
///
/// ```lean, anneal, unsafe(axiom)
/// axiom spec (a b : Std.Usize) (h_req : b.val > 0) :
///   Aeneas.Std.WP.spec (unchecked_div a b) (fun ret_ => ret_.val = a.val / b.val)
/// ```
pub unsafe fn unchecked_div(a: usize, b: usize) -> usize {
    todo!()
}

/// ```lean, anneal, spec
/// theorem spec (self_val : Std.Usize) (rhs : PositiveUsize) :
///   Aeneas.Std.WP.spec (div_positive self_val rhs) (fun ret_ => ret_.val = self_val.val / rhs.val.val) := by
///   sorry
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
