/// ```lean, anneal
/// def isValid (self : Empty) : Prop := True
/// ```
pub struct Empty {}

/// ```lean, anneal
/// def isValid (self : WrapUnit) : Prop := True
/// ```
pub struct WrapUnit {
    pub f: (),
}

/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (unit_arg ()) (fun ret_ => True) := by
///   sorry
/// ```
pub fn unit_arg(_: ()) {}

/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (unit_ret) (fun ret_ => True) := by
///   sorry
/// ```
pub fn unit_ret() -> () {}
