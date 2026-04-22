/// ```lean, anneal
/// def isSafe {Self I O : Type} (inst : NoPanic Self I O) : Prop :=
///   ∀ (f: Self) (i: I), ∃ (o: O), inst.coreopsfunctionFnOnceSelfTupleIOInst.call_once f i = ok o
/// ```
pub unsafe trait NoPanic<I, O>: FnOnce(I) -> O {}

/// ```lean, anneal, spec
/// theorem spec {I O F : Type} (NoPanicInst : NoPanic F I O) (f : F) (i : I)
///   (h_req : NoPanic.isSafe NoPanicInst) :
///   Aeneas.Std.WP.spec (foo NoPanicInst f i) (fun ret_ => True) := by
///   sorry
/// ```
pub unsafe fn foo<I, O, F: NoPanic<I, O>>(f: F, i: I) -> O {
    f(i)
}

fn main() {}
