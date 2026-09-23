/// ```anneal
/// isSafe: ∀ (f: Self) (i: I), ∃ (o: O), inst.coreopsfunctionFnOnceSelfTupleIOInst.call_once f i = ok o
/// ```
pub unsafe trait NoPanic<I, O>: FnOnce(I) -> O {}

/// ```anneal
/// requires: nopanic.NoPanic.Safe F NoPanicInst
/// ensures: True
/// proof (h_progress):
///   rcases h_req.h_anon with ⟨isSafe⟩
///   rcases isSafe f i with ⟨o, ho⟩
///   use o
///   unfold nopanic.foo
///   rw [ho]
/// proof:
///   trivial
/// ```
pub unsafe fn foo<I, O, F: NoPanic<I, O>>(f: F, i: I) -> O {
    f(i)
}

fn main() {}
