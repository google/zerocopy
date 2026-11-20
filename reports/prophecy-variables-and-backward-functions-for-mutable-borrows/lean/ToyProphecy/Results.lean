import ToyProphecy.Monotone
import ToyProphecy.Sim.MainExist

/-!
# Main statements

Every general result in this file quantifies over all programs of the toy
language (straight-line code with borrows of locals, run-time selected borrows,
nested reborrows, writes through borrows, explicit ends, and calls taking and
returning a borrow) and over all initial stores. Hypotheses are the separate
parts of the borrow discipline from `ToyProphecy/Discipline.lean`. The
discipline checker stops at the first scoping error, so for a program with a
scoping error the hypotheses constrain only what is checked before the error.

`prophOutcome_iff_refSem_of_discipline` and
`prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
are derived from the other statements of this file;
`prophOutcomeWith_omitAtEnd_of_prophOutcome` is proved from the simulation
lemmas of `ToyProphecy/Monotone.lean`. The remaining five statements are proved
by the simulation arguments of `ToyProphecy/Sim/`: callee frames in
`Sim/CalleeBack.lean`, `Sim/Callee.lean` and `Sim/CalleeRun.lean`, main programs
in `Sim/Main*.lean`.
-/

namespace Toy.Prophecy

/-! ## Soundness of the backward-function translation -/

/-- **Soundness of the backward-function translation.** For every program that
obeys all five parts of the borrow discipline and every initial store, the
backward-function translation computes exactly the reference semantics' outcome:
the same final store, or stuck exactly when the reference semantics is stuck. -/
theorem backSem_eq_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    backSem P σ = refSem P σ :=
  backSem_eq_refSem_aux P σ hL hF hE hB hX

/-! ## Agreement of the two translations -/

/-- **Agreement.** For every program that obeys all five parts of the borrow
discipline and every initial store, the final stores admitted by the prophecy
translation (over all prophecy assignments satisfying every resolution
constraint, standard policy) are exactly the backward-function translation's
result: one store if the latter succeeds, none if it is stuck. -/
theorem prophOutcome_iff_backSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ backSem P σ = some σ' := by
  intro σ'
  rw [backSem_eq_refSem_aux P σ hL hF hE hB hX]
  exact ⟨prophOutcome_sound_aux P σ σ' hL hF hE hB hX, prophOutcome_of_refSem_aux P σ σ' hL hF hE hB⟩

/-! ## Soundness of the prophecy translation (derived) -/

/-- **Soundness and precision of the prophecy translation.** For every program
that obeys all five parts of the borrow discipline and every initial store, the
final stores admitted by the prophecy translation are exactly the reference
semantics' outcome. (Derived from the two statements above.) -/
theorem prophOutcome_iff_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ refSem P σ = some σ' := by
  intro σ'
  rw [prophOutcome_iff_backSem_of_discipline P σ hL hF hE hB hX σ',
    backSem_eq_refSem_of_discipline P σ hL hF hE hB hX]

/-! ## Inclusion of the real outcome does not need every borrow to be ended -/

/-- **Inclusion: the real outcome is admitted without `AllEndedAtExit`.** For
every program with no access to lent locals, no access to reborrowed borrows, no
use of a borrow after its end, and fresh borrow names, and every initial store:
if the reference semantics produces `σ'`, the prophecy translation (standard
policy) admits `σ'`. Ending every borrow is *not* assumed: the prophecy of a
borrow that never ends is never resolved, which can only add admitted stores. -/
theorem prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcome P σ σ' :=
  prophOutcome_of_refSem_aux P σ σ' hL hF hE hB h

/-! ## Omitting a resolution loses precision, never the real outcome -/

/-- **Omission only weakens.** For every program, store, and borrow name `r`:
every final store admitted under the standard policy is still admitted when no
`endBorrow r` statement of the main program emits its resolution constraint. No
discipline hypothesis is needed. -/
theorem prophOutcomeWith_omitAtEnd_of_prophOutcome (r : RefVar) (P : Prog) (σ σ' : Store)
    (h : ProphOutcome P σ σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ' := by
  obtain ⟨φ, s1, hrun, hsat, rfl⟩ := h
  obtain ⟨s2, hrun2, hst, hcs⟩ :=
    runP_omitAtEnd_sim r φ P 0 (PState.init σ) (PState.init σ) s1 rfl rfl rfl
      (fun _ hc => hc) hrun
  exact ⟨φ, s2, hrun2, fun c hc => hsat c (hcs c hc), hst⟩

/-- **Omission keeps the real outcome.** For every program with no access to lent
locals, no access to reborrowed borrows, no use after end, and fresh borrow
names, and every borrow name `r`: if the reference semantics produces `σ'`, the
prophecy translation with every main-program `endBorrow r` left unresolved
(`ResPolicy.omitAtEnd r`, keyed by the name `r`; callee frames and callee-exit
resolutions unaffected) still admits `σ'`. (Derived from the two statements
above.) -/
theorem prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (r : RefVar) (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ' :=
  prophOutcomeWith_omitAtEnd_of_prophOutcome r P σ σ'
    (prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
      P σ σ' hL hF hE hB h)

/-! ## Calls returning a borrow -/

/-- **Backward functions of single-borrow callees are projections.** For every
callee that is scoped (its body uses no never-bound reference variable and no
local, and its returned reference variable `f.ret` is the parameter or bound by
the body) and binds every borrow name at most once (including names of ended
borrows), the backward function of its backward summary returns the final value
of the returned borrow, whatever the argument: `calleeBack f a v = v`. -/
theorem calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings (f : Callee)
    (hS : CalleeScoped f) (hB : CalleeFreshBindings f) :
    ∀ a v, calleeBack f a v = v :=
  calleeBack_eq_final_aux f hS hB

/-- **Callee summaries agree.** For every callee with no frozen access, no use
after end, and no rebinding (including reuse of an ended name) in its body and
return: its prophecy contract (argument current value `a`, argument prophecy
`pf`, returned borrow `(c, rf)`) holds exactly when `c` is the forward value of
its backward summary at `a` and `pf` is the backward function applied to `a` and
`rf`. Scoping is not assumed. The statement is about one callee in isolation; it
does not mention call sites. -/
theorem prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings
    (f : Callee)
    (hF : CalleeNoFrozenAccess f) (hE : CalleeNoUseAfterEnd f)
    (hB : CalleeFreshBindings f) :
    ∀ a c pf rf, ProphContract f a c pf rf ↔ (calleeFwd f a = some c ∧ pf = calleeBack f a rf) :=
  prophContract_iff_aux f hF hE hB

end Toy.Prophecy
