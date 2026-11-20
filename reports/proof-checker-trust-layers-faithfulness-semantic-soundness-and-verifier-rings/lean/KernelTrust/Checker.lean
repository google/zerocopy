/-
  Toy.KernelTrust.Checker

  The checker interface and the implementation-faithfulness predicate
  `Faithful C R` ("`C` accepts only what the rule table `R` derives").
-/
import KernelTrust.Semantics

namespace Toy.KernelTrust

/-- A proof checker: a type of proof objects and a total decision procedure
that says whether a proof object is accepted as a proof of a sequent.

The checker is an arbitrary function.  It need not mention any rule table; its
relation to a rule table is stated separately by `Faithful` / `Complete`. -/
structure Checker where
  /-- The proof objects (witnesses, certificates, scripts) the checker reads. -/
  Wit : Type
  /-- `accepts w Γ φ = true`: the checker accepts `w` as a proof of `Γ ⊢ φ`. -/
  accepts : Wit → Ctx → Form → Bool

/-- **Implementation faithfulness** (soundness direction): everything the
checker accepts is derivable from the rule table `R`.

This is the *only* direction used by the trust results.  It does not say the
checker accepts anything at all: `rejectAll` is faithful to every rule table
(see `ex_faithful_rejectAll_pos`).  The converse direction is `Complete`. -/
def Faithful (C : Checker) (R : RuleSet) : Prop :=
  ∀ (w : C.Wit) (Γ : Ctx) (φ : Form), C.accepts w Γ φ = true → Derivable R Γ φ

/-- Completeness of a checker for a rule table: every derivable sequent has
some accepted proof object.  Used only to show that the faithful checkers in
the counterexamples are not degenerate. -/
def Complete (C : Checker) (R : RuleSet) : Prop :=
  ∀ (Γ : Ctx) (φ : Form), Derivable R Γ φ → ∃ w : C.Wit, C.accepts w Γ φ = true

/-- The checker accepts some proof object for the sequent `⊢ ⊥`. -/
def Checker.AcceptsBot (C : Checker) : Prop :=
  ∃ w : C.Wit, C.accepts w [] .bot = true

/-- The checker that rejects everything. -/
def rejectAll : Checker := ⟨Unit, fun _ _ _ => false⟩

/-- The checker that accepts everything. -/
def acceptAll : Checker := ⟨Unit, fun _ _ _ => true⟩

/-- **Separate-artifact quorum** of two checkers: a sequent is accepted when
both member checkers accept it, each on *its own* proof object.  The two proof
objects `w.1` and `w.2` are independent and may differ, so this models a
submitter who sends one artifact to each checker, not two checkers re-checking
one exported proof (for that, see `sharedQuorum`). -/
def quorum (C D : Checker) : Checker where
  Wit := C.Wit × D.Wit
  accepts w Γ φ := C.accepts w.1 Γ φ && D.accepts w.2 Γ φ

/-- **Shared-artifact quorum** ("N-version re-checking of one exported proof"):
a sequent is accepted when both member checkers accept the *same* proof object.
`D` reads it through the translation `tr`, which is the identity when both
checkers read the same format. -/
def sharedQuorum (C D : Checker) (tr : C.Wit → D.Wit) : Checker where
  Wit := C.Wit
  accepts w Γ φ := C.accepts w Γ φ && D.accepts (tr w) Γ φ

/-! ## Basic facts -/

/-- A checker that is faithful to a *consistent* rule table never accepts
`⊢ ⊥`.  (Purely syntactic: no semantics involved.) -/
theorem not_acceptsBot_of_faithful_of_consistent {C : Checker} {R : RuleSet}
    (hF : Faithful C R) (hC : Consistent R) : ¬ C.AcceptsBot :=
  fun ⟨w, hw⟩ => hC (hF w [] .bot hw)

/-- A quorum is faithful as soon as *one* member is faithful (left). -/
theorem quorum_faithful_left {C D : Checker} {R : RuleSet} (h : Faithful C R) :
    Faithful (quorum C D) R := by
  intro w Γ φ hw
  simp only [quorum, Bool.and_eq_true] at hw
  exact h w.1 Γ φ hw.1

/-- A quorum is faithful as soon as *one* member is faithful (right). -/
theorem quorum_faithful_right {C D : Checker} {R : RuleSet} (h : Faithful D R) :
    Faithful (quorum C D) R := by
  intro w Γ φ hw
  simp only [quorum, Bool.and_eq_true] at hw
  exact h w.2 Γ φ hw.2

/-- A quorum accepts `⊢ ⊥` exactly when both members do. -/
theorem quorum_acceptsBot_iff {C D : Checker} :
    (quorum C D).AcceptsBot ↔ C.AcceptsBot ∧ D.AcceptsBot := by
  constructor
  · rintro ⟨⟨w1, w2⟩, hw⟩
    simp only [quorum, Bool.and_eq_true] at hw
    exact ⟨⟨w1, hw.1⟩, ⟨w2, hw.2⟩⟩
  · rintro ⟨⟨w1, h1⟩, ⟨w2, h2⟩⟩
    exact ⟨(w1, w2), by simp [quorum, h1, h2]⟩

/-! ## Examples for the definitions above -/

/-- Positive example (`Faithful`), degenerate on purpose: the reject-all
checker is faithful to every rule table.  `Faithful` alone never implies that a
checker is useful. -/
theorem ex_faithful_rejectAll_pos (R : RuleSet) : Faithful rejectAll R := by
  intro w Γ φ h
  cases h

/-- Negative example (`Faithful`): the accept-all checker is not faithful to
the standard rules. -/
theorem ex_faithful_acceptAll_neg : ¬ Faithful acceptAll stdRules :=
  fun h => stdRules_consistent (h () [] .bot rfl)

/-- Positive example (`Complete`): the accept-all checker is complete for
every rule table. -/
theorem ex_complete_acceptAll_pos (R : RuleSet) : Complete acceptAll R :=
  fun _ _ _ => ⟨(), rfl⟩

/-- Negative example (`Complete`): the reject-all checker is not complete for
the standard rules. -/
theorem ex_complete_rejectAll_neg : ¬ Complete rejectAll stdRules := by
  intro h
  obtain ⟨w, hw⟩ := h [] Form.top ex_derivable_top_pos
  cases hw

/-- Positive example (`Checker.AcceptsBot`). -/
theorem ex_acceptsBot_acceptAll_pos : acceptAll.AcceptsBot := ⟨(), rfl⟩

/-- Negative example (`Checker.AcceptsBot`). -/
theorem ex_acceptsBot_rejectAll_neg : ¬ rejectAll.AcceptsBot := by
  rintro ⟨w, hw⟩
  cases hw

/-- Positive example (`quorum`): pairing any checker with a faithful one gives
a faithful quorum, even if the other member accepts everything. -/
theorem ex_quorum_pos (R : RuleSet) : Faithful (quorum acceptAll rejectAll) R :=
  quorum_faithful_right (ex_faithful_rejectAll_pos R)

/-- Negative example (`quorum`): two unfaithful checkers that agree are still
unfaithful; agreement between checkers is not evidence by itself. -/
theorem ex_quorum_neg :
    (quorum acceptAll acceptAll).AcceptsBot ∧ ¬ Faithful (quorum acceptAll acceptAll) stdRules :=
  ⟨⟨((), ()), rfl⟩, fun h => stdRules_consistent (h ((), ()) [] .bot rfl)⟩

/-- A shared-artifact quorum is faithful as soon as its first member is. -/
theorem sharedQuorum_faithful_left {C D : Checker} {tr : C.Wit → D.Wit} {R : RuleSet}
    (h : Faithful C R) : Faithful (sharedQuorum C D tr) R := by
  intro w Γ φ hw
  simp only [sharedQuorum, Bool.and_eq_true] at hw
  exact h w Γ φ hw.1

/-- Positive example (`sharedQuorum`): pairing the accept-all checker with the
reject-all checker on a shared artifact gives a faithful (degenerate) checker. -/
theorem ex_sharedQuorum_pos (R : RuleSet) :
    Faithful (sharedQuorum rejectAll acceptAll (fun _ => ())) R :=
  sharedQuorum_faithful_left (ex_faithful_rejectAll_pos R)

/-- Negative example (`sharedQuorum`): two accept-all checkers reading one
artifact still accept `⊢ ⊥`. -/
theorem ex_sharedQuorum_neg :
    (sharedQuorum acceptAll acceptAll id).AcceptsBot ∧
    ¬ Faithful (sharedQuorum acceptAll acceptAll id) stdRules :=
  ⟨⟨(), rfl⟩, fun h => stdRules_consistent (h () [] .bot rfl)⟩

end Toy.KernelTrust
