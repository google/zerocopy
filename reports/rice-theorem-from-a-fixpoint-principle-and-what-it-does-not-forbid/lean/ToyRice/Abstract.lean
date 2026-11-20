/-
# Abstract Rice theorem and its direct consequences

All results in this file hold in an arbitrary `System`; they use only the laws they name.
-/
import ToyRice.Basic

namespace Toy.Rice

universe u v

variable {S : System.{u, v}}

/-- **Sharp form of abstract Rice.** In a system with the fixpoint principle, let `chk` decide
an extensional predicate `P`, let `a` satisfy `P` and `b` violate it. Then the *swapped*
switch `c ↦ if chk c then b else a` is not admissible.

Only this one switch is used; the unswapped switch `c ↦ if chk c then a else b` may well be
admissible (see `Flat.unswappedSwitch_admissible`). -/
theorem swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    {chk : S.Code → Bool} (hdec : Decides chk P) {a b : S.Code} (ha : P a) (hb : ¬ P b) :
    ¬ S.Adm (switch chk b a) := by
  intro hadm
  obtain ⟨c, hc⟩ := hfix _ hadm
  cases hchk : chk c with
  | true =>
    have hPc : P c := (hdec c).1 hchk
    rw [switch_of_true hchk] at hc
    exact hb ((hext b c hc).2 hPc)
  | false =>
    have hPc : ¬ P c := fun h => by
      rw [(hdec c).2 h] at hchk
      exact Bool.noConfusion hchk
    rw [switch_of_false hchk] at hc
    exact hPc ((hext a c hc).1 ha)

/-- **Abstract Rice theorem.** In any programming system with the fixpoint principle, no
nontrivial extensional predicate on codes is decided inside the system. -/
theorem not_decidedInside_of_fixpointPrinciple_extensional_nontrivial
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hnt : NontrivialPred P) : ¬ DecidedInside S P := by
  rintro ⟨chk, hdec, hsw⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hnt
  exact swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides hfix hext hdec ha hb
    (hsw b a)

/-- **Abstract Rice, class form** (a corollary of the abstract Rice theorem, kept as a lemma).
Let `K` be a class of checkers every member of which has all its switches admissible
(`SwitchClosed S K`, i.e. `K ⊆ SwitchAdmissible S`). In a system with the fixpoint principle, no
checker in `K` decides a nontrivial extensional predicate. -/
theorem not_decidedBy_of_fixpointPrinciple_switchClosed_extensional_nontrivial
    (hfix : FixpointPrinciple S) {K : (S.Code → Bool) → Prop} (hK : SwitchClosed S K)
    {P : S.Code → Prop} (hext : Extensional S P) (hnt : NontrivialPred P) :
    ¬ DecidedBy S K P := by
  rintro ⟨chk, hk, hdec⟩
  exact not_decidedInside_of_fixpointPrinciple_extensional_nontrivial hfix hext hnt
    ⟨chk, hdec, hK chk hk⟩

/-- **Characterization.** In a system with the fixpoint principle whose admissible class
contains the constant transformers, an extensional predicate is decided inside the system
if and only if it is trivial (true of every code or of none). The forward direction uses
classical logic. -/
theorem decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional
    (hfix : FixpointPrinciple S) (hconst : ConstClosed S) {P : S.Code → Prop}
    (hext : Extensional S P) :
    DecidedInside S P ↔ (∀ c, P c) ∨ (∀ c, ¬ P c) := by
  constructor
  · intro hdi
    apply Classical.byContradiction
    intro hnot
    have h1 : ∃ a, P a := Classical.byContradiction fun h =>
      hnot (Or.inr fun c hc => h ⟨c, hc⟩)
    have h2 : ∃ b, ¬ P b := Classical.byContradiction fun h =>
      hnot (Or.inl fun c => Classical.byContradiction fun hc => h ⟨c, hc⟩)
    exact not_decidedInside_of_fixpointPrinciple_extensional_nontrivial hfix hext ⟨h1, h2⟩ hdi
  · rintro (hall | hnone)
    · refine ⟨fun _ => true, fun c => ⟨fun _ => hall c, fun _ => rfl⟩, fun a _ => ?_⟩
      exact hconst a
    · refine ⟨fun _ => false, fun c => ⟨fun h => Bool.noConfusion h, fun h => absurd h (hnone c)⟩,
        fun _ b => ?_⟩
      exact hconst b

/-- If *every* switch on *every* checker is admissible, the fixpoint principle forces the
semantics to be constant. -/
theorem sem_constant_of_fixpointPrinciple_allSwitchesAdmissible
    (hfix : FixpointPrinciple S) (hall : ∀ chk : S.Code → Bool, SwitchAdmissible S chk) :
    ∀ c d, S.sem c = S.sem d := by
  intro c d
  apply Classical.byContradiction
  intro hne
  have hext : Extensional S (fun x => S.sem x = S.sem c) := by
    intro x y hxy
    show S.sem x = S.sem c ↔ S.sem y = S.sem c
    rw [hxy]
  have hnt : NontrivialPred (fun x => S.sem x = S.sem c) :=
    ⟨⟨c, rfl⟩, ⟨d, fun h => hne h.symm⟩⟩
  have hdi : DecidedInside S (fun x => S.sem x = S.sem c) :=
    ⟨fun x => @decide (S.sem x = S.sem c) (Classical.propDecidable _),
      fun x => by simp, hall _⟩
  exact not_decidedInside_of_fixpointPrinciple_extensional_nontrivial hfix hext hnt hdi

/-- The system with codes `C`, behaviours `B`, semantics `sem`, in which every transformer
is admissible. -/
def allAdm {C : Type u} {B : Type v} (sem : C → B) : System.{u, v} :=
  ⟨C, B, sem, fun _ => True⟩

/-- With a nonempty code type and every transformer admissible, the fixpoint principle holds
exactly when all codes have the same behaviour. -/
theorem fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty {C : Type u} {B : Type v}
    (sem : C → B) (hne : Nonempty C) :
    FixpointPrinciple (allAdm sem) ↔ ∀ c d : C, sem c = sem d := by
  constructor
  · intro hfix
    exact sem_constant_of_fixpointPrinciple_allSwitchesAdmissible (S := allAdm sem) hfix
      (fun _ _ _ => trivial)
  · intro hconst f _
    obtain ⟨c⟩ := hne
    exact ⟨c, hconst (f c) c⟩

/-- **What Rice does not forbid: the reject-all checker.** If constant transformers are
admissible, the checker that rejects every code is sound for every predicate and is
switch-admissible. No fixpoint hypothesis is involved, so this holds in systems with the
fixpoint principle too. -/
theorem rejectAll_sound_switchAdmissible_of_constClosed (hconst : ConstClosed S)
    (P : S.Code → Prop) :
    SoundFor (fun _ : S.Code => false) P ∧ SwitchAdmissible S (fun _ : S.Code => false) :=
  ⟨fun _ h => Bool.noConfusion h, fun _ b => hconst b⟩

/-- The dual of the reject-all checker: if constant transformers are admissible, the accept-all
checker is complete for every predicate and switch-admissible. -/
theorem acceptAll_complete_switchAdmissible_of_constClosed (hconst : ConstClosed S)
    (P : S.Code → Prop) :
    CompleteFor (fun _ : S.Code => true) P ∧ SwitchAdmissible S (fun _ : S.Code => true) :=
  ⟨fun _ _ => rfl, fun a _ => hconst a⟩

/-! ## Incompleteness of switch-admissible checkers -/

/-- **Single-switch incompleteness.** In a system with the fixpoint principle, let `chk` be
sound for an extensional `P`, let `b` violate `P`, and suppose the one switch
`c ↦ if chk c then b else a` is admissible. Then some code with the same behaviour as `a` is
rejected by `chk`. (`a` need not satisfy `P`.) The proof uses no classical reasoning (its only axiom is `propext`). -/
theorem exists_sameSem_rejected_of_fixpointPrinciple_extensional_sound_swappedSwitch
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    {chk : S.Code → Bool} (hsound : SoundFor chk P) {a b : S.Code} (hb : ¬ P b)
    (hadm : S.Adm (switch chk b a)) :
    ∃ c, S.sem c = S.sem a ∧ chk c = false := by
  obtain ⟨c, hc⟩ := hfix _ hadm
  cases hchk : chk c with
  | true =>
    rw [switch_of_true hchk] at hc
    exact absurd ((hext b c hc).2 (hsound c hchk)) hb
  | false =>
    rw [switch_of_false hchk] at hc
    exact ⟨c, hc.symm, hchk⟩

/-- **Verdict split, localized.** In a system with the fixpoint principle, let `chk` be
switch-admissible. For any two codes `a` and `b`, `chk` rejects some code with the behaviour of
`a`, or accepts some code with the behaviour of `b`. Consequently no realizable behaviour (the
behaviour of some code) has all its codes accepted while a realizable behaviour has all its codes
rejected (`not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible`);
the two forms are equivalent classically
(`sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected`). Elements of `S.Beh`
that are the behaviour of no code are not covered: all of their (zero) codes are both accepted and
rejected. The proof uses no classical reasoning (its only axiom is `propext`). -/
theorem exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible
    (hfix : FixpointPrinciple S) {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk) :
    ∀ a b, (∃ c, S.sem c = S.sem a ∧ chk c = false) ∨ (∃ c, S.sem c = S.sem b ∧ chk c = true) := by
  intro a b
  obtain ⟨c, hc⟩ := hfix _ (hsw b a)
  cases hchk : chk c with
  | true =>
    rw [switch_of_true hchk] at hc
    exact Or.inr ⟨c, hc.symm, hchk⟩
  | false =>
    rw [switch_of_false hchk] at hc
    exact Or.inl ⟨c, hc.symm, hchk⟩

/-- The negative form of the localized verdict split: for any codes `a` and `b`, not every code
with the behaviour of `a` is accepted while every code with the behaviour of `b` is rejected.
A constructive consequence of the localized split. -/
theorem not_forall_sameSem_accepted_and_forall_sameSem_rejected_of_fixpointPrinciple_switchAdmissible
    (hfix : FixpointPrinciple S) {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk)
    (a b : S.Code) :
    ¬ ((∀ c, S.sem c = S.sem a → chk c = true) ∧ (∀ c, S.sem c = S.sem b → chk c = false)) := by
  rintro ⟨hacc, hrej⟩
  rcases exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible
      hfix hsw a b with ⟨c, hc, hcr⟩ | ⟨c, hc, hca⟩
  · rw [hacc c hc] at hcr
    exact Bool.noConfusion hcr
  · rw [hrej c hc] at hca
    exact Bool.noConfusion hca

/-- For any checker and any codes `a` and `b`, the positive form of the verdict split (a rejected
code with the behaviour of `a` or an accepted code with the behaviour of `b`) is equivalent to the
negative form. The forward direction is constructive; the backward direction uses classical
logic. No hypothesis on the system is involved. -/
theorem sameSem_split_iff_not_forall_sameSem_accepted_and_forall_sameSem_rejected
    (chk : S.Code → Bool) (a b : S.Code) :
    ((∃ c, S.sem c = S.sem a ∧ chk c = false) ∨ (∃ c, S.sem c = S.sem b ∧ chk c = true)) ↔
      ¬ ((∀ c, S.sem c = S.sem a → chk c = true) ∧ (∀ c, S.sem c = S.sem b → chk c = false)) := by
  constructor
  · rintro (⟨c, hc, hcr⟩ | ⟨c, hc, hca⟩) ⟨hacc, hrej⟩
    · rw [hacc c hc] at hcr
      exact Bool.noConfusion hcr
    · rw [hrej c hc] at hca
      exact Bool.noConfusion hca
  · intro hnot
    apply Classical.byContradiction
    intro hno
    apply hnot
    constructor
    · intro c hc
      cases hcv : chk c with
      | true => rfl
      | false => exact absurd (Or.inl ⟨c, hc, hcv⟩) hno
    · intro c hc
      cases hcv : chk c with
      | false => rfl
      | true => exact absurd (Or.inr ⟨c, hc, hcv⟩) hno

/-- **Precise incompleteness, per behaviour.** In a system with the fixpoint principle, let `chk`
be a switch-admissible checker that is sound for an extensional predicate `P` that some code
violates. Then *every realizable* behaviour (the behaviour of some code) has a code that `chk`
rejects: for every code `a` some code with the behaviour of `a` is rejected. In particular the
behaviour of every code satisfying `P`, and the behaviour of every accepted code, contains a
rejected code. Elements of `S.Beh` that are the behaviour of no code are not covered. The proof
uses no classical reasoning (its only axiom is `propext`). -/
theorem forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hviol : ∃ b, ¬ P b) {chk : S.Code → Bool} (hsound : SoundFor chk P)
    (hsw : SwitchAdmissible S chk) :
    ∀ a, ∃ c, S.sem c = S.sem a ∧ chk c = false := by
  intro a
  obtain ⟨b, hb⟩ := hviol
  exact exists_sameSem_rejected_of_fixpointPrinciple_extensional_sound_swappedSwitch hfix hext
    hsound hb (hsw b a)

/-- The existential form of the precise incompleteness statement: a switch-admissible checker
that is sound for a nontrivial extensional predicate `P` rejects some code satisfying `P`.
A corollary of the per-behaviour form; no classical reasoning. -/
theorem exists_satisfying_rejected_of_fixpointPrinciple_extensional_nontrivial_sound_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hnt : NontrivialPred P) {chk : S.Code → Bool} (hsound : SoundFor chk P)
    (hsw : SwitchAdmissible S chk) :
    ∃ c, P c ∧ chk c = false := by
  obtain ⟨⟨a, ha⟩, hviol⟩ := hnt
  obtain ⟨c, hc, hrej⟩ :=
    forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible
      hfix hext hviol hsound hsw a
  exact ⟨c, (hext a c hc.symm).1 ha, hrej⟩

/-- The dual for complete checkers (false positives): in a system with the fixpoint principle, a
switch-admissible checker that is complete for an extensional predicate `P` that some code
satisfies accepts, for every code `b`, some code with the behaviour of `b` (every realizable
behaviour contains an accepted code); in particular the behaviour of every code violating `P`
contains an accepted code. No classical reasoning. -/
theorem forall_exists_sameSem_accepted_of_fixpointPrinciple_extensional_satisfied_complete_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    (hsat : ∃ a, P a) {chk : S.Code → Bool} (hcomp : CompleteFor chk P)
    (hsw : SwitchAdmissible S chk) :
    ∀ b, ∃ c, S.sem c = S.sem b ∧ chk c = true := by
  intro b
  obtain ⟨a, ha⟩ := hsat
  rcases exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible
      hfix hsw a b with ⟨c, hc, hcr⟩ | h
  · have hPc : P c := (hext a c hc.symm).1 ha
    have := hcomp c hPc
    rw [hcr] at this
    exact Bool.noConfusion this
  · exact h

/-- Existential form of the verdict split: a switch-admissible checker that accepts some code and
rejects some code gives different verdicts on two codes with the same behaviour. -/
theorem exists_sameSem_accepted_rejected_of_fixpointPrinciple_switchAdmissible
    (hfix : FixpointPrinciple S) {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk)
    (hacc : ∃ c, chk c = true) (hrej : ∃ d, chk d = false) :
    ∃ c d, S.sem c = S.sem d ∧ chk c = true ∧ chk d = false := by
  obtain ⟨a, ha⟩ := hacc
  obtain ⟨b, hb⟩ := hrej
  rcases exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible
      hfix hsw a b with ⟨c, hc, hcr⟩ | ⟨c, hc, hca⟩
  · exact ⟨a, c, hc.symm, ha, hcr⟩
  · exact ⟨c, b, hc, hca, hb⟩

/-- **Verdict split for sound checkers.** In a system with the fixpoint principle, a
switch-admissible checker that is sound for an extensional `P`, accepts some code and rejects some
code gives different verdicts on two codes with the same behaviour, both satisfying `P`. `P` need
not be nontrivial. The proof uses no classical reasoning (its only axiom is `propext`). -/
theorem exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible
    (hfix : FixpointPrinciple S) {P : S.Code → Prop} (hext : Extensional S P)
    {chk : S.Code → Bool} (hsound : SoundFor chk P) (hsw : SwitchAdmissible S chk)
    (hacc : ∃ c, chk c = true) (hrej : ∃ d, chk d = false) :
    ∃ c d, S.sem c = S.sem d ∧ P c ∧ P d ∧ chk c = true ∧ chk d = false := by
  obtain ⟨c, d, hcd, hc, hd⟩ :=
    exists_sameSem_accepted_rejected_of_fixpointPrinciple_switchAdmissible hfix hsw hacc hrej
  exact ⟨c, d, hcd, hsound c hc, (hext c d hcd).1 (hsound c hc), hc, hd⟩

/-! ## Restriction to a fragment closed under behaviour -/

/-- **Rice for behaviour-closed fragments.** Let `S` have the fixpoint principle and let its
admissible transformers be closed under literal code-equality tests (`EqTestClosed`). Let `F` be
a fragment closed under same behaviour (`Extensional S F`; for example "the program halts"). Then
no predicate that is extensional and nontrivial *on the fragment* is decided inside the
restricted system `S.restrict F`. Restricting to such a fragment does not escape Rice. -/
theorem not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial
    (hfix : FixpointPrinciple S) (heq : EqTestClosed S) {F : S.Code → Prop}
    (hF : Extensional S F) {P : S.Code → Prop}
    (hext : Extensional (S.restrict F) (fun x => P x.val))
    (hnt : NontrivialPred (fun x : {c // F c} => P x.val)) :
    ¬ DecidedInside (S.restrict F) (fun x => P x.val) := by
  rintro ⟨chk, hdec, hsw⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hnt
  obtain ⟨f, hf, hfg⟩ := hsw a b
  have hab : a.val ≠ b.val := fun h => hb (by
    have : a = b := Subtype.ext h
    rw [← this]; exact ha)
  obtain ⟨c, hc⟩ := hfix _ (heq f hf a.val b.val a.val)
  by_cases hfc : f c = a.val
  · -- the test succeeds: `c` behaves like `b`
    have hcb : S.sem b.val = S.sem c := by
      have : (@ite _ (f c = a.val) (Classical.propDecidable _) b.val a.val) = b.val := by
        simp [hfc]
      rw [this] at hc; exact hc
    have hFc : F c := (hF b.val c hcb).1 b.2
    have hval : (cond (chk ⟨c, hFc⟩) a b).val = f c := hfg ⟨c, hFc⟩
    cases hchk : chk ⟨c, hFc⟩ with
    | true =>
      have hPc : P c := (hdec ⟨c, hFc⟩).1 hchk
      exact hb ((hext b ⟨c, hFc⟩ hcb).2 hPc)
    | false =>
      rw [hchk] at hval
      exact hab (hfc.symm.trans hval.symm)
  · -- the test fails: `c` behaves like `a`
    have hca : S.sem a.val = S.sem c := by
      have : (@ite _ (f c = a.val) (Classical.propDecidable _) b.val a.val) = a.val := by
        simp [hfc]
      rw [this] at hc; exact hc
    have hFc : F c := (hF a.val c hca).1 a.2
    have hval : (cond (chk ⟨c, hFc⟩) a b).val = f c := hfg ⟨c, hFc⟩
    cases hchk : chk ⟨c, hFc⟩ with
    | true =>
      rw [hchk] at hval
      exact hfc hval.symm
    | false =>
      have hPc : P c := (hext a ⟨c, hFc⟩ hca).1 ha
      have := (hdec ⟨c, hFc⟩).2 hPc
      rw [hchk] at this
      exact Bool.noConfusion this

end Toy.Rice
