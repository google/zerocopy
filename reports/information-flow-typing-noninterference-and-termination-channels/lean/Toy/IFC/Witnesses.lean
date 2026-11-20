import Toy.IFC.Core
import Toy.IFC.Typing
import Toy.IFC.Hyperproperties
import Toy.IFC.Results

/-!
# Tightness Counterexamples, Non-Vacuity Witnesses, Positive Controls, and Non-Claim Lemmas

Every theorem in this module is fully proved (zero `sorry`, standard axioms only)
and establishes:
- canonical counterexamples for every `tight` hypothesis of the main results,
  using non-degenerate mixed security environments whenever possible (so neither
  `LowEq` nor noninterference collapses trivially);
- non-vacuity witnesses demonstrating that the hypotheses of every result hold
  jointly in concrete intended instances;
- positive controls showing that restoring a dropped constraint blocks the
  counterexample or restores the desired property;
- kernel-checked lemmas substantiating semantic claims made in result non-claims
  (repeated-run termination leakage, incompleteness witnesses, `pc`-sensitivity
  of `TsTyped` on `while 1 do skip`, and why determinism is needed in
  `tsni_iff_tini_and_coterminates`).
-/

namespace Toy.IFC

/-- Three-variable domain used to construct non-degenerate mixed-level tightness
    counterexamples where distinct variables exist AND both `low` and `high`
    variables remain present in the environment. -/
inductive ThreeVar where
  | l
  | m
  | h
  deriving DecidableEq, Repr

/-- Mixed labeling with one `low` (`l`) and two `high` (`m`, `h`) variables. -/
def mixedHighEnv : ThreeVar → Level
  | .l => .low
  | .m => .high
  | .h => .high

/-- Mixed labeling with two `low` (`l`, `m`) and one `high` (`h`) variable. -/
def mixedLowEnv : ThreeVar → Level
  | .l => .low
  | .m => .low
  | .h => .high

/-- All-`low` labeling on `TwoVar` (used for the exact boundary of
    `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`, where absence of any
    `high` variable is necessary and sufficient for subset closure). -/
def allLowEnv : TwoVar → Level := fun _ => .low

/-! ### Tightness Counterexamples (Canonical Form) -/

/-- Tightness counterexample for `hTyped` (explicit-flow rule) in
    `cmdTyped_implies_tini`: `explicitFlowProg .l .h` (`l := h`) is rejected by
    `CmdTyped` at every `pc` and violates `TINI`. -/
theorem untyped_explicit_flow_violates_tini :
    (∀ pc, ¬ CmdTyped twoVarEnv pc (explicitFlowProg .l .h)) ∧
    ¬ TINI twoVarEnv (explicitFlowProg .l .h) :=
  ⟨cmdTyped_neg_explicit_flow, tini_neg_explicit_flow⟩

/-- Tightness counterexample for `hTyped` (program-counter tracking) in
    `cmdTyped_implies_tini`: dropping `pc` tracking (`NoPcTyped`) accepts
    `implicitFlowProg .l .h`, which is rejected by `CmdTyped` at every `pc`
    and violates `TINI`. -/
theorem noPcTyped_violates_tini_witness :
    NoPcTyped twoVarEnv (implicitFlowProg .l .h) ∧
    (∀ pc, ¬ CmdTyped twoVarEnv pc (implicitFlowProg .l .h)) ∧
    ¬ TINI twoVarEnv (implicitFlowProg .l .h) :=
  ⟨noPcTyped_pos_implicit_flow, cmdTyped_neg_implicit_flow,
   (noPcTyped_accepts_implicit_flow_violating_tini (Γ := twoVarEnv) (l := .l) (h := .h) rfl rfl).2⟩

/-- Tightness counterexample for `hTyped` (`pc` tracking at `while`) in
    `cmdTyped_implies_tini`: keeping `pc` on `if` while dropping `pc` at `while`
    (`WhileNoPcTyped`) accepts `whileLeakProg .l .h`, which is rejected by
    `CmdTyped` at every `pc` and violates `TINI`. -/
theorem whileNoPcTyped_violates_tini_witness :
    WhileNoPcTyped twoVarEnv .low (whileLeakProg .l .h) ∧
    (∀ pc, ¬ CmdTyped twoVarEnv pc (whileLeakProg .l .h)) ∧
    ¬ TINI twoVarEnv (whileLeakProg .l .h) := by
  refine ⟨whileNoPcTyped_pos_whileLeakProg, ?_,
    (whileNoPcTyped_accepts_leak_violating_tini (Γ := twoVarEnv) (l := .l) (h := .h) rfl rfl).2⟩
  intro pc ht
  cases ht with
  | whileLoop hb =>
    cases hb with
    | seq hl _ =>
      cases hl with
      | assign _ hpc =>
        simp only [exprLevel, twoVarEnv, Level.join_high_right] at hpc
        exact hpc

/-- Tightness counterexample for `hTyped` in `cmdTyped_implies_tiniHyperprop`:
    `explicitFlowProg .l .h` is rejected by `CmdTyped` at every `pc` and its
    terminating I/O behavior fails `tiniHyperprop`. -/
theorem untyped_explicit_flow_violates_tiniHyperprop :
    (∀ pc, ¬ CmdTyped twoVarEnv pc (explicitFlowProg .l .h)) ∧
    ¬ tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg .l .h)) :=
  ⟨cmdTyped_neg_explicit_flow, tiniHyperprop_neg_explicit_flow⟩

/-- Tightness counterexample for `hLow` in `noPcTyped_accepts_implicit_flow_violating_tini`:
    in the non-degenerate mixed environment `mixedHighEnv` (where `.l` is still `low`),
    keeping `mixedHighEnv .h = .high` while setting the distinct target `.m` to `high`
    makes `implicitFlowProg .m .h` satisfy `TINI`, so the conclusion fails. -/
theorem implicitFlowProg_target_high_satisfies_tini :
    mixedHighEnv .h = .high ∧
    TINI mixedHighEnv (implicitFlowProg .m .h) ∧
    ¬ (NoPcTyped mixedHighEnv (implicitFlowProg .m .h) ∧
       ¬ TINI mixedHighEnv (implicitFlowProg .m .h)) := by
  have hTini : TINI mixedHighEnv (implicitFlowProg .m .h) := by
    intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
    have hPres₁ : LowEq mixedHighEnv σ₁ σ₁' := by
      cases h₁ with
      | iteTrue _ hb =>
        cases hb
        exact LowEq.update_high 1 rfl
      | iteFalse _ hb =>
        cases hb
        exact LowEq.update_high 0 rfl
    have hPres₂ : LowEq mixedHighEnv σ₂ σ₂' := by
      cases h₂ with
      | iteTrue _ hb =>
        cases hb
        exact LowEq.update_high 1 rfl
      | iteFalse _ hb =>
        cases hb
        exact LowEq.update_high 0 rfl
    exact hPres₁.symm.trans (hLow.trans hPres₂)
  exact ⟨rfl, hTini, fun ⟨_, hNot⟩ => hNot hTini⟩

/-- Tightness counterexample for `hHigh` in `noPcTyped_accepts_implicit_flow_violating_tini`:
    in the non-degenerate mixed environment `mixedLowEnv` (where `.h` is still `high`),
    keeping `mixedLowEnv .l = .low` while setting the distinct guard `.m` to `low`
    makes `implicitFlowProg .l .m` satisfy `TINI`, so the conclusion fails. -/
theorem implicitFlowProg_guard_low_satisfies_tini :
    mixedLowEnv .l = .low ∧
    TINI mixedLowEnv (implicitFlowProg .l .m) ∧
    ¬ (NoPcTyped mixedLowEnv (implicitFlowProg .l .m) ∧
       ¬ TINI mixedLowEnv (implicitFlowProg .l .m)) := by
  have hTini : TINI mixedLowEnv (implicitFlowProg .l .m) := by
    intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
    have hm : σ₁ .m = σ₂ .m := hLow .m rfl
    cases h₁ with
    | iteTrue hne₁ hb₁ =>
      cases h₂ with
      | iteTrue _ hb₂ =>
        cases hb₁; cases hb₂
        intro x hx
        by_cases hxl : x = .l
        · subst hxl; simp [eval, Store.update]
        · simp [Store.update, hxl, hLow x hx]
      | iteFalse heq₂ _ =>
        simp [eval, hm] at hne₁ heq₂
        exact absurd heq₂ hne₁
    | iteFalse heq₁ hb₁ =>
      cases h₂ with
      | iteTrue hne₂ _ =>
        simp [eval, hm] at heq₁ hne₂
        exact absurd heq₁ hne₂
      | iteFalse _ hb₂ =>
        cases hb₁; cases hb₂
        intro x hx
        by_cases hxl : x = .l
        · subst hxl; simp [eval, Store.update]
        · simp [Store.update, hxl, hLow x hx]
  exact ⟨rfl, hTini, fun ⟨_, hNot⟩ => hNot hTini⟩

/-- Helper: executing `whileLeakProg .m .h` under `mixedHighEnv` (where both `.m`
    and `.h` are `high`) preserves `LowEq mixedHighEnv`. -/
private theorem whileLeakProg_mixedHigh_preserves_lowEq
    {σ σ' : Store ThreeVar} (hEval : Eval (whileLeakProg .m .h) σ σ') :
    LowEq mixedHighEnv σ σ' := by
  suffices ∀ {c s s'}, Eval c s s' → c = whileLeakProg .m .h → LowEq mixedHighEnv s s' from
    this hEval rfl
  intro c s s' h
  induction h with
  | whileFalse _ =>
    intro _
    exact LowEq.refl _ _
  | whileTrue _ hBody _ _ ihLoop =>
    intro hc
    cases hc
    cases hBody with
    | seq hA hB =>
      cases hA
      cases hB
      exact (LowEq.update_high (Γ := mixedHighEnv) (h := .m) 1 rfl).trans
        ((LowEq.update_high (Γ := mixedHighEnv) (h := .h) 0 rfl).trans (ihLoop rfl))
  | _ =>
    intro hc
    cases hc

/-- Tightness counterexample for `hLow` in `whileNoPcTyped_accepts_leak_violating_tini`:
    in the non-degenerate mixed environment `mixedHighEnv`, keeping
    `mixedHighEnv .h = .high` while setting target `.m` to `high` makes
    `whileLeakProg .m .h` satisfy `TINI`, so the conclusion fails. -/
theorem whileLeakProg_target_high_satisfies_tini :
    mixedHighEnv .h = .high ∧
    TINI mixedHighEnv (whileLeakProg .m .h) ∧
    ¬ (WhileNoPcTyped mixedHighEnv .low (whileLeakProg .m .h) ∧
       ¬ TINI mixedHighEnv (whileLeakProg .m .h)) := by
  have hTini : TINI mixedHighEnv (whileLeakProg .m .h) := by
    intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
    have p₁ := whileLeakProg_mixedHigh_preserves_lowEq h₁
    have p₂ := whileLeakProg_mixedHigh_preserves_lowEq h₂
    exact p₁.symm.trans (hLow.trans p₂)
  exact ⟨rfl, hTini, fun ⟨_, hNot⟩ => hNot hTini⟩

/-- Tightness counterexample for `hHigh` in `whileNoPcTyped_accepts_leak_violating_tini`:
    in the non-degenerate mixed environment `mixedLowEnv`, keeping
    `mixedLowEnv .l = .low` while setting guard `.m` to `low` makes
    `whileLeakProg .l .m` satisfy `TINI`, so the conclusion fails. -/
theorem whileLeakProg_guard_low_satisfies_tini :
    mixedLowEnv .l = .low ∧
    TINI mixedLowEnv (whileLeakProg .l .m) ∧
    ¬ (WhileNoPcTyped mixedLowEnv .low (whileLeakProg .l .m) ∧
       ¬ TINI mixedLowEnv (whileLeakProg .l .m)) := by
  have hTini : TINI mixedLowEnv (whileLeakProg .l .m) := by
    intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
    have hm : σ₁ .m = σ₂ .m := hLow .m rfl
    cases h₁ with
    | whileFalse heq₁ =>
      cases h₂ with
      | whileFalse _ => exact hLow
      | whileTrue hne₂ _ _ =>
        simp [eval, hm] at heq₁ hne₂
        exact absurd heq₁ hne₂
    | whileTrue hne₁ hBody₁ hLoop₁ =>
      cases h₂ with
      | whileFalse heq₂ =>
        simp [eval, hm] at hne₁ heq₂
        exact absurd heq₂ hne₁
      | whileTrue _ hBody₂ hLoop₂ =>
        cases hBody₁ with
        | seq hA₁ hB₁ =>
          cases hA₁; cases hB₁
          cases hLoop₁ with
          | whileFalse _ =>
            cases hBody₂ with
            | seq hA₂ hB₂ =>
              cases hA₂; cases hB₂
              cases hLoop₂ with
              | whileFalse _ =>
                intro x hx
                cases x with
                | l => simp [eval, Store.update]
                | m => simp [eval, Store.update]
                | h => cases hx
              | whileTrue hne₂' _ _ =>
                simp [eval, Store.update] at hne₂'
          | whileTrue hne₁' _ _ =>
            simp [eval, Store.update] at hne₁'
  exact ⟨rfl, hTini, fun ⟨_, hNot⟩ => hNot hTini⟩

/-- Tightness counterexample for `hHigh` in `cmdTyped_allows_termination_channel`:
    in the non-degenerate mixed environment `twoVarEnv` (where `.h` is still `high`),
    dropping `Γ x = high` by taking the `low` variable `.l` makes
    `termChannelProg .l` (`while l do skip`) satisfy `TSNI`, so the conclusion fails. -/
theorem termChannelProg_low_guard_satisfies_tsni :
    twoVarEnv TwoVar.l = .low ∧
    TSNI twoVarEnv (termChannelProg TwoVar.l) ∧
    ¬ (CmdTyped twoVarEnv .low (termChannelProg TwoVar.l) ∧
       LowEq twoVarEnv zeroStore (Store.update zeroStore TwoVar.l 1) ∧
       Terminates (termChannelProg TwoVar.l) zeroStore ∧
       ¬ Terminates (termChannelProg TwoVar.l) (Store.update zeroStore TwoVar.l 1) ∧
       ¬ TSNI twoVarEnv (termChannelProg TwoVar.l)) := by
  have hTsni : TSNI twoVarEnv (termChannelProg TwoVar.l) := by
    intro σ₁ σ₂ σ₁' hLow h₁
    match h₁ with
    | .whileFalse heq =>
      have hl : σ₁ TwoVar.l = σ₂ TwoVar.l := hLow TwoVar.l rfl
      have heq₂ : eval σ₂ (.var TwoVar.l) = 0 := by simpa [eval, hl] using heq
      exact ⟨σ₂, Eval.whileFalse heq₂, hLow⟩
    | h₁@(.whileTrue hne _ _) =>
      exact False.elim (while_skip_no_eval h₁ hne)
  exact ⟨rfl, hTsni, fun ⟨_, _, _, _, hNot⟩ => hNot hTsni⟩

/-- Tightness counterexample for `hHigh` in `pcLowWhileTyped_allows_termination_channel`:
    in `twoVarEnv`, taking the `low` variable `.l` makes `termChannelProg .l`
    satisfy `TSNI`, so the conclusion fails. -/
theorem termChannelProg_low_guard_satisfies_tsni_pcLow :
    twoVarEnv TwoVar.l = .low ∧
    TSNI twoVarEnv (termChannelProg TwoVar.l) ∧
    ¬ (PcLowWhileTyped twoVarEnv .low (termChannelProg TwoVar.l) ∧
       LowEq twoVarEnv zeroStore (Store.update zeroStore TwoVar.l 1) ∧
       Terminates (termChannelProg TwoVar.l) zeroStore ∧
       ¬ Terminates (termChannelProg TwoVar.l) (Store.update zeroStore TwoVar.l 1) ∧
       ¬ TSNI twoVarEnv (termChannelProg TwoVar.l)) :=
  ⟨rfl, termChannelProg_low_guard_satisfies_tsni.2.1,
   fun ⟨_, _, _, _, hNot⟩ => hNot termChannelProg_low_guard_satisfies_tsni.2.1⟩

/-- Tightness counterexample for `hHigh` in `lowGuardWhileTyped_allows_termination_channel`:
    in the non-degenerate mixed environment `twoVarEnv` (where `.h` is still `high`),
    dropping `Γ x = high` by taking the `low` variable `.l` makes
    `highIfLowWhileProg .l` (`if l then (while 1 do skip) else skip`) satisfy `TSNI`,
    so the conclusion fails. -/
theorem highIfLowWhileProg_low_guard_satisfies_tsni :
    twoVarEnv TwoVar.l = .low ∧
    TSNI twoVarEnv (highIfLowWhileProg TwoVar.l) ∧
    ¬ (LowGuardWhileTyped twoVarEnv .low (highIfLowWhileProg TwoVar.l) ∧
       LowEq twoVarEnv zeroStore (Store.update zeroStore TwoVar.l 1) ∧
       Terminates (highIfLowWhileProg TwoVar.l) zeroStore ∧
       ¬ Terminates (highIfLowWhileProg TwoVar.l) (Store.update zeroStore TwoVar.l 1) ∧
       ¬ TSNI twoVarEnv (highIfLowWhileProg TwoVar.l)) := by
  have hTsni : TSNI twoVarEnv (highIfLowWhileProg TwoVar.l) := by
    intro σ₁ σ₂ σ₁' hLow h₁
    cases h₁ with
    | iteTrue _ hLoop =>
      exact False.elim (while_skip_no_eval hLoop (by simp [eval]))
    | iteFalse heq hSkip =>
      cases hSkip
      have hl : σ₁ TwoVar.l = σ₂ TwoVar.l := hLow TwoVar.l rfl
      have heq₂ : eval σ₂ (.var TwoVar.l) = 0 := by simpa [eval, hl] using heq
      exact ⟨σ₂, Eval.iteFalse heq₂ Eval.skip, hLow⟩
  exact ⟨rfl, hTsni, fun ⟨_, _, _, _, hNot⟩ => hNot hTsni⟩

/-- Tightness counterexample for `h2` in `isTwoSafety_implies_subsetClosed`:
    `nonEmptyTraceSet` fails `IsTwoSafety` and fails `SubsetClosed`. -/
theorem nonEmptyTraceSet_not_subsetClosed :
    ¬ IsTwoSafety (nonEmptyTraceSet (α := Unit)) ∧
    ¬ SubsetClosed (nonEmptyTraceSet (α := Unit)) :=
  ⟨fun h2 => subsetClosed_neg_nonEmpty (isTwoSafety_implies_subsetClosed h2),
   subsetClosed_neg_nonEmpty⟩

/-- Tightness counterexample for `hHigh` in
    `tsniHyperprop_termPairs_not_subsetClosed_of_high_var` (degenerate all-`low`
    policy boundary): when all variables are `low`, `tsniHyperprop` IS
    subset-closed (and 2-safety), so `¬ SubsetClosed` fails. -/
theorem tsniHyperprop_all_low_subsetClosed_witness :
    SubsetClosed (tsniHyperprop allLowEnv) :=
  tsniHyperprop_all_low_subsetClosed (fun _ => rfl)

/-- Tightness counterexample for `hHigh` in the corollary
    `tsniHyperprop_termPairs_not_twoSafety_of_high_var`: when all variables are
    `low`, `tsniHyperprop` satisfies `IsTwoSafety`, refuting `¬ IsTwoSafety`. -/
theorem tsniHyperprop_all_low_isTwoSafety_witness :
    IsTwoSafety (tsniHyperprop allLowEnv) :=
  tsniHyperprop_all_low_isTwoSafety (fun _ => rfl)

/-- Tightness counterexample for base `CmdTyped` rules inside `tsTyped_implies_tsni`:
    `explicitFlowProg .l .h` is rejected by `TsTyped` and `CmdTyped` at every
    `pc`, and violates `TSNI` (even though it terminates on every store). -/
theorem untyped_explicit_flow_violates_tsni :
    (∀ pc, ¬ TsTyped twoVarEnv pc (explicitFlowProg .l .h)) ∧
    (∀ pc, ¬ CmdTyped twoVarEnv pc (explicitFlowProg .l .h)) ∧
    ¬ TSNI twoVarEnv (explicitFlowProg .l .h) :=
  ⟨fun pc h => cmdTyped_neg_explicit_flow pc (tsTyped_implies_cmdTyped h),
   cmdTyped_neg_explicit_flow,
   fun hTsni => tini_neg_explicit_flow ((tsni_iff_tini_and_coterminates twoVarEnv _).mp hTsni).1⟩

/-- Tightness counterexample for conditional `pc` tracking inside the base rules
    of `tsTyped_implies_tsni`: the loop-free `implicitFlowProg .l .h` satisfies
    explicit-flow bounds (`NoPcTyped`), is rejected by `TsTyped` at every `pc`,
    and violates `TSNI`. -/
theorem noPcTyped_implicit_flow_violates_tsni_witness :
    NoPcTyped twoVarEnv (implicitFlowProg .l .h) ∧
    (∀ pc, ¬ TsTyped twoVarEnv pc (implicitFlowProg .l .h)) ∧
    ¬ TSNI twoVarEnv (implicitFlowProg .l .h) :=
  ⟨noPcTyped_pos_implicit_flow,
   fun pc ht => cmdTyped_neg_implicit_flow pc (tsTyped_implies_cmdTyped ht),
   fun hT => (noPcTyped_accepts_implicit_flow_violating_tini
      (Γ := twoVarEnv) (l := .l) (h := .h) rfl rfl).2
      ((tsni_iff_tini_and_coterminates twoVarEnv _).mp hT).1⟩

/-- Tightness counterexample for dropping both `while` conjuncts of `TsTyped`
    (relaxing to `CmdTyped`): `termChannelProg .h` is accepted by `CmdTyped`,
    rejected by `TsTyped` at every `pc`, and violates `TSNI`. -/
theorem cmdTyped_violates_tsni_witness :
    CmdTyped twoVarEnv .low (termChannelProg .h) ∧
    (∀ pc, ¬ TsTyped twoVarEnv pc (termChannelProg .h)) ∧
    ¬ TSNI twoVarEnv (termChannelProg .h) :=
  ⟨cmdTyped_pos_while_h, tsTyped_neg_while_h, tsni_neg_while_h⟩

/-- Tightness counterexample for the `exprLevel Γ e = low` conjunct of `TsTyped.whileLoop`
    in isolation (keeping `pc = low` via `PcLowWhileTyped`): `termChannelProg .h`
    is accepted by `PcLowWhileTyped`, rejected by `TsTyped` at every `pc`, and
    violates `TSNI`. -/
theorem pcLowWhileTyped_violates_tsni_witness :
    PcLowWhileTyped twoVarEnv .low (termChannelProg .h) ∧
    (∀ pc, ¬ TsTyped twoVarEnv pc (termChannelProg .h)) ∧
    ¬ TSNI twoVarEnv (termChannelProg .h) :=
  ⟨pcLowWhileTyped_pos_while_h, tsTyped_neg_while_h, tsni_neg_while_h⟩

/-- Tightness counterexample for the `pc = low` conjunct of `TsTyped.whileLoop`
    in isolation (keeping `exprLevel Γ e = low` via `LowGuardWhileTyped`):
    `highIfLowWhileProg .h` is accepted by `LowGuardWhileTyped`, rejected by
    `TsTyped` at every `pc`, and violates `TSNI`. -/
theorem lowGuardWhileTyped_violates_tsni_witness :
    LowGuardWhileTyped twoVarEnv .low (highIfLowWhileProg .h) ∧
    (∀ pc, ¬ TsTyped twoVarEnv pc (highIfLowWhileProg .h)) ∧
    ¬ TSNI twoVarEnv (highIfLowWhileProg .h) :=
  ⟨lowGuardWhileTyped_pos_high_if_low_while, tsTyped_neg_high_if_low_while,
   (lowGuardWhileTyped_allows_termination_channel (Γ := twoVarEnv) (pc := .low) (h := .h) rfl).2.2.2.2⟩

/-! ### Positive Controls (Fully Proved) -/

/-- Positive control for `noPcTyped_accepts_implicit_flow_violating_tini`:
    restoring the `pc` rule (`CmdTyped`) rejects `implicitFlowProg l h` at every
    program-counter level `pc`. -/
theorem implicitFlowProg_rejected_by_cmdTyped
    {Var : Type} {Γ : Var → Level} {l h : Var}
    (hLow : Γ l = .low) (hHigh : Γ h = .high) (pc : Level) :
    ¬ CmdTyped Γ pc (implicitFlowProg l h) := by
  intro ht
  cases ht with
  | ite h₁ _ =>
    cases h₁ with
    | assign _ hpc =>
      simp only [exprLevel, hHigh, Level.join_high_right, hLow] at hpc
      exact hpc

/-- Positive control for `whileNoPcTyped_accepts_leak_violating_tini`:
    restoring `pc` raising at `while` (`CmdTyped`) rejects `whileLeakProg l h`
    at every `pc`. -/
theorem whileLeakProg_rejected_by_cmdTyped
    {Var : Type} {Γ : Var → Level} {l h : Var}
    (hLow : Γ l = .low) (hHigh : Γ h = .high) (pc : Level) :
    ¬ CmdTyped Γ pc (whileLeakProg l h) := by
  intro ht
  cases ht with
  | whileLoop hb =>
    cases hb with
    | seq hl _ =>
      cases hl with
      | assign _ hpc =>
        simp only [exprLevel, hHigh, Level.join_high_right, hLow] at hpc
        exact hpc

/-- Positive control for `cmdTyped_allows_termination_channel` and
    `pcLowWhileTyped_allows_termination_channel`: strengthening to `TsTyped`
    rejects `termChannelProg h` at every `pc`. -/
theorem termChannelProg_rejected_by_tsTyped
    {Var : Type} {Γ : Var → Level} {h : Var}
    (hHigh : Γ h = .high) (pc : Level) :
    ¬ TsTyped Γ pc (termChannelProg h) := by
  intro ht
  cases ht with
  | whileLoop _ he _ =>
    simp [exprLevel, hHigh] at he

/-- Positive control for `lowGuardWhileTyped_allows_termination_channel`:
    adding the `pc = low` requirement (`TsTyped`) rejects `highIfLowWhileProg h`
    at every `pc`. -/
theorem highIfLowWhileProg_rejected_by_tsTyped
    {Var : Type} {Γ : Var → Level} {h : Var}
    (hHigh : Γ h = .high) (pc : Level) :
    ¬ TsTyped Γ pc (highIfLowWhileProg h) := by
  intro ht
  cases ht with
  | ite h₁ _ =>
    cases h₁ with
    | whileLoop hpc _ _ =>
      simp [exprLevel, hHigh] at hpc

/-! ### Non-Vacuity Witnesses (Fully Proved) -/

/-- Non-vacuity witness for `cmdTyped_implies_tini` and `cmdTyped_implies_tiniHyperprop`:
    `sampleTypedProg` is well typed under `CmdTyped twoVarEnv .low`, and two
    low-equivalent stores with distinct secret inputs (`storeZero` and `storeHighOne`)
    both terminate in distinct final stores whose low component advances from `0` to `1`. -/
theorem cmdTyped_implies_tini_nonvacuous :
    CmdTyped twoVarEnv .low sampleTypedProg ∧
    LowEq twoVarEnv storeZero storeHighOne ∧
    Eval sampleTypedProg storeZero storeLowOne ∧
    Eval sampleTypedProg storeHighOne
      (Store.update (Store.update storeHighOne .h 2) .l 1) := by
  refine ⟨cmdTyped_pos_sampleTypedProg, lowEq_pos_high_diff, ?_, ?_⟩
  · apply Eval.seq (σm := storeZero)
    · apply Eval.iteFalse (by simp [eval, storeZero, zeroStore])
      have hEq : Store.update storeZero .h (eval storeZero (.lit 0)) = storeZero := by
        funext x
        cases x <;> simp [eval, storeZero, zeroStore, Store.update]
      exact Eq.mp (congrArg (Eval (.assign .h (.lit 0)) storeZero) hEq) Eval.assign
    · have hEq : Store.update storeZero .l (eval storeZero (.add (.var .l) (.lit 1))) = storeLowOne := by
        funext x
        cases x <;> simp [eval, storeZero, storeLowOne, zeroStore, Store.update]
      exact hEq ▸ (Eval.assign (x := .l) (e := .add (.var .l) (.lit 1)) (σ := storeZero))
  · apply Eval.seq (σm := Store.update storeHighOne .h 2)
    · apply Eval.iteTrue (by simp [eval, storeHighOne, Store.update])
      have hEq : Store.update storeHighOne .h (eval storeHighOne (.add (.var .h) (.lit 1))) =
          Store.update storeHighOne .h 2 := by
        funext x
        cases x <;> simp [eval, storeHighOne, Store.update]
      exact hEq ▸ (Eval.assign (x := .h) (e := .add (.var .h) (.lit 1)) (σ := storeHighOne))
    · have hEq :
          Store.update (Store.update storeHighOne .h 2) .l
            (eval (Store.update storeHighOne .h 2) (.add (.var .l) (.lit 1))) =
          Store.update (Store.update storeHighOne .h 2) .l 1 := by
        funext x
        cases x <;> simp [eval, storeHighOne, storeZero, zeroStore, Store.update]
      exact hEq ▸ (Eval.assign (x := .l) (e := .add (.var .l) (.lit 1))
        (σ := Store.update storeHighOne .h 2))

/-- Second non-vacuity witness for `cmdTyped_implies_tini` and
    `cmdTyped_implies_tiniHyperprop`: exercises a high-guarded `while` loop
    (`whileHZero := while h do h := 0`) accepted by `CmdTyped` (and rejected by
    `TsTyped`) that terminates on two low-equivalent stores taking different
    numbers of iterations (`0` vs. `1`). -/
theorem cmdTyped_implies_tini_nonvacuous_highLoop :
    CmdTyped twoVarEnv .low whileHZero ∧
    LowEq twoVarEnv storeZero storeHighOne ∧
    Eval whileHZero storeZero storeZero ∧
    Eval whileHZero storeHighOne storeZero := by
  refine ⟨CmdTyped.antitone (Level.le_high _) whileHZero_cmdTyped_high, lowEq_pos_high_diff,
    .whileFalse (by simp [eval, storeZero, zeroStore]), ?_⟩
  have hEq : Store.update storeHighOne .h (eval storeHighOne (.lit 0)) = storeZero := by
    funext x
    cases x <;> simp [eval, storeHighOne, storeZero, zeroStore, Store.update]
  exact .whileTrue (σm := storeZero) (by simp [eval, storeHighOne, Store.update])
    (hEq ▸ (Eval.assign (x := .h) (e := .lit 0) (σ := storeHighOne)))
    (.whileFalse (by simp [eval, storeZero, zeroStore]))

/-- Non-vacuity witness for `noPcTyped_accepts_implicit_flow_violating_tini` and
    `whileNoPcTyped_accepts_leak_violating_tini`: `twoVarEnv` provides concrete
    `low` and `high` variables. -/
theorem noPcTyped_implicit_flow_nonvacuous :
    twoVarEnv .l = .low ∧ twoVarEnv .h = .high :=
  ⟨rfl, rfl⟩

/-- Non-vacuity witness for `cmdTyped_allows_termination_channel`,
    `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`,
    `lowGuardWhileTyped_allows_termination_channel`, and
    `pcLowWhileTyped_allows_termination_channel`: `twoVarEnv` provides a
    concrete `high` variable. -/
theorem high_var_nonvacuous : twoVarEnv .h = .high := rfl

/-- Non-vacuity witness for `isTwoSafety_implies_subsetClosed`:
    `tiniHyperprop twoVarEnv` satisfies `IsTwoSafety`. -/
theorem isTwoSafety_implies_subsetClosed_nonvacuous :
    IsTwoSafety (tiniHyperprop twoVarEnv) :=
  tiniHyperprop_isTwoSafety twoVarEnv

/-- Non-vacuity witness for `tiniHyperprop_isTwoSafety`:
    `tiniHyperprop twoVarEnv` is a nontrivial hyperproperty (admitting
    `ioBehavior .skip` and rejecting `ioBehavior (explicitFlowProg .l .h)`). -/
theorem tiniHyperprop_isTwoSafety_nonvacuous :
    tiniHyperprop twoVarEnv (ioBehavior .skip) ∧
    ¬ tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg .l .h)) :=
  ⟨tiniHyperprop_pos_skip, tiniHyperprop_neg_explicit_flow⟩

/-- Non-vacuity witness for `tsni_iff_tsniOutHyperprop` /
    `tsniOutHyperprop_isTwoSafety`: under the mixed environment `twoVarEnv`,
    `tsniOutHyperprop twoVarEnv` is nontrivial (accepting `outcomeBehavior .skip`
    and rejecting `outcomeBehavior (termChannelProg .h)`). -/
theorem tsniOutHyperprop_nonvacuous :
    tsniOutHyperprop twoVarEnv (outcomeBehavior .skip) ∧
    ¬ tsniOutHyperprop twoVarEnv (outcomeBehavior (termChannelProg .h)) :=
  ⟨tsniOutHyperprop_pos_skip, tsniOutHyperprop_neg_while_h⟩

/-- Non-vacuity witness for `tsTyped_implies_tsni`:
    `sampleTsProg` is well typed under `TsTyped twoVarEnv .low`, and two
    low-equivalent stores (`storeLowOne` with `l=1, h=0`, and `l=1, h=5`) both
    enter the loop, take opposite `high` branches, and terminate. -/
theorem tsTyped_implies_tsni_nonvacuous :
    TsTyped twoVarEnv .low sampleTsProg ∧
    LowEq twoVarEnv storeLowOne (Store.update storeLowOne .h 5) ∧
    Eval sampleTsProg storeLowOne storeZero ∧
    Eval sampleTsProg (Store.update storeLowOne .h 5) (Store.update storeZero .h 4) := by
  refine ⟨tsTyped_pos_sampleTsProg, LowEq.update_high 5 rfl, ?_, ?_⟩
  · -- Execution from `storeLowOne` (`l = 1, h = 0`)
    apply Eval.whileTrue (σm := storeZero)
    · simp [eval, storeLowOne, Store.update]
    · apply Eval.seq (σm := storeLowOne)
      · apply Eval.iteFalse (by simp [eval, storeLowOne, storeZero, zeroStore, Store.update])
        have hEq : Store.update storeLowOne .h (eval storeLowOne (.lit 0)) = storeLowOne := by
          funext x
          cases x <;> simp [eval, storeLowOne, storeZero, zeroStore, Store.update]
        exact Eq.mp (congrArg (Eval (.assign .h (.lit 0)) storeLowOne) hEq) Eval.assign
      · have hEq : Store.update storeLowOne .l (eval storeLowOne (.sub (.var .l) (.lit 1))) =
            storeZero := by
          funext x
          cases x <;> simp [eval, storeLowOne, storeZero, zeroStore, Store.update]
        exact hEq ▸ (Eval.assign (x := .l) (e := .sub (.var .l) (.lit 1)) (σ := storeLowOne))
    · exact Eval.whileFalse (by simp [eval, storeZero, zeroStore])
  · -- Execution from `σ₂` (`l = 1, h = 5`)
    let σ₂ := Store.update storeLowOne .h 5
    let σm₁ := Store.update σ₂ .h 4
    let σm₂ := Store.update storeZero .h 4
    apply Eval.whileTrue (σm := σm₂)
    · simp [eval, storeLowOne, Store.update]
    · apply Eval.seq (σm := σm₁)
      · apply Eval.iteTrue (by simp [eval, Store.update])
        have hEq : Store.update σ₂ .h (eval σ₂ (.sub (.var .h) (.lit 1))) = σm₁ := by
          funext x
          cases x <;> simp [eval, σ₂, σm₁, Store.update]
        exact hEq ▸ (Eval.assign (x := .h) (e := .sub (.var .h) (.lit 1)) (σ := σ₂))
      · have hEq : Store.update σm₁ .l (eval σm₁ (.sub (.var .l) (.lit 1))) = σm₂ := by
          funext x
          cases x <;> simp [eval, σ₂, σm₁, σm₂, storeLowOne, storeZero, zeroStore, Store.update]
        exact hEq ▸ (Eval.assign (x := .l) (e := .sub (.var .l) (.lit 1)) (σ := σm₁))
    · exact Eval.whileFalse (by simp [eval, σm₂, storeZero, zeroStore])

/-- Separation witness for `tsni_iff_tini_and_coterminates`: `l := h`
    co-terminates on all low-equivalent inputs yet violates `TINI`. -/
theorem coTerminates_without_tini :
    CoTerminates twoVarEnv (explicitFlowProg .l .h) ∧
    ¬ TINI twoVarEnv (explicitFlowProg .l .h) :=
  ⟨fun _ _ _ => ⟨fun _ => ⟨_, .assign⟩, fun _ => ⟨_, .assign⟩⟩, tini_neg_explicit_flow⟩

/-- Non-vacuity and full conjunct-independence witness for
    `tsni_iff_tini_and_coterminates`: exhibits
    1. `l := l + 1` satisfying `TSNI` (hence both `TINI` and `CoTerminates`);
    2. `while h do skip` satisfying `TINI` while failing `CoTerminates`;
    3. `l := h` satisfying `CoTerminates` while failing `TINI`. -/
theorem tsni_char_nonvacuous :
    TSNI twoVarEnv (.assign .l (.add (.var .l) (.lit 1))) ∧
    (TINI twoVarEnv (termChannelProg .h) ∧ ¬ CoTerminates twoVarEnv (termChannelProg .h)) ∧
    (CoTerminates twoVarEnv (explicitFlowProg .l .h) ∧ ¬ TINI twoVarEnv (explicitFlowProg .l .h)) := by
  refine ⟨tsni_pos_low_inc, ⟨?_, coTerminates_neg_while_h⟩, coTerminates_without_tini⟩
  intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
  have hFix : ∀ {σ σ'}, Eval (termChannelProg TwoVar.h) σ σ' → σ' = σ := by
    intro σ σ' hEval
    match hEval with
    | .whileFalse _ => rfl
    | hEval@(.whileTrue hne _ _) =>
      exact False.elim (while_skip_no_eval hEval hne)
  rw [hFix h₁, hFix h₂]
  exact hLow

/-! ### Kernel-Checked Supporting Lemmas for Card Non-Claims -/

/-- `probeProg l h` (`while l < h do skip`) is accepted by `CmdTyped` at every `pc`. -/
theorem probeProg_cmdTyped {Var : Type} (Γ : Var → Level) (pc : Level) (l h : Var) :
    CmdTyped Γ pc (probeProg l h) :=
  .whileLoop .skip

/-- Exact termination condition of `probeProg l h`: terminates iff `¬ (σ l < σ h)`. -/
theorem probeProg_terminates_iff {Var : Type} [DecidableEq Var] (l h : Var) (σ : Store Var) :
    Terminates (probeProg l h) σ ↔ ¬ (σ l < σ h) := by
  constructor
  · rintro ⟨σ', hE⟩ hlt
    exact while_skip_no_eval hE (by simp [eval, hlt])
  · intro hge
    exact ⟨σ, Eval.whileFalse (by simp [eval, hge])⟩

/-- Repeated-run termination-leakage lemma: if an attacker can rerun the
    `CmdTyped`-well-typed program `probeProg l h` (`while l < h do skip`) across
    chosen values `n : Int` of a distinct variable `l ≠ h`, the resulting
    termination profile determines `σ h` uniquely (so the informal "at most one
    bit" intuition, which no theorem here states, applies at most per run for a
    fixed low input and does not bound total leakage). -/
theorem probeProg_termination_profile_determines_secret
    {Var : Type} [DecidableEq Var] {l h : Var} (hne : l ≠ h)
    (σ σ' : Store Var)
    (hprof : ∀ n : Int,
      Terminates (probeProg l h) (Store.update σ l n) ↔
      Terminates (probeProg l h) (Store.update σ' l n)) :
    σ h = σ' h := by
  have hne' : h ≠ l := hne.symm
  have key : ∀ n : Int, (n < σ h ↔ n < σ' h) := by
    intro n
    have hp := hprof n
    rw [probeProg_terminates_iff, probeProg_terminates_iff] at hp
    simp only [Store.update_eq, Store.update_ne _ _ hne'] at hp
    constructor
    · intro h1
      by_cases h2 : n < σ' h
      · exact h2
      · exact False.elim (hp.mpr h2 h1)
    · intro h2
      by_cases h1 : n < σ h
      · exact h1
      · exact False.elim (hp.mp h1 h2)
  have h1 := key (σ h)
  have h2 := key (σ' h)
  omega

/-- Incompleteness witness for `TsTyped`: `while h do h := 0` satisfies `TSNI`
    yet is rejected by `TsTyped` at every `pc`. -/
theorem whileHZero_tsni_not_tsTyped :
    TSNI twoVarEnv whileHZero ∧ ∀ pc, ¬ TsTyped twoVarEnv pc whileHZero := by
  constructor
  · intro σ₁ σ₂ σ₁' hLow h₁
    have hPres₁ : LowEq twoVarEnv σ₁ σ₁' := by
      cases h₁ with
      | whileFalse _ => exact LowEq.refl _ _
      | whileTrue _ hBody hLoop =>
        cases hBody
        cases hLoop with
        | whileFalse _ => exact LowEq.update_high 0 rfl
        | whileTrue hne' _ _ => simp [eval, Store.update] at hne'
    by_cases h0 : σ₂ .h = 0
    · exact ⟨σ₂, .whileFalse (by simpa [eval] using h0), hPres₁.symm.trans hLow⟩
    · refine ⟨Store.update σ₂ .h 0,
        .whileTrue (by simpa [eval] using h0) .assign (.whileFalse (by simp [eval])), ?_⟩
      exact hPres₁.symm.trans (hLow.trans (LowEq.update_high 0 rfl))
  · intro pc ht
    cases ht with
    | whileLoop _ he _ => simp [exprLevel, twoVarEnv] at he

/-- Incompleteness witness for `CmdTyped`: `l := h - h` satisfies `TINI` yet is
    rejected by `CmdTyped` at every `pc`. -/
theorem subSelf_tini_not_cmdTyped :
    TINI twoVarEnv (.assign .l (.sub (.var .h) (.var .h))) ∧
    ∀ pc, ¬ CmdTyped twoVarEnv pc (.assign .l (.sub (.var .h) (.var .h))) := by
  constructor
  · intro σ₁ σ₂ σ₁' σ₂' _ h₁ h₂
    cases h₁; cases h₂
    intro x hx
    cases x with
    | l => simp [Store.update, eval]
    | h => cases hx
  · intro pc ht
    cases ht with
    | assign he _ => simp [exprLevel, twoVarEnv, LE.le, Level.le, Level.join] at he

/-- Incompleteness witness for `CmdTyped`: `if h then l := 0 else l := 0`
    satisfies `TINI` yet is rejected by `CmdTyped` at every `pc`. -/
theorem constBranch_tini_not_cmdTyped :
    TINI twoVarEnv (.ite (.var .h) (.assign .l (.lit 0)) (.assign .l (.lit 0))) ∧
    ∀ pc, ¬ CmdTyped twoVarEnv pc (.ite (.var .h) (.assign .l (.lit 0)) (.assign .l (.lit 0))) := by
  constructor
  · intro σ₁ σ₂ σ₁' σ₂' _ h₁ h₂
    have hOut : ∀ {σ σ' : Store TwoVar},
        Eval (.ite (.var TwoVar.h) (.assign TwoVar.l (.lit 0)) (.assign TwoVar.l (.lit 0))) σ σ' →
        σ' TwoVar.l = 0 := by
      intro σ σ' hE
      cases hE with
      | iteTrue _ hb => cases hb; simp [eval, Store.update]
      | iteFalse _ hb => cases hb; simp [eval, Store.update]
    intro x hx
    cases x with
    | l => rw [hOut h₁, hOut h₂]
    | h => cases hx
  · intro pc ht
    cases ht with
    | ite h₁ _ =>
      cases h₁ with
      | assign _ hpc =>
        simp only [exprLevel, twoVarEnv, Level.join_high_right] at hpc
        exact hpc

/-- `while 1 do skip` is accepted by `TsTyped twoVarEnv .low` (showing `TsTyped`
    does not enforce termination) yet rejected by `TsTyped twoVarEnv .high`. -/
theorem whileOne_tsTyped_low_not_high :
    TsTyped twoVarEnv .low (.whileLoop (.lit 1) .skip) ∧
    ¬ TsTyped twoVarEnv .high (.whileLoop (.lit 1) .skip) :=
  ⟨.whileLoop rfl rfl .skip, fun ht => by cases ht with | whileLoop hpc _ _ => cases hpc⟩

/-- `if h then (h := h + 1; h := h + 1) else skip` is accepted by `TsTyped twoVarEnv .low`
    (the typing half of the timing-channel non-claim; step-count differences are
    not modeled in `Eval`). -/
theorem timingExample_tsTyped :
    TsTyped twoVarEnv .low
      (.ite (.var .h)
        (.seq (.assign .h (.add (.var .h) (.lit 1)))
              (.assign .h (.add (.var .h) (.lit 1))))
        .skip) :=
  .ite (.seq (.assign (Level.le_high _) (Level.le_high _))
             (.assign (Level.le_high _) (Level.le_high _)))
       .skip

/-- Nondeterministic relational counterexample for the determinism boundary of
    `tsni_iff_tini_and_coterminates`: for a nondeterministic step relation `R`
    that can produce either `storeZero` or `storeLowOne` from any input,
    existential TSNI holds yet relational TINI fails. -/
theorem nondet_existential_tsni_not_tini :
    let R : Store TwoVar → Store TwoVar → Prop := fun _ σ' => σ' = storeZero ∨ σ' = storeLowOne
    (∀ σ₁ σ₂ σ₁', LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → ∃ σ₂', R σ₂ σ₂' ∧ LowEq twoVarEnv σ₁' σ₂') ∧
    ¬ (∀ σ₁ σ₂ σ₁' σ₂', LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → R σ₂ σ₂' → LowEq twoVarEnv σ₁' σ₂') := by
  intro R
  constructor
  · intro _ _ σ₁' _ h₁
    exact ⟨σ₁', h₁, LowEq.refl _ _⟩
  · intro hTini
    have hLow := hTini storeZero storeZero storeZero storeLowOne
      (LowEq.refl _ _) (Or.inl rfl) (Or.inr rfl)
    exact lowEq_neg_low_diff hLow

/-- `PcLowWhileTyped` and `LowGuardWhileTyped` are incomparable (each accepts a program the
    other rejects), so the two `while` ablations isolate different conjuncts. -/
theorem while_ablations_incomparable :
    (PcLowWhileTyped twoVarEnv .low (termChannelProg .h) ∧
      ∀ pc, ¬ LowGuardWhileTyped twoVarEnv pc (termChannelProg .h)) ∧
    (LowGuardWhileTyped twoVarEnv .low (highIfLowWhileProg .h) ∧
      ∀ pc, ¬ PcLowWhileTyped twoVarEnv pc (highIfLowWhileProg .h)) :=
  ⟨⟨pcLowWhileTyped_pos_while_h, lowGuardWhileTyped_neg_while_h⟩,
   ⟨lowGuardWhileTyped_pos_high_if_low_while, pcLowWhileTyped_neg_high_if_low_while⟩⟩

/-- `IsOneSafety` is strictly stronger than `IsTwoSafety` on `tiniHyperprop`:
    `tiniHyperprop twoVarEnv` is 2-safety but not 1-safety. -/
theorem tini_two_not_one :
    IsTwoSafety (tiniHyperprop twoVarEnv) ∧ ¬ IsOneSafety (tiniHyperprop twoVarEnv) :=
  ⟨tiniHyperprop_isTwoSafety twoVarEnv, tiniHyperprop_not_oneSafety⟩

end Toy.IFC
