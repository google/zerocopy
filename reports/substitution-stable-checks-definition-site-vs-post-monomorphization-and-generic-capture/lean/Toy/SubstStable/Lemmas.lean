/-
  Foundational and characterization lemmas for `Toy.SubstStable`.
  Every lemma in this file is kernel-checked with zero `sorry`.
-/
import Toy.SubstStable.Basic

namespace Toy.SubstStable

/-! ## 1. Characterizations of core definitions -/

/-- `DefCheckSound` holds iff every open type accepted by `C` satisfies `AllInstSat B Φ`. -/
theorem defCheckSound_iff_allInstSat
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) :
    DefCheckSound B Φ C ↔ ∀ t, C t = true → AllInstSat B Φ t := by
  constructor
  · intro h t hC A σ τ hB hi
    exact h t A σ τ hC hB hi
  · intro h t A σ τ hC hB hi
    exact h t hC A σ τ hB hi

/-- `DefCheckComplete` holds iff every open type with at least one `Φ`-satisfying `B`-instance
    is accepted by `C`. -/
theorem defCheckComplete_iff_exists_inst
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) :
    DefCheckComplete B Φ C ↔
      ∀ t, (∃ A σ τ, B A σ ∧ instTy A σ t = some τ ∧ Φ τ = true) → C t = true := by
  constructor
  · rintro h t ⟨A, σ, τ, hB, hi, hΦ⟩
    exact h t A σ τ hB hi hΦ
  · intro h t A σ τ hB hi hΦ
    exact h t ⟨A, σ, τ, hB, hi, hΦ⟩

/-- `SubstStable B Φ` holds iff on every open type `t`, either every `B`-instance satisfies `Φ`
    or every `B`-instance falsifies `Φ`. -/
theorem substStable_iff_allInst_const
    (B : BoundPred) (Φ : ClosedTy → Bool) :
    SubstStable B Φ ↔
      ∀ t, AllInstSat B Φ t ∨ AllInstSat B (fun τ => !Φ τ) t := by
  constructor
  · intro hStab t
    by_cases hex : ∃ A σ τ, B A σ ∧ instTy A σ t = some τ ∧ Φ τ = true
    · left
      rcases hex with ⟨A0, σ0, τ0, hB0, hi0, hΦ0⟩
      intro A σ τ hB hi
      have heq := hStab t A σ τ A0 σ0 τ0 hB hi hB0 hi0
      rw [heq, hΦ0]
    · right
      intro A σ τ hB hi
      cases hΦ : Φ τ
      · simp [hΦ]
      · exact False.elim (hex ⟨A, σ, τ, hB, hi, hΦ⟩)
  · intro hOr t A1 σ1 τ1 A2 σ2 τ2 hB1 hi1 hB2 hi2
    rcases hOr t with hTrue | hFalse
    · rw [hTrue A1 σ1 τ1 hB1 hi1, hTrue A2 σ2 τ2 hB2 hi2]
    · have h1 : (!Φ τ1) = true := hFalse A1 σ1 τ1 hB1 hi1
      have h2 : (!Φ τ2) = true := hFalse A2 σ2 τ2 hB2 hi2
      cases hΦ1 : Φ τ1 <;> cases hΦ2 : Φ τ2 <;> simp_all

/-- Universal-premise characterization of `HasInstWitness` without existential nesting. -/
theorem hasInstWitness_iff_forall_inst
    (B : BoundPred) (w : OpenTy → AssocEnv × Subst) :
    HasInstWitness B w ↔
      ∀ t A σ τ, B A σ → instTy A σ t = some τ →
        B (w t).1 (w t).2 ∧ (instTy (w t).1 (w t).2 t).isSome = true := by
  constructor
  · intro hw t A σ τ hB hi
    exact hw t ⟨A, σ, τ, hB, hi⟩
  · rintro h t ⟨A, σ, τ, hB, hi⟩
    exact h t A σ τ hB hi

/-- `witnessDefCheck Φ w t` returns `true` iff every closed type produced at `w t` satisfies `Φ`. -/
theorem witnessDefCheck_eq_true_iff
    (Φ : ClosedTy → Bool) (w : OpenTy → AssocEnv × Subst) (t : OpenTy) :
    (witnessDefCheck Φ w t = true) ↔
      ∀ τ, instTy (w t).1 (w t).2 t = some τ → Φ τ = true := by
  unfold witnessDefCheck
  cases h : instTy (w t).1 (w t).2 t with
  | none =>
      simp
  | some τ0 =>
      constructor
      · intro hΦ τ hτ
        injection hτ with hEq
        subst hEq
        exact hΦ
      · intro hall
        exact hall τ0 rfl

/-- `IdxTotal e` holds iff every const-parameter valuation evaluates `e` to some canonical value. -/
theorem idxTotal_iff_exists_cval (e : IdxTerm) :
    IdxTotal e ↔ ∀ γ : Nat → Nat, ∃ v : CVal, evalIdx γ e = some v := by
  constructor
  · intro h γ
    have hs := h γ
    cases he : evalIdx γ e with
    | none => rw [he] at hs; cases hs
    | some v => exact ⟨v, rfl⟩
  · intro h γ
    rcases h γ with ⟨v, hv⟩
    rw [hv]
    rfl

/-- `sizeLe k τ = true` iff `τ.byteSize ≤ k`. -/
theorem sizeLe_iff_byteSize_le (k : Nat) (τ : ClosedTy) :
    (sizeLe k τ = true) ↔ τ.byteSize ≤ k := by
  unfold sizeLe
  exact decide_eq_true_iff

/-- `eqProdByteSize τ = true` iff `τ` is a product `.prod a b` with equal component byte sizes. -/
theorem eqProdByteSize_iff_exists_prod (τ : ClosedTy) :
    (eqProdByteSize τ = true) ↔
      ∃ a b : ClosedTy, τ = .prod a b ∧ a.byteSize = b.byteSize := by
  cases τ with
  | prod a b =>
      simp only [eqProdByteSize, decide_eq_true_iff]
      constructor
      · intro h
        exact ⟨a, b, rfl, h⟩
      · rintro ⟨a', b', hEq, h⟩
        injection hEq with ha hb
        subst ha; subst hb
        exact h
  | base _ _ | packed _ _ | align _ _ | arr _ _ =>
      simp [eqProdByteSize]

/-- `AllLocalMir P T` holds iff `T.all (isLocalFn P) = true`. -/
theorem allLocalMir_iff_list_all (P : CrateProg) (T : List MonoKey) :
    AllLocalMir P T ↔ T.all (isLocalFn P) = true := by
  unfold AllLocalMir
  rw [List.all_eq_true]

/-- `HasPackedPmeGuard P targetOf T` holds iff `T.all (keyHasPackedGuard P targetOf) = true`. -/
theorem hasPackedPmeGuard_iff_list_all
    (P : CrateProg) (targetOf : Nat → Option OpenTy) (T : List MonoKey) :
    HasPackedPmeGuard P targetOf T ↔ T.all (keyHasPackedGuard P targetOf) = true := by
  unfold HasPackedPmeGuard
  rw [List.all_eq_true]

/-- A `B`-sound definition-site check rejects every open type admitting a `B`-conforming
    closed instance that falsifies `Φ` (without requiring any positive instance of `t`). -/
theorem defCheckSound_eq_false_of_falsifying_inst
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (t : OpenTy) (A2 : AssocEnv) (σ2 : Subst) (τ2 : ClosedTy)
    (hS : DefCheckSound B Φ C)
    (hB2 : B A2 σ2) (hi2 : instTy A2 σ2 t = some τ2) (hΦ2 : Φ τ2 = false) :
    C t = false := by
  cases hc : C t
  · rfl
  · have h := hS t A2 σ2 τ2 hc hB2 hi2
    rw [hΦ2] at h
    cases h

/-- Pointwise local-MIR transfer: for any instance `k` with `isLocalFn P k = true`,
    `passesLocalPme P k = true` implies `passesIntrinsicPme P k = true` without requiring
    crate-wide `AllLocalMir`. -/
theorem passesIntrinsicPme_of_passesLocalPme_of_isLocalFn
    {P : CrateProg} {k : MonoKey}
    (hp : passesLocalPme P k = true) (hl : isLocalFn P k = true) :
    passesIntrinsicPme P k = true := by
  unfold passesLocalPme at hp
  unfold isLocalFn at hl
  unfold passesIntrinsicPme
  cases hfn : P.fns[k.fnId]? with
  | none => rw [hfn] at hl; cases hl
  | some fn =>
      simp only [hfn] at hl hp ⊢
      simpa [hl] using hp

/-- Whenever `instTy A σ t` succeeds under `σ.cnst = fun _ => 0`, `instTy` also succeeds at
    `constZeroNoAlignWitness t` (used for `HasInstWitness FixedConstNoAlignBound`). -/
theorem instTy_constZeroNoAlignWitness_isSome
    {A : AssocEnv} {σ : Subst} (hc : σ.cnst = fun _ => 0) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ →
      (instTy (constZeroNoAlignWitness t).1 (constZeroNoAlignWitness t).2 t).isSome = true
  | .base _ _, _, _ => rfl
  | .tparam _, _, _ => rfl
  | .prod a b, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hi
      have iha := instTy_constZeroNoAlignWitness_isSome hc ha
      have ihb := instTy_constZeroNoAlignWitness_isSome hc hb
      simp only [constZeroNoAlignWitness] at iha ihb ⊢
      simp only [instTy]
      cases ha' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ a <;>
        cases hb' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ b <;>
        simp_all
  | .packed _ inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      have ih := instTy_constZeroNoAlignWitness_isSome hc hin
      simp only [constZeroNoAlignWitness] at ih ⊢
      simp only [instTy, Option.map]
      cases hin' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ inner <;>
        simp_all
  | .align _ inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      have ih := instTy_constZeroNoAlignWitness_isSome hc hin
      simp only [constZeroNoAlignWitness] at ih ⊢
      simp only [instTy, Option.map]
      cases hin' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ inner <;>
        simp_all
  | .arr elem idx, _, hi => by
      simp only [instTy] at hi
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hi
      have ihe := instTy_constZeroNoAlignWitness_isSome hc he
      rw [hc] at hv
      simp only [constZeroNoAlignWitness] at ihe ⊢
      simp only [instTy, hv]
      cases he' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ elem <;>
        simp_all
  | .proj _ arg, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ arg <;> simp [ha] at hi
      have iha := instTy_constZeroNoAlignWitness_isSome hc ha
      simp only [constZeroNoAlignWitness] at iha ⊢
      simp only [instTy]
      cases ha' : instTy (fun _ _ => some (.base 1 1)) ⟨fun _ => .base 1 1, fun _ => 0⟩ arg <;>
        simp_all

/-! ## 2. Structural lemmas under `FullNoAlignBound` (positive-control infrastructure) -/

/-- Under `FullNoAlignBound`, `hasAlignWrapper` of any closed instance agrees with
    `naiveOpenHasAlign` of the open type. -/
theorem hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign
    {A : AssocEnv} {σ : Subst} (hB : FullNoAlignBound A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ → hasAlignWrapper τ = naiveOpenHasAlign t
  | .base _ _, _, hi => by
      injection hi with hτ; subst hτ; rfl
  | .tparam i, _, hi => by
      injection hi with hτ; subst hτ
      exact (hB.1 i).2
  | .prod a b, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hi
      subst hi
      simp [hasAlignWrapper, naiveOpenHasAlign,
        hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign hB ha,
        hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign hB hb]
  | .packed k inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      simp [hasAlignWrapper, naiveOpenHasAlign,
        hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign hB hin]
  | .align n inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      rfl
  | .arr elem idx, _, hi => by
      simp only [instTy] at hi
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hi
      subst hi
      simp [hasAlignWrapper, naiveOpenHasAlign,
        hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign hB he]
  | .proj tr arg, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ arg <;> simp [ha] at hi
      exact (hB.2 tr _ _ hi).2

/-- Under `FullNoAlignBound`, `packedNoAlignWf` of any closed instance agrees identically with
    `naiveDefPackedCheck` of the open type. -/
theorem packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign
    {A : AssocEnv} {σ : Subst} (hB : FullNoAlignBound A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ → packedNoAlignWf τ = naiveDefPackedCheck t
  | .base _ _, _, hi => by
      injection hi with hτ; subst hτ; rfl
  | .tparam i, _, hi => by
      injection hi with hτ; subst hτ
      exact (hB.1 i).1
  | .prod a b, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hi
      subst hi
      simp [packedNoAlignWf, naiveDefPackedCheck,
        packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB ha,
        packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hb]
  | .packed k inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      simp [packedNoAlignWf, naiveDefPackedCheck,
        hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign hB hin,
        packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hin]
  | .align n inner, _, hi => by
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      simp [packedNoAlignWf, naiveDefPackedCheck,
        packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hin]
  | .arr elem idx, _, hi => by
      simp only [instTy] at hi
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hi
      subst hi
      simp [packedNoAlignWf, naiveDefPackedCheck,
        packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB he]
  | .proj tr arg, _, hi => by
      simp only [instTy] at hi
      cases ha : instTy A σ arg <;> simp [ha] at hi
      exact (hB.2 tr _ _ hi).1

end Toy.SubstStable
