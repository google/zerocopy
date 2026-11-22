/-
  Main theorem statements and proofs for `Toy.SubstStable`:
  substitution-stability characterization, instability-induced incompleteness,
  bounded and post-monomorphization `packed`/`align` checking, constructor const-index
  totality and rigid equality, post-monomorphization assertion collection with
  `IntrinsicReachable` adequacy, and generic versus monomorphic IR capture.
-/
import Toy.SubstStable.Basic
import Toy.SubstStable.Lemmas

namespace Toy.SubstStable

/-! ## 1. Substitution stability characterization -/

/-- A definition-site check `C` that is both sound (`DefCheckSound B Φ C`) and instance-complete
    (`DefCheckComplete B Φ C`) exists relative to bound `B` iff `Φ` is substitution-stable
    relative to `B` (`SubstStable B Φ`). -/
theorem exists_sound_complete_defCheck_iff_substStable
    (B : BoundPred) (Φ : ClosedTy → Bool) :
    (∃ C : OpenTy → Bool, DefCheckSound B Φ C ∧ DefCheckComplete B Φ C) ↔
      SubstStable B Φ := by
  constructor
  · rintro ⟨C, hS, hC⟩ t A1 σ1 τ1 A2 σ2 τ2 hB1 hi1 hB2 hi2
    cases h1 : Φ τ1 <;> cases h2 : Φ τ2
    · rfl
    · have hc := hC t A2 σ2 τ2 hB2 hi2 h2
      have hf := hS t A1 σ1 τ1 hc hB1 hi1
      rw [h1] at hf; cases hf
    · have hc := hC t A1 σ1 τ1 hB1 hi1 h1
      have hf := hS t A2 σ2 τ2 hc hB2 hi2
      rw [h2] at hf; cases hf
    · rfl
  · intro hStab
    let C : OpenTy → Bool := fun t => @decide (AllInstSat B Φ t) (Classical.propDecidable _)
    refine ⟨C, ?_, ?_⟩
    · intro t A σ τ hCt hB hi
      have hAll : AllInstSat B Φ t :=
        @of_decide_eq_true (AllInstSat B Φ t) (Classical.propDecidable _) hCt
      exact hAll A σ τ hB hi
    · intro t A0 σ0 τ0 hB0 hi0 hΦ0
      change @decide (AllInstSat B Φ t) (Classical.propDecidable _) = true
      apply @decide_eq_true (AllInstSat B Φ t) (Classical.propDecidable _)
      intro A σ τ hB hi
      rw [hStab t A σ τ A0 σ0 τ0 hB hi hB0 hi0]
      exact hΦ0

/-- Explicit-witness characterization: given any instantiation-witness map `w` satisfying
    `HasInstWitness B w`, the witness-evaluating check `witnessDefCheck Φ w` (defined without
    `Classical.choice`) is both sound and instance-complete relative to `B` iff
    `SubstStable B Φ`. -/
theorem witnessDefCheck_sound_and_complete_iff_substStable
    (B : BoundPred) (Φ : ClosedTy → Bool)
    (w : OpenTy → AssocEnv × Subst) (hw : HasInstWitness B w) :
    (DefCheckSound B Φ (witnessDefCheck Φ w) ∧
      DefCheckComplete B Φ (witnessDefCheck Φ w)) ↔
      SubstStable B Φ := by
  constructor
  · rintro ⟨hS, hC⟩ t A1 σ1 τ1 A2 σ2 τ2 hB1 hi1 hB2 hi2
    cases h1 : Φ τ1 <;> cases h2 : Φ τ2
    · rfl
    · have hc := hC t A2 σ2 τ2 hB2 hi2 h2
      have hf := hS t A1 σ1 τ1 hc hB1 hi1
      rw [h1] at hf; cases hf
    · have hc := hC t A1 σ1 τ1 hB1 hi1 h1
      have hf := hS t A2 σ2 τ2 hc hB2 hi2
      rw [h2] at hf; cases hf
    · rfl
  · intro hStab
    refine ⟨?_, ?_⟩
    · intro t A σ τ hCw hB hi
      have ⟨hBw, hSome⟩ := hw t ⟨A, σ, τ, hB, hi⟩
      unfold witnessDefCheck at hCw
      cases hwi : instTy (w t).1 (w t).2 t with
      | none => rw [hwi] at hSome; cases hSome
      | some τw =>
          rw [hwi] at hCw
          rw [hStab t A σ τ (w t).1 (w t).2 τw hB hi hBw hwi]
          exact hCw
    · intro t A σ τ hB hi hΦ
      have ⟨hBw, hSome⟩ := hw t ⟨A, σ, τ, hB, hi⟩
      unfold witnessDefCheck
      cases hwi : instTy (w t).1 (w t).2 t with
      | none => simp [hwi] at hSome
      | some τw =>
          dsimp only
          rw [hStab t (w t).1 (w t).2 τw A σ τ hBw hwi hB hi]
          exact hΦ

/-- Pointwise instability forces incompleteness: if an open type `t` has two `B`-conforming
    closed instances `τ1` (`Φ τ1 = true`) and `τ2` (`Φ τ2 = false`), every `B`-sound
    definition-site check `C` must reject `t` (`C t = false`, also shown without the positive
    witness by `defCheckSound_eq_false_of_falsifying_inst`) and therefore fails
    `DefCheckComplete B Φ C`. -/
theorem not_defCheckComplete_of_defCheckSound_of_unstable_witness
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (t : OpenTy) (A1 A2 : AssocEnv) (σ1 σ2 : Subst) (τ1 τ2 : ClosedTy)
    (hS : DefCheckSound B Φ C)
    (hB1 : B A1 σ1) (hi1 : instTy A1 σ1 t = some τ1) (hΦ1 : Φ τ1 = true)
    (hB2 : B A2 σ2) (hi2 : instTy A2 σ2 t = some τ2) (hΦ2 : Φ τ2 = false) :
    C t = false ∧ ¬ DefCheckComplete B Φ C := by
  have hCf : C t = false := defCheckSound_eq_false_of_falsifying_inst B Φ C t A2 σ2 τ2 hS hB2 hi2 hΦ2
  refine ⟨hCf, ?_⟩
  intro hComp
  have hCt := hComp t A1 σ1 τ1 hB1 hi1 hΦ1
  rw [hCf] at hCt
  cases hCt

/-- Without parameter bounds (`unbounded`), a closed-type predicate `Φ` is substitution-stable
    iff `Φ` is constant across all closed types (`OpenTy.tparam 0` ranges over every `ClosedTy`). -/
theorem unbounded_substStable_iff_const (Φ : ClosedTy → Bool) :
    SubstStable unbounded Φ ↔ ∀ τ1 τ2 : ClosedTy, Φ τ1 = Φ τ2 := by
  constructor
  · intro hStab τ1 τ2
    exact hStab (.tparam 0)
      (fun _ _ => none) ⟨fun _ => τ1, fun _ => 0⟩ τ1
      (fun _ _ => none) ⟨fun _ => τ2, fun _ => 0⟩ τ2
      trivial rfl trivial rfl
  · intro hConst _ _ _ τ1 _ _ τ2 _ _ _ _
    exact hConst τ1 τ2

/-- Unbounded size-threshold counterexample family: for every byte bound `k : Nat`, `sizeLe k`
    is not substitution-stable under `unbounded`, and every `unbounded`-sound definition-site
    check for `sizeLe k` fails instance-completeness. -/
theorem sizeLe_not_substStable_and_incomplete_of_defCheckSound (k : Nat) :
    ¬ SubstStable unbounded (sizeLe k) ∧
      ∀ C : OpenTy → Bool, DefCheckSound unbounded (sizeLe k) C →
        ¬ DefCheckComplete unbounded (sizeLe k) C := by
  have hPos : sizeLe k (.base 0 1) = true := by
    simp [sizeLe, ClosedTy.byteSize]
  have hNeg : sizeLe k (.base (k + 1) 1) = false :=
    decide_eq_false (by simp [ClosedTy.byteSize])
  refine ⟨?_, ?_⟩
  · intro hStab
    have heq := (unbounded_substStable_iff_const (sizeLe k)).mp hStab (.base 0 1) (.base (k + 1) 1)
    rw [hPos, hNeg] at heq
    cases heq
  · intro C hS
    exact (not_defCheckComplete_of_defCheckSound_of_unstable_witness
      unbounded (sizeLe k) C (.tparam 0)
      (fun _ _ => none) (fun _ _ => none)
      ⟨fun _ => .base 0 1, fun _ => 0⟩ ⟨fun _ => .base (k + 1) 1, fun _ => 0⟩
      (.base 0 1) (.base (k + 1) 1)
      hS trivial rfl hPos trivial rfl hNeg).2

/-! ## 2. Packed/align post-monomorphization and bounded definition-site checks -/

/-- Definitional unfolding of `evalPmeCheck` on `.packedWf t`: re-checking `packedNoAlignWf`
    after substitution and normalization is both sound and exact for each closed instance
    `(A, σ)`. -/
theorem evalPmeCheck_packedWf_iff
    (A : AssocEnv) (σ : Subst) (t : OpenTy) :
    (evalPmeCheck A σ (.packedWf t) = true) ↔
      ∃ τ : ClosedTy, instTy A σ t = some τ ∧ packedNoAlignWf τ = true := by
  unfold evalPmeCheck
  cases hi : instTy A σ t with
  | none =>
      simp [hi]
  | some τ =>
      simp [hi]

private theorem mayHaveAlignUnder_false_imp_noAlign
    {d : DeclBounds} {A : AssocEnv} {σ : Subst} (hsat : DeclBounds.sat d A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      mayHaveAlignUnder d t = false → instTy A σ t = some τ → hasAlignWrapper τ = false
  | .base _ _, _, _, hi => by injection hi with h; subst h; rfl
  | .tparam i, _, hm, hi => by
      injection hi with h; subst h
      simp [mayHaveAlignUnder] at hm
      exact hsat.2.2.1 i hm
  | .prod a b, _, hm, hi => by
      simp [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hi
      subst hi
      simp [hasAlignWrapper, mayHaveAlignUnder_false_imp_noAlign hsat hm.1 ha,
        mayHaveAlignUnder_false_imp_noAlign hsat hm.2 hb]
  | .packed _ inner, _, hm, hi => by
      simp only [mayHaveAlignUnder] at hm
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      simpa [hasAlignWrapper] using mayHaveAlignUnder_false_imp_noAlign hsat hm hin
  | .align _ _, _, hm, _ => by cases hm
  | .arr elem idx, _, hm, hi => by
      simp only [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hi
      subst hi
      simpa [hasAlignWrapper] using mayHaveAlignUnder_false_imp_noAlign hsat hm he
  | .proj tr arg, _, hm, hi => by
      simp [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases ha : instTy A σ arg <;> simp [ha] at hi
      exact hsat.2.2.2 tr hm _ _ hi

/-- Adding syntactic `noAlign` bounds (`DeclBounds`) makes `boundedDefPackedCheck d` sound at
    the definition site for every `DeclBounds.sat d`-conforming instantiation. -/
theorem boundedDefPackedCheck_sound
    (d : DeclBounds) (t : OpenTy) (A : AssocEnv) (σ : Subst) (τ : ClosedTy)
    (hchk : boundedDefPackedCheck d t = true)
    (hsat : DeclBounds.sat d A σ)
    (hinst : instTy A σ t = some τ) :
    packedNoAlignWf τ = true := by
  induction t generalizing τ with
  | base _ _ => injection hinst with h; subst h; rfl
  | tparam i => injection hinst with h; subst h; exact hsat.1 i
  | prod a b iha ihb =>
      simp [boundedDefPackedCheck] at hchk
      simp only [instTy] at hinst
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hinst
      subst hinst
      simp [packedNoAlignWf, iha _ hchk.1 ha, ihb _ hchk.2 hb]
  | packed _ inner ih =>
      simp [boundedDefPackedCheck] at hchk
      simp only [instTy, Option.map] at hinst
      cases hin : instTy A σ inner <;> simp [hin] at hinst
      subst hinst
      simp [packedNoAlignWf, mayHaveAlignUnder_false_imp_noAlign hsat hchk.1 hin, ih _ hchk.2 hin]
  | align _ inner ih =>
      simp only [boundedDefPackedCheck] at hchk
      simp only [instTy, Option.map] at hinst
      cases hin : instTy A σ inner <;> simp [hin] at hinst
      subst hinst
      simpa [packedNoAlignWf] using ih _ hchk hin
  | arr elem idx ih =>
      simp only [boundedDefPackedCheck] at hchk
      simp only [instTy] at hinst
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hinst
      subst hinst
      simpa [packedNoAlignWf] using ih _ hchk he
  | proj tr arg _ =>
      simp only [instTy] at hinst
      cases ha : instTy A σ arg <;> simp [ha] at hinst
      exact hsat.2.1 tr _ _ hinst

/-! ## 3. Constructor const-index totality and decidable rigid syntactic equality -/

mutual
  private theorem isCtorIdx_eval_some (γ : Nat → Nat) :
      (e : IdxTerm) → isCtorIdx e = true → ∃ v : CVal, evalIdx γ e = some v
    | .lit n, _ => ⟨.nat n, rfl⟩
    | .cparam i, _ => ⟨.nat (γ i), rfl⟩
    | .ctor tag args, hc => by
        simp only [isCtorIdx] at hc
        rcases isCtorIdxList_eval_some γ args hc with ⟨vs, hvs⟩
        exact ⟨.ctor tag vs, by simp [evalIdx, hvs]⟩
    | .add _ _, hc => by cases hc
    | .sub _ _, hc => by cases hc
    | .div _ _, hc => by cases hc

  private theorem isCtorIdxList_eval_some (γ : Nat → Nat) :
      (es : List IdxTerm) → isCtorIdxList es = true → ∃ vs : List CVal, evalIdxList γ es = some vs
    | [], _ => ⟨[], rfl⟩
    | e :: es, hc => by
        simp [isCtorIdxList] at hc
        rcases isCtorIdx_eval_some γ e hc.1 with ⟨v, hv⟩
        rcases isCtorIdxList_eval_some γ es hc.2 with ⟨vs, hvs⟩
        exact ⟨v :: vs, by simp [evalIdxList, hv, hvs]⟩
end

/-- Every const-index expression restricted to acyclic constructor and parameter terms
    (`isCtorIdx e = true`) evaluates without failure at every const valuation (`IdxTotal e`). -/
theorem idxTotal_of_isCtorIdx
    (e : IdxTerm) (hCtor : isCtorIdx e = true) :
    IdxTotal e := by
  intro γ
  rcases isCtorIdx_eval_some γ e hCtor with ⟨v, hv⟩
  rw [hv]
  rfl

mutual
  private theorem ctorIdx_semEq_imp_eq :
      (e1 e2 : IdxTerm) → isCtorIdx e1 = true → isCtorIdx e2 = true →
      (∀ γ : Nat → Nat, evalIdx γ e1 = evalIdx γ e2) → e1 = e2
    | .lit n, .lit m, _, _, h => by
        have h0 := h (fun _ => 0)
        simp [evalIdx] at h0
        rw [h0]
    | .lit n, .cparam i, _, _, h => by
        have h0 := h (fun _ => n + 1)
        simp [evalIdx] at h0
    | .lit _, .ctor _ args, _, hc2, h => by
        simp only [isCtorIdx] at hc2
        rcases isCtorIdxList_eval_some (fun _ => 0) args hc2 with ⟨vs, hvs⟩
        have h0 := h (fun _ => 0)
        simp [evalIdx, hvs] at h0
    | .cparam i, .lit n, _, _, h => by
        have h0 := h (fun _ => n + 1)
        simp [evalIdx] at h0
    | .cparam i, .cparam j, _, _, h => by
        by_cases hij : i = j
        · rw [hij]
        · have h0 := h (fun k => if k = i then 1 else 0)
          simp [evalIdx] at h0
          rw [h0.symm]
    | .cparam _, .ctor _ args, _, hc2, h => by
        simp only [isCtorIdx] at hc2
        rcases isCtorIdxList_eval_some (fun _ => 0) args hc2 with ⟨vs, hvs⟩
        have h0 := h (fun _ => 0)
        simp [evalIdx, hvs] at h0
    | .ctor _ args, .lit _, hc1, _, h => by
        simp only [isCtorIdx] at hc1
        rcases isCtorIdxList_eval_some (fun _ => 0) args hc1 with ⟨vs, hvs⟩
        have h0 := h (fun _ => 0)
        simp [evalIdx, hvs] at h0
    | .ctor _ args, .cparam _, hc1, _, h => by
        simp only [isCtorIdx] at hc1
        rcases isCtorIdxList_eval_some (fun _ => 0) args hc1 with ⟨vs, hvs⟩
        have h0 := h (fun _ => 0)
        simp [evalIdx, hvs] at h0
    | .ctor t1 as1, .ctor t2 as2, hc1, hc2, h => by
        simp only [isCtorIdx] at hc1 hc2
        have hTagAndList : ∀ γ : Nat → Nat, t1 = t2 ∧ evalIdxList γ as1 = evalIdxList γ as2 := by
          intro γ
          rcases isCtorIdxList_eval_some γ as1 hc1 with ⟨vs1, hvs1⟩
          rcases isCtorIdxList_eval_some γ as2 hc2 with ⟨vs2, hvs2⟩
          have hγ := h γ
          simp [evalIdx, hvs1, hvs2] at hγ
          exact ⟨hγ.1, by rw [hvs1, hvs2, hγ.2]⟩
        have ht : t1 = t2 := (hTagAndList (fun _ => 0)).1
        have has : as1 = as2 :=
          ctorIdxList_semEq_imp_eq as1 as2 hc1 hc2 (fun γ => (hTagAndList γ).2)
        rw [ht, has]
    | .add _ _, _, hc1, _, _ | .sub _ _, _, hc1, _, _ | .div _ _, _, hc1, _, _ => by cases hc1
    | _, .add _ _, _, hc2, _ | _, .sub _ _, _, hc2, _ | _, .div _ _, _, hc2, _ => by cases hc2

  private theorem ctorIdxList_semEq_imp_eq :
      (as1 as2 : List IdxTerm) → isCtorIdxList as1 = true → isCtorIdxList as2 = true →
      (∀ γ : Nat → Nat, evalIdxList γ as1 = evalIdxList γ as2) → as1 = as2
    | [], [], _, _, _ => rfl
    | [], y :: ys, _, hc2, h => by
        simp [isCtorIdxList] at hc2
        rcases isCtorIdx_eval_some (fun _ => 0) y hc2.1 with ⟨vy, hvy⟩
        rcases isCtorIdxList_eval_some (fun _ => 0) ys hc2.2 with ⟨vys, hvys⟩
        have h0 := h (fun _ => 0)
        simp [evalIdxList, hvy, hvys] at h0
    | x :: xs, [], hc1, _, h => by
        simp [isCtorIdxList] at hc1
        rcases isCtorIdx_eval_some (fun _ => 0) x hc1.1 with ⟨vx, hvx⟩
        rcases isCtorIdxList_eval_some (fun _ => 0) xs hc1.2 with ⟨vxs, hvxs⟩
        have h0 := h (fun _ => 0)
        simp [evalIdxList, hvx, hvxs] at h0
    | x :: xs, y :: ys, hc1, hc2, h => by
        simp [isCtorIdxList] at hc1 hc2
        have hHeadTail :
            ∀ γ : Nat → Nat, evalIdx γ x = evalIdx γ y ∧ evalIdxList γ xs = evalIdxList γ ys := by
          intro γ
          rcases isCtorIdx_eval_some γ x hc1.1 with ⟨vx, hvx⟩
          rcases isCtorIdxList_eval_some γ xs hc1.2 with ⟨vxs, hvxs⟩
          rcases isCtorIdx_eval_some γ y hc2.1 with ⟨vy, hvy⟩
          rcases isCtorIdxList_eval_some γ ys hc2.2 with ⟨vys, hvys⟩
          have hγ := h γ
          simp [evalIdxList, hvx, hvxs, hvy, hvys] at hγ
          exact ⟨by rw [hvx, hvy, hγ.1], by rw [hvxs, hvys, hγ.2]⟩
        rw [ctorIdx_semEq_imp_eq x y hc1.1 hc2.1 (fun γ => (hHeadTail γ).1),
          ctorIdxList_semEq_imp_eq xs ys hc1.2 hc2.2 (fun γ => (hHeadTail γ).2)]
end

/-- For constructor const-index terms (`isCtorIdx`), semantic equality across all const
    valuations (`IdxSemEq`) coincides with rigid syntactic AST equality (`e1 = e2`), which is
    decidable by `decide (e1 = e2)`. -/
theorem idxSemEq_iff_eq_of_isCtorIdx
    (e1 e2 : IdxTerm)
    (h1 : isCtorIdx e1 = true)
    (h2 : isCtorIdx e2 = true) :
    IdxSemEq e1 e2 ↔ e1 = e2 := by
  constructor
  · intro hSem
    exact ctorIdx_semEq_imp_eq e1 e2 h1 h2 hSem
  · rintro rfl _
    rfl

/-! ## 4. Post-monomorphization assertion collection and intrinsic-reachability adequacy -/

private theorem collectLoop_inv
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey) :
    ∀ (fuel : Nat) (wl done T : List MonoKey),
      collectLoop includeMentioned P fuel wl done = .ok T →
      (∀ x ∈ done, Reachable includeMentioned P roots x) →
      (∀ x ∈ wl, Reachable includeMentioned P roots x) →
      (∀ x ∈ done, passesLocalPme P x = true) →
      (∀ x ∈ done, ∃ ks, monoEdges includeMentioned P x = some ks ∧ ∀ y ∈ ks, y ∈ done ∨ y ∈ wl) →
      (∀ r ∈ roots, r ∈ done ∨ r ∈ wl) →
      (∀ x ∈ T, Reachable includeMentioned P roots x) ∧
      (∀ x ∈ T, passesLocalPme P x = true) ∧
      (∀ x ∈ T, ∃ ks, monoEdges includeMentioned P x = some ks ∧ ∀ y ∈ ks, y ∈ T) ∧
      (∀ r ∈ roots, r ∈ T)
  | 0, [], done, T, hOk, hRD, _, hPD, hED, hRoots => by
      simp [collectLoop] at hOk
      subst hOk
      refine ⟨hRD, hPD, ?_, ?_⟩
      · intro x hx
        rcases hED x hx with ⟨ks, hks, hsub⟩
        exact ⟨ks, hks, fun y hy => by rcases hsub y hy with hd | hw; exact hd; cases hw⟩
      · intro r hr
        rcases hRoots r hr with hd | hw
        · exact hd
        · cases hw
  | 0, _ :: _, _, _, hOk, _, _, _, _, _ => by
      simp [collectLoop] at hOk
  | _ + 1, [], done, T, hOk, hRD, _, hPD, hED, hRoots => by
      simp [collectLoop] at hOk
      subst hOk
      refine ⟨hRD, hPD, ?_, ?_⟩
      · intro x hx
        rcases hED x hx with ⟨ks, hks, hsub⟩
        exact ⟨ks, hks, fun y hy => by rcases hsub y hy with hd | hw; exact hd; cases hw⟩
      · intro r hr
        rcases hRoots r hr with hd | hw
        · exact hd
        · cases hw
  | fuel + 1, k :: rest, done, T, hOk, hRD, hRW, hPD, hED, hRoots => by
      simp only [collectLoop] at hOk
      by_cases hMem : k ∈ done
      · simp only [hMem, ↓reduceIte] at hOk
        apply collectLoop_inv includeMentioned P roots fuel rest done T hOk hRD
        · intro x hx; exact hRW x (List.mem_cons_of_mem k hx)
        · exact hPD
        · intro x hx
          rcases hED x hx with ⟨ks, hks, hsub⟩
          refine ⟨ks, hks, fun y hy => ?_⟩
          rcases hsub y hy with hd | hw
          · exact Or.inl hd
          · rcases List.mem_cons.mp hw with rfl | hrest
            · exact Or.inl hMem
            · exact Or.inr hrest
        · intro r hr
          rcases hRoots r hr with hd | hw
          · exact Or.inl hd
          · rcases List.mem_cons.mp hw with rfl | hrest
            · exact Or.inl hMem
            · exact Or.inr hrest
      · simp only [hMem, ↓reduceIte] at hOk
        cases hPme : passesLocalPme P k with
        | false =>
            simp [hPme] at hOk
        | true =>
            simp only [hPme, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            cases hEdges : monoEdges includeMentioned P k with
            | none =>
                simp [hEdges] at hOk
            | some nexts =>
                simp only [hEdges] at hOk
                let fresh := nexts.filter (fun k' => !decide (k' ∈ done))
                have hRk : Reachable includeMentioned P roots k := hRW k (List.Mem.head _)
                apply collectLoop_inv includeMentioned P roots fuel (rest ++ fresh) (done ++ [k]) T hOk
                · intro x hx
                  rcases List.mem_append.mp hx with hd | hk
                  · exact hRD x hd
                  · simp at hk; subst hk; exact hRk
                · intro x hx
                  rcases List.mem_append.mp hx with hrest | hfr
                  · exact hRW x (List.mem_cons_of_mem k hrest)
                  · have hInNexts : x ∈ nexts := (List.mem_filter.mp hfr).1
                    exact Reachable.step hRk hEdges hInNexts
                · intro x hx
                  rcases List.mem_append.mp hx with hd | hk
                  · exact hPD x hd
                  · simp at hk; subst hk; exact hPme
                · intro x hx
                  rcases List.mem_append.mp hx with hd | hk
                  · rcases hED x hd with ⟨ks, hks, hsub⟩
                    refine ⟨ks, hks, fun y hy => ?_⟩
                    rcases hsub y hy with hyd | hyw
                    · exact Or.inl (List.mem_append_left _ hyd)
                    · rcases List.mem_cons.mp hyw with rfl | hyrest
                      · exact Or.inl (List.mem_append_right _ (by simp))
                      · exact Or.inr (List.mem_append_left _ hyrest)
                  · simp at hk; subst hk
                    refine ⟨nexts, hEdges, fun y hy => ?_⟩
                    by_cases hyd : y ∈ done
                    · exact Or.inl (List.mem_append_left _ hyd)
                    · right
                      apply List.mem_append_right
                      exact List.mem_filter.mpr ⟨hy, by simp [hyd]⟩
                · intro r hr
                  rcases hRoots r hr with hd | hw
                  · exact Or.inl (List.mem_append_left _ hd)
                  · rcases List.mem_cons.mp hw with rfl | hrest
                    · exact Or.inl (List.mem_append_right _ (by simp))
                    · exact Or.inr (List.mem_append_left _ hrest)

private theorem usedStmtRefs_subset_mentionedStmtRefs (A : AssocEnv) (σ : Subst) :
    ∀ (s : GenStmt) {us ms : List MonoKey},
      usedStmtRefs A σ s = some us →
      mentionedStmtRefs A σ s = some ms →
      ∀ y ∈ us, y ∈ ms
  | .skip, _, _, hu, _, y, hy => by
      simp [usedStmtRefs] at hu; subst hu; cases hy
  | .deadBranch _, _, _, hu, _, y, hy => by
      simp [usedStmtRefs] at hu; subst hu; cases hy
  | .call callee tys cnsts, _, _, hu, hm, y, hy => by
      simp only [usedStmtRefs] at hu
      simp only [mentionedStmtRefs] at hm
      rw [hu] at hm
      injection hm with hEq
      subst hEq
      exact hy
  | .seq a b, _, _, hu, hm, y, hy => by
      simp only [usedStmtRefs] at hu
      simp only [mentionedStmtRefs] at hm
      cases hua : usedStmtRefs A σ a <;> cases hub : usedStmtRefs A σ b <;> simp [hua, hub] at hu
      cases hma : mentionedStmtRefs A σ a <;> cases hmb : mentionedStmtRefs A σ b <;> simp [hma, hmb] at hm
      subst hu; subst hm
      rcases List.mem_append.mp hy with hya | hyb
      · exact List.mem_append_left _ (usedStmtRefs_subset_mentionedStmtRefs A σ a hua hma y hya)
      · exact List.mem_append_right _ (usedStmtRefs_subset_mentionedStmtRefs A σ b hub hmb y hyb)

/-- When `collectAndCheck includeMentioned P roots fuel` returns `.ok T`, `T` contains
    precisely the collector-visible `monoEdges`-reachable instances (`Reachable includeMentioned`),
    includes all `used`-reachable instances (`Reachable false`), and certifies
    `passesLocalPme P k = true` on every `k ∈ T`. -/
theorem collectAndCheck_ok_mem_and_localPme
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T) :
    (∀ k, k ∈ T ↔ Reachable includeMentioned P roots k) ∧
      (∀ k, Reachable false P roots k → k ∈ T) ∧
      (∀ k ∈ T, passesLocalPme P k = true) := by
  have ⟨hReachOfMem, hPme, hClosed, hRootsInT⟩ :=
    collectLoop_inv includeMentioned P roots fuel roots [] T hOk
      (fun _ h => by cases h)
      (fun _ h => Reachable.root h)
      (fun _ h => by cases h)
      (fun _ h => by cases h)
      (fun _ h => Or.inr h)
  have hMemOfReach : ∀ k, Reachable includeMentioned P roots k → k ∈ T := by
    intro k hR
    induction hR with
    | root hk => exact hRootsInT _ hk
    | step _ hm hk' ih =>
        rcases hClosed _ ih with ⟨ks', hks', hsub⟩
        rw [hm] at hks'
        injection hks' with hEq
        subst hEq
        exact hsub _ hk'
  refine ⟨fun k => ⟨hReachOfMem k, hMemOfReach k⟩, ?_, hPme⟩
  intro k hRFalse
  cases includeMentioned with
  | false => exact hMemOfReach k hRFalse
  | true =>
      induction hRFalse with
      | root hk => exact hRootsInT _ hk
      | @step x y ks_u _ hm_u hy ih =>
          rcases hClosed x ih with ⟨ks_m, hm_m, hsub⟩
          apply hsub y
          unfold monoEdges at hm_u hm_m
          cases hfn : P.fns[x.fnId]? with
          | none => simp [hfn] at hm_u
          | some fn =>
              simp only [hfn] at hm_u hm_m
              cases hloc : fn.localMir with
              | false =>
                  simp [hloc] at hm_u
                  subst hm_u; cases hy
              | true =>
                  simp [hloc] at hm_u hm_m
                  exact usedStmtRefs_subset_mentionedStmtRefs P.assoc (substOfKey x) fn.body hm_u hm_m y hy

/-- Adequacy of collector-visible `Reachable` (`monoEdges`) against intrinsic `fn.body`
    call-graph reachability (`IntrinsicReachable`, `intrinsicEdges`): when `collectAndCheck`
    returns `.ok T` and every collected key has locally available MIR (`AllLocalMir P T`),
    no outgoing call edge in `T` is truncated by `localMir = false`, so `IntrinsicReachable`
    and `Reachable` coincide on every `k : MonoKey`. -/
theorem intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T) (k : MonoKey) :
    IntrinsicReachable includeMentioned P roots k ↔ Reachable includeMentioned P roots k := by
  have hMemIff := (collectAndCheck_ok_mem_and_localPme includeMentioned P roots fuel T hOk).1
  constructor
  · intro hIntr
    induction hIntr with
    | root hk => exact Reachable.root hk
    | @step x y ks _ hIntrEdges hy ih =>
        have hxT : x ∈ T := (hMemIff x).mpr ih
        have hLocX : isLocalFn P x = true := hLoc x hxT
        have hMono : monoEdges includeMentioned P x = some ks := by
          unfold isLocalFn at hLocX
          unfold intrinsicEdges at hIntrEdges
          unfold monoEdges
          cases hfn : P.fns[x.fnId]? with
          | none => simp [hfn] at hLocX
          | some fn =>
              simp only [hfn] at hLocX hIntrEdges ⊢
              simpa [hLocX] using hIntrEdges
        exact Reachable.step ih hMono hy
  · intro hReach
    induction hReach with
    | root hk => exact IntrinsicReachable.root hk
    | @step x y ks _ hMonoEdges hy ih =>
        have hIntr : intrinsicEdges includeMentioned P x = some ks := by
          unfold monoEdges at hMonoEdges
          unfold intrinsicEdges
          cases hfn : P.fns[x.fnId]? with
          | none => simp [hfn] at hMonoEdges
          | some fn =>
              simp only [hfn] at hMonoEdges ⊢
              cases hloc : fn.localMir with
              | false =>
                  simp [hloc] at hMonoEdges
                  subst hMonoEdges
                  cases hy
              | true =>
                  simpa [hloc] using hMonoEdges
        exact IntrinsicReachable.step ih hIntr hy

/-- When `collectAndCheck` returns `.ok T` and every collected key has locally available MIR
    (`AllLocalMir P T`), every intrinsically call-reachable instance `k` (`IntrinsicReachable`)
    satisfies its intrinsic post-monomorphization assertions (`passesIntrinsicPme P k = true`). -/
theorem collectAndCheck_ok_intrinsicPme_of_allLocalMir
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey) (k : MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T)
    (hReach : IntrinsicReachable includeMentioned P roots k) :
    passesIntrinsicPme P k = true := by
  have hColl := collectAndCheck_ok_mem_and_localPme includeMentioned P roots fuel T hOk
  have hR : Reachable includeMentioned P roots k :=
    (intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir
      includeMentioned P roots fuel T hOk hLoc k).mp hReach
  have hkT : k ∈ T := (hColl.1 k).mpr hR
  exact passesIntrinsicPme_of_passesLocalPme_of_isLocalFn (hColl.2.2 k hkT) (hLoc k hkT)

/-! ## 5. Generic versus monomorphic IR capture -/

/-- Elementary corollary of `DefCheckSound` and `exists_sound_complete_defCheck_iff_substStable`:
    under `DefCheckSound B Φ C`, every `C`-accepted open type `t` evaluates `Φ` to `true`
    (hence invariantly `Φ τ1 = Φ τ2`) across all `B`-conforming instances, and if `C` also
    satisfies `DefCheckComplete B Φ C`, `SubstStable B Φ` holds globally. -/
theorem defCheckSound_accepted_true_and_substStable_of_complete
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (hSound : DefCheckSound B Φ C) :
    (∀ t A1 σ1 τ1 A2 σ2 τ2,
      C t = true →
      B A1 σ1 → instTy A1 σ1 t = some τ1 →
      B A2 σ2 → instTy A2 σ2 t = some τ2 →
      Φ τ1 = true ∧ Φ τ1 = Φ τ2) ∧
    (DefCheckComplete B Φ C → SubstStable B Φ) := by
  refine ⟨?_, ?_⟩
  · intro t A1 σ1 τ1 A2 σ2 τ2 hC hB1 hi1 hB2 hi2
    have h1 := hSound t A1 σ1 τ1 hC hB1 hi1
    have h2 := hSound t A2 σ2 τ2 hC hB2 hi2
    exact ⟨h1, by rw [h1, h2]⟩
  · intro hComp
    exact (exists_sound_complete_defCheck_iff_substStable B Φ).mp ⟨C, hSound, hComp⟩

/-- Elementary bound-entailment precomposition: a definition-site check `C` that is sound
    under an assumed bound `B_assumed` remains sound under source bound `B_src` whenever
    `B_src` entails `B_assumed` (`BoundEntails B_src B_assumed`). -/
theorem defCheckSound_of_boundEntails
    (B_src B_assumed : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (hEntails : BoundEntails B_src B_assumed)
    (hSound : DefCheckSound B_assumed Φ C) :
    DefCheckSound B_src Φ C := by
  exact fun t A σ τ hC hB hi => hSound t A σ τ hC (hEntails A σ hB) hi

/-- Generic-IR target certification under entailed definition-site checks: for any generic
    function `fn : GenFn`, if `DeclBounds.sat fn.bounds` entails `B_assumed`, `C` is sound
    under `B_assumed` for `Φ`, and `C openTarget = true`, then `(fn, openTarget)` satisfies
    unconditional generic-body safety (`GenericBodySafeUnconditional fn openTarget Φ`). -/
theorem genericBodySafeUnconditional_of_defCheckSound_of_boundEntails
    (fn : GenFn) (B_assumed : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (openTarget : OpenTy)
    (hEntails : BoundEntails (DeclBounds.sat fn.bounds) B_assumed)
    (hSound : DefCheckSound B_assumed Φ C)
    (hAccept : C openTarget = true) :
    GenericBodySafeUnconditional fn openTarget Φ := by
  exact fun A σ τ hSat hi => hSound openTarget A σ τ hAccept (hEntails A σ hSat) hi

/-- Definitional `List.all` characterization of verifier-side post-monomorphization target
    checking (`checkMonoTarget`) on a captured monomorphic instance list `T`, requiring no
    substitution-stability hypothesis on `Φ`. -/
theorem checkMonoTarget_iff_monoCaptureCertifiedOn
    (A : AssocEnv) (Φ : ClosedTy → Bool)
    (targetOf : Nat → Option OpenTy) (T : List MonoKey) :
    (checkMonoTarget A Φ targetOf T = true) ↔
      MonoCaptureCertifiedOn A Φ targetOf T := by
  unfold checkMonoTarget MonoCaptureCertifiedOn
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    have hkOk := h k hk
    cases ht : targetOf k.fnId with
    | none => rw [ht] at hkOk; cases hkOk
    | some openTarget =>
        simp only [ht] at hkOk
        cases hi : instTy A (substOfKey k) openTarget with
        | none => simp [hi] at hkOk
        | some τ =>
            simp [hi] at hkOk
            exact ⟨openTarget, τ, rfl, hi, hkOk⟩
  · intro h k hk
    rcases h k hk with ⟨openTarget, τ, ht, hi, hΦ⟩
    simp [ht, hi, hΦ]

/-- Monomorphic IR capture discharges substitution-unstable `packedNoAlignWf` obligations on
    all captured instances `T` whenever collection succeeds (`collectAndCheck = .ok T`), all
    captured items have local MIR (`AllLocalMir P T`), and each declares a `.packedWf` PME
    guard (`HasPackedPmeGuard P targetOf T`). -/
theorem monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey) (targetOf : Nat → Option OpenTy)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T)
    (hGuard : HasPackedPmeGuard P targetOf T) :
    MonoCaptureCertifiedOn P.assoc packedNoAlignWf targetOf T := by
  have hColl := collectAndCheck_ok_mem_and_localPme includeMentioned P roots fuel T hOk
  intro k hkT
  have hPmeLocal : passesLocalPme P k = true := hColl.2.2 k hkT
  have hIntrPme : passesIntrinsicPme P k = true :=
    passesIntrinsicPme_of_passesLocalPme_of_isLocalFn hPmeLocal (hLoc k hkT)
  have hKeyG : keyHasPackedGuard P targetOf k = true := hGuard k hkT
  unfold keyHasPackedGuard at hKeyG
  unfold passesIntrinsicPme at hIntrPme
  cases hfn : P.fns[k.fnId]? with
  | none => simp [hfn] at hKeyG
  | some fn =>
      cases ht : targetOf k.fnId with
      | none => simp [hfn, ht] at hKeyG
      | some openTarget =>
          simp [hfn, ht] at hKeyG
          simp only [hfn, List.all_eq_true] at hIntrPme
          have hEval := hIntrPme (.packedWf openTarget) hKeyG
          rcases (evalPmeCheck_packedWf_iff P.assoc (substOfKey k) openTarget).mp hEval with ⟨τ, hi, hWf⟩
          exact ⟨openTarget, τ, rfl, hi, hWf⟩

end Toy.SubstStable
