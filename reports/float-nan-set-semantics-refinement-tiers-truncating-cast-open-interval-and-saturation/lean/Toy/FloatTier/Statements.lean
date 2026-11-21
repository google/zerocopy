/-
Toy.FloatTier.Statements
========================

Main results about refinement tiers: `refinesS_iff_tierSound`,
`Prog.refinesS_iff_tierSound`, `tierOf_refinesS`, `sound_tiers_disagree_on_bits`,
`Prog.runS_of_runS_fold`, `fold_tierCtfe_changes_tierRunA_bits`. The determinism
results are in `Toy.FloatTier.Determinism`, the conversion results in
`Toy.FloatTier.CastStatements`, and the remaining counterexamples in
`Toy.FloatTier.Counterexamples`.
-/
import Toy.FloatTier.VLemmas
import Toy.FloatTier.Cast

namespace Toy.FloatTier

variable {f : Fmt}

/-! ## Refinement tiers -/

theorem FExpr.evalS_evalT_of_tierSound {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (e : FExpr f) (ρ : Nat → V f) : e.evalS X ρ (e.evalT τ ρ) := by
  induction e with
  | lit v => rfl
  | var i => rfl
  | prim p a b iha ihb => exact ⟨_, _, iha, ihb, hτ p _ _⟩
  | neg a ih => exact ⟨_, ih, rfl⟩
  | abs a ih => exact ⟨_, ih, rfl⟩
  | copysign a b iha ihb => exact ⟨_, _, iha, ihb, rfl⟩
  | selLt a b t e iha ihb iht ihe =>
    refine ⟨_, _, iha, ihb, ?_⟩
    by_cases hc : lt (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP = true
    · simp only [hc, ite_true, FExpr.evalT]; exact iht
    · simp only [hc, Bool.false_eq_true, ite_false, FExpr.evalT]; exact ihe

/-- **Refinement iff soundness.** A deterministic tier `τ` refines the
set-valued semantics `S` (with extra payloads `X`) on every expression and
input iff every choice of `τ` lies in the corresponding set of `S`. -/
theorem refinesS_iff_tierSound (X : Extra f) (τ : Tier f) : RefinesS X τ ↔ TierSound X τ := by
  constructor
  · intro h p x y
    obtain ⟨x', y', hx, hy, hr⟩ :=
      h (.prim p (.var 0) (.var 1)) (fun i => if i = 0 then x else y)
    simp only [FExpr.evalS, ite_true, Nat.one_ne_zero, ite_false] at hx hy
    subst hx hy
    simpa [FExpr.evalT] using hr
  · intro h e ρ
    exact FExpr.evalS_evalT_of_tierSound h e ρ

/-- Programs: the observation computed by a sound tier is one of the
observations allowed by `S`. -/
theorem Prog.runS_runT_of_tierSound {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (P : Prog f) (ρ : Nat → V f) : P.runS X ρ (P.runT τ ρ) := by
  cases P with
  | isNaN a => exact ⟨_, FExpr.evalS_evalT_of_tierSound hτ a ρ, rfl⟩
  | eq a b => exact ⟨_, _, FExpr.evalS_evalT_of_tierSound hτ a ρ,
      FExpr.evalS_evalT_of_tierSound hτ b ρ, rfl⟩
  | lt a b => exact ⟨_, _, FExpr.evalS_evalT_of_tierSound hτ a ρ,
      FExpr.evalS_evalT_of_tierSound hτ b ρ, rfl⟩
  | signBit a => exact ⟨_, FExpr.evalS_evalT_of_tierSound hτ a ρ, rfl⟩
  | toBits a => exact ⟨_, FExpr.evalS_evalT_of_tierSound hτ a ρ, rfl⟩

/-- **Refinement iff soundness, for observations.** A tier `τ` computes, on
every program and input, an observation that `S` allows iff every choice of
`τ` lies in the corresponding set of `S`. (The `⇒` direction observes
`toBits (prim p (var 0) (var 1))` and uses injectivity of `V.bits`.) -/
theorem Prog.refinesS_iff_tierSound (X : Extra f) (τ : Tier f) :
    (∀ (P : Prog f) (ρ : Nat → V f), P.runS X ρ (P.runT τ ρ)) ↔ TierSound X τ := by
  constructor
  · intro h p x y
    obtain ⟨r, ⟨x', y', hx, hy, hr⟩, hbits⟩ :=
      h (.toBits (.prim p (.var 0) (.var 1))) (fun i => if i = 0 then x else y)
    simp only [FExpr.evalS, ite_true, Nat.one_ne_zero, ite_false] at hx hy
    subst hx hy
    simp only [Prog.runT, FExpr.evalT, ite_true, Nat.one_ne_zero, ite_false] at hbits
    rw [V.bits_injective hbits]
    exact hr
  · intro h P ρ
    exact Prog.runS_runT_of_tierSound h P ρ

/-- Every policy tier is sound for every extra-payload set. -/
theorem tierOf_sound (X : Extra f) (pol : ChoicePolicy) : TierSound X (tierOf pol) := by
  intro p x y
  cases p with
  | add => exact arith_mem X pol _ x y
  | sub => exact arith_mem X pol _ x y
  | mul => exact arith_mem X pol _ x y
  | min =>
    simp only [tierOf, primSet, minSet]
    split
    · exact nanResult_mem X pol x y
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split <;> simp
  | max =>
    simp only [tierOf, primSet, maxSet]
    split
    · exact nanResult_mem X pol x y
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split <;> simp

/-- **Policy tiers refine `S`.** For every extra-payload set `X` and every
`ChoicePolicy`, the policy tier refines `S`; in particular the example tiers
`tierCtfe` and `tierRunA` do. -/
theorem tierOf_refinesS (X : Extra f) (pol : ChoicePolicy) : RefinesS X (tierOf pol) :=
  (refinesS_iff_tierSound X _).2 (tierOf_sound X pol)

/-- The program `toBits (0.0 * +∞)`. -/
def progBitsZeroMulInf (f : Fmt) : Prog f :=
  .toBits (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))

theorem mul_zero_inf (s t : Bool) : mul (zero f s) (.inf t) = .nan := by
  simp [zero, mul, unitsOf_zero_zero]

theorem progBitsZeroMulInf_runT_tierCtfe (ρ : Nat → V f) :
    (progBitsZeroMulInf f).runT tierCtfe ρ = (V.prefNaN f false).bits := by
  simp [progBitsZeroMulInf, Prog.runT, FExpr.evalT, tierCtfe, tierOf, ChoicePolicy.arith,
    V.zero, V.toFP, ctfePolicy, ChoicePolicy.nanResult, FP.isNaN,
    show (FP.fin false ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩ : FP f) = zero f false from rfl,
    mul_zero_inf]

theorem progBitsZeroMulInf_runT_tierRunA (ρ : Nat → V f) :
    (progBitsZeroMulInf f).runT tierRunA ρ = (V.prefNaN f true).bits := by
  simp [progBitsZeroMulInf, Prog.runT, FExpr.evalT, tierRunA, tierOf, ChoicePolicy.arith,
    V.zero, V.toFP, runPolicyA, ChoicePolicy.nanResult, FP.isNaN, V.isNaN,
    show (FP.fin false ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩ : FP f) = zero f false from rfl,
    mul_zero_inf]

theorem prefNaN_bits_ne : (V.prefNaN f false).bits ≠ (V.prefNaN f true).bits := by
  simp only [V.prefNaN, V.bits, Bool.false_eq_true, ite_false, ite_true]
  have := Nat.two_pow_pos (f.e + f.p - 1)
  omega

/-- **Two sound tiers can disagree on bits.** In every format, for every
extra-payload set `X` and every input `ρ`, the tiers `tierCtfe` and `tierRunA`
both refine `S`, yet on the program `toBits (0.0 * +∞)` they return different
bit patterns: `tierCtfe` returns the bits of the positive preferred quiet NaN
and `tierRunA` those of the negative preferred quiet NaN (they differ in the
sign bit only). -/
theorem sound_tiers_disagree_on_bits (X : Extra f) (ρ : Nat → V f) :
    RefinesS X (tierCtfe (f := f)) ∧ RefinesS X (tierRunA (f := f)) ∧
      (progBitsZeroMulInf f).runT tierCtfe ρ = (V.prefNaN f false).bits ∧
      (progBitsZeroMulInf f).runT tierRunA ρ = (V.prefNaN f true).bits ∧
      (progBitsZeroMulInf f).runT tierCtfe ρ ≠ (progBitsZeroMulInf f).runT tierRunA ρ := by
  refine ⟨tierOf_refinesS X _, tierOf_refinesS X _, progBitsZeroMulInf_runT_tierCtfe ρ,
    progBitsZeroMulInf_runT_tierRunA ρ, ?_⟩
  rw [progBitsZeroMulInf_runT_tierCtfe, progBitsZeroMulInf_runT_tierRunA]
  exact prefNaN_bits_ne

theorem FExpr.evalT_of_closed (τ : Tier f) (e : FExpr f) (he : e.closed = true)
    (ρ ρ' : Nat → V f) : e.evalT τ ρ = e.evalT τ ρ' := by
  induction e with
  | lit _ => rfl
  | var _ => simp [FExpr.closed] at he
  | prim p a b iha ihb =>
    simp only [FExpr.closed, Bool.and_eq_true] at he
    simp only [FExpr.evalT, iha he.1, ihb he.2]
  | neg a ih => simp only [FExpr.closed] at he; simp only [FExpr.evalT, ih he]
  | abs a ih => simp only [FExpr.closed] at he; simp only [FExpr.evalT, ih he]
  | copysign a b iha ihb =>
    simp only [FExpr.closed, Bool.and_eq_true] at he
    simp only [FExpr.evalT, iha he.1, ihb he.2]
  | selLt a b t e iha ihb iht ihe =>
    simp only [FExpr.closed, Bool.and_eq_true] at he
    simp only [FExpr.evalT, iha he.1.1.1, ihb he.1.1.2, iht he.1.2, ihe he.2]

theorem FExpr.evalS_of_evalS_fold {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (ρ : Nat → V f) : ∀ (e : FExpr f) (r : V f), (e.fold τ).evalS X ρ r → e.evalS X ρ r := by
  intro e
  induction e with
  | lit v => intro r h; rw [FExpr.fold] at h; simpa [FExpr.closed, FExpr.evalS, FExpr.evalT] using h
  | var i => intro r h; rw [FExpr.fold] at h; simpa [FExpr.closed, FExpr.evalS] using h
  | prim p a b iha ihb =>
    intro r h
    rw [FExpr.fold] at h
    split at h
    · rename_i hc
      simp only [FExpr.evalS] at h; subst h
      rw [FExpr.evalT_of_closed τ _ hc _ ρ]; exact FExpr.evalS_evalT_of_tierSound hτ _ ρ
    · obtain ⟨x, y, hx, hy, hr⟩ := h
      exact ⟨x, y, iha x hx, ihb y hy, hr⟩
  | neg a ih =>
    intro r h
    rw [FExpr.fold] at h
    split at h
    · rename_i hc
      simp only [FExpr.evalS] at h; subst h
      rw [FExpr.evalT_of_closed τ _ hc _ ρ]; exact FExpr.evalS_evalT_of_tierSound hτ _ ρ
    · obtain ⟨x, hx, hr⟩ := h
      exact ⟨x, ih x hx, hr⟩
  | abs a ih =>
    intro r h
    rw [FExpr.fold] at h
    split at h
    · rename_i hc
      simp only [FExpr.evalS] at h; subst h
      rw [FExpr.evalT_of_closed τ _ hc _ ρ]; exact FExpr.evalS_evalT_of_tierSound hτ _ ρ
    · obtain ⟨x, hx, hr⟩ := h
      exact ⟨x, ih x hx, hr⟩
  | copysign a b iha ihb =>
    intro r h
    rw [FExpr.fold] at h
    split at h
    · rename_i hc
      simp only [FExpr.evalS] at h; subst h
      rw [FExpr.evalT_of_closed τ _ hc _ ρ]; exact FExpr.evalS_evalT_of_tierSound hτ _ ρ
    · obtain ⟨x, y, hx, hy, hr⟩ := h
      exact ⟨x, y, iha x hx, ihb y hy, hr⟩
  | selLt a b t e iha ihb iht ihe =>
    intro r h
    rw [FExpr.fold] at h
    split at h
    · rename_i hc
      simp only [FExpr.evalS] at h; subst h
      rw [FExpr.evalT_of_closed τ _ hc _ ρ]; exact FExpr.evalS_evalT_of_tierSound hτ _ ρ
    · obtain ⟨x, y, hx, hy, hr⟩ := h
      refine ⟨x, y, iha x hx, ihb y hy, ?_⟩
      split
      · rename_i hc; simp only [hc, ↓reduceIte] at hr; exact iht r hr
      · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr; exact ihe r hr

/-- **Constant folding with a sound tier refines `S`.** If every choice of `τ`
lies in the sets of `S` (with extra payloads `X`), then every observation the
folded program `P.fold τ` can produce under `S` is one the original program
`P` can produce under `S`. In particular this holds for `τ = tierCtfe`. -/
theorem Prog.runS_of_runS_fold {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (P : Prog f) (ρ : Nat → V f) (n : Nat) : (P.fold τ).runS X ρ n → P.runS X ρ n := by
  cases P with
  | isNaN a =>
    rintro ⟨x, hx, rfl⟩; exact ⟨x, FExpr.evalS_of_evalS_fold hτ ρ a x hx, rfl⟩
  | eq a b =>
    rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨x, y, FExpr.evalS_of_evalS_fold hτ ρ a x hx, FExpr.evalS_of_evalS_fold hτ ρ b y hy, rfl⟩
  | lt a b =>
    rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨x, y, FExpr.evalS_of_evalS_fold hτ ρ a x hx, FExpr.evalS_of_evalS_fold hτ ρ b y hy, rfl⟩
  | signBit a =>
    rintro ⟨x, hx, rfl⟩; exact ⟨x, FExpr.evalS_of_evalS_fold hτ ρ a x hx, rfl⟩
  | toBits a =>
    rintro ⟨x, hx, rfl⟩; exact ⟨x, FExpr.evalS_of_evalS_fold hτ ρ a x hx, rfl⟩

/-- The open program `toBits (copysign (var 0) (0.0 * +∞))`: the input `var 0`
with the sign bit of the NaN `0.0 * +∞`. -/
def progBitsCopysignVarNaN (f : Fmt) : Prog f :=
  .toBits (.copysign (.var 0) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))

/-- **Folding with the compile-time tier changes a run-time tier's
observation.** In every format and for every input `ρ`, constant folding with
`tierCtfe` keeps the variable of `toBits (copysign (var 0) (0.0 * +∞))` and
replaces only its closed subexpression `0.0 * +∞` by the literal positive
preferred quiet NaN; on the resulting program the run-time tier `tierRunA`
computes a different observation than on the original program (the sign bit
of the result differs). -/
theorem fold_tierCtfe_changes_tierRunA_bits (ρ : Nat → V f) :
    (progBitsCopysignVarNaN f).fold tierCtfe =
        .toBits (.copysign (.var 0) (.lit (V.prefNaN f false))) ∧
      ((progBitsCopysignVarNaN f).fold tierCtfe).runT tierRunA ρ ≠
        (progBitsCopysignVarNaN f).runT tierRunA ρ := by
  have hc : tierCtfe .mul (V.zero f false) (V.inf false) = V.prefNaN f false := by
    show ctfePolicy.arith (mul (V.zero f false).toFP (V.inf false : V f).toFP) (V.zero f false)
      (.inf false) = _
    rw [show (V.zero f false).toFP = zero f false from rfl,
      show (V.inf false : V f).toFP = .inf false from rfl, mul_zero_inf]
    rfl
  have hr : tierRunA .mul (V.zero f false) (V.inf false) = V.prefNaN f true := by
    show runPolicyA.arith (mul (V.zero f false).toFP (V.inf false : V f).toFP) (V.zero f false)
      (.inf false) = _
    rw [show (V.zero f false).toFP = zero f false from rfl,
      show (V.inf false : V f).toFP = .inf false from rfl, mul_zero_inf]
    rfl
  have hfold : (progBitsCopysignVarNaN f).fold tierCtfe =
      .toBits (.copysign (.var 0) (.lit (V.prefNaN f false))) := by
    simp [progBitsCopysignVarNaN, Prog.fold, FExpr.fold, FExpr.closed, FExpr.evalT, hc]
  refine ⟨hfold, ?_⟩
  rw [hfold]
  simp only [progBitsCopysignVarNaN, Prog.runT, FExpr.evalT, hr, V.copysign, V.prefNaN,
    V.signBit, V.bits_withSign_true]
  have := Nat.two_pow_pos (f.e + f.p - 1)
  omega

end Toy.FloatTier
