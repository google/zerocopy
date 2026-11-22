/-
Kernel-checked Lean 4.34.1 formalization of:
  1. The 4-element `rustc` subtyping variance lattice (`Variance`, `glb`, `xform`),
     its algebraic laws, fixpoint monotonicity, and soundness of constructor polarity
     composition (`compiler/rustc_type_ir/src/lib.rs`,
     `compiler/rustc_hir_analysis/src/variance/{constraints,solve,terms}.rs`).
  2. Two-axis `dropck` / `#[may_dangle]` / `PhantomData<T>` soundness over
     reverse-declaration-order drop schedules (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`,
     `compiler/rustc_middle/src/ty/util.rs`, `compiler/rustc_borrowck/src/type_check/liveness/`).
  3. Edition 2021 vs 2024 `RPIT` (`impl Trait`) lifetime capture rules and `use<...>`
     overrides (`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`).
  4. `DispatchFromDyn` single-coerced-field + 1-byte-aligned-ZST ABI representation
     invariance and constructive counterexamples (`compiler/rustc_hir_analysis/src/coherence/builtin.rs`).

TCB / axiom discipline:
  - Purely constructive kernel proofs over finite and inductive data using
    structural recursion and definitional equality alone.
  - Audited via `#print axioms` to depend on at most `[propext]` (zero choice,
    zero compiler reflection, zero unfinished goals, zero partial definitions).
-/

namespace RustcVarianceDropckDispatch

/-! ## Part 1: Four-Element Subtyping Variance Lattice and Polarity Composition -/

/-- The 4-element variance lattice from `compiler/rustc_type_ir/src/lib.rs`.
`Debug` tokens in `rustc`: `bivariant = "*"`, `covariant = "+"`,
`contravariant = "-"`, `invariant = "o"`. -/
inductive Variance where
  | bivariant
  | covariant
  | contravariant
  | invariant
  deriving DecidableEq, Repr

namespace Variance

/-- Context-to-position variance composition (`Variance::xform` in
`compiler/rustc_type_ir/src/lib.rs`, PLDI'11 Figure 1). -/
noncomputable def xform : Variance → Variance → Variance
  | .covariant, .covariant => .covariant
  | .covariant, .contravariant => .contravariant
  | .covariant, .invariant => .invariant
  | .covariant, .bivariant => .bivariant
  | .contravariant, .covariant => .contravariant
  | .contravariant, .contravariant => .covariant
  | .contravariant, .invariant => .invariant
  | .contravariant, .bivariant => .bivariant
  | .invariant, _ => .invariant
  | .bivariant, _ => .bivariant

/-- Greatest lower bound in the `rustc` subtyping-permissiveness lattice
(`fn glb` in `compiler/rustc_hir_analysis/src/variance/solve.rs`):
`bivariant (*)` is top (least restrictive), `covariant (+)` and `contravariant (-)`
are incomparable middle elements, and `invariant (o)` is bottom (most restrictive). -/
noncomputable def glb : Variance → Variance → Variance
  | .invariant, _ => .invariant
  | _, .invariant => .invariant
  | .covariant, .contravariant => .invariant
  | .contravariant, .covariant => .invariant
  | .covariant, .covariant => .covariant
  | .contravariant, .contravariant => .contravariant
  | x, .bivariant => x
  | .bivariant, x => x

/-- Constraint-strength partial order `a ≤_c b`: `b` is at least as restrictive
as `a`, i.e., `bivariant ≤_c {covariant, contravariant} ≤_c invariant`. -/
noncomputable def constraintLe : Variance → Variance → Prop
  | .bivariant, _ => True
  | .covariant, .covariant => True
  | .covariant, .invariant => True
  | .contravariant, .contravariant => True
  | .contravariant, .invariant => True
  | .invariant, .invariant => True
  | _, _ => False

/-- Subtyping-permissiveness partial order `a ≤_p b` (the dual of `constraintLe`):
`invariant ≤_p {covariant, contravariant} ≤_p bivariant`. -/
noncomputable def permissiveLe (a b : Variance) : Prop := constraintLe b a

theorem xform_assoc (a b c : Variance) :
    xform (xform a b) c = xform a (xform b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xform_contra_contra_eq_cov :
    xform .contravariant .contravariant = .covariant := rfl

theorem xform_contra_involutive (v : Variance) :
    xform .contravariant (xform .contravariant v) = v := by
  cases v <;> rfl

theorem xform_cov_left (v : Variance) : xform .covariant v = v := by
  cases v <;> rfl

theorem xform_cov_right (v : Variance) : xform v .covariant = v := by
  cases v <;> rfl

theorem xform_inv_left (v : Variance) : xform .invariant v = .invariant := by
  cases v <;> rfl

theorem xform_biv_left (v : Variance) : xform .bivariant v = .bivariant := by
  cases v <;> rfl

/-- `xform` is non-commutative: `invariant.xform(bivariant) = invariant`,
whereas `bivariant.xform(invariant) = bivariant`. -/
theorem xform_not_comm :
    xform .invariant .bivariant ≠ xform .bivariant .invariant := by
  intro h
  cases h

theorem glb_comm (a b : Variance) : glb a b = glb b a := by
  cases a <;> cases b <;> rfl

theorem glb_assoc (a b c : Variance) : glb (glb a b) c = glb a (glb b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem glb_idem (a : Variance) : glb a a = a := by
  cases a <;> rfl

theorem glb_biv_left (a : Variance) : glb .bivariant a = a := by
  cases a <;> rfl

theorem glb_biv_right (a : Variance) : glb a .bivariant = a := by
  cases a <;> rfl

theorem glb_inv_left (a : Variance) : glb .invariant a = .invariant := by
  cases a <;> rfl

theorem glb_inv_right (a : Variance) : glb a .invariant = .invariant := by
  cases a <;> rfl

/-- `glb` is the exact join in the constraint-strength order `constraintLe`
(equivalently, the exact meet in `permissiveLe`). -/
theorem constraintLe_glb_left (a b : Variance) : constraintLe a (glb a b) := by
  cases a <;> cases b <;> trivial

theorem constraintLe_glb_right (a b : Variance) : constraintLe b (glb a b) := by
  cases a <;> cases b <;> trivial

theorem glb_least_upper_constraint (a b c : Variance)
    (ha : constraintLe a c) (hb : constraintLe b c) :
    constraintLe (glb a b) c := by
  cases a <;> cases b <;> cases c <;> first | trivial | exact ha | exact hb | cases ha | cases hb

/-- Right-distributivity of `xform` over `glb` holds unconditionally, ensuring
monotonicity of constraint evaluation in `variance/solve.rs`. -/
theorem xform_distrib_glb_right (a b c : Variance) :
    xform a (glb b c) = glb (xform a b) (xform a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Left-distributivity of `xform` over `glb` FAILS in `rustc`'s PLDI'11 algebra:
`(covariant.glb contravariant).xform bivariant = invariant.xform bivariant = invariant`,
whereas `(covariant.xform bivariant).glb (contravariant.xform bivariant) = bivariant`.
Consequently, `constraints.rs` treats parameterless leaf types as no-ops rather than
applying `xform(ambient, bivariant)`. -/
theorem xform_not_distrib_glb_left :
    xform (glb .covariant .contravariant) .bivariant ≠
      glb (xform .covariant .bivariant) (xform .contravariant .bivariant) := by
  intro h
  cases h

theorem xform_monotone_right (a b c : Variance) (h : constraintLe b c) :
    constraintLe (xform a b) (xform a c) := by
  cases a <;> cases b <;> cases c <;> first | trivial | cases h

end Variance

/-- Core Rust type constructors audited in the 12-constructor variance matrix,
parameterized by a single lifetime-carrying type parameter `param`. -/
inductive TyExpr where
  | unit
  | param
  | sharedRef (inner : TyExpr)
  | mutRef (inner : TyExpr)
  | rawConst (inner : TyExpr)
  | rawMut (inner : TyExpr)
  | fnTy (arg : TyExpr) (ret : TyExpr)
  | unsafeCell (inner : TyExpr)
  | phantomData (inner : TyExpr)
  | pair (fst : TyExpr) (snd : TyExpr)

/-- Whether `param` occurs syntactically anywhere inside `e`. -/
noncomputable def mentionsParam : TyExpr → Bool
  | .unit => false
  | .param => true
  | .sharedRef t => mentionsParam t
  | .mutRef t => mentionsParam t
  | .rawConst t => mentionsParam t
  | .rawMut t => mentionsParam t
  | .fnTy a r => mentionsParam a || mentionsParam r
  | .unsafeCell t => mentionsParam t
  | .phantomData t => mentionsParam t
  | .pair a b => mentionsParam a || mentionsParam b

/-- Constraint-accumulation variance inference matching
`compiler/rustc_hir_analysis/src/variance/{constraints,terms,solve}.rs`. -/
noncomputable def inferVariance (ambient : Variance) : TyExpr → Variance
  | .unit => .bivariant
  | .param => ambient
  | .sharedRef t => inferVariance ambient t
  | .mutRef t => inferVariance (Variance.xform ambient .invariant) t
  | .rawConst t => inferVariance ambient t
  | .rawMut t => inferVariance (Variance.xform ambient .invariant) t
  | .fnTy arg ret =>
      Variance.glb
        (inferVariance (Variance.xform ambient .contravariant) arg)
        (inferVariance ambient ret)
  | .unsafeCell t => inferVariance (Variance.xform ambient .invariant) t
  | .phantomData t => inferVariance (Variance.xform ambient .covariant) t
  | .pair a b => Variance.glb (inferVariance ambient a) (inferVariance ambient b)

/-- Any type expression that never mentions `param` imposes no constraints and
remains `bivariant` regardless of ambient context variance (mirrors the leaf-type
no-op in `constraints.rs:215-224` and why unused ADT params trigger `E0392`). -/
theorem inferVariance_of_not_mentionsParam (ambient : Variance) (e : TyExpr)
    (h : mentionsParam e = false) :
    inferVariance ambient e = .bivariant := by
  induction e generalizing ambient with
  | unit => rfl
  | param => cases h
  | sharedRef t ih => exact ih ambient h
  | mutRef t ih => exact ih (Variance.xform ambient .invariant) h
  | rawConst t ih => exact ih ambient h
  | rawMut t ih => exact ih (Variance.xform ambient .invariant) h
  | fnTy arg ret ihArg ihRet =>
      cases ha : mentionsParam arg <;> cases hr : mentionsParam ret
      · simp only [inferVariance]
        rw [ihArg (Variance.xform ambient .contravariant) ha, ihRet ambient hr]
        rfl
      · simp [mentionsParam, ha, hr] at h
      · simp [mentionsParam, ha, hr] at h
      · simp [mentionsParam, ha, hr] at h
  | unsafeCell t ih => exact ih (Variance.xform ambient .invariant) h
  | phantomData t ih => exact ih (Variance.xform ambient .covariant) h
  | pair a b iha ihb =>
      cases ha : mentionsParam a <;> cases hb : mentionsParam b
      · simp only [inferVariance]
        rw [iha ambient ha, ihb ambient hb]
        rfl
      · simp [mentionsParam, ha, hb] at h
      · simp [mentionsParam, ha, hb] at h
      · simp [mentionsParam, ha, hb] at h

/-- Polarity composition theorem: whenever `e` mentions `param`, ambient context
variance factors cleanly out of `inferVariance` via `Variance.xform`. -/
theorem inferVariance_ambient_factor (ambient : Variance) (e : TyExpr)
    (h : mentionsParam e = true) :
    inferVariance ambient e = Variance.xform ambient (inferVariance .covariant e) := by
  induction e generalizing ambient with
  | unit => cases h
  | param =>
      simp [inferVariance, Variance.xform_cov_right]
  | sharedRef t ih =>
      exact ih ambient h
  | mutRef t ih =>
      simp only [inferVariance]
      rw [ih (Variance.xform ambient .invariant) h, ih (Variance.xform .covariant .invariant) h,
        Variance.xform_cov_left, Variance.xform_assoc]
  | rawConst t ih =>
      exact ih ambient h
  | rawMut t ih =>
      simp only [inferVariance]
      rw [ih (Variance.xform ambient .invariant) h, ih (Variance.xform .covariant .invariant) h,
        Variance.xform_cov_left, Variance.xform_assoc]
  | fnTy arg ret ihArg ihRet =>
      simp only [inferVariance]
      cases ha : mentionsParam arg <;> cases hr : mentionsParam ret
      · simp [mentionsParam, ha, hr] at h
      · rw [inferVariance_of_not_mentionsParam _ arg ha,
          inferVariance_of_not_mentionsParam _ arg ha,
          ihRet ambient hr, Variance.glb_biv_left, Variance.glb_biv_left]
      · rw [ihArg (Variance.xform ambient .contravariant) ha,
          ihArg (Variance.xform .covariant .contravariant) ha,
          inferVariance_of_not_mentionsParam _ ret hr,
          inferVariance_of_not_mentionsParam _ ret hr,
          Variance.glb_biv_right, Variance.glb_biv_right,
          Variance.xform_cov_left, Variance.xform_assoc]
      · rw [ihArg (Variance.xform ambient .contravariant) ha,
          ihArg (Variance.xform .covariant .contravariant) ha,
          ihRet ambient hr,
          Variance.xform_cov_left,
          Variance.xform_assoc,
          Variance.xform_distrib_glb_right]
  | unsafeCell t ih =>
      simp only [inferVariance]
      rw [ih (Variance.xform ambient .invariant) h, ih (Variance.xform .covariant .invariant) h,
        Variance.xform_cov_left, Variance.xform_assoc]
  | phantomData t ih =>
      simp only [inferVariance, Variance.xform_cov_right]
      exact ih ambient h
  | pair a b iha ihb =>
      simp only [inferVariance]
      cases ha : mentionsParam a <;> cases hb : mentionsParam b
      · simp [mentionsParam, ha, hb] at h
      · rw [inferVariance_of_not_mentionsParam _ a ha,
          inferVariance_of_not_mentionsParam _ a ha,
          ihb ambient hb, Variance.glb_biv_left, Variance.glb_biv_left]
      · rw [iha ambient ha,
          inferVariance_of_not_mentionsParam _ b hb,
          inferVariance_of_not_mentionsParam _ b hb,
          Variance.glb_biv_right, Variance.glb_biv_right]
      · rw [iha ambient ha, ihb ambient hb, Variance.xform_distrib_glb_right]

/-- Semantic lifetime-outlives subtyping relation on `TyExpr`, where a natural
number models a lifetime's scope extent (`r2 ≤ r1` means `'r1 : 'r2`, so
`&'r1 u8 <: &'r2 u8`). -/
noncomputable def tySubtype : TyExpr → Nat → Nat → Prop
  | .unit, _, _ => True
  | .param, r1, r2 => r2 ≤ r1
  | .sharedRef t, r1, r2 => tySubtype t r1 r2
  | .mutRef t, r1, r2 => tySubtype t r1 r2 ∧ tySubtype t r2 r1
  | .rawConst t, r1, r2 => tySubtype t r1 r2
  | .rawMut t, r1, r2 => tySubtype t r1 r2 ∧ tySubtype t r2 r1
  | .fnTy arg ret, r1, r2 => tySubtype arg r2 r1 ∧ tySubtype ret r1 r2
  | .unsafeCell t, r1, r2 => tySubtype t r1 r2 ∧ tySubtype t r2 r1
  | .phantomData t, r1, r2 => tySubtype t r1 r2
  | .pair a b, r1, r2 => tySubtype a r1 r2 ∧ tySubtype b r1 r2

theorem tySubtype_refl (e : TyExpr) (r : Nat) : tySubtype e r r := by
  induction e with
  | unit => trivial
  | param => exact Nat.le_refl r
  | sharedRef t ih => exact ih
  | mutRef t ih => exact ⟨ih, ih⟩
  | rawConst t ih => exact ih
  | rawMut t ih => exact ⟨ih, ih⟩
  | fnTy a b iha ihb => exact ⟨iha, ihb⟩
  | unsafeCell t ih => exact ⟨ih, ih⟩
  | phantomData t ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩

/-- Variance specification: `v` sound for `e` means `r2 ≤ r1` implies the
corresponding directional subtyping obligation on `e`. -/
noncomputable def varianceHolds (v : Variance) (e : TyExpr) (r1 r2 : Nat) : Prop :=
  match v with
  | .bivariant => tySubtype e r1 r2 ∧ tySubtype e r2 r1
  | .covariant => r2 ≤ r1 → tySubtype e r1 r2
  | .contravariant => r1 ≤ r2 → tySubtype e r1 r2
  | .invariant => r1 = r2 → tySubtype e r1 r2

private theorem varianceHolds_weaken {v1 v2 : Variance} {e : TyExpr} {r1 r2 : Nat}
    (hle : Variance.constraintLe v1 v2) (h : varianceHolds v1 e r1 r2) :
    varianceHolds v2 e r1 r2 := by
  cases v1 <;> cases v2
  · exact h
  · intro _; exact h.1
  · intro _; exact h.1
  · intro _; exact h.1
  · cases hle
  · exact h
  · cases hle
  · intro heq; subst heq; exact tySubtype_refl e r1
  · cases hle
  · cases hle
  · exact h
  · intro heq; subst heq; exact tySubtype_refl e r1
  · cases hle
  · cases hle
  · cases hle
  · exact h

/-- Soundness of `inferVariance .covariant` with respect to semantic lifetime subtyping
`tySubtype`: whatever variance the inference lattice derives is semantically valid
for every pair of lifetime extents `(r1, r2)`. -/
theorem inferVariance_sound (e : TyExpr) (r1 r2 : Nat) :
    varianceHolds (inferVariance .covariant e) e r1 r2 := by
  induction e generalizing r1 r2 with
  | unit =>
      exact ⟨trivial, trivial⟩
  | param =>
      intro hle; exact hle
  | sharedRef t ih =>
      exact ih r1 r2
  | mutRef t ih =>
      cases hm : mentionsParam t with
      | false =>
          have hb := inferVariance_of_not_mentionsParam .covariant t hm
          have hbi := inferVariance_of_not_mentionsParam .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left, hbi]
          have h1 := ih r1 r2
          rw [hb] at h1
          exact ⟨h1, ⟨h1.2, h1.1⟩⟩
      | true =>
          have hfac := inferVariance_ambient_factor .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left]
          rw [hfac]
          cases hv : inferVariance .covariant t with
          | bivariant =>
              have h1 := ih r1 r2
              rw [hv] at h1
              intro _
              exact h1
          | covariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | contravariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | invariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
  | rawConst t ih =>
      exact ih r1 r2
  | rawMut t ih =>
      cases hm : mentionsParam t with
      | false =>
          have hb := inferVariance_of_not_mentionsParam .covariant t hm
          have hbi := inferVariance_of_not_mentionsParam .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left, hbi]
          have h1 := ih r1 r2
          rw [hb] at h1
          exact ⟨h1, ⟨h1.2, h1.1⟩⟩
      | true =>
          have hfac := inferVariance_ambient_factor .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left]
          rw [hfac]
          cases hv : inferVariance .covariant t with
          | bivariant =>
              have h1 := ih r1 r2
              rw [hv] at h1
              intro _
              exact h1
          | covariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | contravariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | invariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
  | fnTy arg ret ihArg ihRet =>
      have hArg := ihArg r2 r1
      have hArgRev := ihArg r1 r2
      have hRet := ihRet r1 r2
      have hRetRev := ihRet r2 r1
      have hStep : inferVariance .contravariant arg =
          Variance.xform .contravariant (inferVariance .covariant arg) := by
        cases hm : mentionsParam arg with
        | false =>
            rw [inferVariance_of_not_mentionsParam .contravariant arg hm,
              inferVariance_of_not_mentionsParam .covariant arg hm]
            rfl
        | true =>
            exact inferVariance_ambient_factor .contravariant arg hm
      simp only [inferVariance, Variance.xform_cov_left]
      rw [hStep]
      cases hva : inferVariance .covariant arg <;> cases hvr : inferVariance .covariant ret
      · rw [hva] at hArg hArgRev; rw [hvr] at hRet hRetRev
        exact ⟨⟨hArg.1, hRet.1⟩, ⟨hArgRev.1, hRetRev.1⟩⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg.1, hRet hle⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg.1, hRet hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg hle, hRet.1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg hle, hRet hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg hle, hRet.1⟩
      · rw [hva] at hArg; rw [hvr] at hRet
        intro hle; exact ⟨hArg hle, hRet hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl arg r1, tySubtype_refl ret r1⟩
  | unsafeCell t ih =>
      cases hm : mentionsParam t with
      | false =>
          have hb := inferVariance_of_not_mentionsParam .covariant t hm
          have hbi := inferVariance_of_not_mentionsParam .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left, hbi]
          have h1 := ih r1 r2
          rw [hb] at h1
          exact ⟨h1, ⟨h1.2, h1.1⟩⟩
      | true =>
          have hfac := inferVariance_ambient_factor .invariant t hm
          simp only [inferVariance, Variance.xform_cov_left]
          rw [hfac]
          cases hv : inferVariance .covariant t with
          | bivariant =>
              have h1 := ih r1 r2
              rw [hv] at h1
              intro _
              exact h1
          | covariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | contravariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
          | invariant =>
              intro heq; subst heq; exact ⟨tySubtype_refl t r1, tySubtype_refl t r1⟩
  | phantomData t ih =>
      exact ih r1 r2
  | pair a b iha ihb =>
      simp only [inferVariance]
      have ha1 := iha r1 r2
      have ha2 := iha r2 r1
      have hb1 := ihb r1 r2
      have hb2 := ihb r2 r1
      cases hva : inferVariance .covariant a <;> cases hvb : inferVariance .covariant b
      · rw [hva] at ha1 ha2; rw [hvb] at hb1 hb2
        exact ⟨⟨ha1.1, hb1.1⟩, ⟨ha2.1, hb2.1⟩⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1.1, hb1 hle⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1.1, hb1 hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1 hle, hb1.1⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1 hle, hb1 hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1 hle, hb1.1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · rw [hva] at ha1; rw [hvb] at hb1
        intro hle; exact ⟨ha1 hle, hb1 hle⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩
      · intro heq; subst heq; exact ⟨tySubtype_refl a r1, tySubtype_refl b r1⟩

/-- Exact verification of all 12 audited constructor variances against the lattice. -/
theorem twelve_constructor_variances :
    inferVariance .covariant (.sharedRef .param) = .covariant ∧
    inferVariance .covariant (.mutRef .param) = .invariant ∧
    inferVariance .covariant (.rawConst .param) = .covariant ∧
    inferVariance .covariant (.rawMut .param) = .invariant ∧
    inferVariance .covariant (.fnTy .param .unit) = .contravariant ∧
    inferVariance .covariant (.fnTy .unit .param) = .covariant ∧
    inferVariance .covariant (.fnTy (.fnTy .param .unit) .unit) = .covariant ∧
    inferVariance .covariant (.unsafeCell .param) = .invariant ∧
    inferVariance .covariant (.phantomData .param) = .covariant ∧
    inferVariance .covariant (.phantomData (.fnTy .param .unit)) = .contravariant ∧
    inferVariance .covariant (.phantomData (.fnTy .unit .param)) = .covariant ∧
    inferVariance .covariant (.phantomData (.fnTy .param .param)) = .invariant :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Two-Axis `dropck`, `#[may_dangle]`, and `PhantomData<T>` Soundness -/

/-- Specification of a generic owning container `C<T>` implementing `Drop`
with raw-pointer interior (`*mut T`). -/
structure ContainerSpec where
  /-- Whether `Drop` is declared `unsafe impl<#[may_dangle] T> Drop`. -/
  hasMayDangle : Bool
  /-- Whether the struct carries `PhantomData<T>` (true) vs no marker or
  `PhantomData<fn() -> T>` (false). Note both `PhantomData<T>` and
  `PhantomData<fn() -> T>` have identical `Covariant` variance. -/
  hasPhantomOwnsT : Bool
  /-- Axis 1 behavior: does `C<T>::drop` invoke `T`'s drop glue? -/
  dropRunsTDtor : Bool
  /-- Axis 2 behavior: does `C<T>::drop` directly inspect/read `T` itself
  (e.g., via `Display::fmt` or dereferencing `*mut T`)? -/
  dropDirectlyReadsT : Bool
  deriving DecidableEq, Repr

/-- Specification of a concrete element type `T` instantiated inside `C<T>`
that contains a borrow `&'a S` of a local binding `s : S`. -/
structure ElemSpec where
  /-- Whether `T` holds a reference to the local binding `s`. -/
  borrowsLocalS : Bool
  /-- Whether `T` has a non-trivial destructor that reads the borrowed reference
  (e.g., `PrintOnDrop<'a>` has `true`; trivially-droppable `Copy` `&'a String`
  has `false`). -/
  tDropReadsRef : Bool
  deriving DecidableEq, Repr

/-- Declaration order of local bindings in a lexical scope.
Rust drops local bindings in reverse declaration order (`List.reverse`). -/
inductive DeclSlot where
  | localS
  | guardC
  deriving DecidableEq, Repr

/-- Dynamic drop-execution outcome over a 2-slot scope. -/
inductive DropOutcome where
  | ok
  | useAfterFree
  deriving DecidableEq, Repr

/-- Operational state of the local binding `s` during reverse-order scope exit. -/
structure ScopeMem where
  sAlive : Bool
  deriving DecidableEq, Repr

/-- Execute one slot's drop step in the reverse-declaration-order drop schedule. -/
noncomputable def execDropSlot (c : ContainerSpec) (e : ElemSpec) (st : ScopeMem) :
    DeclSlot → Except DropOutcome ScopeMem
  | .localS => .ok { sAlive := false }
  | .guardC =>
      let accessesBorrow :=
        e.borrowsLocalS &&
          ((c.dropRunsTDtor && e.tDropReadsRef) || c.dropDirectlyReadsT)
      if accessesBorrow && !st.sAlive then
        .error .useAfterFree
      else
        .ok st

/-- Structural execution helper over a concrete drop list. -/
noncomputable def execDropList (c : ContainerSpec) (e : ElemSpec) (st : ScopeMem) :
    List DeclSlot → DropOutcome
  | [] => .ok
  | slot :: rest =>
      match execDropSlot c e st slot with
      | .ok st' => execDropList c e st' rest
      | .error err => err

/-- Execute a full drop schedule (given in declaration order, therefore executed
in `List.reverse declOrder`). -/
noncomputable def execDropSchedule (c : ContainerSpec) (e : ElemSpec)
    (declOrder : List DeclSlot) : DropOutcome :=
  execDropList c e { sAlive := true } declOrder.reverse

/-- Static `rustc` drop-check acceptance predicate matching
`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`
(`trivial_dropck_outlives` + `adt_dtorck_constraint`).

When `declOrder = [.guardC, .localS]` (so `s` drops before `_guard`):
- Without `#[may_dangle]`, `dropck` requires `T` (hence `'a`) to outlive `_guard`'s
  drop point -> rejects (`E0597`) whenever `e.borrowsLocalS = true`.
- With `#[may_dangle]`, `dropck` waives the `Drop`-header requirement on `T`, and
  instead checks non-trivial fields (`PhantomData<T>` -> pushes `T` onto `dtorck_types`,
  which then requires `'a` live iff `!trivial_dropck_outlives(T)`, i.e. `e.tDropReadsRef`). -/
noncomputable def sDroppedBeforeGuard (declOrder : List DeclSlot) : Bool :=
  match declOrder with
  | [.guardC, .localS] => true
  | _ => false

noncomputable def dropckAccepts (c : ContainerSpec) (e : ElemSpec)
    (declOrder : List DeclSlot) : Bool :=
  if !sDroppedBeforeGuard declOrder || !e.borrowsLocalS then
    true
  else if !c.hasMayDangle then
    false
  else
    !(c.hasPhantomOwnsT && e.tDropReadsRef)

/-- Two valid 2-binding lexical scopes: safe order `let (s, _guard)` and
reverse order `let (_guard, s)`. -/
noncomputable def validTwoSlotScope (declOrder : List DeclSlot) : Prop :=
  declOrder = [.localS, .guardC] ∨ declOrder = [.guardC, .localS]

/-- Soundness predicate for a container `c`: across all element types `e` and
all valid 2-slot declaration orders accepted by `dropck`, reverse-order scope
destruction never triggers a use-after-free. -/
noncomputable def ContainerUafFreeUnderDropck (c : ContainerSpec) : Prop :=
  ∀ (e : ElemSpec) (declOrder : List DeclSlot),
    validTwoSlotScope declOrder →
    dropckAccepts c e declOrder = true →
    execDropSchedule c e declOrder = .ok

/-- **Main Theorem (Two-Axis `dropck` Soundness Characterization)**:
For any container declaring `unsafe impl<#[may_dangle] T> Drop`, `dropck`
guarantees UAF-freedom across all accepted instantiations and declaration orders
**if and only if** BOTH:
  1. Axis 1 (ownership obligation): if `Drop` runs `T`'s destructor, the struct
     declares ownership via `PhantomData<T>` (`hasPhantomOwnsT = true`); AND
  2. Axis 2 (`#[may_dangle]` non-access obligation): `Drop` never directly reads
     or inspects `T` (`dropDirectlyReadsT = false`), because trivially-droppable
     `Copy` references (`&'a String`) bypass `PhantomData<T>`'s dropck check. -/
theorem dropck_may_dangle_uaf_free_iff_ownership_and_no_direct_read
    (c : ContainerSpec) (hmd : c.hasMayDangle = true) :
    ContainerUafFreeUnderDropck c ↔
      ((c.dropRunsTDtor = true → c.hasPhantomOwnsT = true) ∧
       c.dropDirectlyReadsT = false) := by
  constructor
  · intro hSafe
    constructor
    · intro hRuns
      cases hPh : c.hasPhantomOwnsT with
      | true => rfl
      | false =>
          have h := hSafe
            { borrowsLocalS := true, tDropReadsRef := true }
            [.guardC, .localS]
            (Or.inr rfl)
            (by simp [dropckAccepts, sDroppedBeforeGuard, hmd, hPh])
          simp [execDropSchedule, execDropList, execDropSlot, hRuns] at h
    · cases hDir : c.dropDirectlyReadsT with
      | false => rfl
      | true =>
          have h := hSafe
            { borrowsLocalS := true, tDropReadsRef := false }
            [.guardC, .localS]
            (Or.inr rfl)
            (by simp [dropckAccepts, sDroppedBeforeGuard, hmd])
          simp [execDropSchedule, execDropList, execDropSlot, hDir] at h
  · rintro ⟨hAxis1, hAxis2⟩ e declOrder hScope hAcc
    rcases hScope with rfl | rfl
    · simp [execDropSchedule, execDropList, execDropSlot]
    · cases hBor : e.borrowsLocalS with
      | false =>
          simp [execDropSchedule, execDropList, execDropSlot, hBor]
      | true =>
          cases hRuns : c.dropRunsTDtor with
          | false =>
              simp [execDropSchedule, execDropList, execDropSlot, hBor, hRuns, hAxis2]
          | true =>
              have hPh : c.hasPhantomOwnsT = true := hAxis1 hRuns
              cases hDtor : e.tDropReadsRef with
              | false =>
                  simp [execDropSchedule, execDropList, execDropSlot, hBor, hRuns, hDtor, hAxis2]
              | true =>
                  simp [dropckAccepts, sDroppedBeforeGuard, hBor, hmd, hPh, hDtor] at hAcc

/-- Without `#[may_dangle]`, `dropck` unconditionally enforces UAF-freedom
even when `Drop` directly inspects `T` or omits `PhantomData<T>`. -/
theorem dropck_without_may_dangle_always_uaf_free
    (c : ContainerSpec) (hno : c.hasMayDangle = false) :
    ContainerUafFreeUnderDropck c := by
  intro e declOrder hScope hAcc
  rcases hScope with rfl | rfl
  · simp [execDropSchedule, execDropList, execDropSlot]
  · cases hBor : e.borrowsLocalS with
    | false => simp [execDropSchedule, execDropList, execDropSlot, hBor]
    | true => simp [dropckAccepts, sDroppedBeforeGuard, hBor, hno] at hAcc

/-- **Constructive Counterexample 1 (Axis 1)**:
`MyBox<T>(*mut T, PhantomData<fn() -> T>)` has identical `Covariant` variance to
`PhantomData<T>`, yet omits `dropck` ownership (`hasPhantomOwnsT = false`).
`dropck` accepts `let (_guard, s)` with `PrintOnDrop<'a>`, and reverse-order
destruction triggers a live UAF. -/
theorem ce1_phantom_fn_misses_dropck_ownership_uaf :
    let myBoxPhantomFn : ContainerSpec :=
      { hasMayDangle := true
        hasPhantomOwnsT := false
        dropRunsTDtor := true
        dropDirectlyReadsT := false }
    let printOnDrop : ElemSpec :=
      { borrowsLocalS := true, tDropReadsRef := true }
    inferVariance .covariant (.phantomData (.fnTy .unit .param)) =
      inferVariance .covariant (.phantomData .param) ∧
    dropckAccepts myBoxPhantomFn printOnDrop [.guardC, .localS] = true ∧
    execDropSchedule myBoxPhantomFn printOnDrop [.guardC, .localS] = .useAfterFree :=
  ⟨rfl, rfl, rfl⟩

/-- **Constructive Counterexample 2 (Axis 2)**:
`InspectBox<T: Display>(*mut T, PhantomData<T>)` includes `PhantomData<T>`,
yet directly inspects `T` inside `unsafe impl<#[may_dangle] T> Drop`.
For trivially-droppable `Copy` `T = &'a String` (`tDropReadsRef = false`),
`dropck` accepts `let (_guard, s)` and reverse-order destruction triggers UAF. -/
theorem ce2_direct_read_of_copy_ref_under_may_dangle_bypasses_phantom_t :
    let inspectBoxWithPhantomT : ContainerSpec :=
      { hasMayDangle := true
        hasPhantomOwnsT := true
        dropRunsTDtor := true
        dropDirectlyReadsT := true }
    let copyRef : ElemSpec :=
      { borrowsLocalS := true, tDropReadsRef := false }
    dropckAccepts inspectBoxWithPhantomT copyRef [.guardC, .localS] = true ∧
    execDropSchedule inspectBoxWithPhantomT copyRef [.guardC, .localS] = .useAfterFree :=
  ⟨rfl, rfl⟩

/-! ## Part 3: Edition 2021 vs 2024 `RPIT` Lifetime Capture Rules -/

inductive RustEdition where
  | ed2021
  | ed2024
  deriving DecidableEq, Repr

inductive OpaqueOrigin where
  | freeFnReturn
  | inherentMethodReturn
  | traitOrImplRpitit
  | asyncFn
  | typeAliasTait
  deriving DecidableEq, Repr

/-- Exact mirror of `opaque_captures_all_in_scope_lifetimes` in
`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`. -/
noncomputable def opaqueCapturesAllInScopeLifetimes
    (edition : RustEdition) (origin : OpaqueOrigin) (hasUseBound : Bool) : Bool :=
  if hasUseBound then
    false
  else
    match origin with
    | .asyncFn | .typeAliasTait => true
    | .traitOrImplRpitit => true
    | .freeFnReturn | .inherentMethodReturn =>
        match edition with
        | .ed2021 => false
        | .ed2024 => true

/-- Whether an unmentioned in-scope lifetime `'a` is captured by `impl Trait`. -/
noncomputable def rpitCapturesUnmentionedLifetime
    (edition : RustEdition) (origin : OpaqueOrigin)
    (useExplicit : Option Bool) : Bool :=
  match useExplicit with
  | some explicitlyListed => explicitlyListed
  | none => opaqueCapturesAllInScopeLifetimes edition origin false

theorem rpit_use_bound_overrides_edition_default
    (ed : RustEdition) (orig : OpaqueOrigin) (listed : Bool) :
    opaqueCapturesAllInScopeLifetimes ed orig true = false ∧
    rpitCapturesUnmentionedLifetime ed orig (some listed) = listed := by
  exact ⟨rfl, rfl⟩

theorem rpit_edition_2021_vs_2024_delta :
    rpitCapturesUnmentionedLifetime .ed2021 .freeFnReturn none = false ∧
    rpitCapturesUnmentionedLifetime .ed2024 .freeFnReturn none = true ∧
    rpitCapturesUnmentionedLifetime .ed2024 .freeFnReturn (some false) = false ∧
    rpitCapturesUnmentionedLifetime .ed2024 .freeFnReturn (some true) = true ∧
    rpitCapturesUnmentionedLifetime .ed2021 .inherentMethodReturn none = false ∧
    rpitCapturesUnmentionedLifetime .ed2024 .inherentMethodReturn none = true ∧
    rpitCapturesUnmentionedLifetime .ed2021 .traitOrImplRpitit none = true ∧
    rpitCapturesUnmentionedLifetime .ed2024 .traitOrImplRpitit none = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 4: `DispatchFromDyn` ABI-Preserving Smart-Pointer Rules -/

inductive StructRepr where
  | rustDefault
  | transparent
  | reprC
  | reprPacked
  deriving DecidableEq, Repr

/-- Layout and coercion metadata for one struct field, mirroring
`visit_implementation_of_dispatch_from_dyn` in
`compiler/rustc_hir_analysis/src/coherence/builtin.rs`. -/
structure FieldSpec where
  sizeBytes : Nat
  alignBytes : Nat
  isPhantomData : Bool
  mentionsNonRegionParam : Bool
  changesUnderCoercion : Bool
  fieldDispatchFromDyn : Bool
  deriving DecidableEq, Repr

structure SmartPtrStruct where
  repr : StructRepr
  fields : List FieldSpec
  deriving DecidableEq, Repr

/-- Representation-level pointer ABI summary (total size, total alignment,
and whether the type is ABI-compatible with its single non-ZST pointer field). -/
inductive AbiKind where
  | transparentPointer (sizeBytes : Nat) (alignBytes : Nat)
  | nonTransparentAggregate (sizeBytes : Nat) (alignBytes : Nat)
  deriving DecidableEq, Repr

/-- Exact structural natural-number maximum. -/
noncomputable def natMax : Nat → Nat → Nat
  | 0, b => b
  | a + 1, 0 => a + 1
  | a + 1, b + 1 => (natMax a b) + 1

theorem natMax_one_left {n : Nat} (h : 1 ≤ n) : natMax 1 n = n := by
  cases n with
  | zero => cases h
  | succ k =>
      cases k with
      | zero => rfl
      | succ m => rfl

theorem natMax_one_right {n : Nat} (h : 1 ≤ n) : natMax n 1 = n := by
  cases n with
  | zero => cases h
  | succ k =>
      cases k with
      | zero => rfl
      | succ m => rfl

/-- Compute aggregate alignment across a list of fields (starting from 1). -/
noncomputable def fieldsAlign : List FieldSpec → Nat
  | [] => 1
  | f :: fs => natMax f.alignBytes (fieldsAlign fs)

/-- Compute sum of field sizes across a list of fields (before alignment padding). -/
noncomputable def fieldsRawSize : List FieldSpec → Nat
  | [] => 0
  | f :: fs => f.sizeBytes + fieldsRawSize fs

/-- Count non-zero-sized fields in a struct. -/
noncomputable def nonZstCount : List FieldSpec → Nat
  | [] => 0
  | f :: fs => (match f.sizeBytes with | 0 => 0 | _ + 1 => 1) + nonZstCount fs

/-- Soundness predicate for `PhantomData<T>` layout guarantee from
`library/core/src/marker.rs`: `size_of == 0` and `align_of == 1`. -/
noncomputable def PhantomLayoutsValid (fields : List FieldSpec) : Prop :=
  ∀ f, f ∈ fields → f.isPhantomData = true → f.sizeBytes = 0 ∧ f.alignBytes = 1

/-- Purely structural `Nat.beq` reflexivity (zero axioms). -/
theorem nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_refl n

/-- Check whether a field is accepted as an ignored auxiliary field by
`visit_implementation_of_dispatch_from_dyn` (`builtin.rs:374-414`):
either `PhantomData`, or a non-changing 1-ZST that mentions no type/const param. -/
noncomputable def isIgnoredExtraField (f : FieldSpec) : Bool :=
  f.isPhantomData ||
    (!f.changesUnderCoercion &&
     Nat.beq f.sizeBytes 0 &&
     Nat.beq f.alignBytes 1 &&
     !f.mentionsNonRegionParam)

/-- Filter to the fields that `DispatchFromDyn` must coerce (matching `coerced_fields`
in `builtin.rs:371-416`). -/
noncomputable def coercedFields : List FieldSpec → List FieldSpec
  | [] => []
  | f :: fs =>
      if f.isPhantomData then
        coercedFields fs
      else if !f.changesUnderCoercion then
        coercedFields fs
      else
        f :: coercedFields fs

/-- Check whether all non-`PhantomData`, non-changing fields pass the `E0378`
1-ZST and no-type/const-generic guard (`builtin.rs:391-411`). -/
noncomputable def allUnchangedFieldsPassE0378 : List FieldSpec → Bool
  | [] => true
  | f :: fs =>
      let okHere :=
        if f.isPhantomData || f.changesUnderCoercion then true
        else (Nat.beq f.sizeBytes 0 && Nat.beq f.alignBytes 1 && !f.mentionsNonRegionParam)
      okHere && allUnchangedFieldsPassE0378 fs

/-- Full `DispatchFromDyn` struct admissibility predicate mirroring
`visit_implementation_of_dispatch_from_dyn` (`builtin.rs:349-460`). -/
noncomputable def dispatchFromDynAdmissible (s : SmartPtrStruct) : Bool :=
  let reprOk :=
    match s.repr with
    | .reprC | .reprPacked => false
    | .rustDefault | .transparent => true
  if !reprOk then
    false
  else if !allUnchangedFieldsPassE0378 s.fields then
    false
  else
    match coercedFields s.fields with
    | [fPtr] => fPtr.fieldDispatchFromDyn
    | _ => false

/-- Struct calling-convention ABI classifier when the single non-ZST field has
pointer layout `(ptrSize, ptrAlign)` (assuming `ptrSize > 0` and `1 ≤ ptrAlign`,
with `ptrSize` already a multiple of `ptrAlign`, as for thin/wide pointers). -/
noncomputable def classifySmartPtrAbi (s : SmartPtrStruct) (ptrSize ptrAlign : Nat) : AbiKind :=
  let sz := fieldsRawSize s.fields
  let al := fieldsAlign s.fields
  let nz := nonZstCount s.fields
  match s.repr with
  | .reprC | .reprPacked => .nonTransparentAggregate sz al
  | .rustDefault | .transparent =>
      match Nat.beq sz ptrSize, Nat.beq al ptrAlign, Nat.beq nz 1 with
      | true, true, true => .transparentPointer ptrSize ptrAlign
      | _, _, _ => .nonTransparentAggregate sz al

private theorem ignored_fields_layout
    (fs : List FieldSpec)
    (hPh : PhantomLayoutsValid fs)
    (hE : allUnchangedFieldsPassE0378 fs = true)
    (hEmpty : coercedFields fs = []) :
    fieldsRawSize fs = 0 ∧ fieldsAlign fs = 1 ∧ nonZstCount fs = 0 := by
  induction fs with
  | nil =>
      exact ⟨rfl, rfl, rfl⟩
  | cons f rest ih =>
      have hPhRest : PhantomLayoutsValid rest := fun g hg hgp =>
        hPh g (List.mem_cons_of_mem f hg) hgp
      cases hfp : f.isPhantomData with
      | true =>
          have ⟨hsz, hal⟩ := hPh f List.mem_cons_self hfp
          simp [allUnchangedFieldsPassE0378, hfp] at hE
          simp [coercedFields, hfp] at hEmpty
          have ⟨rsz, ral, rnz⟩ := ih hPhRest hE hEmpty
          simp [fieldsRawSize, fieldsAlign, nonZstCount, hsz, hal, rsz, ral, rnz, natMax]
      | false =>
          cases hch : f.changesUnderCoercion with
          | true =>
              simp [coercedFields, hfp, hch] at hEmpty
          | false =>
              simp [allUnchangedFieldsPassE0378, hfp, hch] at hE
              simp [coercedFields, hfp, hch] at hEmpty
              have hsz : f.sizeBytes = 0 := hE.1.1.1
              have hal : f.alignBytes = 1 := hE.1.1.2
              have ⟨rsz, ral, rnz⟩ := ih hPhRest hE.2 hEmpty
              simp [fieldsRawSize, fieldsAlign, nonZstCount, hsz, hal, rsz, ral, rnz, natMax]

private theorem single_coerced_field_layout
    (fs : List FieldSpec) (fPtr : FieldSpec)
    (hPh : PhantomLayoutsValid fs)
    (hE : allUnchangedFieldsPassE0378 fs = true)
    (hOne : coercedFields fs = [fPtr])
    (hPtrAlign : 1 ≤ fPtr.alignBytes)
    (hPtrPos : fPtr.sizeBytes ≠ 0) :
    fieldsRawSize fs = fPtr.sizeBytes ∧
    fieldsAlign fs = fPtr.alignBytes ∧
    nonZstCount fs = 1 := by
  induction fs with
  | nil =>
      cases hOne
  | cons f rest ih =>
      have hPhRest : PhantomLayoutsValid rest := fun g hg hgp =>
        hPh g (List.mem_cons_of_mem f hg) hgp
      cases hfp : f.isPhantomData with
      | true =>
          have ⟨hsz, hal⟩ := hPh f List.mem_cons_self hfp
          simp [allUnchangedFieldsPassE0378, hfp] at hE
          simp [coercedFields, hfp] at hOne
          have ⟨rsz, ral, rnz⟩ := ih hPhRest hE hOne
          refine ⟨?_, ?_, ?_⟩
          · simp [fieldsRawSize, hsz, rsz]
          · simp [fieldsAlign, hal, ral, natMax_one_left hPtrAlign]
          · simp [nonZstCount, hsz, rnz]
      | false =>
          cases hch : f.changesUnderCoercion with
          | false =>
              simp [allUnchangedFieldsPassE0378, hfp, hch] at hE
              simp [coercedFields, hfp, hch] at hOne
              have hsz : f.sizeBytes = 0 := hE.1.1.1
              have hal : f.alignBytes = 1 := hE.1.1.2
              have ⟨rsz, ral, rnz⟩ := ih hPhRest hE.2 hOne
              refine ⟨?_, ?_, ?_⟩
              · simp [fieldsRawSize, hsz, rsz]
              · simp [fieldsAlign, hal, ral, natMax_one_left hPtrAlign]
              · simp [nonZstCount, hsz, rnz]
          | true =>
              simp [allUnchangedFieldsPassE0378, hfp, hch] at hE
              simp [coercedFields, hfp, hch] at hOne
              rcases hOne with ⟨rfl, hRestEmpty⟩
              have ⟨rsz, ral, rnz⟩ := ignored_fields_layout rest hPhRest hE hRestEmpty
              refine ⟨?_, ?_, ?_⟩
              · simp [fieldsRawSize, rsz]
              · simp [fieldsAlign, ral, natMax_one_right hPtrAlign]
              · cases hfsz : f.sizeBytes with
                | zero => exact False.elim (hPtrPos hfsz)
                | succ k => simp [nonZstCount, hfsz, rnz]

/-- **Main Theorem (`DispatchFromDyn` ABI-Equivalence)**:
Whenever a struct `s` satisfies `dispatchFromDynAdmissible s = true` with valid
`PhantomData` 1-ZST layout and a single coerced pointer field `fPtr` (size `> 0`,
alignment `≥ 1`), `s` has exact size `fPtr.sizeBytes`, exact alignment
`fPtr.alignBytes`, exactly one non-ZST field, and is transparently ABI-equivalent
to `fPtr`. -/
theorem dispatchFromDyn_preserves_pointer_abi
    (s : SmartPtrStruct) (fPtr : FieldSpec)
    (hAdm : dispatchFromDynAdmissible s = true)
    (hCoerced : coercedFields s.fields = [fPtr])
    (hPh : PhantomLayoutsValid s.fields)
    (hPtrAlign : 1 ≤ fPtr.alignBytes)
    (hPtrPos : fPtr.sizeBytes ≠ 0) :
    fieldsRawSize s.fields = fPtr.sizeBytes ∧
    fieldsAlign s.fields = fPtr.alignBytes ∧
    nonZstCount s.fields = 1 ∧
    classifySmartPtrAbi s fPtr.sizeBytes fPtr.alignBytes =
      .transparentPointer fPtr.sizeBytes fPtr.alignBytes := by
  cases hRepr : s.repr with
  | reprC =>
      simp [dispatchFromDynAdmissible, hRepr] at hAdm
  | reprPacked =>
      simp [dispatchFromDynAdmissible, hRepr] at hAdm
  | rustDefault =>
      cases hE : allUnchangedFieldsPassE0378 s.fields with
      | false =>
          simp [dispatchFromDynAdmissible, hRepr, hE] at hAdm
      | true =>
          have ⟨hsz, hal, hnz⟩ :=
            single_coerced_field_layout s.fields fPtr hPh hE hCoerced hPtrAlign hPtrPos
          refine ⟨hsz, hal, hnz, ?_⟩
          unfold classifySmartPtrAbi
          dsimp only
          rw [hRepr, hsz, hal, hnz]
          dsimp only
          rw [nat_beq_refl, nat_beq_refl]
  | transparent =>
      cases hE : allUnchangedFieldsPassE0378 s.fields with
      | false =>
          simp [dispatchFromDynAdmissible, hRepr, hE] at hAdm
      | true =>
          have ⟨hsz, hal, hnz⟩ :=
            single_coerced_field_layout s.fields fPtr hPh hE hCoerced hPtrAlign hPtrPos
          refine ⟨hsz, hal, hnz, ?_⟩
          unfold classifySmartPtrAbi
          dsimp only
          rw [hRepr, hsz, hal, hnz]
          dsimp only
          rw [nat_beq_refl, nat_beq_refl]

/-- **Constructive Counterexample 3 (Over-aligned ZST breaks `DispatchFromDyn` ABI)**:
`BadAlignedPtr<T>(*const T, Align16Zst)` on 64-bit (`*const dyn Foo` has size 16,
align 8; `Align16Zst` has size 0, align 16) raises struct alignment from 8 to 16,
violating raw-pointer ABI transparency, and is rejected (`E0378`). -/
theorem ce3_overaligned_zst_breaks_dispatch_from_dyn_abi :
    let widePtr : FieldSpec :=
      { sizeBytes := 16, alignBytes := 8, isPhantomData := false,
        mentionsNonRegionParam := true, changesUnderCoercion := true,
        fieldDispatchFromDyn := true }
    let align16Zst : FieldSpec :=
      { sizeBytes := 0, alignBytes := 16, isPhantomData := false,
        mentionsNonRegionParam := false, changesUnderCoercion := false,
        fieldDispatchFromDyn := false }
    let badAlignedPtr : SmartPtrStruct :=
      { repr := .rustDefault, fields := [widePtr, align16Zst] }
    dispatchFromDynAdmissible badAlignedPtr = false ∧
    fieldsAlign badAlignedPtr.fields = 16 ∧
    fieldsAlign badAlignedPtr.fields ≠ widePtr.alignBytes ∧
    classifySmartPtrAbi badAlignedPtr 16 8 = .nonTransparentAggregate 16 16 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro h
  cases h

/-- Positive witness: `PhantomTPtr<T>(*const T, PhantomData<T>)` and
`GoodZstPtr<T>(*const T, UnitZst)` are both admissible and ABI-equivalent to `*const T`. -/
theorem phantom_and_1zst_smart_ptrs_preserve_abi :
    let widePtr : FieldSpec :=
      { sizeBytes := 16, alignBytes := 8, isPhantomData := false,
        mentionsNonRegionParam := true, changesUnderCoercion := true,
        fieldDispatchFromDyn := true }
    let phantomT : FieldSpec :=
      { sizeBytes := 0, alignBytes := 1, isPhantomData := true,
        mentionsNonRegionParam := true, changesUnderCoercion := true,
        fieldDispatchFromDyn := false }
    let unitZst : FieldSpec :=
      { sizeBytes := 0, alignBytes := 1, isPhantomData := false,
        mentionsNonRegionParam := false, changesUnderCoercion := false,
        fieldDispatchFromDyn := false }
    let phantomPtr : SmartPtrStruct :=
      { repr := .rustDefault, fields := [widePtr, phantomT] }
    let unitZstPtr : SmartPtrStruct :=
      { repr := .rustDefault, fields := [widePtr, unitZst] }
    dispatchFromDynAdmissible phantomPtr = true ∧
    classifySmartPtrAbi phantomPtr 16 8 = .transparentPointer 16 8 ∧
    dispatchFromDynAdmissible unitZstPtr = true ∧
    classifySmartPtrAbi unitZstPtr 16 8 = .transparentPointer 16 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative witnesses matching `E0378` (extra `u64`, `#[repr(C)]`, const-generic ZST)
and `E0375` (custom generic `MyZst<T>` changing under `T -> U`). -/
theorem extra_field_repr_c_and_custom_generic_zst_rejected :
    let widePtr : FieldSpec :=
      { sizeBytes := 16, alignBytes := 8, isPhantomData := false,
        mentionsNonRegionParam := true, changesUnderCoercion := true,
        fieldDispatchFromDyn := true }
    let extraU64 : FieldSpec :=
      { sizeBytes := 8, alignBytes := 8, isPhantomData := false,
        mentionsNonRegionParam := false, changesUnderCoercion := false,
        fieldDispatchFromDyn := false }
    let customGenZst : FieldSpec :=
      { sizeBytes := 0, alignBytes := 1, isPhantomData := false,
        mentionsNonRegionParam := true, changesUnderCoercion := true,
        fieldDispatchFromDyn := false }
    let constGenZst : FieldSpec :=
      { sizeBytes := 0, alignBytes := 1, isPhantomData := false,
        mentionsNonRegionParam := true, changesUnderCoercion := false,
        fieldDispatchFromDyn := false }
    dispatchFromDynAdmissible { repr := .rustDefault, fields := [widePtr, extraU64] } = false ∧
    dispatchFromDynAdmissible { repr := .reprC, fields := [widePtr] } = false ∧
    dispatchFromDynAdmissible { repr := .rustDefault, fields := [widePtr, customGenZst] } = false ∧
    (coercedFields [widePtr, customGenZst]).length = 2 ∧
    dispatchFromDynAdmissible { repr := .rustDefault, fields := [widePtr, constGenZst] } = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end RustcVarianceDropckDispatch
