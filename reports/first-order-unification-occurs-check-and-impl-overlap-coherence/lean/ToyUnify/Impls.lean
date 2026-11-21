import ToyUnify.Matching

/-!
# Impl headers, derivable trait facts, and overlap

* `Impl`: a header `impl<vars> Trait for SelfTy where Trait'(U), …`; the generic parameters
  are the variables of the header.
* `Implements I tr ty`: the ground fact `ty: tr` is derivable from the impl set `I` (least fixed
  point: an impl applies at a grounding instance whose where-clause facts are derivable).
* Semantic overlap: `HeadersOverlap` (self types share a ground instance, where-clauses ignored)
  and `ImplsOverlapIn I` (additionally every where-clause holds in `I` at that instance).
* The checker's verdict `overlapCheckSaysDisjoint` (traits differ or `unify` fails on the self
  types) is a different object from the semantic properties.
-/

namespace Toy.Unify

/-- A where-clause bound `Trait(ty)`, e.g. `T: Display`. -/
structure Bound where
  trait : Nat
  ty : Term
  deriving Repr, DecidableEq

/-- An impl header `impl<vars> trait for selfTy where bounds`. The generic parameters are the
variables occurring in `selfTy` and `bounds`. -/
structure Impl where
  trait : Nat
  selfTy : Term
  bounds : List Bound
  deriving Repr, DecidableEq

/-- A set of impls (the impls visible to the crate making a judgement). -/
abbrev ImplSet := List Impl

/-- All variables of an impl header (self type and where-clauses). -/
def Impl.vars (i : Impl) : List Nat := i.selfTy.vars ++ i.bounds.flatMap (fun b => b.ty.vars)

/-- All trait symbols of an impl header (implemented trait and where-clause traits). -/
def Impl.traits (i : Impl) : List Nat := i.trait :: i.bounds.map (fun b => b.trait)

/-- All constructor symbols of an impl header. -/
def Impl.ctors (i : Impl) : List Nat := i.selfTy.ctors ++ i.bounds.flatMap (fun b => b.ty.ctors)

/-- `Implements I tr ty`: the ground fact `ty: tr` is derivable from `I`. An impl `i ∈ I`
yields `tr = i.trait` at `ty = θ i.selfTy` for any `θ` grounding the self type such that every
where-clause `b` of `i` holds at `θ b.ty`. Captures trait-solving over a fixed set of impls
(no negative impls, no auto traits, no associated types). -/
inductive Implements (I : ImplSet) : Nat → Term → Prop
  | intro (i : Impl) (θ : Subst) (hi : i ∈ I) (hg : IsGround (subst θ i.selfTy))
      (hb : ∀ b ∈ i.bounds, Implements I b.trait (subst θ b.ty)) :
      Implements I i.trait (subst θ i.selfTy)

/-- Two terms share a ground instance, instantiating each with its own substitution (so shared
variable names do not matter). -/
def CommonGroundInstance (s t : Term) : Prop :=
  ∃ θ₁ θ₂ : Subst, IsGround (subst θ₁ s) ∧ subst θ₁ s = subst θ₂ t

/-- Semantic header overlap, ignoring where-clauses: same trait and the self types share a
ground instance. -/
def HeadersOverlap (i j : Impl) : Prop := i.trait = j.trait ∧ CommonGroundInstance i.selfTy j.selfTy

/-- Semantic overlap in an impl set: same trait, and some ground type is an instance of both self
types at instantiations under which all where-clauses of both impls are derivable in `I`. This is
a closed-world notion: where-clauses are evaluated in the fixed set `I`, which need not contain
`i` or `j`. -/
def ImplsOverlapIn (I : ImplSet) (i j : Impl) : Prop :=
  i.trait = j.trait ∧ ∃ θ₁ θ₂ : Subst, IsGround (subst θ₁ i.selfTy) ∧
    subst θ₁ i.selfTy = subst θ₂ j.selfTy ∧
    (∀ b ∈ i.bounds, Implements I b.trait (subst θ₁ b.ty)) ∧
    (∀ b ∈ j.bounds, Implements I b.trait (subst θ₂ b.ty))

/-- The unification-based checker's verdict "these headers are disjoint": the traits differ, or
`unify` fails on the two self types. Where-clauses are not consulted. -/
def overlapCheckSaysDisjoint (i j : Impl) : Bool :=
  i.trait != j.trait || (unify i.selfTy j.selfTy).isNone

/-! ## Helper lemmas -/

theorem Implements.inv {I : ImplSet} {tr : Nat} {ty : Term} (h : Implements I tr ty) :
    ∃ i θ, i ∈ I ∧ i.trait = tr ∧ subst θ i.selfTy = ty ∧ IsGround ty ∧
      ∀ b ∈ i.bounds, Implements I b.trait (subst θ b.ty) := by
  cases h with
  | intro i θ hi hg hb => exact ⟨i, θ, hi, rfl, rfl, hg, hb⟩

theorem Implements.isGround {I : ImplSet} {tr : Nat} {ty : Term} (h : Implements I tr ty) :
    IsGround ty := by
  obtain ⟨_, _, _, _, _, hg, _⟩ := h.inv
  exact hg

theorem Implements.mono {I I' : ImplSet} (hsub : ∀ i ∈ I, i ∈ I') {tr : Nat} {ty : Term}
    (h : Implements I tr ty) : Implements I' tr ty := by
  induction h with
  | intro i θ hi hg _ ih => exact .intro i θ (hsub i hi) hg ih

theorem implements_of_mem_of_bounds_nil {I : ImplSet} {i : Impl} (hi : i ∈ I)
    (hb : i.bounds = []) (hg : IsGround i.selfTy) : Implements I i.trait i.selfTy := by
  have h := Implements.intro (I := I) i [] hi (by rw [subst_nil]; exact hg)
    (by intro b hbm; rw [hb] at hbm; simp at hbm)
  rwa [subst_nil] at h

theorem implsOverlapIn_headersOverlap {I : ImplSet} {i j : Impl} (h : ImplsOverlapIn I i j) :
    HeadersOverlap i j := by
  obtain ⟨htr, θ₁, θ₂, hg, heq, _, _⟩ := h
  exact ⟨htr, θ₁, θ₂, hg, heq⟩

/-! ## Example impls

Traits: `Tr` (10), `A` (11), `B` (12), `C` (13). -/

/-- `impl A for u8`. -/
def implA_u8 : Impl := ⟨11, u8, []⟩
/-- `impl B for u32`. -/
def implB_u32 : Impl := ⟨12, u32, []⟩
/-- `impl<T: A> Tr for T`. -/
def i1 : Impl := ⟨10, .var 0, [⟨11, .var 0⟩]⟩
/-- `impl<U: B> Tr for U` (variables renamed apart from `i1`). -/
def i2 : Impl := ⟨10, .var 1, [⟨12, .var 1⟩]⟩
/-- The impl set `{impl A for u8, impl B for u32, i1, i2}`: no type implements both `A`
and `B`. -/
def I_AB : ImplSet := [implA_u8, implB_u32, i1, i2]

theorem implements_I_AB_A_iff (ty : Term) : Implements I_AB 11 ty ↔ ty = u8 := by
  constructor
  · intro h
    obtain ⟨i, θ, hi, htr, hty, _, _⟩ := h.inv
    simp only [I_AB, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [← hty]; exact subst_of_isGround (by decide) θ
    · simp [implB_u32] at htr
    · simp [i1] at htr
    · simp [i2] at htr
  · rintro rfl
    exact implements_of_mem_of_bounds_nil (i := implA_u8) (by simp [I_AB]) rfl (by decide)

theorem implements_I_AB_B_iff (ty : Term) : Implements I_AB 12 ty ↔ ty = u32 := by
  constructor
  · intro h
    obtain ⟨i, θ, hi, htr, hty, _, _⟩ := h.inv
    simp only [I_AB, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [implA_u8] at htr
    · rw [← hty]; exact subst_of_isGround (by decide) θ
    · simp [i1] at htr
    · simp [i2] at htr
  · rintro rfl
    exact implements_of_mem_of_bounds_nil (i := implB_u32) (by simp [I_AB]) rfl (by decide)

/-! ## Definition examples -/

theorem implements_example : Implements I_AB 11 u8 := (implements_I_AB_A_iff u8).2 rfl
theorem not_implements_example : ¬ Implements I_AB 11 u32 := by
  rw [implements_I_AB_A_iff]; decide
/-- `Tr` holds for `u8` via `i1` (its where-clause `u8: A` is derivable). -/
theorem implements_via_bound_example : Implements I_AB 10 u8 := by
  have h := Implements.intro (I := I_AB) i1 [(0, u8)] (by simp [I_AB]) (by decide)
    (by
      intro b hb
      simp only [i1, List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb
      exact implements_example)
  exact h
theorem implements_isGround_example : ¬ Implements I_AB 10 (.var 0) := fun h =>
  absurd h.isGround (by decide)

theorem impl_vars_example : i1.vars = [0, 0] := by decide
theorem not_mem_impl_vars_example : 1 ∉ i1.vars := by decide
theorem impl_traits_example : i1.traits = [10, 11] := by decide
theorem not_mem_impl_traits_example : 12 ∉ i1.traits := by decide
theorem impl_ctors_example : implA_u8.ctors = [0] := by decide
theorem impl_ctors_nil_example : i1.ctors = [] := by decide

theorem commonGroundInstance_example : CommonGroundInstance (pair (.var 0) u8) (pair u32 (.var 0)) :=
  ⟨[(0, u32)], [(0, u8)], by decide, by decide⟩
theorem not_commonGroundInstance_example : ¬ CommonGroundInstance u8 u32 := by
  rintro ⟨θ₁, θ₂, _, h⟩
  simp [u8, u32, subst_con] at h

theorem headersOverlap_example : HeadersOverlap i1 i2 :=
  ⟨rfl, [(0, u8)], [(1, u8)], by decide, by decide⟩
theorem not_headersOverlap_example : ¬ HeadersOverlap i1 implA_u8 := by
  rintro ⟨h, _⟩
  simp [i1, implA_u8] at h

theorem overlapCheckSaysDisjoint_example :
    overlapCheckSaysDisjoint ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by decide
theorem overlapCheckSaysDisjoint_false_example : overlapCheckSaysDisjoint i1 i2 = false := by
  decide

/-! ## Merging and grounding substitutions -/

/-- Use `θ₁` on the variables `vs` and `θ₂` elsewhere. -/
def mergeOn (vs : List Nat) (θ₁ θ₂ : Subst) : Subst :=
  vs.map (fun x => (x, substVar θ₁ x)) ++ θ₂

theorem substVar_mergeOn_left {vs : List Nat} {θ₁ θ₂ : Subst} {x : Nat} (hx : x ∈ vs) :
    substVar (mergeOn vs θ₁ θ₂) x = substVar θ₁ x := by
  unfold mergeOn
  induction vs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.cons_append, substVar_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hys
      · contradiction
      · simp [hxy, ih hys]

theorem substVar_mergeOn_right {vs : List Nat} {θ₁ θ₂ : Subst} {y : Nat} (hy : y ∉ vs) :
    substVar (mergeOn vs θ₁ θ₂) y = substVar θ₂ y := by
  unfold mergeOn
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hy
    simp [List.map_cons, List.cons_append, substVar_cons, hy.1, ih hy.2]

/-- Map every variable of `vs` to `u`. -/
def groundAllTo (u : Term) (vs : List Nat) : Subst := vs.map (fun z => (z, u))

theorem substVar_groundAllTo {u : Term} {vs : List Nat} {x : Nat} (hx : x ∈ vs) :
    substVar (groundAllTo u vs) x = u := by
  unfold groundAllTo
  induction vs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, substVar_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hys
      · contradiction
      · simp [hxy, ih hys]

mutual
theorem vars_subst_groundAllTo_nil {u : Term} (hu : u.vars = []) (vs : List Nat) :
    ∀ t : Term, (∀ x ∈ t.vars, x ∈ vs) → (subst (groundAllTo u vs) t).vars = []
  | .var x, h => by
    have hx : x ∈ vs := h x (by simp [Term.vars])
    simp [subst, substVar_groundAllTo hx, hu]
  | .con _ ts, h => by
    simp only [subst, Term.vars]
    exact varsList_subst_groundAllTo_nil hu vs ts (by simpa [Term.vars] using h)
theorem varsList_subst_groundAllTo_nil {u : Term} (hu : u.vars = []) (vs : List Nat) :
    ∀ ts : List Term, (∀ x ∈ Term.varsList ts, x ∈ vs) →
      Term.varsList (substList (groundAllTo u vs) ts) = []
  | [], _ => rfl
  | a :: as, h => by
    simp only [substList, Term.varsList, List.append_eq_nil_iff]
    exact ⟨vars_subst_groundAllTo_nil hu vs a (fun x hx => h x (by simp [Term.varsList, hx])),
           varsList_subst_groundAllTo_nil hu vs as (fun x hx => h x (by simp [Term.varsList, hx]))⟩
end

/-- Every term has a ground instance (all variables sent to `u8`). -/
theorem isGround_subst_groundAllTo (t : Term) : IsGround (subst (groundAllTo u8 t.vars) t) :=
  vars_subst_groundAllTo_nil rfl t.vars t (fun _ h => h)

/-! ## Results -/

/-- Sound "disjoint" verdict: for impls whose self types are renamed apart, if the checker says
disjoint (traits differ or `unify` fails), the headers have no common ground instance. -/
theorem not_headersOverlap_of_overlapCheckSaysDisjoint {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true) :
    ¬ HeadersOverlap i j := by
  rintro ⟨htr, θ₁, θ₂, _, heq⟩
  let τ := mergeOn i.selfTy.vars θ₁ θ₂
  have hτ : Unifies τ i.selfTy j.selfTy := by
    unfold Unifies
    rw [subst_congr_vars i.selfTy (fun x hx => substVar_mergeOn_left hx),
      subst_congr_vars j.selfTy (fun y hy => substVar_mergeOn_right (fun hyi => hdisj y hyi hy)),
      heq]
  obtain ⟨σ, hσ⟩ := unify_complete hτ
  simp [overlapCheckSaysDisjoint, htr, hσ] at h

/-- Corollary: under the same hypotheses, the impls overlap in no impl set whatsoever. -/
theorem not_implsOverlapIn_of_overlapCheckSaysDisjoint {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true)
    (I : ImplSet) : ¬ ImplsOverlapIn I i j :=
  fun hov => not_headersOverlap_of_overlapCheckSaysDisjoint hdisj h (implsOverlapIn_headersOverlap hov)

/-- Characterization ignoring where-clauses: for self types renamed apart, the headers overlap
exactly when the traits agree and `unify` succeeds on the self types. -/
theorem headersOverlap_iff_unify_isSome {i j : Impl} (hdisj : VarsDisjoint i.selfTy j.selfTy) :
    HeadersOverlap i j ↔ i.trait = j.trait ∧ (unify i.selfTy j.selfTy).isSome = true := by
  constructor
  · intro hov
    refine ⟨hov.1, ?_⟩
    cases hu : unify i.selfTy j.selfTy with
    | some _ => rfl
    | none =>
      exact absurd hov (not_headersOverlap_of_overlapCheckSaysDisjoint hdisj
        (by simp [overlapCheckSaysDisjoint, hu]))
  · rintro ⟨htr, hsome⟩
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hsome
    let θ := groundAllTo u8 (subst σ i.selfTy).vars
    refine ⟨htr, Subst.comp θ σ, Subst.comp θ σ, ?_, ?_⟩
    · rw [subst_comp]
      exact isGround_subst_groundAllTo _
    · rw [subst_comp, subst_comp, unify_sound hσ]

/-- Characterization with where-clauses: for impls whose variables (self types and
where-clauses) are renamed apart, they overlap in `I` exactly when the traits agree, `unify`
returns some `σ` on the self types, and some `θ` grounds `σ i.selfTy` while every where-clause of
both impls holds in `I` at `θ ∘ σ`. -/
theorem implsOverlapIn_iff_mgu_instance (I : ImplSet) {i j : Impl}
    (hdisj : ∀ x ∈ i.vars, x ∉ j.vars) :
    ImplsOverlapIn I i j ↔
      i.trait = j.trait ∧ ∃ σ, unify i.selfTy j.selfTy = some σ ∧
        ∃ θ : Subst, IsGround (subst θ (subst σ i.selfTy)) ∧
          ∀ b ∈ i.bounds ++ j.bounds, Implements I b.trait (subst θ (subst σ b.ty)) := by
  constructor
  · rintro ⟨htr, θ₁, θ₂, hg, heq, hb1, hb2⟩
    let τ := mergeOn i.vars θ₁ θ₂
    have hi_self : subst τ i.selfTy = subst θ₁ i.selfTy :=
      subst_congr_vars _ (fun x hx => substVar_mergeOn_left (by simp [Impl.vars, hx]))
    have hj_self : subst τ j.selfTy = subst θ₂ j.selfTy :=
      subst_congr_vars _ (fun y hy =>
        substVar_mergeOn_right (fun hyi => hdisj y hyi (by simp [Impl.vars, hy])))
    have hτ : Unifies τ i.selfTy j.selfTy := by unfold Unifies; rw [hi_self, hj_self, heq]
    obtain ⟨σ, hσ⟩ := unify_complete hτ
    refine ⟨htr, σ, hσ, τ, ?_, ?_⟩
    · rw [unify_mgu_factor hσ hτ, hi_self]; exact hg
    · intro b hb
      rw [unify_mgu_factor hσ hτ]
      simp only [List.mem_append] at hb
      rcases hb with hbi | hbj
      · have : subst τ b.ty = subst θ₁ b.ty :=
          subst_congr_vars _ (fun x hx => substVar_mergeOn_left (by
            simp only [Impl.vars, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨b, hbi, hx⟩))
        rw [this]; exact hb1 b hbi
      · have : subst τ b.ty = subst θ₂ b.ty :=
          subst_congr_vars _ (fun y hy => substVar_mergeOn_right (fun hyi => hdisj y hyi (by
            simp only [Impl.vars, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨b, hbj, hy⟩)))
        rw [this]; exact hb2 b hbj
  · rintro ⟨htr, σ, hσ, θ, hg, hb⟩
    refine ⟨htr, Subst.comp θ σ, Subst.comp θ σ, ?_, ?_, ?_, ?_⟩
    · rw [subst_comp]; exact hg
    · rw [subst_comp, subst_comp, unify_sound hσ]
    · intro b hbi; rw [subst_comp]; exact hb b (List.mem_append_left _ hbi)
    · intro b hbj; rw [subst_comp]; exact hb b (List.mem_append_right _ hbj)

/-! ## Non-vacuity -/

/-- Hypotheses of `not_headersOverlap_of_overlapCheckSaysDisjoint` hold for
`impl<T> Tr for Vec<T>` and `impl<U> Tr for Box<U>`. -/
theorem not_headersOverlap_of_overlapCheckSaysDisjoint_nonvacuous :
    VarsDisjoint (vec (.var 0)) (box (.var 1)) ∧
      overlapCheckSaysDisjoint ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by decide

/-- Hypothesis of `headersOverlap_iff_unify_isSome` holds for `i1`, `i2`. -/
theorem headersOverlap_iff_unify_isSome_nonvacuous : VarsDisjoint i1.selfTy i2.selfTy := by decide

/-- Hypothesis of `implsOverlapIn_iff_mgu_instance` holds for `i1`, `i2`. -/
theorem implsOverlapIn_iff_mgu_instance_nonvacuous : ∀ x ∈ i1.vars, x ∉ i2.vars := by decide

/-! ## Counterexamples -/

/-- `impl Tr for (T, u8)` and `impl Tr for (u32, T)`, written with the same variable `T`. -/
def iShared1 : Impl := ⟨10, pair (.var 0) u8, []⟩
/-- See `iShared1`. -/
def iShared2 : Impl := ⟨10, pair u32 (.var 0), []⟩

/-- Renaming apart cannot be dropped (instance: two impls of one trait without where-clauses,
whose self types share the variable name `T`): with the shared name, `unify` fails (so the
checker says disjoint), the characterization `headersOverlap_iff_unify_isSome` fails, and yet the
headers overlap at `(u32, u8)`, in every impl set. -/
theorem overlapCheck_needs_renaming_apart :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjoint iShared1 iShared2 = true ∧
      HeadersOverlap iShared1 iShared2 ∧ (∀ I, ImplsOverlapIn I iShared1 iShared2) ∧
      ¬ (HeadersOverlap iShared1 iShared2 ↔
          iShared1.trait = iShared2.trait ∧ (unify iShared1.selfTy iShared2.selfTy).isSome = true) := by
  have hov : HeadersOverlap iShared1 iShared2 := ⟨rfl, [(0, u32)], [(0, u8)], by decide, by decide⟩
  refine ⟨by decide, by decide, hov, ?_, ?_⟩
  · intro I
    refine ⟨rfl, [(0, u32)], [(0, u8)], by decide, by decide, ?_, ?_⟩ <;>
      (intro b hb; simp [iShared1, iShared2] at hb)
  · intro hiff
    have hsome := (hiff.1 hov).2
    revert hsome
    decide

/-- `impl<T, W: A> Tr for (T, u8)`: the where-clause variable `W` is not in the self type. -/
def iW1 : Impl := ⟨10, pair (.var 0) u8, [⟨11, .var 5⟩]⟩
/-- `impl<V, W: B> Tr for (u32, V)`: shares only the where-clause variable `W` with `iW1`. -/
def iW2 : Impl := ⟨10, pair u32 (.var 1), [⟨12, .var 5⟩]⟩

/-- Renaming apart only the self types is not enough for `implsOverlapIn_iff_mgu_instance`: the
self types of `iW1`, `iW2` are disjoint, the impls overlap in `I_AB` (`W` is `u8` in one and
`u32` in the other), but no single `θ` makes `W: A` and `W: B` both hold. -/
theorem implsOverlapIn_iff_mgu_instance_needs_bound_vars_disjoint :
    VarsDisjoint iW1.selfTy iW2.selfTy ∧ ¬ (∀ x ∈ iW1.vars, x ∉ iW2.vars) ∧
      ImplsOverlapIn I_AB iW1 iW2 ∧
      ¬ (∃ σ, unify iW1.selfTy iW2.selfTy = some σ ∧
        ∃ θ : Subst, IsGround (subst θ (subst σ iW1.selfTy)) ∧
          ∀ b ∈ iW1.bounds ++ iW2.bounds,
            Implements I_AB b.trait (subst θ (subst σ b.ty))) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · refine ⟨rfl, [(0, u32), (5, u8)], [(1, u8), (5, u32)], by decide, by decide, ?_, ?_⟩
    · intro b hb
      simp only [iW1, List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb
      exact (implements_I_AB_A_iff _).2 (by decide)
    · intro b hb
      simp only [iW2, List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb
      exact (implements_I_AB_B_iff _).2 (by decide)
  · rintro ⟨σ, hσ, θ, _, hb⟩
    have hu : unify iW1.selfTy iW2.selfTy = some [(1, u8), (0, u32)] := by decide
    rw [hu] at hσ
    cases hσ
    have hA := hb ⟨11, .var 5⟩ (by simp [iW1])
    have hB := hb ⟨12, .var 5⟩ (by simp [iW2])
    have e5 : subst [(1, u8), (0, u32)] (.var 5) = .var 5 := by decide
    simp only [e5] at hA hB
    rw [implements_I_AB_A_iff] at hA
    rw [implements_I_AB_B_iff, hA] at hB
    exact absurd hB (by decide)

/-- Where-clauses break the converse of the sound verdict: `impl<T: A> Tr for T` and
`impl<U: B> Tr for U` have unifiable self types (so the checker does not say disjoint, and the
headers overlap), yet they do not overlap in `I_AB`, where no type implements both `A` and `B`. -/
theorem headersOverlap_not_implsOverlapIn :
    HeadersOverlap i1 i2 ∧ Unifiable i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjoint i1 i2 = false ∧
      (¬ ∃ ty, Implements I_AB 11 ty ∧ Implements I_AB 12 ty) ∧ ¬ ImplsOverlapIn I_AB i1 i2 := by
  refine ⟨headersOverlap_example, ⟨[(0, .var 1)], by decide⟩, by decide, ?_, ?_⟩
  · rintro ⟨ty, hA, hB⟩
    rw [implements_I_AB_A_iff] at hA
    rw [implements_I_AB_B_iff, hA] at hB
    exact absurd hB (by decide)
  · rintro ⟨_, θ₁, θ₂, _, heq, hb1, hb2⟩
    have hA := hb1 ⟨11, .var 0⟩ (by simp [i1])
    have hB := hb2 ⟨12, .var 1⟩ (by simp [i2])
    simp only [i1, i2] at heq hA hB
    rw [implements_I_AB_A_iff] at hA
    rw [implements_I_AB_B_iff, ← heq, hA] at hB
    exact absurd hB (by decide)

/-- Non-monotonicity of where-clause-based disjointness: adding the single impl
`impl B for u8` to `I_AB` makes `i1` and `i2` overlap at `u8` — `u8` instantiates both self
types (`T := u8`, `U := u8`), and `u8: A` and `u8: B` are both derivable. -/
theorem implsOverlapIn_not_monotone :
    ¬ ImplsOverlapIn I_AB i1 i2 ∧
      subst [(0, u8)] i1.selfTy = u8 ∧ subst [(1, u8)] i2.selfTy = u8 ∧
      Implements (I_AB ++ [⟨12, u8, []⟩]) 11 u8 ∧ Implements (I_AB ++ [⟨12, u8, []⟩]) 12 u8 ∧
      ImplsOverlapIn (I_AB ++ [⟨12, u8, []⟩]) i1 i2 := by
  have hA : Implements (I_AB ++ [⟨12, u8, []⟩]) 11 u8 :=
    implements_of_mem_of_bounds_nil (i := implA_u8) (by simp [I_AB]) rfl (by decide)
  have hB : Implements (I_AB ++ [⟨12, u8, []⟩]) 12 u8 :=
    implements_of_mem_of_bounds_nil (i := ⟨12, u8, []⟩) (by simp) rfl (by decide)
  refine ⟨headersOverlap_not_implsOverlapIn.2.2.2.2, by decide, by decide, hA, hB, ?_⟩
  refine ⟨rfl, [(0, u8)], [(1, u8)], by decide, by decide, ?_, ?_⟩
  · intro b hb
    simp only [i1, List.mem_cons, List.mem_nil_iff, or_false] at hb
    subst hb
    exact hA
  · intro b hb
    simp only [i2, List.mem_cons, List.mem_nil_iff, or_false] at hb
    subst hb
    exact hB

end Toy.Unify
