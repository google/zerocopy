/-
Patch-closed and unrestricted hypothesis classes, explicit point-patch
(lookup-table) witnesses for untested inputs, and impossibility of finite
teaching sets over infinite domains.
-/
import Toy.Witness.Core

namespace Toy.Witness

universe u v

/-- A hypothesis class `H` is unrestricted if every total function `X → Y`
belongs to `H` (no structural, syntactic, or state-space restriction on
candidate implementations). -/
def IsUnrestricted {X : Type u} {Y : Type v} (H : HypothesisClass X Y) : Prop :=
  ∀ f : X → Y, H f

/-- A codomain `Y` is nontrivial if it contains at least two distinct values
(otherwise all functions `X → Y` are extensionally equal). -/
def HasTwoDistinct (Y : Type v) : Prop :=
  ∃ y₁ y₂ : Y, y₁ ≠ y₂

/-- A domain `X` is infinite if no finite list enumerates all of its elements. -/
def InfiniteDomain (X : Type u) : Prop :=
  ∀ L : List X, ∃ x : X, x ∉ L

/-- A finite labeled sample `S` leaves an untested input if some `x : X` does
not occur among the input coordinates of `S`. -/
def HasUntestedInput {X : Type u} {Y : Type v} (S : List (X × Y)) : Prop :=
  ∃ x : X, x ∉ S.map Prod.fst

/-- Lookup-table perturbation of `h` at a single input `x₀`: returns `y'` on
`x₀` and agrees with `h` everywhere else. -/
noncomputable def patchAt {X : Type u} {Y : Type v}
    (h : X → Y) (x₀ : X) (y' : Y) : X → Y :=
  open Classical in
  fun x => if x = x₀ then y' else h x

theorem patchAt_self {X : Type u} {Y : Type v}
    (h : X → Y) (x₀ : X) (y' : Y) :
    patchAt h x₀ y' x₀ = y' := by
  classical
  simp [patchAt]

theorem patchAt_of_ne {X : Type u} {Y : Type v}
    (h : X → Y) (x₀ x : X) (y' : Y) (hne : x ≠ x₀) :
    patchAt h x₀ y' x = h x := by
  classical
  simp [patchAt, hne]

/-- A hypothesis class `H` is closed under single-point patches if modifying
any member `h ∈ H` at a single input `x₀` to any output `y'` remains in `H`.
Strictly weaker than `IsUnrestricted` (for example, `EventuallyFalse` and the
class of computable functions on a decidable domain satisfy it without being
unrestricted), and captures the exact closure property driving the
untested-input impossibility. -/
def ClosedUnderPointPatches {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) : Prop :=
  ∀ (h : X → Y) (x₀ : X) (y' : Y), H h → H (patchAt h x₀ y')

/-- Every unrestricted class is closed under single-point patches. -/
theorem isUnrestricted_implies_closedUnderPointPatches {X : Type u} {Y : Type v}
    {H : HypothesisClass X Y} (hUnres : IsUnrestricted H) :
    ClosedUnderPointPatches H :=
  fun h x₀ y' _ => hUnres (patchAt h x₀ y')

/-- The restricted class of eventually-`false` functions `Nat → Bool` (functions
that output `false` on all sufficiently large inputs). Demonstrates that a
strictly restricted class can still be closed under single-point patches and
therefore admit no finite teaching set. -/
def EventuallyFalse : HypothesisClass Nat Bool :=
  fun f => ∃ N : Nat, ∀ x : Nat, N ≤ x → f x = false

theorem eventuallyFalse_not_unrestricted : ¬ IsUnrestricted EventuallyFalse := by
  intro hU
  rcases hU (fun _ => true) with ⟨N, hN⟩
  have := hN N (Nat.le_refl N)
  cases this

theorem eventuallyFalse_closedUnderPointPatches :
    ClosedUnderPointPatches EventuallyFalse := by
  intro h x₀ y' ⟨N, hN⟩
  refine ⟨max N (x₀ + 1), ?_⟩
  intro x hx
  have hne : x ≠ x₀ := by
    have : x₀ + 1 ≤ max N (x₀ + 1) := Nat.le_max_right N (x₀ + 1)
    omega
  rw [patchAt_of_ne h x₀ x y' hne]
  exact hN x (Nat.le_trans (Nat.le_max_left N (x₀ + 1)) hx)

/-! ### Definition Positive and Negative Examples -/

theorem isUnrestricted_pos_example :
    IsUnrestricted (fun (_ : Bool → Bool) => True) :=
  fun _ => trivial

theorem isUnrestricted_neg_example :
    ¬ IsUnrestricted ConstBoolClass := by
  intro hUnres
  rcases hUnres id with heq | heq
  · have := congrFun heq true; cases this
  · have := congrFun heq false; cases this

theorem closedUnderPointPatches_pos_example :
    ClosedUnderPointPatches EventuallyFalse ∧ ¬ IsUnrestricted EventuallyFalse :=
  ⟨eventuallyFalse_closedUnderPointPatches, eventuallyFalse_not_unrestricted⟩

theorem closedUnderPointPatches_neg_example :
    ¬ ClosedUnderPointPatches ConstBoolClass := by
  intro hClosed
  have hPatch := hClosed (fun _ => true) true false (Or.inr rfl)
  rcases hPatch with heq | heq
  · have h0 := congrFun heq false
    rw [patchAt_of_ne (fun _ => true) true false false (by decide)] at h0
    cases h0
  · have h1 := congrFun heq true
    rw [patchAt_self] at h1
    cases h1

theorem hasTwoDistinct_pos_example : HasTwoDistinct Bool :=
  ⟨false, true, by decide⟩

theorem hasTwoDistinct_neg_example : ¬ HasTwoDistinct Unit := by
  intro ⟨a, b, hne⟩
  cases a; cases b
  exact hne rfl

private theorem nat_list_upper_bound (L : List Nat) :
    ∀ n ∈ L, n ≤ L.foldr max 0 := by
  induction L with
  | nil =>
    intro n hn
    cases hn
  | cons a as ih =>
    intro n hn
    simp only [List.mem_cons] at hn
    simp only [List.foldr]
    rcases hn with rfl | hmem
    · exact Nat.le_max_left n (as.foldr max 0)
    · exact Nat.le_trans (ih n hmem) (Nat.le_max_right a (as.foldr max 0))

theorem infiniteDomain_pos_example : InfiniteDomain Nat := by
  intro L
  refine ⟨L.foldr max 0 + 1, ?_⟩
  intro hmem
  have hle := nat_list_upper_bound L (L.foldr max 0 + 1) hmem
  omega

theorem infiniteDomain_neg_example : ¬ InfiniteDomain Bool := by
  intro hInf
  rcases hInf [false, true] with ⟨b, hb⟩
  cases b
  · exact hb (by simp)
  · exact hb (by simp)

theorem hasUntestedInput_pos_example :
    HasUntestedInput ([(false, false)] : List (Bool × Bool)) :=
  ⟨true, by simp⟩

theorem hasUntestedInput_neg_example :
    ¬ HasUntestedInput ([(false, false), (true, true)] : List (Bool × Bool)) := by
  intro ⟨b, hb⟩
  cases b <;> exact hb (by simp)

/-! ### Result 2: Explicit Untested-Input Lookup-Table Witness (Patch-Closed) -/

/-- If `H` is closed under single-point patches, `h ∈ H`, `S` is consistent
with `h`, `x₀` does not appear among the inputs of `S`, and `y' ≠ h x₀`, then
the point-patched function `patchAt h x₀ y'` belongs to `H`, passes `S`, and
differs from `h`; hence `S` does not teach `h` within `H`. -/
theorem patchClosed_untested_input_patch_witness
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (x₀ : X) (y' : Y)
    (hClosed : ClosedUnderPointPatches H)
    (hh : H h)
    (hcon : Consistent S h)
    (hUntested : x₀ ∉ S.map Prod.fst)
    (hDiff : y' ≠ h x₀) :
    H (patchAt h x₀ y') ∧
    Consistent S (patchAt h x₀ y') ∧
    patchAt h x₀ y' ≠ h ∧
    ¬ Teaches H h S := by
  have hH : H (patchAt h x₀ y') := hClosed h x₀ y' hh
  have hconPatch : Consistent S (patchAt h x₀ y') := by
    intro p hp
    have hne : p.1 ≠ x₀ := fun heq => hUntested (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [patchAt_of_ne h x₀ p.1 y' hne]
    exact hcon p hp
  have hnePatch : patchAt h x₀ y' ≠ h := by
    intro heq
    have hval := congrFun heq x₀
    rw [patchAt_self] at hval
    exact hDiff hval
  have hnotT : ¬ Teaches H h S := fun hT => hnePatch (hT.2.2 _ hH hconPatch)
  exact ⟨hH, hconPatch, hnePatch, hnotT⟩

/-- Unrestricted-class specialization of
`patchClosed_untested_input_patch_witness`. -/
theorem unrestricted_untested_input_patch_witness
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (x₀ : X) (y' : Y)
    (hUnres : IsUnrestricted H)
    (hcon : Consistent S h)
    (hUntested : x₀ ∉ S.map Prod.fst)
    (hDiff : y' ≠ h x₀) :
    H (patchAt h x₀ y') ∧
    Consistent S (patchAt h x₀ y') ∧
    patchAt h x₀ y' ≠ h ∧
    ¬ Teaches H h S :=
  patchClosed_untested_input_patch_witness H h S x₀ y'
    (isUnrestricted_implies_closedUnderPointPatches hUnres) (hUnres h) hcon hUntested hDiff

/-- Non-vacuity witness for `patchClosed_untested_input_patch_witness`, using
the strictly restricted patch-closed class `EventuallyFalse`. -/
theorem patchClosed_untested_input_patch_witness_nonvacuity :
    ClosedUnderPointPatches EventuallyFalse ∧
    EventuallyFalse (fun _ => false) ∧
    Consistent [(0, false)] (fun (_ : Nat) => false) ∧
    (1 : Nat) ∉ ([(0, false)] : List (Nat × Bool)).map Prod.fst ∧
    (true : Bool) ≠ (fun (_ : Nat) => false) 1 := by
  refine ⟨eventuallyFalse_closedUnderPointPatches, ⟨0, fun _ _ => rfl⟩, ?_, by simp, by decide⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl; rfl

/-- Tightness counterexample for `hClosed : ClosedUnderPointPatches H` in
`patchClosed_untested_input_patch_witness`: under `ConstBoolClass`, even when
`true` is untested, `[(false, true)]` teaches `fun _ => true` and `patchAt`
lies outside the class. -/
theorem patchClosed_untested_input_ce_not_patchClosed :
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    ¬ ClosedUnderPointPatches ConstBoolClass ∧
    ConstBoolClass h ∧
    Consistent S h ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    (false : Bool) ≠ h true ∧
    ¬ (ConstBoolClass (patchAt h true false) ∧
       Consistent S (patchAt h true false) ∧
       patchAt h true false ≠ h ∧
       ¬ Teaches ConstBoolClass h S) := by
  refine ⟨closedUnderPointPatches_neg_example, Or.inr rfl, teaches_pos_example.2.1,
    by simp, by decide, ?_⟩
  intro ⟨_, _, _, hnotT⟩
  exact hnotT teaches_pos_example

/-- Tightness counterexample for `hh : H h` in
`patchClosed_untested_input_patch_witness`: `EventuallyFalse` is closed under
single-point patches, yet patching `h = fun _ => true ∉ EventuallyFalse` at a
single point still lies outside `EventuallyFalse`. -/
theorem patchClosed_untested_input_ce_not_in_H :
    let h : Nat → Bool := fun _ => true
    let S : List (Nat × Bool) := [(0, true)]
    ClosedUnderPointPatches EventuallyFalse ∧
    ¬ EventuallyFalse h ∧
    Consistent S h ∧
    (1 : Nat) ∉ S.map Prod.fst ∧
    (false : Bool) ≠ h 1 ∧
    ¬ (EventuallyFalse (patchAt h 1 false) ∧
       Consistent S (patchAt h 1 false) ∧
       patchAt h 1 false ≠ h ∧
       ¬ Teaches EventuallyFalse h S) := by
  refine ⟨eventuallyFalse_closedUnderPointPatches, ?_, ?_, by simp, by decide, ?_⟩
  · intro ⟨N, hN⟩
    have := hN N (Nat.le_refl N)
    cases this
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  · intro ⟨⟨N, hN⟩, _, _, _⟩
    have hge : N ≤ max N 2 := Nat.le_max_left N 2
    have hne : max N 2 ≠ 1 := by
      have : 2 ≤ max N 2 := Nat.le_max_right N 2
      omega
    have hval := hN (max N 2) hge
    rw [patchAt_of_ne (fun _ => true) 1 (max N 2) false hne] at hval
    cases hval

/-- Tightness counterexample for `hcon : Consistent S h` in
`patchClosed_untested_input_patch_witness`: if `S` is inconsistent with `h`,
then `patchAt h x₀ y'` also fails to be consistent with `S`. -/
theorem patchClosed_untested_input_ce_inconsistent :
    let H : HypothesisClass Bool Bool := fun _ => True
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, false)]
    ClosedUnderPointPatches H ∧
    H h ∧
    ¬ Consistent S h ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    (false : Bool) ≠ h true ∧
    ¬ (H (patchAt h true false) ∧
       Consistent S (patchAt h true false) ∧
       patchAt h true false ≠ h ∧
       ¬ Teaches H h S) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial), trivial,
    ?_, by simp, by decide, ?_⟩
  · intro hcon
    have := hcon (false, false) (by simp)
    cases this
  · intro ⟨_, hconPatch, _, _⟩
    have hval := hconPatch (false, false) (by simp)
    rw [patchAt_of_ne (fun _ => true) true false false (by decide)] at hval
    cases hval

/-- Tightness counterexample for `hUntested : x₀ ∉ S.map Prod.fst` in
`patchClosed_untested_input_patch_witness`: when `x₀` is already tested by `S`,
patching at `x₀` breaks consistency with `S`. -/
theorem patchClosed_untested_input_ce_tested :
    let H : HypothesisClass Bool Bool := fun _ => True
    let h : Bool → Bool := id
    let S : List (Bool × Bool) := [(false, false), (true, true)]
    ClosedUnderPointPatches H ∧
    H h ∧
    Consistent S h ∧
    ¬ ((false : Bool) ∉ S.map Prod.fst) ∧
    (true : Bool) ≠ h false ∧
    ¬ (H (patchAt h false true) ∧
       Consistent S (patchAt h false true) ∧
       patchAt h false true ≠ h ∧
       ¬ Teaches H h S) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial), trivial,
    ?_, by simp, by decide, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro ⟨_, hconPatch, _, _⟩
    have hval := hconPatch (false, false) (by simp)
    rw [patchAt_self] at hval
    cases hval

/-- Tightness counterexample for `hDiff : y' ≠ h x₀` in
`patchClosed_untested_input_patch_witness`: patching with the same value `h x₀`
yields `patchAt h x₀ (h x₀) = h`, which is not distinct from `h`. -/
theorem patchClosed_untested_input_ce_same_val :
    let H : HypothesisClass Bool Bool := fun _ => True
    let h : Bool → Bool := fun _ => false
    let S : List (Bool × Bool) := [(false, false)]
    ClosedUnderPointPatches H ∧
    H h ∧
    Consistent S h ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    ¬ ((false : Bool) ≠ h true) ∧
    ¬ (H (patchAt h true false) ∧
       Consistent S (patchAt h true false) ∧
       patchAt h true false ≠ h ∧
       ¬ Teaches H h S) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial), trivial,
    ?_, by simp, fun h => h rfl, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  · intro ⟨_, _, hne, _⟩
    apply hne
    funext x
    classical
    by_cases hx : x = true
    · subst hx; simp [patchAt]
    · simp [patchAt, hx]

/-! ### Result 3: Untested-Input Impossibility (Corollary of Result 2) -/

/-- Whenever `H` is closed under single-point patches over `X → Y`, `Y` has at
least two distinct values, and finite sample `S` leaves at least one input in
`X` untested (e.g., `|X| > S.length`), `S` does not teach any `h` within `H`. -/
theorem patchClosed_hasUntestedInput_no_teaching
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hClosed : ClosedUnderPointPatches H)
    (hTwo : HasTwoDistinct Y)
    (hUntested : HasUntestedInput S) :
    ¬ Teaches H h S := by
  intro hT
  rcases hUntested with ⟨x₀, hx₀⟩
  rcases hTwo with ⟨y₁, y₂, hyne⟩
  have ⟨y', hy'⟩ : ∃ y' : Y, y' ≠ h x₀ := by
    by_cases heq : h x₀ = y₁
    · exact ⟨y₂, fun h2 => hyne (heq.symm.trans h2.symm)⟩
    · exact ⟨y₁, fun h1 => heq h1.symm⟩
  exact (patchClosed_untested_input_patch_witness H h S x₀ y'
    hClosed hT.1 hT.2.1 hx₀ hy').2.2.2 hT

/-- Unrestricted-class specialization of
`patchClosed_hasUntestedInput_no_teaching`. -/
theorem unrestricted_hasUntestedInput_no_teaching
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hUnres : IsUnrestricted H)
    (hTwo : HasTwoDistinct Y)
    (hUntested : HasUntestedInput S) :
    ¬ Teaches H h S :=
  patchClosed_hasUntestedInput_no_teaching H h S
    (isUnrestricted_implies_closedUnderPointPatches hUnres) hTwo hUntested

/-- Non-vacuity witness for `patchClosed_hasUntestedInput_no_teaching`. -/
theorem patchClosed_hasUntestedInput_no_teaching_nonvacuity :
    ClosedUnderPointPatches (fun (_ : Bool → Bool) => True) ∧
    HasTwoDistinct Bool ∧
    HasUntestedInput ([(false, false)] : List (Bool × Bool)) :=
  ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial),
   hasTwoDistinct_pos_example, hasUntestedInput_pos_example⟩

/-- Tightness counterexample for `hClosed : ClosedUnderPointPatches H` in
`patchClosed_hasUntestedInput_no_teaching`. -/
theorem patchClosed_hasUntestedInput_ce_not_patchClosed :
    ¬ ClosedUnderPointPatches ConstBoolClass ∧
    HasTwoDistinct Bool ∧
    HasUntestedInput ([(false, true)] : List (Bool × Bool)) ∧
    ¬ (¬ Teaches ConstBoolClass (fun _ => true) [(false, true)]) :=
  ⟨closedUnderPointPatches_neg_example, hasTwoDistinct_pos_example,
   ⟨true, by simp⟩, fun h => h teaches_pos_example⟩

/-- Tightness counterexample for `hTwo : HasTwoDistinct Y` in
`patchClosed_hasUntestedInput_no_teaching`. -/
theorem patchClosed_hasUntestedInput_ce_trivial_codomain :
    ClosedUnderPointPatches (fun (_ : Bool → Unit) => True) ∧
    ¬ HasTwoDistinct Unit ∧
    HasUntestedInput ([(false, ())] : List (Bool × Unit)) ∧
    ¬ (¬ Teaches (fun (_ : Bool → Unit) => True) (fun _ => ()) [(false, ())]) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial),
    hasTwoDistinct_neg_example, ⟨true, by simp⟩, ?_⟩
  intro hnot
  apply hnot
  refine ⟨trivial, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  · intro g _ _
    funext b; cases g b; rfl

/-- Tightness counterexample for `hUntested : HasUntestedInput S` in
`patchClosed_hasUntestedInput_no_teaching`. -/
theorem patchClosed_hasUntestedInput_ce_exhaustive :
    ClosedUnderPointPatches (fun (_ : Bool → Bool) => True) ∧
    HasTwoDistinct Bool ∧
    ¬ HasUntestedInput ([(false, false), (true, true)] : List (Bool × Bool)) ∧
    ¬ (¬ Teaches (fun (_ : Bool → Bool) => True) id [(false, false), (true, true)]) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial),
    hasTwoDistinct_pos_example, hasUntestedInput_neg_example, ?_⟩
  intro hnot
  apply hnot
  refine ⟨trivial, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro g _ hcon
    funext b
    cases b
    · exact hcon (false, false) (by simp)
    · exact hcon (true, true) (by simp)

/-! ### Result 4: Infinite-Domain Impossibility (Corollary of Result 3) -/

/-- Over an infinite domain `X` and nontrivial codomain `Y`, no finite labeled
sample teaches any function within a hypothesis class `H` closed under
single-point patches. -/
theorem patchClosed_infinite_no_finite_teaching_set
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y)
    (hClosed : ClosedUnderPointPatches H)
    (hTwo : HasTwoDistinct Y)
    (hInf : InfiniteDomain X) :
    ∀ (h : X → Y) (S : List (X × Y)), ¬ Teaches H h S :=
  fun h S =>
    patchClosed_hasUntestedInput_no_teaching H h S hClosed hTwo (hInf (S.map Prod.fst))

/-- Unrestricted-class specialization of
`patchClosed_infinite_no_finite_teaching_set`. -/
theorem unrestricted_infinite_no_finite_teaching_set
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y)
    (hUnres : IsUnrestricted H)
    (hTwo : HasTwoDistinct Y)
    (hInf : InfiniteDomain X) :
    ∀ (h : X → Y) (S : List (X × Y)), ¬ Teaches H h S :=
  patchClosed_infinite_no_finite_teaching_set H
    (isUnrestricted_implies_closedUnderPointPatches hUnres) hTwo hInf

/-- Concrete restricted-class corollary: `EventuallyFalse` is strictly smaller
than the unrestricted class (`¬ IsUnrestricted EventuallyFalse`) yet still
admits no finite teaching set for any target. -/
theorem eventuallyFalse_no_finite_teaching_set :
    ∀ (h : Nat → Bool) (S : List (Nat × Bool)), ¬ Teaches EventuallyFalse h S :=
  patchClosed_infinite_no_finite_teaching_set EventuallyFalse
    eventuallyFalse_closedUnderPointPatches hasTwoDistinct_pos_example infiniteDomain_pos_example

/-- Non-vacuity witness for `patchClosed_infinite_no_finite_teaching_set`,
using the strictly restricted class `EventuallyFalse`. -/
theorem patchClosed_infinite_no_finite_teaching_set_nonvacuity :
    ClosedUnderPointPatches EventuallyFalse ∧
    HasTwoDistinct Bool ∧
    InfiniteDomain Nat :=
  ⟨eventuallyFalse_closedUnderPointPatches, hasTwoDistinct_pos_example, infiniteDomain_pos_example⟩

/-- Tightness counterexample for `hClosed : ClosedUnderPointPatches H` in
`patchClosed_infinite_no_finite_teaching_set`: restricting `H` on the infinite
domain `Nat` to constant Boolean functions breaks patch-closure and makes
`[(0, true)]` a finite teaching set. -/
theorem patchClosed_infinite_ce_not_patchClosed :
    let H : HypothesisClass Nat Bool :=
      fun f => f = (fun _ => false) ∨ f = (fun _ => true)
    ¬ ClosedUnderPointPatches H ∧
    HasTwoDistinct Bool ∧
    InfiniteDomain Nat ∧
    ¬ (∀ (h : Nat → Bool) (S : List (Nat × Bool)), ¬ Teaches H h S) := by
  refine ⟨?_, hasTwoDistinct_pos_example, infiniteDomain_pos_example, ?_⟩
  · intro hClosed
    rcases hClosed (fun _ => false) 0 true (Or.inl rfl) with heq | heq
    · have h0 := congrFun heq 0
      rw [patchAt_self] at h0
      cases h0
    · have h1 := congrFun heq 1
      rw [patchAt_of_ne (fun _ => false) 0 1 true (by decide)] at h1
      cases h1
  · intro hall
    apply hall (fun _ => true) [(0, true)]
    refine ⟨Or.inr rfl, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl; rfl
    · intro g hg hcon
      rcases hg with rfl | rfl
      · have := hcon (0, true) (by simp); cases this
      · rfl

/-- Tightness counterexample for `hTwo : HasTwoDistinct Y` in
`patchClosed_infinite_no_finite_teaching_set`: over a subsingleton codomain
`Unit`, the empty sample teaches the unique function `Nat → Unit`. -/
theorem patchClosed_infinite_ce_trivial_codomain :
    let H : HypothesisClass Nat Unit := fun _ => True
    ClosedUnderPointPatches H ∧
    ¬ HasTwoDistinct Unit ∧
    InfiniteDomain Nat ∧
    ¬ (∀ (h : Nat → Unit) (S : List (Nat × Unit)), ¬ Teaches H h S) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial),
    hasTwoDistinct_neg_example, infiniteDomain_pos_example, ?_⟩
  intro hall
  apply hall (fun _ => ()) []
  refine ⟨trivial, (fun _ hp => by cases hp), ?_⟩
  intro g _ _
  funext n
  cases g n
  rfl

/-- Tightness counterexample for `hInf : InfiniteDomain X` in
`patchClosed_infinite_no_finite_teaching_set`: over the finite domain `Bool`,
an exhaustive finite sample teaches `id` even in the unrestricted (hence
patch-closed) class. -/
theorem patchClosed_infinite_ce_finite_domain :
    let H : HypothesisClass Bool Bool := fun _ => True
    ClosedUnderPointPatches H ∧
    HasTwoDistinct Bool ∧
    ¬ InfiniteDomain Bool ∧
    ¬ (∀ (h : Bool → Bool) (S : List (Bool × Bool)), ¬ Teaches H h S) := by
  refine ⟨isUnrestricted_implies_closedUnderPointPatches (fun _ => trivial),
    hasTwoDistinct_pos_example, infiniteDomain_neg_example, ?_⟩
  intro hall
  apply hall id [(false, false), (true, true)]
  refine ⟨trivial, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro g _ hcon
    funext b
    cases b
    · exact hcon (false, false) (by simp)
    · exact hcon (true, true) (by simp)

end Toy.Witness
