/-
Monotone Boolean conjunctions over `m` features, the canonical minimum-size
teaching set construction, exact per-concept minimum teaching-set size
`min (r + 1) m` (including edge cases `r = 0`, `r = m`, and `m = 0`), and
teaching dimension `m`.
-/
import Toy.Witness.Core

namespace Toy.Witness

/-- A Boolean feature assignment over `m` features. -/
abbrev BoolAssignment (m : Nat) : Type := Fin m → Bool

/-- Evaluate the monotone conjunction determined by the indicator vector
`V : Fin m → Bool` on feature assignment `x : BoolAssignment m`: returns `true`
iff every feature `i` selected by `V` (`V i = true`) is set to `true` in `x`.
The empty conjunction (`∀ i, V i = false`) evaluates to constant `true`. -/
def evalMonotoneConj {m : Nat} (V : Fin m → Bool) (x : BoolAssignment m) : Bool :=
  (List.finRange m).all (fun i => !V i || x i)

theorem evalMonotoneConj_eq_true_iff {m : Nat}
    (V : Fin m → Bool) (x : BoolAssignment m) :
    evalMonotoneConj V x = true ↔ ∀ i : Fin m, V i = true → x i = true := by
  simp only [evalMonotoneConj, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro hall i hVi
    have hi := hall i
    rw [hVi] at hi
    simpa using hi
  · intro hall i
    cases hVi : V i
    · simp
    · simp [hall i hVi]

theorem evalMonotoneConj_all_true {m : Nat} (V : Fin m → Bool) :
    evalMonotoneConj V (fun _ => true) = true := by
  rw [evalMonotoneConj_eq_true_iff]
  intro _ _
  rfl

/-- Number of relevant variables (features with `V i = true`) in the monotone
conjunction represented by `V : Fin m → Bool`. -/
def relevantCount {m : Nat} (V : Fin m → Bool) : Nat :=
  ((List.finRange m).filter (fun i => V i)).length

theorem relevantCount_le {m : Nat} (V : Fin m → Bool) :
    relevantCount V ≤ m := by
  unfold relevantCount
  calc
    ((List.finRange m).filter (fun i => V i)).length
        ≤ (List.finRange m).length := List.length_filter_le _ _
    _ = m := List.length_finRange

/-- The hypothesis class of monotone conjunctions over `m` Boolean features:
functions `Fin m → Bool → Bool` of the form `⋀_{i ∈ V} x_i` with positive
literals only (note: constant `false` is excluded because every monotone
conjunction evaluates to `true` on the all-`true` assignment, and monotone
disjunctions such as `x 0 || x 1` are also excluded). -/
def MonotoneConjunctions (m : Nat) : HypothesisClass (BoolAssignment m) Bool :=
  fun f => ∃ V : Fin m → Bool, evalMonotoneConj V = f

/-- Feature assignment equal to `false` at coordinate `i` and `true` at all
other coordinates. -/
def flipBit {m : Nat} (i : Fin m) : BoolAssignment m :=
  fun k => decide (k ≠ i)

/-- The negative labeled examples in the canonical teaching set of `V`: one
`(flipBit i, false)` pair for each relevant feature `i` (`V i = true`). -/
def monotoneConjNegExamples {m : Nat} (V : Fin m → Bool) :
    List (BoolAssignment m × Bool) :=
  ((List.finRange m).filter (fun i => V i)).map (fun i => (flipBit i, false))

/-- Canonical minimum-size labeled teaching set for the monotone conjunction
`V : Fin m → Bool` over `m` features:
- when `relevantCount V < m`, the single positive witness `(V, true)` (ruling
  out every conjunction that adds an irrelevant variable) followed by one
  negative witness `(flipBit i, false)` per relevant variable `i` (ruling out
  every conjunction that drops `i`);
- when `relevantCount V = m`, only the `m` negative witnesses
  `(flipBit i, false)` (no superset conjunction exists, so no positive witness
  is needed). -/
def monotoneConjTeachingSet {m : Nat} (V : Fin m → Bool) :
    List (BoolAssignment m × Bool) :=
  if relevantCount V < m then
    (V, true) :: monotoneConjNegExamples V
  else
    monotoneConjNegExamples V

theorem monotoneConjNegExamples_length {m : Nat} (V : Fin m → Bool) :
    (monotoneConjNegExamples V).length = relevantCount V := by
  simp [monotoneConjNegExamples, relevantCount]

theorem monotoneConjTeachingSet_length {m : Nat} (V : Fin m → Bool) :
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) m := by
  have hle : relevantCount V ≤ m := relevantCount_le V
  unfold monotoneConjTeachingSet
  split
  · rename_i hlt
    simp only [List.length_cons, monotoneConjNegExamples_length]
    omega
  · rename_i hnotlt
    simp only [monotoneConjNegExamples_length]
    omega

private theorem flipBit_injective {m : Nat} {i j : Fin m}
    (h : flipBit i = flipBit j) : i = j := by
  have hi := congrFun h i
  simp [flipBit] at hi
  exact hi

theorem monotoneConjTeachingSet_nodup {m : Nat} (V : Fin m → Bool) :
    (monotoneConjTeachingSet V).Nodup := by
  have hndFin : (List.finRange m).Nodup := List.nodup_finRange m
  have hndFilt : ((List.finRange m).filter (fun i => V i)).Nodup :=
    hndFin.filter _
  have hndNeg : (monotoneConjNegExamples V).Nodup := by
    unfold monotoneConjNegExamples List.Nodup
    exact List.pairwise_map.mpr
      (hndFilt.imp (fun hne heq => hne (flipBit_injective (Prod.mk.inj heq).1)))
  unfold monotoneConjTeachingSet
  split
  · refine List.nodup_cons.mpr ⟨?_, hndNeg⟩
    intro hmem
    simp only [monotoneConjNegExamples, List.mem_map] at hmem
    rcases hmem with ⟨_, _, heq⟩
    have hbool := (Prod.mk.inj heq).2
    cases hbool
  · exact hndNeg

private theorem finRange_two : List.finRange 2 = [0, 1] := rfl

theorem monotoneConjTeachingSet_m2_all :
    monotoneConjTeachingSet (fun _ : Fin 2 => true) =
      [(flipBit (0 : Fin 2), false), (flipBit (1 : Fin 2), false)] := by
  simp [monotoneConjTeachingSet, relevantCount, monotoneConjNegExamples, finRange_two]

/-! ### Definition Positive and Negative Examples -/

theorem monotoneConjunctions_pos_example :
    MonotoneConjunctions 2 (fun x => x 0 && x 1) := by
  refine ⟨fun _ => true, ?_⟩
  funext x
  simp [evalMonotoneConj, finRange_two]

/-- Non-trivial negative example: the disjunction `x 0 || x 1` is monotone and
maps the all-`true` assignment to `true`, yet is not a monotone conjunction. -/
theorem monotoneConjunctions_neg_example_or :
    ¬ MonotoneConjunctions 2 (fun x => x 0 || x 1) := by
  rintro ⟨V, hV⟩
  have hff := congrFun hV (fun _ => false)
  have h0 := congrFun hV (flipBit (0 : Fin 2))
  have h1 := congrFun hV (flipBit (1 : Fin 2))
  cases hv0 : V 0 <;> cases hv1 : V 1 <;>
    simp [evalMonotoneConj, finRange_two, flipBit, hv0, hv1] at hff h0 h1

/-- Constant `false` is excluded from `MonotoneConjunctions 2` because every
monotone conjunction evaluates to `true` on the all-`true` assignment. -/
theorem monotoneConjunctions_neg_example_const_false :
    ¬ MonotoneConjunctions 2 (fun _ => false) := by
  intro ⟨V, hV⟩
  have h1 := congrFun hV (fun _ => true)
  rw [evalMonotoneConj_all_true] at h1
  cases h1

/-! ### Concrete Edge-Case Checks (`m = 0` and `m = 2`: `r = 0, 1, 2`) -/

private theorem fin2_fun_ext {f g : Fin 2 → Bool}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

private theorem two_le_length_of_two_mem {α β : Type} (S : List (α × β)) (a b : α)
    (ha : a ∈ S.map Prod.fst) (hb : b ∈ S.map Prod.fst) (hab : a ≠ b) :
    2 ≤ S.length := by
  match S, ha, hb with
  | [], ha, _ => simp at ha
  | [_], ha, hb =>
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

/-- Concrete check for `m = 2, r = 2` (`x₀ ∧ x₁`): `monotoneConjTeachingSet`
has length `2 = min (2 + 1) 2` and teaches `x₀ ∧ x₁` within
`MonotoneConjunctions 2`. -/
theorem monotone_conj_m2_all_teaches :
    let V : Fin 2 → Bool := fun _ => true
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = 2 := by
  have hset : monotoneConjTeachingSet (fun _ : Fin 2 => true) =
      [(flipBit (0 : Fin 2), false), (flipBit (1 : Fin 2), false)] := by
    simp [monotoneConjTeachingSet, relevantCount, monotoneConjNegExamples, finRange_two]
  refine ⟨⟨⟨fun _ => true, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro p hp
    rw [hset] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  · intro g hg hcon
    rcases hg with ⟨W, rfl⟩
    have h0 : evalMonotoneConj W (flipBit (0 : Fin 2)) = false :=
      hcon (flipBit (0 : Fin 2), false) (by rw [hset]; simp)
    have h1 : evalMonotoneConj W (flipBit (1 : Fin 2)) = false :=
      hcon (flipBit (1 : Fin 2), false) (by rw [hset]; simp)
    have hW0 : W 0 = true := by
      cases hw : W 0 with
      | true => rfl
      | false =>
        have htrue : evalMonotoneConj W (flipBit (0 : Fin 2)) = true := by
          rw [evalMonotoneConj_eq_true_iff]
          intro i hi
          match i with
          | ⟨0, _⟩ => change W 0 = true at hi; rw [hw] at hi; cases hi
          | ⟨1, _⟩ => simp [flipBit]
        rw [htrue] at h0; cases h0
    have hW1 : W 1 = true := by
      cases hw : W 1 with
      | true => rfl
      | false =>
        have htrue : evalMonotoneConj W (flipBit (1 : Fin 2)) = true := by
          rw [evalMonotoneConj_eq_true_iff]
          intro i hi
          match i with
          | ⟨0, _⟩ => simp [flipBit]
          | ⟨1, _⟩ => change W 1 = true at hi; rw [hw] at hi; cases hi
        rw [htrue] at h1; cases h1
    have hWeq : W = fun _ => true := fin2_fun_ext hW0 hW1
    rw [hWeq]
  · rw [hset]; rfl

/-- Concrete check for `m = 2, r = 1` (`x₀`): `monotoneConjTeachingSet` has
length `2 = min (1 + 1) 2` and teaches `x₀` within `MonotoneConjunctions 2`. -/
theorem monotone_conj_m2_single_teaches :
    let V : Fin 2 → Bool := fun i => decide (i.val = 0)
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = 2 := by
  let V : Fin 2 → Bool := fun i => decide (i.val = 0)
  have hset : monotoneConjTeachingSet V = [(V, true), (flipBit (0 : Fin 2), false)] := by
    simp [monotoneConjTeachingSet, relevantCount, monotoneConjNegExamples, finRange_two, V]
  refine ⟨⟨⟨V, rfl⟩, ?_, ?_⟩, by rw [hset]; rfl⟩
  · intro p hp
    rw [hset] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  · intro g hg hcon
    rcases hg with ⟨W, rfl⟩
    have hpos : evalMonotoneConj W V = true :=
      hcon (V, true) (by rw [hset]; simp)
    have hneg : evalMonotoneConj W (flipBit (0 : Fin 2)) = false :=
      hcon (flipBit (0 : Fin 2), false) (by rw [hset]; simp)
    have hW1 : W 1 = false := by
      cases hw : W 1 with
      | false => rfl
      | true =>
        have hv1 := (evalMonotoneConj_eq_true_iff W V).mp hpos 1 hw
        cases hv1
    have hW0 : W 0 = true := by
      cases hw : W 0 with
      | true => rfl
      | false =>
        have htrue : evalMonotoneConj W (flipBit (0 : Fin 2)) = true := by
          rw [evalMonotoneConj_eq_true_iff]
          intro i hi
          match i with
          | ⟨0, _⟩ => change W 0 = true at hi; rw [hw] at hi; cases hi
          | ⟨1, _⟩ => change W 1 = true at hi; rw [hW1] at hi; cases hi
        rw [htrue] at hneg; cases hneg
    have hWeq : W = V := fin2_fun_ext hW0 hW1
    rw [hWeq]

/-- Concrete check for `m = 2, r = 0` (`⊤`): `monotoneConjTeachingSet` has
length `1 = min (0 + 1) 2` and teaches `⊤` within `MonotoneConjunctions 2`. -/
theorem monotone_conj_m2_empty_teaches :
    let V : Fin 2 → Bool := fun _ => false
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = 1 := by
  let V : Fin 2 → Bool := fun _ => false
  have hset : monotoneConjTeachingSet V = [(V, true)] := by
    simp [monotoneConjTeachingSet, relevantCount, monotoneConjNegExamples, finRange_two, V]
  refine ⟨⟨⟨V, rfl⟩, ?_, ?_⟩, by rw [hset]; rfl⟩
  · intro p hp
    rw [hset] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    decide
  · intro g hg hcon
    rcases hg with ⟨W, rfl⟩
    have hpos : evalMonotoneConj W V = true :=
      hcon (V, true) (by rw [hset]; simp)
    have hWeq : W = V := by
      funext i
      cases hw : W i with
      | false => rfl
      | true =>
        have hv := (evalMonotoneConj_eq_true_iff W V).mp hpos i hw
        cases hv
    rw [hWeq]

/-- Full concrete check of `monotone_conj_teaching_set_exact` (including the
`HasMinTeachingSize` lower bound) at `m = 2, r = 1`. -/
theorem monotone_conj_m2_r1_exact :
    let V : Fin 2 → Bool := fun i => decide (i.val = 0)
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) 2 ∧
    HasMinTeachingSize (MonotoneConjunctions 2) (evalMonotoneConj V)
      (min (relevantCount V + 1) 2) := by
  dsimp only
  let V : Fin 2 → Bool := fun i => decide (i.val = 0)
  have hmin : min (relevantCount V + 1) 2 = 2 := by decide
  rw [show min (relevantCount (fun i : Fin 2 => decide (i.val = 0)) + 1) 2 = 2 from hmin]
  refine ⟨monotone_conj_m2_single_teaches.1, monotone_conj_m2_single_teaches.2,
    ⟨⟨_, monotone_conj_m2_single_teaches.2, monotone_conj_m2_single_teaches.1⟩, ?_⟩⟩
  intro S hT
  have hhit := (teaches_iff_hits_disagreement_sets_of_mem_of_consistent
    _ _ S hT.1 hT.2.1).mp hT
  have hne₁ : evalMonotoneConj (fun _ : Fin 2 => false) ≠ evalMonotoneConj V := by
    intro heq; have := congrFun heq (fun _ => false); exact absurd this (by decide)
  have hne₂ : evalMonotoneConj (fun _ : Fin 2 => true) ≠ evalMonotoneConj V := by
    intro heq; have := congrFun heq V; exact absurd this (by decide)
  rcases hhit _ ⟨_, rfl⟩ hne₁ with ⟨x, hx, hdx⟩
  rcases hhit _ ⟨_, rfl⟩ hne₂ with ⟨y, hy, hdy⟩
  have hx0 : x 0 = false := by
    cases h : x 0
    · rfl
    · exfalso; apply hdx
      cases h1 : x 1 <;> simp [evalMonotoneConj, finRange_two, h, h1]
  have hy0 : y 0 = true := by
    cases h : y 0
    · exfalso; apply hdy
      cases h1 : y 1 <;> simp [evalMonotoneConj, finRange_two, h, h1]
    · rfl
  have hxy : x ≠ y := fun heq => by rw [heq, hy0] at hx0; cases hx0
  exact two_le_length_of_two_mem S x y hx hy hxy

/-- Full concrete check of `monotone_conj_teaching_set_exact` (including the
`HasMinTeachingSize` lower bound) at `m = 2, r = 0`. -/
theorem monotone_conj_m2_r0_exact :
    let V : Fin 2 → Bool := fun _ => false
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) 2 ∧
    HasMinTeachingSize (MonotoneConjunctions 2) (evalMonotoneConj V)
      (min (relevantCount V + 1) 2) := by
  dsimp only
  let V : Fin 2 → Bool := fun _ => false
  have hmin : min (relevantCount V + 1) 2 = 1 := by decide
  rw [show min (relevantCount (fun _ : Fin 2 => false) + 1) 2 = 1 from hmin]
  refine ⟨monotone_conj_m2_empty_teaches.1, monotone_conj_m2_empty_teaches.2,
    ⟨⟨_, monotone_conj_m2_empty_teaches.2, monotone_conj_m2_empty_teaches.1⟩, ?_⟩⟩
  intro S hT
  cases S with
  | nil =>
    have heq := hT.2.2 (evalMonotoneConj (fun _ : Fin 2 => true)) ⟨_, rfl⟩
      (fun _ hp => by cases hp)
    have := congrFun heq (fun _ => false)
    exact absurd this (by decide)
  | cons _ _ => simp

/-- Full concrete check of `monotone_conj_teaching_set_exact` (including the
`HasMinTeachingSize` lower bound) at `m = 2, r = 2`. -/
theorem monotone_conj_m2_r2_exact :
    let V : Fin 2 → Bool := fun _ => true
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) 2 ∧
    HasMinTeachingSize (MonotoneConjunctions 2) (evalMonotoneConj V)
      (min (relevantCount V + 1) 2) := by
  dsimp only
  let V : Fin 2 → Bool := fun _ => true
  have hmin : min (relevantCount V + 1) 2 = 2 := by decide
  rw [show min (relevantCount (fun _ : Fin 2 => true) + 1) 2 = 2 from hmin]
  refine ⟨monotone_conj_m2_all_teaches.1, monotone_conj_m2_all_teaches.2,
    ⟨⟨_, monotone_conj_m2_all_teaches.2, monotone_conj_m2_all_teaches.1⟩, ?_⟩⟩
  intro S hT
  have hhit := (teaches_iff_hits_disagreement_sets_of_mem_of_consistent
    (MonotoneConjunctions 2) (evalMonotoneConj V) S hT.1 hT.2.1).mp hT
  have hne0 : evalMonotoneConj (fun i : Fin 2 => decide (i.val = 0)) ≠
      evalMonotoneConj V := by
    intro heq; have := congrFun heq (flipBit (1 : Fin 2)); cases this
  have hne1 : evalMonotoneConj (fun i : Fin 2 => decide (i.val = 1)) ≠
      evalMonotoneConj V := by
    intro heq; have := congrFun heq (flipBit (0 : Fin 2)); cases this
  rcases hhit _ ⟨fun i => decide (i.val = 0), rfl⟩ hne0 with ⟨x1, hx1, hd1⟩
  rcases hhit _ ⟨fun i => decide (i.val = 1), rfl⟩ hne1 with ⟨x0, hx0, hd0⟩
  have hx1_eq : x1 = flipBit (1 : Fin 2) := by
    apply fin2_fun_ext
    · cases h : x1 0
      · exfalso; apply hd1; simp [evalMonotoneConj, finRange_two, V, h]
      · rfl
    · cases h : x1 1
      · rfl
      · exfalso; apply hd1; cases h0 : x1 0 <;> simp [evalMonotoneConj, finRange_two, V, h, h0]
  have hx0_eq : x0 = flipBit (0 : Fin 2) := by
    apply fin2_fun_ext
    · cases h : x0 0
      · rfl
      · exfalso; apply hd0; cases h1 : x0 1 <;> simp [evalMonotoneConj, finRange_two, V, h, h1]
    · cases h : x0 1
      · exfalso; apply hd0; simp [evalMonotoneConj, finRange_two, V, h]
      · rfl
  have hdistinct : x0 ≠ x1 := by
    rw [hx0_eq, hx1_eq]
    intro heq; have := congrFun heq 0; cases this
  exact two_le_length_of_two_mem S x0 x1 hx0 hx1 hdistinct

/-- Concrete check for the degenerate edge case `m = 0`: the class has one
monotone conjunction (`⊤`), taught by the empty sample, so its teaching
dimension is `0`. -/
theorem monotone_conjunctions_m0_td :
    HasTeachingDimension (MonotoneConjunctions 0) 0 := by
  constructor
  · intro h ⟨V, hV⟩
    refine ⟨[], Nat.le_refl 0, ⟨V, hV⟩, (fun _ hp => by cases hp), ?_⟩
    intro g ⟨W, hW⟩ _
    rw [← hW, ← hV]
    congr 1
    funext i
    exact Fin.elim0 i
  · exact ⟨evalMonotoneConj Fin.elim0, ⟨Fin.elim0, rfl⟩, fun _ _ => Nat.zero_le _⟩

/-! ### Result 5: Exact Minimum Teaching-Set Size for Monotone Conjunctions -/

private theorem evalMonotoneConj_eq_false_iff {m : Nat}
    (V : Fin m → Bool) (x : BoolAssignment m) :
    evalMonotoneConj V x = false ↔ ∃ i : Fin m, V i = true ∧ x i = false := by
  constructor
  · intro hfalse
    apply Classical.byContradiction
    intro hno
    have htrue : evalMonotoneConj V x = true := by
      rw [evalMonotoneConj_eq_true_iff]
      intro i hVi
      cases hxi : x i
      · exact absurd ⟨i, hVi, hxi⟩ hno
      · rfl
    rw [htrue] at hfalse
    cases hfalse
  · rintro ⟨i, hVi, hxi⟩
    cases heval : evalMonotoneConj V x
    · rfl
    · have h := (evalMonotoneConj_eq_true_iff V x).mp heval i hVi
      rw [hxi] at h
      cases h

private theorem evalMonotoneConj_self {m : Nat} (V : Fin m → Bool) :
    evalMonotoneConj V V = true :=
  (evalMonotoneConj_eq_true_iff V V).mpr (fun _ h => h)

private theorem evalMonotoneConj_flipBit {m : Nat}
    (W : Fin m → Bool) (i : Fin m) :
    evalMonotoneConj W (flipBit i) = !W i := by
  cases hWi : W i
  · simp only [Bool.not_false]
    rw [evalMonotoneConj_eq_true_iff]
    intro k hWk
    have hne : k ≠ i := fun heq => by subst heq; rw [hWi] at hWk; cases hWk
    simp [flipBit, hne]
  · simp only [Bool.not_true]
    rw [evalMonotoneConj_eq_false_iff]
    exact ⟨i, hWi, by simp [flipBit]⟩

private theorem filter_length_eq_length_iff {α : Type}
    (p : α → Bool) (L : List α) :
    (L.filter p).length = L.length ↔ ∀ a ∈ L, p a = true := by
  induction L with
  | nil => simp
  | cons a as ih =>
    cases hp : p a
    · constructor
      · intro hlen
        simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
        have hle := List.length_filter_le p as
        omega
      · intro hall
        have := hall a (by simp)
        rw [hp] at this
        cases this
    · simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons, Nat.succ.injEq,
        List.mem_cons]
      constructor
      · intro hlen b hb
        rcases hb with rfl | hmem
        · exact hp
        · exact ih.mp hlen b hmem
      · intro hall
        exact ih.mpr (fun b hb => hall b (Or.inr hb))

private theorem relevantCount_lt_iff_exists_false {m : Nat} (V : Fin m → Bool) :
    relevantCount V < m ↔ ∃ j : Fin m, V j = false := by
  have hle : relevantCount V ≤ m := relevantCount_le V
  constructor
  · intro hlt
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i ∈ List.finRange m, V i = true := by
      intro i _
      cases hVi : V i
      · exact absurd ⟨i, hVi⟩ hno
      · rfl
    have heq : relevantCount V = m := by
      unfold relevantCount
      rw [(filter_length_eq_length_iff (fun i => V i) (List.finRange m)).mpr hall,
        List.length_finRange]
    omega
  · rintro ⟨j, hj⟩
    apply Nat.lt_of_le_of_ne hle
    intro heq
    have hlen : ((List.finRange m).filter (fun i => V i)).length = (List.finRange m).length := by
      rw [List.length_finRange]
      exact heq
    have hjtrue := (filter_length_eq_length_iff (fun i => V i) (List.finRange m)).mp hlen j
      (List.mem_finRange j)
    rw [hj] at hjtrue
    cases hjtrue

private theorem mem_monotoneConjNegExamples_of {m : Nat} (V : Fin m → Bool)
    {i : Fin m} (hi : V i = true) :
    (flipBit i, false) ∈ monotoneConjNegExamples V := by
  unfold monotoneConjNegExamples
  exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, hi⟩, rfl⟩

private theorem monotoneConjNegExamples_subset_teachingSet {m : Nat} (V : Fin m → Bool) :
    ∀ p ∈ monotoneConjNegExamples V, p ∈ monotoneConjTeachingSet V := by
  intro p hp
  unfold monotoneConjTeachingSet
  split
  · exact List.mem_cons_of_mem _ hp
  · exact hp

private def dropVar {m : Nat} (V : Fin m → Bool) (i : Fin m) : Fin m → Bool :=
  fun k => if k = i then false else V k

private def addVar {m : Nat} (V : Fin m → Bool) (j : Fin m) : Fin m → Bool :=
  fun k => if k = j then true else V k

private theorem dropVar_ne {m : Nat} (V : Fin m → Bool) {i : Fin m} (hVi : V i = true) :
    evalMonotoneConj (dropVar V i) ≠ evalMonotoneConj V := by
  intro heq
  have hval := congrFun heq (flipBit i)
  rw [evalMonotoneConj_flipBit, evalMonotoneConj_flipBit] at hval
  have hd : dropVar V i i = false := by simp [dropVar]
  rw [hd, hVi] at hval
  cases hval

private theorem addVar_ne {m : Nat} (V : Fin m → Bool) {j : Fin m} (hVj : V j = false) :
    evalMonotoneConj (addVar V j) ≠ evalMonotoneConj V := by
  intro heq
  have hval := congrFun heq V
  rw [evalMonotoneConj_self] at hval
  have he : evalMonotoneConj (addVar V j) V = false := by
    rw [evalMonotoneConj_eq_false_iff]
    exact ⟨j, by simp [addVar], hVj⟩
  rw [he] at hval
  cases hval

private theorem disagreement_dropVar_props {m : Nat} (V : Fin m → Bool)
    {i : Fin m} (hVi : V i = true) {x : BoolAssignment m}
    (hdiff : DisagreementSet (evalMonotoneConj (dropVar V i)) (evalMonotoneConj V) x) :
    x i = false ∧ (∀ k : Fin m, k ≠ i → V k = true → x k = true) ∧
      evalMonotoneConj V x = false := by
  have hxi : x i = false := by
    cases hx : x i
    · rfl
    · exfalso
      apply hdiff
      apply Bool.eq_iff_iff.mpr
      rw [evalMonotoneConj_eq_true_iff, evalMonotoneConj_eq_true_iff]
      constructor
      · intro hall k hVk
        by_cases hki : k = i
        · subst hki; exact hx
        · exact hall k (by simp [dropVar, hki, hVk])
      · intro hall k hdk
        by_cases hki : k = i
        · subst hki; simp [dropVar] at hdk
        · have hVk : V k = true := by simpa [dropVar, hki] using hdk
          exact hall k hVk
  have hother : ∀ k : Fin m, k ≠ i → V k = true → x k = true := by
    intro k hki hVk
    cases hxk : x k
    · exfalso
      apply hdiff
      have hf1 : evalMonotoneConj (dropVar V i) x = false := by
        rw [evalMonotoneConj_eq_false_iff]
        exact ⟨k, by simp [dropVar, hki, hVk], hxk⟩
      have hf2 : evalMonotoneConj V x = false := by
        rw [evalMonotoneConj_eq_false_iff]
        exact ⟨k, hVk, hxk⟩
      rw [hf1, hf2]
    · rfl
  have heval : evalMonotoneConj V x = false := by
    rw [evalMonotoneConj_eq_false_iff]
    exact ⟨i, hVi, hxi⟩
  exact ⟨hxi, hother, heval⟩

private theorem disagreement_addVar_eval_true {m : Nat} (V : Fin m → Bool)
    {j : Fin m} (hVj : V j = false) {x : BoolAssignment m}
    (hdiff : DisagreementSet (evalMonotoneConj (addVar V j)) (evalMonotoneConj V) x) :
    evalMonotoneConj V x = true := by
  cases heval : evalMonotoneConj V x
  · exfalso
    apply hdiff
    rcases (evalMonotoneConj_eq_false_iff V x).mp heval with ⟨k, hVk, hxk⟩
    have hkj : k ≠ j := fun heq => by subst heq; rw [hVj] at hVk; cases hVk
    have he1 : evalMonotoneConj (addVar V j) x = false := by
      rw [evalMonotoneConj_eq_false_iff]
      exact ⟨k, by simp [addVar, hkj, hVk], hxk⟩
    rw [he1, heval]
  · rfl

private theorem exists_erase_of_mem {α : Type} (a : α) (B : List α) (h : a ∈ B) :
    ∃ B' : List α, B'.length + 1 = B.length ∧ ∀ b ∈ B, b ≠ a → b ∈ B' := by
  induction B with
  | nil => cases h
  | cons c cs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | hcs
    · refine ⟨cs, rfl, fun b hb hne => ?_⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hmem
      · exact absurd rfl hne
      · exact hmem
    · rcases ih hcs with ⟨cs', hlen, hsub⟩
      refine ⟨c :: cs', by simp [hlen], fun b hb hne => ?_⟩
      simp only [List.mem_cons] at hb ⊢
      rcases hb with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (hsub b hmem hne)

private theorem nodup_subset_length_le {α : Type}
    (A B : List α) (hnd : A.Nodup) (hsub : ∀ a ∈ A, a ∈ B) :
    A.length ≤ B.length := by
  induction A generalizing B with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    have haB : a ∈ B := hsub a (by simp)
    rcases exists_erase_of_mem a B haB with ⟨B', hlen, hsubB⟩
    have has : ∀ x ∈ as, x ∈ B' := by
      intro x hx
      have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hx)
      exact hsubB x (hsub x (by simp [hx])) hne
    have hle := ih B' hnd.2 has
    simp only [List.length_cons]
    omega

private theorem pairwise_ne_map_of {α β : Type} (P : α → Prop) (f : α → β) (L : List α)
    (hnd : L.Nodup) (hP : ∀ a ∈ L, P a)
    (hinj : ∀ a b, P a → P b → a ≠ b → f a ≠ f b) :
    (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun x hx => hP x (by simp [hx]))⟩
    intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨b, hb, hfab⟩
    have hne : b ≠ a := fun heq => hnd.1 (heq ▸ hb)
    exact hinj b a (hP b (by simp [hb])) (hP a (by simp)) hne hfab

/-- For every `m : Nat` and every monotone conjunction `V : Fin m → Bool` with
`r = relevantCount V` relevant variables, the explicit witness
`monotoneConjTeachingSet V` teaches `evalMonotoneConj V` within
`MonotoneConjunctions m`, has length `min (r + 1) m`, and achieves the exact
minimum teaching-set size `min (r + 1) m` (covering `r = 0`, `0 < r < m`,
`r = m`, and `m = 0`). -/
theorem monotone_conj_teaching_set_exact
    (m : Nat) (V : Fin m → Bool) :
    Teaches (MonotoneConjunctions m) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) m ∧
    HasMinTeachingSize (MonotoneConjunctions m) (evalMonotoneConj V)
      (min (relevantCount V + 1) m) := by
  classical
  have hTeaches : Teaches (MonotoneConjunctions m) (evalMonotoneConj V) (monotoneConjTeachingSet V) := by
    refine ⟨⟨V, rfl⟩, ?_, ?_⟩
    · intro p hp
      have hNegCon : ∀ q ∈ monotoneConjNegExamples V, evalMonotoneConj V q.1 = q.2 := by
        intro q hq
        unfold monotoneConjNegExamples at hq
        simp only [List.mem_map, List.mem_filter] at hq
        rcases hq with ⟨i, ⟨_, hi⟩, rfl⟩
        rw [evalMonotoneConj_flipBit, hi]
        rfl
      unfold monotoneConjTeachingSet at hp
      split at hp
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hmem
        · exact evalMonotoneConj_self V
        · exact hNegCon p hmem
      · exact hNegCon p hp
    · rintro g ⟨W, rfl⟩ hcon
      suffices hWV : W = V by rw [hWV]
      funext i
      cases hVi : V i
      · have hlt : relevantCount V < m := (relevantCount_lt_iff_exists_false V).mpr ⟨i, hVi⟩
        have hmemPos : (V, true) ∈ monotoneConjTeachingSet V := by
          unfold monotoneConjTeachingSet
          simp [hlt]
        have hpos : evalMonotoneConj W V = true := hcon (V, true) hmemPos
        cases hWi : W i
        · rfl
        · have htrue := (evalMonotoneConj_eq_true_iff W V).mp hpos i hWi
          rw [hVi] at htrue
          cases htrue
      · have hmemNeg : (flipBit i, false) ∈ monotoneConjTeachingSet V :=
          monotoneConjNegExamples_subset_teachingSet V _ (mem_monotoneConjNegExamples_of V hVi)
        have hneg : evalMonotoneConj W (flipBit i) = false := hcon (flipBit i, false) hmemNeg
        rw [evalMonotoneConj_flipBit] at hneg
        cases hWi : W i
        · simp [hWi] at hneg
        · rfl
  have hLen : (monotoneConjTeachingSet V).length = min (relevantCount V + 1) m :=
    monotoneConjTeachingSet_length V
  refine ⟨hTeaches, hLen, ⟨⟨monotoneConjTeachingSet V, hLen, hTeaches⟩, ?_⟩⟩
  intro S hTS
  have hHit : HitsAllDisagreements (MonotoneConjunctions m) (evalMonotoneConj V) (S.map Prod.fst) :=
    (teaches_iff_hits_disagreement_sets_of_mem_of_consistent
      (MonotoneConjunctions m) (evalMonotoneConj V) S hTS.1 hTS.2.1).mp hTS
  have hNegProp : ∀ i : Fin m, V i = true →
      ∃ x ∈ S.map Prod.fst,
        x i = false ∧ (∀ k : Fin m, k ≠ i → V k = true → x k = true) ∧
        evalMonotoneConj V x = false := by
    intro i hVi
    rcases hHit (evalMonotoneConj (dropVar V i)) ⟨dropVar V i, rfl⟩ (dropVar_ne V hVi) with
      ⟨x, hx, hdiff⟩
    exact ⟨x, hx, disagreement_dropVar_props V hVi hdiff⟩
  let pickNeg : Fin m → BoolAssignment m := fun i =>
    if hi : V i = true then Classical.choose (hNegProp i hi) else fun _ => false
  have hpickSpec : ∀ (i : Fin m) (hi : V i = true),
      pickNeg i ∈ S.map Prod.fst ∧
      pickNeg i i = false ∧
      (∀ k : Fin m, k ≠ i → V k = true → pickNeg i k = true) ∧
      evalMonotoneConj V (pickNeg i) = false := by
    intro i hi
    dsimp only [pickNeg]
    split
    · exact Classical.choose_spec (hNegProp i ‹_›)
    · contradiction
  let relList : List (Fin m) := (List.finRange m).filter (fun i => V i)
  let W_neg : List (BoolAssignment m) := relList.map pickNeg
  have hW_len : W_neg.length = relevantCount V := by
    simp [W_neg, relList, relevantCount]
  have hW_nd : W_neg.Nodup := by
    apply pairwise_ne_map_of (fun i : Fin m => V i = true) pickNeg relList
    · exact (List.nodup_finRange m).filter _
    · intro i hi
      exact (List.mem_filter.mp hi).2
    · intro i j hi hj hij heq
      have h1 : pickNeg i j = true := (hpickSpec i hi).2.2.1 j hij.symm hj
      have h2 : pickNeg j j = false := (hpickSpec j hj).2.1
      have h3 := congrFun heq j
      rw [h1, h2] at h3
      cases h3
  have hW_sub : ∀ x ∈ W_neg, x ∈ S.map Prod.fst := by
    intro x hx
    simp only [W_neg, List.mem_map] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact (hpickSpec i (List.mem_filter.mp hi).2).1
  have hW_false : ∀ x ∈ W_neg, evalMonotoneConj V x = false := by
    intro x hx
    simp only [W_neg, List.mem_map] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact (hpickSpec i (List.mem_filter.mp hi).2).2.2.2
  have hle_m : relevantCount V ≤ m := relevantCount_le V
  by_cases hlt : relevantCount V < m
  · have hmin : min (relevantCount V + 1) m = relevantCount V + 1 := by omega
    rw [hmin]
    rcases (relevantCount_lt_iff_exists_false V).mp hlt with ⟨j₀, hj₀⟩
    rcases hHit (evalMonotoneConj (addVar V j₀)) ⟨addVar V j₀, rfl⟩ (addVar_ne V hj₀) with
      ⟨xpos, hxpos, hdiff⟩
    have htrue : evalMonotoneConj V xpos = true :=
      disagreement_addVar_eval_true V hj₀ hdiff
    have hnotmem : xpos ∉ W_neg := by
      intro hmem
      have hfalse := hW_false xpos hmem
      rw [htrue] at hfalse
      cases hfalse
    have hnd_all : (xpos :: W_neg).Nodup := List.nodup_cons.mpr ⟨hnotmem, hW_nd⟩
    have hsub_all : ∀ x ∈ xpos :: W_neg, x ∈ S.map Prod.fst := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hmem
      · exact hxpos
      · exact hW_sub x hmem
    have hle := nodup_subset_length_le (xpos :: W_neg) (S.map Prod.fst) hnd_all hsub_all
    simp only [List.length_cons, List.length_map, hW_len] at hle
    exact hle
  · have hmin : min (relevantCount V + 1) m = relevantCount V := by omega
    rw [hmin]
    have hle := nodup_subset_length_le W_neg (S.map Prod.fst) hW_nd hW_sub
    simp only [List.length_map, hW_len] at hle
    exact hle

/-- Non-vacuity witness for `monotone_conj_teaching_set_exact`: directly proves
the full conclusion (teaching, length, and `HasMinTeachingSize` lower bound) at
`m = 2, V = {0}` (`r = 1`), without invoking the general theorem. -/
theorem monotone_conj_teaching_set_exact_nonvacuity :
    let V : Fin 2 → Bool := fun i => decide (i.val = 0)
    Teaches (MonotoneConjunctions 2) (evalMonotoneConj V) (monotoneConjTeachingSet V) ∧
    (monotoneConjTeachingSet V).length = min (relevantCount V + 1) 2 ∧
    HasMinTeachingSize (MonotoneConjunctions 2) (evalMonotoneConj V)
      (min (relevantCount V + 1) 2) :=
  monotone_conj_m2_r1_exact

/-! ### Result 6: Teaching Dimension of Monotone Conjunctions (Corollary of Result 5) -/

/-- The teaching dimension of the class of monotone conjunctions over `m`
Boolean features is `m` (including `m = 0`). Derived directly from
`monotone_conj_teaching_set_exact`. -/
theorem monotone_conjunctions_teaching_dimension (m : Nat) :
    HasTeachingDimension (MonotoneConjunctions m) m := by
  constructor
  · rintro h ⟨V, rfl⟩
    obtain ⟨hT, hlen, _⟩ := monotone_conj_teaching_set_exact m V
    exact ⟨monotoneConjTeachingSet V, by rw [hlen]; exact Nat.min_le_right _ _, hT⟩
  · refine ⟨evalMonotoneConj (fun _ : Fin m => true), ⟨fun _ => true, rfl⟩, ?_⟩
    intro S hT
    have hmin := (monotone_conj_teaching_set_exact m (fun _ => true)).2.2.2 S hT
    have hr : relevantCount (fun _ : Fin m => true) = m := by
      unfold relevantCount
      rw [List.filter_eq_self.mpr (fun _ _ => rfl), List.length_finRange]
    rw [hr] at hmin
    omega

/-- Non-vacuity witness for `monotone_conjunctions_teaching_dimension`: a
direct, self-contained proof that `HasTeachingDimension (MonotoneConjunctions 2) 2`
holds without invoking `monotone_conj_teaching_set_exact`. -/
theorem monotone_conjunctions_teaching_dimension_nonvacuity :
    HasTeachingDimension (MonotoneConjunctions 2) 2 := by
  constructor
  · intro h ⟨V, hV⟩
    rw [← hV]
    cases h0 : V 0 <;> cases h1 : V 1
    · have hEq : V = fun _ => false := fin2_fun_ext h0 h1
      rw [hEq]
      exact ⟨monotoneConjTeachingSet (fun _ => false),
        by rw [monotone_conj_m2_empty_teaches.2]; omega,
        monotone_conj_m2_empty_teaches.1⟩
    · let V1 : Fin 2 → Bool := fun i => decide (i.val = 1)
      have hEq : V = V1 := fin2_fun_ext h0 h1
      rw [hEq]
      have hset : monotoneConjTeachingSet V1 = [(V1, true), (flipBit (1 : Fin 2), false)] := by
        simp [monotoneConjTeachingSet, relevantCount, monotoneConjNegExamples, finRange_two, V1]
      refine ⟨monotoneConjTeachingSet V1, by rw [hset]; decide, ⟨V1, rfl⟩, ?_, ?_⟩
      · intro p hp
        rw [hset] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> decide
      · intro g hg hcon
        rcases hg with ⟨W, rfl⟩
        have hpos : evalMonotoneConj W V1 = true :=
          hcon (V1, true) (by rw [hset]; simp)
        have hneg : evalMonotoneConj W (flipBit (1 : Fin 2)) = false :=
          hcon (flipBit (1 : Fin 2), false) (by rw [hset]; simp)
        have hW0 : W 0 = false := by
          cases hw : W 0 with
          | false => rfl
          | true =>
            have hv0 := (evalMonotoneConj_eq_true_iff W V1).mp hpos 0 hw
            cases hv0
        have hW1 : W 1 = true := by
          cases hw : W 1 with
          | true => rfl
          | false =>
            have htrue : evalMonotoneConj W (flipBit (1 : Fin 2)) = true := by
              rw [evalMonotoneConj_eq_true_iff]
              intro i hi
              match i with
              | ⟨0, _⟩ => change W 0 = true at hi; rw [hW0] at hi; cases hi
              | ⟨1, _⟩ => change W 1 = true at hi; rw [hw] at hi; cases hi
            rw [htrue] at hneg; cases hneg
        have hWeq : W = V1 := fin2_fun_ext hW0 hW1
        rw [hWeq]
    · have hEq : V = fun i => decide (i.val = 0) := fin2_fun_ext h0 h1
      rw [hEq]
      exact ⟨monotoneConjTeachingSet (fun i => decide (i.val = 0)),
        by rw [monotone_conj_m2_single_teaches.2]; omega,
        monotone_conj_m2_single_teaches.1⟩
    · have hEq : V = fun _ => true := fin2_fun_ext h0 h1
      rw [hEq]
      exact ⟨monotoneConjTeachingSet (fun _ => true),
        by rw [monotone_conj_m2_all_teaches.2]; omega,
        monotone_conj_m2_all_teaches.1⟩
  · refine ⟨evalMonotoneConj (fun _ => true), ⟨fun _ => true, rfl⟩, ?_⟩
    exact monotone_conj_m2_r2_exact.2.2.2

end Toy.Witness
