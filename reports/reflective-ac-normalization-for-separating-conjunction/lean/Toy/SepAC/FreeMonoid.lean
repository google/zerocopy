import Toy.SepAC.Normalization

/-!
# Free Commutative Monoid Completeness, Pointwise-Idempotent and Conflict Incompleteness

Constructs the free commutative monoid `Bag` on `Nat` (finitely supported multiplicity
functions `Nat → Nat`, i.e. finite multisets of atom indices) using core Lean only,
proves exact completeness and `↔` characterization of `List.isPerm` relative to `Bag`
(`isPerm_of_bag_denote_eq`, `isPerm_iff_bag_denote_eq`), and proves incompleteness
results across multiple non-free settings:

1. Pointwise idempotence of a single atom value (`IdemElem sep (env 0)`), for any atom value
   that is idempotent as a propositional equality (e.g. `conflict` in a mixed model)
   (`denote_eq_and_isPerm_false_of_idemElem`, with global `SepIdem` as a corollary).
2. Non-idempotent models with absorbing ownership-conflict elements (`CellModel` and
   `TwoCellModel`): incompleteness at specific environments despite `¬ SepIdem`, no aliasing
   (`cellModel_incomplete_without_sepIdem`, `twoCellModel_conflict_distinct_atoms_incomplete`).
3. Aliased and out-of-bounds `listEnv` environments even inside `Bag`
   (`bag_aliased_env_denote_eq_not_isPerm`, `bag_listEnv_oob_denote_eq_not_isPerm`).
4. Incompleteness of set-equality (deduplication) checks on arbitrary idempotent models
   (`boolOr_setCheck_incomplete`).
-/

namespace Toy.SepAC

universe u

/-- Finite support predicate on multiplicity functions `Nat → Nat`: all atom indices
at or above some `bound` have multiplicity `0`. -/
def FiniteSupport (f : Nat → Nat) : Prop :=
  ∃ bound : Nat, ∀ i : Nat, bound ≤ i → f i = 0

/-- Positive example for `FiniteSupport`: the zero multiplicity map has bound `0`. -/
theorem finiteSupport_zero : FiniteSupport (fun _ => 0) :=
  ⟨0, fun _ _ => rfl⟩

/-- Negative example for `FiniteSupport`: the constant-`1` map is not finitely supported. -/
theorem not_finiteSupport_const_one : ¬ FiniteSupport (fun _ => 1) := by
  rintro ⟨bound, h⟩
  have h1 := h bound (Nat.le_refl bound)
  cases h1

/-- Free commutative monoid on `Nat`: finitely supported multiplicity functions
(multisets of atom indices). -/
structure Bag where
  count : Nat → Nat
  finite : FiniteSupport count

@[ext]
theorem Bag.ext {b₁ b₂ : Bag} (h : ∀ i : Nat, b₁.count i = b₂.count i) : b₁ = b₂ := by
  cases b₁ with
  | mk c₁ f₁ =>
    cases b₂ with
    | mk c₂ f₂ =>
      have hc : c₁ = c₂ := funext h
      subst hc
      rfl

/-- Empty multiset (unit element of `Bag`). -/
def Bag.emp : Bag where
  count := fun _ => 0
  finite := finiteSupport_zero

/-- Free generator sending atom index `k` to its singleton multiset. -/
def Bag.single (k : Nat) : Bag where
  count := fun i => if i == k then 1 else 0
  finite := ⟨k + 1, by
    intro i hi
    have hne : (i == k) = false := beq_false_of_ne (by omega)
    simp [hne]⟩

/-- Multiset sum (pointwise multiplicity addition) on `Bag`. -/
def Bag.sep (b₁ b₂ : Bag) : Bag where
  count := fun i => b₁.count i + b₂.count i
  finite := by
    rcases b₁.finite with ⟨n₁, h₁⟩
    rcases b₂.finite with ⟨n₂, h₂⟩
    refine ⟨Nat.max n₁ n₂, fun i hi => ?_⟩
    have hi₁ : n₁ ≤ i := Nat.le_trans (Nat.le_max_left n₁ n₂) hi
    have hi₂ : n₂ ≤ i := Nat.le_trans (Nat.le_max_right n₁ n₂) hi
    dsimp only
    rw [h₁ i hi₁, h₂ i hi₂]

/-! ## Algebraic laws and examples for `Bag` -/

theorem bag_sepAssoc : SepAssoc Bag.sep := by
  intro x y z
  apply Bag.ext
  intro i
  exact Nat.add_assoc (x.count i) (y.count i) (z.count i)

theorem bag_sepComm : SepComm Bag.sep := by
  intro x y
  apply Bag.ext
  intro i
  exact Nat.add_comm (x.count i) (y.count i)

theorem bag_rightUnit : RightUnit Bag.sep Bag.emp := by
  intro x
  apply Bag.ext
  intro i
  exact Nat.add_zero (x.count i)

theorem bag_not_sepIdem : ¬ SepIdem Bag.sep := by
  intro h
  have h0 := congrArg (fun b => b.count 0) (h (Bag.single 0))
  simp [Bag.sep, Bag.single] at h0

theorem bag_single_zero_not_idemElem : ¬ IdemElem Bag.sep (Bag.single 0) := by
  intro h
  have h0 := congrArg (fun b => b.count 0) h
  simp [Bag.sep, Bag.single] at h0

theorem bag_pos_example :
    Bag.sep (Bag.single 0) (Bag.single 1) = Bag.sep (Bag.single 1) (Bag.single 0) :=
  bag_sepComm (Bag.single 0) (Bag.single 1)

theorem bag_neg_example :
    Bag.sep (Bag.single 0) (Bag.single 0) ≠ Bag.single 0 := by
  intro h
  have h0 := congrArg (fun b => b.count 0) h
  simp [Bag.sep, Bag.single] at h0

/-! ## Result 3a: Completeness and `↔` characterization relative to `Bag` -/

/-- Multiplicity homomorphism: evaluating `t` in `Bag` under `Bag.single` counts
each atom index exactly as many times as it occurs in `t.atoms`. -/
theorem bag_count_denote (t : Tree) (k : Nat) :
    (t.denote Bag.sep Bag.emp Bag.single).count k = t.atoms.count k := by
  induction t with
  | atom i =>
    simp only [Tree.denote, Tree.atoms, Bag.single, List.count_cons, List.count_nil]
    by_cases h : k = i
    · subst h; simp
    · have h' : (i == k) = false := beq_false_of_ne (Ne.symm h)
      simp [h, h']
  | unit => rfl
  | node l r ihl ihr =>
    simp [Tree.denote, Tree.atoms, Bag.sep, List.count_append, ihl, ihr]

/-- **Completeness of `List.isPerm` relative to the free commutative monoid `Bag`.**
If two syntax trees `l` and `r` evaluate to the same multiset in `(Bag, Bag.sep, Bag.emp)`
under the free generator map `Bag.single`, then `l.atoms.isPerm r.atoms = true`. -/
theorem isPerm_of_bag_denote_eq {l r : Tree}
    (hDenote : l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single) :
    l.atoms.isPerm r.atoms = true := by
  apply List.isPerm_iff.mpr
  apply List.perm_iff_count.mpr
  intro k
  rw [← bag_count_denote l k, ← bag_count_denote r k, hDenote]

/-- **Soundness and completeness (`↔` characterization) in `Bag` (`R3a-iff`).**
Under the free generator environment `Bag.single`, two syntax trees have equal `Bag`
denotations if and only if `l.atoms.isPerm r.atoms = true`. -/
theorem isPerm_iff_bag_denote_eq (l r : Tree) :
    l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single ↔
      l.atoms.isPerm r.atoms = true :=
  ⟨isPerm_of_bag_denote_eq,
   acu_denote_eq_of_isPerm Bag.sep Bag.emp bag_sepAssoc bag_sepComm bag_rightUnit Bag.single⟩

/-- Non-vacuity witness for `isPerm_of_bag_denote_eq`: two distinct syntax trees
`(atom 0 ∗ unit) ∗ atom 1` and `atom 1 ∗ atom 0` have identical denotations in `Bag`
under `Bag.single`. -/
theorem isPerm_of_bag_denote_eq_nonvacuous :
    let l : Tree := .node (.node (.atom 0) .unit) (.atom 1)
    let r : Tree := .node (.atom 1) (.atom 0)
    l ≠ r ∧ l.denote Bag.sep Bag.emp Bag.single = r.denote Bag.sep Bag.emp Bag.single := by
  refine ⟨by decide, ?_⟩
  apply Bag.ext
  intro i
  simp [Tree.denote, Bag.sep, Bag.emp, Bag.single]
  omega

/-- Canonical tightness of `hDenote` in `isPerm_of_bag_denote_eq`: without equal `Bag`
denotations, `atom 0` and `atom 1` fail `List.isPerm`. -/
theorem bag_tight_denote_eq :
    let l : Tree := .atom 0
    let r : Tree := .atom 1
    l.denote Bag.sep Bag.emp Bag.single ≠ r.denote Bag.sep Bag.emp Bag.single ∧
      l.atoms.isPerm r.atoms = false := by
  refine ⟨?_, by decide⟩
  intro h
  have h0 := congrArg (fun b => b.count 0) h
  simp [Tree.denote, Bag.single] at h0

/-- Scope witness (aliased environments in `Bag`): even inside `Bag`, if `env` maps
distinct indices `0` and `1` to the same generator, `atom 0` and `atom 1` have equal
denotations while `isPerm = false`, refuting completeness for arbitrary `env : Nat → Bag`. -/
theorem bag_aliased_env_denote_eq_not_isPerm :
    let env : Nat → Bag := fun _ => Bag.single 0
    let l : Tree := .atom 0
    let r : Tree := .atom 1
    l.denote Bag.sep Bag.emp env = r.denote Bag.sep Bag.emp env ∧
      l.atoms.isPerm r.atoms = false :=
  ⟨rfl, by decide⟩

/-- Scope witness (unit-valued / out-of-bounds `listEnv` in `Bag`): even inside `Bag`,
an out-of-bounds `listEnv` lookup maps `atom 0` to `Bag.emp`, equating `atom 0` with
`unit` while `isPerm = false`, refuting completeness for arbitrary `env : Nat → Bag`. -/
theorem bag_listEnv_oob_denote_eq_not_isPerm :
    let env : Nat → Bag := listEnv Bag.emp []
    let l : Tree := .atom 0
    let r : Tree := .unit
    l.denote Bag.sep Bag.emp env = r.denote Bag.sep Bag.emp env ∧
      l.atoms.isPerm r.atoms = false :=
  ⟨rfl, by decide⟩

/-- **Universal ACU equational completeness corollary (`R3a-iff` companion).**
Two syntax trees satisfy `l.atoms.isPerm r.atoms = true` if and only if they denote
equally in every `Type`-level associative, commutative, right-unital model `(P, sep, emp)`
and every environment `env : Nat → P`. -/
theorem isPerm_iff_forall_acu_denote_eq (l r : Tree) :
    l.atoms.isPerm r.atoms = true ↔
      (∀ (P : Type) (sep : P → P → P) (emp : P),
        SepAssoc sep → SepComm sep → RightUnit sep emp →
        ∀ env : Nat → P, l.denote sep emp env = r.denote sep emp env) :=
  ⟨fun hPerm _ sep emp hA hC hR env => acu_denote_eq_of_isPerm sep emp hA hC hR env hPerm,
   fun h => isPerm_of_bag_denote_eq
     (h Bag Bag.sep Bag.emp bag_sepAssoc bag_sepComm bag_rightUnit Bag.single)⟩

/-- **Universal AC necessity of equal `unitCount` and `isPerm` (`R1c-unit-count` converse).**
If `l` and `r` denote equally in every `Type`-level associative-commutative model `(P, sep)`
with arbitrary `emp : P` and environment `env : Nat → P`, then `l.unitCount = r.unitCount`
and `l.atoms.isPerm r.atoms = true`. -/
theorem unitCount_eq_and_isPerm_of_forall_ac_denote_eq {l r : Tree}
    (h : ∀ (P : Type) (sep : P → P → P) (emp : P), SepAssoc sep → SepComm sep →
      ∀ env : Nat → P, l.denote sep emp env = r.denote sep emp env) :
    l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true := by
  have hd := h Bag Bag.sep (Bag.single 0) bag_sepAssoc bag_sepComm (fun i => Bag.single (i + 1))
  have key : ∀ (t : Tree) (k : Nat),
      (t.denote Bag.sep (Bag.single 0) (fun i => Bag.single (i + 1))).count k =
        (shiftTree t).atoms.count k := by
    intro t k
    have h1 : t.denote Bag.sep (Bag.single 0) (fun i => Bag.single (i + 1)) =
        (shiftTree t).denote Bag.sep Bag.emp Bag.single := by
      induction t with
      | atom i => rfl
      | unit => rfl
      | node a b iha ihb => simp [Tree.denote, shiftTree, iha, ihb]
    rw [h1, bag_count_denote]
  refine ⟨?_, ?_⟩
  · rw [← count_shift_zero l, ← count_shift_zero r, ← key l 0, ← key r 0, hd]
  · apply List.isPerm_iff.mpr
    apply List.perm_iff_count.mpr
    intro k
    rw [← count_shift_succ l k, ← count_shift_succ r k, ← key l (k + 1), ← key r (k + 1), hd]

/-- Scope witness for `unitCount_eq_and_isPerm_of_forall_ac_denote_eq`: in a single fixed
associative-commutative model where `emp` happens to be a unit (such as `(Nat, Nat.add, 0)`),
equal `unitCount` is not necessary for `l.denote = r.denote`. -/
theorem unitCount_eq_not_necessary_in_fixed_model :
    (Tree.atom 0).unitCount ≠ (Tree.node (.atom 0) .unit).unitCount ∧
    ∀ env : Nat → Nat,
      (Tree.atom 0).denote Nat.add 0 env = (Tree.node (.atom 0) .unit).denote Nat.add 0 env :=
  ⟨by decide, fun env => (Nat.add_zero (env 0)).symm⟩

/-! ## Result 3b: Pointwise-idempotent and non-idempotent conflict incompleteness -/

/-- Duplicated-atom witness tree `atom 0 ∗ atom 0` for testing idempotent atom values. -/
def dupAtomTree : Tree := .node (.atom 0) (.atom 0)

/-- Single-atom witness tree `atom 0` for testing idempotent atom values. -/
def singleAtomTree : Tree := .atom 0

/-- **Pointwise-idempotent incompleteness of `List.isPerm`.**
Whenever a single atom value satisfies `IdemElem sep (env 0)` (`env 0 ∗ env 0 = env 0`) —
even in a mixed separation logic whose `sep` is **not** globally idempotent —
`dupAtomTree` (`atom 0 ∗ atom 0`) and `singleAtomTree` (`atom 0`) have equal denotations
while `dupAtomTree.atoms.isPerm singleAtomTree.atoms = false`. -/
theorem denote_eq_and_isPerm_false_of_idemElem {P : Type u}
    (sep : P → P → P) (emp : P) (env : Nat → P)
    (hIdem0 : IdemElem sep (env 0)) :
    dupAtomTree.denote sep emp env = singleAtomTree.denote sep emp env ∧
      dupAtomTree.atoms.isPerm singleAtomTree.atoms = false :=
  ⟨hIdem0, by decide⟩

/-- Global-idempotence corollary of `denote_eq_and_isPerm_false_of_idemElem`: when
`SepIdem sep` holds everywhere, `dupAtomTree` and `singleAtomTree` denote equally in every
environment `env` while `List.isPerm` returns `false`. -/
theorem denote_eq_and_isPerm_false_of_sepIdem {P : Type u}
    (sep : P → P → P) (emp : P) (hIdem : SepIdem sep) (env : Nat → P) :
    dupAtomTree.denote sep emp env = singleAtomTree.denote sep emp env ∧
      dupAtomTree.atoms.isPerm singleAtomTree.atoms = false :=
  denote_eq_and_isPerm_false_of_idemElem sep emp env (hIdem (env 0))

/-- **Non-vacuity witness (globally idempotent ACU model):**
`(Bool, Bool.or, false)` is a nontrivial (`true ≠ false`) associative, commutative,
unital, globally idempotent model in which `IdemElem Bool.or (env 0)` holds at `env 0 = true`
and `dupAtomTree` vs `singleAtomTree` denote equally while `isPerm` returns `false`. -/
theorem idempotent_bool_acu_incomplete :
    SepAssoc Bool.or ∧
    SepComm Bool.or ∧
    RightUnit Bool.or false ∧
    SepIdem Bool.or ∧
    (let env : Nat → Bool := fun _ => true
     env 0 ≠ false ∧
       IdemElem Bool.or (env 0) ∧
       dupAtomTree.denote Bool.or false env = singleAtomTree.denote Bool.or false env ∧
       dupAtomTree.atoms.isPerm singleAtomTree.atoms = false) := by
  refine ⟨boolOr_sepAssoc, boolOr_sepComm, boolOr_rightUnit, boolOr_sepIdem,
    by decide, rfl, by decide, by decide⟩

/-- **Non-vacuity witness (mixed non-idempotent ACU model with a pointwise-idempotent atom):**
`CellModel` is ACU and violates global `SepIdem`, yet `IdemElem CellModel.sep .conflict`
holds, witnessing `denote_eq_and_isPerm_false_of_idemElem` in a non-idempotent algebra. -/
theorem cellModel_conflict_idemElem_incomplete :
    SepAssoc CellModel.sep ∧
    SepComm CellModel.sep ∧
    RightUnit CellModel.sep .empty ∧
    ¬ SepIdem CellModel.sep ∧
    (let env : Nat → CellModel := fun _ => .conflict
     IdemElem CellModel.sep (env 0) ∧
       dupAtomTree.denote CellModel.sep .empty env = singleAtomTree.denote CellModel.sep .empty env ∧
       dupAtomTree.atoms.isPerm singleAtomTree.atoms = false) := by
  refine ⟨cellModel_sepAssoc, cellModel_sepComm, cellModel_rightUnit, cellModel_not_sepIdem,
    rfl, by decide, by decide⟩

/-- **Incompleteness without global or even pointwise idempotence (absorbing conflict element):**
In the non-idempotent ACU model `CellModel`:
(a) at the pointwise-idempotent element `.conflict`, `dupAtomTree` and `singleAtomTree`
    denote equally while `isPerm = false`;
(b) at the non-idempotent element `.owned` (`¬ IdemElem CellModel.sep .owned`),
    `((atom 0 ∗ atom 0) ∗ atom 0)` and `(atom 0 ∗ atom 0)` both denote `.conflict` with
    a single atom index (no aliasing) while `isPerm = false`. -/
theorem cellModel_incomplete_without_sepIdem :
    SepAssoc CellModel.sep ∧
    SepComm CellModel.sep ∧
    RightUnit CellModel.sep .empty ∧
    ¬ SepIdem CellModel.sep ∧
    (let env : Nat → CellModel := fun _ => .conflict
     dupAtomTree.denote CellModel.sep .empty env = singleAtomTree.denote CellModel.sep .empty env ∧
       dupAtomTree.atoms.isPerm singleAtomTree.atoms = false) ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 0)
     let r : Tree := .node (.atom 0) (.atom 0)
     ¬ IdemElem CellModel.sep (env 0) ∧
       l.denote CellModel.sep .empty env = r.denote CellModel.sep .empty env ∧
       l.atoms.isPerm r.atoms = false) := by
  refine ⟨cellModel_sepAssoc, cellModel_sepComm, cellModel_rightUnit, cellModel_not_sepIdem,
    by decide, cellModel_owned_not_idemElem, by decide⟩

/-- **Distinct-atom conflict incompleteness in `TwoCellModel`:**
In the non-idempotent ACU two-cell model `TwoCellModel` under a non-aliasing environment
(`env 0 = .cellA ≠ .cellB = env 1`, neither idempotent), `(atom 0 ∗ atom 0)` and
`(atom 1 ∗ atom 1)` both denote `.conflict` while `isPerm = false`. -/
theorem twoCellModel_conflict_distinct_atoms_incomplete :
    SepAssoc TwoCellModel.sep ∧
    SepComm TwoCellModel.sep ∧
    RightUnit TwoCellModel.sep .empty ∧
    ¬ SepIdem TwoCellModel.sep ∧
    (let env : Nat → TwoCellModel := fun i => if i == 0 then .cellA else .cellB
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .node (.atom 1) (.atom 1)
     env 0 ≠ env 1 ∧
       ¬ IdemElem TwoCellModel.sep (env 0) ∧
       ¬ IdemElem TwoCellModel.sep (env 1) ∧
       l.denote TwoCellModel.sep .empty env = r.denote TwoCellModel.sep .empty env ∧
       l.atoms.isPerm r.atoms = false) := by
  refine ⟨twoCellModel_sepAssoc, twoCellModel_sepComm, twoCellModel_rightUnit,
    twoCellModel_not_sepIdem, by decide, ?_, ?_, by decide, by decide⟩
  · intro h; cases h
  · intro h; cases h

/-- **Set-equality (deduplication) is NOT complete for arbitrary idempotent models:**
In `(Bool, Bool.or, false)` (which satisfies `SepIdem`), with `env 0 = true` and
`env 1 = false` (a unit-valued atom), `(atom 0 ∗ atom 1)` and `atom 0` have identical
denotations (`true`), yet their deduplicated atom sets `[0, 1]` and `[0]` fail `isPerm`. -/
theorem boolOr_setCheck_incomplete :
    SepAssoc Bool.or ∧
    SepComm Bool.or ∧
    RightUnit Bool.or false ∧
    SepIdem Bool.or ∧
    (let env : Nat → Bool := fun i => i == 0
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .atom 0
     l.denote Bool.or false env = r.denote Bool.or false env ∧
       l.atoms.eraseDups.isPerm r.atoms.eraseDups = false) := by
  refine ⟨boolOr_sepAssoc, boolOr_sepComm, boolOr_rightUnit, boolOr_sepIdem, ?_⟩
  decide

/-- Positive control for `denote_eq_and_isPerm_false_of_idemElem` (and canonical tightness
of `IdemElem`): in the free commutative monoid `Bag` at `Bag.single`, `¬ IdemElem Bag.sep
(Bag.single 0)` (and `¬ SepIdem Bag.sep`), and `dupAtomTree` and `singleAtomTree` have
distinct denotations. -/
theorem bag_dupAtomTree_denote_ne_singleAtomTree :
    SepAssoc Bag.sep ∧
    SepComm Bag.sep ∧
    RightUnit Bag.sep Bag.emp ∧
    ¬ SepIdem Bag.sep ∧
    ¬ IdemElem Bag.sep (Bag.single 0) ∧
    dupAtomTree.denote Bag.sep Bag.emp Bag.single ≠
      singleAtomTree.denote Bag.sep Bag.emp Bag.single :=
  ⟨bag_sepAssoc, bag_sepComm, bag_rightUnit, bag_not_sepIdem,
   bag_single_zero_not_idemElem, bag_neg_example⟩

end Toy.SepAC
