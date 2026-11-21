import Toy.Ledger.Classes

/-!
# Vacuous table cells

A soundness table assigns to each row `r` and column `k` a class of models
`cell r k : M → Prop`; a ✓ at `(r, k)` asserts that every model in the cell has the
property `Q`. A ✓ holds on every empty cell, so an all-✓ table is compatible with every
cell being empty. An *informative* ✓ is a ✓ together with a model in the cell. Over a
finite enumerated list `univ`, the procedure `classify` sorts each cell of a `Bool`-valued
table into one of three verdicts: `witnessedOnUniv` (a model of the cell with the property
was found and no counterexample occurs in `univ`), `emptyOnUniv` (no model of the cell
occurs in `univ`), or `foundCounterexample`. The verdict names say what was observed on
`univ`; the semantic notions over the whole model type are `Check` and `InformativeCheck`.
-/

namespace Toy.Ledger

universe u v w

section Tables

variable {M : Type u} {R : Type v} {K : Type w}

/-- A ✓ at row `r`, column `k`: every model in the cell has property `Q`. Captures a
"sound" or ✓ entry of a soundness table. -/
def Check (cell : R → K → M → Prop) (Q : M → Prop) (r : R) (k : K) : Prop :=
  ∀ x, cell r k x → Q x

/-- An informative ✓: a ✓ together with a model in the cell (a non-vacuity witness for the
entry). -/
def InformativeCheck (cell : R → K → M → Prop) (Q : M → Prop) (r : R) (k : K) : Prop :=
  Check cell Q r k ∧ ∃ x, cell r k x

/-- A ✓ holds on every empty cell. -/
theorem check_of_cell_empty {cell : R → K → M → Prop} {Q : M → Prop} {r : R} {k : K}
    (h : ∀ x, ¬ cell r k x) : Check cell Q r k :=
  fun x hx => absurd hx (h x)

end Tables

/-! ## Examples for `Check` and `InformativeCheck` -/

/-- A 2×2 table over `Nat`: cell `(h1, h1)` is `{2}`, cell `(h1, h2)` is `{3}`, and the
cells of row `h2` are empty. -/
def demoTable : Two → Two → Nat → Prop
  | .h1, .h1 => fun x => x = 2
  | .h1, .h2 => fun x => x = 3
  | .h2, _ => fun _ => False

/-- The property "even". -/
def evenQ : Nat → Prop := fun x => x % 2 = 0

theorem informativeCheck_demo_h1_h1 : InformativeCheck demoTable evenQ .h1 .h1 :=
  ⟨fun x hx => by simp [demoTable] at hx; subst hx; rfl, ⟨2, rfl⟩⟩

theorem not_check_demo_h1_h2 : ¬ Check demoTable evenQ .h1 .h2 := by
  intro h
  have := h 3 rfl
  simp [evenQ] at this

/-- The empty cell `(h2, h1)` carries a ✓ that is not informative. -/
theorem check_not_informative_demo_h2_h1 :
    Check demoTable evenQ .h2 .h1 ∧ ¬ InformativeCheck demoTable evenQ .h2 .h1 :=
  ⟨fun _ hx => hx.elim, fun ⟨_, _, hx⟩ => hx⟩

/-- Counterexample for `h` in `check_of_cell_empty`: the nonempty cell `(h1, h2)` of
`demoTable` has no ✓ for "even". -/
theorem check_of_cell_empty_ce_nonempty : ¬ Check demoTable evenQ .h1 .h2 :=
  not_check_demo_h1_h2

/-- Non-vacuity for `check_of_cell_empty`. -/
theorem check_of_cell_empty_nonvacuity : ∀ x, ¬ demoTable .h2 .h1 x :=
  fun _ hx => hx

/-- The table with every cell empty. -/
def emptyTable : Bool → Bool → Nat → Prop := fun _ _ _ => False

/-- An all-✓ table is compatible with every cell being empty: every cell of `emptyTable`
carries a ✓ even for the unsatisfiable property `False`, and no ✓ is informative. -/
theorem all_checks_with_every_cell_empty :
    (∀ r k, Check emptyTable falseC r k) ∧ (∀ r k, ¬ InformativeCheck emptyTable falseC r k) ∧
      ¬ ∃ x : Nat, falseC x :=
  ⟨fun _ _ _ hx => hx.elim, fun _ _ ⟨_, _, hx⟩ => hx, fun ⟨_, hx⟩ => hx⟩

/-! ## The finite classifier -/

/-- A `Bool`-valued predicate read as a `Prop`-valued one. -/
def liftPred {M : Type u} (q : M → Bool) : M → Prop := fun x => q x = true

/-- A `Bool`-valued table read as a `Prop`-valued one. -/
def liftTable {M : Type u} {R : Type v} {K : Type w} (cell : R → K → M → Bool) :
    R → K → M → Prop :=
  fun r k x => cell r k x = true

theorem find?_eq_none_apply {α : Type u} {p : α → Bool} {l : List α}
    (h : l.find? p = none) {x : α} (hx : x ∈ l) : p x = false := by
  have := List.find?_eq_none.mp h x hx
  simpa using this

/-- The verdict for one cell over the enumerated list `univ`. Each constructor carries its
evidence: `witnessedOnUniv` carries a model in the cell with the property, plus the ✓
restricted to `univ`; `emptyOnUniv` carries emptiness of the cell on `univ`;
`foundCounterexample` carries a model in the cell without the property. -/
inductive CellVerdict {M : Type u} (univ : List M) (cell q : M → Bool) : Type u where
  | witnessedOnUniv (w : M) (hw : cell w = true ∧ q w = true)
      (hall : ∀ x, x ∈ univ → cell x = true → q x = true)
  | emptyOnUniv (hempty : ∀ x, x ∈ univ → cell x = false)
  | foundCounterexample (x : M) (hx : cell x = true ∧ q x = false)

/-- The three verdict kinds of `classify`, as data. -/
inductive CellStatus where
  | witnessedOnUniv
  | emptyOnUniv
  | foundCounterexample
  deriving DecidableEq, Repr

section Classifier

variable {M : Type u} {R : Type v} {K : Type w}

/-- The kind of a verdict. -/
def CellVerdict.status {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → CellStatus
  | .witnessedOnUniv .. => .witnessedOnUniv
  | .emptyOnUniv .. => .emptyOnUniv
  | .foundCounterexample .. => .foundCounterexample

/-- The model carried by a verdict, if any. -/
def CellVerdict.witness? {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → Option M
  | .witnessedOnUniv w .. => some w
  | .emptyOnUniv .. => none
  | .foundCounterexample x .. => some x

/-- Classify one cell: first search `univ` for a counterexample, then for a witness. -/
def classifyCell (univ : List M) (cell q : M → Bool) : CellVerdict univ cell q :=
  match hf : univ.find? (fun x => cell x && !q x) with
  | some x => .foundCounterexample x (by
      have := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this)
  | none =>
    match hw : univ.find? cell with
    | some w =>
      .witnessedOnUniv w ⟨List.find?_some hw, by
          have := find?_eq_none_apply hf (List.mem_of_find?_eq_some hw)
          simp [List.find?_some hw] at this
          exact this⟩
        (fun x hx hc => by
          have := find?_eq_none_apply hf hx
          simp [hc] at this
          exact this)
    | none => .emptyOnUniv (fun x hx => find?_eq_none_apply hw hx)

/-- Classify cell `(r, k)` of a `Bool`-valued table. -/
def classify (univ : List M) (cell : R → K → M → Bool) (q : M → Bool) (r : R) (k : K) :
    CellVerdict univ (cell r k) q :=
  classifyCell univ (cell r k) q

/-- What a verdict value guarantees, read through `liftPred`. -/
def CellVerdict.Sound {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → Prop
  | .witnessedOnUniv w .. =>
      liftPred cell w ∧ liftPred q w ∧ ∀ x, x ∈ univ → liftPred cell x → liftPred q x
  | .emptyOnUniv .. => ∀ x, x ∈ univ → ¬ liftPred cell x
  | .foundCounterexample x .. => liftPred cell x ∧ ¬ liftPred q x

/-- Every value of `CellVerdict` satisfies `CellVerdict.Sound`, by construction (the
constructors carry their evidence). -/
theorem CellVerdict.sound {univ : List M} {cell q : M → Bool} (v : CellVerdict univ cell q) :
    v.Sound := by
  cases v with
  | witnessedOnUniv w hw hall => exact ⟨hw.1, hw.2, hall⟩
  | emptyOnUniv hempty =>
    intro x hx hc
    exact absurd hc (by simp [liftPred, hempty x hx])
  | foundCounterexample x hx => exact ⟨hx.1, by simp [liftPred, hx.2]⟩

/-- Soundness of `classify`, for every list `univ`, stated on the observable data
`status` and `witness?`: a `witnessedOnUniv` verdict carries a model in the cell with the
property and the property holds on the cell's models in `univ`; an `emptyOnUniv` verdict
carries no model and the cell has no model in `univ`; a `foundCounterexample` verdict
carries a model in the cell without the property (so it refutes the ✓ over the whole model
type). -/
theorem classify_sound (univ : List M) (cell : R → K → M → Bool) (q : M → Bool)
    (r : R) (k : K) :
    ((classify univ cell q r k).status = .witnessedOnUniv →
      ∃ w, (classify univ cell q r k).witness? = some w ∧ liftTable cell r k w ∧
        liftPred q w ∧ ∀ x, x ∈ univ → liftTable cell r k x → liftPred q x) ∧
    ((classify univ cell q r k).status = .emptyOnUniv →
      (classify univ cell q r k).witness? = none ∧ ∀ x, x ∈ univ → ¬ liftTable cell r k x) ∧
    ((classify univ cell q r k).status = .foundCounterexample →
      ∃ x, (classify univ cell q r k).witness? = some x ∧ liftTable cell r k x ∧
        ¬ liftPred q x) := by
  generalize classify univ cell q r k = v
  cases v with
  | witnessedOnUniv w hw hall =>
    exact ⟨fun _ => ⟨w, rfl, hw.1, hw.2, hall⟩,
      fun h => CellStatus.noConfusion h, fun h => CellStatus.noConfusion h⟩
  | emptyOnUniv hempty =>
    exact ⟨fun h => CellStatus.noConfusion h,
      fun _ => ⟨rfl, fun x hx hc => absurd hc (by simp [liftTable, hempty x hx])⟩,
      fun h => CellStatus.noConfusion h⟩
  | foundCounterexample x hx =>
    exact ⟨fun h => CellStatus.noConfusion h, fun h => CellStatus.noConfusion h,
      fun _ => ⟨x, rfl, hx.1, by simp [liftPred, hx.2]⟩⟩

/-- Completeness of `classify`: if `univ` lists every model, the verdict kind for cell
`(r, k)` is exactly right: `witnessedOnUniv` iff the cell carries an informative ✓,
`emptyOnUniv` iff it carries a ✓ and is empty, `foundCounterexample` iff it carries no ✓. -/
theorem classify_complete (univ : List M) (hu : ∀ x, x ∈ univ) (cell : R → K → M → Bool)
    (q : M → Bool) (r : R) (k : K) :
    ((classify univ cell q r k).status = .witnessedOnUniv ↔
        InformativeCheck (liftTable cell) (liftPred q) r k) ∧
    ((classify univ cell q r k).status = .emptyOnUniv ↔
        Check (liftTable cell) (liftPred q) r k ∧ ∀ x, ¬ liftTable cell r k x) ∧
    ((classify univ cell q r k).status = .foundCounterexample ↔
        ¬ Check (liftTable cell) (liftPred q) r k) := by
  have hs := (classify univ cell q r k).sound
  generalize classify univ cell q r k = v at hs
  cases v with
  | witnessedOnUniv w hw hall =>
    dsimp [CellVerdict.status, CellVerdict.Sound] at hs ⊢
    have hchk : Check (liftTable cell) (liftPred q) r k :=
      fun x hc => hs.2.2 x (hu x) hc
    have hinf : InformativeCheck (liftTable cell) (liftPred q) r k := ⟨hchk, w, hs.1⟩
    exact ⟨⟨fun _ => hinf, fun _ => rfl⟩,
      ⟨fun h => CellStatus.noConfusion h, fun ⟨_, he⟩ => absurd hs.1 (he w)⟩,
      ⟨fun h => CellStatus.noConfusion h, fun hnc => absurd hchk hnc⟩⟩
  | emptyOnUniv hempty =>
    dsimp [CellVerdict.status, CellVerdict.Sound] at hs ⊢
    have he : ∀ x, ¬ liftTable cell r k x := fun x => hs x (hu x)
    have hchk : Check (liftTable cell) (liftPred q) r k := check_of_cell_empty he
    exact ⟨⟨fun h => CellStatus.noConfusion h, fun ⟨_, w, hw⟩ => absurd hw (he w)⟩,
      ⟨fun _ => ⟨hchk, he⟩, fun _ => rfl⟩,
      ⟨fun h => CellStatus.noConfusion h, fun hnc => absurd hchk hnc⟩⟩
  | foundCounterexample x hx =>
    dsimp [CellVerdict.status, CellVerdict.Sound] at hs ⊢
    have hnc : ¬ Check (liftTable cell) (liftPred q) r k := fun hchk => hs.2 (hchk x hs.1)
    exact ⟨⟨fun h => CellStatus.noConfusion h, fun ⟨hchk, _⟩ => absurd hchk hnc⟩,
      ⟨fun h => CellStatus.noConfusion h, fun ⟨hchk, _⟩ => absurd hchk hnc⟩,
      ⟨fun _ => hnc, fun _ => rfl⟩⟩

end Classifier

/-! ## The classifier on a small table -/

/-- `demoTable` restricted to `Fin 4`, as a `Bool` table. -/
def demoTableB : Two → Two → Fin 4 → Bool
  | .h1, .h1 => fun x => decide (x.val = 2)
  | .h1, .h2 => fun x => decide (x.val = 3)
  | .h2, _ => fun _ => false

/-- "Even" on `Fin 4`. -/
def evenB : Fin 4 → Bool := fun x => decide (x.val % 2 = 0)

/-- `classify` on the four cells of `demoTableB` over `List.finRange 4`: `witnessedOnUniv`
with witness `2`, `foundCounterexample` with model `3`, and `emptyOnUniv` twice. -/
theorem classify_demo :
    ((classify (List.finRange 4) demoTableB evenB .h1 .h1).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h1).witness?) =
        (.witnessedOnUniv, some 2) ∧
    ((classify (List.finRange 4) demoTableB evenB .h1 .h2).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h2).witness?) =
        (.foundCounterexample, some 3) ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h1).status = .emptyOnUniv ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h2).status = .emptyOnUniv := by
  decide

/-- Counterexample for `hu` in `classify_complete`: over the empty list the cell
`(h1, h2)` of `demoTableB` (the cell `{3}`, which has no ✓ for "even") is classified
`emptyOnUniv`, so the conclusion of `classify_complete` fails. -/
theorem classify_complete_ce_incomplete_univ :
    ¬ (((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status = .witnessedOnUniv ↔
          InformativeCheck (liftTable demoTableB) (liftPred evenB) .h1 .h2) ∧
        ((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status = .emptyOnUniv ↔
          Check (liftTable demoTableB) (liftPred evenB) .h1 .h2 ∧
            ∀ x, ¬ liftTable demoTableB .h1 .h2 x) ∧
        ((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status =
            .foundCounterexample ↔
          ¬ Check (liftTable demoTableB) (liftPred evenB) .h1 .h2)) := by
  rintro ⟨_, h2, _⟩
  have := (h2.mp rfl).1 3 rfl
  exact Bool.noConfusion this

/-- Non-vacuity for `classify_complete`: `List.finRange 4` lists every element of `Fin 4`. -/
theorem classify_complete_nonvacuity : ∀ x : Fin 4, x ∈ List.finRange 4 :=
  List.mem_finRange

/-- The one-cell table `{2, 3}` on `Fin 4`. -/
def twoThreeTableB : Unit → Unit → Fin 4 → Bool := fun _ _ x => decide (x.val = 2 ∨ x.val = 3)

/-- On an incomplete list, `witnessedOnUniv` does not imply a ✓: over `univ = [2]` the cell
`{2, 3}` is classified `witnessedOnUniv` for "even", yet the cell has no ✓ (the model `3`
is outside `univ`). -/
theorem classify_witnessedOnUniv_without_check :
    (classify [2] twoThreeTableB evenB () ()).status = .witnessedOnUniv ∧
      ¬ Check (liftTable twoThreeTableB) (liftPred evenB) () () := by
  refine ⟨by decide, fun h => ?_⟩
  have := h 3 (show twoThreeTableB () () 3 = true by decide)
  exact Bool.noConfusion this

end Toy.Ledger
