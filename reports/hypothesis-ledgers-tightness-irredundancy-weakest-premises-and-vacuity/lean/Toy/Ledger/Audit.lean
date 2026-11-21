import Toy.Ledger.Tables

/-!
# An executable ledger audit

Over a finite enumerated list `univ : List M` with `Bool`-valued hypotheses
`H : Fin m → M → Bool` and conclusion `C : M → Bool`, `auditLedger univ H C` returns a
`LedgerReport` with four kinds of verdict, each carrying its evidence:
* sufficiency: `holdsOnUniv` (no counterexample in `univ`) or `foundCounterexample x`;
* for each hypothesis: `foundTightWitness x` or `noTightWitnessOnUniv`;
* non-vacuity: `foundSatisfyingModel x` or `unsatisfiableOnUniv`;
* for each hypothesis: `noWeakeningOnUniv` or `foundWeakeningWitness x` (a model where the
  other hypotheses and the conclusion hold and the hypothesis fails).

The verdict names say what was observed on `univ`; the semantic notions over the whole model
type are `Sufficient`, `TightAt`, `NonVacuous`, and `UnweakenableAt` (read through `liftH`
and `liftPred`). `LedgerReport.summary` renders a report as data, keeping only the carried
model (`Shown.witness x`) or its absence (`Shown.noWitness`). Every carried model is genuine
over the whole model type whatever `univ` is (`auditLedger_sound`); if `univ` lists every
model, every verdict is correct (`auditLedger_complete`).
-/

namespace Toy.Ledger

universe u

/-- A data-only rendering of one verdict: `noWitness` for a verdict that carries no model,
`witness x` for a verdict carrying the model `x`. Which property `noWitness` reports depends
on the field of `LedgerSummary` it appears in (see `auditLedger_sound`). -/
inductive Shown (M : Type u) where
  | noWitness
  | witness (x : M)
  deriving DecidableEq, Repr

/-- A data-only summary of a report: one entry for sufficiency and non-vacuity, one list
entry per hypothesis (in index order) for tightness and weakening. -/
structure LedgerSummary (M : Type u) where
  sufficiency : Shown M
  tightness : List (Shown M)
  nonvacuity : Shown M
  weakening : List (Shown M)
  deriving DecidableEq, Repr

section Audit

variable {M : Type u} {m : Nat}

/-- A `Bool`-valued hypothesis family read as a `Prop`-valued one. -/
def liftH (H : Fin m → M → Bool) : Fin m → M → Prop := fun i x => H i x = true

/-- All hypotheses hold at `x`. -/
def allB (H : Fin m → M → Bool) (x : M) : Bool := decide (∀ j, H j x = true)

/-- All hypotheses other than `i` hold at `x`. -/
def othersB (H : Fin m → M → Bool) (i : Fin m) (x : M) : Bool :=
  decide (∀ j, j ≠ i → H j x = true)

/-- Sufficiency verdict. -/
inductive SuffVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) : Type u where
  | holdsOnUniv (h : ∀ x, x ∈ univ → allB H x = true → C x = true)
  | foundCounterexample (x : M) (hx : allB H x = true ∧ C x = false)

/-- Tightness verdict for hypothesis `i`. -/
inductive TightVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    Type u where
  | foundTightWitness (x : M) (hx : othersB H i x = true ∧ C x = false)
  | noTightWitnessOnUniv (h : ∀ x, x ∈ univ → othersB H i x = true → C x = true)

/-- Non-vacuity verdict. -/
inductive VacVerdict (univ : List M) (H : Fin m → M → Bool) : Type u where
  | foundSatisfyingModel (x : M) (hx : allB H x = true)
  | unsatisfiableOnUniv (h : ∀ x, x ∈ univ → allB H x = false)

/-- Weakening verdict for hypothesis `i`. -/
inductive WeakVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    Type u where
  | noWeakeningOnUniv (h : ∀ x, x ∈ univ → othersB H i x = true → C x = true → H i x = true)
  | foundWeakeningWitness (x : M) (hx : othersB H i x = true ∧ C x = true ∧ H i x = false)

/-- The full audit report. -/
structure LedgerReport (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) : Type u where
  sufficiency : SuffVerdict univ H C
  tightness : (i : Fin m) → TightVerdict univ H C i
  nonvacuity : VacVerdict univ H
  weakening : (i : Fin m) → WeakVerdict univ H C i

/-- Search `univ` for a counterexample to sufficiency. -/
def auditSufficiency (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    SuffVerdict univ H C :=
  match hf : univ.find? (fun x => allB H x && !C x) with
  | some x => .foundCounterexample x (by
      have := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this)
  | none => .holdsOnUniv (fun x hx ha => by
      have := find?_eq_none_apply hf hx
      simp [ha] at this
      exact this)

/-- Search `univ` for a tightness witness for hypothesis `i`. -/
def auditTightness (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    TightVerdict univ H C i :=
  match hf : univ.find? (fun x => othersB H i x && !C x) with
  | some x => .foundTightWitness x (by
      have := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this)
  | none => .noTightWitnessOnUniv (fun x hx ho => by
      have := find?_eq_none_apply hf hx
      simp [ho] at this
      exact this)

/-- Search `univ` for a non-vacuity witness. -/
def auditNonVacuity (univ : List M) (H : Fin m → M → Bool) : VacVerdict univ H :=
  match hf : univ.find? (fun x => allB H x) with
  | some x => .foundSatisfyingModel x (List.find?_some hf)
  | none => .unsatisfiableOnUniv (fun _ hx => find?_eq_none_apply hf hx)

/-- Search `univ` for a weakening witness for hypothesis `i`. -/
def auditWeakening (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    WeakVerdict univ H C i :=
  match hf : univ.find? (fun x => othersB H i x && C x && !H i x) with
  | some x => .foundWeakeningWitness x (by
      have := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact ⟨this.1.1, this.1.2, this.2⟩)
  | none => .noWeakeningOnUniv (fun x hx ho hc => by
      have := find?_eq_none_apply hf hx
      simp [ho, hc] at this
      exact this)

/-- The executable ledger audit. -/
def auditLedger (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    LedgerReport univ H C where
  sufficiency := auditSufficiency univ H C
  tightness := auditTightness univ H C
  nonvacuity := auditNonVacuity univ H
  weakening := auditWeakening univ H C

/-! ### Data-only rendering -/

/-- The rendering of a sufficiency verdict. -/
def SuffVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} :
    SuffVerdict univ H C → Shown M
  | .holdsOnUniv .. => .noWitness
  | .foundCounterexample x .. => .witness x

/-- The rendering of a tightness verdict. -/
def TightVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} {i : Fin m} :
    TightVerdict univ H C i → Shown M
  | .foundTightWitness x .. => .witness x
  | .noTightWitnessOnUniv .. => .noWitness

/-- The rendering of a non-vacuity verdict. -/
def VacVerdict.shown {univ : List M} {H : Fin m → M → Bool} : VacVerdict univ H → Shown M
  | .foundSatisfyingModel x .. => .witness x
  | .unsatisfiableOnUniv .. => .noWitness

/-- The rendering of a weakening verdict. -/
def WeakVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} {i : Fin m} :
    WeakVerdict univ H C i → Shown M
  | .noWeakeningOnUniv .. => .noWitness
  | .foundWeakeningWitness x .. => .witness x

/-- Summarize a report, listing per-hypothesis verdicts in index order. -/
def LedgerReport.summary {univ : List M} {H : Fin m → M → Bool} {C : M → Bool}
    (r : LedgerReport univ H C) : LedgerSummary M where
  sufficiency := r.sufficiency.shown
  tightness := (List.finRange m).map fun i => (r.tightness i).shown
  nonvacuity := r.nonvacuity.shown
  weakening := (List.finRange m).map fun i => (r.weakening i).shown

theorem getElem?_map_finRange {α : Type u} (f : Fin m → α) (i : Fin m) :
    ((List.finRange m).map f)[i.val]? = some (f i) := by
  rw [List.getElem?_map]
  have hlen : i.val < (List.finRange m).length := by simp [List.length_finRange]
  rw [List.getElem?_eq_getElem hlen, List.getElem_finRange]
  simp

theorem allB_eq_true_iff {H : Fin m → M → Bool} {x : M} :
    allB H x = true ↔ ∀ i, liftH H i x := by
  simp [allB, liftH]

theorem othersB_eq_true_iff {H : Fin m → M → Bool} {i : Fin m} {x : M} :
    othersB H i x = true ↔ ∀ j, j ≠ i → liftH H j x := by
  simp [othersB, liftH]

/-! ### What each rendered verdict guarantees -/

section VerdictLemmas

variable {univ : List M} {H : Fin m → M → Bool} {C : M → Bool}

theorem SuffVerdict.shown_witness {v : SuffVerdict univ H C} {x : M}
    (h : v.shown = .witness x) : (∀ i, liftH H i x) ∧ ¬ liftPred C x := by
  cases v with
  | holdsOnUniv _ => simp [SuffVerdict.shown] at h
  | foundCounterexample w hw =>
    cases h
    exact ⟨allB_eq_true_iff.mp hw.1, by simp [liftPred, hw.2]⟩

theorem SuffVerdict.shown_noWitness {v : SuffVerdict univ H C} (h : v.shown = .noWitness) :
    ∀ x, x ∈ univ → (∀ i, liftH H i x) → liftPred C x := by
  cases v with
  | holdsOnUniv hv => exact fun x hx ha => hv x hx (allB_eq_true_iff.mpr ha)
  | foundCounterexample _ _ => simp [SuffVerdict.shown] at h

theorem SuffVerdict.shown_noWitness_iff (hu : ∀ x, x ∈ univ) (v : SuffVerdict univ H C) :
    v.shown = .noWitness ↔ Sufficient (liftH H) (liftPred C) := by
  cases v with
  | holdsOnUniv hv =>
    exact ⟨fun _ x ha => hv x (hu x) (allB_eq_true_iff.mpr ha), fun _ => rfl⟩
  | foundCounterexample w hw =>
    refine ⟨fun h => by simp [SuffVerdict.shown] at h, fun hs => ?_⟩
    have := hs w (allB_eq_true_iff.mp hw.1)
    simp [liftPred, hw.2] at this

theorem TightVerdict.shown_witness {i : Fin m} {v : TightVerdict univ H C i} {x : M}
    (h : v.shown = .witness x) : (∀ j, j ≠ i → liftH H j x) ∧ ¬ liftPred C x := by
  cases v with
  | foundTightWitness w hw =>
    cases h
    exact ⟨othersB_eq_true_iff.mp hw.1, by simp [liftPred, hw.2]⟩
  | noTightWitnessOnUniv _ => simp [TightVerdict.shown] at h

theorem TightVerdict.shown_noWitness {i : Fin m} {v : TightVerdict univ H C i}
    (h : v.shown = .noWitness) :
    ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x := by
  cases v with
  | foundTightWitness _ _ => simp [TightVerdict.shown] at h
  | noTightWitnessOnUniv hv => exact fun x hx ho => hv x hx (othersB_eq_true_iff.mpr ho)

theorem TightVerdict.shown_noWitness_iff (hu : ∀ x, x ∈ univ) {i : Fin m}
    (v : TightVerdict univ H C i) :
    v.shown = .noWitness ↔ ¬ TightAt (liftH H) (liftPred C) i := by
  cases v with
  | foundTightWitness w hw =>
    exact ⟨fun h => by simp [TightVerdict.shown] at h,
      fun hnt => absurd ⟨w, othersB_eq_true_iff.mp hw.1, by simp [liftPred, hw.2]⟩ hnt⟩
  | noTightWitnessOnUniv hv =>
    exact ⟨fun _ ⟨x, ho, hnc⟩ => hnc (hv x (hu x) (othersB_eq_true_iff.mpr ho)), fun _ => rfl⟩

theorem VacVerdict.shown_witness {v : VacVerdict univ H} {x : M}
    (h : v.shown = .witness x) : ∀ i, liftH H i x := by
  cases v with
  | foundSatisfyingModel w hw =>
    cases h
    exact allB_eq_true_iff.mp hw
  | unsatisfiableOnUniv _ => simp [VacVerdict.shown] at h

theorem VacVerdict.shown_noWitness {v : VacVerdict univ H} (h : v.shown = .noWitness) :
    ∀ x, x ∈ univ → ¬ ∀ i, liftH H i x := by
  cases v with
  | foundSatisfyingModel _ _ => simp [VacVerdict.shown] at h
  | unsatisfiableOnUniv hv =>
    intro x hx ha
    have := hv x hx
    rw [allB_eq_true_iff.mpr ha] at this
    exact Bool.noConfusion this

theorem VacVerdict.shown_noWitness_iff (hu : ∀ x, x ∈ univ) (v : VacVerdict univ H) :
    v.shown = .noWitness ↔ ¬ NonVacuous (liftH H) := by
  cases v with
  | foundSatisfyingModel w hw =>
    exact ⟨fun h => by simp [VacVerdict.shown] at h, fun hnv => absurd ⟨w, allB_eq_true_iff.mp hw⟩ hnv⟩
  | unsatisfiableOnUniv hv =>
    refine ⟨fun _ ⟨x, ha⟩ => ?_, fun _ => rfl⟩
    have := hv x (hu x)
    rw [allB_eq_true_iff.mpr ha] at this
    exact Bool.noConfusion this

theorem WeakVerdict.shown_witness {i : Fin m} {v : WeakVerdict univ H C i} {x : M}
    (h : v.shown = .witness x) :
    (∀ j, j ≠ i → liftH H j x) ∧ liftPred C x ∧ ¬ liftH H i x := by
  cases v with
  | noWeakeningOnUniv _ => simp [WeakVerdict.shown] at h
  | foundWeakeningWitness w hw =>
    cases h
    exact ⟨othersB_eq_true_iff.mp hw.1, hw.2.1, by simp [liftH, hw.2.2]⟩

theorem WeakVerdict.shown_noWitness {i : Fin m} {v : WeakVerdict univ H C i}
    (h : v.shown = .noWitness) :
    ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x → liftH H i x := by
  cases v with
  | noWeakeningOnUniv hv => exact fun x hx ho hc => hv x hx (othersB_eq_true_iff.mpr ho) hc
  | foundWeakeningWitness _ _ => simp [WeakVerdict.shown] at h

theorem WeakVerdict.shown_noWitness_iff (hu : ∀ x, x ∈ univ) {i : Fin m}
    (v : WeakVerdict univ H C i) :
    v.shown = .noWitness ↔ UnweakenableAt (liftH H) (liftPred C) i := by
  cases v with
  | noWeakeningOnUniv hv =>
    exact ⟨fun _ x ho hc => hv x (hu x) (othersB_eq_true_iff.mpr ho) hc, fun _ => rfl⟩
  | foundWeakeningWitness w hw =>
    refine ⟨fun h => by simp [WeakVerdict.shown] at h, fun huw => ?_⟩
    have := huw w (othersB_eq_true_iff.mp hw.1) hw.2.1
    simp [liftH, hw.2.2] at this

end VerdictLemmas

/-! ### Soundness and completeness of the audit -/

/-- Soundness of `auditLedger`, for every list `univ`, stated on the summary data. Every
model the summary shows is genuine over the whole model type: a sufficiency entry
`witness x` is a counterexample to the theorem; a tightness entry `witness x` at index `i`
is a tightness witness for `i`; a non-vacuity entry `witness x` satisfies all hypotheses; a
weakening entry `witness x` at `i` satisfies the other hypotheses and the conclusion and
violates hypothesis `i`. Every `noWitness` entry asserts the corresponding universal
property restricted to the members of `univ`. -/
theorem auditLedger_sound (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    (∀ x, (auditLedger univ H C).summary.sufficiency = .witness x →
      (∀ i, liftH H i x) ∧ ¬ liftPred C x) ∧
    ((auditLedger univ H C).summary.sufficiency = .noWitness →
      ∀ x, x ∈ univ → (∀ i, liftH H i x) → liftPred C x) ∧
    (∀ (i : Fin m) x, (auditLedger univ H C).summary.tightness[i.val]? = some (.witness x) →
      (∀ j, j ≠ i → liftH H j x) ∧ ¬ liftPred C x) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness →
      ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x) ∧
    (∀ x, (auditLedger univ H C).summary.nonvacuity = .witness x → ∀ i, liftH H i x) ∧
    ((auditLedger univ H C).summary.nonvacuity = .noWitness →
      ∀ x, x ∈ univ → ¬ ∀ i, liftH H i x) ∧
    (∀ (i : Fin m) x, (auditLedger univ H C).summary.weakening[i.val]? = some (.witness x) →
      (∀ j, j ≠ i → liftH H j x) ∧ liftPred C x ∧ ¬ liftH H i x) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness →
      ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x → liftH H i x) := by
  simp only [LedgerReport.summary, getElem?_map_finRange, Option.some.injEq]
  exact ⟨fun _ h => SuffVerdict.shown_witness h, fun h => SuffVerdict.shown_noWitness h,
    fun _ _ h => TightVerdict.shown_witness h, fun _ h => TightVerdict.shown_noWitness h,
    fun _ h => VacVerdict.shown_witness h, fun h => VacVerdict.shown_noWitness h,
    fun _ _ h => WeakVerdict.shown_witness h, fun _ h => WeakVerdict.shown_noWitness h⟩

/-- Completeness of `auditLedger`: if `univ` lists every model, every entry of the summary
is correct for the whole model type: the sufficiency entry is `noWitness` iff the theorem
holds, the tightness entry at `i` is `noWitness` iff `i` is not tight, the non-vacuity
entry is `noWitness` iff the hypotheses are unsatisfiable, and the weakening entry at `i` is
`noWitness` iff `i` is unweakenable. (With `auditLedger_sound`, a `witness x` entry carries
a model refuting the corresponding universal property.) -/
theorem auditLedger_complete (univ : List M) (hu : ∀ x, x ∈ univ) (H : Fin m → M → Bool)
    (C : M → Bool) :
    ((auditLedger univ H C).summary.sufficiency = .noWitness ↔
      Sufficient (liftH H) (liftPred C)) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness ↔
      ¬ TightAt (liftH H) (liftPred C) i) ∧
    ((auditLedger univ H C).summary.nonvacuity = .noWitness ↔ ¬ NonVacuous (liftH H)) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness ↔
      UnweakenableAt (liftH H) (liftPred C) i) := by
  simp only [LedgerReport.summary, getElem?_map_finRange, Option.some.injEq]
  exact ⟨SuffVerdict.shown_noWitness_iff hu _, fun _ => TightVerdict.shown_noWitness_iff hu _,
    VacVerdict.shown_noWitness_iff hu _, fun _ => WeakVerdict.shown_noWitness_iff hu _⟩

end Audit

/-! ## Runs on the running examples -/

/-- `x ≥ 1, x ≤ 1 ⊢ x = 1` on `Fin 4`. -/
def pinHB : Fin 2 → Fin 4 → Bool :=
  fun i x => if i = 0 then decide (1 ≤ x.val) else decide (x.val ≤ 1)

/-- Conclusion `x = 1` on `Fin 4`. -/
def pinCB : Fin 4 → Bool := fun x => decide (x.val = 1)

/-- `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` on `Fin 3 × Fin 3` (sums computed in `Nat`). -/
def sumHB : Fin 2 → Fin 3 × Fin 3 → Bool :=
  fun i p => if i = 0 then decide (p.1.val ≤ 1) else decide (p.2.val ≤ 1)

/-- Conclusion `x + y ≤ 2`. -/
def sumCB : Fin 3 × Fin 3 → Bool := fun p => decide (p.1.val + p.2.val ≤ 2)

/-- All of `Fin 3 × Fin 3`, first coordinate major. -/
def grid3 : List (Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).map fun b => (a, b)

theorem mem_grid3 (p : Fin 3 × Fin 3) : p ∈ grid3 := by
  simp only [grid3, List.mem_flatMap, List.mem_map]
  exact ⟨p.1, List.mem_finRange _, p.2, List.mem_finRange _, rfl⟩

/-- Duplicated hypotheses `x = 1, x = 1 ⊢ x = 1` on `Fin 4`. -/
def dupHB : Fin 2 → Fin 4 → Bool := fun _ x => decide (x.val = 1)

/-- `x = 1, x = 2 ⊢ False` on `Fin 3`. -/
def vacHB : Fin 2 → Fin 3 → Bool :=
  fun i x => if i = 0 then decide (x.val = 1) else decide (x.val = 2)

/-- `P ∨ C, ¬ P ⊢ C` over `Bool × Bool` with `P = first bit`, `C = second bit`. -/
def schemaHB : Fin 2 → Bool × Bool → Bool := fun i p => if i = 0 then p.1 || p.2 else !p.1

/-- All of `Bool × Bool`. -/
def bools2 : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_bools2 (p : Bool × Bool) : p ∈ bools2 := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> simp [bools2]

/-- `auditLedger` on `x ≥ 1, x ≤ 1 ⊢ x = 1` over `List.finRange 4`: sufficiency entry
`noWitness`; tightness entries `witness 0`, `witness 2`; non-vacuity entry `witness 1`;
weakening entries `noWitness`, `noWitness`. -/
theorem auditLedger_pin :
    (auditLedger (List.finRange 4) pinHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.witness 0, .witness 2],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } := by
  decide

/-- `auditLedger` on `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` over `grid3`: sufficiency entry `noWitness`;
tightness entries `witness (2, 1)`, `witness (1, 2)`; non-vacuity entry `witness (0, 0)`;
weakening entries `witness (2, 0)`, `witness (0, 2)`. -/
theorem auditLedger_sum :
    (auditLedger grid3 sumHB sumCB).summary =
      { sufficiency := .noWitness, tightness := [.witness (2, 1), .witness (1, 2)],
        nonvacuity := .witness (0, 0), weakening := [.witness (2, 0), .witness (0, 2)] } := by
  decide

/-- `auditLedger` on `x = 1, x = 1 ⊢ x = 1` over `List.finRange 4`: sufficiency entry
`noWitness`; tightness entries `noWitness`, `noWitness`; non-vacuity entry `witness 1`;
weakening entries `noWitness`, `noWitness`. -/
theorem auditLedger_dup :
    (auditLedger (List.finRange 4) dupHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.noWitness, .noWitness],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } := by
  decide

/-- `auditLedger` on `x = 1, x = 2 ⊢ False` over `List.finRange 3`: sufficiency entry
`noWitness`; tightness entries `witness 2`, `witness 1`; non-vacuity entry `noWitness`;
weakening entries `noWitness`, `noWitness`. -/
theorem auditLedger_vac :
    (auditLedger (List.finRange 3) vacHB (fun _ => false)).summary =
      { sufficiency := .noWitness, tightness := [.witness 2, .witness 1],
        nonvacuity := .noWitness, weakening := [.noWitness, .noWitness] } := by
  decide

/-- `auditLedger` on the schema `P ∨ C, ¬ P ⊢ C` over `bools2`: sufficiency entry
`noWitness`; tightness entries `witness (false, false)`, `witness (true, false)`;
non-vacuity entry `witness (false, true)`; weakening entries `noWitness`,
`witness (true, true)`. -/
theorem auditLedger_schema :
    (auditLedger bools2 schemaHB (fun p => p.2)).summary =
      { sufficiency := .noWitness, tightness := [.witness (false, false), .witness (true, false)],
        nonvacuity := .witness (false, true),
        weakening := [.noWitness, .witness (true, true)] } := by
  decide

/-- The summaries of `auditLedger` on the five running examples, collected (each conjunct
is one of `auditLedger_pin`, `auditLedger_sum`, `auditLedger_dup`, `auditLedger_vac`,
`auditLedger_schema`). The lists used (`List.finRange 4`, `grid3`, `List.finRange 3`,
`bools2`) list every model (`List.mem_finRange`, `mem_grid3`, `mem_bools2`), so
`auditLedger_complete` applies to each run. -/
theorem auditLedger_running_examples :
    (auditLedger (List.finRange 4) pinHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.witness 0, .witness 2],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger grid3 sumHB sumCB).summary =
      { sufficiency := .noWitness, tightness := [.witness (2, 1), .witness (1, 2)],
        nonvacuity := .witness (0, 0), weakening := [.witness (2, 0), .witness (0, 2)] } ∧
    (auditLedger (List.finRange 4) dupHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.noWitness, .noWitness],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger (List.finRange 3) vacHB (fun _ => false)).summary =
      { sufficiency := .noWitness, tightness := [.witness 2, .witness 1],
        nonvacuity := .noWitness, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger bools2 schemaHB (fun p => p.2)).summary =
      { sufficiency := .noWitness, tightness := [.witness (false, false), .witness (true, false)],
        nonvacuity := .witness (false, true),
        weakening := [.noWitness, .witness (true, true)] } :=
  ⟨auditLedger_pin, auditLedger_sum, auditLedger_dup, auditLedger_vac, auditLedger_schema⟩

/-- When the audited theorem is false, the tightness entries reuse the counterexample: for
the single trivial hypothesis `true` and conclusion `b = true` over `[false, true]`, the
sufficiency entry is `witness false` and the tightness entry of the trivial hypothesis is
the same `witness false` (a model satisfying that hypothesis). -/
theorem auditLedger_false_theorem_tight_entry_reuses_counterexample :
    (auditLedger [false, true] (fun (_ : Fin 1) (_ : Bool) => true) (fun b => b)).summary =
      { sufficiency := .witness false, tightness := [.witness false],
        nonvacuity := .witness false, weakening := [.noWitness] } := by
  decide

/-- Counterexample for `hu` in `auditLedger_complete`: over the empty list the sufficiency
entry for `x ≥ 1, x ≤ 1 ⊢ False` on `Fin 4` is `noWitness`, although the theorem fails
(take `x = 1`), so the conclusion of `auditLedger_complete` fails. -/
theorem auditLedger_complete_ce_incomplete_univ :
    ¬ (((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.sufficiency =
          .noWitness ↔ Sufficient (liftH pinHB) (liftPred (fun _ : Fin 4 => false))) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.tightness[i.val]? =
            some .noWitness ↔ ¬ TightAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i) ∧
        ((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.nonvacuity =
          .noWitness ↔ ¬ NonVacuous (liftH pinHB)) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.weakening[i.val]? =
            some .noWitness ↔ UnweakenableAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i)) := by
  rintro ⟨h1, -⟩
  have hs := h1.mp rfl
  have := hs 1 (fun i => by unfold liftH pinHB; split <;> rfl)
  exact Bool.noConfusion this

/-- Non-vacuity for `auditLedger_complete`: `List.finRange 4` lists every element of
`Fin 4`. -/
theorem auditLedger_complete_nonvacuity : ∀ x : Fin 4, x ∈ List.finRange 4 :=
  List.mem_finRange

end Toy.Ledger
