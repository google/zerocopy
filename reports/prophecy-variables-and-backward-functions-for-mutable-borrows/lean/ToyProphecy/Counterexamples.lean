import ToyProphecy.Results

/-!
# Tightness counterexamples for the discipline hypotheses

For each main statement and each of its hypotheses, a concrete program (and
initial store) that satisfies every *other* hypothesis of that statement while
the statement's conclusion fails. One program per discipline property serves
all three main statements.

Observed values (initial store all zeros; `ref`, `back`, `proph` = reference
semantics, backward-function translation, prophecy translation):

| program | violates | ref | back | proph |
| :--- | :--- | :--- | :--- | :--- |
| `cxLent`   | `NoLentAccess`   | `x1 = 5` | `x1 = 0` | `x1 = 9` (only) |
| `cxFrozen` | `NoFrozenAccess` | `x1 = 7` | `x1 = 0` | `x1 = 9` (only) |
| `cxAfterEnd` | `NoUseAfterEnd` | `x0 = 4` | `x0 = 0` | `x0 = 0` (only) |
| `cxAfterEndUnsat` | `NoUseAfterEnd` | `x0 = 1` | `x0 = 1` | no admitted store |
| `cxRebind` | `FreshBindings`  | `x0 = 5` | `x0 = 0` | any `x0` |
| `cxUnended` | `AllEndedAtExit` | `x0 = 5` | `x0 = 0` | any `x0` |
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-! ## Helpers -/

/-- If the prophecy translation admits `σ'` but `o` disagrees with `σ'` at some
local, the admitted set is not `{τ | o = some τ}`. -/
theorem not_prophOutcome_iff_of_admitted {P : Prog} {σ : Store} {o : Option Store}
    (σ' : Store) (h1 : ProphOutcome P σ σ') (x : Var) (h2 : o.map (· x) ≠ some (σ' x)) :
    ¬ ∀ τ, ProphOutcome P σ τ ↔ o = some τ := by
  intro h
  apply h2
  rw [(h σ').1 h1]
  rfl

/-- If `o = some σ'` but the prophecy translation does not admit `σ'`, the
admitted set is not `{τ | o = some τ}`. -/
theorem not_prophOutcome_iff_of_not_admitted {P : Prog} {σ : Store} {o : Option Store}
    (σ' : Store) (ho : o = some σ') (hn : ¬ ProphOutcome P σ σ') :
    ¬ ∀ τ, ProphOutcome P σ τ ↔ o = some τ :=
  fun h => hn ((h σ').2 ho)

/-- Two partial stores that differ at some local are different. -/
theorem ne_of_map_ne {o₁ o₂ : Option Store} (x : Var)
    (h : o₁.map (· x) ≠ o₂.map (· x)) : o₁ ≠ o₂ :=
  fun he => h (by rw [he])

/-- Prophecy assignment given by a list (default `0`). -/
def phiOf (l : List Int) : Nat → Int := fun k => l.getD k 0

/-! ## The counterexample programs -/

/-- Reads the lent local `x0` while `r0` is live:
`r0 = &mut x0; *r0 = 5; x1 = x0; *r0 = 9; end r0`. -/
def cxLent : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (assign 1 (var 0)), op (write 0 (lit 9)),
   op (endBorrow 0)]

/-- Reads through `r0` while it is reborrowed by `r1`:
`r0 = &mut x0; r1 = &mut *r0; *r1 = 7; x1 = *r0; *r1 = 9; end r1; end r0`. -/
def cxFrozen : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (assign 1 (deref 0)),
   op (write 1 (lit 9)), op (endBorrow 1), op (endBorrow 0)]

/-- Writes through `r1` after it ended:
`r0 = &mut x0; r1 = &mut *r0; end r1; *r1 = 4; end r0`. -/
def cxAfterEnd : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (endBorrow 1), op (write 1 (lit 4)),
   op (endBorrow 0)]

/-- Writes through `r1` after it ended and ends it a second time; the second
resolution contradicts the first:
`r0 = &mut x0; r1 = &mut *r0; end r1; *r1 = *r0 + 1; end r1; end r0`. -/
def cxAfterEndUnsat : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (endBorrow 1),
   op (write 1 (add (deref 0) (lit 1))), op (endBorrow 1), op (endBorrow 0)]

/-- Rebinds the live borrow name `r0`, losing the borrow of `x0`:
`r0 = &mut x0; *r0 = 5; r0 = &mut x1; end r0`. -/
def cxRebind : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (borrow 0 1), op (endBorrow 0)]

/-- Never ends its borrow: `r0 = &mut x0; *r0 = 5`. -/
def cxUnended : Prog := [op (borrow 0 0), op (write 0 (lit 5))]

/-! ## Facts about the counterexample programs -/

theorem cxLent_violations : violations cxLent = [.lentAccess] := by decide
theorem cxFrozen_violations : violations cxFrozen = [.frozenAccess] := by decide
theorem cxAfterEnd_violations : violations cxAfterEnd = [.useAfterEnd] := by decide
theorem cxAfterEndUnsat_violations :
    violations cxAfterEndUnsat = [.useAfterEnd, .useAfterEnd] := by decide
theorem cxRebind_violations : violations cxRebind = [.rebind] := by decide
theorem cxUnended_violations : violations cxUnended = [.unendedAtExit] := by decide

theorem cxLent_ref : (refSem cxLent zeroStore).map (· 1) = some 5 := by decide
theorem cxLent_back : (backSem cxLent zeroStore).map (· 1) = some 0 := by decide
theorem cxFrozen_ref : (refSem cxFrozen zeroStore).map (· 1) = some 7 := by decide
theorem cxFrozen_back : (backSem cxFrozen zeroStore).map (· 1) = some 0 := by decide
theorem cxAfterEnd_ref : (refSem cxAfterEnd zeroStore).map (· 0) = some 4 := by decide
theorem cxAfterEnd_back : (backSem cxAfterEnd zeroStore).map (· 0) = some 0 := by decide
theorem cxRebind_ref : (refSem cxRebind zeroStore).map (· 0) = some 5 := by decide
theorem cxRebind_back : (backSem cxRebind zeroStore).map (· 0) = some 0 := by decide
theorem cxUnended_ref : (refSem cxUnended zeroStore).map (· 0) = some 5 := by decide
theorem cxUnended_back : (backSem cxUnended zeroStore).map (· 0) = some 0 := by decide

/-- The prophecy translation of `cxLent` admits a store with `x1 = 9`: the read
of the lent local sees the lender's prophecy, i.e. the borrow's *final* value. -/
theorem cxLent_proph : ∃ σ', ProphOutcome cxLent zeroStore σ' ∧ σ' 1 = 9 :=
  ⟨_, ⟨phiOf [9], _, rfl, by decide, rfl⟩, rfl⟩

/-- The prophecy translation of `cxFrozen` admits a store with `x1 = 9`: the read
through the reborrowed `r0` sees `r1`'s prophecy. -/
theorem cxFrozen_proph : ∃ σ', ProphOutcome cxFrozen zeroStore σ' ∧ σ' 1 = 9 :=
  ⟨_, ⟨phiOf [9, 9], _, rfl, by decide, rfl⟩, rfl⟩

/-- The prophecy translation of `cxAfterEnd` admits a store with `x0 = 0`: the
write after the end comes after the resolution. -/
theorem cxAfterEnd_proph : ∃ σ', ProphOutcome cxAfterEnd zeroStore σ' ∧ σ' 0 = 0 :=
  ⟨_, ⟨phiOf [0, 0], _, rfl, by decide, rfl⟩, rfl⟩

/-- The prophecy translation of `cxAfterEndUnsat` admits no store at all: its
resolution constraints are unsatisfiable (`φ₁ = 0` and `φ₁ + 1 = φ₁`), although
the reference semantics succeeds. In a verifier that encodes resolutions as
assumptions this program would satisfy every postcondition. -/
theorem cxAfterEndUnsat_no_proph : ∀ σ', ¬ ProphOutcome cxAfterEndUnsat zeroStore σ' := by
  rintro σ' ⟨φ, s, hrun, hsat, -⟩
  simp [cxAfterEndUnsat, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
    fupd] at hrun
  subst hrun
  simp [Sat] at hsat
  omega

theorem cxAfterEndUnsat_ref : (refSem cxAfterEndUnsat zeroStore).map (· 0) = some 1 := by decide
theorem cxAfterEndUnsat_back : (backSem cxAfterEndUnsat zeroStore).map (· 0) = some 1 := by decide

/-- The prophecy translation of `cxRebind` admits `x0 = 7`: the lost borrow's
prophecy is never resolved. -/
theorem cxRebind_proph : ∃ σ', ProphOutcome cxRebind zeroStore σ' ∧ σ' 0 = 7 :=
  ⟨_, ⟨phiOf [7, 0], _, rfl, by decide, rfl⟩, rfl⟩

/-- The prophecy translation of `cxUnended` admits `x0 = 7`: the borrow's
prophecy is never resolved. -/
theorem cxUnended_proph : ∃ σ', ProphOutcome cxUnended zeroStore σ' ∧ σ' 0 = 7 :=
  ⟨_, ⟨phiOf [7], _, rfl, by decide, rfl⟩, rfl⟩

/-! ## Canonical counterexamples: soundness of the backward-function translation -/

/-- `NoLentAccess` is necessary for `backSem_eq_refSem_of_discipline`: `cxLent`
satisfies the other four parts of the discipline and the two semantics differ. -/
theorem backSem_eq_refSem_tight_noLentAccess :
    ¬ NoLentAccess cxLent ∧
    NoFrozenAccess cxLent ∧
    NoUseAfterEnd cxLent ∧
    FreshBindings cxLent ∧
    AllEndedAtExit cxLent ∧
    backSem cxLent zeroStore ≠ refSem cxLent zeroStore :=
  ⟨by decide, by decide, by decide, by decide, by decide, ne_of_map_ne 1 (by rw [cxLent_back, cxLent_ref]; decide)⟩

/-- `NoFrozenAccess` is necessary for `backSem_eq_refSem_of_discipline`: `cxFrozen`
satisfies the other four parts of the discipline and the two semantics differ. -/
theorem backSem_eq_refSem_tight_noFrozenAccess :
    NoLentAccess cxFrozen ∧
    ¬ NoFrozenAccess cxFrozen ∧
    NoUseAfterEnd cxFrozen ∧
    FreshBindings cxFrozen ∧
    AllEndedAtExit cxFrozen ∧
    backSem cxFrozen zeroStore ≠ refSem cxFrozen zeroStore :=
  ⟨by decide, by decide, by decide, by decide, by decide, ne_of_map_ne 1 (by rw [cxFrozen_back, cxFrozen_ref]; decide)⟩

/-- `NoUseAfterEnd` is necessary for `backSem_eq_refSem_of_discipline`: `cxAfterEnd`
satisfies the other four parts of the discipline and the two semantics differ. -/
theorem backSem_eq_refSem_tight_noUseAfterEnd :
    NoLentAccess cxAfterEnd ∧
    NoFrozenAccess cxAfterEnd ∧
    ¬ NoUseAfterEnd cxAfterEnd ∧
    FreshBindings cxAfterEnd ∧
    AllEndedAtExit cxAfterEnd ∧
    backSem cxAfterEnd zeroStore ≠ refSem cxAfterEnd zeroStore :=
  ⟨by decide, by decide, by decide, by decide, by decide, ne_of_map_ne 0 (by rw [cxAfterEnd_back, cxAfterEnd_ref]; decide)⟩

/-- `FreshBindings` is necessary for `backSem_eq_refSem_of_discipline`: `cxRebind`
satisfies the other four parts of the discipline and the two semantics differ. -/
theorem backSem_eq_refSem_tight_freshBindings :
    NoLentAccess cxRebind ∧
    NoFrozenAccess cxRebind ∧
    NoUseAfterEnd cxRebind ∧
    ¬ FreshBindings cxRebind ∧
    AllEndedAtExit cxRebind ∧
    backSem cxRebind zeroStore ≠ refSem cxRebind zeroStore :=
  ⟨by decide, by decide, by decide, by decide, by decide, ne_of_map_ne 0 (by rw [cxRebind_back, cxRebind_ref]; decide)⟩

/-- `AllEndedAtExit` is necessary for `backSem_eq_refSem_of_discipline`: `cxUnended`
satisfies the other four parts of the discipline and the two semantics differ. -/
theorem backSem_eq_refSem_tight_allEndedAtExit :
    NoLentAccess cxUnended ∧
    NoFrozenAccess cxUnended ∧
    NoUseAfterEnd cxUnended ∧
    FreshBindings cxUnended ∧
    ¬ AllEndedAtExit cxUnended ∧
    backSem cxUnended zeroStore ≠ refSem cxUnended zeroStore :=
  ⟨by decide, by decide, by decide, by decide, by decide, ne_of_map_ne 0 (by rw [cxUnended_back, cxUnended_ref]; decide)⟩


/-! ## Canonical counterexamples: agreement of the two translations -/

/-- `NoLentAccess` is necessary for `prophOutcome_iff_backSem_of_discipline`: `cxLent`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that differs from the backward-function translation's result. -/
theorem prophOutcome_iff_backSem_tight_noLentAccess :
    ¬ NoLentAccess cxLent ∧
    NoFrozenAccess cxLent ∧
    NoUseAfterEnd cxLent ∧
    FreshBindings cxLent ∧
    AllEndedAtExit cxLent ∧
    ¬ ∀ σ', ProphOutcome cxLent zeroStore σ' ↔ backSem cxLent zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxLent_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 1 (by rw [cxLent_back, hv]; decide)

/-- `NoFrozenAccess` is necessary for `prophOutcome_iff_backSem_of_discipline`: `cxFrozen`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that differs from the backward-function translation's result. -/
theorem prophOutcome_iff_backSem_tight_noFrozenAccess :
    NoLentAccess cxFrozen ∧
    ¬ NoFrozenAccess cxFrozen ∧
    NoUseAfterEnd cxFrozen ∧
    FreshBindings cxFrozen ∧
    AllEndedAtExit cxFrozen ∧
    ¬ ∀ σ', ProphOutcome cxFrozen zeroStore σ' ↔ backSem cxFrozen zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxFrozen_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 1 (by rw [cxFrozen_back, hv]; decide)

/-- `NoUseAfterEnd` is necessary for `prophOutcome_iff_backSem_of_discipline`:
`cxAfterEndUnsat` satisfies the other four parts of the discipline, the
backward-function translation succeeds, and the prophecy translation admits no
store. -/
theorem prophOutcome_iff_backSem_tight_noUseAfterEnd :
    NoLentAccess cxAfterEndUnsat ∧
    NoFrozenAccess cxAfterEndUnsat ∧
    ¬ NoUseAfterEnd cxAfterEndUnsat ∧
    FreshBindings cxAfterEndUnsat ∧
    AllEndedAtExit cxAfterEndUnsat ∧
    ¬ ∀ σ', ProphOutcome cxAfterEndUnsat zeroStore σ' ↔ backSem cxAfterEndUnsat zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', backSem cxAfterEndUnsat zeroStore = some σ' := ⟨_, rfl⟩
  exact not_prophOutcome_iff_of_not_admitted σ' hσ' (cxAfterEndUnsat_no_proph σ')

/-- `FreshBindings` is necessary for `prophOutcome_iff_backSem_of_discipline`: `cxRebind`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that differs from the backward-function translation's result. -/
theorem prophOutcome_iff_backSem_tight_freshBindings :
    NoLentAccess cxRebind ∧
    NoFrozenAccess cxRebind ∧
    NoUseAfterEnd cxRebind ∧
    ¬ FreshBindings cxRebind ∧
    AllEndedAtExit cxRebind ∧
    ¬ ∀ σ', ProphOutcome cxRebind zeroStore σ' ↔ backSem cxRebind zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxRebind_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 0 (by rw [cxRebind_back, hv]; decide)

/-- `AllEndedAtExit` is necessary for `prophOutcome_iff_backSem_of_discipline`: `cxUnended`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that differs from the backward-function translation's result. -/
theorem prophOutcome_iff_backSem_tight_allEndedAtExit :
    NoLentAccess cxUnended ∧
    NoFrozenAccess cxUnended ∧
    NoUseAfterEnd cxUnended ∧
    FreshBindings cxUnended ∧
    ¬ AllEndedAtExit cxUnended ∧
    ¬ ∀ σ', ProphOutcome cxUnended zeroStore σ' ↔ backSem cxUnended zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxUnended_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 0 (by rw [cxUnended_back, hv]; decide)


/-! ## Canonical counterexamples: soundness and precision of the prophecy translation -/

/-- `NoLentAccess` is necessary for `prophOutcome_iff_refSem_of_discipline`: `cxLent`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that the program does not produce. -/
theorem prophOutcome_iff_refSem_tight_noLentAccess :
    ¬ NoLentAccess cxLent ∧
    NoFrozenAccess cxLent ∧
    NoUseAfterEnd cxLent ∧
    FreshBindings cxLent ∧
    AllEndedAtExit cxLent ∧
    ¬ ∀ σ', ProphOutcome cxLent zeroStore σ' ↔ refSem cxLent zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxLent_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 1 (by rw [cxLent_ref, hv]; decide)

/-- `NoFrozenAccess` is necessary for `prophOutcome_iff_refSem_of_discipline`: `cxFrozen`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that the program does not produce. -/
theorem prophOutcome_iff_refSem_tight_noFrozenAccess :
    NoLentAccess cxFrozen ∧
    ¬ NoFrozenAccess cxFrozen ∧
    NoUseAfterEnd cxFrozen ∧
    FreshBindings cxFrozen ∧
    AllEndedAtExit cxFrozen ∧
    ¬ ∀ σ', ProphOutcome cxFrozen zeroStore σ' ↔ refSem cxFrozen zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxFrozen_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 1 (by rw [cxFrozen_ref, hv]; decide)

/-- `NoUseAfterEnd` is necessary for `prophOutcome_iff_refSem_of_discipline`: `cxAfterEnd`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that the program does not produce. -/
theorem prophOutcome_iff_refSem_tight_noUseAfterEnd :
    NoLentAccess cxAfterEnd ∧
    NoFrozenAccess cxAfterEnd ∧
    ¬ NoUseAfterEnd cxAfterEnd ∧
    FreshBindings cxAfterEnd ∧
    AllEndedAtExit cxAfterEnd ∧
    ¬ ∀ σ', ProphOutcome cxAfterEnd zeroStore σ' ↔ refSem cxAfterEnd zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxAfterEnd_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 0 (by rw [cxAfterEnd_ref, hv]; decide)

/-- `FreshBindings` is necessary for `prophOutcome_iff_refSem_of_discipline`: `cxRebind`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that the program does not produce. -/
theorem prophOutcome_iff_refSem_tight_freshBindings :
    NoLentAccess cxRebind ∧
    NoFrozenAccess cxRebind ∧
    NoUseAfterEnd cxRebind ∧
    ¬ FreshBindings cxRebind ∧
    AllEndedAtExit cxRebind ∧
    ¬ ∀ σ', ProphOutcome cxRebind zeroStore σ' ↔ refSem cxRebind zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxRebind_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 0 (by rw [cxRebind_ref, hv]; decide)

/-- `AllEndedAtExit` is necessary for `prophOutcome_iff_refSem_of_discipline`: `cxUnended`
satisfies the other four parts of the discipline and the prophecy translation
admits a store that the program does not produce. -/
theorem prophOutcome_iff_refSem_tight_allEndedAtExit :
    NoLentAccess cxUnended ∧
    NoFrozenAccess cxUnended ∧
    NoUseAfterEnd cxUnended ∧
    FreshBindings cxUnended ∧
    ¬ AllEndedAtExit cxUnended ∧
    ¬ ∀ σ', ProphOutcome cxUnended zeroStore σ' ↔ refSem cxUnended zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', h1, hv⟩ := cxUnended_proph
  exact not_prophOutcome_iff_of_admitted σ' h1 0 (by rw [cxUnended_ref, hv]; decide)


/-! ## Canonical counterexamples: inclusion of the real outcome -/

/-- Every store admitted for `cxLent` under the standard policy has `x1 = 9`. -/
theorem cxLent_proph_forces :
    ∀ σ', ProphOutcome cxLent zeroStore σ' → σ' 1 = 9 := by
  rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
  simp [cxLent, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std, fupd] at hrun
  subst hrun
  simp [Sat] at hsat
  simp [Store.set, hsat]

/-- With the resolution of `r0` omitted, every store admitted for `cxLent` has
`x0 = x1`: both hold the unresolved prophecy of `r0`. -/
theorem cxLent_omit0_forces :
    ∀ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxLent zeroStore σ' → σ' 0 = σ' 1 := by
  rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
  simp [cxLent, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
    ResPolicy.omitAtEnd, fupd] at hrun
  subst hrun
  simp [Store.set]

/-- The reference outcome of `cxLent`: `x0 = 9`, `x1 = 5`. -/
theorem cxLent_ref01 : (refSem cxLent zeroStore).map (fun σ => (σ 0, σ 1)) = some (9, 5) := by
  decide

/-- Every store admitted for `cxFrozen` (standard policy, or with the resolution
of `r0` omitted) has `x1 = 9`. -/
theorem cxFrozen_proph_forces (pol : ResPolicy)
    (hpol : pol = ResPolicy.std ∨ pol = ResPolicy.omitAtEnd 0) :
    ∀ σ', ProphOutcomeWith pol cxFrozen zeroStore σ' → σ' 1 = 9 := by
  rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
  rcases hpol with rfl | rfl <;>
  · simp [cxFrozen, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
      ResPolicy.omitAtEnd, fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    simp [Store.set]
    omega

/-- No store is admitted for `cxAfterEndUnsat` when the resolution of `r0` is
omitted: the contradictory constraints come from the two ends of `r1`. -/
theorem cxAfterEndUnsat_no_proph_omit0 :
    ∀ σ', ¬ ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxAfterEndUnsat zeroStore σ' := by
  rintro σ' ⟨φ, s, hrun, hsat, -⟩
  simp [cxAfterEndUnsat, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
    ResPolicy.omitAtEnd, fupd] at hrun
  subst hrun
  simp [Sat] at hsat
  omega

/-- `NoLentAccess` is necessary for
`prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`:
`cxLent` satisfies the other three hypotheses, the program produces a store with
`x1 = 5`, and every admitted store has `x1 = 9`. -/
theorem prophOutcome_of_refSem_tight_noLentAccess :
    ¬ NoLentAccess cxLent ∧
    NoFrozenAccess cxLent ∧
    NoUseAfterEnd cxLent ∧
    FreshBindings cxLent ∧
    ∃ σ', refSem cxLent zeroStore = some σ' ∧ ¬ ProphOutcome cxLent zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxLent zeroStore = some σ' := ⟨_, rfl⟩
  refine ⟨σ', hσ', fun h => ?_⟩
  have h1 := cxLent_proph_forces σ' h
  have h2 := cxLent_ref
  rw [hσ'] at h2
  simp at h2
  omega

/-- `NoFrozenAccess` is necessary for
`prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`:
`cxFrozen` satisfies the other three hypotheses, the program produces a store
with `x1 = 7`, and every admitted store has `x1 = 9`. -/
theorem prophOutcome_of_refSem_tight_noFrozenAccess :
    NoLentAccess cxFrozen ∧
    ¬ NoFrozenAccess cxFrozen ∧
    NoUseAfterEnd cxFrozen ∧
    FreshBindings cxFrozen ∧
    ∃ σ', refSem cxFrozen zeroStore = some σ' ∧ ¬ ProphOutcome cxFrozen zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxFrozen zeroStore = some σ' := ⟨_, rfl⟩
  refine ⟨σ', hσ', fun h => ?_⟩
  have h1 := cxFrozen_proph_forces _ (Or.inl rfl) σ' h
  have h2 := cxFrozen_ref
  rw [hσ'] at h2
  simp at h2
  omega

/-- `NoUseAfterEnd` is necessary for
`prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`:
`cxAfterEndUnsat` satisfies the other three hypotheses and produces a store, and
no store is admitted. -/
theorem prophOutcome_of_refSem_tight_noUseAfterEnd :
    NoLentAccess cxAfterEndUnsat ∧
    NoFrozenAccess cxAfterEndUnsat ∧
    ¬ NoUseAfterEnd cxAfterEndUnsat ∧
    FreshBindings cxAfterEndUnsat ∧
    ∃ σ', refSem cxAfterEndUnsat zeroStore = some σ' ∧ ¬ ProphOutcome cxAfterEndUnsat zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxAfterEndUnsat zeroStore = some σ' := ⟨_, rfl⟩
  exact ⟨σ', hσ', cxAfterEndUnsat_no_proph σ'⟩

/-! ## Canonical counterexamples: omission keeps the real outcome

Each counterexample instantiates the omitted name `r` with `0`, the borrow the
program actually creates and ends, so that the resolution of a used borrow is
omitted. -/

/-- `NoLentAccess` is necessary for
`prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
(with `r = 0`): `cxLent` satisfies the other three hypotheses, its outcome has
`x0 = 9` and `x1 = 5`, and with `r0`'s resolution omitted every admitted store has
`x0 = x1`. -/
theorem prophOutcomeWith_omitAtEnd_of_refSem_tight_noLentAccess :
    ¬ NoLentAccess cxLent ∧
    NoFrozenAccess cxLent ∧
    NoUseAfterEnd cxLent ∧
    FreshBindings cxLent ∧
    ∃ σ', refSem cxLent zeroStore = some σ' ∧
      ¬ ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxLent zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxLent zeroStore = some σ' := ⟨_, rfl⟩
  refine ⟨σ', hσ', fun h => ?_⟩
  have h1 := cxLent_omit0_forces σ' h
  have h2 := cxLent_ref01
  rw [hσ'] at h2
  simp at h2
  omega

/-- `NoFrozenAccess` is necessary for
`prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
(with `r = 0`): `cxFrozen` satisfies the other three hypotheses, its outcome has
`x1 = 7`, and with `r0`'s resolution omitted every admitted store has `x1 = 9`. -/
theorem prophOutcomeWith_omitAtEnd_of_refSem_tight_noFrozenAccess :
    NoLentAccess cxFrozen ∧
    ¬ NoFrozenAccess cxFrozen ∧
    NoUseAfterEnd cxFrozen ∧
    FreshBindings cxFrozen ∧
    ∃ σ', refSem cxFrozen zeroStore = some σ' ∧
      ¬ ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxFrozen zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxFrozen zeroStore = some σ' := ⟨_, rfl⟩
  refine ⟨σ', hσ', fun h => ?_⟩
  have h1 := cxFrozen_proph_forces _ (Or.inr rfl) σ' h
  have h2 := cxFrozen_ref
  rw [hσ'] at h2
  simp at h2
  omega

/-- `NoUseAfterEnd` is necessary for
`prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
(with `r = 0`): `cxAfterEndUnsat` satisfies the other three hypotheses and
produces a store, and with `r0`'s resolution omitted no store is admitted. -/
theorem prophOutcomeWith_omitAtEnd_of_refSem_tight_noUseAfterEnd :
    NoLentAccess cxAfterEndUnsat ∧
    NoFrozenAccess cxAfterEndUnsat ∧
    ¬ NoUseAfterEnd cxAfterEndUnsat ∧
    FreshBindings cxAfterEndUnsat ∧
    ∃ σ', refSem cxAfterEndUnsat zeroStore = some σ' ∧
      ¬ ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxAfterEndUnsat zeroStore σ' := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ', refSem cxAfterEndUnsat zeroStore = some σ' := ⟨_, rfl⟩
  exact ⟨σ', hσ', cxAfterEndUnsat_no_proph_omit0 σ'⟩

end Toy.Prophecy
