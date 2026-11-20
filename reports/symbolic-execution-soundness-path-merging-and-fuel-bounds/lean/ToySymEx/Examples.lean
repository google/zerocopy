import ToySymEx.Programs
import ToySymEx.Lemmas

/-!
Named leaves of the example programs, closed forms of their concrete runs, and
proved positive and negative examples for every core definition.
-/

namespace Toy.SymEx

open Term

/-! ## Named leaves of `exDiamond` and `exPanicIfZero` -/

/-- Path condition of the `x0 = 0` branch of `exDiamond`. -/
def dc₁ : Term := Term.and tt (eq (var 0) (int 0))
/-- Path condition of the `x0 ≠ 0` branch of `exDiamond`. -/
def dc₂ : Term := Term.and tt (Term.not (eq (var 0) (int 0)))
/-- Final symbolic store of the `x0 = 0` branch: `x1 ↦ x0 + 1`. -/
def dσ₁ : SymStore := SymStore.init.set 1 (add (var 0) (int 1))
/-- Final symbolic store of the `x0 ≠ 0` branch: `x1 ↦ x0 + 2`. -/
def dσ₂ : SymStore := SymStore.init.set 1 (add (var 0) (int 2))

theorem symExec_exDiamond :
    symExec exDiamond 4 = [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] := rfl

/-- Path condition of the panic leaf of `exPanicIfZero`. -/
def pzPanicPc : Term := Term.and tt (Term.not (Term.not (eq (var 0) (int 0))))
/-- Path condition of the success leaf of `exPanicIfZero`. -/
def pzOkPc : Term := Term.and tt (Term.not (eq (var 0) (int 0)))

theorem symExec_exPanicIfZero :
    symExec exPanicIfZero 2 = [⟨pzPanicPc, .panic ⟨0, 0⟩⟩, ⟨pzOkPc, .ok SymStore.init⟩] := rfl

theorem holds_dc₁ (ρ : Valuation) : holds dc₁ ρ ↔ ρ 0 = .int 0 := by
  by_cases h : ρ 0 = .int 0 <;>
    simp [holds, dc₁, Term.and, Term.tt, Term.ff, Term.int, Term.eval, Val.toBool, h]

theorem holds_dc₂ (ρ : Valuation) : holds dc₂ ρ ↔ ρ 0 ≠ .int 0 := by
  by_cases h : ρ 0 = .int 0 <;>
    simp [holds, dc₂, Term.and, Term.not, Term.tt, Term.ff, Term.int, Term.eval, Val.toBool, h]

theorem holds_pzOkPc (ρ : Valuation) : holds pzOkPc ρ ↔ ρ 0 ≠ .int 0 := by
  by_cases h : ρ 0 = .int 0 <;>
    simp [holds, pzOkPc, Term.and, Term.not, Term.tt, Term.ff, Term.int, Term.eval, Val.toBool, h]

theorem holds_pzPanicPc (ρ : Valuation) : holds pzPanicPc ρ ↔ ρ 0 = .int 0 := by
  by_cases h : ρ 0 = .int 0 <;>
    simp [holds, pzPanicPc, Term.and, Term.not, Term.tt, Term.ff, Term.int, Term.eval, Val.toBool, h]

/-- Closed form of the concrete run of `exDiamond` with fuel 4 from any input. -/
theorem exec_exDiamond (ρ : Valuation) :
    exec exDiamond 4 (SymStore.init.inst ρ) =
      if ρ 0 = .int 0 then .ok (dσ₁.inst ρ) else .ok (dσ₂.inst ρ) := by
  have e1 : (SymStore.init.inst ρ).set 1 (.int ((ρ 0).toInt + 1)) = dσ₁.inst ρ := by
    funext y
    by_cases hy : y = 1 <;>
      simp [Store.set, SymStore.set, SymStore.inst, SymStore.init, dσ₁, hy, Term.eval, Term.int, Val.toInt]
  have e2 : (SymStore.init.inst ρ).set 1 (.int ((ρ 0).toInt + 2)) = dσ₂.inst ρ := by
    funext y
    by_cases hy : y = 1 <;>
      simp [Store.set, SymStore.set, SymStore.inst, SymStore.init, dσ₂, hy, Term.eval, Term.int, Val.toInt]
  by_cases h : ρ 0 = .int 0
  · simp only [h, ↓reduceIte]
    rw [← e1]
    simp [exec, exDiamond, runBlock, select, SymStore.inst, SymStore.init, Term.eval, h, Term.int, Val.toInt]
  · simp only [h, ↓reduceIte]
    rw [← e2]
    simp [exec, exDiamond, runBlock, select, SymStore.inst, SymStore.init, Term.eval, h, Term.int, Val.toInt]

/-- Closed form of the concrete run of `exPanicIfZero` with fuel 2. -/
theorem exec_exPanicIfZero (ρ : Valuation) :
    exec exPanicIfZero 2 (SymStore.init.inst ρ) =
      if ρ 0 = .int 0 then .panic ⟨0, 0⟩ else .ok (SymStore.init.inst ρ) := by
  by_cases h : ρ 0 = .int 0 <;>
    simp [exec, exPanicIfZero, runBlock, SymStore.inst, SymStore.init, Term.eval, h, Term.int,
      Term.not, Term.tt, Term.ff, Val.toBool]

/-! ## Examples for `Val`, `Term.eval`, `holds`, `Sat`, `Disjoint` -/

example : Val.toBool (.int 3) = true := by decide
example : Val.toBool (.int 0) = false := by decide
example : Val.toInt (.bool true) = 1 := by decide

/-- `eval`, positive: `x0 + 1` at `x0 = 5` is `6`. -/
example : (add (var 0) (int 1)).eval ρ5 = .int 6 := by decide
/-- `eval`, negative: `eq` is structural, so the integer `1` is not equal to `true`. -/
example : (eq (int 1) tt).eval ρ0 = .bool false := by decide

/-- `holds`, positive. -/
example : holds (eq (var 0) (int 5)) ρ5 := by decide
/-- `holds`, negative. -/
example : ¬ holds (eq (var 0) (int 5)) ρ0 := by decide
/-- `holds`, negative: integer `0` is false. -/
example : ¬ holds (int 0) ρ0 := by decide

/-- `Sat`, positive. -/
example : Sat dc₁ := ⟨ρ0, (holds_dc₁ ρ0).2 rfl⟩
/-- `Sat`, negative: `c ∧ ¬c` is unsatisfiable. -/
example : ¬ Sat (Term.and dc₁ (Term.not dc₁)) := by
  rintro ⟨ρ, h⟩
  unfold holds Term.and Term.not at h
  cases h1 : (dc₁.eval ρ).toBool <;> simp_all [Term.eval, Term.ff, Term.tt, Val.toBool]

/-- `Disjoint`, positive: the two `exDiamond` branches. -/
theorem disjoint_dc₁_dc₂ : Disjoint dc₁ dc₂ := by
  intro ρ ⟨h1, h2⟩
  exact (holds_dc₂ ρ).1 h2 ((holds_dc₁ ρ).1 h1)
/-- `Disjoint`, negative. -/
example : ¬ Disjoint tt tt := fun h => h ρ0 ⟨rfl, rfl⟩

/-! ## Examples for `subst`, `SymStore.inst`, `select`, `forkSwitch` -/

/-- `subst`, positive: symbolic evaluation of `x1 + x1` in `dσ₁`. -/
example : (add (var 1) (var 1)).subst dσ₁ = add (add (var 0) (int 1)) (add (var 0) (int 1)) := rfl
/-- `subst`, negative: substitution does not simplify (`x1 + 0` stays a sum). -/
example : (add (var 1) (int 0)).subst dσ₁ ≠ add (var 0) (int 1) := by decide

/-- `SymStore.init.inst ρ` is the valuation itself, read as a store. -/
example (ρ : Valuation) : SymStore.init.inst ρ = ρ := rfl
/-- `SymStore.inst`, positive. -/
example : dσ₁.inst ρ5 1 = .int 6 := by decide
/-- `SymStore.inst`, negative: `dσ₂` does not give `x1 = 6` at `x0 = 5`. -/
example : dσ₂.inst ρ5 1 ≠ .int 6 := by decide

/-- `select`, positive: matching target. -/
example : select (.int 0) [(.int 0, 1)] 2 = 1 := by decide
/-- `select`, negative: no match falls through to `otherwise`. -/
example : select (.int 5) [(.int 0, 1)] 2 = 2 := by decide
/-- `select`, negative: matching is structural (`true` is not `1`). -/
example : select (.bool true) [(.int 1, 1)] 2 = 2 := by decide
/-- `select`, first match wins. -/
example : select (.int 0) [(.int 0, 1), (.int 0, 7)] 2 = 1 := by decide

/-- `forkSwitch`, positive: one pair per target plus `otherwise`. -/
example : (forkSwitch (var 0) [(.int 0, 1), (.int 1, 2)] 3 tt).map Prod.snd = [1, 2, 3] := rfl
/-- `forkSwitch`, negative: a duplicated target value yields an unsatisfiable
second branch rather than an overlapping one. -/
example : ¬ Sat ((forkSwitch (var 0) [(.int 0, 1), (.int 0, 2)] 3 tt)[1]!.1) := by
  rintro ⟨ρ, h⟩
  by_cases h0 : ρ 0 = .int 0 <;>
    simp_all [forkSwitch, holds, Term.and, Term.not, Term.tt, Term.ff, Term.eval, Val.toBool]

/-! ## Examples for `runBlock` / `exec` -/

/-- `exec`, positive: `exStraight` returns at fuel 5 with `x2 = 12` from `x0 = 5`. -/
example : (exec exStraight 5 ρ5).get? 2 = some (.int 12) := by decide
/-- `exec`, negative: `exPanicIfZero` panics at `(0, 0)` from `x0 = 0`. -/
example : (exec exPanicIfZero 2 ρ0).panicLoc? = some ⟨0, 0⟩ := by decide
/-- `exec`, negative: too little fuel yields `outOfFuel`, not success. -/
example : (exec exStraight 4 ρ5).tag = 2 := by decide
/-- `exec`, negative: a jump to a missing block is a panic at that block. -/
example : (exec [⟨[], .goto 7⟩] 1 ρ0).panicLoc? = some ⟨7, 0⟩ := by decide
/-- `exec` of the empty CFG panics at `(0, 0)`. -/
example : (exec [] 3 ρ0).panicLoc? = some ⟨0, 0⟩ := by decide

/-! ## Examples for `symExec` -/

/-- `symExec`, positive: `exDiamond` yields two successful leaves at fuel 4. -/
example : (symExec exDiamond 4).map (fun l => l.res.tag) = [0, 0] := by decide
/-- `symExec`, negative: at fuel 4, `exStraight` still has an `outOfFuel` leaf. -/
example : (symExec exStraight 4).map (fun l => l.res.tag) = [1, 2] := by decide
/-- `symExec` at fuel 5 on `exStraight`: no `outOfFuel` leaf. -/
example : (symExec exStraight 5).map (fun l => l.res.tag) = [1, 0] := by decide
/-- `symExec` does not prune: `assert true` still produces a panic leaf, whose
path condition is unsatisfiable. -/
example : (symExec exAssertTrue 2).map (fun l => l.res.tag) = [1, 0] ∧
    ¬ Sat ((symExec exAssertTrue 2)[0]!).pc := by
  refine ⟨by decide, ?_⟩
  rintro ⟨ρ, h⟩
  simp [symExec, exAssertTrue, symBlock, holds, Term.and, Term.not, Term.tt, Term.ff, Term.eval,
    Term.subst, Val.toBool] at h

/-! ## Examples for `OkWith`, `OkWithOrOutOfFuel` -/

example : OkWith (fun st => st 1 = .int 7) (exec exDiamond 4 ρ5) := rfl
example : ¬ OkWith (fun _ => True) (.panic ⟨0, 0⟩) := id
example : ¬ OkWith (fun _ => True) .outOfFuel := id
example : OkWithOrOutOfFuel (fun _ => False) .outOfFuel := trivial
example : ¬ OkWithOrOutOfFuel (fun _ => True) (.panic ⟨0, 0⟩) := id

/-! ## Examples for the leaf checks -/

/-- Postcondition used with `exDiamond`: `x1 ≠ x0`. -/
def QneDiamond : Store → Prop := fun st => st 1 ≠ st 0

/-- `LeavesProve` / `ProvesStrict`, positive. -/
theorem provesStrict_exDiamond : ProvesStrict exDiamond 4 QneDiamond := by
  intro l hl ρ _
  rw [symExec_exDiamond] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;>
  · simp only [SymOutcome.inst, OkWith, QneDiamond]
    cases h0 : ρ 0 <;>
      simp [dσ₁, dσ₂, SymStore.inst, SymStore.set, SymStore.init, Term.eval, Term.int, Val.toInt, h0] <;>
      omega

/-- `LeavesProve` / `ProvesStrict`, negative: the panic leaf of `exPanicIfZero`
is satisfiable. -/
theorem not_provesStrict_exPanicIfZero : ¬ ProvesStrict exPanicIfZero 2 (fun _ => True) := by
  intro h
  have := h ⟨pzPanicPc, .panic ⟨0, 0⟩⟩ (by rw [symExec_exPanicIfZero]; simp) ρ0
    ((holds_pzPanicPc ρ0).2 rfl)
  exact this

/-- `LeavesProveLax` / `ProvesLax`, positive: at fuel 4, `exStraight` has only an
infeasible panic leaf and an `outOfFuel` leaf. -/
theorem provesLax_exStraight_4 : ProvesLax exStraight 4 (fun _ => False) := by
  intro l hl ρ hρ
  simp [symExec, exStraight, symBlock] at hl
  rcases hl with rfl | rfl <;>
    simp_all [holds, Term.eval, OkWithOrOutOfFuel, SymOutcome.inst, Term.and, Term.not, Term.tt,
      Term.ff, Term.int, Val.toBool, Term.subst, SymStore.set, SymStore.init]

/-- The same leaves fail the strict check. -/
theorem not_provesStrict_exStraight_4 : ¬ ProvesStrict exStraight 4 (fun _ => True) := by
  intro h
  have hmem : (⟨Term.and tt (eq (add (var 0) (int 1)) (add (var 0) (int 1))), .outOfFuel⟩ : Leaf)
      ∈ symExec exStraight 4 := by
    simp [symExec, exStraight, symBlock, Term.subst, SymStore.set, SymStore.init, Term.int]
  exact h _ hmem ρ0 (by decide)

/-- `LeavesProveLax`, negative. -/
theorem not_provesLax_exPanicIfZero : ¬ ProvesLax exPanicIfZero 2 (fun _ => True) := by
  intro h
  exact h ⟨pzPanicPc, .panic ⟨0, 0⟩⟩ (by rw [symExec_exPanicIfZero]; simp) ρ0
    ((holds_pzPanicPc ρ0).2 rfl)

/-! ## Examples for `LeavesSound`, `LeavesExhaustive`, `dropPcs` -/

/-- `LeavesSound`, positive: the leaves of `exDiamond` at fuel 4. -/
theorem leavesSound_exDiamond : LeavesSound exDiamond 4 (symExec exDiamond 4) := by
  intro l hl ρ hρ
  rw [symExec_exDiamond] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [exec_exDiamond]
  rcases hl with rfl | rfl
  · simp only [(holds_dc₁ ρ).1 hρ, ↓reduceIte]; rfl
  · simp only [(holds_dc₂ ρ).1 hρ, ↓reduceIte]; rfl

/-- `LeavesSound`, negative: a leaf claiming success on every input of a
program that panics on `x0 = 0`. -/
theorem not_leavesSound_tt_ok_exPanicIfZero :
    ¬ LeavesSound exPanicIfZero 2 [⟨tt, .ok SymStore.init⟩] := by
  intro h
  have := h _ (List.mem_singleton_self _) ρ0 rfl
  rw [exec_exPanicIfZero] at this
  simp [ρ0] at this
  cases this

/-- `LeavesExhaustive`, positive. -/
theorem leavesExhaustive_exDiamond : LeavesExhaustive (symExec exDiamond 4) := by
  intro ρ
  rw [symExec_exDiamond]
  by_cases h : ρ 0 = .int 0
  · exact ⟨_, List.mem_cons_self .., (holds_dc₁ ρ).2 h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (holds_dc₂ ρ).2 h⟩

/-- `LeavesExhaustive`, negative: the success leaf of `exPanicIfZero` alone does
not cover `x0 = 0`. -/
theorem not_leavesExhaustive_pzOk : ¬ LeavesExhaustive [⟨pzOkPc, .ok SymStore.init⟩] := by
  intro h
  obtain ⟨l, hl, hpc⟩ := h ρ0
  rw [List.mem_singleton] at hl
  subst hl
  exact (holds_pzOkPc ρ0).1 hpc rfl

/-- `dropPcs` turns the infeasible panic leaf of `exAssertTrue` into a feasible one. -/
example : ∃ l ∈ dropPcs (symExec exAssertTrue 2), l.res.tag = 1 ∧ holds l.pc ρ0 :=
  ⟨⟨tt, .panic ⟨0, 0⟩⟩, by simp [dropPcs, symExec, exAssertTrue, symBlock], rfl, rfl⟩

/-- `dropPcs`, negative: erased leaves are not per-leaf sound (the erased
panic leaf of `exAssertTrue` claims a panic on every input). -/
theorem dropPcs_not_leavesSound :
    ¬ LeavesSound exAssertTrue 2 (dropPcs (symExec exAssertTrue 2)) := by
  intro hs
  have hmem : (⟨Term.tt, .panic ⟨0, 0⟩⟩ : Leaf) ∈ dropPcs (symExec exAssertTrue 2) := by
    simp [dropPcs, symExec, exAssertTrue, symBlock]
  have h := congrArg Outcome.tag (hs _ hmem ρ0 rfl)
  revert h; decide

/-! ## Examples for `GuardedSound`, merging, and `Covers` -/

/-- Reference for `exDiamond` at fuel 4. -/
def Rdia : Valuation → Outcome := fun ρ => exec exDiamond 4 (SymStore.init.inst ρ)

theorem guardedSound_dc₁_dσ₁ : GuardedSound Rdia Outcome.ok dc₁ dσ₁ := by
  intro ρ h; simp only [Rdia]; rw [exec_exDiamond]; simp only [(holds_dc₁ ρ).1 h, ↓reduceIte]

theorem guardedSound_dc₂_dσ₂ : GuardedSound Rdia Outcome.ok dc₂ dσ₂ := by
  intro ρ h; simp only [Rdia]; rw [exec_exDiamond]; simp only [(holds_dc₂ ρ).1 h, ↓reduceIte]

/-- `GuardedSound`, negative: the `x0 = 0` store does not describe input `x0 = 5`. -/
theorem not_guardedSound_tt_dσ₁ : ¬ GuardedSound Rdia Outcome.ok tt dσ₁ := by
  intro h
  have := congrArg (Outcome.get? 1) (h ρ5 rfl)
  revert this; decide

/-- `mergeStore`, example: the merged `x1` is `ite dc₁ (x0+1) (x0+2)`. -/
example : mergeStore dc₁ dσ₁ dσ₂ 1 = Term.ite dc₁ (add (var 0) (int 1)) (add (var 0) (int 2)) := rfl
/-- `mergeLeaf` picks the first store where its guard holds and the second elsewhere. -/
example : ((mergeLeaf dc₁ dσ₁ dc₂ dσ₂).res.inst ρ0).get? 1 = some (.int 1) ∧
    ((mergeLeaf dc₁ dσ₁ dc₂ dσ₂).res.inst ρ5).get? 1 = some (.int 7) := by decide
/-- `mergeLeafUnguarded` keeps `σ₁` even where only `c₂` holds. -/
example : ((mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂).res.inst ρ5).get? 1 = some (.int 6) := by decide

/-- `Covers`, positive: the two `exDiamond` branch states cover its (functional)
behaviour. -/
theorem covers_exDiamond :
    Covers (fun ρ o => Rdia ρ = o) Outcome.ok [(dc₁, dσ₁), (dc₂, dσ₂)] := by
  intro ρ a h
  subst h
  by_cases h0 : ρ 0 = .int 0
  · exact ⟨_, List.mem_cons_self .., (holds_dc₁ ρ).2 h0, (guardedSound_dc₁_dσ₁ ρ ((holds_dc₁ ρ).2 h0)).symm⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (holds_dc₂ ρ).2 h0,
      (guardedSound_dc₂_dσ₂ ρ ((holds_dc₂ ρ).2 h0)).symm⟩

/-- `Covers`, negative: one branch alone does not cover. -/
theorem not_covers_exDiamond_one_branch :
    ¬ Covers (fun ρ o => Rdia ρ = o) Outcome.ok [(dc₁, dσ₁)] := by
  intro h
  obtain ⟨cs, hcs, hg, _⟩ := h ρ5 _ rfl
  rw [List.mem_singleton] at hcs
  subst hcs
  exact absurd ((holds_dc₁ ρ5).1 hg) (by decide)

/-! ## Examples for `SimpSoundUnder` -/

/-- Rewriting `x0 ↦ 0` is sound under any path condition that forces `x0 = 0`. -/
theorem simpSoundUnder_substVar_of_forces (c : Term)
    (hc : ∀ ρ, holds c ρ → ρ 0 = .int 0) : SimpSoundUnder c (Term.substVar 0 (int 0)) := by
  intro t ρ h
  have h0 := hc ρ h
  induction t with
  | var y =>
    by_cases hy : y = 0
    · subst hy; simp [Term.substVar, Term.subst, Term.eval, Term.int, h0]
    · simp [Term.substVar, Term.subst, Term.eval, hy]
  | lit v => rfl
  | add a b iha ihb =>
    simp only [Term.substVar] at iha ihb
    simp [Term.substVar, Term.subst, Term.eval, iha, ihb]
  | eq a b iha ihb =>
    simp only [Term.substVar] at iha ihb
    simp [Term.substVar, Term.subst, Term.eval, iha, ihb]
  | ite c' t e ihc iht ihe =>
    simp only [Term.substVar] at ihc iht ihe
    simp [Term.substVar, Term.subst, Term.eval, ihc, iht, ihe]

/-- `SimpSoundUnder`, positive: `x0 ↦ 0` under `dc₁`. -/
theorem simpSoundUnder_dc₁ : SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) :=
  simpSoundUnder_substVar_of_forces dc₁ (fun ρ h => (holds_dc₁ ρ).1 h)

/-- `SimpSoundUnder`, negative: the same rewrite is not sound under `true`. -/
theorem not_simpSoundUnder_tt : ¬ SimpSoundUnder tt (Term.substVar 0 (int 0)) := by
  intro h
  have := h (var 0) ρ5 rfl
  revert this; decide

/-- The identity simplifier is sound under every path condition. -/
example (c : Term) : SimpSoundUnder c id := fun _ _ _ => rfl

/-! ## Examples for `Acyclic`, `ForwardEdges`, `StraightLine`, `fuelBound` -/

/-- `ForwardEdges`, positive. -/
example : ForwardEdges exDiamond := by decide
example : ForwardEdges exStraight := by decide
/-- `ForwardEdges`, negative: a back edge. -/
example : ¬ ForwardEdges exLoop3 := by decide
example : ¬ ForwardEdges exSelfLoop := by decide
/-- `ForwardEdges`, negative: an acyclic CFG that is not numbered in
topological order. -/
example : ¬ ForwardEdges exDag := by decide

/-- `Acyclic`, positive: every forward-edge CFG. -/
theorem acyclic_exDiamond : Acyclic exDiamond := acyclic_of_forwardEdges _ (by decide)
theorem acyclic_exStraight : Acyclic exStraight := acyclic_of_forwardEdges _ (by decide)

/-- `Acyclic`, positive: an acyclic CFG that is not numbered in topological
order (ranking `b0 ↦ 0`, `b2 ↦ 1`, `b1 ↦ 2`). -/
theorem acyclic_exDag : Acyclic exDag := by
  refine ⟨fun i => if i = 0 then 0 else if i = 2 then 1 else 2, ?_⟩
  intro i hi b hb _
  match i, hi with
  | 0, _ => simp [exDag, Terminator.targetsOf] at hb; subst hb; decide
  | 1, _ => simp [exDag, Terminator.targetsOf] at hb
  | 2, _ => simp [exDag, Terminator.targetsOf] at hb; subst hb; decide

/-- `Acyclic`, negative: a self-loop. -/
theorem not_acyclic_exSelfLoop : ¬ Acyclic exSelfLoop := by
  rintro ⟨r, h⟩
  have := h 0 (by decide) 0 (by decide) (by decide)
  omega

/-- `Acyclic`, negative: the back edge `b2 → b1` of the three-iteration loop. -/
theorem not_acyclic_exLoop3 : ¬ Acyclic exLoop3 := by
  rintro ⟨r, h⟩
  have h12 := h 1 (by decide) 2 (by decide) (by decide)
  have h21 := h 2 (by decide) 1 (by decide) (by decide)
  omega

theorem not_acyclic_exLoopThenAssertFalse : ¬ Acyclic exLoopThenAssertFalse := by
  rintro ⟨r, h⟩
  have h12 := h 1 (by decide) 2 (by decide) (by decide)
  have h21 := h 2 (by decide) 1 (by decide) (by decide)
  omega

/-- `Acyclic` does not constrain edges to nonexistent blocks (such a jump
panics). -/
example : Acyclic [⟨[], .goto 0⟩, ⟨[], .goto 7⟩] → False := by
  rintro ⟨r, h⟩
  have := h 0 (by decide) 0 (by decide) (by decide)
  omega
example : Acyclic [⟨[], .goto 7⟩] := ⟨id, fun i hi b hb hlt => by
  match i, hi with
  | 0, _ => simp [Terminator.targetsOf] at hb; subst hb; simp at hlt⟩

example : StraightLine exStraight := by decide
/-- `StraightLine`, negative: branches. -/
example : ¬ StraightLine exDiamond := by decide
/-- `StraightLine`, negative: an unreachable block. -/
example : ¬ StraightLine exDeadBlock := by decide
example : ¬ StraightLine [] := by decide
example : fuelBound exStraight = 5 := by decide
example : fuelBound exDiamond = 6 := by decide
example : fuelBound exLoop3 = 6 := by decide
/-- Unreachable blocks count toward `fuelBound`. -/
example : fuelBound exDeadBlock = 2 := by decide
example : fuelBound exDag = 3 := by decide

/-! ## Checking leaf lists whose path conditions are closed

When every path condition that matters is a closed term, a leaf check can be
decided at a single valuation. -/

theorem leavesProve_of_closed_check (L : List Leaf) (Q : Store → Prop) (hQ : ∀ st, Q st)
    (h : ∀ l ∈ L, l.res.tag = 0 ∨ (l.pc.closed = true ∧ ¬ holds l.pc ρ0)) :
    LeavesProve L Q := by
  intro l hl ρ hρ
  rcases h l hl with ht | ⟨hc, hn⟩
  · cases hr : l.res with
    | ok σ => simp only [SymOutcome.inst]; exact hQ _
    | panic _ => rw [hr] at ht; nomatch ht
    | outOfFuel => rw [hr] at ht; nomatch ht
  · exact absurd hρ (not_holds_of_closed l.pc hc ρ0 hn ρ)

theorem leavesProveLax_false_of_closed_check (L : List Leaf)
    (h : ∀ l ∈ L, l.res.tag = 2 ∨ (l.pc.closed = true ∧ ¬ holds l.pc ρ0)) :
    LeavesProveLax L (fun _ => False) := by
  intro l hl ρ hρ
  rcases h l hl with ht | ⟨hc, hn⟩
  · cases hr : l.res with
    | ok σ => rw [hr] at ht; nomatch ht
    | panic _ => rw [hr] at ht; nomatch ht
    | outOfFuel => trivial
  · exact absurd hρ (not_holds_of_closed l.pc hc ρ0 hn ρ)

/-! ## Value coercion versus structural equality -/

/-- `holds` coerces (`5` counts as true), while `eq` compares values
structurally (`5` is not `true`), so Boolean identities such as
`(c == true) = c` fail for non-Boolean `c`. -/
example : holds (Term.or ff (int 5)) ρ0 ∧
    (Term.eq (Term.or ff (int 5)) tt).eval ρ0 = .bool false := by decide

end Toy.SymEx
