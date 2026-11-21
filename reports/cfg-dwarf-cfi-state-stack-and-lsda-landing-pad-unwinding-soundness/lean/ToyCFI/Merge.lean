import ToyCFI.Lemmas

/-!
# Conflicting frame states at a merge point: no correct table exists

In `mergeFn`, block 1 pushes `fp` and block 2 does not; both continue to block 3
(address 3).  A row is a function of the PC alone, and no row recovers the CFA
from both incoming frame states.
-/

namespace Toy.CFI

/-- State at block 3 reached through block 1 (`sp = CFA - 1`). -/
def mergeStVia1 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) .call) (.push .fp)

/-- State at block 3 reached through block 2 (`sp = CFA`). -/
def mergeStVia2 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) .call) .call

theorem mergeFn_reach_via1 (c : Caller) (m : Int → Int) : Reach mergeFn c m 3 0 (mergeStVia1 c m) :=
  Reach.edge (Reach.edge (b' := 1) (Reach.entry (by decide)) rfl (by decide) (by decide) (by decide))
    rfl (by decide) (by decide) (by decide)

theorem mergeFn_reach_via2 (c : Caller) (m : Int → Int) : Reach mergeFn c m 3 0 (mergeStVia2 c m) :=
  Reach.edge (Reach.edge (b' := 2) (Reach.entry (by decide)) rfl (by decide) (by decide) (by decide))
    rfl (by decide) (by decide) (by decide)

/-- Non-vacuity: block 3 is reachable along both edges, with `sp = CFA - 1` and
`sp = CFA` respectively. -/
theorem mergeFn_conflicting_states_reachable (c : Caller) (m : Int → Int) :
    Reach mergeFn c m 3 0 (mergeStVia1 c m) ∧ Reach mergeFn c m 3 0 (mergeStVia2 c m) ∧
      (mergeStVia1 c m).regs.get .sp = c.cfa - 1 ∧ (mergeStVia2 c m).regs.get .sp = c.cfa := by
  refine ⟨mergeFn_reach_via1 c m, mergeFn_reach_via2 c m, ?_, ?_⟩ <;>
    simp [mergeStVia1, mergeStVia2, step, entryState, RegFile.get, RegFile.set]

/-- `ConflictingCfaOffsetsAt f b k`: at PC `(b, k)` no register has a fixed
offset from the CFA across reachable states — for every register `r` there are
two reachable states there (possibly for different callers and memories) in
which `r - CFA` differs.  This is a semantic (concrete-state) condition; it
does not mention the abstract domain. -/
def ConflictingCfaOffsetsAt (f : Func) (b k : Nat) : Prop :=
  ∀ r : Reg, ∃ c₁ m₁ st₁ c₂ m₂ st₂,
    Reach f c₁ m₁ b k st₁ ∧ Reach f c₂ m₂ b k st₂ ∧
      st₁.regs.get r - c₁.cfa ≠ st₂.regs.get r - c₂.cfa

/-- **Impossibility (merge point).** If at some PC `(b, k)` every register's
offset from the CFA varies across reachable states
(`ConflictingCfaOffsetsAt`), then no CFI program whatsoever is correct for `f`:
a row is a function of the PC, and a register+offset CFA rule computes the CFA
only if its base register has a fixed offset from the CFA. -/
theorem no_tableCorrect_of_conflictingCfaOffsetsAt {f : Func} {b k : Nat}
    (hconf : ConflictingCfaOffsetsAt f b k) (prog : List CFIInst) : ¬ TableCorrect f prog := by
  intro htc
  obtain ⟨c₀, m₀, st₀, _, _, _, hr₀, _, _⟩ := hconf .sp
  obtain ⟨pc, R, hpc, hR, _⟩ := htc c₀ m₀ b k st₀ hr₀
  obtain ⟨c₁, m₁, st₁, c₂, m₂, st₂, hr₁, hr₂, hne⟩ := hconf R.cfaReg
  obtain ⟨R₁, hR₁, hrec₁⟩ := htc.row_at hr₁ hpc
  obtain ⟨R₂, hR₂, hrec₂⟩ := htc.row_at hr₂ hpc
  rw [hR] at hR₁ hR₂; cases hR₁; cases hR₂
  have e₁ := hrec₁.1; have e₂ := hrec₂.1
  simp only [cfaOf] at e₁ e₂
  omega

/-- Non-vacuity: in `mergeFn` the merge PC `(3, 0)` has conflicting CFA
offsets (`sp` is `CFA - 1` via block 1 and `CFA` via block 2; `fp`, `s1`, `t1`
hold caller values, whose offset from the CFA depends on the caller). -/
theorem mergeFn_conflictingCfaOffsetsAt : ConflictingCfaOffsetsAt mergeFn 3 0 := by
  intro r
  let m0 : Int → Int := fun _ => 0
  let c1 : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
  let c2 : Caller := ⟨100, ⟨0, 1, 1, 1⟩⟩
  cases r with
  | sp =>
    exact ⟨c1, m0, _, c1, m0, _, mergeFn_reach_via1 c1 m0, mergeFn_reach_via2 c1 m0,
      by simp [mergeStVia1, mergeStVia2, step, entryState, RegFile.get, RegFile.set]; omega⟩
  | fp | s1 | t1 =>
    exact ⟨c1, m0, _, c2, m0, _, mergeFn_reach_via2 c1 m0, mergeFn_reach_via2 c2 m0,
      by simp [mergeStVia2, step, entryState, RegFile.get, RegFile.set, c1, c2]⟩

/-- The concrete instance: no CFI program is correct for `mergeFn`. -/
theorem mergeFn_no_tableCorrect (prog : List CFIInst) : ¬ TableCorrect mergeFn prog :=
  no_tableCorrect_of_conflictingCfaOffsetsAt mergeFn_conflictingCfaOffsetsAt prog

/-- Positive control: when both paths push `fp` (`mergeFnBalanced`), the
generated table is correct. -/
theorem genCFI_mergeFnBalanced_tableCorrect :
    TableCorrect mergeFnBalanced (genCFI mergeFnBalanced (inferredAnn mergeFnBalanced)) :=
  checkCFI_sound (by decide)

/-- The inferred annotation of `mergeFn` is sound but not recoverable (the join
at block 3 loses the CFA). -/
theorem mergeFn_inferred_sound_not_recoverable :
    annSoundB mergeFn (inferredAnn mergeFn) = true ∧
      annRecoverableB mergeFn (inferredAnn mergeFn) = false := by decide


/-- Tightness of `ConflictingCfaOffsetsAt`: at the merge PC `(3, 0)` of
`mergeFnBalanced` the condition fails (some register keeps a fixed CFA offset)
and a correct table exists. -/
theorem no_tableCorrect_fails_without_conflictingCfaOffsetsAt :
    ¬ ConflictingCfaOffsetsAt mergeFnBalanced 3 0 ∧
      ∃ prog, TableCorrect mergeFnBalanced prog :=
  ⟨fun h => no_tableCorrect_of_conflictingCfaOffsetsAt h _ genCFI_mergeFnBalanced_tableCorrect,
    ⟨_, genCFI_mergeFnBalanced_tableCorrect⟩⟩

end Toy.CFI
