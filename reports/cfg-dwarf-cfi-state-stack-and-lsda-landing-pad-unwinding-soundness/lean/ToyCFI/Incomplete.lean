import ToyCFI.Lemmas

/-!
# The checker is sound but not complete

A store followed by a reload through the same unknown address leaves the
register unchanged, but the abstract domain forgets the register.  The checker
then rejects a correct table.
-/

namespace Toy.CFI

theorem Reach.inv_succ {f : Func} {c : Caller} {m : Int → Int} {b k : Nat} {st : MState}
    (h : Reach f c m b (k + 1) st) :
    ∃ st' op, Reach f c m b k st' ∧ f.opAt b k = some op ∧ st = step st' op := by
  cases h with
  | next h hop _ => exact ⟨_, _, h, hop, rfl⟩

/-- `t1` anchors the CFA, a loop moves `sp`, then `fp` is stored to and reloaded
from `[sp]`.  Addresses: block 0 at 0, block 1 at 1, block 2 at 2–4. -/
def incFn : Func :=
  { blocks := [⟨[.movReg .t1 .sp], [1]⟩, ⟨[.subSp 1], [1, 2]⟩,
      ⟨[.saveAt .fp 0, .restore .fp 0, .ret], []⟩],
    layout := [0, 1, 2] }

/-- `CFA = t1 + 0` from address 1 on; every register `same`. -/
def incCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaRegister .t1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1]

/-- **Incompleteness witness.** `incCFI` is correct for `incFn`, yet `checkCFI`
rejects it: after `restore fp 0` through an unknown `sp`, the abstract state
records `fp` as unknown although it still holds the caller's value. -/
theorem checkCFI_incomplete : TableCorrect incFn incCFI ∧ checkCFI incFn incCFI = false := by
  refine ⟨?_, by decide⟩
  intro c m b k st hr
  have hs : annSoundB incFn (inferredAnn incFn) = true := by decide
  have hk := hr.lt_length
  have hb : b < 3 := blockOps_ne_nil_lt (f := incFn) (by omega)
  obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  · have hk0 : k = 0 := by simp [incFn, Func.blockOps] at hk; omega
    subst hk0
    obtain ⟨A, hA, hinv⟩ := reach_inv_inferred hs hr
    have : inferredAnn incFn 0 = some absInit := by decide
    rw [this] at hA; cases hA
    exact ⟨0, initRow, by decide, by decide, entails_sound (by decide) hinv⟩
  · have hk0 : k = 0 := by simp [incFn, Func.blockOps] at hk; omega
    subst hk0
    obtain ⟨A, hA, hinv⟩ := reach_inv_inferred hs hr
    have : inferredAnn incFn 1 = some ⟨⟨.unknown, .callerOf .fp, .callerOf .s1, .cfaRel 0⟩, []⟩ := by
      decide
    rw [this] at hA; cases hA
    exact ⟨1, ⟨.t1, 0, RegFile.const .same⟩, by decide, by decide, entails_sound (by decide) hinv⟩
  · have hk3 : k < 3 := by simpa [incFn, Func.blockOps] using hk
    have hA2 : inferredAnn incFn 2 = some ⟨⟨.unknown, .callerOf .fp, .callerOf .s1, .cfaRel 0⟩, []⟩ := by
      decide
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · obtain ⟨A, hA, hinv⟩ := reach_inv_inferred hs hr
      rw [hA2] at hA; cases hA
      exact ⟨2, ⟨.t1, 0, RegFile.const .same⟩, by decide, by decide, entails_sound (by decide) hinv⟩
    · obtain ⟨A, hA, hinv⟩ := reach_inv_inferred hs hr
      rw [hA2] at hA; cases hA
      exact ⟨3, ⟨.t1, 0, RegFile.const .same⟩, by decide, by decide, entails_sound (by decide) hinv⟩
    · -- the store/reload PC: invert twice and use the state at block 2's entry
      obtain ⟨st1, op1, hr1, hop1, rfl⟩ := Reach.inv_succ hr
      obtain ⟨st0, op0, hr0, hop0, rfl⟩ := Reach.inv_succ hr1
      simp only [incFn, Func.opAt, Func.blockOps] at hop0 hop1
      simp at hop0 hop1
      subst hop0; subst hop1
      obtain ⟨A, hA, hinv⟩ := reach_inv_inferred hs hr0
      rw [hA2] at hA; cases hA
      have ht1 := hinv.1 .t1
      have hfp := hinv.1 .fp
      have hs1 := hinv.1 .s1
      simp only [absAt, List.take_zero, absRun, List.foldl, RegFile.get, SymHolds] at ht1 hfp hs1
      refine ⟨4, ⟨.t1, 0, RegFile.const .same⟩, by decide, by decide, ?_, ?_⟩
      · simp only [cfaOf, step, RegFile.get, RegFile.set]; omega
      · intro r hr'
        simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · simp [ruleVal, step, RegFile.get, RegFile.set, RegFile.const, write, hfp]
        · simp [ruleVal, step, RegFile.get, RegFile.set, RegFile.const, hs1]

end Toy.CFI
