import ToyCFI.ColdBlock
import ToyCFI.Merge

/-!
# Correctness of the generator for linear layouts of CFGs
-/

namespace Toy.CFI

/-! ## The encoder lemma

`rowAt?` of the program emitted by `genCFI` at the linear address of offset `k`
of an annotated block `b` is the row derived from the abstract state there.
The induction over the layout carries the invariant `pendInv`: when the
previous block remembered a row for the current block, the top of the state
stack is the current block's entry row. -/

private theorem rowAtAux_cfaDelta (R R' : Row) (loc : Nat) (stk : List Row)
    (rest : List CFIInst) (pc : Nat) :
    rowAtAux (cfaDelta R R' ++ rest) ⟨loc, R, stk⟩ pc =
      rowAtAux rest ⟨loc, { R with cfaReg := R'.cfaReg, cfaOff := R'.cfaOff }, stk⟩ pc := by
  unfold cfaDelta
  cases R; rename_i cr co rl
  by_cases h1 : cr = R'.cfaReg <;> by_cases h2 : co = R'.cfaOff <;>
    simp [h1, h2, rowAtAux, execInst]

private def oneRuleDelta (R R' : Row) (r : Reg) : List CFIInst :=
  if R.rules.get r = R'.rules.get r then []
  else [match R'.rules.get r with | .same => .restore r | .offset k => .offset r k]

private theorem ruleDelta_eq (R R' : Row) :
    ruleDelta R R' =
      oneRuleDelta R R' .sp ++ oneRuleDelta R R' .fp ++
        oneRuleDelta R R' .s1 ++ oneRuleDelta R R' .t1 := by
  unfold ruleDelta Reg.all oneRuleDelta
  by_cases hsp : R.rules.get .sp = R'.rules.get .sp <;>
  by_cases hfp : R.rules.get .fp = R'.rules.get .fp <;>
  by_cases hs1 : R.rules.get .s1 = R'.rules.get .s1 <;>
  by_cases ht1 : R.rules.get .t1 = R'.rules.get .t1 <;>
    simp [hsp, hfp, hs1, ht1, List.filterMap] <;> repeat constructor

private theorem rowAtAux_oneRuleDelta (cur R R' : Row) (r : Reg)
    (hcur : cur.rules.get r = R.rules.get r) (loc : Nat) (stk : List Row)
    (rest : List CFIInst) (pc : Nat) :
    rowAtAux (oneRuleDelta R R' r ++ rest) ⟨loc, cur, stk⟩ pc =
      rowAtAux rest ⟨loc, { cur with rules := cur.rules.set r (R'.rules.get r) }, stk⟩ pc := by
  unfold oneRuleDelta
  by_cases hr : R.rules.get r = R'.rules.get r
  · have hsame : cur.rules.set r (R'.rules.get r) = cur.rules := by
      rw [← hr, ← hcur]
      cases cur.rules; cases r <;> rfl
    simp [hr, hsame]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hr)]
    cases cur; cases h' : R'.rules.get r <;> simp [rowAtAux, execInst, initRow]

private theorem rowAtAux_delta (R R' : Row) (loc : Nat) (stk : List Row)
    (rest : List CFIInst) (pc : Nat) :
    rowAtAux (delta R R' ++ rest) ⟨loc, R, stk⟩ pc = rowAtAux rest ⟨loc, R', stk⟩ pc := by
  unfold delta
  rw [List.append_assoc, rowAtAux_cfaDelta, ruleDelta_eq]
  simp only [List.append_assoc]
  rw [rowAtAux_oneRuleDelta _ R R' .sp (by rfl)]
  rw [rowAtAux_oneRuleDelta _ R R' .fp (by rfl)]
  rw [rowAtAux_oneRuleDelta _ R R' .s1 (by rfl)]
  rw [rowAtAux_oneRuleDelta _ R R' .t1 (by rfl)]
  have hEq : Row.mk R'.cfaReg R'.cfaOff
      ((((R.rules.set .sp (R'.rules.get .sp)).set .fp (R'.rules.get .fp)).set .s1
        (R'.rules.get .s1)).set .t1 (R'.rules.get .t1)) = R' := by
    cases R'; rename_i cr co rl; cases rl; rfl
  rw [hEq]

private theorem rowAtAux_emitRows :
    ∀ (Rs : List Row) (cur : Row) (loc : Nat) (stk : List Row) (rest : List CFIInst) (pc : Nat),
      loc ≤ pc →
      rowAtAux (emitRows cur Rs ++ rest) ⟨loc, cur, stk⟩ pc =
        if pc - loc < Rs.length then Rs[pc - loc]?
        else rowAtAux rest ⟨loc + Rs.length, (Rs.getLast?).getD cur, stk⟩ pc
  | [], cur, loc, stk, rest, pc, _ => by simp [emitRows]
  | R :: Rs, cur, loc, stk, rest, pc, hle => by
    simp only [emitRows, List.append_assoc]
    rw [rowAtAux_delta]
    simp only [List.cons_append, List.nil_append, rowAtAux]
    by_cases hlt : pc < loc + 1
    · have h0 : pc - loc = 0 := by omega
      simp [hlt, h0]
    · have hle' : loc + 1 ≤ pc := by omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h hlt), rowAtAux_emitRows Rs R (loc + 1) stk rest pc hle']
      by_cases h2 : pc - (loc + 1) < Rs.length
      · have h3 : pc - loc < (R :: Rs).length := by simp; omega
        have hidx : pc - loc = (pc - (loc + 1)) + 1 := by omega
        rw [ite_eq_left_iff.mpr (fun h => absurd h2 h), ite_eq_left_iff.mpr (fun h => absurd h3 h)]
        simp [hidx]
      · have h3 : ¬ (pc - loc < (R :: Rs).length) := by simp; omega
        have hadd : loc + 1 + Rs.length = loc + (R :: Rs).length := by simp; omega
        have hlast : (Rs.getLast?).getD R = ((R :: Rs).getLast?).getD cur := by
          cases Rs <;> rfl
        rw [ite_eq_right_iff.mpr (fun h => absurd h h2), ite_eq_right_iff.mpr (fun h => absurd h h3), hadd, hlast]

private theorem startIn_ge (f : Func) :
    ∀ (lay : List Nat) (acc b pc0 : Nat), f.startIn lay acc b = some pc0 → acc ≤ pc0
  | [], _, _, _, h => by simp [Func.startIn] at h
  | x :: xs, acc, b, pc0, h => by
    simp only [Func.startIn] at h
    by_cases hxb : x = b
    · simp [hxb] at h; omega
    · simp [hxb] at h
      exact Nat.le_trans (Nat.le_add_right _ _) (startIn_ge f xs _ b pc0 h)

private theorem startIn_of_mem (f : Func) :
    ∀ (lay : List Nat) (acc b : Nat), b ∈ lay → ∃ pc0, f.startIn lay acc b = some pc0
  | [], _, _, h => by cases h
  | x :: xs, acc, b, h => by
    simp only [Func.startIn]
    by_cases hxb : x = b
    · exact ⟨acc, by simp [hxb]⟩
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact absurd rfl hxb
      · simpa [hxb] using startIn_of_mem f xs (acc + (f.blockOps x).length) b hmem

private def pendInv (f : Func) (ann : Ann) (lay : List Nat) (pend : Bool) (stk : List Row) : Prop :=
  if pend then ∃ E rest, lay.head?.bind (entryRow f ann) = some E ∧ stk = E :: rest else True

private theorem rowAtAux_genBlocks (f : Func) (ann : Ann) :
    ∀ (lay : List Nat) (cur : Row) (pend : Bool) (loc : Nat) (stk : List Row)
      (b k pc0 : Nat) (A : AState),
      pendInv f ann lay pend stk →
      f.startIn lay loc b = some pc0 →
      ann b = some A →
      k < (f.blockOps b).length →
      rowAtAux (genBlocks f ann cur pend lay) ⟨loc, cur, stk⟩ (pc0 + k) =
        some (rowOf (absAt f A b k))
  | [], _, _, _, _, _, _, _, _, _, hst, _, _ => by simp [Func.startIn] at hst
  | x :: xs, cur, pend, loc, stk, b, k, pc0, A, hinv, hst, hA, hk => by
    simp only [Func.startIn] at hst
    by_cases hxb : x = b
    · subst hxb
      simp only [ite_true, Option.some.injEq] at hst
      subst hst
      obtain ⟨n, hlen⟩ : ∃ n, (f.blockOps x).length = n + 1 :=
        ⟨(f.blockOps x).length - 1, by omega⟩
      have hbrEq : blockRows f ann x =
          some (rowOf (absAt f A x 0) :: (List.range n).map (fun i => rowOf (absAt f A x (i + 1)))) := by
        simp [blockRows, hA, hlen, List.range_succ_eq_map]
      let E := rowOf (absAt f A x 0)
      let Rs := (List.range n).map (fun i => rowOf (absAt f A x (i + 1)))
      have hent : entryRow f ann x = some E := by simp [entryRow, hbrEq, E]
      simp only [genBlocks, hbrEq]
      have hpre : ∃ stk', rowAtAux ((if pend then [CFIInst.restoreState] else delta cur E) ++
          (if decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E)
           then [CFIInst.rememberState] else []) ++ emitRows E (E :: Rs) ++
          genBlocks f ann (((E :: Rs).getLast?).getD E)
            (decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E)) xs)
          ⟨loc, cur, stk⟩ (loc + k) =
          rowAtAux (emitRows E (E :: Rs) ++
            genBlocks f ann (((E :: Rs).getLast?).getD E)
              (decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E)) xs)
            ⟨loc, E, stk'⟩ (loc + k) := by
        cases pend with
        | false =>
          simp only [Bool.false_eq_true, ite_false, List.append_assoc]
          rw [rowAtAux_delta]
          by_cases hrem : decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E) = true
          · exact ⟨E :: stk, by simp [hrem, rowAtAux, execInst]⟩
          · exact ⟨stk, by simp [hrem]⟩
        | true =>
          obtain ⟨E', restStk, hEE', hstk⟩ : ∃ E' restStk, entryRow f ann x = some E' ∧ stk = E' :: restStk := by
            simpa [pendInv, Option.bind] using hinv
          rw [hent] at hEE'; injection hEE' with hEE'; subst hEE'; subst hstk
          by_cases hrem : decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E) = true
          · exact ⟨E :: restStk, by simp [hrem, rowAtAux, execInst]⟩
          · exact ⟨restStk, by simp [hrem, rowAtAux, execInst]⟩
      obtain ⟨stk', hpreEq⟩ := hpre
      rw [hpreEq, rowAtAux_emitRows (E :: Rs) E loc stk' _ (loc + k) (Nat.le_add_right _ _)]
      have hsub : loc + k - loc = k := by omega
      have hklt : loc + k - loc < (E :: Rs).length := by simp [Rs]; omega
      rw [ite_eq_left_iff.mpr (fun h => absurd hklt h), hsub]
      cases k with
      | zero => rfl
      | succ i =>
        have hi : i < n := by omega
        simp [Rs, hi]
    · simp only [hxb, ite_false] at hst
      have hge : loc + (f.blockOps x).length ≤ pc0 := startIn_ge f xs _ b pc0 hst
      cases hbr : blockRows f ann x with
      | none =>
        have hpfalse : pend = false := by
          cases pend with
          | false => rfl
          | true => simp [pendInv, Option.bind, entryRow, hbr] at hinv
        subst hpfalse
        simp only [genBlocks, hbr, List.cons_append, rowAtAux]
        have hnotlt : ¬ (pc0 + k < loc + (f.blockOps x).length) := by omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnotlt)]
        exact rowAtAux_genBlocks f ann xs cur false (loc + (f.blockOps x).length) stk b k pc0 A
          trivial hst hA hk
      | some rows =>
        cases rows with
        | nil =>
          have hpfalse : pend = false := by
            cases pend with
            | false => rfl
            | true => simp [pendInv, Option.bind, entryRow, hbr] at hinv
          subst hpfalse
          have hlen0 : (f.blockOps x).length = 0 := by
            cases hAx : ann x with
            | none => simp [blockRows, hAx] at hbr
            | some Ax => simp [blockRows, hAx] at hbr; simp [hbr]
          simp only [genBlocks, hbr]
          rw [hlen0, Nat.add_zero] at hst
          exact rowAtAux_genBlocks f ann xs cur false loc stk b k pc0 A trivial hst hA hk
        | cons E Rs =>
          have hent : entryRow f ann x = some E := by simp [entryRow, hbr]
          have hlenEq : (E :: Rs).length = (f.blockOps x).length := by
            cases hAx : ann x with
            | none => simp [blockRows, hAx] at hbr
            | some Ax =>
              simp only [blockRows, hAx, Option.map_some, Option.some.injEq] at hbr
              have := congrArg List.length hbr
              simpa using this.symm
          let rem := decide (xs.head?.bind (entryRow f ann) = some E ∧ ((E :: Rs).getLast?).getD E ≠ E)
          simp only [genBlocks, hbr]
          have hstep : ∃ stk',
              pendInv f ann xs rem stk' ∧
              rowAtAux ((if pend then [CFIInst.restoreState] else delta cur E) ++
                (if rem then [CFIInst.rememberState] else []) ++ emitRows E (E :: Rs) ++
                genBlocks f ann (((E :: Rs).getLast?).getD E) rem xs)
                ⟨loc, cur, stk⟩ (pc0 + k) =
              rowAtAux (emitRows E (E :: Rs) ++
                genBlocks f ann (((E :: Rs).getLast?).getD E) rem xs)
                ⟨loc, E, stk'⟩ (pc0 + k) := by
            cases pend with
            | false =>
              simp only [Bool.false_eq_true, ite_false, List.append_assoc]
              rw [rowAtAux_delta]
              by_cases hrem : rem = true
              · have he2 : xs.head?.bind (entryRow f ann) = some E :=
                  ((decide_eq_true_eq).mp hrem).1
                refine ⟨E :: stk, ?_, by simp [hrem, rowAtAux, execInst]⟩
                simp [pendInv, hrem, he2]
              · have hremF : rem = false := Bool.eq_false_iff.mpr hrem
                exact ⟨stk, by simp [pendInv, hremF], by simp [hremF]⟩
            | true =>
              obtain ⟨E', restStk, hEE', hstk⟩ : ∃ E' restStk, entryRow f ann x = some E' ∧ stk = E' :: restStk := by
                simpa [pendInv, Option.bind] using hinv
              rw [hent] at hEE'; injection hEE' with hEE'; subst hEE'; subst hstk
              by_cases hrem : rem = true
              · have he2 : xs.head?.bind (entryRow f ann) = some E :=
                  ((decide_eq_true_eq).mp hrem).1
                refine ⟨E :: restStk, ?_, by simp [hrem, rowAtAux, execInst]⟩
                simp [pendInv, hrem, he2]
              · have hremF : rem = false := Bool.eq_false_iff.mpr hrem
                exact ⟨restStk, by simp [pendInv, hremF], by simp [hremF, rowAtAux, execInst]⟩
          obtain ⟨stk', hinv', hstepEq⟩ := hstep
          rw [hstepEq, rowAtAux_emitRows (E :: Rs) E loc stk' _ (pc0 + k) (by omega)]
          have hnotlt : ¬ (pc0 + k - loc < (E :: Rs).length) := by omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h hnotlt), hlenEq]
          exact rowAtAux_genBlocks f ann xs (((E :: Rs).getLast?).getD E) rem
            (loc + (f.blockOps x).length) stk' b k pc0 A hinv' hst hA hk


/-- **Encoder lemma.** At the linear address of every PC of every annotated
block that appears in the layout, the program emitted by `genCFI` has exactly
the row derived from the abstract state at that PC. -/
theorem rowAt_genCFI_eq_rowOf {f : Func} {ann : Ann} {b k pc0 : Nat} {A : AState}
    (hst : f.blockStart b = some pc0) (hA : ann b = some A) (hk : k < (f.blockOps b).length) :
    rowAt? (genCFI f ann) (pc0 + k) = some (rowOf (absAt f A b k)) :=
  rowAtAux_genBlocks f ann f.layout initRow false 0 [] b k pc0 A trivial hst hA hk

/-- **Generator correctness (general case).** If every non-empty block appears
in the layout, the annotation is sound (block `0`'s state is implied by the
entry state, and along every CFG edge a block's abstract exit state is at least
as precise as the successor's annotated entry state — one entry frame state per
block, shared by all incoming edges), and at every PC of every annotated block
the abstract state is recoverable (some row is entailed by it; see
`annRecoverableB_iff`), then the program emitted by `genCFI` (row deltas inside
blocks; at a layout boundary whose inherited row differs from the entry row,
`rememberState` at the start of the layout predecessor plus `restoreState`, or
an explicit re-definition) is correct. -/
theorem genCFI_tableCorrect_of_sound_recoverable_annotation (f : Func) (ann : Ann)
    (hcover : LayoutCovers f) (hsound : annSoundB f ann = true)
    (hrec : annRecoverableB f ann = true) : TableCorrect f (genCFI f ann) := by
  apply checkWith_sound (ann := ann)
  simp only [checkWith, hsound, Bool.true_and, List.all_eq_true, List.mem_range]
  intro b hb
  unfold rowsOK
  cases hA : ann b with
  | none => rfl
  | some A =>
    simp only [List.all_eq_true, List.mem_range]
    intro k hk
    obtain ⟨pc0, hpc0⟩ := startIn_of_mem f f.layout 0 b (hcover b (by omega))
    have hpc : f.pcOf b k = some (pc0 + k) := by simp [Func.pcOf, Func.blockStart, hpc0]
    have hrow : rowAt? (genCFI f ann) (pc0 + k) = some (rowOf (absAt f A b k)) :=
      rowAt_genCFI_eq_rowOf hpc0 hA hk
    simp only [annRecoverableB, List.all_eq_true, List.mem_range] at hrec
    have hent := hrec b hb
    simp only [hA, List.all_eq_true, List.mem_range] at hent
    simp [hpc, hrow, entails_rowOf_of_stateRecoverableB (hent k hk)]

theorem layoutCovers_of_layout_range {f : Func} (h : ∀ b, b < f.blocks.length → b ∈ f.layout) :
    LayoutCovers f := fun b hb => h b (blockOps_ne_nil_lt hb)

theorem coldFn_layoutCovers : LayoutCovers coldFn :=
  layoutCovers_of_layout_range (by decide)

/-- Non-vacuity: `coldFn` with its inferred annotation satisfies all hypotheses
(and its generated program, which uses `rememberState`/`restoreState`, is
correct: `genCFI_coldFn_tableCorrect`). -/
theorem genCFI_hypotheses_hold_coldFn :
    LayoutCovers coldFn ∧ annSoundB coldFn (inferredAnn coldFn) = true ∧
      annRecoverableB coldFn (inferredAnn coldFn) = true :=
  ⟨coldFn_layoutCovers, by decide, by decide⟩

/-- An unsound annotation of `coldFn`: it claims the cold block is entered with
no frame (the entry state). -/
def coldBadAnn : Ann
  | 0 => some absInit
  | 1 => inferredAnn coldFn 1
  | 2 => some absInit
  | _ => none

/-- Tightness of soundness: `coldBadAnn` is recoverable and the layout covers all
blocks, but the annotation is unsound and the generated table is incorrect. -/
theorem genCFI_incorrect_without_annSound :
    LayoutCovers coldFn ∧ annSoundB coldFn coldBadAnn = false ∧
      annRecoverableB coldFn coldBadAnn = true ∧ ¬ TableCorrect coldFn (genCFI coldFn coldBadAnn) := by
  refine ⟨coldFn_layoutCovers, by decide, by decide, ?_⟩
  let c : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
  refine not_tableCorrect_of_bad_row (coldFn_reach_cold c (fun _ => 0)) (pc := 6) (by decide)
    (R := initRow) (by decide) ?_
  simp only [cfaOf, coldStCold_regs, initRow, RegFile.get]
  decide

/-- Tightness of recoverability: `mergeFn` with its inferred annotation has a
covering layout and a sound annotation, but no table (in particular not the
generated one) is correct. -/
theorem genCFI_incorrect_without_annRecoverable :
    LayoutCovers mergeFn ∧ annSoundB mergeFn (inferredAnn mergeFn) = true ∧
      annRecoverableB mergeFn (inferredAnn mergeFn) = false ∧
      ¬ TableCorrect mergeFn (genCFI mergeFn (inferredAnn mergeFn)) :=
  ⟨layoutCovers_of_layout_range (by decide), by decide, by decide,
    mergeFn_no_tableCorrect _⟩

/-- `coldFn`'s blocks with the cold block missing from the layout. -/
def coldFnMissing : Func := { blocks := coldBlocks, layout := [0, 1] }

/-- Tightness of layout coverage: the annotation is sound and recoverable, but a
reachable block has no address, so no table is correct. -/
theorem genCFI_incorrect_without_layoutCovers :
    ¬ LayoutCovers coldFnMissing ∧ annSoundB coldFnMissing (inferredAnn coldFnMissing) = true ∧
      annRecoverableB coldFnMissing (inferredAnn coldFnMissing) = true ∧
      ¬ TableCorrect coldFnMissing (genCFI coldFnMissing (inferredAnn coldFnMissing)) := by
  refine ⟨fun h => ?_, by decide, by decide, fun h => ?_⟩
  · have := h 2 (by decide)
    simp [coldFnMissing] at this
  · have hr : Reach coldFnMissing ⟨0, ⟨0, 0, 0, 0⟩⟩ (fun _ => 0) 2 0
        (coldStCold ⟨0, ⟨0, 0, 0, 0⟩⟩ (fun _ => 0)) :=
      Reach.edge (Reach.next (Reach.next (Reach.entry (by decide)) rfl (by decide)) rfl
        (by decide)) rfl (by decide) (by decide) (by decide)
    obtain ⟨pc, R, hpc, -, -⟩ := h _ _ _ _ _ hr
    have : coldFnMissing.pcOf 2 0 = none := by decide
    rw [this] at hpc
    cases hpc

/-- Tightness of soundness for `reach_inv_of_annSound`: with the unsound
`coldBadAnn`, a reachable state at the cold block violates the annotated
abstract state. -/
theorem reach_inv_fails_without_annSound :
    annSoundB coldFn coldBadAnn = false ∧
      ∃ c m st A, Reach coldFn c m 2 0 st ∧ coldBadAnn 2 = some A ∧
        ¬ Inv (absAt coldFn A 2 0) c st := by
  refine ⟨by decide, ⟨0, ⟨0, 0, 0, 0⟩⟩, fun _ => 0, _, absInit,
    coldFn_reach_cold _ _, rfl, fun h => ?_⟩
  have := h.1 .sp
  simp only [absAt, List.take_zero, absRun, List.foldl, absInit, RegFile.get, SymHolds,
    coldStCold_regs] at this
  omega

end Toy.CFI
