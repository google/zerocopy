-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.LinearArith
public import Anneal.PTree

public section

/-!
# Tree-Indexed `CutStep` Replay (`Anneal.LinearArithIndexed`)

`Anneal.LinearArith` replays a `CutStep` certificate against a `List` of
hypothesis rows and a reverse-order `List` of derived rows. Each `.hyp idx`,
`.comb s1 _ s2 _`, or `.divCut _ s` step locates its operands by walking those
lists, so a step that cites an early row costs time linear in the number of
rows. A certificate with `N` steps that keeps citing early rows therefore
costs `O(N^2)` reductions when its acceptance is proved by `rfl`.

Rows are also passed between steps as the unevaluated terms that computed
them. Elaborating such a `rfl` proof re-reduces a row's term at every place it
is used, so a certificate that cites a derived row from two later steps (or
twice in one `.comb`) duplicates that work at each level of the derivation,
and the elaboration cost grows exponentially with derivation depth.

This module provides `checkIntCutGoalIdx` and `checkNatCutGoalIdx`, which
accept the same goals and certificates but:

- store hypothesis and derived rows in an `Anneal.PTree.PTree` keyed by
  `Anneal.PTree.natToPosAt`, so a lookup forces `O(log idx)` trie nodes and
  the long certificate above costs `O(N log N)` trie steps; and
- reduce each row to constructors and numerals (`forceRow`) when it is
  pushed, so later steps share the evaluated row instead of its recipe.

Soundness (`checkIntCutGoalIdx_sound`, `checkNatCutGoalIdx_sound`) needs only
that every row stored in a trie holds; it does not depend on how indices map to
keys. Step semantics (`stepCutWith`) are those of `Anneal.LinearArith.stepCut`
with the two row lookups abstracted, so caps, divisibility checks, and
fail-closed behavior are unchanged.
-/

namespace Anneal.LinearArith

/-! ## 1. Generic Step Semantics -/

/-- `stepCut` with hypothesis lookup `getHyp` and derived-row lookup
`getRow` abstracted: `stepCut hyps derived` is
`stepCutWith (listGet? hyps) derived.get?`. -/
@[expose] noncomputable def stepCutWith (getHyp getRow : Nat → Option SparseIneq) :
    CutStep → Option SparseIneq
  | .hyp idx =>
    match getHyp idx with
    | none => none
    | some r =>
      match rowWithinCap r with
      | true => some r
      | false => none
  | .comb s1 k1 s2 k2 =>
    match Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => none
    | true =>
      match getRow s1, getRow s2 with
      | some r1, some r2 =>
        match rowWithinCap r1 && rowWithinCap r2 with
        | false => none
        | true =>
          let t := addTerms (scaleTermsNat k1 r1.terms)
            (scaleTermsNat k2 r2.terms)
          let r :=
            SInt.add (SInt.scaleNat k1 r1.rhs) (SInt.scaleNat k2 r2.rhs)
          let outRow : SparseIneq := ⟨t, r⟩
          match rowWithinCap outRow with
          | true => some outRow
          | false => none
      | _, _ => none
  | .divCut g s =>
    match Nat.ble 1 g && Nat.ble g magCap128 with
    | false => none
    | true =>
      match getRow s with
      | none => none
      | some row =>
        match rowWithinCap row with
        | false => none
        | true =>
          match allDivisible g row.terms with
          | false => none
          | true =>
            let outRow : SparseIneq :=
              ⟨divTerms g row.terms, SInt.fdiv row.rhs g⟩
            match rowWithinCap outRow with
            | true => some outRow
            | false => none

/-- Any row produced by `stepCutWith` holds whenever every row returned by
`getHyp` and `getRow` holds. -/
theorem stepCutWith_sound {env : List Int}
    {getHyp getRow : Nat → Option SparseIneq} {st : CutStep} {out : SparseIneq}
    (hHyp : ∀ (i : Nat) (r : SparseIneq), getHyp i = some r → r.holds env)
    (hRow : ∀ (i : Nat) (r : SparseIneq), getRow i = some r → r.holds env)
    (hStep : stepCutWith getHyp getRow st = some out) :
    out.holds env := by
  cases st with
  | hyp idx =>
    dsimp [stepCutWith] at hStep
    revert hStep
    cases hGet : getHyp idx with
    | none => intro h; nomatch h
    | some r =>
      dsimp
      cases rowWithinCap r with
      | false => intro h; nomatch h
      | true =>
        intro hEq
        injection hEq with hOut
        rw [← hOut]
        exact hHyp idx r hGet
  | comb s1 k1 s2 k2 =>
    dsimp [stepCutWith] at hStep
    revert hStep
    cases Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hg1 : getRow s1 with
      | none => intro h; nomatch h
      | some r1 =>
        cases hg2 : getRow s2 with
        | none => intro h; nomatch h
        | some r2 =>
          dsimp
          cases rowWithinCap r1 && rowWithinCap r2 with
          | false => intro h; nomatch h
          | true =>
            dsimp
            cases rowWithinCap ⟨addTerms (scaleTermsNat k1 r1.terms)
                (scaleTermsNat k2 r2.terms),
                SInt.add (SInt.scaleNat k1 r1.rhs)
                  (SInt.scaleNat k2 r2.rhs)⟩ with
            | false => intro h; nomatch h
            | true =>
              intro hEq
              injection hEq with hOut
              rw [← hOut]
              dsimp [SparseIneq.holds]
              rw [evalTerms_add, evalTerms_scaleNat, evalTerms_scaleNat,
                  sint_add_toInt, sint_scaleNat_toInt, sint_scaleNat_toInt]
              exact int_add_le_add
                (int_mul_nat_le_mul_nat k1 (hRow s1 r1 hg1))
                (int_mul_nat_le_mul_nat k2 (hRow s2 r2 hg2))
  | divCut g s =>
    dsimp [stepCutWith] at hStep
    revert hStep
    cases hg : Nat.ble 1 g && Nat.ble g magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hGet : getRow s with
      | none => intro h; nomatch h
      | some row =>
        dsimp
        cases rowWithinCap row with
        | false => intro h; nomatch h
        | true =>
          dsimp
          cases hDiv : allDivisible g row.terms with
          | false => intro h; nomatch h
          | true =>
            dsimp
            cases rowWithinCap ⟨divTerms g row.terms,
                SInt.fdiv row.rhs g⟩ with
            | false => intro h; nomatch h
            | true =>
              intro hEq
              injection hEq with hOut
              rw [← hOut]
              dsimp [SparseIneq.holds]
              have hg1 : Nat.ble 1 g = true := by
                cases hb : Nat.ble 1 g with
                | true => rfl
                | false => rw [hb] at hg; nomatch hg
              have hgPos : 0 < g := Nat.le_of_ble_eq_true hg1
              have hRowS := hRow s row hGet
              dsimp [SparseIneq.holds] at hRowS
              rw [← evalTerms_divTerms env g hgPos row.terms hDiv] at hRowS
              exact chvatal_gomory_floor_sound hgPos hRowS

/-! ## 2. Value Forcing

A derived row reaches later steps as the unevaluated term that computed it,
and elaborating a `rfl` proof re-reduces that term at every use. These
continuation-passing helpers case-split a value down to constructors and
numerals before handing it to `k`. -/

/-- Passes `v` to `k` after reducing it to a numeral. -/
@[expose] def forceNat {β : Type} (v : Nat) (k : Nat → β) : β :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem forceNat_eq {β : Type} (v : Nat) (k : Nat → β) : forceNat v k = k v := by
  cases v <;> rfl

/-- Passes `s` to `k` after reducing its sign and magnitude. -/
@[expose] def forceSInt {β : Type} (s : SInt) (k : SInt → β) : β :=
  match s with
  | ⟨true, m⟩ => forceNat m fun m' => k ⟨true, m'⟩
  | ⟨false, m⟩ => forceNat m fun m' => k ⟨false, m'⟩

theorem forceSInt_eq {β : Type} (s : SInt) (k : SInt → β) :
    forceSInt s k = k s := by
  cases s with
  | mk neg mag =>
    cases neg <;> dsimp only [forceSInt] <;> rw [forceNat_eq]

/-- Passes `ts` to `k` after reducing its spine, indices, and
coefficients. -/
@[expose] noncomputable def forceTerms {β : Type} :
    List (Nat × SInt) → (List (Nat × SInt) → β) → β
  | [], k => k []
  | (v, c) :: rest, k =>
    forceNat v fun v' =>
      forceSInt c fun c' =>
        forceTerms rest fun rest' => k ((v', c') :: rest')

theorem forceTerms_eq {β : Type} :
    ∀ (ts : List (Nat × SInt)) (k : List (Nat × SInt) → β),
      forceTerms ts k = k ts
  | [], _ => rfl
  | (v, c) :: rest, k => by
    dsimp only [forceTerms]
    rw [forceNat_eq, forceSInt_eq, forceTerms_eq rest]

/-- Passes `r` to `k` after forcing its terms and RHS. -/
@[expose] noncomputable def forceRow {β : Type} (r : SparseIneq)
    (k : SparseIneq → β) : β :=
  forceTerms r.terms fun t => forceSInt r.rhs fun s => k ⟨t, s⟩

theorem forceRow_eq {β : Type} (r : SparseIneq) (k : SparseIneq → β) :
    forceRow r k = k r := by
  dsimp only [forceRow]
  rw [forceTerms_eq, forceSInt_eq]

/-! ## 3. Tree-Indexed Row Log (`IndexedRows`) -/

/-- Bit width of row keys. `rowKey` is injective on indices below
`2 ^ rowKeyDepth - 1`; soundness does not rely on injectivity. -/
@[expose] def rowKeyDepth : Nat := 64

/-- Trie key for forward row index `idx`, computed in `O(log idx)` steps. -/
@[expose] def rowKey (idx : Nat) : Anneal.PTree.Pos :=
  Anneal.PTree.natToPosAt rowKeyDepth idx

/-- Append-only row log with `O(log N)` indexed lookup. `rows` maps
`rowKey i` to the `i`-th pushed row, `len` counts pushes, and `last` caches the
most recent row. -/
structure IndexedRows where
  rows : Anneal.PTree.PTree SparseIneq
  len  : Nat
  last : Option SparseIneq

@[expose] def IndexedRows.empty : IndexedRows :=
  ⟨Anneal.PTree.PTree.empty, 0, none⟩

/-- Pushes `r` after forcing `d.len` and `r` to values (`forceNat`,
`forceRow`). -/
@[expose] noncomputable def IndexedRows.push (d : IndexedRows) (r : SparseIneq) :
    IndexedRows :=
  forceNat d.len fun n =>
    forceRow r fun r' => ⟨d.rows.set (rowKey n) r', n + 1, some r'⟩

/-- Forward-indexed lookup, failing closed (`none`) when `idx ≥ len`. -/
@[expose] noncomputable def IndexedRows.get? (d : IndexedRows) (idx : Nat) :
    Option SparseIneq :=
  match Nat.blt idx d.len with
  | false => none
  | true => d.rows.get (rowKey idx)

/-- Pushes `rs` in order, so `rs[i]` lands at index `d.len + i`. -/
@[expose] noncomputable def IndexedRows.pushAll :
    IndexedRows → List SparseIneq → IndexedRows
  | d, [] => d
  | d, r :: rs => IndexedRows.pushAll (d.push r) rs

/-- Every row stored in `d` (including `d.last`) holds under `env`. -/
@[expose] def IndexedRows.Holds (env : List Int) (d : IndexedRows) : Prop :=
  (∀ (k : Anneal.PTree.Pos) (r : SparseIneq), d.rows.get k = some r →
    r.holds env) ∧
  (∀ r : SparseIneq, d.last = some r → r.holds env)

theorem indexedRows_empty_holds (env : List Int) :
    IndexedRows.empty.Holds env :=
  ⟨fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem indexedRows_push_holds {env : List Int} {d : IndexedRows}
    {r : SparseIneq} (hD : d.Holds env) (hR : r.holds env) :
    (d.push r).Holds env := by
  constructor
  · intro k r' hGet
    dsimp only [IndexedRows.push] at hGet
    rw [forceNat_eq, forceRow_eq] at hGet
    cases hk : Anneal.PTree.Pos.beq (rowKey d.len) k with
    | true =>
      have hEq := Anneal.PTree.pos_eq_of_beq hk
      rw [← hEq, Anneal.PTree.ptree_get_set_same] at hGet
      injection hGet with hr
      rw [← hr]
      exact hR
    | false =>
      have hNe : rowKey d.len ≠ k := by
        intro hEq
        rw [hEq, Anneal.PTree.posBeq_refl] at hk
        nomatch hk
      rw [Anneal.PTree.ptree_get_set_other _ _ _ _ hNe] at hGet
      exact hD.1 k r' hGet
  · intro r' hLast
    dsimp only [IndexedRows.push] at hLast
    rw [forceNat_eq, forceRow_eq] at hLast
    injection hLast with hr
    rw [← hr]
    exact hR

theorem indexedRows_get_holds {env : List Int} {d : IndexedRows}
    (hD : d.Holds env) :
    ∀ (idx : Nat) (r : SparseIneq), d.get? idx = some r → r.holds env := by
  intro idx r hGet
  dsimp [IndexedRows.get?] at hGet
  cases hLt : Nat.blt idx d.len with
  | false => rw [hLt] at hGet; nomatch hGet
  | true =>
    rw [hLt] at hGet
    exact hD.1 (rowKey idx) r hGet

theorem indexedRows_pushAll_holds {env : List Int} :
    ∀ (d : IndexedRows) (rs : List SparseIneq),
      d.Holds env → AllHolds env rs → (d.pushAll rs).Holds env
  | _, [], hD, _ => hD
  | _, r :: rs, hD, hAll =>
    indexedRows_pushAll_holds _ rs
      (indexedRows_push_holds hD (hAll r (List.Mem.head rs)))
      (fun y hy => hAll y (List.Mem.tail r hy))

/-! ## 4. Tree-Indexed Refutation Checker -/

@[expose] noncomputable def runCutStepsIdx (hyps : IndexedRows) :
    List CutStep → IndexedRows → Option IndexedRows
  | [], acc => some acc
  | st :: rest, acc =>
    match stepCutWith hyps.get? acc.get? st with
    | none => none
    | some next => runCutStepsIdx hyps rest (acc.push next)

theorem runCutStepsIdx_sound {env : List Int} {hyps : IndexedRows}
    (hHyps : hyps.Holds env) :
    ∀ (steps : List CutStep) (acc res : IndexedRows),
      acc.Holds env → runCutStepsIdx hyps steps acc = some res → res.Holds env
  | [], acc, res, hAcc, hRun => by
    dsimp [runCutStepsIdx] at hRun
    injection hRun with hEq
    rw [← hEq]
    exact hAcc
  | st :: rest, acc, res, hAcc, hRun => by
    dsimp [runCutStepsIdx] at hRun
    revert hRun
    cases hSt : stepCutWith hyps.get? acc.get? st with
    | none => intro h; nomatch h
    | some next =>
      intro hRest
      have hNext := stepCutWith_sound (indexedRows_get_holds hHyps)
        (indexedRows_get_holds hAcc) hSt
      exact runCutStepsIdx_sound hHyps rest (acc.push next) res
        (indexedRows_push_holds hAcc hNext) hRest

/-- `checkCutRefute` with hypothesis and derived rows stored in
`IndexedRows`: accepts iff every hypothesis is within `magCap128`, every step
succeeds, and the last derived row is `0 ≤ rhs` with `rhs < 0`. -/
@[expose] noncomputable def checkCutRefuteIdx (hyps : List SparseIneq)
    (steps : List CutStep) : Bool :=
  match rowsWithinCap hyps with
  | false => false
  | true =>
    match runCutStepsIdx (IndexedRows.empty.pushAll hyps) steps
        IndexedRows.empty with
    | none => false
    | some derived =>
      match derived.last with
      | none => false
      | some last =>
        match last.terms with
        | [] => last.rhs.isStrictlyNeg
        | _ :: _ => false

/-- A row with no terms and a strictly negative `rhs` (`0 ≤ rhs < 0`) never
holds. -/
theorem emptyRow_strictlyNeg_not_holds {env : List Int} {row : SparseIneq}
    (hTerms : row.terms = []) (hNeg : row.rhs.isStrictlyNeg = true)
    (hHold : row.holds env) : False := by
  dsimp [SparseIneq.holds] at hHold
  rw [hTerms] at hHold
  dsimp [evalTerms] at hHold
  dsimp [SInt.isStrictlyNeg] at hNeg
  cases hN : row.rhs.neg with
  | false => rw [hN] at hNeg; nomatch hNeg
  | true =>
    rw [hN] at hNeg
    dsimp [Bool.and] at hNeg
    have hGe1 : 1 ≤ row.rhs.mag := Nat.le_of_ble_eq_true hNeg
    have hr := sint_intBalance row.rhs
    have hBad := (intBalance_le (intBalance_ofNat 0) hr).1 hHold
    dsimp [SInt.posPart, SInt.negPart] at hBad
    rw [hN, Nat.zero_add] at hBad
    dsimp only at hBad
    have hContra : 1 ≤ 0 := Nat.le_trans hGe1 hBad
    nomatch hContra

/-- Soundness of `checkCutRefuteIdx`: an accepted refutation trace proves
`hyps` cannot jointly hold. -/
theorem checkCutRefuteIdx_sound {env : List Int} {hyps : List SparseIneq}
    {steps : List CutStep}
    (hChk : checkCutRefuteIdx hyps steps = true)
    (hHyps : AllHolds env hyps) : False := by
  dsimp [checkCutRefuteIdx] at hChk
  cases hCap : rowsWithinCap hyps with
  | false => rw [hCap] at hChk; nomatch hChk
  | true =>
    rw [hCap] at hChk
    dsimp at hChk
    cases hRun : runCutStepsIdx (IndexedRows.empty.pushAll hyps) steps
        IndexedRows.empty with
    | none => rw [hRun] at hChk; nomatch hChk
    | some derived =>
      rw [hRun] at hChk
      dsimp at hChk
      cases hLast : derived.last with
      | none => rw [hLast] at hChk; nomatch hChk
      | some last =>
        rw [hLast] at hChk
        dsimp at hChk
        cases hTerms : last.terms with
        | cons _ _ => rw [hTerms] at hChk; nomatch hChk
        | nil =>
          rw [hTerms] at hChk
          have hIdx := indexedRows_pushAll_holds IndexedRows.empty hyps
            (indexedRows_empty_holds env) hHyps
          have hAll := runCutStepsIdx_sound hIdx steps IndexedRows.empty
            derived (indexedRows_empty_holds env) hRun
          exact emptyRow_strictlyNeg_not_holds hTerms hChk (hAll.2 last hLast)

/-! ## 5. Surface Goal Checkers -/

/-- `checkIntCutGoal` replayed with `checkCutRefuteIdx`. -/
@[expose] noncomputable def checkIntCutGoalIdx (g : IntCutGoal)
    (steps : List CutStep) : Bool :=
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  checkCutRefuteIdx ((g.hyps ++ [negConcl]).map ineqToSparse) steps

/-- An accepted `checkIntCutGoalIdx` run proves `g.denote`. -/
theorem checkIntCutGoalIdx_sound (g : IntCutGoal) (steps : List CutStep)
    (hChk : checkIntCutGoalIdx g steps = true) : g.denote := by
  intro env
  apply hypsImp_allHolds_int env g.hyps
  intro hHypsSparse
  apply int_le_of_not_succ_le
  intro hNegConcl
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  have hNegSparse : (ineqToSparse negConcl).holds env :=
    ineqToSparse_sound env negConcl hNegConcl
  apply checkCutRefuteIdx_sound hChk (env := env)
  intro r hr
  have hMap :
      (g.hyps ++ [negConcl]).map ineqToSparse =
        g.hyps.map ineqToSparse ++ [ineqToSparse negConcl] := by
    induction g.hyps with
    | nil => rfl
    | cons _ _ ih => dsimp [List.map]; rw [ih]
  rw [hMap] at hr
  cases mem_of_mem_append hr with
  | inl hL => exact hHypsSparse r hL
  | inr hR =>
    cases hR with
    | head _ => exact hNegSparse
    | tail _ hNil => nomatch hNil

/-- `checkNatCutGoal` replayed with `checkIntCutGoalIdx`; row indices are laid
out exactly as for `checkNatCutGoal`. -/
@[expose] noncomputable def checkNatCutGoalIdx (g : NatCutGoal)
    (steps : List CutStep) : Bool :=
  checkIntCutGoalIdx (natCutGoalToInt g) steps

/-- An accepted `checkNatCutGoalIdx` run proves `g.denote`. -/
theorem checkNatCutGoalIdx_sound (g : NatCutGoal) (steps : List CutStep)
    (hChk : checkNatCutGoalIdx g steps = true) : g.denote := by
  intro env
  have hInt := checkIntCutGoalIdx_sound _ steps hChk (env.map Int.ofNat)
  have hSplit :=
    hypsImp_append (g.hyps.map NatCutIneq.toIntIneq)
      ((natGoalVars g).map natNonnegIntIneq) hInt
  apply hypsImp_nat_to_int env g.hyps
  refine hypsImp_concl_mono ?_ hSplit
  intro hNonneg
  have hC := hypsImp_of_nonneg env (natGoalVars g) hNonneg
  dsimp [natCutGoalToInt, NatCutIneq.toIntIneq, IntCutIneq.holds] at hC
  rw [natLinExpr_toInt_eval env g.concl.lhs,
      natLinExpr_toInt_eval env g.concl.rhs] at hC
  exact (intBalance_le (intBalance_ofNat _) (intBalance_ofNat _)).1 hC

/-! ## 6. Canaries -/

/-- `stepCut` is `stepCutWith` instantiated with list lookups. -/
theorem stepCut_eq_stepCutWith (hyps : List SparseIneq) (derived : DerivedRows)
    (st : CutStep) :
    stepCut hyps derived st = stepCutWith (listGet? hyps) derived.get? st := by
  cases st <;> rfl

/-- The `LinearArith` canary certificates check unchanged under the indexed
checker. -/
theorem idx_canaries_ok :
    checkNatCutGoalIdx parityStrideGoal parityStrideFarkasCert = true ∧
    checkNatCutGoalIdx parityStrideGoal parityStrideCert = true ∧
    checkNatCutGoalIdx natVarNonnegGoal [.hyp 0, .hyp 1, .comb 0 1 1 1] =
      true ∧
    checkNatCutGoalIdx parityCutReqGoal parityCutReqCert = true ∧
    checkIntCutGoalIdx intSubNegMulGoal intSubNegMulCert = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The indexed checker stays fail-closed on the `LinearArith` rejection
canaries. -/
theorem idx_rejections_ok :
    checkNatCutGoalIdx parityCutReqGoal [.hyp 0, .hyp 1, .comb 0 1 1 1] =
      false ∧
    checkIntCutGoalIdx
      { hyps := [⟨.mulC ⟨false, magCap128 + 1⟩ (.var 0), .cst SInt.zero⟩]
        concl := ⟨.cst SInt.one, .cst SInt.zero⟩ }
      [.hyp 0] = false ∧
    checkIntCutGoalIdx
      { hyps := [⟨.cst SInt.one, .cst SInt.zero⟩]
        concl := ⟨.cst SInt.zero, .cst ⟨false, magCap128⟩⟩ }
      [.hyp 0] = false ∧
    checkIntCutGoalIdx
      { hyps := [⟨.mulC ⟨false, magCap128⟩ (.var 0), .cst SInt.zero⟩]
        concl := ⟨.cst SInt.zero, .var 0⟩ }
      [.hyp 0, .comb 0 1 0 1] = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `IndexedRows` preserves forward indexing across pushes, rejects
out-of-bounds indices, and caches the latest row in `last`. -/
theorem indexed_rows_index_ok :
    let r0 : SparseIneq := ⟨[(0, SInt.one)], SInt.zero⟩
    let r1 : SparseIneq := ⟨[(1, SInt.one)], SInt.one⟩
    let r2 : SparseIneq := ⟨[], ⟨true, 1⟩⟩
    let d := IndexedRows.empty.pushAll [r0, r1, r2]
    d.get? 0 = some r0 ∧ d.get? 1 = some r1 ∧ d.get? 2 = some r2 ∧
    d.get? 3 = none ∧ d.last = some r2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `natVarNonnegGoal` discharged through the indexed checker. -/
theorem nat_var_nonneg_no_hyps_idx (x : Nat) : 0 ≤ x :=
  checkNatCutGoalIdx_sound natVarNonnegGoal [.hyp 0, .hyp 1, .comb 0 1 1 1] rfl
    [x]

end Anneal.LinearArith

end
