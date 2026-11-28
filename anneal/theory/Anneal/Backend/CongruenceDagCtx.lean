-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Anneal.InitLemmas
public import Anneal.Backend.Rules
public import Anneal.Backend.CtxFact

public section

/-!
# Two-Polarity DAG Congruence Checker (`Anneal.Backend.CongruenceDagCtx`)

Linear-pass arena verifier for offline hash-consed e-graph explanations over
`PoisonOr Nat`, importing the arena-free rewrite algebra from
`Anneal.Backend.Rules` and the `TrustTier.proven` contextual fact interface from
`Anneal.Backend.CtxFact`:

1. **Topological Acyclicity (`checkArenaTopo`):** Every node at index `i` may
   reference only child IDs `< i`, ruling out extraction cycles by construction.
2. **Two-Polarity Soundness (`verifyDagGoal_sound`):**
   - `.symm` accepts strictly `.eqExact` claims, rejecting poison-erasing
     inversions (`0 -> poison & 0`);
   - `.cong` accepts `.eqExact` children across all operators (including
     `.freeze`), while requiring `SsaOp.isPoisonMonotone` whenever any child
     uses `.refines`;
   - `.biRule` and `.dirRule` check syntactic pattern matching and `CtxFact`
     indices against `Rules.lean`'s soundness theorems.
3. **Guarded Expression-Block Checker (`checkBlockOpt_sound`):** Combines
   `checkGuardsDischarged` and `verifyDagGoal` to prove `SemRefinesUnder`
   (`EntryFactsHold arena ctx`) between a guarded expression block (whose
   failed assertions yield `.aborted ()`) and a zero-guard rewritten block.
-/

namespace Anneal.Backend

open Anneal.InitLemmas

/-! ## 1. Offline Hash-Consed DAG Arena and Topological Evaluation -/

/-- One hash-consed node in the offline e-graph explanation arena. -/
structure DagNode where
  op : SsaOp
  args : List Nat

/-- A verified binary relation claim `(rel, lhs, rhs)` between arena IDs. -/
structure ProvedClaim where
  rel : RelKind
  lhs : Nat
  rhs : Nat

/-- Linear proof-trace step emitted by Tier-1 `aegraph` or Tier-2 `egglog`. -/
inductive DagStep where
  | refl (nodeId : Nat)
  | symm (proofIdx : Nat)
  | trans (p1 p2 : Nat)
  | cong (lhs rhs : Nat) (childProofs : List Nat)
  | biRule (r : BiEqRule) (subst : List Nat) (lhs rhs : Nat)
  | dirRule (r : DirRefineRule) (subst : List Nat) (lhs rhs : Nat)

/-- Check that every child index in `args` is strictly `< bound`. -/
@[expose] def checkArgsBefore (bound : Nat) (args : List Nat) : Bool :=
  List.foldr (fun a acc => Nat.blt a bound && acc) true args

theorem checkArgsBefore_lt {bound : Nat} :
    ∀ (args : List Nat), checkArgsBefore bound args = true →
      ∀ a, a ∈ args → a < bound
  | [] => fun _ _ hMem => by cases hMem
  | x :: xs => fun hChk a hMem => by
    cases hMem with
    | head => exact (nat_blt_iff x bound).1 (bool_and_left hChk)
    | tail _ hTl => exact checkArgsBefore_lt xs (bool_and_right hChk) a hTl

/-- Check topological ordering across `ds` starting at node index `idx`. -/
@[expose] def checkArenaTopoAux (ds0 : List DagNode) (idx0 : Nat) : Bool :=
  List.foldr
    (fun d ih idx => checkArgsBefore idx d.args && ih (idx + 1))
    (fun _ => true)
    ds0 idx0

/-- Check that `arena` is topologically ordered (`arg < nodeId`). -/
@[expose] def checkArenaTopo (arena : List DagNode) : Bool :=
  checkArenaTopoAux arena 0

/-- Evaluate one `DagNode` from already-computed prefix values `vals`. -/
@[expose] def evalNodeFromVals (env : Nat → Nat) (vals : List (PoisonOr Nat))
    (d : DagNode) : PoisonOr Nat :=
  evalSsaOp env d.op
    (List.map (fun aid => (listNthOpt vals aid).getD .poison) d.args)

/-- Forward topological fold computing one `PoisonOr Nat` per `DagNode`. -/
@[expose] def evalArenaAux (env : Nat → Nat) (ds0 : List DagNode)
    (vals0 : List (PoisonOr Nat)) : List (PoisonOr Nat) :=
  List.foldr
    (fun d ih vals => ih (vals ++ [evalNodeFromVals env vals d]))
    (fun vals => vals)
    ds0 vals0

theorem evalArenaAux_cons (env : Nat → Nat) (d : DagNode) (ds : List DagNode)
    (vals : List (PoisonOr Nat)) :
    evalArenaAux env (d :: ds) vals =
      evalArenaAux env ds (vals ++ [evalNodeFromVals env vals d]) :=
  rfl

/-- Evaluate all nodes in `arena` under variable assignment `env`. -/
@[expose] def evalArena (env : Nat → Nat) (arena : List DagNode) :
    List (PoisonOr Nat) :=
  evalArenaAux env arena []

/-- Look up the evaluated value of node `nid` (`.poison` if out of bounds). -/
@[expose] def evalArenaNode (env : Nat → Nat) (arena : List DagNode)
    (nid : Nat) : PoisonOr Nat :=
  (listNthOpt (evalArena env arena) nid).getD .poison

theorem evalArenaAux_ext (env : Nat → Nat) :
    ∀ (ds : List DagNode) (vals : List (PoisonOr Nat)),
      ∃ suffix,
        evalArenaAux env ds vals = vals ++ suffix ∧
        suffix.length = ds.length ∧
        ∀ v, v ∈ suffix → WellTypedVal v
  | [] => fun vals =>
    ⟨[], Eq.symm (List.append_nil vals), rfl, fun _ h => by cases h⟩
  | d :: ds => fun vals => by
    let v := evalNodeFromVals env vals d
    have hWv : WellTypedVal v := evalSsaOp_wellTyped env d.op _
    have ⟨suf, hEq, hLen, hWt⟩ := evalArenaAux_ext env ds (vals ++ [v])
    refine ⟨v :: suf, ?_, ?_, ?_⟩
    · rw [evalArenaAux_cons, hEq, List.append_assoc]
      rfl
    · dsimp only [List.length]
      rw [hLen]
    · intro u hMem
      cases hMem with
      | head => exact hWv
      | tail _ hTl => exact hWt u hTl

theorem map_lookup_prefix_eq (vals suffix : List (PoisonOr Nat)) :
    ∀ (args : List Nat),
      (∀ a, a ∈ args → a < vals.length) →
      List.map (fun aid => (listNthOpt vals aid).getD .poison) args =
        List.map (fun aid => (listNthOpt (vals ++ suffix) aid).getD .poison)
          args
  | [] => fun _ => rfl
  | a :: asRest => fun hBound => by
    have ha : a < vals.length := hBound a (List.Mem.head _)
    have hRest : ∀ x, x ∈ asRest → x < vals.length :=
      fun x hx => hBound x (List.Mem.tail _ hx)
    dsimp only [List.map]
    rw [listNthOpt_append_left vals suffix ha,
      map_lookup_prefix_eq vals suffix asRest hRest]

theorem evalArenaAux_node_eq (env : Nat → Nat) :
    ∀ (ds : List DagNode) (vals : List (PoisonOr Nat)),
      checkArenaTopoAux ds vals.length = true →
      ∀ (k : Nat) (d : DagNode),
        listNthOpt ds k = some d →
        listNthOpt (evalArenaAux env ds vals) (vals.length + k) =
          some (evalNodeFromVals env (evalArenaAux env ds vals) d)
  | [] => fun _ _ _ _ hNth => by cases hNth
  | d0 :: ds => fun vals hTopo k d hNth => by
    cases k with
    | zero =>
      dsimp only [listNthOpt] at hNth
      injection hNth with hEqD
      rw [← hEqD]
      have hArgs : checkArgsBefore vals.length d0.args = true :=
        bool_and_left hTopo
      let v0 := evalNodeFromVals env vals d0
      have ⟨suf, hOutEq, _, _⟩ := evalArenaAux_ext env ds (vals ++ [v0])
      have hIdx : vals.length + 0 = vals.length := Nat.add_zero _
      have hLen1 : vals.length < (vals ++ [v0]).length := by
        rw [List.length_append]
        exact Nat.lt_succ_self vals.length
      have hLhs :
          listNthOpt (evalArenaAux env ds (vals ++ [v0])) vals.length =
            some v0 := by
        rw [hOutEq, listNthOpt_append_left (vals ++ [v0]) suf hLen1,
          listNthOpt_append_singleton vals v0]
      have hRhs :
          evalNodeFromVals env (evalArenaAux env ds (vals ++ [v0])) d0 =
            v0 := by
        rw [hOutEq, List.append_assoc]
        dsimp only [v0, evalNodeFromVals]
        exact Eq.symm
          (congrArg (evalSsaOp env d0.op)
            (map_lookup_prefix_eq vals (v0 :: suf) d0.args
              (checkArgsBefore_lt d0.args hArgs)))
      rw [hIdx, evalArenaAux_cons, hLhs, hRhs]
    | succ k' =>
      dsimp only [listNthOpt] at hNth
      have hTopoRest : checkArenaTopoAux ds (vals.length + 1) = true :=
        bool_and_right hTopo
      let v0 := evalNodeFromVals env vals d0
      have hLen : (vals ++ [v0]).length = vals.length + 1 := by
        rw [List.length_append]
        rfl
      have hTopo' : checkArenaTopoAux ds (vals ++ [v0]).length = true := by
        rw [hLen]
        exact hTopoRest
      have ih := evalArenaAux_node_eq env ds (vals ++ [v0]) hTopo' k' d hNth
      have hIdx : (vals ++ [v0]).length + k' = vals.length + (k' + 1) := by
        rw [hLen, Nat.add_assoc, Nat.add_comm 1 k']
      rw [hIdx] at ih
      exact ih

private theorem listNthOpt_getD_wellTyped :
    ∀ (xs : List (PoisonOr Nat)),
      (∀ v, v ∈ xs → WellTypedVal v) →
      ∀ (nid : Nat), WellTypedVal ((listNthOpt xs nid).getD .poison)
  | [] => fun _ _ => True.intro
  | x :: xs => fun hWt nid =>
    match nid with
    | 0 => hWt x (List.Mem.head _)
    | k + 1 =>
      listNthOpt_getD_wellTyped xs (fun u hu => hWt u (List.Mem.tail _ hu)) k

/-- Length of `evalArena env arena` equals `arena.length`. -/
theorem evalArena_length (env : Nat → Nat) (arena : List DagNode) :
    (evalArena env arena).length = arena.length := by
  have ⟨suf, hEq, hLen, _⟩ := evalArenaAux_ext env arena []
  dsimp only [evalArena]
  rw [hEq, List.nil_append, hLen]

/-- Every node in `evalArena env arena` is `WellTypedVal` (`< 2 ^ 64`). -/
theorem evalArenaNode_wellTyped (env : Nat → Nat) (arena : List DagNode)
    (nid : Nat) : WellTypedVal (evalArenaNode env arena nid) := by
  have ⟨suf, hEq, _, hWt⟩ := evalArenaAux_ext env arena []
  dsimp only [evalArenaNode, evalArena]
  rw [hEq, List.nil_append]
  exact listNthOpt_getD_wellTyped suf hWt nid

/-- Fundamental DAG unfolding equation: in a topologically ordered `arena`,
evaluating node `nid` equals applying `evalSsaOp` to the evaluated values of its
children. -/
theorem evalArenaNode_eq (env : Nat → Nat) (arena : List DagNode)
    (hTopo : checkArenaTopo arena = true) {nid : Nat} {d : DagNode}
    (hNth : listNthOpt arena nid = some d) :
    listNthOpt (evalArena env arena) nid =
      some (evalSsaOp env d.op (List.map (evalArenaNode env arena) d.args)) ∧
    evalArenaNode env arena nid =
      evalSsaOp env d.op (List.map (evalArenaNode env arena) d.args) := by
  have h0 := evalArenaAux_node_eq env arena [] hTopo nid d hNth
  have hZeroAdd : (0 : Nat) + nid = nid := Nat.zero_add nid
  dsimp only [List.length] at h0
  rw [hZeroAdd] at h0
  dsimp only [evalArenaNode, evalArena, evalNodeFromVals] at h0
  dsimp only [evalArenaNode, evalArena, evalNodeFromVals]
  rw [h0]
  exact ⟨rfl, rfl⟩

/-! ## 2. Boolean Rule, Congruence, and `isFreezeFree` Checkers

Every helper uses canonical single-scrutinee `Option`/`List`/`Bool`/enum
matches so Lean compiles directly to primitive `.casesOn` recursors (`0`
`.match_k` auxiliary blockers during proof reduction). -/

/-- Extract a constant literal node's raw value if `nid` is `.lit v` with `[]`.
-/
@[expose] def getLitNode (arena : List DagNode) (nid : Nat) : Option Nat :=
  match listNthOpt arena nid with
  | none => none
  | some d =>
    match d.args with
    | _ :: _ => none
    | [] =>
      match d.op with
      | .lit v => some v
      | .var _ => none
      | .addWrap => none
      | .addNuw => none
      | .subWrap => none
      | .subNuw => none
      | .mulWrap => none
      | .land => none
      | .lor => none
      | .lshr => none
      | .shl => none
      | .bitNot => none
      | .freeze _ => none

theorem getLitNode_eval (env : Nat → Nat) (arena : List DagNode)
    (hTopo : checkArenaTopo arena = true) {nid v : Nat}
    (hLit : getLitNode arena nid = some v) :
    evalArenaNode env arena nid = .val (word64 v) := by
  revert hLit
  dsimp only [getLitNode]
  cases hN : listNthOpt arena nid with
  | none => intro h; cases h
  | some d =>
    dsimp only
    have hEv := (evalArenaNode_eq env arena hTopo hN).2
    cases hdArgs : d.args with
    | cons _ _ => intro h; cases h
    | nil =>
      dsimp only
      cases hdOp : d.op with
      | lit w =>
        dsimp only
        intro hLit
        injection hLit with hw
        rw [hdOp, hdArgs] at hEv
        rw [hw] at hEv
        exact hEv
      | var _ => intro h; cases h
      | addWrap => intro h; cases h
      | addNuw => intro h; cases h
      | subWrap => intro h; cases h
      | subNuw => intro h; cases h
      | mulWrap => intro h; cases h
      | land => intro h; cases h
      | lor => intro h; cases h
      | lshr => intro h; cases h
      | shl => intro h; cases h
      | bitNot => intro h; cases h
      | freeze _ => intro h; cases h

/-- Check congruence child proofs left to right, joining their polarities. -/
@[expose] def checkCongChildren (as0 : List Nat) (proved : List ProvedClaim)
    (bs0 : List Nat) (ps0 : List Nat) : Option RelKind :=
  List.foldr
    (fun a ih bs ps =>
      match bs with
      | [] => none
      | b :: bsRest =>
        match ps with
        | [] => none
        | pIdx :: psRest =>
          match listNthOpt proved pIdx with
          | none => none
          | some cl =>
            match ih bsRest psRest with
            | none => none
            | some restRel =>
              match Nat.beq a cl.lhs && Nat.beq b cl.rhs with
              | false => none
              | true => some (RelKind.join cl.rel restRel))
    (fun bs ps =>
      match bs with
      | _ :: _ => none
      | [] =>
        match ps with
        | [] => some .eqExact
        | _ :: _ => none)
    as0 bs0 ps0

theorem checkCongChildren_nil (proved : List ProvedClaim)
    (bs ps : List Nat) :
    checkCongChildren [] proved bs ps =
      match bs with
      | _ :: _ => none
      | [] =>
        match ps with
        | [] => some .eqExact
        | _ :: _ => none :=
  rfl

theorem checkCongChildren_cons (a : Nat) (asRest : List Nat)
    (proved : List ProvedClaim) (bs ps : List Nat) :
    checkCongChildren (a :: asRest) proved bs ps =
      match bs with
      | [] => none
      | b :: bsRest =>
        match ps with
        | [] => none
        | pIdx :: psRest =>
          match listNthOpt proved pIdx with
          | none => none
          | some cl =>
            match checkCongChildren asRest proved bsRest psRest with
            | none => none
            | some restRel =>
              match Nat.beq a cl.lhs && Nat.beq b cl.rhs with
              | false => none
              | true => some (RelKind.join cl.rel restRel) :=
  rfl

/-- Verify a bidirectional `BiEqRule` step against `arena` and `ctx`. -/
@[expose] def checkBiRule (arena : List DagNode) (ctx : List CtxFact)
    (r : BiEqRule) (subst : List Nat) (lhsId rhsId : Nat) : Bool :=
  match listNthOpt arena lhsId with
  | none => false
  | some nl =>
    match listNthOpt arena rhsId with
    | none => false
    | some nr =>
      match r with
      | .addZero =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | zId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match getLitNode arena zId with
              | none => false
              | some zv =>
                Nat.beq rhsId xId && Nat.beq (word64 zv) 0 &&
                SsaOp.beq nl.op .addWrap && natListBeq nl.args [xId, zId]
      | .addComm =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              SsaOp.beq nl.op .addWrap && natListBeq nl.args [aId, bId] &&
              SsaOp.beq nr.op .addWrap && natListBeq nr.args [bId, aId]
      | .andComm =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              SsaOp.beq nl.op .land && natListBeq nl.args [aId, bId] &&
              SsaOp.beq nr.op .land && natListBeq nr.args [bId, aId]
      | .mul4ToShl2 =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | fourId :: s2 =>
            match s2 with
            | [] => false
            | twoId :: s3 =>
              match s3 with
              | _ :: _ => false
              | [] =>
                match getLitNode arena fourId with
                | none => false
                | some fv =>
                  match getLitNode arena twoId with
                  | none => false
                  | some tv =>
                    Nat.beq fv 4 && Nat.beq tv 2 &&
                    SsaOp.beq nl.op .mulWrap &&
                    natListBeq nl.args [xId, fourId] &&
                    SsaOp.beq nr.op .shl && natListBeq nr.args [xId, twoId]
      | .shrShrAdd =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | inId :: s2 =>
            match s2 with
            | [] => false
            | k1Id :: s3 =>
              match s3 with
              | [] => false
              | k2Id :: s4 =>
                match s4 with
                | [] => false
                | kSumId :: s5 =>
                  match s5 with
                  | _ :: _ => false
                  | [] =>
                    match getLitNode arena k1Id with
                    | none => false
                    | some k1 =>
                      match getLitNode arena k2Id with
                      | none => false
                      | some k2 =>
                        match getLitNode arena kSumId with
                        | none => false
                        | some kSum =>
                          match listNthOpt arena inId with
                          | none => false
                          | some inner =>
                            Nat.ble (k1 + k2) 63 &&
                            Nat.beq (k1 + k2) kSum &&
                            SsaOp.beq inner.op .lshr &&
                            natListBeq inner.args [xId, k1Id] &&
                            SsaOp.beq nl.op .lshr &&
                            natListBeq nl.args [inId, k2Id] &&
                            SsaOp.beq nr.op .lshr &&
                            natListBeq nr.args [xId, kSumId]
      | .notSubOneToNeg =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | sub1Id :: s2 =>
            match s2 with
            | [] => false
            | oneId :: s3 =>
              match s3 with
              | [] => false
              | zeroId :: s4 =>
                match s4 with
                | _ :: _ => false
                | [] =>
                  match getLitNode arena oneId with
                  | none => false
                  | some oneV =>
                    match getLitNode arena zeroId with
                    | none => false
                    | some zeroV =>
                      match listNthOpt arena sub1Id with
                      | none => false
                      | some subNode =>
                        Nat.beq oneV 1 && Nat.beq zeroV 0 &&
                        SsaOp.beq subNode.op .subWrap &&
                        natListBeq subNode.args [xId, oneId] &&
                        SsaOp.beq nl.op .bitNot &&
                        natListBeq nl.args [sub1Id] &&
                        SsaOp.beq nr.op .subWrap &&
                        natListBeq nr.args [zeroId, xId]
      | .maskPow2Elide fIdx exp =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | mId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match listNthOpt ctx fIdx with
              | none => false
              | some fc =>
                match fc with
                | .ltPow2 guardedId fExp =>
                  match getLitNode arena mId with
                  | none => false
                  | some mVal =>
                    Nat.ble exp 64 && Nat.beq fExp exp &&
                    Nat.beq guardedId xId && Nat.beq rhsId xId &&
                    Nat.beq mVal (Nat.pow 2 exp - 1) &&
                    SsaOp.beq nl.op .land && natListBeq nl.args [xId, mId]
                | .addNoOverflow _ _ => false
                | .subNoUnderflow _ _ => false
      | .promoteAddNuw fIdx =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match listNthOpt ctx fIdx with
              | none => false
              | some fc =>
                match fc with
                | .ltPow2 _ _ => false
                | .addNoOverflow ga gb =>
                  Nat.beq ga aId && Nat.beq gb bId &&
                  SsaOp.beq nl.op .addWrap &&
                  natListBeq nl.args [aId, bId] &&
                  SsaOp.beq nr.op .addNuw &&
                  natListBeq nr.args [aId, bId]
                | .subNoUnderflow _ _ => false
      | .promoteSubNuw fIdx =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match listNthOpt ctx fIdx with
              | none => false
              | some fc =>
                match fc with
                | .ltPow2 _ _ => false
                | .addNoOverflow _ _ => false
                | .subNoUnderflow ga gb =>
                  Nat.beq ga aId && Nat.beq gb bId &&
                  SsaOp.beq nl.op .subWrap &&
                  natListBeq nl.args [aId, bId] &&
                  SsaOp.beq nr.op .subNuw &&
                  natListBeq nr.args [aId, bId]

/-- Verify a directional `DirRefineRule` step against `arena`. -/
@[expose] def checkDirRule (arena : List DagNode)
    (r : DirRefineRule) (subst : List Nat) (lhsId rhsId : Nat) : Bool :=
  match listNthOpt arena lhsId with
  | none => false
  | some nl =>
    match listNthOpt arena rhsId with
    | none => false
    | some nr =>
      match r with
      | .landZero =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | zId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match getLitNode arena zId with
              | none => false
              | some zv =>
                Nat.beq rhsId zId && Nat.beq zv 0 &&
                SsaOp.beq nl.op .land && natListBeq nl.args [xId, zId]
      | .mulZero =>
        match subst with
        | [] => false
        | xId :: s1 =>
          match s1 with
          | [] => false
          | zId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              match getLitNode arena zId with
              | none => false
              | some zv =>
                Nat.beq rhsId zId && Nat.beq zv 0 &&
                SsaOp.beq nl.op .mulWrap && natListBeq nl.args [xId, zId]
      | .dropAddNuw =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              SsaOp.beq nl.op .addNuw && natListBeq nl.args [aId, bId] &&
              SsaOp.beq nr.op .addWrap && natListBeq nr.args [aId, bId]
      | .dropSubNuw =>
        match subst with
        | [] => false
        | aId :: s1 =>
          match s1 with
          | [] => false
          | bId :: s2 =>
            match s2 with
            | _ :: _ => false
            | [] =>
              SsaOp.beq nl.op .subNuw && natListBeq nl.args [aId, bId] &&
              SsaOp.beq nr.op .subWrap && natListBeq nr.args [aId, bId]

/-- Check one `DagStep`, returning the newly established `ProvedClaim`. -/
@[expose] def verifyStep (arena : List DagNode) (ctx : List CtxFact)
    (proved : List ProvedClaim) (step : DagStep) : Option ProvedClaim :=
  match step with
  | .refl n =>
    match Nat.blt n arena.length with
    | false => none
    | true => some ⟨.eqExact, n, n⟩
  | .symm p =>
    match listNthOpt proved p with
    | none => none
    | some cl =>
      match cl.rel with
      | .eqExact => some ⟨.eqExact, cl.rhs, cl.lhs⟩
      | .refines => none
  | .trans p1 p2 =>
    match listNthOpt proved p1 with
    | none => none
    | some c1 =>
      match listNthOpt proved p2 with
      | none => none
      | some c2 =>
        match Nat.beq c1.rhs c2.lhs with
        | false => none
        | true => some ⟨RelKind.join c1.rel c2.rel, c1.lhs, c2.rhs⟩
  | .cong n1 n2 childPs =>
    match listNthOpt arena n1 with
    | none => none
    | some d1 =>
      match listNthOpt arena n2 with
      | none => none
      | some d2 =>
        match SsaOp.beq d1.op d2.op with
        | false => none
        | true =>
          match checkCongChildren d1.args proved d2.args childPs with
          | none => none
          | some chRel =>
            match chRel with
            | .eqExact => some ⟨.eqExact, n1, n2⟩
            | .refines =>
              match SsaOp.isPoisonMonotone d1.op with
              | false => none
              | true => some ⟨.refines, n1, n2⟩
  | .biRule r subst n1 n2 =>
    match checkBiRule arena ctx r subst n1 n2 with
    | false => none
    | true => some ⟨.eqExact, n1, n2⟩
  | .dirRule r subst n1 n2 =>
    match checkDirRule arena r subst n1 n2 with
    | false => none
    | true => some ⟨.refines, n1, n2⟩

/-- Linear fold over `steps` (`List.foldl`, `0` `._unsafe_rec`). -/
@[expose] def verifySteps (arena : List DagNode) (ctx : List CtxFact)
    (steps : List DagStep) : Option (List ProvedClaim) :=
  List.foldl
    (fun accOpt step =>
      match accOpt with
      | none => none
      | some proved =>
        match verifyStep arena ctx proved step with
        | none => none
        | some cl => some (proved ++ [cl]))
    (some []) steps

/-- Complete DAG congruence goal check: verifies topological acyclicity of
`arena`, replays `steps`, and confirms the final claim establishes `reqRel`
between `lhsId` and `rhsId`. -/
@[expose] def verifyDagGoal (arena : List DagNode) (ctx : List CtxFact)
    (steps : List DagStep) (lhsId rhsId : Nat) (reqRel : RelKind) : Bool :=
  checkArenaTopo arena &&
  match verifySteps arena ctx steps with
  | none => false
  | some proved =>
    match listNthOpt proved (proved.length - 1) with
    | none => false
    | some cl =>
      !Nat.beq proved.length 0 &&
      Nat.beq cl.lhs lhsId && Nat.beq cl.rhs rhsId &&
      RelKind.satisfies cl.rel reqRel

/-! ## 3. Universal Soundness Proof (`verifyDagGoal_sound`) -/

/-- Semantic validity of a `ProvedClaim`. -/
@[expose] def ClaimHolds (env : Nat → Nat) (arena : List DagNode)
    (cl : ProvedClaim) : Prop :=
  evalRel cl.rel (evalArenaNode env arena cl.lhs)
    (evalArenaNode env arena cl.rhs)

/-- Every claim in `proved` holds semantically. -/
@[expose] def AllClaimsHold (env : Nat → Nat) (arena : List DagNode)
    (proved : List ProvedClaim) : Prop :=
  ∀ p cl, listNthOpt proved p = some cl → ClaimHolds env arena cl

theorem allClaimsHold_append (env : Nat → Nat) (arena : List DagNode) :
    ∀ (proved : List ProvedClaim) (clNew : ProvedClaim),
      AllClaimsHold env arena proved →
      ClaimHolds env arena clNew →
      AllClaimsHold env arena (proved ++ [clNew])
  | [] => fun _clNew _ hNew p _cl hNth => by
    cases p with
    | zero =>
      dsimp only [List.nil_append, listNthOpt] at hNth
      injection hNth with hEq
      rw [← hEq]
      exact hNew
    | succ _ => cases hNth
  | _ :: ps => fun clNew hPrev hNew p cl hNth => by
    cases p with
    | zero => exact hPrev 0 cl hNth
    | succ k =>
      exact allClaimsHold_append env arena ps clNew
        (fun i c hi => hPrev (i + 1) c hi) hNew k cl hNth

theorem checkCongChildren_sound (env : Nat → Nat) (arena : List DagNode)
    (proved : List ProvedClaim) (hProved : AllClaimsHold env arena proved) :
    ∀ (as0 bs0 ps0 : List Nat) (rel : RelKind),
      checkCongChildren as0 proved bs0 ps0 = some rel →
      (rel = .eqExact →
        List.map (evalArenaNode env arena) as0 =
          List.map (evalArenaNode env arena) bs0) ∧
      ArgsRefines (List.map (evalArenaNode env arena) as0)
        (List.map (evalArenaNode env arena) bs0)
  | [] => fun bs0 ps0 _rel hChk => by
    revert hChk
    rw [checkCongChildren_nil]
    cases bs0 with
    | cons _ _ => intro h; cases h
    | nil =>
      dsimp only
      cases ps0 with
      | cons _ _ => intro h; cases h
      | nil => intro _; exact ⟨fun _ => rfl, rfl⟩
  | a :: asRest => fun bs0 ps0 rel hChk => by
    revert hChk
    rw [checkCongChildren_cons]
    cases bs0 with
    | nil => intro h; cases h
    | cons b bsRest =>
      dsimp only
      cases ps0 with
      | nil => intro h; cases h
      | cons pIdx psRest =>
        dsimp only
        cases hCl : listNthOpt proved pIdx with
        | none => intro h; cases h
        | some cl =>
          dsimp only
          cases hRest : checkCongChildren asRest proved bsRest psRest with
          | none => intro h; cases h
          | some restRel =>
            dsimp only
            cases hIds : (Nat.beq a cl.lhs && Nat.beq b cl.rhs) with
            | false => intro h; cases h
            | true =>
              dsimp only
              intro hChk
              injection hChk with hJoin
              have ha : a = cl.lhs := nat_eq_of_beq (bool_and_left hIds)
              have hb : b = cl.rhs := nat_eq_of_beq (bool_and_right hIds)
              have hHead := hProved pIdx cl hCl
              dsimp only [ClaimHolds] at hHead
              rw [← ha, ← hb] at hHead
              have ih := checkCongChildren_sound env arena proved hProved
                asRest bsRest psRest restRel hRest
              refine ⟨fun hRelEq => ?_, ?_⟩
              · rw [← hJoin] at hRelEq
                cases hC1 : cl.rel with
                | refines =>
                  rw [hC1] at hRelEq
                  cases hRelEq
                | eqExact =>
                  cases hC2 : restRel with
                  | refines =>
                    rw [hC1, hC2] at hRelEq
                    cases hRelEq
                  | eqExact =>
                    rw [hC1] at hHead
                    dsimp only [evalRel] at hHead
                    dsimp only [List.map]
                    rw [hHead, ih.1 hC2]
              · have hRefHead :
                    refinesPoison (evalArenaNode env arena a)
                      (evalArenaNode env arena b) :=
                  evalRel_upgrade (r2 := .refines) (by cases cl.rel <;> rfl)
                    hHead
                exact ⟨hRefHead, ih.2⟩

private theorem evalArenaNode_some_val_inv (env : Nat → Nat)
    (arena : List DagNode) {nid v : Nat}
    (hVal : evalArenaNode env arena nid = .val v) :
    listNthOpt (evalArena env arena) nid = some (.val v) := by
  revert hVal
  dsimp only [evalArenaNode]
  cases listNthOpt (evalArena env arena) nid with
  | none => intro h; cases h
  | some p =>
    intro h
    dsimp only [Option.getD] at h
    rw [h]

theorem checkBiRule_sound (env : Nat → Nat)
    (arena : List DagNode) (ctx : List CtxFact)
    (hTopo : checkArenaTopo arena = true)
    (hCtx : AllCtxFactsHold (evalArena env arena) ctx)
    {r : BiEqRule} {subst : List Nat} {lhsId rhsId : Nat}
    (hChk : checkBiRule arena ctx r subst lhsId rhsId = true) :
    evalArenaNode env arena lhsId = evalArenaNode env arena rhsId := by
  revert hChk
  dsimp only [checkBiRule]
  cases hNl : listNthOpt arena lhsId with
  | none => intro h; cases h
  | some nl =>
    dsimp only
    cases hNr : listNthOpt arena rhsId with
    | none => intro h; cases h
    | some nr =>
      dsimp only
      have hEvL := (evalArenaNode_eq env arena hTopo hNl).2
      have hEvR := (evalArenaNode_eq env arena hTopo hNr).2
      cases r with
      | addZero =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons zId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hZ : getLitNode arena zId with
              | none => intro h; cases h
              | some zv =>
                dsimp only
                intro hChk
                have hArgs := eq_of_natListBeq (bool_and_right hChk)
                have c3 := bool_and_left hChk
                have hOp := ssaOp_eq_of_beq (bool_and_right c3)
                have c2 := bool_and_left c3
                have hZv : word64 zv = 0 := nat_eq_of_beq (bool_and_right c2)
                have hRhs := nat_eq_of_beq (bool_and_left c2)
                have hEvZ := getLitNode_eval env arena hTopo hZ
                rw [hZv] at hEvZ
                rw [hEvL, hOp, hArgs, hRhs]
                dsimp only [List.map]
                rw [hEvZ]
                exact biEq_addZero_sound env _
                  (evalArenaNode_wellTyped env arena xId)
      | addComm =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              intro hChk
              have hArgsR := eq_of_natListBeq (bool_and_right hChk)
              have c3 := bool_and_left hChk
              have hOpR := ssaOp_eq_of_beq (bool_and_right c3)
              have c2 := bool_and_left c3
              have hArgsL := eq_of_natListBeq (bool_and_right c2)
              have hOpL := ssaOp_eq_of_beq (bool_and_left c2)
              rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
              exact biEq_addComm_sound env _ _
      | andComm =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              intro hChk
              have hArgsR := eq_of_natListBeq (bool_and_right hChk)
              have c3 := bool_and_left hChk
              have hOpR := ssaOp_eq_of_beq (bool_and_right c3)
              have c2 := bool_and_left c3
              have hArgsL := eq_of_natListBeq (bool_and_right c2)
              have hOpL := ssaOp_eq_of_beq (bool_and_left c2)
              rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
              exact biEq_andComm_sound env _ _
      | mul4ToShl2 =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons fourId s2 =>
            dsimp only
            cases s2 with
            | nil => intro h; cases h
            | cons twoId s3 =>
              dsimp only
              cases s3 with
              | cons _ _ => intro h; cases h
              | nil =>
                dsimp only
                cases hF : getLitNode arena fourId with
                | none => intro h; cases h
                | some fv =>
                  dsimp only
                  cases hT : getLitNode arena twoId with
                  | none => intro h; cases h
                  | some tv =>
                    dsimp only
                    intro hChk
                    have hArgsR := eq_of_natListBeq (bool_and_right hChk)
                    have c4 := bool_and_left hChk
                    have hOpR := ssaOp_eq_of_beq (bool_and_right c4)
                    have c3 := bool_and_left c4
                    have hArgsL := eq_of_natListBeq (bool_and_right c3)
                    have c2 := bool_and_left c3
                    have hOpL := ssaOp_eq_of_beq (bool_and_right c2)
                    have cLits := bool_and_left c2
                    have hFv := nat_eq_of_beq (bool_and_left cLits)
                    have hTv := nat_eq_of_beq (bool_and_right cLits)
                    have hEvF := getLitNode_eval env arena hTopo hF
                    have hEvT := getLitNode_eval env arena hTopo hT
                    rw [hFv] at hEvF
                    rw [hTv] at hEvT
                    rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
                    dsimp only [List.map]
                    rw [hEvF, hEvT]
                    exact biEq_mul4ToShl2_sound env _
      | shrShrAdd =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons inId s2 =>
            dsimp only
            cases s2 with
            | nil => intro h; cases h
            | cons k1Id s3 =>
              dsimp only
              cases s3 with
              | nil => intro h; cases h
              | cons k2Id s4 =>
                dsimp only
                cases s4 with
                | nil => intro h; cases h
                | cons kSumId s5 =>
                  dsimp only
                  cases s5 with
                  | cons _ _ => intro h; cases h
                  | nil =>
                    dsimp only
                    cases hK1 : getLitNode arena k1Id with
                    | none => intro h; cases h
                    | some k1 =>
                      dsimp only
                      cases hK2 : getLitNode arena k2Id with
                      | none => intro h; cases h
                      | some k2 =>
                        dsimp only
                        cases hKS : getLitNode arena kSumId with
                        | none => intro h; cases h
                        | some kSum =>
                          dsimp only
                          cases hIn : listNthOpt arena inId with
                          | none => intro h; cases h
                          | some inner =>
                            dsimp only
                            intro hChk
                            have hArgsR :=
                              eq_of_natListBeq (bool_and_right hChk)
                            have c6 := bool_and_left hChk
                            have hOpR := ssaOp_eq_of_beq (bool_and_right c6)
                            have c5 := bool_and_left c6
                            have hArgsL :=
                              eq_of_natListBeq (bool_and_right c5)
                            have c4 := bool_and_left c5
                            have hOpL := ssaOp_eq_of_beq (bool_and_right c4)
                            have c3 := bool_and_left c4
                            have hArgsIn :=
                              eq_of_natListBeq (bool_and_right c3)
                            have c2 := bool_and_left c3
                            have hOpIn := ssaOp_eq_of_beq (bool_and_right c2)
                            have c1 := bool_and_left c2
                            have hSumEq := nat_eq_of_beq (bool_and_right c1)
                            have hBound :=
                              (nat_ble_iff _ _).1 (bool_and_left c1)
                            have hEvIn :=
                              (evalArenaNode_eq env arena hTopo hIn).2
                            have hEvK1 := getLitNode_eval env arena hTopo hK1
                            have hEvK2 := getLitNode_eval env arena hTopo hK2
                            have hEvKS := getLitNode_eval env arena hTopo hKS
                            have h64 : (64 : Nat) < u64Mod := by decide
                            have hSum64 : k1 + k2 < 64 :=
                              Nat.lt_of_le_of_lt hBound (by decide)
                            have hk1Lt : k1 < u64Mod :=
                              Nat.lt_trans
                                (Nat.lt_of_le_of_lt (Nat.le_add_right k1 k2)
                                  hSum64) h64
                            have hk2Lt : k2 < u64Mod :=
                              Nat.lt_trans
                                (Nat.lt_of_le_of_lt (Nat.le_add_left k2 k1)
                                  hSum64) h64
                            have hSumLt : k1 + k2 < u64Mod :=
                              Nat.lt_trans hSum64 h64
                            rw [← hSumEq] at hEvKS
                            rw [word64_of_lt hk1Lt] at hEvK1
                            rw [word64_of_lt hk2Lt] at hEvK2
                            rw [word64_of_lt hSumLt] at hEvKS
                            rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
                            dsimp only [List.map]
                            rw [hEvIn, hOpIn, hArgsIn]
                            dsimp only [List.map]
                            rw [hEvK1, hEvK2, hEvKS]
                            exact biEq_shrShrAdd_sound env _ k1 k2 hBound
      | notSubOneToNeg =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons sub1Id s2 =>
            dsimp only
            cases s2 with
            | nil => intro h; cases h
            | cons oneId s3 =>
              dsimp only
              cases s3 with
              | nil => intro h; cases h
              | cons zeroId s4 =>
                dsimp only
                cases s4 with
                | cons _ _ => intro h; cases h
                | nil =>
                  dsimp only
                  cases hOne : getLitNode arena oneId with
                  | none => intro h; cases h
                  | some oneV =>
                    dsimp only
                    cases hZero : getLitNode arena zeroId with
                    | none => intro h; cases h
                    | some zeroV =>
                      dsimp only
                      cases hSub : listNthOpt arena sub1Id with
                      | none => intro h; cases h
                      | some subNode =>
                        dsimp only
                        intro hChk
                        have hArgsR :=
                          eq_of_natListBeq (bool_and_right hChk)
                        have c6 := bool_and_left hChk
                        have hOpR := ssaOp_eq_of_beq (bool_and_right c6)
                        have c5 := bool_and_left c6
                        have hArgsL :=
                          eq_of_natListBeq (bool_and_right c5)
                        have c4 := bool_and_left c5
                        have hOpL := ssaOp_eq_of_beq (bool_and_right c4)
                        have c3 := bool_and_left c4
                        have hArgsSub :=
                          eq_of_natListBeq (bool_and_right c3)
                        have c2 := bool_and_left c3
                        have hOpSub := ssaOp_eq_of_beq (bool_and_right c2)
                        have c1 := bool_and_left c2
                        have hZeroEq := nat_eq_of_beq (bool_and_right c1)
                        have hOneEq := nat_eq_of_beq (bool_and_left c1)
                        have hEvSub := (evalArenaNode_eq env arena hTopo hSub).2
                        have hEvOne := getLitNode_eval env arena hTopo hOne
                        have hEvZero := getLitNode_eval env arena hTopo hZero
                        rw [hOneEq] at hEvOne
                        rw [hZeroEq] at hEvZero
                        rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
                        dsimp only [List.map]
                        rw [hEvSub, hOpSub, hArgsSub]
                        dsimp only [List.map]
                        rw [hEvOne, hEvZero]
                        exact biEq_notSubOneToNeg_sound env _
      | maskPow2Elide fIdx exp =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons mId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hFactOpt : listNthOpt ctx fIdx with
              | none => intro h; cases h
              | some fc =>
                dsimp only
                cases fc with
                | addNoOverflow _ _ => intro h; cases h
                | subNoUnderflow _ _ => intro h; cases h
                | ltPow2 guardedId fExp =>
                  dsimp only
                  cases hM : getLitNode arena mId with
                  | none => intro h; cases h
                  | some mVal =>
                    dsimp only
                    intro hChk
                    have hArgsL := eq_of_natListBeq (bool_and_right hChk)
                    have c6 := bool_and_left hChk
                    have hOpL := ssaOp_eq_of_beq (bool_and_right c6)
                    have c5 := bool_and_left c6
                    have hMEq := nat_eq_of_beq (bool_and_right c5)
                    have c4 := bool_and_left c5
                    have hRhs := nat_eq_of_beq (bool_and_right c4)
                    have c3 := bool_and_left c4
                    have hGId := nat_eq_of_beq (bool_and_right c3)
                    have c2 := bool_and_left c3
                    have hFExp := nat_eq_of_beq (bool_and_right c2)
                    have hExpLe := (nat_ble_iff _ _).1 (bool_and_left c2)
                    have hHolds := hCtx fIdx _ hFactOpt
                    dsimp only [CtxFactHolds] at hHolds
                    rw [hGId, hFExp] at hHolds
                    have hEvM := getLitNode_eval env arena hTopo hM
                    have hPowLe : Nat.pow 2 exp ≤ u64Mod := by
                      rw [u64Mod_eq_pow]
                      exact nat_two_pow_le_of_le hExpLe
                    have hMaskLt : Nat.pow 2 exp - 1 < u64Mod :=
                      Nat.lt_of_lt_of_le
                        (Nat.sub_lt (nat_two_pow_pos exp) (by decide)) hPowLe
                    rw [hMEq, word64_of_lt hMaskLt] at hEvM
                    rw [hEvL, hOpL, hArgsL, hRhs]
                    dsimp only [List.map]
                    rw [hEvM]
                    exact biEq_maskPow2Elide_sound env _ exp hExpLe
                      (evalArenaNode_wellTyped env arena xId)
                      (fun v hVal =>
                        hHolds v (evalArenaNode_some_val_inv env arena hVal))
      | promoteAddNuw fIdx =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hFactOpt : listNthOpt ctx fIdx with
              | none => intro h; cases h
              | some fc =>
                dsimp only
                cases fc with
                | ltPow2 _ _ => intro h; cases h
                | subNoUnderflow _ _ => intro h; cases h
                | addNoOverflow ga gb =>
                  dsimp only
                  intro hChk
                  have hArgsR := eq_of_natListBeq (bool_and_right hChk)
                  have c5 := bool_and_left hChk
                  have hOpR := ssaOp_eq_of_beq (bool_and_right c5)
                  have c4 := bool_and_left c5
                  have hArgsL := eq_of_natListBeq (bool_and_right c4)
                  have c3 := bool_and_left c4
                  have hOpL := ssaOp_eq_of_beq (bool_and_right c3)
                  have c2 := bool_and_left c3
                  have hGb := nat_eq_of_beq (bool_and_right c2)
                  have hGa := nat_eq_of_beq (bool_and_left c2)
                  have hHolds := hCtx fIdx _ hFactOpt
                  dsimp only [CtxFactHolds] at hHolds
                  rw [hGa, hGb] at hHolds
                  rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
                  exact biEq_promoteAddNuw_sound env _ _
                    (evalArenaNode_wellTyped env arena aId)
                    (evalArenaNode_wellTyped env arena bId)
                    (fun va vb hVa hVb =>
                      hHolds va vb
                        (evalArenaNode_some_val_inv env arena hVa)
                        (evalArenaNode_some_val_inv env arena hVb))
      | promoteSubNuw fIdx =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hFactOpt : listNthOpt ctx fIdx with
              | none => intro h; cases h
              | some fc =>
                dsimp only
                cases fc with
                | ltPow2 _ _ => intro h; cases h
                | addNoOverflow _ _ => intro h; cases h
                | subNoUnderflow ga gb =>
                  dsimp only
                  intro hChk
                  have hArgsR := eq_of_natListBeq (bool_and_right hChk)
                  have c5 := bool_and_left hChk
                  have hOpR := ssaOp_eq_of_beq (bool_and_right c5)
                  have c4 := bool_and_left c5
                  have hArgsL := eq_of_natListBeq (bool_and_right c4)
                  have c3 := bool_and_left c4
                  have hOpL := ssaOp_eq_of_beq (bool_and_right c3)
                  have c2 := bool_and_left c3
                  have hGb := nat_eq_of_beq (bool_and_right c2)
                  have hGa := nat_eq_of_beq (bool_and_left c2)
                  have hHolds := hCtx fIdx _ hFactOpt
                  dsimp only [CtxFactHolds] at hHolds
                  rw [hGa, hGb] at hHolds
                  rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
                  exact biEq_promoteSubNuw_sound env _ _
                    (evalArenaNode_wellTyped env arena aId)
                    (evalArenaNode_wellTyped env arena bId)
                    (fun va vb hVa hVb =>
                      hHolds va vb
                        (evalArenaNode_some_val_inv env arena hVa)
                        (evalArenaNode_some_val_inv env arena hVb))

theorem checkDirRule_sound (env : Nat → Nat) (arena : List DagNode)
    (hTopo : checkArenaTopo arena = true)
    {r : DirRefineRule} {subst : List Nat} {lhsId rhsId : Nat}
    (hChk : checkDirRule arena r subst lhsId rhsId = true) :
    refinesPoison (evalArenaNode env arena lhsId)
      (evalArenaNode env arena rhsId) := by
  revert hChk
  dsimp only [checkDirRule]
  cases hNl : listNthOpt arena lhsId with
  | none => intro h; cases h
  | some nl =>
    dsimp only
    cases hNr : listNthOpt arena rhsId with
    | none => intro h; cases h
    | some nr =>
      dsimp only
      have hEvL := (evalArenaNode_eq env arena hTopo hNl).2
      have hEvR := (evalArenaNode_eq env arena hTopo hNr).2
      cases r with
      | landZero =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons zId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hZ : getLitNode arena zId with
              | none => intro h; cases h
              | some zv =>
                dsimp only
                intro hChk
                have hArgsL := eq_of_natListBeq (bool_and_right hChk)
                have c3 := bool_and_left hChk
                have hOpL := ssaOp_eq_of_beq (bool_and_right c3)
                have c2 := bool_and_left c3
                have hZv : zv = 0 := nat_eq_of_beq (bool_and_right c2)
                have hRhs := nat_eq_of_beq (bool_and_left c2)
                have hEvZ := getLitNode_eval env arena hTopo hZ
                rw [hZv] at hEvZ
                rw [hEvL, hOpL, hArgsL, hRhs]
                dsimp only [List.map]
                rw [hEvZ]
                exact dirRefine_landZero_sound env _
      | mulZero =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons xId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons zId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              cases hZ : getLitNode arena zId with
              | none => intro h; cases h
              | some zv =>
                dsimp only
                intro hChk
                have hArgsL := eq_of_natListBeq (bool_and_right hChk)
                have c3 := bool_and_left hChk
                have hOpL := ssaOp_eq_of_beq (bool_and_right c3)
                have c2 := bool_and_left c3
                have hZv : zv = 0 := nat_eq_of_beq (bool_and_right c2)
                have hRhs := nat_eq_of_beq (bool_and_left c2)
                have hEvZ := getLitNode_eval env arena hTopo hZ
                rw [hZv] at hEvZ
                rw [hEvL, hOpL, hArgsL, hRhs]
                dsimp only [List.map]
                rw [hEvZ]
                exact dirRefine_mulZero_sound env _
      | dropAddNuw =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              intro hChk
              have hArgsR := eq_of_natListBeq (bool_and_right hChk)
              have c3 := bool_and_left hChk
              have hOpR := ssaOp_eq_of_beq (bool_and_right c3)
              have c2 := bool_and_left c3
              have hArgsL := eq_of_natListBeq (bool_and_right c2)
              have hOpL := ssaOp_eq_of_beq (bool_and_left c2)
              rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
              exact dirRefine_dropAddNuw_sound env _ _
      | dropSubNuw =>
        dsimp only
        cases subst with
        | nil => intro h; cases h
        | cons aId s1 =>
          dsimp only
          cases s1 with
          | nil => intro h; cases h
          | cons bId s2 =>
            dsimp only
            cases s2 with
            | cons _ _ => intro h; cases h
            | nil =>
              dsimp only
              intro hChk
              have hArgsR := eq_of_natListBeq (bool_and_right hChk)
              have c3 := bool_and_left hChk
              have hOpR := ssaOp_eq_of_beq (bool_and_right c3)
              have c2 := bool_and_left c3
              have hArgsL := eq_of_natListBeq (bool_and_right c2)
              have hOpL := ssaOp_eq_of_beq (bool_and_left c2)
              rw [hEvL, hEvR, hOpL, hArgsL, hOpR, hArgsR]
              exact dirRefine_dropSubNuw_sound env _ _

theorem verifyStep_sound (env : Nat → Nat)
    (arena : List DagNode) (ctx : List CtxFact)
    (hTopo : checkArenaTopo arena = true)
    (hCtx : AllCtxFactsHold (evalArena env arena) ctx)
    (proved : List ProvedClaim) (hProved : AllClaimsHold env arena proved)
    (step : DagStep) {cl : ProvedClaim}
    (hStep : verifyStep arena ctx proved step = some cl) :
    ClaimHolds env arena cl := by
  revert hStep
  dsimp only [verifyStep]
  cases step with
  | refl n =>
    dsimp only
    cases Nat.blt n arena.length with
    | false => intro h; cases h
    | true =>
      dsimp only
      intro hStep
      injection hStep with hEq
      rw [← hEq]
      exact rfl
  | symm p =>
    dsimp only
    cases hP : listNthOpt proved p with
    | none => intro h; cases h
    | some cp =>
      dsimp only
      have hHolds := hProved p cp hP
      cases hR : cp.rel with
      | refines => intro h; cases h
      | eqExact =>
        dsimp only
        intro hStep
        dsimp only [ClaimHolds] at hHolds
        rw [hR] at hHolds
        injection hStep with hEq
        rw [← hEq]
        dsimp only [ClaimHolds]
        exact evalRel_symm hHolds
  | trans p1 p2 =>
    dsimp only
    cases hP1 : listNthOpt proved p1 with
    | none => intro h; cases h
    | some c1 =>
      dsimp only
      cases hP2 : listNthOpt proved p2 with
      | none => intro h; cases h
      | some c2 =>
        dsimp only
        cases hMid : Nat.beq c1.rhs c2.lhs with
        | false => intro h; cases h
        | true =>
          dsimp only
          intro hStep
          injection hStep with hEq
          rw [← hEq]
          have h1 := hProved p1 c1 hP1
          have h2 := hProved p2 c2 hP2
          dsimp only [ClaimHolds] at h1 h2
          dsimp only [ClaimHolds]
          rw [nat_eq_of_beq hMid] at h1
          exact evalRel_trans h1 h2
  | cong n1 n2 childPs =>
    dsimp only
    cases hD1 : listNthOpt arena n1 with
    | none => intro h; cases h
    | some d1 =>
      dsimp only
      cases hD2 : listNthOpt arena n2 with
      | none => intro h; cases h
      | some d2 =>
        dsimp only
        cases hOpB : SsaOp.beq d1.op d2.op with
        | false => intro h; cases h
        | true =>
          dsimp only
          have hOpEq : d1.op = d2.op := ssaOp_eq_of_beq hOpB
          have hEv1 := (evalArenaNode_eq env arena hTopo hD1).2
          have hEv2 := (evalArenaNode_eq env arena hTopo hD2).2
          cases hCh : checkCongChildren d1.args proved d2.args childPs with
          | none => intro h; cases h
          | some chRel =>
            dsimp only
            have hChSound :=
              checkCongChildren_sound env arena proved hProved
                d1.args d2.args childPs chRel hCh
            cases chRel with
            | eqExact =>
              dsimp only
              intro hStep
              injection hStep with hEq
              rw [← hEq]
              dsimp only [ClaimHolds]
              rw [hEv1, hEv2, ← hOpEq]
              exact evalSsaOp_cong_eqExact env d1.op (hChSound.1 rfl)
            | refines =>
              dsimp only
              cases hMono : SsaOp.isPoisonMonotone d1.op with
              | false => intro h; cases h
              | true =>
                dsimp only
                intro hStep
                injection hStep with hEq
                rw [← hEq]
                dsimp only [ClaimHolds, evalRel]
                rw [hEv1, hEv2, ← hOpEq]
                exact evalSsaOp_cong_refines env d1.op hMono hChSound.2
  | biRule r subst n1 n2 =>
    dsimp only
    cases hB : checkBiRule arena ctx r subst n1 n2 with
    | false => intro h; cases h
    | true =>
      dsimp only
      intro hStep
      injection hStep with hEq
      rw [← hEq]
      exact checkBiRule_sound env arena ctx hTopo hCtx hB
  | dirRule r subst n1 n2 =>
    dsimp only
    cases hD : checkDirRule arena r subst n1 n2 with
    | false => intro h; cases h
    | true =>
      dsimp only
      intro hStep
      injection hStep with hEq
      rw [← hEq]
      exact checkDirRule_sound env arena hTopo hD

private theorem verifySteps_fold_none (arena : List DagNode)
    (ctx : List CtxFact) :
    ∀ (rest : List DagStep),
      List.foldl
        (fun (aOpt : Option (List ProvedClaim)) (st : DagStep) =>
          match aOpt with
          | none => none
          | some prv =>
            match verifyStep arena ctx prv st with
            | none => none
            | some cl => some (prv ++ [cl]))
        none rest = none
  | [] => rfl
  | _ :: tl => verifySteps_fold_none arena ctx tl

theorem verifySteps_fold_sound (env : Nat → Nat)
    (arena : List DagNode) (ctx : List CtxFact)
    (hTopo : checkArenaTopo arena = true)
    (hCtx : AllCtxFactsHold (evalArena env arena) ctx) :
    ∀ (steps : List DagStep) (accOpt : Option (List ProvedClaim)),
      (∀ initP, accOpt = some initP → AllClaimsHold env arena initP) →
      ∀ (proved : List ProvedClaim),
        List.foldl
            (fun aOpt step =>
              match aOpt with
              | none => none
              | some prv =>
                match verifyStep arena ctx prv step with
                | none => none
                | some cl => some (prv ++ [cl]))
            accOpt steps = some proved →
        AllClaimsHold env arena proved
  | [] => fun accOpt hInit proved hEq => hInit proved hEq
  | step :: rest => fun accOpt hInit proved hEq => by
    cases accOpt with
    | none =>
      rw [List.foldl, verifySteps_fold_none arena ctx rest] at hEq
      cases hEq
    | some prv =>
      have hPrv := hInit prv rfl
      dsimp only [List.foldl] at hEq
      revert hEq
      cases hSt : verifyStep arena ctx prv step with
      | none =>
        intro hEq
        rw [verifySteps_fold_none arena ctx rest] at hEq
        cases hEq
      | some cl =>
        intro hEq
        have hCl :=
          verifyStep_sound env arena ctx hTopo hCtx prv hPrv step hSt
        exact verifySteps_fold_sound env arena ctx hTopo hCtx rest
          (some (prv ++ [cl]))
          (fun initP hSome => by
            injection hSome with hInitEq
            rw [← hInitEq]
            exact allClaimsHold_append env arena prv cl hPrv hCl)
          proved hEq

/-- Master soundness theorem of `CongruenceDagCtx`: any accepted DAG proof trace
establishes `evalRel reqRel` between `lhsId` and `rhsId` across all runtime
environments satisfying `ctx`. -/
theorem verifyDagGoal_sound (env : Nat → Nat)
    (arena : List DagNode) (ctx : List CtxFact)
    (steps : List DagStep) (lhsId rhsId : Nat) (reqRel : RelKind)
    (hCtx : AllCtxFactsHold (evalArena env arena) ctx)
    (hGoal : verifyDagGoal arena ctx steps lhsId rhsId reqRel = true) :
    evalRel reqRel (evalArenaNode env arena lhsId)
      (evalArenaNode env arena rhsId) := by
  have hTopo : checkArenaTopo arena = true := bool_and_left hGoal
  have hRest := bool_and_right hGoal
  revert hRest
  cases hSteps : verifySteps arena ctx steps with
  | none => intro h; cases h
  | some proved =>
    dsimp only
    cases hLast : listNthOpt proved (proved.length - 1) with
    | none => intro h; cases h
    | some cl =>
      dsimp only
      intro hRest
      have hSat : RelKind.satisfies cl.rel reqRel = true :=
        bool_and_right hRest
      have c2 := bool_and_left hRest
      have hRhs : cl.rhs = rhsId := nat_eq_of_beq (bool_and_right c2)
      have c1 := bool_and_left c2
      have hLhs : cl.lhs = lhsId := nat_eq_of_beq (bool_and_right c1)
      have hAll :=
        verifySteps_fold_sound env arena ctx hTopo hCtx steps
          (some [])
          (fun initP hSome => by
            injection hSome with hNil
            rw [← hNil]
            intro _ _ hN
            cases hN)
          proved hSteps
      have hCl := hAll (proved.length - 1) cl hLast
      dsimp only [ClaimHolds] at hCl
      rw [hLhs, hRhs] at hCl
      exact evalRel_upgrade hSat hCl

/-! ## 4. Guarded Expression-Block Elision and DAG Refinement -/

/-- Entry precondition on variable assignment `env`: every `CtxFact` in `ctx`
holds on the evaluated arena. -/
@[expose] def EntryFactsHold (arena : List DagNode) (ctx : List CtxFact)
    (env : Nat → Nat) : Prop :=
  AllCtxFactsHold (evalArena env arena) ctx

/-- Execute an expression block with sequential runtime assertion `guards`
followed by DAG expression `retId`:
- if any guard observes `.poison`, the block faults with `.faultUB`;
- if the first failing guard evaluates to `false`, the block aborts cleanly
  with `.aborted ()`;
- if all guards evaluate to `true`, the block evaluates `retId`. -/
@[expose] def evalBlockWithGuards (guards : List GuardCond)
    (arena : List DagNode) (retId : Nat) (env : Nat → Nat)
    (out : ExecOutcome Nat Unit) : Prop :=
  match evalGuards (evalArena env arena) guards with
  | none => out = .faultUB
  | some false => out = .aborted ()
  | some true =>
    match evalArenaNode env arena retId with
    | .poison => out = .faultUB
    | .val v => out = .returned v ()

/-- Combined Boolean checker verifying both assertion-guard discharge and
two-polarity `CongruenceDagCtx` expression refinement. -/
@[expose] def checkBlockOpt (guards : List GuardCond) (arena : List DagNode)
    (ctx : List CtxFact) (steps : List DagStep)
    (srcRetId optRetId : Nat) : Bool :=
  checkGuardsDischarged guards ctx &&
  verifyDagGoal arena ctx steps srcRetId optRetId .refines

/-- Conditional block optimization soundness: whenever `checkBlockOpt` returns
`true`, the zero-guard rewritten block refines the guarded source block across
all variable assignments satisfying `EntryFactsHold arena ctx`. -/
theorem checkBlockOpt_sound (guards : List GuardCond) (arena : List DagNode)
    (ctx : List CtxFact) (steps : List DagStep) (srcRetId optRetId : Nat)
    (hChk : checkBlockOpt guards arena ctx steps srcRetId optRetId = true) :
    SemRefinesUnder (EntryFactsHold arena ctx)
      (evalBlockWithGuards guards arena srcRetId)
      (evalBlockWithGuards [] arena optRetId) := by
  have hGuards := bool_and_left hChk
  have hDag := bool_and_right hChk
  intro env hFacts hNoUbSrc
  have hNotFalse : evalGuards (evalArena env arena) guards ≠ some false :=
    checkGuardsDischarged_ne_false (evalArena env arena) ctx hFacts
      guards hGuards
  cases hEvG : evalGuards (evalArena env arena) guards with
  | none =>
    exact False.elim
      (hNoUbSrc (by
        dsimp only [evalBlockWithGuards]
        rw [hEvG]))
  | some b =>
    cases b with
    | false => exact False.elim (hNotFalse hEvG)
    | true =>
      have hRef :
          refinesPoison (evalArenaNode env arena srcRetId)
            (evalArenaNode env arena optRetId) :=
        verifyDagGoal_sound env arena ctx steps srcRetId optRetId .refines
          hFacts hDag
      cases hSrcVal : evalArenaNode env arena srcRetId with
      | poison =>
        exact False.elim
          (hNoUbSrc (by
            dsimp only [evalBlockWithGuards]
            rw [hEvG, hSrcVal]))
      | val vs =>
        rw [hSrcVal] at hRef
        cases hOptVal : evalArenaNode env arena optRetId with
        | poison =>
          rw [hOptVal] at hRef
          exact False.elim hRef
        | val vo =>
          rw [hOptVal] at hRef
          dsimp only [refinesPoison] at hRef
          refine ⟨fun hUbTgt => ?_, fun out hOutTgt => ?_⟩
          · dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hUbTgt
            rw [hOptVal] at hUbTgt
            cases hUbTgt
          · dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hOutTgt
            rw [hOptVal] at hOutTgt
            dsimp only [evalBlockWithGuards]
            rw [hEvG, hSrcVal, hRef]
            exact hOutTgt

end Anneal.Backend

end
