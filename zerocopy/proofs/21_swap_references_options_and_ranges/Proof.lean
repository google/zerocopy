-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Init.RCases
import Expected
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Shared Plumbing -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  nomatch h

/-- Split a Boolean conjunction that holds. -/
private theorem and_true_split {x y : Bool} (h : (x && y) = true) :
    x = true ∧ y = true := by
  cases x <;> cases y <;> first | exact ⟨rfl, rfl⟩ | exact nomatch h

/-- An exact-outcome execution yields well-formedness and `returnsExactly`. -/
private theorem returnsExactly_of_exec {defId : DefId} {q : Query}
    {fuel : Nat} {out : TerminalOut}
    (hExec : execProgV2 (entryProgForBody Captured.program defId) fuel q
      (fun o => o = out)) :
    WellFormedV2 (entryProgForBody Captured.program defId) q ∧
    Spec.returnsExactly Captured.program defId q out := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-! ## Mutable-Borrow Span Disjointness Is Order-Independent -/

/-- `spanDisjoint` is symmetric. -/
private theorem spanDisjoint_comm (a b : Bool × AllocId × Nat × Nat) :
    spanDisjoint a b = spanDisjoint b a := by
  let (m1, id1, s1, n1) := a
  let (m2, id2, s2, n2) := b
  have hId : Nat.beq id1 id2 = Nat.beq id2 id1 := by
    cases h : Nat.beq id1 id2 with
    | true =>
      have hEq : id1 = id2 := Nat.eq_of_beq_eq_true h
      rw [hEq, Nat.beq_refl]
    | false =>
      cases h' : Nat.beq id2 id1 with
      | false => rfl
      | true =>
        have hEq : id2 = id1 := Nat.eq_of_beq_eq_true h'
        rw [hEq, Nat.beq_refl] at h
        exact nomatch h
  change (if (!(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 ||
      !Nat.beq id1 id2) = true then true
    else Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1) =
    (if (!(m2 || m1) || Nat.beq n2 0 || Nat.beq n1 0 ||
      !Nat.beq id2 id1) = true then true
    else Nat.ble (s2 + n2) s1 || Nat.ble (s1 + n1) s2)
  rw [hId]
  generalize Nat.beq n1 0 = x1
  generalize Nat.beq n2 0 = x2
  generalize Nat.beq id2 id1 = x3
  generalize Nat.ble (s1 + n1) s2 = y1
  generalize Nat.ble (s2 + n2) s1 = y2
  cases m1 <;> cases m2 <;> cases x1 <;> cases x2 <;> cases x3 <;>
    cases y1 <;> cases y2 <;> rfl

/-- `spanDisjointWith a ys` checks `a` against every span of `ys`. -/
private theorem spanDisjointWith_eq_all (a : Bool × AllocId × Nat × Nat) :
    ∀ ys : List (Bool × AllocId × Nat × Nat),
      spanDisjointWith a ys = ys.all (spanDisjoint a)
  | [] => rfl
  | b :: rest => by
    change (spanDisjoint a b && spanDisjointWith a rest) =
      (spanDisjoint a b && rest.all (spanDisjoint a))
    rw [spanDisjointWith_eq_all a rest]

private theorem all_append {α : Type} (f : α → Bool) :
    ∀ xs ys : List α, (xs ++ ys).all f = (xs.all f && ys.all f)
  | [], _ => rfl
  | x :: xs, ys => by
    change (f x && (xs ++ ys).all f) = ((f x && xs.all f) && ys.all f)
    rw [all_append f xs ys, Bool.and_assoc]

private theorem all_and {α : Type} (f g : α → Bool) :
    ∀ xs : List α, xs.all (fun x => f x && g x) = (xs.all f && xs.all g)
  | [] => rfl
  | x :: xs => by
    change ((f x && g x) && xs.all (fun x => f x && g x)) =
      ((f x && xs.all f) && (g x && xs.all g))
    rw [all_and f g xs]
    cases f x <;> cases g x <;> cases xs.all f <;> cases xs.all g <;> rfl

/-- The cross check between two span lists is symmetric. -/
private theorem cross_comm :
    ∀ xs ys : List (Bool × AllocId × Nat × Nat),
      xs.all (fun a => ys.all (spanDisjoint a)) =
        ys.all (fun b => xs.all (spanDisjoint b))
  | [], ys => by
    change true = ys.all (fun _ => true)
    induction ys with
    | nil => rfl
    | cons _ _ ih => exact ih
  | x :: xs, ys => by
    change (ys.all (spanDisjoint x) &&
        xs.all (fun a => ys.all (spanDisjoint a))) =
      ys.all (fun b => spanDisjoint b x && xs.all (spanDisjoint b))
    rw [all_and, cross_comm xs ys]
    have hSym :
        ys.all (spanDisjoint x) = ys.all (fun b => spanDisjoint b x) := by
      induction ys with
      | nil => rfl
      | cons y rest ih =>
        change (spanDisjoint x y && rest.all (spanDisjoint x)) =
          (spanDisjoint y x && rest.all (fun b => spanDisjoint b x))
        rw [spanDisjoint_comm x y, ih]
    rw [hSym]

/-- Pairwise disjointness of a concatenation splits into both halves and
their cross check. -/
private theorem spansPairwiseDisjoint_append :
    ∀ xs ys : List (Bool × AllocId × Nat × Nat),
      spansPairwiseDisjoint (xs ++ ys) =
        (spansPairwiseDisjoint xs && spansPairwiseDisjoint ys &&
          xs.all (fun a => ys.all (spanDisjoint a)))
  | [], ys => by
    change spansPairwiseDisjoint ys = (true && spansPairwiseDisjoint ys && true)
    cases spansPairwiseDisjoint ys <;> rfl
  | x :: xs, ys => by
    change (spanDisjointWith x (xs ++ ys) && spansPairwiseDisjoint (xs ++ ys)) =
      ((spanDisjointWith x xs && spansPairwiseDisjoint xs) &&
        spansPairwiseDisjoint ys &&
        (ys.all (spanDisjoint x) && xs.all (fun a => ys.all (spanDisjoint a))))
    rw [spanDisjointWith_eq_all, spanDisjointWith_eq_all, all_append,
      spansPairwiseDisjoint_append xs ys]
    cases xs.all (spanDisjoint x) <;> cases ys.all (spanDisjoint x) <;>
      cases spansPairwiseDisjoint xs <;> cases spansPairwiseDisjoint ys <;>
      cases xs.all (fun a => ys.all (spanDisjoint a)) <;> rfl

/-- Swapping two blocks of spans preserves pairwise disjointness. -/
private theorem spansPairwiseDisjoint_swap
    (xs ys : List (Bool × AllocId × Nat × Nat)) :
    spansPairwiseDisjoint (xs ++ ys) = spansPairwiseDisjoint (ys ++ xs) := by
  rw [spansPairwiseDisjoint_append, spansPairwiseDisjoint_append, cross_comm]
  cases spansPairwiseDisjoint xs <;> cases spansPairwiseDisjoint ys <;>
    cases ys.all (fun b => xs.all (spanDisjoint b)) <;> rfl

/-! ## Reference Facts of Component Types -/

/-- On entry, a valid value of type `t` references only caller memory. -/
private abbrev StaysIn (t : MirTy) : Prop :=
  ∀ (cm : CallerMemory) (v : Val),
    refsValidInMem (entryMemoryWithCaller cm) t v = true →
    refsStayInCallerMem cm t v = true

/-- A type whose values hold no allocation ids. -/
private abbrev NoAllocIds (t : MirTy) : Prop :=
  ∀ v : Val, refAllocIds t v = []

private theorem staysIn_of_noAllocIds {t : MirTy} (h : NoAllocIds t) :
    StaysIn t := by
  intro cm v _
  unfold refsStayInCallerMem
  rw [h v]
  rfl

/-- A boolean reference-validity check yields the underlying
`refValidInMem` success. -/
private theorem refValid_of_refsValid {m : MemoryState} {reqMut : Mutability}
    {pt : MirTy} {v : Val}
    (h : refsValidInMem m (.ref reqMut pt) v = true) :
    refValidInMem m reqMut pt v = .ok () := by
  unfold refsValidInMem at h
  revert h
  cases hR : refValidInMem m reqMut pt v with
  | ok u => intro _; cases u; rfl
  | error k => intro h; exact False.elim (boolFalseNeTrue h)

private theorem staysIn_ref (reqMut : Mutability) (pt : MirTy) :
    StaysIn (.ref reqMut pt) :=
  fun _ _ h => refsStayInCallerMem_of_refValid (refValid_of_refsValid h)

private theorem staysIn_option_ref (reqMut : Mutability) (pt : MirTy) :
    StaysIn (.option (.ref reqMut pt)) := by
  intro cm v h
  cases v with
  | optionVal o =>
    cases o with
    | none => rfl
    | some w =>
      change refsStayInCallerMem cm (.ref reqMut pt) w = true
      exact staysIn_ref reqMut pt cm w h
  | _ => rfl

private theorem noAllocIds_int (w : IntWidth) (s : Bool) :
    NoAllocIds (.int w s) := fun v => by
  cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_bool : NoAllocIds .bool := fun v => by
  cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_char : NoAllocIds .char := fun v => by
  cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_unit : NoAllocIds .unit := fun v => by
  cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_ordering : NoAllocIds .ordering := fun v => by
  cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_range (t : MirTy) : NoAllocIds (.range t) :=
  fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl

private theorem noAllocIds_option {t : MirTy} (h : NoAllocIds t) :
    NoAllocIds (.option t) := fun v => by
  cases v with
  | optionVal o =>
    cases o with
    | none => rfl
    | some w => exact h w
  | _ => rfl

private theorem noAllocIds_array {t : MirTy} (n : Nat) (h : NoAllocIds t) :
    NoAllocIds (.array t n) := fun v => by
  cases v with
  | optionVal o => cases o <;> rfl
  | array vs =>
    change refAllocIdsArray t vs = []
    induction vs with
    | nil => rfl
    | cons x xs ih =>
      change refAllocIds t x ++ refAllocIdsArray t xs = []
      rw [h x, ih]
      rfl
  | _ => rfl

private theorem noAllocIds_pair {t1 t2 : MirTy} (h1 : NoAllocIds t1)
    (h2 : NoAllocIds t2) : NoAllocIds (.tuple [t1, t2]) := fun v => by
  cases v with
  | optionVal o => cases o <;> rfl
  | tuple vs =>
    match vs with
    | [] => rfl
    | [x] =>
      change refAllocIds t1 x ++ [] = []
      rw [h1 x]
      rfl
    | [x, y] =>
      change refAllocIds t1 x ++ (refAllocIds t2 y ++ []) = []
      rw [h1 x, h2 y]
      rfl
    | x :: y :: _ :: _ =>
      change refAllocIds t1 x ++ (refAllocIds t2 y ++ []) = []
      rw [h1 x, h2 y]
      rfl
  | _ => rfl

/-! ## `swap` Bodies -/

/-- The entry frame of a `swap` body: an uninitialized return local, the
argument pair, and four dead temporaries. -/
private abbrev swapEntry (a b : Val) : List LocalSlot :=
  [.immediate none, .immediate (some (.tuple [a, b])), .dead, .dead, .dead,
   .dead]

/-- A valid single argument of tuple type `(tA, tB)` is a pair of values of
those types. -/
private theorem pair_arg_of_valid {body : Body} {q : Query} {tA tB : MirTy}
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ a b : Val, q.args = [.tuple [a, b]] ∧ checkValV2 a tA = true ∧
      checkValV2 b tB = true := by
  have hMatch : checkArgsMatchV2 q.args [.tuple [tA, tB]] = true := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    exact h
  let ⟨v, hArgs, hCheck⟩ := checkArgsMatchV2_singleton_inv hMatch
  cases v with
  | tuple vs =>
    match vs, hCheck with
    | [a, b], h =>
      have h' : (checkValV2 a tA && (checkValV2 b tB && true)) = true := h
      let ⟨hA, hB'⟩ := and_true_split h'
      exact ⟨a, b, hArgs, hA, (and_true_split hB').1⟩
    | [], h => exact False.elim (boolFalseNeTrue h)
    | [_], h =>
      have h' : (checkValV2 _ tA && false) = true := h
      exact False.elim (boolFalseNeTrue (and_true_split h').2)
    | _ :: _ :: _ :: _, h =>
      have h' : (checkValV2 _ tA && (checkValV2 _ tB && false)) = true := h
      exact False.elim
        (boolFalseNeTrue (and_true_split (and_true_split h').2).2)
  | optionVal o =>
    cases o with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | boxPtr _ len =>
    cases len with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | _ => exact False.elim (boolFalseNeTrue hCheck)

/-- The run hypothesis of a `swap` body: from its entry frame, with the
entry facts about `a` and `b`, 14 steps return `(b, a)` with memory
untouched. -/
private abbrev SwapRuns (defId : DefId) (tA tB : MirTy) : Prop :=
  ∀ (a b : Val) (cm : CallerMemory),
    checkValV2 a tA = true → checkValV2 b tB = true →
    refsValidInMem (entryMemoryWithCaller cm) tA a = true →
    refsValidInMem (entryMemoryWithCaller cm) tB b = true →
    refsStayInCallerMem cm tA a = true → refsStayInCallerMem cm tB b = true →
    spansPairwiseDisjoint (refAccessSpans tB b ++ (refAccessSpans tA a ++ [])) =
      true →
    execOutcomeStateV2 (entryProgForBody Captured.program defId)
      (fun o => o = .returned ⟨.tuple [b, a],
        extractCallerMemory cm (entryMemoryWithCaller cm)⟩)
      (fun _ => False) 14
      (stateV2 (frameV2 defId 0 0 (swapEntry a b)) cm
        (entryMemoryWithCaller cm))

/-- A `swap` body that satisfies `SwapRuns` returns `(b, a)` with caller
memory unchanged on every valid entry. -/
private theorem swap_body_exec {defId : DefId} {body : Body} {tA tB : MirTy}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hNoRaw : tyListHasRawPtrV2 [.tuple [tA, tB]] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead, .dead])
    (hStayA : StaysIn tA) (hStayB : StaysIn tB)
    (hRun : SwapRuns defId tA tB)
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    ∃ a b : Val, q.args = [.tuple [a, b]] ∧
      execProgV2 (entryProgForBody Captured.program defId) 14 q
        (fun o => o = .returned ⟨.tuple [b, a], q.callerMem⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  let ⟨a, b, hArgs, hA, hB⟩ := pair_arg_of_valid hParams hValid
  have hRV : refsValidInMem (entryMemoryWithCaller q.callerMem) tA a = true ∧
      refsValidInMem (entryMemoryWithCaller q.callerMem) tB b = true := by
    have h := hValid.2.2.1
    rw [hParams, hArgs] at h
    have h' : ((refsValidInMem (entryMemoryWithCaller q.callerMem) tA a &&
        (refsValidInMem (entryMemoryWithCaller q.callerMem) tB b && true)) &&
        true) = true := h
    let ⟨h1, _⟩ := and_true_split h'
    let ⟨hVA, h2⟩ := and_true_split h1
    exact ⟨hVA, (and_true_split h2).1⟩
  have hDisj : spansPairwiseDisjoint
      (refAccessSpans tB b ++ (refAccessSpans tA a ++ [])) = true := by
    have h := hValid.2.2.2
    rw [hParams, hArgs] at h
    have h' : spansPairwiseDisjoint
        ((refAccessSpans tA a ++ (refAccessSpans tB b ++ [])) ++ []) = true := h
    rw [List.append_nil, List.append_nil] at h'
    rw [List.append_nil, spansPairwiseDisjoint_swap]
    exact h'
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0 (swapEntry a b))
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have h := ctx.initStateV2_ok_frameV2 hBody hAdm hValid
      (by rw [hParams]; exact hNoRaw)
    rw [hArgs, hInit] at h
    exact h
  refine ⟨a, b, hArgs, ?_⟩
  have hR := hRun a b q.callerMem hA hB hRV.1 hRV.2
    (hStayA q.callerMem a hRV.1) (hStayB q.callerMem b hRV.2) hDisj
  rw [extractCallerMemory_entry q.callerMem hCM] at hR
  unfold execProgV2
  rw [hInitState]
  exact hR

/-- `swap_body_exec` packaged as `BodyVerifiedV2` plus `swapBodyPost`. -/
private theorem swap_body_verified {defId : DefId} {body : Body}
    {tA tB : MirTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hNoRaw : tyListHasRawPtrV2 [.tuple [tA, tB]] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead, .dead])
    (hStayA : StaysIn tA) (hStayB : StaysIn tB)
    (hRun : SwapRuns defId tA tB) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.swapBodyPost Captured.program defId identity := by
  have hExec := swap_body_exec hBody hAdm hParams hNoRaw hInit hStayA hStayB
    hRun
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.swapBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨a, b, hArgs, hE⟩ := hExec q hValid
    ⟨a, b, hArgs, (returnsExactly_of_exec hE).2⟩⟩

/-- Evaluate a retagging move whose operand reads a reference-valid value. -/
private theorem evalRvalueV2_useRetag_ok {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem : MemoryState} {ty : MirTy}
    {op : Operand} {v : Val}
    (hOp : evalOperandToSlotV2 bodyLocals locals mem op =
      .ok (ty, some v, locals1, mem))
    (hBeq : MirTy.beq ty ty = true)
    (hRV : refsValidInMem mem ty v = true) :
    evalRvalueV2 bodyLocals locals mem ty (.useRetag op) =
      .ok (v, locals1, mem) := by
  unfold evalRvalueV2
  dsimp only
  rw [hOp]
  dsimp only
  rw [hBeq]
  rw [hRV]
  rfl

/-- Evaluate the `swap` result aggregate `(move _4, move _5)`. -/
private theorem evalRvalueV2_swap_pair {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem : MemoryState} {tA tB : MirTy}
    {a b : Val} {typedVals : List (MirTy × Val)}
    (hOps : evalArgOperandsV2 bodyLocals locals mem
      [.move ⟨4, []⟩, .move ⟨5, []⟩] = .ok (typedVals, locals1, mem))
    (hVals : argValues typedVals = [b, a])
    (hB : checkValV2 b tB = true) (hA : checkValV2 a tA = true) :
    evalRvalueV2 bodyLocals locals mem (.tuple [tB, tA])
      (.aggregateTuple [.move ⟨4, []⟩, .move ⟨5, []⟩]) =
      .ok (.tuple [b, a], locals1, mem) := by
  unfold evalRvalueV2
  dsimp only
  rw [hOps]
  dsimp only
  rw [hVals]
  have hList : checkValV2List [b, a] [tB, tA] = true := by
    change (checkValV2 b tB && (checkValV2 a tA && true)) = true
    rw [hB, hA]
    rfl
  rw [hList]
  rfl

/-- `checkValV2` of a pair from its components. -/
private theorem checkValV2_pair {a b : Val} {tA tB : MirTy}
    (hB : checkValV2 b tB = true) (hA : checkValV2 a tA = true) :
    checkValV2 (.tuple [b, a]) (.tuple [tB, tA]) = true := by
  change (checkValV2 b tB && (checkValV2 a tA && true)) = true
  rw [hB, hA]
  rfl

/-- The `return` side conditions for the swapped pair. -/
private theorem pair_return_facts {cm : CallerMemory} {m : MemoryState}
    {tA tB : MirTy} {a b : Val}
    (hVA : refsValidInMem m tA a = true) (hVB : refsValidInMem m tB b = true)
    (hSA : refsStayInCallerMem cm tA a = true)
    (hSB : refsStayInCallerMem cm tB b = true)
    (hD : spansPairwiseDisjoint
      (refAccessSpans tB b ++ (refAccessSpans tA a ++ [])) = true) :
    refsStayInCallerMem cm (.tuple [tB, tA]) (.tuple [b, a]) = true ∧
    refsValidInMem m (.tuple [tB, tA]) (.tuple [b, a]) = true ∧
    spansPairwiseDisjoint (refAccessSpans (.tuple [tB, tA]) (.tuple [b, a])) =
      true := by
  refine ⟨?_, ?_, hD⟩
  · unfold refsStayInCallerMem at hSA hSB
    change (refAllocIds tB b ++ (refAllocIds tA a ++ [])).all
      (fun aid => (findAllocation aid cm.allocations).isSome) = true
    rw [all_append, all_append, hSB, hSA]
    rfl
  · change (refsValidInMem m tB b && (refsValidInMem m tA a && true)) = true
    rw [hVB, hVA]
    rfl

/-- Body 0: `swap::<&[u8], &str>`. -/
private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.swapBodyPost Captured.program 0
      (Spec.swapId "&[u8], &str") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_ref .shared (.slice (.int .i8 false)))
    (staysIn_ref .shared .str)
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 1: `swap::<&mut [u8], &[u8; 4]>`. -/
private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.swapBodyPost Captured.program 1
      (Spec.swapId "&mut [u8], &[u8; 4]") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_ref .mut (.slice (.int .i8 false)))
    (staysIn_ref .shared (.array (.int .i8 false) 4))
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 2: `swap::<&u8, &mut u32>`. -/
private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.swapBodyPost Captured.program 2
      (Spec.swapId "&u8, &mut u32") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_ref .shared (.int .i8 false))
    (staysIn_ref .mut (.int .i32 false))
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVB)
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 3: `swap::<(u8, u16), bool>`. -/
private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.swapBodyPost Captured.program 3
      (Spec.swapId "(u8, u16), bool") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_of_noAllocIds
      (noAllocIds_pair (noAllocIds_int .i8 false) (noAllocIds_int .i16 false)))
    (staysIn_of_noAllocIds noAllocIds_bool)
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 4: `swap::<[u32; 2], core::option::Option<bool>>`. -/
private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.swapBodyPost Captured.program 4
      (Spec.swapId "[u32; 2], core::option::Option<bool>") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_of_noAllocIds (noAllocIds_array 2 (noAllocIds_int .i32 false)))
    (staysIn_of_noAllocIds (noAllocIds_option noAllocIds_bool))
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 5: `swap::<core::cmp::Ordering, ()>`. -/
private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.swapBodyPost Captured.program 5
      (Spec.swapId "core::cmp::Ordering, ()") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_of_noAllocIds noAllocIds_ordering)
    (staysIn_of_noAllocIds noAllocIds_unit)
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 6: `swap::<core::option::Option<&u8>, char>`. -/
private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.swapBodyPost Captured.program 6
      (Spec.swapId "core::option::Option<&u8>, char") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_option_ref .shared (.int .i8 false))
    (staysIn_of_noAllocIds noAllocIds_char)
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_useRetag_ok rfl rfl hVA)
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 7: `swap::<Option<u32>, Range<usize>>`. -/
private theorem body7_verified :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.swapBodyPost Captured.program 7 (Spec.swapId
      "core::option::Option<u32>, core::ops::range::Range<usize>") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (staysIn_of_noAllocIds (noAllocIds_option (noAllocIds_int .i32 false)))
    (staysIn_of_noAllocIds (noAllocIds_range (.int .isize false)))
    (fun _ _ _ hA hB hVA hVB hSA hSB hD =>
      let hR := pair_return_facts hVA hVB hSA hSB hD
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, h =>
      cases (h : some Captured.body_0 = some body); exact body0_verified.1
    | 1, h =>
      cases (h : some Captured.body_1 = some body); exact body1_verified.1
    | 2, h =>
      cases (h : some Captured.body_2 = some body); exact body2_verified.1
    | 3, h =>
      cases (h : some Captured.body_3 = some body); exact body3_verified.1
    | 4, h =>
      cases (h : some Captured.body_4 = some body); exact body4_verified.1
    | 5, h =>
      cases (h : some Captured.body_5 = some body); exact body5_verified.1
    | 6, h =>
      cases (h : some Captured.body_6 = some body); exact body6_verified.1
    | 7, h =>
      cases (h : some Captured.body_7 = some body); exact body7_verified.1
    | n + 8, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2,
      body7_verified.2, trivial⟩

end Proof
