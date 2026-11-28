-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas
import Anneal.MirWp
import Anneal.MirWp.V2Memory

/-! Generic Profile v2 stepping lemmas and `u8` arithmetic facts shared by the
overflow-check proofs. Each proof steps a single-frame state of body `0` one
`evalStepV2` transition at a time; `Runs` hides the fuel so that elaboration
never unfolds `execOutcomeStateV2` on a concrete fuel literal. -/

namespace StepLemmas

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

abbrev u8 (bits : BitVec 128) : Val := .scalar ⟨.i8, false, bits⟩
abbrev im (v : Val) : LocalSlot := .immediate (some v)
abbrev N : LocalSlot := .immediate none
abbrev D : LocalSlot := .dead

/-- Single-frame state at statement `i` of block `b` of body `0`. -/
abbrev st (b i : Nat) (l : List LocalSlot) (cm : CallerMemory)
    (m : MemoryState) : State :=
  ⟨[⟨0, b, i, l, none, none, none⟩], cm, m⟩

/-! ## Stepping -/

/-- `post` holds on the outcome reached from `s` after finitely many steps,
none of which faults. -/
abbrev Runs (p : Program) (post : TerminalOut → Prop) (s : State) : Prop :=
  ∃ fuel, execOutcomeStateV2 p post (fun _ => False) fuel s

theorem runs_step {p : Program} {s s' : State} {post : TerminalOut → Prop}
    (hStep : evalStepV2 p s = .step s') (hRest : Runs p post s') :
    Runs p post s :=
  let ⟨fuel, h⟩ := hRest
  ⟨fuel + 1, by
    change (match evalStepV2 p s with
      | .step s'' => execOutcomeStateV2 p post (fun _ => False) fuel s''
      | .done out => post out
      | .fault k => (fun _ => False) k)
    rw [hStep]
    exact h⟩

theorem runs_done {p : Program} {s : State} {out : TerminalOut}
    {post : TerminalOut → Prop}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    Runs p post s :=
  ⟨1, by
    change (match evalStepV2 p s with
      | .step s'' => execOutcomeStateV2 p post (fun _ => False) 0 s''
      | .done o => post o
      | .fault k => (fun _ => False) k)
    rw [hDone]
    exact hPost⟩

/-- Package a run from the entry state as the adequacy theorem's input. -/
theorem execProgV2_of_runs {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (hInit : initStateV2 p q = .ok s₀)
    (hRuns : Runs p post s₀) : ∃ fuel, execProgV2 p fuel q post :=
  let ⟨fuel, h⟩ := hRuns
  ⟨fuel, by unfold execProgV2; rw [hInit]; exact h⟩

/-- One `assign` statement to an unprojected local in body `0`, split into
its rvalue evaluation and its store. -/
theorem step_assign {p : Program} {body : Body} {bb : BasicBlock}
    {b i : Nat} {l l1 l2 : List LocalSlot} {cm : CallerMemory}
    {m m1 m2 : MemoryState} {lid : LocalId} {rv : Rvalue} {ty : MirTy}
    {v : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies 0 = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign ⟨lid, []⟩ rv))
    (hTy : placeStaticTyV2 body.locals ⟨lid, []⟩ = some ty)
    (hRv : evalRvalueV2 body.locals l m ty rv = .ok (v, l1, m1))
    (hW : writePlaceDestV2 l1 m1 (.local lid) ty v = .ok (l2, m2))
    (hHaz : checkAssignCopyHazardV2 body.locals l m (.local lid) ty rv =
      .ok () := by rfl) :
    evalStepV2 p (st b i l cm m) = .step (st b (i + 1) l2 cm m2) := by
  unfold evalStepV2 activeFrameBody
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBB]
  dsimp only
  rw [hStmt]
  unfold attachCallers evalStatementV2
  dsimp only
  rw [hTy]
  dsimp only
  rw [show resolvePlaceDestV2 body.locals l m ⟨lid, []⟩ ty = .ok (.local lid)
    from rfl]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hW]
  dsimp only
  rw [hHaz]

/-- Storing a well-typed value into a live, uninitialized local. -/
theorem writePlaceDestV2_local {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some N)
    (hSet :
      Trusted.MirSemantics.setElem? locals lid (im val) = some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val = .ok (locals', mem) := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

/-- Entry state of `body` for a query it accepts. -/
theorem initStateV2_ok {p : Program} {body : Body} {args : List Val}
    {cm : CallerMemory}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValidV2 body = true)
    (hCast : castTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hValid : ValidEntryArgsV2 body ⟨args, cm⟩)
    (hAct : assertConditionTypesValid body = true := by decide) :
    initStateV2 p ⟨args, cm⟩ = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body args 0 body.locals, none, none, none⟩], cm,
      entryMemoryForArgsV2 cm ((body.locals.drop 1).take body.argumentCount)
        args⟩ := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  exact Anneal.MirWp.initStateV2_ok_of hPW hPV hCM hEntry hNonEmpty hArgLt
    hSto hDiscr hCast hAct hLocs hArgs hRefs hDisj

/-! ## `u8` values -/

theorem checkVal_u8 {bits : BitVec 128} (hT : truncateBits .i8 bits = bits) :
    checkValV2 (u8 bits) (.int .i8 false) = true :=
  checkVal_int_iff.mpr ⟨bits, rfl, hT⟩

/-- A query accepted by a `fn(u8)` body passes a single truncated `u8`. -/
theorem args_u8 {args : List Val}
    (h : checkArgsMatchV2 args [.int .i8 false] = true) :
    ∃ bits, args = [u8 bits] ∧ truncateBits .i8 bits = bits := by
  match args, h with
  | [], h => cases h
  | v :: vs, h =>
    have hv : checkValV2 v (.int .i8 false) = true := by
      cases hc : checkValV2 v (.int .i8 false) with
      | true => rfl
      | false => rw [checkArgsMatchV2, hc] at h; cases h
    have hvs : vs = [] := by
      cases vs with
      | nil => rfl
      | cons _ _ => rw [checkArgsMatchV2, hv] at h; cases h
    subst hvs
    cases v with
    | scalar sv =>
      let ⟨bits, hEq, hT⟩ := checkVal_int_iff.mp hv
      exact ⟨bits, by rw [hEq], hT⟩
    | optionVal o => cases o <;> cases hv
    | boxPtr _ o => cases o <;> cases hv
    | _ => cases hv

theorem decode_u8 {bits : BitVec 128} (hT : truncateBits .i8 bits = bits) :
    decodeScalar ⟨.i8, false, bits⟩ = Int.ofNat bits.toNat := by
  change Int.ofNat (truncateBits .i8 bits).toNat = _
  rw [hT]

theorem bvOfInt_ofNat (k : Nat) :
    bvOfInt 128 (Int.ofNat k) = BitVec.ofNat 128 k := by
  apply bitVec_eq_of_toNat_eq
  change Nat.mod (Nat.mod k (Nat.pow 2 128)) (2 ^ 128) = Nat.mod k (2 ^ 128)
  exact Nat.mod_mod k (2 ^ 128)

theorem truncate_u8_ofNat {k : Nat} (h : k < 256) :
    truncateBits .i8 (BitVec.ofNat 128 k) = BitVec.ofNat 128 k := by
  apply truncateBits_of_toNat_lt
  change k % 2 ^ 128 < 256
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]
  exact h

theorem truncateScalar_u8 {k : Nat} (h : k < 256) :
    truncateScalar .i8 false (Int.ofNat k) =
      .ok (⟨.i8, false, BitVec.ofNat 128 k⟩, false) := by
  unfold truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfInt_ofNat, truncate_u8_ofNat h, bne_self_eq_false]

/-- `AddWithOverflow(x, 1)` on a `u8` that does not overflow. -/
theorem addWithOverflow_u8 {bits : BitVec 128}
    (hT : truncateBits .i8 bits = bits) (hLt : bits.toNat + 1 < 256) :
    evalBinOp .addWithOverflow (u8 bits) (u8 1#128) =
      .ok (.tuple [u8 (BitVec.ofNat 128 (bits.toNat + 1)), .bool false]) := by
  have hNotNeg : ¬ (Int.ofNat (bits.toNat + 1) < 0) := fun h => nomatch h
  have hNotGe :
      ¬ (Int.ofNat (bits.toNat + 1) ≥ HPow.hPow (2 : Int) 128) := by
    intro h
    have h' : Int.ofNat (2 ^ 128) ≤ Int.ofNat (bits.toNat + 1) := h
    exact Nat.not_le_of_gt (Nat.lt_trans hLt (by decide)) (Int.ofNat_le.mp h')
  have hOne : decodeScalar ⟨.i8, false, 1#128⟩ = Int.ofNat 1 := rfl
  have hAdd :
      Int.ofNat bits.toNat + Int.ofNat 1 = Int.ofNat (bits.toNat + 1) := rfl
  unfold evalBinOp evalArithOp
  dsimp only
  rw [decode_u8 hT, hOne, hAdd, truncateScalar_u8 hLt,
    decide_eq_false hNotNeg, decide_eq_false hNotGe]
  rfl

/-- Wrapping `Add(x, 1)` on a `u8`. -/
theorem add_u8 {bits : BitVec 128} (hT : truncateBits .i8 bits = bits)
    (hLt : bits.toNat < 256) :
    evalBinOp .add (u8 bits) (u8 1#128) =
      .ok (u8 (BitVec.ofNat 128 ((bits.toNat + 1) % 256))) := by
  have hOne : decodeScalar ⟨.i8, false, 1#128⟩ = Int.ofNat 1 := rfl
  have hAdd :
      Int.ofNat bits.toNat + Int.ofNat 1 = Int.ofNat (bits.toNat + 1) := rfl
  have h1 : bits.toNat + 1 < 2 ^ 128 :=
    Nat.lt_trans (Nat.succ_lt_succ hLt) (by decide)
  have h2 : (bits.toNat + 1) % 256 < 2 ^ 128 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [evalBinOp_unsigned_add, decode_u8 hT, hOne, hAdd, bvOfInt_ofNat]
  have hEq : truncateBits .i8 (BitVec.ofNat 128 (bits.toNat + 1)) =
      BitVec.ofNat 128 ((bits.toNat + 1) % 256) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits]
    change (bits.toNat + 1) % 2 ^ 128 % 256 =
      (bits.toNat + 1) % 256 % 2 ^ 128
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  rw [hEq]

end StepLemmas
