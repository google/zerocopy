-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Expected
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## `usize` values -/

private abbrev isz : MirTy := .int .isize false

private abbrev usz (x : BitVec 128) : Val := .scalar ⟨.isize, false, x⟩

private abbrev scal (n : Nat) : Val := usz (BitVec.ofNat 128 n)

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by decide

private theorem toNat_lt_of_wf {x : BitVec 128}
    (h : ScalarVal.wf ⟨.isize, false, x⟩ = true) : x.toNat < Nat.pow 2 64 := by
  have hEq : truncateBits .isize x = x := by
    unfold ScalarVal.wf at h
    exact eq_of_beq h
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem trunc_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  change n % Nat.pow 2 128 < Nat.pow 2 64
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]
  exact h

private theorem wf_ofNat {s : Bool} {n : Nat} (h : n < Nat.pow 2 64) :
    ScalarVal.wf ⟨.isize, s, BitVec.ofNat 128 n⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [trunc_ofNat h]
  exact beq_self_eq_true _

private theorem checkV2_scalar {s : Bool} {x : BitVec 128}
    (h : ScalarVal.wf ⟨.isize, s, x⟩ = true) :
    checkValV2 (.scalar ⟨.isize, s, x⟩) (.int .isize s) = true := by
  dsimp only [checkValV2, checkVal, Val.ty?]
  rw [h, ite_bool_true rfl]
  exact mirTy_beq_refl _

private theorem checkV2_some_scal {n : Nat} (h : n < Nat.pow 2 64) :
    checkValV2 (.optionVal (some (scal n))) (.option isz) = true := by
  dsimp only [checkValV2, checkVal, Val.ty?]
  rw [wf_ofNat h]
  rfl

/-! ## Checked arithmetic without overflow -/

private theorem trunc_scal {n : Nat} (h : n < Nat.pow 2 64) :
    truncateScalar .isize false (Int.ofNat n) =
      .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false) := by
  have hB : bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
    change BitVec.ofNat 128 (n % Nat.pow 2 128) = _
    rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]
  unfold truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [hB, trunc_ofNat h, bne_self_eq_false]

private theorem not_lt_zero (n : Nat) : ¬ (Int.ofNat n < 0) :=
  fun h => nomatch h

private theorem not_pow128_le {n : Nat} (h : n < Nat.pow 2 128) :
    ¬ (HPow.hPow (2 : Int) 128 ≤ Int.ofNat n) := by
  intro hGe
  have hPow : HPow.hPow (2 : Int) 128 =
      Int.ofNat (Nat.succ (Nat.pow 2 128 - 1)) := by decide
  rw [hPow] at hGe
  change Int.NonNeg
    (Int.subNatNat n (Nat.succ (Nat.pow 2 128 - 1))) at hGe
  have hS : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
  rw [hS] at hGe
  unfold Int.subNatNat at hGe
  cases hSub : Nat.pow 2 128 - n with
  | zero => exact Nat.not_le_of_gt h (Nat.le_of_sub_eq_zero hSub)
  | succ k => rw [hSub] at hGe; nomatch hGe

/-- An in-range result neither overflows `usize` nor the 128-bit carrier. -/
private theorem trunc_host {n : Nat} (h : n < Nat.pow 2 64) :
    truncateScalarWithHostOverflow .isize false (Int.ofNat n) =
      .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false) := by
  unfold truncateScalarWithHostOverflow intHostOverflow
  rw [trunc_scal h]
  dsimp only
  rw [ite_bool_false rfl, decide_eq_false (not_lt_zero _),
    decide_eq_false (not_pow128_le (Nat.lt_trans h pow64_lt_pow128))]
  rfl

private theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
  cases b with
  | zero => rfl
  | succ k =>
    change Int.subNatNat a (Nat.succ k) = _
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]

private theorem checkedAdd_ok {x y : BitVec 128} {m : MemoryState}
    (hx : x.toNat < Nat.pow 2 64) (hy : y.toNat < Nat.pow 2 64)
    (hr : x.toNat + y.toNat < Nat.pow 2 64) :
    execCoreCallOpWithMem m (.numCheckedAdd .isize false)
        [(isz, usz x), (isz, usz y)] (.option isz) =
      .ok (.optionVal (some (scal (x.toNat + y.toNat))), m) := by
  change execCheckedArith .add .isize false ⟨.isize, false, x⟩
    ⟨.isize, false, y⟩ m = _
  unfold execCheckedArith
  dsimp only
  rw [decodeScalar_unsigned_of_lt hx, decodeScalar_unsigned_of_lt hy,
    show Int.ofNat x.toNat + Int.ofNat y.toNat =
      Int.ofNat (x.toNat + y.toNat) from rfl, trunc_host hr]
  rfl

private theorem checkedSub_ok {x y : BitVec 128} {m : MemoryState}
    (hx : x.toNat < Nat.pow 2 64) (hy : y.toNat < Nat.pow 2 64)
    (hle : y.toNat ≤ x.toNat) :
    execCoreCallOpWithMem m (.numCheckedSub .isize false)
        [(isz, usz x), (isz, usz y)] (.option isz) =
      .ok (.optionVal (some (scal (x.toNat - y.toNat))), m) := by
  change execCheckedArith .sub .isize false ⟨.isize, false, x⟩
    ⟨.isize, false, y⟩ m = _
  unfold execCheckedArith
  dsimp only
  rw [decodeScalar_unsigned_of_lt hx, decodeScalar_unsigned_of_lt hy,
    ofNat_sub_ofNat hle,
    trunc_host (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx)]
  rfl

private theorem checkedMul_ok {x y : BitVec 128} {m : MemoryState}
    (hx : x.toNat < Nat.pow 2 64) (hy : y.toNat < Nat.pow 2 64)
    (hr : x.toNat * y.toNat < Nat.pow 2 64) :
    execCoreCallOpWithMem m (.numCheckedMul .isize false)
        [(isz, usz x), (isz, usz y)] (.option isz) =
      .ok (.optionVal (some (scal (x.toNat * y.toNat))), m) := by
  change execCheckedArith .mul .isize false ⟨.isize, false, x⟩
    ⟨.isize, false, y⟩ m = _
  unfold execCheckedArith
  dsimp only
  rw [decodeScalar_unsigned_of_lt hx, decodeScalar_unsigned_of_lt hy,
    show Int.ofNat x.toNat * Int.ofNat y.toNat =
      Int.ofNat (x.toNat * y.toNat) from rfl, trunc_host hr]
  rfl

/-! ## The shared body shape

The three captured bodies differ only in the `checked_*` contract that `bb0`
calls. -/

private def bb0 (op : CoreCallOp) : BasicBlock where
  statements := [.storageLive 3, .storageLive 4,
    .assign ⟨4, []⟩ (.use (.copy ⟨1, []⟩)), .storageLive 5,
    .assign ⟨5, []⟩ (.use (.copy ⟨2, []⟩))]
  terminator := .coreCall op [.move ⟨4, []⟩, .move ⟨5, []⟩] ⟨3, []⟩ (some 1)
    .continue_
  cleanup := false

private def arithBody (op : CoreCallOp) (ident : String) : Body where
  argumentCount := 2
  isUnsafe := true
  locals := [isz, isz, isz, .option isz, isz, isz, .int .isize true, isz,
    .never]
  basicBlocks := [
    bb0 op,
    { statements := [.storageDead 5, .storageDead 4, .nop,
        .assign ⟨6, []⟩ (.discriminant ⟨3, []⟩)],
      terminator := .switchInt (.move ⟨6, []⟩)
        ⟨[(BitVec.ofNat 128 0, 3), (BitVec.ofNat 128 1, 4)], 2⟩,
      cleanup := false },
    { statements := [], terminator := .unreachable, cleanup := false },
    { statements := [.storageLive 8], terminator := .unsupported,
      cleanup := false },
    { statements := [.storageLive 7,
        .assign ⟨7, []⟩ (.use (.copy ⟨3, [.downcast 1, .field 0 isz]⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨7, []⟩)), .storageDead 7,
        .storageDead 3],
      terminator := .return_,
      cleanup := false }]
  identity := ident

private abbrev IsCheckedOp (op : CoreCallOp) : Prop :=
  op = .numCheckedAdd .isize false ∨ op = .numCheckedSub .isize false ∨
    op = .numCheckedMul .isize false

/-! ## Stepping -/

private theorem stmt_step {p : Program} {body : Body} {bb : BasicBlock}
    {d b i : Nat} {l : List LocalSlot} {cm : CallerMemory} {m : MemoryState}
    {stmt : StatementKind} {s' : State} {post : TerminalOut → Prop}
    (hBody : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = some stmt)
    (hEval : evalStatementV2 body (frameV2 d b i l) m cm stmt = .step s')
    (hRest : RunsV2 p post s') :
    RunsV2 p post (stateV2 (frameV2 d b i l) cm m) :=
  runsV2_step ((evalStepV2_stmt hBody hBB hStmt).trans hEval) hRest

private theorem term_step {p : Program} {body : Body} {bb : BasicBlock}
    {d b i : Nat} {l : List LocalSlot} {cm : CallerMemory} {m : MemoryState}
    {s' : State} {post : TerminalOut → Prop}
    (hBody : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hEnd : Nat.beq i bb.statements.length = true)
    (hEval : evalTerminatorV2 body bb (frameV2 d b i l) m cm p.panicStrategy
      p.hasLocalPanicHandler p.overflowChecks = .step s')
    (hRest : RunsV2 p post s') :
    RunsV2 p post (stateV2 (frameV2 d b i l) cm m) :=
  runsV2_step ((evalStepV2_term hBody hBB hStmt hEnd).trans hEval) hRest

/-- The `checked_*` call in `bb0` stores `Some(r)` in `_3` and continues at
`bb1`. -/
private theorem call_step {op : CoreCallOp} {ident : String} {d : DefId}
    {cm : CallerMemory} {m : MemoryState} {ps : PanicStrategy} {hl oc : Bool}
    {x y : BitVec 128} {r : Nat} (hK : IsCheckedOp op)
    (hr : r < Nat.pow 2 64)
    (hOp : execCoreCallOpWithMem m op [(isz, usz x), (isz, usz y)]
      (.option isz) = .ok (.optionVal (some (scal r)), m)) :
    evalTerminatorV2 (arithBody op ident) (bb0 op)
      (frameV2 d 0 5 [.immediate none, .immediate (some (usz x)),
        .immediate (some (usz y)), .immediate none,
        .immediate (some (usz x)), .immediate (some (usz y)),
        .immediate none, .dead, .dead]) m cm ps hl oc =
      .step (stateV2 (frameV2 d 1 0 [.immediate none,
        .immediate (some (usz x)), .immediate (some (usz y)),
        .immediate (some (.optionVal (some (scal r)))),
        .immediate none, .immediate none, .immediate none, .dead, .dead])
        cm m) := by
  refine Or.elim hK (fun h => ?_) (fun h => Or.elim h (fun h => ?_)
    (fun h => ?_))
  all_goals
    subst h
    dsimp only [evalTerminatorV2, bb0, arithBody, evalArgOperandsV2,
      evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
    dsimp only
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
    dsimp only
    rw [hOp]
    dsimp only
    rw [writePlaceV2_immediate_ok (checkV2_some_scal hr) (by rfl) (by rfl)]
    rfl

/-- From `bb4`, the body copies `r` out of `Some(r)` and returns it. -/
private theorem run_bb4 {p : Program} {d : DefId} {op : CoreCallOp}
    {ident : String} {cm : CallerMemory} {x y : BitVec 128} {r : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies d =
      some (arithBody op ident))
    (hr : r < Nat.pow 2 64)
    (hExt : extractCallerMemory cm (entryMemoryWithCaller cm) = cm) :
    RunsV2 p (fun o => o = .returned ⟨scal r, cm⟩)
      (stateV2 (frameV2 d 4 0 [.immediate none, .immediate (some (usz x)),
        .immediate (some (usz y)),
        .immediate (some (.optionVal (some (scal r)))), .dead, .dead,
        .immediate none, .dead, .dead]) cm (entryMemoryWithCaller cm)) := by
  -- StorageLive(_7); _7 = copy ((_3 as Some).0); _0 = copy _7;
  -- StorageDead(_7); StorageDead(_3)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply runsV2_step (evalStepV2_assign_local hBody (by rfl) (by rfl) (by rfl)
    (by rfl)
    (writePlaceDestV2_immediate_ok (checkV2_scalar (wf_ofNat hr)) (by rfl)
      (by rfl)))
  apply runsV2_step (evalStepV2_assign_local hBody (by rfl) (by rfl) (by rfl)
    (evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl))
    (writePlaceDestV2_immediate_ok (checkV2_scalar (wf_ofNat hr)) (by rfl)
      (by rfl)))
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  -- return
  exact runsV2_done (evalStepV2_return_ok (retVal := scal r) hBody (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl)) (by rw [extractReturnMemoryV2_entryMemory, hExt])

/-- From `bb1`, the body tests the discriminant of `Some(r)` and jumps to
`bb4`. -/
private theorem run_bb1 {p : Program} {d : DefId} {op : CoreCallOp}
    {ident : String} {cm : CallerMemory} {x y : BitVec 128} {r : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies d =
      some (arithBody op ident))
    (hr : r < Nat.pow 2 64)
    (hExt : extractCallerMemory cm (entryMemoryWithCaller cm) = cm) :
    RunsV2 p (fun o => o = .returned ⟨scal r, cm⟩)
      (stateV2 (frameV2 d 1 0 [.immediate none, .immediate (some (usz x)),
        .immediate (some (usz y)),
        .immediate (some (.optionVal (some (scal r)))), .immediate none,
        .immediate none, .immediate none, .dead, .dead]) cm
        (entryMemoryWithCaller cm)) := by
  -- StorageDead(_5); StorageDead(_4); nop; _6 = discriminant(_3)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply runsV2_step (evalStepV2_assign_local hBody (by rfl) (by rfl) (by rfl)
    (by rfl)
    (writePlaceDestV2_immediate_ok (checkV2_scalar (s := true)
      (wf_ofNat (n := 1) (by decide))) (by rfl) (by rfl)))
  -- switchInt(move _6) [0 -> bb3, 1 -> bb4]
  apply term_step hBody (by rfl) (by rfl) (by rfl) (by rfl)
  exact run_bb4 hBody hr hExt

/-- From entry, a body of shape `arithBody op ident` whose `checked_*` call
returns `Some(r)` returns `r` and the caller's memory. -/
private theorem run_ok {p : Program} {d : DefId} {op : CoreCallOp}
    {ident : String} {cm : CallerMemory} {x y : BitVec 128} {r : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies d =
      some (arithBody op ident))
    (hK : IsCheckedOp op)
    (hx : ScalarVal.wf ⟨.isize, false, x⟩ = true)
    (hy : ScalarVal.wf ⟨.isize, false, y⟩ = true)
    (hr : r < Nat.pow 2 64)
    (hOp : execCoreCallOpWithMem (entryMemoryWithCaller cm) op
      [(isz, usz x), (isz, usz y)] (.option isz) =
        .ok (.optionVal (some (scal r)), entryMemoryWithCaller cm))
    (hExt : extractCallerMemory cm (entryMemoryWithCaller cm) = cm) :
    RunsV2 p (fun o => o = .returned ⟨scal r, cm⟩)
      (stateV2 (frameV2 d 0 0 [.immediate none, .immediate (some (usz x)),
        .immediate (some (usz y)), .dead, .dead, .dead, .immediate none, .dead,
        .dead]) cm (entryMemoryWithCaller cm)) := by
  -- StorageLive(_3); StorageLive(_4); _4 = copy _1; StorageLive(_5);
  -- _5 = copy _2
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply runsV2_step (evalStepV2_assign_local hBody (by rfl) (by rfl) (by rfl)
    (evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl))
    (writePlaceDestV2_immediate_ok (checkV2_scalar hx) (by rfl) (by rfl)))
  apply stmt_step hBody (by rfl) (by rfl) (by rfl)
  apply runsV2_step (evalStepV2_assign_local hBody (by rfl) (by rfl) (by rfl)
    (evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl))
    (writePlaceDestV2_immediate_ok (checkV2_scalar hy) (by rfl) (by rfl)))
  -- _3 = checked_*(move _4, move _5) -> bb1
  apply term_step hBody (by rfl) (by rfl) (by rfl) (call_step hK hr hOp)
  exact run_bb1 hBody hr hExt

/-! ## Per-body correctness -/

private theorem body_ok {k : DefId} {op : CoreCallOp} {ident : String}
    {f : Nat → Nat → Nat} {q : Query}
    (hBodyK : Trusted.MirSemantics.getElem? Captured.program.bodies k =
      some (arithBody op ident))
    (hK : IsCheckedOp op)
    (hAdm : BodyStaticAdmittedV2 Captured.program (arithBody op ident) = true)
    (hValid : ValidEntryArgsV2 (arithBody op ident) q)
    (hF : ∀ x y : BitVec 128, q.args = [usz x, usz y] →
      x.toNat < Nat.pow 2 64 → y.toNat < Nat.pow 2 64 →
      f x.toNat y.toNat < Nat.pow 2 64 ∧
      ∀ m : MemoryState, execCoreCallOpWithMem m op
        [(isz, usz x), (isz, usz y)] (.option isz) =
          .ok (.optionVal (some (scal (f x.toNat y.toNat))), m)) :
    WellFormedV2 (entryProgForBody Captured.program k) q ∧
    match q.args with
    | [.scalar a, .scalar b] =>
      Spec.returnsExactly Captured.program k q
        (.returned ⟨Spec.usizeVal (f a.bits.toNat b.bits.toNat), q.callerMem⟩)
    | _ => False := by
  let ⟨hCM, hMatch, _, _⟩ := hValid
  have hMatch' : checkArgsMatchV2 q.args [isz, isz] = true := hMatch
  let ⟨v0, v1, hArgs, h0, h1⟩ := checkArgsMatchV2_pair_inv hMatch'
  let ⟨x, hv0, hx⟩ := checkValV2_isize_inv h0
  let ⟨y, hv1, hy⟩ := checkValV2_isize_inv h1
  subst hv0 hv1
  let ⟨hr, hOp⟩ := hF x y hArgs (toNat_lt_of_wf hx) (toNat_lt_of_wf hy)
  let ctx : BodyCtx := ⟨Captured.program, k, arithBody op ident⟩
  have hInit :
      initStateV2 (entryProgForBody Captured.program k) q =
        .ok (stateV2 (frameV2 k 0 0
          (initLocalsLoop (arithBody op ident) q.args 0
            (arithBody op ident).locals))
          q.callerMem (entryMemoryWithCaller q.callerMem)) :=
    ctx.initStateV2_ok_frameV2 hBodyK hAdm hValid
  have hL : initLocalsLoop (arithBody op ident) q.args 0
      (arithBody op ident).locals =
      [.immediate none, .immediate (some (usz x)), .immediate (some (usz y)),
        .dead, .dead, .dead, .immediate none, .dead, .dead] := by
    rw [hArgs]
    rfl
  rw [hL] at hInit
  have hRuns := run_ok (p := entryProgForBody Captured.program k) hBodyK hK
    hx hy hr (hOp _) (extractCallerMemory_entry q.callerMem hCM)
  let ⟨_, hExec⟩ := execProgV2_of_runsV2 hInit hRuns
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  refine ⟨hRes.1, ?_⟩
  rw [hArgs]
  exact ⟨hRes.2.1, hRes.2.2.2 _ rfl⟩

private theorem add_pre {q : Query} {x y : BitVec 128} (h : Spec.addSafety q)
    (hA : q.args = [usz x, usz y]) : x.toNat + y.toNat < Nat.pow 2 64 := by
  unfold Spec.addSafety at h
  rw [hA] at h
  exact h

private theorem sub_pre {q : Query} {x y : BitVec 128} (h : Spec.subSafety q)
    (hA : q.args = [usz x, usz y]) : y.toNat ≤ x.toNat := by
  unfold Spec.subSafety at h
  rw [hA] at h
  exact h

private theorem mul_pre {q : Query} {x y : BitVec 128} (h : Spec.mulSafety q)
    (hA : q.args = [usz x, usz y]) : x.toNat * y.toNat < Nat.pow 2 64 := by
  unfold Spec.mulSafety at h
  rw [hA] at h
  exact h

private theorem add_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) (hSafe : Spec.addSafety q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [.scalar a, .scalar b] =>
      Spec.returnsExactly Captured.program 0 q
        (.returned ⟨Spec.usizeVal (a.bits.toNat + b.bits.toNat), q.callerMem⟩)
    | _ => False :=
  body_ok (op := .numCheckedAdd .isize false) (f := fun a b => a + b)
    (ident := Captured.body_0.identity) rfl (.inl rfl) (by decide) hValid
    (fun _ _ hA hx hy =>
      ⟨add_pre hSafe hA, fun _ => checkedAdd_ok hx hy (add_pre hSafe hA)⟩)

private theorem sub_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) (hSafe : Spec.subSafety q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    match q.args with
    | [.scalar a, .scalar b] =>
      Spec.returnsExactly Captured.program 1 q
        (.returned ⟨Spec.usizeVal (a.bits.toNat - b.bits.toNat), q.callerMem⟩)
    | _ => False :=
  body_ok (op := .numCheckedSub .isize false) (f := fun a b => a - b)
    (ident := Captured.body_1.identity) rfl (.inr (.inl rfl)) (by decide)
    hValid
    (fun _ _ hA hx hy =>
      ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx,
        fun _ => checkedSub_ok hx hy (sub_pre hSafe hA)⟩)

private theorem mul_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) (hSafe : Spec.mulSafety q) :
    WellFormedV2 (entryProgForBody Captured.program 2) q ∧
    match q.args with
    | [.scalar a, .scalar b] =>
      Spec.returnsExactly Captured.program 2 q
        (.returned ⟨Spec.usizeVal (a.bits.toNat * b.bits.toNat), q.callerMem⟩)
    | _ => False :=
  body_ok (op := .numCheckedMul .isize false) (f := fun a b => a * b)
    (ident := Captured.body_2.identity) rfl (.inr (.inr rfl)) (by decide)
    hValid
    (fun _ _ hA hx hy =>
      ⟨mul_pre hSafe hA, fun _ => checkedMul_ok hx hy (mul_pre hSafe hA)⟩)

/-! ## Identities -/

private theorem id0 : Captured.body_0.identity = Spec.addIdentity := by decide
private theorem id1 : Captured.body_1.identity = Spec.subIdentity := by decide
private theorem id2 : Captured.body_2.identity = Spec.mulIdentity := by decide
private theorem sub_ne_add : ¬ Spec.subIdentity = Spec.addIdentity := by
  decide
private theorem mul_ne_add : ¬ Spec.mulIdentity = Spec.addIdentity := by
  decide
private theorem mul_ne_sub : ¬ Spec.mulIdentity = Spec.subIdentity := by
  decide

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, hBody =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      have hS := hSafe rfl
      change Spec.safetyPre Captured.body_0.identity q at hS
      unfold Spec.safetyPre at hS
      rw [id0, ite_prop_true rfl] at hS
      exact (add_ok q hValid hS).1
    | 1, hBody =>
      change some Captured.body_1 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      have hS := hSafe rfl
      change Spec.safetyPre Captured.body_1.identity q at hS
      unfold Spec.safetyPre at hS
      rw [id1, ite_prop_false sub_ne_add, ite_prop_true rfl] at hS
      exact (sub_ok q hValid hS).1
    | 2, hBody =>
      change some Captured.body_2 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      have hS := hSafe rfl
      change Spec.safetyPre Captured.body_2.identity q at hS
      unfold Spec.safetyPre at hS
      rw [id2, ite_prop_false mul_ne_add, ite_prop_false mul_ne_sub,
        ite_prop_true rfl] at hS
      exact (mul_ok q hValid hS).1
    | _ + 3, hBody =>
      change none = some body at hBody
      cases hBody
  · intro defId body hBody
    match defId, hBody with
    | 0, hBody =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      unfold Spec.bodyPost
      rw [id0, ite_prop_true rfl]
      exact fun q hValid hSafe => (add_ok q hValid hSafe).2
    | 1, hBody =>
      change some Captured.body_1 = some body at hBody
      cases hBody
      unfold Spec.bodyPost
      rw [id1, ite_prop_false sub_ne_add, ite_prop_true rfl]
      exact fun q hValid hSafe => (sub_ok q hValid hSafe).2
    | 2, hBody =>
      change some Captured.body_2 = some body at hBody
      cases hBody
      unfold Spec.bodyPost
      rw [id2, ite_prop_false mul_ne_add, ite_prop_false mul_ne_sub,
        ite_prop_true rfl]
      exact fun q hValid hSafe => (mul_ok q hValid hSafe).2
    | _ + 3, hBody =>
      change none = some body at hBody
      cases hBody

end Proof
