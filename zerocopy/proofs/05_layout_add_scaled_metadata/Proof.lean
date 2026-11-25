-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Expected
import Anneal.MirWp

/-!
`add_scaled_metadata` calls the `core::num` methods `unchecked_mul` and
`unchecked_add`, so `bodyVerified_of_safe` (which requires a call-free body)
does not apply. Instead we run the deterministic `c = 0` executor
(`execOutcomeState`) through all 21 steps by hand, across both pushed sysroot
frames, and lift the run to `WellFormed`, `Behavior`, and `¬ Diverges`.
-/

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Executor plumbing -/

abbrev isz : MirTy := .int .isize false

private theorem exec_step {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s s' : State}
    (h : evalStep p 0 s = .step s')
    (k : execOutcomeState p onDone onFault fuel s') :
    execOutcomeState p onDone onFault (fuel + 1) s := by
  dsimp only [execOutcomeState, Anneal.Framework.StepWp.execStepOutcome]
  rw [Anneal.Framework.StepWp.execStepPred_succ_iff, h]
  exact k

private theorem exec_done {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s : State}
    {out : TerminalOut} (h : evalStep p 0 s = .done out) (k : onDone out) :
    execOutcomeState p onDone onFault (fuel + 1) s := by
  dsimp only [execOutcomeState, Anneal.Framework.StepWp.execStepOutcome]
  rw [Anneal.Framework.StepWp.execStepPred_succ_iff, h]
  exact k

/-- `writePlace` after its `checkVal` guard has passed. -/
private noncomputable def writeChecked (locals : List LocalSlot)
    (mem : MemoryState) (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  match Trusted.MirSemantics.getElem? locals dstLocalId with
  | none => .error .unsupported
  | some LocalSlot.dead => .error .undefined
  | some (.immediate _) =>
    match setElem? locals dstLocalId (.immediate (some val)) with
    | some locals' => .ok (locals', mem)
    | none => .error .unsupported
  | some (.indirect mplace) =>
    match storeIndirect mem dstTy mplace val with
    | .ok mem' => .ok (locals, mem')
    | .error k => .error k
  | some (.partialTuple _) => .error .unsupported

/-- Discharges the only data-dependent guard of `writePlace` on a symbolic
value; the rest of a step then reduces by `rfl`. -/
private theorem writePlace_of_check {locals : List LocalSlot}
    {mem : MemoryState} {i : LocalId} {ty : MirTy} {v : Val}
    (h : checkVal v ty = true) :
    writePlace locals mem i ty v = writeChecked locals mem i ty v := by
  unfold writePlace
  rw [h]
  rfl

/-! ## Machine states -/

abbrev N : LocalSlot := .immediate none
abbrev D : LocalSlot := .dead
abbrev I (v : Val) : LocalSlot := .immediate (some v)

abbrev mulOp : SysrootNumOp := ⟨.uncheckedMul, .isize, false⟩
abbrev addOp : SysrootNumOp := ⟨.uncheckedAdd, .isize, false⟩

abbrev rootF (blk stmt : Nat) (ls : List LocalSlot) : FrameState :=
  { defId := 0, blockIdx := blk, stmtIdx := stmt, locals := ls }

/-- A pushed sysroot frame returning into caller local `dst` and resuming the
caller at block `tgt`. -/
abbrev calleeF (op : SysrootNumOp) (stmt : Nat) (ls : List LocalSlot)
    (dst tgt : Nat) : FrameState :=
  { defId := 0, blockIdx := 0, stmtIdx := stmt, locals := ls,
    sysrootOp? := some op, retDst? := some ⟨dst, []⟩,
    retTarget? := some tgt }

noncomputable abbrev st (fs : List FrameState) : State :=
  { frames := fs, callerMem := ⟨[]⟩, mem := entryMemory }

noncomputable abbrev P : Program := entryProgForBody Captured.program 0

/-! ## Sysroot callee body `_0 = op(copy _1, copy _2)` -/

private theorem rv_binop (op : BinOp) (a b v : Val)
    (h : evalBinOp op a b = .ok v) :
    evalRvalue [isz, isz, isz] [N, I a, I b] entryMemory isz
        (.binaryOp op (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)) =
      .ok (v, [N, I a, I b], entryMemory) := by
  conv => lhs; whnf
  rw [h]

private theorem callee_assign (kind : SysrootNumKind) (a b v : Val)
    (dst tgt : Nat) (h : evalBinOp (sysrootNumBinOp kind) a b = .ok v)
    (hv : checkVal v isz = true) :
    evalStatement (sysrootNumBody ⟨kind, .isize, false⟩)
        (calleeF ⟨kind, .isize, false⟩ 0 [N, I a, I b] dst tgt) entryMemory
        ⟨[]⟩
        (.assign ⟨0, []⟩ (.binaryOp (sysrootNumBinOp kind)
          (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))) =
      .step (st [calleeF ⟨kind, .isize, false⟩ 1 [I v, I a, I b]
        dst tgt]) := by
  conv => lhs; whnf
  erw [rv_binop _ _ _ _ h]
  conv => lhs; whnf
  rw [writePlace_of_check hv]
  rfl

/-! ## The 21-step run

`x`, `y`, `z` are `base`, `metadata`, `multiple`; `w = y * z` and
`r = x + w` are the sysroot results, abstracted by their `evalBinOp`
equations. -/

private theorem run (x y z w r : Val) (hx : checkVal x isz = true)
    (hy : checkVal y isz = true) (hz : checkVal z isz = true)
    (hmul : evalBinOp .mulUnchecked y z = .ok w)
    (hw : checkVal w isz = true)
    (hadd : evalBinOp .addUnchecked x w = .ok r)
    (hr : checkVal r isz = true) :
    execOutcomeState P (fun o => o = .returned ⟨r, ⟨[]⟩⟩) (fun _ => False)
      21 (st [rootF 0 0 [N, I x, I y, I z, D, D, D, D, D]]) := by
  -- bb0: StorageLive(_4); StorageLive(_5); _5 = copy _2;
  -- StorageLive(_6); _6 = copy _3
  refine exec_step
    (s' := st [rootF 0 1 [N, I x, I y, I z, N, D, D, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 0 2 [N, I x, I y, I z, N, N, D, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 0 3 [N, I x, I y, I z, N, I y, D, D, D]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hy]
    rfl
  refine exec_step
    (s' := st [rootF 0 4 [N, I x, I y, I z, N, I y, N, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 0 5 [N, I x, I y, I z, N, I y, I z, D, D]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hz]
    rfl
  -- _4 = unchecked_mul(move _5, move _6) -> bb1
  refine exec_step
    (s' := st [calleeF mulOp 0 [N, I y, I z] 4 1,
      rootF 0 5 [N, I x, I y, I z, N, N, N, D, D]]) rfl ?_
  refine exec_step
    (s' := st [calleeF mulOp 1 [I w, I y, I z] 4 1,
      rootF 0 5 [N, I x, I y, I z, N, N, N, D, D]]) ?_ ?_
  · conv => lhs; whnf
    erw [callee_assign .uncheckedMul y z w 4 1 hmul hw]
    rfl
  refine exec_step
    (s' := st [rootF 1 0 [N, I x, I y, I z, I w, N, N, D, D]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hw]
    rfl
  -- bb1: StorageDead(_6); StorageDead(_5); StorageLive(_7);
  -- _7 = copy _1; StorageLive(_8); _8 = copy _4
  refine exec_step
    (s' := st [rootF 1 1 [N, I x, I y, I z, I w, N, D, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 1 2 [N, I x, I y, I z, I w, D, D, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 1 3 [N, I x, I y, I z, I w, D, D, N, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 1 4 [N, I x, I y, I z, I w, D, D, I x, D]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hx]
    rfl
  refine exec_step
    (s' := st [rootF 1 5 [N, I x, I y, I z, I w, D, D, I x, N]]) rfl ?_
  refine exec_step
    (s' := st [rootF 1 6 [N, I x, I y, I z, I w, D, D, I x, I w]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hw]
    rfl
  -- _0 = unchecked_add(move _7, move _8) -> bb2
  refine exec_step
    (s' := st [calleeF addOp 0 [N, I x, I w] 0 2,
      rootF 1 6 [N, I x, I y, I z, I w, D, D, N, N]]) rfl ?_
  refine exec_step
    (s' := st [calleeF addOp 1 [I r, I x, I w] 0 2,
      rootF 1 6 [N, I x, I y, I z, I w, D, D, N, N]]) ?_ ?_
  · conv => lhs; whnf
    erw [callee_assign .uncheckedAdd x w r 0 2 hadd hr]
    rfl
  refine exec_step
    (s' := st [rootF 2 0 [I r, I x, I y, I z, I w, D, D, N, N]]) ?_ ?_
  · conv => lhs; whnf
    rw [writePlace_of_check hr]
    rfl
  -- bb2: StorageDead(_8); StorageDead(_7); StorageDead(_4); return
  refine exec_step
    (s' := st [rootF 2 1 [I r, I x, I y, I z, I w, D, D, N, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 2 2 [I r, I x, I y, I z, I w, D, D, D, D]]) rfl ?_
  refine exec_step
    (s' := st [rootF 2 3 [I r, I x, I y, I z, D, D, D, D, D]]) rfl ?_
  exact exec_done rfl rfl

/-! ## `usize` arithmetic without overflow -/

abbrev scal (n : Nat) : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by decide

private theorem trunc_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  change n % Nat.pow 2 128 < Nat.pow 2 64
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]
  exact h

private theorem check_scal {n : Nat} (h : n < Nat.pow 2 64) :
    checkVal (scal n) isz = true := by
  show checkVal (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) isz = true
  rw [← trunc_ofNat h]
  exact checkVal_scalar_truncateBits .isize false _

private theorem decode_scal {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  rw [ite_bool_false rfl, trunc_ofNat h]
  show Int.ofNat (n % Nat.pow 2 128) = Int.ofNat n
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]

private theorem trunc_scal {n : Nat} (h : n < Nat.pow 2 64) :
    truncateScalar .isize false (Int.ofNat n) =
      .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false) := by
  have hB : bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
    show BitVec.ofNat 128 (n % Nat.pow 2 128) = _
    rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]
  unfold truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [hB, trunc_ofNat h, bne_self_eq_false]

private theorem not_lt_zero (n : Nat) : ¬ (Int.ofNat n < 0) :=
  fun h => nomatch h

private theorem not_ge_pow128 {n : Nat} (h : n < Nat.pow 2 128) :
    ¬ (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) := by
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

private theorem mul_scal {a c : Nat} (ha : a < Nat.pow 2 64)
    (hc : c < Nat.pow 2 64) (hac : a * c < Nat.pow 2 64) :
    evalBinOp .mulUnchecked (scal a) (scal c) = .ok (scal (a * c)) := by
  unfold evalBinOp evalArithOp
  dsimp only
  have hMulI : Int.ofNat a * Int.ofNat c = Int.ofNat (a * c) := rfl
  rw [decode_scal ha, decode_scal hc, hMulI, trunc_scal hac,
    decide_eq_false (not_lt_zero _),
    decide_eq_false (not_ge_pow128 (Nat.lt_trans hac pow64_lt_pow128))]
  rfl

private theorem add_scal {a c : Nat} (ha : a < Nat.pow 2 64)
    (hc : c < Nat.pow 2 64) (hac : a + c < Nat.pow 2 64) :
    evalBinOp .addUnchecked (scal a) (scal c) = .ok (scal (a + c)) := by
  unfold evalBinOp evalArithOp
  dsimp only
  have hAddI : Int.ofNat a + Int.ofNat c = Int.ofNat (a + c) := rfl
  rw [decode_scal ha, decode_scal hc, hAddI, trunc_scal hac,
    decide_eq_false (not_lt_zero _),
    decide_eq_false (not_ge_pow128 (Nat.lt_trans hac pow64_lt_pow128))]
  rfl

/-! ## Lifting the run to the boundary predicates -/

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem valid_args {x y z : Val} (hx : checkVal x isz = true)
    (hy : checkVal y isz = true) (hz : checkVal z isz = true) :
    ValidEntryArgs Captured.body_0 [x, y, z] := by
  show (checkVal x isz && (checkVal y isz && (checkVal z isz && true))) =
    true
  rw [hx, hy, hz]
  rfl

/-- Everything the boundary needs about one in-contract call. -/
private theorem outcome (b m k : Spec.UsizeWord)
    (hB : b.toNat + m.toNat * k.toNat < 2 ^ 64) :
    let q : Query := { args := [Spec.usizeVal b, Spec.usizeVal m,
      Spec.usizeVal k] }
    let out := TerminalOut.returned
      ⟨scal (b.toNat + m.toNat * k.toNat), ⟨[]⟩⟩
    WellFormed P q ∧ Behavior P q out ∧ ¬ Diverges P q ∧
      ∀ post : TerminalOut → Prop, post out → SatisfiesPost P q post := by
  have hb : b.toNat < Nat.pow 2 64 := b.isLt
  have hm : m.toNat < Nat.pow 2 64 := m.isLt
  have hk : k.toNat < Nat.pow 2 64 := k.isLt
  have hmk : m.toNat * k.toNat < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hB
  have hExec : execProg P 21
      { args := [Spec.usizeVal b, Spec.usizeVal m, Spec.usizeVal k] }
      (fun o => o = .returned
        ⟨scal (b.toNat + m.toNat * k.toNat), ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_eq_ok (p := P) (body := Captured.body_0)
      (args := [Spec.usizeVal b, Spec.usizeVal m, Spec.usizeVal k]) rfl
      body0_adm
      (valid_args (check_scal hb) (check_scal hm) (check_scal hk))]
    exact run _ _ _ _ _ (check_scal hb) (check_scal hm) (check_scal hk)
      (mul_scal hm hk hmk) (check_scal hmk)
      (add_scal hb hmk hB) (check_scal hB)
  exact spec_and_behavior_of_wp_eq (wpProg_of_execProg hExec)

private theorem body0_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) := by
  refine ⟨rfl, body0_adm, fun args _ hSafe => ?_⟩
  let ⟨_, b, m, k, hArgs, hB⟩ := hSafe rfl
  subst hArgs
  exact (outcome b m k hB).1

private theorem body0_total (b m k : Spec.UsizeWord)
    (hB : b.toNat + m.toNat * k.toNat < 2 ^ 64) :
    Spec.ReturnsTotal Captured.program 0
      [Spec.usizeVal b, Spec.usizeVal m, Spec.usizeVal k]
      (Spec.usizeVal (BitVec.ofNat 64 (b.toNat + m.toNat * k.toNat))) := by
  have hRet : Spec.usizeVal (BitVec.ofNat 64 (b.toNat + m.toNat * k.toNat))
      = scal (b.toNat + m.toNat * k.toNat) := by
    show scal ((b.toNat + m.toNat * k.toNat) % 2 ^ 64) = _
    rw [Nat.mod_eq_of_lt hB]
  rw [hRet]
  let h := outcome b m k hB
  exact ⟨h.2.2.2 _ rfl, h.2.2.1, h.2.1⟩

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
      ⟨body0_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · exact ⟨rfl, 0, Captured.body_0, rfl, rfl, rfl, rfl, body0_total⟩

end Proof
