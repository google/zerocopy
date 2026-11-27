-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp

/-!
`add_scaled_metadata` calls the `core::num` methods `unchecked_mul` and
`unchecked_add`, so `bodyVerified_of_safe` (which requires a call-free body)
does not apply. Instead we run the deterministic `c = 0` executor
(`execOutcomeState`) through all 21 steps by hand, across both pushed sysroot
frames, and lift the run to the contract obligations. Every obligation needs
the caller's safety bound `base + metadata * multiple ≤ usize::MAX`, since
without it the unchecked arithmetic is undefined behavior.
-/

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Executor plumbing -/

private abbrev isz : MirTy := .int .isize false

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

private abbrev N : LocalSlot := .immediate none
private abbrev D : LocalSlot := .dead
private abbrev I (v : Val) : LocalSlot := .immediate (some v)

private abbrev mulOp : SysrootNumOp := ⟨.uncheckedMul, .isize, false⟩
private abbrev addOp : SysrootNumOp := ⟨.uncheckedAdd, .isize, false⟩

private abbrev rootF (blk stmt : Nat) (ls : List LocalSlot) : FrameState :=
  { defId := 0, blockIdx := blk, stmtIdx := stmt, locals := ls }

/-- A pushed sysroot frame returning into caller local `dst` and resuming the
caller at block `tgt`. -/
private abbrev calleeF (op : SysrootNumOp) (stmt : Nat) (ls : List LocalSlot)
    (dst tgt : Nat) : FrameState :=
  { defId := 0, blockIdx := 0, stmtIdx := stmt, locals := ls,
    sysrootOp? := some op, retDst? := some ⟨dst, []⟩,
    retTarget? := some tgt }

private noncomputable abbrev st (fs : List FrameState) : State :=
  { frames := fs, callerMem := ⟨[]⟩, mem := entryMemory }

private noncomputable abbrev P : Program :=
  entryProgForBody Captured.program 0

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

private abbrev scal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by decide

private theorem trunc_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  change n % Nat.pow 2 128 < Nat.pow 2 64
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]
  exact h

private theorem check_scal {n : Nat} (h : n < Nat.pow 2 64) :
    checkVal (scal n) isz = true := by
  change checkVal (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) isz = true
  rw [← trunc_ofNat h]
  exact checkVal_scalar_truncateBits .isize false _

private theorem decode_scal {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  rw [ite_bool_false rfl, trunc_ofNat h]
  change Int.ofNat (n % Nat.pow 2 128) = Int.ofNat n
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]

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

/-! ## Decoding arguments and the contract -/

/-- Every valid `usize` value is `scal n` for some in-range `n`. -/
private theorem isz_inv {v : Val} (h : checkVal v isz = true) :
    ∃ n, n < Nat.pow 2 64 ∧ v = scal n := by
  let ⟨bits, hv, hT⟩ := checkVal_int_iff.mp h
  have hLt : bits.toNat < Nat.pow 2 64 := by
    rw [← hT, toNat_truncateBits]
    exact Nat.mod_lt _ (intWidth_modulus_pos .isize)
  have hBits : BitVec.ofNat 128 bits.toNat = bits := by
    apply bitVec_eq_of_toNat_eq
    change bits.toNat % Nat.pow 2 128 = bits.toNat
    exact Nat.mod_eq_of_lt bits.isLt
  refine ⟨bits.toNat, hLt, ?_⟩
  rw [hv]
  change Val.scalar ⟨.isize, false, bits⟩ =
    .scalar ⟨.isize, false, BitVec.ofNat 128 bits.toNat⟩
  rw [hBits]

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem valid_args {x y z : Val} (hx : checkVal x isz = true)
    (hy : checkVal y isz = true) (hz : checkVal z isz = true) :
    ValidEntryArgs Captured.body_0 [x, y, z] := by
  change (checkVal x isz && (checkVal y isz && (checkVal z isz && true))) =
    true
  rw [hx, hy, hz]
  rfl

private theorem args_inv {args : List Val}
    (h : ValidEntryArgs Captured.body_0 args) :
    ∃ b m k : Nat, b < Nat.pow 2 64 ∧ m < Nat.pow 2 64 ∧
      k < Nat.pow 2 64 ∧ args = [scal b, scal m, scal k] := by
  have hM : checkArgsMatch args [isz, isz, isz] = true := h
  let ⟨x, r1, h1, hx, hr1⟩ := checkArgsMatch_cons_iff.mp hM
  let ⟨y, r2, h2, hy, hr2⟩ := checkArgsMatch_cons_iff.mp hr1
  let ⟨z, r3, h3, hz, hr3⟩ := checkArgsMatch_cons_iff.mp hr2
  have h4 : r3 = [] := checkArgsMatch_nil_iff.mp hr3
  let ⟨b, hb, hxb⟩ := isz_inv hx
  let ⟨m, hm, hym⟩ := isz_inv hy
  let ⟨k, hk, hzk⟩ := isz_inv hz
  refine ⟨b, m, k, hb, hm, hk, ?_⟩
  rw [h1, h2, h3, h4, hxb, hym, hzk]

private theorem int_affine (b m k : Nat) :
    Int.ofNat b + Int.ofNat m * Int.ofNat k = Int.ofNat (b + m * k) := rfl

private theorem nat_lt_of_int_le {x N : Nat}
    (h : Int.ofNat x ≤ Int.ofNat N) : x < Nat.succ N := by
  cases x with
  | zero => exact Nat.succ_pos N
  | succ x' =>
    change Int.NonNeg (Int.subNatNat N (Nat.succ x')) at h
    unfold Int.subNatNat at h
    cases hSub : Nat.succ x' - N with
    | zero => exact Nat.succ_le_succ (Nat.le_of_sub_eq_zero hSub)
    | succ k => rw [hSub] at h; nomatch h

private theorem pow64_eq_succ :
    Nat.pow 2 64 = Nat.succ 18446744073709551615 := by decide

/-- The caller's safety bound, read back over `Nat`. -/
private theorem bound_of_safety {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (h : Spec.fn0_safety { args := [scal b, scal m, scal k] }) :
    b + m * k < Nat.pow 2 64 := by
  change decodeScalar ⟨.isize, false, BitVec.ofNat 128 b⟩ +
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 m⟩ *
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 k⟩ ≤
      Int.ofNat 18446744073709551615 at h
  rw [decode_scal hb, decode_scal hm, decode_scal hk, int_affine] at h
  rw [pow64_eq_succ]
  exact nat_lt_of_int_le h

private theorem post_ok {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (hB : b + m * k < Nat.pow 2 64) :
    Spec.fn0_post { args := [scal b, scal m, scal k] }
      ⟨scal (b + m * k), ⟨[]⟩⟩ := by
  change decodeScalar ⟨.isize, false, BitVec.ofNat 128 (b + m * k)⟩ =
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 b⟩ +
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 m⟩ *
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 k⟩
  rw [decode_scal hB, decode_scal hb, decode_scal hm, decode_scal hk,
    int_affine]

/-! ## Lifting the run to the contract obligations -/

/-- The exact-outcome `wpProg` of one in-contract call. -/
private theorem outcome {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (hB : b + m * k < Nat.pow 2 64) :
    wpProg P 21 { args := [scal b, scal m, scal k] }
      (fun o => o = .returned ⟨scal (b + m * k), ⟨[]⟩⟩) := by
  have hmk : m * k < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hB
  have hExec : execProg P 21 { args := [scal b, scal m, scal k] }
      (fun o => o = .returned ⟨scal (b + m * k), ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_eq_ok (p := P) (body := Captured.body_0)
      (args := [scal b, scal m, scal k]) rfl body0_adm
      (valid_args (check_scal hb) (check_scal hm) (check_scal hk))]
    exact run _ _ _ _ _ (check_scal hb) (check_scal hm) (check_scal hk)
      (mul_scal hm hk hmk) (check_scal hmk)
      (add_scal hb hmk hB) (check_scal hB)
  exact wpProg_of_execProg hExec

/-- The per-argument obligations of `BodyContractSatisfied`, discharged from an
exact-outcome `wpProg` proof whose unique return satisfies `postReturn`. -/
private theorem obligations_of_wp {defId : DefId} {args : List Val}
    {ret : Val} {fuel : Nat} {c : FnContract} {isUnsafe : Bool}
    (h_wp : wpProg (entryProgForBody Captured.program defId) fuel
      { args := args } (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩))
    (h_post : c.postReturn { args := args } ⟨ret, ⟨[]⟩⟩) :
    (c.effectiveSafetyPre isUnsafe { args := args } →
      WellFormed (entryProgForBody Captured.program defId)
        { args := args }) ∧
    (c.effectiveBehaviorPre isUnsafe { args := args } →
      (∀ out : TerminalOut,
        Behavior (entryProgForBody Captured.program defId)
          { args := args } out →
        match out with
        | .returned retOut => c.postReturn { args := args } retOut
        | .unwound uwMem =>
          c.effects.noUnwind = false ∧ c.postUnwind { args := args } uwMem
        | .aborted _ => False) ∧
      (c.effects.terminates = true →
        ¬ Diverges (entryProgForBody Captured.program defId)
          { args := args })) := by
  have h := spec_and_behavior_of_wp_eq h_wp
  refine ⟨fun _ => h.1, fun _ => ⟨fun out hOut => ?_, fun _ => h.2.2.1⟩⟩
  have hEq := (h.2.2.2 (fun o => o = .returned ⟨ret, ⟨[]⟩⟩) rfl).2 out hOut
  subst hEq
  exact h_post

private theorem body0_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) := by
  refine ⟨rfl, body0_adm, fun args valid hSafe => ?_⟩
  let ⟨b, m, k, hb, hm, hk, hArgs⟩ := args_inv valid
  subst hArgs
  have hB := bound_of_safety hb hm hk (hSafe rfl)
  exact (spec_and_behavior_of_wp_eq (outcome hb hm hk hB)).1

private theorem body0_contract :
    BodyContractSatisfied Captured.program 0 Captured.body_0
      Spec.fn0_contract := by
  refine ⟨rfl, body0_adm, fun args valid => ?_⟩
  let ⟨b, m, k, hb, hm, hk, hArgs⟩ := args_inv valid
  subst hArgs
  have hOb := fun hS : Spec.fn0_safety { args := [scal b, scal m, scal k] } =>
    obligations_of_wp (c := Spec.fn0_contract)
      (isUnsafe := Captured.body_0.isUnsafe)
      (outcome hb hm hk (bound_of_safety hb hm hk hS))
      (post_ok hb hm hk (bound_of_safety hb hm hk hS))
  exact ⟨fun hSafe => (hOb (hSafe rfl)).1 hSafe,
    fun hBeh => (hOb (hBeh.1 rfl)).2 hBeh⟩

/-- `base = metadata = multiple = 0` satisfies the safety bound. -/
private theorem safety_zero :
    Spec.fn0_safety { args := [scal 0, scal 0, scal 0] } := by
  change decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ +
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ *
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ ≤
      Int.ofNat 18446744073709551615
  rw [decode_scal (intWidth_modulus_pos .isize)]
  exact Int.NonNeg.mk _

private theorem body0_inhabited :
    ContractPreInhabited Captured.body_0 Spec.fn0_contract :=
  let h0 := check_scal (intWidth_modulus_pos .isize)
  ⟨[scal 0, scal 0, scal 0], valid_args h0 h0 h0, fun _ => safety_zero,
    safety_zero⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
      ⟨body0_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · exact ⟨rfl, ⟨0, Captured.body_0, rfl, rfl, rfl, body0_contract,
      fun _ => body0_inhabited⟩, trivial⟩

end Proof
