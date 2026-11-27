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
import Anneal.MirSymExecCall

/-!
`add_scaled_metadata` calls the `core::num` methods `unchecked_mul` and
`unchecked_add`, so `bodyVerified_of_safe` (which requires a call-free body)
does not apply. Instead the multi-frame symbolic executor
`Anneal.MirSymExecCall` runs all 21 steps, across both pushed sysroot frames,
in five `rfl` chunks. The run returns `base + metadata * multiple` under one
side condition per unchecked operation (that it does not overflow). Every
contract obligation needs the caller's safety bound
`base + metadata * multiple ≤ usize::MAX`, which discharges both.
-/

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.MirTotal
open Anneal.MirSymExec Anneal.MirSymExecCall

private abbrev isz : MirTy := .int .isize false

/-! ## Symbolic run -/

private noncomputable abbrev P : Program :=
  entryProgForBody Captured.program 0

private abbrev vb : SymScalar := .var 0 .isize false
private abbrev vm : SymScalar := .var 1 .isize false
private abbrev vk : SymScalar := .var 2 .isize false
private abbrev vmk : SymScalar := .binOp .mul vm vk
private abbrev vres : SymScalar := .binOp .add vb vmk

private abbrev I (v : SymScalar) : SymSlot := .immediate (some (.scalar v))
private abbrev N : SymSlot := .immediate none
private abbrev D : SymSlot := .dead

private abbrev rootF (blk stmt : Nat) (ls : List SymSlot) : SymFrame :=
  { core := { block := blk, stmt := stmt, slots := ls },
    hdr := ⟨0, none, none, none⟩ }

/-- A pushed sysroot frame computing `kind(a, b)` into caller local `dst` and
resuming the caller at block `tgt`. -/
private abbrev calleeF (kind : SysrootNumKind) (a b : SymScalar)
    (dst tgt : Nat) : SymFrame :=
  { core := { block := 0, stmt := 0, slots := [N, I a, I b] },
    hdr := ⟨0, some ⟨kind, .isize, false⟩, some ⟨dst, []⟩, some tgt⟩ }

private noncomputable abbrev entry : SymProg :=
  symProgEntry 0 Captured.body_0 [.scalar vb, .scalar vm, .scalar vk]

/-- The side conditions: neither unchecked operation overflows. -/
private abbrev conds : List SymCond :=
  [.ok .addUnchecked vb vmk, .ok .mulUnchecked vm vk]

-- bb0: StorageLive(_4); StorageLive(_5); _5 = copy _2; StorageLive(_6);
-- _6 = copy _3; _4 = unchecked_mul(move _5, move _6) -> bb1
private theorem chunk1 :
    symProgRunSteps P 6 entry =
      .step { frames := [calleeF .uncheckedMul vm vk 4 1,
                rootF 0 5 [N, I vb, I vm, I vk, N, N, N, D, D]],
              conds := [] } := rfl

private theorem chunk2 :
    symProgRunSteps P 2
        { frames := [calleeF .uncheckedMul vm vk 4 1,
            rootF 0 5 [N, I vb, I vm, I vk, N, N, N, D, D]], conds := [] } =
      .step { frames := [rootF 1 0 [N, I vb, I vm, I vk, I vmk, N, N, D, D]],
              conds := [.ok .mulUnchecked vm vk] } := rfl

-- bb1: StorageDead(_6); StorageDead(_5); StorageLive(_7); _7 = copy _1;
-- StorageLive(_8); _8 = copy _4; _0 = unchecked_add(move _7, move _8) -> bb2
private theorem chunk3 :
    symProgRunSteps P 7
        { frames := [rootF 1 0 [N, I vb, I vm, I vk, I vmk, N, N, D, D]],
          conds := [.ok .mulUnchecked vm vk] } =
      .step { frames := [calleeF .uncheckedAdd vb vmk 0 2,
                rootF 1 6 [N, I vb, I vm, I vk, I vmk, D, D, N, N]],
              conds := [.ok .mulUnchecked vm vk] } := rfl

private theorem chunk4 :
    symProgRunSteps P 2
        { frames := [calleeF .uncheckedAdd vb vmk 0 2,
            rootF 1 6 [N, I vb, I vm, I vk, I vmk, D, D, N, N]],
          conds := [.ok .mulUnchecked vm vk] } =
      .step { frames := [rootF 2 0
                [I vres, I vb, I vm, I vk, I vmk, D, D, N, N]],
              conds := conds } := rfl

-- bb2: StorageDead(_8); StorageDead(_7); StorageDead(_4); return
private theorem chunk5 :
    symProgRunSteps P 4
        { frames := [rootF 2 0
            [I vres, I vb, I vm, I vk, I vmk, D, D, N, N]],
          conds := conds } =
      .ret (.scalar vres) conds := rfl

private theorem run :
    symProgRunSteps P (6 + (2 + (7 + (2 + 4)))) entry =
      .ret (.scalar vres) conds :=
  symProgRunSteps_trans chunk1 (symProgRunSteps_trans chunk2
    (symProgRunSteps_trans chunk3 (symProgRunSteps_trans chunk4 chunk5)))

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

/-! ## Discharging the side conditions -/

/-- Binds `vb`, `vm`, and `vk` to the `usize` values `b`, `m`, and `k`. -/
private noncomputable abbrev env (b m k : Nat) : SymEnv :=
  fun i => if Nat.beq i 0 then scal b
    else if Nat.beq i 1 then scal m else scal k

private theorem var_eval {n : Nat} (h : n < Nat.pow 2 64) :
    (⟨.isize, false, truncateBitsComp .isize (BitVec.ofNat 128 n)⟩ :
        ScalarVal) = ⟨.isize, false, BitVec.ofNat 128 n⟩ := by
  rw [truncateBitsComp_eq, trunc_ofNat h]

private theorem mul_wrap {a c : Nat} (ha : a < Nat.pow 2 64)
    (hc : c < Nat.pow 2 64) (hac : a * c < Nat.pow 2 64) :
    evalBinOpComp .mul (scal a) (scal c) = .ok (scal (a * c)) := by
  rw [evalBinOpComp_eq]
  exact evalBinOp_unchecked_wrap (k := .uncheckedMul) rfl (mul_scal ha hc hac)

private theorem add_wrap {a c : Nat} (ha : a < Nat.pow 2 64)
    (hc : c < Nat.pow 2 64) (hac : a + c < Nat.pow 2 64) :
    evalBinOpComp .add (scal a) (scal c) = .ok (scal (a + c)) := by
  rw [evalBinOpComp_eq]
  exact evalBinOp_unchecked_wrap (k := .uncheckedAdd) rfl (add_scal ha hc hac)

/-- The symbolic run's side conditions, result, and arguments under
`env b m k`. -/
private theorem run_eval {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (hB : b + m * k < Nat.pow 2 64) :
    condsHold (env b m k) conds = true ∧
      (SymVal.scalar vres).eval (env b m k) = scal (b + m * k) ∧
      ([SymVal.scalar vb, .scalar vm, .scalar vk]).map
          (SymVal.eval (env b m k)) = [scal b, scal m, scal k] := by
  have hmk : m * k < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hB
  have hvb : vb.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 b⟩ :=
    var_eval hb
  have hvm : vm.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 m⟩ :=
    var_eval hm
  have hvk : vk.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 k⟩ :=
    var_eval hk
  have hvmk : vmk.eval (env b m k) =
      ⟨.isize, false, BitVec.ofNat 128 (m * k)⟩ := by
    change (match evalBinOpComp .mul (.scalar (vm.eval (env b m k)))
        (.scalar (vk.eval (env b m k))) with
      | .ok (.scalar sv) => sv
      | _ => ⟨vm.width, vm.signed, BitVec.ofNat 128 0⟩) = _
    rw [hvm, hvk, mul_wrap hm hk hmk]
  refine ⟨?_, ?_, ?_⟩
  · change (SymCond.eval (env b m k) (.ok .addUnchecked vb vmk) &&
      (SymCond.eval (env b m k) (.ok .mulUnchecked vm vk) && true)) = true
    dsimp only [SymCond.eval]
    rw [hvb, hvmk, hvm, hvk, evalBinOpComp_eq, evalBinOpComp_eq,
      add_scal hb hmk hB, mul_scal hm hk hmk]
    rfl
  · change Val.scalar (match evalBinOpComp .add (.scalar (vb.eval (env b m k)))
        (.scalar (vmk.eval (env b m k))) with
      | .ok (.scalar sv) => sv
      | _ => ⟨vb.width, vb.signed, BitVec.ofNat 128 0⟩) = _
    rw [hvb, hvmk, add_wrap hb hmk hB]
  · change [Val.scalar (vb.eval (env b m k)),
      Val.scalar (vm.eval (env b m k)),
      Val.scalar (vk.eval (env b m k))] = _
    rw [hvb, hvm, hvk]

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
    (h : Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_safety { args := [scal b, scal m, scal k] }) :
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
    Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_post { args := [scal b, scal m, scal k] }
      ⟨scal (b + m * k), ⟨[]⟩⟩ := by
  change decodeScalar ⟨.isize, false, BitVec.ofNat 128 (b + m * k)⟩ =
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 b⟩ +
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 m⟩ *
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 k⟩
  rw [decode_scal hB, decode_scal hb, decode_scal hm, decode_scal hk,
    int_affine]

/-! ## Lifting the run to the contract obligations -/

/-- Everything the boundary needs about one in-contract call: it is
well-formed, returns exactly `scal (b + m * k)`, and does not diverge. -/
private theorem outcome {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (hB : b + m * k < Nat.pow 2 64) :
    let q : Query := { args := [scal b, scal m, scal k] }
    let out := TerminalOut.returned ⟨scal (b + m * k), ⟨[]⟩⟩
    WellFormed P q ∧ Behavior P q out ∧ ¬ Diverges P q ∧
      ∀ post : TerminalOut → Prop, post out → SatisfiesPost P q post := by
  let ⟨hConds, hOut, hArgs⟩ := run_eval hb hm hk hB
  have hValid : ValidEntryArgs Captured.body_0
      (([SymVal.scalar vb, .scalar vm, .scalar vk]).map
        (SymVal.eval (env b m k))) := by
    rw [hArgs]
    exact valid_args (check_scal hb) (check_scal hm) (check_scal hk)
  have hRes := symProgRunSteps_entry_behavior (p := Captured.program)
    (defId := 0) rfl body0_adm (env b m k) hValid run hConds
  rw [hArgs, hOut] at hRes
  exact hRes

/-- The per-argument obligations of `BodyContractSatisfied`, discharged from
an exact outcome whose unique return satisfies `postReturn`. -/
private theorem obligations_of_outcome {args : List Val} {ret : Val}
    {c : FnContract} {isUnsafe : Bool}
    (h : WellFormed P { args := args } ∧ ¬ Diverges P { args := args } ∧
      ∀ post : TerminalOut → Prop, post (.returned ⟨ret, ⟨[]⟩⟩) →
        SatisfiesPost P { args := args } post)
    (h_post : c.postReturn { args := args } ⟨ret, ⟨[]⟩⟩) :
    (c.effectiveSafetyPre isUnsafe { args := args } →
      WellFormed P { args := args }) ∧
    (c.effectiveBehaviorPre isUnsafe { args := args } →
      (∀ out : TerminalOut, Behavior P { args := args } out →
        match out with
        | .returned retOut => c.postReturn { args := args } retOut
        | .unwound uwMem =>
          c.effects.noUnwind = false ∧ c.postUnwind { args := args } uwMem
        | .aborted _ => False) ∧
      (c.effects.terminates = true → ¬ Diverges P { args := args })) := by
  refine ⟨fun _ => h.1, fun _ => ⟨fun out hOut => ?_, fun _ => h.2.1⟩⟩
  have hEq := (h.2.2 (fun o => o = .returned ⟨ret, ⟨[]⟩⟩) rfl).2 out hOut
  subst hEq
  exact h_post

private theorem body0_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Specs.zerocopy.zc05_layout_add_scaled_metadata.specs.safety Captured.body_0.identity) := by
  refine ⟨rfl, body0_adm, fun args valid hSafe => ?_⟩
  let ⟨b, m, k, hb, hm, hk, hArgs⟩ := args_inv valid
  subst hArgs
  exact (outcome hb hm hk (bound_of_safety hb hm hk (hSafe rfl))).1

private theorem body0_contract :
    BodyContractSatisfied Captured.program 0 Captured.body_0
      Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_contract := by
  refine ⟨rfl, body0_adm, fun args valid => ?_⟩
  let ⟨b, m, k, hb, hm, hk, hArgs⟩ := args_inv valid
  subst hArgs
  have hOb := fun hS : Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_safety { args := [scal b, scal m, scal k] } =>
    let hB := bound_of_safety hb hm hk hS
    let h := outcome hb hm hk hB
    obligations_of_outcome (c := Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_contract)
      (isUnsafe := Captured.body_0.isUnsafe) ⟨h.1, h.2.2⟩ (post_ok hb hm hk hB)
  exact ⟨fun hSafe => (hOb (hSafe rfl)).1 hSafe,
    fun hBeh => (hOb (hBeh.1 rfl)).2 hBeh⟩

/-- `base = metadata = multiple = 0` satisfies the safety bound. -/
private theorem safety_zero :
    Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_safety { args := [scal 0, scal 0, scal 0] } := by
  change decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ +
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ *
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩ ≤
      Int.ofNat 18446744073709551615
  rw [decode_scal (intWidth_modulus_pos .isize)]
  exact Int.NonNeg.mk _

private theorem body0_inhabited :
    ContractPreInhabited Captured.body_0 Specs.zerocopy.zc05_layout_add_scaled_metadata.fn0_contract :=
  let h0 := check_scal (intWidth_modulus_pos .isize)
  ⟨[scal 0, scal 0, scal 0], valid_args h0 h0 h0, fun _ => safety_zero,
    safety_zero⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Specs.zerocopy.zc05_layout_add_scaled_metadata.specs 0
        Captured.program.bodies :=
      ⟨body0_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · exact ⟨rfl, ⟨0, Captured.body_0, rfl, rfl, rfl, body0_contract,
      fun _ => body0_inhabited⟩, trivial⟩

end Proof
