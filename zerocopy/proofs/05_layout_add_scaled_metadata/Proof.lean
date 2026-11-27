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
import Anneal.MirSymExecCall

/-!
`add_scaled_metadata` calls the `core::num` methods `unchecked_mul` and
`unchecked_add`, so `bodyVerified_of_safe` (which requires a call-free body)
does not apply. Instead the multi-frame symbolic executor
`Anneal.MirSymExecCall` runs all 21 steps, across both pushed sysroot frames,
in five `rfl` chunks. The run returns `base + metadata * multiple` under one
side condition per unchecked operation (that it does not overflow), and the
safety precondition discharges both.
-/

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.MirTotal
open Anneal.MirSymExec Anneal.MirSymExecCall

abbrev isz : MirTy := .int .isize false

/-! ## Symbolic run -/

noncomputable abbrev P : Program := entryProgForBody Captured.program 0

abbrev vb : SymScalar := .var 0 .isize false
abbrev vm : SymScalar := .var 1 .isize false
abbrev vk : SymScalar := .var 2 .isize false
abbrev vmk : SymScalar := .binOp .mul vm vk
abbrev vres : SymScalar := .binOp .add vb vmk

abbrev I (v : SymScalar) : SymSlot := .immediate (some (.scalar v))
abbrev N : SymSlot := .immediate none
abbrev D : SymSlot := .dead

abbrev rootF (blk stmt : Nat) (ls : List SymSlot) : SymFrame :=
  { core := { block := blk, stmt := stmt, slots := ls },
    hdr := ⟨0, none, none, none⟩ }

/-- A pushed sysroot frame computing `kind(a, b)` into caller local `dst` and
resuming the caller at block `tgt`. -/
abbrev calleeF (kind : SysrootNumKind) (a b : SymScalar) (dst tgt : Nat) :
    SymFrame :=
  { core := { block := 0, stmt := 0, slots := [N, I a, I b] },
    hdr := ⟨0, some ⟨kind, .isize, false⟩, some ⟨dst, []⟩, some tgt⟩ }

noncomputable abbrev entry : SymProg :=
  symProgEntry 0 Captured.body_0 [.scalar vb, .scalar vm, .scalar vk]

/-- The side conditions: neither unchecked operation overflows. -/
abbrev conds : List SymCond := [.ok .addUnchecked vb vmk, .ok .mulUnchecked vm vk]

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
      .step { frames := [rootF 2 0 [I vres, I vb, I vm, I vk, I vmk, D, D, N, N]],
              conds := conds } := rfl

-- bb2: StorageDead(_8); StorageDead(_7); StorageDead(_4); return
private theorem chunk5 :
    symProgRunSteps P 4
        { frames := [rootF 2 0 [I vres, I vb, I vm, I vk, I vmk, D, D, N, N]],
          conds := conds } =
      .ret (.scalar vres) conds := rfl

private theorem run :
    symProgRunSteps P (6 + (2 + (7 + (2 + 4)))) entry =
      .ret (.scalar vres) conds :=
  symProgRunSteps_trans chunk1 (symProgRunSteps_trans chunk2
    (symProgRunSteps_trans chunk3 (symProgRunSteps_trans chunk4 chunk5)))

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

/-! ## Discharging the side conditions -/

/-- Binds `vb`, `vm`, and `vk` to the `usize` values `b`, `m`, and `k`. -/
noncomputable abbrev env (b m k : Nat) : SymEnv :=
  fun i => if Nat.beq i 0 then scal b else if Nat.beq i 1 then scal m else scal k

private theorem var_eval {n : Nat} (h : n < Nat.pow 2 64) :
    (⟨.isize, false, truncateBitsComp .isize (BitVec.ofNat 128 n)⟩ : ScalarVal) =
      ⟨.isize, false, BitVec.ofNat 128 n⟩ := by
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

/-- The symbolic run's side conditions and result under `env b m k`. -/
private theorem run_eval {b m k : Nat} (hb : b < Nat.pow 2 64)
    (hm : m < Nat.pow 2 64) (hk : k < Nat.pow 2 64)
    (hB : b + m * k < Nat.pow 2 64) :
    condsHold (env b m k) conds = true ∧
      (SymVal.scalar vres).eval (env b m k) = scal (b + m * k) ∧
      ([SymVal.scalar vb, .scalar vm, .scalar vk]).map (SymVal.eval (env b m k)) =
        [scal b, scal m, scal k] := by
  have hmk : m * k < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hB
  have hvb : vb.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 b⟩ :=
    var_eval hb
  have hvm : vm.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 m⟩ :=
    var_eval hm
  have hvk : vk.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 k⟩ :=
    var_eval hk
  have hvmk : vmk.eval (env b m k) = ⟨.isize, false, BitVec.ofNat 128 (m * k)⟩ := by
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
  · change [Val.scalar (vb.eval (env b m k)), Val.scalar (vm.eval (env b m k)),
      Val.scalar (vk.eval (env b m k))] = _
    rw [hvb, hvm, hvk]

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
  let ⟨hConds, hOut, hArgs⟩ := run_eval hb hm hk hB
  have hValid : ValidEntryArgs Captured.body_0
      (([SymVal.scalar vb, .scalar vm, .scalar vk]).map
        (SymVal.eval (env b.toNat m.toNat k.toNat))) := by
    rw [hArgs]
    exact valid_args (check_scal hb) (check_scal hm) (check_scal hk)
  have hRes := symProgRunSteps_entry_behavior (p := Captured.program)
    (defId := 0) rfl body0_adm (env b.toNat m.toNat k.toNat) hValid run hConds
  rw [hArgs, hOut] at hRes
  exact hRes


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
