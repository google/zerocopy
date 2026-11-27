prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Captured
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

abbrev u64 (n : Nat) : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩
abbrev im (v : Val) : LocalSlot := .immediate (some v)
abbrev N : LocalSlot := .immediate none
abbrev D : LocalSlot := .dead

abbrev st (b i : Nat) (l : List LocalSlot) (cm : CallerMemory)
    (m : MemoryState) : State :=
  ⟨[⟨0, b, i, l, none, none, none⟩], cm, m⟩

abbrev Runs (p : Program) (post : TerminalOut → Prop) (s : State) : Prop :=
  ∃ fuel, execOutcomeStateV2 p post (fun _ => False) fuel s

private theorem runs_step {p : Program} {s s' : State} {post : TerminalOut → Prop}
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

private theorem runs_done {p : Program} {s : State} {out : TerminalOut}
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

private theorem execProgV2_of_runs {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (hInit : initStateV2 p q = .ok s₀)
    (hRuns : Runs p post s₀) : ∃ fuel, execProgV2 p fuel q post :=
  let ⟨fuel, h⟩ := hRuns
  ⟨fuel, by unfold execProgV2; rw [hInit]; exact h⟩

private theorem toNat_bvOfNat_128 {n : Nat} (h : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n :=
  Nat.mod_eq_of_lt h

private theorem scalarVal_wf_isize {sv : ScalarVal} (hWf : ScalarVal.wf sv = true)
    (hW : sv.width = .isize) :
    truncateBits .isize sv.bits = sv.bits := by
  unfold ScalarVal.wf at hWf
  rw [hW] at hWf
  exact eq_of_beq hWf

private theorem truncateBits_isize_toNat_lt {sv : ScalarVal} (hW : sv.width = .isize)
    (hWf : ScalarVal.wf sv = true) :
    sv.bits.toNat < Nat.pow 2 64 := by
  have hEq := scalarVal_wf_isize hWf hW
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem scalar_eq_of_fields {sv : ScalarVal} (hW : sv.width = .isize)
    (hS : sv.signed = false) (hLt : sv.bits.toNat < Nat.pow 2 64) :
    sv = ⟨.isize, false, BitVec.ofNat 128 sv.bits.toNat⟩ := by
  cases sv with
  | mk w s b =>
    dsimp only at hW hS hLt
    subst hW; subst hS
    cases b with
    | ofFin f =>
      cases f with
      | mk v h =>
        apply congrArg (fun bv => ScalarVal.mk .isize false bv)
        apply congrArg BitVec.ofFin
        apply Fin.eq_of_val_eq
        exact (Nat.mod_eq_of_lt (Nat.lt_trans hLt (by decide))).symm

private theorem args_usize {args : List Val}
    (h : checkArgsMatchV2 args [.int .isize false] = true) :
    ∃ p : Nat, args = [u64 p] ∧ p < Nat.pow 2 64 := by
  match args, h with
  | [], h => cases h
  | v :: vs, h =>
    have hv : checkValV2 v (.int .isize false) = true := by
      cases hc : checkValV2 v (.int .isize false) with
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
      have hLt : bits.toNat < Nat.pow 2 64 := by
        rw [← hT, toNat_truncateBits]
        exact Nat.mod_lt _ (by decide)
      have hBits : bits = BitVec.ofNat 128 bits.toNat := by
        cases bits with
        | ofFin f =>
          cases f with
          | mk val hVal =>
            apply congrArg BitVec.ofFin
            apply Fin.eq_of_val_eq
            exact (Nat.mod_eq_of_lt hVal).symm
      exact ⟨bits.toNat, by rw [hEq]; unfold u64; rw [← hBits], hLt⟩
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => cases hv

private theorem decodeScalar_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  have hMod : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact h)
  rw [hTr, hMod]
  rfl

private theorem checkValV2_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    checkValV2 (u64 n) (.int .isize false) = true := by
  refine checkVal_int_iff.mpr ⟨BitVec.ofNat 128 n, rfl, ?_⟩
  have hMod128 : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  exact truncateBits_of_toNat_lt (by rw [hMod128]; exact h)

private theorem bvOfInt_128_ofNat {n : Nat} (h : n < Nat.pow 2 128) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  unfold bvOfInt intEmod
  dsimp only [Int.natAbs, Int.toNat]
  have hMod : Nat.mod n (Nat.pow 2 128) = n := Nat.mod_eq_of_lt h
  change BitVec.ofNat 128 (Nat.mod n (Nat.pow 2 128)) = BitVec.ofNat 128 n
  rw [hMod]

private theorem int_ofNat_not_ge_pow128 {n : Nat} (h : n < Nat.pow 2 128) :
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

private theorem evalBinOp_div_4096 {p : Nat} (hp : p < Nat.pow 2 64) :
    evalBinOp .div (u64 p) (u64 4096) = .ok (u64 (p / 4096)) := by
  have h4096 : (4096 : Nat) < Nat.pow 2 64 := by decide
  have hDiv : p / 4096 < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self p 4096) hp
  have h128 : p / 4096 < Nat.pow 2 128 := Nat.lt_trans hDiv (by decide)
  have hMod : (BitVec.ofNat 128 (p / 4096)).toNat = p / 4096 := toNat_bvOfNat_128 h128
  have hTr : truncateBits .isize (BitVec.ofNat 128 (p / 4096)) = BitVec.ofNat 128 (p / 4096) :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact hDiv)
  have hBne : (BitVec.ofNat 128 (p / 4096) != BitVec.ofNat 128 (p / 4096)) = false := by
    change (!(BitVec.ofNat 128 (p / 4096) == BitVec.ofNat 128 (p / 4096))) = false
    rw [beq_self_eq_true]; rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.div.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat hp, decodeScalar_isize_ofNat h4096]
  rw [ite_bool_false (rfl : (true && (Int.ofNat 4096 == (0 : Int))) = false)]
  rw [ite_bool_false (rfl : (false && true && _) = false)]
  have hDivI : intTdiv (Int.ofNat p) (Int.ofNat 4096) = Int.ofNat (p / 4096) := rfl
  rw [hDivI]
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfInt_128_ofNat h128, hTr, hBne]
  have hHost : (decide (Int.ofNat (p / 4096) < 0) || decide (Int.ofNat (p / 4096) ≥ 2 ^ 128)) = false := by
    rw [decide_eq_false (fun h => nomatch h), decide_eq_false (int_ofNat_not_ge_pow128 h128)]; rfl
  rw [hHost]
  rfl

private theorem evalBinOp_mulOvf_64 {q : Nat} (hq : q < Nat.pow 2 52) :
    evalBinOp .mulWithOverflow (u64 q) (u64 64) = .ok (.tuple [u64 (q * 64), .bool false]) := by
  have hq64 : q < Nat.pow 2 64 := Nat.lt_trans hq (by decide)
  have h64 : (64 : Nat) < Nat.pow 2 64 := by decide
  have hProd : q * 64 < Nat.pow 2 64 := by
    have hpow : (Nat.pow 2 52) * 64 = Nat.pow 2 58 := by decide
    have h58 : Nat.pow 2 58 < Nat.pow 2 64 := by decide
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hq (by decide)) (by rw [hpow]; exact Nat.le_of_lt h58)
  have h128 : q * 64 < Nat.pow 2 128 := Nat.lt_trans hProd (by decide)
  have hMod : (BitVec.ofNat 128 (q * 64)).toNat = q * 64 := toNat_bvOfNat_128 h128
  have hTr : truncateBits .isize (BitVec.ofNat 128 (q * 64)) = BitVec.ofNat 128 (q * 64) :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact hProd)
  have hBne : (BitVec.ofNat 128 (q * 64) != BitVec.ofNat 128 (q * 64)) = false := by
    change (!(BitVec.ofNat 128 (q * 64) == BitVec.ofNat 128 (q * 64))) = false
    rw [beq_self_eq_true]; rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.mulWithOverflow.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat hq64, decodeScalar_isize_ofNat h64]
  rw [ite_bool_false (rfl : (false && (Int.ofNat 64 == (0 : Int))) = false)]
  rw [ite_bool_false (rfl : (false && false && _) = false)]
  have hMulI : Int.ofNat q * Int.ofNat 64 = Int.ofNat (q * 64) := rfl
  rw [hMulI]
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfInt_128_ofNat h128, hTr, hBne]
  have hHost : (decide (Int.ofNat (q * 64) < 0) || decide (Int.ofNat (q * 64) ≥ 2 ^ 128)) = false := by
    rw [decide_eq_false (fun h => nomatch h), decide_eq_false (int_ofNat_not_ge_pow128 h128)]; rfl
  rw [hHost]
  rfl

private theorem evalBinOp_addOvf_noovf {base off : Nat}
    (hb : base < Nat.pow 2 64) (ho : off < Nat.pow 2 64) (hSum : base + off < Nat.pow 2 64) :
    evalBinOp .addWithOverflow (u64 base) (u64 off) =
      .ok (.tuple [u64 (base + off), .bool false]) := by
  have h128 : base + off < Nat.pow 2 128 := Nat.lt_trans hSum (by decide)
  have hMod : (BitVec.ofNat 128 (base + off)).toNat = base + off := toNat_bvOfNat_128 h128
  have hTr : truncateBits .isize (BitVec.ofNat 128 (base + off)) = BitVec.ofNat 128 (base + off) :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact hSum)
  have hBne : (BitVec.ofNat 128 (base + off) != BitVec.ofNat 128 (base + off)) = false := by
    change (!(BitVec.ofNat 128 (base + off) == BitVec.ofNat 128 (base + off))) = false
    rw [beq_self_eq_true]; rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.addWithOverflow.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat hb, decodeScalar_isize_ofNat ho]
  rw [ite_bool_false (rfl : (false && (Int.ofNat off == (0 : Int))) = false)]
  rw [ite_bool_false (rfl : (false && false && _) = false)]
  have hAddI : Int.ofNat base + Int.ofNat off = Int.ofNat (base + off) := rfl
  rw [hAddI]
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfInt_128_ofNat h128, hTr, hBne]
  have hHost : (decide (Int.ofNat (base + off) < 0) || decide (Int.ofNat (base + off) ≥ 2 ^ 128)) = false := by
    rw [decide_eq_false (fun h => nomatch h), decide_eq_false (int_ofNat_not_ge_pow128 h128)]; rfl
  rw [hHost]
  rfl

private theorem evalBinOp_addOvf_ovf {base off : Nat}
    (hb : base < Nat.pow 2 64) (ho : off < Nat.pow 2 64) (hGe : Nat.pow 2 64 ≤ base + off) :
    evalBinOp .addWithOverflow (u64 base) (u64 off) =
      .ok (.tuple [u64 ((base + off) % Nat.pow 2 64), .bool true]) := by
  have hSumLt128 : base + off < Nat.pow 2 128 := by
    have h2 : Nat.pow 2 64 + Nat.pow 2 64 < Nat.pow 2 128 := by decide
    exact Nat.lt_trans (Nat.add_lt_add hb ho) h2
  have hTruncLt : (base + off) % Nat.pow 2 64 < Nat.pow 2 64 := Nat.mod_lt _ (by decide)
  have hTrunc128 : (base + off) % Nat.pow 2 64 < Nat.pow 2 128 := Nat.lt_trans hTruncLt (by decide)
  have hbv : BitVec.ofNat 128 (base + off) =
      truncateBits .isize (BitVec.ofNat 128 (base + off)) ↔ False := by
    exact ⟨fun h => by
      have hNat : (BitVec.ofNat 128 (base + off)).toNat =
          (truncateBits .isize (BitVec.ofNat 128 (base + off))).toNat := congrArg BitVec.toNat h
      rw [toNat_bvOfNat_128 hSumLt128, toNat_truncateBits, toNat_bvOfNat_128 hSumLt128] at hNat
      exact Nat.not_le_of_gt (by rw [hNat]; exact Nat.mod_lt _ (by decide)) hGe, False.elim⟩
  have hTrEq : truncateBits .isize (BitVec.ofNat 128 (base + off)) =
      BitVec.ofNat 128 ((base + off) % Nat.pow 2 64) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits, toNat_bvOfNat_128 hSumLt128, toNat_bvOfNat_128 hTrunc128]
    rfl
  have hBne : (truncateBits .isize (BitVec.ofNat 128 (base + off)) != BitVec.ofNat 128 (base + off)) = true := by
    change (!(truncateBits .isize (BitVec.ofNat 128 (base + off)) == BitVec.ofNat 128 (base + off))) = true
    cases hEq : (truncateBits .isize (BitVec.ofNat 128 (base + off)) == BitVec.ofNat 128 (base + off)) with
    | true => exact False.elim (hbv.mp (eq_of_beq hEq).symm)
    | false => rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.addWithOverflow.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat hb, decodeScalar_isize_ofNat ho]
  rw [ite_bool_false (rfl : (false && (Int.ofNat off == (0 : Int))) = false)]
  rw [ite_bool_false (rfl : (false && false && _) = false)]
  have hAddI : Int.ofNat base + Int.ofNat off = Int.ofNat (base + off) := rfl
  rw [hAddI]
  rw [ite_bool_false rfl]
  rw [bvOfInt_128_ofNat hSumLt128, hBne, hTrEq]
  dsimp only
  rw [Bool.or_true]
  rfl

private noncomputable abbrev P : Program := entryProgForBody Captured.program 0

private theorem nat_div_lt_of_lt_mul {a b c : Nat} (h : a < c * b) : a / b < c :=
  Nat.lt_of_not_le fun hGe =>
    Nat.not_lt_of_le (Nat.le_trans (Nat.mul_le_mul_right b hGe) (Nat.div_mul_le_self a b)) h

private theorem nat_le_div_of_mul_le {a b c : Nat} (hb : 0 < b) (h : c * b ≤ a) : c ≤ a / b :=
  Nat.le_of_not_lt fun hLt => by
    have h1 : (a / b + 1) ≤ c := hLt
    have h2 : (a / b + 1) * b ≤ c * b := Nat.mul_le_mul_right b h1
    have h3 : (a / b + 1) * b = (a / b) * b + b := Nat.succ_mul (a / b) b
    rw [h3] at h2
    have h4 : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hMod : a % b < b := Nat.mod_lt a hb
    rw [Nat.mul_comm] at h4
    have hLt2 : a < (a / b) * b + b := by
      have hAddLt : (a / b) * b + a % b < (a / b) * b + b := Nat.add_lt_add_left hMod _
      rwa [h4] at hAddLt
    exact Nat.not_lt_of_le (Nat.le_trans h2 h) hLt2

private theorem initState_body0 {p : Nat} (_hp : p < Nat.pow 2 64)
    (q : Query) (hArgs : q.args = [u64 p]) (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    initStateV2 P q =
      .ok (st 0 0 [N, im (u64 p), D, D, D, N, D, D, D, N, N] q.callerMem
        (entryMemoryWithCaller q.callerMem)) := by
  let ⟨hCM, hArgM, hRefs, hDisj⟩ := hValid
  have hInit := Anneal.MirWp.initStateV2_ok_of (p := P) (q := q) (body := Captured.body_0)
    rfl rfl hCM rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    hArgM hRefs hDisj
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    exact hInit

private theorem step_assign {p : Program} {body : Body} {bb : BasicBlock}
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
  unfold evalStepV2
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBB]
  dsimp only
  rw [hStmt]
  unfold evalStatementV2
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

private theorem writePlaceDestV2_local {locals locals' : List LocalSlot}
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

private theorem evalBinOp_4096_eq_0 :
    evalBinOp .eq (u64 4096) (u64 0) = .ok (.bool false) := by
  have h4096 : (4096 : Nat) < Nat.pow 2 64 := by decide
  have h0 : (0 : Nat) < Nat.pow 2 64 := by decide
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (rfl : BinOp.eq.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat h4096, decodeScalar_isize_ofNat h0]
  rfl

private theorem frame_to_meta_run (cm : CallerMemory) (m : MemoryState)
    (p : Nat) (hp : p < Nat.pow 2 64) (post : TerminalOut → Prop)
    (hSafe : p < Spec.maxSafePaddr → post (.returned ⟨u64 (Spec.expectedMetaVaddr p), extractCallerMemory cm m⟩))
    (hOvf : Spec.maxSafePaddr ≤ p → post (.aborted (extractCallerMemory cm m))) :
    Runs P post (st 0 0 [N, im (u64 p), D, D, D, N, D, D, D, N, N] cm m) := by
  have hCp := checkValV2_isize_ofNat hp
  let xp := im (u64 p)
  let base := im (u64 Spec.frameMetadataBase)
  have hBaseLt : Spec.frameMetadataBase < Nat.pow 2 64 := by decide
  have hBaseC := checkValV2_isize_ofNat hBaseLt
  have hDivLt : p / 4096 < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self p 4096) hp
  have hCdiv := checkValV2_isize_ofNat hDivLt
  have hq52 : p / 4096 < Nat.pow 2 52 := by
    have hmul : p < (Nat.pow 2 52) * 4096 := hp
    exact nat_div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hmul)
  have hProdLt : (p / 4096) * 64 < Nat.pow 2 64 := by
    have hpow : (Nat.pow 2 52) * 64 = Nat.pow 2 58 := by decide
    have h58 : Nat.pow 2 58 < Nat.pow 2 64 := by decide
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hq52 (by decide)) (by rw [hpow]; exact Nat.le_of_lt h58)
  have hCprod := checkValV2_isize_ofNat hProdLt
  have hEqStep : evalStepV2 P (st 0 5 [N, xp, base, N, xp, N, D, D, D, N, N] cm m) =
      .step (st 0 6 [N, xp, base, N, xp, im (.bool false), D, D, D, N, N] cm m) := by
    refine step_assign rfl rfl rfl rfl ?_ (writePlaceDestV2_local (locals := [N, xp, base, N, xp, N, D, D, D, N, N]) rfl rfl rfl)
    change (match evalBinOp .eq (u64 4096) (u64 0) with
      | Except.error k => Except.error k
      | Except.ok res => Except.ok (res, [N, xp, base, N, xp, N, D, D, D, N, N], m)) = _
    rw [evalBinOp_4096_eq_0]
  have hDivStep : evalStepV2 P (st 1 0 [N, xp, base, N, xp, N, D, D, D, N, N] cm m) =
      .step (st 1 1 [N, xp, base, im (u64 (p / 4096)), N, N, D, D, D, N, N] cm m) := by
    refine step_assign rfl rfl rfl rfl ?_ (writePlaceDestV2_local (locals := [N, xp, base, N, N, N, D, D, D, N, N]) hCdiv rfl rfl)
    change (match evalBinOp .div (u64 p) (u64 4096) with
      | Except.error k => Except.error k
      | Except.ok res => Except.ok (res, [N, xp, base, N, N, N, D, D, D, N, N], m)) = _
    rw [evalBinOp_div_4096 hp]
  have hMulStep : evalStepV2 P (st 1 7 [N, xp, base, im (u64 (p / 4096)), D, N, base, N, im (u64 (p / 4096)), N, N] cm m) =
      .step (st 1 8 [N, xp, base, im (u64 (p / 4096)), D, N, base, N, im (u64 (p / 4096)),
        im (.tuple [u64 ((p / 4096) * 64), .bool false]), N] cm m) := by
    have hChkT : checkValV2 (.tuple [u64 ((p / 4096) * 64), .bool false]) (.tuple [.int .isize false, .bool]) = true := by
      change (checkValV2 (u64 ((p / 4096) * 64)) (.int .isize false) && (true && true)) = true
      rw [hCprod]; rfl
    refine step_assign rfl rfl rfl rfl ?_ (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, N, im (u64 (p / 4096)), N, N]) hChkT rfl rfl)
    change (match evalBinOp .mulWithOverflow (u64 (p / 4096)) (u64 64) with
      | Except.error k => Except.error k
      | Except.ok res => Except.ok (res, _, m)) = _
    rw [evalBinOp_mulOvf_64 hq52]
  refine runs_step (s' := st 0 1 [N, xp, N, D, D, N, D, D, D, N, N] cm m) rfl <|
    runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, N, D, D, N, D, D, D, N, N]) hBaseC rfl rfl)) <|
    runs_step (s' := st 0 3 [N, xp, base, N, D, N, D, D, D, N, N] cm m) rfl <|
    runs_step (s' := st 0 4 [N, xp, base, N, N, N, D, D, D, N, N] cm m) rfl <|
    runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, base, N, N, N, D, D, D, N, N]) hCp rfl rfl)) <|
    runs_step hEqStep <|
    runs_step (s' := st 1 0 [N, xp, base, N, xp, N, D, D, D, N, N] cm m) rfl <|
    runs_step hDivStep <|
    runs_step (s' := st 1 2 [N, xp, base, im (u64 (p / 4096)), D, N, D, D, D, N, N] cm m) rfl <|
    runs_step (s' := st 1 3 [N, xp, base, im (u64 (p / 4096)), D, N, N, D, D, N, N] cm m) rfl <|
    runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, N, D, D, N, N]) hBaseC rfl rfl)) <|
    runs_step (s' := st 1 5 [N, xp, base, im (u64 (p / 4096)), D, N, base, N, D, N, N] cm m) rfl <|
    runs_step (s' := st 1 6 [N, xp, base, im (u64 (p / 4096)), D, N, base, N, N, N, N] cm m) rfl <|
    runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, N, N, N, N]) hCdiv rfl rfl)) <|
    runs_step hMulStep <|
    runs_step (s' := st 2 0 [N, xp, base, im (u64 (p / 4096)), D, N, base, N, im (u64 (p / 4096)),
      .partialTuple [some (u64 ((p / 4096) * 64)), none], N] cm m) rfl <|
    runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, N, im (u64 (p / 4096)), N, N]) hCprod rfl rfl)) <|
    runs_step (s' := st 2 2 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N] cm m) rfl ?_
  cases Nat.lt_or_ge p Spec.maxSafePaddr with
  | inl hLt =>
    have hq39 : p / 4096 < Nat.pow 2 39 := by
      have hmul : p < (Nat.pow 2 39) * 4096 := hLt
      exact nat_div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hmul)
    have hOff45 : (p / 4096) * 64 < Nat.pow 2 45 := by
      have hpow : (Nat.pow 2 39) * 64 = Nat.pow 2 45 := by decide
      rw [← hpow]
      exact Nat.mul_lt_mul_of_pos_right hq39 (by decide)
    have hSumLt : Spec.expectedMetaVaddr p < Nat.pow 2 64 := by
      have hBase45 : Spec.frameMetadataBase + Nat.pow 2 45 = Nat.pow 2 64 := by decide
      change Spec.frameMetadataBase + (p / 4096) * 64 < Nat.pow 2 64
      rw [← hBase45]
      exact Nat.add_lt_add_left hOff45 Spec.frameMetadataBase
    have hCmeta := checkValV2_isize_ofNat hSumLt
    have hChkT : checkValV2 (.tuple [u64 (Spec.expectedMetaVaddr p), .bool false]) (.tuple [.int .isize false, .bool]) = true := by
      change (checkValV2 (u64 (Spec.expectedMetaVaddr p)) (.int .isize false) && (true && true)) = true
      rw [hCmeta]; rfl
    have hAddStep : evalStepV2 P (st 2 2 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N] cm m) =
        .step (st 2 3 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N,
          im (.tuple [u64 (Spec.expectedMetaVaddr p), .bool false])] cm m) := by
      refine step_assign rfl rfl rfl rfl ?_ (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N]) hChkT rfl rfl)
      change (match evalBinOp .addWithOverflow (u64 Spec.frameMetadataBase) (u64 ((p / 4096) * 64)) with
        | Except.error k => Except.error k
        | Except.ok res => Except.ok (res, _, m)) = _
      rw [evalBinOp_addOvf_noovf hBaseLt hProdLt hSumLt]
      rfl
    exact runs_step hAddStep <|
      runs_step (s' := st 3 0 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N,
        .partialTuple [some (u64 (Spec.expectedMetaVaddr p)), none]] cm m) rfl <|
      runs_step (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N]) hCmeta rfl rfl)) <|
      runs_step (s' := st 3 2 [im (u64 (Spec.expectedMetaVaddr p)), xp, base, im (u64 (p / 4096)), D, N, base, D, D, N, N] cm m) rfl <|
      runs_step (s' := st 3 3 [im (u64 (Spec.expectedMetaVaddr p)), xp, base, im (u64 (p / 4096)), D, N, D, D, D, N, N] cm m) rfl <|
      runs_step (s' := st 3 4 [im (u64 (Spec.expectedMetaVaddr p)), xp, base, D, D, N, D, D, D, N, N] cm m) rfl <|
      runs_step (s' := st 3 5 [im (u64 (Spec.expectedMetaVaddr p)), xp, D, D, D, N, D, D, D, N, N] cm m) rfl <|
      runs_done rfl (hSafe hLt)
  | inr hGe =>
    have hq39 : Nat.pow 2 39 ≤ p / 4096 := by
      have hmul : (Nat.pow 2 39) * 4096 ≤ p := hGe
      exact nat_le_div_of_mul_le (by decide) hmul
    have hOff45 : Nat.pow 2 45 ≤ (p / 4096) * 64 := by
      have hpow : (Nat.pow 2 39) * 64 = Nat.pow 2 45 := by decide
      rw [← hpow]
      exact Nat.mul_le_mul_right 64 hq39
    have hSumGe : Nat.pow 2 64 ≤ Spec.frameMetadataBase + (p / 4096) * 64 := by
      have hBase45 : Spec.frameMetadataBase + Nat.pow 2 45 = Nat.pow 2 64 := by decide
      rw [← hBase45]
      exact Nat.add_le_add_left hOff45 Spec.frameMetadataBase
    let wrapped := (Spec.frameMetadataBase + (p / 4096) * 64) % Nat.pow 2 64
    have hModLt : wrapped < Nat.pow 2 64 := Nat.mod_lt _ (by decide)
    have hCmod := checkValV2_isize_ofNat hModLt
    have hChkT : checkValV2 (.tuple [u64 wrapped, .bool true]) (.tuple [.int .isize false, .bool]) = true := by
      change (checkValV2 (u64 wrapped) (.int .isize false) && (true && true)) = true
      rw [hCmod]; rfl
    have hAddStep : evalStepV2 P (st 2 2 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N] cm m) =
        .step (st 2 3 [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N,
          im (.tuple [u64 wrapped, .bool true])] cm m) := by
      refine step_assign rfl rfl rfl rfl ?_ (writePlaceDestV2_local (locals := [N, xp, base, im (u64 (p / 4096)), D, N, base, im (u64 ((p / 4096) * 64)), D, N, N]) hChkT rfl rfl)
      change (match evalBinOp .addWithOverflow (u64 Spec.frameMetadataBase) (u64 ((p / 4096) * 64)) with
        | Except.error k => Except.error k
        | Except.ok res => Except.ok (res, _, m)) = _
      rw [evalBinOp_addOvf_ovf hBaseLt hProdLt hSumGe]
    exact runs_step hAddStep <| runs_done rfl (hOvf hGe)

private theorem body0_allowAbort :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0 Spec.frameToMetaAllowAbort := by
  refine Anneal.MirWp.safeContract_soundness_of_execV2.2.1
    Captured.program 0 Captured.body_0 Spec.frameToMetaAllowAbort rfl (by decide) ?_
  intro q hValid _
  let ⟨p, hArgs, hp⟩ := args_usize hValid.2.1
  have hToNat : (BitVec.ofNat 128 p).toNat = p := toNat_bvOfNat_128 (Nat.lt_trans hp (by decide))
  have hInit := initState_body0 hp q hArgs hValid
  have hCM : extractCallerMemory q.callerMem (entryMemoryWithCaller q.callerMem) = q.callerMem :=
    Anneal.MirWp.extractCallerMemory_entry q.callerMem hValid.1
  have hRuns : Runs P (Spec.frameToMetaAllowAbort.post q)
      (st 0 0 [N, im (u64 p), D, D, D, N, D, D, D, N, N] q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    refine frame_to_meta_run q.callerMem (entryMemoryWithCaller q.callerMem) p hp _ ?_ ?_
    · intro hLt
      rw [hCM]
      unfold SafeContractV2.post Spec.frameToMetaAllowAbort
      dsimp only
      rw [hArgs]
      change _ ∧ _ ∧ _
      dsimp only
      rw [hToNat]
      exact ⟨hLt, rfl, rfl⟩
    · intro hGe
      rw [hCM]
      unfold SafeContractV2.post Spec.frameToMetaAllowAbort
      dsimp only
      rw [hArgs]
      change _ ∧ _ ∧ _
      dsimp only
      rw [hToNat]
      exact ⟨rfl, hGe, rfl⟩
  exact execProgV2_of_runs hInit hRuns

private theorem body0_noAbort :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0 Spec.frameToMetaNoAbort := by
  refine Anneal.MirWp.safeContract_soundness_of_execV2.2.1
    Captured.program 0 Captured.body_0 Spec.frameToMetaNoAbort rfl (by decide) ?_
  intro q hValid hPre
  let ⟨p, hArgs, hp⟩ := args_usize hValid.2.1
  have hToNat : (BitVec.ofNat 128 p).toNat = p := toNat_bvOfNat_128 (Nat.lt_trans hp (by decide))
  have hLt : p < Spec.maxSafePaddr := by
    unfold Spec.frameToMetaNoAbort at hPre
    dsimp only at hPre
    rw [hArgs] at hPre
    dsimp only at hPre
    rw [hToNat] at hPre
    exact hPre
  have hInit := initState_body0 hp q hArgs hValid
  have hCM : extractCallerMemory q.callerMem (entryMemoryWithCaller q.callerMem) = q.callerMem :=
    Anneal.MirWp.extractCallerMemory_entry q.callerMem hValid.1
  have hRuns : Runs P (Spec.frameToMetaNoAbort.post q)
      (st 0 0 [N, im (u64 p), D, D, D, N, D, D, D, N, N] q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    refine frame_to_meta_run q.callerMem (entryMemoryWithCaller q.callerMem) p hp _ ?_ ?_
    · intro _
      rw [hCM]
      unfold SafeContractV2.post Spec.frameToMetaNoAbort Spec.frameToMetaAllowAbort
      dsimp only
      rw [hArgs]
      change _ ∧ _ ∧ _
      dsimp only
      rw [hToNat]
      exact ⟨hLt, rfl, rfl⟩
    · intro hGe
      exact False.elim (Nat.not_le_of_gt hLt hGe)
  exact execProgV2_of_runs hInit hRuns

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      have hEq : Captured.body_0 = body := Option.some.inj hBody
      subst hEq
      exact ⟨rfl, by decide, fun q hValid _ =>
        (body0_allowAbort.2.2 q hValid trivial).1⟩
    | succ _ => cases hBody
  · exact ⟨rfl, rfl, rfl, rfl, body0_allowAbort, body0_noAbort⟩

end Proof
