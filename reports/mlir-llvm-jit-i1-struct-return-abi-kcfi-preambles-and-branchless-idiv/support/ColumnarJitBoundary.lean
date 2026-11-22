prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Int.Basic
import Init.Data.Option.Basic

namespace ColumnarJitBoundary

/-!
# Columnar Row-Kernel Error Gating, `CheckNotError` Subquery Inlining,
# Branchless `#DE`-Free Division, `{i64, i1}` ABI Masking, and Two-Tier KCFI W^X JIT Composition
-/

inductive ErrorCode where
  | none
  | divByZero
  | overflow

def ErrorCode.isErr : ErrorCode → Bool
  | .none => false
  | _ => true

def firstError (e1 e2 : ErrorCode) : ErrorCode :=
  match e1 with
  | .none => e2
  | _ => e1

/-- Columnar cell at a row: when `isNull = true`, `payload` may be an arbitrary
    frozen integer (`llvm.freeze` on stale/slack column memory). -/
structure RawCell where
  payload : Int
  isNull  : Bool

/-- Evaluation result distinguishing catchable expression errors (`catchableErr`,
    caught by `ISERROR` / `SAFE` / `TRY`) from outer subquery errors (`escapedErr`,
    enforced by an outer `CheckNotError` barrier). -/
structure EvalOut where
  val          : Int
  isNull       : Bool
  catchableErr : ErrorCode
  escapedErr   : ErrorCode

def EvalOut.totalErr (o : EvalOut) : ErrorCode :=
  firstError o.escapedErr o.catchableErr

def intMin64 : Int := Int.negOfNat (Nat.shiftLeft 1 63)
def intMax64 : Int := Int.ofNat (Nat.sub (Nat.shiftLeft 1 63) 1)

def inI64Range (z : Int) : Bool :=
  decide (intMin64 ≤ z) && decide (z ≤ intMax64)

def boolXor (a b : Bool) : Bool :=
  match a, b with
  | true, false => true
  | false, true => true
  | _, _ => false

/-- Truncating integer division toward zero over `Init.Data.Nat.Div.Basic` + `Init.Data.Int.Basic`. -/
def intTruncDiv (num den : Int) : Int :=
  let qNat := Nat.div (Int.natAbs num) (Int.natAbs den)
  match boolXor (decide (num < 0)) (decide (den < 0)) with
  | true  => Int.negOfNat qNat
  | false => Int.ofNat qNat

def intBeq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

def hwDivTrap (num den : Int) : Bool :=
  intBeq den 0 || (intBeq num intMin64 && intBeq den (Int.negOfNat 1))

def safeIntQuot (num den : Int) : Int :=
  match intBeq den 0 with
  | true => 0
  | false =>
    match intBeq num intMin64 && intBeq den (Int.negOfNat 1) with
    | true  => intMin64
    | false => intTruncDiv num den

inductive Expr where
  | col          : Nat → Expr
  | lit          : Int → Bool → Expr
  | addI64       : Expr → Expr → Expr
  | divI64       : Expr → Expr → Expr
  | gtZero       : Expr → Expr
  | isError      : Expr → Expr
  | checkNotErr  : Expr → Expr

noncomputable def readCol : List RawCell → Nat → RawCell
  | [], _ => { payload := 0, isNull := true }
  | c :: _, 0 => c
  | _ :: cs, Nat.succ k => readCol cs k

noncomputable def evalExpr (cols : List RawCell) : Expr → EvalOut
  | .col idx =>
    let c := readCol cols idx
    { val := c.payload, isNull := c.isNull, catchableErr := .none, escapedErr := .none }
  | .lit v n =>
    { val := v, isNull := n, catchableErr := .none, escapedErr := .none }
  | .addI64 a b =>
    let ra := evalExpr cols a
    let rb := evalExpr cols b
    let esc := firstError ra.escapedErr rb.escapedErr
    let argCatch := firstError ra.catchableErr rb.catchableErr
    let anyNull := ra.isNull || rb.isNull
    let sum := ra.val + rb.val
    let ownErr := match inI64Range sum with | true => ErrorCode.none | false => ErrorCode.overflow
    let catchErr :=
      match argCatch with
      | .none => match anyNull with | true => ErrorCode.none | false => ownErr
      | e => e
    { val := sum, isNull := anyNull, catchableErr := catchErr, escapedErr := esc }
  | .divI64 a b =>
    let ra := evalExpr cols a
    let rb := evalExpr cols b
    let esc := firstError ra.escapedErr rb.escapedErr
    let argCatch := firstError ra.catchableErr rb.catchableErr
    let anyNull := ra.isNull || rb.isNull
    let ownErr :=
      match intBeq rb.val 0 with
      | true => ErrorCode.divByZero
      | false =>
        match intBeq ra.val intMin64 && intBeq rb.val (Int.negOfNat 1) with
        | true  => ErrorCode.overflow
        | false => ErrorCode.none
    let q := safeIntQuot ra.val rb.val
    let catchErr :=
      match argCatch with
      | .none => match anyNull with | true => ErrorCode.none | false => ownErr
      | e => e
    { val := q, isNull := anyNull, catchableErr := catchErr, escapedErr := esc }
  | .gtZero a =>
    let ra := evalExpr cols a
    let bval := match decide (0 < ra.val) with | true => (1 : Int) | false => 0
    { val := bval, isNull := ra.isNull, catchableErr := ra.catchableErr, escapedErr := ra.escapedErr }
  | .isError a =>
    let ra := evalExpr cols a
    let bval := match ra.catchableErr.isErr with | true => (1 : Int) | false => 0
    { val := bval, isNull := false, catchableErr := .none, escapedErr := ra.escapedErr }
  | .checkNotErr a =>
    let ra := evalExpr cols a
    { val := ra.val, isNull := ra.isNull, catchableErr := .none, escapedErr := ra.totalErr }

def zeroRow : List RawCell := [{ payload := 0, isNull := false }]

theorem naiveSubqueryInline_swallows_error :
    (evalExpr zeroRow (.isError (.addI64 (.divI64 (.lit 1 false) (.col 0)) (.lit 2 false)))).totalErr = .none ∧
    (evalExpr zeroRow (.isError (.addI64 (.divI64 (.lit 1 false) (.col 0)) (.lit 2 false)))).val = 1 :=
  ⟨rfl, rfl⟩

theorem checkNotErrInline_preserves_subquery_abort :
    (evalExpr zeroRow (.isError (.addI64 (.checkNotErr (.divI64 (.lit 1 false) (.col 0))) (.lit 2 false)))).totalErr = .divByZero :=
  rfl

theorem checkNotErr_materialized_col0_equiv (cols : List RawCell) (eInner : Expr) :
    (evalExpr cols eInner).totalErr = .none →
    evalExpr ([{ payload := (evalExpr cols eInner).val, isNull := (evalExpr cols eInner).isNull }]) (.col 0) =
    evalExpr cols (.checkNotErr eInner) := by
  intro hNoErr
  dsimp only [evalExpr, readCol]
  rw [hNoErr]

/-! ## 2. Filter-Before-Projection Gating & Branchless `#DE`-Free Speculative Lowering -/

structure RowKernelResult where
  kept    : Bool
  outVal  : Int
  outNull : Bool
  err     : ErrorCode

noncomputable def semWhereRow (qualifying : Bool) (cols : List RawCell) (filt proj : Expr) : RowKernelResult :=
  match qualifying with
  | false => { kept := false, outVal := 0, outNull := true, err := .none }
  | true =>
    let rf := evalExpr cols filt
    match rf.totalErr with
    | .divByZero => { kept := false, outVal := 0, outNull := true, err := .divByZero }
    | .overflow  => { kept := false, outVal := 0, outNull := true, err := .overflow }
    | .none =>
      match (!rf.isNull) && (!decide (rf.val = 0)) with
      | false => { kept := false, outVal := 0, outNull := true, err := .none }
      | true  =>
        let rp := evalExpr cols proj
        { kept := true, outVal := rp.val, outNull := rp.isNull, err := rp.totalErr }

def rejectedDivZeroRow : List RawCell :=
  [{ payload := 0, isNull := false }, { payload := 0, isNull := false }]

theorem hoistedFallibleOp_leaks_error_on_filtered_row :
    (semWhereRow true rejectedDivZeroRow (.gtZero (.col 0)) (.divI64 (.lit 100 false) (.col 1))).err = .none ∧
    (evalExpr rejectedDivZeroRow (.divI64 (.lit 100 false) (.col 1))).totalErr = .divByZero :=
  ⟨rfl, rfl⟩

structure HwDivStep where
  trapped : Bool
  quot    : Int
  isNull  : Bool
  err     : ErrorCode

def execBranchlessDivLane (laneActive : Bool) (x y : RawCell) : HwDivStep :=
  let anyNull := x.isNull || y.isNull
  let divZero := intBeq y.payload 0
  let divOvfl := intBeq x.payload intMin64 && intBeq y.payload (Int.negOfNat 1)
  let valid := laneActive && (!anyNull) && (!divZero) && (!divOvfl)
  let blendedDen := match valid with | true => y.payload | false => 1
  let trapped := hwDivTrap x.payload blendedDen
  let q := safeIntQuot x.payload blendedDen
  let rawErr :=
    match divZero with
    | true  => ErrorCode.divByZero
    | false => match divOvfl with | true => ErrorCode.overflow | false => ErrorCode.none
  let laneErr :=
    match laneActive && (!anyNull) with
    | true  => rawErr
    | false => ErrorCode.none
  { trapped := trapped, quot := q, isNull := anyNull, err := laneErr }

private theorem hwDivTrap_one_false (num : Int) : hwDivTrap num 1 = false := by
  dsimp only [hwDivTrap]
  have h1 : intBeq 1 0 = false := rfl
  have h2 : intBeq 1 (Int.negOfNat 1) = false := rfl
  rw [h1, h2]
  cases intBeq num intMin64 <;> rfl

theorem execBranchlessDivLane_never_traps (laneActive : Bool) (x y : RawCell) :
    (execBranchlessDivLane laneActive x y).trapped = false := by
  cases x with | mk xp xn =>
  cases y with | mk yp yn =>
  dsimp only [execBranchlessDivLane, RawCell.payload, RawCell.isNull]
  cases laneActive
  · exact hwDivTrap_one_false xp
  · cases xn
    · cases yn
      · cases hDZ : intBeq yp 0
        · cases hMin : intBeq xp intMin64
          · change hwDivTrap xp yp = false
            dsimp only [hwDivTrap]
            rw [hDZ, hMin]
            rfl
          · cases hNeg : intBeq yp (Int.negOfNat 1)
            · change hwDivTrap xp yp = false
              dsimp only [hwDivTrap]
              rw [hDZ, hMin, hNeg]
              rfl
            · exact hwDivTrap_one_false xp
        · exact hwDivTrap_one_false xp
      · exact hwDivTrap_one_false xp
    · exact hwDivTrap_one_false xp

theorem execBranchlessDivLane_refines_sqlDiv (x y : RawCell) :
    (execBranchlessDivLane true x y).err = (evalExpr [x, y] (.divI64 (.col 0) (.col 1))).totalErr ∧
    (execBranchlessDivLane true x y).isNull = (evalExpr [x, y] (.divI64 (.col 0) (.col 1))).isNull ∧
    ((execBranchlessDivLane true x y).isNull = false →
     (execBranchlessDivLane true x y).err = .none →
     (execBranchlessDivLane true x y).quot = (evalExpr [x, y] (.divI64 (.col 0) (.col 1))).val) := by
  cases x with | mk xp xn =>
  cases y with | mk yp yn =>
  dsimp only [execBranchlessDivLane, evalExpr, readCol, EvalOut.totalErr, firstError,
              RawCell.payload, RawCell.isNull, EvalOut.val, EvalOut.isNull,
              EvalOut.catchableErr, EvalOut.escapedErr]
  cases xn
  · cases yn
    · cases hDZ : intBeq yp 0 <;> cases hMin : intBeq xp intMin64 <;> cases hNeg : intBeq yp (Int.negOfNat 1)
      all_goals refine ⟨rfl, rfl, ?_⟩
      all_goals intro _ hErr
      all_goals try cases hErr
      all_goals exact rfl
    · refine ⟨rfl, rfl, ?_⟩
      intro hN _; cases hN
  · refine ⟨rfl, rfl, ?_⟩
    intro hN _; cases hN

/-! ## 3. `{i64, i1}` vs `{i64, i8}` ABI Validity & Two-Tier KCFI W^X JIT Composition -/

def rustBoolValid (dlByte : Nat) : Bool :=
  Nat.blt dlByte 2

def llvmTruncRetDl (flagsByte : Nat) : Nat := flagsByte
def llvmZextRetDl (flagsByte : Nat) : Nat := Nat.land flagsByte 1

theorem llvmTruncRetDl_violates_rustBool_on_2 :
    rustBoolValid (llvmTruncRetDl 2) = false := rfl

theorem llvmZextRetDl_always_valid (b : Bool) :
    rustBoolValid (llvmZextRetDl (match b with | false => 0 | true => 1)) = true := by
  cases b <;> rfl

inductive PagePerm where
  | readWrite
  | readExec

structure SealedJitKernel (Batch Out : Type) where
  expectedTypeId : Nat
  preambleTag    : Nat
  perm           : PagePerm
  copiedPrivate  : Bool
  execSem        : Batch → Option Out

def kcfiCallSafe {Batch Out : Type} (k : SealedJitKernel Batch Out) (callerTypeId : Nat) : Bool :=
  Nat.beq k.preambleTag callerTypeId &&
  (match k.perm with | .readExec => true | .readWrite => false) &&
  k.copiedPrivate

def sealKernelTcb {Code Batch Out : Type}
    (isaDecodeExec : Code → Batch → Option Out)
    (expectedTypeId : Nat) (code : Code) : SealedJitKernel Batch Out :=
  { expectedTypeId := expectedTypeId
    preambleTag    := expectedTypeId
    perm           := .readExec
    copiedPrivate  := true
    execSem        := isaDecodeExec code }

def compileTwoTier {Code Cert Batch Out : Type}
    (isaDecodeExec : Code → Batch → Option Out)
    (expectedTypeId : Nat)
    (tier1Code : Code)
    (optCode : Code) (cert : Cert)
    (certCheck : Code → Cert → Bool) : SealedJitKernel Batch Out :=
  let chosen := match certCheck optCode cert with | true => optCode | false => tier1Code
  sealKernelTcb isaDecodeExec expectedTypeId chosen

theorem compileTwoTier_sound_and_kcfi_safe
    {Code Cert Batch Out : Type}
    (isaDecodeExec : Code → Batch → Option Out)
    (spec : Batch → Out)
    (typeId : Nat)
    (tier1Code optCode : Code)
    (cert : Cert)
    (certCheck : Code → Cert → Bool)
    (hTier1 : ∀ b, isaDecodeExec tier1Code b = some (spec b))
    (hCertSound : certCheck optCode cert = true → ∀ b, isaDecodeExec optCode b = some (spec b)) :
    kcfiCallSafe (compileTwoTier isaDecodeExec typeId tier1Code optCode cert certCheck) typeId = true ∧
    ∀ b, (compileTwoTier isaDecodeExec typeId tier1Code optCode cert certCheck).execSem b = some (spec b) := by
  unfold compileTwoTier sealKernelTcb kcfiCallSafe
  have hBeq : Nat.beq typeId typeId = true := Nat.beq_refl typeId
  rw [hBeq]
  refine ⟨rfl, ?_⟩
  intro b
  cases hC : certCheck optCode cert
  · exact hTier1 b
  · exact hCertSound hC b

/-- Concrete non-vacuous `MiniX86DivProg` instantiation of `compileTwoTier`:
    `corruptOptProg` omits `blendBeforeIdiv` (`false`, trapping on `(42, 0)` -> `none`), so `checkMiniX86Cert`
    rejects it (`false`) and `compileTwoTier` falls back cleanly to `tier1DivProg`. -/
structure MiniX86DivProg where
  blendBeforeIdiv : Bool
  maskRetDl       : Bool

def evalMiniX86Div (prog : MiniX86DivProg) (pair : RawCell × RawCell) : Option (Bool × ErrorCode × Int) :=
  match prog.maskRetDl with
  | false => none
  | true =>
    let step := execBranchlessDivLane true pair.1 pair.2
    match prog.blendBeforeIdiv with
    | false =>
      match hwDivTrap pair.1.payload pair.2.payload with
      | true  => none
      | false => some (step.isNull, step.err, step.quot)
    | true => some (step.isNull, step.err, step.quot)

def checkMiniX86Cert (prog : MiniX86DivProg) (_cert : Unit) : Bool :=
  prog.blendBeforeIdiv && prog.maskRetDl

def tier1DivProg : MiniX86DivProg := { blendBeforeIdiv := true, maskRetDl := true }
def corruptOptProg : MiniX86DivProg := { blendBeforeIdiv := false, maskRetDl := true }

theorem concrete_twoTier_corruptOpt_rejected_and_falls_back :
    let deadZeroBatch : RawCell × RawCell := ({ payload := 42, isNull := true }, { payload := 0, isNull := false })
    evalMiniX86Div corruptOptProg deadZeroBatch = none ∧
    checkMiniX86Cert corruptOptProg () = false ∧
    (compileTwoTier evalMiniX86Div 0xb11990e8 tier1DivProg corruptOptProg () checkMiniX86Cert).execSem deadZeroBatch =
      some (true, .none, 42) :=
  ⟨rfl, rfl, rfl⟩

end ColumnarJitBoundary
