prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Option.Basic

namespace Wave2ColumnarAdtAndSqlSemantics

/-!
# Wave 2 Mechanization:
1. Nominal `AdtDefTable` Indirection + `PtrMetaKind` (`thin | sliceLen | dynVtable`) for
   Recursive MIR Types (`Box<Expr>`, Custom DSTs) vs. Unboxed & Zero-Length Array Cycle Rejection
2. Segmented Null-Gap Nested `Array` Column Offset Invariants vs. Arrow Global Monotonicity
3. Three-Tier SQL Error Lattice: Unsuppressible `sysAbortErr` (`CANCELLED`/`DEADLINE`/`OOM`),
   `AND`/`OR` Dominant-Value User-Error Absorption (`<err> AND FALSE = FALSE`), and
   `CASE`/`IF` Left-to-Right Error Short-Circuiting
4. Sterbenz-Exact `f64 -> i64` Halfway-Away-From-Zero Rounding vs. `floor(x + 0.5)` Double-Rounding
5. `Quot`-Free, `_unsafe_rec`-Free Constructive Bag Equivalence (`List.foldr` `countOcc`) &
   Exact-Accumulator Order / Sliding-Window Invariance
-/

/-! ## 1. Nominal `AdtDefTable` + `PtrMetaKind` Layout Resolution for Recursive MIR Types -/

abbrev AdtId := Nat

/-- Explicit pointer metadata tag carried on `.rawPtr` / `.ref` so layout computation
    never unfolds `pointee` even when `pointee` is `[T]`, `dyn Trait`, or a custom
    unsized DST struct (`struct Dst { hdr: u64, tail: [u8] }`). -/
inductive PtrMetaKind where
  | thin      -- `Sized` pointee: 8 B on 64-bit targets
  | sliceLen  -- `[T]`, `str`, or slice-tailed custom DST: 16 B (`ptr + elem_count`)
  | dynVtable -- `dyn Trait` or dyn-tailed custom DST: 16 B (`ptr + vtable_ptr`)

inductive NominalMirTy where
  | i64
  | rawPtr (ptrMeta : PtrMetaKind) (pointee : NominalMirTy)
  | array (elem : NominalMirTy) (len : Nat)
  | adt (id : AdtId)

inductive AdtDecl where
  | structDecl (fields : List NominalMirTy)
  | enumDecl (tagBytes : Nat) (variants : List (List NominalMirTy))

def listGet? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  (xs.drop idx).head?

def maxNat (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true  => b
  | false => a

def ptrByteSize : PtrMetaKind → Nat
  | .thin      => 8
  | .sliceLen  => 16
  | .dynVtable => 16

def sumFieldsSizeWith (rec : NominalMirTy → Option Nat) (fs : List NominalMirTy) : Option Nat :=
  fs.foldr
    (fun f acc =>
      match rec f, acc with
      | some a, some b => some (a + b)
      | _, _ => none)
    (some 0)

def maxVariantsSizeWith (rec : NominalMirTy → Option Nat)
    (vs : List (List NominalMirTy)) : Option Nat :=
  vs.foldr
    (fun v acc =>
      match sumFieldsSizeWith rec v, acc with
      | some a, some b => some (maxNat a b)
      | _, _ => none)
    (some 0)

/-- Computable (`0` `noncomputable`, `0` `_unsafe_rec`) `@Nat.rec` inline byte-size resolver:
    - `.rawPtr meta _` returns `ptrByteSize meta` (`8` or `16` B) in O(1) WITHOUT unfolding `pointee`,
      resolving cyclic pointer-indirected types (`Box<Expr>`, `*const [Expr]`, custom DSTs).
    - `.array elem len` unconditionally consumes inline `fuel` on `elem` even when `len = 0`,
      rejecting illegal zero-length unboxed cycles (`struct Weird([Weird; 0])`) alongside `enum Bad { Val(Bad) }`. -/
def byteSizeOfTy (table : List AdtDecl) (fuel : Nat) : NominalMirTy → Option Nat :=
  @Nat.rec (fun _ => NominalMirTy → Option Nat)
    (fun ty =>
      match ty with
      | .i64 => some 8
      | .rawPtr ptrMeta _ => some (ptrByteSize ptrMeta)
      | .array _ _ => none
      | .adt _ => none)
    (fun _ rec ty =>
      match ty with
      | .i64 => some 8
      | .rawPtr ptrMeta _ => some (ptrByteSize ptrMeta)
      | .array elem len =>
        match rec elem with
        | none => none
        | some elemBytes => some (elemBytes * len)
      | .adt id =>
        match listGet? table id with
        | none => none
        | some (.structDecl fs) => sumFieldsSizeWith rec fs
        | some (.enumDecl tagBytes vs) =>
          match maxVariantsSizeWith rec vs with
          | none => none
          | some maxPayload => some (tagBytes + maxPayload))
    fuel

/-- `AdtId 0` = `enum Expr { Lit(i64), Add(*const Expr, *const Expr), Slice(*const [Expr]) }`
    (`8B tag + max(8, 16, 16) = 24B`).
    `AdtId 1` = illegal unboxed `enum Bad { SelfVal(Bad) }`.
    `AdtId 2` = illegal zero-length array cycle `struct Weird([Weird; 0])`. -/
def sampleAdtTable : List AdtDecl :=
  [ .enumDecl 8 [[.i64], [.rawPtr .thin (.adt 0), .rawPtr .thin (.adt 0)], [.rawPtr .sliceLen (.adt 0)]]
  , .enumDecl 8 [[.adt 1]]
  , .structDecl [.array (.adt 2) 0] ]

theorem boxedRecursiveExpr_layout_24B :
    byteSizeOfTy sampleAdtTable 2 (.adt 0) = some 24 := rfl

theorem unboxedAndZeroArrayCycles_rejected_failClosed :
    byteSizeOfTy sampleAdtTable 5 (.adt 1) = none ∧
    byteSizeOfTy sampleAdtTable 5 (.adt 2) = none :=
  ⟨rfl, rfl⟩

/-! ## 2. Segmented Null-Gap Nested `Array` Column Offset Invariant -/

structure NullGapArrayCol where
  elements : List Nat
  offsets  : List Nat
  isNull   : List Bool

def arrowGlobalMonotonic (xs : List Nat) : Bool :=
  (xs.foldr
    (fun a st =>
      match st with
      | (none, ok) => (some a, ok)
      | (some next, ok) => (some a, Nat.ble a next && ok))
    (none, true)).2

/-- Per-row active-slice invariant: ONLY non-null rows `r` (`isNull[r] = false`) require
    `offsets[r] <= offsets[r + 1] <= elements.length`; offsets straddling two adjacent
    null arrays (`isNull[k-1] = true ∧ isNull[k] = true`), leading null row `0`, or trailing
    final null row `N - 1` may hold arbitrary `u32` slack values! -/
def nullGapRowValid (col : NullGapArrayCol) (r : Nat) : Bool :=
  match listGet? col.isNull r with
  | none => false
  | some true => true
  | some false =>
    match listGet? col.offsets r, listGet? col.offsets (Nat.succ r) with
    | some lo, some hi => Nat.ble lo hi && Nat.ble hi col.elements.length
    | _, _ => false

def readNullGapArrayRow (col : NullGapArrayCol) (r : Nat) :
    Option (Option (List Nat)) :=
  match listGet? col.isNull r with
  | none => none
  | some true => some none
  | some false =>
    match listGet? col.offsets r, listGet? col.offsets (Nat.succ r) with
    | some lo, some hi =>
      match Nat.ble lo hi && Nat.ble hi col.elements.length with
      | true  => some (some ((col.elements.drop lo).take (Nat.sub hi lo)))
      | false => none
    | _, _ => none

/-- Concrete witness: 4 arrays `[[10, 20], NULL, NULL, [30]]` with `offsets = [0, 2, 999999, 2, 3]`:
    `offsets[2] = 999999` sits between two adjacent `NULL` rows (`isNull[1] = true, isNull[2] = true`).
    Arrow's global monotonicity check rejects it (`false`), whereas `nullGapRowValid` holds on all
    rows `0..3` and reads `row 0 = [10, 20]`, `row 1 = NULL`, `row 2 = NULL`, `row 3 = [30]`! -/
def validNullGapCol : NullGapArrayCol :=
  { elements := [10, 20, 30]
    offsets  := [0, 2, 999999, 2, 3]
    isNull   := [false, true, true, false] }

theorem naiveArrowCheck_rejects_valid_nullGap_column :
    arrowGlobalMonotonic validNullGapCol.offsets = false ∧
    nullGapRowValid validNullGapCol 0 = true ∧
    nullGapRowValid validNullGapCol 1 = true ∧
    nullGapRowValid validNullGapCol 2 = true ∧
    nullGapRowValid validNullGapCol 3 = true ∧
    readNullGapArrayRow validNullGapCol 0 = some (some [10, 20]) ∧
    readNullGapArrayRow validNullGapCol 2 = some none ∧
    readNullGapArrayRow validNullGapCol 3 = some (some [30]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem readNullGapArrayRow_total_of_valid (col : NullGapArrayCol) (r : Nat)
    (hValid : nullGapRowValid col r = true) :
    ∃ res, readNullGapArrayRow col r = some res := by
  revert hValid
  dsimp only [nullGapRowValid, readNullGapArrayRow]
  cases listGet? col.isNull r with
  | none =>
    intro hF
    nomatch hF
  | some isN =>
    cases isN with
    | true =>
      intro _
      exact ⟨none, rfl⟩
    | false =>
      dsimp only
      cases listGet? col.offsets r with
      | none =>
        intro hF
        nomatch hF
      | some lo =>
        cases listGet? col.offsets (Nat.succ r) with
        | none =>
          intro hF
          nomatch hF
        | some hi =>
          dsimp only
          cases Nat.ble lo hi && Nat.ble hi col.elements.length with
          | false =>
            intro hF
            nomatch hF
          | true =>
            intro _
            exact ⟨some ((col.elements.drop lo).take (Nat.sub hi lo)), rfl⟩

/-! ## 3. Three-Tier SQL Error Lattice: `sysAbortErr` vs. `AND`/`OR` Absorption vs. `CASE` -/

inductive SqlErrTier where
  | ok
  | userEvalErr   -- `OUT_OF_RANGE` / `INVALID_ARGUMENT`: suppressible by `SAFE` / `IFERROR` / `ISERROR` AND skippable under `AND FALSE` / `OR TRUE`
  | sysAbortErr   -- `CANCELLED` / `DEADLINE_EXCEEDED` / `RESOURCE_EXHAUSTED`: NEVER suppressed or absorbed!

structure BoolEval3 where
  val    : Bool
  isNull : Bool
  err    : SqlErrTier

def evalIsError3Tier (x : BoolEval3) : BoolEval3 :=
  match x.err with
  | .ok          => { val := false, isNull := false, err := .ok }
  | .userEvalErr => { val := true,  isNull := false, err := .ok }
  | .sysAbortErr => { val := false, isNull := true,  err := .sysAbortErr }

def isDefinitelyFalse (x : BoolEval3) : Bool :=
  match x.err with
  | .ok => (!x.isNull) && (!x.val)
  | _   => false

def isDefinitelyTrue (x : BoolEval3) : Bool :=
  match x.err with
  | .ok => (!x.isNull) && x.val
  | _   => false

def firstErrTier (e1 e2 : SqlErrTier) : SqlErrTier :=
  match e1, e2 with
  | .sysAbortErr, _ => .sysAbortErr
  | _, .sysAbortErr => .sysAbortErr
  | .userEvalErr, _ => .userEvalErr
  | _, .userEvalErr => .userEvalErr
  | .ok, .ok        => .ok

/-- SQL `AND` under unordered/skippable operand evaluation:
    - If `a` is `sysAbortErr`, aborts immediately without evaluating `b`.
    - If `a` is `FALSE`, short-circuits `b` and returns `FALSE`.
    - Otherwise evaluates `b`: if `b` raises `sysAbortErr`, aborts; if `b` is `FALSE`,
      `FALSE` absorbs an earlier `a.err = .userEvalErr` (`<user_err> AND FALSE == FALSE`)! -/
def evalSqlAnd3Tier (a b : BoolEval3) : BoolEval3 :=
  match a.err with
  | .sysAbortErr => { val := false, isNull := true, err := .sysAbortErr }
  | _ =>
    match isDefinitelyFalse a with
    | true => { val := false, isNull := false, err := .ok }
    | false =>
      match b.err with
      | .sysAbortErr => { val := false, isNull := true, err := .sysAbortErr }
      | _ =>
        match isDefinitelyFalse b with
        | true => { val := false, isNull := false, err := .ok }
        | false =>
          let combErr := firstErrTier a.err b.err
          match combErr with
          | .ok =>
            let anyN := a.isNull || b.isNull
            { val := (!anyN), isNull := anyN, err := .ok }
          | e => { val := false, isNull := true, err := e }

/-- SQL `CASE WHEN c0 THEN t0 WHEN c1 THEN t1 ELSE e END`:
    Unlike `AND`, an error (`userEvalErr` or `sysAbortErr`) in `c0` IMMEDIATELY halts
    evaluation and returns `c0.err`, even if `c1` is `TRUE`! -/
def evalSqlCase2When (c0 t0 c1 t1 els : BoolEval3) : BoolEval3 :=
  match c0.err with
  | .sysAbortErr => { val := false, isNull := true, err := .sysAbortErr }
  | .userEvalErr => { val := false, isNull := true, err := .userEvalErr }
  | .ok =>
    match isDefinitelyTrue c0 with
    | true  => t0
    | false =>
      match c1.err with
      | .sysAbortErr => { val := false, isNull := true, err := .sysAbortErr }
      | .userEvalErr => { val := false, isNull := true, err := .userEvalErr }
      | .ok =>
        match isDefinitelyTrue c1 with
        | true  => t1
        | false => els

def vFalse     : BoolEval3 := { val := false, isNull := false, err := .ok }
def vTrue      : BoolEval3 := { val := true,  isNull := false, err := .ok }
def vUserErr   : BoolEval3 := { val := false, isNull := true,  err := .userEvalErr }
def vSysCancel : BoolEval3 := { val := false, isNull := true,  err := .sysAbortErr }

theorem isError_suppresses_userErr_but_propagates_sysAbort :
    evalIsError3Tier vUserErr = { val := true, isNull := false, err := .ok } ∧
    (evalIsError3Tier vSysCancel).err = .sysAbortErr :=
  ⟨rfl, rfl⟩

theorem sqlAnd_false_absorbs_userErr_while_case_propagates_and_sysAbort_wins :
    evalSqlAnd3Tier vUserErr vFalse = vFalse ∧
    (evalSqlAnd3Tier vSysCancel vFalse).err = .sysAbortErr ∧
    (evalSqlAnd3Tier vUserErr vSysCancel).err = .sysAbortErr ∧
    (evalSqlCase2When vUserErr vTrue vTrue vTrue vFalse).err = .userEvalErr :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. Sterbenz-Exact `f64 -> i64` Halfway-Away-From-Zero vs. `floor(x + 0.5)` Double-Rounding -/

/-- Scaled representation of non-negative binary64 numbers in `[0, 2)` in units of `2^-54`:
    `1.0 = 2^54`, `0.5 = 2^53`, and `0.5 - 2^-54 = 2^53 - 1` (`0x3fdfffffffffffff` in `[0.25, 0.5)`).
    - In `[0.25, 0.5)`, `1 ULP = 1` unit (`2^-54`).
    - In `[0.5, 1.0)`,  `1 ULP = 2` units (`2^-53`).
    - In `[1.0, 2.0)`,  `1 ULP = 4` units (`2^-52`). -/
def unitHalf : Nat := Nat.shiftLeft 1 53
def unitOne  : Nat := Nat.shiftLeft 1 54
def preHalfPred : Nat := Nat.sub unitHalf 1

def roundNearestEvenStep (exact step : Nat) : Nat :=
  let halfStep := Nat.div step 2
  let rem := Nat.mod exact step
  let base := Nat.sub exact rem
  if Nat.blt rem halfStep then base
  else if Nat.blt halfStep rem then base + step
  else if Nat.beq (Nat.mod (Nat.div base step) 2) 0 then base else base + step

def ieee64AddUnits2Pow54 (a b : Nat) : Nat :=
  let exact := a + b
  if Nat.ble unitOne exact then
    roundNearestEvenStep exact 4
  else if Nat.ble unitHalf exact then
    roundNearestEvenStep exact 2
  else
    exact

def buggyFloorPlusHalf (xUnits : Nat) : Nat :=
  Nat.div (ieee64AddUnits2Pow54 xUnits unitHalf) unitOne

def sterbenzRoundAwayFromZero (xUnits : Nat) : Nat :=
  let truncInt := Nat.div xUnits unitOne
  let remUnits := Nat.sub xUnits (truncInt * unitOne)
  match Nat.ble unitHalf remUnits with
  | true  => truncInt + 1
  | false => truncInt

theorem floorPlusHalf_doubleRounds_preHalf_while_sterbenz_is_exact :
    buggyFloorPlusHalf preHalfPred = 1 ∧
    sterbenzRoundAwayFromZero preHalfPred = 0 ∧
    sterbenzRoundAwayFromZero unitHalf = 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 5. `Quot`-Free, `_unsafe_rec`-Free Constructive Bag Equivalence & Exact-Sum Invariance -/

def countOcc {α : Type} (eqA : α → α → Bool) (needle : α) (xs : List α) : Nat :=
  xs.foldr
    (fun x rest =>
      match eqA needle x with
      | true  => Nat.succ rest
      | false => rest)
    0

def BagEquiv {α : Type} (eqA : α → α → Bool) (xs ys : List α) : Prop :=
  ∀ k : α, countOcc eqA k xs = countOcc eqA k ys

theorem countOcc_append {α : Type} (eqA : α → α → Bool) (k : α) :
    ∀ (xs ys : List α), countOcc eqA k (xs ++ ys) = countOcc eqA k xs + countOcc eqA k ys
  | [], ys => by
    dsimp only [List.nil_append, countOcc, List.foldr]
    rw [Nat.zero_add]
  | x :: xs, ys => by
    dsimp only [List.cons_append, countOcc, List.foldr]
    change (match eqA k x with | true => Nat.succ (countOcc eqA k (xs ++ ys)) | false => countOcc eqA k (xs ++ ys)) =
      (match eqA k x with | true => Nat.succ (countOcc eqA k xs) | false => countOcc eqA k xs) + countOcc eqA k ys
    rw [countOcc_append eqA k xs ys]
    cases eqA k x
    · rfl
    · rw [Nat.succ_add]

theorem bagEquiv_swap_adjacent {α : Type} (eqA : α → α → Bool) (x y : α) (rest : List α) :
    BagEquiv eqA (x :: y :: rest) (y :: x :: rest) := by
  intro k
  dsimp only [countOcc, List.foldr]
  cases eqA k x <;> cases eqA k y <;> rfl

/-- Exact fixed-point / 2163-bit superaccumulator model (`sumExact : List Nat → Nat`):
    Adding and removing elements in a sliding window or across reordered hash buckets
    satisfies exact associativity, commutativity, and `Add`+`Remove` cancellation! -/
def sumExact (xs : List Nat) : Nat :=
  xs.foldr Nat.add 0

theorem sumExact_swap_adjacent (x y : Nat) (rest : List Nat) :
    sumExact (x :: y :: rest) = sumExact (y :: x :: rest) := by
  dsimp only [sumExact, List.foldr]
  change x + (y + sumExact rest) = y + (x + sumExact rest)
  rw [← Nat.add_assoc x y (sumExact rest)]
  rw [Nat.add_comm x y]
  rw [Nat.add_assoc y x (sumExact rest)]

theorem sumExact_window_slide_cancel (leaving acc : Nat) :
    (acc + leaving) - leaving = acc := by
  rw [Nat.add_sub_cancel]

end Wave2ColumnarAdtAndSqlSemantics
