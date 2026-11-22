prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.Option.Basic

namespace ColumnarMemoryAndFloat

/-!
# Columnar Dead-Row Bit-Validity (`FromBytes` vs. `bool`), Empty-Safe Dictionary Gather,
# Disconnected Ghost-Real Float Unsoundness, and GoogleSQL `NaN < -Inf` Total Preorder
-/

/-! ## 1. Rust MIR Uninitialized & Bit-Validity Rules on Dead/NULL Columnar Slots -/

inductive MemSlot where
  | uninit
  | init (bits : Nat)

/-- `FromBytes` integer (`i64`/`u64`) read: faults iff `.uninit`; every initialized bit pattern is valid. -/
def rustMirReadFromBytesI64 (slot : MemSlot) : Option Nat :=
  match slot with
  | .uninit    => none
  | .init bits => some bits

/-- Restricted-validity scalar (`bool`, `0..=1`) read (`Validity.checkScalar` `invalidScalarBits`):
    faults on BOTH `.uninit` AND initialized bytes `>= 2`. -/
def rustMirReadBoolByte (slot : MemSlot) : Option Bool :=
  match slot with
  | .uninit    => none
  | .init bits =>
    if Nat.beq bits 0 then some false
    else if Nat.beq bits 1 then some true
    else none

def branchlessScanI64 (validBit : Bool) (slot : MemSlot) : Option (Option Nat) :=
  match rustMirReadFromBytesI64 slot with
  | none      => none
  | some bits => some (match validBit with | true => some bits | false => none)

theorem branchlessScan_uninit_dead_row_is_ub :
    branchlessScanI64 false .uninit = none := rfl

theorem branchlessScan_stale_init_i64_safe_and_invariant (s1 s2 : Nat) :
    branchlessScanI64 false (.init s1) = some none ∧
    branchlessScanI64 false (.init s1) = branchlessScanI64 false (.init s2) :=
  ⟨rfl, rfl⟩

/-- Contrast witness: unlike `i64` (`FromBytes`), reading initialized slack byte `2`
    as Rust `bool` faults with `invalidScalarBits` UB (`none`). -/
theorem rustMirReadBool_stale_byte2_is_ub :
    rustMirReadBoolByte (.init 2) = none ∧ rustMirReadBoolByte (.init 0) = some false :=
  ⟨rfl, rfl⟩

/-! ## 2. Dictionary Column Double-Null Indirection (Empty-Safe & Optional-Bitmap) -/

structure DictColumn where
  dictVals   : List Int
  dictNulls  : Option (List Bool)
  indices    : List Nat
  outerNulls : Option (List Bool)

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ k => listGet? xs k

noncomputable def listGetInt? (xs : List Int) (idx : Nat) : Option Int := listGet? xs idx
noncomputable def listGetBool? (xs : List Bool) (idx : Nat) : Option Bool := listGet? xs idx
noncomputable def listGetNat? (xs : List Nat) (idx : Nat) : Option Nat := listGet? xs idx

noncomputable def readOptNullBit (optNulls : Option (List Bool)) (idx : Nat) : Option Bool :=
  match optNulls with
  | none    => some false
  | some bs => listGetBool? bs idx

noncomputable def logicalMappedRead (col : DictColumn) (r : Nat) : Option (Option Int) :=
  match readOptNullBit col.outerNulls r, listGetNat? col.indices r with
  | some true, some _ => some none
  | some false, some idx =>
    match readOptNullBit col.dictNulls idx, listGetInt? col.dictVals idx with
    | some true, some _  => some none
    | some false, some v => some (some v)
    | _, _               => none
  | _, _ => none

noncomputable def safeBlendedGather (col : DictColumn) (r : Nat) : Option (Option Int) :=
  match readOptNullBit col.outerNulls r, listGetNat? col.indices r with
  | some outerN, some rawIdx =>
    match col.dictVals with
    | [] =>
      match outerN with
      | true  => some none
      | false => none
    | _ :: _ =>
      let blendedIdx := match outerN with | true => 0 | false => rawIdx
      match readOptNullBit col.dictNulls blendedIdx, listGetInt? col.dictVals blendedIdx with
      | some innerN, some v =>
        some (match outerN || innerN with | true => none | false => some v)
      | _, _ => none
  | _, _ => none

def emptyDictAllOuterNull : DictColumn :=
  { dictVals := [], dictNulls := none, indices := [999999], outerNulls := some [true] }

def omittedOuterBitmapInnerNull : DictColumn :=
  { dictVals := [100, 777], dictNulls := some [false, true], indices := [0, 1], outerNulls := none }

theorem mappedGather_emptyDict_and_omittedBitmap_witness :
    safeBlendedGather emptyDictAllOuterNull 0 = some none ∧
    logicalMappedRead emptyDictAllOuterNull 0 = some none ∧
    safeBlendedGather omittedOuterBitmapInnerNull 0 = some (some 100) ∧
    safeBlendedGather omittedOuterBitmapInnerNull 1 = some none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem safeBlendedGather_eq_logicalMappedRead (col : DictColumn) (r : Nat)
    (hDictNullsWf :
      match col.dictVals, col.dictNulls with
      | _ :: _, some [] => False
      | _, _ => True)
    (hActiveInBounds :
      match readOptNullBit col.outerNulls r, listGetNat? col.indices r with
      | some false, some idx =>
        ∃ b v, readOptNullBit col.dictNulls idx = some b ∧ listGetInt? col.dictVals idx = some v
      | _, _ => True) :
    safeBlendedGather col r = logicalMappedRead col r := by
  cases col with | mk dvs dns idxs ons =>
  dsimp only [safeBlendedGather, logicalMappedRead] at hDictNullsWf hActiveInBounds ⊢
  cases hOn : readOptNullBit ons r
  · rfl
  · rename_i outerN
    cases hIdx : listGetNat? idxs r
    · cases outerN <;> rfl
    · rename_i rawIdx
      cases dvs
      · cases outerN
        · rw [hOn, hIdx] at hActiveInBounds
          cases hActiveInBounds with | intro b hRest =>
          cases hRest with | intro v hPair =>
          cases hPair with | intro _ hV =>
          cases hV
        · rfl
      · rename_i d0 ds
        cases outerN
        · rw [hOn, hIdx] at hActiveInBounds
          cases hActiveInBounds with | intro b hRest =>
          cases hRest with | intro v hPair =>
          cases hPair with | intro hB hV =>
          dsimp only []
          rw [hB, hV]
          cases b <;> rfl
        · cases dns
          · dsimp only [readOptNullBit, listGetInt?, Bool.true_or]; rfl
          · rename_i dnList
            cases dnList
            · exfalso; exact hDictNullsWf
            · dsimp only [readOptNullBit, listGetBool?, listGetInt?, Bool.true_or]; rfl

/-! ## 3. Ghost-Real Float Soundness Trap (`(2^54 + 1) - 2^54`) vs. GoogleSQL Float Order -/

def twoPow54 : Nat := Nat.shiftLeft 1 54

def ieee64AddAt2Pow54 (a b : Nat) : Nat :=
  let exact := a + b
  if Nat.ble twoPow54 exact then
    let rem4 := Nat.mod exact 4
    let base := Nat.sub exact rem4
    if Nat.blt rem4 2 then base
    else if Nat.blt 2 rem4 then base + 4
    else if Nat.beq (Nat.mod (Nat.div base 4) 2) 0 then base else base + 4
  else exact

structure DisconnectedIdealFloat where
  ieeeVal    : Nat
  ghostExact : Nat

def flFromNat (n : Nat) : DisconnectedIdealFloat :=
  { ieeeVal := n, ghostExact := n }

def flAdd (a b : DisconnectedIdealFloat) : DisconnectedIdealFloat :=
  { ieeeVal := ieee64AddAt2Pow54 a.ieeeVal b.ieeeVal, ghostExact := a.ghostExact + b.ghostExact }

def flSub (a b : DisconnectedIdealFloat) : DisconnectedIdealFloat :=
  { ieeeVal := Nat.sub a.ieeeVal b.ieeeVal, ghostExact := Nat.sub a.ghostExact b.ghostExact }

def runtimeIdealEq (a b : DisconnectedIdealFloat) : Bool :=
  Nat.beq a.ieeeVal b.ieeeVal

def axiomatizedSpecEq (a b : DisconnectedIdealFloat) : Bool :=
  Nat.beq a.ghostExact b.ghostExact

theorem ghostRealFloat_proves_inBounds_while_runtime_oob :
    let big  := flFromNat twoPow54
    let one  := flFromNat 1
    let diff := flSub (flAdd big one) big
    let specIdx    := match axiomatizedSpecEq diff one with | true => 0 | false => 999
    let runtimeIdx := match runtimeIdealEq diff one with | true => 0 | false => 999
    Nat.blt specIdx 1 = true ∧ Nat.blt runtimeIdx 1 = false ∧ runtimeIdx = 999 :=
  ⟨rfl, rfl, rfl⟩

inductive SqlFloatClass where
  | nan      : SqlFloatClass
  | negInf   : SqlFloatClass
  | negZero  : SqlFloatClass
  | posZero  : SqlFloatClass
  | finiteNz : Int → SqlFloatClass
  | posInf   : SqlFloatClass

def intLeBool (a b : Int) : Bool := decide (a ≤ b)
def intEqBool (a b : Int) : Bool := decide (a = b)

def googleSqlSortLe : SqlFloatClass → SqlFloatClass → Bool
  | .nan, _ => true
  | _, .nan => false
  | .negInf, _ => true
  | _, .negInf => false
  | .posInf, .posInf => true
  | _, .posInf => true
  | .posInf, _ => false
  | .negZero, .negZero => true
  | .negZero, .posZero => true
  | .posZero, .negZero => true
  | .posZero, .posZero => true
  | .negZero, .finiteNz b => intLeBool 0 b
  | .posZero, .finiteNz b => intLeBool 0 b
  | .finiteNz a, .negZero => intLeBool a 0
  | .finiteNz a, .posZero => intLeBool a 0
  | .finiteNz a, .finiteNz b => intLeBool a b

def googleSqlGroupEq (a b : SqlFloatClass) : Bool :=
  googleSqlSortLe a b && googleSqlSortLe b a

def googleSqlCanonHash : SqlFloatClass → Int
  | .nan        => Int.negOfNat 2000000000
  | .negInf     => Int.negOfNat 1000000000
  | .negZero    => 0
  | .posZero    => 0
  | .finiteNz z => match intEqBool z 0 with | true => 0 | false => z
  | .posInf     => Int.ofNat 1000000000

theorem googleSqlFloat_nan_smallest_and_signedZero_congruent :
    googleSqlSortLe .nan .negInf = true ∧
    googleSqlSortLe .negInf .nan = false ∧
    googleSqlGroupEq .negZero .posZero = true ∧
    googleSqlCanonHash .negZero = googleSqlCanonHash .posZero :=
  ⟨rfl, rfl, rfl, rfl⟩

end ColumnarMemoryAndFloat
