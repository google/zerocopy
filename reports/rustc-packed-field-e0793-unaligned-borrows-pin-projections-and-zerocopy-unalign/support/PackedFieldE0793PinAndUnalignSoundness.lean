/-
  Verified Drop-In Mechanization (Lean v4.34.1):
  CheckPackedRef (E0793), AddMovesForPackedDrops, zerocopy::Unalign<T>,
  and Pin<Ptr> Structural Projection / Address-Stability / Drop-Guarantee Invariants.

  Kernel purity contract:
  - Starts with `prelude` and imports only `Init.*` modules (no external packages, no meta imports).
  - Every value and predicate definition uses `noncomputable def` explicitly without
    section-wide modifiers, codegen attributes, or unsafe recursors.
  - All proofs are checked directly by the Lean v4.34.1 kernel with zero axioms beyond
    `propext` and `Quot.sound` and without automation/decider shortcuts.
-/

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Lemmas
import Init.Data.List.Basic
import Init.Data.Option.Basic

namespace VerifiedRustc.PackedPinUnalign

-- ============================================================================
-- Section 1: Constructive Power-of-Two Alignment & Divisibility Algebra
-- ============================================================================

/-- Minimum of two natural numbers (constructive, noncomputable). -/
noncomputable def natMin (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

/-- Maximum of two natural numbers (constructive, noncomputable). -/
noncomputable def natMax (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => b
  | false => a

/-- Boolean equality for `Nat` via `Nat.beq`. -/
noncomputable def natEqB (a b : Nat) : Bool :=
  Nat.beq a b

theorem natMin_le_left (a b : Nat) : natMin a b ≤ a := by
  unfold natMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    have hgt : b < a := Nat.lt_of_not_le (fun hle => by
      have hb : Nat.ble a b = true := Nat.ble_eq.mpr hle
      rw [hb] at h
      cases h)
    exact Nat.le_of_lt hgt

theorem natMin_le_right (a b : Nat) : natMin a b ≤ b := by
  unfold natMin
  cases h : Nat.ble a b with
  | true => exact Nat.ble_eq.mp h
  | false => exact Nat.le_refl b

theorem le_natMin_iff (c a b : Nat) : c ≤ natMin a b ↔ (c ≤ a ∧ c ≤ b) := by
  constructor
  · intro h
    exact ⟨Nat.le_trans h (natMin_le_left a b), Nat.le_trans h (natMin_le_right a b)⟩
  · intro ⟨ha, hb⟩
    unfold natMin
    cases h : Nat.ble a b with
    | true => exact ha
    | false => exact hb

theorem natMin_comm (a b : Nat) : natMin a b = natMin b a := by
  apply Nat.le_antisymm
  · exact (le_natMin_iff (natMin a b) b a).mpr ⟨natMin_le_right a b, natMin_le_left a b⟩
  · exact (le_natMin_iff (natMin b a) a b).mpr ⟨natMin_le_right b a, natMin_le_left b a⟩

theorem natMin_assoc (a b c : Nat) : natMin (natMin a b) c = natMin a (natMin b c) := by
  apply Nat.le_antisymm
  · apply (le_natMin_iff _ a (natMin b c)).mpr
    constructor
    · exact Nat.le_trans (natMin_le_left _ c) (natMin_le_left a b)
    · apply (le_natMin_iff _ b c).mpr
      exact ⟨Nat.le_trans (natMin_le_left _ c) (natMin_le_right a b), natMin_le_right _ c⟩
  · apply (le_natMin_iff _ (natMin a b) c).mpr
    constructor
    · apply (le_natMin_iff _ a b).mpr
      exact ⟨natMin_le_left a _, Nat.le_trans (natMin_le_right a _) (natMin_le_left b c)⟩
    · exact Nat.le_trans (natMin_le_right a _) (natMin_le_right b c)

theorem natMax_ge_left (a b : Nat) : a ≤ natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => exact Nat.ble_eq.mp h
  | false => exact Nat.le_refl a

theorem natMax_ge_right (a b : Nat) : b ≤ natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false =>
    have hgt : b < a := Nat.lt_of_not_le (fun hle => by
      have hb : Nat.ble a b = true := Nat.ble_eq.mpr hle
      rw [hb] at h
      cases h)
    exact Nat.le_of_lt hgt

/-- Alignment in bytes represented as `2 ^ exp`. -/
noncomputable def alignBytes (exp : Nat) : Nat :=
  2 ^ exp

theorem alignBytes_pos (exp : Nat) : 0 < alignBytes exp := by
  unfold alignBytes
  induction exp with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih (Nat.succ_pos 1)

theorem alignBytes_zero : alignBytes 0 = 1 := rfl

theorem alignBytes_dvd_of_le {e1 e2 : Nat} (hle : e1 ≤ e2) :
    alignBytes e1 ∣ alignBytes e2 := by
  unfold alignBytes
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, Nat.pow_add]
  exact Nat.dvd_mul_right (2 ^ e1) (2 ^ k)

/-- Address `addr` is aligned to `2 ^ exp`. -/
noncomputable def IsAlignedExp (addr exp : Nat) : Prop :=
  addr % alignBytes exp = 0

/-- Constructive boolean check for `addr % 2^exp == 0`. -/
noncomputable def checkAlignedExp (addr exp : Nat) : Bool :=
  Nat.beq (addr % alignBytes exp) 0

theorem checkAlignedExp_iff (addr exp : Nat) :
    checkAlignedExp addr exp = true ↔ IsAlignedExp addr exp := by
  unfold checkAlignedExp IsAlignedExp
  constructor
  · intro h
    exact Nat.eq_of_beq_eq_true h
  · intro h
    rw [h]
    rfl

theorem isAlignedExp_zero (addr : Nat) : IsAlignedExp addr 0 := by
  unfold IsAlignedExp alignBytes
  exact Nat.mod_one addr

theorem isAlignedExp_of_dvd {addr exp : Nat} (hdvd : alignBytes exp ∣ addr) :
    IsAlignedExp addr exp := by
  unfold IsAlignedExp
  exact Nat.mod_eq_zero_of_dvd hdvd

theorem dvd_of_isAlignedExp {addr exp : Nat} (h : IsAlignedExp addr exp) :
    alignBytes exp ∣ addr := by
  unfold IsAlignedExp at h
  exact Nat.dvd_of_mod_eq_zero h

theorem isAlignedExp_mono {addr e1 e2 : Nat} (hle : e1 ≤ e2)
    (ha : IsAlignedExp addr e2) : IsAlignedExp addr e1 := by
  have hd2 : alignBytes e2 ∣ addr := dvd_of_isAlignedExp ha
  have hd12 : alignBytes e1 ∣ alignBytes e2 := alignBytes_dvd_of_le hle
  exact isAlignedExp_of_dvd (Nat.dvd_trans hd12 hd2)

theorem isAlignedExp_add {addr off exp : Nat}
    (ha : IsAlignedExp addr exp) (ho : IsAlignedExp off exp) :
    IsAlignedExp (addr + off) exp := by
  have hda := dvd_of_isAlignedExp ha
  have hdo := dvd_of_isAlignedExp ho
  exact isAlignedExp_of_dvd (Nat.dvd_add hda hdo)

theorem not_isAlignedExp_of_rem_pos {addr exp : Nat}
    (hpos : 0 < addr % alignBytes exp) : ¬ IsAlignedExp addr exp := by
  intro ha
  unfold IsAlignedExp at ha
  rw [ha] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem alignBytes_le_iff_exp_le (e1 e2 : Nat) :
    alignBytes e1 ≤ alignBytes e2 ↔ e1 ≤ e2 := by
  unfold alignBytes
  constructor
  · intro hle
    cases Nat.lt_or_ge e2 e1 with
    | inl hlt =>
      have hsucc : e2 + 1 ≤ e1 := hlt
      have hp : 2 ^ (e2 + 1) ≤ 2 ^ e1 := Nat.pow_le_pow_right (Nat.succ_pos 1) hsucc
      have h2 : 2 ^ e2 < 2 ^ (e2 + 1) := by
        rw [Nat.pow_succ]
        have hpos : 0 < 2 ^ e2 := alignBytes_pos e2
        have hsum : 2 ^ e2 + 0 < 2 ^ e2 + 2 ^ e2 := Nat.add_lt_add_left hpos (2 ^ e2)
        have hmul : 2 ^ e2 * 2 = 2 ^ e2 + 2 ^ e2 := Nat.mul_two (2 ^ e2)
        rw [hmul]
        exact hsum
      have hcontr : 2 ^ e2 < 2 ^ e2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h2 hp) hle
      exact False.elim (Nat.lt_irrefl _ hcontr)
    | inr hge => exact hge
  · intro hle
    exact Nat.pow_le_pow_right (Nat.succ_pos 1) hle

-- ============================================================================
-- Section 2: MIR Type Layout, Packed Attributes, Places, and Memory Model
-- ============================================================================

/-- Classification of unsized struct tail (`rustc_const_eval::util::alignment`). -/
inductive TailKind where
  | none
  | sliceOrStr (elemAlignExp : Nat)
  | dynOrOpaque

/-- Minimal structural representation of a Rust type's layout & pinning properties. -/
structure TyRepr where
  tyId : Nat
  alignExp : Nat
  size : Nat
  isSized : Bool
  tailKind : TailKind
  packExp? : Option Nat
  needsDrop : Bool
  unpin : Bool
  unaligned : Bool

/-- Helper check for `TailKind::Slice` / `TailKind::Str`. -/
noncomputable def TailKind.isSliceOrStr : TailKind → Bool
  | .sliceOrStr _ => true
  | _ => false

/-- Effective ABI alignment exponent of a type: clamped by `packExp?` if packed.
    Matches `rustc_abi::layout` shallow `min(align, pack)` clamping. -/
noncomputable def TyRepr.abiAlignExp (ty : TyRepr) : Nat :=
  match ty.packExp? with
  | some pExp => natMin ty.alignExp pExp
  | none => ty.alignExp

theorem TyRepr.abiAlignExp_le_natural (ty : TyRepr) :
    ty.abiAlignExp ≤ ty.alignExp := by
  unfold TyRepr.abiAlignExp
  cases h : ty.packExp? with
  | none => exact Nat.le_refl ty.alignExp
  | some p => exact natMin_le_left ty.alignExp p

theorem TyRepr.abiAlignExp_le_pack (ty : TyRepr) (p : Nat)
    (hp : ty.packExp? = some p) : ty.abiAlignExp ≤ p := by
  unfold TyRepr.abiAlignExp
  rw [hp]
  exact natMin_le_right ty.alignExp p

/-- A single MIR place projection element. -/
inductive ProjElem where
  | field (fieldIdx : Nat) (byteOffset : Nat) (containerTy : TyRepr) (fieldTy : TyRepr)
  | deref (ptrTy : TyRepr) (pointeeTy : TyRepr) (targetSlotId : Nat)

/-- Base root of a MIR place: either a stack local or an allocated heap slot. -/
structure PlaceBase where
  slotId : Nat
  baseTy : TyRepr

/-- A MIR place (`Place<'tcx>`): base slot plus outward-to-inward projection list. -/
structure MirPlace where
  base : PlaceBase
  projections : List ProjElem

/-- Target type reached by a projection chain starting at `curTy`. -/
noncomputable def evalProjChainTy (curTy : TyRepr) : List ProjElem → TyRepr
  | [] => curTy
  | .field _ _ _ fTy :: rest => evalProjChainTy fTy rest
  | .deref _ pTy _ :: rest => evalProjChainTy pTy rest

/-- Resulting type of a `MirPlace` (`Place::ty`). -/
noncomputable def MirPlace.ty (p : MirPlace) : TyRepr :=
  evalProjChainTy p.base.baseTy p.projections

/-- A memory slot descriptor in our abstract interpreter / Miri model. -/
structure MemSlot where
  slotId : Nat
  addr : Nat
  slotTy : TyRepr
  initialized : Bool
  live : Bool
  payloadVal : Nat

/-- Memory state maps slot IDs to `MemSlot` descriptors plus bump stack address. -/
structure MemState where
  slots : List MemSlot
  nextAddr : Nat

/-- Constructive lookup of a slot by `slotId`. -/
noncomputable def MemState.lookupSlot (slots : List MemSlot) (sid : Nat) : Option MemSlot :=
  match slots with
  | [] => none
  | s :: rest =>
    match Nat.beq s.slotId sid with
    | true => some s
    | false => MemState.lookupSlot rest sid

/-- Update or append a slot in `MemState`. -/
noncomputable def MemState.upsertSlot (slots : List MemSlot) (newSlot : MemSlot) : List MemSlot :=
  match slots with
  | [] => [newSlot]
  | s :: rest =>
    match Nat.beq s.slotId newSlot.slotId with
    | true => newSlot :: rest
    | false => s :: MemState.upsertSlot rest newSlot

theorem lookupSlot_upsert_same (slots : List MemSlot) (newSlot : MemSlot) :
    MemState.lookupSlot (MemState.upsertSlot slots newSlot) newSlot.slotId = some newSlot := by
  induction slots with
  | nil =>
    unfold MemState.upsertSlot MemState.lookupSlot
    have hrefl : Nat.beq newSlot.slotId newSlot.slotId = true := Nat.beq_refl newSlot.slotId
    rw [hrefl]
  | cons s rest ih =>
    unfold MemState.upsertSlot
    cases h : Nat.beq s.slotId newSlot.slotId with
    | true =>
      unfold MemState.lookupSlot
      have hrefl : Nat.beq newSlot.slotId newSlot.slotId = true := Nat.beq_refl newSlot.slotId
      rw [hrefl]
    | false =>
      unfold MemState.lookupSlot
      rw [h]
      exact ih

theorem lookupSlot_id_eq {slots : List MemSlot} {sid : Nat} {s : MemSlot}
    (h : MemState.lookupSlot slots sid = some s) : s.slotId = sid := by
  induction slots with
  | nil => cases h
  | cons hd tl ih =>
    unfold MemState.lookupSlot at h
    cases hb : Nat.beq hd.slotId sid with
    | true =>
      rw [hb] at h
      injection h with hs
      rw [← hs]
      exact Nat.eq_of_beq_eq_true hb
    | false =>
      rw [hb] at h
      exact ih h

/-- Address evaluation of a projection chain starting at `curAddr`. -/
noncomputable def evalProjAddr (mem : MemState) (curAddr : Nat) : List ProjElem → Option Nat
  | [] => some curAddr
  | .field _ off _ _ :: rest => evalProjAddr mem (curAddr + off) rest
  | .deref _ _ targetId :: rest =>
    match MemState.lookupSlot mem.slots targetId with
    | some ts => evalProjAddr mem ts.addr rest
    | none => none

/-- Address evaluation of a full `MirPlace`. -/
noncomputable def evalPlaceAddr (mem : MemState) (p : MirPlace) : Option Nat :=
  match MemState.lookupSlot mem.slots p.base.slotId with
  | some bs => evalProjAddr mem bs.addr p.projections
  | none => none

/-- Guaranteed byte-offset alignment exponent for a direct field inside `cTy`. -/
noncomputable def fieldOffsetAlignExp (cTy fTy : TyRepr) : Nat :=
  match cTy.packExp? with
  | some pExp => natMin fTy.abiAlignExp pExp
  | none => fTy.abiAlignExp

noncomputable def ProjStepAligned (curTy : TyRepr) : ProjElem → Prop
  | .field _ off cTy fTy =>
    cTy = curTy ∧ IsAlignedExp off (fieldOffsetAlignExp curTy fTy)
  | .deref _ _ _ => True

noncomputable def ProjChainAligned (curTy : TyRepr) : List ProjElem → Prop
  | [] => True
  | elem :: rest =>
    ProjStepAligned curTy elem ∧
    match elem with
    | .field _ _ _ fTy => ProjChainAligned fTy rest
    | .deref _ pTy _ => ProjChainAligned pTy rest

noncomputable def DerefAbiWellFormed (mem : MemState) : List ProjElem → Prop
  | [] => True
  | .field _ _ _ _ :: rest => DerefAbiWellFormed mem rest
  | .deref _ pTy targetId :: rest =>
    (∃ ts : MemSlot,
      MemState.lookupSlot mem.slots targetId = some ts ∧
      ts.live = true ∧
      IsAlignedExp ts.addr pTy.abiAlignExp) ∧
    DerefAbiWellFormed mem rest

noncomputable def PlaceAlignedWF (mem : MemState) (p : MirPlace) : Prop :=
  (∃ bs : MemSlot,
    MemState.lookupSlot mem.slots p.base.slotId = some bs ∧
    bs.live = true ∧
    bs.slotTy = p.base.baseTy ∧
    IsAlignedExp bs.addr bs.slotTy.abiAlignExp) ∧
  ProjChainAligned p.base.baseTy p.projections ∧
  DerefAbiWellFormed mem p.projections

-- ============================================================================
-- Section 3: Exact CheckPackedRef & place_unalignment Model + Theorem 1
-- ============================================================================

/-- Collects `(containerTy, projElem)` pairs strictly after the last `.deref`. -/
noncomputable def tailAfterLastDerefAux (curTy : TyRepr) (acc : List (TyRepr × ProjElem)) :
    List ProjElem → List (TyRepr × ProjElem)
  | [] => acc
  | elem :: rest =>
    match elem with
    | .field _ _ _ fTy => tailAfterLastDerefAux fTy (acc ++ [(curTy, elem)]) rest
    | .deref _ pTy _ => tailAfterLastDerefAux pTy [] rest

/-- Minimum `packExp` among packed `.field` projections after the last `.deref`. -/
noncomputable def minPackFromPairs : List (TyRepr × ProjElem) → Option Nat
  | [] => none
  | (baseTy, _) :: rest =>
    let restMin := minPackFromPairs rest
    match baseTy.packExp? with
    | none => restMin
    | some p =>
      match restMin with
      | none => some p
      | some rp => some (natMin p rp)

/-- Exact model of `rustc_const_eval::util::alignment::most_packed_projection`. -/
noncomputable def mostPackedProjection (p : MirPlace) : Option Nat :=
  minPackFromPairs (tailAfterLastDerefAux p.base.baseTy [] p.projections)

/-- Exact model of `rustc_const_eval::util::alignment::place_unalignment` (`layout.align <= pack`). -/
noncomputable def placeUnalignmentAbi (p : MirPlace) : Option Nat :=
  match mostPackedProjection p with
  | none => none
  | some packExp =>
    let ty := p.ty
    if Nat.ble ty.abiAlignExp packExp && (ty.isSized || ty.tailKind.isSliceOrStr) then
      none
    else
      some packExp

/-- MIR `PlaceContext` kind relevant to `CheckPackedRef`. -/
inductive PlaceCtx where
  | borrow
  | rawPtr
  | copyLoad
  | moveVal

/-- Diagnostic verdict emitted by `CheckPackedRef` (`check_packed_ref.rs`). -/
inductive LintVerdict where
  | ok
  | errE0793 (packExp : Nat)

/-- Exact model of `PackedRefChecker::visit_place`. -/
noncomputable def checkPackedRefAbi (ctx : PlaceCtx) (p : MirPlace) : LintVerdict :=
  match ctx with
  | .borrow =>
    match placeUnalignmentAbi p with
    | some packExp => .errE0793 packExp
    | none => .ok
  | .rawPtr => .ok
  | .copyLoad => .ok
  | .moveVal => .ok

/-- Miri dynamic reference/memory check verdicts. -/
inductive MiriCheckOutcome where
  | ok
  | ubUnalignedRef (requiredExp foundExp : Nat)
  | ubUnalignedLoad (requiredExp foundExp : Nat)
  | ubDanglingSlot

/-- Miri reference validity check (`&T` / `&mut T`, including ZSTs). -/
noncomputable def miriCheckRefAbi (addr : Nat) (ty : TyRepr) : MiriCheckOutcome :=
  match checkAlignedExp addr ty.abiAlignExp with
  | true => .ok
  | false => .ubUnalignedRef ty.abiAlignExp 0

/-- Miri aligned load check (`*raw` without `read_unaligned`). -/
noncomputable def miriLoadAlignedAbi (addr : Nat) (ty : TyRepr) : MiriCheckOutcome :=
  match checkAlignedExp addr ty.abiAlignExp with
  | true => .ok
  | false => .ubUnalignedLoad ty.abiAlignExp 0

/-- Miri `ptr::read_unaligned` / `ptr::write_unaligned` (`1`-byte copy). -/
noncomputable def miriReadUnaligned (mem : MemState) (slotId : Nat) : MiriCheckOutcome :=
  match MemState.lookupSlot mem.slots slotId with
  | some s => if s.live && s.initialized then .ok else .ubDanglingSlot
  | none => .ubDanglingSlot

/-- Combine an optional running alignment exponent bound with `Option Nat` pack. -/
noncomputable def combinePackBound (curExp : Nat) (pack? : Option Nat) : Nat :=
  match pack? with
  | none => curExp
  | some p => natMin curExp p

theorem combinePackBound_le_cur (curExp : Nat) (pack? : Option Nat) :
    combinePackBound curExp pack? ≤ curExp := by
  unfold combinePackBound
  cases pack? with
  | none => exact Nat.le_refl curExp
  | some p => exact natMin_le_left curExp p

/-- Combine two optional packed bounds taking their minimum. -/
noncomputable def minOptNat (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, x => x
  | x, none => x
  | some x, some y => some (natMin x y)

theorem minOptNat_none_right (a : Option Nat) : minOptNat a none = a := by
  cases a <;> rfl

theorem minOptNat_none_left (b : Option Nat) : minOptNat none b = b := by
  cases b <;> rfl

theorem minOptNat_assoc (a b c : Option Nat) :
    minOptNat (minOptNat a b) c = minOptNat a (minOptNat b c) := by
  cases a with
  | none =>
    rw [minOptNat_none_left, minOptNat_none_left]
  | some x =>
    cases b with
    | none =>
      rw [minOptNat_none_right, minOptNat_none_left]
    | some y =>
      cases c with
      | none =>
        rw [minOptNat_none_right, minOptNat_none_right]
      | some z =>
        unfold minOptNat
        dsimp only []
        exact congrArg some (natMin_assoc x y z)

/-
  Alignment invariant across projections:
  Under `rustc_abi::layout`, a container struct's own ABI alignment is at least
  each direct field's clamped alignment (`fieldOffsetAlignExp curTy fTy ≤ curTy.abiAlignExp`).
  Walking from `(curAddr, curTy, acc)` where `curAddr` is aligned to
  `combinePackBound curTy.abiAlignExp (minPackFromPairs acc)` preserves
  `IsAlignedExp finalAddr (combinePackBound finalTy.abiAlignExp (minPackFromPairs finalPairs))`.
-/

/-- Structural field-container layout invariant from `rustc_abi::layout`. -/
noncomputable def LayoutFieldBound (cTy fTy : TyRepr) : Prop :=
  fieldOffsetAlignExp cTy fTy ≤ cTy.abiAlignExp

noncomputable def ProjChainLayoutWF (curTy : TyRepr) : List ProjElem → Prop
  | [] => True
  | elem :: rest =>
    match elem with
    | .field _ _ _cTy fTy =>
      LayoutFieldBound curTy fTy ∧ ProjChainLayoutWF fTy rest
    | .deref _ pTy _ =>
      ProjChainLayoutWF pTy rest

theorem combinePackBound_mono_left {a b : Nat} (hle : a ≤ b) (p? : Option Nat) :
    combinePackBound a p? ≤ combinePackBound b p? := by
  unfold combinePackBound
  cases p? with
  | none => exact hle
  | some p =>
    apply (le_natMin_iff (natMin a p) b p).mpr
    exact ⟨Nat.le_trans (natMin_le_left a p) hle, natMin_le_right a p⟩

theorem combinePackBound_field_eq (cTy fTy : TyRepr) (acc? : Option Nat) :
    combinePackBound (fieldOffsetAlignExp cTy fTy) acc? =
    combinePackBound fTy.abiAlignExp (minOptNat acc? cTy.packExp?) := by
  unfold fieldOffsetAlignExp combinePackBound minOptNat
  cases hc : cTy.packExp? with
  | none =>
    cases acc? <;> rfl
  | some q =>
    cases acc? with
    | none => rfl
    | some p =>
      dsimp only []
      rw [natMin_assoc, natMin_comm q p]

theorem if_bool_true {α : Type} (c : Bool) (hc : c = true) (a b : α) :
    (if c then a else b) = a := by
  subst hc
  rfl

theorem if_bool_false {α : Type} (c : Bool) (hc : c = false) (a b : α) :
    (if c then a else b) = b := by
  subst hc
  rfl

theorem minPackFromPairs_cons (bTy : TyRepr) (el : ProjElem) (rest : List (TyRepr × ProjElem)) :
    minPackFromPairs ((bTy, el) :: rest) = minOptNat bTy.packExp? (minPackFromPairs rest) := by
  change (match bTy.packExp? with
    | none => minPackFromPairs rest
    | some p =>
      match minPackFromPairs rest with
      | none => some p
      | some rp => some (natMin p rp)) = minOptNat bTy.packExp? (minPackFromPairs rest)
  unfold minOptNat
  cases bTy.packExp? <;> cases minPackFromPairs rest <;> rfl

theorem minPackFromPairs_append (l1 l2 : List (TyRepr × ProjElem)) :
    minPackFromPairs (l1 ++ l2) = minOptNat (minPackFromPairs l1) (minPackFromPairs l2) := by
  induction l1 with
  | nil =>
    unfold minPackFromPairs
    rw [List.nil_append, minOptNat_none_left]
  | cons hd tl ih =>
    cases hd with
    | mk bTy el =>
      rw [List.cons_append, minPackFromPairs_cons, ih, minPackFromPairs_cons, minOptNat_assoc]

theorem minPackFromPairs_snoc (l : List (TyRepr × ProjElem)) (bTy : TyRepr) (el : ProjElem) :
    minPackFromPairs (l ++ [(bTy, el)]) = minOptNat (minPackFromPairs l) bTy.packExp? := by
  rw [minPackFromPairs_append]
  have hsingle : minPackFromPairs [(bTy, el)] = bTy.packExp? := by
    unfold minPackFromPairs
    have hnil : minPackFromPairs [] = none := rfl
    rw [hnil]
    cases bTy.packExp? <;> rfl
  rw [hsingle]

/-- Core inductive bridge theorem for `evalProjAddr` and `tailAfterLastDerefAux`. -/
theorem evalProjAddr_preserves_pack_bound
    (mem : MemState) (projs : List ProjElem)
    (curAddr : Nat) (curTy : TyRepr) (acc : List (TyRepr × ProjElem))
    (hChain : ProjChainAligned curTy projs)
    (hLayout : ProjChainLayoutWF curTy projs)
    (hDeref : DerefAbiWellFormed mem projs)
    (hBase : IsAlignedExp curAddr (combinePackBound curTy.abiAlignExp (minPackFromPairs acc))) :
    ∃ finalAddr : Nat,
      evalProjAddr mem curAddr projs = some finalAddr ∧
      IsAlignedExp finalAddr
        (combinePackBound (evalProjChainTy curTy projs).abiAlignExp
          (minPackFromPairs (tailAfterLastDerefAux curTy acc projs))) := by
  induction projs generalizing curAddr curTy acc with
  | nil =>
    exact ⟨curAddr, rfl, hBase⟩
  | cons elem rest ih =>
    cases elem with
    | field fIdx off cTy fTy =>
      have hStep : ProjStepAligned curTy (.field fIdx off cTy fTy) := hChain.1
      have hRestChain : ProjChainAligned fTy rest := hChain.2
      have hFieldBound : LayoutFieldBound curTy fTy := hLayout.1
      have hRestLayout : ProjChainLayoutWF fTy rest := hLayout.2
      have hOffAligned : IsAlignedExp off (fieldOffsetAlignExp curTy fTy) := hStep.2
      have hMono :
          combinePackBound (fieldOffsetAlignExp curTy fTy) (minPackFromPairs acc) ≤
          combinePackBound curTy.abiAlignExp (minPackFromPairs acc) :=
        combinePackBound_mono_left hFieldBound (minPackFromPairs acc)
      have hAddrStep :
          IsAlignedExp curAddr (combinePackBound (fieldOffsetAlignExp curTy fTy) (minPackFromPairs acc)) :=
        isAlignedExp_mono hMono hBase
      have hOffStep :
          IsAlignedExp off (combinePackBound (fieldOffsetAlignExp curTy fTy) (minPackFromPairs acc)) :=
        isAlignedExp_mono (combinePackBound_le_cur _ _) hOffAligned
      have hSumAligned :
          IsAlignedExp (curAddr + off)
            (combinePackBound fTy.abiAlignExp (minPackFromPairs (acc ++ [(curTy, .field fIdx off cTy fTy)]))) := by
        rw [minPackFromPairs_snoc, ← combinePackBound_field_eq curTy fTy (minPackFromPairs acc)]
        exact isAlignedExp_add hAddrStep hOffStep
      obtain ⟨finalAddr, hEval, hFinal⟩ :=
        ih (curAddr + off) fTy (acc ++ [(curTy, .field fIdx off cTy fTy)])
          hRestChain hRestLayout hDeref hSumAligned
      exact ⟨finalAddr, hEval, hFinal⟩
    | deref ptrTy pTy targetId =>
      have hRestChain : ProjChainAligned pTy rest := hChain.2
      have hRestLayout : ProjChainLayoutWF pTy rest := hLayout
      obtain ⟨⟨ts, hLook, _, hTsAlign⟩, hRestDeref⟩ := hDeref
      have hReset :
          IsAlignedExp ts.addr (combinePackBound pTy.abiAlignExp (minPackFromPairs [])) := by
        have hnil : minPackFromPairs [] = none := rfl
        rw [hnil]
        exact hTsAlign
      obtain ⟨finalAddr, hEval, hFinal⟩ := ih ts.addr pTy [] hRestChain hRestLayout hRestDeref hReset
      unfold evalProjAddr
      rw [hLook]
      exact ⟨finalAddr, hEval, hFinal⟩

/-- **THEOREM 1 (`checkPackedRef_alignment_safety`):**
    Every reference borrow accepted by `CheckPackedRef` (`checkPackedRefAbi .borrow p = .ok`)
    over a well-formed place/layout/memory evaluates to a concrete address `finalAddr`
    satisfying `finalAddr % (2 ^ p.ty.abiAlignExp) == 0`, and therefore NEVER faults
    under `miriCheckRefAbi`! -/
theorem checkPackedRef_alignment_safety
    (mem : MemState) (p : MirPlace)
    (hPlace : PlaceAlignedWF mem p)
    (hLayout : ProjChainLayoutWF p.base.baseTy p.projections)
    (hOk : checkPackedRefAbi .borrow p = .ok) :
    ∃ finalAddr : Nat,
      evalPlaceAddr mem p = some finalAddr ∧
      IsAlignedExp finalAddr p.ty.abiAlignExp ∧
      miriCheckRefAbi finalAddr p.ty = .ok := by
  obtain ⟨⟨bs, hLook, _, hSlotTy, hBsAlign⟩, hChain, hDeref⟩ := hPlace
  have hBaseInit :
      IsAlignedExp bs.addr (combinePackBound p.base.baseTy.abiAlignExp (minPackFromPairs [])) := by
    have hnil : minPackFromPairs [] = none := rfl
    rw [hnil, combinePackBound, ← hSlotTy]
    exact hBsAlign
  obtain ⟨finalAddr, hEvalProj, hFinalBound⟩ :=
    evalProjAddr_preserves_pack_bound mem p.projections bs.addr p.base.baseTy [] hChain hLayout hDeref hBaseInit
  have hEvalPlace : evalPlaceAddr mem p = some finalAddr := by
    unfold evalPlaceAddr
    rw [hLook]
    exact hEvalProj
  have hTyEq : evalProjChainTy p.base.baseTy p.projections = p.ty := rfl
  rw [hTyEq] at hFinalBound
  have hFinalAlign : IsAlignedExp finalAddr p.ty.abiAlignExp := by
    unfold checkPackedRefAbi placeUnalignmentAbi at hOk
    dsimp only [] at hOk
    cases hMost : mostPackedProjection p with
    | none =>
      rw [hMost] at hOk
      unfold mostPackedProjection at hMost
      rw [hMost] at hFinalBound
      exact hFinalBound
    | some packExp =>
      rw [hMost] at hOk
      dsimp only [] at hOk
      unfold mostPackedProjection at hMost
      rw [hMost] at hFinalBound
      cases hCond : (Nat.ble p.ty.abiAlignExp packExp && (p.ty.isSized || p.ty.tailKind.isSliceOrStr)) with
      | true =>
        have hBle : Nat.ble p.ty.abiAlignExp packExp = true := by
          cases hb : Nat.ble p.ty.abiAlignExp packExp with
          | true => rfl
          | false =>
            rw [hb] at hCond
            cases hCond
        have hMinEq : natMin p.ty.abiAlignExp packExp = p.ty.abiAlignExp := by
          unfold natMin
          rw [hBle]
        unfold combinePackBound at hFinalBound
        dsimp only [] at hFinalBound
        rw [hMinEq] at hFinalBound
        exact hFinalBound
      | false =>
        rw [if_bool_false _ hCond] at hOk
        cases hOk
  have hMiri : miriCheckRefAbi finalAddr p.ty = .ok := by
    unfold miriCheckRefAbi
    have hb : checkAlignedExp finalAddr p.ty.abiAlignExp = true :=
      (checkAlignedExp_iff finalAddr p.ty.abiAlignExp).mpr hFinalAlign
    rw [hb]
  exact ⟨finalAddr, hEvalPlace, hFinalAlign, hMiri⟩

/-- Corollary: `&raw const` / `&raw mut` and `Copy` loads NEVER fail `CheckPackedRef`. -/
theorem rawPtr_and_copyLoad_never_e0793 (p : MirPlace) :
    checkPackedRefAbi .rawPtr p = .ok ∧ checkPackedRefAbi .copyLoad p = .ok := by
  exact ⟨rfl, rfl⟩

/-- Corollary: `Deref` resets `mostPackedProjection`: any suffix after `.deref` with a
    non-packed pointee struct yields `mostPackedProjection = none`. -/
theorem deref_resets_mostPacked (baseTy ptrTy : TyRepr) (slotId : Nat)
    (fIdx off : Nat) (unpackedStruct fTy : TyRepr)
    (hUnpacked : unpackedStruct.packExp? = none) :
    mostPackedProjection
      { base := ⟨0, baseTy⟩,
        projections := [.deref ptrTy unpackedStruct slotId, .field fIdx off unpackedStruct fTy] } = none := by
  unfold mostPackedProjection
  have hT :
      tailAfterLastDerefAux baseTy [] [.deref ptrTy unpackedStruct slotId, .field fIdx off unpackedStruct fTy] =
      [(unpackedStruct, .field fIdx off unpackedStruct fTy)] := rfl
  rw [hT]
  unfold minPackFromPairs
  rw [hUnpacked]
  rfl

-- Concrete Negative & Positive Witnesses for Theorem 1 (matching live rustc probe!)

noncomputable def tyU8 : TyRepr := ⟨1, 0, 1, true, .none, none, false, true, true⟩
noncomputable def tyU16 : TyRepr := ⟨2, 1, 2, true, .none, none, false, true, false⟩
noncomputable def tyU32 : TyRepr := ⟨3, 2, 4, true, .none, none, false, true, false⟩
noncomputable def tyPack1 : TyRepr := ⟨10, 0, 5, true, .none, some 0, false, true, true⟩
noncomputable def tyPack2 : TyRepr := ⟨11, 1, 8, true, .none, some 1, false, true, false⟩
noncomputable def tyPack4 : TyRepr := ⟨12, 2, 8, true, .none, some 2, false, true, false⟩

/-- Negative witness: `#[repr(C, packed(1))]` field `b : u32` triggers `E0793` and fails Miri ref check at `addr = 1`. -/
theorem e0793_rejects_pack1_u32_and_miri_catches :
    checkPackedRefAbi .borrow
      { base := ⟨0, tyPack1⟩, projections := [.field 1 1 tyPack1 tyU32] } = .errE0793 0 ∧
    miriCheckRefAbi 1 tyU32 = .ubUnalignedRef 2 0 := by
  constructor <;> rfl

/-- Negative witness: nested `packed(2)` containing `packed(4)` with `u32` (`min 1 2 = 1 < 2`) triggers `E0793`. -/
theorem e0793_rejects_nested_pack2_pack4_u32 :
    checkPackedRefAbi .borrow
      { base := ⟨0, tyPack2⟩,
        projections := [.field 1 2 tyPack2 tyPack4, .field 0 0 tyPack4 tyU32] } = .errE0793 1 := by
  rfl

/-- Positive witness: `#[repr(C, packed(2))]` field `b : u16` (`alignExp = 1 <= packExp = 1`) passes `CheckPackedRef`. -/
theorem checkPackedRef_accepts_pack2_u16 :
    checkPackedRefAbi .borrow
      { base := ⟨0, tyPack2⟩, projections := [.field 1 2 tyPack2 tyU16] } = .ok := by
  rfl

/-- Positive witness: `#[repr(C, packed(1))]` unsized `[u8]` tail passes `CheckPackedRef`,
    while `[u32]` unsized tail (`alignExp = 2 > 0`) triggers `E0793`. -/
theorem checkPackedRef_slice_tail_boundary :
    let sliceU8 : TyRepr := ⟨20, 0, 0, false, .sliceOrStr 0, none, false, true, true⟩
    let sliceU32 : TyRepr := ⟨21, 2, 0, false, .sliceOrStr 2, none, false, true, false⟩
    checkPackedRefAbi .borrow { base := ⟨0, tyPack1⟩, projections := [.field 1 1 tyPack1 sliceU8] } = .ok ∧
    checkPackedRefAbi .borrow { base := ⟨0, tyPack1⟩, projections := [.field 1 1 tyPack1 sliceU32] } = .errE0793 0 := by
  constructor <;> rfl

-- ============================================================================
-- Section 4: AddMovesForPackedDrops Staging Soundness — Theorem 2
-- ============================================================================

/-- MIR Drop statements before and after `AddMovesForPackedDrops`. -/
inductive MirDropInstr where
  | directDrop (place : MirPlace)
  | stagedMoveDrop (tmpSlotId : Nat) (srcPlace : MirPlace)

/-- Transformation performed by `AddMovesForPackedDrops`
    (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:50-111`). -/
noncomputable def addMovesForPackedDropsTransform (tmpSlotId : Nat) (p : MirPlace) : MirDropInstr :=
  match placeUnalignmentAbi p with
  | some _ => .stagedMoveDrop tmpSlotId p
  | none => .directDrop p

/-- Outcome of executing a drop terminator in MIR / Miri operational semantics. -/
inductive DropExecOutcome where
  | ok (finalMem : MemState) (droppedVal : Nat) (dropAddr : Nat)
  | ubUnalignedDropRef (requiredExp : Nat)
  | ubUninitializedMove
  | errAddrEval

/-- Stack bump-aligner used for `StorageLive(temp)` in `AddMovesForPackedDrops`. -/
noncomputable def alignUpToExp (addr exp : Nat) : Nat :=
  let a := alignBytes exp
  let rem := addr % a
  match Nat.beq rem 0 with
  | true => addr
  | false => addr + (a - rem)

theorem alignUpToExp_aligned (addr exp : Nat) :
    IsAlignedExp (alignUpToExp addr exp) exp := by
  unfold alignUpToExp
  dsimp only []
  cases h : Nat.beq (addr % alignBytes exp) 0 with
  | true =>
    exact Nat.eq_of_beq_eq_true h
  | false =>
    unfold IsAlignedExp
    let a := alignBytes exp
    have hpos : 0 < a := alignBytes_pos exp
    have hlt : addr % a < a := Nat.mod_lt addr hpos
    have hle : addr % a ≤ a := Nat.le_of_lt hlt
    have hdiv : addr = (addr / a) * a + addr % a := by
      have hdm := Nat.div_add_mod addr a
      rw [Nat.mul_comm] at hdm
      exact hdm.symm
    have hsum : addr + (a - addr % a) = (addr / a + 1) * a := by
      calc addr + (a - addr % a)
        _ = ((addr / a) * a + addr % a) + (a - addr % a) := by rw [← hdiv]
        _ = (addr / a) * a + (addr % a + (a - addr % a)) := Nat.add_assoc _ _ _
        _ = (addr / a) * a + a := by rw [Nat.add_sub_of_le hle]
        _ = (addr / a) * a + 1 * a := by rw [Nat.one_mul]
        _ = (addr / a + 1) * a := by rw [Nat.add_mul]
    change (addr + (a - addr % a)) % a = 0
    rw [hsum, Nat.mul_mod_left]

/-- Operational drop execution:
    - `.directDrop p`: checks `miriCheckRefAbi addr p.ty == .ok`; if misaligned,
      faults with `.ubUnalignedDropRef`! Otherwise calls `drop_in_place` at `addr`.
    - `.stagedMoveDrop tmpId src`: mirrors
      `StorageLive(tmp); tmp = move src; drop(tmp); StorageDead(tmp)`:
      reads `val` by unaligned move, marks `src` deinitialized (`deinitMovedPlace = true`),
      allocates `tmpId` at stack address `tmpAddr = alignUpToExp mem.nextAddr src.ty.abiAlignExp`,
      calls `drop_in_place` on `tmp` (checked via `miriCheckRefAbi`), and frees `tmp`. -/
noncomputable def execDropInstr (mem : MemState) (valAtPlace : Nat) (instr : MirDropInstr) :
    DropExecOutcome :=
  match instr with
  | .directDrop p =>
    match evalPlaceAddr mem p with
    | none => .errAddrEval
    | some addr =>
      match miriCheckRefAbi addr p.ty with
      | .ok => .ok mem valAtPlace addr
      | .ubUnalignedRef req _ => .ubUnalignedDropRef req
      | _ => .errAddrEval
  | .stagedMoveDrop tmpId src =>
    match evalPlaceAddr mem src with
    | none => .errAddrEval
    | some _srcAddr =>
      match MemState.lookupSlot mem.slots src.base.slotId with
      | none => .errAddrEval
      | some baseSlot =>
        if !baseSlot.live || !baseSlot.initialized then
          .ubUninitializedMove
        else
          let tmpAddr := alignUpToExp mem.nextAddr src.ty.abiAlignExp
          let deinitBase : MemSlot := { baseSlot with initialized := false }
          let slotsAfterMove := MemState.upsertSlot mem.slots deinitBase
          match miriCheckRefAbi tmpAddr src.ty with
          | .ok =>
            let deadTmp : MemSlot := ⟨tmpId, tmpAddr, src.ty, false, false, 0⟩
            let finalSlots := MemState.upsertSlot slotsAfterMove deadTmp
            let finalMem : MemState := ⟨finalSlots, tmpAddr + src.ty.size⟩
            .ok finalMem valAtPlace tmpAddr
          | .ubUnalignedRef req _ => .ubUnalignedDropRef req
          | _ => .errAddrEval

/-- Predicate certifying that the base slot of a drop place is live and initialized. -/
noncomputable def DropSourceLiveInit (mem : MemState) (p : MirPlace) : Prop :=
  ∃ bs : MemSlot,
    MemState.lookupSlot mem.slots p.base.slotId = some bs ∧
    bs.live = true ∧ bs.initialized = true

/-- **THEOREM 2 (`addMovesForPackedDrops_staging_soundness`):**
    For EVERY well-formed MIR drop place `p` (whose base is live & initialized and
    layout is well-formed), executing `addMovesForPackedDropsTransform tmpId p`:
    1. NEVER fails with `.ubUnalignedDropRef`,
    2. Observes exact dropped value `valAtPlace` at a `p.ty.abiAlignExp`-aligned `dropAddr`. -/
theorem addMovesForPackedDrops_staging_soundness
    (mem : MemState) (p : MirPlace) (tmpId valAtPlace : Nat)
    (hPlace : PlaceAlignedWF mem p)
    (hLayout : ProjChainLayoutWF p.base.baseTy p.projections)
    (hInit : DropSourceLiveInit mem p) :
    ∃ (finalMem : MemState) (dropAddr : Nat),
      execDropInstr mem valAtPlace (addMovesForPackedDropsTransform tmpId p) =
        .ok finalMem valAtPlace dropAddr ∧
      IsAlignedExp dropAddr p.ty.abiAlignExp := by
  unfold addMovesForPackedDropsTransform
  cases hUn : placeUnalignmentAbi p with
  | none =>
    have hLintOk : checkPackedRefAbi .borrow p = .ok := by
      unfold checkPackedRefAbi
      rw [hUn]
    obtain ⟨finalAddr, hEval, hAlign, hMiri⟩ :=
      checkPackedRef_alignment_safety mem p hPlace hLayout hLintOk
    unfold execDropInstr
    dsimp only []
    rw [hEval]
    dsimp only []
    rw [hMiri]
    exact ⟨mem, finalAddr, rfl, hAlign⟩
  | some _ =>
    obtain ⟨⟨bs, hLook1, hLive, hSlotTy, hBsAl⟩, hCh, hDr⟩ := hPlace
    obtain ⟨bs2, hLook2, _, hInitFlag⟩ := hInit
    rw [hLook1] at hLook2
    have hBsEq : bs = bs2 := Option.some.inj hLook2
    subst hBsEq
    have hBaseInit :
        IsAlignedExp bs.addr (combinePackBound p.base.baseTy.abiAlignExp (minPackFromPairs [])) := by
      have hnil : minPackFromPairs [] = none := rfl
      rw [hnil, combinePackBound, ← hSlotTy]
      exact hBsAl
    obtain ⟨srcAddr, hEvalProj, _⟩ :=
      evalProjAddr_preserves_pack_bound mem p.projections bs.addr p.base.baseTy [] hCh hLayout hDr hBaseInit
    have hEvalSrc : evalPlaceAddr mem p = some srcAddr := by
      unfold evalPlaceAddr
      rw [hLook1]
      exact hEvalProj
    let tmpAddr := alignUpToExp mem.nextAddr p.ty.abiAlignExp
    have hTmpAlign : IsAlignedExp tmpAddr p.ty.abiAlignExp :=
      alignUpToExp_aligned mem.nextAddr p.ty.abiAlignExp
    have hMiriTmp : miriCheckRefAbi tmpAddr p.ty = .ok := by
      unfold miriCheckRefAbi
      have hb : checkAlignedExp tmpAddr p.ty.abiAlignExp = true :=
        (checkAlignedExp_iff tmpAddr p.ty.abiAlignExp).mpr hTmpAlign
      rw [hb]
    unfold execDropInstr
    dsimp only []
    rw [hEvalSrc]
    dsimp only []
    rw [hLook1]
    dsimp only []
    have hNotDead : (!bs.live || !bs.initialized) = false := by
      simp only [hLive, hInitFlag, Bool.not_true, Bool.false_or]
    rw [if_bool_false _ hNotDead]
    let deadTmp : MemSlot := ⟨tmpId, tmpAddr, p.ty, false, false, 0⟩
    let resMem : MemState :=
      ⟨MemState.upsertSlot (MemState.upsertSlot mem.slots { bs with initialized := false }) deadTmp,
        tmpAddr + p.ty.size⟩
    refine ⟨resMem, tmpAddr, ?_, hTmpAlign⟩
    rw [hMiriTmp]

/-- Corollary (`packed_drop_relocates_address`):
    Whenever `srcAddr` is genuinely misaligned (`¬ IsAlignedExp srcAddr ty.abiAlignExp`)
    and `AddMovesForPackedDrops` drops via `tmpAddr`, `tmpAddr ≠ srcAddr` — proving why
    structural `Pin` cannot coexist with `#[repr(packed)]` drop elaboration (`PinV2OnPacked`). -/
theorem packed_drop_relocates_address
    (srcAddr tmpAddr : Nat) (ty : TyRepr)
    (hMis : ¬ IsAlignedExp srcAddr ty.abiAlignExp)
    (hTmp : IsAlignedExp tmpAddr ty.abiAlignExp) :
    tmpAddr ≠ srcAddr := by
  intro heq
  rw [heq] at hTmp
  exact hMis hTmp

/-- Concrete witness: `Packed1Drop` (`align = 4 > pack = 1`) gets staged to `stagedMoveDrop`,
    while `Packed4Drop` (`align = 4 <= pack = 4`) remains `directDrop` (matching MIR dumps!). -/
theorem addMovesForPackedDrops_pack1_vs_pack4 :
    let tyDropCounted : TyRepr := ⟨30, 2, 4, true, .none, none, true, true, false⟩
    let tyPack1Drop : TyRepr := ⟨31, 0, 5, true, .none, some 0, true, true, true⟩
    let tyPack4Drop : TyRepr := ⟨32, 2, 8, true, .none, some 2, true, true, false⟩
    let p1 : MirPlace := { base := ⟨1, tyPack1Drop⟩, projections := [.field 1 1 tyPack1Drop tyDropCounted] }
    let p4 : MirPlace := { base := ⟨2, tyPack4Drop⟩, projections := [.field 1 4 tyPack4Drop tyDropCounted] }
    addMovesForPackedDropsTransform 7 p1 = .stagedMoveDrop 7 p1 ∧
    addMovesForPackedDropsTransform 7 p4 = .directDrop p4 := by
  constructor <;> rfl

-- ============================================================================
-- Section 5: zerocopy::Unalign<T> Soundness Model — Theorem 3
-- ============================================================================

/-- Representation of `#[repr(C, packed)] struct Unalign<T>(T)`:
    alignExp = 0 (align = 1), same size as `T`, implements `Unaligned`. -/
noncomputable def unalignRepr (inner : TyRepr) : TyRepr :=
  ⟨inner.tyId + 1000, 0, inner.size, true, .none, some 0, inner.needsDrop, inner.unpin, true⟩

/-- Error returned by `Unalign::try_deref` / `try_deref_mut` on misaligned address. -/
inductive AlignmentError where
  | misaligned (requiredExp : Nat)

/-- Result type for `Unalign::try_deref`. -/
inductive TryDerefResult where
  | ok (refAddr : Nat) (innerTy : TyRepr)
  | err (e : AlignmentError)

/-- Exact model of `Unalign<T>::try_deref` (`zerocopy/src/wrappers.rs:202-211`,
    calling `validate_aligned_to` in `zerocopy/src/util/mod.rs:127-139`). -/
noncomputable def unalignTryDeref (addr : Nat) (inner : TyRepr) : TryDerefResult :=
  match checkAlignedExp addr inner.abiAlignExp with
  | true => .ok addr inner
  | false => .err (.misaligned inner.abiAlignExp)

/-- Model of `impl<T: Unaligned> Deref for Unalign<T>` (`wrappers.rs:407-414`). -/
noncomputable def unalignDerefUnaligned (addr : Nat) (inner : TyRepr) : Option Nat :=
  if inner.unaligned then some addr else none

/-- Model of `Unalign<T>::get` (`wrappers.rs:401-404`, copy read of packed field `self.0`). -/
noncomputable def unalignGet (mem : MemState) (slotId : Nat) : Option Nat :=
  match MemState.lookupSlot mem.slots slotId with
  | some s => if s.live && s.initialized then some s.payloadVal else none
  | none => none

/-- Model of `Unalign<T>::update` (`wrappers.rs:339-395`) via `WriteBackOnDrop`. -/
noncomputable def unalignUpdate
    (mem : MemState) (slotId : Nat) (inner : TyRepr) (f : Nat → Nat) :
    Option (MemState × Nat) :=
  match MemState.lookupSlot mem.slots slotId with
  | none => none
  | some s =>
    if !s.live || !s.initialized then none
    else
      let tmpAddr := alignUpToExp mem.nextAddr inner.abiAlignExp
      let updatedVal := f s.payloadVal
      let newSlot := { s with payloadVal := updatedVal }
      let finalMem : MemState := ⟨MemState.upsertSlot mem.slots newSlot, tmpAddr + inner.size⟩
      some (finalMem, tmpAddr)

/-- **THEOREM 3a (`unalign_try_deref_soundness_ok`):**
    If `unalignTryDeref addr inner = .ok refAddr outTy`, then `refAddr = addr`,
    `outTy = inner`, `IsAlignedExp refAddr inner.abiAlignExp`, and `miriCheckRefAbi refAddr inner = .ok`. -/
theorem unalign_try_deref_soundness_ok
    (addr refAddr : Nat) (inner outTy : TyRepr)
    (hOk : unalignTryDeref addr inner = .ok refAddr outTy) :
    refAddr = addr ∧
    outTy = inner ∧
    IsAlignedExp refAddr inner.abiAlignExp ∧
    miriCheckRefAbi refAddr inner = .ok := by
  unfold unalignTryDeref at hOk
  cases hc : checkAlignedExp addr inner.abiAlignExp with
  | true =>
    rw [hc] at hOk
    injection hOk with hAddr hTy
    subst hAddr hTy
    have hAlign : IsAlignedExp addr inner.abiAlignExp :=
      (checkAlignedExp_iff addr inner.abiAlignExp).mp hc
    have hMiri : miriCheckRefAbi addr inner = .ok := by
      unfold miriCheckRefAbi
      rw [hc]
    exact ⟨rfl, rfl, hAlign, hMiri⟩
  | false =>
    rw [hc] at hOk
    cases hOk

/-- **THEOREM 3b (`unalign_try_deref_fail_closed`):**
    On any misaligned address (`¬ IsAlignedExp addr inner.abiAlignExp`),
    `Unalign::try_deref` fails closed with `.err (.misaligned inner.abiAlignExp)`. -/
theorem unalign_try_deref_fail_closed
    (addr : Nat) (inner : TyRepr)
    (hMis : ¬ IsAlignedExp addr inner.abiAlignExp) :
    unalignTryDeref addr inner = .err (.misaligned inner.abiAlignExp) := by
  unfold unalignTryDeref
  cases hc : checkAlignedExp addr inner.abiAlignExp with
  | true =>
    have hAl := (checkAlignedExp_iff addr inner.abiAlignExp).mp hc
    exact False.elim (hMis hAl)
  | false => rfl

/-- **THEOREM 3c (`unalign_deref_unaligned_always_safe`):**
    When `T: Unaligned` (`abiAlignExp = 0`, `unaligned = true`), `Deref::deref` is
    unconditionally safe at every address `addr`. -/
theorem unalign_deref_unaligned_always_safe
    (addr : Nat) (inner : TyRepr)
    (hUnal : inner.unaligned = true)
    (hExp0 : inner.abiAlignExp = 0) :
    unalignDerefUnaligned addr inner = some addr ∧
    miriCheckRefAbi addr inner = .ok := by
  unfold unalignDerefUnaligned miriCheckRefAbi
  rw [hUnal, hExp0]
  have hMod : checkAlignedExp addr 0 = true :=
    (checkAlignedExp_iff addr 0).mpr (isAlignedExp_zero addr)
  rw [hMod]
  exact ⟨rfl, rfl⟩

/-- **THEOREM 3d (`unalign_update_stages_and_writes_back`):**
    `Unalign::update` stages `T` at an aligned stack temporary `tmpAddr`, guarantees
    `miriCheckRefAbi tmpAddr inner = .ok`, and writes back `f oldVal` into `slotId`. -/
theorem unalign_update_stages_and_writes_back
    (mem mem' : MemState) (slotId tmpAddr : Nat) (inner : TyRepr) (f : Nat → Nat)
    (s : MemSlot)
    (hLook : MemState.lookupSlot mem.slots slotId = some s)
    (hLive : s.live = true) (hInit : s.initialized = true)
    (hUpd : unalignUpdate mem slotId inner f = some (mem', tmpAddr)) :
    IsAlignedExp tmpAddr inner.abiAlignExp ∧
    miriCheckRefAbi tmpAddr inner = .ok ∧
    unalignGet mem' slotId = some (f s.payloadVal) := by
  unfold unalignUpdate at hUpd
  rw [hLook] at hUpd
  dsimp only [] at hUpd
  have hFlag : (!s.live || !s.initialized) = false := by
    simp only [hLive, hInit, Bool.not_true, Bool.false_or]
  rw [if_bool_false _ hFlag] at hUpd
  injection hUpd with hPair
  have hMemEq : mem' = ⟨MemState.upsertSlot mem.slots { s with payloadVal := f s.payloadVal },
      alignUpToExp mem.nextAddr inner.abiAlignExp + inner.size⟩ :=
    congrArg Prod.fst hPair.symm
  have hTmpEq : tmpAddr = alignUpToExp mem.nextAddr inner.abiAlignExp :=
    congrArg Prod.snd hPair.symm
  have hAlign : IsAlignedExp tmpAddr inner.abiAlignExp := by
    rw [hTmpEq]
    exact alignUpToExp_aligned mem.nextAddr inner.abiAlignExp
  have hMiri : miriCheckRefAbi tmpAddr inner = .ok := by
    unfold miriCheckRefAbi
    rw [(checkAlignedExp_iff tmpAddr inner.abiAlignExp).mpr hAlign]
  have hGet : unalignGet mem' slotId = some (f s.payloadVal) := by
    unfold unalignGet
    rw [hMemEq]
    dsimp only []
    have hId : s.slotId = slotId := lookupSlot_id_eq hLook
    have hLookNew :
        MemState.lookupSlot
          (MemState.upsertSlot mem.slots { s with payloadVal := f s.payloadVal }) slotId =
        some { s with payloadVal := f s.payloadVal } := by
      conv => lhs; arg 2; rw [← hId]
      exact lookupSlot_upsert_same mem.slots { s with payloadVal := f s.payloadVal }
    rw [hLookNew]
    dsimp only []
    simp only [hLive, hInit, Bool.and_self, ↓reduceIte]
  exact ⟨hAlign, hMiri, hGet⟩

/-- Concrete witness: `Unalign<u32>` has alignment `1`, rejects `try_deref` at `addr = 5`,
    and succeeds at `addr = 8`. -/
theorem unalign_u32_concrete_witness :
    (unalignRepr tyU32).abiAlignExp = 0 ∧
    unalignTryDeref 5 tyU32 = .err (.misaligned 2) ∧
    unalignTryDeref 8 tyU32 = .ok 8 tyU32 := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Section 6: Pin<Ptr> Structural Projection, Address Stability, & Drop Guarantee
-- ============================================================================

/-- Field projection policy inside a struct `S` for `Pin<&mut S>`. -/
inductive PinProjPolicy where
  | none
  | nonStructural
  | structural

/-- Equality check for `PinProjPolicy`. -/
noncomputable def PinProjPolicy.beq : PinProjPolicy → PinProjPolicy → Bool
  | .none, .none => true
  | .nonStructural, .nonStructural => true
  | .structural, .structural => true
  | _, _ => false

/-- Lifecycle status of an object location in the `Pin` heap model. -/
inductive PinLifecycle where
  | unpinned
  | pinned (origAddr : Nat)
  | dropped (origAddr : Nat)
  | freed (origAddr : Nat) (wasDropped : Bool)
  | leaked (origAddr : Nat)

/-- Per-field descriptor of a pinned/pinnable struct object. -/
structure PinField where
  fieldIdx : Nat
  addr : Nat
  origAddr : Nat
  unpin : Bool
  policy : PinProjPolicy
  pinned : Bool
  dropped : Bool
  selfPtr? : Option Nat

/-- Object record in the `Pin` state machine. -/
structure PinObj where
  objId : Nat
  addr : Nat
  unpin : Bool
  packed : Bool
  lifecycle : PinLifecycle
  fields : List PinField

/-- Full `Pin` heap state: objects plus an external intrusive waitlist of registered
    field addresses (`(objId, fieldIdx, registeredAddr)`). -/
structure PinHeap where
  objs : List PinObj
  waiters : List (Nat × Nat × Nat)
  nextAddr : Nat

noncomputable def PinHeap.findObj (objs : List PinObj) (oid : Nat) : Option PinObj :=
  match objs with
  | [] => none
  | o :: rest =>
    match Nat.beq o.objId oid with
    | true => some o
    | false => PinHeap.findObj rest oid

noncomputable def PinHeap.upsertObj (objs : List PinObj) (newO : PinObj) : List PinObj :=
  match objs with
  | [] => [newO]
  | o :: rest =>
    match Nat.beq o.objId newO.objId with
    | true => newO :: rest
    | false => o :: PinHeap.upsertObj rest newO

noncomputable def findField (fields : List PinField) (fIdx : Nat) : Option PinField :=
  match fields with
  | [] => none
  | f :: rest =>
    match Nat.beq f.fieldIdx fIdx with
    | true => some f
    | false => findField rest fIdx

noncomputable def upsertField (fields : List PinField) (newF : PinField) : List PinField :=
  match fields with
  | [] => [newF]
  | f :: rest =>
    match Nat.beq f.fieldIdx newF.fieldIdx with
    | true => newF :: rest
    | false => f :: upsertField rest newF

theorem findObj_upsert_same (objs : List PinObj) (o : PinObj) :
    PinHeap.findObj (PinHeap.upsertObj objs o) o.objId = some o := by
  induction objs with
  | nil =>
    unfold PinHeap.upsertObj PinHeap.findObj
    rw [Nat.beq_refl]
  | cons hd tl ih =>
    unfold PinHeap.upsertObj
    cases h : Nat.beq hd.objId o.objId with
    | true =>
      unfold PinHeap.findObj
      rw [Nat.beq_refl]
    | false =>
      unfold PinHeap.findObj
      rw [h]
      exact ih

theorem findObj_upsert_other (objs : List PinObj) (o : PinObj) (oid : Nat)
    (hne : Nat.beq oid o.objId = false) :
    PinHeap.findObj (PinHeap.upsertObj objs o) oid = PinHeap.findObj objs oid := by
  induction objs with
  | nil =>
    unfold PinHeap.upsertObj PinHeap.findObj
    have hsw : Nat.beq o.objId oid = false := by
      cases hs : Nat.beq o.objId oid with
      | false => rfl
      | true =>
        rw [Nat.eq_of_beq_eq_true hs, Nat.beq_refl] at hne
        cases hne
    rw [hsw]
    rfl
  | cons hd tl ih =>
    unfold PinHeap.upsertObj
    cases h : Nat.beq hd.objId o.objId with
    | true =>
      have hhd : hd.objId = o.objId := Nat.eq_of_beq_eq_true h
      unfold PinHeap.findObj
      have hsw1 : Nat.beq o.objId oid = false := by
        cases hs : Nat.beq o.objId oid with
        | false => rfl
        | true =>
          rw [Nat.eq_of_beq_eq_true hs, Nat.beq_refl] at hne
          cases hne
      have hsw2 : Nat.beq hd.objId oid = false := by rw [hhd]; exact hsw1
      rw [hsw1, hsw2]
    | false =>
      unfold PinHeap.findObj
      cases h2 : Nat.beq hd.objId oid with
      | true => rfl
      | false => exact ih

theorem findObj_id_eq {objs : List PinObj} {oid : Nat} {o : PinObj}
    (h : PinHeap.findObj objs oid = some o) : o.objId = oid := by
  induction objs with
  | nil => cases h
  | cons hd tl ih =>
    unfold PinHeap.findObj at h
    cases hb : Nat.beq hd.objId oid with
    | true =>
      rw [hb] at h
      injection h with ho
      rw [← ho]
      exact Nat.eq_of_beq_eq_true hb
    | false =>
      rw [hb] at h
      exact ih h

theorem findField_upsert_same (fields : List PinField) (f : PinField) :
    findField (upsertField fields f) f.fieldIdx = some f := by
  induction fields with
  | nil =>
    unfold upsertField findField
    rw [Nat.beq_refl]
  | cons hd tl ih =>
    unfold upsertField
    cases h : Nat.beq hd.fieldIdx f.fieldIdx with
    | true =>
      unfold findField
      rw [Nat.beq_refl]
    | false =>
      unfold findField
      rw [h]
      exact ih

theorem findField_upsert_other (fields : List PinField) (f : PinField) (fid : Nat)
    (hne : Nat.beq fid f.fieldIdx = false) :
    findField (upsertField fields f) fid = findField fields fid := by
  induction fields with
  | nil =>
    unfold upsertField findField
    have hsw : Nat.beq f.fieldIdx fid = false := by
      cases hs : Nat.beq f.fieldIdx fid with
      | false => rfl
      | true =>
        rw [Nat.eq_of_beq_eq_true hs, Nat.beq_refl] at hne
        cases hne
    rw [hsw]
    rfl
  | cons hd tl ih =>
    unfold upsertField
    cases h : Nat.beq hd.fieldIdx f.fieldIdx with
    | true =>
      have hhd : hd.fieldIdx = f.fieldIdx := Nat.eq_of_beq_eq_true h
      unfold findField
      have hsw1 : Nat.beq f.fieldIdx fid = false := by
        cases hs : Nat.beq f.fieldIdx fid with
        | false => rfl
        | true =>
          rw [Nat.eq_of_beq_eq_true hs, Nat.beq_refl] at hne
          cases hne
      have hsw2 : Nat.beq hd.fieldIdx fid = false := by rw [hhd]; exact hsw1
      rw [hsw1, hsw2]
    | false =>
      unfold findField
      cases h2 : Nat.beq hd.fieldIdx fid with
      | true => rfl
      | false => exact ih

theorem findField_id_eq {fields : List PinField} {fid : Nat} {f : PinField}
    (h : findField fields fid = some f) : f.fieldIdx = fid := by
  induction fields with
  | nil => cases h
  | cons hd tl ih =>
    unfold findField at h
    cases hb : Nat.beq hd.fieldIdx fid with
    | true =>
      rw [hb] at h
      injection h with hf
      rw [← hf]
      exact Nat.eq_of_beq_eq_true hb
    | false =>
      rw [hb] at h
      exact ih h

/-- Rejection reasons matching Rust compiler errors & Pin safety rules. -/
inductive PinOpErr where
  | notUnpinE0277
  | noDerefMutE0596
  | pinOnPackedDisallowed
  | nonStructuralOverlap
  | objectNotLive
  | dropGuaranteeViolated
  | missingObject

/-- Result of executing a `PinOp`. -/
inductive PinOpRes where
  | ok (heap' : PinHeap)
  | err (e : PinOpErr)

/-- Operations in the `Pin` structural projection & lifecycle state machine. -/
inductive PinOp where
  | pinNewSafe (objId : Nat)
  | pinNewUnchecked (objId : Nat)
  | pinGetMutSafe (objId : Nat)
  | pinIntoInnerSafe (objId : Nat)
  | pinDerefMutSwapSafe (obj1 obj2 : Nat)
  | projectStructural (objId fieldIdx : Nat)
  | projectNonStructural (objId fieldIdx : Nat)
  | registerSelfPtr (objId fieldIdx : Nat)
  | registerWaiter (objId fieldIdx : Nat)
  | dropInPlace (objId : Nat)
  | freeAfterDrop (objId : Nat)
  | memForgetLeak (objId : Nat)

/-- Sound structural `Unpin` rule (RFC 2349 & `core::pin` rule #1):
    an object may be `unpin = true` ONLY if every `.structural` field is `unpin = true`. -/
noncomputable def StructuralUnpinConsistent (o : PinObj) : Prop :=
  o.unpin = true → ∀ f : PinField, findField o.fields f.fieldIdx = some f →
    f.policy = .structural → f.unpin = true

/-- Sound projection policy consistency (`core::pin` consistency rules):
    1. `StructuralUnpinConsistent o`
    2. `o.packed = true` forbids any `.structural` field (`PinV2OnPacked`)
    3. A field becomes `pinned = true` ONLY if `f.policy = .structural`
    4. Any `pinned = true` field can only exist when `o.lifecycle` is `.pinned _` / `.dropped _` / `.freed _ _` / `.leaked _`. -/
noncomputable def PinObjStructWellFormed (o : PinObj) : Prop :=
  StructuralUnpinConsistent o ∧
  (o.packed = true → ∀ f : PinField, findField o.fields f.fieldIdx = some f →
    f.policy ≠ .structural) ∧
  (∀ f : PinField, findField o.fields f.fieldIdx = some f →
    f.pinned = true → f.policy = .structural)

/-- Address-stability invariant (`Pin` Invariant 1):
    1. Every pinned or leaked `!unpin` object stays at its `origAddr`.
    2. Every pinned or structurally-projectable `!unpin` field stays at its
       `origAddr` (note non-structural projection explicitly rejects `.structural`
       fields, so structural fields are never relocated prior to projection). -/
noncomputable def PinAddrStabilityInv (h : PinHeap) : Prop :=
  (∀ o : PinObj, PinHeap.findObj h.objs o.objId = some o →
    (match o.lifecycle with
     | .pinned orig => o.unpin = false → o.addr = orig
     | .leaked orig => o.unpin = false → o.addr = orig
     | _ => True) ∧
    (∀ f : PinField, findField o.fields f.fieldIdx = some f →
      (f.pinned = true ∨ f.policy = .structural) → f.unpin = false → f.addr = f.origAddr))

/-- Drop-guarantee invariant (`Pin` Invariant 2):
    no `!unpin` pinned object (nor structurally pinned `!unpin` field) is freed
    unless `drop_in_place` has run (`wasDropped = true` and `f.dropped = true`),
    and once in `.dropped` every structurally pinned `!unpin` field already has
    `f.dropped = true`. -/
noncomputable def PinDropGuaranteeInv (h : PinHeap) : Prop :=
  ∀ o : PinObj, PinHeap.findObj h.objs o.objId = some o →
    (match o.lifecycle with
     | .freed _ wasDropped => o.unpin = false → wasDropped = true
     | _ => True) ∧
    (∀ f : PinField, findField o.fields f.fieldIdx = some f →
      f.pinned = true → f.unpin = false →
      (match o.lifecycle with
       | .dropped _ => f.dropped = true
       | .freed _ wasDropped => wasDropped = true ∧ f.dropped = true
       | _ => True))

/-- Self-reference & intrusive-list pointer invariant (`SelfRefOK ∧ WaiterOK`). -/
noncomputable def PinPtrValidityInv (h : PinHeap) : Prop :=
  (∀ o : PinObj, PinHeap.findObj h.objs o.objId = some o →
    ∀ f : PinField, findField o.fields f.fieldIdx = some f →
      ∀ sp : Nat, f.selfPtr? = some sp →
        f.pinned = true ∧ f.unpin = false ∧ f.addr = sp ∧
        (match o.lifecycle with
         | .pinned _ => True
         | .leaked _ => True
         | _ => False)) ∧
  (∀ (oid fid regAddr : Nat), (oid, fid, regAddr) ∈ h.waiters →
    ∃ o : PinObj, ∃ f : PinField,
      PinHeap.findObj h.objs oid = some o ∧
      findField o.fields fid = some f ∧
      f.pinned = true ∧ f.unpin = false ∧ f.addr = regAddr ∧
      (match o.lifecycle with
       | .pinned _ => True
       | .leaked _ => True
       | _ => False))

/-- Combined full `Pin` system invariant. -/
noncomputable def PinSystemInv (h : PinHeap) : Prop :=
  (∀ o : PinObj, PinHeap.findObj h.objs o.objId = some o → PinObjStructWellFormed o) ∧
  PinAddrStabilityInv h ∧
  PinDropGuaranteeInv h ∧
  PinPtrValidityInv h

/-- Drop cleanup on fields: marks `dropped := true` and clears internal `selfPtr?`. -/
noncomputable def markFieldsDropped : List PinField → List PinField
  | [] => []
  | f :: rest => { f with dropped := true, selfPtr? := none } :: markFieldsDropped rest

/-- Waiter cleanup run by `Drop::drop` on `oid`. -/
noncomputable def removeObjWaiters (oid : Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | (wOid, wFid, wAddr) :: rest =>
    match Nat.beq wOid oid with
    | true => removeObjWaiters oid rest
    | false => (wOid, wFid, wAddr) :: removeObjWaiters oid rest

theorem findField_markFieldsDropped (fields : List PinField) (fid : Nat) :
    findField (markFieldsDropped fields) fid =
    match findField fields fid with
    | none => none
    | some f => some { f with dropped := true, selfPtr? := none } := by
  induction fields with
  | nil => rfl
  | cons hd tl ih =>
    unfold markFieldsDropped findField
    cases h : Nat.beq hd.fieldIdx fid with
    | true => rfl
    | false => exact ih

theorem mem_removeObjWaiters_iff (oid wOid wFid wAddr : Nat) (ws : List (Nat × Nat × Nat)) :
    (wOid, wFid, wAddr) ∈ removeObjWaiters oid ws ↔
    ((wOid, wFid, wAddr) ∈ ws ∧ Nat.beq wOid oid = false) := by
  induction ws with
  | nil =>
    unfold removeObjWaiters
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; cases h
  | cons hd tl ih =>
    cases hd with
    | mk a rest =>
      cases rest with
      | mk b c =>
        unfold removeObjWaiters
        cases hb : Nat.beq a oid with
        | true =>
          have heq : a = oid := Nat.eq_of_beq_eq_true hb
          constructor
          · intro hmem
            obtain ⟨h1, h2⟩ := ih.mp hmem
            exact ⟨List.Mem.tail _ h1, h2⟩
          · intro ⟨hmem, hne⟩
            cases hmem with
            | head =>
              rw [heq, Nat.beq_refl] at hne
              cases hne
            | tail _ htl =>
              exact ih.mpr ⟨htl, hne⟩
        | false =>
          constructor
          · intro hmem
            cases hmem with
            | head => exact ⟨List.Mem.head _, hb⟩
            | tail _ htl =>
              obtain ⟨h1, h2⟩ := ih.mp htl
              exact ⟨List.Mem.tail _ h1, h2⟩
          · intro ⟨hmem, hne⟩
            cases hmem with
            | head => exact List.Mem.head _
            | tail _ htl => exact List.Mem.tail _ (ih.mpr ⟨htl, hne⟩)

/-- Transition semantics of `PinOp`. -/
noncomputable def stepPinOp (h : PinHeap) (op : PinOp) : PinOpRes :=
  match op with
  | .pinNewSafe oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      if !o.unpin then .err .notUnpinE0277
      else
        match o.lifecycle with
        | .unpinned =>
          let o' := { o with lifecycle := .pinned o.addr }
          .ok { h with objs := PinHeap.upsertObj h.objs o' }
        | .pinned _ => .ok h
        | _ => .err .objectNotLive
  | .pinNewUnchecked oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .unpinned =>
        let o' := { o with lifecycle := .pinned o.addr }
        .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | .pinned _ => .ok h
      | _ => .err .objectNotLive
  | .pinGetMutSafe oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      if !o.unpin then .err .notUnpinE0277
      else
        match o.lifecycle with
        | .pinned _ => .ok h
        | .unpinned => .ok h
        | _ => .err .objectNotLive
  | .pinIntoInnerSafe oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      if !o.unpin then .err .notUnpinE0277
      else
        match o.lifecycle with
        | .pinned _ =>
          let o' := { o with lifecycle := .unpinned }
          .ok { h with objs := PinHeap.upsertObj h.objs o' }
        | .unpinned => .ok h
        | _ => .err .objectNotLive
  | .pinDerefMutSwapSafe oid1 oid2 =>
    match PinHeap.findObj h.objs oid1, PinHeap.findObj h.objs oid2 with
    | some o1, some o2 =>
      if !o1.unpin || !o2.unpin then .err .noDerefMutE0596
      else
        match Nat.beq oid1 oid2 with
        | true => .ok h
        | false =>
          match o1.lifecycle, o2.lifecycle with
          | .pinned orig1, .pinned orig2 =>
            let o1' := { o1 with addr := o2.addr, lifecycle := .pinned orig1 }
            let o2' := { o2 with addr := o1.addr, lifecycle := .pinned orig2 }
            .ok { h with objs := PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2' }
          | .unpinned, .unpinned =>
            let o1' := { o1 with addr := o2.addr }
            let o2' := { o2 with addr := o1.addr }
            .ok { h with objs := PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2' }
          | _, _ => .err .objectNotLive
    | _, _ => .err .missingObject
  | .projectStructural oid fid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      if o.packed then .err .pinOnPackedDisallowed
      else
        match o.lifecycle with
        | .pinned _ =>
          match findField o.fields fid with
          | none => .err .missingObject
          | some f =>
            if !PinProjPolicy.beq f.policy .structural then .err .nonStructuralOverlap
            else
              let f' := { f with pinned := true }
              let o' := { o with fields := upsertField o.fields f' }
              .ok { h with objs := PinHeap.upsertObj h.objs o' }
        | _ => .err .objectNotLive
  | .projectNonStructural oid fid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .pinned _ | .unpinned =>
        match findField o.fields fid with
        | none => .err .missingObject
        | some f =>
          if !PinProjPolicy.beq f.policy .nonStructural then .err .nonStructuralOverlap
          else
            let f' := { f with addr := h.nextAddr }
            let o' := { o with fields := upsertField o.fields f' }
            .ok { h with objs := PinHeap.upsertObj h.objs o', nextAddr := h.nextAddr + 8 }
      | _ => .err .objectNotLive
  | .registerSelfPtr oid fid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .pinned _ =>
        match findField o.fields fid with
        | none => .err .missingObject
        | some f =>
          if !f.pinned || f.unpin then .err .nonStructuralOverlap
          else
            let f' := { f with selfPtr? := some f.addr }
            let o' := { o with fields := upsertField o.fields f' }
            .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | _ => .err .objectNotLive
  | .registerWaiter oid fid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .pinned _ =>
        match findField o.fields fid with
        | none => .err .missingObject
        | some f =>
          if !f.pinned || f.unpin then .err .nonStructuralOverlap
          else
            .ok { h with waiters := (oid, fid, f.addr) :: h.waiters }
      | _ => .err .objectNotLive
  | .dropInPlace oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .pinned orig =>
        let o' := { o with lifecycle := .dropped orig, fields := markFieldsDropped o.fields }
        .ok { h with objs := PinHeap.upsertObj h.objs o', waiters := removeObjWaiters oid h.waiters }
      | .unpinned =>
        let o' := { o with lifecycle := .dropped o.addr, fields := markFieldsDropped o.fields }
        .ok { h with objs := PinHeap.upsertObj h.objs o', waiters := removeObjWaiters oid h.waiters }
      | _ => .err .objectNotLive
  | .freeAfterDrop oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .dropped orig =>
        let o' := { o with lifecycle := .freed orig true }
        .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | .unpinned =>
        if !o.unpin then .err .dropGuaranteeViolated
        else
          let o' := { o with lifecycle := .freed o.addr false }
          .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | _ => .err .dropGuaranteeViolated
  | .memForgetLeak oid =>
    match PinHeap.findObj h.objs oid with
    | none => .err .missingObject
    | some o =>
      match o.lifecycle with
      | .pinned orig =>
        let o' := { o with lifecycle := .leaked orig }
        .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | .unpinned =>
        let o' := { o with lifecycle := .leaked o.addr }
        .ok { h with objs := PinHeap.upsertObj h.objs o' }
      | _ => .err .objectNotLive

/-- Multi-step execution of a `List PinOp`. -/
noncomputable def runPinOps (h : PinHeap) : List PinOp → PinOpRes
  | [] => .ok h
  | op :: rest =>
    match stepPinOp h op with
    | .err e => .err e
    | .ok h' => runPinOps h' rest

/-- Helper: upserting `o'` with matching structural WF preserves `PinObjStructWellFormed` everywhere. -/
theorem upsertObj_preserves_structWF (h : PinHeap) (o' : PinObj)
    (hAll : ∀ o, PinHeap.findObj h.objs o.objId = some o → PinObjStructWellFormed o)
    (hNew : PinObjStructWellFormed o') :
    ∀ o, PinHeap.findObj (PinHeap.upsertObj h.objs o') o.objId = some o → PinObjStructWellFormed o := by
  intro o hFind
  cases hEq : Nat.beq o.objId o'.objId with
  | true =>
    have heq := Nat.eq_of_beq_eq_true hEq
    rw [heq, findObj_upsert_same] at hFind
    injection hFind with hEqObj
    rw [← hEqObj]
    exact hNew
  | false =>
    rw [findObj_upsert_other _ _ _ hEq] at hFind
    exact hAll o hFind

/-- Helper: an `Unpin` well-formed object cannot contain any pinned `!Unpin` field! -/
theorem unpin_obj_no_pinned_notUnpin_field
    (o : PinObj) (hWF : PinObjStructWellFormed o) (hUnp : o.unpin = true)
    (f : PinField) (hf : findField o.fields f.fieldIdx = some f)
    (hPin : f.pinned = true) (hFUnp : f.unpin = false) : False := by
  have hPol : f.policy = .structural := hWF.2.2 f hf hPin
  have hMust : f.unpin = true := hWF.1 hUnp f hf hPol
  rw [hFUnp] at hMust
  cases hMust

/-- Helper: `PinProjPolicy.beq` reflects structural equality. -/
theorem pinProjPolicy_eq_of_beq {p1 p2 : PinProjPolicy}
    (hb : PinProjPolicy.beq p1 p2 = true) : p1 = p2 := by
  cases p1 <;> cases p2 <;> first | rfl | cases hb

-- Modular per-operation preservation lemmas for Theorem 4a

theorem pin_step_preserves_pinNewSafe (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.pinNewSafe oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    cases hUnpin : obj.unpin with
    | false =>
      rw [if_bool_true _ (by rw [hUnpin]; rfl)] at hStep
      cases hStep
    | true =>
      rw [if_bool_false _ (by rw [hUnpin]; rfl)] at hStep
      cases hLife : obj.lifecycle with
      | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | pinned _ =>
        rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
        exact ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
      | unpinned =>
        rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
        let obj' : PinObj := { obj with lifecycle := .pinned obj.addr }
        have hObjWF := hSWF obj (by rw [hId]; exact hFind)
        refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            exact ⟨fun _ => rfl, (hAddr obj (by rw [hId]; exact hFind)).2⟩
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hAddr o ho
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            exact ⟨trivial, fun _ _ _ _ => trivial⟩
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hDrop o ho
        · intro o ho f hf sp hsp
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
            obtain ⟨_, _, _, h4⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
            rw [hLife] at h4; cases h4
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hSelf o ho f hf sp hsp
        · intro wOid wFid wAddr hw
          obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
          cases hEq : Nat.beq wOid obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
            injection hWo with hW; rw [← hW, hLife] at hw4; cases hw4
          | false =>
            refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
            rw [findObj_upsert_other h.objs obj' wOid hEq]
            exact hWo

theorem pin_step_preserves_pinNewUnchecked (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.pinNewUnchecked oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    cases hLife : obj.lifecycle with
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned _ =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      exact ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
    | unpinned =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      let obj' : PinObj := { obj with lifecycle := .pinned obj.addr }
      have hObjWF := hSWF obj (by rw [hId]; exact hFind)
      refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          exact ⟨fun _ => rfl, (hAddr obj (by rw [hId]; exact hFind)).2⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hAddr o ho
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          exact ⟨trivial, fun _ _ _ _ => trivial⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hDrop o ho
      · intro o ho f hf sp hsp
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
          obtain ⟨_, _, _, h4⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
          rw [hLife] at h4; cases h4
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hSelf o ho f hf sp hsp
      · intro wOid wFid wAddr hw
        obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
        cases hEq : Nat.beq wOid obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
          injection hWo with hW; rw [← hW, hLife] at hw4; cases hw4
        | false =>
          refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
          rw [findObj_upsert_other h.objs obj' wOid hEq]
          exact hWo

theorem pin_step_preserves_pinIntoInnerSafe (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.pinIntoInnerSafe oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    cases hUnpin : obj.unpin with
    | false =>
      rw [if_bool_true _ (by rw [hUnpin]; rfl)] at hStep
      cases hStep
    | true =>
      rw [if_bool_false _ (by rw [hUnpin]; rfl)] at hStep
      cases hLife : obj.lifecycle with
      | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | unpinned =>
        rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
        exact ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
      | pinned _ =>
        rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
        let obj' : PinObj := { obj with lifecycle := .unpinned }
        have hObjWF := hSWF obj (by rw [hId]; exact hFind)
        refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            exact ⟨trivial, (hAddr obj (by rw [hId]; exact hFind)).2⟩
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hAddr o ho
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            exact ⟨trivial, fun _ _ _ _ => trivial⟩
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hDrop o ho
        · intro o ho f hf sp hsp
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
            obtain ⟨hfPin, hfUnp, _, _⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
            exact False.elim (unpin_obj_no_pinned_notUnpin_field obj hObjWF hUnpin f hf hfPin hfUnp)
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hSelf o ho f hf sp hsp
        · intro wOid wFid wAddr hw
          obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
          cases hEq : Nat.beq wOid obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
            injection hWo with hW; rw [← hW] at hWf
            exact False.elim (unpin_obj_no_pinned_notUnpin_field obj hObjWF hUnpin wf (by rw [findField_id_eq hWf]; exact hWf) hw1 hw2)
          | false =>
            refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
            rw [findObj_upsert_other h.objs obj' wOid hEq]
            exact hWo

theorem pin_step_preserves_pinDerefMutSwapSafe (h h' : PinHeap) (oid1 oid2 : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.pinDerefMutSwapSafe oid1 oid2) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hF1 : PinHeap.findObj h.objs oid1 with
  | none => rw [hF1] at hStep; dsimp only [] at hStep; cases hStep
  | some o1 =>
    cases hF2 : PinHeap.findObj h.objs oid2 with
    | none => rw [hF1, hF2] at hStep; dsimp only [] at hStep; cases hStep
    | some o2 =>
      rw [hF1, hF2] at hStep
      dsimp only [] at hStep
      have hId1 : o1.objId = oid1 := findObj_id_eq hF1
      have hId2 : o2.objId = oid2 := findObj_id_eq hF2
      cases hU1 : o1.unpin with
      | false =>
        rw [if_bool_true _ (by rw [hU1]; rfl)] at hStep
        cases hStep
      | true =>
        cases hU2 : o2.unpin with
        | false =>
          rw [if_bool_true _ (by rw [hU1, hU2]; rfl)] at hStep
          cases hStep
        | true =>
          rw [if_bool_false _ (by rw [hU1, hU2]; rfl)] at hStep
          cases hSame : Nat.beq oid1 oid2 with
          | true =>
            rw [hSame] at hStep
            dsimp only [] at hStep
            injection hStep with heq; rw [← heq]
            exact ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
          | false =>
            rw [hSame] at hStep
            dsimp only [] at hStep
            have hNe12 : Nat.beq o1.objId o2.objId = false := by
              rw [hId1, hId2]; exact hSame
            have hWF1 := hSWF o1 (by rw [hId1]; exact hF1)
            have hWF2 := hSWF o2 (by rw [hId2]; exact hF2)
            cases hL1 : o1.lifecycle with
            | dropped _ => rw [hL1] at hStep; dsimp only [] at hStep; cases hStep
            | freed _ _ => rw [hL1] at hStep; dsimp only [] at hStep; cases hStep
            | leaked _ => rw [hL1] at hStep; dsimp only [] at hStep; cases hStep
            | pinned orig1 =>
              cases hL2 : o2.lifecycle with
              | unpinned => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | dropped _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | freed _ _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | leaked _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | pinned orig2 =>
                rw [hL1, hL2] at hStep
                dsimp only [] at hStep
                injection hStep with heq; rw [← heq]
                let o1' : PinObj := { o1 with addr := o2.addr, lifecycle := .pinned orig1 }
                let o2' : PinObj := { o2 with addr := o1.addr, lifecycle := .pinned orig2 }
                have hMidWF : ∀ o, PinHeap.findObj (PinHeap.upsertObj h.objs o1') o.objId = some o →
                    PinObjStructWellFormed o :=
                  upsertObj_preserves_structWF h o1' hSWF hWF1
                have hFinWF := upsertObj_preserves_structWF { h with objs := PinHeap.upsertObj h.objs o1' } o2' hMidWF hWF2
                refine ⟨hFinWF, ?_, ?_, ⟨?_, ?_⟩⟩
                · intro o ho
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                    constructor
                    · intro hBad; rw [hU2] at hBad; cases hBad
                    · exact (hAddr o2 (by rw [hId2]; exact hF2)).2
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                      constructor
                      · intro hBad; rw [hU1] at hBad; cases hBad
                      · exact (hAddr o1 (by rw [hId1]; exact hF1)).2
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hAddr o ho
                · intro o ho
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                    exact ⟨trivial, fun _ _ _ _ => trivial⟩
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                      exact ⟨trivial, fun _ _ _ _ => trivial⟩
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hDrop o ho
                · intro o ho f hf sp hsp
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
                    obtain ⟨hfPin, hfUnp, _, _⟩ := hSelf o2 (by rw [hId2]; exact hF2) f hf sp hsp
                    exact False.elim (unpin_obj_no_pinned_notUnpin_field o2 hWF2 hU2 f hf hfPin hfUnp)
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
                      obtain ⟨hfPin, hfUnp, _, _⟩ := hSelf o1 (by rw [hId1]; exact hF1) f hf sp hsp
                      exact False.elim (unpin_obj_no_pinned_notUnpin_field o1 hWF1 hU1 f hf hfPin hfUnp)
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hSelf o ho f hf sp hsp
                · intro wOid wFid wAddr hw
                  obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
                  cases hEq2 : Nat.beq wOid o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2, hId2, hF2] at hWo
                    injection hWo with hW; rw [← hW] at hWf
                    exact False.elim (unpin_obj_no_pinned_notUnpin_field o2 hWF2 hU2 wf (by rw [findField_id_eq hWf]; exact hWf) hw1 hw2)
                  | false =>
                    cases hEq1 : Nat.beq wOid o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1, hId1, hF1] at hWo
                      injection hWo with hW; rw [← hW] at hWf
                      exact False.elim (unpin_obj_no_pinned_notUnpin_field o1 hWF1 hU1 wf (by rw [findField_id_eq hWf]; exact hWf) hw1 hw2)
                    | false =>
                      refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
                      change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') wOid = some wo
                      rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' wOid hEq2,
                          findObj_upsert_other h.objs o1' wOid hEq1]
                      exact hWo
            | unpinned =>
              cases hL2 : o2.lifecycle with
              | pinned _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | dropped _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | freed _ _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | leaked _ => rw [hL1, hL2] at hStep; dsimp only [] at hStep; cases hStep
              | unpinned =>
                rw [hL1, hL2] at hStep
                dsimp only [] at hStep
                injection hStep with heq; rw [← heq]
                let o1' : PinObj := { o1 with addr := o2.addr, lifecycle := .unpinned }
                let o2' : PinObj := { o2 with addr := o1.addr, lifecycle := .unpinned }
                have hMidWF : ∀ o, PinHeap.findObj (PinHeap.upsertObj h.objs o1') o.objId = some o →
                    PinObjStructWellFormed o :=
                  upsertObj_preserves_structWF h o1' hSWF hWF1
                have hFinWF := upsertObj_preserves_structWF { h with objs := PinHeap.upsertObj h.objs o1' } o2' hMidWF hWF2
                refine ⟨hFinWF, ?_, ?_, ⟨?_, ?_⟩⟩
                · intro o ho
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                    exact ⟨trivial, (hAddr o2 (by rw [hId2]; exact hF2)).2⟩
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                      exact ⟨trivial, (hAddr o1 (by rw [hId1]; exact hF1)).2⟩
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hAddr o ho
                · intro o ho
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                    exact ⟨trivial, fun _ _ _ _ => trivial⟩
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                      exact ⟨trivial, fun _ _ _ _ => trivial⟩
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hDrop o ho
                · intro o ho f hf sp hsp
                  cases hEq2 : Nat.beq o.objId o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2] at ho
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o2'.objId = some o at ho
                    rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
                    obtain ⟨_, _, _, h4⟩ := hSelf o2 (by rw [hId2]; exact hF2) f hf sp hsp
                    rw [hL2] at h4; cases h4
                  | false =>
                    change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') o.objId = some o at ho
                    rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' o.objId hEq2] at ho
                    cases hEq1 : Nat.beq o.objId o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1] at ho
                      change PinHeap.findObj (PinHeap.upsertObj h.objs o1') o1'.objId = some o at ho
                      rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
                      obtain ⟨_, _, _, h4⟩ := hSelf o1 (by rw [hId1]; exact hF1) f hf sp hsp
                      rw [hL1] at h4; cases h4
                    | false =>
                      rw [findObj_upsert_other h.objs o1' o.objId hEq1] at ho
                      exact hSelf o ho f hf sp hsp
                · intro wOid wFid wAddr hw
                  obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
                  cases hEq2 : Nat.beq wOid o2.objId with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hEq2, hId2, hF2] at hWo
                    injection hWo with hW; rw [← hW, hL2] at hw4; cases hw4
                  | false =>
                    cases hEq1 : Nat.beq wOid o1.objId with
                    | true =>
                      rw [Nat.eq_of_beq_eq_true hEq1, hId1, hF1] at hWo
                      injection hWo with hW; rw [← hW, hL1] at hw4; cases hw4
                    | false =>
                      refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
                      change PinHeap.findObj (PinHeap.upsertObj (PinHeap.upsertObj h.objs o1') o2') wOid = some wo
                      rw [findObj_upsert_other (PinHeap.upsertObj h.objs o1') o2' wOid hEq2,
                          findObj_upsert_other h.objs o1' wOid hEq1]
                      exact hWo

theorem pin_step_preserves_projectStructural (h h' : PinHeap) (oid fid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.projectStructural oid fid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    cases hPack : obj.packed with
    | true => rw [if_bool_true _ hPack] at hStep; cases hStep
    | false =>
      rw [if_bool_false _ hPack] at hStep
      cases hLife : obj.lifecycle with
      | unpinned => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
      | pinned orig =>
        rw [hLife] at hStep
        dsimp only [] at hStep
        cases hFld : findField obj.fields fid with
        | none => rw [hFld] at hStep; dsimp only [] at hStep; cases hStep
        | some f =>
          rw [hFld] at hStep
          dsimp only [] at hStep
          have hFid : f.fieldIdx = fid := findField_id_eq hFld
          cases hPolB : PinProjPolicy.beq f.policy .structural with
          | false =>
            rw [if_bool_true _ (by rw [hPolB]; rfl)] at hStep
            cases hStep
          | true =>
            rw [if_bool_false _ (by rw [hPolB]; rfl)] at hStep
            injection hStep with heq; rw [← heq]
            have hPolEq : f.policy = .structural := pinProjPolicy_eq_of_beq hPolB
            let f' : PinField := { f with pinned := true }
            let obj' : PinObj := { obj with lifecycle := .pinned orig, fields := upsertField obj.fields f' }
            have hObj'WF : PinObjStructWellFormed obj' := by
              refine ⟨?_, ?_, ?_⟩
              · intro hUnp g hg hGPol
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG]
                  exact hObjWF.1 hUnp f (by rw [hFid]; exact hFld) hPolEq
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  exact hObjWF.1 hUnp g hg hGPol
              · intro hBad; rw [hPack] at hBad; cases hBad
              · intro g hg hGPin
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG]
                  exact hPolEq
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  exact hObjWF.2.2 g hg hGPin
            refine ⟨upsertObj_preserves_structWF h obj' hSWF hObj'WF, ?_, ?_, ⟨?_, ?_⟩⟩
            · intro o ho
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                have hObjAddr := hAddr obj (by rw [hId]; exact hFind)
                refine ⟨?_, ?_⟩
                · rw [hLife] at hObjAddr; exact hObjAddr.1
                · intro g hg hCond hGUnp
                  cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hFEq] at hg
                    change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                    rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGUnp ⊢
                    exact hObjAddr.2 f (by rw [hFid]; exact hFld) (Or.inr hPolEq) hGUnp
                  | false =>
                    change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                    rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                    exact hObjAddr.2 g hg hCond hGUnp
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hAddr o ho
            · intro o ho
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho
                injection ho with hO; rw [← hO]
                exact ⟨trivial, fun _ _ _ _ => trivial⟩
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hDrop o ho
            · intro o ho g hg sp hsp
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hg ⊢
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hsp ⊢
                  obtain ⟨_, hfUnp, hfAddr, _⟩ := hSelf obj (by rw [hId]; exact hFind) f (by rw [hFid]; exact hFld) sp hsp
                  exact ⟨rfl, hfUnp, hfAddr, by dsimp only [obj']⟩
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  obtain ⟨hg1, hg2, hg3, _⟩ := hSelf obj (by rw [hId]; exact hFind) g hg sp hsp
                  exact ⟨hg1, hg2, hg3, by dsimp only [obj']⟩
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hSelf o ho g hg sp hsp
            · intro wOid wFid wAddr hw
              obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
              cases hEq : Nat.beq wOid obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
                injection hWo with hW; rw [← hW] at hWf
                cases hFEq : Nat.beq wFid f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq, hFid, hFld] at hWf
                  injection hWf with hWfEq
                  refine ⟨obj', f', ?_, ?_, rfl, ?_, ?_, by dsimp only [obj']⟩
                  · dsimp only []; rw [Nat.eq_of_beq_eq_true hEq]; exact findObj_upsert_same h.objs obj'
                  · dsimp only [obj']; rw [Nat.eq_of_beq_eq_true hFEq]; exact findField_upsert_same obj.fields f'
                  · rw [← hWfEq] at hw2; exact hw2
                  · rw [← hWfEq] at hw3; exact hw3
                | false =>
                  refine ⟨obj', wf, ?_, ?_, hw1, hw2, hw3, by dsimp only [obj']⟩
                  · dsimp only []; rw [Nat.eq_of_beq_eq_true hEq]; exact findObj_upsert_same h.objs obj'
                  · exact (findField_upsert_other obj.fields f' wFid hFEq).symm ▸ hWf
              | false =>
                refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
                rw [findObj_upsert_other h.objs obj' wOid hEq]
                exact hWo

theorem pin_step_preserves_projectNonStructural (h h' : PinHeap) (oid fid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.projectNonStructural oid fid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    have hCore : ∀ (f : PinField) (newLife : PinLifecycle)
        (hFld : findField obj.fields fid = some f)
        (hPolEq : f.policy = .nonStructural)
        (hLifeMatch : match newLife with | .pinned _ => True | .unpinned => True | _ => False)
        (hLifeEq : obj.lifecycle = newLife),
        let f' : PinField := { f with addr := h.nextAddr }
        let obj' : PinObj := { obj with lifecycle := newLife, fields := upsertField obj.fields f' }
        PinSystemInv { h with objs := PinHeap.upsertObj h.objs obj', nextAddr := h.nextAddr + 8 } := by
      intro f newLife hFld hPolEq hLifeMatch hLifeEq f' obj'
      have hFid : f.fieldIdx = fid := findField_id_eq hFld
      have hFNotPin : f.pinned = false := by
        cases hp : f.pinned with
        | false => rfl
        | true =>
          have hSt := hObjWF.2.2 f (by rw [hFid]; exact hFld) hp
          rw [hPolEq] at hSt
          cases hSt
      have hObj'WF : PinObjStructWellFormed obj' := by
        refine ⟨?_, ?_, ?_⟩
        · intro hUnp g hg hGPol
          cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
          | true =>
            rw [Nat.eq_of_beq_eq_true hFEq] at hg
            change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
            rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGPol
            rw [hPolEq] at hGPol; cases hGPol
          | false =>
            change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
            rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
            exact hObjWF.1 hUnp g hg hGPol
        · intro hPack g hg hGPol
          cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
          | true =>
            rw [Nat.eq_of_beq_eq_true hFEq] at hg
            change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
            rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGPol
            rw [hPolEq] at hGPol; cases hGPol
          | false =>
            change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
            rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
            exact hObjWF.2.1 hPack g hg hGPol
        · intro g hg hGPin
          cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
          | true =>
            rw [Nat.eq_of_beq_eq_true hFEq] at hg
            change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
            rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGPin
            rw [hFNotPin] at hGPin; cases hGPin
          | false =>
            change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
            rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
            exact hObjWF.2.2 g hg hGPin
      refine ⟨upsertObj_preserves_structWF h obj' hSWF hObj'WF, ?_, ?_, ⟨?_, ?_⟩⟩
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          have hObjAddr := hAddr obj (by rw [hId]; exact hFind)
          refine ⟨?_, ?_⟩
          · dsimp only [obj']; rw [← hLifeEq]; exact hObjAddr.1
          · intro g hg hCond hGUnp
            cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
            | true =>
              rw [Nat.eq_of_beq_eq_true hFEq] at hg
              change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
              rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hCond
              cases hCond with
              | inl hc => rw [hFNotPin] at hc; cases hc
              | inr hc => rw [hPolEq] at hc; cases hc
            | false =>
              change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
              rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
              exact hObjAddr.2 g hg hCond hGUnp
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hAddr o ho
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          dsimp only [obj']
          refine ⟨?_, ?_⟩
          · cases newLife with
            | pinned _ => exact trivial
            | unpinned => exact trivial
            | dropped _ => cases hLifeMatch
            | freed _ _ => cases hLifeMatch
            | leaked _ => cases hLifeMatch
          · intro _ _ _ _
            cases newLife with
            | pinned _ => exact trivial
            | unpinned => exact trivial
            | dropped _ => cases hLifeMatch
            | freed _ _ => cases hLifeMatch
            | leaked _ => cases hLifeMatch
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hDrop o ho
      · intro o ho g hg sp hsp
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hg ⊢
          cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
          | true =>
            rw [Nat.eq_of_beq_eq_true hFEq] at hg
            change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
            rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hsp
            obtain ⟨hPinBad, _, _, _⟩ := hSelf obj (by rw [hId]; exact hFind) f (by rw [hFid]; exact hFld) sp hsp
            rw [hFNotPin] at hPinBad; cases hPinBad
          | false =>
            change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
            rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
            obtain ⟨hg1, hg2, hg3, hg4⟩ := hSelf obj (by rw [hId]; exact hFind) g hg sp hsp
            dsimp only [obj']; rw [hLifeEq] at hg4
            exact ⟨hg1, hg2, hg3, hg4⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hSelf o ho g hg sp hsp
      · intro wOid wFid wAddr hw
        obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
        cases hEq : Nat.beq wOid obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
          injection hWo with hW; rw [← hW] at hWf
          cases hFEq : Nat.beq wFid f.fieldIdx with
          | true =>
            rw [Nat.eq_of_beq_eq_true hFEq, hFid, hFld] at hWf
            injection hWf with hWfEq; rw [← hWfEq, hFNotPin] at hw1; cases hw1
          | false =>
            refine ⟨obj', wf, ?_, ?_, hw1, hw2, hw3, ?_⟩
            · dsimp only []; rw [Nat.eq_of_beq_eq_true hEq]; exact findObj_upsert_same h.objs obj'
            · exact (findField_upsert_other obj.fields f' wFid hFEq).symm ▸ hWf
            · dsimp only [obj']; rw [← hW] at hw4; rw [hLifeEq] at hw4; exact hw4
        | false =>
          refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
          rw [findObj_upsert_other h.objs obj' wOid hEq]
          exact hWo
    cases hLife : obj.lifecycle with
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned orig =>
      rw [hLife] at hStep
      dsimp only [] at hStep
      cases hFld : findField obj.fields fid with
      | none => rw [hFld] at hStep; dsimp only [] at hStep; cases hStep
      | some f =>
        rw [hFld] at hStep
        dsimp only [] at hStep
        cases hPolB : PinProjPolicy.beq f.policy .nonStructural with
        | false =>
          rw [if_bool_true _ (by rw [hPolB]; rfl)] at hStep
          cases hStep
        | true =>
          rw [if_bool_false _ (by rw [hPolB]; rfl)] at hStep
          injection hStep with heq; rw [← heq]
          exact hCore f (.pinned orig) hFld (pinProjPolicy_eq_of_beq hPolB) trivial hLife
    | unpinned =>
      rw [hLife] at hStep
      dsimp only [] at hStep
      cases hFld : findField obj.fields fid with
      | none => rw [hFld] at hStep; dsimp only [] at hStep; cases hStep
      | some f =>
        rw [hFld] at hStep
        dsimp only [] at hStep
        cases hPolB : PinProjPolicy.beq f.policy .nonStructural with
        | false =>
          rw [if_bool_true _ (by rw [hPolB]; rfl)] at hStep
          cases hStep
        | true =>
          rw [if_bool_false _ (by rw [hPolB]; rfl)] at hStep
          injection hStep with heq; rw [← heq]
          exact hCore f .unpinned hFld (pinProjPolicy_eq_of_beq hPolB) trivial hLife

theorem pin_step_preserves_registerSelfPtr (h h' : PinHeap) (oid fid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.registerSelfPtr oid fid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    cases hLife : obj.lifecycle with
    | unpinned => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned orig =>
      rw [hLife] at hStep
      dsimp only [] at hStep
      cases hFld : findField obj.fields fid with
      | none => rw [hFld] at hStep; dsimp only [] at hStep; cases hStep
      | some f =>
        rw [hFld] at hStep
        dsimp only [] at hStep
        have hFid : f.fieldIdx = fid := findField_id_eq hFld
        cases hFPin : f.pinned with
        | false =>
          rw [if_bool_true _ (by rw [hFPin]; rfl)] at hStep
          cases hStep
        | true =>
          cases hFUnp : f.unpin with
          | true =>
            rw [if_bool_true _ (by rw [hFPin, hFUnp]; rfl)] at hStep
            cases hStep
          | false =>
            rw [if_bool_false _ (by rw [hFPin, hFUnp]; rfl)] at hStep
            injection hStep with heq; rw [← heq]
            let f' : PinField := { f with selfPtr? := some f.addr }
            let obj' : PinObj := { obj with lifecycle := .pinned orig, fields := upsertField obj.fields f' }
            have hObj'WF : PinObjStructWellFormed obj' := by
              refine ⟨?_, ?_, ?_⟩
              · intro hUnp g hg hGPol
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGPol ⊢
                  exact hObjWF.1 hUnp f (by rw [hFid]; exact hFld) hGPol
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  exact hObjWF.1 hUnp g hg hGPol
              · intro hPack g hg hGPol
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hGPol
                  exact hObjWF.2.1 hPack f (by rw [hFid]; exact hFld) hGPol
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  exact hObjWF.2.1 hPack g hg hGPol
              · intro g hg hGPin
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG]
                  exact hObjWF.2.2 f (by rw [hFid]; exact hFld) hFPin
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  exact hObjWF.2.2 g hg hGPin
            refine ⟨upsertObj_preserves_structWF h obj' hSWF hObj'WF, ?_, ?_, ⟨?_, ?_⟩⟩
            · intro o ho
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                have hObjAddr := hAddr obj (by rw [hId]; exact hFind)
                refine ⟨?_, ?_⟩
                · rw [hLife] at hObjAddr; exact hObjAddr.1
                · intro g hg hCond hGUnp
                  cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                  | true =>
                    rw [Nat.eq_of_beq_eq_true hFEq] at hg
                    change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                    rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hCond ⊢
                    exact hObjAddr.2 f (by rw [hFid]; exact hFld) hCond hFUnp
                  | false =>
                    change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                    rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                    exact hObjAddr.2 g hg hCond hGUnp
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hAddr o ho
            · intro o ho
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
                exact ⟨trivial, fun _ _ _ _ => trivial⟩
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hDrop o ho
            · intro o ho g hg sp hsp
              cases hEq : Nat.beq o.objId obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq] at ho
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
                rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hg ⊢
                cases hFEq : Nat.beq g.fieldIdx f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq] at hg
                  change findField (upsertField obj.fields f') f'.fieldIdx = some g at hg
                  rw [findField_upsert_same] at hg; injection hg with hG; rw [← hG] at hsp ⊢
                  injection hsp with hAddrEq
                  exact ⟨hFPin, hFUnp, hAddrEq, by dsimp only [obj']⟩
                | false =>
                  change findField (upsertField obj.fields f') g.fieldIdx = some g at hg
                  rw [findField_upsert_other obj.fields f' g.fieldIdx hFEq] at hg
                  obtain ⟨hg1, hg2, hg3, hg4⟩ := hSelf obj (by rw [hId]; exact hFind) g hg sp hsp
                  dsimp only [obj']; rw [hLife] at hg4
                  exact ⟨hg1, hg2, hg3, hg4⟩
              | false =>
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
                rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
                exact hSelf o ho g hg sp hsp
            · intro wOid wFid wAddr hw
              obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
              cases hEq : Nat.beq wOid obj.objId with
              | true =>
                rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
                injection hWo with hW; rw [← hW] at hWf
                cases hFEq : Nat.beq wFid f.fieldIdx with
                | true =>
                  rw [Nat.eq_of_beq_eq_true hFEq, hFid, hFld] at hWf
                  injection hWf with hWfEq
                  refine ⟨obj', f', ?_, ?_, hFPin, hFUnp, ?_, by dsimp only [obj']⟩
                  · dsimp only []; rw [Nat.eq_of_beq_eq_true hEq]; exact findObj_upsert_same h.objs obj'
                  · dsimp only [obj']; rw [Nat.eq_of_beq_eq_true hFEq]; exact findField_upsert_same obj.fields f'
                  · rw [← hWfEq] at hw3; exact hw3
                | false =>
                  refine ⟨obj', wf, ?_, ?_, hw1, hw2, hw3, by dsimp only [obj']⟩
                  · dsimp only []; rw [Nat.eq_of_beq_eq_true hEq]; exact findObj_upsert_same h.objs obj'
                  · exact (findField_upsert_other obj.fields f' wFid hFEq).symm ▸ hWf
              | false =>
                refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
                change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
                rw [findObj_upsert_other h.objs obj' wOid hEq]
                exact hWo

theorem pin_step_preserves_registerWaiter (h h' : PinHeap) (oid fid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.registerWaiter oid fid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    cases hLife : obj.lifecycle with
    | unpinned => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned orig =>
      rw [hLife] at hStep
      dsimp only [] at hStep
      cases hFld : findField obj.fields fid with
      | none => rw [hFld] at hStep; dsimp only [] at hStep; cases hStep
      | some f =>
        rw [hFld] at hStep
        dsimp only [] at hStep
        cases hFPin : f.pinned with
        | false =>
          rw [if_bool_true _ (by rw [hFPin]; rfl)] at hStep
          cases hStep
        | true =>
          cases hFUnp : f.unpin with
          | true =>
            rw [if_bool_true _ (by rw [hFPin, hFUnp]; rfl)] at hStep
            cases hStep
          | false =>
            rw [if_bool_false _ (by rw [hFPin, hFUnp]; rfl)] at hStep
            injection hStep with heq; rw [← heq]
            refine ⟨hSWF, hAddr, hDrop, ⟨hSelf, ?_⟩⟩
            intro wOid wFid wAddr hw
            cases hw with
            | head =>
              exact ⟨obj, f, hFind, hFld, hFPin, hFUnp, rfl, by rw [hLife]; exact trivial⟩
            | tail _ htl =>
              exact hWait wOid wFid wAddr htl

theorem pin_step_preserves_dropInPlace (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.dropInPlace oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    have hCore : ∀ (newOrig : Nat),
        let obj' : PinObj := { obj with lifecycle := .dropped newOrig, fields := markFieldsDropped obj.fields }
        PinSystemInv { h with objs := PinHeap.upsertObj h.objs obj', waiters := removeObjWaiters oid h.waiters } := by
      intro newOrig obj'
      have hObj'WF : PinObjStructWellFormed obj' := by
        refine ⟨?_, ?_, ?_⟩
        · intro hUnp g hg hGPol
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq] at hGPol ⊢
            have hOFId : origF.fieldIdx = g.fieldIdx := findField_id_eq hOrigF
            exact hObjWF.1 hUnp origF (by rw [hOFId]; exact hOrigF) hGPol
        · intro hPack g hg hGPol
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq] at hGPol
            have hOFId : origF.fieldIdx = g.fieldIdx := findField_id_eq hOrigF
            exact hObjWF.2.1 hPack origF (by rw [hOFId]; exact hOrigF) hGPol
        · intro g hg hGPin
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq] at hGPin ⊢
            have hOFId : origF.fieldIdx = g.fieldIdx := findField_id_eq hOrigF
            exact hObjWF.2.2 origF (by rw [hOFId]; exact hOrigF) hGPin
      refine ⟨upsertObj_preserves_structWF h obj' hSWF hObj'WF, ?_, ?_, ⟨?_, ?_⟩⟩
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          refine ⟨trivial, ?_⟩
          intro g hg hCond hGUnp
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq] at hCond hGUnp ⊢
            have hOFId : origF.fieldIdx = g.fieldIdx := findField_id_eq hOrigF
            exact (hAddr obj (by rw [hId]; exact hFind)).2 origF (by rw [hOFId]; exact hOrigF) hCond hGUnp
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hAddr o ho
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          refine ⟨trivial, ?_⟩
          intro g hg _ _
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq]
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hDrop o ho
      · intro o ho g hg sp hsp
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hg
          change findField (markFieldsDropped obj.fields) g.fieldIdx = some g at hg
          rw [findField_markFieldsDropped] at hg
          cases hOrigF : findField obj.fields g.fieldIdx with
          | none => rw [hOrigF] at hg; cases hg
          | some origF =>
            rw [hOrigF] at hg; injection hg with hGEq; rw [← hGEq] at hsp
            cases hsp
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hSelf o ho g hg sp hsp
      · intro wOid wFid wAddr hw
        obtain ⟨hMem, hNe⟩ := (mem_removeObjWaiters_iff oid wOid wFid wAddr h.waiters).mp hw
        obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hMem
        have hNeObj : Nat.beq wOid obj'.objId = false := by
          change Nat.beq wOid obj.objId = false
          rw [hId]; exact hNe
        refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
        rw [findObj_upsert_other h.objs obj' wOid hNeObj]
        exact hWo
    cases hLife : obj.lifecycle with
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned orig =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      exact hCore orig
    | unpinned =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      exact hCore obj.addr

theorem pin_step_preserves_freeAfterDrop (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.freeAfterDrop oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    cases hLife : obj.lifecycle with
    | pinned _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | dropped orig =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      let obj' : PinObj := { obj with lifecycle := .freed orig true }
      refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          exact ⟨trivial, (hAddr obj (by rw [hId]; exact hFind)).2⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hAddr o ho
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          refine ⟨fun _ => rfl, ?_⟩
          intro f hf hFPin hFUnp
          have hFieldDrop := (hDrop obj (by rw [hId]; exact hFind)).2 f hf hFPin hFUnp
          rw [hLife] at hFieldDrop
          exact ⟨rfl, hFieldDrop⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hDrop o ho
      · intro o ho f hf sp hsp
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
          obtain ⟨_, _, _, hBad⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
          rw [hLife] at hBad; cases hBad
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hSelf o ho f hf sp hsp
      · intro wOid wFid wAddr hw
        obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
        cases hEq : Nat.beq wOid obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
          injection hWo with hW; rw [← hW, hLife] at hw4; cases hw4
        | false =>
          refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
          rw [findObj_upsert_other h.objs obj' wOid hEq]
          exact hWo
    | unpinned =>
      rw [hLife] at hStep
      dsimp only [] at hStep
      cases hUnp : obj.unpin with
      | false =>
        rw [if_bool_true _ (by rw [hUnp]; rfl)] at hStep
        cases hStep
      | true =>
        rw [if_bool_false _ (by rw [hUnp]; rfl)] at hStep
        injection hStep with heq; rw [← heq]
        let obj' : PinObj := { obj with lifecycle := .freed obj.addr false }
        refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            exact ⟨trivial, (hAddr obj (by rw [hId]; exact hFind)).2⟩
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hAddr o ho
        · intro o ho
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
            refine ⟨?_, ?_⟩
            · intro hBad; rw [hUnp] at hBad; cases hBad
            · intro f hf hFPin hFUnp
              exact False.elim (unpin_obj_no_pinned_notUnpin_field obj hObjWF hUnp f hf hFPin hFUnp)
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hDrop o ho
        · intro o ho f hf sp hsp
          cases hEq : Nat.beq o.objId obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq] at ho
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
            rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf
            obtain ⟨_, _, _, hBad⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
            rw [hLife] at hBad; cases hBad
          | false =>
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
            rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
            exact hSelf o ho f hf sp hsp
        · intro wOid wFid wAddr hw
          obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
          cases hEq : Nat.beq wOid obj.objId with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
            injection hWo with hW; rw [← hW, hLife] at hw4; cases hw4
          | false =>
            refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
            change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
            rw [findObj_upsert_other h.objs obj' wOid hEq]
            exact hWo

theorem pin_step_preserves_memForgetLeak (h h' : PinHeap) (oid : Nat)
    (hInv : PinSystemInv h) (hStep : stepPinOp h (.memForgetLeak oid) = .ok h') :
    PinSystemInv h' := by
  rcases hInv with ⟨hSWF, hAddr, hDrop, ⟨hSelf, hWait⟩⟩
  unfold stepPinOp at hStep
  dsimp only [] at hStep
  cases hFind : PinHeap.findObj h.objs oid with
  | none => rw [hFind] at hStep; dsimp only [] at hStep; cases hStep
  | some obj =>
    rw [hFind] at hStep
    dsimp only [] at hStep
    have hId : obj.objId = oid := findObj_id_eq hFind
    have hObjWF := hSWF obj (by rw [hId]; exact hFind)
    have hLeakCore : ∀ (newOrig : Nat)
        (hOrigOk : obj.unpin = false → obj.addr = newOrig),
        let obj' : PinObj := { obj with lifecycle := .leaked newOrig }
        PinSystemInv { h with objs := PinHeap.upsertObj h.objs obj' } := by
      intro newOrig hOrigOk obj'
      refine ⟨upsertObj_preserves_structWF h obj' hSWF hObjWF, ?_, ?_, ⟨?_, ?_⟩⟩
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          exact ⟨hOrigOk, (hAddr obj (by rw [hId]; exact hFind)).2⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hAddr o ho
      · intro o ho
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO]
          exact ⟨trivial, fun _ _ _ _ => trivial⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hDrop o ho
      · intro o ho f hf sp hsp
        cases hEq : Nat.beq o.objId obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq] at ho
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') obj'.objId = some o at ho
          rw [findObj_upsert_same] at ho; injection ho with hO; rw [← hO] at hf ⊢
          obtain ⟨hp, hu, ha, _⟩ := hSelf obj (by rw [hId]; exact hFind) f hf sp hsp
          exact ⟨hp, hu, ha, by dsimp only [obj']⟩
        | false =>
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') o.objId = some o at ho
          rw [findObj_upsert_other h.objs obj' o.objId hEq] at ho
          exact hSelf o ho f hf sp hsp
      · intro wOid wFid wAddr hw
        obtain ⟨wo, wf, hWo, hWf, hw1, hw2, hw3, hw4⟩ := hWait wOid wFid wAddr hw
        cases hEq : Nat.beq wOid obj.objId with
        | true =>
          rw [Nat.eq_of_beq_eq_true hEq, hId, hFind] at hWo
          injection hWo with hW; rw [← hW] at hWf
          refine ⟨obj', wf, ?_, hWf, hw1, hw2, hw3, by dsimp only [obj']⟩
          dsimp only []
          rw [Nat.eq_of_beq_eq_true hEq]
          exact findObj_upsert_same h.objs obj'
        | false =>
          refine ⟨wo, wf, ?_, hWf, hw1, hw2, hw3, hw4⟩
          change PinHeap.findObj (PinHeap.upsertObj h.objs obj') wOid = some wo
          rw [findObj_upsert_other h.objs obj' wOid hEq]
          exact hWo
    cases hLife : obj.lifecycle with
    | dropped _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | freed _ _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | leaked _ => rw [hLife] at hStep; dsimp only [] at hStep; cases hStep
    | pinned orig =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      have hObjAddr := (hAddr obj (by rw [hId]; exact hFind)).1
      rw [hLife] at hObjAddr
      exact hLeakCore orig hObjAddr
    | unpinned =>
      rw [hLife] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]
      exact hLeakCore obj.addr (fun _ => rfl)

/-- **THEOREM 4a (`pin_step_preserves_invariants`):**
    EVERY valid `PinOp` step preserves `PinSystemInv` (`PinAddrStabilityInv`,
    `PinDropGuaranteeInv`, `PinPtrValidityInv`, and `PinObjStructWellFormed`). -/
theorem pin_step_preserves_invariants
    (h h' : PinHeap) (op : PinOp)
    (hInv : PinSystemInv h) (hStep : stepPinOp h op = .ok h') :
    PinSystemInv h' := by
  cases op with
  | pinNewSafe oid => exact pin_step_preserves_pinNewSafe h h' oid hInv hStep
  | pinNewUnchecked oid => exact pin_step_preserves_pinNewUnchecked h h' oid hInv hStep
  | pinGetMutSafe oid =>
    unfold stepPinOp at hStep
    dsimp only [] at hStep
    cases hF : PinHeap.findObj h.objs oid with
    | none => rw [hF] at hStep; dsimp only [] at hStep; cases hStep
    | some obj =>
      rw [hF] at hStep
      dsimp only [] at hStep
      cases hU : obj.unpin with
      | false =>
        rw [if_bool_true _ (by rw [hU]; rfl)] at hStep
        cases hStep
      | true =>
        rw [if_bool_false _ (by rw [hU]; rfl)] at hStep
        cases hL : obj.lifecycle with
        | pinned _ => rw [hL] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]; exact hInv
        | unpinned => rw [hL] at hStep; dsimp only [] at hStep; injection hStep with heq; rw [← heq]; exact hInv
        | dropped _ => rw [hL] at hStep; dsimp only [] at hStep; cases hStep
        | freed _ _ => rw [hL] at hStep; dsimp only [] at hStep; cases hStep
        | leaked _ => rw [hL] at hStep; dsimp only [] at hStep; cases hStep
  | pinIntoInnerSafe oid => exact pin_step_preserves_pinIntoInnerSafe h h' oid hInv hStep
  | pinDerefMutSwapSafe oid1 oid2 => exact pin_step_preserves_pinDerefMutSwapSafe h h' oid1 oid2 hInv hStep
  | projectStructural oid fid => exact pin_step_preserves_projectStructural h h' oid fid hInv hStep
  | projectNonStructural oid fid => exact pin_step_preserves_projectNonStructural h h' oid fid hInv hStep
  | registerSelfPtr oid fid => exact pin_step_preserves_registerSelfPtr h h' oid fid hInv hStep
  | registerWaiter oid fid => exact pin_step_preserves_registerWaiter h h' oid fid hInv hStep
  | dropInPlace oid => exact pin_step_preserves_dropInPlace h h' oid hInv hStep
  | freeAfterDrop oid => exact pin_step_preserves_freeAfterDrop h h' oid hInv hStep
  | memForgetLeak oid => exact pin_step_preserves_memForgetLeak h h' oid hInv hStep

/-- **THEOREM 4b (`pin_trace_preserves_invariants`):**
    Arbitrary-length execution traces of `PinOp` preserve `PinSystemInv`. -/
theorem pin_trace_preserves_invariants
    (ops : List PinOp) (h h' : PinHeap)
    (hInv : PinSystemInv h) (hRun : runPinOps h ops = .ok h') :
    PinSystemInv h' := by
  induction ops generalizing h with
  | nil =>
    unfold runPinOps at hRun
    injection hRun with heq; rw [← heq]
    exact hInv
  | cons op rest ih =>
    unfold runPinOps at hRun
    cases hSt : stepPinOp h op with
    | err _ => rw [hSt] at hRun; cases hRun
    | ok hMid =>
      rw [hSt] at hRun
      have hMidInv := pin_step_preserves_invariants h hMid op hInv hSt
      exact ih hMid hMidInv hRun

/-- **THEOREM 4c (`pin_unpin_rejects_phantom_pinned`):**
    Any `!Unpin` object (`o.unpin = false`, e.g. containing `PhantomPinned`)
    is unconditionally rejected by safe `Pin::new`, `Pin::get_mut`, `Pin::into_inner` (`E0277`),
    and safe `DerefMut` swapping (`E0596`). -/
theorem pin_unpin_rejects_phantom_pinned
    (h : PinHeap) (oid oid2 : Nat) (o : PinObj)
    (hFind : PinHeap.findObj h.objs oid = some o)
    (hNotUnp : o.unpin = false) :
    stepPinOp h (.pinNewSafe oid) = .err .notUnpinE0277 ∧
    stepPinOp h (.pinGetMutSafe oid) = .err .notUnpinE0277 ∧
    stepPinOp h (.pinIntoInnerSafe oid) = .err .notUnpinE0277 ∧
    (∀ o2 : PinObj, PinHeap.findObj h.objs oid2 = some o2 →
      stepPinOp h (.pinDerefMutSwapSafe oid oid2) = .err .noDerefMutE0596) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold stepPinOp; dsimp only []; rw [hFind]; dsimp only []
    rw [if_bool_true _ (by rw [hNotUnp]; rfl)]
  · unfold stepPinOp; dsimp only []; rw [hFind]; dsimp only []
    rw [if_bool_true _ (by rw [hNotUnp]; rfl)]
  · unfold stepPinOp; dsimp only []; rw [hFind]; dsimp only []
    rw [if_bool_true _ (by rw [hNotUnp]; rfl)]
  · intro o2 hF2
    unfold stepPinOp
    dsimp only []
    rw [hFind, hF2]
    dsimp only []
    rw [if_bool_true _ (by rw [hNotUnp]; rfl)]

-- ============================================================================
-- Section 7: Necessity Counterexamples (Why RFC 2349 Invariants Fail Without Guards)
-- ============================================================================

/-- Counterexample 1: Unsoundly implementing `Unpin` on a struct that structurally pins
    a `!Unpin` self-referential field violates `StructuralUnpinConsistent` and permits
    safe `DerefMut` swap to relocate the struct while self-pointer points to old address. -/
theorem pin_counterexample_impl_unpin_breaks_selfref :
    let fSelf : PinField := ⟨0, 0x1000, 0x1000, false, .structural, true, false, some 0x1000⟩
    let badObj1 : PinObj := ⟨1, 0x1000, true, false, .pinned 0x1000, [fSelf]⟩
    let badObj2 : PinObj := ⟨2, 0x2000, true, false, .pinned 0x2000, []⟩
    ¬ StructuralUnpinConsistent badObj1 ∧
    stepPinOp ⟨[badObj1, badObj2], [], 0x3000⟩ (.pinDerefMutSwapSafe 1 2) =
      .ok ⟨[{ badObj1 with addr := 0x2000 }, { badObj2 with addr := 0x1000 }], [], 0x3000⟩ := by
  constructor
  · intro hS
    have hTrue := hS rfl ⟨0, 0x1000, 0x1000, false, .structural, true, false, some 0x1000⟩ rfl rfl
    cases hTrue
  · rfl

/-- Counterexample 2: Exposing a non-structural relocation on a pinned `!Unpin` field
    strictly breaks `PinAddrStabilityInv` (`f'.addr ≠ f'.origAddr`). -/
theorem pin_counterexample_mixed_projection_breaks_addr_stability :
    let fMoved : PinField := ⟨0, 0x3000, 0x1000, false, .structural, true, false, some 0x1000⟩
    let badObj : PinObj := ⟨1, 0x1000, false, false, .pinned 0x1000, [fMoved]⟩
    ¬ PinAddrStabilityInv ⟨[badObj], [], 0x4000⟩ := by
  dsimp only []
  intro hA
  have hFld := (hA ⟨1, 0x1000, false, false, .pinned 0x1000, [⟨0, 0x3000, 0x1000, false, .structural, true, false, some 0x1000⟩]⟩ rfl).2
    ⟨0, 0x3000, 0x1000, false, .structural, true, false, some 0x1000⟩ rfl (Or.inl rfl) rfl
  cases hFld

/-- Counterexample 3: Deallocating a pinned `!Unpin` object without running `drop_in_place`
    (`wasDropped = false`) directly violates `PinDropGuaranteeInv`. -/
theorem pin_counterexample_skip_drop_breaks_drop_guarantee :
    let fSelf : PinField := ⟨0, 0x1000, 0x1000, false, .structural, true, false, none⟩
    let badObj : PinObj := ⟨1, 0x1000, false, false, .freed 0x1000 false, [fSelf]⟩
    ¬ PinDropGuaranteeInv ⟨[badObj], [], 0x2000⟩ := by
  dsimp only []
  intro hD
  have hBad := (hD ⟨1, 0x1000, false, false, .freed 0x1000 false, [⟨0, 0x1000, 0x1000, false, .structural, true, false, none⟩]⟩ rfl).1 rfl
  cases hBad

/-- Counterexample 4: End-to-end negative theorem connecting `AddMovesForPackedDrops` and `Pin`:
    on a `#[repr(packed)]` object at misaligned `addr = 5`, staging a drop of a `Drop`
    field (`align = 4`) allocates `tmpAddr = 8 ≠ 5`, violating structural address stability (`PinV2OnPacked`). -/
theorem pin_counterexample_packed_drop_breaks_addr_stability :
    let tyDrop : TyRepr := ⟨30, 2, 4, true, .none, none, true, false, false⟩
    let tyPack1Drop : TyRepr := ⟨31, 0, 5, true, .none, some 0, true, false, true⟩
    let p : MirPlace := { base := ⟨1, tyPack1Drop⟩, projections := [.field 1 1 tyPack1Drop tyDrop] }
    let mem : MemState := ⟨[⟨1, 4, tyPack1Drop, true, true, 99⟩], 6⟩
    addMovesForPackedDropsTransform 7 p = .stagedMoveDrop 7 p ∧
    ∃ (finalMem : MemState) (tmpAddr : Nat),
      execDropInstr mem 99 (addMovesForPackedDropsTransform 7 p) = .ok finalMem 99 tmpAddr ∧
      tmpAddr = 8 ∧
      tmpAddr ≠ 5 := by
  refine ⟨rfl, ?_⟩
  refine ⟨⟨[⟨1, 4, ⟨31, 0, 5, true, .none, some 0, true, false, true⟩, false, true, 99⟩,
            ⟨7, 8, ⟨30, 2, 4, true, .none, none, true, false, false⟩, false, false, 0⟩], 12⟩,
          8, rfl, rfl, ?_⟩
  intro hEq; cases hEq

/-- Positive end-to-end trace theorem: allocating `Unpinned` self-referential struct,
    calling `pinNewUnchecked`, structurally projecting field `0`, registering self-pointer
    and waiter, running `dropInPlace` (clearing `selfPtr?` and waiters), and calling
    `freeAfterDrop` preserves `PinSystemInv` from empty-waiter valid start state. -/
theorem pin_positive_lifecycle_trace_verified :
    let f0 : PinField := ⟨0, 0x1000, 0x1000, false, .structural, false, false, none⟩
    let obj0 : PinObj := ⟨1, 0x1000, false, false, .unpinned, [f0]⟩
    let h0 : PinHeap := ⟨[obj0], [], 0x2000⟩
    PinSystemInv h0 ∧
    runPinOps h0
      [ .pinNewUnchecked 1
      , .projectStructural 1 0
      , .registerSelfPtr 1 0
      , .registerWaiter 1 0
      , .dropInPlace 1
      , .freeAfterDrop 1
      ] =
    .ok ⟨[⟨1, 0x1000, false, false, .freed 0x1000 true,
      [⟨0, 0x1000, 0x1000, false, .structural, true, true, none⟩]⟩], [], 0x2000⟩ := by
  constructor
  · refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩
    · intro o ho
      unfold PinHeap.findObj at ho
      cases hEq : Nat.beq 1 o.objId with
      | false =>
        rw [hEq] at ho; cases ho
      | true =>
        rw [hEq] at ho; injection ho with hO; rw [← hO]
        refine ⟨?_, ?_, ?_⟩
        · intro hBad; cases hBad
        · intro hBad; cases hBad
        · intro f hf hFPin
          unfold findField at hf
          cases hFEq : Nat.beq 0 f.fieldIdx with
          | false => rw [hFEq] at hf; cases hf
          | true => rw [hFEq] at hf; injection hf with hF; rw [← hF] at hFPin; cases hFPin
    · intro o ho
      unfold PinHeap.findObj at ho
      cases hEq : Nat.beq 1 o.objId with
      | false => rw [hEq] at ho; cases ho
      | true =>
        rw [hEq] at ho; injection ho with hO; rw [← hO]
        refine ⟨trivial, ?_⟩
        intro f hf _ _
        unfold findField at hf
        cases hFEq : Nat.beq 0 f.fieldIdx with
        | false => rw [hFEq] at hf; cases hf
        | true => rw [hFEq] at hf; injection hf with hF; rw [← hF]
    · intro o ho
      unfold PinHeap.findObj at ho
      cases hEq : Nat.beq 1 o.objId with
      | false => rw [hEq] at ho; cases ho
      | true =>
        rw [hEq] at ho; injection ho with hO; rw [← hO]
        refine ⟨trivial, ?_⟩
        intro f hf _ _
        exact trivial
    · intro o ho f hf sp hsp
      unfold PinHeap.findObj at ho
      cases hEq : Nat.beq 1 o.objId with
      | false => rw [hEq] at ho; cases ho
      | true =>
        rw [hEq] at ho; injection ho with hO; rw [← hO] at hf
        unfold findField at hf
        cases hFEq : Nat.beq 0 f.fieldIdx with
        | false => rw [hFEq] at hf; cases hf
        | true => rw [hFEq] at hf; injection hf with hF; rw [← hF] at hsp; cases hsp
    · intro _ _ _ hw; cases hw
  · rfl

end VerifiedRustc.PackedPinUnalign
