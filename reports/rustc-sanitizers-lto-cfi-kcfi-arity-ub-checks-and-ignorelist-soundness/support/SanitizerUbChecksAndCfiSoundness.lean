/-!
# Soundness, Incompleteness, Lattice Monotonicity, and Blame Algebra for `rustc`
# Runtime UB Checks, LTO CFI / KCFI, and Sanitizer Ignorelists

This standalone Lean 4 (`v4.34.1`) module formalizes three coupled mechanisms in `rustc`:
1. MIR runtime UB-check instrumentation (`CheckAlignment`, `CheckNull`, `CheckEnums`)
   against an operational memory/value validity model (`miriWellDefined`).
2. LTO CFI 4-point type-ID coarsening lattice `(normalizeInts, generalizePtrs)`,
   LLVM `LowerTypeTests` 8-byte-stride jump-table rotation checks (`@llvm.fshl.i64(..., 61)`),
   and x86-64 KCFI arity register encoding (`-Z sanitizer-kcfi-arity`).
3. `SanitizerIgnoreList` lexicographic last-match-wins blame resolution (`isBlameIgnored`)
   composed with `#[sanitize(... = "off")]` function attributes and the documented
   unfiltered-sanitizer gap (`SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, `REALTIME`).

Constructive verification hygiene:
- Purely total, kernel-checked proofs relying solely on Lean's constructive core
  (no classical choice, no unchecked holes, no external decision-procedure axioms,
  no unsafe or non-terminating definitions, zero warnings under `-DwarningAsError=true`).
-/

namespace SanitizerUbChecksAndCfiSoundness

/-! ## Section 0: Constructive Arithmetic Helpers -/

private theorem nat_add_mod_right_dvd {a b d : Nat} (hd : d ∣ b) :
    (a + b) % d = a % d := by
  rcases hd with ⟨k, rfl⟩
  exact Nat.add_mul_mod_self_left a d k

private theorem nat_dvd_trans_mod {a d1 d2 : Nat} (h12 : d1 ∣ d2) (h2 : a % d2 = 0) :
    a % d1 = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h12 (Nat.dvd_of_mod_eq_zero h2))

private theorem nat_eq_zero_of_mul_add_lt {a b c n : Nat}
    (hc : n ≤ c) (hlt : a + b * c < n) : b = 0 := by
  cases b with
  | zero => rfl
  | succ b' =>
    exfalso
    have h1 : c ≤ (b' + 1) * c := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.le_add_left c (b' * c)
    have h2 : n ≤ a + (b' + 1) * c := Nat.le_trans hc (Nat.le_trans h1 (Nat.le_add_left _ a))
    exact Nat.not_lt.mpr h2 hlt

private theorem list_elem_eq_true_of_mem {α : Type} [BEq α] [LawfulBEq α]
    {x : α} {xs : List α} (h : x ∈ xs) : xs.elem x = true := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.elem_cons]
    cases h with
    | head => simp
    | tail _ hmem =>
      cases hEq : (x == y) with
      | true => rfl
      | false => exact ih hmem

private theorem nat_mod_zero_of_mul_eight (k : Nat) : (8 * k) % 8 = 0 :=
  Nat.mul_mod_right 8 k

private theorem nat_div_eight_of_mul_eight (k : Nat) : (8 * k) / 8 = k :=
  Nat.mul_div_right k (by decide : 0 < 8)

private theorem nat_add_sub_cancel_mod {base d mod : Nat}
    (hBase : base < mod) (hd : d < mod) :
    ((base + d) % mod + (mod - base)) % mod = d := by
  have h1 : ((base + d) % mod + (mod - base)) % mod = ((base + d) + (mod - base)) % mod :=
    Nat.mod_add_mod (base + d) mod (mod - base)
  rw [h1]
  have h2 : (base + d) + (mod - base) = d + mod := by
    have hmb : base + (mod - base) = mod := Nat.add_sub_of_le (Nat.le_of_lt hBase)
    calc
      (base + d) + (mod - base) = (d + base) + (mod - base) := by rw [Nat.add_comm base d]
      _ = d + (base + (mod - base)) := Nat.add_assoc d base (mod - base)
      _ = d + mod := by rw [hmb]
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hd]

/-! ## Section 1: MIR Runtime UB-Check Passes (`CheckAlignment`, `CheckNull`, `CheckEnums`) -/

/-- Wrapping range `[startVal, endVal]` modulo `modulus` (`rustc_abi::WrappingRange`). -/
structure WrappingRange where
  startVal : Nat
  endVal : Nat
  modulus : Nat
  deriving DecidableEq, Repr

/-- Wrapping-range membership mirroring `CheckEnums::insert_niche_check` (`check_enums.rs:489-526`):
`(v - start) mod modulus ≤ (end - start) mod modulus`. -/
def WrappingRange.contains (r : WrappingRange) (v : Nat) : Bool :=
  if r.modulus == 0 then
    false
  else
    let shift := r.modulus - (r.startVal % r.modulus)
    let lhs := (v % r.modulus + shift) % r.modulus
    let rhs := (r.endVal % r.modulus + shift) % r.modulus
    decide (lhs ≤ rhs)

/-- MIR type universe capturing every case distinguished by `CheckAlignment`,
`CheckNull`, `CheckEnums`, and Miri value validity. -/
inductive MirTy where
  | unit
  | primBool
  | primU8
  | primI8
  | primU32
  | structTy (size : Nat) (align : Nat)
  | enumEmpty
  | enumSingle (inner : MirTy)
  | enumDirect (validDiscrs : List Nat) (size : Nat) (align : Nat)
  | enumNiche (tagOffset : Nat) (range : WrappingRange) (size : Nat) (align : Nat)
  deriving DecidableEq, Repr

def MirTy.size : MirTy → Nat
  | .unit => 0
  | .primBool => 1
  | .primU8 => 1
  | .primI8 => 1
  | .primU32 => 4
  | .structTy sz _ => sz
  | .enumEmpty => 0
  | .enumSingle inner => inner.size
  | .enumDirect _ sz _ => sz
  | .enumNiche _ _ sz _ => sz

def MirTy.align : MirTy → Nat
  | .unit => 1
  | .primBool => 1
  | .primU8 => 1
  | .primI8 => 1
  | .primU32 => 4
  | .structTy _ al => al
  | .enumEmpty => 1
  | .enumSingle inner => inner.align
  | .enumDirect _ _ al => al
  | .enumNiche _ _ _ al => al

def MirTy.isInhabited : MirTy → Bool
  | .enumEmpty => false
  | .enumSingle inner => inner.isInhabited
  | _ => true

/-- `CheckAlignment`'s `excluded_pointees = [bool, i8, u8]` (`check_alignment.rs:22`). -/
def isAlignmentExcluded : MirTy → Bool
  | .primBool | .primI8 | .primU8 => true
  | _ => false

/-- MIR `PlaceContext` categories handled by `check_pointers.rs:182-198`. -/
inductive PlaceCtx where
  | copyRead
  | storeWrite
  | sharedBorrow
  | mutBorrow
  | rawAddrOf
  deriving DecidableEq, Repr

def PlaceCtx.isBorrow : PlaceCtx → Bool
  | .sharedBorrow | .mutBorrow => true
  | _ => false

def PlaceCtx.visitedByCheckPointers : PlaceCtx → Bool
  | .rawAddrOf => false
  | _ => true

/-- Target configuration relevant to MIR UB checks. -/
structure TargetUbCfg where
  hasPanicImpl : Bool
  ubChecksEnabled : Bool
  /-- Clamped alignment modeling `min(align, max_reliable_alignment())` (`check_alignment.rs:86-108`):
  always divides the true alignment and is positive. -/
  effectiveAlign : MirTy → Nat
  effectiveAlign_dvd : ∀ t, effectiveAlign t ∣ t.align
  effectiveAlign_pos : ∀ t, 0 < effectiveAlign t

/-- Concrete MIR operations audited for UB-check soundness and completeness. -/
inductive MirOp where
  | ptrAccess (ctx : PlaceCtx) (baseAddr : Nat) (baseTy : MirTy)
      (fieldOffset : Nat) (fieldTy : MirTy)
  | transmute (srcTy : MirTy) (dstTy : MirTy) (srcBytes : List Nat)
  | ptrReadValue (baseAddr : Nat) (dstTy : MirTy) (memBytes : List Nat)
  deriving DecidableEq, Repr

/-- `AssertKind` abort reasons injected by `CheckAlignment`, `CheckNull`, and `CheckEnums`. -/
inductive UbAbortKind where
  | misalignedPtrDeref
  | nullPtrDeref
  | nullRefConstructed
  | invalidEnumConstruction
  deriving DecidableEq, Repr

inductive CheckOutcome where
  | ok
  | abort (kind : UbAbortKind)
  deriving DecidableEq, Repr

/-- Extract byte at offset (modeling `[MaybeUninit<u8>; N]` subslice extraction in
`check_enums.rs:278-303`). -/
def byteAt (bytes : List Nat) (off : Nat) : Nat :=
  match bytes.drop off with
  | b :: _ => b % 256
  | [] => 0

/-- Full operational byte-level value validity (Miri oracle). -/
def validValueBytes : MirTy → List Nat → Prop
  | .unit, _ => True
  | .primBool, bs => byteAt bs 0 ≤ 1
  | .primU8, _ => True
  | .primI8, _ => True
  | .primU32, _ => True
  | .structTy _ _, _ => True
  | .enumEmpty, _ => False
  | .enumSingle inner, bs => validValueBytes inner bs
  | .enumDirect validDiscrs _ _, bs => byteAt bs 0 ∈ validDiscrs
  | .enumNiche tagOffset r _ _, bs => r.contains (byteAt bs tagOffset) = true

/-- Layout invariant for non-packed field projections: field offset is a multiple of field alignment. -/
def layoutAlignedOffset : MirOp → Prop
  | .ptrAccess _ _ _ fieldOffset fieldTy => fieldTy.align ∣ fieldOffset
  | _ => True

/-- Operational Miri well-definedness predicate for an executed `MirOp`.
For `transmute`, a dynamically reached transmute requires an inhabited source value
(`srcTy.isInhabited = true`) and a byte representation satisfying the destination type's
full validity invariant (`validValueBytes dstTy srcBytes`). -/
def miriWellDefined : MirOp → Prop
  | .ptrAccess ctx baseAddr baseTy fieldOffset fieldTy =>
    match ctx with
    | .rawAddrOf => True
    | .sharedBorrow | .mutBorrow =>
      baseAddr ≠ 0 ∧ (baseAddr + fieldOffset) % fieldTy.align = 0
    | .copyRead | .storeWrite =>
      (baseTy.size ≠ 0 → baseAddr ≠ 0) ∧ baseAddr % baseTy.align = 0
  | .transmute srcTy dstTy srcBytes =>
    srcTy.isInhabited = true ∧ validValueBytes dstTy srcBytes
  | .ptrReadValue baseAddr dstTy memBytes =>
    (dstTy.size ≠ 0 → baseAddr ≠ 0) ∧
    baseAddr % dstTy.align = 0 ∧
    validValueBytes dstTy memBytes

/-- `CheckAlignment` pass semantics (`check_alignment.rs:20-148`, `FollowProjections`). -/
def runCheckAlignment (cfg : TargetUbCfg) (op : MirOp) : CheckOutcome :=
  if !cfg.ubChecksEnabled || !cfg.hasPanicImpl then
    .ok
  else
    match op with
    | .ptrAccess ctx baseAddr baseTy _ fieldTy =>
      if !ctx.visitedByCheckPointers then
        .ok
      else
        let checkedTy := if ctx.isBorrow then fieldTy else baseTy
        if isAlignmentExcluded checkedTy then
          .ok
        else
          let reqAlign := cfg.effectiveAlign checkedTy
          if baseAddr % reqAlign == 0 then .ok else .abort .misalignedPtrDeref
    | .ptrReadValue baseAddr dstTy _ =>
      if isAlignmentExcluded dstTy then
        .ok
      else
        let reqAlign := cfg.effectiveAlign dstTy
        if baseAddr % reqAlign == 0 then .ok else .abort .misalignedPtrDeref
    | .transmute _ _ _ => .ok

/-- `CheckNull` pass semantics (`check_null.rs:18-128`, `NoFollowProjections`). -/
def runCheckNull (cfg : TargetUbCfg) (op : MirOp) : CheckOutcome :=
  if !cfg.ubChecksEnabled || !cfg.hasPanicImpl then
    .ok
  else
    match op with
    | .ptrAccess ctx baseAddr baseTy _ _ =>
      if !ctx.visitedByCheckPointers then
        .ok
      else if ctx.isBorrow then
        if baseAddr == 0 then .abort .nullRefConstructed else .ok
      else
        if baseAddr == 0 && baseTy.size != 0 then .abort .nullPtrDeref else .ok
    | .ptrReadValue baseAddr dstTy _ =>
      if baseAddr == 0 && dstTy.size != 0 then .abort .nullPtrDeref else .ok
    | .transmute _ _ _ => .ok

/-- `CheckEnums` pass semantics (`check_enums.rs:167-238`):
visits `Rvalue::Cast(CastKind::Transmute, op, ty)` on `adt_def.is_enum()` only,
skipping `Variants::Single`, `ty::Bool`, and pointer dereference reads. -/
def runCheckEnums (cfg : TargetUbCfg) (op : MirOp) : CheckOutcome :=
  if !cfg.ubChecksEnabled || !cfg.hasPanicImpl then
    .ok
  else
    match op with
    | .transmute srcTy dstTy srcBytes =>
      match dstTy with
      | .enumEmpty =>
        if !srcTy.isInhabited then .ok else .abort .invalidEnumConstruction
      | .enumSingle _ =>
        .ok
      | .enumDirect validDiscrs _ _ =>
        let tag := byteAt srcBytes 0
        if validDiscrs.elem tag then .ok else .abort .invalidEnumConstruction
      | .enumNiche tagOffset r _ _ =>
        let tag := byteAt srcBytes tagOffset
        if r.contains tag then .ok else .abort .invalidEnumConstruction
      | _ => .ok
    | .ptrAccess _ _ _ _ _ => .ok
    | .ptrReadValue _ _ _ => .ok

/-- Composition in exact `rustc_mir_transform/src/lib.rs:711-713` pass order:
`CheckAlignment` -> `CheckNull` -> `CheckEnums`. -/
def runUbChecks (cfg : TargetUbCfg) (op : MirOp) : CheckOutcome :=
  match runCheckAlignment cfg op with
  | .abort k => .abort k
  | .ok =>
    match runCheckNull cfg op with
    | .abort k => .abort k
    | .ok => runCheckEnums cfg op

theorem checkAlignment_sound (cfg : TargetUbCfg) (op : MirOp)
    (hLayout : layoutAlignedOffset op) (hWd : miriWellDefined op) :
    runCheckAlignment cfg op = .ok := by
  unfold runCheckAlignment
  cases hEn : cfg.ubChecksEnabled <;> cases hPi : cfg.hasPanicImpl
  · rfl
  · rfl
  · rfl
  · dsimp only
    cases op with
    | ptrAccess ctx baseAddr baseTy fieldOffset fieldTy =>
      cases ctx with
      | rawAddrOf => rfl
      | copyRead =>
        dsimp only [PlaceCtx.visitedByCheckPointers, PlaceCtx.isBorrow]
        change (if isAlignmentExcluded baseTy = true then CheckOutcome.ok
          else if (baseAddr % cfg.effectiveAlign baseTy == 0) = true then CheckOutcome.ok
          else CheckOutcome.abort UbAbortKind.misalignedPtrDeref) = CheckOutcome.ok
        cases hEx : isAlignmentExcluded baseTy with
        | true => rfl
        | false =>
          have hEff : baseAddr % cfg.effectiveAlign baseTy = 0 :=
            nat_dvd_trans_mod (cfg.effectiveAlign_dvd baseTy) hWd.2
          rw [hEff]
          rfl
      | storeWrite =>
        dsimp only [PlaceCtx.visitedByCheckPointers, PlaceCtx.isBorrow]
        change (if isAlignmentExcluded baseTy = true then CheckOutcome.ok
          else if (baseAddr % cfg.effectiveAlign baseTy == 0) = true then CheckOutcome.ok
          else CheckOutcome.abort UbAbortKind.misalignedPtrDeref) = CheckOutcome.ok
        cases hEx : isAlignmentExcluded baseTy with
        | true => rfl
        | false =>
          have hEff : baseAddr % cfg.effectiveAlign baseTy = 0 :=
            nat_dvd_trans_mod (cfg.effectiveAlign_dvd baseTy) hWd.2
          rw [hEff]
          rfl
      | sharedBorrow =>
        dsimp only [PlaceCtx.visitedByCheckPointers, PlaceCtx.isBorrow]
        change (if isAlignmentExcluded fieldTy = true then CheckOutcome.ok
          else if (baseAddr % cfg.effectiveAlign fieldTy == 0) = true then CheckOutcome.ok
          else CheckOutcome.abort UbAbortKind.misalignedPtrDeref) = CheckOutcome.ok
        cases hEx : isAlignmentExcluded fieldTy with
        | true => rfl
        | false =>
          have hShift : (baseAddr + fieldOffset) % fieldTy.align = baseAddr % fieldTy.align :=
            nat_add_mod_right_dvd hLayout
          have hMod : baseAddr % fieldTy.align = 0 := hShift.symm.trans hWd.2
          have hEff : baseAddr % cfg.effectiveAlign fieldTy = 0 :=
            nat_dvd_trans_mod (cfg.effectiveAlign_dvd fieldTy) hMod
          rw [hEff]
          rfl
      | mutBorrow =>
        dsimp only [PlaceCtx.visitedByCheckPointers, PlaceCtx.isBorrow]
        change (if isAlignmentExcluded fieldTy = true then CheckOutcome.ok
          else if (baseAddr % cfg.effectiveAlign fieldTy == 0) = true then CheckOutcome.ok
          else CheckOutcome.abort UbAbortKind.misalignedPtrDeref) = CheckOutcome.ok
        cases hEx : isAlignmentExcluded fieldTy with
        | true => rfl
        | false =>
          have hShift : (baseAddr + fieldOffset) % fieldTy.align = baseAddr % fieldTy.align :=
            nat_add_mod_right_dvd hLayout
          have hMod : baseAddr % fieldTy.align = 0 := hShift.symm.trans hWd.2
          have hEff : baseAddr % cfg.effectiveAlign fieldTy = 0 :=
            nat_dvd_trans_mod (cfg.effectiveAlign_dvd fieldTy) hMod
          rw [hEff]
          rfl
    | transmute _ _ _ => rfl
    | ptrReadValue baseAddr dstTy _ =>
      change (if isAlignmentExcluded dstTy = true then CheckOutcome.ok
        else if (baseAddr % cfg.effectiveAlign dstTy == 0) = true then CheckOutcome.ok
        else CheckOutcome.abort UbAbortKind.misalignedPtrDeref) = CheckOutcome.ok
      cases hEx : isAlignmentExcluded dstTy with
      | true => rfl
      | false =>
        have hEff : baseAddr % cfg.effectiveAlign dstTy = 0 :=
          nat_dvd_trans_mod (cfg.effectiveAlign_dvd dstTy) hWd.2.1
        rw [hEff]
        rfl

theorem checkNull_sound (cfg : TargetUbCfg) (op : MirOp) (hWd : miriWellDefined op) :
    runCheckNull cfg op = .ok := by
  unfold runCheckNull
  cases hEn : cfg.ubChecksEnabled <;> cases hPi : cfg.hasPanicImpl
  · rfl
  · rfl
  · rfl
  · simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases op with
    | ptrAccess ctx baseAddr baseTy _ _ =>
      cases ctx with
      | rawAddrOf => rfl
      | sharedBorrow =>
        simp only [PlaceCtx.visitedByCheckPointers, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          PlaceCtx.isBorrow]
        have hEq : (baseAddr == 0) = false := beq_false_of_ne hWd.1
        rw [hEq]
        rfl
      | mutBorrow =>
        simp only [PlaceCtx.visitedByCheckPointers, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          PlaceCtx.isBorrow]
        have hEq : (baseAddr == 0) = false := beq_false_of_ne hWd.1
        rw [hEq]
        rfl
      | copyRead =>
        simp only [PlaceCtx.visitedByCheckPointers, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          PlaceCtx.isBorrow]
        cases hZero : (baseAddr == 0) with
        | false => rfl
        | true =>
          have hAddr : baseAddr = 0 := eq_of_beq hZero
          cases hSz : (baseTy.size != 0) with
          | false => rfl
          | true =>
            exfalso
            have hSzNe : baseTy.size ≠ 0 := by
              intro heq
              rw [heq] at hSz
              exact Bool.false_ne_true hSz
            exact (hWd.1 hSzNe) hAddr
      | storeWrite =>
        simp only [PlaceCtx.visitedByCheckPointers, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          PlaceCtx.isBorrow]
        cases hZero : (baseAddr == 0) with
        | false => rfl
        | true =>
          have hAddr : baseAddr = 0 := eq_of_beq hZero
          cases hSz : (baseTy.size != 0) with
          | false => rfl
          | true =>
            exfalso
            have hSzNe : baseTy.size ≠ 0 := by
              intro heq
              rw [heq] at hSz
              exact Bool.false_ne_true hSz
            exact (hWd.1 hSzNe) hAddr
    | transmute _ _ _ => rfl
    | ptrReadValue baseAddr dstTy _ =>
      dsimp only
      cases hZero : (baseAddr == 0) with
      | false => rfl
      | true =>
        have hAddr : baseAddr = 0 := eq_of_beq hZero
        cases hSz : (dstTy.size != 0) with
        | false => rfl
        | true =>
          exfalso
          have hSzNe : dstTy.size ≠ 0 := by
            intro heq
            rw [heq] at hSz
            exact Bool.false_ne_true hSz
          exact (hWd.1 hSzNe) hAddr

theorem checkEnums_sound (cfg : TargetUbCfg) (op : MirOp) (hWd : miriWellDefined op) :
    runCheckEnums cfg op = .ok := by
  unfold runCheckEnums
  cases hEn : cfg.ubChecksEnabled <;> cases hPi : cfg.hasPanicImpl
  · rfl
  · rfl
  · rfl
  · simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases op with
    | ptrAccess _ _ _ _ _ => rfl
    | ptrReadValue _ _ _ => rfl
    | transmute srcTy dstTy srcBytes =>
      cases dstTy with
      | enumEmpty => exact False.elim hWd.2
      | enumSingle _ => rfl
      | enumDirect validDiscrs _ _ =>
        have hElem : validDiscrs.elem (byteAt srcBytes 0) = true :=
          list_elem_eq_true_of_mem hWd.2
        dsimp only
        rw [hElem]
        rfl
      | enumNiche tagOffset r _ _ =>
        have hCont : r.contains (byteAt srcBytes tagOffset) = true := hWd.2
        dsimp only
        rw [hCont]
        rfl
      | unit => rfl
      | primBool => rfl
      | primU8 => rfl
      | primI8 => rfl
      | primU32 => rfl
      | structTy _ _ => rfl

/-- **Theorem 1 (No-False-Positive Soundness of MIR UB Checks)**:
Every well-defined execution (`miriWellDefined`) over a layout-aligned projection never
triggers an abort in `CheckAlignment`, `CheckNull`, or `CheckEnums`, regardless of target
alignment clamping (`max_reliable_alignment()`), `PanicImpl` availability, or `-Z ub-checks`. -/
theorem ubChecks_never_reject_well_defined_execution (cfg : TargetUbCfg) (op : MirOp)
    (hLayout : layoutAlignedOffset op) (hWd : miriWellDefined op) :
    runUbChecks cfg op = .ok := by
  unfold runUbChecks
  rw [checkAlignment_sound cfg op hLayout hWd]
  rw [checkNull_sound cfg op hWd]
  exact checkEnums_sound cfg op hWd

/-- Concrete host configuration with `ub-checks = yes`, `PanicImpl` present, and exact alignment
(e.g. `x86_64-unknown-linux-gnu` where `max_reliable_alignment() = Align::MAX`). -/
def x86HostUbCfg : TargetUbCfg where
  hasPanicImpl := true
  ubChecksEnabled := true
  effectiveAlign := fun t => if t.align == 0 then 1 else t.align
  effectiveAlign_dvd := by
    intro t
    cases h : (t.align == 0) with
    | true =>
      have hz : t.align = 0 := eq_of_beq h
      rw [hz]
      exact ⟨0, rfl⟩
    | false => exact Nat.dvd_refl t.align
  effectiveAlign_pos := by
    intro t
    cases h : (t.align == 0) with
    | true => exact Nat.zero_lt_one
    | false =>
      have hne : t.align ≠ 0 := by
        intro hz
        rw [hz] at h
        exact Bool.false_ne_true h.symm
      exact Nat.pos_of_ne_zero hne

def alignedStructTy : MirTy := .structTy 8 4
def directEnumTy : MirTy := .enumDirect [0, 1] 1 1
def singleWrapBoolTy : MirTy := .enumSingle .primBool
def optionBoolNicheTy : MirTy := .enumNiche 0 ⟨0, 2, 256⟩ 1 1
def multibyteOptionTy : MirTy := .enumNiche 4 ⟨0, 2, 256⟩ 8 4

/-- Umbrella Theorem 1 bundling general no-false-positive soundness with the exact edge cases
distinguishing `FollowProjections`, `NoFollowProjections`, and ZST dereference vs. borrow. -/
theorem ubChecks_sound_no_false_positives :
    (∀ cfg op, layoutAlignedOffset op → miriWellDefined op → runUbChecks cfg op = .ok) ∧
    (miriWellDefined (.ptrAccess .sharedBorrow 1 alignedStructTy 4 .primU8) ∧
     runUbChecks x86HostUbCfg (.ptrAccess .sharedBorrow 1 alignedStructTy 4 .primU8) = .ok) ∧
    (miriWellDefined (.ptrAccess .copyRead 0 .unit 0 .unit) ∧
     runUbChecks x86HostUbCfg (.ptrAccess .copyRead 0 .unit 0 .unit) = .ok) ∧
    (¬ miriWellDefined (.ptrAccess .sharedBorrow 0 .unit 0 .unit) ∧
     runUbChecks x86HostUbCfg (.ptrAccess .sharedBorrow 0 .unit 0 .unit) =
       .abort .nullRefConstructed) ∧
    (¬ miriWellDefined (.ptrAccess .sharedBorrow 0 alignedStructTy 4 .primU8) ∧
     runUbChecks x86HostUbCfg (.ptrAccess .sharedBorrow 0 alignedStructTy 4 .primU8) =
       .abort .nullRefConstructed) ∧
    (runUbChecks x86HostUbCfg
       (.transmute (.structTy 8 1) multibyteOptionTy [0, 0, 0, 0, 3, 0, 0, 0]) =
       .abort .invalidEnumConstruction) := by
  refine ⟨ubChecks_never_reject_well_defined_execution, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide⟩, rfl⟩
  · refine ⟨⟨fun h => absurd rfl h, by decide⟩, rfl⟩
  · refine ⟨fun h => h.1 rfl, rfl⟩
  · refine ⟨fun h => h.1 rfl, rfl⟩
  · rfl

/-- **Counterexample 1 (`ce1_ub_checks_miss_single_variant_bool_and_ptr_read_enum_ub`)**:
Strict incompleteness of `CheckEnums` against Miri value validity across all three
uninstrumented paths:
1. `transmute::<u8, SingleWrapBool>(2)` (`Variants::Single { .. } => {}`),
2. `transmute::<u8, bool>(2)` (non-ADT `ty::Bool`),
3. `*(ptr as *const DirectEnum)` reading byte `2` (`Rvalue::Use(Copy(*p))`, not `Transmute`). -/
theorem ce1_ub_checks_miss_single_variant_bool_and_ptr_read_enum_ub :
    let opSingle : MirOp := .transmute .primU8 singleWrapBoolTy [2]
    let opBool   : MirOp := .transmute .primU8 .primBool [2]
    let opPtrRd  : MirOp := .ptrReadValue 4096 directEnumTy [2]
    (¬ miriWellDefined opSingle ∧ runUbChecks x86HostUbCfg opSingle = .ok) ∧
    (¬ miriWellDefined opBool   ∧ runUbChecks x86HostUbCfg opBool   = .ok) ∧
    (¬ miriWellDefined opPtrRd  ∧ runUbChecks x86HostUbCfg opPtrRd  = .ok) := by
  refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩, ⟨?_, rfl⟩⟩
  · intro h
    have hle : 2 ≤ 1 := h.2
    exact absurd hle (by decide)
  · intro h
    have hle : 2 ≤ 1 := h.2
    exact absurd hle (by decide)
  · intro h
    have hmem : 2 ∈ ([0, 1] : List Nat) := h.2.2
    exact absurd hmem (by decide)

/-! ## Section 2: LTO CFI 4-Point Coarsening Lattice, `LowerTypeTests`, and KCFI Arity -/

/-- 4-point CFI type-ID coarsening lattice `(normalizeInts, generalizePtrs)` matching
`compiler/rustc_codegen_llvm/src/declare.rs:216-226`. -/
structure CfiMode where
  normalizeInts : Bool
  generalizePtrs : Bool
  deriving DecidableEq, Repr

/-- Lattice ordering: `m1 ≤ m2` iff `m2` enables a superset of coarsening flags. -/
def CfiMode.le (m1 m2 : CfiMode) : Prop :=
  (m1.normalizeInts = true → m2.normalizeInts = true) ∧
  (m1.generalizePtrs = true → m2.generalizePtrs = true)

def CfiMode.raw : CfiMode := ⟨false, false⟩
def CfiMode.normalized : CfiMode := ⟨true, false⟩
def CfiMode.generalized : CfiMode := ⟨false, true⟩
def CfiMode.normalizedGeneralized : CfiMode := ⟨true, true⟩

/-- Base value/pointer types modeled for Itanium C++ ABI CFI encoding (`transform.rs:76-219`). -/
inductive CfiBaseTy where
  | tyVoid
  | tyBool
  | tyChar
  | tyU8
  | tyU32
  | tyI32
  | tyU64
  | tyUsize
  | tyRawPtr (isMut : Bool) (pointee : CfiBaseTy)
  | tyRef (isMut : Bool) (pointee : CfiBaseTy)
  deriving DecidableEq, Repr

/-- Full CFI type including arbitrary-arity function pointers (`ty::FnPtr`, `transform.rs:213-219`). -/
inductive CfiTy where
  | base (t : CfiBaseTy)
  | tyFnPtr (ret : CfiBaseTy) (args : List CfiBaseTy)
  deriving DecidableEq, Repr

def generalizeBaseTy : CfiBaseTy → CfiBaseTy
  | .tyRawPtr isMut _ => .tyRawPtr isMut .tyVoid
  | .tyRef isMut _ => .tyRef isMut .tyVoid
  | t => t

def normalizeIntBaseTy : CfiBaseTy → CfiBaseTy
  | .tyBool => .tyU8
  | .tyChar => .tyU32
  | .tyUsize => .tyU64
  | .tyRawPtr isMut p => .tyRawPtr isMut (normalizeIntBaseTy p)
  | .tyRef isMut p => .tyRef isMut (normalizeIntBaseTy p)
  | t => t

/-- Pointer generalization (`TransformTyOptions::GENERALIZE_POINTERS`, `transform.rs:189-219`):
replaces `*const T`/`*mut T`/`&T`/`&mut T`/`fn(...)` pointees with `()` (`tyVoid`). -/
def generalizeTy : CfiTy → CfiTy
  | .base t => .base (generalizeBaseTy t)
  | .tyFnPtr _ _ => .base (.tyRawPtr false .tyVoid)

/-- Integer normalization on 64-bit targets (`TransformTyOptions::NORMALIZE_INTEGERS`,
`transform.rs:76-115`): `bool -> u8`, `char -> u32`, `usize -> u64`. -/
def normalizeIntTy : CfiTy → CfiTy
  | .base t => .base (normalizeIntBaseTy t)
  | .tyFnPtr r args => .tyFnPtr (normalizeIntBaseTy r) (args.map normalizeIntBaseTy)

/-- Combined transformation matching `TransformTy::fold_ty` (`transform.rs:51-220`). -/
def transformCfiTy (m : CfiMode) (t : CfiTy) : CfiTy :=
  let t1 := if m.normalizeInts then normalizeIntTy t else t
  if m.generalizePtrs then generalizeTy t1 else t1

structure CfiFnSig where
  ret : CfiTy
  args : List CfiTy
  deriving DecidableEq, Repr

/-- Encoded CFI type metadata identifier with canonical mode suffixes
(`.normalized`, `.generalized`, `itanium_cxx_abi/mod.rs:97-103`). -/
structure CfiTypeId where
  mode : CfiMode
  ret : CfiTy
  args : List CfiTy
  deriving DecidableEq, Repr

def cfiTypeId (m : CfiMode) (sig : CfiFnSig) : CfiTypeId :=
  ⟨m, transformCfiTy m sig.ret, sig.args.map (transformCfiTy m)⟩

private theorem normalizeIntBaseTy_idemp (t : CfiBaseTy) :
    normalizeIntBaseTy (normalizeIntBaseTy t) = normalizeIntBaseTy t := by
  induction t with
  | tyRawPtr isMut p ih => simp only [normalizeIntBaseTy, ih]
  | tyRef isMut p ih => simp only [normalizeIntBaseTy, ih]
  | _ => rfl

private theorem normalizeIntTy_idemp (t : CfiTy) :
    normalizeIntTy (normalizeIntTy t) = normalizeIntTy t := by
  cases t with
  | base b => exact congrArg CfiTy.base (normalizeIntBaseTy_idemp b)
  | tyFnPtr r args =>
    simp only [normalizeIntTy, List.map_map]
    rw [normalizeIntBaseTy_idemp r]
    congr 1
    induction args with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, Function.comp_apply]
      rw [normalizeIntBaseTy_idemp y, ih]

private theorem generalizeBaseTy_idemp (t : CfiBaseTy) :
    generalizeBaseTy (generalizeBaseTy t) = generalizeBaseTy t := by
  cases t <;> rfl

private theorem generalizeTy_idemp (t : CfiTy) :
    generalizeTy (generalizeTy t) = generalizeTy t := by
  cases t with
  | base b => exact congrArg CfiTy.base (generalizeBaseTy_idemp b)
  | tyFnPtr _ _ => rfl

private theorem generalizeBaseTy_comm_normalizeIntBaseTy (t : CfiBaseTy) :
    generalizeBaseTy (normalizeIntBaseTy t) = normalizeIntBaseTy (generalizeBaseTy t) := by
  cases t <;> rfl

private theorem generalizeTy_comm_normalizeIntTy (t : CfiTy) :
    generalizeTy (normalizeIntTy t) = normalizeIntTy (generalizeTy t) := by
  cases t with
  | base b => exact congrArg CfiTy.base (generalizeBaseTy_comm_normalizeIntBaseTy b)
  | tyFnPtr _ _ => rfl

private theorem transformCfiTy_compose {m1 m2 : CfiMode} (hle : m1.le m2) (t : CfiTy) :
    transformCfiTy m2 (transformCfiTy m1 t) = transformCfiTy m2 t := by
  rcases m1 with ⟨n1, g1⟩
  rcases m2 with ⟨n2, g2⟩
  rcases hle with ⟨hn, hg⟩
  cases n1 <;> cases g1 <;> cases n2 <;> cases g2
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (Bool.false_ne_true (hg rfl))
  · simp only [transformCfiTy, Bool.false_eq_true, ↓reduceIte, generalizeTy_idemp]
  · exact False.elim (Bool.false_ne_true (hg rfl))
  · simp only [transformCfiTy, ↓reduceIte, Bool.false_eq_true]
    rw [← generalizeTy_comm_normalizeIntTy, generalizeTy_idemp]
  · exact False.elim (Bool.false_ne_true (hn rfl))
  · exact False.elim (Bool.false_ne_true (hn rfl))
  · simp only [transformCfiTy, Bool.false_eq_true, ↓reduceIte, normalizeIntTy_idemp]
  · simp only [transformCfiTy, ↓reduceIte, Bool.false_eq_true, normalizeIntTy_idemp]
  · exact False.elim (Bool.false_ne_true (hn rfl))
  · exact False.elim (Bool.false_ne_true (hn rfl))
  · exact False.elim (Bool.false_ne_true (hg rfl))
  · simp only [transformCfiTy, ↓reduceIte]
    rw [← generalizeTy_comm_normalizeIntTy, generalizeTy_idemp, normalizeIntTy_idemp]

/-- Lattice coarsening monotonicity on function signatures: any two signatures equated at a
finer mode `m1` remain equated at every coarser mode `m2 ≥ m1`. -/
theorem cfi_mode_coarsening_monotone {m1 m2 : CfiMode} (hle : m1.le m2)
    (s1 s2 : CfiFnSig)
    (heq : cfiTypeId m1 s1 = cfiTypeId m1 s2) :
    cfiTypeId m2 s1 = cfiTypeId m2 s2 := by
  have hret : transformCfiTy m1 s1.ret = transformCfiTy m1 s2.ret :=
    congrArg CfiTypeId.ret heq
  have hargs : s1.args.map (transformCfiTy m1) = s2.args.map (transformCfiTy m1) :=
    congrArg CfiTypeId.args heq
  unfold cfiTypeId
  congr 1
  · calc
      transformCfiTy m2 s1.ret = transformCfiTy m2 (transformCfiTy m1 s1.ret) :=
        (transformCfiTy_compose hle s1.ret).symm
      _ = transformCfiTy m2 (transformCfiTy m1 s2.ret) := by rw [hret]
      _ = transformCfiTy m2 s2.ret := transformCfiTy_compose hle s2.ret
  · have hmap : ∀ xs : List CfiTy,
        (xs.map (transformCfiTy m1)).map (transformCfiTy m2) = xs.map (transformCfiTy m2) := by
      intro xs
      induction xs with
      | nil => rfl
      | cons y ys ih =>
        simp only [List.map_cons]
        rw [transformCfiTy_compose hle y, ih]
    calc
      s1.args.map (transformCfiTy m2)
          = (s1.args.map (transformCfiTy m1)).map (transformCfiTy m2) := (hmap s1.args).symm
      _ = (s2.args.map (transformCfiTy m1)).map (transformCfiTy m2) := by rw [hargs]
      _ = s2.args.map (transformCfiTy m2) := hmap s2.args

/-- Coarsening preserves non-ZST parameter arity across all 4 lattice points. -/
theorem cfi_typeid_preserves_arity (m : CfiMode) (sig : CfiFnSig) :
    (cfiTypeId m sig).args.length = sig.args.length :=
  List.length_map (transformCfiTy m)

/-- 64-bit word modulus (`2^64`) and 61-bit shift (`2^61`) for x86-64 8-byte-stride
`LowerTypeTests` jump-table rotation (`@llvm.fshl.i64(d, d, 61)` = rotate right by 3). -/
def word64 : Nat := 18446744073709551616
def pow2_61 : Nat := 2305843009213693952

/-- Exact 64-bit rotate-right-by-3 (`@llvm.fshl.i64(d, d, 61)`). -/
def ror3_64 (d : Nat) : Nat :=
  (d % word64) / 8 + ((d % word64) % 8) * pow2_61

/-- `LowerTypeTests` jump-table membership check for a table of `slotCount` 8-byte slots
rooted at `jtBase` (`addr ∈ [0, 2^64)`):
- For `slotCount = 1`, singleton `icmp eq ptr %f, @.cfi.jumptable`.
- For general `slotCount`, `(ror3 ((addr - jtBase) mod 2^64)) < slotCount`. -/
def lowerTypeTestsCheck (jtBase slotCount addr : Nat) : Bool :=
  if slotCount == 1 then
    addr == jtBase
  else
    let diff := (addr + (word64 - jtBase % word64)) % word64
    decide (ror3_64 diff < slotCount)

/-- Exact equivalence of the `ror3_64` check: for `d < 2^64` and `slotCount ≤ 2^61`,
`ror3_64 d < slotCount` holds if and only if `d` is 8-byte aligned (`d % 8 = 0`) and
its slot index `d / 8` is strictly less than `slotCount`. -/
theorem ror3_64_lt_iff {d slotCount : Nat} (hd : d < word64) (hn : slotCount ≤ pow2_61) :
    ror3_64 d < slotCount ↔ d % 8 = 0 ∧ d / 8 < slotCount := by
  unfold ror3_64
  rw [Nat.mod_eq_of_lt hd]
  constructor
  · intro hlt
    have hrem : d % 8 = 0 := nat_eq_zero_of_mul_add_lt hn hlt
    rw [hrem, Nat.zero_mul, Nat.add_zero] at hlt
    exact ⟨hrem, hlt⟩
  · intro ⟨hrem, hdiv⟩
    rw [hrem, Nat.zero_mul, Nat.add_zero]
    exact hdiv

/-- **Jump-Table Exactness (`cfi_jump_table_accepts_iff_matching_type_id`)**:
For any jump table with `0 < slotCount ≤ 2^61` at base `jtBase < 2^64` (no 64-bit wraparound:
`jtBase + 8 * slotCount ≤ 2^64`), `lowerTypeTestsCheck jtBase slotCount addr = true` holds
if and only if `addr` equals `jtBase + 8 * k` for some valid slot index `k < slotCount`. -/
theorem cfi_jump_table_accepts_iff_matching_type_id
    (jtBase slotCount addr : Nat)
    (hBase : jtBase < word64)
    (hAddr : addr < word64)
    (_hPos : 0 < slotCount)
    (hBound : slotCount ≤ pow2_61)
    (hNoWrap : jtBase + 8 * slotCount ≤ word64) :
    lowerTypeTestsCheck jtBase slotCount addr = true ↔
      ∃ k, k < slotCount ∧ addr = jtBase + 8 * k := by
  unfold lowerTypeTestsCheck
  cases hOne : (slotCount == 1) with
  | true =>
    have hS : slotCount = 1 := eq_of_beq hOne
    subst hS
    simp only [↓reduceIte, beq_iff_eq]
    constructor
    · intro heq
      exact ⟨0, Nat.zero_lt_one, by rw [Nat.mul_zero, Nat.add_zero]; exact heq⟩
    · intro ⟨k, hk, heq⟩
      cases k with
      | zero => simpa using heq
      | succ k' => exact False.elim (Nat.not_lt_zero k' (Nat.lt_of_succ_lt_succ hk))
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt hBase]
    have hDiffLt : (addr + (word64 - jtBase)) % word64 < word64 :=
      Nat.mod_lt _ (by decide : 0 < word64)
    rw [ror3_64_lt_iff hDiffLt hBound]
    constructor
    · intro ⟨hMod8, hDivLt⟩
      let d := (addr + (word64 - jtBase)) % word64
      let k := d / 8
      have hd_eq : d = 8 * k := by
        have hdm := Nat.div_add_mod d 8
        rw [hMod8, Nat.add_zero] at hdm
        exact hdm.symm
      have h8k_lt : 8 * k < word64 := by
        rw [← hd_eq]
        exact hDiffLt
      have hSumLt : jtBase + 8 * k < word64 := by
        have hstep : 8 * k < 8 * slotCount := by
          have hk1 : k + 1 ≤ slotCount := Nat.succ_le_of_lt hDivLt
          have hmul : 8 * (k + 1) ≤ 8 * slotCount := Nat.mul_le_mul_left 8 hk1
          have hlt8 : 8 * k < 8 * (k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            exact Nat.lt_add_of_pos_right (by decide : 0 < 8)
          exact Nat.lt_of_lt_of_le hlt8 hmul
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hstep jtBase) hNoWrap
      have hEq : addr = jtBase + 8 * k := by
        have hback : ((jtBase + 8 * k) % word64 + (word64 - jtBase)) % word64 = 8 * k :=
          nat_add_sub_cancel_mod hBase h8k_lt
        rw [Nat.mod_eq_of_lt hSumLt] at hback
        have hSame : (addr + (word64 - jtBase)) % word64 =
            ((jtBase + 8 * k) + (word64 - jtBase)) % word64 :=
          hd_eq.trans hback.symm
        have hAddBase : ∀ x, x < word64 →
            (((x + (word64 - jtBase)) % word64) + jtBase) % word64 = x := by
          intro x hx
          rw [Nat.mod_add_mod]
          have hassoc : (x + (word64 - jtBase)) + jtBase = x + word64 := by
            rw [Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hBase)]
          rw [hassoc, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
        calc
          addr = (((addr + (word64 - jtBase)) % word64) + jtBase) % word64 :=
            (hAddBase addr hAddr).symm
          _ = ((((jtBase + 8 * k) + (word64 - jtBase)) % word64) + jtBase) % word64 := by
            rw [hSame]
          _ = jtBase + 8 * k := hAddBase (jtBase + 8 * k) hSumLt
      exact ⟨k, hDivLt, hEq⟩
    · intro ⟨k, hk, heq⟩
      subst heq
      have h8k_lt : 8 * k < word64 := by
        have hk1 : k + 1 ≤ slotCount := Nat.succ_le_of_lt hk
        have hmul : 8 * (k + 1) ≤ 8 * slotCount := Nat.mul_le_mul_left 8 hk1
        have hlt8 : 8 * k < 8 * (k + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.lt_add_of_pos_right (by decide : 0 < 8)
        have hltS : 8 * k < 8 * slotCount := Nat.lt_of_lt_of_le hlt8 hmul
        exact Nat.lt_of_lt_of_le hltS (Nat.le_trans (Nat.le_add_left (8 * slotCount) jtBase) hNoWrap)
      have hDiff : ((jtBase + 8 * k) + (word64 - jtBase)) % word64 = 8 * k := by
        have h := nat_add_sub_cancel_mod hBase h8k_lt
        rwa [Nat.mod_eq_of_lt hAddr] at h
      rw [hDiff]
      exact ⟨nat_mod_zero_of_mul_eight k, by rw [nat_div_eight_of_mul_eight]; exact hk⟩

/-- x86-64 KCFI preamble register encoding (`-Z sanitizer-kcfi-arity=yes` vs default):
Without `kcfi-arity`, every function preamble emits `movl $<hash>, %eax`.
With `kcfi-arity`, LLVM encodes register-passed parameter count in the destination register
(`0 -> %eax`, `1 -> %ecx`, `2 -> %edx`, `3 -> %ebx`, `4 -> %esi`, `5 -> %edi`, `6+ -> %ebp`). -/
inductive X86KcfiReg where
  | eax | ecx | edx | ebx | esi | edi | ebp
  deriving DecidableEq, Repr

def kcfiPreambleReg (arityEnabled : Bool) (regArgs : Nat) : X86KcfiReg :=
  if !arityEnabled then
    .eax
  else
    match regArgs with
    | 0 => .eax
    | 1 => .ecx
    | 2 => .edx
    | 3 => .ebx
    | 4 => .esi
    | 5 => .edi
    | _ => .ebp

def sigTargetI32Ptr : CfiFnSig := ⟨.base .tyI32, [.base (.tyRawPtr false .tyI32)]⟩
def sigTargetU8Ptr  : CfiFnSig := ⟨.base .tyI32, [.base (.tyRawPtr false .tyU8)]⟩
def sigTargetTwoArgs : CfiFnSig := ⟨.base .tyI32, [.base .tyI32, .base .tyI32]⟩

/-- **Theorem 2 (`cfi_generalize_strictly_coarser_and_arity_preserving`)**:
1. Lattice coarsening is monotone for all `m1 ≤ m2`.
2. Every lattice point preserves non-ZST parameter arity (never merges 1-arg and 2-arg signatures).
3. Pointer generalization is strictly coarser than default CFI (`target_i32_ptr` vs `target_u8_ptr`).
4. `-Z sanitizer-kcfi-arity=yes` separates 0-, 1-, 2-, and 3-arg x86-64 KCFI preambles into
   distinct registers (`%eax`, `%ecx`, `%edx`, `%ebx`), whereas default KCFI collapses all to `%eax`. -/
theorem cfi_generalize_strictly_coarser_and_arity_preserving :
    (∀ m1 m2 s1 s2, m1.le m2 → cfiTypeId m1 s1 = cfiTypeId m1 s2 →
      cfiTypeId m2 s1 = cfiTypeId m2 s2) ∧
    (∀ m sig, (cfiTypeId m sig).args.length = sig.args.length) ∧
    (cfiTypeId CfiMode.raw sigTargetI32Ptr ≠ cfiTypeId CfiMode.raw sigTargetU8Ptr ∧
     cfiTypeId CfiMode.generalized sigTargetI32Ptr = cfiTypeId CfiMode.generalized sigTargetU8Ptr ∧
     cfiTypeId CfiMode.generalized sigTargetI32Ptr ≠ cfiTypeId CfiMode.generalized sigTargetTwoArgs) ∧
    (kcfiPreambleReg false 1 = .eax ∧ kcfiPreambleReg false 2 = .eax ∧
     kcfiPreambleReg true 0 = .eax ∧ kcfiPreambleReg true 1 = .ecx ∧
     kcfiPreambleReg true 2 = .edx ∧ kcfiPreambleReg true 3 = .ebx) := by
  refine ⟨fun _ _ s1 s2 hle heq => cfi_mode_coarsening_monotone hle s1 s2 heq,
          cfi_typeid_preserves_arity,
          ⟨by decide, rfl, by decide⟩,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Counterexample 2 (`ce2_cfi_generalize_pointers_admits_cross_pointee_type_confusion`)**:
Under `-Z sanitizer-cfi-generalize-pointers=yes`, `target_u8_ptr` (`*const u8 -> i32`) shares
the generalized type ID with `target_i32_ptr` (`*const i32 -> i32`), placing both into a 2-slot
jump table (`jtBase` and `jtBase + 8`) where `lowerTypeTestsCheck` accepts `target_u8_ptr` at a
`call_indirect_i32_ptr` call site (while default CFI's 1-slot table rejects it and rejects
misaligned mid-slot jumps `jtBase + 1`). -/
theorem ce2_cfi_generalize_pointers_admits_cross_pointee_type_confusion :
    let jtBase : Nat := 4096
    let addrI32 : Nat := jtBase
    let addrU8  : Nat := jtBase + 8
    let addrMisaligned : Nat := jtBase + 1
    cfiTypeId CfiMode.raw sigTargetI32Ptr ≠ cfiTypeId CfiMode.raw sigTargetU8Ptr ∧
    cfiTypeId CfiMode.generalized sigTargetI32Ptr = cfiTypeId CfiMode.generalized sigTargetU8Ptr ∧
    lowerTypeTestsCheck jtBase 1 addrU8 = false ∧
    lowerTypeTestsCheck jtBase 2 addrI32 = true ∧
    lowerTypeTestsCheck jtBase 2 addrU8 = true ∧
    lowerTypeTestsCheck jtBase 2 addrMisaligned = false := by
  refine ⟨by decide, rfl, rfl, by decide, by decide, by decide⟩

/-! ## Section 3: `SanitizerIgnoreList` Blame Algebra & `#[sanitize(...)]` Composition -/

/-- Exact mirror of `compiler/rustc_sanitizers/src/ignorelist/ffi.rs:9-27`:
`Blame { file_idx, line_no }` with `NONE = (0, 0)`, `is_some ↔ line_no ≠ 0`,
and lexicographic order `(file_idx, line_no)`. -/
structure Blame where
  fileIdx : Nat
  lineNo : Nat
  deriving DecidableEq, Repr

def Blame.none : Blame := ⟨0, 0⟩

def Blame.isSome (b : Blame) : Bool := b.lineNo != 0

def Blame.gt (a b : Blame) : Bool :=
  decide (a.fileIdx > b.fileIdx ∨ (a.fileIdx = b.fileIdx ∧ a.lineNo > b.lineNo))

def Blame.max (a b : Blame) : Blame :=
  if Blame.gt a b then a else b

/-- Exact mirror of `compiler/rustc_sanitizers/src/ignorelist/mod.rs:8-10`:
`no_san.is_some() && (san.is_none() || no_san > san)`. -/
def isBlameIgnored (noSan san : Blame) : Bool :=
  noSan.isSome && (!san.isSome || Blame.gt noSan san)

/-- Sanitizer kinds from `compiler/rustc_structures/src/sanitizer_set.rs:11-26`. -/
inductive SanitizerKind where
  | address
  | kernelAddress
  | memory
  | thread
  | hwAddress
  | kernelHwAddress
  | cfi
  | kcfi
  | safeStack
  | shadowCallStack
  | memTag
  | realtime
  deriving DecidableEq, Repr

/-- Whether `SanitizerIgnoreList::filter_instance_sanitizers` (`ignorelist/mod.rs:111-159`)
actually filters this sanitizer (`FIXME` on line 151 omits `SAFESTACK`, `SHADOWCALLSTACK`,
`MEMTAG`, and `REALTIME`). -/
def isFilteredByIgnorelist : SanitizerKind → Bool
  | .address | .kernelAddress | .memory | .thread | .hwAddress | .kernelHwAddress
  | .cfi | .kcfi => true
  | .safeStack | .shadowCallStack | .memTag | .realtime => false

/-- Four query axes evaluated by `SanitizerIgnoreList::instance_blame` (`ignorelist/mod.rs:91-96`):
mangled `fun`, demangled `fun`, `src` filename, and crate `mainfile`. -/
structure FourAxisBlame where
  funMangledNoSan : Blame
  funMangledSan : Blame
  funDemangledNoSan : Blame
  funDemangledSan : Blame
  srcNoSan : Blame
  srcSan : Blame
  mainfileNoSan : Blame
  mainfileSan : Blame
  deriving DecidableEq, Repr

/-- Exact aggregation in `instance_blame` (`ignorelist/mod.rs:83-98`):
componentwise lexicographic maximum across the 4 query axes. -/
def aggregateFourAxisBlame (q : FourAxisBlame) : Blame × Blame :=
  let noSan :=
    Blame.max (Blame.max (Blame.max q.funMangledNoSan q.funDemangledNoSan) q.srcNoSan)
      q.mainfileNoSan
  let san :=
    Blame.max (Blame.max (Blame.max q.funMangledSan q.funDemangledSan) q.srcSan)
      q.mainfileSan
  (noSan, san)

/-- Composition of session `-Z sanitizer=...`, `#[sanitize(... = "off")]` attribute, and
`-Z sanitizer-ignorelist` matching `rustc_codegen_llvm/src/attributes.rs:158-170` and
`rustc_sanitizers/src/ignorelist/mod.rs:111-159`. -/
def effectiveSanitizerEnabled
    (kind : SanitizerKind)
    (sessEnabled : Bool)
    (attrDisabled : Bool)
    (blame : Blame × Blame) : Bool :=
  let afterAttr := sessEnabled && !attrDisabled
  if !afterAttr then
    false
  else if isFilteredByIgnorelist kind then
    !isBlameIgnored blame.1 blame.2
  else
    afterAttr

/-- `#[sanitize(s = "off")]` unconditionally disables instrumentation regardless of any
ignorelist `=sanitize` re-enable rule, because `tcx.sess.sanitizers() - sanitizer_fn_attr.disabled`
executes before `filter_instance_sanitizers` and ignorelist filtering can only remove sanitizers. -/
theorem attr_off_dominates_ignorelist (kind : SanitizerKind) (sess : Bool) (blame : Blame × Blame) :
    effectiveSanitizerEnabled kind sess true blame = false := by
  unfold effectiveSanitizerEnabled
  cases sess <;> rfl

/-- When both a disable rule (`noSan`) and a `=sanitize` rule (`san`) match in the same file,
last-match-wins holds: strictly later `san` re-enables instrumentation (`isBlameIgnored = false`),
strictly later `noSan` disables instrumentation (`isBlameIgnored = true`), and equal blame
resolves in favor of sanitizing (`isBlameIgnored = false`). -/
theorem isBlameIgnored_same_file_last_match_wins (f lNo lSan : Nat)
    (hNoPos : lNo ≠ 0) (hSanPos : lSan ≠ 0) :
    (lSan ≥ lNo → isBlameIgnored ⟨f, lNo⟩ ⟨f, lSan⟩ = false) ∧
    (lNo > lSan → isBlameIgnored ⟨f, lNo⟩ ⟨f, lSan⟩ = true) := by
  have hNoSome : (Blame.mk f lNo).isSome = true := by
    unfold Blame.isSome
    cases h : (lNo != 0) with
    | true => rfl
    | false =>
      exfalso
      have hz : lNo = 0 := by
        simp only [bne_eq_false_iff_eq] at h
        exact h
      exact hNoPos hz
  have hSanSome : (Blame.mk f lSan).isSome = true := by
    unfold Blame.isSome
    cases h : (lSan != 0) with
    | true => rfl
    | false =>
      exfalso
      have hz : lSan = 0 := by
        simp only [bne_eq_false_iff_eq] at h
        exact h
      exact hSanPos hz
  constructor
  · intro hge
    unfold isBlameIgnored
    rw [hNoSome, hSanSome]
    simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    unfold Blame.gt
    simp only [decide_eq_false_iff_not]
    intro hor
    cases hor with
    | inl hlt => exact Nat.lt_irrefl f hlt
    | inr hpair => exact Nat.not_lt.mpr hge hpair.2
  · intro hgt
    unfold isBlameIgnored
    rw [hNoSome, hSanSome]
    simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    unfold Blame.gt
    simp only [decide_eq_true_eq]
    exact Or.inr ⟨trivial, hgt⟩

/-- **FIXME Gap Theorem**: For the 4 sanitizers omitted in `filter_instance_sanitizers`
(`SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, `REALTIME`, `ignorelist/mod.rs:151-153`),
a matching ignorelist rule has zero effect on `effectiveSanitizerEnabled`. -/
theorem unfiltered_sanitizers_ignore_ignorelist (kind : SanitizerKind)
    (hUnfiltered : isFilteredByIgnorelist kind = false)
    (sess : Bool) (blame : Blame × Blame) :
    effectiveSanitizerEnabled kind sess false blame = sess := by
  unfold effectiveSanitizerEnabled
  cases sess with
  | false => rfl
  | true =>
    simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hUnfiltered]

/-- **Theorem 3 (`ignorelist_blame_and_attr_composition`)**:
Combines:
1. `#[sanitize(... = "off")]` dominance over any ignorelist `=sanitize` rule,
2. Same-file last-match-wins blame resolution (`isBlameIgnored`),
3. Unfiltered-sanitizer `FIXME` invariance for `SAFESTACK`/`SHADOWCALLSTACK`/`MEMTAG`/`REALTIME`,
4. Exact 4-function probe table (`normal_fn`, `attr_off_fn`, `ignorelist_excluded_fn`,
   `ignorelist_reenabled_fn`). -/
theorem ignorelist_blame_and_attr_composition :
    (∀ k s b, effectiveSanitizerEnabled k s true b = false) ∧
    (∀ f lNo lSan, lNo ≠ 0 → lSan ≠ 0 →
      (lSan ≥ lNo → isBlameIgnored ⟨f, lNo⟩ ⟨f, lSan⟩ = false) ∧
      (lNo > lSan → isBlameIgnored ⟨f, lNo⟩ ⟨f, lSan⟩ = true)) ∧
    (∀ k s b, isFilteredByIgnorelist k = false → effectiveSanitizerEnabled k s false b = s) ∧
    (effectiveSanitizerEnabled .address true false (Blame.none, Blame.none) = true ∧
     effectiveSanitizerEnabled .address true true  (Blame.none, ⟨0, 3⟩) = false ∧
     effectiveSanitizerEnabled .address true false (⟨0, 2⟩, Blame.none) = false ∧
     effectiveSanitizerEnabled .address true false (⟨0, 3⟩, ⟨0, 4⟩) = true) := by
  refine ⟨attr_off_dominates_ignorelist,
          isBlameIgnored_same_file_last_match_wins,
          fun k s b h => unfiltered_sanitizers_ignore_ignorelist k h s b,
          ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Naive (buggy) order-insensitive ignorelist model that forgets blame ordering and
ignores any function matching a plain rule, even if a later `=sanitize` rule re-enables it. -/
def naiveSetIgnored (noSan _san : Blame) : Bool := noSan.isSome

/-- **Counterexample 3 (`ce3_forgetting_blame_ordering_drops_later_sanitize_reenable_rule`)**:
For `ignorelist_reenabled_fn`, line 3 matches `fun:*ignorelist_reenabled_fn*` and line 4
matches `fun:*ignorelist_reenabled_fn*=sanitize`. Forgetting blame ordering misclassifies the
function as ignored (`true` -> ASan stripped), whereas `rustc`'s `is_blame_ignored` evaluates
to `false` (ASan preserved) even when aggregated across the 4 query axes (`fun` mangled/demangled,
`src`, `mainfile`). -/
theorem ce3_forgetting_blame_ordering_drops_later_sanitize_reenable_rule :
    let q : FourAxisBlame := {
      funMangledNoSan := ⟨0, 3⟩,
      funMangledSan := ⟨0, 4⟩,
      funDemangledNoSan := ⟨0, 3⟩,
      funDemangledSan := ⟨0, 4⟩,
      srcNoSan := Blame.none,
      srcSan := Blame.none,
      mainfileNoSan := Blame.none,
      mainfileSan := Blame.none
    }
    let agg := aggregateFourAxisBlame q
    naiveSetIgnored agg.1 agg.2 = true ∧
    isBlameIgnored agg.1 agg.2 = false ∧
    effectiveSanitizerEnabled .address true false agg = true := by
  exact ⟨rfl, rfl, rfl⟩

end SanitizerUbChecksAndCfiSoundness

#print axioms SanitizerUbChecksAndCfiSoundness.ubChecks_never_reject_well_defined_execution
#print axioms SanitizerUbChecksAndCfiSoundness.ubChecks_sound_no_false_positives
#print axioms SanitizerUbChecksAndCfiSoundness.cfi_jump_table_accepts_iff_matching_type_id
#print axioms SanitizerUbChecksAndCfiSoundness.cfi_generalize_strictly_coarser_and_arity_preserving
#print axioms SanitizerUbChecksAndCfiSoundness.ignorelist_blame_and_attr_composition
#print axioms SanitizerUbChecksAndCfiSoundness.ce1_ub_checks_miss_single_variant_bool_and_ptr_read_enum_ub
#print axioms SanitizerUbChecksAndCfiSoundness.ce2_cfi_generalize_pointers_admits_cross_pointee_type_confusion
#print axioms SanitizerUbChecksAndCfiSoundness.ce3_forgetting_blame_ordering_drops_later_sanitize_reenable_rule
