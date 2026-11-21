/-!
# Kernel-Checked Mechanization of `c_variadic`, Multi-Target `va_list` State Machines,
# Miri `VaList` Validation, and `#[unsafe(naked)]` Frame Contracts

Standalone constructive `Init`-only Lean `v4.34.1` development using only structural
induction, rewriting, kernel reduction, and `[propext, Quot.sound]`.
-/

namespace CVariadicVaListAndNakedAsmSoundness

/-! ## Section 1: C Default Promotions, `VaArgSafe`, and Miri `VaList` Heap -/

inductive PrimTy where
  | i8
  | u8
  | i16
  | u16
  | i32
  | u32
  | i64
  | u64
  | i128
  | u128
  | f32
  | f64
  | ptrVoid
  | ptrU8
  | ptrI8
  | ptrU32
  | bool
  | char
  deriving DecidableEq, Repr

structure CTargetProfile where
  cIntBits : Nat
  f32IsCDouble : Bool
  hasInt128 : Bool
  enableCVariadicInt128 : Bool
  deriving DecidableEq, Repr

def lp64SysV : CTargetProfile :=
  { cIntBits := 32, f32IsCDouble := false, hasInt128 := true, enableCVariadicInt128 := true }

def lp64SysVStable : CTargetProfile :=
  { cIntBits := 32, f32IsCDouble := false, hasInt128 := true, enableCVariadicInt128 := false }

def llp64Win64 : CTargetProfile :=
  { cIntBits := 32, f32IsCDouble := false, hasInt128 := false, enableCVariadicInt128 := false }

def avr16 : CTargetProfile :=
  { cIntBits := 16, f32IsCDouble := true, hasInt128 := false, enableCVariadicInt128 := false }

def cDefaultPromote (prof : CTargetProfile) (t : PrimTy) : PrimTy :=
  match t with
  | .i8 => .i32
  | .u8 => .u32
  | .bool => .i32
  | .i16 => if prof.cIntBits == 16 then .i16 else .i32
  | .u16 => if prof.cIntBits == 16 then .u16 else .u32
  | .f32 => if prof.f32IsCDouble then .f32 else .f64
  | _ => t

/-- Models `core::ffi::VaArgSafe` (`library/core/src/ffi/va_list.rs:313-485`). -/
def implementsVaArgSafe (prof : CTargetProfile) (t : PrimTy) : Bool :=
  match t with
  | .i8 | .u8 | .bool | .char => false
  | .i16 | .u16 => prof.cIntBits == 16
  | .f32 => prof.f32IsCDouble
  | .i128 | .u128 => prof.hasInt128 && prof.enableCVariadicInt128
  | .i32 | .u32 | .i64 | .u64 | .f64 | .ptrVoid | .ptrU8 | .ptrI8 | .ptrU32 => true

theorem vaArgSafe_excludes_default_promoted_types (prof : CTargetProfile) (t : PrimTy) :
    implementsVaArgSafe prof t = true → cDefaultPromote prof t = t := by
  intro h
  cases t with
  | i8 | u8 | bool | char => cases h
  | i16 =>
    dsimp only [implementsVaArgSafe] at h
    dsimp only [cDefaultPromote]
    simp only [h, ↓reduceIte]
  | u16 =>
    dsimp only [implementsVaArgSafe] at h
    dsimp only [cDefaultPromote]
    simp only [h, ↓reduceIte]
  | f32 =>
    dsimp only [implementsVaArgSafe] at h
    dsimp only [cDefaultPromote]
    simp only [h, ↓reduceIte]
  | i32 | u32 | i64 | u64 | i128 | u128 | f64 | ptrVoid | ptrU8 | ptrI8 | ptrU32 =>
    rfl

theorem vaArgSafe_lp64_excludes_promoted :
    implementsVaArgSafe lp64SysV .i8 = false ∧
    implementsVaArgSafe lp64SysV .u8 = false ∧
    implementsVaArgSafe lp64SysV .i16 = false ∧
    implementsVaArgSafe lp64SysV .u16 = false ∧
    implementsVaArgSafe lp64SysV .f32 = false ∧
    implementsVaArgSafe lp64SysV .bool = false ∧
    implementsVaArgSafe lp64SysV .char = false ∧
    implementsVaArgSafe lp64SysVStable .u128 = false ∧
    implementsVaArgSafe lp64SysV .u128 = true := by
  decide

def primSizeBytes : PrimTy → Nat
  | .i8 | .u8 | .bool => 1
  | .i16 | .u16 => 2
  | .i32 | .u32 | .f32 | .char => 4
  | .i64 | .u64 | .f64 | .ptrVoid | .ptrU8 | .ptrI8 | .ptrU32 => 8
  | .i128 | .u128 => 16

inductive VarArgCompat where
  | compatible
  | incompatible
  | castIntTo (sourceIsSigned : Bool)
  deriving DecidableEq, Repr

/-- Models `validate_c_variadic_compatible_ty` (`rustc_const_eval/src/interpret/intrinsics.rs:783-858`). -/
def checkVarArgCompat (caller callee : PrimTy) : VarArgCompat :=
  if caller == callee then
    .compatible
  else if primSizeBytes caller != primSizeBytes callee then
    .incompatible
  else
    match caller, callee with
    | .i8, .i8 | .i16, .i16 | .i32, .i32 | .i64, .i64 | .i128, .i128 => .compatible
    | .u8, .u8 | .u16, .u16 | .u32, .u32 | .u64, .u64 | .u128, .u128 => .compatible
    | .i8, .u8 | .i16, .u16 | .i32, .u32 | .i64, .u64 | .i128, .u128 =>
      .castIntTo true
    | .u8, .i8 | .u16, .i16 | .u32, .i32 | .u64, .i64 | .u128, .i128 =>
      .castIntTo false
    | .ptrVoid, .ptrU8 | .ptrVoid, .ptrI8
    | .ptrU8, .ptrVoid | .ptrI8, .ptrVoid
    | .ptrU8, .ptrI8 | .ptrI8, .ptrU8 => .compatible
    | _, _ => .incompatible

structure PassedVarArg where
  ty : PrimTy
  rawVal : Nat
  isNegativeSigned : Bool
  deriving DecidableEq, Repr

inductive MiriError where
  | vaArgOutOfBoundsUB
  | vaArgTypeMismatchUB
  | vaArgValueMismatchUB
  | invalidVaListPtrUB
  deriving DecidableEq, Repr

/-- Models `validate_c_variadic_argument` (`rustc_const_eval/src/interpret/intrinsics.rs:735-768`). -/
def validateCVariadicArg (arg : PassedVarArg) (callee : PrimTy) : Except MiriError Unit :=
  match checkVarArgCompat arg.ty callee with
  | .compatible => .ok ()
  | .incompatible => .error .vaArgTypeMismatchUB
  | .castIntTo _sourceIsSigned =>
    if arg.isNegativeSigned then .error .vaArgValueMismatchUB else .ok ()

/-- Models Miri's `AllocKind::VaList` global table (`memory.rs:939-941, 1017-1052`,
    `intrinsics.rs:667-717`): every `va_arg` step invalidates `key` and allocates `nextId`. -/
structure MiriHeap where
  nextId : Nat
  entries : List (Nat × List PassedVarArg)
  deriving DecidableEq, Repr

noncomputable def lookupVaList : List (Nat × List PassedVarArg) → Nat → Option (List PassedVarArg)
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else lookupVaList rest key

noncomputable def removeVaList : List (Nat × List PassedVarArg) → Nat → List (Nat × List PassedVarArg)
  | [], _ => []
  | (k, v) :: rest, key => if k == key then removeVaList rest key else (k, v) :: removeVaList rest key

def miriVaStart (h : MiriHeap) (args : List PassedVarArg) : Nat × MiriHeap :=
  let key := h.nextId
  (key, { nextId := key + 1, entries := (key, args) :: h.entries })

noncomputable def miriVaCopy (h : MiriHeap) (srcKey : Nat) : Except MiriError (Nat × MiriHeap) :=
  match lookupVaList h.entries srcKey with
  | none => .error .invalidVaListPtrUB
  | some q =>
    let newKey := h.nextId
    .ok (newKey, { nextId := newKey + 1, entries := (newKey, q) :: h.entries })

noncomputable def miriVaEnd (h : MiriHeap) (key : Nat) : Except MiriError MiriHeap :=
  match lookupVaList h.entries key with
  | none => .error .invalidVaListPtrUB
  | some _ => .ok { h with entries := removeVaList h.entries key }

noncomputable def miriVaArg (h : MiriHeap) (key : Nat) (calleeTy : PrimTy) :
    Except MiriError (PassedVarArg × Nat × MiriHeap) :=
  match lookupVaList h.entries key with
  | none => .error .invalidVaListPtrUB
  | some q =>
    let h' := { h with entries := removeVaList h.entries key }
    match q with
    | [] => .error .vaArgOutOfBoundsUB
    | arg :: rest =>
      match validateCVariadicArg arg calleeTy with
      | .error e => .error e
      | .ok () =>
        let newKey := h'.nextId
        .ok (arg, newKey, { nextId := newKey + 1, entries := (newKey, rest) :: h'.entries })

def AllKeysLt (bound : Nat) (xs : List (Nat × List PassedVarArg)) : Prop :=
  ∀ k, lookupVaList xs k ≠ none → k < bound

private theorem nat_beq_self (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

private theorem lookupVaList_remove_ne (xs : List (Nat × List PassedVarArg)) (k1 k2 : Nat)
    (hne : k1 ≠ k2) :
    lookupVaList (removeVaList xs k1) k2 = lookupVaList xs k2 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk k v =>
      by_cases hk : k = k1
      · subst hk
        have hSelf : (k == k) = true := nat_beq_self k
        have hne2 : (k == k2) = false := by
          cases hb : (k == k2)
          · rfl
          · exact False.elim (hne (beq_iff_eq.mp hb))
        dsimp only [removeVaList]
        simp only [hSelf, ↓reduceIte]
        dsimp only [lookupVaList]
        simp only [hne2, Bool.false_eq_true, ↓reduceIte]
        exact ih
      · have hne1 : (k == k1) = false := by
          cases hb : (k == k1)
          · rfl
          · exact False.elim (hk (beq_iff_eq.mp hb))
        dsimp only [removeVaList]
        simp only [hne1, Bool.false_eq_true, ↓reduceIte]
        dsimp only [lookupVaList]
        cases (k == k2)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih
        · simp only [↓reduceIte]

private theorem lookupVaList_remove_self (xs : List (Nat × List PassedVarArg)) (k : Nat) :
    lookupVaList (removeVaList xs k) k = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk k0 v0 =>
      by_cases hk : k0 = k
      · subst hk
        have hSelf : (k0 == k0) = true := nat_beq_self k0
        dsimp only [removeVaList]
        simp only [hSelf, ↓reduceIte]
        exact ih
      · have hne : (k0 == k) = false := by
          cases hb : (k0 == k)
          · rfl
          · exact False.elim (hk (beq_iff_eq.mp hb))
        dsimp only [removeVaList]
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        dsimp only [lookupVaList]
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact ih

theorem miri_vaCopy_non_interference (h : MiriHeap) (srcKey : Nat) (q : List PassedVarArg)
    (hAll : AllKeysLt h.nextId h.entries)
    (hLookup : lookupVaList h.entries srcKey = some q) :
    ∃ copyKey h1,
      miriVaCopy h srcKey = .ok (copyKey, h1) ∧
      copyKey ≠ srcKey ∧
      lookupVaList h1.entries copyKey = some q ∧
      lookupVaList h1.entries srcKey = some q := by
  have hLt : srcKey < h.nextId := by
    apply hAll
    rw [hLookup]
    intro hc
    cases hc
  have hNe : h.nextId ≠ srcKey := Nat.ne_of_gt hLt
  have hNeB : (h.nextId == srcKey) = false := by
    cases hb : (h.nextId == srcKey)
    · rfl
    · exact False.elim (hNe (beq_iff_eq.mp hb))
  have hSelf : (h.nextId == h.nextId) = true := nat_beq_self h.nextId
  refine ⟨h.nextId, { nextId := h.nextId + 1, entries := (h.nextId, q) :: h.entries }, ?_, hNe, ?_, ?_⟩
  · dsimp only [miriVaCopy]
    rw [hLookup]
  · dsimp only [lookupVaList]
    simp only [hSelf, ↓reduceIte]
  · dsimp only [lookupVaList]
    simp only [hNeB, Bool.false_eq_true, ↓reduceIte]
    exact hLookup

theorem miri_use_after_vaEnd_is_ub (h : MiriHeap) (key : Nat) (h1 : MiriHeap)
    (calleeTy : PrimTy) (hEnd : miriVaEnd h key = .ok h1) :
    miriVaArg h1 key calleeTy = .error .invalidVaListPtrUB := by
  dsimp only [miriVaEnd] at hEnd
  cases hL : lookupVaList h.entries key with
  | none =>
    rw [hL] at hEnd
    cases hEnd
  | some q =>
    rw [hL] at hEnd
    cases hEnd
    dsimp only [miriVaArg]
    rw [lookupVaList_remove_self]

theorem miri_raw_memcpy_after_step_is_ub (h : MiriHeap) (key newKey : Nat)
    (arg : PassedVarArg) (h1 : MiriHeap) (calleeTy1 calleeTy2 : PrimTy)
    (hAll : AllKeysLt h.nextId h.entries)
    (hStep : miriVaArg h key calleeTy1 = .ok (arg, newKey, h1)) :
    miriVaArg h1 key calleeTy2 = .error .invalidVaListPtrUB := by
  dsimp only [miriVaArg] at hStep
  cases hL : lookupVaList h.entries key with
  | none =>
    rw [hL] at hStep
    cases hStep
  | some q =>
    have hLt : key < h.nextId := by
      apply hAll
      rw [hL]
      intro hc
      cases hc
    have hNe : h.nextId ≠ key := Nat.ne_of_gt hLt
    have hNeB : (h.nextId == key) = false := by
      cases hb : (h.nextId == key)
      · rfl
      · exact False.elim (hNe (beq_iff_eq.mp hb))
    rw [hL] at hStep
    dsimp only at hStep
    cases q with
    | nil => cases hStep
    | cons hd tl =>
      dsimp only at hStep
      cases hV : validateCVariadicArg hd calleeTy1 with
      | error e =>
        rw [hV] at hStep
        cases hStep
      | ok u =>
        rw [hV] at hStep
        dsimp only at hStep
        cases hStep
        dsimp only [miriVaArg, lookupVaList]
        simp only [hNeB, Bool.false_eq_true, ↓reduceIte]
        rw [lookupVaList_remove_self]

/-! ## Section 2: System V AMD64 `SysVVaList` State Machine & Universal Exactness -/

inductive RegSaveSlot where
  | unsaved
  | saved (word : UInt64)
  deriving DecidableEq, Repr

inductive SysVArgTy where
  | gp64
  | fp64
  | int128
  deriving DecidableEq, Repr

inductive SysVArgVal where
  | gp64 (v : UInt64)
  | fp64 (v : UInt64)
  | int128 (lo hi : UInt64)
  deriving DecidableEq, Repr

def SysVArgVal.ty : SysVArgVal → SysVArgTy
  | .gp64 _ => .gp64
  | .fp64 _ => .fp64
  | .int128 _ _ => .int128

noncomputable def countFpArgs : List SysVArgVal → Nat
  | [] => 0
  | .fp64 _ :: rest => countFpArgs rest + 1
  | _ :: rest => countFpArgs rest

/-- Models the callee register save area (`[0..48)` GP, `[48..176)` XMM) and caller overflow stack. -/
structure SysVCallFrame where
  gpSlots : Nat → UInt64
  fpSlots : Nat → RegSaveSlot
  overflowWords : Nat → UInt64
  callerAl : Nat

def emptySysVCallFrame (callerAl : Nat) : SysVCallFrame :=
  { gpSlots := fun _ => 0
    fpSlots := fun _ => .unsaved
    overflowWords := fun _ => 0
    callerAl := callerAl }

/-- Models `struct __va_list_tag` (`gp_offset`, `fp_offset`, and 8-byte `overflowIdx`). -/
structure SysVVaList where
  gpOffset : Nat
  fpOffset : Nat
  overflowIdx : Nat
  deriving DecidableEq, Repr

def sysvInitVaList (fixedGp fixedFp : Nat) : SysVVaList :=
  { gpOffset := fixedGp * 8
    fpOffset := 48 + fixedFp * 16
    overflowIdx := 0 }

def vaCopy (ap : SysVVaList) : SysVVaList := ap

inductive SysVVaError where
  | unsavedXmmReadUB
  | unexpectedArgMismatch
  deriving DecidableEq, Repr

def alignUpEven (n : Nat) : Nat :=
  if n % 2 == 0 then n else n + 1

private theorem le_alignUpEven (n : Nat) : n ≤ alignUpEven n := by
  unfold alignUpEven
  cases (n % 2 == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_succ n
  · simp only [↓reduceIte]
    exact Nat.le_refl n

/-- Models `emit_x86_64_sysv64_va_arg` (`compiler/rustc_codegen_llvm/src/va_arg.rs:552-854`):
    - `.gp64`: fits in GP save area iff `gpOffset ≤ 40`; else reads `overflowWords[overflowIdx]`.
    - `.fp64`: fits in FP save area iff `fpOffset ≤ 160` (and requires `.saved` per caller `%al`).
    - `.int128`: fits in GP save area iff `gpOffset ≤ 32` (uses 8-byte-aligned `copy_to_temporary_if_more_aligned`
      without rounding `gpOffset` to 16); else falls back to 16-byte-aligned `overflowWords` (`alignUpEven`)
      while keeping `gpOffset` unchanged so a later `.gp64` can still backfill `%r9` (`gpOffset = 40`). -/
def sysvVaNextArg (frame : SysVCallFrame) (ap : SysVVaList) (ty : SysVArgTy) :
    Except SysVVaError (SysVArgVal × SysVVaList) :=
  match ty with
  | .gp64 =>
    if ap.gpOffset ≤ 40 then
      let slot := ap.gpOffset / 8
      .ok (.gp64 (frame.gpSlots slot), { ap with gpOffset := ap.gpOffset + 8 })
    else
      .ok (.gp64 (frame.overflowWords ap.overflowIdx), { ap with overflowIdx := ap.overflowIdx + 1 })
  | .fp64 =>
    if ap.fpOffset ≤ 160 then
      let slot := (ap.fpOffset - 48) / 16
      match frame.fpSlots slot with
      | .unsaved => .error .unsavedXmmReadUB
      | .saved w => .ok (.fp64 w, { ap with fpOffset := ap.fpOffset + 16 })
    else
      .ok (.fp64 (frame.overflowWords ap.overflowIdx), { ap with overflowIdx := ap.overflowIdx + 1 })
  | .int128 =>
    if ap.gpOffset ≤ 32 then
      let slot := ap.gpOffset / 8
      let lo := frame.gpSlots slot
      let hi := frame.gpSlots (slot + 1)
      .ok (.int128 lo hi, { ap with gpOffset := ap.gpOffset + 16 })
    else
      let aligned := alignUpEven ap.overflowIdx
      let lo := frame.overflowWords aligned
      let hi := frame.overflowWords (aligned + 1)
      .ok (.int128 lo hi, { ap with overflowIdx := aligned + 2 })

noncomputable def sysvVaNextArgs (frame : SysVCallFrame) (ap : SysVVaList) :
    List SysVArgTy → Except SysVVaError (List SysVArgVal × SysVVaList)
  | [] => .ok ([], ap)
  | ty :: rest =>
    match sysvVaNextArg frame ap ty with
    | .error e => .error e
    | .ok (v, ap') =>
      match sysvVaNextArgs frame ap' rest with
      | .error e => .error e
      | .ok (vs, ap'') => .ok (v :: vs, ap'')

noncomputable def sysvPackLoop (gpOff fpOff ovIdx : Nat) : List SysVArgVal → SysVCallFrame → SysVCallFrame
  | [], acc => acc
  | .gp64 v :: rest, acc =>
    if gpOff ≤ 40 then
      let slot := gpOff / 8
      let acc' := { acc with gpSlots := fun i => if i == slot then v else acc.gpSlots i }
      sysvPackLoop (gpOff + 8) fpOff ovIdx rest acc'
    else
      let acc' := { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k }
      sysvPackLoop gpOff fpOff (ovIdx + 1) rest acc'
  | .fp64 v :: rest, acc =>
    if fpOff ≤ 160 then
      let slot := (fpOff - 48) / 16
      let slotVal := if slot < acc.callerAl then RegSaveSlot.saved v else RegSaveSlot.unsaved
      let acc' := { acc with fpSlots := fun i => if i == slot then slotVal else acc.fpSlots i }
      sysvPackLoop gpOff (fpOff + 16) ovIdx rest acc'
    else
      let acc' := { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k }
      sysvPackLoop gpOff fpOff (ovIdx + 1) rest acc'
  | .int128 lo hi :: rest, acc =>
    if gpOff ≤ 32 then
      let slot := gpOff / 8
      let acc' := {
        acc with
        gpSlots := fun i =>
          if i == slot then lo
          else if i == slot + 1 then hi
          else acc.gpSlots i
      }
      sysvPackLoop (gpOff + 16) fpOff ovIdx rest acc'
    else
      let aligned := alignUpEven ovIdx
      let acc' := {
        acc with
        overflowWords := fun k =>
          if k == aligned then lo
          else if k == aligned + 1 then hi
          else acc.overflowWords k
      }
      sysvPackLoop gpOff fpOff (aligned + 2) rest acc'

noncomputable def sysvPackVariadicCall (fixedGp fixedFp callerAl : Nat) (args : List SysVArgVal) : SysVCallFrame :=
  sysvPackLoop (fixedGp * 8) (48 + fixedFp * 16) 0 args (emptySysVCallFrame callerAl)

private theorem div8_add8 (n : Nat) : (n + 8) / 8 = n / 8 + 1 := by
  change (n + 1 * 8) / 8 = n / 8 + 1
  exact Nat.add_mul_div_right n 1 (by decide)

private theorem div8_add16 (n : Nat) : (n + 16) / 8 = n / 8 + 2 := by
  change (n + 2 * 8) / 8 = n / 8 + 2
  exact Nat.add_mul_div_right n 2 (by decide)

private theorem div16_sub48_add16 (n : Nat) (h : 48 ≤ n) :
    ((n + 16) - 48) / 16 = (n - 48) / 16 + 1 := by
  have h1 : (n + 16) - 48 = (n - 48) + 1 * 16 := by
    rw [Nat.sub_add_comm h]
  rw [h1]
  exact Nat.add_mul_div_right (n - 48) 1 (by decide)

private theorem beq_nat_false_of_lt {a b : Nat} (h : a < b) : (a == b) = false := by
  cases hb : (a == b)
  · rfl
  · exact False.elim (Nat.lt_irrefl a (beq_iff_eq.mp hb ▸ h))

private theorem sysvPackLoop_frame
    (gpOff fpOff ovIdx : Nat) (args : List SysVArgVal) (acc : SysVCallFrame)
    (hFp : 48 ≤ fpOff) :
    (∀ i, i < gpOff / 8 → (sysvPackLoop gpOff fpOff ovIdx args acc).gpSlots i = acc.gpSlots i) ∧
    (∀ i, i < (fpOff - 48) / 16 → (sysvPackLoop gpOff fpOff ovIdx args acc).fpSlots i = acc.fpSlots i) ∧
    (∀ k, k < ovIdx → (sysvPackLoop gpOff fpOff ovIdx args acc).overflowWords k = acc.overflowWords k) ∧
    (sysvPackLoop gpOff fpOff ovIdx args acc).callerAl = acc.callerAl := by
  induction args generalizing gpOff fpOff ovIdx acc with
  | nil =>
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | cons hd tl ih =>
    cases hd with
    | gp64 v =>
      dsimp only [sysvPackLoop]
      by_cases hGp : gpOff ≤ 40
      · simp only [hGp, ite_true]
        have hSub := ih (gpOff + 8) fpOff ovIdx
          { acc with gpSlots := fun i => if i == gpOff / 8 then v else acc.gpSlots i } hFp
        refine ⟨?_, hSub.2.1, hSub.2.2.1, hSub.2.2.2⟩
        intro i hi
        have hi' : i < (gpOff + 8) / 8 := by
          rw [div8_add8]
          exact Nat.lt_succ_of_lt hi
        rw [hSub.1 i hi']
        dsimp only
        simp only [beq_nat_false_of_lt hi, Bool.false_eq_true, ↓reduceIte]
      · simp only [hGp, ite_false]
        have hSub := ih gpOff fpOff (ovIdx + 1)
          { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k } hFp
        refine ⟨hSub.1, hSub.2.1, ?_, hSub.2.2.2⟩
        intro k hk
        rw [hSub.2.2.1 k (Nat.lt_succ_of_lt hk)]
        dsimp only
        simp only [beq_nat_false_of_lt hk, Bool.false_eq_true, ↓reduceIte]
    | fp64 v =>
      dsimp only [sysvPackLoop]
      by_cases hF : fpOff ≤ 160
      · simp only [hF, ite_true]
        have hFp' : 48 ≤ fpOff + 16 := Nat.le_trans hFp (Nat.le_add_right fpOff 16)
        have hSub := ih gpOff (fpOff + 16) ovIdx
          { acc with fpSlots := fun i =>
              if i == (fpOff - 48) / 16 then
                if (fpOff - 48) / 16 < acc.callerAl then RegSaveSlot.saved v else RegSaveSlot.unsaved
              else acc.fpSlots i } hFp'
        refine ⟨hSub.1, ?_, hSub.2.2.1, hSub.2.2.2⟩
        intro i hi
        have hi' : i < (fpOff + 16 - 48) / 16 := by
          rw [div16_sub48_add16 fpOff hFp]
          exact Nat.lt_succ_of_lt hi
        rw [hSub.2.1 i hi']
        dsimp only
        simp only [beq_nat_false_of_lt hi, Bool.false_eq_true, ↓reduceIte]
      · simp only [hF, ite_false]
        have hSub := ih gpOff fpOff (ovIdx + 1)
          { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k } hFp
        refine ⟨hSub.1, hSub.2.1, ?_, hSub.2.2.2⟩
        intro k hk
        rw [hSub.2.2.1 k (Nat.lt_succ_of_lt hk)]
        dsimp only
        simp only [beq_nat_false_of_lt hk, Bool.false_eq_true, ↓reduceIte]
    | int128 lo hi =>
      dsimp only [sysvPackLoop]
      by_cases hGp : gpOff ≤ 32
      · simp only [hGp, ite_true]
        have hSub := ih (gpOff + 16) fpOff ovIdx
          { acc with gpSlots := fun i =>
              if i == gpOff / 8 then lo
              else if i == gpOff / 8 + 1 then hi
              else acc.gpSlots i } hFp
        refine ⟨?_, hSub.2.1, hSub.2.2.1, hSub.2.2.2⟩
        intro i hi1
        have hi' : i < (gpOff + 16) / 8 := by
          rw [div8_add16]
          exact Nat.lt_trans hi1 (Nat.lt_add_of_pos_right (by decide))
        rw [hSub.1 i hi']
        have hi2 : i < gpOff / 8 + 1 := Nat.lt_succ_of_lt hi1
        dsimp only
        simp only [beq_nat_false_of_lt hi1, beq_nat_false_of_lt hi2, Bool.false_eq_true, ↓reduceIte]
      · simp only [hGp, ite_false]
        have hSub := ih gpOff fpOff (alignUpEven ovIdx + 2)
          { acc with overflowWords := fun k =>
              if k == alignUpEven ovIdx then lo
              else if k == alignUpEven ovIdx + 1 then hi
              else acc.overflowWords k } hFp
        refine ⟨hSub.1, hSub.2.1, ?_, hSub.2.2.2⟩
        intro k hk
        have hAlign : ovIdx ≤ alignUpEven ovIdx := le_alignUpEven ovIdx
        have hk0 : k < alignUpEven ovIdx := Nat.lt_of_lt_of_le hk hAlign
        have hk1 : k < alignUpEven ovIdx + 1 := Nat.lt_succ_of_lt hk0
        have hk2 : k < alignUpEven ovIdx + 2 := Nat.lt_succ_of_lt hk1
        rw [hSub.2.2.1 k hk2]
        dsimp only
        simp only [beq_nat_false_of_lt hk0, beq_nat_false_of_lt hk1, Bool.false_eq_true, ↓reduceIte]

private theorem fpSlot_lt_8_of_fpOff_le_160 (fpIdx : Nat) (h : 48 + fpIdx * 16 ≤ 160) :
    fpIdx < 8 := by
  have hMul : fpIdx * 16 ≤ 7 * 16 := by
    have hSum : 48 + fpIdx * 16 ≤ 48 + 7 * 16 := h
    exact Nat.le_of_add_le_add_left hSum
  have hLe7 : fpIdx ≤ 7 := Nat.le_of_mul_le_mul_right hMul (by decide)
  exact Nat.lt_succ_of_le hLe7

private theorem min_succ_le_of_fp_head {fpIdx restCount callerAl : Nat}
    (hLt8 : fpIdx < 8)
    (hBound : Nat.min (fpIdx + (restCount + 1)) 8 ≤ callerAl) :
    fpIdx < callerAl ∧ Nat.min ((fpIdx + 1) + restCount) 8 ≤ callerAl := by
  have hSum : fpIdx + 1 ≤ fpIdx + (restCount + 1) := by
    rw [← Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.le_add_left 1 restCount) fpIdx
  have hLeMin : fpIdx + 1 ≤ Nat.min (fpIdx + (restCount + 1)) 8 :=
    Nat.le_min.mpr ⟨hSum, hLt8⟩
  have hLtAl : fpIdx < callerAl := Nat.lt_of_lt_of_le (Nat.lt_succ_self fpIdx) (Nat.le_trans hLeMin hBound)
  have hEq : (fpIdx + 1) + restCount = fpIdx + (restCount + 1) := by
    rw [Nat.add_assoc, Nat.add_comm 1 restCount]
  rw [hEq]
  exact ⟨hLtAl, hBound⟩

private theorem div16_48_add_mul16 (fpIdx : Nat) :
    ((48 + fpIdx * 16) - 48) / 16 = fpIdx := by
  rw [Nat.add_sub_cancel_left]
  exact Nat.mul_div_left fpIdx (by decide)

private theorem sysv_pack_then_next_arg_loop
    (gpOff fpIdx ovIdx : Nat) (args : List SysVArgVal) (acc : SysVCallFrame)
    (hAlBound : Nat.min (fpIdx + countFpArgs args) 8 ≤ acc.callerAl) :
    ∃ ap',
      sysvVaNextArgs
        (sysvPackLoop gpOff (48 + fpIdx * 16) ovIdx args acc)
        { gpOffset := gpOff, fpOffset := 48 + fpIdx * 16, overflowIdx := ovIdx }
        (args.map SysVArgVal.ty)
      = .ok (args, ap') := by
  induction args generalizing gpOff fpIdx ovIdx acc with
  | nil =>
    exact ⟨{ gpOffset := gpOff, fpOffset := 48 + fpIdx * 16, overflowIdx := ovIdx }, rfl⟩
  | cons hd tl ih =>
    have hFpGe : 48 ≤ 48 + fpIdx * 16 := Nat.le_add_right 48 (fpIdx * 16)
    cases hd with
    | gp64 v =>
      dsimp only [List.map, sysvPackLoop, sysvVaNextArgs, sysvVaNextArg, SysVArgVal.ty]
      by_cases hGp : gpOff ≤ 40
      · simp only [hGp, ite_true]
        let acc1 := { acc with gpSlots := fun i => if i == gpOff / 8 then v else acc.gpSlots i }
        have hFrame := sysvPackLoop_frame (gpOff + 8) (48 + fpIdx * 16) ovIdx tl acc1 hFpGe
        have hRead : (sysvPackLoop (gpOff + 8) (48 + fpIdx * 16) ovIdx tl acc1).gpSlots (gpOff / 8) = v := by
          have hLt : gpOff / 8 < (gpOff + 8) / 8 := by
            rw [div8_add8]
            exact Nat.lt_succ_self (gpOff / 8)
          rw [hFrame.1 (gpOff / 8) hLt]
          dsimp only [acc1]
          simp only [nat_beq_self, ↓reduceIte]
        have hAl1 : Nat.min (fpIdx + countFpArgs tl) 8 ≤ acc1.callerAl := hAlBound
        obtain ⟨ap', hRest⟩ := ih (gpOff + 8) fpIdx ovIdx acc1 hAl1
        refine ⟨ap', ?_⟩
        rw [hRead, hRest]
      · simp only [hGp, ite_false]
        let acc1 := { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k }
        have hFrame := sysvPackLoop_frame gpOff (48 + fpIdx * 16) (ovIdx + 1) tl acc1 hFpGe
        have hRead : (sysvPackLoop gpOff (48 + fpIdx * 16) (ovIdx + 1) tl acc1).overflowWords ovIdx = v := by
          rw [hFrame.2.2.1 ovIdx (Nat.lt_succ_self ovIdx)]
          dsimp only [acc1]
          simp only [nat_beq_self, ↓reduceIte]
        have hAl1 : Nat.min (fpIdx + countFpArgs tl) 8 ≤ acc1.callerAl := hAlBound
        obtain ⟨ap', hRest⟩ := ih gpOff fpIdx (ovIdx + 1) acc1 hAl1
        refine ⟨ap', ?_⟩
        rw [hRead, hRest]
    | fp64 v =>
      dsimp only [List.map, sysvPackLoop, sysvVaNextArgs, sysvVaNextArg, SysVArgVal.ty]
      by_cases hF : 48 + fpIdx * 16 ≤ 160
      · simp only [hF, ite_true]
        have hLt8 : fpIdx < 8 := fpSlot_lt_8_of_fpOff_le_160 fpIdx hF
        dsimp only [countFpArgs] at hAlBound
        obtain ⟨hLtAl, hNextAl⟩ := min_succ_le_of_fp_head hLt8 hAlBound
        have hSlotEq : ((48 + fpIdx * 16) - 48) / 16 = fpIdx := div16_48_add_mul16 fpIdx
        let acc1 := {
          acc with
          fpSlots := fun i =>
            if i == fpIdx then
              if fpIdx < acc.callerAl then RegSaveSlot.saved v else RegSaveSlot.unsaved
            else acc.fpSlots i
        }
        have hFpNext : 48 + fpIdx * 16 + 16 = 48 + (fpIdx + 1) * 16 := by
          rw [Nat.add_assoc, Nat.add_mul, Nat.one_mul]
        have hFpGeNext : 48 ≤ 48 + (fpIdx + 1) * 16 := Nat.le_add_right 48 ((fpIdx + 1) * 16)
        have hFrame := sysvPackLoop_frame gpOff (48 + (fpIdx + 1) * 16) ovIdx tl acc1 hFpGeNext
        have hRead : (sysvPackLoop gpOff (48 + (fpIdx + 1) * 16) ovIdx tl acc1).fpSlots fpIdx = .saved v := by
          have hLtSlot : fpIdx < ((48 + (fpIdx + 1) * 16) - 48) / 16 := by
            rw [div16_48_add_mul16 (fpIdx + 1)]
            exact Nat.lt_succ_self fpIdx
          rw [hFrame.2.1 fpIdx hLtSlot]
          dsimp only [acc1]
          simp only [nat_beq_self, hLtAl, ↓reduceIte]
        have hAl1 : Nat.min ((fpIdx + 1) + countFpArgs tl) 8 ≤ acc1.callerAl := hNextAl
        obtain ⟨ap', hRest⟩ := ih gpOff (fpIdx + 1) ovIdx acc1 hAl1
        refine ⟨ap', ?_⟩
        simp only [hSlotEq, hFpNext]
        rw [hRead]
        dsimp only
        rw [hRest]
      · simp only [hF, ite_false]
        dsimp only [countFpArgs] at hAlBound
        have hAlRest : Nat.min (fpIdx + countFpArgs tl) 8 ≤ acc.callerAl := by
          have hSub : fpIdx + countFpArgs tl ≤ fpIdx + (countFpArgs tl + 1) :=
            Nat.add_le_add_left (Nat.le_succ (countFpArgs tl)) fpIdx
          exact Nat.le_trans (Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hSub, Nat.min_le_right _ _⟩) hAlBound
        let acc1 := { acc with overflowWords := fun k => if k == ovIdx then v else acc.overflowWords k }
        have hFrame := sysvPackLoop_frame gpOff (48 + fpIdx * 16) (ovIdx + 1) tl acc1 hFpGe
        have hRead : (sysvPackLoop gpOff (48 + fpIdx * 16) (ovIdx + 1) tl acc1).overflowWords ovIdx = v := by
          rw [hFrame.2.2.1 ovIdx (Nat.lt_succ_self ovIdx)]
          dsimp only [acc1]
          simp only [nat_beq_self, ↓reduceIte]
        obtain ⟨ap', hRest⟩ := ih gpOff fpIdx (ovIdx + 1) acc1 hAlRest
        refine ⟨ap', ?_⟩
        rw [hRead, hRest]
    | int128 lo hi =>
      dsimp only [List.map, sysvPackLoop, sysvVaNextArgs, sysvVaNextArg, SysVArgVal.ty]
      by_cases hGp : gpOff ≤ 32
      · simp only [hGp, ite_true]
        let acc1 := {
          acc with
          gpSlots := fun i =>
            if i == gpOff / 8 then lo
            else if i == gpOff / 8 + 1 then hi
            else acc.gpSlots i
        }
        have hFrame := sysvPackLoop_frame (gpOff + 16) (48 + fpIdx * 16) ovIdx tl acc1 hFpGe
        have hReadLo : (sysvPackLoop (gpOff + 16) (48 + fpIdx * 16) ovIdx tl acc1).gpSlots (gpOff / 8) = lo := by
          have hLt : gpOff / 8 < (gpOff + 16) / 8 := by
            rw [div8_add16]
            exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
          rw [hFrame.1 (gpOff / 8) hLt]
          dsimp only [acc1]
          simp only [nat_beq_self, ↓reduceIte]
        have hReadHi : (sysvPackLoop (gpOff + 16) (48 + fpIdx * 16) ovIdx tl acc1).gpSlots (gpOff / 8 + 1) = hi := by
          have hLt : gpOff / 8 + 1 < (gpOff + 16) / 8 := by
            rw [div8_add16]
            exact Nat.lt_succ_self _
          rw [hFrame.1 (gpOff / 8 + 1) hLt]
          have hNe : (gpOff / 8 + 1 == gpOff / 8) = false := by
            cases hb : (gpOff / 8 + 1 == gpOff / 8)
            · rfl
            · exact False.elim (Nat.succ_ne_self (gpOff / 8) (beq_iff_eq.mp hb))
          dsimp only [acc1]
          simp only [hNe, Bool.false_eq_true, nat_beq_self, ↓reduceIte]
        obtain ⟨ap', hRest⟩ := ih (gpOff + 16) fpIdx ovIdx acc1 hAlBound
        refine ⟨ap', ?_⟩
        rw [hReadLo, hReadHi, hRest]
      · simp only [hGp, ite_false]
        let aligned := alignUpEven ovIdx
        let acc1 := {
          acc with
          overflowWords := fun k =>
            if k == aligned then lo
            else if k == aligned + 1 then hi
            else acc.overflowWords k
        }
        have hFrame := sysvPackLoop_frame gpOff (48 + fpIdx * 16) (aligned + 2) tl acc1 hFpGe
        have hReadLo : (sysvPackLoop gpOff (48 + fpIdx * 16) (aligned + 2) tl acc1).overflowWords aligned = lo := by
          have hLt : aligned < aligned + 2 := Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
          rw [hFrame.2.2.1 aligned hLt]
          dsimp only [acc1]
          simp only [nat_beq_self, ↓reduceIte]
        have hReadHi : (sysvPackLoop gpOff (48 + fpIdx * 16) (aligned + 2) tl acc1).overflowWords (aligned + 1) = hi := by
          have hLt : aligned + 1 < aligned + 2 := Nat.lt_succ_self _
          rw [hFrame.2.2.1 (aligned + 1) hLt]
          have hNe : (aligned + 1 == aligned) = false := by
            cases hb : (aligned + 1 == aligned)
            · rfl
            · exact False.elim (Nat.succ_ne_self aligned (beq_iff_eq.mp hb))
          dsimp only [acc1]
          simp only [hNe, Bool.false_eq_true, nat_beq_self, ↓reduceIte]
        obtain ⟨ap', hRest⟩ := ih gpOff fpIdx (aligned + 2) acc1 hAlBound
        refine ⟨ap', ?_⟩
        rw [hReadLo, hReadHi, hRest]

/-- **Theorem 1: Exact Pack-Then-`next_arg` Sequence Extraction Across Mixed GP, XMM, Overflow, and `u128`**.
    Covers arbitrary fixed-argument counts, `%r9` backfill after spilled `u128`, 16-byte overflow
    alignment, and 9+ XMM spill when `callerAl ≥ min(fixedFp + countFpArgs args, 8)`. -/
theorem sysv_pack_then_next_arg_exact
    (fixedGp fixedFp callerAl : Nat) (args : List SysVArgVal)
    (hAlBound : Nat.min (fixedFp + countFpArgs args) 8 ≤ callerAl) :
    ∃ ap',
      sysvVaNextArgs
        (sysvPackVariadicCall fixedGp fixedFp callerAl args)
        (sysvInitVaList fixedGp fixedFp)
        (args.map SysVArgVal.ty)
      = .ok (args, ap') :=
  sysv_pack_then_next_arg_loop (fixedGp * 8) fixedFp 0 args (emptySysVCallFrame callerAl) hAlBound

/-- **Theorem 2: `vaCopy` Cursor-Fork Observational Non-Interference**. -/
theorem vaCopy_cursor_fork_non_interference
    (frame : SysVCallFrame) (ap : SysVVaList) (tys : List SysVArgTy) :
    let apFork := vaCopy ap
    sysvVaNextArgs frame apFork tys = sysvVaNextArgs frame ap tys ∧
    ap = { gpOffset := ap.gpOffset, fpOffset := ap.fpOffset, overflowIdx := ap.overflowIdx } := by
  exact ⟨rfl, rfl⟩

/-- **Theorem 3: Caller `%al >= actualXmmUsed` Safety Bound Preventing Unsaved XMM Read UB**. -/
theorem caller_al_ge_actualXmmUsed_prevents_unsaved_xmm_ub
    (fixedGp fixedFp callerAl : Nat) (args : List SysVArgVal)
    (hAlBound : Nat.min (fixedFp + countFpArgs args) 8 ≤ callerAl) :
    sysvVaNextArgs
      (sysvPackVariadicCall fixedGp fixedFp callerAl args)
      (sysvInitVaList fixedGp fixedFp)
      (args.map SysVArgVal.ty)
    ≠ .error .unsavedXmmReadUB := by
  obtain ⟨ap', hOk⟩ := sysv_pack_then_next_arg_exact fixedGp fixedFp callerAl args hAlBound
  rw [hOk]
  intro hErr
  cases hErr

/-! ## Section 3: Three Constructive Sharpness Counterexamples, AAPCS64 Contrast, & Indirect Decay -/

/-- **CE1**: Under-reporting `%al` (`callerAl = 0` when 1 `f64` is passed) yields `.error .unsavedXmmReadUB`,
    whereas `callerAl = 1` extracts the exact `f64`. -/
theorem ce1_underreported_al_reads_unsaved_xmm_slot_ub (w : UInt64) :
    sysvVaNextArgs (sysvPackVariadicCall 0 0 0 [.fp64 w]) (sysvInitVaList 0 0) [.fp64]
      = .error .unsavedXmmReadUB ∧
    (∃ ap',
      sysvVaNextArgs (sysvPackVariadicCall 0 0 1 [.fp64 w]) (sysvInitVaList 0 0) [.fp64]
        = .ok ([.fp64 w], ap')) := by
  refine ⟨rfl, ?_⟩
  have hAl : Nat.min (0 + countFpArgs [.fp64 w]) 8 ≤ 1 := by
    dsimp only [countFpArgs]
    exact Nat.le_refl 1
  exact sysv_pack_then_next_arg_exact 0 0 1 [.fp64 w] hAl

def buggySysvU128NoPairCheck (frame : SysVCallFrame) (ap : SysVVaList) : SysVArgVal :=
  let slot := ap.gpOffset / 8
  .int128 (frame.gpSlots slot) (frame.gpSlots (slot + 1))

def buggySysvU128NoOverflowAlign16 (frame : SysVCallFrame) (ap : SysVVaList) : SysVArgVal :=
  .int128 (frame.overflowWords ap.overflowIdx) (frame.overflowWords (ap.overflowIdx + 1))

/-- **CE2**: Concrete witness showing all three SysV `u128` alignment/spill pitfalls:
    (1) at `gpOffset = 40` (`5` GP regs used), omitting `gpOffset ≤ 32` reads garbage `gpSlots 5, 6` instead of `overflowWords[0..2]`;
    (2) at `gpOffset = 8` (`1` GP reg used), the register save area pointer is `16*k + 8` (mod `16 = 8 ≠ 0`), requiring `copy_to_temporary_if_more_aligned`;
    (3) after a spilled `u64` (`overflowIdx = 1`), omitting `alignUpEven` reads `(padding = 0, lo)` instead of `(lo, hi)`, while `sysvVaNextArg` recovers the exact `u128` AND backfills `%r9`. -/
theorem ce2_odd_gp_offset_u128_without_alignment_adjustment_corrupts_arg :
    let vLo : UInt64 := 0x99AABBCCDDEEFF00
    let vHi : UInt64 := 0x1122334455667788
    let r9Val : UInt64 := 9
    -- (a) 5 fixed GP args (gpOffset = 40), variadic [u128, u64]:
    let frame5 := sysvPackVariadicCall 5 0 0 [.int128 vLo vHi, .gp64 r9Val]
    let ap5 := sysvInitVaList 5 0
    buggySysvU128NoPairCheck frame5 ap5 ≠ .int128 vLo vHi ∧
    (∃ ap5', sysvVaNextArgs frame5 ap5 [.int128, .gp64] = .ok ([.int128 vLo vHi, .gp64 r9Val], ap5')) ∧
    -- (b) 1 fixed GP arg (gpOffset = 8), save-area address mod 16 is 8 (not 16-byte aligned):
    (∀ k : Nat, (16 * k + 8) % 16 = 8) ∧
    -- (c) 6 fixed GP args (gpOffset = 48), variadic [u64 11, u128]: overflowIdx = 1 without 16B align corrupts arg:
    let frame6 := sysvPackVariadicCall 6 0 0 [.gp64 11, .int128 vLo vHi]
    let ap6AfterFirst : SysVVaList := { gpOffset := 48, fpOffset := 48, overflowIdx := 1 }
    buggySysvU128NoOverflowAlign16 frame6 ap6AfterFirst ≠ .int128 vLo vHi ∧
    (∃ ap6', sysvVaNextArgs frame6 (sysvInitVaList 6 0) [.gp64, .int128] = .ok ([.gp64 11, .int128 vLo vHi], ap6')) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact sysv_pack_then_next_arg_exact 5 0 0 [.int128 0x99AABBCCDDEEFF00 0x1122334455667788, .gp64 9] (by decide)
  · intro k
    have h1 : (8 + k * 16) % 16 = 8 % 16 := Nat.add_mul_mod_self_right 8 k 16
    rw [Nat.mul_comm 16 k, Nat.add_comm (k * 16) 8]
    exact h1
  · decide
  · exact sysv_pack_then_next_arg_exact 6 0 0 [.gp64 11, .int128 0x99AABBCCDDEEFF00 0x1122334455667788] (by decide)

/-- AAPCS64 (`emit_aapcs_va_arg`, `va_arg.rs:196-301`) contrast: `gr_offs` starts at `-64 + 8 * fixedGp`,
    rounds `u128` upward to an even `-16` multiple (`gr_offs + 15) & -16`, and when `-8` rounds up to `0`
    (`0 + 16 > 0`), it stores `new_gr_offs = 16 > 0` so a subsequent `u64` does NOT backfill `x7`. -/
def aapcs64NextU128Offs (grOffs : Int) : Int × Bool :=
  let aligned : Int :=
    if grOffs % 16 == 0 then grOffs else grOffs + 8
  let nextOffs := aligned + 16
  (nextOffs, decide (nextOffs > 0))

theorem aapcs64_gr_offs_contrasts_with_sysv_backfill :
    -- 1 GP arg used (gr_offs = -56): rounds to -48 (skips x1, uses x2:x3), next = -32 (in reg)
    aapcs64NextU128Offs (-56) = (-32, false) ∧
    -- 7 GP args used (gr_offs = -8): rounds to 0, stores +16 (spills to stack, exhausts x7)
    aapcs64NextU128Offs (-8) = (16, true) := by
  decide

/-- **CE3**: Passing `3.5f32` (`0x40600000`) to a variadic C function promotes to `3.5f64` (`0x400c000000000000`).
    Miri catches `.f64` read as `.f32` (`vaArgTypeMismatchUB`); raw 32-bit LE load reads `0 ≠ 0x40600000`;
    and `implementsVaArgSafe lp64SysV .f32 = false` prevents the unsound read statically. -/
theorem ce3_c_default_promoted_f32_read_as_unpromoted_f32_type_mismatch_ub :
    let f32Bits3_5 : Nat := 0x40600000
    let f64Bits3_5 : Nat := 0x400c000000000000
    let promotedLow32Le : Nat := f64Bits3_5 % (2 ^ 32)
    cDefaultPromote lp64SysV .f32 = .f64 ∧
    implementsVaArgSafe lp64SysV .f32 = false ∧
    validateCVariadicArg { ty := .f64, rawVal := f64Bits3_5, isNegativeSigned := false } .f32
      = .error .vaArgTypeMismatchUB ∧
    promotedLow32Le ≠ f32Bits3_5 := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-! ## Section 4: `VaList` Parameter Decay (`#[rustc_pass_indirectly_in_non_rustic_abis]`) & `#[unsafe(naked)]` -/

inductive VaListFlavor where
  | ptrOpaque (bytes : Nat)        -- Win64 / Darwin ARM64 / RISCV64 / i686 / PPC64
  | structByVal (bytes : Nat)      -- Linux AAPCS64 (32B struct, passed indirectly by C ABI >16B)
  | singleElemArrayIndirect (bytes : Nat) -- SysV x86_64 (24B), s390x (32B), PPC32/Xtensa/Hexagon (12B)
  deriving DecidableEq, Repr

inductive AbiPassMode where
  | direct
  | indirectPointer
  deriving DecidableEq, Repr

def hasPassIndirectlyAttr : VaListFlavor → Bool
  | .singleElemArrayIndirect _ => true
  | .ptrOpaque _ | .structByVal _ => false

/-- Models `x86_64.rs:231-235` + `rustc_ty_utils/src/abi.rs:447-453`:
    non-rustic ABIs must lower `#[rustc_pass_indirectly_in_non_rustic_abis]` via `PassMode::Indirect`. -/
def passModeForNonRusticAbi (flavor : VaListFlavor) (structBytes : Nat) : AbiPassMode :=
  if hasPassIndirectlyAttr flavor then .indirectPointer
  else if structBytes > 16 then .indirectPointer
  else .direct

theorem passIndirectly_forces_indirect_on_sysv_x86_64 :
    passModeForNonRusticAbi (.singleElemArrayIndirect 24) 24 = .indirectPointer ∧
    passModeForNonRusticAbi (.structByVal 32) 32 = .indirectPointer ∧
    passModeForNonRusticAbi (.ptrOpaque 8) 8 = .direct := by
  decide

/-- Models `rustc_hir_typeck/src/naked_functions.rs` + `rustc_ast_passes/src/ast_validation.rs`. -/
inductive NakedBodyKind where
  | singleNakedAsm (usesOnlyConstOrSym : Bool) (usesOnlyAttOrRawOpts : Bool)
  | regularAsm
  | nonAsmStmts
  | multipleAsms
  deriving DecidableEq, Repr

structure NakedFnHirDecl where
  hasTrivialPatterns : Bool
  referencesParamInBody : Bool
  bodyKind : NakedBodyKind
  isCVariadic : Bool
  abiSupportsCVariadic : Bool
  deriving DecidableEq, Repr

inductive NakedHirError where
  | patternsNotAllowed
  | paramsNotAllowed
  | e0787MustBeNakedAsm
  | e0787SingleNakedAsmBlock
  | invalidNakedAsmOperandOrOption
  | badNakedCVariadicAbi
  deriving DecidableEq, Repr

def checkNakedFnHir (d : NakedFnHirDecl) : Except NakedHirError Unit :=
  if !d.hasTrivialPatterns then .error .patternsNotAllowed
  else if d.referencesParamInBody then .error .paramsNotAllowed
  else
    match d.bodyKind with
    | .regularAsm => .error .e0787MustBeNakedAsm
    | .nonAsmStmts | .multipleAsms => .error .e0787SingleNakedAsmBlock
    | .singleNakedAsm okOp okOpt =>
      if !(okOp && okOpt) then .error .invalidNakedAsmOperandOrOption
      else if d.isCVariadic && !d.abiSupportsCVariadic then .error .badNakedCVariadicAbi
      else .ok ()

structure NakedAsmState where
  rsp : Nat
  rip : Nat
  retSlotAddr : Nat
  retAddrInSlot : Nat
  calleeSaved : Nat → Nat

/-- A `#[unsafe(naked)]` body suppresses compiler prologue/epilogue (`LLVM Attribute::Naked` bypassed
    via `codegen_naked_asm` -> `module asm`). Soundness requires the inline instructions to reach
    `ret` with net stack delta `0` (`rsp == rspEntry`) and preserved callee-saved registers. -/
def execNakedBodyThenRet (s0 : NakedAsmState) (stackDeltaAtRet : Int)
    (clobberedCalleeSaved : Bool) : NakedAsmState :=
  let rspAtRet := if stackDeltaAtRet ≥ 0 then s0.rsp + stackDeltaAtRet.toNat else s0.rsp - (-stackDeltaAtRet).toNat
  let jumpedRip := if rspAtRet == s0.retSlotAddr then s0.retAddrInSlot else 0xBAD0
  let rspAfterRet := rspAtRet + 8
  let regs' := if clobberedCalleeSaved then fun _ => 0xDEAD else s0.calleeSaved
  { s0 with rsp := rspAfterRet, rip := jumpedRip, calleeSaved := regs' }

theorem nakedFnContract_sound (rsp0 retAddr : Nat) (saved : Nat → Nat) :
    let s0 : NakedAsmState := {
      rsp := rsp0, rip := 0x1000, retSlotAddr := rsp0, retAddrInSlot := retAddr, calleeSaved := saved
    }
    let s1 := execNakedBodyThenRet s0 0 false
    s1.rip = retAddr ∧ s1.rsp = rsp0 + 8 ∧ s1.calleeSaved = saved := by
  dsimp only [execNakedBodyThenRet]
  have hCond : (0 : Int) ≥ 0 := by decide
  have hToNat : (0 : Int).toNat = 0 := by decide
  have hBeq : (rsp0 == rsp0) = true := nat_beq_self rsp0
  simp only [hCond, ↓reduceIte, hToNat, Nat.add_zero, hBeq, Bool.false_eq_true, and_self]

theorem ce4_nonzero_stack_delta_in_naked_ret_corrupts_return (rsp0 retAddr : Nat)
    (hStack : 8 ≤ rsp0) (hRet : retAddr ≠ 0xBAD0) (saved : Nat → Nat) :
    let s0 : NakedAsmState := {
      rsp := rsp0, rip := 0x1000, retSlotAddr := rsp0, retAddrInSlot := retAddr, calleeSaved := saved
    }
    let sBad := execNakedBodyThenRet s0 (-8) false
    sBad.rip ≠ retAddr := by
  have hPos : 0 < rsp0 := Nat.lt_of_lt_of_le (by decide) hStack
  have hLt : rsp0 - 8 < rsp0 := Nat.sub_lt hPos (by decide)
  have hNe : rsp0 - 8 ≠ rsp0 := Nat.ne_of_lt hLt
  have hBeqFalse : (rsp0 - 8 == rsp0) = false := beq_false_of_ne hNe
  have hCond : ¬ ((-8 : Int) ≥ 0) := by decide
  have hToNat : (-(-8 : Int)).toNat = 8 := by decide
  dsimp only [execNakedBodyThenRet]
  simp only [hCond, ↓reduceIte, hToNat, hBeqFalse, Bool.false_eq_true]
  exact hRet.symm

#print axioms vaArgSafe_excludes_default_promoted_types
#print axioms vaArgSafe_lp64_excludes_promoted
#print axioms miri_vaCopy_non_interference
#print axioms miri_use_after_vaEnd_is_ub
#print axioms miri_raw_memcpy_after_step_is_ub
#print axioms sysv_pack_then_next_arg_exact
#print axioms vaCopy_cursor_fork_non_interference
#print axioms caller_al_ge_actualXmmUsed_prevents_unsaved_xmm_ub
#print axioms ce1_underreported_al_reads_unsaved_xmm_slot_ub
#print axioms ce2_odd_gp_offset_u128_without_alignment_adjustment_corrupts_arg
#print axioms aapcs64_gr_offs_contrasts_with_sysv_backfill
#print axioms ce3_c_default_promoted_f32_read_as_unpromoted_f32_type_mismatch_ub
#print axioms passIndirectly_forces_indirect_on_sysv_x86_64
#print axioms nakedFnContract_sound
#print axioms ce4_nonzero_stack_delta_in_naked_ret_corrupts_return

end CVariadicVaListAndNakedAsmSoundness
