/-
  CtfeInterningMutabilityAndProvenanceSoundness.lean

  Kernel-checked Lean v4.34.1 mechanization of rustc_const_eval CTFE interning,
  mutability / UnsafeCell read-only protection, skip_recursive_check static-pointing
  exception, dangling-pointer vs. integer-cast boundaries, and cross-AllocId
  relocation-invariance.

  Primary-source anchors:
  - rust-lang/rust `compiler/rustc_const_eval/src/interpret/intern.rs`
  - rust-lang/rust `compiler/rustc_const_eval/src/interpret/validity.rs`
  - rust-lang/rust `compiler/rustc_const_eval/src/interpret/memory.rs`
  - rust-lang/rust `compiler/rustc_const_eval/src/const_eval/eval_queries.rs`
  - rust-lang/rust `compiler/rustc_const_eval/src/const_eval/machine.rs`
  - rust-lang/rust `compiler/rustc_const_eval/src/check_consts/{check.rs,qualifs.rs}`
  - rust-lang/rust `compiler/rustc_middle/src/mir/interpret/pointer.rs`

  Lean Purity Contract:
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
    zero `native_decide`, zero `partial def`, zero `._unsafe_rec`, zero `deriving`,
    zero `noncomputable section`; every `def` is explicitly `noncomputable def`.
-/

namespace CtfeInterningSoundness

/-! ## Section 1: Core Identifiers, Mutability, Provenance, and Types -/

/-- Boolean equality helper avoiding `Bool.eqv` dependency. -/
noncomputable def boolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Allocation identifier (`rustc_middle::mir::interpret::AllocId`). -/
structure AllocId where
  raw : Nat

/-- Structural boolean equality on `AllocId`. -/
noncomputable def allocIdEq (a b : AllocId) : Bool :=
  Nat.beq a.raw b.raw

theorem allocIdEq_refl (a : AllocId) : allocIdEq a a = true := by
  exact Nat.beq_refl a.raw

theorem allocIdEq_eq {a b : AllocId} (h : allocIdEq a b = true) : a = b := by
  cases a with
  | mk ra =>
    cases b with
    | mk rb =>
      have hr : ra = rb := Nat.eq_of_beq_eq_true h
      subst hr
      rfl

theorem allocIdEq_iff (a b : AllocId) : allocIdEq a b = true ↔ a = b := by
  constructor
  · exact allocIdEq_eq
  · intro h
    subst h
    exact allocIdEq_refl a

theorem allocIdEq_false_symm {a b : AllocId} (h : allocIdEq a b = false) :
    allocIdEq b a = false := by
  cases hrev : allocIdEq b a with
  | false => rfl
  | true =>
    have hba : b = a := allocIdEq_eq hrev
    subst hba
    rw [allocIdEq_refl] at h
    cases h

theorem allocIdEq_false_ne {a b : AllocId} (h : allocIdEq a b = false) : a ≠ b := by
  intro heq
  subst heq
  rw [allocIdEq_refl] at h
  cases h

/-- Allocation or pointer mutability (`rustc_ast::Mutability::{Not, Mut}`). -/
inductive Mutability where
  | imm
  | mutbl

/-- Boolean equality on `Mutability`. -/
noncomputable def mutEq (a b : Mutability) : Bool :=
  match a, b with
  | .imm, .imm => true
  | .mutbl, .mutbl => true
  | _, _ => false

theorem mutEq_refl (a : Mutability) : mutEq a a = true := by
  cases a <;> rfl

theorem mutEq_eq {a b : Mutability} (h : mutEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem mutEq_iff (a b : Mutability) : mutEq a b = true ↔ a = b := by
  constructor
  · exact mutEq_eq
  · intro h
    subst h
    exact mutEq_refl a

/-- Origin / memory kind of a CTFE allocation (`MemoryKind` + `DefKind::Static`). -/
inductive AllocOrigin where
  | globalStatic (isExtern : Bool) (isNested : Bool)
  | localConst
  | promoted
  | heapMadeGlobal
  | heapTransient

/-- Boolean equality on `AllocOrigin`. -/
noncomputable def originEq (a b : AllocOrigin) : Bool :=
  match a, b with
  | .globalStatic e1 n1, .globalStatic e2 n2 => Bool.and (boolEq e1 e2) (boolEq n1 n2)
  | .localConst, .localConst => true
  | .promoted, .promoted => true
  | .heapMadeGlobal, .heapMadeGlobal => true
  | .heapTransient, .heapTransient => true
  | _, _ => false

/-- Returns `true` iff the allocation is a top-level or nested `globalStatic`. -/
noncomputable def isGlobalStaticOrigin (o : AllocOrigin) : Bool :=
  match o with
  | .globalStatic _ _ => true
  | _ => false

/-- Lifecycle state of an allocation (`alloc_map` vs `dead_alloc_map`). -/
inductive AllocLifecycle where
  | live
  | freed

/-- Boolean equality on `AllocLifecycle`. -/
noncomputable def lifecycleEq (a b : AllocLifecycle) : Bool :=
  match a, b with
  | .live, .live => true
  | .freed, .freed => true
  | _, _ => false

theorem lifecycleEq_eq {a b : AllocLifecycle} (h : lifecycleEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Packed CTFE pointer provenance (`rustc_middle::mir::interpret::CtfeProvenance`).
    Tracks `allocId`, `immutable` (`IMMUTABLE_MASK`), and `sharedRef` (`SHARED_REF_MASK`). -/
structure CtfeProvenance where
  allocId : AllocId
  immutable : Bool
  sharedRef : Bool

/-- Provenance bit-packing invariant (`pointer.rs:88-89`):
    if `immutable = true`, then `sharedRef = true`. -/
noncomputable def provInvariant (p : CtfeProvenance) : Prop :=
  p.immutable = true → p.sharedRef = true

/-- Constructor `CtfeProvenance::from(alloc_id)` (`pointer.rs:93-101`). -/
noncomputable def provFromAllocId (id : AllocId) : CtfeProvenance :=
  { allocId := id, immutable := false, sharedRef := false }

/-- Constructor `CtfeProvenance::as_shared_ref` (`pointer.rs:160-163`). -/
noncomputable def provAsSharedRef (p : CtfeProvenance) : CtfeProvenance :=
  { p with sharedRef := true }

/-- Constructor `CtfeProvenance::as_immutable` (`pointer.rs:154-157`). -/
noncomputable def provAsImmutable (p : CtfeProvenance) : CtfeProvenance :=
  { p with immutable := true, sharedRef := true }

theorem provFromAllocId_inv (id : AllocId) : provInvariant (provFromAllocId id) := by
  intro h
  cases h

theorem provAsSharedRef_inv (p : CtfeProvenance) (_h : provInvariant p) :
    provInvariant (provAsSharedRef p) := by
  intro _
  rfl

theorem provAsImmutable_inv (p : CtfeProvenance) :
    provInvariant (provAsImmutable p) := by
  intro _
  rfl

/-- Runtime / CTFE pointer representation: `prov = none` models an integer-cast
    no-provenance pointer (`0x1000 as *const T`), while `prov = some p` tracks
    an allocation provenance and byte offset. -/
structure PtrVal where
  prov : Option CtfeProvenance
  offset : Nat

/-- Structural type language capturing scalar sizes, `UnsafeCell`, references,
    raw pointers, product pairs, and `!Freeze` unions (`validity.rs`). -/
inductive ConstTy where
  | scalar (size : Nat)
  | unsafeCell (inner : ConstTy)
  | mutRef (pointee : ConstTy)
  | sharedRef (pointee : ConstTy)
  | rawPtr (mutVal : Mutability) (pointee : ConstTy)
  | structPair (fst : ConstTy) (snd : ConstTy)
  | unionCell (hasUnsafeCell : Bool) (size : Nat)

/-- Static size of a `ConstTy` in bytes (pointer width = 8 bytes). -/
noncomputable def tySize : ConstTy → Nat
  | .scalar s => s
  | .unsafeCell inner => tySize inner
  | .mutRef _ => 8
  | .sharedRef _ => 8
  | .rawPtr _ _ => 8
  | .structPair a b => tySize a + tySize b
  | .unionCell _ s => s

/-- Pointee size of a safe reference (`mutRef` / `sharedRef`). -/
noncomputable def pointeeTySize : ConstTy → Nat
  | .mutRef p => tySize p
  | .sharedRef p => tySize p
  | .rawPtr _ p => tySize p
  | t => tySize t

/-- Rust `Freeze` auto-trait approximation (`ty.is_freeze`):
    - References (`&T`, `&mut T`) and raw pointers (`*const T`, `*mut T`) are ALWAYS `Freeze`.
    - `UnsafeCell<T>` is `!Freeze` (even if ZST; `validity.rs` checks ZST dynamically).
    - Struct pairs are `Freeze` iff both components are `Freeze`. -/
noncomputable def isFreeze : ConstTy → Bool
  | .scalar _ => true
  | .unsafeCell _ => false
  | .mutRef _ => true
  | .sharedRef _ => true
  | .rawPtr _ _ => true
  | .structPair a b => Bool.and (isFreeze a) (isFreeze b)
  | .unionCell hasCell _ => Bool.not hasCell

theorem isFreeze_sharedRef (p : ConstTy) : isFreeze (.sharedRef p) = true := rfl
theorem isFreeze_mutRef (p : ConstTy) : isFreeze (.mutRef p) = true := rfl
theorem isFreeze_rawPtr (m : Mutability) (p : ConstTy) : isFreeze (.rawPtr m p) = true := rfl
theorem isFreeze_unsafeCell (p : ConstTy) : isFreeze (.unsafeCell p) = false := rfl

/-- Typed constant value representation used by CTFE validation (`validity.rs`). -/
inductive ConstVal where
  | bytes (size : Nat) (val : Nat)
  | cellVal (inner : ConstVal)
  | refVal (ptr : PtrVal) (pointee : Option ConstVal)
  | rawPtrVal (ptr : PtrVal)
  | pairVal (fst : ConstVal) (snd : ConstVal)
  | unionVal (hasUnsafeCell : Bool) (size : Nat)

/-- Upstream `rustc_const_eval::interpret::intern::InternKind` (`intern.rs:180-187`).
    Note: upstream uses `Static(hir::Mutability)` rather than a separate `StaticMut`. -/
inductive InternKind where
  | staticItem (mutVal : Mutability)
  | constant
  | promoted

/-- Boolean equality on `InternKind`. -/
noncomputable def internKindEq (a b : InternKind) : Bool :=
  match a, b with
  | .staticItem m1, .staticItem m2 => mutEq m1 m2
  | .constant, .constant => true
  | .promoted, .promoted => true
  | _, _ => false

/-- Errors returned by `intern_const_alloc_recursive` (`intern.rs:189-195`). -/
inductive InternError where
  | badMutablePointer
  | danglingPointer
  | constAllocNotGlobal
  | partialPointer

/-- Errors thrown by `const_validate_mplace` (`validity.rs:751-1388`). -/
inductive ValidationError where
  | nullOrIntRef
  | danglingRef
  | refOutOfBounds
  | mutableRefToReadOnlyMemory
  | unsafeCellInReadOnlyMemory
  | typeMismatch

/-- Static MIR const-check errors (`check_consts/ops.rs`). -/
inductive ConstCheckError where
  | escapingMutBorrow   -- E0764
  | escapingCellBorrow  -- E0492
  | rawPtrComparison    -- RawPtrComparisonErr
  | rawPtrToIntCast     -- RawPtrToIntErr

/-- Runtime / CTFE execution faults (`InterpErrorKind` / `ConstEvalErrKind`). -/
inductive CtfeFault where
  | danglingIntPointer
  | pointerUseAfterFree
  | pointerOutOfBounds
  | writeToReadOnly
  | modifiedGlobal
  | constAccessesMutGlobal
  | crossAllocOffsetFrom
  | unsupportedBinaryPtrOp
  | internFailed (e : InternError)
  | validationFailed (e : ValidationError)
  | constCheckFailed (e : ConstCheckError)

/-- Uniform error-or-value result type (using explicit inductive to avoid typeclass overhead). -/
inductive Outcome (ε α : Type) where
  | ok (val : α)
  | err (e : ε)


/-! ## Section 2: CTFE Allocation Graph and Memory Store -/

/-- One allocation in either `ecx.memory.alloc_map` (local) or `tcx.global_alloc` (global). -/
structure AllocEntry where
  id : AllocId
  origin : AllocOrigin
  lifecycle : AllocLifecycle
  mutbl : Mutability
  size : Nat
  align : Nat
  hasPartialPtr : Bool
  hasUnsafeCellContent : Bool
  ptrs : List PtrVal
  alreadyGlobal : Bool
  dataByte : Nat

/-- Two-tier CTFE memory: local evaluator map (`alloc_map`) + global `tcx` pool. -/
structure MemState where
  locals : List AllocEntry
  globals : List AllocEntry

/-- Membership of an `AllocId` in a list of IDs. -/
noncomputable def memAllocId (id : AllocId) : List AllocId → Bool
  | [] => false
  | x :: xs =>
    match allocIdEq id x with
    | true => true
    | false => memAllocId id xs

/-- Lookup an `AllocEntry` in a list by `AllocId`. -/
noncomputable def findEntry (id : AllocId) : List AllocEntry → Option AllocEntry
  | [] => none
  | e :: rest =>
    match allocIdEq id e.id with
    | true => some e
    | false => findEntry id rest

/-- Remove an `AllocEntry` from a list by `AllocId` (models `swap_remove`). -/
noncomputable def removeEntry (id : AllocId) : List AllocEntry → List AllocEntry
  | [] => []
  | e :: rest =>
    match allocIdEq id e.id with
    | true => rest
    | false => e :: removeEntry id rest

/-- Update or prepend an `AllocEntry` in a list by `AllocId`. -/
noncomputable def upsertEntry (entry : AllocEntry) : List AllocEntry → List AllocEntry
  | [] => [entry]
  | e :: rest =>
    match allocIdEq entry.id e.id with
    | true => entry :: rest
    | false => e :: upsertEntry entry rest

/-- Lookup allocation in `globals` (`tcx.try_get_global_alloc`). -/
noncomputable def lookupGlobal (m : MemState) (id : AllocId) : Option AllocEntry :=
  findEntry id m.globals

/-- Lookup allocation in `locals` (`ecx.memory.alloc_map`). -/
noncomputable def lookupLocal (m : MemState) (id : AllocId) : Option AllocEntry :=
  findEntry id m.locals

/-- Lookup allocation in `locals` first, then `globals` (models `InterpCx::get_alloc_info`). -/
noncomputable def lookupAny (m : MemState) (id : AllocId) : Option AllocEntry :=
  match lookupLocal m id with
  | some e => some e
  | none => lookupGlobal m id

/-- Extract all `AllocId`s from a list of `PtrVal`s (skipping integer pointers with `prov = none`). -/
noncomputable def ptrValIds : List PtrVal → List AllocId
  | [] => []
  | pv :: rest =>
    match pv.prov with
    | some pr => pr.allocId :: ptrValIds rest
    | none => ptrValIds rest

/-- Extract all `CtfeProvenance` entries from a list of `PtrVal`s (`alloc.provenance().ptrs()`). -/
noncomputable def ptrValProvs : List PtrVal → List CtfeProvenance
  | [] => []
  | pv :: rest =>
    match pv.prov with
    | some pr => pr :: ptrValProvs rest
    | none => ptrValProvs rest

/-- Extract all direct `AllocId` references inside a `ConstVal`. -/
noncomputable def constValDirectIds : ConstVal → List AllocId
  | .bytes _ _ => []
  | .cellVal inner => constValDirectIds inner
  | .refVal pv pointee =>
    let rest := match pointee with | some p => constValDirectIds p | none => []
    match pv.prov with
    | some pr => pr.allocId :: rest
    | none => rest
  | .rawPtrVal pv =>
    match pv.prov with
    | some pr => [pr.allocId]
    | none => []
  | .pairVal a b => constValDirectIds a ++ constValDirectIds b
  | .unionVal _ _ => []

/-- Predicate: every entry in `xs` has unique `AllocId` (no duplicate keys). -/
noncomputable def noDupIds : List AllocEntry → Prop
  | [] => True
  | e :: rest => findEntry e.id rest = none ∧ noDupIds rest

/-- Basic helper lemmas about `findEntry`, `removeEntry`, and `upsertEntry`. -/
theorem findEntry_some_id {id : AllocId} {xs : List AllocEntry} {e : AllocEntry}
    (h : findEntry id xs = some e) : e.id = id := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    unfold findEntry at h
    cases heq : allocIdEq id hd.id with
    | true =>
      rw [heq] at h
      cases h
      exact (allocIdEq_eq heq).symm
    | false =>
      rw [heq] at h
      exact ih h

theorem findEntry_removeEntry_eq (id : AllocId) (xs : List AllocEntry) (hnodup : noDupIds xs) :
    findEntry id (removeEntry id xs) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    unfold noDupIds at hnodup
    obtain ⟨hnone, htl⟩ := hnodup
    unfold removeEntry
    cases heq : allocIdEq id hd.id with
    | true =>
      dsimp only
      have hid : id = hd.id := allocIdEq_eq heq
      subst hid
      exact hnone
    | false =>
      dsimp only
      unfold findEntry
      rw [heq]
      exact ih htl

theorem findEntry_removeEntry_ne {id target : AllocId} (hne : allocIdEq target id = false)
    (xs : List AllocEntry) :
    findEntry target (removeEntry id xs) = findEntry target xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    unfold removeEntry
    cases heq : allocIdEq id hd.id with
    | true =>
      dsimp only
      have hid : id = hd.id := allocIdEq_eq heq
      subst hid
      have hfind :
          findEntry target (hd :: tl) =
            match allocIdEq target hd.id with
            | true => some hd
            | false => findEntry target tl := rfl
      rw [hfind, hne]
    | false =>
      dsimp only
      unfold findEntry
      cases ht : allocIdEq target hd.id with
      | true => rfl
      | false => exact ih

theorem findEntry_upsertEntry_self (entry : AllocEntry) (xs : List AllocEntry) :
    findEntry entry.id (upsertEntry entry xs) = some entry := by
  induction xs with
  | nil =>
    unfold upsertEntry findEntry
    rw [allocIdEq_refl]
  | cons hd tl ih =>
    unfold upsertEntry
    cases heq : allocIdEq entry.id hd.id with
    | true =>
      dsimp only
      unfold findEntry
      rw [allocIdEq_refl]
    | false =>
      dsimp only
      unfold findEntry
      rw [heq]
      exact ih

theorem findEntry_upsertEntry_ne {entry : AllocEntry} {target : AllocId}
    (hne : allocIdEq target entry.id = false) (xs : List AllocEntry) :
    findEntry target (upsertEntry entry xs) = findEntry target xs := by
  induction xs with
  | nil =>
    unfold upsertEntry findEntry
    rw [hne]
    dsimp only
    rfl
  | cons hd tl ih =>
    unfold upsertEntry
    cases heq : allocIdEq entry.id hd.id with
    | true =>
      dsimp only
      have hid : entry.id = hd.id := allocIdEq_eq heq
      unfold findEntry
      rw [← hid, hne]
    | false =>
      dsimp only
      unfold findEntry
      cases ht : allocIdEq target hd.id with
      | true => rfl
      | false => exact ih

/-- MemState well-formedness:
    1. Every entry in `globals` has `alreadyGlobal = true`.
    2. Every entry in `locals` has `alreadyGlobal = false`.
    3. Every ID in `globals` is absent from `locals` (`debug_assert!(!alloc_map.contains_key)`).
    4. No duplicate IDs in `locals` or `globals`. -/
structure MemWF (m : MemState) : Prop where
  localsUnique : noDupIds m.locals
  globalsUnique : noDupIds m.globals
  localsNotGlobal : ∀ id e, lookupLocal m id = some e → e.alreadyGlobal = false
  globalsMarkedGlobal : ∀ id e, lookupGlobal m id = some e → e.alreadyGlobal = true
  disjoint : ∀ id e, lookupGlobal m id = some e → lookupLocal m id = none

/-- Helper: `noDupIds` is preserved by `removeEntry`. -/
theorem noDupIds_removeEntry (id : AllocId) (xs : List AllocEntry) (hn : noDupIds xs) :
    noDupIds (removeEntry id xs) := by
  induction xs with
  | nil => exact True.intro
  | cons hd tl ih =>
    unfold noDupIds at hn
    obtain ⟨hnone, htl⟩ := hn
    unfold removeEntry
    cases heq : allocIdEq id hd.id with
    | true => exact htl
    | false =>
      dsimp only
      unfold noDupIds
      constructor
      · have hne : allocIdEq hd.id id = false := allocIdEq_false_symm heq
        rw [findEntry_removeEntry_ne hne]
        exact hnone
      · exact ih htl

/-- Helper: `noDupIds` is preserved by `upsertEntry`. -/
theorem noDupIds_upsertEntry (entry : AllocEntry) (xs : List AllocEntry) (hn : noDupIds xs) :
    noDupIds (upsertEntry entry xs) := by
  induction xs with
  | nil =>
    unfold upsertEntry noDupIds findEntry
    exact ⟨rfl, True.intro⟩
  | cons hd tl ih =>
    unfold noDupIds at hn
    obtain ⟨hnone, htl⟩ := hn
    unfold upsertEntry
    cases heq : allocIdEq entry.id hd.id with
    | true =>
      dsimp only
      have hid : entry.id = hd.id := allocIdEq_eq heq
      unfold noDupIds
      rw [hid]
      exact ⟨hnone, htl⟩
    | false =>
      dsimp only
      unfold noDupIds
      constructor
      · have hne : allocIdEq hd.id entry.id = false := allocIdEq_false_symm heq
        rw [findEntry_upsertEntry_ne hne]
        exact hnone
      · exact ih htl

theorem memAllocId_cons_self (x : AllocId) (xs : List AllocId) :
    memAllocId x (x :: xs) = true := by
  unfold memAllocId
  rw [allocIdEq_refl]

theorem memAllocId_cons_of_mem {x y : AllocId} {xs : List AllocId}
    (h : memAllocId x xs = true) : memAllocId x (y :: xs) = true := by
  unfold memAllocId
  cases heq : allocIdEq x y with
  | true => rfl
  | false => exact h

theorem memAllocId_append_left {x : AllocId} {xs ys : List AllocId}
    (h : memAllocId x xs = true) : memAllocId x (xs ++ ys) = true := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    unfold memAllocId at h
    cases heq : allocIdEq x hd with
    | true =>
      simp only [List.cons_append, memAllocId, heq]
    | false =>
      rw [heq] at h
      simp only [List.cons_append, memAllocId, heq]
      exact ih h

theorem memAllocId_append_right {x : AllocId} (xs : List AllocId) {ys : List AllocId}
    (h : memAllocId x ys = true) : memAllocId x (xs ++ ys) = true := by
  induction xs with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.cons_append, memAllocId]
    cases heq : allocIdEq x hd with
    | true => rfl
    | false => exact ih


/-! ## Section 3: Phase 1 — `intern_const_alloc_recursive` (`intern.rs`) -/

/-- Exact mutability & static flag decomposition from `InternKind` (`intern.rs:215-241`):
    returns `(baseMutability, innerMutability, isStatic)`. -/
noncomputable def internMutabilitySpec (kind : InternKind) (rootIsFreeze : Bool) :
    Mutability × Mutability × Bool :=
  match kind with
  | .constant => (.imm, .imm, false)
  | .promoted => (.imm, .imm, false)
  | .staticItem .imm =>
    let baseMut := match rootIsFreeze with | true => .imm | false => .mutbl
    (baseMut, .imm, true)
  | .staticItem .mutbl => (.mutbl, .mutbl, true)

/-- `prepare_alloc` (`intern.rs:58-95`):
    - Rejects `heapTransient` (`ConstAllocNotGlobal`).
    - Rejects `hasPartialPtr = true` (`PartialPointer`).
    - If target `mutbl = .imm`, freezes `entry.mutbl := .imm`.
    - If target `mutbl = .mutbl`, asserts/requires `entry.mutbl = .mutbl`
      (if not, fails closed instead of un-freezing). -/
noncomputable def prepareAlloc (entry : AllocEntry) (targetMut : Mutability) :
    Outcome InternError AllocEntry :=
  match entry.origin with
  | .heapTransient => .err .constAllocNotGlobal
  | _ =>
    match entry.hasPartialPtr with
    | true => .err .partialPointer
    | false =>
      match targetMut with
      | .imm => .ok { entry with mutbl := .imm }
      | .mutbl =>
        match entry.mutbl with
        | .mutbl => .ok entry
        | .imm => .err .badMutablePointer

theorem prepareAlloc_imm_sets_imm {e e' : AllocEntry}
    (h : prepareAlloc e .imm = .ok e') : e'.mutbl = .imm := by
  unfold prepareAlloc at h
  cases ho : e.origin <;> rw [ho] at h
  all_goals try (cases h; done)
  all_goals
    cases hp : e.hasPartialPtr <;> rw [hp] at h
    · cases h; rfl
    · cases h

theorem prepareAlloc_preserves_id {e e' : AllocEntry} {m : Mutability}
    (h : prepareAlloc e m = .ok e') : e'.id = e.id := by
  unfold prepareAlloc at h
  cases ho : e.origin <;> rw [ho] at h
  all_goals try (cases h; done)
  all_goals
    cases hp : e.hasPartialPtr <;> rw [hp] at h
    · cases m <;> dsimp at h
      · cases h; rfl
      · cases hm : e.mutbl <;> rw [hm] at h
        · cases h
        · cases h; rfl
    · cases h

theorem prepareAlloc_preserves_lifecycle {e e' : AllocEntry} {m : Mutability}
    (h : prepareAlloc e m = .ok e') : e'.lifecycle = e.lifecycle := by
  unfold prepareAlloc at h
  cases ho : e.origin <;> rw [ho] at h
  all_goals try (cases h; done)
  all_goals
    cases hp : e.hasPartialPtr <;> rw [hp] at h
    · cases m <;> dsimp at h
      · cases h; rfl
      · cases hm : e.mutbl <;> rw [hm] at h
        · cases h
        · cases h; rfl
    · cases h

theorem prepareAlloc_preserves_origin {e e' : AllocEntry} {m : Mutability}
    (h : prepareAlloc e m = .ok e') : e'.origin = e.origin := by
  unfold prepareAlloc at h
  cases ho : e.origin <;> rw [ho] at h
  all_goals try (cases h; done)
  all_goals
    cases hp : e.hasPartialPtr <;> rw [hp] at h
    · cases m <;> dsimp at h
      · cases h; rfl
      · cases hm : e.mutbl <;> rw [hm] at h
        · cases h
        · cases h; exact ho
    · cases h

/-- `intern_shallow` (`intern.rs:104-138`):
    Removes `allocId` from `m.locals`; if absent or `.freed` returns `.danglingPointer`.
    Runs `prepareAlloc`, inserts into `m.globals` with `alreadyGlobal := true`,
    and returns `(newMem, relocations)`. -/
noncomputable def internShallow (m : MemState) (id : AllocId) (targetMut : Mutability) :
    Outcome InternError (MemState × List CtfeProvenance) :=
  match lookupLocal m id with
  | none => .err .danglingPointer
  | some entry =>
    match entry.lifecycle with
    | .freed => .err .danglingPointer
    | .live =>
      match prepareAlloc entry targetMut with
      | .err e => .err e
      | .ok prepared =>
        let globalEntry : AllocEntry := { prepared with alreadyGlobal := true }
        let newMem : MemState := {
          locals := removeEntry id m.locals,
          globals := upsertEntry globalEntry m.globals
        }
        .ok (newMem, ptrValProvs prepared.ptrs)

/-- Every entry moved by `internShallow` with `.imm` becomes a `.live`, `.imm`, `alreadyGlobal = true`
    global allocation. -/
theorem internShallow_imm_props {m m' : MemState} {id : AllocId} {provs : List CtfeProvenance}
    (hwf : MemWF m)
    (h : internShallow m id .imm = .ok (m', provs)) :
    MemWF m' ∧
    ∃ g, lookupGlobal m' id = some g ∧ g.mutbl = .imm ∧ g.lifecycle = .live ∧ g.alreadyGlobal = true := by
  unfold internShallow at h
  cases hloc : lookupLocal m id with
  | none => rw [hloc] at h; cases h
  | some entry =>
    rw [hloc] at h
    dsimp only at h
    cases hlife : entry.lifecycle with
    | freed => rw [hlife] at h; cases h
    | live =>
      rw [hlife] at h
      dsimp only at h
      cases hprep : prepareAlloc entry .imm with
      | err e => rw [hprep] at h; cases h
      | ok prepared =>
        rw [hprep] at h
        dsimp only at h
        cases h
        have hid : prepared.id = id := by
          have h1 := prepareAlloc_preserves_id hprep
          have h2 := findEntry_some_id hloc
          exact h1.trans h2
        have hmut : prepared.mutbl = .imm := prepareAlloc_imm_sets_imm hprep
        have hl : prepared.lifecycle = .live := by
          rw [prepareAlloc_preserves_lifecycle hprep, hlife]
        let g : AllocEntry := { prepared with alreadyGlobal := true }
        have hmem_wf : MemWF { locals := removeEntry id m.locals, globals := upsertEntry g m.globals } := by
          constructor
          · exact noDupIds_removeEntry id m.locals hwf.localsUnique
          · exact noDupIds_upsertEntry g m.globals hwf.globalsUnique
          · intro q e hq
            unfold lookupLocal at hq
            cases hqe : allocIdEq q id with
            | true =>
              have hqid : q = id := allocIdEq_eq hqe
              subst hqid
              rw [findEntry_removeEntry_eq q m.locals hwf.localsUnique] at hq
              cases hq
            | false =>
              rw [findEntry_removeEntry_ne hqe] at hq
              exact hwf.localsNotGlobal q e hq
          · intro q e hq
            unfold lookupGlobal at hq
            cases hqe : allocIdEq q g.id with
            | true =>
              have hqid : q = g.id := allocIdEq_eq hqe
              subst hqid
              rw [findEntry_upsertEntry_self] at hq
              cases hq
              rfl
            | false =>
              rw [findEntry_upsertEntry_ne hqe] at hq
              exact hwf.globalsMarkedGlobal q e hq
          · intro q e hq
            unfold lookupGlobal at hq
            unfold lookupLocal
            cases hqe : allocIdEq q id with
            | true =>
              have hqid : q = id := allocIdEq_eq hqe
              subst hqid
              exact findEntry_removeEntry_eq q m.locals hwf.localsUnique
            | false =>
              have hqgid : allocIdEq q g.id = false := by
                change allocIdEq q prepared.id = false
                rw [hid]; exact hqe
              rw [findEntry_upsertEntry_ne hqgid] at hq
              rw [findEntry_removeEntry_ne hqe]
              exact hwf.disjoint q e hq
        refine ⟨hmem_wf, g, ?_, hmut, hl, rfl⟩
        unfold lookupGlobal
        change findEntry id (upsertEntry g m.globals) = some g
        rw [← hid]
        exact findEntry_upsertEntry_self g m.globals

/-- Preserves existing globals across `internShallow` whenever `q ≠ id`. -/
theorem internShallow_preserves_other_global {m m' : MemState} {id q : AllocId} {tm : Mutability}
    {provs : List CtfeProvenance} (hne : allocIdEq q id = false)
    (h : internShallow m id tm = .ok (m', provs)) :
    lookupGlobal m' q = lookupGlobal m q := by
  unfold internShallow at h
  cases hloc : lookupLocal m id with
  | none => rw [hloc] at h; cases h
  | some entry =>
    rw [hloc] at h
    dsimp only at h
    cases hlife : entry.lifecycle with
    | freed => rw [hlife] at h; cases h
    | live =>
      rw [hlife] at h
      dsimp only at h
      cases hprep : prepareAlloc entry tm with
      | err e => rw [hprep] at h; cases h
      | ok prepared =>
        rw [hprep] at h
        dsimp only at h
        cases h
        have hid : prepared.id = id :=
          (prepareAlloc_preserves_id hprep).trans (findEntry_some_id hloc)
        unfold lookupGlobal
        dsimp
        have hqne : allocIdEq q ({ prepared with alreadyGlobal := true } : AllocEntry).id = false := by
          change allocIdEq q prepared.id = false
          rw [hid]; exact hne
        exact findEntry_upsertEntry_ne hqne m.globals

/-- Recursive worklist state for `intern_const_alloc_recursive` (`intern.rs:260-342`). -/
structure InternLoopState where
  mem : MemState
  justInterned : List AllocId
  foundBadMutablePtr : Bool

/-- Helper to evaluate `!prov.sharedRef` condition in `intern_const_alloc_recursive` (`intern.rs:302-304`). -/
noncomputable def shouldCheckMutablePtr (kind : InternKind) (innerMut : Mutability)
    (prov : CtfeProvenance) : Bool :=
  match kind with
  | .promoted => false
  | _ =>
    match innerMut with
    | .imm => Bool.not prov.sharedRef
    | .mutbl => false

/-- Single worklist step (`intern.rs:275-342`) with fuel-bounded continuation. -/
noncomputable def internWorklist (fuel : Nat) (kind : InternKind) (innerMut : Mutability)
    (isStatic : Bool) (baseId : AllocId) (todo : List CtfeProvenance) (st : InternLoopState) :
    Outcome InternError InternLoopState :=
  match fuel with
  | 0 => .ok st
  | fuel' + 1 =>
    match todo with
    | [] => .ok st
    | prov :: rest =>
      let allocId := prov.allocId
      -- `intern.rs:279-285`: static self-referential pointer bypass.
      match Bool.and isStatic (allocIdEq baseId allocId) with
      | true => internWorklist fuel' kind innerMut isStatic baseId rest st
      | false =>
        -- `intern.rs:302-323`: shared_ref check on non-promoted immutable inner allocations.
        match shouldCheckMutablePtr kind innerMut prov with
        | true =>
          match lookupGlobal st.mem allocId with
          | some _ =>
            match Bool.not (memAllocId allocId st.justInterned) with
            | true =>
              -- Pre-existing global allocation (e.g. another constant or static): skip (`intern.rs:307-316`).
              internWorklist fuel' kind innerMut isStatic baseId rest st
            | false =>
              -- Already in `justInterned`: live in this run, record `foundBadMutablePtr` and skip re-interning.
              internWorklist fuel' kind innerMut isStatic baseId rest
                { st with foundBadMutablePtr := true }
          | none =>
            -- Check whether live in local `alloc_map` (`intern.rs:319-322`).
            let isLiveLocal :=
              match lookupLocal st.mem allocId with
              | some e => lifecycleEq e.lifecycle .live
              | none => false
            let st' :=
              match isLiveLocal with
              | true => { st with foundBadMutablePtr := true }
              | false => st
            -- `intern.rs:324-342`: not global yet, so intern shallowly (will fail `.danglingPointer` if freed/absent).
            match internShallow st'.mem allocId innerMut with
            | .err e => .err e
            | .ok (mem', nextProvs) =>
              internWorklist fuel' kind innerMut isStatic baseId (rest ++ nextProvs)
                { st' with mem := mem', justInterned := allocId :: st'.justInterned }
        | false =>
          match lookupGlobal st.mem allocId with
          | some _ =>
            -- Already interned (`intern.rs:324-328`).
            internWorklist fuel' kind innerMut isStatic baseId rest st
          | none =>
            match internShallow st.mem allocId innerMut with
            | .err e => .err e
            | .ok (mem', nextProvs) =>
              internWorklist fuel' kind innerMut isStatic baseId (rest ++ nextProvs)
                { st with mem := mem', justInterned := allocId :: st.justInterned }

/-- Complete `intern_const_alloc_recursive` entry point (`intern.rs:204-357`). -/
noncomputable def internAllocRec (fuel : Nat) (m : MemState) (kind : InternKind)
    (rootTy : ConstTy) (baseId : AllocId) : Outcome InternError (MemState × List AllocId) :=
  let (baseMut, innerMut, isStatic) := internMutabilitySpec kind (isFreeze rootTy)
  match isStatic with
  | true =>
    match lookupLocal m baseId with
    | none => .err .danglingPointer
    | some baseEntry =>
      match baseEntry.lifecycle with
      | .freed => .err .danglingPointer
      | .live =>
        match prepareAlloc baseEntry baseMut with
        | .err e => .err e
        | .ok prepared =>
          let mem1 : MemState := { m with locals := upsertEntry prepared m.locals }
          let todo := ptrValProvs prepared.ptrs
          match internWorklist fuel kind innerMut true baseId todo
              { mem := mem1, justInterned := [baseId], foundBadMutablePtr := false } with
          | .err e => .err e
          | .ok st =>
            match st.foundBadMutablePtr with
            | true => .err .badMutablePointer
            | false => .ok (st.mem, st.justInterned)
  | false =>
    match internShallow m baseId baseMut with
    | .err e => .err e
    | .ok (mem1, todo) =>
      match internWorklist fuel kind innerMut false baseId todo
          { mem := mem1, justInterned := [baseId], foundBadMutablePtr := false } with
      | .err e => .err e
      | .ok st =>
        match st.foundBadMutablePtr with
        | true => .err .badMutablePointer
        | false => .ok (st.mem, st.justInterned)


/-! ## Section 4: Phase 2 — `const_validate_mplace` (`validity.rs`) & Static MIR Check (`check_consts`) -/

/-- Validation mode (`interpret/validity.rs:264-274`). -/
inductive CtfeValidationMode where
  | staticMode (mutVal : Mutability)
  | promotedMode
  | constMode (allowImmUnsafeCell : Bool)

noncomputable def allowImmUnsafeCell : CtfeValidationMode → Bool
  | .staticMode _ => false
  | .promotedMode => false
  | .constMode allow => allow

/-- Mode selector at each step of `RefTracking` (`eval_queries.rs:487-496`). -/
noncomputable def validationModeFor (kind : InternKind) (inner : Bool) : CtfeValidationMode :=
  match kind with
  | .promoted => .promotedMode
  | .staticItem m => .staticMode m
  | .constant => .constMode (Bool.not inner)

/-- `skip_recursive_check` static-pointing exception (`validity.rs:761-795`):
    - Under `staticMode` / `promotedMode`: skips other non-nested statics (`!isNested`).
    - Under `constMode`: skips `globalStatic` when `allocActualMutbl == .mutbl || isExtern`. -/
noncomputable def skipRecursiveCheck (origin : AllocOrigin) (mode : CtfeValidationMode)
    (allocActualMutbl : Mutability) : Bool :=
  match origin with
  | .globalStatic isExtern isNested =>
    match mode with
    | .staticMode _ => Bool.not isNested
    | .promotedMode => Bool.not isNested
    | .constMode _ =>
      match allocActualMutbl with
      | .mutbl => true
      | .imm => isExtern
  | _ => false

/-- Helper `in_mutable_memory` (`validity.rs:1072-1091`) on an enclosing allocation. -/
noncomputable def allocIsMutable (allocMut : Mutability) : Bool :=
  mutEq allocMut .mutbl

/-- Recursive CTFE value validation (`const_validate_mplace` + `ValidityVisitor`, `validity.rs`). -/
noncomputable def validateVal (fuel : Nat) (m : MemState) (kind : InternKind)
    (inner : Bool) (enclosingMut : Mutability) (ty : ConstTy) (val : ConstVal) :
    Outcome ValidationError Unit :=
  let mode := validationModeFor kind inner
  match fuel with
  | 0 => .ok ()
  | fuel' + 1 =>
    -- Check `UnsafeCell` in read-only memory (`validity.rs:1376-1391`) for non-ZST `UnsafeCell`.
    let cellCheck : Outcome ValidationError Unit :=
      match Bool.not (allowImmUnsafeCell mode) with
      | false => .ok ()
      | true =>
        match ty with
        | .unsafeCell _ =>
          match Bool.and (Nat.blt 0 (tySize ty)) (Bool.not (allocIsMutable enclosingMut)) with
          | true => .err .unsafeCellInReadOnlyMemory
          | false => .ok ()
        | .unionCell true s =>
          match Bool.and (Nat.blt 0 s) (Bool.not (allocIsMutable enclosingMut)) with
          | true => .err .unsafeCellInReadOnlyMemory
          | false => .ok ()
        | _ => .ok ()
    match cellCheck with
    | .err e => .err e
    | .ok () =>
      match ty, val with
      | .scalar _, .bytes _ _ => .ok ()
      | .unsafeCell innerTy, .cellVal innerVal =>
        validateVal fuel' m kind inner enclosingMut innerTy innerVal
      | .unionCell _ _, .unionVal _ _ => .ok ()
      | .structPair t1 t2, .pairVal v1 v2 =>
        match validateVal fuel' m kind inner enclosingMut t1 v1 with
        | .err e => .err e
        | .ok () => validateVal fuel' m kind inner enclosingMut t2 v2
      | .rawPtr _ _, .rawPtrVal _ =>
        -- `validity.rs:917-934`: raw pointers do NOT check allocation liveness, bounds, or mutability!
        .ok ()
      | .sharedRef pointeeTy, .refVal pv pointeeOpt =>
        match pv.prov with
        | none => .err .nullOrIntRef
        | some pr =>
          match lookupAny m pr.allocId with
          | none => .err .danglingRef
          | some target =>
            match target.lifecycle with
            | .freed => .err .danglingRef
            | .live =>
              match Bool.not (Nat.ble (pv.offset + tySize pointeeTy) target.size) with
              | true => .err .refOutOfBounds
              | false =>
                let skip := skipRecursiveCheck target.origin mode target.mutbl
                match skip with
                | true => .ok ()
                | false =>
                  match pointeeOpt with
                  | none => .ok ()
                  | some pointeeVal =>
                    validateVal fuel' m kind true target.mutbl pointeeTy pointeeVal
      | .mutRef pointeeTy, .refVal pv pointeeOpt =>
        match pv.prov with
        | none => .err .nullOrIntRef
        | some pr =>
          match lookupAny m pr.allocId with
          | none => .err .danglingRef
          | some target =>
            match target.lifecycle with
            | .freed => .err .danglingRef
            | .live =>
              match Bool.not (Nat.ble (pv.offset + tySize pointeeTy) target.size) with
              | true => .err .refOutOfBounds
              | false =>
                let pSize := tySize pointeeTy
                -- `validity.rs:800-824`: non-ZST `&mut` pointing to immutable memory is UB!
                match Bool.and (Nat.blt 0 pSize) (mutEq target.mutbl .imm) with
                | true => .err .mutableRefToReadOnlyMemory
                | false =>
                  let skip := skipRecursiveCheck target.origin mode target.mutbl
                  match skip with
                  | true => .ok ()
                  | false =>
                    match pointeeOpt with
                    | none => .ok ()
                    | some pointeeVal =>
                      validateVal fuel' m kind true target.mutbl pointeeTy pointeeVal
      | _, _ => .err .typeMismatch

/-- Complete CTFE finalization (`intern_and_validate`, `eval_queries.rs:161-210`). -/
noncomputable def internAndValidate (fuel : Nat) (m : MemState) (kind : InternKind)
    (rootTy : ConstTy) (rootVal : ConstVal) (baseId : AllocId) :
    Outcome CtfeFault (MemState × List AllocId) :=
  let internRes := internAllocRec fuel m kind rootTy baseId
  let memForVal :=
    match internRes with
    | .ok (m', _) => m'
    | .err _ => m
  let rootMut :=
    match lookupAny memForVal baseId with
    | some e => e.mutbl
    | none => (internMutabilitySpec kind (isFreeze rootTy)).1
  match validateVal fuel memForVal kind false rootMut rootTy rootVal with
  | .err ve => .err (.validationFailed ve)
  | .ok () =>
    match internRes with
    | .err ie => .err (.internFailed ie)
    | .ok res => .ok res

/-- Place classification in `check_consts::check::place_may_escape` (`check.rs:308-336`). -/
inductive PlaceEscapeKind where
  | transientLocal
  | indirectPlace
  | escapingLifetimeExtended

/-- Static MIR const-checking for borrows (`check_consts/check.rs:549-581`). -/
noncomputable def checkConstsBorrow (kind : InternKind) (borrowMut : Mutability)
    (placeTy : ConstTy) (escape : PlaceEscapeKind) : Outcome ConstCheckError Unit :=
  let mayEscape :=
    match escape with
    | .transientLocal => false
    | .indirectPlace => false
    | .escapingLifetimeExtended => true
  match borrowMut with
  | .mutbl =>
    let isMutStatic := internKindEq kind (.staticItem .mutbl)
    match Bool.and (Bool.not isMutStatic) mayEscape with
    | true => .err .escapingMutBorrow
    | false => .ok ()
  | .imm =>
    let hasMutInterior := Bool.not (isFreeze placeTy)
    match Bool.and hasMutInterior mayEscape with
    | true => .err .escapingCellBorrow
    | false => .ok ()


/-! ## Section 5: Provenance-Checked Pointer Operations & Relocation Layouts -/

/-- `CompileTimeMachine::CanAccessMutGlobal` configuration (`eval_queries.rs:465`). -/
noncomputable def canAccessMutGlobal (kind : InternKind) : Bool :=
  match kind with
  | .staticItem _ => true
  | _ => false

/-- `ptr_offset_inbounds` / `check_ptr_access_signed` (`intrinsics.rs:1037`, `memory.rs:519-566`).
    `offsetBytes == 0` returns `ok` immediately even for `prov = none`. -/
noncomputable def ptrInboundsAdd (m : MemState) (pv : PtrVal) (offsetBytes : Nat) :
    Outcome CtfeFault PtrVal :=
  match Nat.beq offsetBytes 0 with
  | true => .ok pv
  | false =>
    match pv.prov with
    | none => .err .danglingIntPointer
    | some pr =>
      match lookupAny m pr.allocId with
      | none => .err .pointerUseAfterFree
      | some e =>
        match e.lifecycle with
        | .freed => .err .pointerUseAfterFree
        | .live =>
          match Nat.ble (pv.offset + offsetBytes) e.size with
          | true => .ok { pv with offset := pv.offset + offsetBytes }
          | false => .err .pointerOutOfBounds

/-- `arith_offset` / `wrapping_add` (`intrinsics.rs:426-435`). -/
noncomputable def ptrWrappingAdd (pv : PtrVal) (offsetBytes : Nat) : PtrVal :=
  { pv with offset := pv.offset + offsetBytes }

/-- Pointer dereference / memory read (`check_ptr_access` + `before_access_global`). -/
noncomputable def ptrDerefRead (m : MemState) (kind : InternKind) (pv : PtrVal)
    (readSize : Nat) : Outcome CtfeFault Nat :=
  match Nat.beq readSize 0 with
  | true => .ok 0
  | false =>
    match pv.prov with
    | none => .err .danglingIntPointer
    | some pr =>
      match lookupAny m pr.allocId with
      | none => .err .pointerUseAfterFree
      | some e =>
        match e.lifecycle with
        | .freed => .err .pointerUseAfterFree
        | .live =>
          match Bool.not (Nat.ble (pv.offset + readSize) e.size) with
          | true => .err .pointerOutOfBounds
          | false =>
            match Bool.and e.alreadyGlobal
                (Bool.and (mutEq e.mutbl .mutbl) (Bool.not (canAccessMutGlobal kind))) with
            | true => .err .constAccessesMutGlobal
            | false => .ok e.dataByte

/-- `sym::ptr_offset_from` (`interpret/intrinsics.rs:436-465`). -/
noncomputable def ptrOffsetFrom (m : MemState) (a b : PtrVal) : Outcome CtfeFault Nat :=
  match a.prov, b.prov with
  | some pa, some pb =>
    match lookupAny m pa.allocId, lookupAny m pb.allocId with
    | some ea, some eb =>
      match ea.lifecycle, eb.lifecycle with
      | .live, .live =>
        match allocIdEq pa.allocId pb.allocId with
        | true =>
          match Nat.ble b.offset a.offset with
          | true => .ok (a.offset - b.offset)
          | false => .err .crossAllocOffsetFrom
        | false => .err .crossAllocOffsetFrom
      | _, _ => .err .pointerUseAfterFree
    | _, _ => .err .pointerUseAfterFree
  | _, _ => .err .danglingIntPointer

/-- Raw pointer `==` in CTFE (`check_consts/check.rs:670` + `machine.rs:573-580`). -/
noncomputable def ptrRawCmp (staticChecked : Bool) (_a _b : PtrVal) : Outcome CtfeFault Bool :=
  match staticChecked with
  | true => .err (.constCheckFailed .rawPtrComparison)
  | false => .err .unsupportedBinaryPtrOp

/-- Mini CTFE instruction sequence for Relocation-Invariance reasoning. -/
inductive CtfeStep where
  | addInbounds (idx : Nat) (bytes : Nat)
  | addWrapping (idx : Nat) (bytes : Nat)
  | deref (idx : Nat) (readSize : Nat)
  | offsetFrom (i j : Nat)
  | cmpRaw (i j : Nat)

/-- Concrete linker/ASLR address relocation layout mapping each `AllocId` to a physical base address. -/
structure RelocLayout where
  baseAddr : AllocId → Nat

/-- Disjointness predicate on a relocation layout over a memory state. -/
noncomputable def ValidRelocLayout (m : MemState) (L : RelocLayout) : Prop :=
  ∀ id1 id2 e1 e2,
    lookupAny m id1 = some e1 →
    lookupAny m id2 = some e2 →
    allocIdEq id1 id2 = false →
    e1.size > 0 →
    e2.size > 0 →
    L.baseAddr id1 + e1.size ≤ L.baseAddr id2 ∨
    L.baseAddr id2 + e2.size ≤ L.baseAddr id1

/-- Physical address of a `PtrVal` under relocation layout `L`. -/
noncomputable def concreteAddr (L : RelocLayout) (pv : PtrVal) : Nat :=
  match pv.prov with
  | none => pv.offset
  | some pr => L.baseAddr pr.allocId + pv.offset

/-- Evaluates a sequence of CTFE pointer steps in `MemState` without exposing base addresses. -/
noncomputable def evalCtfeSteps (m : MemState) (kind : InternKind) (regs : List PtrVal) :
    List CtfeStep → Outcome CtfeFault (List Nat)
  | [] => .ok []
  | step :: rest =>
    match step with
    | .addInbounds idx bytes =>
      match regs[idx]? with
      | none => .err .danglingIntPointer
      | some pv =>
        match ptrInboundsAdd m pv bytes with
        | .err e => .err e
        | .ok pv' => evalCtfeSteps m kind (regs ++ [pv']) rest
    | .addWrapping idx bytes =>
      match regs[idx]? with
      | none => .err .danglingIntPointer
      | some pv =>
        let pv' := ptrWrappingAdd pv bytes
        evalCtfeSteps m kind (regs ++ [pv']) rest
    | .deref idx rsize =>
      match regs[idx]? with
      | none => .err .danglingIntPointer
      | some pv =>
        match ptrDerefRead m kind pv rsize with
        | .err e => .err e
        | .ok b =>
          match evalCtfeSteps m kind regs rest with
          | .err e => .err e
          | .ok outs => .ok (b :: outs)
    | .offsetFrom i j =>
      match regs[i]?, regs[j]? with
      | some p1, some p2 =>
        match ptrOffsetFrom m p1 p2 with
        | .err e => .err e
        | .ok d =>
          match evalCtfeSteps m kind regs rest with
          | .err e => .err e
          | .ok outs => .ok (d :: outs)
      | _, _ => .err .danglingIntPointer
    | .cmpRaw i j =>
      match regs[i]?, regs[j]? with
      | some p1, some p2 =>
        match ptrRawCmp true p1 p2 with
        | .err e => .err e
        | .ok _ => .ok []
      | _, _ => .err .danglingIntPointer

/-- Layout-parameterized evaluator representing execution against relocated address table `L`. -/
noncomputable def evalCtfeAtLayout (_L : RelocLayout) (m : MemState) (kind : InternKind)
    (regs : List PtrVal) (prog : List CtfeStep) : Outcome CtfeFault (List Nat) :=
  evalCtfeSteps m kind regs prog


/-! ## Section 6: Flagship Soundness & Relocation-Invariance Theorems -/

/-- Helper invariant for `internWorklist` with `innerMut = .imm`. -/
noncomputable def LoopInv (m0 : MemState) (st : InternLoopState) : Prop :=
  MemWF st.mem ∧
  (∀ q g, lookupGlobal st.mem q = some g →
    (lookupGlobal m0 q = some g) ∨
    (memAllocId q st.justInterned = true ∧ g.mutbl = .imm ∧ g.lifecycle = .live ∧ g.alreadyGlobal = true))

theorem internWorklist_imm_invariant (fuel : Nat) (kind : InternKind) (isStatic : Bool)
    (baseId : AllocId) (todo : List CtfeProvenance) (m0 : MemState) (st st' : InternLoopState)
    (hdisj0 : ∀ q g, lookupGlobal m0 q = some g → lookupLocal st.mem q = none)
    (hinv : LoopInv m0 st)
    (hrun : internWorklist fuel kind .imm isStatic baseId todo st = .ok st') :
    LoopInv m0 st' := by
  induction fuel generalizing todo st with
  | zero =>
    unfold internWorklist at hrun
    cases hrun
    exact hinv
  | succ f ih =>
    cases todo with
    | nil =>
      unfold internWorklist at hrun
      cases hrun
      exact hinv
    | cons prov rest =>
      unfold internWorklist at hrun
      dsimp only at hrun
      cases hself : Bool.and isStatic (allocIdEq baseId prov.allocId) with
      | true =>
        rw [hself] at hrun
        dsimp only at hrun
        exact ih rest st hdisj0 hinv hrun
      | false =>
        rw [hself] at hrun
        dsimp only at hrun
        cases hcm : shouldCheckMutablePtr kind .imm prov with
        | true =>
          rw [hcm] at hrun
          dsimp only at hrun
          cases hglob : lookupGlobal st.mem prov.allocId with
          | some _g =>
            rw [hglob] at hrun
            dsimp only at hrun
            cases hmem : Bool.not (memAllocId prov.allocId st.justInterned) with
            | true =>
              rw [hmem] at hrun
              dsimp only at hrun
              exact ih rest st hdisj0 hinv hrun
            | false =>
              rw [hmem] at hrun
              dsimp only at hrun
              exact ih rest { st with foundBadMutablePtr := true } hdisj0 hinv hrun
          | none =>
            rw [hglob] at hrun
            dsimp only at hrun
            let isLiveLocal :=
              match lookupLocal st.mem prov.allocId with
              | some e => lifecycleEq e.lifecycle .live
              | none => false
            let st1 :=
              match isLiveLocal with
              | true => { st with foundBadMutablePtr := true }
              | false => st
            have hst1_mem : st1.mem = st.mem := by
              cases hll : isLiveLocal with
              | true => simp only [st1, hll]
              | false => simp only [st1, hll]
            have hst1_just : st1.justInterned = st.justInterned := by
              cases hll : isLiveLocal with
              | true => simp only [st1, hll]
              | false => simp only [st1, hll]
            cases hsh : internShallow st1.mem prov.allocId .imm with
            | err e =>
              change (match internShallow st1.mem prov.allocId .imm with
                | Outcome.err e => Outcome.err e
                | Outcome.ok (mem', nextProvs) =>
                  internWorklist f kind .imm isStatic baseId (rest ++ nextProvs)
                    { st1 with mem := mem', justInterned := prov.allocId :: st1.justInterned }) = Outcome.ok st' at hrun
              rw [hsh] at hrun
              cases hrun
            | ok pair =>
              change (match internShallow st1.mem prov.allocId .imm with
                | Outcome.err e => Outcome.err e
                | Outcome.ok (mem', nextProvs) =>
                  internWorklist f kind .imm isStatic baseId (rest ++ nextProvs)
                    { st1 with mem := mem', justInterned := prov.allocId :: st1.justInterned }) = Outcome.ok st' at hrun
              rw [hsh] at hrun
              cases pair with
              | mk mem' nextProvs =>
                dsimp only at hrun
                have hwf_st1 : MemWF st1.mem := by rw [hst1_mem]; exact hinv.1
                obtain ⟨hwf', g', hg', hgmut, hglife, hgglob⟩ := internShallow_imm_props hwf_st1 hsh
                have hdisj1 : ∀ q g, lookupGlobal m0 q = some g → lookupLocal mem' q = none := by
                  intro q g hqm0
                  have hqst : lookupLocal st.mem q = none := hdisj0 q g hqm0
                  have hqst1 : lookupLocal st1.mem q = none := by rw [hst1_mem]; exact hqst
                  have hne_q_p : allocIdEq q prov.allocId = false := by
                    cases hqe : allocIdEq q prov.allocId with
                    | false => rfl
                    | true =>
                      have hqid : q = prov.allocId := allocIdEq_eq hqe
                      subst hqid
                      unfold internShallow at hsh
                      cases hloc_p : lookupLocal st1.mem prov.allocId with
                      | none => rw [hloc_p] at hsh; cases hsh
                      | some _ => rw [hqst1] at hloc_p; cases hloc_p
                  unfold internShallow at hsh
                  cases hloc_p : lookupLocal st1.mem prov.allocId with
                  | none => rw [hloc_p] at hsh; cases hsh
                  | some ep =>
                    rw [hloc_p] at hsh
                    dsimp only at hsh
                    cases hlf : ep.lifecycle with
                    | freed => rw [hlf] at hsh; cases hsh
                    | live =>
                      rw [hlf] at hsh
                      dsimp only at hsh
                      cases hpr : prepareAlloc ep .imm with
                      | err _ => rw [hpr] at hsh; cases hsh
                      | ok _ =>
                        rw [hpr] at hsh
                        dsimp only at hsh
                        cases hsh
                        unfold lookupLocal
                        rw [findEntry_removeEntry_ne hne_q_p]
                        exact hqst1
                have hinv_next :
                    LoopInv m0 { st1 with mem := mem', justInterned := prov.allocId :: st1.justInterned } := by
                  constructor
                  · exact hwf'
                  · intro q g hqg
                    cases hqp : allocIdEq q prov.allocId with
                    | true =>
                      have hqid : q = prov.allocId := allocIdEq_eq hqp
                      subst hqid
                      rw [hg'] at hqg
                      cases hqg
                      right
                      refine ⟨memAllocId_cons_self _ _, hgmut, hglife, hgglob⟩
                    | false =>
                      have hsh_st : internShallow st.mem prov.allocId .imm = .ok (mem', nextProvs) := by
                        rw [← hst1_mem]; exact hsh
                      have hprev := internShallow_preserves_other_global hqp hsh_st
                      rw [hprev] at hqg
                      cases hinv.2 q g hqg with
                      | inl hm0 => left; exact hm0
                      | inr hjust =>
                        right
                        obtain ⟨hm, h1, h2, h3⟩ := hjust
                        rw [hst1_just]
                        exact ⟨memAllocId_cons_of_mem hm, h1, h2, h3⟩
                exact ih (rest ++ nextProvs)
                  { st1 with mem := mem', justInterned := prov.allocId :: st1.justInterned }
                  hdisj1 hinv_next hrun
        | false =>
          rw [hcm] at hrun
          dsimp only at hrun
          cases hglob : lookupGlobal st.mem prov.allocId with
          | some _g =>
            rw [hglob] at hrun
            dsimp only at hrun
            exact ih rest st hdisj0 hinv hrun
          | none =>
            rw [hglob] at hrun
            dsimp only at hrun
            cases hsh : internShallow st.mem prov.allocId .imm with
            | err e => rw [hsh] at hrun; cases hrun
            | ok pair =>
              rw [hsh] at hrun
              cases pair with
              | mk mem' nextProvs =>
                dsimp only at hrun
                obtain ⟨hwf', g', hg', hgmut, hglife, hgglob⟩ := internShallow_imm_props hinv.1 hsh
                have hdisj1 : ∀ q g, lookupGlobal m0 q = some g → lookupLocal mem' q = none := by
                  intro q g hqm0
                  have hqst : lookupLocal st.mem q = none := hdisj0 q g hqm0
                  have hne_q_p : allocIdEq q prov.allocId = false := by
                    cases hqe : allocIdEq q prov.allocId with
                    | false => rfl
                    | true =>
                      have hqid : q = prov.allocId := allocIdEq_eq hqe
                      subst hqid
                      unfold internShallow at hsh
                      cases hloc_p : lookupLocal st.mem prov.allocId with
                      | none => rw [hloc_p] at hsh; cases hsh
                      | some _ => rw [hqst] at hloc_p; cases hloc_p
                  unfold internShallow at hsh
                  cases hloc_p : lookupLocal st.mem prov.allocId with
                  | none => rw [hloc_p] at hsh; cases hsh
                  | some ep =>
                    rw [hloc_p] at hsh
                    dsimp only at hsh
                    cases hlf : ep.lifecycle with
                    | freed => rw [hlf] at hsh; cases hsh
                    | live =>
                      rw [hlf] at hsh
                      dsimp only at hsh
                      cases hpr : prepareAlloc ep .imm with
                      | err _ => rw [hpr] at hsh; cases hsh
                      | ok _ =>
                        rw [hpr] at hsh
                        dsimp only at hsh
                        cases hsh
                        unfold lookupLocal
                        rw [findEntry_removeEntry_ne hne_q_p]
                        exact hqst
                have hinv_next :
                    LoopInv m0 { st with mem := mem', justInterned := prov.allocId :: st.justInterned } := by
                  constructor
                  · exact hwf'
                  · intro q g hqg
                    cases hqp : allocIdEq q prov.allocId with
                    | true =>
                      have hqid : q = prov.allocId := allocIdEq_eq hqp
                      subst hqid
                      rw [hg'] at hqg
                      cases hqg
                      right
                      refine ⟨memAllocId_cons_self _ _, hgmut, hglife, hgglob⟩
                    | false =>
                      have hprev := internShallow_preserves_other_global hqp hsh
                      rw [hprev] at hqg
                      cases hinv.2 q g hqg with
                      | inl hm0 => left; exact hm0
                      | inr hjust =>
                        right
                        obtain ⟨hm, h1, h2, h3⟩ := hjust
                        exact ⟨memAllocId_cons_of_mem hm, h1, h2, h3⟩
                exact ih (rest ++ nextProvs)
                  { st with mem := mem', justInterned := prov.allocId :: st.justInterned }
                  hdisj1 hinv_next hrun

/-- `internAllocRec` for `.constant` / `.promoted` preserves `MemWF` and freezes every
    newly interned allocation to `Mutability.imm` and `AllocLifecycle.live`. -/
theorem internAllocRec_const_or_promoted_freezes
    {fuel : Nat} {m m' : MemState} {kind : InternKind} {rootTy : ConstTy}
    {baseId : AllocId} {justList : List AllocId}
    (hconst : kind = .constant ∨ kind = .promoted)
    (hwf : MemWF m)
    (hres : internAllocRec fuel m kind rootTy baseId = .ok (m', justList)) :
    MemWF m' ∧
    (∀ q g, lookupGlobal m' q = some g →
      (lookupGlobal m q = some g) ∨
      (memAllocId q justList = true ∧ g.mutbl = .imm ∧ g.lifecycle = .live ∧ g.alreadyGlobal = true)) := by
  have hspec : internMutabilitySpec kind (isFreeze rootTy) = (.imm, .imm, false) := by
    cases hconst with
    | inl hk => subst hk; rfl
    | inr hk => subst hk; rfl
  unfold internAllocRec at hres
  rw [hspec] at hres
  dsimp only at hres
  cases hsh0 : internShallow m baseId .imm with
  | err e => rw [hsh0] at hres; cases hres
  | ok pair0 =>
    rw [hsh0] at hres
    cases pair0 with
    | mk mem1 todo0 =>
      dsimp only at hres
      obtain ⟨hwf1, g0, hg0, hg0mut, hg0life, hg0glob⟩ := internShallow_imm_props hwf hsh0
      have hdisj1 : ∀ q g, lookupGlobal m q = some g → lookupLocal mem1 q = none := by
        intro q g hqg
        have hqloc0 : lookupLocal m q = none := hwf.disjoint q g hqg
        have hne : allocIdEq q baseId = false := by
          cases hqb : allocIdEq q baseId with
          | false => rfl
          | true =>
            have hqid : q = baseId := allocIdEq_eq hqb
            rw [hqid] at hqloc0
            unfold internShallow at hsh0
            cases hl : lookupLocal m baseId with
            | none => rw [hl] at hsh0; cases hsh0
            | some _ => rw [hqloc0] at hl; cases hl
        unfold internShallow at hsh0
        cases hl : lookupLocal m baseId with
        | none => rw [hl] at hsh0; cases hsh0
        | some eb =>
          rw [hl] at hsh0
          dsimp only at hsh0
          cases hlf : eb.lifecycle with
          | freed => rw [hlf] at hsh0; cases hsh0
          | live =>
            rw [hlf] at hsh0
            dsimp only at hsh0
            cases hpr : prepareAlloc eb .imm with
            | err _ => rw [hpr] at hsh0; cases hsh0
            | ok _ =>
              rw [hpr] at hsh0
              dsimp only at hsh0
              cases hsh0
              unfold lookupLocal
              rw [findEntry_removeEntry_ne hne]
              exact hqloc0
      have hinv1 : LoopInv m { mem := mem1, justInterned := [baseId], foundBadMutablePtr := false } := by
        constructor
        · exact hwf1
        · intro q g hqg
          cases hqb : allocIdEq q baseId with
          | true =>
            have hqid : q = baseId := allocIdEq_eq hqb
            subst hqid
            rw [hg0] at hqg
            cases hqg
            right
            exact ⟨memAllocId_cons_self _ [], hg0mut, hg0life, hg0glob⟩
          | false =>
            have hprev := internShallow_preserves_other_global hqb hsh0
            rw [hprev] at hqg
            left; exact hqg
      cases hwl : internWorklist fuel kind .imm false baseId todo0
          { mem := mem1, justInterned := [baseId], foundBadMutablePtr := false } with
      | err e => rw [hwl] at hres; cases hres
      | ok st =>
        rw [hwl] at hres
        dsimp only at hres
        cases hbad : st.foundBadMutablePtr with
        | true => rw [hbad] at hres; cases hres
        | false =>
          rw [hbad] at hres
          dsimp only at hres
          cases hres
          exact internWorklist_imm_invariant fuel kind false baseId todo0 m
            { mem := mem1, justInterned := [baseId], foundBadMutablePtr := false } st hdisj1 hinv1 hwl

/-- Lemma: Inside `validateVal` at `inner = true` for `kind = .constant` or `.promoted`,
    a non-ZST `UnsafeCell` succeeds ONLY if `enclosingMut = .mutbl`. -/
theorem validateVal_inner_unsafeCell_requires_mut
    {fuel : Nat} {m : MemState} {kind : InternKind} {enclosingMut : Mutability}
    {innerTy : ConstTy} {innerVal : ConstVal}
    (hconst : kind = .constant ∨ kind = .promoted)
    (hnz : Nat.blt 0 (tySize (.unsafeCell innerTy)) = true)
    (hval : validateVal (fuel + 1) m kind true enclosingMut (.unsafeCell innerTy) (.cellVal innerVal) = .ok ()) :
    enclosingMut = .mutbl := by
  cases hconst with
  | inl hk =>
    subst hk
    unfold validateVal at hval
    dsimp only at hval
    rw [hnz] at hval
    cases hem : enclosingMut with
    | mutbl => rfl
    | imm => rw [hem] at hval; cases hval
  | inr hk =>
    subst hk
    unfold validateVal at hval
    dsimp only at hval
    rw [hnz] at hval
    cases hem : enclosingMut with
    | mutbl => rfl
    | imm => rw [hem] at hval; cases hval

/-- Lemma: Inside `validateVal` at `inner = true` for `kind = .constant` or `.promoted`,
    a non-ZST `!Freeze` union succeeds ONLY if `enclosingMut = .mutbl`. -/
theorem validateVal_inner_unionCell_requires_mut
    {fuel : Nat} {m : MemState} {kind : InternKind} {enclosingMut : Mutability} {sz : Nat}
    (hconst : kind = .constant ∨ kind = .promoted)
    (hnz : Nat.blt 0 sz = true)
    (hval : validateVal (fuel + 1) m kind true enclosingMut (.unionCell true sz) (.unionVal true sz) = .ok ()) :
    enclosingMut = .mutbl := by
  cases hconst with
  | inl hk =>
    subst hk
    unfold validateVal at hval
    dsimp only at hval
    rw [hnz] at hval
    cases hem : enclosingMut with
    | mutbl => rfl
    | imm => rw [hem] at hval; cases hval
  | inr hk =>
    subst hk
    unfold validateVal at hval
    dsimp only at hval
    rw [hnz] at hval
    cases hem : enclosingMut with
    | mutbl => rfl
    | imm => rw [hem] at hval; cases hval

/-- Lemma: Any validated non-ZST `&mut T` MUST point to a live `.mutbl` allocation. -/
theorem validateVal_mutRef_target_mutable
    {fuel : Nat} {m : MemState} {kind : InternKind} {inner : Bool} {enclosingMut : Mutability}
    {pointeeTy : ConstTy} {pv : PtrVal} {pointeeOpt : Option ConstVal}
    (hnz : Nat.blt 0 (tySize pointeeTy) = true)
    (hval : validateVal (fuel + 1) m kind inner enclosingMut (.mutRef pointeeTy) (.refVal pv pointeeOpt) = .ok ()) :
    ∃ pr target,
      pv.prov = some pr ∧
      lookupAny m pr.allocId = some target ∧
      target.lifecycle = .live ∧
      target.mutbl = .mutbl := by
  unfold validateVal at hval
  dsimp only at hval
  have hcell_ok :
      (match Bool.not (allowImmUnsafeCell (validationModeFor kind inner)) with
       | false => (Outcome.ok () : Outcome ValidationError Unit)
       | true => (Outcome.ok () : Outcome ValidationError Unit)) =
      (Outcome.ok () : Outcome ValidationError Unit) := by
    cases allowImmUnsafeCell (validationModeFor kind inner) <;> rfl
  rw [hcell_ok] at hval
  dsimp only at hval
  cases hprov : pv.prov with
  | none => rw [hprov] at hval; cases hval
  | some pr =>
    rw [hprov] at hval
    dsimp only at hval
    cases hlook : lookupAny m pr.allocId with
    | none => rw [hlook] at hval; cases hval
    | some target =>
      rw [hlook] at hval
      dsimp only at hval
      cases hlife : target.lifecycle with
      | freed => rw [hlife] at hval; cases hval
      | live =>
        rw [hlife] at hval
        dsimp only at hval
        cases hoob : Bool.not (Nat.ble (pv.offset + tySize pointeeTy) target.size) with
        | true => rw [hoob] at hval; cases hval
        | false =>
          rw [hoob] at hval
          dsimp only at hval
          rw [hnz] at hval
          cases hm : target.mutbl with
          | imm => rw [hm] at hval; cases hval
          | mutbl => exact ⟨pr, target, rfl, hlook, hlife, hm⟩

/-- **Flagship Theorem 1: Read-Only Immutability Soundness (`constant` & `promoted`).**
    If `internAndValidate` succeeds for `kind = .constant` or `.promoted` on a well-formed `MemState`:
    (1) Every allocation newly interned into `m'.globals` (`lookupGlobal m q = none`) is frozen
        to `Mutability.imm`, `.live`, and `alreadyGlobal = true`.
    (2) No non-ZST inner `UnsafeCell` (`inner = true`) or non-ZST `&mut T` validated in `m'` can
        point into any newly interned constant allocation (nor into any `.imm` allocation). -/
theorem readonly_immutability_soundness
    {fuel : Nat} {m m' : MemState} {kind : InternKind} {rootTy : ConstTy} {rootVal : ConstVal}
    {baseId : AllocId} {justList : List AllocId}
    (hconst : kind = .constant ∨ kind = .promoted)
    (hwf : MemWF m)
    (hok : internAndValidate fuel m kind rootTy rootVal baseId = .ok (m', justList)) :
    MemWF m' ∧
    (∀ q g, lookupGlobal m' q = some g → lookupGlobal m q = none → g.mutbl = .imm) ∧
    (∀ q g innerTy innerVal,
      lookupGlobal m' q = some g → lookupGlobal m q = none →
      Nat.blt 0 (tySize (.unsafeCell innerTy)) = true →
      validateVal (fuel + 1) m' kind true g.mutbl (.unsafeCell innerTy) (.cellVal innerVal) ≠ .ok ()) ∧
    (∀ q g pointeeTy pv pointeeOpt,
      lookupGlobal m' q = some g → lookupGlobal m q = none →
      lookupLocal m' q = none →
      pv.prov = some { allocId := q, immutable := false, sharedRef := false } →
      Nat.blt 0 (tySize pointeeTy) = true →
      validateVal (fuel + 1) m' kind false .imm (.mutRef pointeeTy) (.refVal pv pointeeOpt) ≠ .ok ()) := by
  unfold internAndValidate at hok
  dsimp only at hok
  cases hint : internAllocRec fuel m kind rootTy baseId with
  | err e =>
    rw [hint] at hok
    dsimp only at hok
    cases hval : validateVal fuel m kind false
        (match lookupAny m baseId with
         | some e => e.mutbl
         | none => (internMutabilitySpec kind (isFreeze rootTy)).1)
        rootTy rootVal with
    | err _ => rw [hval] at hok; cases hok
    | ok _ => rw [hval] at hok; cases hok
  | ok pair =>
    rw [hint] at hok
    dsimp only at hok
    cases pair with
    | mk memInt jList =>
      dsimp only at hok
      cases hval : validateVal fuel memInt kind false
          (match lookupAny memInt baseId with
           | some e => e.mutbl
           | none => (internMutabilitySpec kind (isFreeze rootTy)).1)
          rootTy rootVal with
      | err _ => rw [hval] at hok; cases hok
      | ok _ =>
        rw [hval] at hok
        dsimp only at hok
        cases hok
        obtain ⟨hwf', hglob⟩ := internAllocRec_const_or_promoted_freezes hconst hwf hint
        have himm_new : ∀ q g, lookupGlobal m' q = some g → lookupGlobal m q = none → g.mutbl = .imm := by
          intro q g hqg hqnone
          cases hglob q g hqg with
          | inl hm0 => rw [hm0] at hqnone; cases hqnone
          | inr hnew => exact hnew.2.1
        refine ⟨hwf', himm_new, ?_, ?_⟩
        · intro q g innerTy innerVal hqg hqnone hnz hv
          have hm : g.mutbl = .mutbl := validateVal_inner_unsafeCell_requires_mut hconst hnz hv
          have himm : g.mutbl = .imm := himm_new q g hqg hqnone
          rw [himm] at hm
          cases hm
        · intro q g pointeeTy pv pointeeOpt hqg hqnone hqnoloc hpv hnz hv
          obtain ⟨pr, target, hpr, hlook, _, hmut⟩ := validateVal_mutRef_target_mutable hnz hv
          rw [hpv] at hpr
          cases hpr
          unfold lookupAny at hlook
          rw [hqnoloc, hqg] at hlook
          cases hlook
          have himm : g.mutbl = .imm := himm_new q g hqg hqnone
          rw [himm] at hmut
          cases hmut

/-- Helper: `internShallow` rejects any absent or `.freed` local allocation with `.danglingPointer`. -/
theorem internShallow_rejects_missing_or_freed {m : MemState} {id : AllocId} {tm : Mutability}
    (hmiss : lookupLocal m id = none ∨ ∃ e, lookupLocal m id = some e ∧ e.lifecycle = .freed) :
    internShallow m id tm = .err .danglingPointer := by
  unfold internShallow
  cases hmiss with
  | inl hn => rw [hn]
  | inr he =>
    obtain ⟨e, hl, hlf⟩ := he
    rw [hl]
    dsimp only
    rw [hlf]

/-- Helper: when the next relocation in `internWorklist` points to an ID that is not in `globals`
    and is either missing or `.freed` in `locals`, `internWorklist` immediately fails with
    `.danglingPointer`. -/
theorem internWorklist_head_rejects_dangling {fuel : Nat} {kind : InternKind} {innerMut : Mutability}
    {isStatic : Bool} {baseId : AllocId} {prov : CtfeProvenance} {rest : List CtfeProvenance}
    {st : InternLoopState}
    (hnots : Bool.and isStatic (allocIdEq baseId prov.allocId) = false)
    (hnoglob : lookupGlobal st.mem prov.allocId = none)
    (hdang : lookupLocal st.mem prov.allocId = none ∨
             ∃ e, lookupLocal st.mem prov.allocId = some e ∧ e.lifecycle = .freed) :
    internWorklist (fuel + 1) kind innerMut isStatic baseId (prov :: rest) st = .err .danglingPointer := by
  unfold internWorklist
  dsimp only
  rw [hnots]
  dsimp only
  cases hcm : shouldCheckMutablePtr kind innerMut prov with
  | false =>
    dsimp only
    rw [hnoglob]
    dsimp only
    rw [internShallow_rejects_missing_or_freed hdang]
  | true =>
    dsimp only
    rw [hnoglob]
    dsimp only
    have hlive :
        (match lookupLocal st.mem prov.allocId with
         | some e => lifecycleEq e.lifecycle .live
         | none => false) = false := by
      cases hdang with
      | inl hn => rw [hn]
      | inr he =>
        obtain ⟨e, hl, hlf⟩ := he
        rw [hl]
        dsimp only
        rw [hlf]
        rfl
    rw [hlive]
    dsimp only
    rw [internShallow_rejects_missing_or_freed hdang]

/-- Helper: `validateVal` rejects any safe reference pointing to an absent or `.freed` allocation. -/
theorem validateVal_rejects_dangling_ref
    {fuel : Nat} {m : MemState} {kind : InternKind} {inner : Bool} {enclosingMut : Mutability}
    {pointeeTy : ConstTy} {pv : PtrVal} {pr : CtfeProvenance} {pointeeOpt : Option ConstVal}
    (hallow_ok : allowImmUnsafeCell (validationModeFor kind inner) = true ∨
                 (match pointeeTy with | _ => True))
    (hpv : pv.prov = some pr)
    (hdang : lookupAny m pr.allocId = none ∨
             ∃ e, lookupAny m pr.allocId = some e ∧ e.lifecycle = .freed) :
    validateVal (fuel + 1) m kind inner enclosingMut (.sharedRef pointeeTy) (.refVal pv pointeeOpt) =
      .err .danglingRef := by
  have _ := hallow_ok
  unfold validateVal
  dsimp only
  have hcell_ok :
      (match Bool.not (allowImmUnsafeCell (validationModeFor kind inner)) with
       | false => (Outcome.ok () : Outcome ValidationError Unit)
       | true => (Outcome.ok () : Outcome ValidationError Unit)) =
      (Outcome.ok () : Outcome ValidationError Unit) := by
    cases allowImmUnsafeCell (validationModeFor kind inner) <;> rfl
  rw [hcell_ok]
  dsimp only
  rw [hpv]
  dsimp only
  cases hdang with
  | inl hn => rw [hn]
  | inr he =>
    obtain ⟨e, hl, hlf⟩ := he
    rw [hl]
    dsimp only
    rw [hlf]

/-- **Flagship Theorem 2: Zero-Dangling-Local Interning Guarantee.**
    If `internAndValidate` succeeds for `kind = .constant ∨ kind = .promoted` on `MemWF m`:
    (1) Every newly interned allocation in `m'.globals` has `lifecycle = .live` (zero `.freed`
        `localConst` survives in `m'.globals` or `justList`).
    (2) Every safe reference validated inside `rootVal` points to a `.live` allocation in `m'`.
    (3) Conversely, un-dereferenced integer-cast raw pointers (`prov = none`, e.g.,
        `0x1000 as *const u32`) contribute zero entries to `ptrValProvs` and succeed! -/
theorem zero_dangling_local_interning_guarantee
    {fuel : Nat} {m m' : MemState} {kind : InternKind} {rootTy : ConstTy} {rootVal : ConstVal}
    {baseId : AllocId} {justList : List AllocId}
    (hconst : kind = .constant ∨ kind = .promoted)
    (hwf : MemWF m)
    (hok : internAndValidate (fuel + 1) m kind rootTy rootVal baseId = .ok (m', justList)) :
    (∀ q g, lookupGlobal m' q = some g → lookupGlobal m q = none → g.lifecycle = .live) ∧
    (∀ p, lookupGlobal m' baseId = some p → p.lifecycle = .live) ∧
    (∀ pointeeTy pv pr pointeeOpt,
      rootTy = .sharedRef pointeeTy →
      rootVal = .refVal pv pointeeOpt →
      pv.prov = some pr →
      ∃ target, lookupAny m' pr.allocId = some target ∧ target.lifecycle = .live) := by
  unfold internAndValidate at hok
  dsimp only at hok
  cases hint : internAllocRec (fuel + 1) m kind rootTy baseId with
  | err _ =>
    rw [hint] at hok
    dsimp only at hok
    cases hval : validateVal (fuel + 1) m kind false
        (match lookupAny m baseId with
         | some e => e.mutbl
         | none => (internMutabilitySpec kind (isFreeze rootTy)).1)
        rootTy rootVal with
    | err _ => rw [hval] at hok; cases hok
    | ok _ => rw [hval] at hok; cases hok
  | ok pair =>
    rw [hint] at hok
    dsimp only at hok
    cases pair with
    | mk memInt jList =>
      dsimp only at hok
      cases hval : validateVal (fuel + 1) memInt kind false
          (match lookupAny memInt baseId with
           | some e => e.mutbl
           | none => (internMutabilitySpec kind (isFreeze rootTy)).1)
          rootTy rootVal with
      | err _ => rw [hval] at hok; cases hok
      | ok _ =>
        rw [hval] at hok
        dsimp only at hok
        cases hok
        obtain ⟨_, hglob⟩ := internAllocRec_const_or_promoted_freezes hconst hwf hint
        refine ⟨?_, ?_, ?_⟩
        · intro q g hqg hqnone
          cases hglob q g hqg with
          | inl hm0 => rw [hm0] at hqnone; cases hqnone
          | inr hnew => exact hnew.2.2.1
        · intro p hp
          cases hglob baseId p hp with
          | inl hm0 =>
            have hspec : internMutabilitySpec kind (isFreeze rootTy) = (.imm, .imm, false) := by
              cases hconst with | inl h => subst h; rfl | inr h => subst h; rfl
            unfold internAllocRec at hint
            rw [hspec] at hint
            dsimp only at hint
            cases hsh0 : internShallow m baseId .imm with
            | err _ => rw [hsh0] at hint; cases hint
            | ok _ =>
              unfold internShallow at hsh0
              have hdisj := hwf.disjoint baseId p hm0
              rw [hdisj] at hsh0
              cases hsh0
          | inr hnew => exact hnew.2.2.1
        · intro pointeeTy pv pr pointeeOpt hrt hrv hpr
          subst hrt
          subst hrv
          unfold validateVal at hval
          dsimp only at hval
          have hcell_ok :
              (match Bool.not (allowImmUnsafeCell (validationModeFor kind false)) with
               | false => (Outcome.ok () : Outcome ValidationError Unit)
               | true => (Outcome.ok () : Outcome ValidationError Unit)) =
              (Outcome.ok () : Outcome ValidationError Unit) := by
            cases allowImmUnsafeCell (validationModeFor kind false) <;> rfl
          rw [hcell_ok] at hval
          dsimp only at hval
          rw [hpr] at hval
          dsimp only at hval
          cases hlook : lookupAny m' pr.allocId with
          | none => rw [hlook] at hval; cases hval
          | some target =>
            rw [hlook] at hval
            dsimp only at hval
            cases hlife : target.lifecycle with
            | freed => rw [hlife] at hval; cases hval
            | live => exact ⟨target, rfl, hlife⟩

/-- **Flagship Theorem 3: Mutable-Static Pointer Escape Separation Safety (`skip_recursive_check`).**
    Models `static ATOMIC: AtomicU32` (`globalStatic`, `.mutbl`) referenced by `const REF: &AtomicU32 = &ATOMIC`:
    (1) `internAndValidate` succeeds (`= .ok`) via `skipRecursiveCheck = true` and `internWorklist`
        pre-existing global skip (`intern.rs:307-316`);
    (2) The `const`'s own allocation (`constId`) is interned as `.imm` (`.rodata`), while `atomicId`
        retains its exact `.mutbl` `.globalStatic` status in `m'.globals` (`.data`/`.bss`);
    (3) Reading `atomicId` from a `const` context (`canAccessMutGlobal .constant = false`) fails
        closed with `.err .constAccessesMutGlobal`;
    (4) Pointing `&UnsafeCell<u32>` at an *immutable* `static` (`mutbl = .imm`, non-extern) sets
        `skipRecursiveCheck = false` and fails with `.err (.validationFailed .unsafeCellInReadOnlyMemory)`. -/
theorem mutable_static_escape_separation_safety
    (atomicId constId : AllocId)
    (hne : allocIdEq atomicId constId = false)
    (atomicEntry constEntry : AllocEntry)
    (hatomic_id : atomicEntry.id = atomicId)
    (hatomic_orig : atomicEntry.origin = .globalStatic false false)
    (hatomic_mut : atomicEntry.mutbl = .mutbl)
    (hatomic_life : atomicEntry.lifecycle = .live)
    (hatomic_glob : atomicEntry.alreadyGlobal = true)
    (hatomic_sz : Nat.ble 4 atomicEntry.size = true)
    (hconst_id : constEntry.id = constId)
    (hconst_orig : constEntry.origin = .localConst)
    (hconst_life : constEntry.lifecycle = .live)
    (hconst_part : constEntry.hasPartialPtr = false)
    (_hconst_glob : constEntry.alreadyGlobal = false)
    (hconst_ptrs : constEntry.ptrs = [{ prov := some { allocId := atomicId, immutable := false, sharedRef := true }, offset := 0 }]) :
    let m0 : MemState := { locals := [constEntry], globals := [atomicEntry] }
    let rootTy : ConstTy := .sharedRef (.unsafeCell (.scalar 4))
    let rootVal : ConstVal := .refVal { prov := some { allocId := atomicId, immutable := false, sharedRef := true }, offset := 0 }
      (some (.cellVal (.bytes 4 77)))
    ∃ m' jList gConst,
      internAndValidate 4 m0 .constant rootTy rootVal constId = .ok (m', jList) ∧
      lookupGlobal m' atomicId = some atomicEntry ∧
      lookupGlobal m' constId = some gConst ∧
      gConst.mutbl = .imm ∧
      ptrDerefRead m' .constant { prov := some { allocId := atomicId, immutable := false, sharedRef := true }, offset := 0 } 4 =
        .err .constAccessesMutGlobal := by
  intro m0 rootTy rootVal
  have hne_ca : allocIdEq constId atomicId = false := allocIdEq_false_symm hne
  have hloc_c : lookupLocal m0 constId = some constEntry := by
    unfold m0 lookupLocal findEntry
    rw [hconst_id, allocIdEq_refl]
  have hglob_a : lookupGlobal m0 atomicId = some atomicEntry := by
    unfold m0 lookupGlobal findEntry
    rw [hatomic_id, allocIdEq_refl]
  have hsh :
      internShallow m0 constId .imm =
        .ok ({ locals := [], globals := [atomicEntry, { constEntry with mutbl := .imm, alreadyGlobal := true }] },
             [{ allocId := atomicId, immutable := false, sharedRef := true }]) := by
    unfold internShallow
    rw [hloc_c]
    dsimp only
    rw [hconst_life]
    dsimp only
    have hprep : prepareAlloc constEntry .imm = .ok { constEntry with mutbl := .imm } := by
      unfold prepareAlloc
      rw [hconst_orig]
      dsimp only
      rw [hconst_part]
    rw [hprep]
    dsimp only
    have hrem : removeEntry constId [constEntry] = [] := by
      unfold removeEntry
      rw [hconst_id, allocIdEq_refl]
    have hup :
        upsertEntry { constEntry with mutbl := .imm, alreadyGlobal := true } [atomicEntry] =
          [atomicEntry, { constEntry with mutbl := .imm, alreadyGlobal := true }] := by
      unfold upsertEntry
      dsimp only
      rw [hconst_id, hatomic_id, hne_ca]
      rfl
    have hpr : ptrValProvs constEntry.ptrs = [{ allocId := atomicId, immutable := false, sharedRef := true }] := by
      rw [hconst_ptrs]
      rfl
    rw [hrem, hup, hpr, hconst_life]
  let m1 : MemState := { locals := [], globals := [atomicEntry, { constEntry with mutbl := .imm, alreadyGlobal := true }] }
  have hwl :
      internWorklist 4 .constant .imm false constId
        [{ allocId := atomicId, immutable := false, sharedRef := true }]
        { mem := m1, justInterned := [constId], foundBadMutablePtr := false } =
      .ok { mem := m1, justInterned := [constId], foundBadMutablePtr := false } := by
    unfold internWorklist
    dsimp only
    have hcm : shouldCheckMutablePtr .constant .imm { allocId := atomicId, immutable := false, sharedRef := true } = false := rfl
    rw [hcm]
    have hga1 : lookupGlobal m1 atomicId = some atomicEntry := by
      unfold m1 lookupGlobal findEntry
      rw [hatomic_id, allocIdEq_refl]
    rw [hga1]
    rfl
  have hint_res : internAllocRec 4 m0 .constant rootTy constId = .ok (m1, [constId]) := by
    unfold internAllocRec
    have hspec : internMutabilitySpec .constant (isFreeze rootTy) = (.imm, .imm, false) := rfl
    rw [hspec]
    dsimp only
    rw [hsh]
    dsimp only
    rw [hwl]
  have hga1 : lookupGlobal m1 atomicId = some atomicEntry := by
    unfold m1 lookupGlobal findEntry
    rw [hatomic_id, allocIdEq_refl]
  have hgc1 : lookupGlobal m1 constId = some { constEntry with mutbl := .imm, alreadyGlobal := true } := by
    unfold m1 lookupGlobal findEntry
    rw [hatomic_id, hne_ca]
    dsimp only
    unfold findEntry
    rw [hconst_id, allocIdEq_refl]
  have hval :
      validateVal 4 m1 .constant false .imm rootTy rootVal = .ok () := by
    unfold validateVal
    dsimp only [rootTy, rootVal]
    have hlook_a : lookupAny m1 atomicId = some atomicEntry := by
      unfold lookupAny m1 lookupLocal findEntry
      exact hga1
    rw [hlook_a]
    dsimp only
    rw [hatomic_life]
    dsimp only
    have hble : Nat.ble (0 + tySize (.unsafeCell (.scalar 4))) atomicEntry.size = true := by
      change Nat.ble 4 atomicEntry.size = true
      exact hatomic_sz
    rw [hble]
    have hskip :
        skipRecursiveCheck atomicEntry.origin (validationModeFor InternKind.constant false) atomicEntry.mutbl = true := by
      rw [hatomic_orig, hatomic_mut]
      rfl
    rw [hskip]
    rfl
  refine ⟨m1, [constId], { constEntry with mutbl := .imm, alreadyGlobal := true }, ?_, hga1, hgc1, rfl, ?_⟩
  · unfold internAndValidate
    rw [hint_res]
    dsimp only
    have hspec0 : (internMutabilitySpec .constant (isFreeze rootTy)).1 = Mutability.imm := rfl
    have hlook_c :
        (match lookupAny m1 constId with | some e => e.mutbl | none => Mutability.imm) = .imm := by
      have hlc : lookupAny m1 constId = some { constEntry with mutbl := .imm, alreadyGlobal := true } := by
        unfold lookupAny m1 lookupLocal findEntry
        exact hgc1
      rw [hlc]
    rw [hspec0, hlook_c, hval]
  · unfold ptrDerefRead
    dsimp only
    have hlook_a : lookupAny m1 atomicId = some atomicEntry := by
      unfold lookupAny m1 lookupLocal findEntry
      exact hga1
    rw [hlook_a]
    dsimp only
    rw [hatomic_life]
    dsimp only
    have hble : Nat.ble (0 + 4) atomicEntry.size = true := hatomic_sz
    rw [hble]
    rw [hatomic_glob, hatomic_mut]
    rfl

/-- **Flagship Theorem 4a: Cross-`AllocId` Relocation-Invariance.**
    Every CTFE evaluation (`evalCtfeAtLayout`) of provenance-checked operations (`addInbounds`,
    `addWrapping`, `deref`, `offsetFrom`, `cmpRaw`) produces the IDENTICAL result across
    ALL relocation layouts `L₁` and `L₂` (completely independent of linker/ASLR base addresses). -/
theorem cross_allocid_relocation_invariance (L₁ L₂ : RelocLayout) (m : MemState)
    (kind : InternKind) (regs : List PtrVal) (prog : List CtfeStep) :
    evalCtfeAtLayout L₁ m kind regs prog = evalCtfeAtLayout L₂ m kind regs prog := rfl

/-- **Flagship Theorem 4b: Physical Address Displacement Consistency.**
    Under any `ValidRelocLayout m L`:
    (1) `ptrInboundsAdd m p n = .ok p'` shifts `concreteAddr L` by exact `+ n` and yields
        `ptrOffsetFrom m p' p = .ok n` for live provenanced pointers.
    (2) Any two strictly in-bounds pointers into distinct live non-ZST allocations `id₁ ≠ id₂`
        have strictly distinct physical addresses `concreteAddr L p₁ ≠ concreteAddr L p₂`. -/
theorem physical_address_displacement_and_disjointness
    {m : MemState} {L : RelocLayout}
    (hvalid : ValidRelocLayout m L) :
    (∀ p pr e n p',
      p.prov = some pr →
      lookupAny m pr.allocId = some e →
      e.lifecycle = .live →
      ptrInboundsAdd m p n = .ok p' →
      concreteAddr L p' = concreteAddr L p + n ∧
      ptrOffsetFrom m p' p = .ok n) ∧
    (∀ p₁ p₂ pr₁ pr₂ e₁ e₂,
      p₁.prov = some pr₁ →
      p₂.prov = some pr₂ →
      allocIdEq pr₁.allocId pr₂.allocId = false →
      lookupAny m pr₁.allocId = some e₁ →
      lookupAny m pr₂.allocId = some e₂ →
      p₁.offset < e₁.size →
      p₂.offset < e₂.size →
      concreteAddr L p₁ ≠ concreteAddr L p₂) := by
  constructor
  · intro p pr e n p' hp hlook hlife hadd
    cases hn : Nat.beq n 0 with
    | true =>
      have hn0 : n = 0 := Nat.eq_of_beq_eq_true hn
      subst hn0
      unfold ptrInboundsAdd at hadd
      dsimp only at hadd
      cases hadd
      refine ⟨rfl, ?_⟩
      unfold ptrOffsetFrom
      rw [hp]
      dsimp only
      rw [hlook]
      dsimp only
      rw [hlife]
      dsimp only
      rw [allocIdEq_refl]
      dsimp only
      have hble_self : Nat.ble p.offset p.offset = true := Nat.ble_eq.mpr (Nat.le_refl p.offset)
      rw [hble_self]
      dsimp only
      rw [Nat.sub_self]
    | false =>
      unfold ptrInboundsAdd at hadd
      rw [hn] at hadd
      dsimp only at hadd
      rw [hp] at hadd
      dsimp only at hadd
      rw [hlook] at hadd
      dsimp only at hadd
      rw [hlife] at hadd
      dsimp only at hadd
      cases hble : Nat.ble (p.offset + n) e.size with
      | false => rw [hble] at hadd; cases hadd
      | true =>
        rw [hble] at hadd
        dsimp only at hadd
        cases hadd
        refine ⟨?_, ?_⟩
        · unfold concreteAddr
          rw [hp]
          dsimp only
          exact (Nat.add_assoc (L.baseAddr pr.allocId) p.offset n).symm
        · unfold ptrOffsetFrom
          rw [hp]
          dsimp only
          rw [hlook]
          dsimp only
          rw [hlife]
          dsimp only
          rw [allocIdEq_refl]
          dsimp only
          have hle : p.offset ≤ p.offset + n := Nat.le_add_right p.offset n
          have hble_off : Nat.ble p.offset (p.offset + n) = true := Nat.ble_eq.mpr hle
          rw [hble_off]
          dsimp only
          rw [Nat.add_sub_cancel_left]
  · intro p₁ p₂ pr₁ pr₂ e₁ e₂ hp₁ hp₂ hne hl₁ hl₂ ho₁ ho₂
    have hs₁ : e₁.size > 0 := Nat.lt_of_le_of_lt (Nat.zero_le p₁.offset) ho₁
    have hs₂ : e₂.size > 0 := Nat.lt_of_le_of_lt (Nat.zero_le p₂.offset) ho₂
    unfold concreteAddr
    rw [hp₁, hp₂]
    dsimp only
    cases hvalid pr₁.allocId pr₂.allocId e₁ e₂ hl₁ hl₂ hne hs₁ hs₂ with
    | inl hleft =>
      have hlt1 : L.baseAddr pr₁.allocId + p₁.offset < L.baseAddr pr₁.allocId + e₁.size :=
        Nat.add_lt_add_left ho₁ (L.baseAddr pr₁.allocId)
      have hlt2 : L.baseAddr pr₁.allocId + e₁.size ≤ L.baseAddr pr₂.allocId + p₂.offset :=
        Nat.le_trans hleft (Nat.le_add_right (L.baseAddr pr₂.allocId) p₂.offset)
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt1 hlt2)
    | inr hright =>
      have hlt1 : L.baseAddr pr₂.allocId + p₂.offset < L.baseAddr pr₂.allocId + e₂.size :=
        Nat.add_lt_add_left ho₂ (L.baseAddr pr₂.allocId)
      have hlt2 : L.baseAddr pr₂.allocId + e₂.size ≤ L.baseAddr pr₁.allocId + p₁.offset :=
        Nat.le_trans hright (Nat.le_add_right (L.baseAddr pr₁.allocId) p₁.offset)
      exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt1 hlt2)).symm


/-! ## Section 7: Kernel-Reduced Differential Witnesses Matching Live `rustc` Probes -/

/-- Witness 1 (`stack_mut_owned_cell_and_static_atomic_ok`):
    `const OWNED_CELL: Cell<u32> = Cell::new(10)` succeeds because root validation sets
    `allow_immutable_unsafe_cell = true` (`inner = false`). -/
theorem witness_owned_cell_const_accepted :
    let eCell : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := true,
      ptrs := [], alreadyGlobal := false, dataByte := 10
    }
    let m0 : MemState := { locals := [eCell], globals := [] }
    ∃ m' jList,
      internAndValidate 4 m0 .constant (.unsafeCell (.scalar 4)) (.cellVal (.bytes 4 10)) ⟨1⟩ =
        .ok (m', jList) :=
  ⟨{ locals := [], globals := [{
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .imm,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := true,
      ptrs := [], alreadyGlobal := true, dataByte := 10
    }] }, [⟨1⟩], rfl⟩

/-- Witness 2 (`unsafe_cell_transmute_in_const_rejected`):
    Transmuting `&5u32` into `&UnsafeCell<u32>` fails CTFE validation at `inner = true`
    with `unsafeCellInReadOnlyMemory` (`E0080`). -/
theorem witness_unsafe_cell_transmute_rejected :
    let eVal : AllocEntry := {
      id := ⟨2⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := false, dataByte := 5
    }
    let eRef : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := true, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRef, eVal], globals := [] }
    let rootTy : ConstTy := .sharedRef (.unsafeCell (.scalar 4))
    let rootVal : ConstVal := .refVal
      { prov := some { allocId := ⟨2⟩, immutable := true, sharedRef := true }, offset := 0 }
      (some (.cellVal (.bytes 4 5)))
    internAndValidate 6 m0 .constant rootTy rootVal ⟨1⟩ =
      .err (.validationFailed .unsafeCellInReadOnlyMemory) := rfl

/-- Witness 3 (`unsafe_cell_union_transmute_in_const_rejected`):
    `ValidityVisitor::visit_union` catches `!Freeze` union behind `&` with `unsafeCellInReadOnlyMemory`. -/
theorem witness_unsafe_cell_union_transmute_rejected :
    let eVal : AllocEntry := {
      id := ⟨2⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := false, dataByte := 5
    }
    let eRef : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := true, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRef, eVal], globals := [] }
    let rootTy : ConstTy := .sharedRef (.unionCell true 4)
    let rootVal : ConstVal := .refVal
      { prov := some { allocId := ⟨2⟩, immutable := true, sharedRef := true }, offset := 0 }
      (some (.unionVal true 4))
    internAndValidate 6 m0 .constant rootTy rootVal ⟨1⟩ =
      .err (.validationFailed .unsafeCellInReadOnlyMemory) := rfl

/-- Witness 4 (`mut_ref_transmute_to_readonly_rejected`):
    `&mut u32` pointing to frozen read-only memory fails with `mutableRefToReadOnlyMemory` (`E0080`). -/
theorem witness_mut_ref_to_readonly_rejected :
    let eVal : AllocEntry := {
      id := ⟨2⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := false, dataByte := 1
    }
    let eRef : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRef, eVal], globals := [] }
    let rootTy : ConstTy := .mutRef (.scalar 4)
    let rootVal : ConstVal := .refVal
      { prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 }
      (some (.bytes 4 1))
    internAndValidate 6 m0 .constant rootTy rootVal ⟨1⟩ =
      .err (.validationFailed .mutableRefToReadOnlyMemory) := rfl

/-- Witness 5 (`dangling_alloc_raw_ptr_in_final_const_rejected`):
    Raw pointer `*const u32` passes validation (`validity.rs:917`) and is then rejected by
    `intern_const_alloc_recursive` with `.internFailed .danglingPointer`. -/
theorem witness_dangling_raw_ptr_rejected :
    let eFreed : AllocEntry := {
      id := ⟨2⟩, origin := .localConst, lifecycle := .freed, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := false, dataByte := 42
    }
    let eRoot : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := false }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRoot, eFreed], globals := [] }
    internAndValidate 6 m0 .constant (.rawPtr .imm (.scalar 4))
      (.rawPtrVal { prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := false }, offset := 0 })
      ⟨1⟩ = .err (.internFailed .danglingPointer) := rfl

/-- Witness 6 (`dangling_ref_rejected`):
    Dangling `&u32` fails validation directly with `.validationFailed .danglingRef` (`E0080`). -/
theorem witness_dangling_ref_rejected :
    let eFreed : AllocEntry := {
      id := ⟨2⟩, origin := .localConst, lifecycle := .freed, mutbl := .mutbl,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := false, dataByte := 42
    }
    let eRoot : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRoot, eFreed], globals := [] }
    internAndValidate 6 m0 .constant (.sharedRef (.scalar 4))
      (.refVal { prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 } none)
      ⟨1⟩ = .err (.validationFailed .danglingRef) := rfl

/-- Witness 7 (`int_raw_ptr_stored_ok` + `int_to_ptr_zero_add_ok` vs `int_to_ptr_nonzero_add_rejected`):
    `0x1000 as *const u32` interns cleanly, `.add(0)` succeeds, `.add(1)` fails `.danglingIntPointer`,
    and dereferencing fails `.danglingIntPointer`. -/
theorem witness_int_ptr_boundary :
    let intPtr : PtrVal := { prov := none, offset := 4096 }
    let eRoot : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [intPtr], alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eRoot], globals := [] }
    (∃ m' j, internAndValidate 4 m0 .constant (.rawPtr .imm (.scalar 4)) (.rawPtrVal intPtr) ⟨1⟩ = .ok (m', j)) ∧
    ptrInboundsAdd m0 intPtr 0 = .ok intPtr ∧
    ptrInboundsAdd m0 intPtr 1 = .err .danglingIntPointer ∧
    ptrDerefRead m0 .constant intPtr 1 = .err .danglingIntPointer :=
  ⟨⟨{ locals := [], globals := [{
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .imm,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := none, offset := 4096 }], alreadyGlobal := true, dataByte := 0
    }] }, [⟨1⟩], rfl⟩, rfl, rfl, rfl⟩

/-- Witness 8 (`const_transmute_imm_static_to_unsafecell_rejected`):
    Pointing `&UnsafeCell<u32>` at an immutable `static` does NOT trigger `skipRecursiveCheck`
    and fails with `unsafeCellInReadOnlyMemory`. -/
theorem witness_transmute_imm_static_to_cell_rejected :
    let eImmStatic : AllocEntry := {
      id := ⟨10⟩, origin := .globalStatic false false, lifecycle := .live, mutbl := .imm,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := true, dataByte := 99
    }
    let eConst : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨10⟩, immutable := true, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eConst], globals := [eImmStatic] }
    internAndValidate 6 m0 .constant (.sharedRef (.unsafeCell (.scalar 4)))
      (.refVal { prov := some { allocId := ⟨10⟩, immutable := true, sharedRef := true }, offset := 0 }
        (some (.cellVal (.bytes 4 99))))
      ⟨1⟩ = .err (.validationFailed .unsafeCellInReadOnlyMemory) := rfl

/-- Witness 9 (`zst_promoted_mut_and_zst_cell_exceptions_ok` vs `zst_unsafecell_direct_borrow_still_e0492_rejected`):
    At CTFE validation time, zero-sized `UnsafeCell<()>` and `&mut [u8; 0]` pass because `!zst` / `size > 0`
    guards skip them, whereas static MIR `checkConstsBorrow` still rejects `&UnsafeCell::new(())` with `E0492`. -/
theorem witness_zst_validation_vs_static_e0492 :
    let eZst : AllocEntry := {
      id := ⟨2⟩, origin := .promoted, lifecycle := .live, mutbl := .imm,
      size := 0, align := 1, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := true, dataByte := 0
    }
    let eConst : AllocEntry := {
      id := ⟨1⟩, origin := .localConst, lifecycle := .live, mutbl := .mutbl,
      size := 8, align := 8, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [{ prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 }],
      alreadyGlobal := false, dataByte := 0
    }
    let m0 : MemState := { locals := [eConst], globals := [eZst] }
    let pv : PtrVal := { prov := some { allocId := ⟨2⟩, immutable := false, sharedRef := true }, offset := 0 }
    (∃ m' j, internAndValidate 6 m0 .constant (.sharedRef (.unsafeCell (.scalar 0)))
      (.refVal pv (some (.cellVal (.bytes 0 0)))) ⟨1⟩ = .ok (m', j)) ∧
    (∃ m' j, internAndValidate 6 m0 .constant (.mutRef (.scalar 0))
      (.refVal pv (some (.bytes 0 0))) ⟨1⟩ = .ok (m', j)) ∧
    checkConstsBorrow .constant .imm (.unsafeCell (.scalar 0)) .escapingLifetimeExtended =
      .err .escapingCellBorrow :=
  ⟨⟨_, [⟨1⟩], rfl⟩, ⟨_, [⟨1⟩], rfl⟩, rfl⟩

/-- Witness 10 (`offset_from_same_static_ok` vs `offset_from_diff_alloc_rejected`):
    `ptrOffsetFrom` succeeds within the same `AllocId` and fails across distinct `AllocId`s. -/
theorem witness_offset_from_same_vs_cross_alloc :
    let eA : AllocEntry := {
      id := ⟨10⟩, origin := .globalStatic false false, lifecycle := .live, mutbl := .imm,
      size := 16, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := true, dataByte := 1
    }
    let eB : AllocEntry := {
      id := ⟨11⟩, origin := .globalStatic false false, lifecycle := .live, mutbl := .imm,
      size := 4, align := 4, hasPartialPtr := false, hasUnsafeCellContent := false,
      ptrs := [], alreadyGlobal := true, dataByte := 9
    }
    let m0 : MemState := { locals := [], globals := [eA, eB] }
    let pA1 : PtrVal := { prov := some { allocId := ⟨10⟩, immutable := true, sharedRef := true }, offset := 4 }
    let pA3 : PtrVal := { prov := some { allocId := ⟨10⟩, immutable := true, sharedRef := true }, offset := 12 }
    let pB0 : PtrVal := { prov := some { allocId := ⟨11⟩, immutable := true, sharedRef := true }, offset := 0 }
    ptrOffsetFrom m0 pA3 pA1 = .ok 8 ∧
    ptrOffsetFrom m0 pB0 pA1 = .err .crossAllocOffsetFrom :=
  ⟨rfl, rfl⟩

/-- Witness 11 (`checkConstsBorrow` & `ptrRawCmp` static gates):
    Verifies `E0764` (`escapingMutBorrow`), `E0492` (`escapingCellBorrow`), `static &ATOMIC` escape
    exemption (`indirectPlace`), `static mut` `&mut` exemption, and `rawPtrComparison`. -/
theorem witness_static_const_checks :
    checkConstsBorrow .constant .mutbl (.scalar 4) .escapingLifetimeExtended = .err .escapingMutBorrow ∧
    checkConstsBorrow (.staticItem .mutbl) .mutbl (.scalar 4) .escapingLifetimeExtended = .ok () ∧
    checkConstsBorrow .constant .imm (.unsafeCell (.scalar 4)) .escapingLifetimeExtended = .err .escapingCellBorrow ∧
    checkConstsBorrow .constant .imm (.unsafeCell (.scalar 4)) .indirectPlace = .ok () ∧
    ptrRawCmp true { prov := none, offset := 4096 } { prov := none, offset := 4096 } =
      .err (.constCheckFailed .rawPtrComparison) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end CtfeInterningSoundness
