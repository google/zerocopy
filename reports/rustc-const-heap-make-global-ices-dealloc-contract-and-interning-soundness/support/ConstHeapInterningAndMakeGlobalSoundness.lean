/-!
# Formal Semantics of `rustc` CTFE `const_heap`, `const_make_global`,
# `const_deallocate`, and `intern_const_alloc_recursive`

Kernel-checked Lean 4 formalization modeling:
1. `CtfeProvenance` (`compiler/rustc_middle/src/mir/interpret/pointer.rs`),
   `CompileTimeMachine` CTFE heap intrinsics (`const_allocate`,
   `const_deallocate`, `const_make_global` in
   `compiler/rustc_const_eval/src/const_eval/{machine,intrinsics}.rs`),
   `make_const_heap_ptr_global` and `deallocate_ptr`
   (`compiler/rustc_const_eval/src/interpret/memory.rs`), and
   `prepare_alloc` / `intern_shallow` / `intern_const_alloc_recursive`
   (`compiler/rustc_const_eval/src/interpret/intern.rs`).
2. Mechanized reproductions of:
   - ICE #1 (`intern.rs:350:13`): `const_make_global` preserves `shared_ref = false`
     on the returned `*const u8`, causing `intern_const_alloc_recursive` to trigger
     `span_bug!` for raw pointers returned from `const` and immutable `static`.
   - ICE #2 (`intern.rs:91:13`): `prepare_alloc` asserts `alloc.mutability == Mut`
     for every inner allocation of `static mut`, unconditionally panicking on any
     same-evaluation `const_make_global` allocation (already frozen to `Not`),
     yielding a complete catch-22 deadlock for `const_heap` inside `static mut`.
   - The `core::intrinsics::const_deallocate` `# Safety` docstring contradiction
     (`library/core/src/intrinsics/mod.rs`) and CTFE-vs-runtime/Miri fallback
     divergence under `#[miri::intrinsic_fallback_is_spec]`.
3. Repaired semantics (`constMakeGlobalFixed` + `prepareAllocFixed`) with
   universal soundness and completeness proofs establishing:
   - Elimination of ICE #1 and ICE #2 across `const`, `promoted`, `static`, and
     `static mut`;
   - Immutability soundness: every interned `const_make_global` heap allocation
     remains strictly immutable (`Mutability.not`) in global memory (even when
     referenced from `static mut`), and no transient `wasMadeGlobal = false`
     allocation can ever escape into global memory;
   - Exact characterization of the pre-call alias provenance boundary.

TCB hygiene: zero `sorry`, zero `Classical.choice`, zero `omega`, zero
`bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
-/

namespace ConstHeapInterning

abbrev AllocId := Nat

inductive Mutability where
  | not
  | mut_

noncomputable def Mutability.beq : Mutability → Mutability → Bool
  | .not, .not => true
  | .mut_, .mut_ => true
  | _, _ => false

theorem Mutability.beq_eq_true (a b : Mutability) : a.beq b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

inductive LocalAllocKind where
  | stack
  | callerLocation
  | heap (wasMadeGlobal : Bool)

noncomputable def LocalAllocKind.beq : LocalAllocKind → LocalAllocKind → Bool
  | .stack, .stack => true
  | .callerLocation, .callerLocation => true
  | .heap a, .heap b => Bool.and (Bool.or (Bool.not a) b) (Bool.or (Bool.not b) a)
  | _, _ => false

/-- Packed CTFE provenance (`compiler/rustc_middle/src/mir/interpret/pointer.rs`).
Invariant: `immutable = true → sharedRef = true`. -/
structure CtfeProvenance where
  allocId : AllocId
  immutable : Bool
  sharedRef : Bool

noncomputable def CtfeProvenance.wf (p : CtfeProvenance) : Prop :=
  p.immutable = true → p.sharedRef = true

noncomputable def CtfeProvenance.fromAllocId (id : AllocId) : CtfeProvenance :=
  { allocId := id, immutable := false, sharedRef := false }

noncomputable def CtfeProvenance.asSharedRef (p : CtfeProvenance) : CtfeProvenance :=
  { p with sharedRef := true }

noncomputable def CtfeProvenance.asImmutable (p : CtfeProvenance) : CtfeProvenance :=
  { p with immutable := true, sharedRef := true }

theorem CtfeProvenance.fromAllocId_wf (id : AllocId) :
    (CtfeProvenance.fromAllocId id).wf := by
  intro h; cases h

theorem CtfeProvenance.asSharedRef_wf (p : CtfeProvenance) :
    p.asSharedRef.wf := by
  intro _; rfl

theorem CtfeProvenance.asImmutable_wf (p : CtfeProvenance) :
    p.asImmutable.wf := by
  intro _; rfl

structure Pointer where
  prov : Option CtfeProvenance
  offset : Nat

noncomputable def nullPtr : Pointer :=
  { prov := none, offset := 0 }

noncomputable def Pointer.isNull (p : Pointer) : Bool :=
  match p.prov with
  | none => Nat.beq p.offset 0
  | some _ => false

/-- Models `CompileTimeMachine::retag_ptr_value` (`const_eval/machine.rs:1125-1158`)
for shared references `&T` (`Mutability::Not`): sets `asImmutable` if `T : Freeze`
and `asSharedRef` if `T : !Freeze`. -/
noncomputable def retagSharedRef (ptr : Pointer) (isFreeze : Bool) : Pointer :=
  match ptr.prov with
  | none => ptr
  | some p =>
    if p.immutable then
      ptr
    else if isFreeze then
      { ptr with prov := some p.asImmutable }
    else
      { ptr with prov := some p.asSharedRef }

theorem retagSharedRef_sets_sharedRef (p : CtfeProvenance) (off : Nat) (isFreeze : Bool)
    (hwf : p.wf) :
    ∃ p', (retagSharedRef { prov := some p, offset := off } isFreeze).prov = some p' ∧
          p'.allocId = p.allocId ∧ p'.sharedRef = true ∧ p'.wf := by
  unfold retagSharedRef
  dsimp only
  cases hImm : p.immutable with
  | true =>
    simp only [↓reduceIte]
    exact ⟨p, rfl, rfl, hwf hImm, hwf⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases isFreeze with
    | true =>
      simp only [↓reduceIte]
      exact ⟨p.asImmutable, rfl, rfl, rfl, CtfeProvenance.asImmutable_wf p⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨p.asSharedRef, rfl, rfl, rfl, CtfeProvenance.asSharedRef_wf p⟩

/-- Local CTFE session allocation stored in `ecx.memory.alloc_map`. -/
structure LocalAlloc where
  kind : LocalAllocKind
  mutbl : Mutability
  size : Nat
  align : Nat
  ptrs : List CtfeProvenance
  hasPartialPtr : Bool

/-- Global allocation stored in `tcx` (`GlobalAlloc::Memory` when `isStatic = false`,
`GlobalAlloc::Static` when `isStatic = true`). -/
structure GlobalEntry where
  isStatic : Bool
  mutbl : Mutability
  size : Nat
  align : Nat
  ptrs : List CtfeProvenance
  originWasHeap : Bool

structure CtfeState where
  nextId : AllocId
  localMap : List (AllocId × LocalAlloc)
  deadMap : List (AllocId × Nat × Nat)
  globalMap : List (AllocId × GlobalEntry)
  unleashMiri : Bool

noncomputable def lookupLocal : List (AllocId × LocalAlloc) → AllocId → Option LocalAlloc
  | [], _ => none
  | (k, v) :: rest, id => if Nat.beq k id then some v else lookupLocal rest id

noncomputable def removeLocal : List (AllocId × LocalAlloc) → AllocId → List (AllocId × LocalAlloc)
  | [], _ => []
  | (k, v) :: rest, id => if Nat.beq k id then removeLocal rest id else (k, v) :: removeLocal rest id

noncomputable def updateLocal : List (AllocId × LocalAlloc) → AllocId → LocalAlloc → List (AllocId × LocalAlloc)
  | [], id, v => [(id, v)]
  | (k, old) :: rest, id, v =>
    if Nat.beq k id then (k, v) :: rest else (k, old) :: updateLocal rest id v

noncomputable def lookupGlobal : List (AllocId × GlobalEntry) → AllocId → Option GlobalEntry
  | [], _ => none
  | (k, v) :: rest, id => if Nat.beq k id then some v else lookupGlobal rest id

noncomputable def insertGlobal (gmap : List (AllocId × GlobalEntry)) (id : AllocId) (entry : GlobalEntry) :
    List (AllocId × GlobalEntry) :=
  (id, entry) :: gmap

noncomputable def memId : List AllocId → AllocId → Bool
  | [], _ => false
  | x :: xs, id => if Nat.beq x id then true else memId xs id

theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem nat_beq_eq (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    | succ b =>
      constructor
      · intro h
        exact congrArg Nat.succ ((ih b).mp h)
      · intro h
        injection h with h'
        exact (ih b).mpr h'

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_eq a b).mp hb))

theorem lookupLocal_remove_same (m : List (AllocId × LocalAlloc)) (id : AllocId) :
    lookupLocal (removeLocal m id) id = none := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold removeLocal
    cases h : Nat.beq k id with
    | true =>
      simp only [↓reduceIte]
      exact ih
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold lookupLocal
      rw [h]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih

theorem lookupLocal_remove_ne (m : List (AllocId × LocalAlloc)) {id target : AllocId}
    (hne : id ≠ target) :
    lookupLocal (removeLocal m id) target = lookupLocal m target := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold removeLocal
    cases hk1 : Nat.beq k id with
    | true =>
      have hkEq : k = id := (nat_beq_eq k id).mp hk1
      have hkNe : k ≠ target := by rw [hkEq]; exact hne
      simp only [↓reduceIte]
      change lookupLocal (removeLocal tl id) target =
        if Nat.beq k target = true then some v else lookupLocal tl target
      rw [nat_beq_false_of_ne hkNe]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      change (if Nat.beq k target = true then some v else lookupLocal (removeLocal tl id) target) =
        (if Nat.beq k target = true then some v else lookupLocal tl target)
      cases hk2 : Nat.beq k target with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih

theorem lookupGlobal_insert_same (gmap : List (AllocId × GlobalEntry)) (id : AllocId) (e : GlobalEntry) :
    lookupGlobal (insertGlobal gmap id e) id = some e := by
  unfold insertGlobal lookupGlobal
  rw [nat_beq_refl]
  simp only [↓reduceIte]

theorem lookupGlobal_insert_ne (gmap : List (AllocId × GlobalEntry)) {id target : AllocId}
    (e : GlobalEntry) (hne : id ≠ target) :
    lookupGlobal (insertGlobal gmap id e) target = lookupGlobal gmap target := by
  unfold insertGlobal
  change (if Nat.beq id target = true then some e else lookupGlobal gmap target) = lookupGlobal gmap target
  rw [nat_beq_false_of_ne hne]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Fuel-bounded power-of-two test (computable without `omega` or `partial`). -/
noncomputable def isPow2Aux : Nat → Nat → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | _ + 1, 1 => true
  | fuel + 1, n =>
    if Nat.beq (n % 2) 0 then isPow2Aux fuel (n / 2) else false

noncomputable def isPowerOfTwo (n : Nat) : Bool :=
  isPow2Aux n n

theorem isPowerOfTwo_one : isPowerOfTwo 1 = true := rfl
theorem isPowerOfTwo_three : isPowerOfTwo 3 = false := rfl

inductive EvalError where
  | invalidAlign
  | missingProvenance
  | nonZeroOffset
  | nonHeapMakeGlobal
  | danglingMakeGlobal
  | alreadyMadeGlobal
  | deallocStaticMemory
  | deallocDangling
  | deallocImmutable
  | deallocWrongKind
  | deallocLayoutMismatch
  | writeToReadOnly
  | writeThroughImmutablePtr

/-- `sym::const_allocate` (`machine.rs:503-521` / `intrinsics.rs:34-52`). -/
noncomputable def constAllocate (st : CtfeState) (size align : Nat) :
    Except EvalError (Pointer × CtfeState) :=
  if isPowerOfTwo align then
    let id := st.nextId
    let alloc : LocalAlloc :=
      { kind := .heap false
      , mutbl := .mut_
      , size := size
      , align := align
      , ptrs := []
      , hasPartialPtr := false
      }
    let st' : CtfeState :=
      { st with
        nextId := id + 1
      , localMap := (id, alloc) :: st.localMap
      }
    .ok ({ prov := some (CtfeProvenance.fromAllocId id), offset := 0 }, st')
  else
    .error .invalidAlign

/-- `InterpCx::deallocate_ptr` (`interpret/memory.rs:380-450`). -/
noncomputable def deallocatePtr (st : CtfeState) (ptr : Pointer) (size align : Nat)
    (expectedKind : LocalAllocKind) : Except EvalError CtfeState :=
  match ptr.prov with
  | none => .error .missingProvenance
  | some prov =>
    if !Nat.beq ptr.offset 0 then
      .error .nonZeroOffset
    else
      match lookupLocal st.localMap prov.allocId with
      | none =>
        match lookupGlobal st.globalMap prov.allocId with
        | some _ => .error .deallocStaticMemory
        | none => .error .deallocDangling
      | some alloc =>
        match alloc.mutbl with
        | .not => .error .deallocImmutable
        | .mut_ =>
          if !LocalAllocKind.beq alloc.kind expectedKind then
            .error .deallocWrongKind
          else if !(Nat.beq alloc.size size && Nat.beq alloc.align align) then
            .error .deallocLayoutMismatch
          else
            .ok { st with
                  localMap := removeLocal st.localMap prov.allocId
                , deadMap := (prov.allocId, alloc.size, alloc.align) :: st.deadMap
                }

/-- `sym::const_deallocate` (`machine.rs:522-550` / `intrinsics.rs:53-81`).
`Align::from_bytes` runs BEFORE checking `GlobalAlloc::Memory(_)`, and
`is_allocated_in_another_const` skips ONLY `GlobalAlloc::Memory(_)` (NOT
`LocalAllocKind.stack`, NOT `GlobalAlloc::Static(_)`, NOT same-const made-global
heap allocations). -/
noncomputable def constDeallocate (st : CtfeState) (ptr : Pointer) (size align : Nat) :
    Except EvalError CtfeState :=
  if !isPowerOfTwo align then
    .error .invalidAlign
  else
    match ptr.prov with
    | none => .error .missingProvenance
    | some prov =>
      let isAllocatedInAnotherConst : Bool :=
        match lookupGlobal st.globalMap prov.allocId with
        | some g => !g.isStatic
        | none => false
      if isAllocatedInAnotherConst then
        .ok st
      else
        deallocatePtr st ptr size align (.heap false)

/-- `InterpCx::make_const_heap_ptr_global` (`interpret/memory.rs:335-377`). -/
noncomputable def makeConstHeapPtrGlobal (st : CtfeState) (ptr : Pointer) :
    Except EvalError CtfeState :=
  match ptr.prov with
  | none => .error .missingProvenance
  | some prov =>
    if !Nat.beq ptr.offset 0 then
      .error .nonZeroOffset
    else
      match lookupGlobal st.globalMap prov.allocId with
      | some _ => .error .nonHeapMakeGlobal
      | none =>
        match lookupLocal st.localMap prov.allocId with
        | none => .error .danglingMakeGlobal
        | some alloc =>
          match alloc.kind with
          | .stack | .callerLocation => .error .nonHeapMakeGlobal
          | .heap true => .error .alreadyMadeGlobal
          | .heap false =>
            let frozen : LocalAlloc := { alloc with kind := .heap true, mutbl := .not }
            .ok { st with localMap := updateLocal st.localMap prov.allocId frozen }

/-- Buggy upstream `sym::const_make_global` (`machine.rs:552-556` / `intrinsics.rs:83-87`):
calls `make_const_heap_ptr_global(ptr)` and writes `ptr` BACK UNCHANGED
(`shared_ref = false`, `immutable = false`). -/
noncomputable def constMakeGlobalBuggy (st : CtfeState) (ptr : Pointer) :
    Except EvalError (Pointer × CtfeState) :=
  match makeConstHeapPtrGlobal st ptr with
  | .error e => .error e
  | .ok st' => .ok (ptr, st')

/-- Repaired `sym::const_make_global`: freezes the allocation AND updates the
returned pointer's provenance with `CtfeProvenance::as_immutable` (`immutable = true`,
`sharedRef = true`). -/
noncomputable def constMakeGlobalFixed (st : CtfeState) (ptr : Pointer) :
    Except EvalError (Pointer × CtfeState) :=
  match makeConstHeapPtrGlobal st ptr with
  | .error e => .error e
  | .ok st' =>
    let ptr' : Pointer :=
      match ptr.prov with
      | none => ptr
      | some p => { ptr with prov := some p.asImmutable }
    .ok (ptr', st')

/-- Models CTFE write check (`before_memory_write` at `machine.rs:1171-1189` plus
allocation `mutability` check in `get_bytes_mut`). -/
noncomputable def ctfeWriteCheck (st : CtfeState) (ptr : Pointer) : Except EvalError Unit :=
  match ptr.prov with
  | none => .error .missingProvenance
  | some prov =>
    if prov.immutable then
      .error .writeThroughImmutablePtr
    else
      match lookupLocal st.localMap prov.allocId with
      | some alloc =>
        match alloc.mutbl with
        | .not => .error .writeToReadOnly
        | .mut_ => .ok ()
      | none =>
        match lookupGlobal st.globalMap prov.allocId with
        | some _ => .error .writeToReadOnly
        | none => .error .deallocDangling

/-! ## Interning State Machine (`compiler/rustc_const_eval/src/interpret/intern.rs`) -/

inductive InternKind where
  | constant
  | promoted
  | staticNot (rootIsFreeze : Bool)
  | staticMut
  | threadLocalStatic (mutbl : Mutability) (rootIsFreeze : Bool)

inductive InternFail where
  | errConstAllocNotGlobal
  | errPartialPointer
  | errDanglingPointer
  | errBadMutablePointer
  | errNestedStaticInThreadLocal
  | ice1BadMutablePtrSpanBug
  | ice2PrepareAllocMutAssertFailed
  | fuelExhausted

inductive InternOutcome where
  | ok (st : CtfeState)
  | fail (f : InternFail)

inductive InternPolicy where
  | buggy
  | fixed

/-- Buggy upstream `prepare_alloc` (`intern.rs:58-95`):
when `reqMutbl = Mutability.mut_` (inner allocations of `static mut`),
unconditionally asserts `alloc.mutability == Mutability.mut_` (line 91),
panicking on any `Heap { wasMadeGlobal := true }` allocation. -/
noncomputable def prepareAllocBuggy (alloc : LocalAlloc) (reqMutbl : Mutability) :
    Except InternFail LocalAlloc :=
  match alloc.kind with
  | .heap false => .error .errConstAllocNotGlobal
  | .heap true | .stack | .callerLocation =>
    if alloc.hasPartialPtr then
      .error .errPartialPointer
    else
      match reqMutbl with
      | .not => .ok { alloc with mutbl := .not }
      | .mut_ =>
        match alloc.mutbl with
        | .mut_ => .ok alloc
        | .not => .error .ice2PrepareAllocMutAssertFailed

/-- Repaired `prepare_alloc`:
1. Rejects transient `Heap { wasMadeGlobal := false }` (`ConstAllocNotGlobal`)
   and partial pointers (`PartialPointer`).
2. Preserves `Mutability.not` on `Heap { wasMadeGlobal := true }` even when
   `reqMutbl = Mutability.mut_` (never un-freezes a made-global heap allocation,
   and never panics on `static mut`).
3. Preserves the existing immutability/mutability rules on `Stack` and
   `CallerLocation` allocations. -/
noncomputable def prepareAllocFixed (alloc : LocalAlloc) (reqMutbl : Mutability) :
    Except InternFail LocalAlloc :=
  match alloc.kind with
  | .heap false => .error .errConstAllocNotGlobal
  | .heap true =>
    if alloc.hasPartialPtr then
      .error .errPartialPointer
    else
      .ok { alloc with mutbl := .not }
  | .stack | .callerLocation =>
    if alloc.hasPartialPtr then
      .error .errPartialPointer
    else
      match reqMutbl with
      | .not => .ok { alloc with mutbl := .not }
      | .mut_ =>
        match alloc.mutbl with
        | .mut_ => .ok alloc
        | .not => .error .ice2PrepareAllocMutAssertFailed

noncomputable def prepareAlloc (pol : InternPolicy) (alloc : LocalAlloc) (reqMutbl : Mutability) :
    Except InternFail LocalAlloc :=
  match pol with
  | .buggy => prepareAllocBuggy alloc reqMutbl
  | .fixed => prepareAllocFixed alloc reqMutbl

noncomputable def internKindParams : InternKind → (Mutability × Mutability × Bool × Bool × Bool)
  -- (baseMutbl, innerMutbl, isStatic, isPromoted, isThreadLocal)
  | .constant => (.not, .not, false, false, false)
  | .promoted => (.not, .not, false, true, false)
  | .staticNot rootIsFreeze =>
    ((if rootIsFreeze then .not else .mut_), .not, true, false, false)
  | .staticMut => (.mut_, .mut_, true, false, false)
  | .threadLocalStatic .not rootIsFreeze =>
    ((if rootIsFreeze then .not else .mut_), .not, true, false, true)
  | .threadLocalStatic .mut_ _ => (.mut_, .mut_, true, false, true)

noncomputable def localKindIsHeap : LocalAllocKind → Bool
  | .heap _ => true
  | .stack | .callerLocation => false

/-- `intern_shallow` (`intern.rs:104-138`) + `intern_as_new_static` (`intern.rs:142-177`). -/
noncomputable def internShallow (pol : InternPolicy) (st : CtfeState) (allocId : AllocId)
    (reqMutbl : Mutability) (isStatic isThreadLocal : Bool) :
    Except InternFail (List CtfeProvenance × CtfeState) :=
  match lookupLocal st.localMap allocId with
  | none => .error .errDanglingPointer
  | some alloc =>
    match prepareAlloc pol alloc reqMutbl with
    | .error err => .error err
    | .ok prepared =>
      if isStatic && isThreadLocal then
        .error .errNestedStaticInThreadLocal
      else
        let entry : GlobalEntry :=
          { isStatic := isStatic
          , mutbl := prepared.mutbl
          , size := prepared.size
          , align := prepared.align
          , ptrs := prepared.ptrs
          , originWasHeap := localKindIsHeap prepared.kind
          }
        let st' : CtfeState :=
          { st with
            localMap := removeLocal st.localMap allocId
          , globalMap := insertGlobal st.globalMap allocId entry
          }
        .ok (prepared.ptrs, st')

/-- Recursive worklist loop of `intern_const_alloc_recursive` (`intern.rs:275-356`). -/
noncomputable def internLoop (pol : InternPolicy) (baseId : AllocId)
    (innerMutbl : Mutability) (isStatic isPromoted isThreadLocal : Bool) :
    Nat → CtfeState → List AllocId → Bool → List CtfeProvenance → InternOutcome
  | _, st, _, foundBadMut, [] =>
    if foundBadMut then
      if st.unleashMiri then .fail .errBadMutablePointer else .fail .ice1BadMutablePtrSpanBug
    else
      .ok st
  | 0, _, _, _, _ :: _ => .fail .fuelExhausted
  | fuel + 1, st, justInterned, foundBadMut, prov :: rest =>
    let allocId := prov.allocId
    if Nat.beq baseId allocId && isStatic then
      internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
        fuel st justInterned foundBadMut rest
    else
      let checkSharedRef : Bool :=
        !isPromoted && Mutability.beq innerMutbl .not && !prov.sharedRef
      let isAlreadyGlobal : Bool :=
        match lookupGlobal st.globalMap allocId with
        | some _ => true
        | none => false
      if checkSharedRef && isAlreadyGlobal && !memId justInterned allocId then
        internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
          fuel st justInterned foundBadMut rest
      else
        let isLocalPresent : Bool :=
          match lookupLocal st.localMap allocId with
          | some _ => true
          | none => false
        let dangling : Bool := !isAlreadyGlobal && !isLocalPresent
        let foundBadMut' : Bool :=
          if checkSharedRef && !dangling then true else foundBadMut
        if isAlreadyGlobal then
          internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
            fuel st justInterned foundBadMut' rest
        else
          match internShallow pol st allocId innerMutbl isStatic isThreadLocal with
          | .error err => .fail err
          | .ok (nextPtrs, st') =>
            internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
              fuel st' (allocId :: justInterned) foundBadMut' (nextPtrs ++ rest)

/-- Entry point mirroring `intern_const_alloc_recursive` (`intern.rs:204-357`). -/
noncomputable def internConstAllocRecursive (pol : InternPolicy) (st : CtfeState)
    (kind : InternKind) (baseId : AllocId) (fuel : Nat) : InternOutcome :=
  let (baseMutbl, innerMutbl, isStatic, isPromoted, isThreadLocal) := internKindParams kind
  if isStatic then
    match lookupLocal st.localMap baseId with
    | none => .fail .errDanglingPointer
    | some baseAlloc =>
      match prepareAlloc pol baseAlloc baseMutbl with
      | .error err => .fail err
      | .ok prepared =>
        let st1 : CtfeState :=
          { st with localMap := updateLocal st.localMap baseId prepared }
        internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
          fuel st1 [baseId] false prepared.ptrs
  else
    match internShallow pol st baseId baseMutbl false false with
    | .error err => .fail err
    | .ok (todo0, st1) =>
      internLoop pol baseId innerMutbl isStatic isPromoted isThreadLocal
        fuel st1 [baseId] false todo0

/-! ## Part I: Mechanized Reproduction of ICE #1 (`intern.rs:350`) and ICE #2 (`intern.rs:91`) -/

noncomputable def mkSingleHeapRootState (rootMutbl : Mutability) (storedProv : CtfeProvenance)
    (wasMadeGlobal : Bool) (heapMutbl : Mutability) (unleashMiri : Bool) : CtfeState :=
  { nextId := 2
  , localMap :=
      [ (0, { kind := .stack
            , mutbl := rootMutbl
            , size := 8
            , align := 8
            , ptrs := [storedProv]
            , hasPartialPtr := false })
      , (1, { kind := .heap wasMadeGlobal
            , mutbl := heapMutbl
            , size := 1
            , align := 1
            , ptrs := []
            , hasPartialPtr := false })
      ]
  , deadMap := []
  , globalMap := []
  , unleashMiri := unleashMiri
  }

noncomputable def stateAfterBuggyMakeGlobalRaw (unleashMiri : Bool) : CtfeState :=
  let st0 : CtfeState :=
    { nextId := 1
    , localMap := [(0, { kind := .stack, mutbl := .mut_, size := 8, align := 8
                       , ptrs := [], hasPartialPtr := false })]
    , deadMap := []
    , globalMap := []
    , unleashMiri := unleashMiri
    }
  match constAllocate st0 1 1 with
  | .error _ => st0
  | .ok (p, st1) =>
    match constMakeGlobalBuggy st1 p with
    | .error _ => st1
    | .ok (g, st2) =>
      match g.prov with
      | none => st2
      | some prov =>
        { st2 with
          localMap := updateLocal st2.localMap 0
            { kind := .stack, mutbl := .mut_, size := 8, align := 8
            , ptrs := [prov], hasPartialPtr := false } }

/-- **Theorem 1a (ICE #1 on `const` raw pointer):** Returning `*const u8` directly
from `const_make_global` in a `const` item triggers `intern.rs:350` `span_bug!`
when `-Z unleash-the-miri-inside-of-you` is off. -/
theorem buggy_constMakeGlobal_raw_ptr_triggers_intern_ice1_const :
    internConstAllocRecursive .buggy (stateAfterBuggyMakeGlobalRaw false) .constant 0 10 =
      .fail .ice1BadMutablePtrSpanBug := by
  rfl

/-- **Theorem 1b (ICE #1 on immutable `static` raw pointer):** Same crash for
immutable `static` (`InternKind::Static(Mutability::Not)`), regardless of
whether the root `static` is `Freeze` or `!Freeze`. -/
theorem buggy_constMakeGlobal_raw_ptr_triggers_intern_ice1_static (rootIsFreeze : Bool) :
    internConstAllocRecursive .buggy (stateAfterBuggyMakeGlobalRaw false)
      (.staticNot rootIsFreeze) 0 10 =
      .fail .ice1BadMutablePtrSpanBug := by
  cases rootIsFreeze <;> rfl

/-- **Theorem 2 (`-Z unleash-the-miri-inside-of-you` downgrades ICE #1):** With
`unleashMiri = true`, `intern.rs:347-349` returns `InternError::BadMutablePointer`
instead of panicking. -/
theorem buggy_constMakeGlobal_raw_ptr_unleash_miri_not_ice1 :
    internConstAllocRecursive .buggy (stateAfterBuggyMakeGlobalRaw true) .constant 0 10 =
      .fail .errBadMutablePointer := by
  rfl

/-- **Theorem 3 (Reborrow workaround avoids ICE #1 for both `Freeze` and `!Freeze`):**
Applying `retagSharedRef` (`(&*const_make_global(p)) as *const T`) sets
`sharedRef = true`, so buggy `intern_const_alloc_recursive` succeeds (`ok`) for
both `const` and immutable `static`. -/
theorem reborrow_shared_ref_avoids_ice1_const (isFreeze : Bool) :
    ∃ st',
      internConstAllocRecursive .buggy
        (mkSingleHeapRootState .mut_
          (match (retagSharedRef { prov := some (CtfeProvenance.fromAllocId 1), offset := 0 } isFreeze).prov with
           | some p => p
           | none => CtfeProvenance.fromAllocId 1)
          true .not false)
        .constant 0 10 = .ok st' := by
  cases isFreeze <;> exact ⟨_, rfl⟩

/-- **Theorem 4 (ICE #2 on `static mut` — unconditional for ALL provenance flags
and BOTH `unleashMiri` settings):** In `static mut`, `inner_mutability = Mut`, so
`prepare_alloc` hits `assert_eq!(alloc.mutability, Mutability::Mut)` (`intern.rs:91`)
against the already-frozen `const_make_global` allocation (`mutbl = Not`), crashing
regardless of whether the pointer was reborrowed (`sharedRef = true`) or raw
(`sharedRef = false`), and even with `-Z unleash-the-miri-inside-of-you` enabled. -/
theorem buggy_prepareAlloc_static_mut_triggers_ice2
    (immutable sharedRef unleashMiri : Bool) :
    internConstAllocRecursive .buggy
      (mkSingleHeapRootState .mut_
        { allocId := 1, immutable := immutable, sharedRef := sharedRef }
        true .not unleashMiri)
      .staticMut 0 10 = .fail .ice2PrepareAllocMutAssertFailed := by
  cases immutable <;> cases sharedRef <;> cases unleashMiri <;> rfl

/-- **Theorem 5 (`static mut` Catch-22 Deadlock in Buggy `rustc`):**
For ANY same-evaluation `const_allocate` heap allocation reachable from a
`static mut` root:
- if `const_make_global` was NOT called (`wasMadeGlobal = false`), interning fails
  with `errConstAllocNotGlobal` (`ConstHeapPtrInFinal`);
- if `const_make_global` WAS called (`wasMadeGlobal = true`, `mutbl = .not`),
  interning crashes with ICE #2 (`ice2PrepareAllocMutAssertFailed`). -/
theorem static_mut_catch22_deadlock_in_buggy_rustc
    (immutable sharedRef unleashMiri : Bool) :
    (internConstAllocRecursive .buggy
      (mkSingleHeapRootState .mut_
        { allocId := 1, immutable := immutable, sharedRef := sharedRef }
        false .mut_ unleashMiri)
      .staticMut 0 10 = .fail .errConstAllocNotGlobal) ∧
    (internConstAllocRecursive .buggy
      (mkSingleHeapRootState .mut_
        { allocId := 1, immutable := immutable, sharedRef := sharedRef }
        true .not unleashMiri)
      .staticMut 0 10 = .fail .ice2PrepareAllocMutAssertFailed) := by
  constructor
  · cases immutable <;> cases sharedRef <;> cases unleashMiri <;> rfl
  · exact buggy_prepareAlloc_static_mut_triggers_ice2 immutable sharedRef unleashMiri

/-- **Theorem 5b (`#[thread_local]` nested static rejection, `intern.rs:162-165`):** -/
theorem thread_local_static_nested_const_heap_rejected (rootIsFreeze : Bool) :
    internConstAllocRecursive .buggy
      (mkSingleHeapRootState .mut_ (CtfeProvenance.fromAllocId 1).asImmutable true .not false)
      (.threadLocalStatic .not rootIsFreeze) 0 10 = .fail .errNestedStaticInThreadLocal := by
  cases rootIsFreeze <;> rfl

/-! ## Part II: `const_deallocate` `# Safety` Contract Contradictions & CTFE-vs-Runtime Divergence -/

/-- **Theorem 6 (`const_deallocate` Stack-Local Docstring Contradiction):**
Contrary to `library/core/src/intrinsics/mod.rs` (`"If the ptr is pointing to a
local variable, this intrinsic doesn't deallocate it"`), for ANY CTFE state `st`,
ANY stack local `allocId` in `st.localMap` (not shadowed in `st.globalMap`), ANY
`size`, and ANY power-of-two `align`, `constDeallocate` throws UB
(`EvalError.deallocWrongKind`) rather than acting as a no-op. -/
theorem constDeallocate_stack_local_contradicts_core_docstring
    (st : CtfeState) (allocId size align : Nat) (alloc : LocalAlloc)
    (hPow2 : isPowerOfTwo align = true)
    (hNotGlobal : lookupGlobal st.globalMap allocId = none)
    (hLocal : lookupLocal st.localMap allocId = some alloc)
    (hStack : alloc.kind = .stack)
    (hMut : alloc.mutbl = .mut_) :
    constDeallocate st { prov := some (CtfeProvenance.fromAllocId allocId), offset := 0 } size align =
      .error .deallocWrongKind := by
  unfold constDeallocate
  rw [hPow2]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold CtfeProvenance.fromAllocId
  dsimp only
  rw [hNotGlobal]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold deallocatePtr
  dsimp only
  rw [nat_beq_refl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hLocal]
  dsimp only
  rw [hMut, hStack]
  rfl

/-- **Theorem 7a (`const_deallocate` cross-const `GlobalAlloc::Memory` bypasses
size/layout validation when `align` is a power of two, but STILL rejects invalid
alignment first):** -/
theorem constDeallocate_cross_const_memory_noop_and_align_order
    (st : CtfeState) (allocId offset wrongSize goodAlign badAlign : Nat) (g : GlobalEntry)
    (hGood : isPowerOfTwo goodAlign = true)
    (hBad : isPowerOfTwo badAlign = false)
    (hMem : lookupGlobal st.globalMap allocId = some g)
    (hNotStatic : g.isStatic = false) :
    constDeallocate st { prov := some (CtfeProvenance.fromAllocId allocId), offset := offset } wrongSize goodAlign =
      .ok st ∧
    constDeallocate st { prov := some (CtfeProvenance.fromAllocId allocId), offset := offset } wrongSize badAlign =
      .error .invalidAlign := by
  constructor
  · unfold constDeallocate
    rw [hGood]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold CtfeProvenance.fromAllocId
    dsimp only
    simp only [hMem, hNotStatic, Bool.not_false, ↓reduceIte]
  · unfold constDeallocate
    rw [hBad]
    rfl

/-- **Theorem 7b (`const_deallocate` on `GlobalAlloc::Static` throws `deallocStaticMemory`):** -/
theorem constDeallocate_static_item_throws_ub
    (st : CtfeState) (allocId size align : Nat) (g : GlobalEntry)
    (hPow2 : isPowerOfTwo align = true)
    (hNotLocal : lookupLocal st.localMap allocId = none)
    (hStatic : lookupGlobal st.globalMap allocId = some g)
    (hIsStatic : g.isStatic = true) :
    constDeallocate st { prov := some (CtfeProvenance.fromAllocId allocId), offset := 0 } size align =
      .error .deallocStaticMemory := by
  unfold constDeallocate
  rw [hPow2]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold CtfeProvenance.fromAllocId
  dsimp only
  simp only [hStatic, hIsStatic, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold deallocatePtr
  dsimp only
  rw [nat_beq_refl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hNotLocal, hStatic]

/-- **Theorem 7c (`const_deallocate` on same-const `const_make_global` throws `deallocImmutable`):** -/
theorem constDeallocate_same_const_after_make_global_throws_ub
    (st : CtfeState) (allocId size align : Nat) (alloc : LocalAlloc)
    (hPow2 : isPowerOfTwo align = true)
    (hNotGlobal : lookupGlobal st.globalMap allocId = none)
    (hLocal : lookupLocal st.localMap allocId = some alloc)
    (hFrozen : alloc.mutbl = .not) :
    constDeallocate st { prov := some (CtfeProvenance.fromAllocId allocId), offset := 0 } size align =
      .error .deallocImmutable := by
  unfold constDeallocate
  rw [hPow2]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold CtfeProvenance.fromAllocId
  dsimp only
  rw [hNotGlobal]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold deallocatePtr
  dsimp only
  rw [nat_beq_refl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hLocal]
  dsimp only
  rw [hFrozen]

/-- Runtime & Miri fallback bodies (`library/core/src/intrinsics/mod.rs:2715-2749`,
all carrying `#[miri::intrinsic_fallback_is_spec]`). -/
noncomputable def runtimeConstAllocate (_size _align : Nat) : Pointer := nullPtr
noncomputable def runtimeConstDeallocate (_ptr : Pointer) (_size _align : Nat) : Unit := ()
noncomputable def runtimeConstMakeGlobal (ptr : Pointer) : Pointer := ptr

noncomputable def evalDualProbeCtfe (st : CtfeState) : Except EvalError (Bool × Nat) :=
  match constAllocate st 1 1 with
  | .error e => .error e
  | .ok (p, st1) =>
    if !p.isNull then
      match constMakeGlobalBuggy st1 p with
      | .error e => .error e
      | .ok (_, _) => .ok (true, 88)
    else
      .ok (false, 0)

noncomputable def evalDualProbeRuntime (stackPtr : Pointer) : Bool × Nat :=
  let p := runtimeConstAllocate 1 1
  if !p.isNull then
    (false, 0)
  else
    let _ := runtimeConstDeallocate stackPtr 999 3
    let badAlloc := runtimeConstAllocate 1 3
    let gp := runtimeConstMakeGlobal stackPtr
    (badAlloc.isNull && !gp.isNull, 77)

/-- **Theorem 8 (CTFE vs. Runtime/Miri Fallback Divergence):**
The exact same `const fn` evaluates to `(true, 88)` under CTFE and `(true, 77)`
under runtime and Miri (`#[miri::intrinsic_fallback_is_spec]`), while runtime/Miri
silently accept invalid alignment `3` and stack-local pointers. -/
theorem ctfe_vs_runtime_fallback_divergence (st : CtfeState) (stackId : AllocId)
    (hFreshGlobal : lookupGlobal st.globalMap st.nextId = none) :
    evalDualProbeCtfe st = .ok (true, 88) ∧
    evalDualProbeRuntime { prov := some (CtfeProvenance.fromAllocId stackId), offset := 0 } = (true, 77) ∧
    constAllocate st 1 3 = .error .invalidAlign ∧
    runtimeConstAllocate 1 3 = nullPtr := by
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold evalDualProbeCtfe constAllocate
  rw [isPowerOfTwo_one]
  simp only [↓reduceIte, Pointer.isNull, Bool.not_false]
  unfold constMakeGlobalBuggy makeConstHeapPtrGlobal CtfeProvenance.fromAllocId
  dsimp only
  rw [nat_beq_refl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hFreshGlobal]
  unfold lookupLocal
  rw [nat_beq_refl]
  simp only [↓reduceIte]

/-! ## Part III: Repaired Semantics — Completeness & Immutability Soundness -/

noncomputable def HeapInvariants (st : CtfeState) : Prop :=
  (∀ id alloc, lookupLocal st.localMap id = some alloc →
    alloc.kind = .heap true → alloc.mutbl = .not) ∧
  (∀ id alloc, lookupLocal st.localMap id = some alloc →
    (alloc.kind = .stack ∨ alloc.kind = .callerLocation) → alloc.mutbl = .mut_) ∧
  (∀ id, lookupLocal st.localMap id ≠ none → lookupGlobal st.globalMap id = none)

noncomputable def AllLocalReadyForIntern (st : CtfeState) : Prop :=
  ∀ id alloc, lookupLocal st.localMap id = some alloc →
    alloc.kind ≠ .heap false ∧
    alloc.hasPartialPtr = false ∧
    (∀ p, p ∈ alloc.ptrs → p.sharedRef = true)

theorem mem_append_left {α : Type} {x : α} {xs ys : List α} (h : x ∈ xs) :
    x ∈ xs ++ ys := by
  induction xs with
  | nil => cases h
  | cons _ _ ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (ih h')

theorem mem_append_right {α : Type} {x : α} {xs ys : List α} (h : x ∈ ys) :
    x ∈ xs ++ ys := by
  induction xs with
  | nil => exact h
  | cons _ _ ih => exact List.Mem.tail _ ih

theorem mem_append_iff {α : Type} {x : α} {xs ys : List α} :
    x ∈ xs ++ ys ↔ x ∈ xs ∨ x ∈ ys := by
  constructor
  · intro h
    induction xs with
    | nil => exact Or.inr h
    | cons _ _ ih =>
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h' =>
        cases ih h' with
        | inl hl => exact Or.inl (List.Mem.tail _ hl)
        | inr hr => exact Or.inr hr
  · intro h
    cases h with
    | inl hl => exact mem_append_left hl
    | inr hr => exact mem_append_right hr

/-- **Theorem 9 (`constMakeGlobalFixed` Correctness, Provenance WF, and Post-Freeze Guards):** -/
theorem constMakeGlobalFixed_correct_and_blocks_post_freeze_ops
    (st : CtfeState) (size align : Nat)
    (hPow2 : isPowerOfTwo align = true)
    (hFreshGlobal : lookupGlobal st.globalMap st.nextId = none) :
    ∃ p st1 g st2,
      constAllocate st size align = .ok (p, st1) ∧
      constMakeGlobalFixed st1 p = .ok (g, st2) ∧
      g.offset = 0 ∧
      g.prov = some { allocId := st.nextId, immutable := true, sharedRef := true } ∧
      (match g.prov with | some pr => pr.wf | none => False) ∧
      lookupLocal st2.localMap st.nextId =
        some { kind := .heap true, mutbl := .not, size := size, align := align
             , ptrs := [], hasPartialPtr := false } ∧
      constMakeGlobalFixed st2 g = .error .alreadyMadeGlobal ∧
      constDeallocate st2 g size align = .error .deallocImmutable ∧
      ctfeWriteCheck st2 g = .error .writeThroughImmutablePtr ∧
      ctfeWriteCheck st2 p = .error .writeToReadOnly := by
  unfold constAllocate
  rw [hPow2]
  simp only [↓reduceIte]
  let p : Pointer := { prov := some (CtfeProvenance.fromAllocId st.nextId), offset := 0 }
  let st1 : CtfeState :=
    { st with
      nextId := st.nextId + 1
    , localMap := (st.nextId, { kind := .heap false, mutbl := .mut_, size := size
                              , align := align, ptrs := [], hasPartialPtr := false }) :: st.localMap
    }
  let g : Pointer := { prov := some { allocId := st.nextId, immutable := true, sharedRef := true }, offset := 0 }
  let st2 : CtfeState :=
    { st1 with
      localMap := (st.nextId, { kind := .heap true, mutbl := .not, size := size
                              , align := align, ptrs := [], hasPartialPtr := false }) :: st.localMap
    }
  refine ⟨p, st1, g, st2, rfl, ?_, rfl, rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p, st1, g, st2]
    unfold constMakeGlobalFixed makeConstHeapPtrGlobal CtfeProvenance.fromAllocId
    dsimp only
    rw [nat_beq_refl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hFreshGlobal]
    unfold lookupLocal updateLocal
    rw [nat_beq_refl]
    simp only [↓reduceIte]
    rfl
  · dsimp only [st2]
    unfold lookupLocal
    rw [nat_beq_refl]
    simp only [↓reduceIte]
  · unfold constMakeGlobalFixed makeConstHeapPtrGlobal
    dsimp only [g, st2, st1]
    rw [nat_beq_refl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hFreshGlobal]
    unfold lookupLocal
    rw [nat_beq_refl]
    simp only [↓reduceIte]
  · unfold constDeallocate
    rw [hPow2]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    dsimp only [g, st2, st1]
    rw [hFreshGlobal]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold deallocatePtr
    dsimp only
    rw [nat_beq_refl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold lookupLocal
    rw [nat_beq_refl]
    simp only [↓reduceIte]
  · unfold ctfeWriteCheck
    rfl
  · dsimp only [p, st2, st1]
    unfold ctfeWriteCheck CtfeProvenance.fromAllocId
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold lookupLocal
    rw [nat_beq_refl]
    simp only [↓reduceIte]

/-- **Lemma (`prepareAllocFixed` Soundness):** -/
theorem prepareAllocFixed_sound
    (alloc prepared : LocalAlloc) (reqMutbl : Mutability)
    (hOk : prepareAllocFixed alloc reqMutbl = .ok prepared) :
    alloc.kind ≠ .heap false ∧
    (alloc.kind = .heap true → prepared.mutbl = .not) ∧
    (reqMutbl = .not → prepared.mutbl = .not) ∧
    (prepared.kind = alloc.kind) ∧
    (prepared.ptrs = alloc.ptrs) := by
  unfold prepareAllocFixed at hOk
  cases hk : alloc.kind with
  | heap b =>
    rw [hk] at hOk
    cases b with
    | false => cases hOk
    | true =>
      cases hp : alloc.hasPartialPtr with
      | true => rw [hp] at hOk; cases hOk
      | false =>
        rw [hp] at hOk
        simp only [Bool.false_eq_true, ↓reduceIte] at hOk
        injection hOk with hEq
        subst hEq
        refine ⟨fun h => (nomatch h), fun _ => rfl, fun _ => rfl, rfl, rfl⟩
  | stack =>
    rw [hk] at hOk
    cases hp : alloc.hasPartialPtr with
    | true => rw [hp] at hOk; cases hOk
    | false =>
      rw [hp] at hOk
      simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      cases reqMutbl with
      | not =>
        injection hOk with hEq
        subst hEq
        refine ⟨fun h => (nomatch h), fun h => (nomatch h), fun _ => rfl, rfl, rfl⟩
      | mut_ =>
        cases hm : alloc.mutbl with
        | not => rw [hm] at hOk; cases hOk
        | mut_ =>
          rw [hm] at hOk
          injection hOk with hEq
          subst hEq
          refine ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), hk, rfl⟩
  | callerLocation =>
    rw [hk] at hOk
    cases hp : alloc.hasPartialPtr with
    | true => rw [hp] at hOk; cases hOk
    | false =>
      rw [hp] at hOk
      simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      cases reqMutbl with
      | not =>
        injection hOk with hEq
        subst hEq
        refine ⟨fun h => (nomatch h), fun h => (nomatch h), fun _ => rfl, rfl, rfl⟩
      | mut_ =>
        cases hm : alloc.mutbl with
        | not => rw [hm] at hOk; cases hOk
        | mut_ =>
          rw [hm] at hOk
          injection hOk with hEq
          subst hEq
          refine ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), hk, rfl⟩

/-- **Lemma (`prepareAllocFixed` Completeness / Zero ICE #2):** -/
theorem prepareAllocFixed_complete
    (alloc : LocalAlloc) (reqMutbl : Mutability)
    (hNoTransient : alloc.kind ≠ .heap false)
    (hNoPartial : alloc.hasPartialPtr = false)
    (hNonHeapMut : (alloc.kind = .stack ∨ alloc.kind = .callerLocation) → alloc.mutbl = .mut_) :
    ∃ prepared, prepareAllocFixed alloc reqMutbl = .ok prepared := by
  unfold prepareAllocFixed
  cases hk : alloc.kind with
  | heap b =>
    cases b with
    | false => exact False.elim (hNoTransient hk)
    | true =>
      rw [hNoPartial]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl⟩
  | stack =>
    rw [hNoPartial]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases reqMutbl with
    | not => exact ⟨_, rfl⟩
    | mut_ =>
      rw [hNonHeapMut (Or.inl hk)]
      exact ⟨_, rfl⟩
  | callerLocation =>
    rw [hNoPartial]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases reqMutbl with
    | not => exact ⟨_, rfl⟩
    | mut_ =>
      rw [hNonHeapMut (Or.inr hk)]
      exact ⟨_, rfl⟩

/-- Global immutability invariant for all heap-origin entries in `globalMap`. -/
noncomputable def GlobalHeapImmutable (st : CtfeState) : Prop :=
  ∀ id g, lookupGlobal st.globalMap id = some g →
    g.originWasHeap = true → g.mutbl = .not

theorem internShallow_fixed_preserves_invariants
    (st st' : CtfeState) (allocId : AllocId) (reqMutbl : Mutability)
    (isStatic isThreadLocal : Bool) (nextPtrs : List CtfeProvenance)
    (hGlobImm : GlobalHeapImmutable st)
    (hShallow : internShallow .fixed st allocId reqMutbl isStatic isThreadLocal = .ok (nextPtrs, st')) :
    GlobalHeapImmutable st' ∧
    (∃ orig, lookupLocal st.localMap allocId = some orig ∧ orig.kind ≠ .heap false) ∧
    (st'.localMap = removeLocal st.localMap allocId) ∧
    (∀ id g, lookupGlobal st'.globalMap id = some g →
      (id = allocId ∧ (reqMutbl = .not → g.mutbl = .not) ∧ (g.originWasHeap = true → g.mutbl = .not)) ∨
      lookupGlobal st.globalMap id = some g) := by
  unfold internShallow at hShallow
  cases hLoc : lookupLocal st.localMap allocId with
  | none => rw [hLoc] at hShallow; cases hShallow
  | some alloc =>
    rw [hLoc] at hShallow
    dsimp only at hShallow
    cases hPrep : prepareAlloc .fixed alloc reqMutbl with
    | error e => rw [hPrep] at hShallow; cases hShallow
    | ok prepared =>
      rw [hPrep] at hShallow
      dsimp only at hShallow
      cases hTls : (isStatic && isThreadLocal) with
      | true => rw [hTls] at hShallow; cases hShallow
      | false =>
        rw [hTls] at hShallow
        simp only [Bool.false_eq_true, ↓reduceIte] at hShallow
        injection hShallow with hPair
        injection hPair with _ hSt'
        subst hSt'
        have hSound := prepareAllocFixed_sound alloc prepared reqMutbl hPrep
        have hGlobImm' : GlobalHeapImmutable
            { st with
              localMap := removeLocal st.localMap allocId
            , globalMap := insertGlobal st.globalMap allocId
                { isStatic := isStatic, mutbl := prepared.mutbl
                , size := prepared.size, align := prepared.align
                , ptrs := prepared.ptrs, originWasHeap := localKindIsHeap prepared.kind } } := by
          intro id g hG hHeap
          cases hEq : Nat.beq allocId id with
          | true =>
            have hid : allocId = id := (nat_beq_eq allocId id).mp hEq
            subst hid
            dsimp only at hG
            rw [lookupGlobal_insert_same] at hG
            injection hG with hgEq
            subst hgEq
            dsimp only at hHeap
            rw [hSound.2.2.2.1] at hHeap
            cases hk : alloc.kind with
            | heap b =>
              cases b with
              | false => exact False.elim (hSound.1 hk)
              | true => exact hSound.2.1 hk
            | stack => rw [hk] at hHeap; cases hHeap
            | callerLocation => rw [hk] at hHeap; cases hHeap
          | false =>
            have hne : allocId ≠ id := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
            dsimp only at hG
            rw [lookupGlobal_insert_ne _ _ hne] at hG
            exact hGlobImm id g hG hHeap
        refine ⟨hGlobImm', ⟨alloc, rfl, hSound.1⟩, rfl, ?_⟩
        intro id g hG
        cases hEq : Nat.beq allocId id with
        | true =>
          have hid : allocId = id := (nat_beq_eq allocId id).mp hEq
          subst hid
          dsimp only at hG
          rw [lookupGlobal_insert_same] at hG
          injection hG with hgEq
          subst hgEq
          left
          refine ⟨rfl, hSound.2.2.1, ?_⟩
          intro hHeap
          dsimp only at hHeap
          rw [hSound.2.2.2.1] at hHeap
          cases hk : alloc.kind with
          | heap b =>
            cases b with
            | false => exact False.elim (hSound.1 hk)
            | true => exact hSound.2.1 hk
          | stack => rw [hk] at hHeap; cases hHeap
          | callerLocation => rw [hk] at hHeap; cases hHeap
        | false =>
          have hne : allocId ≠ id := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
          dsimp only at hG
          rw [lookupGlobal_insert_ne _ _ hne] at hG
          exact Or.inr hG

/-- **Inductive Soundness Theorem for `internLoop .fixed`:** -/
theorem internLoop_fixed_immutability_and_no_transient_escape
    (baseId : AllocId) (innerMutbl : Mutability) (isStatic isPromoted isThreadLocal : Bool) :
    ∀ (fuel : Nat) (st st' : CtfeState) (justInterned : List AllocId)
      (foundBadMut : Bool) (todo : List CtfeProvenance),
      GlobalHeapImmutable st →
      internLoop .fixed baseId innerMutbl isStatic isPromoted isThreadLocal
        fuel st justInterned foundBadMut todo = .ok st' →
      GlobalHeapImmutable st' ∧
      (∀ id g, lookupGlobal st'.globalMap id = some g →
        lookupGlobal st.globalMap id = none →
        ∃ orig, lookupLocal st.localMap id = some orig ∧ orig.kind ≠ .heap false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st st' justInterned foundBadMut todo hGlobImm hLoop
    cases todo with
    | nil =>
      unfold internLoop at hLoop
      cases foundBadMut with
      | true =>
        simp only [↓reduceIte] at hLoop
        cases hU : st.unleashMiri with
        | true => rw [hU] at hLoop; cases hLoop
        | false => rw [hU] at hLoop; cases hLoop
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
        injection hLoop with hEq
        subst hEq
        exact ⟨hGlobImm, fun _ _ hSome hNone => by rw [hNone] at hSome; cases hSome⟩
    | cons _ _ =>
      unfold internLoop at hLoop
      cases hLoop
  | succ fuel ih =>
    intro st st' justInterned foundBadMut todo hGlobImm hLoop
    cases todo with
    | nil =>
      unfold internLoop at hLoop
      cases foundBadMut with
      | true =>
        simp only [↓reduceIte] at hLoop
        cases hU : st.unleashMiri with
        | true => rw [hU] at hLoop; cases hLoop
        | false => rw [hU] at hLoop; cases hLoop
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
        injection hLoop with hEq
        subst hEq
        exact ⟨hGlobImm, fun _ _ hSome hNone => by rw [hNone] at hSome; cases hSome⟩
    | cons prov rest =>
      unfold internLoop at hLoop
      dsimp only at hLoop
      cases hSelf : (Nat.beq baseId prov.allocId && isStatic) with
      | true =>
        rw [hSelf] at hLoop
        simp only [↓reduceIte] at hLoop
        exact ih st st' justInterned foundBadMut rest hGlobImm hLoop
      | false =>
        rw [hSelf] at hLoop
        simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
        let checkSharedRef : Bool := !isPromoted && Mutability.beq innerMutbl .not && !prov.sharedRef
        let isAlreadyGlobal : Bool :=
          match lookupGlobal st.globalMap prov.allocId with
          | some _ => true
          | none => false
        cases hSkip : (checkSharedRef && isAlreadyGlobal && !memId justInterned prov.allocId) with
        | true =>
          change (if (checkSharedRef && isAlreadyGlobal && !memId justInterned prov.allocId) = true then _ else _) = InternOutcome.ok st' at hLoop
          rw [hSkip] at hLoop
          simp only [↓reduceIte] at hLoop
          exact ih st st' justInterned foundBadMut rest hGlobImm hLoop
        | false =>
          change (if (checkSharedRef && isAlreadyGlobal && !memId justInterned prov.allocId) = true then _ else _) = InternOutcome.ok st' at hLoop
          rw [hSkip] at hLoop
          simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
          cases hGlob : lookupGlobal st.globalMap prov.allocId with
          | some _ =>
            simp only [hGlob, ↓reduceIte] at hLoop
            exact ih st st' justInterned _ rest hGlobImm hLoop
          | none =>
            simp only [hGlob, Bool.false_eq_true, ↓reduceIte] at hLoop
            cases hSh : internShallow .fixed st prov.allocId innerMutbl isStatic isThreadLocal with
            | error e => rw [hSh] at hLoop; cases hLoop
            | ok pair =>
              rcases pair with ⟨nextPtrs, st1⟩
              rw [hSh] at hLoop
              have hStep := internShallow_fixed_preserves_invariants st st1 prov.allocId innerMutbl
                isStatic isThreadLocal nextPtrs hGlobImm hSh
              have hRec := ih st1 st' (prov.allocId :: justInterned) _ (nextPtrs ++ rest) hStep.1 hLoop
              refine ⟨hRec.1, ?_⟩
              intro id g hG' hGNone
              cases hEq : Nat.beq prov.allocId id with
              | true =>
                have hid : prov.allocId = id := (nat_beq_eq prov.allocId id).mp hEq
                subst hid
                exact hStep.2.1
              | false =>
                have hne : prov.allocId ≠ id := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
                have hG1None : lookupGlobal st1.globalMap id = none := by
                  cases hG1 : lookupGlobal st1.globalMap id with
                  | none => rfl
                  | some g1 =>
                    cases hStep.2.2.2 id g1 hG1 with
                    | inl hEqId => exact False.elim (hne hEqId.1.symm)
                    | inr hOld => rw [hGNone] at hOld; cases hOld
                have hFrom1 := hRec.2 id g hG' hG1None
                rcases hFrom1 with ⟨orig, hLoc1, hNotTrans⟩
                rw [hStep.2.2.1] at hLoc1
                rw [lookupLocal_remove_ne _ hne] at hLoc1
                exact ⟨orig, hLoc1, hNotTrans⟩

/-- **Theorem 10a (Universal Repaired Interning Immutability & No-Transient-Escape Soundness):**
For ANY `InternKind`, ANY initial state `st` satisfying `GlobalHeapImmutable st`,
and ANY `baseId` and `fuel`, if `internConstAllocRecursive .fixed st kind baseId fuel = .ok st'`,
then EVERY heap-origin global allocation in `st'` is strictly immutable (`Mutability.not`),
even when `kind = .staticMut`. -/
theorem repaired_interning_immutability_soundness
    (st st' : CtfeState) (kind : InternKind) (baseId fuel : Nat)
    (hGlobImm : GlobalHeapImmutable st)
    (hOk : internConstAllocRecursive .fixed st kind baseId fuel = .ok st') :
    GlobalHeapImmutable st' := by
  unfold internConstAllocRecursive at hOk
  cases kind with
  | constant =>
    dsimp only [internKindParams] at hOk
    simp only [Bool.false_eq_true, ↓reduceIte] at hOk
    cases hSh : internShallow .fixed st baseId .not false false with
    | error e => rw [hSh] at hOk; cases hOk
    | ok pair =>
      rcases pair with ⟨todo0, st1⟩
      rw [hSh] at hOk
      have hStep := internShallow_fixed_preserves_invariants st st1 baseId .not false false todo0 hGlobImm hSh
      exact (internLoop_fixed_immutability_and_no_transient_escape baseId .not false false false
        fuel st1 st' [baseId] false todo0 hStep.1 hOk).1
  | promoted =>
    dsimp only [internKindParams] at hOk
    simp only [Bool.false_eq_true, ↓reduceIte] at hOk
    cases hSh : internShallow .fixed st baseId .not false false with
    | error e => rw [hSh] at hOk; cases hOk
    | ok pair =>
      rcases pair with ⟨todo0, st1⟩
      rw [hSh] at hOk
      have hStep := internShallow_fixed_preserves_invariants st st1 baseId .not false false todo0 hGlobImm hSh
      exact (internLoop_fixed_immutability_and_no_transient_escape baseId .not false true false
        fuel st1 st' [baseId] false todo0 hStep.1 hOk).1
  | staticNot rootIsFreeze =>
    dsimp only [internKindParams] at hOk
    simp only [↓reduceIte] at hOk
    cases hLoc : lookupLocal st.localMap baseId with
    | none => rw [hLoc] at hOk; cases hOk
    | some baseAlloc =>
      rw [hLoc] at hOk
      dsimp only at hOk
      cases hPrep : prepareAlloc .fixed baseAlloc (if rootIsFreeze then .not else .mut_) with
      | error e => rw [hPrep] at hOk; cases hOk
      | ok prepared =>
        rw [hPrep] at hOk
        exact (internLoop_fixed_immutability_and_no_transient_escape baseId .not true false false
          fuel { st with localMap := updateLocal st.localMap baseId prepared } st'
          [baseId] false prepared.ptrs hGlobImm hOk).1
  | staticMut =>
    dsimp only [internKindParams] at hOk
    simp only [↓reduceIte] at hOk
    cases hLoc : lookupLocal st.localMap baseId with
    | none => rw [hLoc] at hOk; cases hOk
    | some baseAlloc =>
      rw [hLoc] at hOk
      dsimp only at hOk
      cases hPrep : prepareAlloc .fixed baseAlloc .mut_ with
      | error e => rw [hPrep] at hOk; cases hOk
      | ok prepared =>
        rw [hPrep] at hOk
        exact (internLoop_fixed_immutability_and_no_transient_escape baseId .mut_ true false false
          fuel { st with localMap := updateLocal st.localMap baseId prepared } st'
          [baseId] false prepared.ptrs hGlobImm hOk).1
  | threadLocalStatic m rootIsFreeze =>
    cases m with
    | not =>
      dsimp only [internKindParams] at hOk
      simp only [↓reduceIte] at hOk
      cases hLoc : lookupLocal st.localMap baseId with
      | none => rw [hLoc] at hOk; cases hOk
      | some baseAlloc =>
        rw [hLoc] at hOk
        dsimp only at hOk
        cases hPrep : prepareAlloc .fixed baseAlloc (if rootIsFreeze then .not else .mut_) with
        | error e => rw [hPrep] at hOk; cases hOk
        | ok prepared =>
          rw [hPrep] at hOk
          exact (internLoop_fixed_immutability_and_no_transient_escape baseId .not true false true
            fuel { st with localMap := updateLocal st.localMap baseId prepared } st'
            [baseId] false prepared.ptrs hGlobImm hOk).1
    | mut_ =>
      dsimp only [internKindParams] at hOk
      simp only [↓reduceIte] at hOk
      cases hLoc : lookupLocal st.localMap baseId with
      | none => rw [hLoc] at hOk; cases hOk
      | some baseAlloc =>
        rw [hLoc] at hOk
        dsimp only at hOk
        cases hPrep : prepareAlloc .fixed baseAlloc .mut_ with
        | error e => rw [hPrep] at hOk; cases hOk
        | ok prepared =>
          rw [hPrep] at hOk
          exact (internLoop_fixed_immutability_and_no_transient_escape baseId .mut_ true false true
            fuel { st with localMap := updateLocal st.localMap baseId prepared } st'
            [baseId] false prepared.ptrs hGlobImm hOk).1

theorem removeLocal_preserves_ready (st : CtfeState) (id : AllocId) (entry : GlobalEntry)
    (hInv : HeapInvariants st) (hReady : AllLocalReadyForIntern st) :
    HeapInvariants { st with localMap := removeLocal st.localMap id, globalMap := insertGlobal st.globalMap id entry } ∧
    AllLocalReadyForIntern { st with localMap := removeLocal st.localMap id, globalMap := insertGlobal st.globalMap id entry } := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro k a hLoc hHeap
      dsimp only at hLoc
      cases hEq : Nat.beq id k with
      | true =>
        have hk : id = k := (nat_beq_eq id k).mp hEq
        subst hk
        rw [lookupLocal_remove_same] at hLoc; cases hLoc
      | false =>
        have hne : id ≠ k := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
        rw [lookupLocal_remove_ne _ hne] at hLoc
        exact hInv.1 k a hLoc hHeap
    · intro k a hLoc hNonHeap
      dsimp only at hLoc
      cases hEq : Nat.beq id k with
      | true =>
        have hk : id = k := (nat_beq_eq id k).mp hEq
        subst hk
        rw [lookupLocal_remove_same] at hLoc; cases hLoc
      | false =>
        have hne : id ≠ k := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
        rw [lookupLocal_remove_ne _ hne] at hLoc
        exact hInv.2.1 k a hLoc hNonHeap
    · intro k hLocNe
      dsimp only at hLocNe ⊢
      cases hEq : Nat.beq id k with
      | true =>
        have hk : id = k := (nat_beq_eq id k).mp hEq
        subst hk
        rw [lookupLocal_remove_same] at hLocNe
        exact False.elim (hLocNe rfl)
      | false =>
        have hne : id ≠ k := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
        rw [lookupLocal_remove_ne _ hne] at hLocNe
        rw [lookupGlobal_insert_ne _ _ hne]
        exact hInv.2.2 k hLocNe
  · intro k a hLoc
    dsimp only at hLoc
    cases hEq : Nat.beq id k with
    | true =>
      have hk : id = k := (nat_beq_eq id k).mp hEq
      subst hk
      rw [lookupLocal_remove_same] at hLoc; cases hLoc
    | false =>
      have hne : id ≠ k := fun he => by subst he; rw [nat_beq_refl] at hEq; cases hEq
      rw [lookupLocal_remove_ne _ hne] at hLoc
      exact hReady k a hLoc

/-- **Theorem 10b (Universal ICE #1 & ICE #2 Elimination in `internLoop .fixed`):**
For ANY `fuel`, ANY `st` satisfying `HeapInvariants st` and
`AllLocalReadyForIntern st`, ANY non-thread-local `isThreadLocal = false`, and
ANY worklist `todo` whose pointers carry `sharedRef = true`:
`internLoop .fixed` NEVER returns `ice1BadMutablePtrSpanBug`,
`ice2PrepareAllocMutAssertFailed`, `errBadMutablePointer`, or
`errConstAllocNotGlobal`. -/
theorem internLoop_fixed_ice_free
    (baseId : AllocId) (innerMutbl : Mutability) (isStatic isPromoted : Bool) :
    ∀ (fuel : Nat) (st : CtfeState) (justInterned : List AllocId)
      (todo : List CtfeProvenance),
      HeapInvariants st →
      AllLocalReadyForIntern st →
      (∀ p, p ∈ todo → p.sharedRef = true) →
      let out := internLoop .fixed baseId innerMutbl isStatic isPromoted false
                   fuel st justInterned false todo
      out ≠ .fail .ice1BadMutablePtrSpanBug ∧
      out ≠ .fail .ice2PrepareAllocMutAssertFailed ∧
      out ≠ .fail .errBadMutablePointer ∧
      out ≠ .fail .errConstAllocNotGlobal := by
  intro fuel
  induction fuel with
  | zero =>
    intro st justInterned todo _ _ _
    cases todo with
    | nil =>
      exact ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h)⟩
    | cons _ _ =>
      exact ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h)⟩
  | succ fuel ih =>
    intro st justInterned todo hInv hReady hTodoShared
    cases todo with
    | nil =>
      exact ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h)⟩
    | cons prov rest =>
      have hProvShared : prov.sharedRef = true := hTodoShared prov (List.Mem.head _)
      have hRestShared : ∀ p, p ∈ rest → p.sharedRef = true :=
        fun p hp => hTodoShared p (List.Mem.tail _ hp)
      unfold internLoop
      dsimp only
      cases hSelf : (Nat.beq baseId prov.allocId && isStatic) with
      | true =>
        simp only [↓reduceIte]
        exact ih st justInterned rest hInv hReady hRestShared
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hProvShared]
        simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        cases hGlob : lookupGlobal st.globalMap prov.allocId with
        | some _ =>
          simp only [↓reduceIte]
          exact ih st justInterned rest hInv hReady hRestShared
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold internShallow
          cases hLoc : lookupLocal st.localMap prov.allocId with
          | none =>
            dsimp only
            exact ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h)⟩
          | some alloc =>
            dsimp only
            have hAllocReady := hReady prov.allocId alloc hLoc
            have hPrepEx := prepareAllocFixed_complete alloc innerMutbl
              hAllocReady.1 hAllocReady.2.1 (hInv.2.1 prov.allocId alloc hLoc)
            rcases hPrepEx with ⟨prepared, hPrep⟩
            have hPrepSound := prepareAllocFixed_sound alloc prepared innerMutbl hPrep
            unfold prepareAlloc
            rw [hPrep]
            simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            have hNext := removeLocal_preserves_ready st prov.allocId
              { isStatic := isStatic, mutbl := prepared.mutbl
              , size := prepared.size, align := prepared.align
              , ptrs := prepared.ptrs, originWasHeap := localKindIsHeap prepared.kind }
              hInv hReady
            have hNewTodoShared : ∀ p, p ∈ prepared.ptrs ++ rest → p.sharedRef = true := by
              intro p hp
              cases (mem_append_iff.mp hp) with
              | inl hl =>
                rw [hPrepSound.2.2.2.2] at hl
                exact hAllocReady.2.2 p hl
              | inr hr => exact hRestShared p hr
            exact ih _ (prov.allocId :: justInterned) (prepared.ptrs ++ rest)
              hNext.1 hNext.2 hNewTodoShared

noncomputable def stateAfterFixedMakeGlobalRaw (unleashMiri : Bool) : CtfeState :=
  let st0 : CtfeState :=
    { nextId := 1
    , localMap := [(0, { kind := .stack, mutbl := .mut_, size := 8, align := 8
                       , ptrs := [], hasPartialPtr := false })]
    , deadMap := []
    , globalMap := []
    , unleashMiri := unleashMiri
    }
  match constAllocate st0 1 1 with
  | .error _ => st0
  | .ok (p, st1) =>
    match constMakeGlobalFixed st1 p with
    | .error _ => st1
    | .ok (g, st2) =>
      match g.prov with
      | none => st2
      | some prov =>
        { st2 with
          localMap := updateLocal st2.localMap 0
            { kind := .stack, mutbl := .mut_, size := 8, align := 8
            , ptrs := [prov], hasPartialPtr := false } }

/-- **Theorem 10c (Concrete End-to-End Repaired Compilation Across ALL Four Contexts):**
Building a `const_allocate` + `constMakeGlobalFixed` raw `*const u8` pointer and
interning via `internConstAllocRecursive .fixed` succeeds (`ok st'`) with the
interned heap allocation strictly immutable (`g.mutbl = .not`) across ALL FOUR
contexts (`const`, `promoted`, immutable `static`, AND `static mut`). -/
theorem repaired_constMakeGlobal_and_prepareAlloc_succeeds_all_four_contexts
    (rootIsFreeze unleashMiri : Bool) :
    (∃ st', internConstAllocRecursive .fixed (stateAfterFixedMakeGlobalRaw unleashMiri) .constant 0 10 = .ok st' ∧
            ∃ g, lookupGlobal st'.globalMap 1 = some g ∧ g.mutbl = .not) ∧
    (∃ st', internConstAllocRecursive .fixed (stateAfterFixedMakeGlobalRaw unleashMiri) .promoted 0 10 = .ok st' ∧
            ∃ g, lookupGlobal st'.globalMap 1 = some g ∧ g.mutbl = .not) ∧
    (∃ st', internConstAllocRecursive .fixed (stateAfterFixedMakeGlobalRaw unleashMiri) (.staticNot rootIsFreeze) 0 10 = .ok st' ∧
            ∃ g, lookupGlobal st'.globalMap 1 = some g ∧ g.mutbl = .not) ∧
    (∃ st', internConstAllocRecursive .fixed (stateAfterFixedMakeGlobalRaw unleashMiri) .staticMut 0 10 = .ok st' ∧
            ∃ g, lookupGlobal st'.globalMap 1 = some g ∧ g.mutbl = .not) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases unleashMiri <;> exact ⟨_, rfl, _, rfl, rfl⟩
  · cases unleashMiri <;> exact ⟨_, rfl, _, rfl, rfl⟩
  · cases rootIsFreeze <;> cases unleashMiri <;> exact ⟨_, rfl, _, rfl, rfl⟩
  · cases unleashMiri <;> exact ⟨_, rfl, _, rfl, rfl⟩

/-- **Theorem 11 (Pre-Call Alias Provenance Boundary):**
If a caller retains a pre-call alias `p` (from `const_allocate`, with
`sharedRef = false`), calls `let _ = constMakeGlobalFixed(p)` discarding the
returned pointer, and returns `p as *const u8` in a `const`:
fixing ONLY `const_make_global`'s return value still leaves `p.sharedRef = false`,
so strict `internLoop` still hits `ice1BadMutablePtrSpanBug` unless either
(a) `const_make_global`'s return value is used, or (b) `intern_const_alloc_recursive`
exempts `Heap { wasMadeGlobal := true }` allocations or emits a clean error. -/
theorem repaired_constMakeGlobalFixed_precall_alias_boundary :
    internConstAllocRecursive .fixed
      (mkSingleHeapRootState .mut_ (CtfeProvenance.fromAllocId 1) true .not false)
      .constant 0 10 = .fail .ice1BadMutablePtrSpanBug := by
  rfl

/-- **Theorem 12 (Pre-Interned Cross-`const` Workaround for `static mut` in Buggy `rustc`):**
If a `const_make_global` allocation (id 1) was ALREADY interned into `globalMap`
by a separate `const` item (`GlobalAlloc::Memory`), referencing it from a
`static mut` root bypasses `internShallow`/`prepareAlloc` (`intern.rs:324`) and
succeeds even in buggy `rustc` while keeping allocation 1 immutable. -/
theorem static_mut_preinterned_const_avoids_ice2_in_buggy_rustc
    (immutable sharedRef unleashMiri : Bool) :
    let st : CtfeState :=
      { nextId := 2
      , localMap :=
          [(0, { kind := .stack, mutbl := .mut_, size := 8, align := 8
               , ptrs := [{ allocId := 1, immutable := immutable, sharedRef := sharedRef }]
               , hasPartialPtr := false })]
      , deadMap := []
      , globalMap :=
          [(1, { isStatic := false, mutbl := .not, size := 1, align := 1
               , ptrs := [], originWasHeap := true })]
      , unleashMiri := unleashMiri
      }
    ∃ st', internConstAllocRecursive .buggy st .staticMut 0 10 = .ok st' ∧
           ∃ g, lookupGlobal st'.globalMap 1 = some g ∧ g.mutbl = .not := by
  cases immutable <;> cases sharedRef <;> cases unleashMiri <;> exact ⟨_, rfl, _, rfl, rfl⟩

end ConstHeapInterning
