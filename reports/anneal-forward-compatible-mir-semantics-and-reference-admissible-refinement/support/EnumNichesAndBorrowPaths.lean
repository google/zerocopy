-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Extending Forward-Compatible MIR Semantics to Enums, Niches, and Path-Indexed Borrow Projections

This standalone, zero-`sorry`, zero-axiom Lean 4 module mechanizes two extensions to forward-compatible MIR operational semantics:

1. **Challenge 5A — Path-Indexed Borrow Projections (`&s.field_k`, `&mut s.field_k`)**:
   - Replaces scalar `fieldDepth : Nat` in `MirVal.ref` with `fieldPath : List Nat`,
     supporting arbitrary multi-field projections (`.field k` for any `k : Nat`) and
     nested paths (`&s.f1.f2`, reborrows `&(*r).field_k`) over `.fieldCons` / `.fieldNil`
     aggregate spines.
   - Defines `readFieldAt`, `writeFieldAt`, `peelPath`, `writePath`, `resolveRefPath`,
     `evalRefProjPath`, and `mutateRefPath`, and proves unconditional read-after-write
     and sibling frame-preservation theorems.
   - Formalizes the decoupling between place projection (`&s.field_k`, which succeeds in
     all `(adtPad, adtFieldOffset)` worlds even for `#[repr(Rust)]` structs) and byte-level
     `offset_of!(S, field_k)` (`evalLayoutQuery (.offsetOf ...)`), which is Reference-determined
     for `#[repr(C)]` structs (`r[layout.repr.c.struct]`) and world-varying (`adtFieldOffset`)
     for `#[repr(Rust)]` structs unless constrained by a compile-time `const` guard.

2. **Challenge 5B — Forward-Compatible `enum` and `Option<T>` Niche Layout & Transmute Semantics**:
   - Models `EnumRepr` across `reprRustEnum`, `reprIntFieldless` (`r[layout.repr.primitive.fieldless]`),
     `reprCEnumFieldless` (`r[layout.repr.c.enum.fieldless]`), `reprCIntTagged`
     (`r[layout.repr.c.enum.fields]`, `r[layout.repr.c-primitive]`), `reprIntTagged`
     (`r[layout.repr.primitive.fields]`), and `optionNiche` (`r[layout.option-niche]`).
   - Defines the closed inductive Reference niche predicate `optionNicheGuaranteed`
     ($\mathcal{N}_{\text{Option}}$: `&U`, `&mut U`, `NonNull<U>`, `fn(...)`, `NonZero<Int>`,
     and `#[repr(transparent)]` wrappers around them with 1-ZST sibling fields, excluding
     `UnsafeCell`/`UnsafePinned`).
   - Proves the four flagship verification theorems:
     1. `transmute::<Option<NonZeroU32>, u32>` (and `#[repr(transparent)]` wrappers around
        `NonZeroU32`) succeeds unconditionally across all `adtPad` worlds.
     2. `transmute::<MyReprU8FieldlessEnum, u8>` succeeds unconditionally across all `adtPad`
        worlds (and `u8 -> MyReprU8FieldlessEnum` succeeds iff the discriminant is valid).
     3. `transmute::<Option<bool>, u8>` is rejected in unguarded forward-compatible mode
        (fails when `adtPad > 0` and has non-guaranteed niche encoding).
     4. Multi-field `&s.field_1` and `&mut s.field_1` projections step cleanly without UB
        across all `adtPad` worlds while preserving sibling fields.
-/

namespace EnumNichesAndBorrowPaths

/-! ## Part 1: Core Identifiers, Values, and Path-Indexed References (`Challenge 5A`) -/

/-- Local variable identifier (`_0`, `_1`, ...). -/
abbrev LocalId := Nat

/-- Algebraic Data Type (struct or enum) identifier. -/
abbrev AdtId := Nat

/-- Runtime values in the forward-compatible MIR operational model.
`MirVal.ref` replaces the scalar `fieldDepth : Nat` with a path
`fieldPath : List Nat` of 0-based field indices from the root referent to the
borrowed sub-place. -/
inductive MirVal where
  | int (bits : Nat) (sizeBytes : Nat)
  | nonZeroInt (bits : Nat) (sizeBytes : Nat)
  | unit
  | fieldNil
  | fieldCons (head : MirVal) (tail : MirVal)
  | adt (id : AdtId) (fields : MirVal)
  | enumAdt (id : AdtId) (variantIdx : Nat) (fields : MirVal)
  | ref (frameId : Nat) (gen : Nat) (loc : LocalId) (derefDepth : Nat) (fieldPath : List Nat)
  | rawPtr (frameId : Nat) (gen : Nat) (loc : LocalId) (fieldPath : List Nat)
  | fnPtr (fnId : Nat)
  | uninit (sizeBytes : Nat)
  deriving DecidableEq, Repr

/-- Read the `idx`-th field from a `.fieldCons` / `.fieldNil` spine. -/
def readFieldAt : Nat → MirVal → Option MirVal
  | 0, .fieldCons head _ => some head
  | idx + 1, .fieldCons _ tail => readFieldAt idx tail
  | _, _ => none

/-- Functionally update the `idx`-th field in a `.fieldCons` / `.fieldNil` spine,
returning `none` if `idx` is out of bounds. -/
def writeFieldAt (idx : Nat) (newVal : MirVal) : MirVal → Option MirVal
  | .fieldCons head tail =>
    match idx with
    | 0 => some (.fieldCons newVal tail)
    | idx' + 1 =>
      match writeFieldAt idx' newVal tail with
      | some tail' => some (.fieldCons head tail')
      | none => none
  | _ => none

/-- Extract the nested sub-value at `fieldPath : List Nat` inside a struct/ADT value. -/
def peelPath : List Nat → MirVal → Option MirVal
  | [], v => some v
  | idx :: rest, .adt _ fields =>
    match readFieldAt idx fields with
    | some fieldVal => peelPath rest fieldVal
    | none => none
  | idx :: rest, .enumAdt _ _ fields =>
    match readFieldAt idx fields with
    | some fieldVal => peelPath rest fieldVal
    | none => none
  | _, _ => none

/-- Functionally update the nested sub-value at `fieldPath : List Nat` inside a
struct/ADT value, preserving the outer ADT tag and all sibling fields. -/
def writePath : List Nat → MirVal → MirVal → Option MirVal
  | [], newVal, _ => some newVal
  | idx :: rest, newVal, .adt id fields =>
    match readFieldAt idx fields with
    | some oldField =>
      match writePath rest newVal oldField with
      | some updatedField =>
        match writeFieldAt idx updatedField fields with
        | some fields' => some (.adt id fields')
        | none => none
      | none => none
    | none => none
  | idx :: rest, newVal, .enumAdt id vIdx fields =>
    match readFieldAt idx fields with
    | some oldField =>
      match writePath rest newVal oldField with
      | some updatedField =>
        match writeFieldAt idx updatedField fields with
        | some fields' => some (.enumAdt id vIdx fields')
        | none => none
      | none => none
    | none => none
  | _ :: _, _, _ => none

/-! ### Algebraic Laws for `readFieldAt`, `writeFieldAt`, `peelPath`, and `writePath` -/

/-- **Unconditional Spine Read-After-Write (`readFieldAt_writeFieldAt_same`)**:
Reading field `idx` immediately after writing `newVal` to field `idx` yields `some newVal`. -/
theorem readFieldAt_writeFieldAt_same (idx : Nat) (newVal fields fields' : MirVal)
    (hWrite : writeFieldAt idx newVal fields = some fields') :
    readFieldAt idx fields' = some newVal := by
  induction fields generalizing idx fields' with
  | fieldCons head tail _ ihTail =>
    cases idx with
    | zero =>
      simp [writeFieldAt] at hWrite
      subst hWrite
      rfl
    | succ idx' =>
      simp only [writeFieldAt] at hWrite
      cases hRec : writeFieldAt idx' newVal tail with
      | none =>
        rw [hRec] at hWrite
        simp at hWrite
      | some tail' =>
        rw [hRec] at hWrite
        simp at hWrite
        subst hWrite
        simp [readFieldAt, ihTail idx' tail' hRec]
  | _ => simp [writeFieldAt] at hWrite

/-- **Unconditional Spine Frame Theorem (`readFieldAt_writeFieldAt_ne`)**:
Writing to field `idx` leaves every sibling field `j ≠ idx` unchanged. -/
theorem readFieldAt_writeFieldAt_ne {idx j : Nat} {newVal fields fields' : MirVal}
    (hNe : j ≠ idx)
    (hWrite : writeFieldAt idx newVal fields = some fields') :
    readFieldAt j fields' = readFieldAt j fields := by
  induction fields generalizing idx j fields' with
  | fieldCons head tail _ ihTail =>
    cases idx with
    | zero =>
      simp [writeFieldAt] at hWrite
      subst hWrite
      cases j with
      | zero => exact absurd rfl hNe
      | succ j' => rfl
    | succ idx' =>
      simp only [writeFieldAt] at hWrite
      cases hRec : writeFieldAt idx' newVal tail with
      | none => rw [hRec] at hWrite; simp at hWrite
      | some tail' =>
        rw [hRec] at hWrite
        simp at hWrite
        subst hWrite
        cases j with
        | zero => rfl
        | succ j' =>
          have hNe' : j' ≠ idx' := fun hEq => hNe (congrArg Nat.succ hEq)
          simp [readFieldAt, ihTail hNe' hRec]
  | _ => simp [writeFieldAt] at hWrite

/-- **Read-After-Write Theorem for Nested Field Paths (`peelPath_writePath_same`)**:
For any aggregate `v` and any path `path : List Nat`, reading `path` after updating
`path` to `newVal` returns `some newVal`. -/
theorem peelPath_writePath_same (path : List Nat) (newVal v v' : MirVal)
    (hWrite : writePath path newVal v = some v') :
    peelPath path v' = some newVal := by
  induction path generalizing v v' with
  | nil =>
    simp [writePath] at hWrite
    subst hWrite
    rfl
  | cons idx rest ih =>
    cases v with
    | adt id fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hReadAfter := readFieldAt_writeFieldAt_same idx updatedField fields fields' hUpd
            simp [peelPath, hReadAfter, ih oldField updatedField hSub]
    | enumAdt id vIdx fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hReadAfter := readFieldAt_writeFieldAt_same idx updatedField fields fields' hUpd
            simp [peelPath, hReadAfter, ih oldField updatedField hSub]
    | _ => simp [writePath] at hWrite

/-- Disjointness of two field paths: they diverge at some field index (`idx1 ≠ idx2`). -/
inductive DisjointPath : List Nat → List Nat → Prop where
  | diffHead {idx1 idx2 : Nat} (rest1 rest2 : List Nat) (hNe : idx1 ≠ idx2) :
      DisjointPath (idx1 :: rest1) (idx2 :: rest2)
  | sameHead (idx : Nat) {rest1 rest2 : List Nat} (hSub : DisjointPath rest1 rest2) :
      DisjointPath (idx :: rest1) (idx :: rest2)

/-- **Sibling Frame Theorem for Nested Field Paths (`peelPath_writePath_disjoint`)**:
Updating a sub-place at `path1` leaves every disjoint sub-place `path2` unchanged. -/
theorem peelPath_writePath_disjoint {path1 path2 : List Nat} {newVal v v' : MirVal}
    (hDisj : DisjointPath path1 path2)
    (hWrite : writePath path1 newVal v = some v') :
    peelPath path2 v' = peelPath path2 v := by
  induction hDisj generalizing v v' with
  | @diffHead idx1 idx2 rest1 rest2 hNe =>
    cases v with
    | adt id fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx1 fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest1 newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx1 updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hFrame := readFieldAt_writeFieldAt_ne hNe.symm hUpd
            simp [peelPath, hFrame]
    | enumAdt id vIdx fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx1 fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest1 newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx1 updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hFrame := readFieldAt_writeFieldAt_ne hNe.symm hUpd
            simp [peelPath, hFrame]
    | _ => simp [writePath] at hWrite
  | @sameHead idx rest1 rest2 _ ih =>
    cases v with
    | adt id fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest1 newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hReadSame := readFieldAt_writeFieldAt_same idx updatedField fields fields' hUpd
            simp [peelPath, hReadSame, hRead, ih hSub]
    | enumAdt id vIdx fields =>
      simp only [writePath] at hWrite
      cases hRead : readFieldAt idx fields with
      | none => rw [hRead] at hWrite; simp at hWrite
      | some oldField =>
        rw [hRead] at hWrite
        dsimp only at hWrite
        cases hSub : writePath rest1 newVal oldField with
        | none => rw [hSub] at hWrite; simp at hWrite
        | some updatedField =>
          rw [hSub] at hWrite
          dsimp only at hWrite
          cases hUpd : writeFieldAt idx updatedField fields with
          | none => rw [hUpd] at hWrite; simp at hWrite
          | some fields' =>
            rw [hUpd] at hWrite
            simp at hWrite
            subst hWrite
            have hReadSame := readFieldAt_writeFieldAt_same idx updatedField fields fields' hUpd
            simp [peelPath, hReadSame, hRead, ih hSub]
    | _ => simp [writePath] at hWrite

/-! ### Local Store, Reference Resolution (`resolveRefPath`), and Mutation (`mutateRefPath`) -/

/-- A local store mapping `LocalId` to `(generation, allocated, value)`. -/
structure LocalSlot where
  gen : Nat := 0
  allocated : Bool := true
  val : MirVal := .unit
  deriving DecidableEq, Repr

/-- Execution state parameterized by both local slots and the world's opaque layout choices:
- `adtPad : AdtId → Nat` (compiler-chosen extra padding bytes for `#[repr(Rust)]` ADTs and
  non-Reference-guaranteed enum niches, modeling unpinned compiler layout freedom),
- `adtFieldOffset : AdtId → Nat → Option Nat` (compiler-chosen field byte offsets for
  `#[repr(Rust)]` structs when queried by `offset_of!`). -/
structure State where
  frameId : Nat := 0
  locals : List LocalSlot := []
  adtPad : AdtId → Nat := fun _ => 0
  adtFieldOffset : AdtId → Nat → Option Nat := fun _ _ => none

def getLocalSlot : List LocalSlot → LocalId → Option LocalSlot
  | [], _ => none
  | slot :: _, 0 => some slot
  | _ :: rest, idx + 1 => getLocalSlot rest idx

def setLocalSlot : List LocalSlot → LocalId → LocalSlot → Option (List LocalSlot)
  | [], _, _ => none
  | _ :: rest, 0, newSlot => some (newSlot :: rest)
  | slot :: rest, idx + 1, newSlot =>
    match setLocalSlot rest idx newSlot with
    | some rest' => some (slot :: rest')
    | none => none

/-- Place projection elements (`*place` and `.field idx`). -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  deriving DecidableEq, Repr

/-- Resolve a direct (`derefDepth = 0`) reference against `s : State`. -/
def resolveDirectRefPath (s : State) (frameId : Nat) (gen : Nat) (loc : LocalId)
    (fieldPath : List Nat) : Option MirVal :=
  if frameId == s.frameId then
    match getLocalSlot s.locals loc with
    | some slot =>
      if slot.allocated && slot.gen == gen then
        peelPath fieldPath slot.val
      else
        none
    | none => none
  else
    none

/-- Structurally recursive reference resolution over `derefDepth : Nat`:
- When `derefDepth = 0`, looks up `loc` in `s.locals` (checking `frameId` and live `gen`)
  and peels `fieldPath : List Nat` via `peelPath`.
- When `derefDepth = d + 1`, first resolves the inner reference stored at `(loc, d, [])`
  and then peels `fieldPath` from its referent. -/
def resolveRefPath (s : State) (frameId : Nat) (gen : Nat) (loc : LocalId) :
    Nat → List Nat → Option MirVal
  | 0, fieldPath => resolveDirectRefPath s frameId gen loc fieldPath
  | d + 1, fieldPath =>
    match resolveRefPath s frameId gen loc d [] with
    | some (.ref f' g' loc' 0 basePath) =>
      match resolveDirectRefPath s f' g' loc' basePath with
      | some targetVal => peelPath fieldPath targetVal
      | none => none
    | _ => none

/-- Evaluate a borrow expression `&place` or `&mut place` starting from a base reference
`(frameId, gen, loc, derefDepth, fieldPath)` and a projection list `projs : List PlaceElem`.
Unlike a depth-only `evalRefProj` (which rejects `.field k` for `k ≥ 1`), `evalRefProjPath`
accepts `.field idx` for **any** valid field index `idx : Nat` and appends `idx` to `fieldPath`! -/
def evalRefProjPath (s : State) (frameId : Nat) (gen : Nat) (loc : LocalId)
    (derefDepth : Nat) (fieldPath : List Nat) :
    List PlaceElem → MirVal → Option MirVal
  | [], _ => some (.ref frameId gen loc derefDepth fieldPath)
  | .field idx :: rest, .adt _ fields =>
    match readFieldAt idx fields with
    | some fieldVal =>
      evalRefProjPath s frameId gen loc derefDepth (fieldPath ++ [idx]) rest fieldVal
    | none => none
  | .field idx :: rest, .enumAdt _ _ fields =>
    match readFieldAt idx fields with
    | some fieldVal =>
      evalRefProjPath s frameId gen loc derefDepth (fieldPath ++ [idx]) rest fieldVal
    | none => none
  | .deref :: rest, .ref f' g' loc' d' path' =>
    match resolveRefPath s f' g' loc' d' path' with
    | some target =>
      evalRefProjPath s f' g' loc' d' path' rest target
    | none => none
  | _, _ => none

/-- Mutate the sub-place targeted by a mutable reference
`MirVal.ref frameId gen loc derefDepth fieldPath` to `newVal` in `s : State`. -/
def mutateRefPath (s : State) (frameId : Nat) (gen : Nat) (loc : LocalId)
    (derefDepth : Nat) (fieldPath : List Nat) (newVal : MirVal) : Option State :=
  match derefDepth with
  | 0 =>
    if frameId == s.frameId then
      match getLocalSlot s.locals loc with
      | some slot =>
        if slot.allocated && slot.gen == gen then
          match writePath fieldPath newVal slot.val with
          | some updatedRoot =>
            match setLocalSlot s.locals loc { slot with val := updatedRoot } with
            | some locals' => some { s with locals := locals' }
            | none => none
          | none => none
        else
          none
      | none => none
    else
      none
  | _ + 1 => none

theorem getLocalSlot_setLocalSlot_same (locals locals' : List LocalSlot) (loc : LocalId)
    (newSlot : LocalSlot)
    (hSet : setLocalSlot locals loc newSlot = some locals') :
    getLocalSlot locals' loc = some newSlot := by
  induction locals generalizing loc locals' with
  | nil => simp [setLocalSlot] at hSet
  | cons slot rest ih =>
    cases loc with
    | zero =>
      simp [setLocalSlot] at hSet
      subst hSet
      rfl
    | succ idx =>
      simp only [setLocalSlot] at hSet
      cases hRec : setLocalSlot rest idx newSlot with
      | none => rw [hRec] at hSet; simp at hSet
      | some rest' =>
        rw [hRec] at hSet
        simp at hSet
        subst hSet
        simp [getLocalSlot, ih rest' idx hRec]

/-- **Reference Read-After-Write Theorem (`resolveRefPath_mutateRefPath_same`)**:
Mutating through a direct reference `MirVal.ref frameId gen loc 0 fieldPath` and then reading
through that same reference yields `some newVal` across **all** `(adtPad, adtFieldOffset)` worlds. -/
theorem resolveRefPath_mutateRefPath_same (s s' : State) (frameId gen : Nat) (loc : LocalId)
    (fieldPath : List Nat) (newVal : MirVal)
    (hMut : mutateRefPath s frameId gen loc 0 fieldPath newVal = some s') :
    resolveRefPath s' frameId gen loc 0 fieldPath = some newVal := by
  simp only [mutateRefPath] at hMut
  split at hMut
  · rename_i hFrame
    cases hSlot : getLocalSlot s.locals loc with
    | none => rw [hSlot] at hMut; simp at hMut
    | some slot =>
      rw [hSlot] at hMut
      dsimp only at hMut
      split at hMut
      · rename_i hLive
        cases hWrite : writePath fieldPath newVal slot.val with
        | none => rw [hWrite] at hMut; simp at hMut
        | some updatedRoot =>
          rw [hWrite] at hMut
          dsimp only at hMut
          cases hSet : setLocalSlot s.locals loc { slot with val := updatedRoot } with
          | none => rw [hSet] at hMut; simp at hMut
          | some locals' =>
            rw [hSet] at hMut
            simp at hMut
            subst hMut
            have hGetAfter := getLocalSlot_setLocalSlot_same s.locals locals' loc
              { slot with val := updatedRoot } hSet
            have hPeel := peelPath_writePath_same fieldPath newVal slot.val updatedRoot hWrite
            simp [resolveRefPath, resolveDirectRefPath, hFrame, hGetAfter, hLive, hPeel]
      · simp at hMut
  · simp at hMut

/-- **Reference Sibling-Field Frame Theorem (`resolveRefPath_mutateRefPath_disjoint`)**:
Mutating through `&mut s.fieldPath1` preserves the value observed through any disjoint
reference `&s.fieldPath2` (such as `&s.field_0` when mutating `&mut s.field_1`). -/
theorem resolveRefPath_mutateRefPath_disjoint (s s' : State) (frameId gen : Nat) (loc : LocalId)
    (fieldPath1 fieldPath2 : List Nat) (newVal : MirVal)
    (hDisj : DisjointPath fieldPath1 fieldPath2)
    (hMut : mutateRefPath s frameId gen loc 0 fieldPath1 newVal = some s') :
    resolveRefPath s' frameId gen loc 0 fieldPath2 =
      resolveRefPath s frameId gen loc 0 fieldPath2 := by
  simp only [mutateRefPath] at hMut
  split at hMut
  · rename_i hFrame
    cases hSlot : getLocalSlot s.locals loc with
    | none => rw [hSlot] at hMut; simp at hMut
    | some slot =>
      rw [hSlot] at hMut
      dsimp only at hMut
      split at hMut
      · rename_i hLive
        cases hWrite : writePath fieldPath1 newVal slot.val with
        | none => rw [hWrite] at hMut; simp at hMut
        | some updatedRoot =>
          rw [hWrite] at hMut
          dsimp only at hMut
          cases hSet : setLocalSlot s.locals loc { slot with val := updatedRoot } with
          | none => rw [hSet] at hMut; simp at hMut
          | some locals' =>
            rw [hSet] at hMut
            simp at hMut
            subst hMut
            have hGetAfter := getLocalSlot_setLocalSlot_same s.locals locals' loc
              { slot with val := updatedRoot } hSet
            have hPeel := peelPath_writePath_disjoint hDisj hWrite
            simp [resolveRefPath, resolveDirectRefPath, hFrame, hGetAfter, hSlot, hLive, hPeel]
      · simp at hMut
  · simp at hMut

/-! ## Part 2: Forward-Compatible Type Layout for Structs, Enums, and `Option<T>` Niches (`Challenge 5B`) -/

/-- Primitive integer widths (`u8..=u128`, `i8..=i128`, `usize`, `isize`). -/
inductive IntWidth where
  | bits8
  | bits16
  | bits32
  | bits64
  | bits128
  | ptrSize
  deriving DecidableEq, Repr

/-- Target ABI parameters relevant to layout and `#[repr(C)]` enums for target-parameterized layout evaluation. -/
structure TargetLayout where
  ptrByteWidth : Nat := 8
  ptrAlignBytes : Nat := 8
  i128AlignBytes : Nat := 16
  cEnumByteWidth : Nat := 4
  cEnumAlignBytes : Nat := 4
  deriving DecidableEq, Repr

def defaultTarget64 : TargetLayout := {}

def IntWidth.byteSize (t : TargetLayout) : IntWidth → Nat
  | .bits8 => 1
  | .bits16 => 2
  | .bits32 => 4
  | .bits64 => 8
  | .bits128 => 16
  | .ptrSize => t.ptrByteWidth

def IntWidth.alignBytes (t : TargetLayout) : IntWidth → Nat
  | .bits8 => 1
  | .bits16 => 2
  | .bits32 => 4
  | .bits64 => 8
  | .bits128 => t.i128AlignBytes
  | .ptrSize => t.ptrAlignBytes

/-- Types in the forward-compatible MIR model. -/
inductive MirTy where
  | bool
  | char
  | scalar (signed : Bool) (width : IntWidth)
  | nonZeroScalar (signed : Bool) (width : IntWidth)
  | ref (mutability : Bool) (inner : MirTy)
  | nonNullPtr (inner : MirTy)
  | rawPtr (inner : MirTy)
  | fnPtr
  | unit
  | never
  | adt (id : AdtId)
  deriving DecidableEq, Repr

/-- Struct representation attributes (`r[layout.repr.rust]`, `r[layout.repr.c.struct]`,
`r[layout.repr.transparent]`).
`isNoNicheInteriorMutable` records `UnsafeCell` / `UnsafePinned`, which inhibit niche
propagation through `#[repr(transparent)]` (`compiler/rustc_ty_utils/src/layout.rs:717`). -/
inductive StructRepr where
  | reprRust
  | reprC
  | reprTransparent (isNoNicheInteriorMutable : Bool := false)
  deriving DecidableEq, Repr

/-- A single enum variant declaration (`name`, explicit/assigned integer `discriminant`,
and payload `fields`). -/
structure VariantDecl where
  name : String
  discriminant : Nat
  fields : List MirTy
  deriving DecidableEq, Repr

/-- Enum representation attributes under `r[layout.repr.rust]`, `r[layout.repr.c.enum]`,
`r[layout.repr.primitive]`, `r[layout.repr.c-primitive]`, and `r[layout.option-niche]`. -/
inductive EnumRepr where
  /-- Default `#[repr(Rust)]` enum (`r[layout.repr.rust]`).
  `minByteSize` is the minimum Reference-admissible size (e.g., `1` for `Option<bool>` or a
  small enum when `rustc` applies an opportunistic niche), to which the world adds `s.adtPad id`. -/
  | reprRustEnum (minByteSize : Nat) (minAlignBytes : Nat)
  /-- Fieldless `#[repr(u8)]` / `#[repr(i32)]` / etc. enum (`r[layout.repr.primitive.fieldless]`).
  Guaranteed to have the exact size and alignment of `intWidth` across all `adtPad` worlds. -/
  | reprIntFieldless (signed : Bool) (intWidth : IntWidth)
  /-- Fieldless `#[repr(C)]` enum (`r[layout.repr.c.enum.fieldless]`).
  Guaranteed to match the target C ABI default `enum` width (`t.cEnumByteWidth`) across all worlds. -/
  | reprCEnumFieldless
  /-- Data-carrying `#[repr(C, Int)]` (or `#[repr(C)]` data-carrying enum when `intWidth` is the
  C enum width) (`r[layout.repr.c.enum.fields]`, `r[layout.repr.c-primitive]`).
  Guaranteed across all worlds to equal a 2-field `#[repr(C)]` struct `{ tag: Int, payload: union }`. -/
  | reprCIntTagged (signed : Bool) (intWidth : IntWidth)
  /-- Data-carrying `#[repr(Int)]` enum without `C` (`r[layout.repr.primitive.fields]`).
  Tag is at offset 0 with size `intWidth`, while variant payload layout varies with `adtPad id`. -/
  | reprIntTagged (signed : Bool) (intWidth : IntWidth)
  /-- `core::option::Option<innerTy>` (`r[layout.option-niche]`).
  When `innerTy` is in the Reference-guaranteed niche family $\mathcal{N}_{\text{Option}}$,
  `Option<innerTy>` has the exact size, alignment, and bit-level niche representation of `innerTy`
  across ALL `adtPad` worlds (`None` = `0`, `Some(v)` = `bits(v)`).
  When `innerTy` is NOT in $\mathcal{N}_{\text{Option}}$ (e.g., `Option<bool>`), `Option<innerTy>`
  falls back to `#[repr(Rust)]` enum layout (`size = size(innerTy) + s.adtPad id`). -/
  | optionNiche (innerTy : MirTy)
  deriving DecidableEq, Repr

/-- Unified ADT declaration covering both structs and enums. -/
inductive AdtKind where
  | structDecl (repr : StructRepr) (fields : List MirTy)
  | enumDecl (repr : EnumRepr) (variants : List VariantDecl)
  deriving DecidableEq, Repr

structure AdtDecl where
  id : AdtId
  name : String
  kind : AdtKind
  deriving DecidableEq, Repr

def findAdtDecl : List AdtDecl → AdtId → Option AdtDecl
  | [], _ => none
  | d :: rest, id => if d.id == id then some d else findAdtDecl rest id

/-- Round `offset` up to the next multiple of `align` (`align > 0`). -/
def alignUp (offset : Nat) (align : Nat) : Nat :=
  if align ≤ 1 then offset
  else
    let rem := offset % align
    if rem == 0 then offset else offset + (align - rem)

/-- Fold `#[repr(C)]` struct field layouts (`r[layout.repr.c.struct]`):
starts at `offset = 0`, `maxAlign = 1`; for each field `(fSz, fAl)`, aligns `offset` to `fAl`,
advances by `fSz`, and updates `maxAlign := Nat.max maxAlign fAl`. -/
def foldReprCFields : List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], offset, maxAlign => (alignUp offset maxAlign, maxAlign)
  | (fSz, fAl) :: rest, offset, maxAlign =>
    let alignedOff := alignUp offset fAl
    foldReprCFields rest (alignedOff + fSz) (Nat.max maxAlign fAl)

/-- Compute the byte offset of field `targetIdx` inside a `#[repr(C)]` field list. -/
def reprCFieldOffsetAux : List (Nat × Nat) → Nat → Nat → Option Nat
  | [], _, _ => none
  | (_, fAl) :: _, 0, offset => some (alignUp offset fAl)
  | (fSz, fAl) :: rest, idx + 1, offset =>
    let alignedOff := alignUp offset fAl
    reprCFieldOffsetAux rest idx (alignedOff + fSz)

/-- Check whether a type is a guaranteed 1-ZST (`size == 0` and `align == 1` across all worlds),
as required for sibling fields in `#[repr(transparent)]` wrappers (`r[layout.repr.transparent]`). -/
def isGuaranteedOneZst (adts : List AdtDecl) : Nat → MirTy → Bool
  | 0, _ => false
  | _ + 1, .unit => true
  | fuel + 1, .adt id =>
    match findAdtDecl adts id with
    | some ⟨_, _, .structDecl (.reprRust) []⟩ => true
    | some ⟨_, _, .structDecl (.reprC) []⟩ => false
    | some ⟨_, _, .structDecl (.reprTransparent _) fields⟩ =>
      fields.all (isGuaranteedOneZst adts fuel)
    | _ => false
  | _ + 1, _ => false

/-- Filter out guaranteed 1-ZST fields from a `#[repr(transparent)]` field list to find the
unique non-1-ZST payload field (or confirms all fields are 1-ZST). -/
def filterNonOneZstFields (adts : List AdtDecl) (fuel : Nat) : List MirTy → List MirTy
  | [] => []
  | f :: rest =>
    if isGuaranteedOneZst adts fuel f then
      filterNonOneZstFields adts fuel rest
    else
      f :: filterNonOneZstFields adts fuel rest

/-- **Closed Reference Niche Family $\mathcal{N}_{\text{Option}}$ (`r[layout.option-niche]`,
`library/core/src/option.rs:116-159`)**:
Returns `true` iff `ty` is normatively guaranteed by the Rust Reference across ALL
Reference-admissible compilers and worlds to enjoy the `Option<T>` null-pointer/non-zero
optimization (`size_of::<Option<T>>() == size_of::<T>()`, `align_of::<Option<T>>() == align_of::<T>()`,
and `None` represented as all-zero bits `0`):
1. `&U` and `&mut U` (`.ref _ _`),
2. `core::ptr::NonNull<U>` (`.nonNullPtr _`),
3. `[unsafe] [extern "ABI"] fn(...) -> Ret` (`.fnPtr`),
4. `core::num::NonZero<Int>` (`.nonZeroScalar _ _`), and
5. Any `#[repr(transparent)]` struct (excluding `UnsafeCell` / `UnsafePinned`, i.e.,
   `isNoNicheInteriorMutable = false`) wrapping a single non-1-ZST field in $\mathcal{N}_{\text{Option}}$
   alongside any number of guaranteed 1-ZST fields. -/
def optionNicheGuaranteed (adts : List AdtDecl) : Nat → MirTy → Bool
  | 0, _ => false
  | _ + 1, .ref _ _ => true
  | _ + 1, .nonNullPtr _ => true
  | _ + 1, .fnPtr => true
  | _ + 1, .nonZeroScalar _ _ => true
  | fuel + 1, .adt id =>
    match findAdtDecl adts id with
    | some ⟨_, _, .structDecl (.reprTransparent false) fields⟩ =>
      match filterNonOneZstFields adts fuel fields with
      | [singleField] => optionNicheGuaranteed adts fuel singleField
      | _ => false
    | _ => false
  | _ + 1, _ => false

/-- Map an `Option`-returning layout function across a list of types. -/
def mapOptionList {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, mapOptionList f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Compute `(maxPayloadSize, maxPayloadAlign)` across all variants of a `#[repr(C, Int)]` enum
using a given single-type layout function `stepField`. -/
def foldReprCVariantsUnion (stepField : MirTy → Option (Nat × Option Nat)) :
    List VariantDecl → Option (Nat × Nat)
  | [] => some (0, 1)
  | v :: rest =>
    match mapOptionList stepField v.fields, foldReprCVariantsUnion stepField rest with
    | some fLayouts, some (restSz, restAl) =>
      let concreteFields := fLayouts.filterMap (fun (sz, alOpt) =>
        match alOpt with
        | some al => some (sz, al)
        | none => none)
      if concreteFields.length == fLayouts.length then
        let (vSz, vAl) := foldReprCFields concreteFields 0 1
        some (Nat.max vSz restSz, Nat.max vAl restAl)
      else
        none
    | _, _ => none

/-- Forward-compatible type layout function `tyLayoutStep` (structurally recursive on `fuel : Nat`):
Returns `some (byteSize, alignOpt)` where `alignOpt = some align` when alignment is
Reference-determined across all worlds, and `alignOpt = none` when alignment is
compiler-varying (`#[repr(Rust)]` structs/enums). -/
def tyLayoutStep (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat) :
    Nat → MirTy → Option (Nat × Option Nat)
  | 0, _ => none
  | _ + 1, .bool => some (1, some 1)
  | _ + 1, .char => some (4, some 4)
  | _ + 1, .scalar _ w => some (w.byteSize t, some (w.alignBytes t))
  | _ + 1, .nonZeroScalar _ w => some (w.byteSize t, some (w.alignBytes t))
  | _ + 1, .ref _ _ => some (t.ptrByteWidth, some t.ptrAlignBytes)
  | _ + 1, .nonNullPtr _ => some (t.ptrByteWidth, some t.ptrAlignBytes)
  | _ + 1, .rawPtr _ => some (t.ptrByteWidth, some t.ptrAlignBytes)
  | _ + 1, .fnPtr => some (t.ptrByteWidth, some t.ptrAlignBytes)
  | _ + 1, .unit => some (0, some 1)
  | _ + 1, .never => some (0, some 1)
  | fuel + 1, .adt id =>
    let stepField := tyLayoutStep t adts adtPad fuel
    match findAdtDecl adts id with
    | none => none
    | some decl =>
      match decl.kind with
      | .structDecl .reprRust fields =>
        match mapOptionList stepField fields with
        | some fLayouts =>
          let sumSizes := fLayouts.foldl (fun acc (sz, _) => acc + sz) 0
          if sumSizes == 0 then
            some (0, if fields.isEmpty then some 1 else none)
          else
            some (sumSizes + adtPad id, none)
        | none => none
      | .structDecl .reprC fields =>
        match mapOptionList stepField fields with
        | some fLayouts =>
          let concreteFields := fLayouts.filterMap (fun (sz, alOpt) =>
            match alOpt with
            | some al => some (sz, al)
            | none => none)
          if concreteFields.length == fLayouts.length then
            let (cSz, cAl) := foldReprCFields concreteFields 0 1
            some (cSz, some cAl)
          else
            none
        | none => none
      | .structDecl (.reprTransparent _) fields =>
        match mapOptionList stepField fields with
        | some fLayouts =>
          let nonZst := fLayouts.filter (fun (sz, alOpt) => !(sz == 0 && alOpt == some 1))
          match nonZst with
          | [] => some (0, some 1)
          | [(sz, alOpt)] => some (sz, alOpt)
          | _ => none
        | none => none
      | .enumDecl (.reprRustEnum minSz _) variants =>
        if variants.isEmpty then
          some (0, some 1)
        else
          some (minSz + adtPad id, none)
      | .enumDecl (.reprIntFieldless _ intWidth) variants =>
        if variants.all (fun v => v.fields.isEmpty) then
          some (intWidth.byteSize t, some (intWidth.alignBytes t))
        else
          none
      | .enumDecl .reprCEnumFieldless variants =>
        if variants.all (fun v => v.fields.isEmpty) then
          some (t.cEnumByteWidth, some t.cEnumAlignBytes)
        else
          none
      | .enumDecl (.reprCIntTagged _ intWidth) variants =>
        match foldReprCVariantsUnion stepField variants with
        | some (unionSz, unionAl) =>
          let tagSz := intWidth.byteSize t
          let tagAl := intWidth.alignBytes t
          let (totalSz, totalAl) := foldReprCFields [(tagSz, tagAl), (unionSz, unionAl)] 0 1
          some (totalSz, some totalAl)
        | none => none
      | .enumDecl (.reprIntTagged _ intWidth) _ =>
        some (intWidth.byteSize t + adtPad id, none)
      | .enumDecl (.optionNiche innerTy) _ =>
        match stepField innerTy with
        | some (innerSz, innerAlOpt) =>
          if optionNicheGuaranteed adts fuel innerTy then
            some (innerSz, innerAlOpt)
          else
            some (innerSz + adtPad id, none)
        | none => none

def defaultLayoutFuel (adts : List AdtDecl) : Nat := adts.length + 4

def evalTyByteSize (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat)
    (ty : MirTy) : Option Nat :=
  match tyLayoutStep t adts adtPad (defaultLayoutFuel adts) ty with
  | some (sz, _) => some sz
  | none => none

def evalTyAlign (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat)
    (ty : MirTy) : Option Nat :=
  match tyLayoutStep t adts adtPad (defaultLayoutFuel adts) ty with
  | some (_, some al) => some al
  | _ => none

/-- Layout queries (`size_of::<T>()`, `align_of::<T>()`, `offset_of!(T, variant, field)`). -/
inductive LayoutQuery where
  | sizeOf (ty : MirTy)
  | alignOf (ty : MirTy)
  | offsetOf (ty : MirTy) (variantIdx : Nat) (fieldIdx : Nat)
  deriving DecidableEq, Repr

/-- Evaluate a `LayoutQuery` in state `s : State`:
- For `#[repr(C)]` structs, `offsetOf (.adt id) 0 fieldIdx` is Reference-determined across
  all worlds (provided earlier fields have Reference-determined sizes and alignments).
- For `#[repr(C, Int)]` enums (`reprCIntTagged`), `offsetOf (.adt id) 0 0` (the tag) is `0`,
  and `offsetOf (.adt id) 0 1` (the payload union, where every variant's first field starts!)
  is `alignUp tagSz payloadUnionAlign`.
- For `#[repr(Rust)]` structs, `offsetOf (.adt id) 0 fieldIdx` queries the world's opaque
  `s.adtFieldOffset id fieldIdx` (which is `none` or varies across worlds unless constrained
  by a compile-time `const { assert!(offset_of!(S, f) == K) }` guard). -/
def evalLayoutQuery (t : TargetLayout) (adts : List AdtDecl) (s : State) :
    LayoutQuery → Option Nat
  | .sizeOf ty => evalTyByteSize t adts s.adtPad ty
  | .alignOf ty => evalTyAlign t adts s.adtPad ty
  | .offsetOf (.adt id) variantIdx fieldIdx =>
    let stepField := tyLayoutStep t adts s.adtPad (defaultLayoutFuel adts)
    match findAdtDecl adts id with
    | some ⟨_, _, .structDecl .reprC fields⟩ =>
      if variantIdx == 0 then
        match mapOptionList stepField fields with
        | some fLayouts =>
          let concreteFields := fLayouts.filterMap (fun (sz, alOpt) =>
            match alOpt with
            | some al => some (sz, al)
            | none => none)
          if concreteFields.length == fLayouts.length then
            reprCFieldOffsetAux concreteFields fieldIdx 0
          else
            none
        | none => none
      else
        none
    | some ⟨_, _, .structDecl .reprRust fields⟩ =>
      if variantIdx == 0 && fieldIdx < fields.length then
        s.adtFieldOffset id fieldIdx
      else
        none
    | some ⟨_, _, .enumDecl (.reprCIntTagged _ intWidth) variants⟩ =>
      match foldReprCVariantsUnion stepField variants with
      | some (_, unionAl) =>
        if variantIdx == 0 && fieldIdx == 0 then
          some 0
        else if variantIdx == 0 && fieldIdx == 1 then
          some (alignUp (intWidth.byteSize t) unionAl)
        else
          none
      | none => none
    | _ => none
  | .offsetOf _ _ _ => none

/-! ## Part 3: Forward-Compatible Transmute Semantics (`evalTransmuteVal`) for Enums & `Option<T>` -/

/-- Extract the Reference-guaranteed bit pattern `(bits, sizeBytes)` of a runtime value `v`
at source type `srcTy`. -/
def extractTransmuteBits (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat) :
    Nat → MirTy → MirVal → Option (Nat × Nat)
  | 0, _, _ => none
  | _ + 1, .scalar _ w, .int bits sz =>
    if sz == w.byteSize t then some (bits, sz) else none
  | _ + 1, .nonZeroScalar _ w, .nonZeroInt bits sz =>
    if sz == w.byteSize t && bits != 0 then some (bits, sz) else none
  | _ + 1, .bool, .int bits 1 =>
    if bits ≤ 1 then some (bits, 1) else none
  | fuel + 1, .adt id, v =>
    match findAdtDecl adts id with
    | none => none
    | some decl =>
      match decl.kind, v with
      | .structDecl (.reprTransparent _) fields, .adt id' (.fieldCons innerVal .fieldNil) =>
        if id == id' then
          match filterNonOneZstFields adts fuel fields with
          | [singleTy] => extractTransmuteBits t adts adtPad fuel singleTy innerVal
          | _ => none
        else
          none
      | .enumDecl (.reprIntFieldless _ intWidth) variants, .enumAdt id' vIdx .fieldNil =>
        if id == id' then
          match variants[vIdx]? with
          | some vDecl =>
            if vDecl.fields.isEmpty then
              some (vDecl.discriminant, intWidth.byteSize t)
            else
              none
          | none => none
        else
          none
      | .enumDecl .reprCEnumFieldless variants, .enumAdt id' vIdx .fieldNil =>
        if id == id' then
          match variants[vIdx]? with
          | some vDecl =>
            if vDecl.fields.isEmpty then
              some (vDecl.discriminant, t.cEnumByteWidth)
            else
              none
          | none => none
        else
          none
      | .enumDecl (.optionNiche innerTy) _, .enumAdt id' vIdx payloadFields =>
        if id == id' && optionNicheGuaranteed adts fuel innerTy then
          match tyLayoutStep t adts adtPad fuel innerTy with
          | some (innerSz, _) =>
            match vIdx, payloadFields with
            | 0, .fieldNil =>
              some (0, innerSz)
            | 1, .fieldCons payloadVal .fieldNil =>
              match extractTransmuteBits t adts adtPad fuel innerTy payloadVal with
              | some (bits, sz) =>
                if sz == innerSz && bits != 0 then some (bits, sz) else none
              | none => none
            | _, _ => none
          | none => none
        else
          none
      | _, _ => none
  | _ + 1, _, _ => none

/-- Find the index of a fieldless enum variant whose declared `discriminant` equals `bits`. -/
def findVariantByDiscriminant : List VariantDecl → Nat → Option Nat
  | [], _ => none
  | v :: rest, bits =>
    if v.discriminant == bits && v.fields.isEmpty then
      some 0
    else
      match findVariantByDiscriminant rest bits with
      | some idx => some (idx + 1)
      | none => none

/-- Construct a runtime value of destination type `dstTy` from raw transmuted `(bits, sizeBytes)`. -/
def constructTransmuteVal (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat) :
    Nat → MirTy → Nat → Nat → Option MirVal
  | 0, _, _, _ => none
  | _ + 1, .scalar _ w, bits, sz =>
    if sz == w.byteSize t then some (.int bits sz) else none
  | _ + 1, .nonZeroScalar _ w, bits, sz =>
    if sz == w.byteSize t && bits != 0 then some (.nonZeroInt bits sz) else none
  | _ + 1, .bool, bits, 1 =>
    if bits ≤ 1 then some (.int bits 1) else none
  | fuel + 1, .adt id, bits, sz =>
    match findAdtDecl adts id with
    | none => none
    | some decl =>
      match decl.kind with
      | .structDecl (.reprTransparent _) fields =>
        match filterNonOneZstFields adts fuel fields with
        | [singleTy] =>
          match constructTransmuteVal t adts adtPad fuel singleTy bits sz with
          | some innerVal => some (.adt id (.fieldCons innerVal .fieldNil))
          | none => none
        | _ => none
      | .enumDecl (.reprIntFieldless _ intWidth) variants =>
        if sz == intWidth.byteSize t then
          match findVariantByDiscriminant variants bits with
          | some vIdx => some (.enumAdt id vIdx .fieldNil)
          | none => none
        else
          none
      | .enumDecl .reprCEnumFieldless variants =>
        if sz == t.cEnumByteWidth then
          match findVariantByDiscriminant variants bits with
          | some vIdx => some (.enumAdt id vIdx .fieldNil)
          | none => none
        else
          none
      | .enumDecl (.optionNiche innerTy) _ =>
        if optionNicheGuaranteed adts fuel innerTy then
          match tyLayoutStep t adts adtPad fuel innerTy with
          | some (innerSz, _) =>
            if sz == innerSz then
              if bits == 0 then
                some (.enumAdt id 0 .fieldNil)
              else
                match constructTransmuteVal t adts adtPad fuel innerTy bits sz with
                | some innerVal => some (.enumAdt id 1 (.fieldCons innerVal .fieldNil))
                | none => none
            else
              none
          | none => none
        else
          none
      | _ => none
  | _ + 1, _, _, _ => none

/-- Forward-compatible `Rvalue.transmute` evaluator (`evalTransmuteVal`). -/
def evalTransmuteVal (t : TargetLayout) (adts : List AdtDecl) (adtPad : AdtId → Nat)
    (srcTy dstTy : MirTy) (srcVal : MirVal) : Option MirVal :=
  let fuel := defaultLayoutFuel adts
  match evalTyByteSize t adts adtPad srcTy, evalTyByteSize t adts adtPad dstTy with
  | some srcSz, some dstSz =>
    if srcSz == dstSz then
      match extractTransmuteBits t adts adtPad fuel srcTy srcVal with
      | some (bits, bitsSz) =>
        if bitsSz == dstSz then
          constructTransmuteVal t adts adtPad fuel dstTy bits bitsSz
        else
          none
      | none => none
    else
      none
  | _, _ => none

/-! ## Part 4: Concrete Benchmark Declarations and Flagship Verification Theorems -/

def optNonZeroU32Id : AdtId := 0
def myReprU8EnumId : AdtId := 1
def optBoolId : AdtId := 2
def rustPairId : AdtId := 3
def reprCPairId : AdtId := 4
def transparentNonZeroU32Id : AdtId := 5
def optTransparentNonZeroU32Id : AdtId := 6
def reprCU8EnumId : AdtId := 7

def u8Ty : MirTy := .scalar false .bits8
def u32Ty : MirTy := .scalar false .bits32
def u64Ty : MirTy := .scalar false .bits64
def nonZeroU32Ty : MirTy := .nonZeroScalar false .bits32

def testAdts : List AdtDecl :=
  [ { id := optNonZeroU32Id
      name := "Option<NonZeroU32>"
      kind := .enumDecl (.optionNiche nonZeroU32Ty)
        [ { name := "None", discriminant := 0, fields := [] }
        , { name := "Some", discriminant := 1, fields := [nonZeroU32Ty] } ] }
  , { id := myReprU8EnumId
      name := "MyReprU8FieldlessEnum"
      kind := .enumDecl (.reprIntFieldless false .bits8)
        [ { name := "Off", discriminant := 0, fields := [] }
        , { name := "On", discriminant := 1, fields := [] }
        , { name := "Auto", discriminant := 2, fields := [] } ] }
  , { id := optBoolId
      name := "Option<bool>"
      kind := .enumDecl (.optionNiche .bool)
        [ { name := "None", discriminant := 0, fields := [] }
        , { name := "Some", discriminant := 1, fields := [.bool] } ] }
  , { id := rustPairId
      name := "RustPair"
      kind := .structDecl .reprRust [u32Ty, u32Ty] }
  , { id := reprCPairId
      name := "ReprCPair"
      kind := .structDecl .reprC [u32Ty, u32Ty] }
  , { id := transparentNonZeroU32Id
      name := "TransparentNonZeroU32"
      kind := .structDecl (.reprTransparent false) [nonZeroU32Ty] }
  , { id := optTransparentNonZeroU32Id
      name := "Option<TransparentNonZeroU32>"
      kind := .enumDecl (.optionNiche (.adt transparentNonZeroU32Id))
        [ { name := "None", discriminant := 0, fields := [] }
        , { name := "Some", discriminant := 1, fields := [.adt transparentNonZeroU32Id] } ] }
  , { id := reprCU8EnumId
      name := "ReprCU8Enum"
      kind := .enumDecl (.reprCIntTagged false .bits8)
        [ { name := "A", discriminant := 0, fields := [u8Ty] }
        , { name := "B", discriminant := 1, fields := [u64Ty] } ] }
  ]

/-! ### Flagship Theorem 1: `transmute::<Option<NonZeroU32>, u32>` is Verified Unconditionally Across All `adtPad` Worlds -/

/-- Across all `adtPad` worlds, `Option<NonZeroU32>` has exact size 4 and alignment 4. -/
theorem option_nonZeroU32_layout_all_worlds (adtPad : AdtId → Nat) :
    evalTyByteSize defaultTarget64 testAdts adtPad (.adt optNonZeroU32Id) = some 4 ∧
    evalTyAlign defaultTarget64 testAdts adtPad (.adt optNonZeroU32Id) = some 4 := by
  exact ⟨rfl, rfl⟩

/-- **Flagship Theorem 1a (`None` case)**:
`transmute::<Option<NonZeroU32>, u32>(None)` evaluates to `some (.int 0 4)` in **every**
`adtPad` world without any `const` size assertion. -/
theorem transmute_option_nonZeroU32_none_to_u32_verified_all_worlds (adtPad : AdtId → Nat) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt optNonZeroU32Id) u32Ty (.enumAdt optNonZeroU32Id 0 .fieldNil) =
      some (.int 0 4) := by
  rfl

/-- **Flagship Theorem 1b (`Some(x)` case)**:
For any non-zero 32-bit integer `bits != 0`, `transmute::<Option<NonZeroU32>, u32>(Some(x))`
evaluates to `some (.int bits 4)` in **every** `adtPad` world without any `const` assertion. -/
theorem transmute_option_nonZeroU32_some_to_u32_verified_all_worlds
    (adtPad : AdtId → Nat) (bits : Nat) (hNonZero : (bits != 0) = true) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt optNonZeroU32Id) u32Ty
      (.enumAdt optNonZeroU32Id 1 (.fieldCons (.nonZeroInt bits 4) .fieldNil)) =
      some (.int bits 4) := by
  cases bits with
  | zero => contradiction
  | succ n => rfl

/-- **Flagship Theorem 1c (Inverse `u32 -> Option<NonZeroU32>`)**:
`transmute::<u32, Option<NonZeroU32>>(0)` yields `None`, and for `bits != 0` yields `Some(bits)`
across all `adtPad` worlds. -/
theorem transmute_u32_to_option_nonZeroU32_verified_all_worlds
    (adtPad : AdtId → Nat) (bits : Nat) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      u32Ty (.adt optNonZeroU32Id) (.int bits 4) =
      if bits == 0 then
        some (.enumAdt optNonZeroU32Id 0 .fieldNil)
      else
        some (.enumAdt optNonZeroU32Id 1 (.fieldCons (.nonZeroInt bits 4) .fieldNil)) := by
  change (if (bits == 0) = true then
            some (MirVal.enumAdt optNonZeroU32Id 0 MirVal.fieldNil)
          else
            match (if (true && (bits != 0)) = true then some (MirVal.nonZeroInt bits 4) else none) with
            | some innerVal =>
              some (MirVal.enumAdt optNonZeroU32Id 1 (MirVal.fieldCons innerVal MirVal.fieldNil))
            | none => none) = _
  cases hZero : bits == 0
  · have hNe : (bits != 0) = true := by
      simp [bne, hZero]
    rw [hNe]
    rfl
  · rfl

/-- **Flagship Theorem 1d (`#[repr(transparent)]` Niche Propagation)**:
`Option<TransparentNonZeroU32>` also satisfies `optionNicheGuaranteed` (`r[layout.option-niche]`)
and transmutes to `u32` unconditionally across all `adtPad` worlds! -/
theorem transmute_option_transparent_nonZeroU32_some_to_u32_verified_all_worlds
    (adtPad : AdtId → Nat) (bits : Nat) (hNonZero : (bits != 0) = true) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt optTransparentNonZeroU32Id) u32Ty
      (.enumAdt optTransparentNonZeroU32Id 1
        (.fieldCons (.adt transparentNonZeroU32Id (.fieldCons (.nonZeroInt bits 4) .fieldNil)) .fieldNil)) =
      some (.int bits 4) := by
  cases bits with
  | zero => contradiction
  | succ n => rfl

/-! ### Flagship Theorem 2: `transmute::<MyReprU8FieldlessEnum, u8>` is Verified Unconditionally Across All `adtPad` Worlds -/

/-- Across all `adtPad` worlds, `MyReprU8FieldlessEnum` has exact size 1 and alignment 1. -/
theorem reprU8_fieldless_enum_layout_all_worlds (adtPad : AdtId → Nat) :
    evalTyByteSize defaultTarget64 testAdts adtPad (.adt myReprU8EnumId) = some 1 ∧
    evalTyAlign defaultTarget64 testAdts adtPad (.adt myReprU8EnumId) = some 1 := by
  exact ⟨rfl, rfl⟩

/-- **Flagship Theorem 2a (Enum -> `u8` for all declared variants)**:
For every valid variant index `vIdx ∈ {0, 1, 2}` of `MyReprU8FieldlessEnum`,
`transmute::<MyReprU8FieldlessEnum, u8>` succeeds unconditionally across all `adtPad` worlds
and produces the variant's declared discriminant. -/
theorem transmute_reprU8_fieldless_enum_to_u8_verified_all_worlds (adtPad : AdtId → Nat) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt myReprU8EnumId) u8Ty (.enumAdt myReprU8EnumId 0 .fieldNil) = some (.int 0 1) ∧
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt myReprU8EnumId) u8Ty (.enumAdt myReprU8EnumId 1 .fieldNil) = some (.int 1 1) ∧
    evalTransmuteVal defaultTarget64 testAdts adtPad
      (.adt myReprU8EnumId) u8Ty (.enumAdt myReprU8EnumId 2 .fieldNil) = some (.int 2 1) := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Flagship Theorem 2b (Inverse `u8 -> MyReprU8FieldlessEnum` validity boundary)**:
Transmuting `u8` to `MyReprU8FieldlessEnum` succeeds across all `adtPad` worlds when the
discriminant is in `{0, 1, 2}`, and fails closed (`none`, rejecting UB under `r[undefined.invalid]`)
when the byte is an invalid discriminant such as `3`. -/
theorem transmute_u8_to_reprU8_fieldless_enum_discriminant_check (adtPad : AdtId → Nat) :
    evalTransmuteVal defaultTarget64 testAdts adtPad
      u8Ty (.adt myReprU8EnumId) (.int 2 1) = some (.enumAdt myReprU8EnumId 2 .fieldNil) ∧
    evalTransmuteVal defaultTarget64 testAdts adtPad
      u8Ty (.adt myReprU8EnumId) (.int 3 1) = none := by
  exact ⟨rfl, rfl⟩

/-! ### Flagship Theorem 3: `transmute::<Option<bool>, u8>` is Rejected in Unguarded Forward-Compatible Mode -/

/-- `Option<bool>` is NOT in the Reference-guaranteed niche family $\mathcal{N}_{\text{Option}}$. -/
theorem option_bool_not_niche_guaranteed :
    optionNicheGuaranteed testAdts (defaultLayoutFuel testAdts) .bool = false := by
  rfl

/-- While `Option<bool>` has size 1 in the `adtPad = 0` world (matching `rustc`'s opportunistic
niche optimization), its size in a general Reference-admissible world is `1 + adtPad optBoolId`
(so at `adtPad optBoolId = 1`, `size_of::<Option<bool>>() = 2`). -/
theorem option_bool_size_varies_across_worlds (adtPad : AdtId → Nat) :
    evalTyByteSize defaultTarget64 testAdts adtPad (.adt optBoolId) =
      some (1 + adtPad optBoolId) := by
  rfl

/-- Helper lemma: `extractTransmuteBits` always rejects `Option<bool>` (`optBoolId`) because
`optionNicheGuaranteed` is `false` for `.bool`. -/
theorem extractTransmuteBits_optBool_none (adtPad : AdtId → Nat) (v : MirVal) :
    extractTransmuteBits defaultTarget64 testAdts adtPad
      (defaultLayoutFuel testAdts) (.adt optBoolId) v = none := by
  cases v with
  | enumAdt id' vIdx payloadFields =>
    change (if (2 == id' && false) = true then _ else none) = none
    rw [Bool.and_false]
    rfl
  | _ => rfl

/-- **Flagship Theorem 3 (`transmute::<Option<bool>, u8>` rejected)**:
1. In any world where `adtPad optBoolId > 0` (such as `adtPad optBoolId = 1`), the size of
   `Option<bool>` (`1 + adtPad optBoolId`) does not even match `size_of::<u8>() == 1`.
2. Even when `adtPad optBoolId = 0`, `evalTransmuteVal` rejects `transmute::<Option<bool>, u8>`
   (`= none`) because `Option<bool>`'s discriminant/niche bit encoding is not guaranteed by
   `r[layout.option-niche]`. -/
theorem transmute_option_bool_to_u8_rejected_forward_compatible
    (adtPad : AdtId → Nat) (v : MirVal) :
    evalTransmuteVal defaultTarget64 testAdts adtPad (.adt optBoolId) u8Ty v = none := by
  unfold evalTransmuteVal
  have hSrc : evalTyByteSize defaultTarget64 testAdts adtPad (.adt optBoolId) =
      some (1 + adtPad optBoolId) := rfl
  have hDst : evalTyByteSize defaultTarget64 testAdts adtPad u8Ty = some 1 := rfl
  rw [hSrc, hDst]
  dsimp only
  rw [extractTransmuteBits_optBool_none]
  cases (1 + adtPad optBoolId == 1) <;> rfl

/-! ### Flagship Theorem 4: Multi-Field `&s.field_1` and `&mut s.field_1` Step Cleanly Across All `adtPad` Worlds -/

/-- Initial state holding a local `_0 : RustPair = RustPair { a: 10, b: 20 }` parameterized by
arbitrary world functions `adtPad` and `adtFieldOffset`. -/
def mkRustPairState (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) : State :=
  { frameId := 0
    locals :=
      [ { gen := 1
          allocated := true
          val := .adt rustPairId (.fieldCons (.int 10 4) (.fieldCons (.int 20 4) .fieldNil)) } ]
    adtPad := adtPad
    adtFieldOffset := adtFieldOffset }

/-- State after mutating `*(&mut pair.1) = 99` on `mkRustPairState`. -/
def mkRustPairMutatedState (adtPad : AdtId → Nat)
    (adtFieldOffset : AdtId → Nat → Option Nat) : State :=
  { frameId := 0
    locals :=
      [ { gen := 1
          allocated := true
          val := .adt rustPairId (.fieldCons (.int 10 4) (.fieldCons (.int 99 4) .fieldNil)) } ]
    adtPad := adtPad
    adtFieldOffset := adtFieldOffset }

/-- **Flagship Theorem 4 (`borrow_and_mutate_multi_field_1_verified_all_worlds`)**:
For `RustPair { a: 10, b: 20 }` in local `_0`, across **all** `adtPad` and `adtFieldOffset` worlds:
1. Borrowing the second field `&pair.1` (`PlaceElem.field 1`) succeeds and produces the
   path-indexed reference `MirVal.ref 0 1 0 0 [1]`.
2. Reading through `&pair.1` resolves to `some (.int 20 4)`.
3. Mutating `*(&mut pair.1) = 99` via `mutateRefPath` succeeds and produces `s'`.
4. Reading `&pair.1` in `s'` yields the updated value `some (.int 99 4)`, while reading
   the sibling field `&pair.0` in `s'` still yields the original `some (.int 10 4)`! -/
theorem borrow_and_mutate_multi_field_1_verified_all_worlds
    (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) :
    let s := mkRustPairState adtPad adtFieldOffset
    let rootVal := .adt rustPairId (.fieldCons (.int 10 4) (.fieldCons (.int 20 4) .fieldNil))
    evalRefProjPath s 0 1 0 0 [] [.field 1] rootVal = some (.ref 0 1 0 0 [1]) ∧
    resolveRefPath s 0 1 0 0 [1] = some (.int 20 4) ∧
    ∃ s',
      mutateRefPath s 0 1 0 0 [1] (.int 99 4) = some s' ∧
      resolveRefPath s' 0 1 0 0 [1] = some (.int 99 4) ∧
      resolveRefPath s' 0 1 0 0 [0] = some (.int 10 4) := by
  exact ⟨rfl, rfl, mkRustPairMutatedState adtPad adtFieldOffset, rfl, rfl, rfl⟩

/-! ### Flagship Theorem 5: Decoupling `&s.field_1` from `offset_of!(S, field_1)` and `#[repr(C, u8)]` Layout -/

/-- **Theorem 5a (`offset_of!` on `#[repr(C)]` vs. `#[repr(Rust)]` structs)**:
- For `ReprCPair` (`#[repr(C)] struct ReprCPair { a: u32, b: u32 }`), `offset_of!(ReprCPair, 1)`
  evaluates deterministically to `some 4` in **every** `(adtPad, adtFieldOffset)` world.
- For `RustPair` (`#[repr(Rust)] struct RustPair { a: u32, b: u32 }`), `offset_of!(RustPair, 1)`
  evaluates to `adtFieldOffset rustPairId 1` (which is `none` in an unguarded world, or `some K`
  only in worlds constrained by `const { assert!(offset_of!(RustPair, b) == K) }`), even though
  borrowing `&rust_pair.1` succeeds unconditionally in all worlds (Theorem 4). -/
theorem offsetOf_reprC_deterministic_vs_reprRust_world_varying
    (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) :
    let s := mkRustPairState adtPad adtFieldOffset
    evalLayoutQuery defaultTarget64 testAdts s (.offsetOf (.adt reprCPairId) 0 1) = some 4 ∧
    evalLayoutQuery defaultTarget64 testAdts s (.offsetOf (.adt rustPairId) 0 1) =
      adtFieldOffset rustPairId 1 := by
  exact ⟨rfl, rfl⟩

/-- **Theorem 5b (`#[repr(C, u8)]` data-carrying enum layout across all `adtPad` worlds)**:
For `#[repr(C, u8)] enum ReprCU8Enum { A(u8), B(u64) }` (`r[layout.repr.c.enum.fields]`,
`r[layout.repr.c-primitive]`):
- Total byte size is deterministically `16` across all `adtPad` worlds,
- Alignment is deterministically `8` across all `adtPad` worlds,
- Tag offset (`field 0`) is `0`, and payload union offset (`field 1`, where BOTH `A.0` and `B.0`
  begin!) is `8` across all `adtPad` worlds. -/
theorem reprCIntTagged_enum_layout_deterministic_all_worlds
    (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) :
    let s := mkRustPairState adtPad adtFieldOffset
    evalTyByteSize defaultTarget64 testAdts adtPad (.adt reprCU8EnumId) = some 16 ∧
    evalTyAlign defaultTarget64 testAdts adtPad (.adt reprCU8EnumId) = some 8 ∧
    evalLayoutQuery defaultTarget64 testAdts s (.offsetOf (.adt reprCU8EnumId) 0 0) = some 0 ∧
    evalLayoutQuery defaultTarget64 testAdts s (.offsetOf (.adt reprCU8EnumId) 0 1) = some 8 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem 5c (Nested Reborrow `&mut (*r).1` at Path `[1, 1]` Across All Worlds)**:
When `_0` holds a nested struct `Outer { left: RustPair(1, 2), right: RustPair(3, 4) }` and
`r = &mut _0.1` (`MirVal.ref 0 1 0 0 [1]`), reborrowing `&mut (*r).1` via
`evalRefProjPath ... [.deref, .field 1]` produces `MirVal.ref 0 1 0 0 [1, 1]`, and mutating
`*(&mut (*r).1) = 77` updates `_0.1.1` to `77` while preserving `_0.1.0 = 3` and `_0.0 = RustPair(1, 2)`
across all `adtPad` and `adtFieldOffset` worlds. -/
def outerPairId : AdtId := 8

def mkOuterPairState (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) : State :=
  let leftPair := MirVal.adt rustPairId (.fieldCons (.int 1 4) (.fieldCons (.int 2 4) .fieldNil))
  let rightPair := MirVal.adt rustPairId (.fieldCons (.int 3 4) (.fieldCons (.int 4 4) .fieldNil))
  { frameId := 0
    locals :=
      [ { gen := 1
          allocated := true
          val := .adt outerPairId (.fieldCons leftPair (.fieldCons rightPair .fieldNil)) } ]
    adtPad := adtPad
    adtFieldOffset := adtFieldOffset }

def mkOuterPairMutatedState (adtPad : AdtId → Nat)
    (adtFieldOffset : AdtId → Nat → Option Nat) : State :=
  let leftPair := MirVal.adt rustPairId (.fieldCons (.int 1 4) (.fieldCons (.int 2 4) .fieldNil))
  let rightPair' := MirVal.adt rustPairId (.fieldCons (.int 3 4) (.fieldCons (.int 77 4) .fieldNil))
  { frameId := 0
    locals :=
      [ { gen := 1
          allocated := true
          val := .adt outerPairId (.fieldCons leftPair (.fieldCons rightPair' .fieldNil)) } ]
    adtPad := adtPad
    adtFieldOffset := adtFieldOffset }

theorem nested_reborrow_and_mutate_path_1_1_verified_all_worlds
    (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat) :
    let s := mkOuterPairState adtPad adtFieldOffset
    let rRight := MirVal.ref 0 1 0 0 [1]
    evalRefProjPath s 0 1 0 0 [] [.deref, .field 1] rRight = some (.ref 0 1 0 0 [1, 1]) ∧
    resolveRefPath s 0 1 0 0 [1, 1] = some (.int 4 4) ∧
    ∃ s',
      mutateRefPath s 0 1 0 0 [1, 1] (.int 77 4) = some s' ∧
      resolveRefPath s' 0 1 0 0 [1, 1] = some (.int 77 4) ∧
      resolveRefPath s' 0 1 0 0 [1, 0] = some (.int 3 4) ∧
      resolveRefPath s' 0 1 0 0 [0, 1] = some (.int 2 4) := by
  exact ⟨rfl, rfl, mkOuterPairMutatedState adtPad adtFieldOffset, rfl, rfl, rfl, rfl⟩

/-- **Theorem 5d (Compile-Time `const` Guard Pins `offset_of!` on `#[repr(Rust)]` Structs)**:
In any world `(adtPad, adtFieldOffset)` that survives the compile-time assertion
`const { assert!(offset_of!(RustPair, 1) == 4) }` (`evalLayoutQuery ... = some 4`),
the world parameter `adtFieldOffset rustPairId 1` is pinned to `some 4`. -/
theorem const_guarded_offsetOf_reprRust_pins_world
    (adtPad : AdtId → Nat) (adtFieldOffset : AdtId → Nat → Option Nat)
    (hGuard : evalLayoutQuery defaultTarget64 testAdts (mkRustPairState adtPad adtFieldOffset)
                (.offsetOf (.adt rustPairId) 0 1) = some 4) :
    adtFieldOffset rustPairId 1 = some 4 := by
  exact hGuard

end EnumNichesAndBorrowPaths

#print axioms EnumNichesAndBorrowPaths.peelPath_writePath_same
#print axioms EnumNichesAndBorrowPaths.peelPath_writePath_disjoint
#print axioms EnumNichesAndBorrowPaths.resolveRefPath_mutateRefPath_same
#print axioms EnumNichesAndBorrowPaths.resolveRefPath_mutateRefPath_disjoint
#print axioms EnumNichesAndBorrowPaths.transmute_option_nonZeroU32_none_to_u32_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.transmute_option_nonZeroU32_some_to_u32_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.transmute_u32_to_option_nonZeroU32_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.transmute_option_transparent_nonZeroU32_some_to_u32_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.transmute_reprU8_fieldless_enum_to_u8_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.transmute_u8_to_reprU8_fieldless_enum_discriminant_check
#print axioms EnumNichesAndBorrowPaths.transmute_option_bool_to_u8_rejected_forward_compatible
#print axioms EnumNichesAndBorrowPaths.borrow_and_mutate_multi_field_1_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.offsetOf_reprC_deterministic_vs_reprRust_world_varying
#print axioms EnumNichesAndBorrowPaths.reprCIntTagged_enum_layout_deterministic_all_worlds
#print axioms EnumNichesAndBorrowPaths.nested_reborrow_and_mutate_path_1_1_verified_all_worlds
#print axioms EnumNichesAndBorrowPaths.const_guarded_offsetOf_reprRust_pins_world
