-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Standalone Lean 4.34.1 Mechanization Probe for Cluster D2 (Question 6)

Unifying Byte-Addressed Memory (`Option UInt8` + `BytePerm` + Spatial Provenance)
with Multi-Field Padded Structs (`AdtDecl`), Polymorphic Types (`X86Ty.param`),
and Generalized `AdmissibleLibInv`.

This standalone `prelude`-only file mechanizes:
1. `Trusted.Refinement` and `Trusted.StepResult` (exact copies of the Phase 1–2
   TCB foundations).
2. Slot/allocation-indexed byte memory (`AllocBlock` with `BytePerm`, `size : Nat`,
   `bytes : List (Option UInt8)`, `ptr : Option Ptr`, and `written : Bool`) and
   spatial provenance pointers (`Ptr (alloc : AllocId) (offset : Nat)`).
3. Multi-field padded struct declarations (`FieldDecl` with `offset`, `size`,
   `ty`, `access`, and `AdtDecl` with `id`, `size`, `fields`, `nonExhaustive`),
   byte-level type validity (`hasTy`), and generalized `AdmissibleLibInv`.
4. Byte-slice extraction (`extractSlice`), byte-slice update (`writeSlice`),
   little-endian scalar encoding/decoding (`encodeLeBytes`, `decodeLeBytes`),
   sub-field `movSlice`, byte-level `alu`, pointer arithmetic (`leaSlot`,
   `addPtrOffset`, `loadPtr`, `storePtr`), and unified `rep movsb` (`evalRepMovsb`).
5. Machine-checked proofs of all four Cluster D2 target theorems and negative
   adequacy canaries with zero `sorry` and zero custom axioms.
-/

namespace ByteMemoryProvenanceProbe

/-!
## 1. Refinement Preorder and Small-Step Prefix Semantics (`Trusted` Foundations)
-/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  ByteMemoryProvenanceProbe.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

class TrustedAssumption (A : Type) where
  meaning : A → Prop

structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

def VerificationResultOn
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

/-!
## 2. Unified Byte-Addressed Memory (`Option UInt8` + `BytePerm` + Provenance)
-/

/-- Stack-frame slot / memory allocation identifier. -/
structure SlotId where
  index : Nat

/-- Basic-block label identifier (`.Lbb<index>`). -/
structure BlockLabel where
  index : Nat

/-- Ghost memory permission on an allocation block (`AllocBlock`), catching
    unallocated/dead-storage (`StorageDead`), caller-frame, and read-only
    violations as immediate `.failed .ub`. -/
inductive BytePerm where
  | unallocated
  | callerFrame
  | readOnly
  | readWrite

def BytePerm.canRead : BytePerm → Bool
  | .readOnly | .readWrite => true
  | .unallocated | .callerFrame => false

def BytePerm.canWrite : BytePerm → Bool
  | .readWrite => true
  | .unallocated | .callerFrame | .readOnly => false

/-- Provenance-carrying pointer pairing an allocation identifier (`alloc`) with
    a byte offset (`offset`) relative to that allocation's base address.

    Pointer arithmetic (`Ptr.addOffset`) modifies `offset` while keeping `alloc`
    fixed, so stepping past `size` of `alloc` can never forge access to an
    adjacent stack slot. -/
structure Ptr where
  alloc : SlotId
  offset : Nat

def Ptr.addOffset (p : Ptr) (delta : Nat) : Ptr :=
  { p with offset := p.offset + delta }

/-- A byte sequence where each byte is either initialized (`some b`) or
    uninitialized / padding (`none`). -/
abbrev ByteVec := List (Option UInt8)

/-- Isolated byte-addressed allocation block for a stack slot. -/
structure AllocBlock where
  perm : BytePerm := .unallocated
  size : Nat := 0
  bytes : ByteVec := []
  ptr : Option Ptr := none
  written : Bool := false

/-- Unallocated block default. -/
def unallocBlock : AllocBlock :=
  { perm := .unallocated, size := 0, bytes := [], ptr := none, written := false }

/-- Replicate a byte value `n` times. -/
def replicateBytes (n : Nat) (v : Option UInt8) : ByteVec :=
  match n with
  | 0 => []
  | k + 1 => v :: replicateBytes k v

/-- Drop the first `n` elements of a list.
    Matches on `n` first so `dropBytes 0 xs` reduces to `xs` by `rfl` even for
    symbolic `xs`. -/
def dropBytes (n : Nat) (xs : List α) : List α :=
  match n with
  | 0 => xs
  | k + 1 =>
    match xs with
    | [] => []
    | _ :: rest => dropBytes k rest

/-- Take the first `n` elements of a list.
    Matches on `n` first so `takeBytes 0 xs` reduces to `[]` by `rfl` even for
    symbolic `xs`. -/
def takeBytes (n : Nat) (xs : List α) : List α :=
  match n with
  | 0 => []
  | k + 1 =>
    match xs with
    | [] => []
    | x :: rest => x :: takeBytes k rest

/-- Extract a contiguous slice of `len` elements starting at `offset`. -/
def extractSlice (xs : List α) (offset len : Nat) : List α :=
  takeBytes len (dropBytes offset xs)

/-- Overwrite a contiguous slice starting at `offset` with `patch`.
    Recurses structurally on `offset : Nat` (`Nat.rec`) so `writeSlice xs 0 patch`
    reduces definitionally (`rfl`) to `patch ++ dropBytes patch.length xs` even
    when `xs` is a symbolic list. -/
def writeSliceAt (offset : Nat) (xs : List α) (patch : List α) : List α :=
  match offset with
  | 0 => patch ++ dropBytes patch.length xs
  | k + 1 =>
    match xs with
    | [] => []
    | x :: rest => x :: writeSliceAt k rest patch

abbrev writeSlice (xs : List α) (offset : Nat) (patch : List α) : List α :=
  writeSliceAt offset xs patch

/-- Encode a natural number `n` as a little-endian list of `width` initialized
    bytes (`some (UInt8.ofNat ...)`). -/
def encodeLeBytes (width : Nat) (n : Nat) : ByteVec :=
  match width with
  | 0 => []
  | w + 1 => some (UInt8.ofNat (n % 256)) :: encodeLeBytes w (n / 256)

/-- Decode a little-endian list of `Option UInt8` into `some n` if every byte is
    initialized (`some b`), or `none` if any byte is uninitialized (`none`). -/
def decodeLeBytes : ByteVec → Option Nat
  | [] => some 0
  | none :: _ => none
  | some b :: rest =>
    match decodeLeBytes rest with
    | some hi => some (b.toNat + 256 * hi)
    | none => none

/-- Predicate asserting that every byte in a `ByteVec` is initialized (`some _`). -/
def allBytesInit : ByteVec → Prop
  | [] => True
  | none :: _ => False
  | some _ :: rest => allBytesInit rest

/-- Update allocation `target` in `mem`, leaving all other allocations unchanged.
    Uses `Bool.casesOn` (`match Nat.beq i target with ...`) rather than `@ite`
    so `updateAlloc mem target blk i` reduces definitionally via `dsimp` for
    concrete indices `i` and `target` even when `mem` is a symbolic function. -/
def updateAlloc (mem : Nat → AllocBlock) (target : Nat)
    (blk : AllocBlock) : Nat → AllocBlock :=
  fun i =>
    match Nat.beq i target with
    | true => blk
    | false => mem i

/-- Read `width` bytes from `mem` at provenance pointer `p`.
    Uses `match ... with | true => ... | false => ...` (`Bool.casesOn`) rather
    than `@ite` (`if ... then ...`) so `rw` on `mem` never encounters dependent
    `Decidable` motives, and places `width` on the left of `+` (`width + p.offset`)
    so `width + 0` reduces definitionally (`rfl`) for symbolic `width`. -/
def readSlice (mem : Nat → AllocBlock) (p : Ptr) (width : Nat) : Option ByteVec :=
  let blk := mem p.alloc.index
  match blk.perm.canRead && blk.written &&
        Nat.ble (width + p.offset) blk.size &&
        Nat.ble (width + p.offset) blk.bytes.length with
  | true => some (extractSlice blk.bytes p.offset width)
  | false => none

/-- Write `patch` bytes into `mem` at provenance pointer `p`. -/
def writeSliceMem (mem : Nat → AllocBlock) (p : Ptr) (patch : ByteVec) :
    Option (Nat → AllocBlock) :=
  let blk := mem p.alloc.index
  match blk.perm.canWrite &&
        Nat.ble (patch.length + p.offset) blk.size &&
        Nat.ble (patch.length + p.offset) blk.bytes.length with
  | true =>
    let newBlk : AllocBlock := {
      blk with
      bytes := writeSlice blk.bytes p.offset patch
      written := true
    }
    some (updateAlloc mem p.alloc.index newBlk)
  | false => none

/-!
## 3. Generalized `X86Ty`, Multi-Field Padded `AdtDecl`, `hasTy`, and `AdmissibleLibInv`
-/

inductive FieldAccess where
  | pubSafe
  | priv
  | unsafeField

inductive X86Ty where
  | u8
  | u16
  | u32
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)

/-- Single field declaration inside a multi-field struct (`AdtDecl`), recording
    its byte offset (`offset`), byte width (`size`), field type (`ty`), and
    visibility/safety classification (`access`). -/
structure FieldDecl where
  offset : Nat
  size : Nat
  ty : X86Ty
  access : FieldAccess

/-- Captured ADT (struct) declaration recording its crate-local identifier,
    total byte size (including alignment padding), field layout declarations,
    and `#[non_exhaustive]` attribute status. -/
structure AdtDecl where
  id : Nat
  size : Nat
  fields : List FieldDecl
  nonExhaustive : Bool := false

def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  !decl.nonExhaustive &&
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv | .unsafeField => false)

/-- Look up an `AdtDecl` by `id` in `adts`. -/
def lookupAdt (adts : List AdtDecl) (id : Nat) : Option AdtDecl :=
  match adts with
  | [] => none
  | d :: ds =>
    match Nat.beq d.id id with
    | true => some d
    | false => lookupAdt ds id

/-- Byte size of an `X86Ty` under `adts` and `tySizes`. -/
def evalX86TyByteSize (adts : List AdtDecl) (tySizes : Nat → Nat) (ty : X86Ty) : Nat :=
  match ty with
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt id =>
    match lookupAdt adts id with
    | some decl => decl.size
    | none => 0
  | .param idx => tySizes idx
  | .refParam _ => 8

/-- Conjunction asserting that every field slice `(f.offset, f.size)` of `bytes`
    satisfies `pred f.ty (extractSlice bytes f.offset f.size)`. -/
def allFieldsSatisfy (pred : X86Ty → ByteVec → Prop)
    (bytes : ByteVec) : List FieldDecl → Prop
  | [] => True
  | f :: fs =>
    pred f.ty (extractSlice bytes f.offset f.size) ∧
    allFieldsSatisfy pred bytes fs

/-- Dynamic language-level ABI type-validity relation for scalar and polymorphic
    parameter field types (`V_lang`). -/
def hasFieldTy (tySizes : Nat → Nat) (ty : X86Ty) (bytes : ByteVec) : Prop :=
  match ty with
  | .u8 => bytes.length = 1 ∧ allBytesInit bytes
  | .u16 => bytes.length = 2 ∧ allBytesInit bytes
  | .u32 => bytes.length = 4 ∧ allBytesInit bytes
  | .usize => bytes.length = 8 ∧ allBytesInit bytes
  | .bool => bytes = [some 0] ∨ bytes = [some 1]
  | .unit => bytes = []
  | .param idx => bytes.length = tySizes idx
  | .refParam _ => bytes.length = 8 ∧ allBytesInit bytes
  | .adt _ => False

/-- Dynamic language-level ABI type-validity relation (`V_lang`) matching a
    `ByteVec` against an `X86Ty` under `adts` and `tySizes`.

    Notice that for `.adt id`, only the slices `extractSlice bytes f.offset f.size`
    for `f ∈ decl.fields` are constrained; padding bytes outside `decl.fields`
    may be `none` (uninitialized) or `some _` (`r[validity.struct]`). -/
def hasTy (adts : List AdtDecl) (tySizes : Nat → Nat)
    (bytes : ByteVec) (ty : X86Ty) : Prop :=
  match ty with
  | .adt id =>
    match lookupAdt adts id with
    | none => False
    | some decl =>
      bytes.length = decl.size ∧
      allFieldsSatisfy (hasFieldTy tySizes) bytes decl.fields
  | _ => hasFieldTy tySizes ty bytes

/-- Library representation invariant map (`I_lib`) over byte sequences. -/
abbrev LibInv := (Nat → Nat) → X86Ty → ByteVec → Prop

/-- Default library representation invariant equating library validity with
    language-level byte validity (`hasTy adts`). -/
def defaultLibInv (adts : List AdtDecl) : LibInv :=
  fun tySizes ty bytes => hasTy adts tySizes bytes ty

/-- Generalized admissibility of a library representation invariant `libInv` for
    a crate's multi-field (and potentially padded) ADT declarations `adts`:
    1. Refines language validity (`libInv → hasTy`).
    2. Scalar primitives (`.u8`, `.u16`, `.u32`, `.usize`, `.bool`, `.unit`) and
       generic `Copy` byte parameters (`.param idx`) are open.
    3. Public-safe multi-field struct closure (`r[expr.struct.safety]`): for any
       ADT `decl` in `adts` with `decl.allFieldsPubSafe = true`, any `bytes` of
       length `decl.size` whose field slices each satisfy `hasFieldTy` and
       `libInv` (with arbitrary initialized or uninitialized `Option UInt8`
       padding bytes between fields!) must satisfy
       `libInv tySizes (.adt id) bytes`. -/
def AdmissibleLibInv (adts : List AdtDecl) (libInv : LibInv) : Prop :=
  (∀ tySizes ty bytes, libInv tySizes ty bytes → hasTy adts tySizes bytes ty) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u8 → libInv tySizes .u8 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u16 → libInv tySizes .u16 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u32 → libInv tySizes .u32 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .usize → libInv tySizes .usize bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .bool → libInv tySizes .bool bytes) ∧
  (∀ tySizes, libInv tySizes .unit []) ∧
  (∀ tySizes idx bytes, bytes.length = tySizes idx → libInv tySizes (.param idx) bytes) ∧
  (∀ id decl, lookupAdt adts id = some decl → decl.allFieldsPubSafe = true →
    ∀ tySizes bytes,
      bytes.length = decl.size →
      allFieldsSatisfy (hasFieldTy tySizes) bytes decl.fields →
      allFieldsSatisfy (libInv tySizes) bytes decl.fields →
      libInv tySizes (.adt id) bytes)

/-!
## 4. Byte-Addressed x86-64 Instruction Set & Small-Step Operational Semantics
-/

/-- Source operand of a byte-addressed x86-64 instruction:
    - `slotSlice slot offset width consume`: reads `width` bytes from stack slot
      `slot` at byte offset `offset`. When `consume = true`, deinitializes those
      `width` bytes to `none` (`r[expr.move.deinitialization]`).
    - `immWord width val`: immediate `width`-byte little-endian integer `val`.
    - `immBool b`: immediate 1-byte boolean (`[some 0]` or `[some 1]`).
    - `immUnit`: immediate 0-byte unit value `[]`. -/
inductive X86Operand where
  | slotSlice (slot : SlotId) (offset : Nat := 0) (width : Nat := 8)
      (consume : Bool := false)
  | immWord (width : Nat) (val : Nat)
  | immBool (b : Bool)
  | immUnit

inductive X86BinOp where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | eq
  | ne
  | lt
  | le
  | gt
  | ge

/-- Sequential instruction in a byte-addressed x86-64 basic block:
    - `movSlice dst dstOff src`: copies the byte slice `src` into stack slot
      `dst` at byte offset `dstOff` (preserving untouched field and padding bytes
      in `dst`!).
    - `alu op width dst dstOff lhs rhs`: decodes `width`-byte little-endian
      integers from `lhs` and `rhs` (failing with `.failed .ub` if any accessed
      byte is `none`!), evaluates `op`, and writes the result into `dst` at
      `dstOff`.
    - `leaSlot dst target offset`: stores provenance pointer `Ptr target offset`
      into `dst` (requiring `target` to be live).
    - `addPtrOffset dst srcPtr delta`: adds `delta` bytes to the pointer in
      `srcPtr`, keeping its `alloc` provenance fixed!
    - `reborrowSlot dst srcPtr`: copies the pointer in `srcPtr` to `dst` after
      verifying its target allocation is live.
    - `loadPtr dst dstOff srcPtr width`: reads `width` bytes from memory at the
      pointer in `srcPtr` (failing with `.failed .ub` if `offset + width > size`)
      and writes them into `dst` at `dstOff`.
    - `storePtr dstPtr src`: writes the byte slice `src` to memory at the pointer
      in `dstPtr` (failing with `.failed .ub` if `offset + width > size`).
    - `allocSlot slot size`: allocates `size` uninitialized (`none`) bytes for
      `slot` with `.readWrite` permission (`StorageLive`).
    - `deallocSlot slot`: deallocates `slot` to `.unallocated` (`StorageDead`).
    - `nop`: architectural `nop`. -/
inductive X86Instr where
  | movSlice (dst : SlotId) (dstOff : Nat) (src : X86Operand)
  | alu (op : X86BinOp) (width : Nat) (dst : SlotId) (dstOff : Nat)
      (lhs : X86Operand) (rhs : X86Operand)
  | leaSlot (dst : SlotId) (target : SlotId) (offset : Nat := 0)
  | addPtrOffset (dst : SlotId) (srcPtr : SlotId) (delta : Nat)
  | reborrowSlot (dst : SlotId) (srcPtr : SlotId)
  | loadPtr (dst : SlotId) (dstOff : Nat) (srcPtr : SlotId) (width : Nat)
  | storePtr (dstPtr : SlotId) (src : X86Operand)
  | allocSlot (slot : SlotId) (size : Nat)
  | deallocSlot (slot : SlotId)
  | nop

mutual
  inductive X86Term where
    | ret
    | jmp (target : BlockLabel)
    | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
        (trueTarget : BlockLabel)
    | ud2
    | abortPanic
    | movSizeOfJmp (dst : SlotId) (ty : X86Ty) (target : BlockLabel)
    | cmpSizeEqJmp (dst : SlotId) (ty1 ty2 : X86Ty) (target : BlockLabel)
    | repMovsbJmp (dst : SlotId) (srcTy dstTy : X86Ty) (ptrSlot : SlotId)
        (target : BlockLabel)
    | call1 (dst : SlotId) (callee : X86Body) (arg : X86Operand)
        (target : BlockLabel)

  structure X86Block where
    instrs : List X86Instr
    term : X86Term

  structure X86Body where
    adts : List AdtDecl := []
    argTys : List X86Ty
    retTy : X86Ty
    slotCount : Nat
    blocks : List X86Block
    requiredConsts : List X86Body := []
end

structure X86CallFrame where
  callerBody : Option X86Body
  callerMem : Nat → AllocBlock
  retSlot : SlotId
  retBlock : Nat

structure X86State where
  mem : Nat → AllocBlock
  bb : Nat
  ip : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option X86Body := none
  stack : List X86CallFrame := []

/-- Evaluate an `X86Operand`, returning the loaded `ByteVec` and updated memory. -/
def evalX86Operand (mem : Nat → AllocBlock) (op : X86Operand) :
    Option (ByteVec × (Nat → AllocBlock)) :=
  match op with
  | .slotSlice slot offset width false =>
    match readSlice mem { alloc := slot, offset := offset } width with
    | some bs => some (bs, mem)
    | none => none
  | .slotSlice slot offset width true =>
    match readSlice mem { alloc := slot, offset := offset } width with
    | some bs =>
      let blk := mem slot.index
      let clearedBlk : AllocBlock := {
        blk with
        bytes := writeSlice blk.bytes offset (replicateBytes width none)
      }
      some (bs, updateAlloc mem slot.index clearedBlk)
    | none => none
  | .immWord width val =>
    some (encodeLeBytes width val, mem)
  | .immBool b =>
    some ([some (if b then 1 else 0)], mem)
  | .immUnit =>
    some ([], mem)

/-- Evaluate an x86-64 binary ALU, bitwise, shift, or comparison operation on
    two `width`-byte slices. Returns `none` (triggering `.failed .ub`) if any
    accessed byte in `lhs` or `rhs` is uninitialized (`none` / poison). -/
def evalX86BinOp (op : X86BinOp) (width : Nat) (lhs rhs : ByteVec) :
    Option ByteVec :=
  match Nat.beq lhs.length width && Nat.beq rhs.length width with
  | true =>
    match decodeLeBytes lhs, decodeLeBytes rhs with
    | some a, some b =>
      match op with
      | .add => some (encodeLeBytes width (a + b))
      | .sub => some (encodeLeBytes width (a - b))
      | .mul => some (encodeLeBytes width (a * b))
      | .bitAnd => some (encodeLeBytes width (Nat.land a b))
      | .bitOr => some (encodeLeBytes width (Nat.lor a b))
      | .bitXor => some (encodeLeBytes width (Nat.xor a b))
      | .shl => some (encodeLeBytes width (a <<< b))
      | .shr => some (encodeLeBytes width (a >>> b))
      | .eq => some [some (match Nat.beq a b with | true => 1 | false => 0)]
      | .ne => some [some (match Nat.beq a b with | true => 0 | false => 1)]
      | .lt => some [some (match Nat.blt a b with | true => 1 | false => 0)]
      | .le => some [some (match Nat.ble a b with | true => 1 | false => 0)]
      | .gt => some [some (match Nat.blt b a with | true => 1 | false => 0)]
      | .ge => some [some (match Nat.ble b a with | true => 1 | false => 0)]
    | _, _ => none
  | false => none

/-- Single-step evaluation of a sequential instruction (`X86Instr`). -/
def evalX86Instr (s : X86State) (instr : X86Instr) :
    StepResult X86State Unit ByteVec :=
  match instr with
  | .movSlice dst dstOff src =>
    match evalX86Operand s.mem src with
    | some (bs, mem') =>
      match writeSliceMem mem' { alloc := dst, offset := dstOff } bs with
      | some mem'' => .step () { s with mem := mem'', ip := s.ip + 1 }
      | none => .failed .ub
    | none => .failed .ub
  | .alu op width dst dstOff lhs rhs =>
    match evalX86Operand s.mem lhs with
    | some (bs1, mem1) =>
      match evalX86Operand mem1 rhs with
      | some (bs2, mem2) =>
        match evalX86BinOp op width bs1 bs2 with
        | some outBs =>
          match writeSliceMem mem2 { alloc := dst, offset := dstOff } outBs with
          | some mem3 => .step () { s with mem := mem3, ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .leaSlot dst target offset =>
    let targetBlk := s.mem target.index
    let dstBlk := s.mem dst.index
    match targetBlk.perm.canRead && targetBlk.written &&
          Nat.ble offset targetBlk.size && dstBlk.perm.canWrite with
    | true =>
      let newDst : AllocBlock := {
        dstBlk with
        ptr := some { alloc := target, offset := offset }
        written := true
      }
      .step () { s with mem := updateAlloc s.mem dst.index newDst, ip := s.ip + 1 }
    | false => .failed .ub
  | .addPtrOffset dst srcPtr delta =>
    let srcBlk := s.mem srcPtr.index
    let dstBlk := s.mem dst.index
    match srcBlk.perm.canRead && srcBlk.written && dstBlk.perm.canWrite with
    | true =>
      match srcBlk.ptr with
      | some p =>
        let newDst : AllocBlock := {
          dstBlk with
          ptr := some (p.addOffset delta)
          written := true
        }
        .step () { s with mem := updateAlloc s.mem dst.index newDst, ip := s.ip + 1 }
      | none => .failed .ub
    | false => .failed .ub
  | .reborrowSlot dst srcPtr =>
    let srcBlk := s.mem srcPtr.index
    let dstBlk := s.mem dst.index
    match srcBlk.perm.canRead && srcBlk.written && dstBlk.perm.canWrite with
    | true =>
      match srcBlk.ptr with
      | some p =>
        let targetBlk := s.mem p.alloc.index
        match targetBlk.perm.canRead && targetBlk.written &&
              Nat.ble p.offset targetBlk.size with
        | true =>
          let newDst : AllocBlock := {
            dstBlk with
            ptr := some p
            written := true
          }
          .step () { s with mem := updateAlloc s.mem dst.index newDst, ip := s.ip + 1 }
        | false => .failed .ub
      | none => .failed .ub
    | false => .failed .ub
  | .loadPtr dst dstOff srcPtr width =>
    let srcBlk := s.mem srcPtr.index
    match srcBlk.perm.canRead && srcBlk.written with
    | true =>
      match srcBlk.ptr with
      | some p =>
        match readSlice s.mem p width with
        | some bs =>
          match writeSliceMem s.mem { alloc := dst, offset := dstOff } bs with
          | some mem' => .step () { s with mem := mem', ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | none => .failed .ub
    | false => .failed .ub
  | .storePtr dstPtr src =>
    match evalX86Operand s.mem src with
    | some (bs, mem1) =>
      let ptrBlk := mem1 dstPtr.index
      match ptrBlk.perm.canRead && ptrBlk.written with
      | true =>
        match ptrBlk.ptr with
        | some p =>
          match writeSliceMem mem1 p bs with
          | some mem2 => .step () { s with mem := mem2, ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | false => .failed .ub
    | none => .failed .ub
  | .allocSlot slot size =>
    let newBlk : AllocBlock := {
      perm := .readWrite
      size := size
      bytes := replicateBytes size none
      ptr := none
      written := false
    }
    .step () { s with mem := updateAlloc s.mem slot.index newBlk, ip := s.ip + 1 }
  | .deallocSlot slot =>
    .step () { s with mem := updateAlloc s.mem slot.index unallocBlock, ip := s.ip + 1 }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

/-- Unified `rep movsb` block copy (`X86Term.repMovsbJmp`) over `ByteVec`. -/
def evalRepMovsb (adts : List AdtDecl) (tySizes : Nat → Nat)
    (mem : Nat → AllocBlock) (dst : SlotId) (srcTy dstTy : X86Ty)
    (ptrSlot : SlotId) : Option (Nat → AllocBlock) :=
  let srcSz := evalX86TyByteSize adts tySizes srcTy
  let dstSz := evalX86TyByteSize adts tySizes dstTy
  match Nat.beq srcSz dstSz with
  | true =>
    let ptrBlk := mem ptrSlot.index
    match ptrBlk.perm.canRead && ptrBlk.written with
    | true =>
      match ptrBlk.ptr with
      | some p =>
        let memAfterMove := updateAlloc mem ptrSlot.index
          { ptrBlk with ptr := none, written := false }
        match readSlice memAfterMove p srcSz with
        | some copiedBytes =>
          writeSliceMem memAfterMove { alloc := dst, offset := 0 } copiedBytes
        | none => none
      | none => none
    | false => none
  | false => none

/-- Single-step evaluation of a basic-block terminator (`X86Term`). -/
def evalX86Term (adts : List AdtDecl) (s : X86State) (term : X86Term) :
    StepResult X86State Unit ByteVec :=
  match term with
  | .ret =>
    let retBlk := s.mem 0
    match retBlk.perm.canRead && retBlk.written &&
          Nat.beq retBlk.bytes.length retBlk.size with
    | true =>
      let retBytes := retBlk.bytes
      match s.stack with
      | [] => .terminated (.normal retBytes)
      | frame :: restStack =>
        match writeSliceMem frame.callerMem { alloc := frame.retSlot, offset := 0 } retBytes with
        | some callerMem' =>
          .step () {
            mem := callerMem'
            bb := frame.retBlock
            ip := 0
            tySizes := s.tySizes
            curBody := frame.callerBody
            stack := restStack
          }
        | none => .failed .ub
    | false => .failed .ub
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .abortPanic =>
    .terminated .unwind
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some ([some 0], mem') =>
      .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
    | some ([some 1], mem') =>
      .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
    | _ => .failed .ub
  | .movSizeOfJmp dst ty target =>
    let sz := evalX86TyByteSize adts s.tySizes ty
    match writeSliceMem s.mem { alloc := dst, offset := 0 } (encodeLeBytes 8 sz) with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .cmpSizeEqJmp dst ty1 ty2 target =>
    let sz1 := evalX86TyByteSize adts s.tySizes ty1
    let sz2 := evalX86TyByteSize adts s.tySizes ty2
    let eqByte : UInt8 := match Nat.beq sz1 sz2 with | true => 1 | false => 0
    match writeSliceMem s.mem { alloc := dst, offset := 0 } [some eqByte] with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .repMovsbJmp dst srcTy dstTy ptrSlot target =>
    match evalRepMovsb adts s.tySizes s.mem dst srcTy dstTy ptrSlot with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalX86Operand s.mem arg with
    | some (argBytes, callerMem') =>
      let retSz := evalX86TyByteSize adts s.tySizes callee.retTy
      let retBlk : AllocBlock := {
        perm := .readWrite
        size := retSz
        bytes := replicateBytes retSz none
        ptr := none
        written := false
      }
      let argBlk : AllocBlock := {
        perm := .readWrite
        size := argBytes.length
        bytes := argBytes
        ptr := none
        written := true
      }
      let calleeMem : Nat → AllocBlock :=
        updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk) 1 argBlk
      let frame : X86CallFrame := {
        callerBody := s.curBody
        callerMem := callerMem'
        retSlot := dst
        retBlock := target.index
      }
      .step () {
        mem := calleeMem
        bb := 0
        ip := 0
        tySizes := s.tySizes
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed .ub

def evalX86Step (rootBody : X86Body) (s : X86State) :
    StepResult X86State Unit ByteVec :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalX86Instr s instr
    | none => evalX86Term active.adts s blk.term

/-- Entry initialization condition for parameter home slots `1 ..= argTys.length`
    and unallocated higher slots. -/
def argsMatchStack (adts : List AdtDecl) (tySizes : Nat → Nat)
    (argTys : List X86Ty) (mem : Nat → AllocBlock) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      let sz := evalX86TyByteSize adts tySizes ty
      (∃ bs,
        mem k = {
          perm := .readWrite
          size := sz
          bytes := bs
          ptr := none
          written := true
        } ∧
        hasTy adts tySizes bs ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → mem j = unallocBlock)
    1

/-- Entry state predicate for an `X86Body`:
    - Return slot `0` is allocated with size `evalX86TyByteSize body.adts s.tySizes body.retTy`
      and `replicateBytes retSz none` (`written := false`).
    - Parameter slots `1 ..= argTys.length` hold type-valid `ByteVec`s. -/
def initX86State (body : X86Body) (s : X86State) : Prop :=
  let retSz := evalX86TyByteSize body.adts s.tySizes body.retTy
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.mem 0 = {
    perm := .readWrite
    size := retSz
    bytes := replicateBytes retSz none
    ptr := none
    written := false
  } ∧
  argsMatchStack body.adts s.tySizes body.argTys s.mem

def X86Machine : SmallStepMachine X86Body X86State Unit ByteVec where
  initState := initX86State
  step body s r := r = evalX86Step body s

def X86Lang : Language :=
  X86Machine.toLanguage

abbrev X86Sem (body : X86Body) : X86Lang.Behavior :=
  X86Lang.sem body

/-!
## 5. PME Admission, Crate Verification Envelope, and Byte-Slice Lemmas
-/

inductive RequiresConst : X86Body → X86Body → Prop where
  | direct {body c : X86Body} :
      c ∈ body.requiredConsts →
      RequiresConst body c
  | nested {body c' c : X86Body} :
      c' ∈ body.requiredConsts →
      RequiresConst c' c →
      RequiresConst body c
  | call1 {body callee c : X86Body} {blk : X86Block}
      {dst : SlotId} {arg : X86Operand} {target : BlockLabel} :
      blk ∈ body.blocks →
      blk.term = .call1 dst callee arg target →
      RequiresConst callee c →
      RequiresConst body c

def ConstSucceeds (tySizes : Nat → Nat) (c : X86Body) : Prop :=
  ∃ (s₀ : X86State) (n : Nat) (tr : List Unit) (v : ByteVec),
    s₀.tySizes = tySizes ∧
    initX86State c s₀ ∧
    ReachesPrefix X86Machine c s₀ n s₀ tr (.terminated (.normal v))

def MonoAdmitted (tySizes : Nat → Nat) (body : X86Body) : Prop :=
  ∀ c, RequiresConst body c → ConstSucceeds tySizes c

def argsSatisfyLibInv (adts : List AdtDecl) (libInv : LibInv) (tySizes : Nat → Nat)
    (argTys : List X86Ty) (mem : Nat → AllocBlock) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      let sz := evalX86TyByteSize adts tySizes ty
      (∃ bs,
        mem k = {
          perm := .readWrite
          size := sz
          bytes := bs
          ptr := none
          written := true
        } ∧
        libInv tySizes ty bs) ∧
      rest (k + 1))
    (fun _ => True)
    1

def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=
  X86Lang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

structure TargetArtifact where
  private mk ::
  unit : Unit

opaque assemble : X86Body → TargetArtifact := fun _ => { unit := () }

opaque TargetSem :
    TargetArtifact → ExecQuery X86State → Partial (ExecOut Unit ByteVec → Prop) :=
  fun _ _ => Partial.ub

def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery X86State
  Out := ExecOut Unit ByteVec
  sem := TargetSem

opaque π_asm : X86Lang.Behavior → TargetLang.Behavior :=
  fun b => b

def AssemblerCompiler : Compiler X86Lang TargetLang where
  compile := assemble
  π := π_asm

inductive TCBItem where
  | assemblerLowering (fnName : String) (body : X86Body)
  | userAxiom (name : String) (prop : Prop)

instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .assemblerLowering _ body => AssemblerCompiler.SoundOn body
    | .userAxiom _ prop => prop

def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .assemblerLowering _ _ => True
    | .userAxiom _ _ => False

inductive FnKind where
  | pubSafe (traitLaws : Prop := True)
  | pubUnsafe (traitLaws : Prop := True) (safetyPre : ExecQuery X86State → Prop)
  | priv (pre : ExecQuery X86State → Prop := fun _ => True)

structure CapturedFn where
  name : String
  prog : X86Body
  kind : FnKind := .pubSafe True
  specs : List X86Lang.Behavior := []

def CapturedFn.effectivePre (libInv : LibInv)
    (fn : CapturedFn) (q : ExecQuery X86State) : Prop :=
  MonoAdmitted q.init.tySizes fn.prog ∧
  match fn.kind with
  | .pubSafe traitLaws =>
    traitLaws ∧
    argsSatisfyLibInv fn.prog.adts libInv q.init.tySizes fn.prog.argTys q.init.mem
  | .pubUnsafe traitLaws safetyPre =>
    traitLaws ∧
    argsSatisfyLibInv fn.prog.adts libInv q.init.tySizes fn.prog.argTys q.init.mem ∧
    safetyPre q
  | .priv internalPre =>
    internalPre q

def CapturedFn.effectiveSpecs (libInv : LibInv)
    (fn : CapturedFn) : List X86Lang.Behavior :=
  let pre := fn.effectivePre libInv
  match fn.kind with
  | .pubSafe _ | .pubUnsafe _ _ =>
    EnsuresRetLibInv libInv fn.prog.retTy pre :: fn.specs
  | .priv _ =>
    fn.specs

structure Crate where
  adts : List AdtDecl := []
  libInv : LibInv := defaultLibInv adts
  functions : List CapturedFn
  tcb : List TCBItem

def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AdmissibleLibInv c.adts c.libInv ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResultOn AssemblerCompiler defaultTrustPolicy
      c.tcb fn.prog (fn.effectivePre c.libInv) (fn.effectiveSpecs c.libInv)))

/-!
## 6. Structural Machine Meta-Theorems, Symbolic Execution Helpers, and Byte-Slice Lemmas
-/

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

theorem x86Machine_total : TotalStep X86Machine :=
  fun body s => ⟨evalX86Step body s, rfl⟩

theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

theorem ensuresRetLibInv_le_wellFormedOn (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop) :
    EnsuresRetLibInv libInv retTy pre ≤ X86Lang.WellFormedOn pre :=
  specOn_le_wellFormedOn (L := X86Lang) pre _

theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   h_ver.2.1,
   Preorder.le_trans h_ver.2.2 (h_mono h_le)⟩

theorem Compiler.Verified.with_wellFormedOn
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {pre : L_src.Query → Prop} {spec : L_src.Behavior}
    (h_ver : C.Verified s spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre)
    (h_mono : Monotone C.π) :
    AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s)) :=
  ⟨Compiler.Verified.mono h_ver h_wf h_mono, h_ver, True.intro⟩

theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

theorem reachesPrefix_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome ByteVec}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    out = .running ∨
      ∃ n' tr', ReachesPrefix X86Machine body init n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : StepResult.step () s₂ = evalX86Step body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs
    subst hs
    exact Or.inr ⟨n', tr', hr⟩
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome ByteVec} {term : TerminationKind ByteVec}
    (hstep : evalX86Step body s = .terminated term)
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    out = .running ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalX86Step body s := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

def SafeAndEnsures (P : ByteVec → Prop) (out : PrefixOutcome ByteVec) : Prop :=
  out.isSafe ∧ ∀ ret, out = .terminated (.normal ret) → P ret

theorem reachesPrefix_safeAndEnsures_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome ByteVec} {P : ByteVec → Prop}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix X86Machine body init n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_safeAndEnsures_of_normal
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome ByteVec} {P : ByteVec → Prop} {v : ByteVec}
    (hstep : evalX86Step body s = .terminated (.normal v))
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with h1
    injection h1 with h2
    subst h2
    exact hPv

theorem reachesPrefix_not_normal_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {v : ByteVec}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix X86Machine body init n' s' tr' (.terminated (.normal v)) →
      False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_normal_of_unwind
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {v : ByteVec}
    (hstep : evalX86Step body s = .terminated .unwind)
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => cases hrun
  | inr hunw => cases hunw

/-- Structural byte-slice lemmas for symbolic-length polymorphic types (`param idx`). -/
theorem replicateBytes_length (n : Nat) (v : Option UInt8) :
    (replicateBytes n v).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [replicateBytes, List.length]
    exact congrArg (· + 1) ih

theorem takeBytes_length (xs : List α) :
    takeBytes xs.length xs = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp [takeBytes, List.length]
    exact congrArg (x :: ·) ih

theorem takeBytes_of_eq_length (xs : List α) (n : Nat) (h : xs.length = n) :
    takeBytes n xs = xs := by
  subst h
  exact takeBytes_length xs

theorem dropBytes_length (xs : List α) :
    dropBytes xs.length xs = [] := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [dropBytes, List.length]
    exact ih

theorem dropBytes_of_eq_length (xs : List α) (n : Nat) (h : xs.length = n) :
    dropBytes n xs = [] := by
  subst h
  exact dropBytes_length xs

theorem append_nil_bytes (xs : List α) :
    xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    change x :: (rest ++ []) = x :: rest
    exact congrArg (x :: ·) ih

theorem extractSlice_zero_of_eq_length (xs : List α) (n : Nat) (h : xs.length = n) :
    extractSlice xs 0 n = xs := by
  dsimp [extractSlice, dropBytes]
  exact takeBytes_of_eq_length xs n h

theorem writeSlice_zero_of_eq_length (dst patch : List α)
    (h : dst.length = patch.length) :
    writeSlice dst 0 patch = patch := by
  change patch ++ dropBytes patch.length dst = patch
  rw [dropBytes_of_eq_length dst patch.length h]
  exact append_nil_bytes patch

theorem encodeLeBytes_length (width n : Nat) :
    (encodeLeBytes width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ w ih =>
    dsimp [encodeLeBytes, List.length]
    exact congrArg (· + 1) (ih (n / 256))

theorem encodeLeBytes_allBytesInit (width n : Nat) :
    allBytesInit (encodeLeBytes width n) := by
  induction width generalizing n with
  | zero => exact True.intro
  | succ w ih =>
    dsimp [encodeLeBytes, allBytesInit]
    exact ih (n / 256)

theorem decodeLeBytes_isSome_of_allBytesInit (bs : ByteVec)
    (h : allBytesInit bs) :
    ∃ n, decodeLeBytes bs = some n := by
  induction bs with
  | nil => exact ⟨0, rfl⟩
  | cons b rest ih =>
    cases b with
    | none => cases h
    | some byte =>
      dsimp [allBytesInit] at h
      cases ih h with
      | intro hi hhi =>
        refine ⟨byte.toNat + 256 * hi, ?_⟩
        dsimp [decodeLeBytes]
        rw [hhi]

/-!
## 7. Experiment 4: Generalized `AdmissibleLibInv` for Multi-Field Structs with Padding
-/

/-- `defaultLibInv adts` is admissible for ANY crate ADT list `adts : List AdtDecl`
    (including multi-field structs with arbitrary uninitialized padding bytes). -/
theorem defaultLibInv_admissible (adts : List AdtDecl) :
    AdmissibleLibInv adts (defaultLibInv adts) := by
  refine ⟨fun _ _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ => rfl,
          fun _ _ _ h => h,
          ?_⟩
  intro id decl hlook _ tySizes bytes hlen hfields _
  dsimp [defaultLibInv, hasTy]
  rw [hlook]
  exact ⟨hlen, hfields⟩

/-- Generic single-function `CrateTheorem` discharge for a safe function under
    `defaultLibInv adts`. -/
theorem verify_single_fn_wf_crate
    (adts : List AdtDecl) (fnName : String) (body : X86Body)
    (h_ret : X86Sem body ≤
      EnsuresRetLibInv (defaultLibInv adts) body.retTy
        (CapturedFn.effectivePre (defaultLibInv adts)
          { name := fnName, prog := body, specs := [] })) :
    CrateTheorem {
      adts := adts
      libInv := defaultLibInv adts
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), defaultLibInv_admissible adts, ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 h_ret)
    (ensuresRetLibInv_le_wellFormedOn _ _ _)
    hAssumptions.1.1

/-- `#[repr(transparent)] pub struct NonZeroUsize { val: usize }` (`id := 0`,
    total size 8, single private `.usize` field at offset 0). -/
def nonZeroAdtDecl : AdtDecl where
  id := 0
  size := 8
  fields := [{ offset := 0, size := 8, ty := .usize, access := .priv }]

/-- `#[repr(C)] pub struct Padded { pub a: u8, /* 3 bytes padding at 1..4 */ pub b: u32 }`
    (`id := 1`, total size 8, `a` at offset 0 of size 1, `b` at offset 4 of size 4,
    with 3 padding bytes at offsets `1, 2, 3`). -/
def paddedAdtDecl : AdtDecl where
  id := 1
  size := 8
  fields := [
    { offset := 0, size := 1, ty := .u8, access := .pubSafe },
    { offset := 4, size := 4, ty := .u32, access := .pubSafe }
  ]

/-- Library representation invariant for a crate containing both `NonZeroUsize`
    (`id = 0`, private field requiring `decodeLeBytes bytes ≠ some 0`) and
    `Padded` (`id = 1`, public-safe fields with unconstrained padding bytes at
    offsets `1..4`). -/
def nonZeroAndPaddedLibInv (tySizes : Nat → Nat) (ty : X86Ty)
    (bytes : ByteVec) : Prop :=
  match ty with
  | .adt 0 =>
    hasTy [nonZeroAdtDecl, paddedAdtDecl] tySizes bytes (.adt 0) ∧
    decodeLeBytes bytes ≠ some 0
  | .adt 1 =>
    hasTy [nonZeroAdtDecl, paddedAdtDecl] tySizes bytes (.adt 1)
  | .adt _ => False
  | _ => hasFieldTy tySizes ty bytes

/-- `nonZeroAndPaddedLibInv` satisfies `AdmissibleLibInv [nonZeroAdtDecl, paddedAdtDecl]`:
    - `NonZeroUsize` (`id = 0`) has a private field (`allFieldsPubSafe = false`),
      so restricting `decodeLeBytes bytes ≠ some 0` is permitted.
    - `Padded` (`id = 1`) has all `pubSafe` fields, and `nonZeroAndPaddedLibInv`
      accepts any 8-byte sequence whose field `a` (offset 0, size 1) and field `b`
      (offset 4, size 4) are initialized, regardless of whether padding bytes
      `1, 2, 3` are `none` or `some _`. -/
theorem nonZeroAndPaddedLibInv_admissible :
    AdmissibleLibInv [nonZeroAdtDecl, paddedAdtDecl] nonZeroAndPaddedLibInv := by
  refine ⟨?_,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ => rfl,
          fun _ _ _ h => h,
          ?_⟩
  · intro tySizes ty bytes hinv
    cases ty with
    | u8 | u16 | u32 | usize | bool | unit | param _ | refParam _ => exact hinv
    | adt id =>
      cases id with
      | zero => exact hinv.1
      | succ k =>
        cases k with
        | zero => exact hinv
        | succ _ => cases hinv
  · intro id decl hlook hpub tySizes bytes hlen hfields _
    cases id with
    | zero =>
      dsimp [lookupAdt, nonZeroAdtDecl] at hlook
      injection hlook with hdecl
      subst hdecl
      cases hpub
    | succ k =>
      cases k with
      | zero =>
        dsimp [lookupAdt, nonZeroAdtDecl, paddedAdtDecl] at hlook
        injection hlook with hdecl
        subst hdecl
        exact ⟨hlen, hfields⟩
      | succ m =>
        dsimp [lookupAdt, nonZeroAdtDecl, paddedAdtDecl] at hlook
        cases hlook

/-- Restricted library invariant that attempts to require field `b` (at offset 4,
    width 4) of `pub struct Padded { pub a: u8, pub b: u32 }` to be non-zero. -/
def badRestrictedFieldPaddedLibInv (tySizes : Nat → Nat) (ty : X86Ty)
    (bytes : ByteVec) : Prop :=
  match ty with
  | .adt 1 =>
    hasTy [paddedAdtDecl] tySizes bytes (.adt 1) ∧
    decodeLeBytes (extractSlice bytes 4 4) ≠ some 0
  | .adt _ => False
  | _ => hasFieldTy tySizes ty bytes

/-- Negative adequacy canary 4A: `AdmissibleLibInv` rejects `badRestrictedFieldPaddedLibInv`
    because safe downstream code can construct `Padded { a: 0, b: 0 }` via struct
    literal syntax (`allFieldsPubSafe = true`). -/
theorem canary_pubSafe_padded_rejects_field_restriction :
    ¬ AdmissibleLibInv [paddedAdtDecl] badRestrictedFieldPaddedLibInv := by
  intro hAdm
  have hClosure := hAdm.2.2.2.2.2.2.2.2 1 paddedAdtDecl rfl rfl (fun _ => 0)
    [some 0, none, none, none, some 0, some 0, some 0, some 0]
    rfl
    ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩
    ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩
  exact hClosure.2 rfl

/-- Restricted library invariant that attempts to require the padding bytes
    (offsets `1, 2, 3`) of `pub struct Padded { pub a: u8, pub b: u32 }` to be
    initialized (`allBytesInit bytes`). -/
def badRequireInitPaddingLibInv (tySizes : Nat → Nat) (ty : X86Ty)
    (bytes : ByteVec) : Prop :=
  match ty with
  | .adt 1 =>
    hasTy [paddedAdtDecl] tySizes bytes (.adt 1) ∧
    allBytesInit bytes
  | .adt _ => False
  | _ => hasFieldTy tySizes ty bytes

/-- Negative adequacy canary 4B: `AdmissibleLibInv` rejects `badRequireInitPaddingLibInv`
    because safe downstream code constructing `Padded { a: 10, b: 1 }` leaves
    the 3 padding bytes at offsets `1, 2, 3` uninitialized (`none`)! -/
theorem canary_pubSafe_padded_rejects_padding_init_requirement :
    ¬ AdmissibleLibInv [paddedAdtDecl] badRequireInitPaddingLibInv := by
  intro hAdm
  have hClosure := hAdm.2.2.2.2.2.2.2.2 1 paddedAdtDecl rfl rfl (fun _ => 0)
    [some 10, none, none, none, some 1, some 0, some 0, some 0]
    rfl
    ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩
    ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩
  exact hClosure.2

/-!
## 8. Experiment 1: Multi-Field Struct with Padding (`Padded`), Sub-Field Projections, `rep movsb`, and Uninitialized-Byte ALU UB
-/

/-- Concrete 8-byte representation of `Padded { a: 10, b: 1 }` with 3
    uninitialized (`none`) padding bytes at offsets `1, 2, 3`. -/
def samplePaddedBytes : ByteVec :=
  [some 10, none, none, none, some 1, some 0, some 0, some 0]

theorem samplePaddedBytes_hasTy :
    hasTy [paddedAdtDecl] (fun _ => 0) samplePaddedBytes (.adt 1) :=
  ⟨rfl, ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩

theorem samplePaddedBytes_field_a :
    extractSlice samplePaddedBytes 0 1 = [some 10] := rfl

theorem samplePaddedBytes_padding :
    extractSlice samplePaddedBytes 1 3 = [none, none, none] := rfl

theorem samplePaddedBytes_field_b :
    extractSlice samplePaddedBytes 4 4 = [some 1, some 0, some 0, some 0] := rfl

theorem samplePaddedBytes_write_field_a_preserves_padding :
    writeSlice samplePaddedBytes 0 [some 42] =
      [some 42, none, none, none, some 1, some 0, some 0, some 0] := rfl

theorem samplePaddedBytes_write_field_b_preserves_padding :
    writeSlice samplePaddedBytes 4 [some 99, some 0, some 0, some 0] =
      [some 10, none, none, none, some 99, some 0, some 0, some 0] := rfl

/-- Decomposition lemma: any `ByteVec` satisfying `hasTy [paddedAdtDecl] tySizes bs (.adt 1)`
    consists of an initialized 1-byte field `some a0` at offset `0`, three
    arbitrary (possibly `none`) padding bytes `p1, p2, p3` at offsets `1..3`,
    and an initialized 4-byte field `some c0, some c1, some c2, some c3` at
    offsets `4..7`. -/
theorem padded_hasTy_decompose (tySizes : Nat → Nat) (bs : ByteVec)
    (h : hasTy [paddedAdtDecl] tySizes bs (.adt 1)) :
    ∃ (a0 : UInt8) (p1 p2 p3 : Option UInt8) (c0 c1 c2 c3 : UInt8),
      bs = [some a0, p1, p2, p3, some c0, some c1, some c2, some c3] := by
  have hlen : bs.length = 8 := h.1
  have hfa : allBytesInit (extractSlice bs 0 1) := h.2.1.2
  have hfb : allBytesInit (extractSlice bs 4 4) := h.2.2.1.2
  cases bs with
  | nil => cases hlen
  | cons x0 r1 =>
    cases r1 with
    | nil => cases hlen
    | cons p1 r2 =>
      cases r2 with
      | nil => cases hlen
      | cons p2 r3 =>
        cases r3 with
        | nil => cases hlen
        | cons p3 r4 =>
          cases r4 with
          | nil => cases hlen
          | cons x4 r5 =>
            cases r5 with
            | nil => cases hlen
            | cons x5 r6 =>
              cases r6 with
              | nil => cases hlen
              | cons x6 r7 =>
                cases r7 with
                | nil => cases hlen
                | cons x7 r8 =>
                  cases r8 with
                  | cons _ _ => cases hlen
                  | nil =>
                    cases x0 with
                    | none => cases hfa
                    | some a0 =>
                      cases x4 with
                      | none => cases hfb
                      | some c0 =>
                        cases x5 with
                        | none => cases hfb
                        | some c1 =>
                          cases x6 with
                          | none => cases hfb
                          | some c2 =>
                            cases x7 with
                            | none => cases hfb
                            | some c3 =>
                              exact ⟨a0, p1, p2, p3, c0, c1, c2, c3, rfl⟩

/-- `X86Body` for a function on `Padded` (`#[repr(C)] struct Padded { a: u8, b: u32 }`):
    1. Allocates scratch slot `2` (8 bytes) and pointer slot `3` (8 bytes).
    2. Takes the address of `_1` (`leaSlot ⟨3⟩ ⟨1⟩ 0`) and copies all 8 bytes of
       `_1` (including any `none` padding bytes at offsets `1..3`) into slot `2`
       via `repMovsbJmp`.
    3. Adds `1` to sub-field `a` (offset `0`, width `1`) in slot `2` via a 1-byte
       `.alu .add 1` instruction, preserving offsets `1..7`.
    4. Adds `10` to sub-field `b` (offset `4`, width `4`) in slot `2` via a 4-byte
       `.alu .add 4` instruction, preserving offsets `0..4`.
    5. Copies the updated 8-byte `Padded` struct from slot `2` into return slot `0`
       via `repMovsbJmp` and returns. -/
def paddedSubfieldAndCopyBody : X86Body where
  adts := [paddedAdtDecl]
  argTys := [.adt 1]
  retTy := .adt 1
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0
      ]
      term := .repMovsbJmp ⟨2⟩ (.adt 1) (.adt 1) ⟨3⟩ ⟨1⟩ },
    { instrs := [
        .alu .add 1 ⟨2⟩ 0 (.slotSlice ⟨2⟩ 0 1 false) (.immWord 1 1),
        .alu .add 4 ⟨2⟩ 4 (.slotSlice ⟨2⟩ 4 4 false) (.immWord 4 10),
        .leaSlot ⟨3⟩ ⟨2⟩ 0
      ]
      term := .repMovsbJmp ⟨0⟩ (.adt 1) (.adt 1) ⟨3⟩ ⟨2⟩ },
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩
      ]
      term := .ret }
  ]

/-- `paddedSubfieldAndCopyBody` is UB-free and preserves `defaultLibInv [paddedAdtDecl]`
    across all valid `Padded` inputs (including inputs whose padding bytes at
    offsets `1, 2, 3` are `none`!). -/
theorem paddedSubfieldAndCopyBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := paddedSubfieldAndCopyBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv [paddedAdtDecl]) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [paddedAdtDecl])) := by
  intro fn
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out _ hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : bb0 = 0 := hinit.1
    have hs : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hmem0_0 := hinit.2.2.2.2.1
    subst hb hs hc hst
    cases hinit.2.2.2.2.2.1 with
    | intro bs hbs =>
      have hmem0_1 := hbs.1
      have hbsty := hbs.2
      cases padded_hasTy_decompose tySizes0 bs hbsty with
      | intro a0 h1 =>
      cases h1 with
      | intro p1 h2 =>
      cases h2 with
      | intro p2 h3 =>
      cases h3 with
      | intro p3 h4 =>
      cases h4 with
      | intro c0 h5 =>
      cases h5 with
      | intro c1 h6 =>
      cases h6 with
      | intro c2 h7 =>
      cases h7 with
      | intro c3 hbs_eq =>
        subst hbs_eq
        let inBytes : ByteVec :=
          [some a0, p1, p2, p3, some c0, some c1, some c2, some c3]
        have hm0_0 : mem0 0 = { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false } :=
          hmem0_0
        have hm0_1 : mem0 1 = { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true } :=
          hmem0_1
        let s0 : X86State := { mem := mem0, bb := 0, ip := 0, tySizes := tySizes0 }
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr1 (fun _ _ hr2 => ?_)
        let m2 := updateAlloc (updateAlloc mem0 2
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }) 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
        have hm2_1 : m2 1 = { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true } :=
          hm0_1
        let s2 : X86State := { mem := m2, bb := 0, ip := 2, tySizes := tySizes0 }
        let m3 := updateAlloc m2 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
        let s3 : X86State := { mem := m3, bb := 0, ip := 3, tySizes := tySizes0 }
        have hstep2 : evalX86Step paddedSubfieldAndCopyBody s2 = .step () s3 := by
          change evalX86Instr s2 (.leaSlot ⟨3⟩ ⟨1⟩ 0) = .step () s3
          dsimp only [evalX86Instr, s2]
          rw [hm2_1]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
        let m3_deinit := updateAlloc m3 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
        let m4 := updateAlloc m3_deinit 2
          { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true }
        let s4 : X86State := { mem := m4, bb := 1, ip := 0, tySizes := tySizes0 }
        have hstep3 : evalX86Step paddedSubfieldAndCopyBody s3 = .step () s4 := by
          change evalX86Term [paddedAdtDecl] s3 (.repMovsbJmp ⟨2⟩ (.adt 1) (.adt 1) ⟨3⟩ ⟨1⟩) = .step () s4
          dsimp only [evalX86Term, evalRepMovsb, evalX86TyByteSize, lookupAdt, paddedAdtDecl,
            readSlice, writeSliceMem, updateAlloc, s3, m3, m2]
          rw [hm0_1]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep3 hr3 (fun _ _ hr4 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr5 (fun _ _ hr6 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr6 (fun _ _ hr7 => ?_)
        let outBytes : ByteVec :=
          writeSlice (writeSlice inBytes 0 (encodeLeBytes 1 (a0.toNat + 1))) 4
            (encodeLeBytes 4 (c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * (c3.toNat + 256 * 0))) + 10))
        let m_bb1_end := updateAlloc (updateAlloc (updateAlloc m4 2
          { perm := .readWrite, size := 8, bytes := writeSlice inBytes 0 (encodeLeBytes 1 (a0.toNat + 1)), ptr := none, written := true }) 2
          { perm := .readWrite, size := 8, bytes := outBytes, ptr := none, written := true }) 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨2⟩, offset := 0 }, written := true }
        let m_bb1_deinit := updateAlloc m_bb1_end 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
        let s7 : X86State := { mem := m_bb1_end, bb := 1, ip := 3, tySizes := tySizes0 }
        let m8 := updateAlloc m_bb1_deinit 0
          { perm := .readWrite, size := 8, bytes := outBytes, ptr := none, written := true }
        let s8 : X86State := { mem := m8, bb := 2, ip := 0, tySizes := tySizes0 }
        have hstep7 : evalX86Step paddedSubfieldAndCopyBody s7 = .step () s8 := by
          change evalX86Term [paddedAdtDecl] s7 (.repMovsbJmp ⟨0⟩ (.adt 1) (.adt 1) ⟨3⟩ ⟨2⟩) = .step () s8
          dsimp only [evalX86Term, evalRepMovsb, evalX86TyByteSize, lookupAdt, paddedAdtDecl,
            readSlice, writeSliceMem, updateAlloc, s7, m_bb1_end, m4, m3_deinit, m3, m2]
          rw [hm0_0]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep7 hr7 (fun _ _ hr8 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := outBytes) rfl hr10
          ⟨rfl, ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩

/-- Ready-to-apply `CrateTheorem` witness for `paddedSubfieldAndCopyBody`. -/
theorem prove_padded_subfield_crate (fnName : String) :
    CrateTheorem {
      adts := [paddedAdtDecl]
      libInv := defaultLibInv [paddedAdtDecl]
      functions := [{ name := fnName, prog := paddedSubfieldAndCopyBody }]
      tcb := [TCBItem.assemblerLowering fnName paddedSubfieldAndCopyBody]
    } :=
  verify_single_fn_wf_crate [paddedAdtDecl] fnName paddedSubfieldAndCopyBody
    (paddedSubfieldAndCopyBody_verified fnName)

/-- Buggy `X86Body` that attempts a 64-bit ALU `.add` (`width := 8`) across the
    entire 8-byte `Padded` struct in slot `1` (which spans uninitialized padding
    bytes at offsets `1..3`). -/
def badWholeWordAluOnPaddedBody : X86Body where
  adts := [paddedAdtDecl]
  argTys := [.adt 1]
  retTy := .adt 1
  slotCount := 2
  blocks := [
    { instrs := [
        .alu .add 8 ⟨0⟩ 0 (.slotSlice ⟨1⟩ 0 8 false) (.immWord 8 1)
      ]
      term := .ret }
  ]

/-- Negative adequacy canary 1: executing an 8-byte ALU operation (`add`) across
    `samplePaddedBytes` (`[some 10, none, none, none, some 1, some 0, some 0, some 0]`)
    triggers `.failed .ub` at step `1` because `decodeLeBytes` encounters `none`
    at offset `1`, refuting `CrateTheorem`! -/
theorem canary_alu_on_uninit_padding_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn badWholeWordAluOnPaddedBody) :
    ¬ CrateTheorem {
      adts := [paddedAdtDecl]
      libInv := defaultLibInv [paddedAdtDecl]
      functions := [{ name := fnName, prog := badWholeWordAluOnPaddedBody }]
      tcb := [TCBItem.assemblerLowering fnName badWholeWordAluOnPaddedBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let retBlk0 : AllocBlock := {
    perm := .readWrite
    size := 8
    bytes := replicateBytes 8 none
    ptr := none
    written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite
    size := 8
    bytes := samplePaddedBytes
    ptr := none
    written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hrest : ∀ j, 2 ≤ j → mem0 j = unallocBlock := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hinit : initX86State badWholeWordAluOnPaddedBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨samplePaddedBytes, rfl, samplePaddedBytes_hasTy⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) badWholeWordAluOnPaddedBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 1 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [paddedAdtDecl])
        { name := fnName, prog := badWholeWordAluOnPaddedBody } q :=
    ⟨hmono, True.intro, ⟨samplePaddedBytes, rfl, samplePaddedBytes_hasTy⟩, True.intro⟩
  have hr0 : ReachesPrefix X86Machine badWholeWordAluOnPaddedBody s0 1 s0 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s0 .ub rfl
  exact (hWF q hpre).1 hinit [] (.failed .ub) hr0

/-!
## 9. Experiment 2: Spatial Provenance & Cross-Slot Out-of-Bounds Pointer Arithmetic UB
-/

/-- `X86Body` that allocates and initializes adjacent stack slot `2` (8 bytes),
    takes a pointer to stack slot `1` (`Ptr ⟨1⟩ 0`), adds 8 bytes via
    `addPtrOffset` (`Ptr ⟨1⟩ 8`—which in a flat unguarded address space would be
    the address of slot `2`!), and attempts to load 8 bytes through `Ptr ⟨1⟩ 8`. -/
def oobCrossSlotLoadBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .movSlice ⟨2⟩ 0 (.immWord 8 77),
        .allocSlot ⟨3⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0,
        .addPtrOffset ⟨3⟩ ⟨3⟩ 8,
        .loadPtr ⟨0⟩ 0 ⟨3⟩ 8
      ]
      term := .ret }
  ]

/-- Negative adequacy canary 2A: stepping 8 bytes past the base of 8-byte stack
    slot `1` (`Ptr ⟨1⟩ 8`) and executing `loadPtr` triggers immediate `.failed .ub`
    instead of reading adjacent stack slot `2`, refuting `CrateTheorem`! -/
theorem canary_oob_ptr_load_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn oobCrossSlotLoadBody) :
    ¬ CrateTheorem {
      functions := [{ name := fnName, prog := oobCrossSlotLoadBody }]
      tcb := [TCBItem.assemblerLowering fnName oobCrossSlotLoadBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let inBs := encodeLeBytes 8 42
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := inBs, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hrest : ∀ j, 2 ≤ j → mem0 j = unallocBlock := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hinit : initX86State oobCrossSlotLoadBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨inBs, rfl, ⟨rfl, True.intro⟩⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) oobCrossSlotLoadBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 6 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [])
        { name := fnName, prog := oobCrossSlotLoadBody } q :=
    ⟨hmono, True.intro, ⟨inBs, rfl, ⟨rfl, True.intro⟩⟩, True.intro⟩
  let s1 : X86State := {
    s0 with
    mem := updateAlloc mem0 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 1
  }
  let s2 : X86State := {
    s1 with
    mem := updateAlloc s1.mem 2 { perm := .readWrite, size := 8, bytes := encodeLeBytes 8 77, ptr := none, written := true }
    ip := 2
  }
  let s3 : X86State := {
    s2 with
    mem := updateAlloc s2.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 3
  }
  let s4 : X86State := {
    s3 with
    mem := updateAlloc s3.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
    ip := 4
  }
  let s5 : X86State := {
    s4 with
    mem := updateAlloc s4.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 8 }, written := true }
    ip := 5
  }
  have hr5 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 1 s5 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s5 .ub rfl
  have hr4 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 2 s4 [()] (.failed .ub) :=
    ReachesPrefix.step 1 s4 s5 () [] (.failed .ub) rfl hr5
  have hr3 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 3 s3 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s3 s4 () [()] (.failed .ub) rfl hr4
  have hr2 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 4 s2 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s2 s3 () [(), ()] (.failed .ub) rfl hr3
  have hr1 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 5 s1 [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s1 s2 () [(), (), ()] (.failed .ub) rfl hr2
  have hr0 : ReachesPrefix X86Machine oobCrossSlotLoadBody s0 6 s0 [(), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 5 s0 s1 () [(), (), (), ()] (.failed .ub) rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), (), ()] (.failed .ub) hr0

/-- `X86Body` that takes a pointer to stack slot `1` (`Ptr ⟨1⟩ 0`), adds 8 bytes
    via `addPtrOffset` (`Ptr ⟨1⟩ 8`), and attempts to store 8 bytes through
    `Ptr ⟨1⟩ 8` (attempting to overwrite adjacent stack slot `2`). -/
def oobCrossSlotStoreBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .movSlice ⟨2⟩ 0 (.immWord 8 77),
        .allocSlot ⟨3⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0,
        .addPtrOffset ⟨3⟩ ⟨3⟩ 8,
        .storePtr ⟨3⟩ (.immWord 8 99),
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨2⟩ 0 8 false)
      ]
      term := .ret }
  ]

/-- Negative adequacy canary 2B: attempting to store through an out-of-bounds
    pointer `Ptr ⟨1⟩ 8` triggers `.failed .ub` at the `storePtr` step and never
    overwrites adjacent stack slot `2`! -/
theorem canary_oob_ptr_store_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn oobCrossSlotStoreBody) :
    ¬ CrateTheorem {
      functions := [{ name := fnName, prog := oobCrossSlotStoreBody }]
      tcb := [TCBItem.assemblerLowering fnName oobCrossSlotStoreBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let inBs := encodeLeBytes 8 42
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := inBs, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hrest : ∀ j, 2 ≤ j → mem0 j = unallocBlock := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hinit : initX86State oobCrossSlotStoreBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨inBs, rfl, ⟨rfl, True.intro⟩⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) oobCrossSlotStoreBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 6 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [])
        { name := fnName, prog := oobCrossSlotStoreBody } q :=
    ⟨hmono, True.intro, ⟨inBs, rfl, ⟨rfl, True.intro⟩⟩, True.intro⟩
  let s1 : X86State := {
    s0 with
    mem := updateAlloc mem0 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 1
  }
  let s2 : X86State := {
    s1 with
    mem := updateAlloc s1.mem 2 { perm := .readWrite, size := 8, bytes := encodeLeBytes 8 77, ptr := none, written := true }
    ip := 2
  }
  let s3 : X86State := {
    s2 with
    mem := updateAlloc s2.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 3
  }
  let s4 : X86State := {
    s3 with
    mem := updateAlloc s3.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
    ip := 4
  }
  let s5 : X86State := {
    s4 with
    mem := updateAlloc s4.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 8 }, written := true }
    ip := 5
  }
  have hr5 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 1 s5 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s5 .ub rfl
  have hr4 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 2 s4 [()] (.failed .ub) :=
    ReachesPrefix.step 1 s4 s5 () [] (.failed .ub) rfl hr5
  have hr3 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 3 s3 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s3 s4 () [()] (.failed .ub) rfl hr4
  have hr2 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 4 s2 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s2 s3 () [(), ()] (.failed .ub) rfl hr3
  have hr1 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 5 s1 [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s1 s2 () [(), (), ()] (.failed .ub) rfl hr2
  have hr0 : ReachesPrefix X86Machine oobCrossSlotStoreBody s0 6 s0 [(), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 5 s0 s1 () [(), (), (), ()] (.failed .ub) rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), (), ()] (.failed .ub) hr0

/-- Positive spatial-provenance contrast: taking a pointer to `_1 : Padded`
    (`Ptr ⟨1⟩ 0`), adding an **in-bounds** 4-byte field offset via
    `addPtrOffset ⟨3⟩ ⟨3⟩ 4` (`Ptr ⟨1⟩ 4`), and loading 4 bytes (`width := 4`)
    into return slot `0` (`retTy := .u32`) succeeds without UB because
    `4 + 4 ≤ 8`! -/
def inboundsPtrFieldLoadBody : X86Body where
  adts := [paddedAdtDecl]
  argTys := [.adt 1]
  retTy := .u32
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨3⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0,
        .addPtrOffset ⟨3⟩ ⟨3⟩ 4,
        .loadPtr ⟨0⟩ 0 ⟨3⟩ 4,
        .deallocSlot ⟨3⟩
      ]
      term := .ret }
  ]

theorem inboundsPtrFieldLoadBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := inboundsPtrFieldLoadBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv [paddedAdtDecl]) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [paddedAdtDecl])) := by
  intro fn
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out _ hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : bb0 = 0 := hinit.1
    have hs : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hmem0_0 := hinit.2.2.2.2.1
    subst hb hs hc hst
    cases hinit.2.2.2.2.2.1 with
    | intro bs hbs =>
      have hmem0_1 := hbs.1
      have hbsty := hbs.2
      cases padded_hasTy_decompose tySizes0 bs hbsty with
      | intro a0 h1 =>
      cases h1 with
      | intro p1 h2 =>
      cases h2 with
      | intro p2 h3 =>
      cases h3 with
      | intro p3 h4 =>
      cases h4 with
      | intro c0 h5 =>
      cases h5 with
      | intro c1 h6 =>
      cases h6 with
      | intro c2 h7 =>
      cases h7 with
      | intro c3 hbs_eq =>
        subst hbs_eq
        let inBytes : ByteVec :=
          [some a0, p1, p2, p3, some c0, some c1, some c2, some c3]
        refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
        let m1 := updateAlloc mem0 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
        have hm1_1 : m1 1 = { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true } :=
          hmem0_1
        let s1 : X86State := { mem := m1, bb := 0, ip := 1, tySizes := tySizes0 }
        let m2 := updateAlloc m1 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
        let s2 : X86State := { mem := m2, bb := 0, ip := 2, tySizes := tySizes0 }
        have hstep1 : evalX86Step inboundsPtrFieldLoadBody s1 = .step () s2 := by
          change evalX86Instr s1 (.leaSlot ⟨3⟩ ⟨1⟩ 0) = .step () s2
          dsimp only [evalX86Instr, s1]
          rw [hm1_1]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep1 hr1 (fun _ _ hr2 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
        let m3 := updateAlloc m2 3
          { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 4 }, written := true }
        have hm3_1 : m3 1 = { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true } :=
          hmem0_1
        have hm3_0 : m3 0 = { perm := .readWrite, size := 4, bytes := replicateBytes 4 none, ptr := none, written := false } :=
          hmem0_0
        have hm0_0 : mem0 0 = { perm := .readWrite, size := 4, bytes := replicateBytes 4 none, ptr := none, written := false } :=
          hmem0_0
        have hm0_1 : mem0 1 = { perm := .readWrite, size := 8, bytes := inBytes, ptr := none, written := true } :=
          hmem0_1
        let s3 : X86State := { mem := m3, bb := 0, ip := 3, tySizes := tySizes0 }
        let m4 := updateAlloc m3 0
          { perm := .readWrite, size := 4, bytes := [some c0, some c1, some c2, some c3], ptr := none, written := true }
        let s4 : X86State := { mem := m4, bb := 0, ip := 4, tySizes := tySizes0 }
        have hstep3 : evalX86Step inboundsPtrFieldLoadBody s3 = .step () s4 := by
          change evalX86Instr s3 (.loadPtr ⟨0⟩ 0 ⟨3⟩ 4) = .step () s4
          dsimp only [evalX86Instr, readSlice, writeSliceMem, updateAlloc, s3, m3, m2, m1]
          rw [hm0_1, hm0_0]
          rfl
        refine reachesPrefix_safeAndEnsures_of_step hstep3 hr3 (fun _ _ hr4 => ?_)
        refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
        exact reachesPrefix_safeAndEnsures_of_normal
          (v := [some c0, some c1, some c2, some c3]) rfl hr5
          ⟨rfl, True.intro⟩

theorem prove_inbounds_ptr_field_load_crate (fnName : String) :
    CrateTheorem {
      adts := [paddedAdtDecl]
      libInv := defaultLibInv [paddedAdtDecl]
      functions := [{ name := fnName, prog := inboundsPtrFieldLoadBody }]
      tcb := [TCBItem.assemblerLowering fnName inboundsPtrFieldLoadBody]
    } :=
  verify_single_fn_wf_crate [paddedAdtDecl] fnName inboundsPtrFieldLoadBody
    (inboundsPtrFieldLoadBody_verified fnName)

/-!
## 10. Experiment 3 — Polymorphic `transmute_copy<Src, Dst>` on the Unified Byte-Addressed Machine
-/

theorem nat_beq_refl : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | k + 1 => nat_beq_refl k

theorem eq_of_nat_beq_eq_true : {a b : Nat} → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (eq_of_nat_beq_eq_true h)

theorem nat_ble_refl : (n : Nat) → Nat.ble n n = true
  | 0 => rfl
  | k + 1 => nat_ble_refl k

/-- PME `const { assert!(size_of::<Src>() == size_of::<Dst>()) }` body on the
    byte-addressed x86-64 machine:
    - `bb0`: allocates slot `1` (`bool`, 1 byte) and executes
      `cmpSizeEqJmp ⟨1⟩ (.param 0) (.param 1) ⟨1⟩`.
    - `bb1`: branches on the 1-byte boolean in slot `1` via `jccBool` to `bb2`
      (success) or `bb3` (`abortPanic`). -/
def sizeEqConstBody : X86Body where
  argTys := []
  retTy := .unit
  slotCount := 2
  blocks := [
    { instrs := [.allocSlot ⟨1⟩ 1]
      term := .cmpSizeEqJmp ⟨1⟩ (.param 0) (.param 1) ⟨1⟩ },
    { instrs := []
      term := .jccBool (.slotSlice ⟨1⟩ 0 1 true) ⟨3⟩ ⟨2⟩ },
    { instrs := [
        .movSlice ⟨0⟩ 0 .immUnit,
        .deallocSlot ⟨1⟩
      ]
      term := .ret },
    { instrs := []
      term := .abortPanic }
  ]

/-- Key PME soundness lemma on the byte-addressed machine: if CTFE of
    `sizeEqConstBody` succeeds under `tySizes`, then `Src` and `Dst` have equal
    byte size (`tySizes 0 = tySizes 1`). -/
theorem constSucceeds_sizeEqConstBody_imp_eq (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 := by
  cases h with
  | intro s0 h1 =>
  cases s0 with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : tySizes0 = tySizes := h4.1
    have hinit := h4.2.1
    have hreach := h4.2.2
    have hb : bb0 = 0 := hinit.1
    have hs : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hts hb hs hc hst
    cases hbeq : Nat.beq (tySizes0 0) (tySizes0 1) with
    | true => exact eq_of_nat_beq_eq_true hbeq
    | false =>
      refine False.elim ?_
      refine reachesPrefix_not_normal_of_step rfl hreach (fun _ _ hr1 => ?_)
      let m1 := updateAlloc mem0 1
        { perm := .readWrite, size := 1, bytes := [none], ptr := none, written := false }
      let m2 := updateAlloc m1 1
        { perm := .readWrite, size := 1, bytes := [some 0], ptr := none, written := true }
      let s1 : X86State := { mem := m1, bb := 0, ip := 1, tySizes := tySizes0 }
      let s2 : X86State := { mem := m2, bb := 1, ip := 0, tySizes := tySizes0 }
      have hstep1 : evalX86Step sizeEqConstBody s1 = .step () s2 := by
        change evalX86Term [] s1 (.cmpSizeEqJmp ⟨1⟩ (.param 0) (.param 1) ⟨1⟩) = .step () s2
        dsimp only [evalX86Term, evalX86TyByteSize, writeSliceMem, updateAlloc, s1, m1]
        rw [hbeq]
        rfl
      refine reachesPrefix_not_normal_of_step hstep1 hr1 (fun _ _ hr2 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_normal_of_unwind rfl hr3

/-- Polymorphic `pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst`
    compiled to the byte-addressed x86-64 machine, gated by
    `requiredConsts := [sizeEqConstBody]`:
    - `bb0`: evaluates the unit const block into slot `2`, allocates pointer
      slots `3` and `4` (size 8), takes the provenance pointer of `x` (`slot 1`,
      offset 0) into slot `4`, reborrows into slot `3`, and executes
      `repMovsbJmp ⟨0⟩ (.param 0) (.param 1) ⟨3⟩ ⟨1⟩` to copy the raw `ByteVec`
      of `Src` (including any initialized or uninitialized `none` padding bytes)
      into return slot `0`. -/
def transmuteCheckedBody : X86Body where
  argTys := [.param 0]
  retTy := .param 1
  slotCount := 5
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 0,
        .movSlice ⟨2⟩ 0 .immUnit,
        .deallocSlot ⟨2⟩,
        .allocSlot ⟨3⟩ 8,
        .allocSlot ⟨4⟩ 8,
        .leaSlot ⟨4⟩ ⟨1⟩ 0,
        .reborrowSlot ⟨3⟩ ⟨4⟩
      ]
      term := .repMovsbJmp ⟨0⟩ (.param 0) (.param 1) ⟨3⟩ ⟨1⟩ },
    { instrs := [
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩
      ]
      term := .ret }
  ]
  requiredConsts := [sizeEqConstBody]

/-- Theorem 3 (Polymorphic `transmute_copy<Src, Dst>` on the Unified
    Byte-Addressed Machine):
    `transmuteCheckedBody` satisfies `EnsuresRetLibInv (defaultLibInv []) (.param 1)`
    on its canonical `effectivePre`: PME admission guarantees
    `tySizes 0 = tySizes 1`, so `rep movsb` copies the exact `ByteVec` `bs`
    (arbitrary initialized/uninitialized bytes of `Src`) into return slot `0`
    without triggering `.ub`. -/
theorem transmuteCheckedBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := transmuteCheckedBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv []) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [])) := by
  intro fn
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  cases q with
  | mk init steps =>
  cases init with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
  cases out with
  | mk trace outcome =>
    have hinit := hpfx.1
    have hreach := hpfx.2
    have hb : bb0 = 0 := hinit.1
    have hs : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hmem0_0 := hinit.2.2.2.2.1
    subst hb hs hc hst
    have hconst : ConstSucceeds tySizes0 sizeEqConstBody :=
      hpre.1 sizeEqConstBody (.direct (.head _))
    have heq : tySizes0 0 = tySizes0 1 :=
      constSucceeds_sizeEqConstBody_imp_eq tySizes0 hconst
    cases hinit.2.2.2.2.2.1 with
    | intro bs hbs =>
      have hm0_0 : mem0 0 = {
          perm := .readWrite
          size := tySizes0 1
          bytes := replicateBytes (tySizes0 1) none
          ptr := none
          written := false
        } := hmem0_0
      have hm0_1 : mem0 1 = {
          perm := .readWrite
          size := tySizes0 0
          bytes := bs
          ptr := none
          written := true
        } := hbs.1
      have hbs_len : bs.length = tySizes0 0 := hbs.2
      refine reachesPrefix_safeAndEnsures_of_step rfl hreach (fun _ _ hr1 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr1 (fun _ _ hr2 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr2 (fun _ _ hr3 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr3 (fun _ _ hr4 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr4 (fun _ _ hr5 => ?_)
      let m5 := updateAlloc (updateAlloc (updateAlloc (updateAlloc (updateAlloc mem0 2
        { perm := .readWrite, size := 0, bytes := [], ptr := none, written := false }) 2
        { perm := .readWrite, size := 0, bytes := [], ptr := none, written := true }) 2
        unallocBlock) 3
        { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }) 4
        { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
      let s5 : X86State := { mem := m5, bb := 0, ip := 5, tySizes := tySizes0 }
      let m6 := updateAlloc m5 4
        { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
      let s6 : X86State := { mem := m6, bb := 0, ip := 6, tySizes := tySizes0 }
      have hstep5 : evalX86Step transmuteCheckedBody s5 = .step () s6 := by
        change evalX86Instr s5 (.leaSlot ⟨4⟩ ⟨1⟩ 0) = .step () s6
        dsimp only [evalX86Instr, updateAlloc, s5, m5]
        rw [hm0_1]
        rfl
      refine reachesPrefix_safeAndEnsures_of_step hstep5 hr5 (fun _ _ hr6 => ?_)
      let m7 := updateAlloc m6 3
        { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
      let s7 : X86State := { mem := m7, bb := 0, ip := 7, tySizes := tySizes0 }
      have hstep6 : evalX86Step transmuteCheckedBody s6 = .step () s7 := by
        change evalX86Instr s6 (.reborrowSlot ⟨3⟩ ⟨4⟩) = .step () s7
        dsimp only [evalX86Instr, updateAlloc, s6, m6, m5]
        rw [hm0_1]
        rfl
      refine reachesPrefix_safeAndEnsures_of_step hstep6 hr6 (fun _ _ hr7 => ?_)
      let m7_deinit := updateAlloc m7 3
        { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
      let m8 := updateAlloc m7_deinit 0
        { perm := .readWrite, size := tySizes0 1, bytes := bs, ptr := none, written := true }
      let s8 : X86State := { mem := m8, bb := 1, ip := 0, tySizes := tySizes0 }
      have hbeq_sz : Nat.beq (tySizes0 0) (tySizes0 1) = true := by
        rw [← heq]
        exact nat_beq_refl (tySizes0 0)
      have hble_sz : Nat.ble (tySizes0 0) (tySizes0 0) = true :=
        nat_ble_refl (tySizes0 0)
      have hble_bs : Nat.ble (tySizes0 0) bs.length = true := by
        rw [hbs_len]
        exact nat_ble_refl (tySizes0 0)
      have hext : extractSlice bs 0 (tySizes0 0) = bs :=
        extractSlice_zero_of_eq_length bs (tySizes0 0) hbs_len
      have hble_dst_sz : Nat.ble bs.length (tySizes0 1) = true := by
        rw [hbs_len, ← heq]
        exact nat_ble_refl (tySizes0 0)
      have hble_dst_rep : Nat.ble bs.length (replicateBytes (tySizes0 1) (none : Option UInt8)).length = true := by
        rw [replicateBytes_length, hbs_len, ← heq]
        exact nat_ble_refl (tySizes0 0)
      have hwrite : writeSlice (replicateBytes (tySizes0 1) (none : Option UInt8)) 0 bs = bs := by
        refine writeSlice_zero_of_eq_length _ bs ?_
        rw [replicateBytes_length, hbs_len, heq]
      have hstep7 : evalX86Step transmuteCheckedBody s7 = .step () s8 := by
        change evalX86Term [] s7 (.repMovsbJmp ⟨0⟩ (.param 0) (.param 1) ⟨3⟩ ⟨1⟩) = .step () s8
        dsimp only [evalX86Term, evalRepMovsb, evalX86TyByteSize, readSlice, writeSliceMem,
          updateAlloc, BytePerm.canRead, BytePerm.canWrite, and, Nat.add_zero, s7, m7, m6, m5]
        rw [hbeq_sz, hm0_1, hm0_0]
        dsimp only [BytePerm.canRead, BytePerm.canWrite, and, Nat.add_zero]
        rw [hble_sz, hble_bs, hext]
        dsimp only [and, Nat.add_zero]
        rw [hble_dst_sz, hble_dst_rep, hwrite]
      refine reachesPrefix_safeAndEnsures_of_step hstep7 hr7 (fun _ _ hr8 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr8 (fun _ _ hr9 => ?_)
      refine reachesPrefix_safeAndEnsures_of_step rfl hr9 (fun _ _ hr10 => ?_)
      let m10 := updateAlloc (updateAlloc m8 4 unallocBlock) 3 unallocBlock
      let s10 : X86State := { mem := m10, bb := 1, ip := 2, tySizes := tySizes0 }
      have hbeq_ret : Nat.beq bs.length (tySizes0 1) = true := by
        rw [hbs_len, ← heq]
        exact nat_beq_refl (tySizes0 0)
      have hstep10 : evalX86Step transmuteCheckedBody s10 = .terminated (.normal bs) := by
        change evalX86Term [] s10 .ret = .terminated (.normal bs)
        dsimp only [evalX86Term, updateAlloc, s10, m10, m8]
        rw [hbeq_ret]
        rfl
      exact reachesPrefix_safeAndEnsures_of_normal
        (v := bs) hstep10 hr10 (hbs_len.trans heq)

/-- Ready-to-apply `CrateTheorem` witness for `transmuteCheckedBody` on the
    unified byte-addressed machine. -/
theorem prove_pme_transmute_single_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := transmuteCheckedBody }]
      tcb := [TCBItem.assemblerLowering fnName transmuteCheckedBody]
    } :=
  verify_single_fn_wf_crate [] fnName transmuteCheckedBody
    (transmuteCheckedBody_verified fnName)

/-- Unchecked `transmute_copy<Src, Dst>` body (`requiredConsts := []`) that
    omits `sizeEqConstBody`. -/
def transmuteUncheckedBody : X86Body where
  argTys := [.param 0]
  retTy := .param 1
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0,
        .reborrowSlot ⟨2⟩ ⟨3⟩
      ]
      term := .repMovsbJmp ⟨0⟩ (.param 0) (.param 1) ⟨2⟩ ⟨1⟩ },
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩
      ]
      term := .ret }
  ]
  requiredConsts := []

/-- Negative adequacy canary 3: `transmuteUncheckedBody` (missing the PME
    `sizeEqConstBody` obligation) triggers `.failed .ub` at step `5` when
    instantiated with `Src` of size `1` and `Dst` of size `2`, refuting
    `CrateTheorem`! -/
theorem canary_transmuteUnchecked_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn transmuteUncheckedBody) :
    ¬ CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := transmuteUncheckedBody }]
      tcb := [TCBItem.assemblerLowering fnName transmuteUncheckedBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let tySizesBad : Nat → Nat := fun idx =>
    match idx with
    | 0 => 1
    | _ => 2
  let retBlk0 : AllocBlock := {
    perm := .readWrite
    size := 2
    bytes := [none, none]
    ptr := none
    written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite
    size := 1
    bytes := [some 42]
    ptr := none
    written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0, tySizes := tySizesBad }
  have hrest : ∀ j, 2 ≤ j → mem0 j = unallocBlock := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hinit : initX86State transmuteUncheckedBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨[some 42], rfl, rfl⟩, hrest⟩⟩
  have hmono : MonoAdmitted tySizesBad transmuteUncheckedBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ htail =>
        cases htail with
        | head => cases hterm
        | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 5 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [])
        { name := fnName, prog := transmuteUncheckedBody } q :=
    ⟨hmono, True.intro, ⟨[some 42], rfl, rfl⟩, True.intro⟩
  let s1 : X86State := {
    s0 with
    mem := updateAlloc mem0 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 1
  }
  let s2 : X86State := {
    s1 with
    mem := updateAlloc s1.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false }
    ip := 2
  }
  let s3 : X86State := {
    s2 with
    mem := updateAlloc s2.mem 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
    ip := 3
  }
  let s4 : X86State := {
    s3 with
    mem := updateAlloc s3.mem 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
    ip := 4
  }
  have hr4 : ReachesPrefix X86Machine transmuteUncheckedBody s0 1 s4 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s4 .ub rfl
  have hr3 : ReachesPrefix X86Machine transmuteUncheckedBody s0 2 s3 [()] (.failed .ub) :=
    ReachesPrefix.step 1 s3 s4 () [] (.failed .ub) rfl hr4
  have hr2 : ReachesPrefix X86Machine transmuteUncheckedBody s0 3 s2 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s2 s3 () [()] (.failed .ub) rfl hr3
  have hr1 : ReachesPrefix X86Machine transmuteUncheckedBody s0 4 s1 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s1 s2 () [(), ()] (.failed .ub) rfl hr2
  have hr0 : ReachesPrefix X86Machine transmuteUncheckedBody s0 5 s0 [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s0 s1 () [(), (), ()] (.failed .ub) rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), ()] (.failed .ub) hr0

end ByteMemoryProvenanceProbe
