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
# Phase 3 Semantics & Syntax-Directed Byte VCGen Probe (`Phase3SemanticsProbe.lean`)

Round 2 — Question R2-3: Niche-Encoded Enums, Wide Slice Pointers (`&[T]`),
`copy_nonoverlapping` Disjointness, Signed/Unsigned Casts, and Syntax-Directed
`wpByteX86` on the Unified Byte-Addressed Provenance Machine.

This standalone `prelude`-only Lean 4.34.1 file mechanizes:
1. `Trusted.Refinement` and `Trusted.StepResult` (exact copies of the Phase 1–2
   TCB foundations).
2. Unified byte-addressed provenance memory (`AllocBlock` with `BytePerm`,
   `size : Nat`, `bytes : List (Option UInt8)`, `ptr : Option Ptr`, and
   `written : Bool`), extended with spatial disjointness checking
   (`ptrsNonOverlapping`, `evalCopyNonOverlapping`), wide slice metadata
   (`ptrMetadata`, `ptrOffsetIndex`, `makeSlice`), enum discriminant extraction
   (`evalDiscriminant` for both `TagEncoding::Direct` and `TagEncoding::Niche`),
   and byte-level width casts (`movzx`, `movsx`, `truncate`).
3. Canonical entry-state folding (`updateAlloc_eq_self`, `forallTypedByteArgs`,
   `initX86State_canonical`) that preserves caller-frame pointee allocations
   while reducing all parameter and local slot accesses by `rfl`.
4. Syntax-directed weakest-precondition (`wpByteX86`, `wpByteX86_sound`) and
   normal-termination necessity (`necByteX86Normal`, `necByteX86Normal_sound`)
   generators for the byte-addressed provenance machine.
5. Machine-checked positive `CrateTheorem` witnesses and negative adequacy
   canaries (`¬ CrateTheorem`) across all four Phase 3 semantic domains with
   zero `sorry` and zero custom axioms.
-/

namespace Phase3SemanticsProbe

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
  Phase3SemanticsProbe.Behavior L.Query L.Out

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
## 2. Unified Byte-Addressed Memory, Spatial Disjointness, and Width Casts
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
    a byte offset (`offset`) relative to that allocation's base address. -/
structure Ptr where
  alloc : SlotId
  offset : Nat

def Ptr.addOffset (p : Ptr) (delta : Nat) : Ptr :=
  { p with offset := p.offset + delta }

/-- A byte sequence where each byte is either initialized (`some b`) or
    uninitialized / padding (`none`). -/
abbrev ByteVec := List (Option UInt8)

/-- Isolated byte-addressed allocation block for a stack slot or caller buffer. -/
structure AllocBlock where
  perm : BytePerm := .unallocated
  size : Nat := 0
  bytes : ByteVec := []
  ptr : Option Ptr := none
  written : Bool := false

/-- Unallocated block default. -/
def unallocBlock : AllocBlock :=
  { perm := .unallocated, size := 0, bytes := [], ptr := none, written := false }

/-- Initialized return block default before any return value is written. -/
def initRetBlock (retSz : Nat) : AllocBlock where
  perm := .readWrite
  size := retSz
  bytes :=
    let rec loop : Nat → ByteVec
      | 0 => []
      | k + 1 => none :: loop k
    loop retSz
  ptr := none
  written := false

/-- Replicate a byte value `n` times. -/
def replicateBytes (n : Nat) (v : Option UInt8) : ByteVec :=
  match n with
  | 0 => []
  | k + 1 => v :: replicateBytes k v

/-- Drop the first `n` elements of a list. -/
def dropBytes (n : Nat) (xs : List α) : List α :=
  match n with
  | 0 => xs
  | k + 1 =>
    match xs with
    | [] => []
    | _ :: rest => dropBytes k rest

/-- Take the first `n` elements of a list. -/
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

/-- Overwrite a contiguous slice starting at `offset` with `patch`. -/
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

/-- Boolean check that every byte in a `ByteVec` is initialized (`some _`). -/
def allBytesInitBool : ByteVec → Bool
  | [] => true
  | none :: _ => false
  | some _ :: rest => allBytesInitBool rest

/-- Return the most-significant (last) byte in a little-endian `ByteVec`. -/
def lastByte : ByteVec → Option UInt8
  | [] => none
  | [b] => b
  | _ :: rest => lastByte rest

/-- Byte-level zero-extension (`movzx`): extends an initialized non-empty
    `src : ByteVec` to `dstWidth` bytes by appending `some 0` bytes. Returns
    `none` (triggering `.failed .ub`) if any byte in `src` is `none`. -/
def evalZeroExtend (dstWidth : Nat) (src : ByteVec) : Option ByteVec :=
  match allBytesInitBool src && Nat.ble 1 src.length && Nat.ble src.length dstWidth with
  | true =>
    some (src ++ replicateBytes (dstWidth - src.length) (some 0))
  | false => none

/-- Byte-level sign-extension (`movsx`): extends an initialized non-empty
    little-endian `src : ByteVec` to `dstWidth` bytes by replicating the sign bit
    (bit 7 of the most-significant byte: `255` if `msb ≥ 128`, else `0`).
    Returns `none` (triggering `.failed .ub`) if any byte in `src` is `none`. -/
def evalSignExtend (dstWidth : Nat) (src : ByteVec) : Option ByteVec :=
  match allBytesInitBool src && Nat.ble 1 src.length && Nat.ble src.length dstWidth with
  | true =>
    match lastByte src with
    | some msb =>
      let signFill : UInt8 :=
        match Nat.ble 128 msb.toNat with
        | true => 255
        | false => 0
      some (src ++ replicateBytes (dstWidth - src.length) (some signFill))
    | none => none
  | false => none

/-- Byte-level truncation: takes the low `dstWidth` bytes of an initialized
    little-endian `src : ByteVec`. Returns `none` if any byte in `src` is `none`
    or `dstWidth > src.length`. -/
def evalTruncate (dstWidth : Nat) (src : ByteVec) : Option ByteVec :=
  match allBytesInitBool src && Nat.ble dstWidth src.length with
  | true => some (takeBytes dstWidth src)
  | false => none

/-- Update allocation `target` in `mem`, leaving all other allocations unchanged. -/
def updateAlloc (mem : Nat → AllocBlock) (target : Nat)
    (blk : AllocBlock) : Nat → AllocBlock :=
  fun i =>
    match Nat.beq i target with
    | true => blk
    | false => mem i

/-- Read `width` bytes from `mem` at provenance pointer `p`. -/
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

/-- Spatial disjointness check for `core::intrinsics::copy_nonoverlapping`:
    returns `true` iff `src` and `dst` belong to distinct allocations, or
    `byteCount == 0`, or the byte intervals `[src.offset, src.offset + byteCount)`
    and `[dst.offset, dst.offset + byteCount)` within the same allocation do not
    overlap. -/
def ptrsNonOverlapping (src dst : Ptr) (byteCount : Nat) : Bool :=
  !Nat.beq src.alloc.index dst.alloc.index ||
  Nat.beq byteCount 0 ||
  Nat.ble (byteCount + src.offset) dst.offset ||
  Nat.ble (byteCount + dst.offset) src.offset

/-- Evaluate `copy_nonoverlapping(src, dst, byteCount)`:
    verifies that both pointer slots hold readable, initialized provenance
    pointers `srcPtr` and `dstPtr`, checks `ptrsNonOverlapping srcPtr dstPtr byteCount`,
    reads `byteCount` bytes from `srcPtr`, and writes them to `dstPtr`. -/
def evalCopyNonOverlapping (mem : Nat → AllocBlock)
    (dstPtrSlot srcPtrSlot : SlotId) (byteCount : Nat) :
    Option (Nat → AllocBlock) :=
  let srcPtrBlk := mem srcPtrSlot.index
  let dstPtrBlk := mem dstPtrSlot.index
  match srcPtrBlk.perm.canRead && srcPtrBlk.written &&
        dstPtrBlk.perm.canRead && dstPtrBlk.written with
  | true =>
    match srcPtrBlk.ptr, dstPtrBlk.ptr with
    | some srcPtr, some dstPtr =>
      match ptrsNonOverlapping srcPtr dstPtr byteCount with
      | true =>
        match readSlice mem srcPtr byteCount with
        | some copiedBytes =>
          writeSliceMem mem dstPtr copiedBytes
        | none => none
      | false => none
    | _, _ => none
  | false => none

/-!
## 3. Generalized `X86Ty`, Struct & Enum `AdtDecl` (`Direct` vs `Niche`), Slice Types, and `AdmissibleLibInv`
-/

inductive FieldAccess where
  | pubSafe
  | priv
  | unsafeField

inductive X86Ty where
  | u8
  | i8
  | u16
  | u32
  | usize
  | isize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)
  | slice (elemTy : X86Ty)

/-- Single field declaration inside a multi-field struct (`AdtDecl`). -/
structure FieldDecl where
  offset : Nat
  size : Nat
  ty : X86Ty
  access : FieldAccess

/-- Shape of an ADT declaration in Phase 3:
    - `structDecl fields nonExhaustive`: multi-field struct (potentially with
      inter-field or trailing alignment padding).
    - `directOption payloadTy`: direct-tagged `Option<T>` (`TagEncoding::Direct`,
      total size 16B: 8B discriminant tag `0` or `1` at offset `0..8`, and
      `payloadTy` at offset `8..16` when tag is `1`, or unconstrained padding
      when tag is `0`).
    - `nicheOption nicheVal payloadAdtId`: niche-encoded `Option<T>`
      (`TagEncoding::Niche`, total size 8B: `nicheVal` at offset `0..8` encodes
      `None` with logical discriminant `0`, and any other 8B initialized value
      encodes `Some(payload)` with logical discriminant `1` at offset `0..8`). -/
inductive AdtShape where
  | structDecl (fields : List FieldDecl) (nonExhaustive : Bool := false)
  | directOption (payloadTy : X86Ty)
  | nicheOption (nicheVal : Nat) (payloadAdtId : Nat)

/-- Captured ADT (struct or enum) declaration. -/
structure AdtDecl where
  id : Nat
  size : Nat
  shape : AdtShape

def FieldDecl.isPubSafe (f : FieldDecl) : Bool :=
  match f.access with
  | .pubSafe => true
  | .priv | .unsafeField => false

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
  | .u8 | .i8 => 1
  | .u16 => 2
  | .u32 => 4
  | .usize | .isize => 8
  | .bool => 1
  | .unit => 0
  | .adt id =>
    match lookupAdt adts id with
    | some decl => decl.size
    | none => 0
  | .param idx => tySizes idx
  | .refParam _ => 8
  | .slice _ => 16

/-- Conjunction asserting that every field slice `(f.offset, f.size)` of `bytes`
    satisfies `pred f.ty (extractSlice bytes f.offset f.size)`. -/
def allFieldsSatisfy (pred : X86Ty → ByteVec → Prop)
    (bytes : ByteVec) : List FieldDecl → Prop
  | [] => True
  | f :: fs =>
    pred f.ty (extractSlice bytes f.offset f.size) ∧
    allFieldsSatisfy pred bytes fs

/-- Dynamic language-level ABI type-validity relation for scalar, slice, and
    polymorphic parameter field types (`V_lang`). -/
def hasFieldTy (tySizes : Nat → Nat) (ty : X86Ty) (bytes : ByteVec) : Prop :=
  match ty with
  | .u8 | .i8 => bytes.length = 1 ∧ allBytesInit bytes
  | .u16 => bytes.length = 2 ∧ allBytesInit bytes
  | .u32 => bytes.length = 4 ∧ allBytesInit bytes
  | .usize | .isize => bytes.length = 8 ∧ allBytesInit bytes
  | .bool => bytes = [some 0] ∨ bytes = [some 1]
  | .unit => bytes = []
  | .param idx => bytes.length = tySizes idx
  | .refParam _ => bytes.length = 8 ∧ allBytesInit bytes
  | .slice _ => bytes.length = 16 ∧ allBytesInit bytes
  | .adt _ => False

/-- Dynamic language-level ABI type-validity relation (`V_lang`) matching a
    `ByteVec` against an `X86Ty` under `adts` and `tySizes`. -/
def hasTy (adts : List AdtDecl) (tySizes : Nat → Nat)
    (bytes : ByteVec) (ty : X86Ty) : Prop :=
  match ty with
  | .adt id =>
    match lookupAdt adts id with
    | none => False
    | some decl =>
      bytes.length = decl.size ∧
      match decl.shape with
      | .structDecl fields _ =>
        allFieldsSatisfy (hasFieldTy tySizes) bytes fields
      | .directOption payloadTy =>
        let tagSlice := extractSlice bytes 0 8
        let payloadSz := evalX86TyByteSize adts tySizes payloadTy
        let payloadSlice := extractSlice bytes 8 payloadSz
        decodeLeBytes tagSlice = some 0 ∨
        (decodeLeBytes tagSlice = some 1 ∧ hasFieldTy tySizes payloadTy payloadSlice)
      | .nicheOption _ _ =>
        allBytesInit bytes
  | _ => hasFieldTy tySizes ty bytes

/-- Evaluate the logical discriminant (`0` for `None`, `1` for `Some`) of an
    enum `ByteVec` according to its `AdtShape`:
    - For `.directOption _`: reads the 8-byte tag at offset `0..8`; returns
      `some 0` if the tag is `0`, `some 1` if the tag is `1`, and `none`
      otherwise (catching invalid tags or uninitialized tag bytes as UB).
    - For `.nicheOption nicheVal _`: decodes the 8-byte value at offset `0..8`;
      returns `some 0` if `val == nicheVal` (`None`), `some 1` if
      `val != nicheVal` (`Some`), and `none` if any byte is `none`. -/
def evalEnumDiscr (shape : AdtShape) (bytes : ByteVec) : Option Nat :=
  match shape with
  | .directOption _ =>
    match decodeLeBytes (extractSlice bytes 0 8) with
    | some 0 => some 0
    | some 1 => some 1
    | _ => none
  | .nicheOption nicheVal _ =>
    match decodeLeBytes (extractSlice bytes 0 8) with
    | some val =>
      match Nat.beq val nicheVal with
      | true => some 0
      | false => some 1
    | none => none
  | .structDecl _ _ => none

/-- Library representation invariant map (`I_lib`) over byte sequences. -/
abbrev LibInv := (Nat → Nat) → X86Ty → ByteVec → Prop

/-- Default library representation invariant equating library validity with
    language-level byte validity (`hasTy adts`). -/
def defaultLibInv (adts : List AdtDecl) : LibInv :=
  fun tySizes ty bytes => hasTy adts tySizes bytes ty

/-- Generalized admissibility of a library representation invariant `libInv` for
    a crate's struct and enum declarations `adts`:
    1. Refines language validity (`libInv → hasTy`).
    2. Scalar primitives (`.u8`, `.i8`, `.u16`, `.u32`, `.usize`, `.isize`,
       `.bool`, `.unit`), wide slice headers (`.slice elemTy`), and generic
       `Copy` byte parameters (`.param idx`) are open.
    3. Public-safe struct closure (`r[expr.struct.safety]`): if a `.structDecl`
       has `nonExhaustive = false` and all fields `.pubSafe`, any `bytes` of
       length `decl.size` whose field slices satisfy `hasFieldTy` and `libInv`
       must satisfy `libInv tySizes (.adt id) bytes`.
    4. Public enum variant closure for `.directOption payloadTy` (`None` and
       `Some(v)` are public variants).
    5. Public enum variant closure for `.nicheOption nicheVal payloadAdtId`
       (`None` encoded as `nicheVal` and `Some(v)` where `v` satisfies
       `libInv tySizes (.adt payloadAdtId)` are public variants). -/
def AdmissibleLibInv (adts : List AdtDecl) (libInv : LibInv) : Prop :=
  (∀ tySizes ty bytes, libInv tySizes ty bytes → hasTy adts tySizes bytes ty) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u8 → libInv tySizes .u8 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .i8 → libInv tySizes .i8 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u16 → libInv tySizes .u16 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .u32 → libInv tySizes .u32 bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .usize → libInv tySizes .usize bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .isize → libInv tySizes .isize bytes) ∧
  (∀ tySizes bytes, hasTy adts tySizes bytes .bool → libInv tySizes .bool bytes) ∧
  (∀ tySizes, libInv tySizes .unit []) ∧
  (∀ tySizes elemTy bytes,
    hasTy adts tySizes bytes (.slice elemTy) → libInv tySizes (.slice elemTy) bytes) ∧
  (∀ tySizes idx bytes, bytes.length = tySizes idx → libInv tySizes (.param idx) bytes) ∧
  (∀ id decl fields,
    lookupAdt adts id = some decl →
    decl.shape = .structDecl fields false →
    fields.all FieldDecl.isPubSafe = true →
    ∀ tySizes bytes,
      bytes.length = decl.size →
      allFieldsSatisfy (hasFieldTy tySizes) bytes fields →
      allFieldsSatisfy (libInv tySizes) bytes fields →
      libInv tySizes (.adt id) bytes) ∧
  (∀ id decl payloadTy,
    lookupAdt adts id = some decl →
    decl.shape = .directOption payloadTy →
    ∀ tySizes bytes,
      bytes.length = decl.size →
      (decodeLeBytes (extractSlice bytes 0 8) = some 0 ∨
       (decodeLeBytes (extractSlice bytes 0 8) = some 1 ∧
        hasFieldTy tySizes payloadTy
          (extractSlice bytes 8 (evalX86TyByteSize adts tySizes payloadTy)) ∧
        libInv tySizes payloadTy
          (extractSlice bytes 8 (evalX86TyByteSize adts tySizes payloadTy)))) →
      libInv tySizes (.adt id) bytes) ∧
  (∀ id decl nicheVal payloadAdtId,
    lookupAdt adts id = some decl →
    decl.shape = .nicheOption nicheVal payloadAdtId →
    ∀ tySizes bytes,
      bytes.length = decl.size →
      allBytesInit bytes →
      (decodeLeBytes bytes = some nicheVal ∨
       libInv tySizes (.adt payloadAdtId) bytes) →
      libInv tySizes (.adt id) bytes)

/-!
## 4. Byte-Addressed x86-64 Instruction Set & Small-Step Operational Semantics
-/

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
    - `movSlice dst dstOff src`: copies the byte slice `src` into `dst` at `dstOff`.
    - `alu op width dst dstOff lhs rhs`: evaluates `op` on `width`-byte operands.
    - `movzx dst dstOff dstWidth src`: zero-extends `src` to `dstWidth` bytes.
    - `movsx dst dstOff dstWidth src`: sign-extends `src` to `dstWidth` bytes.
    - `truncate dst dstOff dstWidth src`: truncates `src` to its low `dstWidth` bytes.
    - `discriminant dst srcSlot adtId`: extracts the 8-byte logical discriminant
      (`0` or `1`) of enum `adtId` in `srcSlot` into `dst` (`TagEncoding::Direct`
      or `TagEncoding::Niche`).
    - `leaSlot dst target offset`: stores `Ptr target offset` into `dst`.
    - `addPtrOffset dst srcPtr delta`: adds constant `delta` bytes to `srcPtr`.
    - `ptrOffsetIndex dst srcPtr idxOp stride`: adds dynamic `idx * stride` bytes
      to the pointer in `srcPtr` (used for slice/array element addressing
      `&(*slice)[idx]`).
    - `ptrMetadata dst srcSlice`: extracts the 8-byte slice length metadata
      (`UnOp::PtrMetadata`, stored at offset `8..16` of wide slice `srcSlice`)
      into `dst`.
    - `makeSlice dst basePtr lenOp`: constructs a 16-byte wide slice in `dst`
      from provenance pointer `basePtr` and 8-byte length `lenOp`.
    - `reborrowSlot dst srcPtr`: copies the pointer in `srcPtr` to `dst` after
      verifying its target allocation is live.
    - `loadPtr dst dstOff srcPtr width`: loads `width` bytes from the pointer in
      `srcPtr` into `dst` at `dstOff`.
    - `storePtr dstPtr src`: writes `src` to memory at the pointer in `dstPtr`.
    - `copyNonOverlapping dstPtr srcPtr byteCount`: copies `byteCount` bytes
      from `srcPtr` to `dstPtr`, failing with `.failed .ub` if the two byte
      ranges overlap in the same allocation or are out of bounds.
    - `allocSlot slot size`: allocates `size` uninitialized bytes for `slot`.
    - `deallocSlot slot`: deallocates `slot` to `.unallocated`.
    - `nop`: architectural `nop`. -/
inductive X86Instr where
  | movSlice (dst : SlotId) (dstOff : Nat) (src : X86Operand)
  | alu (op : X86BinOp) (width : Nat) (dst : SlotId) (dstOff : Nat)
      (lhs : X86Operand) (rhs : X86Operand)
  | movzx (dst : SlotId) (dstOff : Nat) (dstWidth : Nat) (src : X86Operand)
  | movsx (dst : SlotId) (dstOff : Nat) (dstWidth : Nat) (src : X86Operand)
  | truncate (dst : SlotId) (dstOff : Nat) (dstWidth : Nat) (src : X86Operand)
  | discriminant (dst : SlotId) (srcSlot : SlotId) (adtId : Nat)
  | leaSlot (dst : SlotId) (target : SlotId) (offset : Nat := 0)
  | addPtrOffset (dst : SlotId) (srcPtr : SlotId) (delta : Nat)
  | ptrOffsetIndex (dst : SlotId) (srcPtr : SlotId) (idxOp : X86Operand)
      (stride : Nat)
  | ptrMetadata (dst : SlotId) (srcSlice : SlotId)
  | makeSlice (dst : SlotId) (basePtr : SlotId) (lenOp : X86Operand)
  | reborrowSlot (dst : SlotId) (srcPtr : SlotId)
  | loadPtr (dst : SlotId) (dstOff : Nat) (srcPtr : SlotId) (width : Nat)
  | storePtr (dstPtr : SlotId) (src : X86Operand)
  | copyNonOverlapping (dstPtr : SlotId) (srcPtr : SlotId) (byteCount : Nat)
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
    | copyNonOverlappingJmp (dstPtr : SlotId) (srcPtr : SlotId)
        (byteCount : Nat) (target : BlockLabel)
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

/-- Convert a `Bool` into its canonical Rust `bool` ABI byte (`1` or `0`). -/
def boolToByte (c : Bool) : UInt8 :=
  match c with
  | true => 1
  | false => 0

/-- Evaluate an x86-64 binary ALU, bitwise, shift, or comparison operation on
    two `width`-byte slices. -/
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
      | .eq => some [some (boolToByte (Nat.beq a b))]
      | .ne => some [some (boolToByte (!Nat.beq a b))]
      | .lt => some [some (boolToByte (Nat.blt a b))]
      | .le => some [some (boolToByte (Nat.ble a b))]
      | .gt => some [some (boolToByte (Nat.blt b a))]
      | .ge => some [some (boolToByte (Nat.ble b a))]
    | _, _ => none
  | false => none

/-- Single-step evaluation of a sequential instruction (`X86Instr`). -/
def evalX86Instr (adts : List AdtDecl) (s : X86State) (instr : X86Instr) :
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
  | .movzx dst dstOff dstWidth src =>
    match evalX86Operand s.mem src with
    | some (bs, mem1) =>
      match evalZeroExtend dstWidth bs with
      | some outBs =>
        match writeSliceMem mem1 { alloc := dst, offset := dstOff } outBs with
        | some mem2 => .step () { s with mem := mem2, ip := s.ip + 1 }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .movsx dst dstOff dstWidth src =>
    match evalX86Operand s.mem src with
    | some (bs, mem1) =>
      match evalSignExtend dstWidth bs with
      | some outBs =>
        match writeSliceMem mem1 { alloc := dst, offset := dstOff } outBs with
        | some mem2 => .step () { s with mem := mem2, ip := s.ip + 1 }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .truncate dst dstOff dstWidth src =>
    match evalX86Operand s.mem src with
    | some (bs, mem1) =>
      match evalTruncate dstWidth bs with
      | some outBs =>
        match writeSliceMem mem1 { alloc := dst, offset := dstOff } outBs with
        | some mem2 => .step () { s with mem := mem2, ip := s.ip + 1 }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .discriminant dst srcSlot adtId =>
    match lookupAdt adts adtId with
    | some decl =>
      let srcBlk := s.mem srcSlot.index
      match srcBlk.perm.canRead && srcBlk.written &&
            Nat.ble decl.size srcBlk.size &&
            Nat.ble decl.size srcBlk.bytes.length with
      | true =>
        match evalEnumDiscr decl.shape srcBlk.bytes with
        | some d =>
          match writeSliceMem s.mem { alloc := dst, offset := 0 } (encodeLeBytes 8 d) with
          | some mem' => .step () { s with mem := mem', ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | false => .failed .ub
    | none => .failed .ub
  | .leaSlot dst target offset =>
    let targetBlk := s.mem target.index
    let dstBlk := s.mem dst.index
    match targetBlk.perm.canRead &&
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
  | .ptrOffsetIndex dst srcPtr idxOp stride =>
    match evalX86Operand s.mem idxOp with
    | some (idxBs, mem1) =>
      match Nat.beq idxBs.length 8, decodeLeBytes idxBs with
      | true, some idx =>
        let srcBlk := mem1 srcPtr.index
        let dstBlk := mem1 dst.index
        match srcBlk.perm.canRead && srcBlk.written && dstBlk.perm.canWrite with
        | true =>
          match srcBlk.ptr with
          | some p =>
            let newDst : AllocBlock := {
              dstBlk with
              ptr := some (p.addOffset (idx * stride))
              written := true
            }
            .step () { s with mem := updateAlloc mem1 dst.index newDst, ip := s.ip + 1 }
          | none => .failed .ub
        | false => .failed .ub
      | _, _ => .failed .ub
    | none => .failed .ub
  | .ptrMetadata dst srcSlice =>
    let sliceBlk := s.mem srcSlice.index
    match sliceBlk.perm.canRead && sliceBlk.written && sliceBlk.ptr.isSome &&
          Nat.ble 16 sliceBlk.size && Nat.ble 16 sliceBlk.bytes.length with
    | true =>
      let lenBytes := extractSlice sliceBlk.bytes 8 8
      match writeSliceMem s.mem { alloc := dst, offset := 0 } lenBytes with
      | some mem' => .step () { s with mem := mem', ip := s.ip + 1 }
      | none => .failed .ub
    | false => .failed .ub
  | .makeSlice dst basePtr lenOp =>
    match evalX86Operand s.mem lenOp with
    | some (lenBs, mem1) =>
      let ptrBlk := mem1 basePtr.index
      let dstBlk := mem1 dst.index
      match Nat.beq lenBs.length 8 && allBytesInitBool lenBs &&
            ptrBlk.perm.canRead && ptrBlk.written &&
            dstBlk.perm.canWrite && Nat.beq dstBlk.size 16 with
      | true =>
        match ptrBlk.ptr with
        | some p =>
          let newDst : AllocBlock := {
            dstBlk with
            bytes := encodeLeBytes 8 p.offset ++ lenBs
            ptr := some p
            written := true
          }
          .step () { s with mem := updateAlloc mem1 dst.index newDst, ip := s.ip + 1 }
        | none => .failed .ub
      | false => .failed .ub
    | none => .failed .ub
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
  | .copyNonOverlapping dstPtr srcPtr byteCount =>
    match evalCopyNonOverlapping s.mem dstPtr srcPtr byteCount with
    | some mem' => .step () { s with mem := mem', ip := s.ip + 1 }
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
    let eqByte : UInt8 := boolToByte (Nat.beq sz1 sz2)
    match writeSliceMem s.mem { alloc := dst, offset := 0 } [some eqByte] with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .repMovsbJmp dst srcTy dstTy ptrSlot target =>
    match evalRepMovsb adts s.tySizes s.mem dst srcTy dstTy ptrSlot with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .copyNonOverlappingJmp dstPtr srcPtr byteCount target =>
    match evalCopyNonOverlapping s.mem dstPtr srcPtr byteCount with
    | some mem' =>
      .step () { s with mem := mem', bb := target.index, ip := 0 }
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalX86Operand s.mem arg with
    | some (argBytes, callerMem') =>
      let retSz := evalX86TyByteSize callee.adts s.tySizes callee.retTy
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
    | some instr => evalX86Instr active.adts s instr
    | none => evalX86Term active.adts s blk.term

/-- Slot matching predicate for a parameter of type `ty`:
    - For `.slice elemTy`: a 16-byte wide slice slot with `ptr = some p` and
      16 initialized bytes (`0..8` offset bytes and `8..16` length bytes).
    - For all other types: a value slot of size `evalX86TyByteSize adts tySizes ty`
      with `ptr = none` and `bytes` satisfying `pred ty bs`. -/
def slotMatchesPred (adts : List AdtDecl) (tySizes : Nat → Nat)
    (pred : X86Ty → ByteVec → Prop) (ty : X86Ty) (blk : AllocBlock) : Prop :=
  let sz := evalX86TyByteSize adts tySizes ty
  match ty with
  | .slice elemTy =>
    ∃ (p : Ptr) (bs : ByteVec),
      blk = {
        perm := .readWrite
        size := 16
        bytes := bs
        ptr := some p
        written := true
      } ∧
      pred (.slice elemTy) bs
  | _ =>
    ∃ (bs : ByteVec),
      blk = {
        perm := .readWrite
        size := sz
        bytes := bs
        ptr := none
        written := true
      } ∧
      pred ty bs

/-- Entry initialization condition for parameter home slots `1 ..= argTys.length`. -/
def argsMatchStack (adts : List AdtDecl) (tySizes : Nat → Nat)
    (argTys : List X86Ty) (mem : Nat → AllocBlock) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      slotMatchesPred adts tySizes (fun t bs => hasTy adts tySizes bs t) ty (mem k) ∧
      rest (k + 1))
    (fun _ => True)
    1

/-- Entry state predicate for an `X86Body`:
    - Return slot `0` is allocated with size `evalX86TyByteSize body.adts s.tySizes body.retTy`
      and `replicateBytes retSz none` (`written := false`).
    - Parameter slots `1 ..= argTys.length` hold type-valid `AllocBlock`s.
    - Slots beyond `argTys.length` may hold caller-frame allocations (e.g., slice
      backing arrays), while local scratch slots allocated during execution use
      explicit `.allocSlot`. -/
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
## 5. PME Admission and Crate Verification Envelope
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
      slotMatchesPred adts tySizes (libInv tySizes) ty (mem k) ∧
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
## 6. Structural Machine Meta-Theorems and Byte-Slice Lemmas
-/

theorem nat_beq_refl : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | k + 1 => nat_beq_refl k

theorem eq_of_nat_beq_eq_true : {a b : Nat} → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (eq_of_nat_beq_eq_true h)

theorem ne_of_nat_beq_eq_false : {a b : Nat} → Nat.beq a b = false → a ≠ b
  | 0, 0, h, _ => Bool.noConfusion h
  | 0, _ + 1, _, h => Nat.noConfusion h
  | _ + 1, 0, _, h => Nat.noConfusion h
  | a + 1, b + 1, h, heq => by
    injection heq with heq'
    exact @ne_of_nat_beq_eq_false a b h heq'

theorem nat_ble_refl : (n : Nat) → Nat.ble n n = true
  | 0 => rfl
  | k + 1 => nat_ble_refl k

theorem le_of_nat_ble_eq_true : {a b : Nat} → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (@le_of_nat_ble_eq_true a b h)

theorem nat_ble_eq_true_of_le : {a b : Nat} → a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | a + 1, 0, h => False.elim (Nat.not_lt_zero a h)
  | a + 1, b + 1, h => @nat_ble_eq_true_of_le a b (Nat.le_of_succ_le_succ h)

theorem lt_of_nat_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  le_of_nat_ble_eq_true h

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

theorem behaviorOf_le_pure
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).Spec Post :=
  behaviorOf_le_specOn (fun q out _ hpfx => h q out hpfx)

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

theorem reachesPrefix_safeAndEnsures_of_unwind
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome ByteVec} {P : ByteVec → Prop}
    (hstep : evalX86Step body s = .terminated .unwind)
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    exact ⟨True.intro, fun _ h => by cases h⟩

theorem reachesPrefix_normal_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {v : ByteVec} {Q : ByteVec → Prop}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix X86Machine body init n' s' tr' (.terminated (.normal v)) →
      Q v) :
    Q v := by
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

theorem reachesPrefix_normal_of_failed
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {err : FailureKind} {v : ByteVec}
    (hstep : evalX86Step body s = .failed err)
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v))) :
    False := by
  cases hreach with
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'

/-- Structural byte-slice lemmas. -/
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

theorem allBytesInit_dropBytes :
    (n : Nat) → (xs : ByteVec) → allBytesInit xs → allBytesInit (dropBytes n xs)
  | 0, _, h => h
  | _ + 1, [], _ => True.intro
  | _ + 1, none :: _, h => False.elim h
  | k + 1, some _ :: rest, h => allBytesInit_dropBytes k rest h

theorem allBytesInit_takeBytes :
    (n : Nat) → (xs : ByteVec) → allBytesInit xs → allBytesInit (takeBytes n xs)
  | 0, _, _ => True.intro
  | _ + 1, [], _ => True.intro
  | _ + 1, none :: _, h => False.elim h
  | k + 1, some _ :: rest, h => allBytesInit_takeBytes k rest h

theorem allBytesInit_extractSlice (xs : ByteVec) (off len : Nat)
    (h : allBytesInit xs) :
    allBytesInit (extractSlice xs off len) :=
  allBytesInit_takeBytes len (dropBytes off xs) (allBytesInit_dropBytes off xs h)

theorem takeBytes_length_of_ble :
    (n : Nat) → (xs : List α) → Nat.ble n xs.length = true →
      (takeBytes n xs).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => Bool.noConfusion h
  | k + 1, _ :: rest, h =>
    congrArg Nat.succ (takeBytes_length_of_ble k rest h)

theorem extractSlice_length_of_ble :
    (off : Nat) → (xs : List α) → (w : Nat) →
      Nat.ble (w + off) xs.length = true →
      (extractSlice xs off w).length = w
  | 0, xs, w, h => by
    dsimp [extractSlice, dropBytes]
    rw [Nat.add_zero] at h
    exact takeBytes_length_of_ble w xs h
  | k + 1, [], w, h => by
    have hle := le_of_nat_ble_eq_true h
    exact False.elim (Nat.not_lt_zero (w + k) hle)
  | k + 1, _ :: rest, w, h => by
    dsimp [extractSlice, dropBytes]
    exact extractSlice_length_of_ble k rest w h

/-!
## 7. Canonical Stack-Frame Memory, `wpByteX86`, and `necByteX86Normal`
-/

/-- Fundamental entry-state folding identity: overwriting slot `k` of `mem` with
    its own value `blk = mem k` is definitionally `updateAlloc mem k blk` and
    extensionally equal to `mem`, while allowing lookups at `k` to reduce by `rfl`
    and preserving all caller-frame allocations at other indices. -/
theorem updateAlloc_eq_self {mem : Nat → AllocBlock} {k : Nat} {blk : AllocBlock}
    (hk : mem k = blk) :
    updateAlloc mem k blk = mem := by
  funext i
  dsimp [updateAlloc]
  cases heq : Nat.beq i k with
  | true =>
    rw [eq_of_nat_beq_eq_true heq]
    exact hk.symm
  | false => rfl

theorem decompose_init_cons {bs : ByteVec} {n : Nat}
    (hlen : bs.length = n + 1) (hinit : allBytesInit bs) :
    ∃ (b : UInt8) (rest : ByteVec),
      bs = some b :: rest ∧ rest.length = n ∧ allBytesInit rest := by
  cases bs with
  | nil => cases hlen
  | cons x rest =>
    cases x with
    | none => cases hinit
    | some b =>
      injection hlen with hlen'
      exact ⟨b, rest, rfl, hlen', hinit⟩

theorem decompose_init_nil {bs : ByteVec} (hlen : bs.length = 0) :
    bs = [] := by
  cases bs with
  | nil => rfl
  | cons _ _ => cases hlen

theorem decompose_bytes_1 {bs : ByteVec}
    (h : bs.length = 1 ∧ allBytesInit bs) :
    ∃ (b0 : UInt8), bs = [some b0] := by
  cases decompose_init_cons h.1 h.2 with
  | intro b0 hrest =>
  cases hrest with
  | intro rest hr =>
    rw [decompose_init_nil hr.2.1] at hr
    exact ⟨b0, hr.1⟩

theorem decompose_bytes_2 {bs : ByteVec}
    (h : bs.length = 2 ∧ allBytesInit bs) :
    ∃ (b0 b1 : UInt8), bs = [some b0, some b1] := by
  cases decompose_init_cons h.1 h.2 with
  | intro b0 hrest =>
  cases hrest with
  | intro rest1 hr1 =>
  cases decompose_bytes_1 ⟨hr1.2.1, hr1.2.2⟩ with
  | intro b1 hr2 =>
    rw [hr2] at hr1
    exact ⟨b0, b1, hr1.1⟩

theorem decompose_bytes_4 {bs : ByteVec}
    (h : bs.length = 4 ∧ allBytesInit bs) :
    ∃ (b0 b1 b2 b3 : UInt8), bs = [some b0, some b1, some b2, some b3] := by
  cases decompose_init_cons h.1 h.2 with
  | intro b0 hrest1 =>
  cases hrest1 with
  | intro rest1 hr1 =>
  cases decompose_init_cons hr1.2.1 hr1.2.2 with
  | intro b1 hrest2 =>
  cases hrest2 with
  | intro rest2 hr2 =>
  cases decompose_bytes_2 ⟨hr2.2.1, hr2.2.2⟩ with
  | intro b2 hrest3 =>
  cases hrest3 with
  | intro b3 hr3 =>
    rw [hr3] at hr2
    rw [hr2.1] at hr1
    exact ⟨b0, b1, b2, b3, hr1.1⟩

theorem decompose_bytes_8 {bs : ByteVec}
    (h : bs.length = 8 ∧ allBytesInit bs) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8),
      bs = [some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7] := by
  cases decompose_init_cons h.1 h.2 with
  | intro b0 hrest1 =>
  cases hrest1 with
  | intro rest1 hr1 =>
  cases decompose_init_cons hr1.2.1 hr1.2.2 with
  | intro b1 hrest2 =>
  cases hrest2 with
  | intro rest2 hr2 =>
  cases decompose_init_cons hr2.2.1 hr2.2.2 with
  | intro b2 hrest3 =>
  cases hrest3 with
  | intro rest3 hr3 =>
  cases decompose_init_cons hr3.2.1 hr3.2.2 with
  | intro b3 hrest4 =>
  cases hrest4 with
  | intro rest4 hr4 =>
  cases decompose_bytes_4 ⟨hr4.2.1, hr4.2.2⟩ with
  | intro b4 h5 =>
  cases h5 with
  | intro b5 h6 =>
  cases h6 with
  | intro b6 h7 =>
  cases h7 with
  | intro b7 hr5 =>
    rw [hr5] at hr4
    rw [hr4.1] at hr3
    rw [hr3.1] at hr2
    rw [hr2.1] at hr1
    exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, hr1.1⟩

theorem decompose_bytes_16 {bs : ByteVec}
    (h : bs.length = 16 ∧ allBytesInit bs) :
    ∃ (a0 a1 a2 a3 a4 a5 a6 a7 l0 l1 l2 l3 l4 l5 l6 l7 : UInt8),
      bs = [some a0, some a1, some a2, some a3, some a4, some a5, some a6, some a7,
            some l0, some l1, some l2, some l3, some l4, some l5, some l6, some l7] := by
  cases decompose_init_cons h.1 h.2 with
  | intro a0 hr1 =>
  cases hr1 with
  | intro rest1 h1 =>
  cases decompose_init_cons h1.2.1 h1.2.2 with
  | intro a1 hr2 =>
  cases hr2 with
  | intro rest2 h2 =>
  cases decompose_init_cons h2.2.1 h2.2.2 with
  | intro a2 hr3 =>
  cases hr3 with
  | intro rest3 h3 =>
  cases decompose_init_cons h3.2.1 h3.2.2 with
  | intro a3 hr4 =>
  cases hr4 with
  | intro rest4 h4 =>
  cases decompose_init_cons h4.2.1 h4.2.2 with
  | intro a4 hr5 =>
  cases hr5 with
  | intro rest5 h5 =>
  cases decompose_init_cons h5.2.1 h5.2.2 with
  | intro a5 hr6 =>
  cases hr6 with
  | intro rest6 h6 =>
  cases decompose_init_cons h6.2.1 h6.2.2 with
  | intro a6 hr7 =>
  cases hr7 with
  | intro rest7 h7 =>
  cases decompose_init_cons h7.2.1 h7.2.2 with
  | intro a7 hr8 =>
  cases hr8 with
  | intro rest8 h8 =>
  cases decompose_bytes_8 ⟨h8.2.1, h8.2.2⟩ with
  | intro l0 hl1 =>
  cases hl1 with
  | intro l1 hl2 =>
  cases hl2 with
  | intro l2 hl3 =>
  cases hl3 with
  | intro l3 hl4 =>
  cases hl4 with
  | intro l4 hl5 =>
  cases hl5 with
  | intro l5 hl6 =>
  cases hl6 with
  | intro l6 hl7 =>
  cases hl7 with
  | intro l7 hr9 =>
    rw [hr9] at h8
    rw [h8.1] at h7
    rw [h7.1] at h6
    rw [h6.1] at h5
    rw [h5.1] at h4
    rw [h4.1] at h3
    rw [h3.1] at h2
    rw [h2.1] at h1
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, l0, l1, l2, l3, l4, l5, l6, l7, h1.1⟩

/-- Quantifier telescope over typed entry arguments starting at stack slot `k`. -/
def forallTypedByteArgsAux (adts : List AdtDecl) (tySizes : Nat → Nat)
    (k : Nat) (argTys : List X86Ty) (acc : Nat → AllocBlock)
    (P : (Nat → AllocBlock) → Prop) : Prop :=
  match argTys with
  | [] => P acc
  | (.u8 :: tys) | (.i8 :: tys) =>
    ∀ (b0 : UInt8),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 1, bytes := [some b0], ptr := none, written := true
        }) P
  | .u16 :: tys =>
    ∀ (b0 b1 : UInt8),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 2, bytes := [some b0, some b1], ptr := none, written := true
        }) P
  | .u32 :: tys =>
    ∀ (b0 b1 b2 b3 : UInt8),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 4,
          bytes := [some b0, some b1, some b2, some b3],
          ptr := none, written := true
        }) P
  | (.usize :: tys) | (.isize :: tys) | (.refParam _ :: tys) =>
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 8,
          bytes := [some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7],
          ptr := none, written := true
        }) P
  | .bool :: tys =>
    ∀ (b : Bool),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 1,
          bytes := [some (if b then 1 else 0)],
          ptr := none, written := true
        }) P
  | .unit :: tys =>
    forallTypedByteArgsAux adts tySizes (k + 1) tys
      (updateAlloc acc k {
        perm := .readWrite, size := 0, bytes := [], ptr := none, written := true
      }) P
  | .param idx :: tys =>
    ∀ (bs : ByteVec),
      bs.length = tySizes idx →
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := tySizes idx, bytes := bs, ptr := none, written := true
        }) P
  | .slice _ :: tys =>
    ∀ (p : Ptr) (a0 a1 a2 a3 a4 a5 a6 a7 l0 l1 l2 l3 l4 l5 l6 l7 : UInt8),
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite, size := 16,
          bytes := [some a0, some a1, some a2, some a3, some a4, some a5, some a6, some a7,
                    some l0, some l1, some l2, some l3, some l4, some l5, some l6, some l7],
          ptr := some p, written := true
        }) P
  | .adt id :: tys =>
    ∀ (bs : ByteVec),
      hasTy adts tySizes bs (.adt id) →
      forallTypedByteArgsAux adts tySizes (k + 1) tys
        (updateAlloc acc k {
          perm := .readWrite,
          size := evalX86TyByteSize adts tySizes (.adt id),
          bytes := bs, ptr := none, written := true
        }) P

/-- Top-level entry-argument quantifier telescope starting from `baseMem` with
    return slot `0` initialized. -/
def forallTypedByteArgs (body : X86Body) (tySizes : Nat → Nat)
    (baseMem : Nat → AllocBlock) (P : (Nat → AllocBlock) → Prop) : Prop :=
  let retSz := evalX86TyByteSize body.adts tySizes body.retTy
  let retBlk : AllocBlock := {
    perm := .readWrite
    size := retSz
    bytes := replicateBytes retSz none
    ptr := none
    written := false
  }
  forallTypedByteArgsAux body.adts tySizes 1 body.argTys
    (updateAlloc baseMem 0 retBlk) P

theorem forallTypedByteArgsAux_sound (adts : List AdtDecl) (tySizes : Nat → Nat)
    (argTys : List X86Ty) (mem : Nat → AllocBlock)
    (P : (Nat → AllocBlock) → Prop) :
    ∀ (k : Nat) (acc : Nat → AllocBlock),
      acc = mem →
      argTys.foldr
        (fun ty rest idx =>
          slotMatchesPred adts tySizes (fun t bs => hasTy adts tySizes bs t) ty (mem idx) ∧
          rest (idx + 1))
        (fun _ => True)
        k →
      forallTypedByteArgsAux adts tySizes k argTys acc P →
      P mem := by
  induction argTys with
  | nil =>
    intro _ acc hacc _ hforall
    rw [← hacc]
    exact hforall
  | cons ty tys ih =>
    intro k acc hacc hfold hforall
    cases hfold with
    | intro hslot hrest =>
      cases ty with
      | u8 =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_1 hbs.2 with
          | intro b0 hb0 =>
            subst hb0
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0)
      | i8 =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_1 hbs.2 with
          | intro b0 hb0 =>
            subst hb0
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0)
      | u16 =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_2 hbs.2 with
          | intro b0 hb1 =>
          cases hb1 with
          | intro b1 hb =>
            subst hb
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0 b1)
      | u32 =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_4 hbs.2 with
          | intro b0 hb1 =>
          cases hb1 with
          | intro b1 hb2 =>
          cases hb2 with
          | intro b2 hb3 =>
          cases hb3 with
          | intro b3 hb =>
            subst hb
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0 b1 b2 b3)
      | usize =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_8 hbs.2 with
          | intro b0 hb1 =>
          cases hb1 with
          | intro b1 hb2 =>
          cases hb2 with
          | intro b2 hb3 =>
          cases hb3 with
          | intro b3 hb4 =>
          cases hb4 with
          | intro b4 hb5 =>
          cases hb5 with
          | intro b5 hb6 =>
          cases hb6 with
          | intro b6 hb7 =>
          cases hb7 with
          | intro b7 hb =>
            subst hb
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0 b1 b2 b3 b4 b5 b6 b7)
      | isize =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_8 hbs.2 with
          | intro b0 hb1 =>
          cases hb1 with
          | intro b1 hb2 =>
          cases hb2 with
          | intro b2 hb3 =>
          cases hb3 with
          | intro b3 hb4 =>
          cases hb4 with
          | intro b4 hb5 =>
          cases hb5 with
          | intro b5 hb6 =>
          cases hb6 with
          | intro b6 hb7 =>
          cases hb7 with
          | intro b7 hb =>
            subst hb
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0 b1 b2 b3 b4 b5 b6 b7)
      | refParam _ =>
        cases hslot with
        | intro bs hbs =>
          cases decompose_bytes_8 hbs.2 with
          | intro b0 hb1 =>
          cases hb1 with
          | intro b1 hb2 =>
          cases hb2 with
          | intro b2 hb3 =>
          cases hb3 with
          | intro b3 hb4 =>
          cases hb4 with
          | intro b4 hb5 =>
          cases hb5 with
          | intro b5 hb6 =>
          cases hb6 with
          | intro b6 hb7 =>
          cases hb7 with
          | intro b7 hb =>
            subst hb
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest (hforall b0 b1 b2 b3 b4 b5 b6 b7)
      | bool =>
        cases hslot with
        | intro bs hbs =>
          have hupd : updateAlloc acc k (mem k) = mem := by
            rw [hacc]
            exact updateAlloc_eq_self rfl
          rw [hbs.1] at hupd
          cases hbs.2 with
          | inl h0 =>
            subst h0
            exact ih (k + 1) _ hupd hrest (hforall false)
          | inr h1 =>
            subst h1
            exact ih (k + 1) _ hupd hrest (hforall true)
      | unit =>
        cases hslot with
        | intro bs hbs =>
          have hnil : bs = [] := hbs.2
          subst hnil
          have hupd : updateAlloc acc k (mem k) = mem := by
            rw [hacc]
            exact updateAlloc_eq_self rfl
          rw [hbs.1] at hupd
          exact ih (k + 1) _ hupd hrest hforall
      | param idx =>
        cases hslot with
        | intro bs hbs =>
          have hupd : updateAlloc acc k (mem k) = mem := by
            rw [hacc]
            exact updateAlloc_eq_self rfl
          rw [hbs.1] at hupd
          exact ih (k + 1) _ hupd hrest (hforall bs hbs.2)
      | slice _ =>
        cases hslot with
        | intro p hp =>
        cases hp with
        | intro bs hbs =>
          cases decompose_bytes_16 hbs.2 with
          | intro a0 ha1 =>
          cases ha1 with
          | intro a1 ha2 =>
          cases ha2 with
          | intro a2 ha3 =>
          cases ha3 with
          | intro a3 ha4 =>
          cases ha4 with
          | intro a4 ha5 =>
          cases ha5 with
          | intro a5 ha6 =>
          cases ha6 with
          | intro a6 ha7 =>
          cases ha7 with
          | intro a7 hl0 =>
          cases hl0 with
          | intro l0 hl1 =>
          cases hl1 with
          | intro l1 hl2 =>
          cases hl2 with
          | intro l2 hl3 =>
          cases hl3 with
          | intro l3 hl4 =>
          cases hl4 with
          | intro l4 hl5 =>
          cases hl5 with
          | intro l5 hl6 =>
          cases hl6 with
          | intro l6 hl7 =>
          cases hl7 with
          | intro l7 hbs_eq =>
            subst hbs_eq
            have hupd : updateAlloc acc k (mem k) = mem := by
              rw [hacc]
              exact updateAlloc_eq_self rfl
            rw [hbs.1] at hupd
            exact ih (k + 1) _ hupd hrest
              (hforall p a0 a1 a2 a3 a4 a5 a6 a7 l0 l1 l2 l3 l4 l5 l6 l7)
      | adt id =>
        cases hslot with
        | intro bs hbs =>
          have hupd : updateAlloc acc k (mem k) = mem := by
            rw [hacc]
            exact updateAlloc_eq_self rfl
          rw [hbs.1] at hupd
          exact ih (k + 1) _ hupd hrest (hforall bs hbs.2)

/-- Universal entry-state canonicalization theorem on the byte-addressed
    provenance machine: any property `P s` of an initial state `s` satisfying
    `initX86State body s` reduces to proving `P` over the canonical `updateAlloc`
    memory generated by `forallTypedByteArgs`. -/
theorem initX86State_canonical (body : X86Body) (s : X86State)
    (P : X86State → Prop)
    (hinit : initX86State body s)
    (hcanonical : forallTypedByteArgs body s.tySizes s.mem (fun mem =>
      P { mem := mem, bb := 0, ip := 0, tySizes := s.tySizes })) :
    P s := by
  cases s with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
    have hb : bb0 = 0 := hinit.1
    have hip : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hm0 : mem0 0 = _ := hinit.2.2.2.2.1
    have hargs := hinit.2.2.2.2.2
    subst hb hip hc hst
    have hacc0 : updateAlloc mem0 0 _ = mem0 := updateAlloc_eq_self hm0
    exact forallTypedByteArgsAux_sound body.adts tySizes0 body.argTys mem0
      (fun mem => P { mem := mem, bb := 0, ip := 0, tySizes := tySizes0 })
      1 _ hacc0 hargs hcanonical

/-- Quantifier-free unfolding of `argsSatisfyLibInv` that reduces by `rfl` when
    applied to a canonical `updateAlloc` memory map. -/
def allArgsByteLibInv (libInv : LibInv) (tySizes : Nat → Nat) (k : Nat)
    (argTys : List X86Ty) (mem : Nat → AllocBlock) : Prop :=
  match argTys with
  | [] => True
  | ty :: tys =>
    libInv tySizes ty (mem k).bytes ∧
    allArgsByteLibInv libInv tySizes (k + 1) tys mem

theorem argsSatisfyLibInv_imp_allArgsByteLibInv (adts : List AdtDecl)
    (libInv : LibInv) (tySizes : Nat → Nat) (argTys : List X86Ty)
    (mem : Nat → AllocBlock) :
    ∀ (k : Nat),
      argTys.foldr
        (fun ty rest idx =>
          slotMatchesPred adts tySizes (libInv tySizes) ty (mem idx) ∧
          rest (idx + 1))
        (fun _ => True)
        k →
      allArgsByteLibInv libInv tySizes k argTys mem := by
  induction argTys with
  | nil =>
    intro _ _
    exact True.intro
  | cons ty tys ih =>
    intro k hfold
    cases hfold with
    | intro hslot hrest =>
      refine ⟨?_, ih (k + 1) hrest⟩
      cases ty with
      | slice _ =>
        cases hslot with
        | intro p hp =>
        cases hp with
        | intro bs hbs =>
          rw [hbs.1]
          exact hbs.2
      | u8 | i8 | u16 | u32 | usize | isize | bool | unit | adt _ | param _ | refParam _ =>
        cases hslot with
        | intro bs hbs =>
          rw [hbs.1]
          exact hbs.2

/-- Fuel-bounded, syntax-directed weakest precondition generator (`wpByteX86`)
    for the unified byte-addressed provenance machine (`X86Body`). -/
def wpByteX86 (fuel : Nat) (rootBody : X86Body) (s : X86State)
    (P : ByteVec → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    let active := s.curBody.getD rootBody
    match active.blocks[s.bb]? with
    | none => False
    | some blk =>
      match blk.instrs[s.ip]? with
      | some instr =>
        match instr with
        | .loadPtr dst dstOff srcPtr width =>
          let srcBlk := s.mem srcPtr.index
          match srcBlk.perm.canRead && srcBlk.written with
          | true =>
            match srcBlk.ptr with
            | some p =>
              let targetBlk := s.mem p.alloc.index
              let dstBlk := s.mem dst.index
              targetBlk.perm.canRead = true ∧
              targetBlk.written = true ∧
              Nat.ble (width + p.offset) targetBlk.size = true ∧
              Nat.ble (width + p.offset) targetBlk.bytes.length = true ∧
              dstBlk.perm.canWrite = true ∧
              let bs := extractSlice targetBlk.bytes p.offset width
              Nat.ble (bs.length + dstOff) dstBlk.size = true ∧
              Nat.ble (bs.length + dstOff) dstBlk.bytes.length = true ∧
              let newDst : AllocBlock := {
                dstBlk with
                bytes := writeSlice dstBlk.bytes dstOff bs
                written := true
              }
              wpByteX86 fuel' rootBody
                { s with mem := updateAlloc s.mem dst.index newDst, ip := s.ip + 1 } P
            | none => False
          | false => False
        | .discriminant dst srcSlot adtId =>
          match lookupAdt active.adts adtId with
          | some decl =>
            let srcBlk := s.mem srcSlot.index
            (srcBlk.perm.canRead && srcBlk.written &&
              Nat.ble decl.size srcBlk.size &&
              Nat.ble decl.size srcBlk.bytes.length) = true ∧
            ∃ d,
              evalEnumDiscr decl.shape srcBlk.bytes = some d ∧
              match writeSliceMem s.mem { alloc := dst, offset := 0 } (encodeLeBytes 8 d) with
              | some mem' =>
                wpByteX86 fuel' rootBody { s with mem := mem', ip := s.ip + 1 } P
              | none => False
          | none => False
        | .ptrOffsetIndex dst srcPtr idxOp stride =>
          match evalX86Operand s.mem idxOp with
          | some (idxBs, mem1) =>
            let srcBlk := mem1 srcPtr.index
            let dstBlk := mem1 dst.index
            Nat.beq idxBs.length 8 = true ∧
            (srcBlk.perm.canRead && srcBlk.written && dstBlk.perm.canWrite) = true ∧
            ∃ idx p,
              decodeLeBytes idxBs = some idx ∧
              srcBlk.ptr = some p ∧
              let newDst : AllocBlock := {
                dstBlk with
                ptr := some (p.addOffset (idx * stride))
                written := true
              }
              wpByteX86 fuel' rootBody
                { s with mem := updateAlloc mem1 dst.index newDst, ip := s.ip + 1 } P
          | none => False
        | _ =>
          match evalX86Instr active.adts s instr with
          | .step () s' => wpByteX86 fuel' rootBody s' P
          | .terminated (.normal v) => P v
          | .terminated .unwind => True
          | _ => False
      | none =>
        match blk.term with
        | .ret =>
          let retBlk := s.mem 0
          match s.stack with
          | [] =>
            retBlk.perm.canRead = true ∧
            retBlk.written = true ∧
            retBlk.bytes.length = retBlk.size ∧
            P retBlk.bytes
          | frame :: restStack =>
            retBlk.perm.canRead = true ∧
            retBlk.written = true ∧
            retBlk.bytes.length = retBlk.size ∧
            match writeSliceMem frame.callerMem { alloc := frame.retSlot, offset := 0 } retBlk.bytes with
            | some callerMem' =>
              wpByteX86 fuel' rootBody {
                mem := callerMem'
                bb := frame.retBlock
                ip := 0
                tySizes := s.tySizes
                curBody := frame.callerBody
                stack := restStack
              } P
            | none => False
        | .jccBool cond falseTarget trueTarget =>
          match evalX86Operand s.mem cond with
          | some ([some b], mem') =>
            (b = 0 →
              wpByteX86 fuel' rootBody
                { s with mem := mem', bb := falseTarget.index, ip := 0 } P) ∧
            (b = 1 →
              wpByteX86 fuel' rootBody
                { s with mem := mem', bb := trueTarget.index, ip := 0 } P) ∧
            (b = 0 ∨ b = 1)
          | _ => False
        | .repMovsbJmp dst srcTy dstTy ptrSlot target =>
          let srcSz := evalX86TyByteSize active.adts s.tySizes srcTy
          let dstSz := evalX86TyByteSize active.adts s.tySizes dstTy
          let ptrBlk := s.mem ptrSlot.index
          match ptrBlk.perm.canRead && ptrBlk.written with
          | true =>
            match ptrBlk.ptr with
            | some p =>
              let memAfterMove := updateAlloc s.mem ptrSlot.index
                { ptrBlk with ptr := none, written := false }
              let srcBlk := memAfterMove p.alloc.index
              let dstBlk := memAfterMove dst.index
              p.offset = 0 ∧
              srcSz = dstSz ∧
              srcBlk.perm.canRead = true ∧
              srcBlk.written = true ∧
              srcBlk.size = srcSz ∧
              srcBlk.bytes.length = srcSz ∧
              dstBlk.perm.canWrite = true ∧
              dstBlk.size = dstSz ∧
              dstBlk.bytes.length = dstSz ∧
              let newDst : AllocBlock := {
                dstBlk with
                bytes := srcBlk.bytes
                written := true
              }
              wpByteX86 fuel' rootBody {
                s with
                mem := updateAlloc memAfterMove dst.index newDst
                bb := target.index
                ip := 0
              } P
            | none => False
          | false => False
        | term =>
          match evalX86Term active.adts s term with
          | .step () s' => wpByteX86 fuel' rootBody s' P
          | .terminated (.normal v) => P v
          | .terminated .unwind => True
          | _ => False

/-- Branch-splitting helper for `wpByteX86` on a boolean comparison byte
    `boolToByte c`. -/
theorem wp_jcc_split (c : Bool) {P0 P1 : Prop} :
    (c = false → P0) →
    (c = true → P1) →
    let b : UInt8 := boolToByte c
    (b = 0 → P0) ∧ (b = 1 → P1) ∧ (b = 0 ∨ b = 1) := by
  cases c with
  | false =>
    intro hfalse _
    refine ⟨fun _ => hfalse rfl, ?_, Or.inl rfl⟩
    intro h
    injection h with h1
    injection h1 with h2
    cases h2
  | true =>
    intro _ htrue
    refine ⟨?_, fun _ => htrue rfl, Or.inr rfl⟩
    intro h
    injection h with h1
    injection h1 with h2
    cases h2

/-- Helper lemma proving `evalX86Instr` for `.loadPtr` when the propositional
    bounds obligations hold. -/
theorem evalX86Instr_loadPtr_eq (adts : List AdtDecl) (s : X86State)
    (dst : SlotId) (dstOff : Nat) (srcPtr : SlotId) (width : Nat) (p : Ptr)
    (hsrc : ((s.mem srcPtr.index).perm.canRead && (s.mem srcPtr.index).written) = true)
    (hptr : (s.mem srcPtr.index).ptr = some p)
    (ht1 : (s.mem p.alloc.index).perm.canRead = true)
    (ht2 : (s.mem p.alloc.index).written = true)
    (ht3 : Nat.ble (width + p.offset) (s.mem p.alloc.index).size = true)
    (ht4 : Nat.ble (width + p.offset) (s.mem p.alloc.index).bytes.length = true)
    (hd1 : (s.mem dst.index).perm.canWrite = true)
    (hd2 : Nat.ble ((extractSlice (s.mem p.alloc.index).bytes p.offset width).length + dstOff)
             (s.mem dst.index).size = true)
    (hd3 : Nat.ble ((extractSlice (s.mem p.alloc.index).bytes p.offset width).length + dstOff)
             (s.mem dst.index).bytes.length = true) :
    let dstBlk := s.mem dst.index
    let bs := extractSlice (s.mem p.alloc.index).bytes p.offset width
    let newDst : AllocBlock := {
      dstBlk with
      bytes := writeSlice dstBlk.bytes dstOff bs
      written := true
    }
    evalX86Instr adts s (.loadPtr dst dstOff srcPtr width) =
      .step () { s with mem := updateAlloc s.mem dst.index newDst, ip := s.ip + 1 } := by
  dsimp only [evalX86Instr, readSlice, writeSliceMem]
  rw [hsrc]
  dsimp only
  rw [hptr]
  dsimp only
  rw [ht1, ht2, ht3, ht4]
  dsimp only [and]
  rw [hd1, hd2, hd3]

/-- Helper lemma proving `evalX86Term` for `.repMovsbJmp` when the propositional
    equality obligations hold. -/
theorem evalX86Term_repMovsbJmp_eq (adts : List AdtDecl) (s : X86State)
    (dst : SlotId) (srcTy dstTy : X86Ty) (ptrSlot : SlotId) (target : BlockLabel)
    (p : Ptr)
    (hptr_rw : ((s.mem ptrSlot.index).perm.canRead && (s.mem ptrSlot.index).written) = true)
    (hptr : (s.mem ptrSlot.index).ptr = some p)
    (hoff : p.offset = 0)
    (hsz : evalX86TyByteSize adts s.tySizes srcTy = evalX86TyByteSize adts s.tySizes dstTy) :
    let srcSz := evalX86TyByteSize adts s.tySizes srcTy
    let dstSz := evalX86TyByteSize adts s.tySizes dstTy
    let ptrBlk := s.mem ptrSlot.index
    let memAfterMove := updateAlloc s.mem ptrSlot.index
      { ptrBlk with ptr := none, written := false }
    let srcBlk := memAfterMove p.alloc.index
    let dstBlk := memAfterMove dst.index
    srcBlk.perm.canRead = true →
    srcBlk.written = true →
    srcBlk.size = srcSz →
    srcBlk.bytes.length = srcSz →
    dstBlk.perm.canWrite = true →
    dstBlk.size = dstSz →
    dstBlk.bytes.length = dstSz →
    evalX86Term adts s (.repMovsbJmp dst srcTy dstTy ptrSlot target) =
      .step () {
        s with
        mem := updateAlloc memAfterMove dst.index {
          dstBlk with
          bytes := srcBlk.bytes
          written := true
        }
        bb := target.index
        ip := 0
      } := by
  intro srcSz dstSz ptrBlk memAfterMove srcBlk dstBlk
    hs_read hs_writ hs_sz hs_len hd_writ hd_sz hd_len
  have hsz' : srcSz = dstSz := hsz
  have hbeq_sz : Nat.beq srcSz dstSz = true := by
    rw [hsz']
    exact nat_beq_refl _
  have hble_src1 : Nat.ble (srcSz + p.offset) srcBlk.size = true := by
    rw [hoff, Nat.add_zero, hs_sz]
    exact nat_ble_refl _
  have hble_src2 : Nat.ble (srcSz + p.offset) srcBlk.bytes.length = true := by
    rw [hoff, Nat.add_zero, hs_len]
    exact nat_ble_refl _
  have hext : extractSlice srcBlk.bytes p.offset srcSz = srcBlk.bytes := by
    rw [hoff]
    exact extractSlice_zero_of_eq_length srcBlk.bytes srcSz hs_len
  have hble_dst1 : Nat.ble (srcBlk.bytes.length + 0) dstBlk.size = true := by
    rw [Nat.add_zero, hs_len, hsz', hd_sz]
    exact nat_ble_refl _
  have hble_dst2 : Nat.ble (srcBlk.bytes.length + 0) dstBlk.bytes.length = true := by
    rw [Nat.add_zero, hs_len, hsz', hd_len]
    exact nat_ble_refl _
  have hwrite : writeSlice dstBlk.bytes 0 srcBlk.bytes = srcBlk.bytes := by
    refine writeSlice_zero_of_eq_length dstBlk.bytes srcBlk.bytes ?_
    rw [hd_len, hs_len, hsz']
  have hrep : evalRepMovsb adts s.tySizes s.mem dst srcTy dstTy ptrSlot =
      some (updateAlloc memAfterMove dst.index {
        dstBlk with
        bytes := srcBlk.bytes
        written := true
      }) := by
    dsimp only [evalRepMovsb, readSlice, writeSliceMem]
    rw [hbeq_sz, hptr_rw]
    dsimp only
    rw [hptr]
    dsimp only
    rw [hs_read, hs_writ, hble_src1, hble_src2]
    dsimp only [and]
    rw [hext, hd_writ, hble_dst1, hble_dst2]
    dsimp only [and]
    rw [hwrite]
  dsimp only [evalX86Term]
  rw [hrep]

/-- Universal soundness theorem for `wpByteX86`: if `wpByteX86 fuel body s P`
    holds, every finite execution prefix reachable from `s` is free of UB/stuck
    states and satisfies `P` on normal termination. -/
theorem wpByteX86_sound (fuel : Nat) (body : X86Body) (init s : X86State)
    (P : ByteVec → Prop) (hwp : wpByteX86 fuel body s P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome ByteVec),
      ReachesPrefix X86Machine body init n s tr out →
      SafeAndEnsures P out := by
  induction fuel generalizing s with
  | zero => cases hwp
  | succ fuel' ih =>
    intro n tr out hreach
    dsimp [wpByteX86] at hwp
    cases hblk : (s.curBody.getD body).blocks[s.bb]? with
    | none =>
      rw [hblk] at hwp
      cases hwp
    | some blk =>
      rw [hblk] at hwp
      dsimp at hwp
      cases hinstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body s = evalX86Instr (s.curBody.getD body).adts s instr := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases instr with
        | loadPtr dst dstOff srcPtr width =>
          dsimp at hwp
          cases hsrc : (s.mem srcPtr.index).perm.canRead && (s.mem srcPtr.index).written with
          | false =>
            rw [hsrc] at hwp
            cases hwp
          | true =>
            rw [hsrc] at hwp
            dsimp at hwp
            cases hptr : (s.mem srcPtr.index).ptr with
            | none =>
              rw [hptr] at hwp
              cases hwp
            | some p =>
              rw [hptr] at hwp
              dsimp at hwp
              have hload := evalX86Instr_loadPtr_eq (s.curBody.getD body).adts s
                dst dstOff srcPtr width p hsrc hptr
                hwp.1 hwp.2.1 hwp.2.2.1 hwp.2.2.2.1
                hwp.2.2.2.2.1 hwp.2.2.2.2.2.1 hwp.2.2.2.2.2.2.1
              rw [hload] at hstep_eq
              exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
                (fun n' tr' hr' => ih _ hwp.2.2.2.2.2.2.2 n' tr' out hr')
        | discriminant dst srcSlot adtId =>
          dsimp at hwp
          cases hlook : lookupAdt (s.curBody.getD body).adts adtId with
          | none =>
            rw [hlook] at hwp
            cases hwp
          | some decl =>
            rw [hlook] at hwp
            dsimp at hwp
            have hguard := hwp.1
            cases hwp.2 with
            | intro d hd =>
              have hdiscr := hd.1
              have hrest := hd.2
              cases hw : writeSliceMem s.mem { alloc := dst, offset := 0 } (encodeLeBytes 8 d) with
              | none =>
                rw [hw] at hrest
                cases hrest
              | some mem' =>
                rw [hw] at hrest
                have hstep_discr :
                    evalX86Step body s = .step () { s with mem := mem', ip := s.ip + 1 } := by
                  rw [hstep_eq]
                  dsimp only [evalX86Instr]
                  rw [hlook]
                  dsimp only
                  rw [hguard]
                  dsimp only
                  rw [hdiscr]
                  dsimp only
                  rw [hw]
                exact reachesPrefix_safeAndEnsures_of_step hstep_discr hreach
                  (fun n' tr' hr' => ih _ hrest n' tr' out hr')
        | ptrOffsetIndex dst srcPtr idxOp stride =>
          dsimp at hwp
          cases hop : evalX86Operand s.mem idxOp with
          | none =>
            rw [hop] at hwp
            cases hwp
          | some pair =>
            cases pair with
            | mk idxBs mem1 =>
              rw [hop] at hwp
              dsimp at hwp
              have hlen := hwp.1
              have hguard := hwp.2.1
              cases hwp.2.2 with
              | intro idx hidx_ex =>
                cases hidx_ex with
                | intro p hp_ex =>
                  have hdec := hp_ex.1
                  have hptr := hp_ex.2.1
                  have hrest := hp_ex.2.2
                  have hstep_ptr :
                      evalX86Step body s =
                        .step () {
                          s with
                          mem := updateAlloc mem1 dst.index {
                            mem1 dst.index with
                            ptr := some (p.addOffset (idx * stride))
                            written := true
                          }
                          ip := s.ip + 1
                        } := by
                    rw [hstep_eq]
                    dsimp only [evalX86Instr]
                    rw [hop]
                    dsimp only
                    rw [hlen, hdec]
                    dsimp only
                    rw [hguard]
                    dsimp only
                    rw [hptr]
                  exact reachesPrefix_safeAndEnsures_of_step hstep_ptr hreach
                    (fun n' tr' hr' => ih _ hrest n' tr' out hr')
        | movSlice _ _ _ | alu _ _ _ _ _ _ | movzx _ _ _ _ | movsx _ _ _ _
        | truncate _ _ _ _ | leaSlot _ _ _ | addPtrOffset _ _ _
        | ptrMetadata _ _ | makeSlice _ _ _ | reborrowSlot _ _
        | storePtr _ _ | copyNonOverlapping _ _ _ | allocSlot _ _ | deallocSlot _ | nop =>
          dsimp at hwp
          cases hres : evalX86Instr (s.curBody.getD body).adts s _ with
          | step obs s' =>
            cases obs
            rw [hres] at hwp hstep_eq
            exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
              (fun n' tr' hr' => ih s' hwp n' tr' out hr')
          | terminated term =>
            cases term with
            | normal v =>
              rw [hres] at hwp hstep_eq
              exact reachesPrefix_safeAndEnsures_of_normal hstep_eq hreach hwp
            | unwind =>
              rw [hres] at hstep_eq
              exact reachesPrefix_safeAndEnsures_of_unwind hstep_eq hreach
          | failed _ =>
            rw [hres] at hwp
            cases hwp
          | choice _ _ =>
            rw [hres] at hwp
            cases hwp
      | none =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body s = evalX86Term (s.curBody.getD body).adts s blk.term := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hterm : blk.term with
        | ret =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hst : s.stack with
          | nil =>
            rw [hst] at hwp
            dsimp at hwp
            have hbeq : Nat.beq (s.mem 0).bytes.length (s.mem 0).size = true := by
              rw [hwp.2.2.1]
              exact nat_beq_refl _
            have hstep_ret :
                evalX86Step body s = .terminated (.normal (s.mem 0).bytes) := by
              rw [hstep_eq]
              dsimp only [evalX86Term]
              rw [hwp.1, hwp.2.1, hbeq, hst]
              rfl
            exact reachesPrefix_safeAndEnsures_of_normal hstep_ret hreach hwp.2.2.2
          | cons frame restStack =>
            rw [hst] at hwp
            dsimp at hwp
            have hbeq : Nat.beq (s.mem 0).bytes.length (s.mem 0).size = true := by
              rw [hwp.2.2.1]
              exact nat_beq_refl _
            cases hw : writeSliceMem frame.callerMem { alloc := frame.retSlot, offset := 0 } (s.mem 0).bytes with
            | none =>
              rw [hw] at hwp
              cases hwp.2.2.2
            | some callerMem' =>
              rw [hw] at hwp
              have hstep_ret :
                  evalX86Step body s = .step () {
                    mem := callerMem'
                    bb := frame.retBlock
                    ip := 0
                    tySizes := s.tySizes
                    curBody := frame.callerBody
                    stack := restStack
                  } := by
                rw [hstep_eq]
                dsimp only [evalX86Term]
                rw [hwp.1, hwp.2.1, hbeq, hst]
                dsimp only [and]
                rw [hw]
              exact reachesPrefix_safeAndEnsures_of_step hstep_ret hreach
                (fun n' tr' hr' => ih _ hwp.2.2.2 n' tr' out hr')
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hcond : evalX86Operand s.mem cond with
          | none =>
            rw [hcond] at hwp
            cases hwp
          | some pair =>
            cases pair with
            | mk bs mem' =>
              cases bs with
              | nil =>
                rw [hcond] at hwp
                cases hwp
              | cons optB restBs =>
                cases optB with
                | none =>
                  rw [hcond] at hwp
                  cases hwp
                | some b =>
                  cases restBs with
                  | cons _ _ =>
                    rw [hcond] at hwp
                    cases hwp
                  | nil =>
                    rw [hcond] at hwp
                    dsimp at hwp
                    cases hwp.2.2 with
                    | inl hb0 =>
                      subst hb0
                      have hstep_false :
                          evalX86Step body s =
                            .step () { s with mem := mem', bb := falseTarget.index, ip := 0 } := by
                        rw [hstep_eq]
                        dsimp only [evalX86Term]
                        rw [hcond]
                        rfl
                      exact reachesPrefix_safeAndEnsures_of_step hstep_false hreach
                        (fun n' tr' hr' => ih _ (hwp.1 rfl) n' tr' out hr')
                    | inr hb1 =>
                      subst hb1
                      have hstep_true :
                          evalX86Step body s =
                            .step () { s with mem := mem', bb := trueTarget.index, ip := 0 } := by
                        rw [hstep_eq]
                        dsimp only [evalX86Term]
                        rw [hcond]
                        rfl
                      exact reachesPrefix_safeAndEnsures_of_step hstep_true hreach
                        (fun n' tr' hr' => ih _ (hwp.2.1 rfl) n' tr' out hr')
        | repMovsbJmp dst srcTy dstTy ptrSlot target =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hptr_rw : (s.mem ptrSlot.index).perm.canRead && (s.mem ptrSlot.index).written with
          | false =>
            rw [hptr_rw] at hwp
            cases hwp
          | true =>
            rw [hptr_rw] at hwp
            dsimp at hwp
            cases hptr : (s.mem ptrSlot.index).ptr with
            | none =>
              rw [hptr] at hwp
              cases hwp
            | some p =>
              rw [hptr] at hwp
              dsimp at hwp
              have hrep := evalX86Term_repMovsbJmp_eq (s.curBody.getD body).adts s
                dst srcTy dstTy ptrSlot target p hptr_rw hptr
                hwp.1 hwp.2.1 hwp.2.2.1 hwp.2.2.2.1 hwp.2.2.2.2.1
                hwp.2.2.2.2.2.1 hwp.2.2.2.2.2.2.1 hwp.2.2.2.2.2.2.2.1 hwp.2.2.2.2.2.2.2.2.1
              rw [hrep] at hstep_eq
              exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
                (fun n' tr' hr' => ih _ hwp.2.2.2.2.2.2.2.2.2 n' tr' out hr')
        | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ | cmpSizeEqJmp _ _ _ _
        | copyNonOverlappingJmp _ _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hres : evalX86Term (s.curBody.getD body).adts s blk.term with
          | step obs s' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hwp hstep_eq
            exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
              (fun n' tr' hr' => ih s' hwp n' tr' out hr')
          | terminated term =>
            cases term with
            | normal v =>
              rw [hterm] at hres
              rw [hres] at hwp hstep_eq
              exact reachesPrefix_safeAndEnsures_of_normal hstep_eq hreach hwp
            | unwind =>
              rw [hterm] at hres
              rw [hres] at hstep_eq
              exact reachesPrefix_safeAndEnsures_of_unwind hstep_eq hreach
          | failed _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp
          | choice _ _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp

/-- Dual normal-termination necessity evaluator (`necByteX86Normal`) for PME/CTFE. -/
def necByteX86Normal (fuel : Nat) (rootBody : X86Body) (s : X86State)
    (Q : ByteVec → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    let active := s.curBody.getD rootBody
    match active.blocks[s.bb]? with
    | none => True
    | some blk =>
      match blk.instrs[s.ip]? with
      | some instr =>
        match evalX86Instr active.adts s instr with
        | .step () s' => necByteX86Normal fuel' rootBody s' Q
        | .terminated (.normal v) => Q v
        | .terminated .unwind => True
        | .failed _ => True
        | .choice _ _ => False
      | none =>
        match blk.term with
        | .jccBool cond falseTarget trueTarget =>
          match evalX86Operand s.mem cond with
          | some ([some b], mem') =>
            (b = 0 →
              necByteX86Normal fuel' rootBody
                { s with mem := mem', bb := falseTarget.index, ip := 0 } Q) ∧
            (b = 1 →
              necByteX86Normal fuel' rootBody
                { s with mem := mem', bb := trueTarget.index, ip := 0 } Q)
          | none => True
          | _ => False
        | term =>
          match evalX86Term active.adts s term with
          | .step () s' => necByteX86Normal fuel' rootBody s' Q
          | .terminated (.normal v) => Q v
          | .terminated .unwind => True
          | .failed _ => True
          | .choice _ _ => False

/-- Extract a compile-time PME fact `P` from `ConstSucceeds tySizes c` via
    `wpByteX86`. -/
theorem constSucceeds_of_wpByteX86 (fuel : Nat) {tySizes : Nat → Nat}
    {c : X86Body} {P : Prop}
    (h : ConstSucceeds tySizes c)
    (hwp : ∀ (baseMem : Nat → AllocBlock),
      forallTypedByteArgs c tySizes baseMem (fun mem =>
        wpByteX86 fuel c { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
          (fun _ => P))) :
    P := by
  cases h with
  | intro s₀ h1 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : s₀.tySizes = tySizes := h4.1
    have hinit : initX86State c s₀ := h4.2.1
    have hreach := h4.2.2
    have hwp_s₀ : wpByteX86 fuel c s₀ (fun _ => P) := by
      refine initX86State_canonical c s₀
        (fun s => wpByteX86 fuel c s (fun _ => P))
        hinit ?_
      rw [hts]
      exact hwp s₀.mem
    exact (wpByteX86_sound fuel c s₀ s₀ (fun _ => P) hwp_s₀ n tr
      (.terminated (.normal v)) hreach).2 v rfl

/-- Universal bridge for unconditional specifications (`X86Lang.Spec`). -/
theorem verifyByteX86Spec (fuel : Nat) (body : X86Body)
    (Q : X86State → ByteVec → Prop)
    (hvc : ∀ (tySizes : Nat → Nat) (baseMem : Nat → AllocBlock),
      forallTypedByteArgs body tySizes baseMem (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        wpByteX86 fuel body s₀ (Q s₀))) :
    X86Sem body ≤ X86Lang.Spec (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) → Q q.init ret) := by
  refine behaviorOf_le_pure (M := X86Machine) ?_
  intro q out hpfx
  have hwp_init : wpByteX86 fuel body q.init (Q q.init) :=
    initX86State_canonical body q.init
      (fun s => wpByteX86 fuel body s (Q s))
      hpfx.1 (hvc q.init.tySizes q.init.mem)
  exact wpByteX86_sound fuel body q.init q.init (Q q.init) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for `EnsuresRetLibInv` on a `pubSafe` function. -/
theorem verifyPubSafeRetByteLibInv (fuel : Nat) (libInv : LibInv) (fn : CapturedFn)
    (traitLaws : Prop) (hkind : fn.kind = .pubSafe traitLaws)
    (hvc : ∀ (tySizes : Nat → Nat) (baseMem : Nat → AllocBlock),
      MonoAdmitted tySizes fn.prog →
      traitLaws →
      forallTypedByteArgs fn.prog tySizes baseMem (fun mem =>
        allArgsByteLibInv libInv tySizes 1 fn.prog.argTys mem →
        wpByteX86 fuel fn.prog { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
          (libInv tySizes fn.prog.retTy))) :
    X86Sem fn.prog ≤
      EnsuresRetLibInv libInv fn.prog.retTy (fn.effectivePre libInv) := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  have hmono : MonoAdmitted q.init.tySizes fn.prog := hpre.1
  have hrest := hpre.2
  rw [hkind] at hrest
  have htrait : traitLaws := hrest.1
  have hlib : allArgsByteLibInv libInv q.init.tySizes 1 fn.prog.argTys q.init.mem :=
    argsSatisfyLibInv_imp_allArgsByteLibInv fn.prog.adts libInv q.init.tySizes
      fn.prog.argTys q.init.mem 1 hrest.2
  have hwp_init :
      wpByteX86 fuel fn.prog q.init (libInv q.init.tySizes fn.prog.retTy) :=
    initX86State_canonical fn.prog q.init
      (fun s =>
        allArgsByteLibInv libInv s.tySizes 1 fn.prog.argTys s.mem →
        wpByteX86 fuel fn.prog s (libInv s.tySizes fn.prog.retTy))
      hpfx.1 (hvc q.init.tySizes q.init.mem hmono htrait) hlib
  exact wpByteX86_sound fuel fn.prog q.init q.init
    (libInv q.init.tySizes fn.prog.retTy) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for `EnsuresRetLibInv` on a `pubUnsafe` function. -/
theorem verifyPubUnsafeRetByteLibInv (fuel : Nat) (libInv : LibInv)
    (fn : CapturedFn) (traitLaws : Prop)
    (safetyPre : ExecQuery X86State → Prop)
    (hkind : fn.kind = .pubUnsafe traitLaws safetyPre)
    (hvc : ∀ (tySizes : Nat → Nat) (steps : Nat) (baseMem : Nat → AllocBlock),
      MonoAdmitted tySizes fn.prog →
      traitLaws →
      forallTypedByteArgs fn.prog tySizes baseMem (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        allArgsByteLibInv libInv tySizes 1 fn.prog.argTys mem →
        safetyPre { init := s₀, steps := steps } →
        wpByteX86 fuel fn.prog s₀ (libInv tySizes fn.prog.retTy))) :
    X86Sem fn.prog ≤
      EnsuresRetLibInv libInv fn.prog.retTy (fn.effectivePre libInv) := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  have hmono : MonoAdmitted q.init.tySizes fn.prog := hpre.1
  have hrest := hpre.2
  rw [hkind] at hrest
  have htrait : traitLaws := hrest.1
  have hlib : allArgsByteLibInv libInv q.init.tySizes 1 fn.prog.argTys q.init.mem :=
    argsSatisfyLibInv_imp_allArgsByteLibInv fn.prog.adts libInv q.init.tySizes
      fn.prog.argTys q.init.mem 1 hrest.2.1
  have hsafety : safetyPre q := hrest.2.2
  have hwp_init :
      wpByteX86 fuel fn.prog q.init (libInv q.init.tySizes fn.prog.retTy) :=
    initX86State_canonical fn.prog q.init
      (fun s =>
        allArgsByteLibInv libInv s.tySizes 1 fn.prog.argTys s.mem →
        safetyPre { init := s, steps := q.steps } →
        wpByteX86 fuel fn.prog s (libInv s.tySizes fn.prog.retTy))
      hpfx.1 (hvc q.init.tySizes q.steps q.init.mem hmono htrait) hlib hsafety
  exact wpByteX86_sound fuel fn.prog q.init q.init
    (libInv q.init.tySizes fn.prog.retTy) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-!
## 8. Generalized `defaultLibInv_admissible` & Cluster D2 Benchmarks via `wpByteX86`
-/

/-- `defaultLibInv adts` satisfies the Phase 3 `AdmissibleLibInv` for ANY list of
    struct, direct-tagged enum, and niche-encoded enum declarations `adts`. -/
theorem defaultLibInv_admissible (adts : List AdtDecl) :
    AdmissibleLibInv adts (defaultLibInv adts) := by
  refine ⟨fun _ _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ => rfl,
          fun _ _ _ h => h,
          fun _ _ _ h => h,
          ?_, ?_, ?_⟩
  · intro id decl fields hlook hshape _ tySizes bytes hlen hfields _
    dsimp [defaultLibInv, hasTy]
    rw [hlook]
    dsimp
    rw [hshape]
    exact ⟨hlen, hfields⟩
  · intro id decl payloadTy hlook hshape tySizes bytes hlen hvar
    dsimp [defaultLibInv, hasTy]
    rw [hlook]
    dsimp
    rw [hshape]
    refine ⟨hlen, ?_⟩
    cases hvar with
    | inl h0 => exact Or.inl h0
    | inr h1 => exact Or.inr ⟨h1.1, h1.2.1⟩
  · intro id decl nicheVal payloadAdtId hlook hshape tySizes bytes hlen hinit _
    dsimp [defaultLibInv, hasTy]
    rw [hlook]
    dsimp
    rw [hshape]
    exact ⟨hlen, hinit⟩

/-- Generic single-function `CrateTheorem` discharge for a safe function under
    an admissible `libInv`. -/
theorem verify_single_fn_wf_crate_with_inv
    (adts : List AdtDecl) (libInv : LibInv)
    (hAdm : AdmissibleLibInv adts libInv)
    (fnName : String) (body : X86Body)
    (h_ret : X86Sem body ≤
      EnsuresRetLibInv libInv body.retTy
        (CapturedFn.effectivePre libInv
          { name := fnName, prog := body, specs := [] })) :
    CrateTheorem {
      adts := adts
      libInv := libInv
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName body]
    } := by
  refine ⟨(by intro h; cases h), hAdm, ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 h_ret)
    (ensuresRetLibInv_le_wellFormedOn _ _ _)
    hAssumptions.1.1

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
    } :=
  verify_single_fn_wf_crate_with_inv adts (defaultLibInv adts)
    (defaultLibInv_admissible adts) fnName body h_ret

/-- `#[repr(C)] pub struct Padded { pub a: u8, /* 3B pad */ pub b: u32 }` (`id := 1`). -/
def paddedAdtDecl : AdtDecl where
  id := 1
  size := 8
  shape := .structDecl [
    { offset := 0, size := 1, ty := .u8, access := .pubSafe },
    { offset := 4, size := 4, ty := .u32, access := .pubSafe }
  ] false

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

/-- `paddedSubfieldAndCopyBody` proved via `wpByteX86` in 12 lines (down from
    107 lines of manual stepping in `ByteMemoryProvenanceProbe.lean`!). -/
theorem paddedSubfieldAndCopyBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := paddedSubfieldAndCopyBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv [paddedAdtDecl]) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [paddedAdtDecl])) := by
  intro fn
  refine verifyPubSafeRetByteLibInv 20 (defaultLibInv [paddedAdtDecl]) fn True rfl
    (fun tySizes _ _ _ bs hty _ => ?_)
  let ⟨a0, p1, p2, p3, c0, c1, c2, c3, hbs⟩ := padded_hasTy_decompose tySizes bs hty
  subst hbs
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, ⟨rfl, ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, True.intro⟩⟩

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

/-- PME necessity for `sizeEqConstBody` on the byte-addressed machine in 2 lines
    via `constSucceeds_of_wpByteX86` + `wp_jcc_split` (down from 40 lines in
    `ByteMemoryProvenanceProbe.lean`!). -/
theorem constSucceeds_sizeEqConstBody_vcgen (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 :=
  constSucceeds_of_wpByteX86 15 h (fun _ =>
    wp_jcc_split (Nat.beq (tySizes 0) (tySizes 1))
      (fun _ => True.intro)
      (fun htrue => ⟨rfl, rfl, rfl, eq_of_nat_beq_eq_true htrue⟩))

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

/-- `transmuteCheckedBody` proved via `wpByteX86` in 6 lines (down from 122 lines
    of manual stepping in `ByteMemoryProvenanceProbe.lean`!). -/
theorem transmuteCheckedBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := transmuteCheckedBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv []) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [])) := by
  intro fn
  refine verifyPubSafeRetByteLibInv 20 (defaultLibInv []) fn True rfl
    (fun tySizes _ hmono _ bs hbs _ => ?_)
  have heq : tySizes 0 = tySizes 1 :=
    constSucceeds_sizeEqConstBody_vcgen tySizes
      (hmono sizeEqConstBody (.direct (.head _)))
  exact ⟨rfl, heq, rfl, rfl, rfl, hbs, rfl, rfl, replicateBytes_length _ _,
         rfl, rfl, hbs.trans heq, hbs.trans heq⟩

/-!
## 9. Niche-Encoded Enums (`Option<NonZeroUsize>`) vs Direct-Tagged Enums (`Option<usize>`)
-/

/-- `#[repr(transparent)] pub struct NonZeroUsize(usize)` (`id := 0`, 8B, single
    private `.usize` field at offset 0). -/
def nonZeroAdtDecl : AdtDecl where
  id := 0
  size := 8
  shape := .structDecl [
    { offset := 0, size := 8, ty := .usize, access := .priv }
  ] false

/-- `Option<usize>` (`id := 2`, 16B `TagEncoding::Direct`: 8B tag at `0..8`,
    8B `usize` payload at `8..16`). -/
def optionUsizeDirectDecl : AdtDecl where
  id := 2
  size := 16
  shape := .directOption .usize

/-- `Option<NonZeroUsize>` (`id := 3`, 8B `TagEncoding::Niche`: niche value `0`
    encodes `None` with logical discriminant `0`; any non-zero value encodes
    `Some(NonZeroUsize)` with logical discriminant `1` at offset `0..8`). -/
def optionNonZeroNicheDecl : AdtDecl where
  id := 3
  size := 8
  shape := .nicheOption 0 0

def enumCrateAdts : List AdtDecl :=
  [nonZeroAdtDecl, optionUsizeDirectDecl, optionNonZeroNicheDecl]

/-- Library representation invariant for `enumCrateAdts`:
    - `NonZeroUsize` (`id = 0`): 8 initialized bytes with `decodeLeBytes bytes ≠ some 0`.
    - `Option<usize>` (`id = 2`): 16-byte direct-tagged `Option<usize>`.
    - `Option<NonZeroUsize>` (`id = 3`): 8 initialized bytes (where `0` is `None`
      and any non-zero value is `Some(nz)`). -/
def enumCrateLibInv (tySizes : Nat → Nat) (ty : X86Ty) (bytes : ByteVec) : Prop :=
  match ty with
  | .adt 0 =>
    hasTy enumCrateAdts tySizes bytes (.adt 0) ∧
    decodeLeBytes bytes ≠ some 0
  | .adt 2 =>
    hasTy enumCrateAdts tySizes bytes (.adt 2)
  | .adt 3 =>
    hasTy enumCrateAdts tySizes bytes (.adt 3)
  | .adt _ => False
  | _ => hasFieldTy tySizes ty bytes

/-- `enumCrateLibInv` satisfies `AdmissibleLibInv enumCrateAdts`. -/
theorem enumCrateLibInv_admissible :
    AdmissibleLibInv enumCrateAdts enumCrateLibInv := by
  refine ⟨?_,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ _ h => h,
          fun _ => rfl,
          fun _ _ _ h => h,
          fun _ _ _ h => h,
          ?_, ?_, ?_⟩
  · intro tySizes ty bytes hinv
    cases ty with
    | u8 | i8 | u16 | u32 | usize | isize | bool | unit
    | param _ | refParam _ | slice _ => exact hinv
    | adt id =>
      cases id with
      | zero => exact hinv.1
      | succ k1 =>
        cases k1 with
        | zero => cases hinv
        | succ k2 =>
          cases k2 with
          | zero => exact hinv
          | succ k3 =>
            cases k3 with
            | zero => exact hinv
            | succ _ => cases hinv
  · intro id decl fields hlook hshape hpub _ _ _ _ _
    cases id with
    | zero =>
      dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl] at hlook
      injection hlook with hdecl
      subst hdecl
      dsimp [nonZeroAdtDecl] at hshape
      injection hshape with hf _
      subst hf
      cases hpub
    | succ k1 =>
      cases k1 with
      | zero =>
        dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
          optionNonZeroNicheDecl] at hlook
        cases hlook
      | succ k2 =>
        cases k2 with
        | zero =>
          dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl] at hlook
          injection hlook with hdecl
          subst hdecl
          cases hshape
        | succ k3 =>
          cases k3 with
          | zero =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            injection hlook with hdecl
            subst hdecl
            cases hshape
          | succ _ =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            cases hlook
  · intro id decl payloadTy hlook hshape tySizes bytes hlen hvar
    cases id with
    | zero =>
      dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl] at hlook
      injection hlook with hdecl; subst hdecl; cases hshape
    | succ k1 =>
      cases k1 with
      | zero =>
        dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
          optionNonZeroNicheDecl] at hlook
        cases hlook
      | succ k2 =>
        cases k2 with
        | zero =>
          dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl] at hlook
          injection hlook with hdecl
          subst hdecl
          dsimp [optionUsizeDirectDecl] at hshape
          injection hshape with hpay
          subst hpay
          refine ⟨hlen, ?_⟩
          cases hvar with
          | inl h0 => exact Or.inl h0
          | inr h1 => exact Or.inr ⟨h1.1, h1.2.1⟩
        | succ k3 =>
          cases k3 with
          | zero =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            injection hlook with hdecl; subst hdecl; cases hshape
          | succ _ =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            cases hlook
  · intro id decl nicheVal payloadAdtId hlook hshape _ bytes hlen hinit _
    cases id with
    | zero =>
      dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl] at hlook
      injection hlook with hdecl; subst hdecl; cases hshape
    | succ k1 =>
      cases k1 with
      | zero =>
        dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
          optionNonZeroNicheDecl] at hlook
        cases hlook
      | succ k2 =>
        cases k2 with
        | zero =>
          dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl] at hlook
          injection hlook with hdecl; subst hdecl; cases hshape
        | succ k3 =>
          cases k3 with
          | zero =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            injection hlook with hdecl
            subst hdecl
            exact ⟨hlen, hinit⟩
          | succ _ =>
            dsimp [lookupAdt, enumCrateAdts, nonZeroAdtDecl, optionUsizeDirectDecl,
              optionNonZeroNicheDecl] at hlook
            cases hlook

/-- `pub fn unwrap_or_zero_niche(opt: Option<NonZeroUsize>) -> usize`:
    Extracts the logical discriminant of `opt` (8B niche-encoded enum in slot `1`)
    into slot `2` via `.discriminant ⟨2⟩ ⟨1⟩ 3`, compares against `1` (`Some`) in
    slot `3`, and branches via `jccBool`:
    - `bb1` (`None`, discriminant `0`): writes `0` (`immWord 8 0`) to return slot `0`.
    - `bb2` (`Some`, discriminant `1`): extracts the 8B payload `((_1 as Some).0)`
      at offset `0..8` of slot `1` into return slot `0`. -/
def unwrapOrZeroNicheBody : X86Body where
  adts := enumCrateAdts
  argTys := [.adt 3]
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 1,
        .discriminant ⟨2⟩ ⟨1⟩ 3,
        .alu .eq 8 ⟨3⟩ 0 (.slotSlice ⟨2⟩ 0 8 true) (.immWord 8 1)
      ]
      term := .jccBool (.slotSlice ⟨3⟩ 0 1 true) ⟨1⟩ ⟨2⟩ },
    -- bb1 (None): return 0
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩,
        .movSlice ⟨0⟩ 0 (.immWord 8 0)
      ]
      term := .ret },
    -- bb2 (Some): return payload at offset 0..8
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩,
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨1⟩ 0 8 false)
      ]
      term := .ret }
  ]

theorem evalEnumDiscr_direct_0 {payloadTy : X86Ty} {bytes : ByteVec} :
    decodeLeBytes (extractSlice bytes 0 8) = some 0 →
    evalEnumDiscr (.directOption payloadTy) bytes = some 0 := by
  intro h
  dsimp only [evalEnumDiscr]
  rw [h]
  rfl

theorem evalEnumDiscr_direct_1 {payloadTy : X86Ty} {bytes : ByteVec} :
    decodeLeBytes (extractSlice bytes 0 8) = some 1 →
    evalEnumDiscr (.directOption payloadTy) bytes = some 1 := by
  intro h
  dsimp only [evalEnumDiscr]
  rw [h]
  rfl

theorem evalEnumDiscr_niche_of_decode {nicheVal payloadId : Nat} {bytes : ByteVec} {val : Nat} :
    decodeLeBytes (extractSlice bytes 0 8) = some val →
    Nat.beq val nicheVal = true →
    evalEnumDiscr (.nicheOption nicheVal payloadId) bytes = some 0 := by
  intro hdec hbeq
  dsimp only [evalEnumDiscr]
  rw [hdec]
  dsimp only
  rw [hbeq]

theorem evalEnumDiscr_niche_of_decode_ne {nicheVal payloadId : Nat} {bytes : ByteVec} {val : Nat} :
    decodeLeBytes (extractSlice bytes 0 8) = some val →
    Nat.beq val nicheVal = false →
    evalEnumDiscr (.nicheOption nicheVal payloadId) bytes = some 1 := by
  intro hdec hbeq
  dsimp only [evalEnumDiscr]
  rw [hdec]
  dsimp only
  rw [hbeq]

theorem decodeLeBytes_8_some (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ∃ val : Nat,
      decodeLeBytes [some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7] = some val :=
  ⟨_, rfl⟩

theorem unwrapOrZeroNicheBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := unwrapOrZeroNicheBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv enumCrateLibInv fn.prog.retTy
        (fn.effectivePre enumCrateLibInv) := by
  intro fn
  refine verifyPubSafeRetByteLibInv 20 enumCrateLibInv fn True rfl
    (fun _ _ _ _ bs hty _ => ?_)
  let ⟨b0, b1, b2, b3, b4, b5, b6, b7, hbs⟩ := decompose_bytes_8 ⟨hty.1, hty.2⟩
  subst hbs
  cases decodeLeBytes_8_some b0 b1 b2 b3 b4 b5 b6 b7 with
  | intro val hdec =>
    cases hzero : Nat.beq val 0 with
    | true =>
      refine ⟨rfl, 0, evalEnumDiscr_niche_of_decode hdec hzero, ?_⟩
      exact wp_jcc_split false
        (fun _ => ⟨rfl, rfl, rfl, rfl, True.intro⟩)
        (fun h => Bool.noConfusion h)
    | false =>
      refine ⟨rfl, 1, evalEnumDiscr_niche_of_decode_ne hdec hzero, ?_⟩
      exact wp_jcc_split true
        (fun h => Bool.noConfusion h)
        (fun _ => ⟨rfl, rfl, rfl, rfl, True.intro⟩)

/-- End-to-end `CrateTheorem` for `unwrap_or_zero_niche(opt: Option<NonZeroUsize>) -> usize`. -/
theorem prove_unwrap_or_zero_niche_crate (fnName : String) :
    CrateTheorem {
      adts := enumCrateAdts
      libInv := enumCrateLibInv
      functions := [{ name := fnName, prog := unwrapOrZeroNicheBody }]
      tcb := [TCBItem.assemblerLowering fnName unwrapOrZeroNicheBody]
    } :=
  verify_single_fn_wf_crate_with_inv enumCrateAdts enumCrateLibInv
    enumCrateLibInv_admissible fnName unwrapOrZeroNicheBody
    (unwrapOrZeroNicheBody_verified fnName)

/-- `pub fn map_nonzero_to_opt(nz: NonZeroUsize) -> Option<NonZeroUsize> { Some(nz) }`:
    Under `TagEncoding::Niche`, constructing `Option::<NonZeroUsize>::Some(nz)`
    copies the 8-byte `NonZeroUsize` payload directly to offset `0..8` of the
    8-byte `Option<NonZeroUsize>` return slot `0` without writing a separate tag
    word! -/
def mapNonZeroToOptBody : X86Body where
  adts := enumCrateAdts
  argTys := [.adt 0]
  retTy := .adt 3
  slotCount := 2
  blocks := [
    { instrs := [
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨1⟩ 0 8 false)
      ]
      term := .ret }
  ]

/-- Specification asserting that every returned `Option<NonZeroUsize>` has
    logical discriminant `1` (`Some`) and preserves the input payload bytes. -/
def EnsuresSomeNicheDiscr (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=
  X86Lang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      evalEnumDiscr (.nicheOption 0 0) ret = some 1 ∧
      ret = (q.init.mem 1).bytes)

theorem takeBytes_self (bs : ByteVec) : takeBytes bs.length bs = bs := by
  induction bs with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [takeBytes]
    rw [ih]

theorem nonzero_hasTy_decompose (tySizes : Nat → Nat) (bs : ByteVec)
    (h : hasTy enumCrateAdts tySizes bs (.adt 0)) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : UInt8,
      bs = [some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7] := by
  have hlen : bs.length = 8 := h.1
  have hinit_slice : allBytesInit (takeBytes 8 bs) := h.2.1.2
  have htake : takeBytes 8 bs = bs := by
    rw [← hlen]
    exact takeBytes_self bs
  rw [htake] at hinit_slice
  exact decompose_bytes_8 ⟨hlen, hinit_slice⟩

theorem mapNonZeroToOptBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := mapNonZeroToOptBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv enumCrateLibInv fn.prog.retTy
        (fn.effectivePre enumCrateLibInv) := by
  intro fn
  refine verifyPubSafeRetByteLibInv 10 enumCrateLibInv fn True rfl
    (fun tySizes _ _ _ bs hty _ => ?_)
  let ⟨b0, b1, b2, b3, b4, b5, b6, b7, hbs⟩ := nonzero_hasTy_decompose tySizes bs hty
  subst hbs
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

/-- Functional specification proof for `mapNonZeroToOptBody`: because the input
    `nz : NonZeroUsize` satisfies `enumCrateLibInv` (`decodeLeBytes bs ≠ some 0`),
    its 8-byte niche encoding in `Option<NonZeroUsize>` is guaranteed to have
    logical discriminant `1` (`Some`)! -/
theorem mapNonZeroToOptBody_ensures_some_discr (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := mapNonZeroToOptBody }
    X86Sem fn.prog ≤
      EnsuresSomeNicheDiscr (fn.effectivePre enumCrateLibInv) := by
  intro fn
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  have hlib : allArgsByteLibInv enumCrateLibInv q.init.tySizes 1 fn.prog.argTys q.init.mem :=
    argsSatisfyLibInv_imp_allArgsByteLibInv fn.prog.adts enumCrateLibInv q.init.tySizes
      fn.prog.argTys q.init.mem 1 hpre.2.2
  have hwp_init :
      wpByteX86 10 fn.prog q.init (fun ret =>
        evalEnumDiscr (.nicheOption 0 0) ret = some 1 ∧
        ret = (q.init.mem 1).bytes) := by
    refine initX86State_canonical fn.prog q.init
      (fun s =>
        allArgsByteLibInv enumCrateLibInv s.tySizes 1 fn.prog.argTys s.mem →
        wpByteX86 10 fn.prog s (fun ret =>
          evalEnumDiscr (.nicheOption 0 0) ret = some 1 ∧
          ret = (s.mem 1).bytes))
      hpfx.1 ?_ hlib
    intro bs hty hargInv
    let ⟨b0, b1, b2, b3, b4, b5, b6, b7, hbs⟩ :=
      nonzero_hasTy_decompose q.init.tySizes bs hty
    subst hbs
    have hne0 : decodeLeBytes [some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7] ≠ some 0 :=
      hargInv.1.2
    cases decodeLeBytes_8_some b0 b1 b2 b3 b4 b5 b6 b7 with
    | intro val hdec =>
      have hbeq_false : Nat.beq val 0 = false := by
        cases hbeq : Nat.beq val 0 with
        | false => rfl
        | true =>
          have hval0 : val = 0 := eq_of_nat_beq_eq_true hbeq
          rw [hval0] at hdec
          exact False.elim (hne0 hdec)
      exact ⟨rfl, rfl, rfl, evalEnumDiscr_niche_of_decode_ne hdec hbeq_false, rfl⟩
  exact wpByteX86_sound 10 fn.prog q.init q.init _ hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- End-to-end `CrateTheorem` for `map_nonzero_to_opt(nz: NonZeroUsize) -> Option<NonZeroUsize>`
    including both `EnsuresRetLibInv` and `EnsuresSomeNicheDiscr`. -/
theorem prove_map_nonzero_to_opt_crate (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := mapNonZeroToOptBody
      specs := [EnsuresSomeNicheDiscr (CapturedFn.effectivePre enumCrateLibInv
        { name := fnName, prog := mapNonZeroToOptBody })]
    }
    CrateTheorem {
      adts := enumCrateAdts
      libInv := enumCrateLibInv
      functions := [fn]
      tcb := [TCBItem.assemblerLowering fnName mapNonZeroToOptBody]
    } := by
  intro fn
  refine ⟨(by intro h; cases h), enumCrateLibInv_admissible, ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  have hVerRet := Compiler.SoundOn.verify hAssumptions.1 (mapNonZeroToOptBody_verified fnName)
  have hVerSpec := Compiler.SoundOn.verify hAssumptions.1 (mapNonZeroToOptBody_ensures_some_discr fnName)
  have hWF := Compiler.Verified.mono hVerRet (ensuresRetLibInv_le_wellFormedOn _ _ _) hAssumptions.1.1
  exact ⟨hWF, hVerRet, hVerSpec, True.intro⟩

/-- Direct-tagged `pub fn unwrap_or_zero_direct(opt: Option<usize>) -> usize`
    (`id := 2`, 16B `TagEncoding::Direct`):
    - Reads the 8-byte discriminant at offset `0..8` via `.discriminant ⟨2⟩ ⟨1⟩ 2`.
    - When discriminant is `0` (`None`), branches to `bb1` and returns `0`
      without reading the uninitialized payload bytes at `8..16`!
    - When discriminant is `1` (`Some`), branches to `bb2` and copies the 8-byte
      payload from offset `8..16` (`slotSlice ⟨1⟩ 8 8`) into return slot `0`. -/
def unwrapOrZeroDirectBody : X86Body where
  adts := enumCrateAdts
  argTys := [.adt 2]
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 1,
        .discriminant ⟨2⟩ ⟨1⟩ 2,
        .alu .eq 8 ⟨3⟩ 0 (.slotSlice ⟨2⟩ 0 8 true) (.immWord 8 1)
      ]
      term := .jccBool (.slotSlice ⟨3⟩ 0 1 true) ⟨1⟩ ⟨2⟩ },
    -- bb1 (None): return 0
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩,
        .movSlice ⟨0⟩ 0 (.immWord 8 0)
      ]
      term := .ret },
    -- bb2 (Some): return payload at offset 8..16
    { instrs := [
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨2⟩,
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨1⟩ 8 8 false)
      ]
      term := .ret }
  ]

theorem direct_option_hasTy_decompose (tySizes : Nat → Nat) (bs : ByteVec)
    (h : hasTy enumCrateAdts tySizes bs (.adt 2)) :
    (∃ (t0 t1 t2 t3 t4 t5 t6 t7 : UInt8) (p0 p1 p2 p3 p4 p5 p6 p7 : Option UInt8),
      bs = [some t0, some t1, some t2, some t3, some t4, some t5, some t6, some t7,
            p0, p1, p2, p3, p4, p5, p6, p7] ∧
      decodeLeBytes [some t0, some t1, some t2, some t3, some t4, some t5, some t6, some t7] = some 0) ∨
    (∃ (t0 t1 t2 t3 t4 t5 t6 t7 v0 v1 v2 v3 v4 v5 v6 v7 : UInt8),
      bs = [some t0, some t1, some t2, some t3, some t4, some t5, some t6, some t7,
            some v0, some v1, some v2, some v3, some v4, some v5, some v6, some v7] ∧
      decodeLeBytes [some t0, some t1, some t2, some t3, some t4, some t5, some t6, some t7] = some 1) := by
  have hlen : bs.length = 16 := h.1
  cases bs with
  | nil => cases hlen
  | cons x0 r1 =>
  cases r1 with
  | nil => cases hlen
  | cons x1 r2 =>
  cases r2 with
  | nil => cases hlen
  | cons x2 r3 =>
  cases r3 with
  | nil => cases hlen
  | cons x3 r4 =>
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
  | nil => cases hlen
  | cons p0 r9 =>
  cases r9 with
  | nil => cases hlen
  | cons p1 r10 =>
  cases r10 with
  | nil => cases hlen
  | cons p2 r11 =>
  cases r11 with
  | nil => cases hlen
  | cons p3 r12 =>
  cases r12 with
  | nil => cases hlen
  | cons p4 r13 =>
  cases r13 with
  | nil => cases hlen
  | cons p5 r14 =>
  cases r14 with
  | nil => cases hlen
  | cons p6 r15 =>
  cases r15 with
  | nil => cases hlen
  | cons p7 r16 =>
  cases r16 with
  | cons _ _ => cases hlen
  | nil =>
    have htag_or := h.2
    dsimp [extractSlice, dropBytes, takeBytes] at htag_or
    have htag_some :
        decodeLeBytes [x0, x1, x2, x3, x4, x5, x6, x7] = some 0 ∨
        decodeLeBytes [x0, x1, x2, x3, x4, x5, x6, x7] = some 1 := by
      cases htag_or with
      | inl h0 => exact Or.inl h0
      | inr h1 => exact Or.inr h1.1
    cases x0 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t0 =>
    cases x1 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t1 =>
    cases x2 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t2 =>
    cases x3 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t3 =>
    cases x4 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t4 =>
    cases x5 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t5 =>
    cases x6 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t6 =>
    cases x7 with
    | none => cases htag_some with | inl h0 => cases h0 | inr h1 => cases h1
    | some t7 =>
      cases htag_or with
      | inl h0 =>
        exact Or.inl ⟨t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6, p7, rfl, h0⟩
      | inr h1 =>
        have hp_init : allBytesInit [p0, p1, p2, p3, p4, p5, p6, p7] := h1.2.2
        cases p0 with
        | none => cases hp_init
        | some v0 =>
        cases p1 with
        | none => cases hp_init
        | some v1 =>
        cases p2 with
        | none => cases hp_init
        | some v2 =>
        cases p3 with
        | none => cases hp_init
        | some v3 =>
        cases p4 with
        | none => cases hp_init
        | some v4 =>
        cases p5 with
        | none => cases hp_init
        | some v5 =>
        cases p6 with
        | none => cases hp_init
        | some v6 =>
        cases p7 with
        | none => cases hp_init
        | some v7 =>
          exact Or.inr ⟨t0, t1, t2, t3, t4, t5, t6, t7, v0, v1, v2, v3, v4, v5, v6, v7, rfl, h1.1⟩

theorem unwrapOrZeroDirectBody_verified (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := unwrapOrZeroDirectBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv enumCrateLibInv fn.prog.retTy
        (fn.effectivePre enumCrateLibInv) := by
  intro fn
  refine verifyPubSafeRetByteLibInv 20 enumCrateLibInv fn True rfl
    (fun tySizes _ _ _ bs hty _ => ?_)
  cases direct_option_hasTy_decompose tySizes bs hty with
  | inl hnone =>
    let ⟨t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6, p7, hbs, htag0⟩ := hnone
    subst hbs
    refine ⟨rfl, 0, evalEnumDiscr_direct_0 htag0, ?_⟩
    exact wp_jcc_split false
      (fun _ => ⟨rfl, rfl, rfl, rfl, True.intro⟩)
      (fun h => Bool.noConfusion h)
  | inr hsome =>
    let ⟨t0, t1, t2, t3, t4, t5, t6, t7, v0, v1, v2, v3, v4, v5, v6, v7, hbs, htag1⟩ := hsome
    subst hbs
    refine ⟨rfl, 1, evalEnumDiscr_direct_1 htag1, ?_⟩
    exact wp_jcc_split true
      (fun h => Bool.noConfusion h)
      (fun _ => ⟨rfl, rfl, rfl, rfl, True.intro⟩)

/-- End-to-end `CrateTheorem` for `unwrap_or_zero_direct(opt: Option<usize>) -> usize`. -/
theorem prove_unwrap_or_zero_direct_crate (fnName : String) :
    CrateTheorem {
      adts := enumCrateAdts
      libInv := enumCrateLibInv
      functions := [{ name := fnName, prog := unwrapOrZeroDirectBody }]
      tcb := [TCBItem.assemblerLowering fnName unwrapOrZeroDirectBody]
    } :=
  verify_single_fn_wf_crate_with_inv enumCrateAdts enumCrateLibInv
    enumCrateLibInv_admissible fnName unwrapOrZeroDirectBody
    (unwrapOrZeroDirectBody_verified fnName)

/-- Buggy `Option<usize>` function that reads the payload at offset `8..16` and
    adds `1` without checking the discriminant (failing with `.failed .ub` when
    `opt` is `None` with uninitialized `none` payload bytes). -/
def badUncheckedDirectOptionBody : X86Body where
  adts := enumCrateAdts
  argTys := [.adt 2]
  retTy := .usize
  slotCount := 2
  blocks := [
    { instrs := [
        .alu .add 8 ⟨0⟩ 0 (.slotSlice ⟨1⟩ 8 8 false) (.immWord 8 1)
      ]
      term := .ret }
  ]

/-- Negative adequacy canary for direct-tagged enums: reading the payload of
    `Option::<usize>::None` (tag `0` at `0..8`, uninitialized `none` padding at
    `8..16`) and performing an ALU operation triggers `.failed .ub`, refuting
    `CrateTheorem`! -/
theorem canary_direct_option_uninit_payload_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn badUncheckedDirectOptionBody) :
    ¬ CrateTheorem {
      adts := enumCrateAdts
      libInv := enumCrateLibInv
      functions := [{ name := fnName, prog := badUncheckedDirectOptionBody }]
      tcb := [TCBItem.assemblerLowering fnName badUncheckedDirectOptionBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let noneBytes : ByteVec := encodeLeBytes 8 0 ++ replicateBytes 8 none
  have hnone_ty : hasTy enumCrateAdts (fun _ => 0) noneBytes (.adt 2) :=
    ⟨rfl, Or.inl rfl⟩
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 16, bytes := noneBytes, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hinit : initX86State badUncheckedDirectOptionBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨noneBytes, rfl, hnone_ty⟩, True.intro⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) badUncheckedDirectOptionBody := by
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
      CapturedFn.effectivePre enumCrateLibInv
        { name := fnName, prog := badUncheckedDirectOptionBody } q :=
    ⟨hmono, True.intro, ⟨noneBytes, rfl, hnone_ty⟩, True.intro⟩
  have hr0 : ReachesPrefix X86Machine badUncheckedDirectOptionBody s0 1 s0 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s0 .ub rfl
  exact (hWF q hpre).1 hinit [] (.failed .ub) hr0

/-- Buggy `Option<NonZeroUsize> -> NonZeroUsize` function that projects the
    niche-encoded payload (`((_1 as Some).0)` at offset `0..8`) into a
    `NonZeroUsize` return slot without checking the discriminant (`0` vs `1`),
    allowing the niche value `0` (`None`) to forge a zero `NonZeroUsize`! -/
def badUncheckedNicheUnwrapBody : X86Body where
  adts := enumCrateAdts
  argTys := [.adt 3]
  retTy := .adt 0
  slotCount := 2
  blocks := [
    { instrs := [
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨1⟩ 0 8 false)
      ]
      term := .ret }
  ]

/-- Negative adequacy canary for niche-encoded enums: projecting `((_1 as Some).0)`
    out of `Option::<NonZeroUsize>::None` (`encodeLeBytes 8 0`) into `NonZeroUsize`
    without checking `.discriminant` returns `encodeLeBytes 8 0`, violating
    `enumCrateLibInv`'s `decodeLeBytes ret ≠ some 0` obligation in
    `EnsuresRetLibInv` and refuting `CrateTheorem`! -/
theorem canary_niche_forged_zero_nonzero_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn badUncheckedNicheUnwrapBody) :
    ¬ CrateTheorem {
      adts := enumCrateAdts
      libInv := enumCrateLibInv
      functions := [{ name := fnName, prog := badUncheckedNicheUnwrapBody }]
      tcb := [TCBItem.assemblerLowering fnName badUncheckedNicheUnwrapBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hRetInv := hFnVer.2.1.1
  let zeroBytes : ByteVec := encodeLeBytes 8 0
  have hzero_ty : hasTy enumCrateAdts (fun _ => 0) zeroBytes (.adt 3) :=
    ⟨rfl, True.intro⟩
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := zeroBytes, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hinit : initX86State badUncheckedNicheUnwrapBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨zeroBytes, rfl, hzero_ty⟩, True.intro⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) badUncheckedNicheUnwrapBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 2 }
  have hpre :
      CapturedFn.effectivePre enumCrateLibInv
        { name := fnName, prog := badUncheckedNicheUnwrapBody } q :=
    ⟨hmono, True.intro, ⟨zeroBytes, rfl, hzero_ty⟩, True.intro⟩
  let m1 := updateAlloc mem0 0 { perm := .readWrite, size := 8, bytes := zeroBytes, written := true }
  let s1 : X86State := { s0 with mem := m1, ip := 1 }
  have hr1 : ReachesPrefix X86Machine badUncheckedNicheUnwrapBody s0 1 s1 [] (.terminated (.normal zeroBytes)) :=
    ReachesPrefix.terminated 0 s1 (.normal zeroBytes) rfl
  have hr0 : ReachesPrefix X86Machine badUncheckedNicheUnwrapBody s0 2 s0 [()] (.terminated (.normal zeroBytes)) :=
    ReachesPrefix.step 1 s0 s1 () [] _ rfl hr1
  have hPost := (hRetInv q hpre).2 { trace := [()], outcome := .terminated (.normal zeroBytes) } ⟨hinit, hr0⟩
  have hInv0 : enumCrateLibInv (fun _ => 0) (.adt 0) zeroBytes := hPost zeroBytes rfl
  exact hInv0.2 rfl

/-!
## 10. Wide Pointers / Slices (`&[u32]`), `PtrMetadata`, and Bounds-Checked Indexing
-/

/-- Caller validity invariant for a shared slice reference `slice: &[u32]`
    passed in slot `1` pointing into caller buffer allocation `⟨6⟩`:
    - Slot `1` holds provenance pointer `{ alloc := ⟨6⟩, offset := baseOff }`.
    - Pointee allocation `⟨6⟩` is readable, initialized (`written = true`), and
      has `bytes.length = size`.
    - For the element count `len` stored in the wide pointer's 8-byte metadata
      at offset `8..16` of slot `1`, every in-bounds element index `idx < len`
      lies within `(s.mem 6).size` (`4 + (baseOff + idx * 4) ≤ (s.mem 6).size`)
      and its 4 element bytes are initialized (`allBytesInit`). -/
def SliceArgValid (s : X86State) : Prop :=
  ∃ (baseOff : Nat),
    (s.mem 1).ptr = some { alloc := ⟨6⟩, offset := baseOff } ∧
    (s.mem 6).perm.canRead = true ∧
    (s.mem 6).written = true ∧
    (s.mem 6).bytes.length = (s.mem 6).size ∧
    ∀ (len idx : Nat),
      decodeLeBytes (extractSlice (s.mem 1).bytes 8 8) = some len →
      Nat.blt idx len = true →
      Nat.ble (4 + (baseOff + idx * 4)) (s.mem 6).size = true ∧
      allBytesInit (extractSlice (s.mem 6).bytes (baseOff + idx * 4) 4)

theorem sliceArgValid_canonical {s : X86State} {blk1 blk6 : AllocBlock}
    (h1 : s.mem 1 = blk1) (h6 : s.mem 6 = blk6)
    (h : SliceArgValid s) :
    ∃ (baseOff : Nat),
      blk1.ptr = some { alloc := ⟨6⟩, offset := baseOff } ∧
      blk6.perm.canRead = true ∧
      blk6.written = true ∧
      blk6.bytes.length = blk6.size ∧
      ∀ (len idx : Nat),
        decodeLeBytes (extractSlice blk1.bytes 8 8) = some len →
        Nat.blt idx len = true →
        Nat.ble (4 + (baseOff + idx * 4)) blk6.size = true ∧
        allBytesInit (extractSlice blk6.bytes (baseOff + idx * 4) 4) := by
  dsimp only [SliceArgValid] at h
  rw [h1, h6] at h
  exact h

/-- `pub fn slice_get_checked(slice: &[u32], idx: usize) -> u32 { slice[idx] }`:
    - `bb0`: extracts the 8-byte slice length metadata into slot `3` via
      `.ptrMetadata ⟨3⟩ ⟨1⟩`, compares `idx < len` into boolean slot `4`, and
      branches via `.jccBool (.slotSlice ⟨4⟩ 0 1 true) ⟨2⟩ ⟨1⟩`.
    - `bb1` (in-bounds `idx < len`): computes element pointer `&slice[idx]` in
      slot `5` via `.ptrOffsetIndex ⟨5⟩ ⟨1⟩ (.slotSlice ⟨2⟩ 0 8 true) 4` and
      loads 4 bytes into return slot `0` via `.loadPtr ⟨0⟩ 0 ⟨5⟩ 4`.
    - `bb2` (out-of-bounds `!(idx < len)`): panics via `.abortPanic`
      (`.terminated .unwind`, which is safe). -/
def sliceGetCheckedBody : X86Body where
  argTys := [.slice .u32, .usize]
  retTy := .u32
  slotCount := 6
  blocks := [
    { instrs := [
        .allocSlot ⟨3⟩ 8,
        .allocSlot ⟨4⟩ 1,
        .allocSlot ⟨5⟩ 8,
        .ptrMetadata ⟨3⟩ ⟨1⟩,
        .alu .lt 8 ⟨4⟩ 0 (.slotSlice ⟨2⟩ 0 8 false) (.slotSlice ⟨3⟩ 0 8 false)
      ]
      term := .jccBool (.slotSlice ⟨4⟩ 0 1 true) ⟨2⟩ ⟨1⟩ },
    -- bb1 (idx < len): compute element pointer and load u32
    { instrs := [
        .ptrOffsetIndex ⟨5⟩ ⟨1⟩ (.slotSlice ⟨2⟩ 0 8 true) 4,
        .loadPtr ⟨0⟩ 0 ⟨5⟩ 4,
        .deallocSlot ⟨5⟩,
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩
      ]
      term := .ret },
    -- bb2 (!(idx < len)): bounds-check panic
    { instrs := []
      term := .abortPanic }
  ]

/-- Helper lemma discharging `.loadPtr` and `.ret` obligations for loading a
    4-byte `u32` element from a caller slice buffer `blk6` at `off`. -/
theorem u32_load_wp_obligations (tySizes : Nat → Nat) (blk6 : AllocBlock) (off : Nat)
    (hread : blk6.perm.canRead = true)
    (hwrit : blk6.written = true)
    (hsz : blk6.bytes.length = blk6.size)
    (hble : Nat.ble (4 + off) blk6.size = true)
    (hinit : allBytesInit (extractSlice blk6.bytes off 4)) :
    let bs := extractSlice blk6.bytes off 4
    blk6.perm.canRead = true ∧
    blk6.written = true ∧
    Nat.ble (4 + off) blk6.size = true ∧
    Nat.ble (4 + off) blk6.bytes.length = true ∧
    Nat.ble (bs.length + 0) 4 = true ∧
    (writeSlice [none, none, none, none] 0 bs).length = 4 ∧
    defaultLibInv [] tySizes .u32 (writeSlice [none, none, none, none] 0 bs) := by
  have hble_len : Nat.ble (4 + off) blk6.bytes.length = true := by
    rw [hsz]
    exact hble
  have hlen4 : (extractSlice blk6.bytes off 4).length = 4 :=
    extractSlice_length_of_ble off blk6.bytes 4 hble_len
  have hw : writeSlice [none, none, none, none] 0 (extractSlice blk6.bytes off 4) =
      extractSlice blk6.bytes off 4 :=
    writeSlice_zero_of_eq_length [none, none, none, none] (extractSlice blk6.bytes off 4) hlen4.symm
  refine ⟨hread, hwrit, hble, hble_len, ?_, ?_, ?_⟩
  · rw [Nat.add_zero, hlen4]
    rfl
  · rw [hw, hlen4]
  · dsimp [defaultLibInv, hasTy, hasFieldTy]
    rw [hw]
    exact ⟨hlen4, hinit⟩

/-- `sliceGetCheckedBody` verified via `wpByteX86` under `SliceArgValid`. -/
theorem sliceGetCheckedBody_verified (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := sliceGetCheckedBody
      kind := .pubUnsafe True (fun q => SliceArgValid q.init)
    }
    X86Sem fn.prog ≤
      EnsuresRetLibInv (defaultLibInv []) fn.prog.retTy
        (fn.effectivePre (defaultLibInv [])) := by
  intro fn
  refine verifyPubUnsafeRetByteLibInv 20 (defaultLibInv []) fn True
    (fun q => SliceArgValid q.init) rfl
    (fun tySizes _ baseMem _ _ p a0 a1 a2 a3 a4 a5 a6 a7 l0 l1 l2 l3 l4 l5 l6 l7
         i0 i1 i2 i3 i4 i5 i6 i7 _ hslice => ?_)
  let sliceBlk1 : AllocBlock := {
    perm := .readWrite, size := 16,
    bytes := [some a0, some a1, some a2, some a3, some a4, some a5, some a6, some a7,
              some l0, some l1, some l2, some l3, some l4, some l5, some l6, some l7],
    ptr := some p, written := true
  }
  cases sliceArgValid_canonical (blk1 := sliceBlk1) (blk6 := baseMem 6) rfl rfl hslice with
  | intro baseOff hsb =>
    injection hsb.1 with hp
    subst hp
    let len0 := l0.toNat + 256 * (l1.toNat + 256 * (l2.toNat + 256 * (l3.toNat +
      256 * (l4.toNat + 256 * (l5.toNat + 256 * (l6.toNat + 256 * (l7.toNat + 256 * 0)))))))
    let idx0 := i0.toNat + 256 * (i1.toNat + 256 * (i2.toNat + 256 * (i3.toNat +
      256 * (i4.toNat + 256 * (i5.toNat + 256 * (i6.toNat + 256 * (i7.toNat + 256 * 0)))))))
    refine wp_jcc_split (Nat.blt idx0 len0) (fun _ => True.intro) (fun hlt0 => ?_)
    dsimp only
    cases decodeLeBytes_8_some i0 i1 i2 i3 i4 i5 i6 i7 with
    | intro idx hidx =>
      have hidx_some : some idx0 = some idx := hidx
      injection hidx_some with hidx_eq
      rw [hidx_eq] at hlt0
      have helem := hsb.2.2.2.2 len0 idx rfl hlt0
      have hpost := u32_load_wp_obligations tySizes (baseMem 6) (baseOff + idx * 4)
        hsb.2.1 hsb.2.2.1 hsb.2.2.2.1 helem.1 helem.2
      exact ⟨rfl, rfl, idx, { alloc := ⟨6⟩, offset := baseOff }, hidx, rfl,
             hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, rfl,
             hpost.2.2.2.2.1, hpost.2.2.2.2.1, rfl, rfl,
             hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2⟩

/-- End-to-end `CrateTheorem` for `slice_get_checked(slice: &[u32], idx: usize) -> u32`. -/
theorem prove_slice_get_checked_crate (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := sliceGetCheckedBody
      kind := .pubUnsafe True (fun q => SliceArgValid q.init)
    }
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [fn]
      tcb := [TCBItem.assemblerLowering fnName sliceGetCheckedBody]
    } := by
  intro fn
  refine ⟨(by intro h; cases h), defaultLibInv_admissible [], ⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hAssumptions
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hAssumptions.1 (sliceGetCheckedBody_verified fnName))
    (ensuresRetLibInv_le_wellFormedOn _ _ _)
    hAssumptions.1.1

/-- Negative adequacy canary for wide slices: if `sliceGetCheckedBody` is
    verified WITHOUT the wide-pointer slice validity invariant (`pre := True`),
    a caller can pass a forged wide slice `(ptr = ⟨6, 0⟩, len = 4)` pointing to
    an 8-byte `[u32; 2]` buffer at slot `6` along with `idx = 2`. The dynamic
    bounds check `idx < len` (`2 < 4`) succeeds and branches to `bb1`, where
    `.loadPtr` attempts to read bytes `8..12` from an 8-byte allocation and
    triggers `.failed .ub`, refuting `CrateTheorem`! -/
theorem canary_forged_slice_len_oob_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn sliceGetCheckedBody) :
    ¬ CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := sliceGetCheckedBody }]
      tcb := [TCBItem.assemblerLowering fnName sliceGetCheckedBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let sliceBytes : ByteVec := encodeLeBytes 8 0 ++ encodeLeBytes 8 4
  let idxBytes : ByteVec := encodeLeBytes 8 2
  let bufBytes : ByteVec := encodeLeBytes 4 10 ++ encodeLeBytes 4 20
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 4, bytes := replicateBytes 4 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 16, bytes := sliceBytes,
    ptr := some { alloc := ⟨6⟩, offset := 0 }, written := true
  }
  let argBlk2 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := idxBytes, ptr := none, written := true
  }
  let bufBlk6 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := bufBytes, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (updateAlloc (updateAlloc (fun _ => unallocBlock)
      6 bufBlk6) 0 retBlk0) 1 argBlk1) 2 argBlk2
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hslice_ty : hasTy [] (fun _ => 0) sliceBytes (.slice .u32) :=
    ⟨rfl, True.intro⟩
  have hidx_ty : hasTy [] (fun _ => 0) idxBytes .usize :=
    ⟨rfl, True.intro⟩
  have hinit : initX86State sliceGetCheckedBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl,
     ⟨⟨{ alloc := ⟨6⟩, offset := 0 }, sliceBytes, rfl, hslice_ty⟩,
      ⟨⟨idxBytes, rfl, hidx_ty⟩, True.intro⟩⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) sliceGetCheckedBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ h1 =>
        cases h1 with
        | head => cases hterm
        | tail _ h2 =>
          cases h2 with
          | head => cases hterm
          | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 8 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [])
        { name := fnName, prog := sliceGetCheckedBody } q :=
    ⟨hmono, True.intro,
     ⟨{ alloc := ⟨6⟩, offset := 0 }, sliceBytes, rfl, hslice_ty⟩,
     ⟨idxBytes, rfl, hidx_ty⟩, True.intro⟩
  -- Trace the 7 steps from s0 to the OOB .loadPtr in bb1:
  let m1 := updateAlloc mem0 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none }
  let s1 : X86State := { s0 with mem := m1, ip := 1 }
  let m2 := updateAlloc m1 4 { perm := .readWrite, size := 1, bytes := replicateBytes 1 none }
  let s2 : X86State := { s1 with mem := m2, ip := 2 }
  let m3 := updateAlloc m2 5 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none }
  let s3 : X86State := { s2 with mem := m3, ip := 3 }
  let m4 := updateAlloc m3 3 { perm := .readWrite, size := 8, bytes := encodeLeBytes 8 4, written := true }
  let s4 : X86State := { s3 with mem := m4, ip := 4 }
  let m5 := updateAlloc m4 4 { perm := .readWrite, size := 1, bytes := [some 1], written := true }
  let s5 : X86State := { s4 with mem := m5, ip := 5 }
  let m6 := updateAlloc m5 4 { perm := .readWrite, size := 1, bytes := [none], written := true }
  let s6 : X86State := { s5 with mem := m6, bb := 1, ip := 0 }
  let m7 := updateAlloc (updateAlloc m6 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, written := true })
    5 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨6⟩, offset := 8 }, written := true }
  let s7 : X86State := { s6 with mem := m7, bb := 1, ip := 1 }
  have hr7 : ReachesPrefix X86Machine sliceGetCheckedBody s0 1 s7 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s7 .ub rfl
  have hr6 : ReachesPrefix X86Machine sliceGetCheckedBody s0 2 s6 [()] (.failed .ub) :=
    ReachesPrefix.step 1 s6 s7 () [] _ rfl hr7
  have hr5 : ReachesPrefix X86Machine sliceGetCheckedBody s0 3 s5 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s5 s6 () [()] _ rfl hr6
  have hr4 : ReachesPrefix X86Machine sliceGetCheckedBody s0 4 s4 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s4 s5 () [(), ()] _ rfl hr5
  have hr3 : ReachesPrefix X86Machine sliceGetCheckedBody s0 5 s3 [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s3 s4 () [(), (), ()] _ rfl hr4
  have hr2 : ReachesPrefix X86Machine sliceGetCheckedBody s0 6 s2 [(), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 5 s2 s3 () [(), (), (), ()] _ rfl hr3
  have hr1 : ReachesPrefix X86Machine sliceGetCheckedBody s0 7 s1 [(), (), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 6 s1 s2 () [(), (), (), (), ()] _ rfl hr2
  have hr0 : ReachesPrefix X86Machine sliceGetCheckedBody s0 8 s0 [(), (), (), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 7 s0 s1 () [(), (), (), (), (), ()] _ rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), (), (), (), ()] (.failed .ub) hr0

/-- Constructing a wide slice `&[u32]` of length `2` over a stack-allocated
    2-element `u32` array `[100, 200]` (`8B` in slot `⟨1⟩`) via `.makeSlice`,
    extracting its length via `.ptrMetadata`, indexing element `1` via
    `.ptrOffsetIndex`, and loading `200`. -/
def sliceMakeAndGetBody : X86Body where
  adts := []
  argTys := []
  retTy := .u32
  slotCount := 6
  blocks := [
    { instrs := [
        .allocSlot ⟨1⟩ 8,
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 16,
        .allocSlot ⟨4⟩ 8,
        .allocSlot ⟨5⟩ 8,
        .movSlice ⟨1⟩ 0 (.immWord 4 100),
        .movSlice ⟨1⟩ 4 (.immWord 4 200),
        .leaSlot ⟨2⟩ ⟨1⟩ 0,
        .makeSlice ⟨3⟩ ⟨2⟩ (.immWord 8 2),
        .ptrMetadata ⟨4⟩ ⟨3⟩,
        .ptrOffsetIndex ⟨5⟩ ⟨3⟩ (.immWord 8 1) 4,
        .loadPtr ⟨0⟩ 0 ⟨5⟩ 4
      ]
      term := .ret }
  ]

theorem sliceMakeAndGetBody_verified (fnName : String) :
    X86Sem sliceMakeAndGetBody ≤
      EnsuresRetLibInv (defaultLibInv []) .u32
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := sliceMakeAndGetBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 15 (defaultLibInv [])
    { name := fnName, prog := sliceMakeAndGetBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ _
  exact ⟨rfl, rfl, 1, { alloc := ⟨1⟩, offset := 0 }, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_slice_make_and_get_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := sliceMakeAndGetBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName sliceMakeAndGetBody]
    } :=
  verify_single_fn_wf_crate [] fnName sliceMakeAndGetBody
    (sliceMakeAndGetBody_verified fnName)

theorem sliceMakeAndGetBody_ensures_200 :
    X86Sem sliceMakeAndGetBody ≤
      X86Lang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret = encodeLeBytes 4 200) := by
  refine verifyByteX86Spec 15 sliceMakeAndGetBody
    (fun _ ret => ret = encodeLeBytes 4 200) ?_
  intro tySizes baseMem
  exact ⟨rfl, rfl, 1, { alloc := ⟨1⟩, offset := 0 }, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl⟩

/-!
## 11. `copy_nonoverlapping` Spatial Disjointness & Byte Copy
-/

/-- `pub fn copy_u32_distinct_slots(x: u32) -> u32`:
    allocates a local 4-byte `u32` slot `⟨2⟩`, takes pointers to `x` (`⟨1⟩` in
    pointer slot `⟨3⟩`) and `dst` (`⟨2⟩` in pointer slot `⟨4⟩`), runs
    `copy_nonoverlapping(dst, src, 4)` (`X86Instr.copyNonOverlapping ⟨4⟩ ⟨3⟩ 4`),
    and moves `dst` into return slot `⟨0⟩`. -/
def copyNonOverlappingDistinctSlotsBody : X86Body where
  adts := []
  argTys := [.u32]
  retTy := .u32
  slotCount := 5
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 4,
        .allocSlot ⟨3⟩ 8,
        .allocSlot ⟨4⟩ 8,
        .leaSlot ⟨3⟩ ⟨1⟩ 0,
        .leaSlot ⟨4⟩ ⟨2⟩ 0,
        .copyNonOverlapping ⟨4⟩ ⟨3⟩ 4,
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨2⟩ 0 4 true)
      ]
      term := .ret }
  ]

theorem copyNonOverlappingDistinctSlotsBody_verified (fnName : String) :
    X86Sem copyNonOverlappingDistinctSlotsBody ≤
      EnsuresRetLibInv (defaultLibInv []) .u32
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := copyNonOverlappingDistinctSlotsBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 10 (defaultLibInv [])
    { name := fnName, prog := copyNonOverlappingDistinctSlotsBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ x0 x1 x2 x3 _
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_copy_nonoverlapping_distinct_slots_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := copyNonOverlappingDistinctSlotsBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName copyNonOverlappingDistinctSlotsBody]
    } :=
  verify_single_fn_wf_crate [] fnName copyNonOverlappingDistinctSlotsBody
    (copyNonOverlappingDistinctSlotsBody_verified fnName)

theorem copyNonOverlappingDistinctSlotsBody_preserves_bytes :
    X86Sem copyNonOverlappingDistinctSlotsBody ≤
      X86Lang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret = (q.init.mem 1).bytes) := by
  refine verifyByteX86Spec 10 copyNonOverlappingDistinctSlotsBody
    (fun s₀ ret => ret = (s₀.mem 1).bytes) ?_
  intro tySizes baseMem x0 x1 x2 x3
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `pub fn copy_u32_disjoint_subslices_same_alloc(x: u32) -> u32`:
    allocates an 8-byte `[u32; 2]` buffer in slot `⟨2⟩`, writes `x` to the first
    half (`offset 0..4`), takes pointers to `offset 0..4` (`⟨3⟩`) and
    `offset 4..8` (`⟨4⟩`) within the **same** allocation `⟨2⟩`, runs
    `copy_nonoverlapping(dst, src, 4)`, and returns the second half
    (`offset 4..8`). -/
def copyNonOverlappingSubSlicesBody : X86Body where
  adts := []
  argTys := [.u32]
  retTy := .u32
  slotCount := 5
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 8,
        .allocSlot ⟨4⟩ 8,
        .movSlice ⟨2⟩ 0 (.slotSlice ⟨1⟩ 0 4 false),
        .leaSlot ⟨3⟩ ⟨2⟩ 0,
        .leaSlot ⟨4⟩ ⟨2⟩ 4,
        .copyNonOverlapping ⟨4⟩ ⟨3⟩ 4,
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨2⟩ 4 4 true)
      ]
      term := .ret }
  ]

theorem copyNonOverlappingSubSlicesBody_verified (fnName : String) :
    X86Sem copyNonOverlappingSubSlicesBody ≤
      EnsuresRetLibInv (defaultLibInv []) .u32
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := copyNonOverlappingSubSlicesBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 10 (defaultLibInv [])
    { name := fnName, prog := copyNonOverlappingSubSlicesBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ x0 x1 x2 x3 _
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_copy_nonoverlapping_subslices_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := copyNonOverlappingSubSlicesBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName copyNonOverlappingSubSlicesBody]
    } :=
  verify_single_fn_wf_crate [] fnName copyNonOverlappingSubSlicesBody
    (copyNonOverlappingSubSlicesBody_verified fnName)

theorem copyNonOverlappingSubSlicesBody_preserves_bytes :
    X86Sem copyNonOverlappingSubSlicesBody ≤
      X86Lang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret = (q.init.mem 1).bytes) := by
  refine verifyByteX86Spec 10 copyNonOverlappingSubSlicesBody
    (fun s₀ ret => ret = (s₀.mem 1).bytes) ?_
  intro tySizes baseMem x0 x1 x2 x3
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Negative canary: attempting `copy_nonoverlapping` of 4 bytes from `offset 0..4`
    to `offset 2..6` within the same 8-byte buffer (`⟨1⟩`) overlaps on bytes `2..4`
    and must fail with `.failed .ub`. -/
def badOverlappingCopyBody : X86Body where
  adts := []
  argTys := []
  retTy := .u32
  slotCount := 4
  blocks := [
    { instrs := [
        .allocSlot ⟨1⟩ 8,
        .allocSlot ⟨2⟩ 8,
        .allocSlot ⟨3⟩ 8,
        .movSlice ⟨1⟩ 0 (.immWord 8 0x0102030405060708),
        .leaSlot ⟨2⟩ ⟨1⟩ 0,
        .leaSlot ⟨3⟩ ⟨1⟩ 2,
        .copyNonOverlapping ⟨3⟩ ⟨2⟩ 4,
        .movSlice ⟨0⟩ 0 (.slotSlice ⟨1⟩ 2 4 true)
      ]
      term := .ret }
  ]

theorem canary_copy_nonoverlapping_overlapping_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn badOverlappingCopyBody) :
    ¬ CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := badOverlappingCopyBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName badOverlappingCopyBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 4, bytes := replicateBytes 4 none, ptr := none, written := false
  }
  let mem0 : Nat → AllocBlock := updateAlloc (fun _ => unallocBlock) 0 retBlk0
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hinit : initX86State badOverlappingCopyBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have hmono : MonoAdmitted (fun _ => 0) badOverlappingCopyBody := by
    intro _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  let q : ExecQuery X86State := { init := s0, steps := 7 }
  have hpre :
      CapturedFn.effectivePre (defaultLibInv [])
        { name := fnName, prog := badOverlappingCopyBody } q :=
    ⟨hmono, True.intro, True.intro⟩
  let m1 := updateAlloc mem0 1 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none }
  let s1 : X86State := { s0 with mem := m1, ip := 1 }
  let m2 := updateAlloc m1 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none }
  let s2 : X86State := { s1 with mem := m2, ip := 2 }
  let m3 := updateAlloc m2 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none }
  let s3 : X86State := { s2 with mem := m3, ip := 3 }
  let m4 := updateAlloc m3 1 { perm := .readWrite, size := 8, bytes := encodeLeBytes 8 0x0102030405060708, written := true }
  let s4 : X86State := { s3 with mem := m4, ip := 4 }
  let m5 := updateAlloc m4 2 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 0 }, written := true }
  let s5 : X86State := { s4 with mem := m5, ip := 5 }
  let m6 := updateAlloc m5 3 { perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := some { alloc := ⟨1⟩, offset := 2 }, written := true }
  let s6 : X86State := { s5 with mem := m6, ip := 6 }
  have hr6 : ReachesPrefix X86Machine badOverlappingCopyBody s0 1 s6 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s6 .ub rfl
  have hr5 : ReachesPrefix X86Machine badOverlappingCopyBody s0 2 s5 [()] (.failed .ub) :=
    ReachesPrefix.step 1 s5 s6 () [] _ rfl hr6
  have hr4 : ReachesPrefix X86Machine badOverlappingCopyBody s0 3 s4 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s4 s5 () [()] _ rfl hr5
  have hr3 : ReachesPrefix X86Machine badOverlappingCopyBody s0 4 s3 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s3 s4 () [(), ()] _ rfl hr4
  have hr2 : ReachesPrefix X86Machine badOverlappingCopyBody s0 5 s2 [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s2 s3 () [(), (), ()] _ rfl hr3
  have hr1 : ReachesPrefix X86Machine badOverlappingCopyBody s0 6 s1 [(), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 5 s1 s2 () [(), (), (), ()] _ rfl hr2
  have hr0 : ReachesPrefix X86Machine badOverlappingCopyBody s0 7 s0 [(), (), (), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 6 s0 s1 () [(), (), (), (), ()] _ rfl hr1
  exact (hWF q hpre).1 hinit [(), (), (), (), (), ()] (.failed .ub) hr0

/-!
## 12. Signed vs Unsigned Width Casts (`movzx` 1B→8B, `movsx` 1B→8B, `truncate` 8B→1B) & Kernel Audit
-/

/-- `pub fn cast_u8_to_u64_zero_extend(x: u8) -> usize`:
    zero-extends a 1-byte `u8` in slot `⟨1⟩` to an 8-byte `usize` in return slot
    `⟨0⟩` via `X86Instr.movzx ⟨0⟩ 0 8 (.slotSlice ⟨1⟩ 0 1 true)`. -/
def castU8ToU64ZeroExtendBody : X86Body where
  adts := []
  argTys := [.u8]
  retTy := .usize
  slotCount := 2
  blocks := [
    { instrs := [
        .movzx ⟨0⟩ 0 8 (.slotSlice ⟨1⟩ 0 1 true)
      ]
      term := .ret }
  ]

theorem castU8ToU64ZeroExtendBody_verified (fnName : String) :
    X86Sem castU8ToU64ZeroExtendBody ≤
      EnsuresRetLibInv (defaultLibInv []) .usize
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := castU8ToU64ZeroExtendBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 2 (defaultLibInv [])
    { name := fnName, prog := castU8ToU64ZeroExtendBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ b0 _
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_cast_u8_to_u64_zero_extend_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := castU8ToU64ZeroExtendBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName castU8ToU64ZeroExtendBody]
    } :=
  verify_single_fn_wf_crate [] fnName castU8ToU64ZeroExtendBody
    (castU8ToU64ZeroExtendBody_verified fnName)

theorem castU8ToU64ZeroExtendBody_spec :
    X86Sem castU8ToU64ZeroExtendBody ≤
      X86Lang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret = (q.init.mem 1).bytes ++ replicateBytes 7 (some 0)) := by
  refine verifyByteX86Spec 2 castU8ToU64ZeroExtendBody
    (fun s₀ ret => ret = (s₀.mem 1).bytes ++ replicateBytes 7 (some 0)) ?_
  intro tySizes baseMem b0
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `pub fn cast_i8_to_i64_sign_extend(x: i8) -> isize`:
    sign-extends a 1-byte `i8` in slot `⟨1⟩` to an 8-byte `isize` in return slot
    `⟨0⟩` via `X86Instr.movsx ⟨0⟩ 0 8 (.slotSlice ⟨1⟩ 0 1 true)`. -/
def castI8ToI64SignExtendBody : X86Body where
  adts := []
  argTys := [.i8]
  retTy := .isize
  slotCount := 2
  blocks := [
    { instrs := [
        .movsx ⟨0⟩ 0 8 (.slotSlice ⟨1⟩ 0 1 true)
      ]
      term := .ret }
  ]

theorem castI8ToI64SignExtendBody_verified (fnName : String) :
    X86Sem castI8ToI64SignExtendBody ≤
      EnsuresRetLibInv (defaultLibInv []) .isize
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := castI8ToI64SignExtendBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 2 (defaultLibInv [])
    { name := fnName, prog := castI8ToI64SignExtendBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ b0 _
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_cast_i8_to_i64_sign_extend_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := castI8ToI64SignExtendBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName castI8ToI64SignExtendBody]
    } :=
  verify_single_fn_wf_crate [] fnName castI8ToI64SignExtendBody
    (castI8ToI64SignExtendBody_verified fnName)

/-- Full symbolic functional specification of `cast_i8_to_i64_sign_extend`:
    if the sign bit of `b0` is set (`128 ≤ b0.toNat`), the upper 7 bytes are
    filled with `0xFF` (`255`); otherwise they are filled with `0x00` (`0`). -/
theorem castI8ToI64SignExtendBody_spec :
    X86Sem castI8ToI64SignExtendBody ≤
      X86Lang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ∃ b0 : UInt8,
            (q.init.mem 1).bytes = [some b0] ∧
            ret = [some b0] ++ replicateBytes 7
              (some (match Nat.ble 128 b0.toNat with | true => 255 | false => 0))) := by
  refine verifyByteX86Spec 2 castI8ToI64SignExtendBody
    (fun s₀ ret =>
      ∃ b0 : UInt8,
        (s₀.mem 1).bytes = [some b0] ∧
        ret = [some b0] ++ replicateBytes 7
          (some (match Nat.ble 128 b0.toNat with | true => 255 | false => 0))) ?_
  intro tySizes baseMem b0
  exact ⟨rfl, rfl, rfl, b0, rfl, rfl⟩

/-- Concrete contrast between `movzx` (`0xFF` → `255`) and `movsx`
    (`0xFF` / `-1i8` → `0xFFFFFFFFFFFFFFFF` / `-1i64`), while both agree on
    non-negative `42` (`0x2A` → `42`). -/
theorem movsx_vs_movzx_neg1_and_pos42 :
    evalZeroExtend 8 [some 255] = some (encodeLeBytes 8 255) ∧
    evalSignExtend 8 [some 255] = some (encodeLeBytes 8 0xFFFFFFFFFFFFFFFF) ∧
    evalZeroExtend 8 [some 42] = some (encodeLeBytes 8 42) ∧
    evalSignExtend 8 [some 42] = some (encodeLeBytes 8 42) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `pub fn cast_u64_to_u8_truncate(x: usize) -> u8`:
    truncates an 8-byte `usize` in slot `⟨1⟩` to its low 1-byte `u8` in return
    slot `⟨0⟩` via `X86Instr.truncate ⟨0⟩ 0 1 (.slotSlice ⟨1⟩ 0 8 true)`. -/
def castU64ToU8TruncateBody : X86Body where
  adts := []
  argTys := [.usize]
  retTy := .u8
  slotCount := 2
  blocks := [
    { instrs := [
        .truncate ⟨0⟩ 0 1 (.slotSlice ⟨1⟩ 0 8 true)
      ]
      term := .ret }
  ]

theorem castU64ToU8TruncateBody_verified (fnName : String) :
    X86Sem castU64ToU8TruncateBody ≤
      EnsuresRetLibInv (defaultLibInv []) .u8
        (CapturedFn.effectivePre (defaultLibInv [])
          { name := fnName, prog := castU64ToU8TruncateBody, specs := [] }) := by
  refine verifyPubSafeRetByteLibInv 2 (defaultLibInv [])
    { name := fnName, prog := castU64ToU8TruncateBody, specs := [] } True rfl ?_
  intro tySizes baseMem _ _ b0 b1 b2 b3 b4 b5 b6 b7 _
  exact ⟨rfl, rfl, rfl, rfl, True.intro⟩

theorem prove_cast_u64_to_u8_truncate_crate (fnName : String) :
    CrateTheorem {
      adts := []
      libInv := defaultLibInv []
      functions := [{ name := fnName, prog := castU64ToU8TruncateBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName castU64ToU8TruncateBody]
    } :=
  verify_single_fn_wf_crate [] fnName castU64ToU8TruncateBody
    (castU64ToU8TruncateBody_verified fnName)

theorem castU64ToU8TruncateBody_spec :
    X86Sem castU64ToU8TruncateBody ≤
      X86Lang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret = takeBytes 1 (q.init.mem 1).bytes) := by
  refine verifyByteX86Spec 2 castU64ToU8TruncateBody
    (fun s₀ ret => ret = takeBytes 1 (s₀.mem 1).bytes) ?_
  intro tySizes baseMem b0 b1 b2 b3 b4 b5 b6 b7
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Negative canary: attempting `movsx` (`evalSignExtend`) on an uninitialized
    1-byte slot (`[none]`) fails with `.failed .ub`. -/
def badUninitSignExtendBody : X86Body where
  adts := [paddedAdtDecl]
  argTys := [.adt 1]
  retTy := .isize
  slotCount := 2
  blocks := [
    { instrs := [
        -- Byte 1 of `Padded` is uninitialized padding; sign-extending it to 8B
        -- must fail when that padding byte is `none`.
        .movsx ⟨0⟩ 0 8 (.slotSlice ⟨1⟩ 1 1 false)
      ]
      term := .ret }
  ]

theorem canary_movsx_uninit_rejected (fnName : String)
    (hSound : AssemblerCompiler.SoundOn badUninitSignExtendBody) :
    ¬ CrateTheorem {
      adts := [paddedAdtDecl]
      libInv := defaultLibInv [paddedAdtDecl]
      functions := [{ name := fnName, prog := badUninitSignExtendBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName badUninitSignExtendBody]
    } := by
  intro hCrate
  have hFnVer := hCrate.2.2.1.2 ⟨hSound, True.intro⟩
  have hWF := hFnVer.1.1
  let paddedBytes : ByteVec :=
    [some 7, none, none, none, some 1, some 0, some 0, some 0]
  let retBlk0 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := replicateBytes 8 none, ptr := none, written := false
  }
  let argBlk1 : AllocBlock := {
    perm := .readWrite, size := 8, bytes := paddedBytes, ptr := none, written := true
  }
  let mem0 : Nat → AllocBlock :=
    updateAlloc (updateAlloc (fun _ => unallocBlock) 0 retBlk0) 1 argBlk1
  let s0 : X86State := { mem := mem0, bb := 0, ip := 0 }
  have hpad_ty : hasTy [paddedAdtDecl] (fun _ => 0) paddedBytes (.adt 1) :=
    ⟨rfl,
     ⟨rfl, True.intro⟩,
     ⟨rfl, True.intro⟩,
     True.intro⟩
  have hinit : initX86State badUninitSignExtendBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨paddedBytes, rfl, hpad_ty⟩, True.intro⟩⟩
  have hmono : MonoAdmitted (fun _ => 0) badUninitSignExtendBody := by
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
        { name := fnName, prog := badUninitSignExtendBody } q :=
    ⟨hmono, True.intro, ⟨paddedBytes, rfl, hpad_ty⟩, True.intro⟩
  have hr0 : ReachesPrefix X86Machine badUninitSignExtendBody s0 1 s0 [] (.failed .ub) :=
    ReachesPrefix.failed 0 s0 .ub rfl
  exact (hWF q hpre).1 hinit [] (.failed .ub) hr0

