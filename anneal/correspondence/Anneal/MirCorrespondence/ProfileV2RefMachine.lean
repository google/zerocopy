-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Array.Basic
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.ValidityMemory
import Miri.Interpreter.MemoryErrors
import Miri.Interpreter.OperandMachine
import Miri.Interpreter.ForeignItems
import Trusted.MirAst
import Trusted.MirModel
import Trusted.Correspondence.Codec
import Trusted.Correspondence.State
import Trusted.Correspondence.Config

namespace Anneal.MirCorrespondence

open Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory

/-!
# Profile v2 `lean-miri` Reference Machine (`ProfileV2RefMachine`)

Zero-TCB Profile v2 reference machine $M_{\text{ref}}^{\text{v2}}$ built
directly over vendored `Miri.Interpreter.ExecutionMachine.step` reusing
`Trusted.Correspondence.{RefUser,RefState,RefOutcome}` with:

1. **Little-endian natural-alignment target (`refRuntimeLayoutV2`):** 64-bit
   little-endian `RuntimeTargetDataLayout` with natural integer alignments
   (`1, 2, 4, 8, 16`) matching Profile v2's captured target ABI.
2. **Full Profile v2 `LayoutData` (`refLayoutDataForTyV2`):** natural-aligned
   scalars, `bool`, `char`, `Ordering`, fieldless enums, overflow pairs, thin
   pointers/references (`8` bytes, align `8`), wide slice pointers/references
   (`16`-byte `(ptr, usize)` `ScalarPair`, align `8`), unsized slices, fixed
   arrays (`refIsSupportedDataTyV2`/`refIsSupportedLocalTyV2` admit fixed
   arrays for type admission and layout agreement, while
   `refValidityHooksV2.classify` and `refProjectFieldLayoutV2` reject `.array`
   outside the executed fragment),
   `RangeTo`/`RangeFrom<usize>`, and general Profile v2 tuples; expression
   and call lowerings (`toMiriOperandV2`, `toMiriProjElemV2`, `toMiriRvalueV2`,
   `toMiriTerminatorV2`, `refCoreCallOfDefId`) emit sentinel MIR constructs
   (`.Indirect`, `.PhantomDeref`, `.CopyForDeref`, `.CoroutineDrop`, `none`)
   that `lean-miri` rejects to `.blocked` on `.aggregateArray`/`.repeat_`,
   rodata constants, `constantIndex`, `unsize`, `intToLeBytes`, and `arrayEq`.
3. **`CallerMemory` & query-boundary adapter (`refInitCallerMemoryV2`,
   `refExtractCallerMemoryV2`, `initRefStateV2`, `refReadReturnValV2`):**
   rejects `AllocId` values `0` or `≥ 2^64` and partial/mismatched pointer
   provenance runs in live caller allocations, materializes live/dead caller
   allocations into `MemoryState` with exact bytes, `InitMask`,
   `ProvenanceMap`, `Mutability`, and natural `Align`, enables stack cleanup
   on root `Return` (`returnContinuation := .stop true`), and extracts
   post-state caller allocations (both whole 8-byte pointers and surviving
   `byteFragments`) without exposing callee stack allocations. Entry reference
   checks (`refRefsValidInMiriListV2`), exit caller confinement/validity
   (`refRefsStayInCallerMemV2`, `refRefsValidInMiriV2`), and pairwise
   mutable-borrow disjointness sit in this boundary adapter
   (`borrowTracker = none`).
4. **Real `ExecutionMachine.Config` (`refExecutionConfigV2`):** wires symbolic
   alignment (`PointerPlaceMachine.misalignmentWith` with
   `AlignmentCheck.Symbolic`), `deinitMovedPlace := true`, typed deref (with
   in-step eager `&T`/`&mut T` pointee validation inside operand hook
   `refDereferenceOpV2`) and field projections, `Rvalue.{Ref,RawPtr,Aggregate}`,
   `UnOp.PtrMetadata`, `BinOp.Offset`,
   `Cast.{IntToInt,PtrToPtr,PointerWithExposedProvenance}`, `ValidityVisitor`
   + `ValidityMemory.bind`, `Panic.assertPanic` (`refPanicLangItemV2`
   supporting `--panic abort` safe asserts and `--overflow-checks` optional
   overflow aborts with post-mutation `CallerMemory` extraction on `.abort`),
   and `ForeignItems.emulate` dispatch for `CoreCallOp` (`sliceLen`,
   `sliceGetUncheckedRangeTo`, `sliceGetUncheckedRangeFrom`,
   `usizeUncheckedSub`, `ptrAdd`; `.sysrootCall` lowers to `.blocked`).

Imports only `Init.*`, `Miri.*`, `Trusted.MirAst`, `Trusted.MirModel` (shared
pure value/outcome definitions in namespace `Trusted.MirSemantics`), and
`Trusted.Correspondence.{Codec,State,Config}` — never `Trusted.Correspondence`
root, `Trusted.Correspondence.Simulation`, or any operational
`Trusted.MirSemantics.*` module.
-/

/-- Local aliases for Miri state types (no new state wrappers). -/
abbrev RefMiriMem := MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit
abbrev RefMiriAlloc := Allocation Provenance Miri.TreeBorrows.BorrowTree
abbrev RefMiriState := Miri.Interpreter.MachineHooks.State Unit RefUser
abbrev RefMiriRes (α : Type) :=
  EStateM.Result Miri.Interpreter.StepError RefMiriState α
abbrev RefLocalState :=
  Miri.Interpreter.LocalState Provenance Miri.Interpreter.LocalLayout

/-! ## Section 1: Little-Endian Natural-Alignment Target and Layouts -/

/-- 64-bit little-endian `RuntimeTargetDataLayout` with natural integer
alignments (`1, 2, 4, 8, 16`) matching Profile v2's captured target. -/
noncomputable def refRuntimeLayoutV2 : RuntimeTargetDataLayout := {
  base := ⟨.little, .w64⟩
  i1Align := Align.ONE, i8Align := Align.ONE
  i16Align := ⟨1⟩, i32Align := ⟨2⟩, i64Align := ⟨3⟩, i128Align := ⟨4⟩
  f16Align := ⟨1⟩, f32Align := ⟨2⟩, f64Align := Align.EIGHT, f128Align := ⟨4⟩
  aggregateAlign := Align.ONE
  vectorAlign := Array.mk [(Size.ofBytes 8, Align.EIGHT), (Size.ofBytes 16, ⟨4⟩)]
  defaultAddressSpace := AddressSpace.ZERO
  defaultAddressSpacePointerSpec :=
    ⟨Size.ofBytes 8, Align.EIGHT, Size.ofBytes 8, false⟩
  addressSpaceInfo := Array.empty
  instructionAddressSpace := AddressSpace.ZERO
  cEnumMinSize := .I32
}

/-- Natural `Align` for an Anneal `IntWidth` (`1, 2, 4, 8, 16`). -/
noncomputable def refNaturalAlignForInt : IntWidth → Align
  | .i8 => ⟨0⟩ | .i16 => ⟨1⟩ | .i32 => ⟨2⟩
  | .i64 | .isize => ⟨3⟩ | .i128 => ⟨4⟩

/-- Baseline `LayoutData` with explicit alignment `al`. -/
noncomputable def refBaseLayoutDataV2 (repr : BackendRepr)
    (sz : Size) (al : Align) : Miri.ABI.LayoutData := {
  fields := .Primitive, variants := .Single 0, backendRepr := repr
  largestNiche := none, uninhabited := false
  align := AbiAlign.new al, size := sz, maxReprAlign := none
  unadjustedAbiAlign := al, reprC := false, randomizationSeed := 0
}

/-- Natural-aligned integer scalar `LayoutData` for `(w, signed)`. -/
noncomputable def refScalarLayoutDataV2 (w : IntWidth) (s : Bool) :
    Miri.ABI.LayoutData :=
  let sz := toMiriSize w
  refBaseLayoutDataV2
    (.Scalar (.Initialized (value := .Int (toMiriInteger w) s)
      (validRange := refFullWrappingRangeSize sz)))
    sz (refNaturalAlignForInt w)

/-- Natural-aligned `bool` `LayoutData` (`size = 1`, `align = 1`). -/
noncomputable def refBoolLayoutDataV2 : Miri.ABI.LayoutData :=
  refBaseLayoutDataV2
    (.Scalar (.Initialized (value := .Int .I8 false)
      (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩)))
    (Size.ofBytes 1) Align.ONE

/-- Natural-aligned `char` `LayoutData` (`size = 4`, `align = 4`). -/
noncomputable def refCharLayoutDataV2 : Miri.ABI.LayoutData :=
  refBaseLayoutDataV2
    (.Scalar (.Initialized (value := .Int .I32 false)
      (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 0x10ffff⟩)))
    (Size.ofBytes 4) ⟨2⟩

/-- 0-byte fieldless aggregate `LayoutData` for `()` and 1-variant ZST enums. -/
noncomputable def refUnitLayoutDataV2 : Miri.ABI.LayoutData := {
  refBaseLayoutDataV2 (.Memory (sized := true)) Size.ZERO Align.ONE with
  fields := .Arbitrary Array.empty Array.empty, variants := .Single 0
}

/-- Uninhabited 0-byte `LayoutData` for `!` (`MirTy.never`). -/
noncomputable def refNeverLayoutDataV2 : Miri.ABI.LayoutData := {
  refBaseLayoutDataV2 (.Memory (sized := true)) Size.ZERO Align.ONE with
  fields := .Arbitrary Array.empty Array.empty
  variants := .Empty, uninhabited := true
}

/-- Natural-aligned overflow pair `(T, bool)` `LayoutData`. -/
noncomputable def refOverflowPairLayoutDataV2 (w : IntWidth) (s : Bool) :
    Miri.ABI.LayoutData :=
  let sz := toMiriSize w
  { refBaseLayoutDataV2
      (.ScalarPair
        (a := .Initialized (value := .Int (toMiriInteger w) s)
          (validRange := refFullWrappingRangeSize sz))
        (b := .Initialized (value := .Int .I8 false)
          (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩))
        (bOffset := sz))
      (Size.ofBytes (2 * sz.bytes)) (refNaturalAlignForInt w) with
    fields := .Arbitrary (Array.mk [Size.ZERO, sz]) (Array.mk [0, 1]) }

/-- Natural-aligned fieldless-enum `LayoutData`. -/
noncomputable def refEnumLayoutDataV2 (ety : EnumTy) : Miri.ABI.LayoutData :=
  match ety.tagRepr with
  | .zeroSized => refUnitLayoutDataV2
  | .scalar tagW tagS =>
    let tag : Miri.ABI.Scalar := .Union (value := .Int (toMiriInteger tagW) tagS)
    let vs := Array.mk (ety.discriminants.map (fun _ => refInhabitedVariantLayout))
    { refBaseLayoutDataV2 (.Scalar tag) (toMiriSize tagW)
        (refNaturalAlignForInt tagW) with
      fields := .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0])
      variants := .Multiple tag .Direct 0 vs }

/-- 64-bit thin pointer/reference `LayoutData` (`size = 8`, `align = 8`). -/
noncomputable def refThinPtrLayoutDataV2 : Miri.ABI.LayoutData :=
  refBaseLayoutDataV2
    (.Scalar (.Initialized (value := .Pointer AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8))))
    (Size.ofBytes 8) Align.EIGHT

/-- 64-bit wide slice pointer/reference `LayoutData` (`size = 16`, `align = 8`,
`ScalarPair` of pointer and `usize` length at offset `8`). -/
noncomputable def refWideSlicePtrLayoutDataV2 : Miri.ABI.LayoutData :=
  let sz8 := Size.ofBytes 8
  refBaseLayoutDataV2
    (.ScalarPair
      (a := .Initialized (value := .Pointer AddressSpace.ZERO)
        (validRange := refFullWrappingRangeSize sz8))
      (b := .Initialized (value := .Int .I64 false)
        (validRange := refFullWrappingRangeSize sz8))
      (bOffset := sz8))
    (Size.ofBytes 16) Align.EIGHT

/-- 8-byte single-field struct `LayoutData` for `RangeTo`/`RangeFrom<usize>`. -/
noncomputable def refRangeUsizeLayoutDataV2 : Miri.ABI.LayoutData :=
  let sz8 := Size.ofBytes 8
  { refBaseLayoutDataV2
      (.Scalar (.Initialized (value := .Int .I64 false)
        (validRange := refFullWrappingRangeSize sz8)))
      sz8 Align.EIGHT with
    fields := .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) }

/-- Round `off` up to a multiple of `2^alignPow2`. -/
noncomputable def refAlignUpNat (off alignPow2 : Nat) : Nat :=
  let a := Nat.pow 2 alignPow2
  let rem := Nat.mod off a
  if Nat.beq rem 0 then off else off + (a - rem)

/-- Build `[start, ..., start + n - 1]` for tuple field memory order. -/
noncomputable def refRangeNats (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: refRangeNats (start + 1) n

mutual
  /-- Compute sequential natural-aligned field offsets, unpadded end offset,
  and maximum alignment exponent for a general Profile v2 tuple. -/
  noncomputable def refTupleFieldsLayoutV2 (curOff maxPow2 : Nat) :
      List MirTy → List Size × Nat × Nat
    | [] => ([], curOff, maxPow2)
    | ty :: rest =>
      let ld := refLayoutDataForTyV2 ty
      let fPow2 := ld.align.abi.pow2
      let aligned := refAlignUpNat curOff fPow2
      let (restOffs, endOff, finalMax) :=
        refTupleFieldsLayoutV2 (aligned + ld.size.bytes.toNat)
          (Nat.max maxPow2 fPow2) rest
      (Size.ofBytes (UInt64.ofNat aligned) :: restOffs, endOff, finalMax)

  /-- Whether any tuple field type has an uninhabited Profile v2 layout. -/
  noncomputable def refTyListUninhabitedV2 : List MirTy → Bool
    | [] => false
    | ty :: rest =>
      (refLayoutDataForTyV2 ty).uninhabited || refTyListUninhabitedV2 rest

  /-- Canonical natural-aligned `LayoutData` for any Profile v2 `MirTy`. -/
  noncomputable def refLayoutDataForTyV2 : MirTy → Miri.ABI.LayoutData
    | .int w s => refScalarLayoutDataV2 w s
    | .bool => refBoolLayoutDataV2
    | .char => refCharLayoutDataV2
    | .unit => refUnitLayoutDataV2
    | .never => refNeverLayoutDataV2
    | .ordering => refEnumLayoutDataV2 refOrderingEnumTy
    | .enum ety => refEnumLayoutDataV2 ety
    | .rawPtr _ (.slice _) | .ref _ (.slice _) => refWideSlicePtrLayoutDataV2
    | .rawPtr _ _ | .ref _ _ => refThinPtrLayoutDataV2
    | .slice elem =>
      let elemLd := refLayoutDataForTyV2 elem
      { refBaseLayoutDataV2 (.Memory (sized := false))
          Size.ZERO elemLd.align.abi with
        fields := .Array elemLd.size 0 }
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) =>
      refRangeUsizeLayoutDataV2
    | .array elem len =>
      let elemLd := refLayoutDataForTyV2 elem
      let uninhabited := elemLd.uninhabited && !Nat.beq len 0
      { refBaseLayoutDataV2 (.Memory (sized := true))
          (Size.ofBytes (UInt64.ofNat (len * elemLd.size.bytes.toNat)))
          elemLd.align.abi with
        fields := .Array elemLd.size (UInt64.ofNat len)
        variants := if uninhabited then .Empty else .Single 0
        uninhabited := uninhabited }
    | .tuple [.int w s, .bool] => refOverflowPairLayoutDataV2 w s
    | .tuple fs =>
      let (offs, endOff, maxPow2) := refTupleFieldsLayoutV2 0 0 fs
      let totalSize := refAlignUpNat endOff maxPow2
      let uninhabited := refTyListUninhabitedV2 fs
      { refBaseLayoutDataV2 (.Memory (sized := true))
          (Size.ofBytes (UInt64.ofNat totalSize)) ⟨maxPow2⟩ with
        fields := .Arbitrary (Array.mk offs) (Array.mk (refRangeNats 0 fs.length))
        variants := if uninhabited then .Empty else .Single 0
        uninhabited := uninhabited }
    | _ => refUnitLayoutDataV2
end

/-- Canonical `LocalLayout` for Profile v2 `ty`. -/
noncomputable def refLocalLayoutForTyV2 (types : List MirTy) (ty : MirTy) :
    Miri.Interpreter.LocalLayout :=
  ⟨tyIdFor types ty, refLayoutDataForTyV2 ty⟩

/-- Whether `n : Nat` round-trips losslessly through `UInt64` (`n < 2^64`). -/
noncomputable def refNatFitsU64V2 (n : Nat) : Bool :=
  Nat.beq (UInt64.ofNat n).toNat n

mutual
  /-- Whether every tuple field layout, aligned field offset, running end
  offset, and final aligned size fits losslessly in 64 bits (`< 2^64`). -/
  noncomputable def refTupleLayoutFitsU64V2 (curOff maxPow2 : Nat) :
      List MirTy → Bool
    | [] => refNatFitsU64V2 (refAlignUpNat curOff maxPow2)
    | ty :: rest =>
      refTyLayoutFitsU64V2 ty &&
        let ld := refLayoutDataForTyV2 ty
        let fPow2 := ld.align.abi.pow2
        let aligned := refAlignUpNat curOff fPow2
        let nextOff := aligned + ld.size.bytes.toNat
        refNatFitsU64V2 aligned && refNatFitsU64V2 nextOff &&
          refTupleLayoutFitsU64V2 nextOff (Nat.max maxPow2 fPow2) rest

  /-- Whether `ty` (recursing through pointees, slice elements, arrays, and
  tuples) has an exact 64-bit layout (`< 2^64`) without `UInt64.ofNat`
  wrap-around of array counts, array byte sizes, or tuple offsets. -/
  noncomputable def refTyLayoutFitsU64V2 : MirTy → Bool
    | .slice elem | .rawPtr _ elem | .ref _ elem =>
      refTyLayoutFitsU64V2 elem
    | .array elem len =>
      let elemLd := refLayoutDataForTyV2 elem
      refTyLayoutFitsU64V2 elem && refNatFitsU64V2 len &&
        refNatFitsU64V2 (len * elemLd.size.bytes.toNat)
    | .tuple [.int _ _, .bool] => true
    | .tuple fs => refTupleLayoutFitsU64V2 0 0 fs
    | _ => true
end

/-- Whether `ty`'s own ABI value layout fits losslessly in 64 bits
(thin/wide pointers and references always occupy `8` or `16` bytes regardless
of pointee size). -/
noncomputable def refOwnLayoutFitsU64V2 : MirTy → Bool
  | .slice elem => refTyLayoutFitsU64V2 elem
  | .array elem len =>
    let elemLd := refLayoutDataForTyV2 elem
    refTyLayoutFitsU64V2 elem && refNatFitsU64V2 len &&
      refNatFitsU64V2 (len * elemLd.size.bytes.toNat)
  | .tuple [.int _ _, .bool] => true
  | .tuple fs => refTupleLayoutFitsU64V2 0 0 fs
  | _ => true

/-- Checked Profile v2 `LayoutData` failing closed (`none`) before Miri layout
construction when `refTyLayoutFitsU64V2 ty = false`. -/
noncomputable def refCheckedLayoutDataForTyV2 (ty : MirTy) :
    Option Miri.ABI.LayoutData :=
  if refTyLayoutFitsU64V2 ty then some (refLayoutDataForTyV2 ty) else none

/-- Checked Profile v2 `LocalLayout` failing closed (`none`) before Miri
layout construction when `refTyLayoutFitsU64V2 ty = false`. -/
noncomputable def refCheckedLocalLayoutForTyV2 (types : List MirTy)
    (ty : MirTy) : Option Miri.Interpreter.LocalLayout :=
  match refCheckedLayoutDataForTyV2 ty with
  | some ld => some ⟨tyIdFor types ty, ld⟩
  | none => none

/-! ## Section 2: Independent Profile v2 Static Checks and Type Admission -/

/-- Whether `ty` is an unsized slice type in $M_{\text{ref}}^{\text{v2}}$. -/
noncomputable def refIsUnsizedTyV2 : MirTy → Bool
  | .slice _ => true
  | _ => false

/-- Supported fixed-size Profile v2 data type (`[T; N]` over scalars, units,
and admitted fieldless enums, excluding overflow pairs, pointers, and
references). -/
noncomputable def refIsSupportedDataTyV2 : MirTy → Bool
  | .array elem _ => refIsSupportedDataTyV2 elem
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum ety => refEnumAdmitted ety
  | _ => false

/-- Supported pointee type of a Profile v2 reference or raw pointer. -/
noncomputable def refIsSupportedPointeeTyV2 : MirTy → Bool
  | .slice (.int _ _) => true
  | pt => refIsSupportedDataTyV2 pt

mutual
  /-- Supported Profile v2 local type in $M_{\text{ref}}^{\text{v2}}$. -/
  noncomputable def refIsSupportedLocalTyV2 : MirTy → Bool
    | .bool | .int _ _ | .char | .ordering | .unit | .never => true
    | .enum ety => refEnumAdmitted ety
    | .array elem _ => refIsSupportedDataTyV2 elem
    | .rawPtr _ pt | .ref _ pt => refIsSupportedPointeeTyV2 pt
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => true
    | .tuple fs => refIsSupportedLocalTyListV2 fs
    | _ => false

  /-- Pointwise Profile v2 local-type support check. -/
  noncomputable def refIsSupportedLocalTyListV2 : List MirTy → Bool
    | [] => true
    | t :: ts => refIsSupportedLocalTyV2 t && refIsSupportedLocalTyListV2 ts
end

/-- Whether `aid : AllocId` is non-zero and fits in `UInt64` (exact
Nat-to-UInt64 round-trip). -/
noncomputable def refAllocIdFitsU64V2 (aid : Trusted.MirAst.AllocId) : Bool :=
  !Nat.beq aid 0 && Nat.beq (UInt64.ofNat aid).toNat aid

/-- Convert an `AllocId` into `Miri.Memory.AllocId`, failing closed (`none`)
on `0` or values greater than `UInt64.max`. -/
noncomputable def refExactAllocIdV2 (aid : Trusted.MirAst.AllocId) :
    Option Miri.Memory.AllocId :=
  if refAllocIdFitsU64V2 aid then
    Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat aid)
  else none

/-- Independent `CallerMemory` validity check: non-zero 64-bit
(`UInt64`-representable) pairwise-distinct `allocId`s, size `< 2^63`,
`alignLog2 ≤ 29`. -/
noncomputable def refAllocIdsValidV2 (seen : List Trusted.MirAst.AllocId) :
    List Trusted.MirSemantics.Allocation → Bool
  | [] => true
  | a :: rest =>
    refAllocIdFitsU64V2 a.allocId && refNatNotElem a.allocId seen &&
      Nat.blt a.bytes.length (Nat.pow 2 63) && Nat.ble a.alignLog2 29 &&
      refAllocIdsValidV2 (a.allocId :: seen) rest

/-- Independent caller-memory structural check. -/
noncomputable def refValidCallerMemoryV2 (cm : CallerMemory) : Bool :=
  refAllocIdsValidV2 [] cm.allocations

/-- Largest `allocId` appearing in `allocs` (or `0` when empty). -/
noncomputable def refMaxAllocIdV2 :
    List Trusted.MirSemantics.Allocation → Trusted.MirAst.AllocId
  | [] => 0
  | a :: rest => Nat.max a.allocId (refMaxAllocIdV2 rest)

/-- Whether `allocId` occurs in `allocs`. -/
noncomputable def refHasAllocIdV2 (id : Trusted.MirAst.AllocId) :
    List Trusted.MirSemantics.Allocation → Bool
  | [] => false
  | a :: rest => Nat.beq a.allocId id || refHasAllocIdV2 id rest

/-- Largest provenance `allocId` carried by initialized bytes in `bs`
(or `0` when no byte carries provenance). -/
noncomputable def refMaxByteProvAllocIdV2 :
    List Trusted.MirSemantics.AllocByte → Trusted.MirAst.AllocId
  | [] => 0
  | .uninit :: rest => refMaxByteProvAllocIdV2 rest
  | .init _ none :: rest => refMaxByteProvAllocIdV2 rest
  | .init _ (some aid) :: rest =>
    Nat.max aid (refMaxByteProvAllocIdV2 rest)

/-- Largest byte-provenance `allocId` across `allocs` (or `0` when none). -/
noncomputable def refMaxAllocBytesProvIdV2 :
    List Trusted.MirSemantics.Allocation → Trusted.MirAst.AllocId
  | [] => 0
  | a :: rest =>
    Nat.max (refMaxByteProvAllocIdV2 a.bytes)
      (refMaxAllocBytesProvIdV2 rest)

/-- Whether `id` appears as provenance on an initialized byte in `bs`. -/
noncomputable def refByteProvHasIdV2 (id : Trusted.MirAst.AllocId) :
    List Trusted.MirSemantics.AllocByte → Bool
  | [] => false
  | .uninit :: rest => refByteProvHasIdV2 id rest
  | .init _ none :: rest => refByteProvHasIdV2 id rest
  | .init _ (some aid) :: rest =>
    Nat.beq aid id || refByteProvHasIdV2 id rest

/-- Whether `id` appears as byte provenance in any allocation of `allocs`. -/
noncomputable def refAllocBytesHaveProvIdV2 (id : Trusted.MirAst.AllocId) :
    List Trusted.MirSemantics.Allocation → Bool
  | [] => false
  | a :: rest =>
    refByteProvHasIdV2 id a.bytes || refAllocBytesHaveProvIdV2 id rest

/-- Validate uniform element types across a list of values. -/
noncomputable def refCheckValUniformV2 (check : Val → Bool) :
    List Val → Bool
  | [] => true
  | v :: vs => check v && refCheckValUniformV2 check vs

mutual
  /-- Independent Profile v2 value-type well-formedness check; constructors
  outside the corresponded Profile v2 fragment fail closed to `false`. -/
  noncomputable def checkRefValV2 : Val → MirTy → Bool
    | .scalar sv, .int w s => checkRefVal (.scalar sv) (.int w s)
    | .bool b, .bool => checkRefVal (.bool b) .bool
    | .char c, .char => checkRefVal (.char c) .char
    | .ordering o, .ordering => checkRefVal (.ordering o) .ordering
    | .unit, .unit => checkRefVal .unit .unit
    | .enumVal ety v, .enum ety' => checkRefVal (.enumVal ety v) (.enum ety')
    | .ptr pv, .rawPtr _ pt | .ptr pv, .ref _ pt =>
      !refIsUnsizedTyV2 pt && IntWidth.beq pv.width .isize
    | .slicePtr pv _, .rawPtr _ (.slice _)
    | .slicePtr pv _, .ref _ (.slice _) =>
      IntWidth.beq pv.width .isize
    | .rangeTo _, .rangeTo (.int .isize false) => true
    | .rangeFrom _, .rangeFrom (.int .isize false) => true
    | .array vs, .array elem len =>
      Nat.beq vs.length len &&
        refCheckValUniformV2 (fun v => checkRefValV2 v elem) vs
    | .tuple vs, .tuple ts => checkRefValListV2 vs ts
    | _, _ => false

  /-- Pointwise Profile v2 value-type check. -/
  noncomputable def checkRefValListV2 : List Val → List MirTy → Bool
    | [], [] => true
    | v :: vs, t :: ts => checkRefValV2 v t && checkRefValListV2 vs ts
    | _, _ => false
end

/-- Independent Profile v2 argument-list type check. -/
noncomputable def checkRefArgsMatchV2 : List Val → List MirTy → Bool :=
  checkRefValListV2

mutual
  /-- Whether every `allocId` carried inside argument value `v` is valid and
  fits in `UInt64` (so `ptrValToMiriV2` never truncates or drops provenance).
  Values outside the corresponded fragment fail closed to `false`. -/
  noncomputable def refValAllocIdsFitU64V2 : Val → Bool
    | .scalar _ | .bool _ | .char _ | .ordering _ | .unit
    | .enumVal _ _ | .rangeTo _ | .rangeFrom _ => true
    | .ptr pv | .slicePtr pv _ =>
      match pv.allocId with
      | none => true
      | some aid => refAllocIdFitsU64V2 aid
    | .tuple vs | .array vs => refValListAllocIdsFitU64V2 vs
    | _ => false

  /-- Pointwise `refValAllocIdsFitU64V2` check across a value list. -/
  noncomputable def refValListAllocIdsFitU64V2 : List Val → Bool
    | [] => true
    | v :: vs => refValAllocIdsFitU64V2 v && refValListAllocIdsFitU64V2 vs
end

mutual
  /-- Largest provenance `allocId` occurring inside argument value `v` (or `0`
  when `v` carries no provenance). Exhaustive over `Val` so adding new value
  constructors forces updating provenance-freshness tracking. -/
  noncomputable def refMaxValAllocIdV2 : Val → Trusted.MirAst.AllocId
    | .ptr p => p.allocId.getD 0
    | .slicePtr p _ => p.allocId.getD 0
    | .vec p _ _ => p.allocId.getD 0
    | .boxPtr p _ => p.allocId.getD 0
    | .tuple vs => refMaxValListAllocIdV2 vs
    | .array vs => refMaxValListAllocIdV2 vs
    | .bytes bs => refMaxByteProvAllocIdV2 bs
    | .optionVal none => 0
    | .optionVal (some v') => refMaxValAllocIdV2 v'
    | .scalar _ | .range _ _ | .rangeTo _ | .rangeFrom _ | .bool _ | .char _
    | .ordering _ | .unit | .enumVal _ _ => 0

  /-- Largest provenance `allocId` across a list of argument values. -/
  noncomputable def refMaxValListAllocIdV2 :
      List Val → Trusted.MirAst.AllocId
    | [] => 0
    | v :: vs => Nat.max (refMaxValAllocIdV2 v) (refMaxValListAllocIdV2 vs)
end

mutual
  /-- Whether `id` occurs as provenance anywhere inside argument value `v`.
  Exhaustive over `Val`. -/
  noncomputable def refValHasAllocIdV2 (id : Trusted.MirAst.AllocId) :
      Val → Bool
    | .ptr p =>
      match p.allocId with
      | none => false
      | some aid => Nat.beq aid id
    | .slicePtr p _ =>
      match p.allocId with
      | none => false
      | some aid => Nat.beq aid id
    | .vec p _ _ =>
      match p.allocId with
      | none => false
      | some aid => Nat.beq aid id
    | .boxPtr p _ =>
      match p.allocId with
      | none => false
      | some aid => Nat.beq aid id
    | .tuple vs => refValListHasAllocIdV2 id vs
    | .array vs => refValListHasAllocIdV2 id vs
    | .bytes bs => refByteProvHasIdV2 id bs
    | .optionVal none => false
    | .optionVal (some v') => refValHasAllocIdV2 id v'
    | .scalar _ | .range _ _ | .rangeTo _ | .rangeFrom _ | .bool _ | .char _
    | .ordering _ | .unit | .enumVal _ _ => false

  /-- Whether `id` occurs as provenance anywhere inside `vs`. -/
  noncomputable def refValListHasAllocIdV2 (id : Trusted.MirAst.AllocId) :
      List Val → Bool
    | [] => false
    | v :: vs => refValHasAllocIdV2 id v || refValListHasAllocIdV2 id vs
end

/-! ## Section 3: `CallerMemory` Materialization, Extraction, and Codecs -/

/-- Convert Anneal `Mutability` to `Miri.Memory.Mutability`. -/
noncomputable def toMiriMutV2 : Trusted.MirAst.Mutability → Miri.Memory.Mutability
  | .shared => .Not | .mut => .Mut

/-- Convert `Miri.Memory.Mutability` back to Anneal `Mutability`. -/
noncomputable def ofMiriMutV2 : Miri.Memory.Mutability → Trusted.MirAst.Mutability
  | .Not => .shared | .Mut => .mut

/-- Convert Anneal `PtrVal` to a Miri `Pointer (Option Provenance)` using root
tag `BorTag.one` (requiring an exact 64-bit `AllocId`). -/
noncomputable def ptrValToMiriV2 (pv : PtrVal) : Pointer (Option Provenance) :=
  let prov : Option Provenance :=
    match pv.allocId with
    | none => none
    | some aid =>
      match refExactAllocIdV2 aid with
      | some id => some (.concrete id BorTag.one)
      | none => none
  ⟨Size.ofBytes pv.offsetBytes, prov⟩

/-- Convert a Miri `Pointer (Option Provenance)` back to an Anneal `PtrVal`. -/
noncomputable def miriPtrToPtrValV2 (ptr : Pointer (Option Provenance)) :
    PtrVal :=
  let aid : Option Trusted.MirAst.AllocId :=
    match ptr.provenance with
    | some (.concrete id _) => some id.value.toNat
    | _ => none
  ⟨aid, ptr.offset.bytes, .isize⟩

/-- Convert a Miri `Scalar Provenance` to a `PtrVal` via `Scalar.toPointer`. -/
noncomputable def miriScalarToPtrValV2 (sc : Miri.Memory.Scalar Provenance) :
    Except FaultKind PtrVal :=
  match sc.toPointer refRuntimeLayoutV2.base with
  | .ok ptr => .ok (miriPtrToPtrValV2 ptr)
  | .error _ => .error .unsupported

/-- Extract plain non-provenance initialized bytes when every byte is
`.init b none` (fast path for `Allocation.fromBytes`). -/
noncomputable def refPlainInitBytesV2? : List AllocByte → Option (List UInt8)
  | [] => some []
  | .init b none :: rest =>
    match refPlainInitBytesV2? rest with
    | some bs => some (b :: bs)
    | none => none
  | _ => none

/-- Little-endian unsigned integer decoded from raw bytes. -/
noncomputable def refNatOfLeBytesV2 : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * refNatOfLeBytesV2 rest

/-- Populate a mutable Miri `Allocation` from remaining `AllocByte`s
(supporting `.uninit`, `.init b none`, and contiguous 8-byte uniform-provenance
pointer runs whose `AllocId` fits in `UInt64`; partial, mismatched, or
out-of-range `.init b (some _)` runs fail closed to `.error .unsupported`).
Structurally recursive on the byte list. -/
noncomputable def refPopulateAllocBytesV2
    (alloc : Miri.Memory.Allocation Provenance Unit) (idx : Nat) :
    List AllocByte → Except FaultKind (Miri.Memory.Allocation Provenance Unit)
  | [] => .ok alloc
  | .init b0 (some a0) :: .init b1 (some a1) :: .init b2 (some a2) ::
    .init b3 (some a3) :: .init b4 (some a4) :: .init b5 (some a5) ::
    .init b6 (some a6) :: .init b7 (some a7) :: rest =>
    if Nat.beq a0 a1 && Nat.beq a0 a2 && Nat.beq a0 a3 && Nat.beq a0 a4 &&
        Nat.beq a0 a5 && Nat.beq a0 a6 && Nat.beq a0 a7 then
      match refExactAllocIdV2 a0 with
      | none => .error .unsupported
      | some mid =>
        let raw8 := [b0, b1, b2, b3, b4, b5, b6, b7]
        let ptr : Pointer Provenance :=
          ⟨Size.ofBytes (UInt64.ofNat (refNatOfLeBytesV2 raw8)),
           .concrete mid BorTag.one⟩
        let range := allocRange (Size.ofBytes (UInt64.ofNat idx)) (Size.ofBytes 8)
        match alloc.writePointer refRuntimeLayoutV2.base range ptr with
        | .ok () alloc1 => refPopulateAllocBytesV2 alloc1 (idx + 8) rest
        | .error _ _ => .error .unsupported
    else
      .error .unsupported
  | .init _ (some _) :: _ => .error .unsupported
  | .init b none :: rest =>
    match alloc.writeBytes (Size.ofBytes (UInt64.ofNat idx))
        (Array.mk [b]) (Size.ofBytes 8) with
    | .ok () alloc1 => refPopulateAllocBytesV2 alloc1 (idx + 1) rest
    | .error _ _ => .error .unsupported
  | .uninit :: rest => refPopulateAllocBytesV2 alloc (idx + 1) rest

/-- Materialize one Anneal `Allocation` into a real `RefMiriAlloc`. -/
noncomputable def refAllocToMiriV2 (a : Trusted.MirSemantics.Allocation) :
    Except FaultKind RefMiriAlloc :=
  let sz := Size.ofBytes (UInt64.ofNat a.bytes.length)
  let al : Align := ⟨a.alignLog2⟩
  let miriMut := toMiriMutV2 a.mutability
  let tree := Miri.TreeBorrows.BorrowTree.new BorTag.one sz
  match refPlainInitBytesV2? a.bytes with
  | some raw =>
    match Miri.Memory.Allocation.fromBytes (Prov := Provenance)
        (Array.mk raw) al miriMut with
    | .ok rawAlloc => .ok (rawAlloc.withExtra tree)
    | .error _ => .error .unsupported
  | none =>
    match Miri.Memory.Allocation.tryNew (Prov := Provenance) sz al .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
    | .error _ => .error .unsupported
    | .ok blank =>
      match refPopulateAllocBytesV2 blank 0 a.bytes with
      | .error k => .error k
      | .ok filled => .ok ((filled.withMutability miriMut).withExtra tree)

/-- Materialize all `cm.allocations` into `mem` (live vs dead + `issuedIds`). -/
noncomputable def refInsertCallerAllocsV2 (mem : RefMiriMem)
    (issued : Array Miri.Memory.AllocId) :
    List Trusted.MirSemantics.Allocation →
      Except FaultKind (RefMiriMem × Array Miri.Memory.AllocId)
  | [] => .ok (mem, issued)
  | a :: rest =>
    match refExactAllocIdV2 a.allocId with
    | none => .error .unsupported
    | some mid =>
      if a.live then
        match refAllocToMiriV2 a with
        | .error k => .error k
        | .ok miriAlloc =>
          let mem1 := { mem with
            live := mem.live.push (mid, ⟨.machine (), miriAlloc⟩) }
          refInsertCallerAllocsV2 mem1 (issued.push mid) rest
      else
        let deadEntry : DeadAllocation :=
          ⟨mid, Size.ofBytes (UInt64.ofNat a.bytes.length), ⟨a.alignLog2⟩⟩
        refInsertCallerAllocsV2
          { mem with dead := mem.dead.push deadEntry } (issued.push mid) rest

/-- Initialize Profile v2 `RefMiriMem` with all caller allocations plus a fresh
non-aliasing return buffer `retPlace`, optionally validating caller-only
memory via `validateCallerMem` before `retPlace` is inserted and reserving fresh
ids strictly past caller allocations, caller byte provenances, and optional
`extraMax`/`extraHasOne` argument provenances. -/
noncomputable def refInitCallerMemoryV2 (types : List MirTy)
    (cm : CallerMemory) (retTy : MirTy)
    (validateCallerMem : RefMiriMem → Bool := fun _ => true)
    (extraMax : Trusted.MirAst.AllocId := 0)
    (extraHasOne : Bool := false) :
    Except FaultKind (RefMiriMem × Miri.Interpreter.MPlaceTy Provenance) :=
  if !refOwnLayoutFitsU64V2 retTy then .error .unsupported
  else
    let retLayout := refLocalLayoutForTyV2 types retTy
    let sz := retLayout.layout.size
    let al := retLayout.layout.align.abi
    match Miri.Memory.Allocation.tryNew (Prov := Provenance) sz al .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
    | .error _ => .error .unsupported
    | .ok rawRet =>
      match refInsertCallerAllocsV2 Miri.Memory.MemoryState.empty Array.empty
          cm.allocations with
      | .error k => .error k
      | .ok (mem1, issued1) =>
        if !validateCallerMem mem1 then .error .undefined
        else
          let callerMax := Nat.max
            (Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations))
            extraMax
          let hasOne := refHasAllocIdV2 1 cm.allocations ||
            refAllocBytesHaveProvIdV2 1 cm.allocations || extraHasOne
          let retIdNat := if hasOne then callerMax + 1 else 1
          let nextIdNat :=
            if hasOne then callerMax + 2 else Nat.max 2 (callerMax + 1)
          match refExactAllocIdV2 retIdNat with
          | none => .error .unsupported
          | some retId =>
            if !Nat.beq (UInt64.ofNat nextIdNat).toNat nextIdNat then
              .error .unsupported
            else
              let tree := Miri.TreeBorrows.BorrowTree.new BorTag.one sz
              let mem2 := ({ mem1 with
                nextAllocId := UInt64.ofNat nextIdNat
                live := mem1.live.push (retId, ⟨.stack, rawRet.withExtra tree⟩)
              }).setIssuedIds (issued1.push retId)
              let ptr : Pointer (Option Provenance) :=
                ⟨Size.ZERO, some (.concrete retId BorTag.one)⟩
              .ok (mem2, ⟨⟨ptr, .none, none⟩, retLayout⟩)

/-- Find the pointer provenance (whole 8-byte pointer in `pmap.ptrs` or
surviving per-byte fragment in `pmap.byteFragments`) covering byte offset `idx`
in `pmap`. -/
noncomputable def refByteProvAtV2 (pmap : ProvenanceMap Provenance)
    (idx : Nat) : Option Trusted.MirAst.AllocId :=
  match pmap.ptrs.find? (fun entry =>
      Nat.ble entry.1.bytes.toNat idx &&
        Nat.blt idx (entry.1.bytes.toNat + 8)) with
  | some (_, .concrete id _) => some id.value.toNat
  | some _ => none
  | none =>
    match pmap.byteFragments with
    | none => none
    | some frags =>
      match frags.find? (fun entry => Nat.beq entry.1.bytes.toNat idx) with
      | some (_, frag) =>
        match frag.prov with
        | .concrete id _ => some id.value.toNat
        | .wildcard => none
      | none => none

/-- Reconstruct `List AllocByte` for `[idx .. idx + rem)` from `alloc`. -/
noncomputable def refReadAllocBytesLoopV2 (alloc : RefMiriAlloc)
    (raw : Array UInt8) (idx : Nat) : Nat → List AllocByte
  | 0 => []
  | rem + 1 =>
    let isInit : Bool :=
      match alloc.initializationMask.get (Size.ofBytes (UInt64.ofNat idx)) with
      | .ok b => b | .error _ => false
    let ab : AllocByte :=
      if isInit then
        AllocByte.init ((raw[idx]?).getD 0) (refByteProvAtV2 alloc.provenanceMap idx)
      else AllocByte.uninit
    ab :: refReadAllocBytesLoopV2 alloc raw (idx + 1) rem

/-- Reconstruct one caller `Allocation` from `memory` on return (the `orig`
fallback on `getBytesUnchecked` is unreachable on valid Miri allocations). -/
noncomputable def refExtractOneCallerAllocV2 (memory : RefMiriMem)
    (orig : Trusted.MirSemantics.Allocation) : Trusted.MirSemantics.Allocation :=
  match refExactAllocIdV2 orig.allocId with
  | none => orig
  | some mid =>
    match memory.live.find? (fun entry => entry.1 == mid) with
    | none => { orig with live := false }
    | some (_, localAlloc) =>
      let alloc := localAlloc.allocation
      let len := alloc.byteSize.bytes.toNat
      match alloc.getBytesUnchecked (allocRange Size.ZERO alloc.byteSize) with
      | .error _ => orig
      | .ok raw => {
          allocId := orig.allocId, alignLog2 := alloc.align.pow2
          mutability := ofMiriMutV2 alloc.mutability
          bytes := refReadAllocBytesLoopV2 alloc raw 0 len, live := true }

/-- Extract post-state caller allocations in `orig.allocations` order. -/
noncomputable def refExtractCallerMemoryV2 (orig : CallerMemory)
    (memory : RefMiriMem) : CallerMemory :=
  ⟨orig.allocations.map (refExtractOneCallerAllocV2 memory)⟩

/-! ## Section 4: Value Encoding, Return Decoding, and Miri Reference Checks -/

/-- Encode a Profile v2 `Val` at type `ty` into a Miri `Immediate`; pairs
outside the corresponded fragment fail closed to `.uninit`. -/
noncomputable def valToMiriImmediateV2 :
    MirTy → Val → Miri.Interpreter.Immediate Provenance
  | .int w s, .scalar sv => valToMiriImmediate (.int w s) (.scalar sv)
  | .bool, .bool b => valToMiriImmediate .bool (.bool b)
  | .char, .char c => valToMiriImmediate .char (.char c)
  | .ordering, .ordering o => valToMiriImmediate .ordering (.ordering o)
  | .unit, .unit => valToMiriImmediate .unit .unit
  | .enum ety, .enumVal ety' v =>
    valToMiriImmediate (.enum ety) (.enumVal ety' v)
  | .tuple [.int w s, .bool], .tuple [.scalar sv, .bool b] =>
    valToMiriImmediate (.tuple [.int w s, .bool]) (.tuple [.scalar sv, .bool b])
  | .rawPtr _ pt, .ptr pv | .ref _ pt, .ptr pv =>
    if refIsUnsizedTyV2 pt then .uninit
    else
      match Miri.Memory.Scalar.fromMaybePointer refRuntimeLayoutV2.base
          (ptrValToMiriV2 pv) with
      | .ok sc => .scalar sc | .error _ => .uninit
  | .rawPtr _ (.slice _), .slicePtr pv len
  | .ref _ (.slice _), .slicePtr pv len =>
    match Miri.Memory.Scalar.fromMaybePointer refRuntimeLayoutV2.base
        (ptrValToMiriV2 pv) with
    | .ok ptrSc =>
      .scalarPair ptrSc
        (.fromScalarInt (miriScalar .isize (BitVec.ofNat 128 len.toNat)))
    | .error _ => .uninit
  | .rangeTo (.int .isize false), .rangeTo e =>
    .scalar (.fromScalarInt (miriScalar .isize (BitVec.ofNat 128 e.toNat)))
  | .rangeFrom (.int .isize false), .rangeFrom s =>
    .scalar (.fromScalarInt (miriScalar .isize (BitVec.ofNat 128 s.toNat)))
  | _, _ => .uninit

/-- Whether `ty` is represented directly as a Miri `Immediate`; types outside
the corresponded fragment fail closed to `false`. -/
noncomputable def refTyIsImmediateV2 : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never | .enum _
  | .rawPtr _ _ | .ref _ _ | .rangeTo (.int .isize false)
  | .rangeFrom (.int .isize false) | .tuple [.int _ _, .bool]
  | .tuple [] => true
  | _ => false

/-- Decode `rem` consecutive array elements using `f` at stride `stride`. -/
noncomputable def refReadArrayWithV2 (f : Nat → Except FaultKind Val)
    (curOff stride : Nat) : Nat → Except FaultKind (List Val)
  | 0 => .ok []
  | rem + 1 =>
    match f curOff with
    | .error k => .error k
    | .ok v =>
      match refReadArrayWithV2 f (curOff + stride) stride rem with
      | .error k => .error k
      | .ok vs => .ok (v :: vs)

/-- Write array element values sequentially into `alloc` using `f`. -/
noncomputable def refWriteArrayWithV2
    (f : Miri.Memory.Allocation Provenance Unit → Nat → Val →
      Except FaultKind (Miri.Memory.Allocation Provenance Unit))
    (alloc : Miri.Memory.Allocation Provenance Unit)
    (curOff stride : Nat) :
    List Val → Except FaultKind (Miri.Memory.Allocation Provenance Unit)
  | [] => .ok alloc
  | v :: vs =>
    match f alloc curOff v with
    | .error k => .error k
    | .ok alloc1 => refWriteArrayWithV2 f alloc1 (curOff + stride) stride vs

/-- Read a plain (non-provenance) `ScalarInt` of byte size `sz` at `off`. -/
noncomputable def refReadScalarIntFromAllocV2 (alloc : RefMiriAlloc)
    (off : Nat) (sz : Size) : Except FaultKind ScalarInt :=
  let range := allocRange (Size.ofBytes (UInt64.ofNat off)) sz
  match alloc.readScalar refRuntimeLayoutV2.base range false with
  | .ok sc =>
    match sc.tryToScalarInt with
    | .ok (.integer sci) => .ok sci
    | _ => .error .unsupported
  | .error (.invalidUninitBytes _) => .error .undefined
  | .error _ => .error .unsupported

/-- Decode a non-tuple, non-array Profile v2 leaf `Val` from `alloc` at
`baseOff`. -/
noncomputable def refReadLeafValFromAllocV2 (alloc : RefMiriAlloc)
    (baseOff : Nat) (ty : MirTy) : Except FaultKind Val :=
  let offSz := Size.ofBytes (UInt64.ofNat baseOff)
  match ty with
  | .unit => .ok .unit
  | .never => .error .undefined
  | .int w s =>
    match refReadScalarIntFromAllocV2 alloc baseOff (toMiriSize w) with
    | .ok sci => .ok (.scalar ⟨w, s, sci.data⟩)
    | .error k => .error k
  | .bool =>
    match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 1) with
    | .error k => .error k
    | .ok sci =>
      match sci.tryToBool with
      | .ok b => .ok (.bool b)
      | .error (.invalidBool _) => .error .undefined
      | .error _ => .error .unsupported
  | .char =>
    match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 4) with
    | .error k => .error k
    | .ok sci =>
      match sci.toChar with
      | .ok c => .ok (.char c)
      | .error (.invalidChar _) => .error .undefined
      | .error _ => .error .unsupported
  | .rawPtr _ (.slice _) | .ref _ (.slice _) =>
    let pRange := allocRange offSz (Size.ofBytes 8)
    match alloc.readScalar refRuntimeLayoutV2.base pRange true with
    | .error (.invalidUninitBytes _) => .error .undefined
    | .error _ => .error .unsupported
    | .ok pSc =>
      match miriScalarToPtrValV2 pSc,
          refReadScalarIntFromAllocV2 alloc (baseOff + 8) (Size.ofBytes 8) with
      | .ok pv, .ok lSci => .ok (.slicePtr pv (UInt64.ofNat lSci.data.toNat))
      | .error k, _ => .error k
      | _, .error k => .error k
  | .rawPtr _ pt | .ref _ pt =>
    if refIsUnsizedTyV2 pt then .error .unsupported
    else
      let range := allocRange offSz (Size.ofBytes 8)
      match alloc.readScalar refRuntimeLayoutV2.base range true with
      | .ok sc =>
        match miriScalarToPtrValV2 sc with
        | .ok pv => .ok (.ptr pv)
        | .error k => .error k
      | .error (.invalidUninitBytes _) => .error .undefined
      | .error _ => .error .unsupported
  | .rangeTo (.int .isize false) =>
    match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 8) with
    | .ok sci => .ok (.rangeTo (UInt64.ofNat sci.data.toNat))
    | .error k => .error k
  | .rangeFrom (.int .isize false) =>
    match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 8) with
    | .ok sci => .ok (.rangeFrom (UInt64.ofNat sci.data.toNat))
    | .error k => .error k
  | other =>
    match refAsEnumTy? other with
    | none => .error .unsupported
    | some ety =>
      match ety.tagRepr with
      | .zeroSized =>
        if refIsZstEnumTy ety then
          match refValOfEnumVariant? other 0 with
          | some val => .ok val | none => .error .unsupported
        else .error .unsupported
      | .scalar tagW tagS =>
        if !refEnumAdmitted ety then .error .unsupported
        else
          match refReadScalarIntFromAllocV2 alloc baseOff (toMiriSize tagW) with
          | .error k => .error k
          | .ok sci =>
            match refMiriTagToDiscrBits tagW tagS ety.discrWidth sci.data with
            | none => .error .unsupported
            | some discrBits =>
              match refFindDiscrVariant? discrBits ety.discriminants with
              | none => .error .undefined
              | some v =>
                match refValOfEnumVariant? other v with
                | some val => .ok val | none => .error .unsupported

/-- Decode a fixed-size data or array value out of `alloc` at `baseOff`
(standalone recursion on `MirTy` so `refReadValFromAllocV2` stays structurally
recursive). -/
noncomputable def refReadDataValFromAllocV2 (alloc : RefMiriAlloc) :
    MirTy → Nat → Except FaultKind Val
  | .array elem len, baseOff =>
    if !refTyLayoutFitsU64V2 (.array elem len) then .error .unsupported
    else
      let elemLd := refLayoutDataForTyV2 elem
      match refReadArrayWithV2 (refReadDataValFromAllocV2 alloc elem)
          baseOff elemLd.size.bytes.toNat len with
      | .ok vs => .ok (.array vs)
      | .error k => .error k
  | ty, baseOff => refReadLeafValFromAllocV2 alloc baseOff ty

mutual
  /-- Decode tuple fields sequentially out of `alloc` at `baseOff`. -/
  noncomputable def refReadTupleFieldsFromAllocV2 (alloc : RefMiriAlloc)
      (baseOff : Nat) : List MirTy → List Size → Except FaultKind (List Val)
    | [], [] => .ok []
    | ty :: tys, off :: offs =>
      match refReadValFromAllocV2 alloc (baseOff + off.bytes.toNat) ty with
      | .error k => .error k
      | .ok v =>
        match refReadTupleFieldsFromAllocV2 alloc baseOff tys offs with
        | .error k => .error k
        | .ok vs => .ok (v :: vs)
    | _, _ => .error .unsupported

  /-- Decode one Profile v2 `Val` of type `ty` from `alloc` at `baseOff`. -/
  noncomputable def refReadValFromAllocV2 (alloc : RefMiriAlloc)
      (baseOff : Nat) (ty : MirTy) : Except FaultKind Val :=
    let offSz := Size.ofBytes (UInt64.ofNat baseOff)
    match ty with
    | .unit => .ok .unit
    | .never => .error .undefined
    | .int w s =>
      match refReadScalarIntFromAllocV2 alloc baseOff (toMiriSize w) with
      | .ok sci => .ok (.scalar ⟨w, s, sci.data⟩)
      | .error k => .error k
    | .bool =>
      match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 1) with
      | .error k => .error k
      | .ok sci =>
        match sci.tryToBool with
        | .ok b => .ok (.bool b)
        | .error (.invalidBool _) => .error .undefined
        | .error _ => .error .unsupported
    | .char =>
      match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 4) with
      | .error k => .error k
      | .ok sci =>
        match sci.toChar with
        | .ok c => .ok (.char c)
        | .error (.invalidChar _) => .error .undefined
        | .error _ => .error .unsupported
    | .rawPtr _ (.slice _) | .ref _ (.slice _) =>
      let pRange := allocRange offSz (Size.ofBytes 8)
      match alloc.readScalar refRuntimeLayoutV2.base pRange true with
      | .error (.invalidUninitBytes _) => .error .undefined
      | .error _ => .error .unsupported
      | .ok pSc =>
        match miriScalarToPtrValV2 pSc,
            refReadScalarIntFromAllocV2 alloc (baseOff + 8) (Size.ofBytes 8) with
        | .ok pv, .ok lSci => .ok (.slicePtr pv (UInt64.ofNat lSci.data.toNat))
        | .error k, _ => .error k
        | _, .error k => .error k
    | .rawPtr _ pt | .ref _ pt =>
      if refIsUnsizedTyV2 pt then .error .unsupported
      else
        let range := allocRange offSz (Size.ofBytes 8)
        match alloc.readScalar refRuntimeLayoutV2.base range true with
        | .ok sc =>
          match miriScalarToPtrValV2 sc with
          | .ok pv => .ok (.ptr pv)
          | .error k => .error k
        | .error (.invalidUninitBytes _) => .error .undefined
        | .error _ => .error .unsupported
    | .rangeTo (.int .isize false) =>
      match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 8) with
      | .ok sci => .ok (.rangeTo (UInt64.ofNat sci.data.toNat))
      | .error k => .error k
    | .rangeFrom (.int .isize false) =>
      match refReadScalarIntFromAllocV2 alloc baseOff (Size.ofBytes 8) with
      | .ok sci => .ok (.rangeFrom (UInt64.ofNat sci.data.toNat))
      | .error k => .error k
    | .tuple [.int w s, .bool] =>
      match refReadScalarIntFromAllocV2 alloc baseOff (toMiriSize w),
          refReadScalarIntFromAllocV2 alloc (baseOff + w.byteSize)
            (Size.ofBytes 1) with
      | .ok intSci, .ok boolSci =>
        match boolSci.tryToBool with
        | .ok b => .ok (.tuple [.scalar ⟨w, s, intSci.data⟩, .bool b])
        | .error (.invalidBool _) => .error .undefined
        | .error _ => .error .unsupported
      | .error k, _ => .error k
      | _, .error k => .error k
    | .tuple fs =>
      if !refTupleLayoutFitsU64V2 0 0 fs then .error .unsupported
      else
        let (offs, _, _) := refTupleFieldsLayoutV2 0 0 fs
        match refReadTupleFieldsFromAllocV2 alloc baseOff fs offs with
        | .ok vs => .ok (.tuple vs)
        | .error k => .error k
    | .array elem len => refReadDataValFromAllocV2 alloc (.array elem len) baseOff
    | other =>
      match refAsEnumTy? other with
      | none => .error .unsupported
      | some ety =>
        match ety.tagRepr with
        | .zeroSized =>
          if refIsZstEnumTy ety then
            match refValOfEnumVariant? other 0 with
            | some val => .ok val | none => .error .unsupported
          else .error .unsupported
        | .scalar tagW tagS =>
          if !refEnumAdmitted ety then .error .unsupported
          else
            match refReadScalarIntFromAllocV2 alloc baseOff (toMiriSize tagW) with
            | .error k => .error k
            | .ok sci =>
              match refMiriTagToDiscrBits tagW tagS ety.discrWidth sci.data with
              | none => .error .unsupported
              | some discrBits =>
                match refFindDiscrVariant? discrBits ety.discriminants with
                | none => .error .undefined
                | some v =>
                  match refValOfEnumVariant? other v with
                  | some val => .ok val | none => .error .unsupported
end

/-- Write a non-tuple, non-array Profile v2 leaf `Val` into `alloc` at
`baseOff`. -/
noncomputable def refWriteLeafValToAllocV2
    (alloc : Miri.Memory.Allocation Provenance Unit)
    (baseOff : Nat) (ty : MirTy) (v : Val) :
    Except FaultKind (Miri.Memory.Allocation Provenance Unit) :=
  if !refIsSupportedLocalTyV2 ty || !refTyLayoutFitsU64V2 ty then
    .error .unsupported
  else
    let offSz := Size.ofBytes (UInt64.ofNat baseOff)
    let ld := refLayoutDataForTyV2 ty
    if ld.isZst then .ok alloc
    else
      match valToMiriImmediateV2 ty v with
      | .uninit => .error .unsupported
      | .scalar sc =>
        match alloc.writeScalar refRuntimeLayoutV2.base
            (allocRange offSz ld.size) sc with
        | .ok () alloc1 => .ok alloc1 | .error _ _ => .error .unsupported
      | .scalarPair a b =>
        let r1 := allocRange offSz a.size
        let r2 := allocRange
          (Size.ofBytes (UInt64.ofNat (baseOff + a.size.bytes.toNat))) b.size
        match alloc.writeScalar refRuntimeLayoutV2.base r1 a with
        | .error _ _ => .error .unsupported
        | .ok () alloc1 =>
          match alloc1.writeScalar refRuntimeLayoutV2.base r2 b with
          | .ok () alloc2 => .ok alloc2 | .error _ _ => .error .unsupported

/-- Write a fixed-size data or array value into `alloc` at `baseOff`
(standalone recursion on `MirTy` so `refWriteValToAllocV2` stays structurally
recursive). -/
noncomputable def refWriteDataValToAllocV2 :
    MirTy → Miri.Memory.Allocation Provenance Unit → Nat → Val →
      Except FaultKind (Miri.Memory.Allocation Provenance Unit)
  | .array elem len, alloc, baseOff, .array vs =>
    if !Nat.beq vs.length len || !refTyLayoutFitsU64V2 (.array elem len) then
      .error .unsupported
    else
      let elemLd := refLayoutDataForTyV2 elem
      refWriteArrayWithV2
        (fun a off val => refWriteDataValToAllocV2 elem a off val)
        alloc baseOff elemLd.size.bytes.toNat vs
  | .array _ _, _, _, _ => .error .unsupported
  | ty, alloc, baseOff, v => refWriteLeafValToAllocV2 alloc baseOff ty v

mutual
  /-- Write tuple field values sequentially into `alloc` at `baseOff`. -/
  noncomputable def refWriteTupleFieldsToAllocV2
      (alloc : Miri.Memory.Allocation Provenance Unit) (baseOff : Nat) :
      List MirTy → List Val → List Size →
        Except FaultKind (Miri.Memory.Allocation Provenance Unit)
    | [], [], [] => .ok alloc
    | ty :: tys, v :: vs, off :: offs =>
      match refWriteValToAllocV2 alloc (baseOff + off.bytes.toNat) ty v with
      | .error k => .error k
      | .ok alloc1 => refWriteTupleFieldsToAllocV2 alloc1 baseOff tys vs offs
    | _, _, _ => .error .unsupported

  /-- Write a Profile v2 `Val` into a mutable Miri `Allocation` at `baseOff`. -/
  noncomputable def refWriteValToAllocV2
      (alloc : Miri.Memory.Allocation Provenance Unit)
      (baseOff : Nat) (ty : MirTy) (v : Val) :
      Except FaultKind (Miri.Memory.Allocation Provenance Unit) :=
    let offSz := Size.ofBytes (UInt64.ofNat baseOff)
    match ty, v with
    | .tuple [.int w _, .bool], .tuple [.scalar sv, .bool b] =>
      let intSc : Miri.Memory.Scalar Provenance :=
        .fromScalarInt (miriScalar w sv.bits)
      let boolSc : Miri.Memory.Scalar Provenance := .fromBool b
      match alloc.writeScalar refRuntimeLayoutV2.base
          (allocRange offSz (toMiriSize w)) intSc with
      | .error _ _ => .error .unsupported
      | .ok () alloc1 =>
        let br := allocRange
          (Size.ofBytes (UInt64.ofNat (baseOff + w.byteSize))) (Size.ofBytes 1)
        match alloc1.writeScalar refRuntimeLayoutV2.base br boolSc with
        | .ok () alloc2 => .ok alloc2 | .error _ _ => .error .unsupported
    | .tuple fs, .tuple vs =>
      if !refTupleLayoutFitsU64V2 0 0 fs then .error .unsupported
      else
        let (offs, _, _) := refTupleFieldsLayoutV2 0 0 fs
        refWriteTupleFieldsToAllocV2 alloc baseOff fs vs offs
    | .array elem len, .array vs =>
      refWriteDataValToAllocV2 (.array elem len) alloc baseOff (.array vs)
    | _, _ =>
      if !refIsSupportedLocalTyV2 ty || !refTyLayoutFitsU64V2 ty then
        .error .unsupported
      else
        let ld := refLayoutDataForTyV2 ty
        if ld.isZst then .ok alloc
        else
          match valToMiriImmediateV2 ty v with
          | .uninit => .error .unsupported
          | .scalar sc =>
            match alloc.writeScalar refRuntimeLayoutV2.base
                (allocRange offSz ld.size) sc with
            | .ok () alloc1 => .ok alloc1 | .error _ _ => .error .unsupported
          | .scalarPair a b =>
            let r1 := allocRange offSz a.size
            let r2 := allocRange
              (Size.ofBytes (UInt64.ofNat (baseOff + a.size.bytes.toNat))) b.size
            match alloc.writeScalar refRuntimeLayoutV2.base r1 a with
            | .error _ _ => .error .unsupported
            | .ok () alloc1 =>
              match alloc1.writeScalar refRuntimeLayoutV2.base r2 b with
              | .ok () alloc2 => .ok alloc2 | .error _ _ => .error .unsupported
end

/-- Independent Miri-backed reference validity check for
`(&T | &mut T | &[uN] | &mut [uN])` against a real `RefMiriMem`. -/
noncomputable def refValidateRefInMiriV2 (memory : RefMiriMem)
    (reqMut : Trusted.MirAst.Mutability) (pointee : MirTy) (v : Val) :
    Except FaultKind Unit :=
  match pointee, v with
  | .slice (.int w _), .slicePtr pv len =>
    let elemLd := refScalarLayoutDataV2 w false
    let totalBytes := len.toNat * elemLd.size.bytes.toNat
    let elemPow2 := elemLd.align.abi.pow2
    if !Nat.blt totalBytes (Nat.pow 2 63) then .error .undefined
    else
      match pv.allocId with
      | none =>
        if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 totalBytes ||
            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 elemPow2)) 0 then
          .error .undefined
        else .ok ()
      | some aid =>
        match refExactAllocIdV2 aid with
        | none => .error .undefined
        | some mid =>
          match memory.live.find? (fun entry => entry.1 == mid) with
          | none => .error .undefined
          | some (_, la) =>
            let alloc := la.allocation
            let off := pv.offsetBytes.toNat
            if !Nat.ble (off + totalBytes) alloc.byteSize.bytes.toNat ||
                !Nat.ble elemPow2 alloc.align.pow2 ||
                !Nat.beq (Nat.mod off (Nat.pow 2 elemPow2)) 0 ||
                (Trusted.MirAst.Mutability.beq reqMut .mut &&
                  alloc.mutability != .Mut) then
              .error .undefined
            else if Nat.beq totalBytes 0 then
              .ok ()
            else
              let range := allocRange (Size.ofBytes pv.offsetBytes)
                (Size.ofBytes (UInt64.ofNat totalBytes))
              match alloc.initializationMask.isRangeInitialized range with
              | .ok (.ok ()) => .ok () | _ => .error .undefined
  | .slice _, _ => .error .unsupported
  | _, .ptr pv =>
    if !refIsSupportedPointeeTyV2 pointee || !refTyLayoutFitsU64V2 pointee then
      .error .unsupported
    else
      let ld := refLayoutDataForTyV2 pointee
      let sz := ld.size.bytes.toNat
      let pow2 := ld.align.abi.pow2
      match pv.allocId with
      | none =>
        if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 sz ||
            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 pow2)) 0 ||
            ld.uninhabited then .error .undefined
        else .ok ()
      | some aid =>
        match refExactAllocIdV2 aid with
        | none => .error .undefined
        | some mid =>
          match memory.live.find? (fun entry => entry.1 == mid) with
          | none => .error .undefined
          | some (_, la) =>
            let alloc := la.allocation
            let off := pv.offsetBytes.toNat
            if !Nat.ble (off + sz) alloc.byteSize.bytes.toNat ||
                !Nat.ble pow2 alloc.align.pow2 ||
                !Nat.beq (Nat.mod off (Nat.pow 2 pow2)) 0 ||
                (Trusted.MirAst.Mutability.beq reqMut .mut &&
                  alloc.mutability != .Mut) ||
                ld.uninhabited then
              .error .undefined
            else
              match refReadValFromAllocV2 alloc off pointee with
              | .ok _ => .ok () | .error k => .error k
  | _, _ => .error .unsupported

mutual
  /-- Validate all references embedded inside `(ty, v)` against `memory`;
  types or values outside the corresponded fragment fail closed to `false`. -/
  noncomputable def refRefsValidInMiriV2 (memory : RefMiriMem) :
      MirTy → Val → Bool
    | .ref reqMut pt, v =>
      match refValidateRefInMiriV2 memory reqMut pt v with
      | .ok () => true | .error _ => false
    | .tuple ts, .tuple vs => refRefsValidInMiriListV2 memory ts vs
    | .array elem _, .array vs => refRefsValidInMiriArrayV2 memory elem vs
    | .bool, .bool _ | .int _ _, .scalar _ | .char, .char _
    | .ordering, .ordering _ | .unit, .unit | .enum _, .enumVal _ _
    | .rawPtr _ _, .ptr _ | .rawPtr _ (.slice (.int _ _)), .slicePtr _ _
    | .rangeTo (.int .isize false), .rangeTo _
    | .rangeFrom (.int .isize false), .rangeFrom _ => true
    | _, _ => false

  /-- Pointwise Miri reference validity check. -/
  noncomputable def refRefsValidInMiriListV2 (memory : RefMiriMem) :
      List MirTy → List Val → Bool
    | [], [] => true
    | t :: ts, v :: vs =>
      refRefsValidInMiriV2 memory t v && refRefsValidInMiriListV2 memory ts vs
    | _, _ => false

  /-- Element-wise Miri reference validity check across fixed arrays. -/
  noncomputable def refRefsValidInMiriArrayV2 (memory : RefMiriMem)
      (elem : MirTy) : List Val → Bool
    | [] => true
    | v :: vs =>
      refRefsValidInMiriV2 memory elem v &&
        refRefsValidInMiriArrayV2 memory elem vs
end

mutual
  /-- Extract `(isMut, allocId, offset, byteSize)` spans for references. -/
  noncomputable def refAccessSpansV2 :
      MirTy → Val → List (Bool × Trusted.MirAst.AllocId × Nat × Nat)
    | .ref reqMut (.slice (.int w _)), .slicePtr pv len =>
      match pv.allocId with
      | some aid =>
        [(Trusted.MirAst.Mutability.beq reqMut .mut, aid, pv.offsetBytes.toNat,
          len.toNat * (toMiriSize w).bytes.toNat)]
      | none => []
    | .ref reqMut pt, .ptr pv =>
      if refIsUnsizedTyV2 pt then []
      else
        match pv.allocId with
        | some aid =>
          [(Trusted.MirAst.Mutability.beq reqMut .mut, aid, pv.offsetBytes.toNat,
            (refLayoutDataForTyV2 pt).size.bytes.toNat)]
        | none => []
    | .tuple ts, .tuple vs => refAccessSpansListV2 ts vs
    | .array elem _, .array vs => refAccessSpansArrayV2 elem vs
    | _, _ => []

  /-- Concatenate reference spans across a list of typed values. -/
  noncomputable def refAccessSpansListV2 :
      List MirTy → List Val →
        List (Bool × Trusted.MirAst.AllocId × Nat × Nat)
    | [], [] => []
    | t :: ts, v :: vs => refAccessSpansV2 t v ++ refAccessSpansListV2 ts vs
    | _, _ => []

  /-- Concatenate reference spans across fixed-array elements. -/
  noncomputable def refAccessSpansArrayV2 (elem : MirTy) :
      List Val → List (Bool × Trusted.MirAst.AllocId × Nat × Nat)
    | [] => []
    | v :: vs => refAccessSpansV2 elem v ++ refAccessSpansArrayV2 elem vs
end

/-- Disjointness of two reference spans `(isMut, allocId, start, len)`. -/
noncomputable def refSpanDisjointV2
    (a b : Bool × Trusted.MirAst.AllocId × Nat × Nat) : Bool :=
  let (m1, id1, s1, n1) := a
  let (m2, id2, s2, n2) := b
  if !(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then true
  else Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1

noncomputable def refSpanDisjointWithV2
    (a : Bool × Trusted.MirAst.AllocId × Nat × Nat) :
    List (Bool × Trusted.MirAst.AllocId × Nat × Nat) → Bool
  | [] => true
  | b :: rest => refSpanDisjointV2 a b && refSpanDisjointWithV2 a rest

/-- Pairwise disjointness across active mutable borrow spans. -/
noncomputable def refSpansPairwiseDisjointV2 :
    List (Bool × Trusted.MirAst.AllocId × Nat × Nat) → Bool
  | [] => true
  | a :: rest => refSpanDisjointWithV2 a rest && refSpansPairwiseDisjointV2 rest

mutual
  /-- Extract all allocation IDs referenced by any `.ref` in `(ty, v)`. -/
  noncomputable def refRefAllocIdsV2 :
      MirTy → Val → List Trusted.MirAst.AllocId
    | .ref _ (.slice _), .slicePtr pv _ =>
      match pv.allocId with | some aid => [aid] | none => []
    | .ref _ _, .ptr pv =>
      match pv.allocId with | some aid => [aid] | none => []
    | .tuple ts, .tuple vs => refRefAllocIdsListV2 ts vs
    | .array elem _, .array vs => refRefAllocIdsArrayV2 elem vs
    | _, _ => []

  /-- Concatenate referenced allocation IDs across a list of typed values. -/
  noncomputable def refRefAllocIdsListV2 :
      List MirTy → List Val → List Trusted.MirAst.AllocId
    | [], [] => []
    | t :: ts, v :: vs => refRefAllocIdsV2 t v ++ refRefAllocIdsListV2 ts vs
    | _, _ => []

  /-- Concatenate referenced allocation IDs across fixed-array elements. -/
  noncomputable def refRefAllocIdsArrayV2 (elem : MirTy) :
      List Val → List Trusted.MirAst.AllocId
    | [] => []
    | v :: vs => refRefAllocIdsV2 elem v ++ refRefAllocIdsArrayV2 elem vs
end

/-- Verify that every reference in `(ty, v)` stays inside caller memory `cm`. -/
noncomputable def refRefsStayInCallerMemV2 (cm : CallerMemory) (ty : MirTy)
    (v : Val) : Bool :=
  (refRefAllocIdsV2 ty v).all (fun aid => refHasAllocIdV2 aid cm.allocations)

/-- Decode the entry function's returned `Val` from `retPlace` after `Return`
and root stack cleanup, verifying caller confinement, reference validity, and
mutable-borrow disjointness. -/
noncomputable def refReadReturnValV2 (memory : RefMiriMem)
    (callerMem : CallerMemory) (retTy : MirTy)
    (retPlace : Miri.Interpreter.MPlaceTy Provenance) : Except FaultKind Val :=
  if !refTyLayoutFitsU64V2 retTy then .error .unsupported
  else
    let rawRes : Except FaultKind Val :=
      match retTy with
      | .unit => .ok .unit
      | _ =>
        match retPlace.mplace.ptr.provenance with
        | some (.concrete allocId _) =>
          match memory.live.find? (fun entry => entry.1 == allocId) with
          | none => .error .unsupported
          | some (_, la) => refReadValFromAllocV2 la.allocation 0 retTy
        | _ => .error .unsupported
    match rawRes with
    | .error k => .error k
    | .ok retVal =>
      if !refRefsStayInCallerMemV2 callerMem retTy retVal ||
          !refRefsValidInMiriV2 memory retTy retVal ||
          !refSpansPairwiseDisjointV2 (refAccessSpansV2 retTy retVal) then
        .error .undefined
      else .ok retVal

/-! ## Section 5: Real `Miri.MIR` Syntax Lowering for Profile v2 -/

/-- Base `TyId` offset reserved for synthetic `CoreCallOp` `FnDef` callees. -/
noncomputable def refCoreCallTyBase (types : List MirTy) : Nat :=
  types.length + 16

/-- Encode a `CoreCallOp` into a collision-free synthetic `DefId`; any
unmodeled `CoreCallOp` maps to `4` (`none` in `refCoreCallOfDefId`). -/
noncomputable def refCoreCallDefId (types : List MirTy) : CoreCallOp → Nat
  | .sliceLen => 0
  | .sliceGetUncheckedRangeTo => 1
  | .sliceGetUncheckedRangeFrom => 2
  | .usizeUncheckedSub => 3
  | .ptrAdd reqMut pointee =>
    6 + 2 * tyIdFor types pointee +
      (if Trusted.MirAst.Mutability.beq reqMut .mut then 1 else 0)
  | _ => 4

/-- Decode a synthetic `CoreCallOp` `DefId` back to its `CoreCallOp`. -/
noncomputable def refCoreCallOfDefId (types : List MirTy) (defId : Nat) :
    Option CoreCallOp :=
  match defId with
  | 0 => some .sliceLen
  | 1 => some .sliceGetUncheckedRangeTo
  | 2 => some .sliceGetUncheckedRangeFrom
  | 3 => some .usizeUncheckedSub
  | 4 | 5 => none
  | n + 6 =>
    let reqMut : Trusted.MirAst.Mutability :=
      if Nat.beq (Nat.mod n 2) 1 then .mut else .shared
    match resolveTy types (Nat.div n 2) with
    | some pt => some (.ptrAdd reqMut pt)
    | none => none

/-- Zero-sized `ConstOperand` representing the `FnDef` callee of `op`. -/
noncomputable def mkCoreCallFnOperandV2 (types : List MirTy) (op : CoreCallOp) :
    Miri.MIR.Operand :=
  .Constant ⟨⟨0⟩, none,
    .Val .ZeroSized (refCoreCallTyBase types + refCoreCallDefId types op)⟩

/-- Lower a `RefProjectionElem` to `Miri.MIR.ProjectionElem`; unmodeled
projections lower fail-closed to `.PhantomDeref`. -/
noncomputable def toMiriProjElemV2 (types : List MirTy) :
    RefProjectionElem → Miri.MIR.ProjectionElem
  | .deref => .Deref
  | .field idx tyId => .Field idx (canonicalTyId types tyId)
  | _ => .PhantomDeref

/-- Lower a `RefPlace` to a real `Miri.MIR.Place`. -/
noncomputable def toMiriPlaceV2 (types : List MirTy) (rp : RefPlace) :
    Miri.MIR.Place :=
  ⟨rp.localId, Array.mk (rp.projection.map (toMiriProjElemV2 types))⟩

/-- Lower a `RefOperand` to a real `Miri.MIR.Operand`. -/
noncomputable def toMiriOperandV2 (types : List MirTy) :
    RefOperand → Miri.MIR.Operand
  | .copy rp => .Copy (toMiriPlaceV2 types rp)
  | .move rp => .Move (toMiriPlaceV2 types rp)
  | .constant c =>
    let cv : Miri.MIR.ConstValue :=
      match c.lit with
      | .scalar bits => .Scalar (.Int bits.toNat 16)
      | .zeroSized => .ZeroSized
      | _ => .Indirect 0 0
    .Constant ⟨⟨0⟩, none, .Val cv (canonicalTyId types c.ty)⟩

/-- Lower a `RefRvalue` to a real `Miri.MIR.Rvalue` for Profile v2; any
unmodeled rvalue or cast kind lowers fail-closed to `.CopyForDeref`. -/
noncomputable def toMiriRvalueV2 (types : List MirTy) :
    RefRvalue → Miri.MIR.Rvalue
  | .use op => .Use (toMiriOperandV2 types op) .No
  | .useRetag op => .Use (toMiriOperandV2 types op) .Yes
  | .binaryOp op lhs rhs =>
    .BinaryOp (toMiriBinOp op) (toMiriOperandV2 types lhs)
      (toMiriOperandV2 types rhs)
  | .unaryOp op opnd => .UnaryOp (toMiriUnOp op) (toMiriOperandV2 types opnd)
  | .cast .intToInt opnd ty =>
    .Cast .IntToInt (toMiriOperandV2 types opnd) (canonicalTyId types ty)
  | .cast .ptrToPtr opnd ty =>
    .Cast .PtrToPtr (toMiriOperandV2 types opnd) (canonicalTyId types ty)
  | .cast .intToPtr opnd ty =>
    .Cast .PointerWithExposedProvenance (toMiriOperandV2 types opnd)
      (canonicalTyId types ty)
  | .discriminant rp => .Discriminant (toMiriPlaceV2 types rp)
  | .ref .shared rp => .Ref .Erased .Shared (toMiriPlaceV2 types rp)
  | .ref .mut rp => .Ref .Erased (.Mut .Default) (toMiriPlaceV2 types rp)
  | .addressOf .shared rp => .RawPtr .Const (toMiriPlaceV2 types rp)
  | .addressOf .mut rp => .RawPtr .Mut (toMiriPlaceV2 types rp)
  | .aggregateTuple ops =>
    .Aggregate .Tuple (Array.mk (ops.map (toMiriOperandV2 types)))
  | .aggregateRangeTo _ endOp =>
    .Aggregate .Tuple (Array.mk [toMiriOperandV2 types endOp])
  | .aggregateRangeFrom _ startOp =>
    .Aggregate .Tuple (Array.mk [toMiriOperandV2 types startOp])
  | _ => .CopyForDeref ⟨0, Array.empty⟩

/-- Lower a `RefStatementKind` to `Miri.MIR.Statement`; unmodeled statements
lower fail-closed to `.CopyForDeref`. -/
noncomputable def toMiriStatementV2 (types : List MirTy) :
    RefStatementKind → Miri.MIR.Statement
  | .nop => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Nop }
  | .storageLive id => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageLive id }
  | .storageDead id => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageDead id }
  | .assign dst rv =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign (toMiriPlaceV2 types dst) (toMiriRvalueV2 types rv) }
  | _ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign ⟨0, Array.empty⟩ (.CopyForDeref ⟨0, Array.empty⟩) }

/-- Constant `usize` operand for lowered `AssertKind` payloads. -/
noncomputable def mkConstUsizeOperandV2 (types : List MirTy) (n : Nat) :
    Miri.MIR.Operand :=
  .Constant ⟨⟨0⟩, none,
    .Val (.Scalar (.Int n 16)) (tyIdFor types (.int .isize false))⟩

/-- Lower `Trusted.MirAst.AssertKind` to `Miri.MIR.AssertKind`. -/
noncomputable def toMiriAssertKindV2 (types : List MirTy) :
    AssertKind → Miri.MIR.AssertKind
  | .misalignedPtrDeref =>
    .MisalignedPointerDereference
      (mkConstUsizeOperandV2 types 1) (mkConstUsizeOperandV2 types 0)
  | .nullPtrDeref => .NullPointerDereference
  | .boundsCheck =>
    .BoundsCheck (mkConstUsizeOperandV2 types 0) (mkConstUsizeOperandV2 types 0)
  | .overflow op =>
    .Overflow (toMiriBinOp op)
      (mkConstUsizeOperandV2 types 0) (mkConstUsizeOperandV2 types 0)
  | .overflowNeg => .OverflowNeg (mkConstUsizeOperandV2 types 0)
  | .divByZero => .DivisionByZero (mkConstUsizeOperandV2 types 0)
  | .remByZero => .RemainderByZero (mkConstUsizeOperandV2 types 0)
  | _ => .NullReferenceConstructed

/-- Lower `Trusted.MirAst.UnwindAction` to `Miri.MIR.UnwindAction`. -/
noncomputable def toMiriUnwindActionV2 : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue | .unreachable => .Unreachable
  | .terminate => .Terminate .Abi | .cleanup bb => .Cleanup bb

/-- Lower a `RefTerminatorKind` to `Miri.MIR.Terminator` for Profile v2; any
unmodeled terminator or `CoreCallOp` lowers fail-closed to `.CoroutineDrop`. -/
noncomputable def toMiriTerminatorV2 (types : List MirTy) :
    RefTerminatorKind → Miri.MIR.Terminator
  | .goto target =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Goto target Array.empty }
  | .return_ => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  | .unreachable => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Unreachable }
  | .switchInt discr targets =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SwitchInt (toMiriOperandV2 types discr)
        { cases := Array.mk (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  | .assert cond expected msg target unwind =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assert (toMiriOperandV2 types cond) expected
        (toMiriAssertKindV2 types msg) target (toMiriUnwindActionV2 unwind) }
  | .coreCall op args dst (some target) unwind =>
    if !dst.projection.isEmpty then
      { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .CoroutineDrop }
    else
      match op with
      | .sliceLen | .sliceGetUncheckedRangeTo | .sliceGetUncheckedRangeFrom
      | .usizeUncheckedSub | .ptrAdd _ _ =>
        { sourceInfo := ⟨⟨0⟩, 0⟩
          kind := .Call (mkCoreCallFnOperandV2 types op)
            (Array.mk (args.map (fun a => ⟨⟨0⟩, toMiriOperandV2 types a⟩)))
            (toMiriPlaceV2 types dst) (some target)
            (toMiriUnwindActionV2 unwind) .Normal ⟨0⟩ }
      | _ => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .CoroutineDrop }
  | _ => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .CoroutineDrop }

/-- Lower a `RefBasicBlock` to `Miri.MIR.BasicBlock` for Profile v2. -/
noncomputable def toMiriBasicBlockV2 (types : List MirTy)
    (rbb : RefBasicBlock) : Miri.MIR.BasicBlock := {
  statements := Array.mk (rbb.statements.map (toMiriStatementV2 types))
  terminator := toMiriTerminatorV2 types rbb.terminator
  cleanup := rbb.cleanup
}

/-- Lower a `RefBody` to a real `Miri.MIR.Body` for Profile v2. -/
noncomputable def toMiriBodyV2 (types : List MirTy) (rbody : RefBody) :
    Miri.MIR.Body := {
  phase := .Runtime .PostCleanup
  argumentCount := rbody.argumentCount
  spreadArgument := none
  locals := Array.mk (rbody.locals.map (canonicalTyId types))
  basicBlocks := Array.mk (rbody.basicBlocks.map (toMiriBasicBlockV2 types))
}

/-! ## Section 6: Profile v2 `ExecutionMachine.Config` Construction -/

/-- Resource budget passed to `Miri.Interpreter.ExecutionMachine.step`. -/
noncomputable def refLimitsV2 : Miri.Interpreter.ExecutionMachine.Limits :=
  { callDispatch := 16, casts := 16, retag := 16, validation := 16 }

/-- Dynamic layout resolver for unsized slice places in Profile v2. -/
noncomputable def refDynamicLayoutResolverV2 (types : List MirTy) :
    Miri.Interpreter.DynamicLayoutResolver Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser) :=
  fun mem h place =>
    match place.layout.canonicalType with
    | none => ⟨mem, h, .ok none⟩
    | some tyId =>
      match resolveTy types tyId with
      | some (.slice elem) =>
        match place.mplace.metadata with
        | .metadata sc =>
          match sc.toTargetUsize (Size.ofBytes 8) with
          | .error e => ⟨mem, h, .error (toString e)⟩
          | .ok len =>
            if !refTyLayoutFitsU64V2 elem then
              ⟨mem, h, .error "slice element layout exceeds UInt64"⟩
            else
              let elemLd := refLayoutDataForTyV2 elem
              let prod := elemLd.size.bytes.toNat * len.toNat
              if !Nat.blt prod (Nat.pow 2 63) then
                ⟨mem,
                  ⟨h.machine, some (.undefinedBehavior "InvalidMeta(SliceTooBig)")⟩,
                  .error "InvalidMeta(SliceTooBig)"⟩
              else
                ⟨mem, h, .ok (some (Size.ofBytes (UInt64.ofNat prod),
                  elemLd.align.abi))⟩
        | .none => ⟨mem, h, .error "slice place missing length metadata"⟩
      | _ => ⟨mem, h, .ok none⟩

/-- `PlaceMachine.AccessConfig` for Profile v2. -/
noncomputable def refAccessConfigV2 (types : List MirTy) :
    Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser :=
  { refAccessConfig with
    runtime := refRuntimeLayoutV2
    dynamicLayout := refDynamicLayoutResolverV2 types
    deinitMovedPlace := true }

/-- Symbolic alignment context for `PointerPlaceMachine.misalignmentWith`. -/
noncomputable def refAlignCtxV2 :
    Miri.Interpreter.PointerPlaceMachine.AlignmentContext RefUser :=
  { policy := fun _ => .Symbolic, promises := fun _ => Array.empty }

/-- Resolve a `LocalLayout` by canonical `TyId` against `types`, failing
closed if `ty`'s layout does not fit in `UInt64`. -/
noncomputable def refLayoutOfTyIdV2 (types : List MirTy) (tyId : TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.LocalLayout :=
  match resolveTy types tyId with
  | some ty =>
    match refCheckedLocalLayoutForTyV2 types ty with
    | some lay => .ok lay
    | none => .error (.unsupported "layout exceeds UInt64")
  | none => .error (.invalidProgram "unknown TyId in Profile v2 layoutOf")

/-- Field-layout projection for Profile v2 tuples, ranges, slices, and enums. -/
noncomputable def refProjectFieldLayoutV2 (types : List MirTy)
    (base : Miri.Interpreter.LocalLayout) (fieldIdx : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  let checkedProj (ty : MirTy) :
      Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
    match refCheckedLocalLayoutForTyV2 types ty with
    | some lay => .ok lay
    | none => .error (.obligation "projected layout exceeds UInt64")
  match resolveTy types base.ty with
  | some (.tuple fs) =>
    match Trusted.MirSemantics.getElem? fs fieldIdx with
    | some fTy => checkedProj fTy
    | none => .error (.invariant "tuple field index out of bounds")
  | some (.rangeTo (.int .isize false)) | some (.rangeFrom (.int .isize false)) =>
    if Nat.beq fieldIdx 0 then checkedProj (.int .isize false)
    else .error (.invariant "range field index out of bounds")
  | some (.slice elem) =>
    if Nat.beq fieldIdx 0 then checkedProj elem
    else .error (.invariant "slice element field index out of bounds")
  | some ty =>
    match refAsEnumTy? ty with
    | some ety =>
      if Nat.beq fieldIdx 0 then
        match ety.tagRepr with
        | .scalar tagW tagS => checkedProj (.int tagW tagS)
        | .zeroSized => .error (.invariant "field projection on ZST enum")
      else .error (.obligation "non-zero field projection on enum")
    | none => .error (.obligation "field projection unsupported in Profile v2")
  | none => .error (.obligation "unknown type in field projection")

/-- Variant-layout projection for Profile v2 enum-like types. -/
noncomputable def refProjectVariantLayoutV2 (types : List MirTy)
    (base : Miri.Interpreter.LocalLayout) (variant : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  match (resolveTy types base.ty).bind refAsEnumTy? with
  | some ety =>
    if Nat.blt variant ety.discriminants.length then
      .ok ⟨base.ty, { refUnitLayoutDataV2 with variants := .Single variant }⟩
    else .error (.invariant "enum variant index out of bounds")
  | none => .error (.obligation "variant projection unsupported in Profile v2")

/-- Pure `ProjectionCx` for Profile v2. -/
noncomputable def refProjectionCxV2 (types : List MirTy) :
    Miri.Interpreter.ProjectionCx Provenance :=
  { refProjectionCx types with
    target := refRuntimeLayoutV2.base
    isSliceOrStr := fun tyId =>
      match resolveTy types tyId with | some (.slice _) => .ok true | _ => .ok false
    field := refProjectFieldLayoutV2 types
    variant := refProjectVariantLayoutV2 types
    layoutOf := fun tyId =>
      match resolveTy types tyId with
      | some ty =>
        match refCheckedLocalLayoutForTyV2 types ty with
        | some lay => .ok lay
        | none => .error (.obligation "layout exceeds UInt64")
      | none => .error (.invariant "unknown TyId in ProjectionCx.layoutOf") }

/-- `DynamicLayoutHooks` for Profile v2 supporting sized types and slices. -/
noncomputable def refDynamicLayoutHooksV2 (types : List MirTy) :
    Miri.Interpreter.DynamicLayoutHooks Provenance RefMiriState Choice := {
  target := refRuntimeLayoutV2.base, maxSizeOfVal := refMaxSizeOfVal
  classify := fun _ tyId st =>
    match resolveTy types tyId with
    | some (.slice _) => .ok .slice st
    | _ => .error (.unsupported "unsized non-slice type unsupported") st
  field := fun _ base idx st =>
    match refProjectFieldLayoutV2 types base idx with
    | .ok l => .ok l st | .error e => .error (refProjErrToStepErr e) st
  packedAlign := fun _ _ st => .ok none st
  vtableSizeAndAlign := fun _ _ _ st => .error (.unsupported "vtable unsupported") st
}

/-- Nullness check for relative-offset Profile v2 pointers: provenance pointers
are non-null; provenance-less integer pointers are null iff address is `0`. -/
noncomputable def refScalarMayBeNullV2 (sc : Miri.Memory.Scalar Provenance) :
    Except Miri.Interpreter.StepError Bool :=
  if sc.isPointer then .ok false
  else
    match sc.tryToScalarInt with
    | .ok (.integer sci) => .ok sci.isNull
    | .ok (.erasedPointer _ _) => .ok false
    | .error e => .error (Miri.Interpreter.ScalarOps.scalarError e)

/-- Pointer access check for Profile v2 validity and safe-pointer deref. -/
noncomputable def refCheckPointerAccessResultV2 (types : List MirTy)
    (ptr : Pointer (Option Provenance)) (sz : Size) (st : RefMiriState) :
    RefMiriRes (Except AccessError Unit) :=
  match sizeAsI64 sz with
  | .error e => .ok (.error e) st
  | .ok signed =>
    if signed == 0 then .ok (.ok ()) st
    else
      let resolved := refResolvePointerPure ptr signed
      match checkPtrAccess ⟨(refAccessConfigV2 types).runtime.pointerSize⟩
          ptr sz (.dereferenceable "pointer") (fun _ _ => resolved)
          st.machine.memory.getAllocInfo with
      | .ok () => .ok (.ok ()) st
      | .error e => .ok (.error e) st

/-- Pointer alignment check using symbolic alignment (`Symbolic`). -/
noncomputable def refCheckPointerAlignResultV2 (types : List MirTy)
    (ptr : Pointer (Option Provenance)) (required : Align) (st : RefMiriState) :
    RefMiriRes (Except Misalignment Unit) :=
  match Miri.Interpreter.PointerPlaceMachine.misalignmentWith
      (refAccessConfigV2 types) refAlignCtxV2 ptr required st with
  | .error e st1 => .error e st1
  | .ok none st1 => .ok (.ok ()) st1
  | .ok (some bad) st1 => .ok (.error bad) st1

/-- Convert an immediate pointer into a typed `MPlaceTy` caching its symbolic
`Misalignment` (`PointerPlaceMachine.fromImmediate`). -/
noncomputable def refFromImmediatePtrV2 (types : List MirTy)
    (value : Miri.Interpreter.RvalueImmTy Provenance) (st : RefMiriState) :
    RefMiriRes (Miri.Interpreter.MPlaceTy Provenance) :=
  match resolveTy types value.layout.ty with
  | some (.ref _ pt) | some (.rawPtr _ pt) =>
    if !refTyLayoutFitsU64V2 pt then
      .error (.unsupported "pointee layout exceeds UInt64") st
    else
      let ptLayout := refLocalLayoutForTyV2 types pt
      match value.imm.toScalarAndMeta with
      | .error e => .error (Miri.Interpreter.ScalarOps.immediateError e) st
      | .ok (sc, metaVal) =>
        match sc.toPointer refRuntimeLayoutV2.base with
        | .error e => .error (Miri.Interpreter.ScalarOps.scalarError e) st
        | .ok ptr =>
          match Miri.Interpreter.PointerPlaceMachine.misalignmentWith
              (refAccessConfigV2 types) refAlignCtxV2 ptr
              ptLayout.layout.align.abi st with
          | .error e st1 => .error e st1
          | .ok mis st1 => .ok ⟨⟨ptr, metaVal, mis⟩, ptLayout⟩ st1
  | _ => .error (.invalidProgram "imm_ptr_to_mplace on non-pointer type") st

/-- Full typed dereference in Profile v2 (`PointerPlaceMachine.dereference`).
On `&T` / `&mut T` references, eagerly checks non-null, access, alignment,
and pointee validity via `refValidateRefInMiriV2` (matching
`Trusted.MirSemantics` deref rules rather than lazy scalar validity on read).
-/
noncomputable def refDereferenceOpV2 (types : List MirTy) (c : Choice)
    (source : Miri.Interpreter.OpTy Provenance) (st : RefMiriState) :
    RefMiriRes (Miri.Interpreter.MPlaceTy Provenance) :=
  let ptrKindOpt : Option (Bool × Trusted.MirAst.Mutability × MirTy) :=
    match resolveTy types source.layout.ty with
    | some (.ref m pt) => some (true, m, pt)
    | some (.rawPtr m pt) => some (false, m, pt)
    | _ => none
  match ptrKindOpt with
  | none => .error (.invalidProgram "dereferencing non-pointer type") st
  | some (isRef, reqMut, pt) =>
    match Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 types) source st with
    | .error e st1 => .error e st1
    | .ok val st1 =>
      match refFromImmediatePtrV2 types val st1 with
      | .error e st2 => .error e st2
      | .ok place st2 =>
        if !isRef then .ok place st2
        else
          match Miri.Memory.Scalar.fromMaybePointer
              refRuntimeLayoutV2.base place.mplace.ptr with
          | .error e => .error (Miri.Interpreter.ScalarOps.scalarError e) st2
          | .ok sc =>
            match refScalarMayBeNullV2 sc with
            | .error e => .error e st2
            | .ok true => .error (.undefinedBehavior "null reference deref") st2
            | .ok false =>
              match Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
                  (refDynamicLayoutHooksV2 types) c 8
                  place.mplace.metadata place.layout st2 with
              | .error e st3 => .error e st3
              | .ok dynOpt st3 =>
                let (sz, al) := dynOpt.getD
                  (place.layout.layout.size, place.layout.layout.align.abi)
                match refCheckPointerAccessResultV2 types
                    place.mplace.ptr sz st3 with
                | .error e st4 => .error e st4
                | .ok (.error ae) st4 =>
                  .error (.undefinedBehavior ("deref access: " ++ reprStr ae)) st4
                | .ok (.ok ()) st4 =>
                  match refCheckPointerAlignResultV2 types
                      place.mplace.ptr al st4 with
                  | .error e st5 => .error e st5
                  | .ok (.error bad) st5 =>
                    .error (.undefinedBehavior ("deref align: " ++ reprStr bad)) st5
                  | .ok (.ok ()) st5 =>
                    let pv := miriPtrToPtrValV2 place.mplace.ptr
                    let refValOpt : Option Val :=
                      match pt, place.mplace.metadata with
                      | .slice _, .metadata lenSc =>
                        match lenSc.toTargetUsize (Size.ofBytes 8) with
                        | .ok len => some (.slicePtr pv len) | .error _ => none
                      | .slice _, .none => none
                      | _, _ => some (.ptr pv)
                    match refValOpt with
                    | none => .error (.invalidProgram "missing slice metadata") st5
                    | some rv =>
                      match refValidateRefInMiriV2 st5.machine.memory reqMut
                          pt rv with
                      | .ok () => .ok place st5
                      | .error .undefined =>
                        .error (.undefinedBehavior "invalid reference deref") st5
                      | .error .unsupported =>
                        .error (.unsupported "unsupported reference deref") st5

/-- Base `PlaceMachine.CompilerHooks` for Profile v2 before `validate`. -/
noncomputable def refBaseCompilerHooksV2 (types : List MirTy) :
    Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice :=
  let noDeref :
      Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice :=
    { refBaseCompilerHooks types with
      layout := fun _ localId st =>
        match st.stack.currentFrame? with
        | none => .error (.stack .emptyStack) st
        | some frame =>
          match frame.body.locals[localId]? with
          | none => .error (.stack (.missingLocalType localId)) st
          | some tyId =>
            match refLayoutOfTyIdV2 types tyId with
            | .ok l => .ok l st | .error e => .error e st
      projection := fun _ st =>
        .ok { refProjectionCxV2 types with
          memoryOffset := Miri.Interpreter.projectionMemoryOffset
            refPointerArithmetic refResolvePointerPure
            st.machine.memory.getAllocInfo } st }
  let basePlaces := Miri.Interpreter.PlaceMachine.placeHooks
    (refAccessConfigV2 types) refAllocationConfig noDeref
  { noDeref with
    deref := fun c source skip st =>
      match Miri.Interpreter.placeToOp basePlaces c source st with
      | .error e st1 => .error e st1
      | .ok op st1 =>
        if skip then
          match Miri.Interpreter.PlaceMachine.readImmediate
              (refAccessConfigV2 types) op st1 with
          | .error e st2 => .error e st2
          | .ok val st2 =>
            match refFromImmediatePtrV2 types val st2 with
            | .error e st3 => .error e st3
            | .ok mp st3 => .ok ⟨.memory mp.mplace, mp.layout⟩ st3
        else
          match refDereferenceOpV2 types c op st1 with
          | .error e st2 => .error e st2
          | .ok mp st2 => .ok ⟨.memory mp.mplace, mp.layout⟩ st2 }

/-- Base `PlaceProjectionHooks` for Profile v2. -/
noncomputable def refBasePlaceProjectionHooksV2 (types : List MirTy) :
    Miri.Interpreter.PlaceProjectionHooks Provenance RefMiriState Choice
      Miri.Interpreter.MachineHooks.FrameExtra :=
  { refBasePlaceProjectionHooks types with
    place := Miri.Interpreter.PlaceMachine.placeHooks
      (refAccessConfigV2 types) refAllocationConfig
      (refBaseCompilerHooksV2 types)
    target := refRuntimeLayoutV2.base
    dynamic := refDynamicLayoutHooksV2 types
    isSliceOrStr := fun _ tyId st =>
      match resolveTy types tyId with
      | some (.slice _) => .ok true st | _ => .ok false st
    field := fun _ base idx st =>
      match refProjectFieldLayoutV2 types base idx with
      | .ok l => .ok l st | .error e => .error (refProjErrToStepErr e) st
    variant := fun _ base v st =>
      match refProjectVariantLayoutV2 types base v with
      | .ok l => .ok l st | .error e => .error (refProjErrToStepErr e) st
    layoutOf := fun _ tyId st =>
      match refLayoutOfTyIdV2 types tyId with
      | .ok l => .ok l st | .error e => .error e st }

/-- Decode a `Miri.MIR.ConstOperand` in Profile v2 (including `CoreCallOp`
`FnDef` constants). -/
noncomputable def refEvalConstOperandV2 (types : List MirTy)
    (c : Miri.MIR.ConstOperand) (st : RefMiriState) :
    RefMiriRes (Miri.Interpreter.OpTy Provenance) :=
  match c with
  | ⟨_, _, .Val .ZeroSized tyId⟩ =>
    if Nat.ble (refCoreCallTyBase types) tyId then
      match refCoreCallOfDefId types (tyId - refCoreCallTyBase types) with
      | some _ => .ok ⟨.immediate .uninit, ⟨tyId, refUnitLayoutDataV2⟩⟩ st
      | none => .error (.unsupported "unknown coreCall FnDef") st
    else
      match Trusted.MirSemantics.getElem? types tyId with
      | none => .error (.unsupported "constant TyId out of bounds") st
      | some ty =>
        match refCheckedLocalLayoutForTyV2 types ty with
        | none => .error (.unsupported "constant layout exceeds UInt64") st
        | some lay =>
          match evalRefConstLit ty .zeroSized with
          | .ok v =>
            .ok ⟨.immediate (valToMiriImmediateV2 ty v), lay⟩ st
          | .error .undefined =>
            .error (.undefinedBehavior "invalid zero-sized constant") st
          | .error .unsupported =>
            .error (.unsupported "unsupported zero-sized constant") st
  | ⟨_, _, .Val (.Scalar (.Int bitsNat _)) tyId⟩ =>
    match Trusted.MirSemantics.getElem? types tyId with
    | none =>
      match resolveTy types tyId with
      | some (.int .isize false) =>
        match evalRefConstLit (.int .isize false)
            (.scalar (BitVec.ofNat 128 bitsNat)) with
        | .ok v =>
          .ok ⟨.immediate (valToMiriImmediateV2 (.int .isize false) v),
            refLocalLayoutForTyV2 types (.int .isize false)⟩ st
        | _ => .error (.unsupported "invalid aux usize constant") st
      | _ => .error (.unsupported "constant TyId out of bounds") st
    | some ty =>
      match refCheckedLocalLayoutForTyV2 types ty with
      | none => .error (.unsupported "constant layout exceeds UInt64") st
      | some lay =>
        match evalRefConstLit ty (.scalar (BitVec.ofNat 128 bitsNat)) with
        | .ok v =>
          .ok ⟨.immediate (valToMiriImmediateV2 ty v), lay⟩ st
        | .error .undefined =>
          .error (.undefinedBehavior "invalid constant scalar literal") st
        | .error .unsupported =>
          .error (.unsupported "unsupported constant scalar literal") st
  | _ => .error (.unsupported "unsupported ConstOperand") st

/-- `ExecutionLeaves.Operand` for Profile v2. -/
noncomputable def refOperandLeavesV2 (types : List MirTy) :
    Miri.Interpreter.ExecutionLeaves.Operand RefMiriState Choice := {
  checkPlaceType := fun _ _ _ st => .ok () st
  dereference := refDereferenceOpV2 types
  runtimeChecks := fun _ _ st => .error (.unsupported "RuntimeChecks") st
  boolLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .bool) st
  constantAt := fun _ _ c _ st => refEvalConstOperandV2 types c st
}

/-- Padding decision for Profile v2 `PlaceCopyHooks`. -/
noncomputable def refHasPaddingV2 (layout : Miri.Interpreter.LocalLayout) :
    Except Miri.Interpreter.StepError Bool :=
  match layout.layout.backendRepr with
  | .Scalar _ => .ok false
  | .ScalarPair (a := a) (b := b) (bOffset := _) =>
    match a.size refRuntimeLayoutV2, b.size refRuntimeLayoutV2 with
    | .ok sizeA, .ok sizeB =>
      match sizeA.add sizeB with
      | .ok total => .ok (total != layout.layout.size)
      | .error _ => .error (.invalidProgram "scalar-pair size overflow")
    | _, _ => .error (.invalidProgram "scalar-pair scalar size unavailable")
  | _ => .ok true

/-- `PlaceCopyHooks` for Profile v2. -/
noncomputable def refPlaceCopyHooksV2 (types : List MirTy) :
    Miri.Interpreter.PlaceCopyHooks Provenance RefMiriState Choice := {
  compatible := fun a b => .ok (a.ty == b.ty)
  hasPadding := refHasPaddingV2
  readRaw := fun _ =>
    Miri.Interpreter.PlaceMachine.readRaw (refAccessConfigV2 types)
  memoryCopy := fun _ _ _ st =>
    .error (.unsupported "memoryCopy bound by ExecutionMachine.withValidation") st
  validateSource := fun _ _ _ st => .ok () st
}

/-- `ExecutionLeaves.Discriminant` for Profile v2. `discriminantLayout` checks
`refEnumAdmitted ety` and returns `u8` (`(.int .i8 false)`) for non-enum types
during uniform `ValidityVisitor` dispatch, while tag-value and variant hooks
dispatch on `refAsEnumTy?` relying on `refDiscriminantTypesValid` at entry. -/
noncomputable def refDiscriminantLeavesV2 (types : List MirTy) :
    Miri.Interpreter.ExecutionLeaves.Discriminant RefMiriState Choice := {
  discriminantLayout := fun _ tyId st =>
    match resolveTy types tyId with
    | none => .error (.unsupported "unknown type in discriminantLayout") st
    | some ty =>
      match refAsEnumTy? ty with
      | some ety =>
        if refEnumAdmitted ety then
          .ok (refLocalLayoutForTyV2 types (.int ety.discrWidth ety.discrSigned)) st
        else .error (.unsupported "unadmitted enum in discriminantLayout") st
      | none => .ok (refLocalLayoutForTyV2 types (.int .i8 false)) st
  tagLayout := fun _ tag st =>
    match tag.primitive with
    | .Int integer signed =>
      .ok (refLocalLayoutForTyV2 types (.int (intWidthOfMiriInteger integer) signed)) st
    | _ => .error (.invalidProgram "non-integer enum tag") st
  discriminantValue := fun _ tyId variant st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety =>
      match Trusted.MirSemantics.getElem? ety.discriminants variant with
      | some disc =>
        .ok (some (tyIdFor types (.int ety.discrWidth ety.discrSigned),
          BitVec.ofNat 128 disc)) st
      | none => .error (.invalidProgram "enum variant out of bounds") st
    | none => .error (.unsupported "discriminantValue on non-enum type") st
  variantForDiscriminant := fun _ tyId discrBits st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety => .ok (refFindDiscrVariant? discrBits ety.discriminants) st
    | none => .error (.unsupported "variantForDiscriminant on non-enum type") st
  adtVariantCount := fun _ tyId st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety => .ok ety.discriminants.length st
    | none => .error (.unsupported "adtVariantCount on non-enum type") st
  scalarMayBeNull := fun _ sc st =>
    match refScalarMayBeNullV2 sc with | .ok b => .ok b st | .error e => .error e st
}

/-- `OperandMachine.Hooks` used by `ValidityVisitor`'s `discriminant` hooks. -/
noncomputable def refValidityOperandHooksV2 (types : List MirTy) :
    Miri.Interpreter.OperandMachine.Hooks Unit RefUser Choice := {
  compiler := refBaseCompilerHooksV2 types
  projection := refBasePlaceProjectionHooksV2 types
  layoutCompatible := (refPlaceCopyHooksV2 types).compatible
  checkPlaceType := fun _ _ _ st => .ok () st
  dereference := (refOperandLeavesV2 types).dereference
  runtimeChecks := (refOperandLeavesV2 types).runtimeChecks
  boolLayout := (refOperandLeavesV2 types).boolLayout
  constant := fun _ _ _ st => .error (.unsupported "constant unused in validity") st
  constantAt := (refOperandLeavesV2 types).constantAt
  deinitMovedPlace := true
}

/-- `DiscriminantHooks` supplied to `ValidityVisitor.Hooks` in Profile v2. -/
noncomputable def refValidityDiscriminantHooksV2 (types : List MirTy) :
    Miri.Interpreter.DiscriminantHooks Provenance RefMiriState Choice
      (Miri.Interpreter.RuntimePlace Provenance) :=
  let leaves := refDiscriminantLeavesV2 types
  let proj := refBasePlaceProjectionHooksV2 types
  {
    runtimeTarget := refRuntimeLayoutV2
    discriminantLayout := leaves.discriminantLayout
    tagLayout := leaves.tagLayout
    discriminantValue := leaves.discriminantValue
    variantForDiscriminant := leaves.variantForDiscriminant
    adtVariantCount := leaves.adtVariantCount
    projectRead :=
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooksV2 types)
    readImmediate := fun _ =>
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfigV2 types with ghostMode := true, deinitMovedPlace := false }
    destLayout := Miri.Interpreter.RuntimePlace.layout
    projectWrite := Miri.Interpreter.PlaceDynamic.field proj
    writeScalar := fun c sc dest =>
      Miri.Interpreter.writePlaceImmediate proj.place c (.scalar sc) dest
    toOp := Miri.Interpreter.placeToOp proj.place
    scalarMayBeNull := leaves.scalarMayBeNull
  }

/-- `ValidityMemory.Environment` for Profile v2. -/
noncomputable def refValidityMemoryEnvV2 (types : List MirTy) :
    Miri.Interpreter.ValidityMemory.Environment Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser)
      ProvenanceExtra RefMiriState :=
  let acc := refAccessConfigV2 types
  { refValidityMemoryEnv with
    context := {
      runtime := acc.runtime, ghostMode := true, globalKind := none
      globalHooks := acc.globalHooks
      accessHooks := Miri.Interpreter.PlaceMachine.accessHooks acc
      dynamicLayout := acc.dynamicLayout } }

/-- `ValidityVisitor.Hooks` bound to real `ValidityMemory.bind` for Profile v2.
-/
noncomputable def refValidityHooksV2 (types : List MirTy) :
    Miri.Interpreter.ValidityVisitor.Hooks Provenance RefMiriState Choice
      Miri.Interpreter.MachineHooks.FrameExtra
      (Miri.Interpreter.FnVal Unit) (FnAbi TyId)
      Miri.Interpreter.ValidityMemory.PaddingHandle :=
  let proj := refBasePlaceProjectionHooksV2 types
  let base :=
    { refValidityHooks types with
      target := refRuntimeLayoutV2, projection := proj
      discriminant := refValidityDiscriminantHooksV2 types
      classify := fun _ tyId st =>
        match resolveTy types tyId with
        | some .bool => .ok .boolean st
        | some (.int _ _) => .ok .integer st
        | some .char => .ok .character st
        | some .unit => .ok (.aggregate false false false) st
        | some .never => .ok .never st
        | some (.rawPtr _ pt) =>
          .ok (.rawPointer (tyIdFor types pt) (!refIsUnsizedTyV2 pt)) st
        | some (.ref .shared _) => .ok (.reference false) st
        | some (.ref .mut _) => .ok (.reference true) st
        | some (.slice elem) => .ok (.sequence (tyIdFor types elem)) st
        | some (.rangeTo (.int .isize false))
        | some (.rangeFrom (.int .isize false))
        | some (.tuple _) => .ok (.aggregate false false false) st
        | some ty =>
          match refAsEnumTy? ty with
          | some _ => .ok (.aggregate false false true) st
          | none => .error (.invalidProgram "unsupported validity type") st
        | none => .error (.invalidProgram "unsupported validity type") st
      unitLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .unit) st
      opsemInhabited := fun _ tyId st =>
        match resolveTy types tyId with
        | some ty => .ok (!(refLayoutDataForTyV2 ty).uninhabited) st
        | none => .error (.invalidProgram "unknown TyId in opsemInhabited") st
      isFreeze := fun _ _ st => .ok true st
      fieldPath := fun _ _ idx _ st => .ok (.tupleElem idx) st
      toOp := Miri.Interpreter.placeToOp proj.place
      sizeAndAlign := fun c mp st =>
        Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
          (refDynamicLayoutHooksV2 types) c 8 mp.mplace.metadata mp.layout st
      ptrToPlace := fun _ value st => refFromImmediatePtrV2 types value st
      metadataTail := fun _ tyId st =>
        match resolveTy types tyId with
        | some (.slice _) => .ok .sliceOrStr st
        | _ => .error (.invalidProgram "non-slice metadataTail") st
      checkPointerAccess := fun _ ptr sz st =>
        refCheckPointerAccessResultV2 types ptr sz st
      checkPointerAlign := fun _ ptr al st =>
        match refCheckPointerAlignResultV2 types ptr al st with
        | .error e st1 => .error e st1
        | .ok (.ok ()) st1 => .ok () st1
        | .ok (.error bad) st1 =>
          .error (.undefinedBehavior ("misaligned pointer: " ++ reprStr bad)) st1
      checkPointerAlignResult := fun _ ptr al st =>
        refCheckPointerAlignResultV2 types ptr al st
      scalarMayBeNull := fun _ sc st =>
        match refScalarMayBeNullV2 sc with
        | .ok b => .ok b st | .error e => .error e st
      retagPointer := fun _ _ _ st => .ok none st
      inMutableMemory := fun _ place st =>
        match place.ref with
        | .local _ _ _ _ => .ok true st
        | .memory mp =>
          match mp.ptr.provenance with
          | some (.concrete id _) =>
            match st.machine.memory.live.find? (fun e => e.1 == id) with
            | some (_, la) => .ok (la.allocation.mutability == .Mut) st
            | none => .ok false st
          | _ => .ok false st }
  Miri.Interpreter.ValidityMemory.bind base (refValidityMemoryEnvV2 types)
    (fun st => .ok false st) (fun _ _ st => .ok () st) (fun _ => true)

/-- `ExecutionScalar.Leaves` for Profile v2. -/
noncomputable def refScalarLeavesV2 (types : List MirTy) :
    Miri.Interpreter.ExecutionScalar.Leaves RefMiriState Choice := {
  classify := fun _ tyId st =>
    match resolveTy types tyId with
    | some .bool => .ok .boolean st
    | some (.int w s) => .ok (.integer (toMiriIntKind w s)) st
    | some .char => .ok .character st
    | some (.rawPtr _ _) | some (.ref _ _) => .ok .pointer st
    | _ => .error (.invalidProgram "non-scalar operand type") st
  boolLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .bool) st
  orderingLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .ordering) st
  overflowLayout := fun _ input st =>
    match resolveTy types input.ty with
    | some (.int w s) =>
      .ok (refLocalLayoutForTyV2 types (.tuple [.int w s, .bool])) st
    | _ => .error (.invalidProgram "overflow layout on non-integer type") st
  metadataLayout := fun _ tyId st =>
    match resolveTy types tyId with
    | some (.rawPtr _ (.slice _)) | some (.ref _ (.slice _)) =>
      .ok (refLocalLayoutForTyV2 types (.int .isize false)) st
    | some (.rawPtr _ _) | some (.ref _ _) =>
      .ok (refLocalLayoutForTyV2 types .unit) st
    | _ => .error (.invalidProgram "PtrMetadata on non-pointer type") st
  unitLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .unit) st
}

/-- Map `MemoryLifecycleError` into `StepError`. -/
noncomputable def refLifecycleErrToStepErr :
    MemoryLifecycleError → Miri.Interpreter.StepError
  | .useAfterFree _ => .undefinedBehavior "deallocating dead allocation"
  | .danglingPointer _ => .undefinedBehavior "deallocating dangling pointer"
  | .nonzeroAllocationOffset _ _ _ =>
    .undefinedBehavior "deallocating non-zero allocation offset"
  | .immutableAllocation _ =>
    .undefinedBehavior "deallocating immutable allocation"
  | .memoryKindMismatch _ => .undefinedBehavior "deallocation kind mismatch"
  | .layoutMismatch _ _ _ _ _ =>
    .undefinedBehavior "deallocation layout mismatch"
  | e => .invalidProgram ("lifecycle error: " ++ reprStr e)

/-- Real stack deallocation backed by `MemoryLifecycle.deallocatePtrWith`. -/
noncomputable def refDeallocateStackV2 (ptr : Pointer (Option Provenance))
    (st : RefMiriState) : RefMiriRes Unit :=
  let hooks : MemoryDeallocationHooks Provenance Miri.TreeBorrows.BorrowTree
      Unit Unit ProvenanceExtra := {
    synchronizeMemory := fun _ _ => ()
    resolvePointer := fun mem _ p sz =>
      match refResolvePointerPure p sz with
      | .ok r => ⟨mem, (), .ok (r.allocId, r.offset, r.extra)⟩
      | .error addr => ⟨mem, (), .error addr⟩
    beforeDeallocation := fun mem _ _ _ _ _ _ _ _ => ⟨mem, (), .ok ()⟩
  }
  let res := MemoryLifecycle.deallocatePtrWith
    st.machine.memory () ptr none .stack hooks
  let st1 := { st with machine := { st.machine with memory := res.memory } }
  match res.outcome with
  | .ok () => .ok () st1
  | .error e => .error (refLifecycleErrToStepErr e) st1

/-- `MachineHooks.StorageHooks` for Profile v2 with real stack deallocation. -/
noncomputable def refStorageHooksV2 (types : List MirTy) :
    Miri.Interpreter.MachineHooks.StorageHooks Unit RefUser := {
  veryTriviallySized := fun _ => .ok true
  layout := fun localId st =>
    match st.stack.currentFrame? with
    | none => .error (.stack .emptyStack) st
    | some frame =>
      match frame.body.locals[localId]? with
      | none => .error (.stack (.missingLocalType localId)) st
      | some tyId =>
        match refLayoutOfTyIdV2 types tyId with
        | .ok l => .ok l st | .error e => .error e st
  allocateDyn := fun _ _ st => .error (.unsupported "unsized local") st
  deallocateStack := refDeallocateStackV2
}

/-- `PlaceMachine.CompilerHooks` bound to `ValidityVisitor.validatePlace`. -/
noncomputable def refCompilerHooksV2 (types : List MirTy) :
    Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice :=
  (Miri.Interpreter.TypedMachineBindings.bindValidation
    (refBaseCompilerHooksV2 types) (refPlaceCopyHooksV2 types)
    (refValidityHooksV2 types) refRetagHooks refLimitsV2.retag
    refLimitsV2.validation (fun _ _ st => .ok true st)).1

/-- `PlaceProjectionHooks` for Profile v2 carrying validated `PlaceHooks`. -/
noncomputable def refPlaceProjectionHooksV2 (types : List MirTy) :
    Miri.Interpreter.PlaceProjectionHooks Provenance RefMiriState Choice
      Miri.Interpreter.MachineHooks.FrameExtra :=
  { refBasePlaceProjectionHooksV2 types with
    place := Miri.Interpreter.PlaceMachine.placeHooks
      (refAccessConfigV2 types) refAllocationConfig
      (refCompilerHooksV2 types) }

/-- `ExecutionCast.Leaves` for Profile v2 (`IntToInt`, `PtrToPtr`, and
`PointerWithExposedProvenance`). -/
noncomputable def refCastLeavesV2 (types : List MirTy) :
    Miri.Interpreter.ExecutionCast.Leaves RefMiriState Choice :=
  { refCastLeaves types with
    typeInfo := fun _ tyId st =>
      match resolveTy types tyId with
      | some (.int w s) => .ok (.integer (toMiriIntKind w s)) st
      | some .bool => .ok .boolean st
      | some .char => .ok .character st
      | some (.rawPtr _ pt) => .ok (.rawPointer (tyIdFor types pt)) st
      | some (.ref _ pt) => .ok (.reference (tyIdFor types pt)) st
      | some (.slice elem) => .ok (.slice (tyIdFor types elem)) st
      | _ => .error (.unsupported "cast type unsupported in Profile v2") st
    layoutOf := fun _ tyId st =>
      match refLayoutOfTyIdV2 types tyId with
      | .ok l => .ok l st | .error e => .error e st
    pointerFromExposedAddress := fun _ addr st =>
      .ok (Pointer.new none (Size.ofBytes addr)) st
    usizeLayout := fun _ st =>
      .ok (refLocalLayoutForTyV2 types (.int .isize false)) st
    builtinDeref := fun _ tyId _ st =>
      match resolveTy types tyId with
      | some (.rawPtr _ pt) | some (.ref _ pt) =>
        .ok (some (tyIdFor types pt)) st
      | _ => .ok none st
    fieldLayout := fun _ base idx st =>
      match refProjectFieldLayoutV2 types base idx with
      | .ok l => .ok l st | .error e => .error (refProjErrToStepErr e) st }

/-- Signed in-bounds pointer offset helper shared by `slice::get_unchecked`
and `ptr::add` (skips `checkPtrAccessSigned` at offset `0`, matching Miri). -/
noncomputable def refOffsetPtrSignedV2 (mem : RefMiriMem)
    (ptr : Pointer (Option Provenance)) (offset : Int64) :
    Except Miri.Interpreter.StepError (Miri.Memory.Scalar Provenance) :=
  let checkRes : Except AccessError Unit :=
    if offset == 0 then .ok ()
    else
      checkPtrAccessSigned refPointerArithmetic ptr offset
        .inboundsPointerArithmetic
        (fun _ _ => refResolvePointerPure ptr offset.toInt) mem.getAllocInfo
  match checkRes with
  | .error e => .error (.undefinedBehavior (toString e))
  | .ok () =>
    match ptr.wrappingSignedOffset offset refPointerArithmetic with
    | .error e => .error (.invalidProgram (reprStr e))
    | .ok ptr' =>
      match Miri.Memory.Scalar.fromMaybePointer refRuntimeLayoutV2.base ptr' with
      | .error e => .error (Miri.Interpreter.ScalarOps.scalarError e)
      | .ok sc => .ok sc

/-- Execute `core::slice::<impl [T]>::len` inside `ForeignItems.emulate`. -/
noncomputable def refExecSliceLenV2 (types : List MirTy)
    (args : Array (Miri.Interpreter.OpTy Provenance))
    (dest : Miri.Interpreter.RuntimePlace Provenance) (st : RefMiriState) :
    RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult :=
  match args[0]? with
  | none => .error (.unsupported "sliceLen arity mismatch") st
  | some arg0 =>
    if args.size != 1 then .error (.unsupported "sliceLen arity mismatch") st
    else
      match resolveTy types arg0.layout.ty, resolveTy types dest.layout.ty with
      | some (.ref reqMut (.slice (.int w s))), some (.int .isize false) =>
        match Miri.Interpreter.PlaceMachine.readImmediate
            (refAccessConfigV2 types) arg0 st with
        | .error e st1 => .error e st1
        | .ok imm0 st1 =>
          match imm0.imm.toScalarPair with
          | .error e => .error (Miri.Interpreter.ScalarOps.immediateError e) st1
          | .ok (ptrSc, lenSc) =>
            match miriScalarToPtrValV2 ptrSc,
                lenSc.toTargetUsize (Size.ofBytes 8) with
            | .ok pv, .ok len =>
              match refValidateRefInMiriV2 st1.machine.memory reqMut
                  (.slice (.int w s)) (.slicePtr pv len) with
              | .error .undefined => .error (.undefinedBehavior "sliceLen UB") st1
              | .error .unsupported => .error (.unsupported "sliceLen") st1
              | .ok () =>
                let resSc : Miri.Memory.Scalar Provenance :=
                  .fromScalarInt (miriScalar .isize (BitVec.ofNat 128 len.toNat))
                match Miri.Interpreter.writePlaceImmediate
                    (refPlaceProjectionHooksV2 types).place 0
                    (.scalar resSc) dest st1 with
                | .error e st2 => .error e st2
                | .ok () st2 => .ok .NeedsReturn st2
            | _, _ => .error (.unsupported "sliceLen decode failed") st1
      | _, _ => .error (.unsupported "sliceLen signature mismatch") st

/-- Execute `core::slice::get_unchecked` (`RangeTo`/`RangeFrom`). -/
noncomputable def refExecSliceGetUncheckedV2 (types : List MirTy)
    (isRangeTo : Bool) (args : Array (Miri.Interpreter.OpTy Provenance))
    (dest : Miri.Interpreter.RuntimePlace Provenance) (st : RefMiriState) :
    RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult :=
  match args[0]?, args[1]? with
  | some arg0, some arg1 =>
    let arg1Ok : Bool :=
      match resolveTy types arg1.layout.ty with
      | some (.rangeTo (.int .isize false)) => isRangeTo
      | some (.rangeFrom (.int .isize false)) => !isRangeTo
      | _ => false
    if args.size != 2 || !arg1Ok then
      .error (.unsupported "sliceGetUnchecked signature mismatch") st
    else
      match resolveTy types arg0.layout.ty, resolveTy types dest.layout.ty with
      | some (.ref inMut (.slice (.int .i8 false))),
        some (.ref outMut (.slice (.int .i8 false))) =>
        if Trusted.MirAst.Mutability.beq inMut .shared &&
            Trusted.MirAst.Mutability.beq outMut .mut then
          .error (.undefinedBehavior "sliceGetUnchecked shared-to-mut") st
        else
          let acc := refAccessConfigV2 types
          match Miri.Interpreter.PlaceMachine.readImmediate acc arg0 st with
          | .error e st1 => .error e st1
          | .ok imm0 st1 =>
            match Miri.Interpreter.PlaceMachine.readImmediate acc arg1 st1 with
            | .error e st2 => .error e st2
            | .ok imm1 st2 =>
              match imm0.imm.toScalarPair, imm1.imm.toScalar with
              | .ok (ptrSc, lenSc), .ok boundSc =>
                match ptrSc.toPointer refRuntimeLayoutV2.base,
                    lenSc.toTargetUsize (Size.ofBytes 8),
                    boundSc.toTargetUsize (Size.ofBytes 8) with
                | .ok ptr, .ok len, .ok bound =>
                  match refValidateRefInMiriV2 st2.machine.memory inMut
                      (.slice (.int .i8 false))
                      (.slicePtr (miriPtrToPtrValV2 ptr) len) with
                  | .error .undefined =>
                    .error (.undefinedBehavior "sliceGetUnchecked invalid") st2
                  | .error .unsupported =>
                    .error (.unsupported "sliceGetUnchecked unsupported") st2
                  | .ok () =>
                    let startOff := if isRangeTo then 0 else bound.toNat
                    let endOff := if isRangeTo then bound.toNat else len.toNat
                    if !Nat.ble startOff endOff || !Nat.ble endOff len.toNat then
                      .error (.undefinedBehavior "slice::get_unchecked OOB") st2
                    else
                      let offI64 := Int64.ofInt (Int.ofNat startOff)
                      match refOffsetPtrSignedV2 st2.machine.memory ptr offI64 with
                      | .error e => .error e st2
                      | .ok ptrSc' =>
                        let lenSc' : Miri.Memory.Scalar Provenance :=
                          .fromScalarInt (miriScalar .isize
                            (BitVec.ofNat 128 (endOff - startOff)))
                        match Miri.Interpreter.writePlaceImmediate
                            (refPlaceProjectionHooksV2 types).place 0
                            (.scalarPair ptrSc' lenSc') dest st2 with
                        | .error e st3 => .error e st3
                        | .ok () st3 => .ok .NeedsReturn st3
                | _, _, _ => .error (.unsupported "sliceGetUnchecked decode") st2
              | _, _ => .error (.unsupported "sliceGetUnchecked imm") st2
      | _, _ => .error (.unsupported "sliceGetUnchecked signature mismatch") st
  | _, _ => .error (.unsupported "sliceGetUnchecked arity mismatch") st

/-- Execute `core::ptr::{const,mut}_ptr::add` inside `ForeignItems.emulate`. -/
noncomputable def refExecPtrAddV2 (types : List MirTy) (abi : FnAbi TyId)
    (args : Array (Miri.Interpreter.OpTy Provenance))
    (dest : Miri.Interpreter.RuntimePlace Provenance) (st : RefMiriState) :
    RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult :=
  match args[0]?, args[1]? with
  | some arg0, some arg1 =>
    let expectedTy := abi.ret.layout.ty
    if args.size != 2 || arg0.layout.ty != expectedTy ||
        dest.layout.ty != expectedTy then
      .error (.unsupported "ptrAdd signature mismatch") st
    else
      match resolveTy types expectedTy, resolveTy types arg1.layout.ty with
      | some (.rawPtr _ pointee), some (.int .isize false) =>
        if refIsUnsizedTyV2 pointee || !refIsSupportedPointeeTyV2 pointee ||
            !refTyLayoutFitsU64V2 pointee then
          .error (.unsupported "ptrAdd unsupported pointee") st
        else
          let acc := refAccessConfigV2 types
          match Miri.Interpreter.PlaceMachine.readImmediate acc arg0 st with
          | .error e st1 => .error e st1
          | .ok imm0 st1 =>
            match Miri.Interpreter.PlaceMachine.readImmediate acc arg1 st1 with
            | .error e st2 => .error e st2
            | .ok imm1 st2 =>
              let ptLd := refLayoutDataForTyV2 pointee
              let strideRes := Miri.Memory.Scalar.fromUInt
                (BitVec.ofNat 128 ptLd.size.bytes.toNat) imm1.layout.layout.size
              match imm0.imm.toScalar, strideRes with
              | .ok ptrSc, .ok strideSc =>
                match ptrSc.toPointer refRuntimeLayoutV2.base with
                | .error e =>
                  .error (Miri.Interpreter.ScalarOps.scalarError e) st2
                | .ok ptr =>
                  match Miri.Interpreter.ExecutionScalar.integerBinary
                      (refScalarLeavesV2 types) 0 .MulWithOverflow
                      imm1 ⟨.scalar strideSc, imm1.layout⟩ st2 with
                  | .error e st3 => .error e st3
                  | .ok mult st3 =>
                    match mult.imm.toScalarPair with
                    | .error e =>
                      .error (Miri.Interpreter.ScalarOps.immediateError e) st3
                    | .ok (deltaSc, ovSc) =>
                      match ovSc.toBool,
                          deltaSc.toTargetIsize
                            refPointerArithmetic.pointerSize with
                      | .ok true, _ =>
                        .error (.undefinedBehavior "PointerArithOverflow") st3
                      | .ok false, .ok offset =>
                        if offset.toInt < 0 then
                          .error (.undefinedBehavior "PointerArithOverflow") st3
                        else
                          match refOffsetPtrSignedV2 st3.machine.memory
                              ptr offset with
                          | .error e => .error e st3
                          | .ok resSc =>
                            match Miri.Interpreter.writePlaceImmediate
                                (refPlaceProjectionHooksV2 types).place 0
                                (.scalar resSc) dest st3 with
                            | .error e st4 => .error e st4
                            | .ok () st4 => .ok .NeedsReturn st4
                      | _, _ => .error (.unsupported "ptrAdd mul decode") st3
              | _, _ => .error (.unsupported "ptrAdd scalar decode") st2
      | _, _ => .error (.unsupported "ptrAdd signature mismatch") st
  | _, _ => .error (.unsupported "ptrAdd arity mismatch") st

/-- Execute `usize::unchecked_sub` inside `ForeignItems.emulate`. -/
noncomputable def refExecUsizeUncheckedSubV2 (types : List MirTy)
    (args : Array (Miri.Interpreter.OpTy Provenance))
    (dest : Miri.Interpreter.RuntimePlace Provenance) (st : RefMiriState) :
    RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult :=
  match args[0]?, args[1]? with
  | some arg0, some arg1 =>
    if args.size != 2 then
      .error (.unsupported "usizeUncheckedSub arity mismatch") st
    else
      match resolveTy types arg0.layout.ty, resolveTy types arg1.layout.ty,
          resolveTy types dest.layout.ty with
      | some (.int .isize false), some (.int .isize false),
        some (.int .isize false) =>
        let acc := refAccessConfigV2 types
        match Miri.Interpreter.PlaceMachine.readImmediate acc arg0 st with
        | .error e st1 => .error e st1
        | .ok imm0 st1 =>
          match Miri.Interpreter.PlaceMachine.readImmediate acc arg1 st1 with
          | .error e st2 => .error e st2
          | .ok imm1 st2 =>
            match Miri.Interpreter.ExecutionScalar.integerBinary
                (refScalarLeavesV2 types) 0 .SubWithOverflow
                imm0 imm1 st2 with
            | .error e st3 => .error e st3
            | .ok subRes st3 =>
              match subRes.imm.toScalarPair with
              | .ok (diffSc, ovSc) =>
                match ovSc.toBool with
                | .ok true =>
                  .error (.undefinedBehavior "usize::unchecked_sub underflow") st3
                | .ok false =>
                  match Miri.Interpreter.writePlaceImmediate
                      (refPlaceProjectionHooksV2 types).place 0
                      (.scalar diffSc) dest st3 with
                  | .error e st4 => .error e st4
                  | .ok () st4 => .ok .NeedsReturn st4
                | .error e =>
                  .error (Miri.Interpreter.ScalarOps.scalarError e) st3
              | .error e =>
                .error (Miri.Interpreter.ScalarOps.immediateError e) st3
      | _, _, _ => .error (.unsupported "usizeUncheckedSub signature") st
  | _, _ => .error (.unsupported "usizeUncheckedSub arity mismatch") st

/-- Dispatch synthetic Profile v2 `CoreCallOp` foreign symbols. -/
noncomputable def refExecCoreCallForeignV2 (types : List MirTy)
    (name : String) (abi : FnAbi TyId)
    (args : Array (Miri.Interpreter.OpTy Provenance))
    (dest : Miri.Interpreter.RuntimePlace Provenance) (st : RefMiriState) :
    RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult :=
  if name == "__anneal_core_slice_len" then
    refExecSliceLenV2 types args dest st
  else if name == "__anneal_core_slice_get_unchecked_range_to" then
    refExecSliceGetUncheckedV2 types true args dest st
  else if name == "__anneal_core_slice_get_unchecked_range_from" then
    refExecSliceGetUncheckedV2 types false args dest st
  else if name == "__anneal_core_ptr_add" then
    refExecPtrAddV2 types abi args dest st
  else if name == "__anneal_core_usize_unchecked_sub" then
    refExecUsizeUncheckedSubV2 types args dest st
  else .ok .NotSupported st

/-- `ForeignItems.Hooks` for Profile v2 `CoreCallOp` dispatch. -/
noncomputable def refForeignHooksV2 (types : List MirTy) :
    Miri.Interpreter.ForeignItems.Hooks Provenance RefMiriState
      (Miri.Interpreter.RuntimePlace Provenance)
      (Miri.Interpreter.RuntimePlace Provenance)
      (Pointer (Option Provenance))
      Miri.Interpreter.LoadedBody Miri.Interpreter.CallInstance := {
  family := .other, os := "none", arch := "x86_64"
  maximumSize := refMaxSizeOfVal.bytes
  noAllocShimSymbol := "__anneal_no_alloc_shim"
  allocatorSymbol := fun _ st => .ok none st
  lookupFunction := fun _ st => .ok none st
  forceAllocation := fun d st => .ok d st
  returnToBlock := fun target st =>
    let (st', res) := Miri.Interpreter.ControlFlow.returnToBlock target st
    match res with | .ok () => .ok () st' | .error e => .error e st'
  unwindToBlock := fun _ st => .error (.unsupported "unwind") st
  nativeEnabled := false, callNative := fun _ _ _ st => .ok false st
  expectedAbi := fun _ st => .error (.unsupported "expectedAbi") st
  argumentCompat := fun _ _ st => .ok true st
  checkSymbolClash := fun _ st => .ok () st
  transmute := fun op _ st => .ok op st
  readUsize := fun _ st => .error (.unsupported "unused") st
  readPointer := fun _ st => .error (.unsupported "unused") st
  readI32 := fun _ st => .error (.unsupported "unused") st
  isNull := fun _ st => .error (.unsupported "unused") st
  allocate := fun _ _ _ _ st => .error (.unsupported "unused") st
  deallocate := fun _ _ _ st => .error (.unsupported "unused") st
  reallocate := fun _ _ _ _ _ st => .error (.unsupported "unused") st
  writePointer := fun _ _ st => .error (.unsupported "unused") st
  writeNull := fun _ st => .error (.unsupported "unused") st
  setEnomem := fun st => .ok () st
  startExit := fun _ st => .error (.unsupported "unused") st
  specialDestination := fun d st => .ok d st
  math := refExecCoreCallForeignV2 types
  unix := fun _ _ _ _ st => .ok .NotSupported st
  windows := fun _ _ _ _ st => .ok .NotSupported st
  otherPortable := fun _ _ _ _ st => .ok none st
}

/-- Build the `FnAbi TyId` for a synthetic `CoreCallOp` `CallInstance`. -/
noncomputable def refFnAbiOfCoreCallV2 (types : List MirTy)
    (inst : Miri.Interpreter.CallInstance) :
    Except Miri.Interpreter.StepError (FnAbi TyId) :=
  match refCoreCallOfDefId types inst.defId with
  | none => .error (.unsupported "unknown coreCall instance")
  | some op =>
    let mkArg (ty : MirTy) : ArgAbi TyId :=
      ⟨refLocalLayoutForTyV2 types ty, .Direct ArgAttributes.new⟩
    match op with
    | .sliceLen =>
      .ok ⟨Array.mk [mkArg (.ref .shared (.slice (.int .i8 false)))],
        mkArg (.int .isize false), false, 1, .Rust, false⟩
    | .sliceGetUncheckedRangeTo =>
      .ok ⟨Array.mk
          [mkArg (.ref .shared (.slice (.int .i8 false))),
           mkArg (.rangeTo (.int .isize false))],
        mkArg (.ref .shared (.slice (.int .i8 false))), false, 2, .Rust, false⟩
    | .sliceGetUncheckedRangeFrom =>
      .ok ⟨Array.mk
          [mkArg (.ref .shared (.slice (.int .i8 false))),
           mkArg (.rangeFrom (.int .isize false))],
        mkArg (.ref .shared (.slice (.int .i8 false))), false, 2, .Rust, false⟩
    | .usizeUncheckedSub =>
      .ok ⟨Array.mk [mkArg (.int .isize false), mkArg (.int .isize false)],
        mkArg (.int .isize false), false, 2, .Rust, false⟩
    | .ptrAdd reqMut pointee =>
      if !refTyLayoutFitsU64V2 pointee then
        .error (.unsupported "ptrAdd pointee layout exceeds UInt64")
      else
        .ok ⟨Array.mk
            [mkArg (.rawPtr reqMut pointee), mkArg (.int .isize false)],
          mkArg (.rawPtr reqMut pointee), false, 2, .Rust, false⟩
    | _ =>
      .error (.unsupported "coreCall unsupported in Profile v2")

/-- Map a synthetic `CoreCallOp` `CallInstance` to its dispatch symbol name. -/
noncomputable def refCoreCallSymbolNameV2 (types : List MirTy)
    (inst : Miri.Interpreter.CallInstance) : String :=
  match refCoreCallOfDefId types inst.defId with
  | some .sliceLen => "__anneal_core_slice_len"
  | some .sliceGetUncheckedRangeTo =>
    "__anneal_core_slice_get_unchecked_range_to"
  | some .sliceGetUncheckedRangeFrom =>
    "__anneal_core_slice_get_unchecked_range_from"
  | some .usizeUncheckedSub => "__anneal_core_usize_unchecked_sub"
  | some (.ptrAdd _ _) => "__anneal_core_ptr_add"
  | _ => ""

/-- Panic lang-item handler for Profile v2: reuses `refPanicLangItem rp` for
UB pointer-dereference panics and non-optional safe panics (yielding
`.termination (.abort "panic abort")` when `rp.hasLocalPanicHandler = false`,
`rp.panicStrategy = .abort`, and the `Assert` terminator has a non-cleanup
unwind action), and additionally admits optional overflow panics iff
`rp.overflowChecks = true`. All other panic lang items remain `.unsupported`.
-/
noncomputable def refPanicLangItemV2 (rp : RefProg) (c : Choice)
    (item : Miri.Interpreter.Panic.LangItem) (st : RefMiriState) :
    RefMiriRes (Option Miri.MIR.DefId) :=
  match item with
  | .PanicAddOverflow | .PanicSubOverflow | .PanicMulOverflow
  | .PanicNegOverflow | .PanicShrOverflow | .PanicShlOverflow =>
    if rp.overflowChecks then
      refPanicLangItem rp c .PanicDivZero st
    else
      .error (.unsupported "optional overflow check unsupported") st
  | _ => refPanicLangItem rp c item st

/-- Canonical `Miri.Interpreter.ExecutionMachine.Config` for Profile v2. -/
noncomputable def refExecutionConfigV2 (rp : RefProg) :
    Miri.Interpreter.ExecutionMachine.Config Unit RefUser Choice Unit Unit
      Unit :=
  let types := rp.types
  let baseCfg := refExecutionConfig rp
  { baseCfg with
    access := refAccessConfigV2 types
    compiler := refCompilerHooksV2 types
    projection := refPlaceProjectionHooksV2 types
    operands := refOperandLeavesV2 types
    copy := refPlaceCopyHooksV2 types
    validity := refValidityHooksV2 types
    validationRecursive := fun _ _ st => .ok true st
    lifecycle := { refLifecycle types with storage := refStorageHooksV2 types }
    calls := {
      baseCfg.calls with
      compiler := {
        baseCfg.calls.compiler with
        functionSignature := fun _ layout st =>
          if Nat.ble (refCoreCallTyBase types) layout.ty then
            match refCoreCallOfDefId types (layout.ty - refCoreCallTyBase types) with
            | some .sliceLen => .ok (1, ()) st
            | some .sliceGetUncheckedRangeTo
            | some .sliceGetUncheckedRangeFrom
            | some .usizeUncheckedSub
            | some (.ptrAdd _ _) => .ok (2, ()) st
            | _ => .error (.unsupported "unknown coreCall signature") st
          else .error (.unsupported "non-coreCall call unsupported") st
        functionKind := fun tyId st =>
          if Nat.ble (refCoreCallTyBase types) tyId then
            let defId := tyId - refCoreCallTyBase types
            match refCoreCallOfDefId types defId with
            | some _ => .ok (.FnDef defId Array.empty) st
            | none => .error (.unsupported "unknown coreCall kind") st
          else .error (.unsupported "non-coreCall call unsupported") st
        resolve := fun _ defId args st =>
          match refCoreCallOfDefId types defId with
          | some _ => .ok ⟨.Item defId, args⟩ st
          | none => .error (.unsupported "unknown coreCall resolve") st
        fnAbiOfInstance := fun _ inst _ st =>
          match refFnAbiOfCoreCallV2 types inst with
          | .ok abi => .ok abi st | .error e => .error e st
        checkArgumentCompat := fun _ _ _ st => .ok true st
      }
      dispatch := {
        baseCfg.calls.dispatch with
        foreign := some (fun st => .ok (refForeignHooksV2 types) st)
        returnToBlock := fun target st =>
          let (st', res) := Miri.Interpreter.ControlFlow.returnToBlock target st
          match res with | .ok () => .ok () st' | .error e => .error e st'
        isForeignItem := fun inst st =>
          .ok (refCoreCallOfDefId types inst.defId).isSome st
        symbolName := fun inst st =>
          .ok (refCoreCallSymbolNameV2 types inst) st
      }
    }
    virtual := { baseCfg.virtual with alignment := refAlignCtxV2 }
    helpers := { baseCfg.helpers with
      unitLayout := refLocalLayoutForTyV2 types .unit }
    panic := {
      baseCfg.panic with
      driver := {
        baseCfg.panic.driver with
        readImmediate := fun _ op st =>
          Miri.Interpreter.PlaceMachine.readImmediate (refAccessConfigV2 types)
            op st
      }
      langItem := refPanicLangItemV2 rp
      evalOperand := fun _ op st =>
        match op with
        | .Constant c => refEvalConstOperandV2 types c st
        | _ => .error (.unsupported "non-const panic assert operand") st
    }
    discriminant := refDiscriminantLeavesV2 types
    scalar := refScalarLeavesV2 types
    floats := { refFloatOpsHooks types with
      boolLayout := fun _ st => .ok (refLocalLayoutForTyV2 types .bool) st }
    casts := refCastLeavesV2 types
    isRawPointer := fun _ tyId st =>
      match resolveTy types tyId with
      | some (.rawPtr _ _) => .ok true st | _ => .ok false st
    usizeLayout := fun _ st =>
      .ok (refLocalLayoutForTyV2 types (.int .isize false)) st
    pointeeLayout := fun _ tyId st =>
      match resolveTy types tyId with
      | some (.rawPtr _ pt) | some (.ref _ pt) =>
        match refCheckedLocalLayoutForTyV2 types pt with
        | some lay => .ok lay st
        | none => .error (.unsupported "pointee layout exceeds UInt64") st
      | _ => .error (.invalidProgram "pointeeLayout on non-pointer type") st
    deinitMovedPlace := true }

/-! ## Section 7: Entry Initialization, Single-Step Evaluator, and Predicates -/

/-- Initialize Profile v2 local states (pre-populating natural-aligned
`LocalLayout` and allocating stack storage for non-immediate tuple arguments).
-/
noncomputable def initRefLocalsLoopV2 (types : List MirTy) (rbody : RefBody)
    (args : List Val) (mem : RefMiriMem) :
    Nat → List MirTy → Except FaultKind (List RefLocalState × RefMiriMem)
  | _, [] => .ok ([], mem)
  | idx, ty :: rest =>
    if !refTyLayoutFitsU64V2 ty then .error .unsupported
    else
      let lay := refLocalLayoutForTyV2 types ty
      if Nat.beq idx 0 then
        match initRefLocalsLoopV2 types rbody args mem (idx + 1) rest with
        | .error k => .error k
        | .ok (ls, mem') => .ok (⟨.live (.immediate .uninit), some lay⟩ :: ls, mem')
      else if Nat.ble idx rbody.argumentCount then
        match Trusted.MirSemantics.getElem? args (idx - 1) with
        | none => .error .unsupported
        | some v =>
          if refTyIsImmediateV2 ty then
            let stA : RefLocalState :=
              ⟨.live (.immediate (valToMiriImmediateV2 ty v)), some lay⟩
            match initRefLocalsLoopV2 types rbody args mem (idx + 1) rest with
            | .error k => .error k | .ok (ls, mem') => .ok (stA :: ls, mem')
          else
            let sz := lay.layout.size
            let al := lay.layout.align.abi
            match Miri.Memory.Allocation.tryNew (Prov := Provenance) sz al .Uninit
                (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
            | .error _ => .error .unsupported
            | .ok blank =>
              match refWriteValToAllocV2 blank 0 ty v with
              | .error k => .error k
              | .ok filled =>
                let (mem1, reserved) := mem.reserveAllocId
                match reserved with
                | .error _ => .error .unsupported
                | .ok aid =>
                  let tree := Miri.TreeBorrows.BorrowTree.new BorTag.one sz
                  let mem2 := { mem1 with
                    live := mem1.live.push (aid, ⟨.stack, filled.withExtra tree⟩) }
                  let mp : Miri.Interpreter.MemPlace Provenance :=
                    ⟨⟨Size.ZERO, some (.concrete aid BorTag.one)⟩, .none, none⟩
                  let stA : RefLocalState := ⟨.live (.indirect mp), some lay⟩
                  match initRefLocalsLoopV2 types rbody args mem2 (idx + 1) rest with
                  | .error k => .error k | .ok (ls, mem') => .ok (stA :: ls, mem')
      else if refHasStorageAnnotation rbody idx then
        match initRefLocalsLoopV2 types rbody args mem (idx + 1) rest with
        | .error k => .error k
        | .ok (ls, mem') => .ok (⟨.dead, some lay⟩ :: ls, mem')
      else
        match initRefLocalsLoopV2 types rbody args mem (idx + 1) rest with
        | .error k => .error k
        | .ok (ls, mem') => .ok (⟨.live (.immediate .uninit), some lay⟩ :: ls, mem')

/-- Construct a real Profile v2 `Miri.Interpreter.Frame` with root cleanup
enabled (`returnContinuation := .stop true`). -/
noncomputable def mkRefMiriFrameV2 (types : List MirTy) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (locals : List RefLocalState)
    (retPlace : Miri.Interpreter.MPlaceTy Provenance) :
    Miri.Interpreter.Frame Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra :=
  { mkRefMiriFrame types defId rbody blockIdx stmtIdx locals retPlace with
    body := toMiriBodyV2 types rbody
    returnContinuation := .stop true }

/-- Profile v2 reference entry initialization (`initRefStateV2 rp q maxSteps`).
-/
noncomputable def initRefStateV2 (rp : RefProg) (q : Query)
    (maxSteps : Nat) : Except FaultKind RefState :=
  if !Nat.beq rp.pointerWidthBits 64 || !Nat.beq rp.mirProfileVersion 2 then
    .error .unsupported
  else if !refValidCallerMemoryV2 q.callerMem then
    .error .unsupported
  else
    match Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId with
    | none => .error .unsupported
    | some rbody =>
      match decodeLocalTys rp.types rbody.locals with
      | none => .error .unsupported
      | some localTys =>
        if rbody.basicBlocks.isEmpty ||
            !Nat.blt rbody.argumentCount localTys.length ||
            !refStorageAnnotationsInBounds rbody ||
            !refDiscriminantTypesValid localTys rbody ||
            !refCastTypesValid rp.types localTys rbody ||
            !localTys.all refIsSupportedLocalTyV2 ||
            !localTys.all refTyLayoutFitsU64V2 then
          .error .unsupported
        else
          let paramTys := (localTys.drop 1).take rbody.argumentCount
          if !checkRefArgsMatchV2 q.args paramTys ||
              !refValListAllocIdsFitU64V2 q.args then .error .unsupported
          else
            match Trusted.MirSemantics.getElem? localTys 0 with
            | none => .error .unsupported
            | some retTy =>
              match refInitCallerMemoryV2 rp.types q.callerMem retTy
                  (fun memCaller =>
                    refRefsValidInMiriListV2 memCaller paramTys q.args &&
                      refSpansPairwiseDisjointV2
                        (refAccessSpansListV2 paramTys q.args))
                  (refMaxValListAllocIdV2 q.args)
                  (refValListHasAllocIdV2 1 q.args) with
              | .error k => .error k
              | .ok (mem0, retPlace) =>
                match initRefLocalsLoopV2 rp.types rbody q.args mem0 0
                    localTys with
                | .error k => .error k
                | .ok (rlocals, mem1) =>
                    let frame := mkRefMiriFrameV2 rp.types rp.entryDefId rbody
                      0 0 rlocals retPlace
                    .ok {
                      miri := mkRefMiriState frame mem1 refInitControl q.callerMem
                      retTy := retTy, retPlace := retPlace
                      stepsExecuted := 0, maxSteps := maxSteps }

/-- Single-step Profile v2 reference evaluator driving
`Miri.Interpreter.ExecutionMachine.step` on `refExecutionConfigV2 rp`. -/
noncomputable def evalRefStepV2 (rp : RefProg) (c : Choice)
    (rs : RefState) : RefOutcome :=
  if !Nat.blt rs.stepsExecuted rs.maxSteps then .exhaustedStepLimit
  else
    match Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfigV2 rp) refLimitsV2 c rs.miri with
    | (miri', .ok true) =>
      if miri'.stack.frames.isEmpty then
        let origCm := miri'.machine.user.callerMem
        match refReadReturnValV2 miri'.machine.memory origCm rs.retTy
            rs.retPlace with
        | .ok retVal =>
          .returned (.returned ⟨retVal,
            refExtractCallerMemoryV2 origCm miri'.machine.memory⟩)
        | .error k => faultToRefOutcome k
      else
        .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }
    | (_, .ok false) => .blocked
    | (miri', .error (.termination (.abort _))) =>
      .returned (.aborted
        (refExtractCallerMemoryV2 miri'.machine.user.callerMem
          miri'.machine.memory))
    | (_, .error (.undefinedBehavior _)) => .ub
    | (_, .error (.stack (.localExpectedLive _))) => .ub
    | (_, .error _) => .blocked

/-- Profile v2 reference single-step relation directly instantiating
`Miri.Interpreter.ExecutionMachine.AllowedStep`. -/
def RefAllowedStepV2 (rp : RefProg) (before after : RefMiriState)
    (outcome : Except Miri.Interpreter.StepError Bool) : Prop :=
  Miri.Interpreter.ExecutionMachine.AllowedStep
    (refExecutionConfigV2 rp) (fun _ c => c = 0) before after outcome

/-- Every concrete `ExecutionMachine.step` call performed by `evalRefStepV2`
under `ValidRefChoice` witnesses `RefAllowedStepV2`. -/
theorem refStepV2_sound_for_allowedStepV2 (rp : RefProg) (c : Choice)
    (rs : RefState) (h_c : ValidRefChoice rp rs c) :
    let res := Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 c rs.miri
    RefAllowedStepV2 rp rs.miri res.1 res.2 :=
  ⟨refLimitsV2, c, h_c, rfl⟩

/-- Relational small-step transition of $M_{\text{ref}}^{\text{v2}}$. -/
def RefStepV2 (rp : RefProg) (rs : RefState) (out : RefOutcome) : Prop :=
  ∃ c : Choice, ValidRefChoice rp rs c ∧ evalRefStepV2 rp c rs = out

/-- Unbounded finite-step reachability in $M_{\text{ref}}^{\text{v2}}$. -/
inductive RefReachesV2 (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReachesV2 rp rs rs
  | tail {rs₁ rs₂ rs₃ : RefState} :
      RefReachesV2 rp rs₁ rs₂ →
      RefStepV2 rp rs₂ (.running rs₃) →
      RefReachesV2 rp rs₁ rs₃

/-- Outcome `out` is reached in $M_{\text{ref}}^{\text{v2}}$ from `(rp, q)`
under step budget `maxSteps`. -/
def RefReachesOutcomeV2 (rp : RefProg) (q : Query)
    (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefStateV2 rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReachesV2 rp rs₀ rs ∧ RefStepV2 rp rs out

/-- All-prefix well-formedness in $M_{\text{ref}}^{\text{v2}}$. -/
def RefWellFormedV2 (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefStateV2 rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReachesV2 rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcomeV2 rp q maxSteps .ub ∧
    ¬ RefReachesOutcomeV2 rp q maxSteps .blocked

/-- Observable terminal behavior (value + post-state `CallerMemory`) in
$M_{\text{ref}}^{\text{v2}}$. -/
def RefBehaviorV2 (rp : RefProg) (q : Query) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcomeV2 rp q maxSteps (.returned out)

/-- Divergence in $M_{\text{ref}}^{\text{v2}}$. -/
def RefDivergesV2 (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState,
    initRefStateV2 rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStepV2 rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })

/-! ## Section 8: Choice-Coupled Profile v2 Reference Predicates -/

/-- Choice-coupled finite-step reachability in $M_{\text{ref}}^{\text{v2}}$. -/
inductive RefReachesAtChoicesV2 (rp : RefProg) :
    RefState → List Choice → RefState → Prop where
  | nil (rs : RefState) : RefReachesAtChoicesV2 rp rs [] rs
  | cons {rs₁ rs₂ rs₃ : RefState} {c : Choice} {cs : List Choice} :
      ValidRefChoice rp rs₁ c →
      evalRefStepV2 rp c rs₁ = .running rs₂ →
      RefReachesAtChoicesV2 rp rs₂ cs rs₃ →
      RefReachesAtChoicesV2 rp rs₁ (c :: cs) rs₃

/-- Choice-coupled finite prefix admissibility in
$M_{\text{ref}}^{\text{v2}}$. -/
def RefValidPrefixAtChoicesV2 (rp : RefProg) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ maxSteps : Nat, ∃ rs₀ rs : RefState,
    initRefStateV2 rp q maxSteps = .ok rs₀ ∧
    RefReachesAtChoicesV2 rp rs₀ choices rs

/-- Choice-coupled outcome reachability in $M_{\text{ref}}^{\text{v2}}$. -/
def RefReachesOutcomeAtChoicesV2 (rp : RefProg) (q : Query)
    (choices : List Choice) (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefStateV2 rp q maxSteps with
  | .error k => choices = [] ∧ out = faultToRefOutcome k
  | .ok rs₀ =>
    ∃ (prefixChoices : List Choice) (c : Choice) (rs : RefState),
      choices = prefixChoices ++ [c] ∧
      RefReachesAtChoicesV2 rp rs₀ prefixChoices rs ∧
      ValidRefChoice rp rs c ∧
      evalRefStepV2 rp c rs = out

/-- Choice-coupled observable terminal behavior in
$M_{\text{ref}}^{\text{v2}}$. -/
def RefBehaviorAtChoicesV2 (rp : RefProg) (q : Query)
    (choices : List Choice) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat,
    RefReachesOutcomeAtChoicesV2 rp q choices maxSteps (.returned out)

/-- Choice-coupled divergence in $M_{\text{ref}}^{\text{v2}}$. -/
def RefDivergesAtChoicesV2 (rp : RefProg) (q : Query)
    (choiceStream : Nat → Choice) : Prop :=
  ∃ rs₀ : RefState,
    initRefStateV2 rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        ValidRefChoice rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (choiceStream n) ∧
        evalRefStepV2 rp (choiceStream n)
          { trace n with stepsExecuted := n, maxSteps := n + 1 } =
          .running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 }

private theorem list_find?_append_one_some {α : Type} {p : α → Bool}
    {xs : List α} {x y : α} (h : xs.find? p = some y) :
    (xs ++ [x]).find? p = some y := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    dsimp only [List.cons_append, List.find?]
    dsimp only [List.find?] at h
    cases h_pa : p a with
    | true => rw [h_pa] at h; exact h
    | false => rw [h_pa] at h; exact ih h

private theorem list_find?_append_one_ne {α : Type} {p : α → Bool}
    (xs : List α) {x : α} (h_px : p x = false) :
    (xs ++ [x]).find? p = xs.find? p := by
  induction xs with
  | nil => dsimp only [List.nil_append, List.find?]; rw [h_px]
  | cons a rest ih =>
    dsimp only [List.cons_append, List.find?]
    cases p a with
    | true => rfl
    | false => exact ih

/-- Injectivity helper: when `refExactAllocIdV2 aid = some mid`,
`mid.value.toNat = aid`. -/
theorem refExactAllocIdV2_toNat {aid : Trusted.MirAst.AllocId}
    {mid : Miri.Memory.AllocId} (h_mid : refExactAllocIdV2 aid = some mid) :
    mid.value.toNat = aid := by
  dsimp only [refExactAllocIdV2] at h_mid
  cases h_fits : refAllocIdFitsU64V2 aid with
  | false =>
    simp only [h_fits, Bool.false_eq_true, ite_false] at h_mid
    cases h_mid
  | true =>
    simp only [h_fits, ite_true] at h_mid
    dsimp only [refAllocIdFitsU64V2] at h_fits
    cases h_nz : !Nat.beq aid 0 with
    | false => rw [h_nz] at h_fits; cases h_fits
    | true =>
      cases h_u : Nat.beq (UInt64.ofNat aid).toNat aid with
      | false => rw [h_nz, h_u] at h_fits; cases h_fits
      | true =>
        have h_val := Miri.Memory.AllocId.constructed_value h_mid
        rw [h_val]
        exact Nat.eq_of_beq_eq_true h_u

private theorem refByteProvHasIdV2_false_of_gt (id : Trusted.MirAst.AllocId) :
    ∀ (bs : List Trusted.MirSemantics.AllocByte),
      refMaxByteProvAllocIdV2 bs < id → refByteProvHasIdV2 id bs = false
  | [], _ => rfl
  | .uninit :: rest, h_lt => refByteProvHasIdV2_false_of_gt id rest h_lt
  | .init _ none :: rest, h_lt => refByteProvHasIdV2_false_of_gt id rest h_lt
  | .init _ (some aid) :: rest, h_lt => by
    dsimp only [refMaxByteProvAllocIdV2] at h_lt
    have h_a : aid < id := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h_lt
    have h_r : refMaxByteProvAllocIdV2 rest < id :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h_lt
    have h_neq : Nat.beq aid id = false := by
      cases h_b : Nat.beq aid id with
      | false => rfl
      | true =>
        exact False.elim (Nat.ne_of_lt h_a (Nat.eq_of_beq_eq_true h_b))
    dsimp only [refByteProvHasIdV2]
    rw [h_neq, refByteProvHasIdV2_false_of_gt id rest h_r]
    rfl

mutual
  /-- If every provenance id inside `v` is strictly below `id`, then
  `refValHasAllocIdV2 id v = false`. -/
  theorem refValHasAllocIdV2_false_of_gt (id : Trusted.MirAst.AllocId) :
      ∀ (v : Trusted.MirSemantics.Val), refMaxValAllocIdV2 v < id →
        refValHasAllocIdV2 id v = false
    | .ptr p, h_lt | .slicePtr p _, h_lt
    | .vec p _ _, h_lt | .boxPtr p _, h_lt => by
      dsimp only [refMaxValAllocIdV2] at h_lt
      dsimp only [refValHasAllocIdV2]
      cases h_aid : p.allocId with
      | none => rfl
      | some aid =>
        rw [h_aid] at h_lt
        cases h_b : Nat.beq aid id with
        | false => dsimp only; exact h_b
        | true =>
          exact False.elim (Nat.ne_of_lt h_lt (Nat.eq_of_beq_eq_true h_b))
    | .tuple vs, h_lt => refValListHasAllocIdV2_false_of_gt id vs h_lt
    | .array vs, h_lt => refValListHasAllocIdV2_false_of_gt id vs h_lt
    | .bytes bs, h_lt => refByteProvHasIdV2_false_of_gt id bs h_lt
    | .optionVal none, _ => rfl
    | .optionVal (some v'), h_lt => refValHasAllocIdV2_false_of_gt id v' h_lt
    | .scalar _, _ | .range _ _, _ | .rangeTo _, _ | .rangeFrom _, _
    | .bool _, _ | .char _, _ | .ordering _, _ | .unit, _
    | .enumVal _ _, _ => rfl

  /-- Pointwise upper-bound non-occurrence across argument values `vs`. -/
  theorem refValListHasAllocIdV2_false_of_gt (id : Trusted.MirAst.AllocId) :
      ∀ (vs : List Trusted.MirSemantics.Val),
        refMaxValListAllocIdV2 vs < id →
        refValListHasAllocIdV2 id vs = false
    | [], _ => rfl
    | v :: vs, h_lt => by
      dsimp only [refMaxValListAllocIdV2] at h_lt
      have h_v : refMaxValAllocIdV2 v < id :=
        Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h_lt
      have h_vs : refMaxValListAllocIdV2 vs < id :=
        Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h_lt
      dsimp only [refValListHasAllocIdV2]
      rw [refValHasAllocIdV2_false_of_gt id v h_v,
        refValListHasAllocIdV2_false_of_gt id vs h_vs]
      rfl
end

private theorem refValidateRefInMiriV2_push_spec (mBefore mAfter : RefMiriMem)
    (row : Miri.Memory.AllocId × Miri.Memory.LocalAllocation
      Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (h_live : mAfter.live = mBefore.live.push row)
    (reqMut : Trusted.MirAst.Mutability) (pointee : MirTy)
    (v : Trusted.MirSemantics.Val) :
    (refValHasAllocIdV2 row.1.value.toNat v = false →
      refValidateRefInMiriV2 mAfter reqMut pointee v =
        refValidateRefInMiriV2 mBefore reqMut pointee v) ∧
    (refValidateRefInMiriV2 mBefore reqMut pointee v = .ok () →
      refValidateRefInMiriV2 mAfter reqMut pointee v = .ok ()) := by
  have h_live_mono : ∀ (mid : Miri.Memory.AllocId)
      {r : Miri.Memory.AllocId × Miri.Memory.LocalAllocation
        Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit},
      mBefore.live.find? (fun e => e.1 == mid) = some r →
      mAfter.live.find? (fun e => e.1 == mid) = some r := by
    intro mid r h_f
    rw [← Array.find?_toList] at h_f
    rw [h_live, ← Array.find?_toList, Array.toList_push]
    exact list_find?_append_one_some h_f
  have h_live_ne : ∀ (aid : Trusted.MirAst.AllocId)
      (mid : Miri.Memory.AllocId),
      Nat.beq aid row.1.value.toNat = false →
      refExactAllocIdV2 aid = some mid →
      mAfter.live.find? (fun e => e.1 == mid) =
        mBefore.live.find? (fun e => e.1 == mid) := by
    intro aid mid h_ne h_ex
    have h_mval := refExactAllocIdV2_toNat h_ex
    have h_beq : (row.1 == mid) = false := by
      cases h_eq : (row.1 == mid) with
      | false => rfl
      | true =>
        have h_id : row.1 = mid := eq_of_beq h_eq
        have h_eqNat : aid = row.1.value.toNat := by rw [← h_mval, h_id]
        rw [h_eqNat, Nat.beq_refl] at h_ne
        cases h_ne
    rw [h_live, ← Array.find?_toList, ← Array.find?_toList, Array.toList_push]
    exact list_find?_append_one_ne mBefore.live.toList h_beq
  cases v with
  | slicePtr pv len =>
    cases pointee with
    | slice elem =>
      cases elem with
      | int w s =>
        dsimp only [refValidateRefInMiriV2]
        refine ⟨fun h_fr => ?_, fun h_ok => ?_⟩
        · cases !Nat.blt (len.toNat *
              (refScalarLayoutDataV2 w false).size.bytes.toNat)
              (Nat.pow 2 63) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            cases h_aid : pv.allocId with
            | none => rfl
            | some aid =>
              dsimp only
              cases h_ex : refExactAllocIdV2 aid with
              | none => rfl
              | some mid =>
                dsimp only [refValHasAllocIdV2] at h_fr
                rw [h_aid] at h_fr
                dsimp only at h_fr
                dsimp only
                rw [h_live_ne aid mid h_fr h_ex]
        · cases h_sz : !Nat.blt (len.toNat *
              (refScalarLayoutDataV2 w false).size.bytes.toNat)
              (Nat.pow 2 63) with
          | true =>
            rw [h_sz] at h_ok; simp only [ite_true] at h_ok; cases h_ok
          | false =>
            rw [h_sz] at h_ok
            simp only [Bool.false_eq_true, ite_false] at h_ok
            simp only [Bool.false_eq_true, ite_false]
            cases h_aid : pv.allocId with
            | none =>
              rw [h_aid] at h_ok; dsimp only at h_ok; dsimp only; exact h_ok
            | some aid =>
              rw [h_aid] at h_ok; dsimp only at h_ok; dsimp only
              cases h_ex : refExactAllocIdV2 aid with
              | none =>
                rw [h_ex] at h_ok; dsimp only at h_ok; cases h_ok
              | some mid =>
                rw [h_ex] at h_ok; dsimp only at h_ok; dsimp only
                cases h_f : mBefore.live.find? (fun e => e.1 == mid) with
                | none =>
                  rw [h_f] at h_ok; dsimp only at h_ok; cases h_ok
                | some _ =>
                  rw [h_f] at h_ok; dsimp only at h_ok
                  rw [h_live_mono mid h_f]; exact h_ok
      | _ => exact ⟨fun _ => rfl, id⟩
    | _ => exact ⟨fun _ => rfl, id⟩
  | ptr pv =>
    cases pointee with
    | slice elem => cases elem <;> exact ⟨fun _ => rfl, id⟩
    | _ =>
      dsimp only [refValidateRefInMiriV2]
      refine ⟨fun h_fr => ?_, fun h_ok => ?_⟩
      · cases !refIsSupportedPointeeTyV2 _ || !refTyLayoutFitsU64V2 _ with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases h_aid : pv.allocId with
          | none => rfl
          | some aid =>
            dsimp only
            cases h_ex : refExactAllocIdV2 aid with
            | none => rfl
            | some mid =>
              dsimp only [refValHasAllocIdV2] at h_fr
              rw [h_aid] at h_fr
              dsimp only at h_fr
              dsimp only
              rw [h_live_ne aid mid h_fr h_ex]
      · cases h_sup : (!refIsSupportedPointeeTyV2 _ ||
            !refTyLayoutFitsU64V2 _) with
        | true =>
          rw [h_sup] at h_ok; simp only [ite_true] at h_ok; cases h_ok
        | false =>
          rw [h_sup] at h_ok
          simp only [Bool.false_eq_true, ite_false] at h_ok
          simp only [Bool.false_eq_true, ite_false]
          cases h_aid : pv.allocId with
          | none =>
            rw [h_aid] at h_ok; dsimp only at h_ok; dsimp only; exact h_ok
          | some aid =>
            rw [h_aid] at h_ok; dsimp only at h_ok; dsimp only
            cases h_ex : refExactAllocIdV2 aid with
            | none =>
              rw [h_ex] at h_ok; dsimp only at h_ok; cases h_ok
            | some mid =>
              rw [h_ex] at h_ok; dsimp only at h_ok; dsimp only
              cases h_f : mBefore.live.find? (fun e => e.1 == mid) with
              | none =>
                rw [h_f] at h_ok; dsimp only at h_ok; cases h_ok
              | some _ =>
                rw [h_f] at h_ok; dsimp only at h_ok
                rw [h_live_mono mid h_f]; exact h_ok
  | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
  | array _ | range _ _ | rangeTo _ | rangeFrom _ | optionVal _
  | vec _ _ _ | boxPtr _ _ | bytes _ =>
    cases pointee with
    | slice elem => cases elem <;> exact ⟨fun _ => rfl, id⟩
    | _ => exact ⟨fun _ => rfl, id⟩

private theorem refRefsValidInMiriV2_rangeTo_indep
    (m1 m2 : RefMiriMem) (pt : MirTy) (v : Trusted.MirSemantics.Val) :
    refRefsValidInMiriV2 m1 (.rangeTo pt) v =
      refRefsValidInMiriV2 m2 (.rangeTo pt) v := by
  cases pt with
  | int w s => cases w <;> cases s <;> cases v <;> rfl
  | _ => cases v <;> rfl

private theorem refRefsValidInMiriV2_rangeFrom_indep
    (m1 m2 : RefMiriMem) (pt : MirTy) (v : Trusted.MirSemantics.Val) :
    refRefsValidInMiriV2 m1 (.rangeFrom pt) v =
      refRefsValidInMiriV2 m2 (.rangeFrom pt) v := by
  cases pt with
  | int w s => cases w <;> cases s <;> cases v <;> rfl
  | _ => cases v <;> rfl

mutual
  /-- Fresh-allocation push framing and monotonicity for
  `refRefsValidInMiriV2`. -/
  theorem refRefsValidInMiriV2_push_spec (mBefore mAfter : RefMiriMem)
      (row : Miri.Memory.AllocId × Miri.Memory.LocalAllocation
        Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
      (h_live : mAfter.live = mBefore.live.push row) :
      ∀ (t : MirTy) (v : Trusted.MirSemantics.Val),
        (refValHasAllocIdV2 row.1.value.toNat v = false →
          refRefsValidInMiriV2 mAfter t v = refRefsValidInMiriV2 mBefore t v) ∧
        (refRefsValidInMiriV2 mBefore t v = true →
          refRefsValidInMiriV2 mAfter t v = true)
    | .ref reqMut pt, v => by
      unfold refRefsValidInMiriV2
      have h_sp :=
        refValidateRefInMiriV2_push_spec mBefore mAfter row h_live reqMut pt v
      refine ⟨fun h_f => by rw [h_sp.1 h_f], fun h_ok => ?_⟩
      cases h_val : refValidateRefInMiriV2 mBefore reqMut pt v with
      | error _ => rw [h_val] at h_ok; cases h_ok
      | ok _ => rw [h_sp.2 h_val]
    | .tuple ts, v => by
      cases v with
      | tuple vs =>
        exact refRefsValidInMiriListV2_push_spec mBefore mAfter row h_live ts vs
      | _ => exact ⟨fun _ => rfl, id⟩
    | .array elem _, .array vs =>
      refRefsValidInMiriArrayV2_push_spec mBefore mAfter row h_live elem vs
    | .array _ _, .scalar _ | .array _ _, .bool _ | .array _ _, .char _
    | .array _ _, .ordering _ | .array _ _, .unit | .array _ _, .enumVal _ _
    | .array _ _, .ptr _ | .array _ _, .slicePtr _ _ | .array _ _, .range _ _
    | .array _ _, .rangeTo _ | .array _ _, .rangeFrom _
    | .array _ _, .optionVal _ | .array _ _, .tuple _
    | .array _ _, .vec _ _ _ | .array _ _, .boxPtr _ _
    | .array _ _, .bytes _ =>
      ⟨fun _ => rfl, id⟩
    | .bool, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .int _ _, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .char, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .ordering, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .unit, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .enum _, v => by cases v <;> exact ⟨fun _ => rfl, id⟩
    | .rawPtr _ pt, v => by
      cases v with
      | slicePtr _ _ =>
        cases pt with
        | slice elem => cases elem <;> exact ⟨fun _ => rfl, id⟩
        | _ => exact ⟨fun _ => rfl, id⟩
      | _ => exact ⟨fun _ => rfl, id⟩
    | .rangeTo pt, v =>
      ⟨fun _ => refRefsValidInMiriV2_rangeTo_indep mAfter mBefore pt v,
       fun h => by
         rw [refRefsValidInMiriV2_rangeTo_indep mAfter mBefore pt v]
         exact h⟩
    | .rangeFrom pt, v =>
      ⟨fun _ => refRefsValidInMiriV2_rangeFrom_indep mAfter mBefore pt v,
       fun h => by
         rw [refRefsValidInMiriV2_rangeFrom_indep mAfter mBefore pt v]
         exact h⟩
    | .never, v | .slice _, v | .str, v | .range _, v | .option _, v
    | .vec _, v | .box _, v | .unsupported, v => by
      cases v <;> exact ⟨fun _ => rfl, id⟩

  /-- Fresh-allocation push framing and monotonicity for
  `refRefsValidInMiriListV2`. -/
  theorem refRefsValidInMiriListV2_push_spec
      (mBefore mAfter : RefMiriMem)
      (row : Miri.Memory.AllocId × Miri.Memory.LocalAllocation
        Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
      (h_live : mAfter.live = mBefore.live.push row) :
      ∀ (ts : List MirTy) (vs : List Trusted.MirSemantics.Val),
        (refValListHasAllocIdV2 row.1.value.toNat vs = false →
          refRefsValidInMiriListV2 mAfter ts vs =
            refRefsValidInMiriListV2 mBefore ts vs) ∧
        (refRefsValidInMiriListV2 mBefore ts vs = true →
          refRefsValidInMiriListV2 mAfter ts vs = true)
    | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
    | t :: ts, v :: vs => by
      have h1 := refRefsValidInMiriV2_push_spec mBefore mAfter row h_live t v
      have h2 :=
        refRefsValidInMiriListV2_push_spec mBefore mAfter row h_live ts vs
      refine ⟨fun h_f => ?_, fun h_ok => ?_⟩
      · dsimp only [refValListHasAllocIdV2] at h_f
        cases h_fv : refValHasAllocIdV2 row.1.value.toNat v with
        | true => rw [h_fv] at h_f; cases h_f
        | false =>
          rw [h_fv] at h_f
          simp only [Bool.false_or] at h_f
          dsimp only [refRefsValidInMiriListV2]
          rw [h1.1 h_fv, h2.1 h_f]
      · dsimp only [refRefsValidInMiriListV2] at h_ok
        dsimp only [refRefsValidInMiriListV2]
        cases h_t : refRefsValidInMiriV2 mBefore t v with
        | false => rw [h_t] at h_ok; cases h_ok
        | true =>
          rw [h_t] at h_ok
          simp only [Bool.true_and] at h_ok
          rw [h1.2 h_t, h2.2 h_ok]; rfl
    | [], _ :: _ | _ :: _, [] => ⟨fun _ => rfl, id⟩

  /-- Fresh-allocation push framing and monotonicity for
  `refRefsValidInMiriArrayV2`. -/
  theorem refRefsValidInMiriArrayV2_push_spec
      (mBefore mAfter : RefMiriMem)
      (row : Miri.Memory.AllocId × Miri.Memory.LocalAllocation
        Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
      (h_live : mAfter.live = mBefore.live.push row)
      (elem : MirTy) :
      ∀ (vs : List Trusted.MirSemantics.Val),
        (refValListHasAllocIdV2 row.1.value.toNat vs = false →
          refRefsValidInMiriArrayV2 mAfter elem vs =
            refRefsValidInMiriArrayV2 mBefore elem vs) ∧
        (refRefsValidInMiriArrayV2 mBefore elem vs = true →
          refRefsValidInMiriArrayV2 mAfter elem vs = true)
    | [] => ⟨fun _ => rfl, fun _ => rfl⟩
    | v :: vs => by
      have h1 :=
        refRefsValidInMiriV2_push_spec mBefore mAfter row h_live elem v
      have h2 :=
        refRefsValidInMiriArrayV2_push_spec mBefore mAfter row h_live elem vs
      refine ⟨fun h_f => ?_, fun h_ok => ?_⟩
      · dsimp only [refValListHasAllocIdV2] at h_f
        cases h_fv : refValHasAllocIdV2 row.1.value.toNat v with
        | true => rw [h_fv] at h_f; cases h_f
        | false =>
          rw [h_fv] at h_f
          simp only [Bool.false_or] at h_f
          dsimp only [refRefsValidInMiriArrayV2]
          rw [h1.1 h_fv, h2.1 h_f]
      · dsimp only [refRefsValidInMiriArrayV2] at h_ok
        dsimp only [refRefsValidInMiriArrayV2]
        cases h_t : refRefsValidInMiriV2 mBefore elem v with
        | false => rw [h_t] at h_ok; cases h_ok
        | true =>
          rw [h_t] at h_ok
          simp only [Bool.true_and] at h_ok
          rw [h1.2 h_t, h2.2 h_ok]; rfl
end

end Anneal.MirCorrespondence
