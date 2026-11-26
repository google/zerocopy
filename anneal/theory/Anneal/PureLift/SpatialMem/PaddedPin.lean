-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.UInt.BasicAux
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.BlockCfg
public import Anneal.PureLift.MirBridge
public import Anneal.PureLift.SpatialMem.MirMemMirror

public section

namespace Anneal.PureLift

open Trusted.MirAst Trusted.MirSemantics

/-!
# Padded and Provenance-Aware `MemoryState` Spatial Pinning (`PaddedPin`)

Defines `SpatialTargetSpec` (`AuditedFieldSpec`), `AuditedBodyAdtEntry`,
`BodySpatialCtx` (`bodySpatialCtxWf`, `specsMatchBodyCtx`),
`TypedSpatialMemCodec`, `PromotedLocalEntry`, `PaddedSpatialBlock`, and
`PaddedSymMemState` (`freezePaddedToMem`, `mutatePaddedInMem`,
`reabsorbPaddedFromMem`, `writePaddedSymPlace`, `endPaddedLoan`,
`syncPromotedLocalsToMem`, `evalPaddedMirOperand`, and
`deallocatePromotedLocal`), authenticating `st.mirLocalTypes` against the
captured `Trusted.MirAst.Body` and an explicit per-body audited `#[repr(C)]` ADT
side-table before allowing aggregates with uninitialized padding bytes and Day-1
scalars to promote an initialized MIR local to `LocalSlot.indirect` (or reuse an
existing initialized, synchronized unpinned `LocalSlot.indirect` allocation in
place without clobbering padding) inside `MemoryState`, undergo aligned byte
writes, reabsorb into `.activeMut` using the exact lawful codec captured at
freeze time while keeping both `.indirect` stack allocations and `.immediate`
MIR slots synchronized with symbolic writes until `StorageDead`
(`deallocatePromotedLocal`), and fail-closed reject uninitialized non-padding
bytes, per-field bidirectional provenance stripping or surplus provenance
forgery (`valAndBytesMatchTargetSpec`), unauthenticated `.unsupported` / `.ref`
/ general `MirTy.tuple` targets, `.dead` or `.immediate none` borrow/sub-path
desynchronization, aliased promoted `AllocId`s, pre-existing `nextAllocId`
references across symbolic and opaque-decoder reservoirs
(`freshPromotedAllocId`), stale or `Operand.move` MIR reads
(`allPromotedLocalsMemSynced`), unauthenticated `memBlocks` entries, tampered
owner or place metadata, and borrow-handle injection (`replaceableVal`).
Includes lawful codecs for `u32`, a padded `#[repr(C)]` `(u8, [pad; 3], u32)`
struct, and a provenance-carrying `#[repr(C)]` pointer struct.
-/

/-! ## Padded and Provenance-Aware `MemoryState` Spatial Pinning -/

/-- Structural equality on `Option AllocId`. -/
@[expose] def optAllocIdBeq (o1 o2 : Option AllocId) : Bool :=
  match o1 with
  | none =>
    match o2 with
    | none => true
    | some _ => false
  | some p1 =>
    match o2 with
    | none => false
    | some p2 => Nat.beq p1 p2

/-- Structural equality on `AllocByte` including byte value and provenance. -/
@[expose] def allocByteBeq (x y : AllocByte) : Bool :=
  match x with
  | .uninit =>
    match y with
    | .uninit => true
    | .init _ _ => false
  | .init bx px =>
    match y with
    | .uninit => false
    | .init by_ py => Nat.beq bx.toNat by_.toNat && optAllocIdBeq px py

/-- Elementwise equality on `List AllocByte`. -/
@[expose] def allocBytesListBeq (b1 b2 : List AllocByte) : Bool :=
  b1.foldr
    (fun x k ys =>
      match ys with
      | [] => false
      | y :: ys' => allocByteBeq x y && k ys')
    (fun ys =>
      match ys with
      | [] => true
      | _ :: _ => false)
    b2

private theorem optAllocIdBeq_refl (p : Option AllocId) :
    optAllocIdBeq p p = true := by
  cases p with
  | none => rfl
  | some a => exact natBeq_refl a

private theorem allocByteBeq_refl (x : AllocByte) :
    allocByteBeq x x = true := by
  cases x with
  | uninit => rfl
  | init b p =>
    dsimp only [allocByteBeq]
    rw [natBeq_refl b.toNat, optAllocIdBeq_refl p]
    rfl

private theorem allocBytesListBeq_refl :
    ∀ (bs : List AllocByte), allocBytesListBeq bs bs = true
  | [] => rfl
  | x :: xs => by
    change (allocByteBeq x x && allocBytesListBeq xs xs) = true
    rw [allocByteBeq_refl x, allocBytesListBeq_refl xs]
    rfl

/-- Extracts the raw `UInt8` iff the byte is initialized with `prov = none`. -/
@[expose] def allocByteNoProvOpt : AllocByte → Option UInt8
  | .init b none => some b
  | .init _ (some _) | .uninit => none

/-- True iff `bytes` has the same length as `mask` and every position with
`isPad = false` holds an initialized `AllocByte.init`. -/
@[expose] def nonPadBytesInitialized (mask : List Bool) (bytes : List AllocByte)
    : Bool :=
  mask.foldr
    (fun isPad k bs =>
      match bs with
      | [] => false
      | ab :: rest =>
        if isPad then k rest
        else
          match ab with
          | .uninit => false
          | .init _ _ => k rest)
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    bytes

/-- True iff `b1` and `b2` match `mask`'s length and agree on every non-padding
position (`isPad = false`), allowing arbitrary differences on padding bytes. -/
@[expose] def sameAtNonPad (mask : List Bool) (b1 b2 : List AllocByte) : Bool :=
  mask.foldr
    (fun isPad k xs ys =>
      match xs with
      | [] => false
      | x :: xs' =>
        match ys with
        | [] => false
        | y :: ys' =>
          if isPad then k xs' ys'
          else allocByteBeq x y && k xs' ys')
    (fun xs ys =>
      match xs with
      | [] =>
        match ys with
        | [] => true
        | _ :: _ => false
      | _ :: _ => false)
    b1 b2

/-- Extracts the raw `UInt8` from an initialized `AllocByte`. -/
@[expose] def allocByteValOpt : AllocByte → Option UInt8
  | .uninit => none
  | .init b _ => some b

/-- True iff every byte in `bytes` is `.init` carrying `some expectedProv`. -/
@[expose] def allHaveProv (bytes : List AllocByte) (expectedProv : AllocId) :
    Bool :=
  bytes.foldr
    (fun ab acc =>
      match ab with
      | .uninit => false
      | .init _ prov => optAllocIdBeq prov (some expectedProv) && acc)
    true

/-- Alias for `execInitBytes?`, extracting the raw `UInt8` list iff every byte
in `bytes` is `.init`. -/
abbrev extractInitRawBytes (bytes : List AllocByte) : Option (List UInt8) :=
  execInitBytes? bytes

/-- Computable maximum of two `Nat`s. -/
@[expose] def natMaxComp (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

/-- Rounds `off` up to the next multiple of `2^alignLog2`. -/
@[expose] def alignUpPow2 (off alignLog2 : Nat) : Nat :=
  let align := Nat.pow 2 alignLog2
  let rem := Nat.mod off align
  if Nat.beq rem 0 then off else off + (align - rem)

/-- Audited field descriptor inside an explicit `#[repr(C)]` struct layout:
audited byte `offset` and primitive/pointer field `MirTy`. -/
structure AuditedFieldSpec where
  offset : Nat
  fieldTy : MirTy

/-- Target type and layout authority for a local in `PaddedSymMemState`: either
an exact captured `MirTy` (admitting only Day-1 scalar/enum/overflow-pair types
and thin `.rawPtr` pointers to sized admitted `MirTy`s for promotion; general
`MirTy.tuple`, `.ref`, and `.unsupported` cannot be promoted) or an explicit
`#[repr(C)]` struct ADT carrying an `adtTag` and audited declaration-order field
offsets (`AuditedFieldSpec`). -/
inductive SpatialTargetSpec where
  | mirTy (ty : MirTy)
  | reprCAdt (adtTag : Nat) (fields : List AuditedFieldSpec)

/-- Maps a `SpatialTargetSpec` to the `MirTy` recorded in captured `Body.locals`
(`.unsupported` for `#[repr(C)]` struct ADTs, `ty` for `.mirTy ty`). -/
@[expose] def SpatialTargetSpec.toCapturedMirTy : SpatialTargetSpec → MirTy
  | .mirTy ty => ty
  | .reprCAdt _ _ => .unsupported

/-- Computable structural equality on `AuditedFieldSpec`. -/
@[expose] def auditedFieldSpecBeq (a b : AuditedFieldSpec) : Bool :=
  Nat.beq a.offset b.offset && mirTyBeq a.fieldTy b.fieldTy

/-- Elementwise computable equality on `List AuditedFieldSpec`. -/
@[expose] def auditedFieldSpecsBeq (fs1 fs2 : List AuditedFieldSpec) : Bool :=
  fs1.foldr
    (fun f k ys =>
      match ys with
      | [] => false
      | y :: ys' => auditedFieldSpecBeq f y && k ys')
    (fun ys => match ys with | [] => true | _ :: _ => false)
    fs2

/-- Computable structural equality on `SpatialTargetSpec`. -/
@[expose] def spatialTargetSpecBeq : SpatialTargetSpec → SpatialTargetSpec →
    Bool
  | .mirTy t1, .mirTy t2 => mirTyBeq t1 t2
  | .reprCAdt id1 fs1, .reprCAdt id2 fs2 =>
    Nat.beq id1 id2 && auditedFieldSpecsBeq fs1 fs2
  | _, _ => false

/-- Bounded-depth check that a raw-pointer pointee `MirTy` has a known sized
layout (Day-1 scalar/enum/overflow-pair or thin `.rawPtr` to a sized admitted
`MirTy`), failing closed (`false`) on `.unsupported`, `.ref`, general `.tuple`,
and unadmitted `.enum` so wide pointers (`*mut [T]`, `*const str`, `*mut dyn`)
are never assigned 8-byte thin layouts. -/
@[expose] def sizedPointeeAdmittedAt (d : Nat) (ty : MirTy) : Bool :=
  natFold
    (fun t => (execLayoutOfTy t).isSome)
    (fun _ ih t =>
      match t with
      | .rawPtr _ pointee => ih pointee
      | _ => (execLayoutOfTy t).isSome)
    d ty

/-- Layout of a non-aggregate primitive or thin-`rawPtr` field `MirTy`,
rejecting `.tuple`, `.ref`, `.unsupported`, and wide-pointer pointees. -/
@[expose] def primitiveFieldLayout? (ty : MirTy) : Option LayoutData :=
  match ty with
  | .bool | .int _ _ | .char | .ordering | .unit | .never | .enum _ =>
    execLayoutOfTy ty
  | .rawPtr _ pointee =>
    if sizedPointeeAdmittedAt 8 pointee then some ⟨8, 3⟩ else none
  | .tuple _ | .ref _ _ | .slice _ | .array _ _ | .rangeTo _ | .rangeFrom _
  | .range _
  | .option _ | .unsupported => none

/-- Computes the canonical 64-bit `(LayoutData, padMask)` for `spec`, agreeing
identically with `Trusted.MirSemantics.layoutOfTy` on all Day-1 `.mirTy` types
(including `(T, bool)` overflow pairs), admitting thin `.rawPtr` to sized
admitted `MirTy`s, verifying audited `#[repr(C)]` field offsets on `.reprCAdt`,
and rejecting general `MirTy.tuple`, `.ref`, and `.unsupported`. -/
@[expose] def targetSpecLayoutAndMask (spec : SpatialTargetSpec) :
    Option (LayoutData × List Bool) :=
  match spec with
  | .mirTy ty =>
    match ty with
    | .tuple [t1, t2] =>
      match t1, t2 with
      | .int w _, .bool =>
        let sz := (execIntLayout w).size
        some (execOverflowPairLayout w,
              List.replicate sz false ++ [false] ++ List.replicate (sz - 1) true)
      | _, _ => none
    | _ =>
      match primitiveFieldLayout? ty with
      | some l => some (l, List.replicate l.size false)
      | none => none
  | .reprCAdt _ fields =>
    if fields.isEmpty then none
    else
      fields.foldr
        (fun (f : AuditedFieldSpec) k (acc : Nat × Nat × List Bool) =>
          match primitiveFieldLayout? f.fieldTy with
          | none => none
          | some fLay =>
            let alignedOff := alignUpPow2 acc.1 fLay.alignLog2
            if !Nat.beq f.offset alignedOff then none
            else
              let pad := alignedOff - acc.1
              k (alignedOff + fLay.size,
                 natMaxComp acc.2.1 fLay.alignLog2,
                 acc.2.2 ++ List.replicate pad true ++
                   List.replicate fLay.size false))
        (fun (acc : Nat × Nat × List Bool) =>
          let padTail := alignUpPow2 acc.1 acc.2.1 - acc.1
          some (⟨acc.1 + padTail, acc.2.1⟩,
                acc.2.2 ++ List.replicate padTail true))
        (0, 0, [])

/-- Computable UTF-8 byte equality on `String` without `._unsafe_rec`. -/
@[expose] def spatialStringBeq (s1 s2 : String) : Bool :=
  s1.toByteArray.data.toList.foldr
    (fun b1 k ys =>
      match ys with
      | [] => false
      | b2 :: ys' => Nat.beq b1.toNat b2.toNat && k ys')
    (fun ys => match ys with | [] => true | _ :: _ => false)
    s2.toByteArray.data.toList

/-- Externally audited `#[repr(C)]` ADT local descriptor binding a captured
`MirTy.unsupported` slot `localReg` of the MIR `Body` identified by non-empty
`bodyIdentity` to its `adtTag` and declaration-order `AuditedFieldSpec`
layout. -/
structure AuditedBodyAdtEntry where
  bodyIdentity : String
  localReg : LocalId
  adtTag : Nat
  fields : List AuditedFieldSpec

/-- Captured-MIR and audited `#[repr(C)]` ADT authority context for a
`Trusted.MirAst.Body`. Because `rustc-capture` lowers non-enum ADTs to
`MirTy.unsupported` in `Body.locals`, `adtLocals` supplies the externally
audited per-body `(bodyIdentity, localReg, adtTag, fields)` table authenticating
which `.unsupported` slots of `body` carry `#[repr(C)]` aggregate layouts. -/
structure BodySpatialCtx where
  body : Body
  adtLocals : List AuditedBodyAdtEntry := []

/-- True iff `entries` contains any `AuditedBodyAdtEntry` for `reg`. -/
@[expose] def hasAnyAdtEntryForLocal (entries : List AuditedBodyAdtEntry)
    (reg : LocalId) : Bool :=
  entries.foldr (fun e acc => Nat.beq e.localReg reg || acc) false

/-- Extracts the unique `AuditedBodyAdtEntry` for `reg`, returning `none` if
absent or duplicated. -/
@[expose] def findUniqueAdtEntryForLocal (entries : List AuditedBodyAdtEntry)
    (reg : LocalId) : Option AuditedBodyAdtEntry :=
  let res :=
    entries.foldr
      (fun e (acc : Bool × Option AuditedBodyAdtEntry) =>
        if Nat.beq e.localReg reg then
          match acc.2 with
          | some _ => (true, acc.2)
          | none => (acc.1, some e)
        else
          acc)
      (false, none)
  if res.1 then none else res.2

/-- True iff `ctx.adtLocals` is either empty or binds a non-empty
`ctx.body.identity` with pairwise-distinct `localReg` entries, each targeting an
in-bounds `MirTy.unsupported` slot of `ctx.body.locals` with a valid
`#[repr(C)]` layout (`targetSpecLayoutAndMask`). -/
@[expose] def bodySpatialCtxWf (ctx : BodySpatialCtx) : Bool :=
  if ctx.adtLocals.isEmpty then true
  else
    !ctx.body.identity.toByteArray.data.toList.isEmpty &&
    ctx.adtLocals.foldr
      (fun e acc =>
        spatialStringBeq e.bodyIdentity ctx.body.identity &&
        (findUniqueAdtEntryForLocal ctx.adtLocals e.localReg).isSome &&
        (match mirListGet? ctx.body.locals e.localReg with
         | some .unsupported => true
         | _ => false) &&
        (targetSpecLayoutAndMask (.reprCAdt e.adtTag e.fields)).isSome &&
        acc)
      true

/-- Authenticates `specs` (`st.mirLocalTypes`) slot-for-slot against captured
`ctx.body.locals` and `ctx.adtLocals`: every `.mirTy ty` slot must equal
`ctx.body.locals[idx]` (`mirTyBeq`) and carry no ADT side-table entry, while
every `.reprCAdt adtTag fields` slot must correspond to `MirTy.unsupported` in
`ctx.body.locals[idx]` and match the unique audited `ctx.adtLocals` entry for
`idx`. -/
@[expose] def specsMatchBodyCtx (ctx : BodySpatialCtx)
    (specs : List SpatialTargetSpec) : Bool :=
  bodySpatialCtxWf ctx &&
  Nat.beq ctx.body.locals.length specs.length &&
  (ctx.body.locals.foldr
    (fun capTy k idx remSpecs =>
      match remSpecs with
      | [] => false
      | spec :: restSpecs =>
        let okHere : Bool :=
          match spec with
          | .mirTy ty =>
            mirTyBeq capTy ty && !hasAnyAdtEntryForLocal ctx.adtLocals idx
          | .reprCAdt adtTag fields =>
            (match capTy with | .unsupported => true | _ => false) &&
            (match findUniqueAdtEntryForLocal ctx.adtLocals idx with
             | some e =>
               Nat.beq e.adtTag adtTag &&
               auditedFieldSpecsBeq e.fields fields
             | none => false)
        okHere && k (idx + 1) restSpecs)
    (fun _ remSpecs => match remSpecs with | [] => true | _ :: _ => false)
    0
    specs)

/-- `targetSpecLayoutAndMask (.mirTy ty)` strictly extends
`Trusted.MirSemantics.layoutOfTy` on every Day-1 `MirTy` (including all six
`IntWidth` overflow-pair layouts). -/
theorem reprCLayout_extends_trusted_layoutOfTy (ty : MirTy) (l : LayoutData)
    (h : Trusted.MirSemantics.layoutOfTy ty = some l) :
    Exists fun mask => targetSpecLayoutAndMask (.mirTy ty) = some (l, mask) := by
  rw [← execLayoutOfTy_eq ty] at h
  cases ty with
  | bool => injection h with hl; subst hl; exact ⟨[false], rfl⟩
  | ordering => injection h with hl; subst hl; exact ⟨[false], rfl⟩
  | char =>
    injection h with hl; subst hl
    exact ⟨[false, false, false, false], rfl⟩
  | unit => injection h with hl; subst hl; exact ⟨[], rfl⟩
  | never => injection h with hl; subst hl; exact ⟨[], rfl⟩
  | int w s =>
    injection h with hl; subst hl
    exact ⟨List.replicate (execIntLayout w).size false, rfl⟩
  | enum ety =>
    dsimp only [execLayoutOfTy] at h
    cases hAdm : mirEnumAdmitted ety with
    | false => rw [hAdm] at h; nomatch h
    | true =>
      rw [hAdm] at h
      cases hTag : ety.tagRepr with
      | zeroSized =>
        rw [hTag] at h
        injection h with hl; subst hl
        refine ⟨[], ?_⟩
        dsimp only [targetSpecLayoutAndMask, primitiveFieldLayout?,
          execLayoutOfTy]
        rw [hAdm, hTag]
        rfl
      | scalar tagW tagS =>
        rw [hTag] at h
        injection h with hl; subst hl
        refine ⟨List.replicate (execIntLayout tagW).size false, ?_⟩
        dsimp only [targetSpecLayoutAndMask, primitiveFieldLayout?,
          execLayoutOfTy]
        rw [hAdm, hTag]
        rfl
  | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
  | range _ | option _
  | unsupported => nomatch h
  | tuple fs =>
    cases fs with
    | nil => nomatch h
    | cons t1 r1 =>
      cases t1 with
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
      | range _ | option _
      | unsupported =>
        cases r1 with
        | nil => nomatch h
        | cons _ r2 => cases r2 <;> nomatch h
      | int w s =>
        cases r1 with
        | nil => nomatch h
        | cons t2 r2 =>
          cases t2 with
          | int _ _ | unit | never | char | ordering | enum _ | tuple _
          | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
          | range _ | option _
          | unsupported =>
            cases r2 <;> nomatch h
          | bool =>
            cases r2 with
            | cons _ _ => nomatch h
            | nil =>
              injection h with hl; subst hl
              cases w <;> exact ⟨_, rfl⟩

/-- Compatibility check between a symbolic `Val` and a primitive or thin
`.rawPtr` field `MirTy` (rejecting `.tuple`, `.ref`, `.unsupported`, and
wide-pointer pointees). -/
@[expose] def primFieldValCompat (v : Val) (ty : MirTy) : Bool :=
  match ty with
  | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _ =>
    mirCheckVal v ty
  | .rawPtr _ pointee =>
    sizedPointeeAdmittedAt 8 pointee &&
    match v with
    | .ptr pv => mirIntWidthBeq pv.width .isize
    | _ => false
  | .tuple _ | .ref _ _ | .slice _ | .array _ _ | .rangeTo _ | .rangeFrom _
  | .range _
  | .option _ | .unsupported => false

/-- Compatibility check between a symbolic `Val` and its declared
`SpatialTargetSpec`, agreeing with `mirCheckVal` on Day-1 `.mirTy` scalars,
enums, and overflow pairs, requiring 64-bit `Val.ptr` on thin `.rawPtr`s to
sized admitted `MirTy`s, verifying fieldwise compatibility on `.reprCAdt`, and
rejecting `.ref`, `.unsupported`, and general `MirTy.tuple`. -/
@[expose] def valCompatWithTargetSpec (v : Val) (spec : SpatialTargetSpec) :
    Bool :=
  match spec with
  | .mirTy ty =>
    match ty with
    | .tuple [.int w s, .bool] => mirCheckVal v (.tuple [.int w s, .bool])
    | _ => primFieldValCompat v ty
  | .reprCAdt _ fields =>
    if fields.isEmpty then false
    else
      match v with
      | .tuple fVals =>
        fVals.foldr
          (fun fv k fs =>
            match fs with
            | [] => false
            | f :: fs' => primFieldValCompat fv f.fieldTy && k fs')
          (fun fs => match fs with | [] => true | _ :: _ => false)
          fields
      | _ => false

/-- Type compatibility check for an initialized `LocalSlot.immediate` value
against its declared `SpatialTargetSpec`: requires `valCompatWithTargetSpec` for
all value types, and a valid `PureLift` borrow handle (`mirDecodeRef` plus
`mirDecodeRefIsShared` matching `.mut` vs. `.shared`) for `.mirTy (.ref _ _)`.
-/
@[expose] def immValCompatWithTargetSpec (v : Val) (spec : SpatialTargetSpec) :
    Bool :=
  match spec with
  | .mirTy (.ref .mut _) => (mirDecodeRef v).isSome && !mirDecodeRefIsShared v
  | .mirTy (.ref .shared _) => (mirDecodeRef v).isSome && mirDecodeRefIsShared v
  | other => valCompatWithTargetSpec v other

/-- True iff every byte in `bs` is initialized with `prov = none`. -/
@[expose] def sliceAllInitNoProv (bs : List AllocByte) : Bool :=
  bs.foldr
    (fun ab acc =>
      match ab with
      | .init _ none => acc
      | .init _ (some _) | .uninit => false)
    true

/-- True iff every byte in `bs` is initialized with `optAllocIdBeq prov`
matching `expected`. -/
@[expose] def sliceAllInitOptProv (bs : List AllocByte) (expected : Option
    AllocId) :
    Bool :=
  bs.foldr
    (fun ab acc =>
      match ab with
      | .init _ prov => optAllocIdBeq prov expected && acc
      | .uninit => false)
    true

/-- Validates padding byte slices: when `requireUninit = true` (encode/freeze),
every padding byte must be `.uninit`; when `requireUninit = false`
(decode/reabsorb), padding bytes may be `.uninit` or `.init _ none` but may
never carry `some aid` provenance. -/
@[expose] def padBytesClean (requireUninit : Bool) (bs : List AllocByte) : Bool
    :=
  bs.foldr
    (fun ab acc =>
      match ab with
      | .uninit => acc
      | .init _ none => !requireUninit && acc
      | .init _ (some _) => false)
    true

/-- Validates exact per-field byte value, initialization, and bidirectional
provenance conservation for a single primitive or thin-`.rawPtr` field
`(ty, v, slice)`: scalar/bool/char/ordering/unit/enum slices must equal
`execEncodeVal execProfileTargetEndian ty v` (with `prov = none` on every byte),
while `.rawPtr` 8-byte slices must encode `pv.offsetBytes` and carry
`pv.allocId` uniformly across all 8 bytes. -/
@[expose] def primFieldBytesMatch (ty : MirTy) (v : Val) (slice : List
    AllocByte) : Bool :=
  match ty with
  | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _ =>
    mirCheckVal v ty &&
    match execLayoutOfTy ty, execEncodeVal execProfileTargetEndian ty v with
    | some l, .ok enc =>
      Nat.beq slice.length l.size &&
      sliceAllInitNoProv slice &&
      allocBytesListBeq slice enc
    | _, _ => false
  | .rawPtr _ pointee =>
    sizedPointeeAdmittedAt 8 pointee &&
    match v with
    | .ptr pv =>
      let expectedSlice :=
        (execEncodeUInt execProfileTargetEndian 8 pv.offsetBytes.toNat).map
          (fun b => AllocByte.init b pv.allocId)
      mirIntWidthBeq pv.width .isize &&
      Nat.beq slice.length 8 &&
      sliceAllInitOptProv slice pv.allocId &&
      allocBytesListBeq slice expectedSlice
    | _ => false
  | .tuple _ | .ref _ _ | .slice _ | .array _ _ | .rangeTo _ | .rangeFrom _
  | .range _
  | .option _ | .unsupported => false

/-- Codec-independent per-field byte-value, bidirectional provenance, and
padding guard: verifies that `bytes` matches `spec`'s exact layout size, every
padding byte satisfies `padBytesClean requireUninitPad` (never carrying
provenance, and `.uninit` on encode), every scalar/enum/overflow-pair field
slice matches `execEncodeVal` with `prov = none` on all value bytes, and every
`.rawPtr` field slice encodes `pv.offsetBytes` and carries `pv.allocId` on all
8 bytes at its exact field offset. -/
@[expose] def valAndBytesMatchTargetSpec (requireUninitPad : Bool)
    (spec : SpatialTargetSpec) (v : Val) (bytes : List AllocByte) : Bool :=
  match spec with
  | .mirTy ty =>
    match ty with
    | .tuple [.int w s, .bool] =>
      let sz := (execIntLayout w).size
      mirCheckVal v (.tuple [.int w s, .bool]) &&
      Nat.beq bytes.length (2 * sz) &&
      sliceAllInitNoProv (bytes.take (sz + 1)) &&
      (match execEncodeVal execProfileTargetEndian
           (.tuple [.int w s, .bool]) v with
       | .ok enc => allocBytesListBeq (bytes.take (sz + 1)) (enc.take (sz + 1))
       | .error _ => false) &&
      padBytesClean requireUninitPad (bytes.drop (sz + 1))
    | _ => primFieldBytesMatch ty v bytes
  | .reprCAdt _ fields =>
    if fields.isEmpty then false
    else
      match v with
      | .tuple fVals =>
        fields.foldr
          (fun (f : AuditedFieldSpec) k (vs : List Val) (curOff maxAl : Nat) =>
            match vs, primitiveFieldLayout? f.fieldTy with
            | fv :: vs', some fLay =>
              let alignedOff := alignUpPow2 curOff fLay.alignLog2
              if !Nat.beq f.offset alignedOff then false
              else
                let padLen := alignedOff - curOff
                let padSlice := (bytes.drop curOff).take padLen
                let fldSlice := (bytes.drop alignedOff).take fLay.size
                padBytesClean requireUninitPad padSlice &&
                primFieldBytesMatch f.fieldTy fv fldSlice &&
                k vs' (alignedOff + fLay.size) (natMaxComp maxAl fLay.alignLog2)
            | _, _ => false)
          (fun (vs : List Val) (curOff maxAl : Nat) =>
            match vs with
            | _ :: _ => false
            | [] =>
              let totalSize := alignUpPow2 curOff maxAl
              Nat.beq bytes.length totalSize &&
              padBytesClean requireUninitPad (bytes.drop curOff))
          fVals 0 0
      | _ => false

private theorem padBytesClean_false_of_true :
    ∀ (bs : List AllocByte),
      padBytesClean true bs = true → padBytesClean false bs = true
  | [], _ => rfl
  | .uninit :: rest, h => padBytesClean_false_of_true rest h
  | .init _ none :: _, h => nomatch h
  | .init _ (some _) :: _, h => nomatch h

private def reprCFieldsMatchBytes (requireUninitPad : Bool)
    (bytes : List AllocByte) :
    List AuditedFieldSpec → List Val → Nat → Nat → Bool :=
  fun fields fVals curOff maxAl =>
    fields.foldr
      (fun (f : AuditedFieldSpec) k (vs : List Val) (cOff mAl : Nat) =>
        match vs, primitiveFieldLayout? f.fieldTy with
        | fv :: vs', some fLay =>
          let alignedOff := alignUpPow2 cOff fLay.alignLog2
          if !Nat.beq f.offset alignedOff then false
          else
            let padLen := alignedOff - cOff
            let padSlice := (bytes.drop cOff).take padLen
            let fldSlice := (bytes.drop alignedOff).take fLay.size
            padBytesClean requireUninitPad padSlice &&
            primFieldBytesMatch f.fieldTy fv fldSlice &&
            k vs' (alignedOff + fLay.size) (natMaxComp mAl fLay.alignLog2)
        | _, _ => false)
      (fun (vs : List Val) (cOff mAl : Nat) =>
        match vs with
        | _ :: _ => false
        | [] =>
          let totalSize := alignUpPow2 cOff mAl
          Nat.beq bytes.length totalSize &&
          padBytesClean requireUninitPad (bytes.drop cOff))
      fVals curOff maxAl

private theorem reprCFieldsMatchBytes_false_of_true (bytes : List AllocByte) :
    ∀ (fields : List AuditedFieldSpec) (fVals : List Val) (curOff maxAl : Nat),
      reprCFieldsMatchBytes true bytes fields fVals curOff maxAl = true →
      reprCFieldsMatchBytes false bytes fields fVals curOff maxAl = true
  | [], _ :: _, _, _, h => nomatch h
  | [], [], curOff, maxAl, h => by
    unfold reprCFieldsMatchBytes at h
    unfold reprCFieldsMatchBytes
    dsimp only [List.foldr] at h
    dsimp only [List.foldr]
    cases hLen : Nat.beq bytes.length (alignUpPow2 curOff maxAl) with
    | false => rw [hLen] at h; nomatch h
    | true =>
      rw [hLen, Bool.true_and] at h
      rw [Bool.true_and]
      exact padBytesClean_false_of_true (bytes.drop curOff) h
  | f :: fs, [], _, _, h => by
    unfold reprCFieldsMatchBytes at h
    dsimp only [List.foldr] at h
    nomatch h
  | f :: fs, fv :: vs', curOff, maxAl, h => by
    unfold reprCFieldsMatchBytes at h
    unfold reprCFieldsMatchBytes
    dsimp only [List.foldr] at h
    dsimp only [List.foldr]
    cases hLay : primitiveFieldLayout? f.fieldTy with
    | none => rw [hLay] at h; nomatch h
    | some fLay =>
      rw [hLay] at h
      dsimp only at h
      dsimp only
      cases hOff : !Nat.beq f.offset (alignUpPow2 curOff fLay.alignLog2) with
      | true => rw [hOff] at h; nomatch h
      | false =>
        rw [hOff, ite_bool_false rfl] at h
        rw [ite_bool_false rfl]
        cases hPad :
            padBytesClean true
              ((bytes.drop curOff).take
                (alignUpPow2 curOff fLay.alignLog2 - curOff)) with
        | false => rw [hPad] at h; nomatch h
        | true =>
          rw [hPad, Bool.true_and] at h
          rw [padBytesClean_false_of_true _ hPad, Bool.true_and]
          cases hFld :
              primFieldBytesMatch f.fieldTy fv
                ((bytes.drop (alignUpPow2 curOff fLay.alignLog2)).take
                  fLay.size) with
          | false => rw [hFld] at h; nomatch h
          | true =>
            rw [hFld, Bool.true_and] at h
            rw [Bool.true_and]
            exact reprCFieldsMatchBytes_false_of_true bytes fs vs' _ _ h

/-- Any byte slice satisfying `valAndBytesMatchTargetSpec true` (encode/freeze
mode requiring `.uninit` padding) also satisfies
`valAndBytesMatchTargetSpec false` (decode/reabsorb mode allowing non-provenance
initialized padding). -/
theorem valAndBytesMatchTargetSpec_false_of_true (spec : SpatialTargetSpec)
    (v : Val) (bytes : List AllocByte)
    (h : valAndBytesMatchTargetSpec true spec v bytes = true) :
    valAndBytesMatchTargetSpec false spec v bytes = true := by
  cases spec with
  | mirTy ty =>
    cases ty with
    | bool | int _ _ | unit | never | char | ordering | enum _ | ref _ _
    | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
    | range _ | option _
    | unsupported => exact h
    | tuple ts =>
      cases ts with
      | nil => exact h
      | cons t1 r1 =>
        cases t1 with
        | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
        | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
        | range _ | option _
        | unsupported =>
          cases r1 with
          | nil => exact h
          | cons _ r2 => cases r2 <;> exact h
        | int w s =>
          cases r1 with
          | nil => exact h
          | cons t2 r2 =>
            cases t2 with
            | int _ _ | unit | never | char | ordering | enum _ | tuple _
            | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _
            | rangeFrom _
            | range _ | option _ | unsupported =>
              cases r2 <;> exact h
            | bool =>
              cases r2 with
              | cons _ _ => exact h
              | nil =>
                dsimp only [valAndBytesMatchTargetSpec] at h
                dsimp only [valAndBytesMatchTargetSpec]
                cases h1 :
                    (mirCheckVal v (.tuple [.int w s, .bool]) &&
                     Nat.beq bytes.length (2 * (execIntLayout w).size) &&
                     sliceAllInitNoProv
                       (bytes.take ((execIntLayout w).size + 1)) &&
                     match execEncodeVal execProfileTargetEndian
                         (.tuple [.int w s, .bool]) v with
                     | .ok enc =>
                       allocBytesListBeq
                         (bytes.take ((execIntLayout w).size + 1))
                         (enc.take ((execIntLayout w).size + 1))
                     | .error _ => false) with
                | false => rw [h1, Bool.false_and] at h; nomatch h
                | true =>
                  rw [h1, Bool.true_and] at h
                  rw [Bool.true_and]
                  exact padBytesClean_false_of_true _ h
  | reprCAdt tag fields =>
    dsimp only [valAndBytesMatchTargetSpec] at h
    dsimp only [valAndBytesMatchTargetSpec]
    cases hEmp : fields.isEmpty with
    | true => rw [hEmp] at h; nomatch h
    | false =>
      rw [hEmp, ite_bool_false rfl] at h
      rw [ite_bool_false rfl]
      cases v with
      | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
      | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | bytes _ =>
        nomatch h
      | tuple fVals =>
        exact reprCFieldsMatchBytes_false_of_true bytes fields fVals 0 0 h

/-- Typed codec connecting a symbolic `Val` representation of `α` for a local of
declared `SpatialTargetSpec` `targetTy` to its `MemoryState` `AllocByte` layout.
In `padMask`, `true` marks padding byte positions (which encode as `.uninit` and
never carry provenance) and `false` marks value byte positions (which must be
`.init`). `provCheck` allows codec-specific byte checks on top of the
codec-independent `valAndBytesMatchTargetSpec` guard enforced at freeze and
reabsorption. -/
structure TypedSpatialMemCodec (α : Type) where
  codecId : Nat
  targetTy : SpatialTargetSpec
  layout : LayoutData
  padMask : List Bool
  encodeValToMem : α → List AllocByte
  decodeValFromMem : List AllocByte → Option α
  provCheck : List AllocByte → Bool
  encodeToSymVal : α → Val
  decodeFromSymVal : Val → Option α

/-- Well-formedness, `SpatialTargetSpec` compatibility, bidirectional
per-field provenance conservation, universal non-padding get-put re-encoding,
Day-1 `encodeVal`/`decodeVal` agreement, and round-trip contract for a
`TypedSpatialMemCodec`. -/
@[expose] def LawfulTypedSpatialMemCodec {α : Type} (c : TypedSpatialMemCodec α)
    : Prop :=
  targetSpecLayoutAndMask c.targetTy = some (c.layout, c.padMask) ∧
  c.padMask.length = c.layout.size ∧
  (∀ x, (c.encodeValToMem x).length = c.layout.size ∧
    nonPadBytesInitialized c.padMask (c.encodeValToMem x) = true ∧
    c.provCheck (c.encodeValToMem x) = true ∧
    valCompatWithTargetSpec (c.encodeToSymVal x) c.targetTy = true ∧
    valAndBytesMatchTargetSpec true c.targetTy (c.encodeToSymVal x)
      (c.encodeValToMem x) = true ∧
    c.decodeValFromMem (c.encodeValToMem x) = some x ∧
    c.decodeFromSymVal (c.encodeToSymVal x) = some x) ∧
  (∀ v x, c.decodeFromSymVal v = some x → c.encodeToSymVal x = v) ∧
  (∀ bs x, bs.length = c.layout.size →
    nonPadBytesInitialized c.padMask bs = true →
    c.provCheck bs = true →
    c.decodeValFromMem bs = some x →
    sameAtNonPad c.padMask bs (c.encodeValToMem x) = true) ∧
  (∀ ty l, c.targetTy = .mirTy ty →
    Trusted.MirSemantics.layoutOfTy ty = some l →
    (∀ x, Trusted.MirSemantics.encodeVal profileTargetEndian ty
        (c.encodeToSymVal x) = .ok (c.encodeValToMem x)) ∧
    (∀ x, Trusted.MirSemantics.decodeVal profileTargetEndian ty
        (c.encodeValToMem x) = .ok (some (c.encodeToSymVal x))) ∧
    (∀ bs x, bs.length = c.layout.size →
      nonPadBytesInitialized c.padMask bs = true →
      c.provCheck bs = true →
      valAndBytesMatchTargetSpec false c.targetTy (c.encodeToSymVal x) bs =
        true →
      c.decodeValFromMem bs = some x →
      Trusted.MirSemantics.decodeVal profileTargetEndian ty bs =
        .ok (some (c.encodeToSymVal x)))) ∧
  (∀ b1 b2, b1.length = c.layout.size → b2.length = c.layout.size →
    nonPadBytesInitialized c.padMask b1 = true →
    nonPadBytesInitialized c.padMask b2 = true →
    sameAtNonPad c.padMask b1 b2 = true →
    c.decodeValFromMem b1 = c.decodeValFromMem b2)

/-- Metadata for a loan promoted into `MemoryState` at `place`. Every field is
checked and authenticated against `LoanPhase.spatialPinned` during byte
mutation, reabsorption, and `allPromotedLocalsMemSynced`. -/
structure PaddedSpatialBlock where
  blockId : BlockId
  originLoan : LoanId
  ownerLocal : LocalId
  perm : SpatialPerm
  provenanceTag : Nat
  activeSubSplits : Nat
  layout : LayoutData
  place : MemPlace
  codecId : Nat

/-- Authority and byte-synchronization witness for a local promoted to
`LocalSlot.indirect` inside `PaddedSymMemState`. -/
structure PromotedLocalEntry where
  localReg : LocalId
  localTy : SpatialTargetSpec
  place : MemPlace
  layout : LayoutData
  padMask : List Bool
  codecId : Nat
  encodeSymToMem : Val → Option (List AllocByte)

/-- Combined pure `SymState Val`, per-local `SpatialTargetSpec` and `LocalSlot`
frame, `MemoryState`, active `PaddedSpatialBlock` table, and promoted-local
synchronization table. While a loan is authenticated in
`LoanPhase.spatialPinned`, `mem` is authoritative for that local; otherwise
`allPromotedLocalsMemSynced` verifies that both promoted `LocalSlot.indirect`
bytes and unpromoted `LocalSlot.immediate` values agree with `st.sym` before any
MIR operand read (`evalPaddedMirOperand`), while `writePaddedSymPlace` and
`endPaddedLoan` refresh both views across symbolic writes. -/
structure PaddedSymMemState where
  sym : SymState Val
  mirLocalTypes : List SpatialTargetSpec
  mirLocals : List LocalSlot
  mem : MemoryState
  memBlocks : List PaddedSpatialBlock
  promotedLocals : List PromotedLocalEntry := []

/-- Counts active `PaddedSpatialBlock` entries originating from `lid`. -/
@[expose] def countPaddedBlocksForLoan (lid : LoanId)
    (blocks : List PaddedSpatialBlock) : Nat :=
  blocks.foldr (fun b n => if Nat.beq b.originLoan lid then n + 1 else n) 0

/-- True iff `blocks` contains an entry with `blockId = bid`. -/
@[expose] def hasPaddedBlockId (bid : BlockId)
    (blocks : List PaddedSpatialBlock) : Bool :=
  !Nat.beq (blocks.foldr (fun b n => if Nat.beq b.blockId bid then n + 1 else n) 0) 0

/-- Extracts the unique `PaddedSpatialBlock` with `blockId = bid` together with
the remaining blocks, returning `none` if absent or duplicated. -/
@[expose] def findPaddedSpatialBlock (blocks : List PaddedSpatialBlock)
    (bid : BlockId) :
    Option (PaddedSpatialBlock × List PaddedSpatialBlock) :=
  let res :=
    blocks.foldr
      (fun b (acc : Bool × Option PaddedSpatialBlock × List PaddedSpatialBlock) =>
        if Nat.beq b.blockId bid then
          match acc.2.1 with
          | some _ => (true, acc.2.1, acc.2.2)
          | none => (acc.1, some b, acc.2.2)
        else
          (acc.1, acc.2.1, b :: acc.2.2))
      (false, none, [])
  if res.1 then none
  else
    match res.2.1 with
    | none => none
    | some found => some (found, res.2.2)

/-- Computable equality on `OrderingVal`. -/
@[expose] def mirOrderingBeq : OrderingVal → OrderingVal → Bool
  | .less, .less => true
  | .equal, .equal => true
  | .greater, .greater => true
  | _, _ => false

/-- Computable equality on `Bool`. -/
@[expose] def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Computable structural equality on `ScalarVal`. -/
@[expose] def mirScalarValBeq (s1 s2 : ScalarVal) : Bool :=
  mirIntWidthBeq s1.width s2.width &&
  boolBeq s1.signed s2.signed &&
  Nat.beq s1.bits.toNat s2.bits.toNat

/-- Computable structural equality on `PtrVal`. -/
@[expose] def mirPtrValBeq (p1 p2 : PtrVal) : Bool :=
  optAllocIdBeq p1.allocId p2.allocId &&
  Nat.beq p1.offsetBytes.toNat p2.offsetBytes.toNat &&
  mirIntWidthBeq p1.width p2.width

/-- Bounded-depth computable equality on `Val`, failing closed (`false`) if
tuple nesting exceeds `d`. -/
@[expose] def mirValBeqAt (d : Nat) (v1 v2 : Val) : Bool :=
  natFold
    (fun a b =>
      match a, b with
      | .scalar s1, .scalar s2 => mirScalarValBeq s1 s2
      | .ptr p1, .ptr p2 => mirPtrValBeq p1 p2
      | .bool b1, .bool b2 => boolBeq b1 b2
      | .char c1, .char c2 => Nat.beq c1.toNat c2.toNat
      | .ordering o1, .ordering o2 => mirOrderingBeq o1 o2
      | .unit, .unit => true
      | .enumVal et1 vr1, .enumVal et2 vr2 =>
        mirEnumTyBeq et1 et2 && Nat.beq vr1 vr2
      | .bytes bs1, .bytes bs2 => allocBytesListBeq bs1 bs2
      | _, _ => false)
    (fun _ ih a b =>
      match a, b with
      | .tuple fs1, .tuple fs2 =>
        fs1.foldr
          (fun x k ys =>
            match ys with
            | [] => false
            | y :: ys' => ih x y && k ys')
          (fun ys =>
            match ys with
            | [] => true
            | _ :: _ => false)
          fs2
      | .scalar s1, .scalar s2 => mirScalarValBeq s1 s2
      | .ptr p1, .ptr p2 => mirPtrValBeq p1 p2
      | .bool b1, .bool b2 => boolBeq b1 b2
      | .char c1, .char c2 => Nat.beq c1.toNat c2.toNat
      | .ordering o1, .ordering o2 => mirOrderingBeq o1 o2
      | .unit, .unit => true
      | .enumVal et1 vr1, .enumVal et2 vr2 =>
        mirEnumTyBeq et1 et2 && Nat.beq vr1 vr2
      | .bytes bs1, .bytes bs2 => allocBytesListBeq bs1 bs2
      | _, _ => false)
    d v1 v2

/-- True iff `bs` contains no `AllocByte.init` carrying `some aid`. Because
`mirEncodeRef` and `mirEncodeSharedRef` represent `PureLift` borrow handles as
`Val.bytes` leaves using `AllocByte` provenance slots for `LoanId`s, a 1-byte
borrow handle `(aid, [])` is representationally indistinguishable from a 1-byte
pointer-provenance fragment referencing `AllocId = aid`; checking every
`some p` conservatively over-approximates allocation references so no provenance
byte can bypass deallocation or reuse checks. -/
@[expose] def bytesFreeOfAllocId (aid : AllocId) (bs : List AllocByte) : Bool :=
  bs.foldr
    (fun b acc =>
      match b with
      | .uninit => acc
      | .init _ none => acc
      | .init _ (some p) => !Nat.beq p aid && acc)
    true

/-- True iff `v` has tuple depth at most `d` and contains no pointer or byte
provenance referencing `aid` (conservatively rejecting `Val.bytes` borrow
handles whose `LoanId` or `SubPath` provenance slot equals `aid`; see
`bytesFreeOfAllocId`). -/
@[expose] def valFreeOfAllocId (d : Nat) (aid : AllocId) (v : Val) : Bool :=
  natFold
    (fun x =>
      match x with
      | .tuple _ | .array _ => false
      | .ptr p =>
        match p.allocId with
        | none => true
        | some pId => !Nat.beq pId aid
      | .slicePtr p _ =>
        match p.allocId with
        | none => true
        | some pId => !Nat.beq pId aid
      | .bytes bs => bytesFreeOfAllocId aid bs
      | .scalar _ | .bool _ | .unit | .char _ | .ordering _ | .enumVal _ _
      | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _ =>
        true)
    (fun _ ih x =>
      match x with
      | .tuple fields | .array fields =>
        fields.foldr (fun c acc => ih c && acc) true
      | .ptr p =>
        match p.allocId with
        | none => true
        | some pId => !Nat.beq pId aid
      | .slicePtr p _ =>
        match p.allocId with
        | none => true
        | some pId => !Nat.beq pId aid
      | .bytes bs => bytesFreeOfAllocId aid bs
      | .scalar _ | .bool _ | .unit | .char _ | .ordering _ | .enumVal _ _
      | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _ =>
        true)
    d v

/-- Extracts `some reg` iff `t` is a direct root local `.localReg reg`. -/
@[expose] def loanDirectLocal? (t : BackTarget Val) : Option LocalId :=
  match t.steps with
  | [.direct (.localReg reg) []] => some reg
  | _ => none

/-- True iff `t` mentions `reg` in any `.direct` or `.lensCall` writeback
step. -/
@[expose] def backTargetMentionsLocal (reg : LocalId) (t : BackTarget Val) :
    Bool :=
  t.steps.foldr
    (fun s acc =>
      match s with
      | .direct (.localReg r) _ => Nat.beq r reg || acc
      | .lensCall targets _ =>
        targets.foldr
          (fun tp tAcc =>
            match tp.1 with
            | .localReg r => Nat.beq r reg || tAcc
            | .parentLoan _ => tAcc)
          false || acc
      | _ => acc)
    false

/-- True iff `symLocals[reg]` exists and its normalized permission tree is the
single exclusive root lock `[([], .mutLocked lid)]`, guaranteeing
`ownerHasBorrowLock` at `[]` and blocking all `readPlaceVal`, `writePlaceVal`,
and `acquirePerm` operations on `reg` and its sub-places without any
co-existing shared or joined sibling lock. -/
@[expose] def localExclusivelyMutLockedBy (reg : LocalId) (lid : LoanId)
    (symLocals : List (PlaceCell Val)) : Bool :=
  match mirListGet? symLocals reg with
  | some symCell =>
    match toEntries symCell.perm with
    | [([], .mutLocked l)] => Nat.beq l lid
    | _ => false
  | none => false

/-- True iff any non-ended loan with `id ≠ lid` mentions `reg` in its
`BackTarget`. -/
@[expose] def otherNonEndedTargetsReg (reg : LocalId) (lid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun le acc =>
      (!le.phase.isEnded && !Nat.beq le.id lid &&
       backTargetMentionsLocal reg le.target) || acc)
    false

/-- True iff any active `RegionGroupEntry` mentions `.localReg reg` in its
`inputTargets`. -/
@[expose] def activeRegionMentionsLocal (reg : LocalId)
    (groups : List (RegionGroupEntry Val)) : Bool :=
  groups.foldr
    (fun rg acc =>
      (rg.active &&
       rg.inputTargets.foldr
         (fun tp tAcc =>
           match tp.1 with
           | .localReg r => Nat.beq r reg || tAcc
           | .parentLoan _ => tAcc)
         false) || acc)
    false

/-- True iff `sym.locals[reg]` is exclusively mutably locked by `lid` and no
other non-ended loan or active region group targets `reg`. -/
@[expose] def ownerLocalExclusivelyHeldByLoan (reg : LocalId) (lid : LoanId)
    (sym : SymState Val) : Bool :=
  localExclusivelyMutLockedBy reg lid sym.locals &&
  !otherNonEndedTargetsReg reg lid sym.loans &&
  !activeRegionMentionsLocal reg sym.regionGroups

/-- Encodes an accepted symbolic `Val` into `MemoryState` bytes via `codec`,
verifying canonical symbolic round-trip, `valCompatWithTargetSpec`, and
`valAndBytesMatchTargetSpec true` (rejecting surplus provenance or initialized
padding on encode). -/
@[expose] def encodeSymOfCodec {α : Type} (codec : TypedSpatialMemCodec α)
    (v : Val) : Option (List AllocByte) :=
  match codec.decodeFromSymVal v with
  | none => none
  | some x =>
    let raw := codec.encodeValToMem x
    if mirValBeqAt 8 (codec.encodeToSymVal x) v &&
       valCompatWithTargetSpec v codec.targetTy &&
       codec.provCheck raw &&
       valAndBytesMatchTargetSpec true codec.targetTy v raw then
      some raw
    else
      none

/-- True iff `entries` contains a `PromotedLocalEntry` for `reg`. -/
@[expose] def hasPromotedLocalEntry (reg : LocalId)
    (entries : List PromotedLocalEntry) : Bool :=
  !Nat.beq
    (entries.foldr (fun e n => if Nat.beq e.localReg reg then n + 1 else n) 0)
    0

/-- Extracts the unique `PromotedLocalEntry` for `reg` together with the
remaining entries, returning `none` if absent or duplicated. -/
@[expose] def findUniquePromotedLocalEntry (entries : List PromotedLocalEntry)
    (reg : LocalId) :
    Option (PromotedLocalEntry × List PromotedLocalEntry) :=
  let res :=
    entries.foldr
      (fun e (acc : Bool × Option PromotedLocalEntry × List PromotedLocalEntry) =>
        if Nat.beq e.localReg reg then
          match acc.2.1 with
          | some _ => (true, acc.2.1, acc.2.2)
          | none => (acc.1, some e, acc.2.2)
        else
          (acc.1, acc.2.1, e :: acc.2.2))
      (false, none, [])
  if res.1 then none
  else
    match res.2.1 with
    | none => none
    | some found => some (found, res.2.2)

/-- Replaces the `PromotedLocalEntry` for `newEntry.localReg` in place. -/
@[expose] def replacePromotedLocalEntry (newEntry : PromotedLocalEntry)
    (entries : List PromotedLocalEntry) : List PromotedLocalEntry :=
  entries.foldr
    (fun e acc =>
      if Nat.beq e.localReg newEntry.localReg then newEntry :: acc
      else e :: acc)
    []

/-- Removes all `PromotedLocalEntry` records for `reg`. -/
@[expose] def removePromotedLocalEntry (reg : LocalId)
    (entries : List PromotedLocalEntry) : List PromotedLocalEntry :=
  entries.foldr
    (fun e acc => if Nat.beq e.localReg reg then acc else e :: acc)
    []

/-- True iff any `PromotedLocalEntry` targets `aid`. -/
@[expose] def anyPromotedEntryUsesAlloc (aid : AllocId)
    (entries : List PromotedLocalEntry) : Bool :=
  entries.foldr (fun e acc => Nat.beq e.place.allocId aid || acc) false

/-- True iff any `PromotedLocalEntry` for a local `localReg ≠ reg` targets
`aid`. -/
@[expose] def otherPromotedEntryUsesAlloc (reg : LocalId) (aid : AllocId)
    (entries : List PromotedLocalEntry) : Bool :=
  entries.foldr
    (fun e acc =>
      (!Nat.beq e.localReg reg && Nat.beq e.place.allocId aid) || acc)
    false

/-- True iff any `LocalSlot.indirect` at index `idx ≠ reg` targets `aid`. -/
@[expose] def otherIndirectLocalUsesAlloc (reg : LocalId) (aid : AllocId)
    (locals : List LocalSlot) : Bool :=
  locals.foldr
    (fun slot k idx =>
      let here : Bool :=
        if Nat.beq idx reg then false
        else
          match slot with
          | .indirect mp => Nat.beq mp.allocId aid
          | _ => false
      here || k (idx + 1))
    (fun _ => false)
    0

/-- `SpatialCodec Val` witness stored inside `LoanPhase.spatialPinned` that
authenticates `(place, ownerReg, codec.layout)` via `encode .unit` (carrying an
`.uninit` sentinel cell so pure `reabsorbFromSpatialInState` always rejects
contrived cross-layer blocks), binds the exact typed `padMask`, `provCheck`,
`decodeValFromMem`, and `encodeToSymVal` captured at `freezePaddedToMem` time,
and enforces per-field bidirectional provenance conservation via
`valAndBytesMatchTargetSpec false`. -/
@[expose] def paddedLoanWitnessCodec {α : Type}
    (codec : TypedSpatialMemCodec α) (ownerReg : LocalId) (place : MemPlace) :
    SpatialCodec Val where
  codecId := codec.codecId
  encode v :=
    [.init v, .uninit,
     .init (.bytes [.init 0 (some place.allocId),
                    .init 0 (some place.offset),
                    .init 0 (some ownerReg),
                    .init 0 (some codec.layout.size),
                    .init 0 (some codec.layout.alignLog2)])]
  decode cells :=
    match cells with
    | [.init v, .uninit, .init _] => some v
    | [.uninit, .init (.bytes memBytes)] =>
      if !nonPadBytesInitialized codec.padMask memBytes then
        none
      else if !codec.provCheck memBytes then
        none
      else
        match codec.decodeValFromMem memBytes with
        | none => none
        | some typedVal =>
          let symVal := codec.encodeToSymVal typedVal
          if !valAndBytesMatchTargetSpec false codec.targetTy symVal memBytes then
            none
          else
            some symVal
    | _ => none
  decode_encode _ := rfl

/-- Verifies that `blk`'s codec ID, owner local, `MemPlace`, and `LayoutData`
match the authenticated witness bound in `LoanPhase.spatialPinned`. -/
@[expose] def witnessMatchesBlock (pinnedCodec : SpatialCodec Val)
    (ownerReg : LocalId) (blk : PaddedSpatialBlock) : Bool :=
  Nat.beq pinnedCodec.codecId blk.codecId &&
  Nat.beq blk.ownerLocal ownerReg &&
  match pinnedCodec.encode .unit with
  | [.init .unit, .uninit,
     .init (.bytes [.init _ (some wAlloc),
                    .init _ (some wOff),
                    .init _ (some wOwner),
                    .init _ (some wSize),
                    .init _ (some wAlign)])] =>
    Nat.beq wAlloc blk.place.allocId &&
    Nat.beq wOff blk.place.offset &&
    Nat.beq wOwner ownerReg &&
    Nat.beq wSize blk.layout.size &&
    Nat.beq wAlign blk.layout.alignLog2
  | _ => false

/-- True iff any MIR local at index `idx ≠ ownerReg` references `aid`. -/
@[expose] def otherLocalUsesAlloc (ownerReg : LocalId) (aid : AllocId)
    (locals : List LocalSlot) : Bool :=
  (locals.foldr
    (fun slot k idx =>
      let here : Bool :=
        if Nat.beq idx ownerReg then false
        else
          match slot with
          | .dead => false
          | .immediate none => false
          | .immediate (some v) => !valFreeOfAllocId 8 aid v
          | .indirect mp => Nat.beq mp.allocId aid
          | .partialTuple _ => true
      here || k (idx + 1))
    (fun _ => false)
    0)

/-- True iff any symbolic local at index `idx ≠ ownerReg` references `aid`. -/
@[expose] def otherSymLocalUsesAlloc (ownerReg : LocalId) (aid : AllocId)
    (symLocals : List (PlaceCell Val)) : Bool :=
  (symLocals.foldr
    (fun cell k idx =>
      let here : Bool :=
        if Nat.beq idx ownerReg then false
        else !valFreeOfAllocId 8 aid cell.val
      here || k (idx + 1))
    (fun _ => false)
    0)

/-- True iff `t` stores a `.choiceJoin` condition referencing `aid` or an
uninspectable `.lensCall` writeback closure. -/
@[expose] def backTargetUsesAlloc (aid : AllocId) (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun s acc =>
      match s with
      | .choiceJoin cond => !valFreeOfAllocId 8 aid cond || acc
      | .lensCall _ _ => true
      | _ => acc)
    false

/-- True iff any non-ended loan is spatially pinned (holding an uninspectable
`SpatialCodec` decoder closure), stores a cell value referencing `aid`, or has a
`BackTarget` referencing `aid` or holding a `.lensCall` closure. -/
@[expose] def activeLoanValUsesAlloc (aid : AllocId) (loans : List (LoanEntry
    Val)) :
    Bool :=
  loans.foldr
    (fun le acc =>
      (!le.phase.isEnded &&
       ((match le.phase with | .spatialPinned _ _ => true | _ => false) ||
        !valFreeOfAllocId 8 aid le.cell.val ||
        backTargetUsesAlloc aid le.target)) || acc)
    false

/-- True iff any pure `SpatialBlock` in `st.sym.spatial` holds a `.rawByte`
cell or an initialized cell value referencing `aid`. -/
@[expose] def pureSpatialUsesAlloc (aid : AllocId)
    (blocks : List (SpatialBlock Val)) : Bool :=
  blocks.foldr
    (fun blk acc =>
      blk.cells.foldr
        (fun c cAcc =>
          (match c with
           | .uninit => false
           | .rawByte _ => true
           | .init v => !valFreeOfAllocId 8 aid v) || cAcc)
        false || acc)
    false

/-- True iff any pending `regionDeposits` entry references `aid`. -/
@[expose] def regionDepositsUseAlloc (aid : AllocId)
    (deposits : List (RegionGroupId × Val)) : Bool :=
  deposits.foldr
    (fun d acc => !valFreeOfAllocId 8 aid d.2 || acc)
    false

/-- True iff any `RegionGroupEntry` remains active (`rg.active = true`),
holding an uninspectable `backFn` closure that can emit values when ended. -/
@[expose] def activeRegionGroupExists (groups : List (RegionGroupEntry Val)) :
    Bool :=
  groups.foldr (fun rg acc => rg.active || acc) false

/-- True iff any `PaddedSpatialBlock` in `blocks` targets `aid`. -/
@[expose] def anyBlockUsesAlloc (aid : AllocId) (blocks : List
    PaddedSpatialBlock) :
    Bool :=
  blocks.foldr (fun b acc => Nat.beq b.place.allocId aid || acc) false

/-- True iff any live `Allocation` with `allocId ≠ aid` carries provenance
referencing `aid`. -/
@[expose] def otherLiveAllocRefsAlloc (aid : AllocId) (allocs : List Allocation)
    :
    Bool :=
  allocs.foldr
    (fun a acc =>
      if Nat.beq a.allocId aid || !a.live then acc
      else !bytesFreeOfAllocId aid a.bytes || acc)
    false

/-- True iff any existing `Allocation` (live or dead) carries byte provenance
referencing `aid`. -/
@[expose] def anyAllocBytesRefAlloc (aid : AllocId) (allocs : List Allocation) :
    Bool :=
  allocs.foldr (fun a acc => !bytesFreeOfAllocId aid a.bytes || acc) false

/-- Conservative exclusive-ownership check for `aid`: verifies that no active
`PaddedSpatialBlock`, other `PromotedLocalEntry`, other MIR or symbolic local,
non-ended loan (conservatively rejecting any `.spatialPinned` loan or
`.lensCall` closure), pure `SpatialBlock` (rejecting any `.rawByte` cell),
region deposit, active region group, or other live `MemoryState` allocation
references `aid`. -/
@[expose] def allocExclusivelyOwnedByLocal (reg : LocalId) (aid : AllocId)
    (st : PaddedSymMemState) : Bool :=
  !anyBlockUsesAlloc aid st.memBlocks &&
  !otherPromotedEntryUsesAlloc reg aid st.promotedLocals &&
  !otherLocalUsesAlloc reg aid st.mirLocals &&
  !otherSymLocalUsesAlloc reg aid st.sym.locals &&
  !activeLoanValUsesAlloc aid st.sym.loans &&
  !pureSpatialUsesAlloc aid st.sym.spatial &&
  !regionDepositsUseAlloc aid st.sym.regionDeposits &&
  !activeRegionGroupExists st.sym.regionGroups &&
  !otherLiveAllocRefsAlloc aid st.mem.allocations

/-- True iff `place` is an unpinned, exclusively owned, live mutable stack
allocation matching `layout` (with `sym.locals[reg]` free of self-references to
`place.allocId`) that can be reused in place when re-freezing `reg`. -/
@[expose] def reusablePromotedPlace (reg : LocalId) (place : MemPlace)
    (layout : LayoutData) (st : PaddedSymMemState) : Bool :=
  Nat.beq place.offset 0 &&
  allocExclusivelyOwnedByLocal reg place.allocId st &&
  (match mirListGet? st.sym.locals reg with
   | some symCell => valFreeOfAllocId 8 place.allocId symCell.val
   | none => false) &&
  match execFindAllocation place.allocId st.mem.allocations with
  | some alloc =>
    alloc.live &&
    (match alloc.mutability with | .mut => true | .shared => false) &&
    Nat.beq alloc.bytes.length layout.size &&
    Nat.beq alloc.alignLog2 layout.alignLog2
  | none => false

/-- True iff any `LocalSlot.indirect` entry in `locals` targets `aid`. -/
@[expose] def indirectLocalsUseAlloc (aid : AllocId) (locals : List LocalSlot) :
    Bool :=
  locals.foldr
    (fun slot acc =>
      (match slot with
       | .indirect mp => Nat.beq mp.allocId aid
       | _ => false) || acc)
    false

/-- True iff `aid` is completely unused across `st.mem.allocations`,
`st.mirLocals` (both `.indirect` places and `.immediate` values across all
locals including `reg`), `st.sym.locals`, non-ended `st.sym.loans` (including
opaque `.spatialPinned` decoders and `.lensCall` closures), `st.sym.spatial`
(including `.rawByte` cells), `st.sym.regionDeposits`, active
`st.sym.regionGroups`, `st.memBlocks`, `st.promotedLocals`, and byte provenance
across all existing allocations. -/
@[expose] def freshPromotedAllocId (reg : LocalId) (aid : AllocId)
    (st : PaddedSymMemState) : Bool :=
  (execFindAllocation aid st.mem.allocations).isNone &&
  !indirectLocalsUseAlloc aid st.mirLocals &&
  !anyPromotedEntryUsesAlloc aid st.promotedLocals &&
  (match mirListGet? st.mirLocals reg, mirListGet? st.sym.locals reg with
   | some (.immediate (some slotVal)), some symCell =>
     valFreeOfAllocId 8 aid slotVal && valFreeOfAllocId 8 aid symCell.val
   | _, _ => false) &&
  allocExclusivelyOwnedByLocal reg aid st &&
  !anyAllocBytesRefAlloc aid st.mem.allocations

/-- True iff `place.allocId` resolves in `mem` to a live `.mut` allocation
whose bounds and alignment cover `(place, layout)`, enforcing allocation
liveness, mutability, bounds, and alignment even on zero-sized reads or
zero-length writes. -/
@[expose] def liveMutSliceValid (mem : MemoryState) (place : MemPlace)
    (layout : LayoutData) : Bool :=
  match execFindAllocation place.allocId mem.allocations with
  | some alloc =>
    alloc.live &&
    (match alloc.mutability with | .mut => true | .shared => false) &&
    execIsInBounds alloc place.offset layout.size &&
    execIsAligned alloc place.offset layout.alignLog2
  | none => false

/-- True iff pinned loan `e` (`blk.originLoan`) has an unborrowed cell, no
active child loan or region edges, an exclusively mutably locked owner local
`ownerReg` in `sym`, and no extra spatial blocks in `restBlocks` or
`sym.spatial`. -/
@[expose] def pinnedLoanSymCoherent (e : LoanEntry Val) (ownerReg : LocalId)
    (blk : PaddedSpatialBlock) (restBlocks : List PaddedSpatialBlock)
    (sym : SymState Val) : Bool :=
  isUnborrowed e.cell.perm &&
  noActiveChildLoanEdgesIn mirValAlg blk.originLoan sym.loans &&
  noActiveChildRegionEdges blk.originLoan sym.regionGroups &&
  ownerLocalExclusivelyHeldByLoan ownerReg blk.originLoan sym &&
  Nat.beq (countPaddedBlocksForLoan blk.originLoan restBlocks) 0 &&
  Nat.beq (countBlocksForLoan blk.originLoan sym.spatial) 0

/-- True iff `locals[ownerLocal]` is `LocalSlot.indirect expected`. -/
@[expose] def slotMatchesIndirection (locals : List LocalSlot) (ownerLocal :
    Nat)
    (expected : MemPlace) : Bool :=
  match mirListGet? locals ownerLocal with
  | some (.indirect slotPlace) =>
    Nat.beq slotPlace.allocId expected.allocId &&
    Nat.beq slotPlace.offset expected.offset
  | _ => false

/-- Freezes an unborrowed `.activeMut` root-local loan `lid` into `MemoryState`
using lawful `codec`: verifies `LawfulTypedSpatialMemCodec codec`,
`mirLocalTypes[reg] = codec.targetTy`, `ownerLocalExclusivelyHeldByLoan`, and
exact bidirectional provenance conservation (`valAndBytesMatchTargetSpec true`),
promotes an initialized `LocalSlot.immediate (some v)` matching `e.cell.val` to
a fresh `LocalSlot.indirect` stack allocation verified free of pre-existing
references via `freshPromotedAllocId` (or reuses a tracked, exclusively owned,
initialized, and synchronized unpinned `LocalSlot.indirect` allocation in place
without clobbering existing padding bytes), records a `PromotedLocalEntry`, and
binds `paddedLoanWitnessCodec` inside `LoanPhase.spatialPinned`. -/
@[expose] def freezePaddedToMem {α : Type}
    (ctx : BodySpatialCtx)
    (lid : LoanId) (codec : TypedSpatialMemCodec α)
    (_hLawful : LawfulTypedSpatialMemCodec codec)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length then .fail
  else if !hasUniqueLoanId lid st.sym.loans then .fail
  else
    match findLoan lid st.sym.loans with
    | none => .fail
    | some e =>
      let pureChecksOk : Bool :=
        e.phase.isActiveMut &&
        isUnborrowed e.cell.perm &&
        noActiveChildLoanEdgesIn mirValAlg lid st.sym.loans &&
        noActiveChildRegionEdges lid st.sym.regionGroups &&
        Nat.beq (countPaddedBlocksForLoan lid st.memBlocks) 0 &&
        !hasPaddedBlockId st.sym.nextSpatialTag st.memBlocks &&
        Nat.beq (countBlocksForLoan lid st.sym.spatial) 0 &&
        !hasSpatialBlockId st.sym.nextSpatialTag st.sym.spatial
      if !pureChecksOk then
        .fail
      else
        match loanDirectLocal? e.target with
        | none => .fail
        | some reg =>
          match mirListGet? st.mirLocalTypes reg with
          | none => .fail
          | some localTy =>
            if !spatialTargetSpecBeq localTy codec.targetTy then
              .fail
            else if !ownerLocalExclusivelyHeldByLoan reg lid st.sym then
              .fail
            else
              match codec.decodeFromSymVal e.cell.val with
              | none => .fail
              | some typedVal =>
                let rawBytes := codec.encodeValToMem typedVal
                let encChecksOk : Bool :=
                  mirValBeqAt 8 (codec.encodeToSymVal typedVal) e.cell.val &&
                  valCompatWithTargetSpec e.cell.val localTy &&
                  Nat.beq rawBytes.length codec.layout.size &&
                  Nat.beq codec.padMask.length codec.layout.size &&
                  nonPadBytesInitialized codec.padMask rawBytes &&
                  codec.provCheck rawBytes &&
                  valAndBytesMatchTargetSpec true localTy e.cell.val rawBytes
                if !encChecksOk then
                  .fail
                else
                  match mirListGet? st.mirLocals reg with
                  | some (.immediate (some slotVal)) =>
                    if !mirValBeqAt 8 slotVal e.cell.val then
                      .fail
                    else if hasPromotedLocalEntry reg st.promotedLocals then
                      .fail
                    else if !freshPromotedAllocId reg st.mem.nextAllocId st then
                      .fail
                    else
                      let allocRes := execAllocateStack st.mem codec.layout
                      let mem1 := allocRes.1
                      let place := allocRes.2
                      match execWriteBytes mem1 place codec.layout.alignLog2
                          rawBytes with
                      | .error _ => .fail
                      | .ok mem2 =>
                        match mirListSet? st.mirLocals reg (.indirect place) with
                        | none => .fail
                        | some mirLocals' =>
                          let bid := st.sym.nextSpatialTag
                          let witness := paddedLoanWitnessCodec codec reg place
                          let loans' := updateLoan lid
                            (fun x =>
                              ⟨x.id, .spatialPinned bid witness, x.cell,
                               x.target⟩)
                            st.sym.loans
                          let sym' : SymState Val :=
                            { st.sym with
                              loans := loans', nextSpatialTag := bid + 1 }
                          let blk : PaddedSpatialBlock :=
                            ⟨bid, lid, reg, .readWrite, bid, 0, codec.layout,
                             place, codec.codecId⟩
                          let entry : PromotedLocalEntry :=
                            ⟨reg, localTy, place, codec.layout, codec.padMask,
                             codec.codecId, encodeSymOfCodec codec⟩
                          .ok ⟨sym', st.mirLocalTypes, mirLocals', mem2,
                               st.memBlocks ++ [blk],
                               st.promotedLocals ++ [entry]⟩
                  | some (.indirect existingPlace) =>
                    match findUniquePromotedLocalEntry st.promotedLocals reg with
                    | none => .fail
                    | some (prevEntry, _) =>
                      let prevOk : Bool :=
                        Nat.beq prevEntry.place.allocId existingPlace.allocId &&
                        Nat.beq prevEntry.place.offset existingPlace.offset &&
                        spatialTargetSpecBeq prevEntry.localTy localTy
                      if !prevOk then
                        .fail
                      else if !reusablePromotedPlace reg existingPlace
                          codec.layout st then
                        .fail
                      else if !liveMutSliceValid st.mem existingPlace
                          codec.layout then
                        .fail
                      else
                        let witness :=
                          paddedLoanWitnessCodec codec reg existingPlace
                        let curMemValid : Bool :=
                          match execReadBytes st.mem existingPlace
                              codec.layout.size codec.layout.alignLog2 with
                          | .error _ => false
                          | .ok curBytes =>
                            match witness.decode
                                [.uninit, .init (.bytes curBytes)] with
                            | some curVal => mirValBeqAt 8 curVal e.cell.val
                            | none => false
                        if !curMemValid then
                          .fail
                        else
                          let bid := st.sym.nextSpatialTag
                          let loans' := updateLoan lid
                            (fun x =>
                              ⟨x.id, .spatialPinned bid witness, x.cell,
                               x.target⟩)
                            st.sym.loans
                          let sym' : SymState Val :=
                            { st.sym with
                              loans := loans', nextSpatialTag := bid + 1 }
                          let blk : PaddedSpatialBlock :=
                            ⟨bid, lid, reg, .readWrite, bid, 0, codec.layout,
                             existingPlace, codec.codecId⟩
                          let entry : PromotedLocalEntry :=
                            ⟨reg, localTy, existingPlace, codec.layout,
                             codec.padMask, codec.codecId,
                             encodeSymOfCodec codec⟩
                          .ok ⟨sym', st.mirLocalTypes, st.mirLocals, st.mem,
                               st.memBlocks ++ [blk],
                               replacePromotedLocalEntry entry
                                 st.promotedLocals⟩
                  | some (.immediate none) | some .dead | some (.partialTuple _)
                  | none => .fail

/-- Structural equality on `List Bool` masks. -/
@[expose] def boolListBeq (xs ys : List Bool) : Bool :=
  xs.foldr
    (fun x k zs =>
      match zs with
      | [] => false
      | y :: ys' =>
        match x, y with
        | true, true => k ys'
        | false, false => k ys'
        | _, _ => false)
    (fun zs =>
      match zs with
      | [] => true
      | _ :: _ => false)
    ys

/-- Retains only the non-padding bytes of `bytes` according to `padMask`,
failing closed to `[]` if lengths disagree. -/
@[expose] def nonPadBytesOfMask (padMask : List Bool) (bytes : List AllocByte) :
    List AllocByte :=
  if !Nat.beq padMask.length bytes.length then
    []
  else
    (padMask.foldr
      (fun isPad k bs =>
        match bs with
        | [] => []
        | b :: rest =>
          if isPad then k rest else b :: k rest)
      (fun _ => [])
      bytes)

/-- True iff every provenance tag `some aid` occurring in `src` already
appears in `allowed`. -/
@[expose] def bytesProvSubset (src allowed : List AllocByte) : Bool :=
  src.foldr
    (fun b acc =>
      match b with
      | .init _ (some aid) => !bytesFreeOfAllocId aid allowed && acc
      | _ => acc)
    true

/-- Performs an in-bounds, aligned byte write (`execWriteBytes`) into a pinned
`PaddedSpatialBlock` after authenticating its loan, symbolic lock coherence,
pinned block ID and caller provenance tag, write permission, sub-split count,
owner local, `MemPlace` witness, target layout/mask, live mutable backing
allocation, and provenance conservation (every `some aid` tag in `newBytes`
must already appear in a non-padding byte of the pinned block). -/
@[expose] def mutatePaddedInMem
    (ctx : BodySpatialCtx)
    (bid tag offset writeAlignLog2 : Nat)
    (newBytes : List AllocByte)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length then .fail
  else
    match findPaddedSpatialBlock st.memBlocks bid with
    | none => .fail
    | some (blk, restBlocks) =>
      if !hasUniqueLoanId blk.originLoan st.sym.loans then .fail
      else
        match findLoan blk.originLoan st.sym.loans with
        | none => .fail
        | some e =>
          match e.phase, loanDirectLocal? e.target with
          | .spatialPinned loanBid pinnedCodec, some ownerReg =>
            if !pinnedLoanSymCoherent e ownerReg blk restBlocks st.sym then
              .fail
            else
              match mirListGet? st.mirLocalTypes ownerReg with
              | none => .fail
              | some localTy =>
                match targetSpecLayoutAndMask localTy with
                | none => .fail
                | some (specLay, specMask) =>
                  let writable : Bool :=
                    match blk.perm with
                    | .readWrite => true
                    | .readOnly => false
                  let metaChecksOk : Bool :=
                    Nat.beq loanBid bid &&
                    Nat.beq blk.provenanceTag bid &&
                    Nat.beq blk.provenanceTag tag &&
                    witnessMatchesBlock pinnedCodec ownerReg blk &&
                    Nat.beq specLay.size blk.layout.size &&
                    Nat.beq specLay.alignLog2 blk.layout.alignLog2 &&
                    writable &&
                    Nat.beq blk.activeSubSplits 0 &&
                    Nat.ble (offset + newBytes.length) blk.layout.size &&
                    Nat.ble writeAlignLog2 blk.layout.alignLog2 &&
                    Nat.beq
                      (Nat.mod (blk.place.offset + offset)
                        (Nat.pow 2 writeAlignLog2))
                      0
                  if !metaChecksOk then
                    .fail
                  else if !slotMatchesIndirection st.mirLocals ownerReg
                      blk.place ||
                      otherPromotedEntryUsesAlloc ownerReg blk.place.allocId
                        st.promotedLocals ||
                      otherIndirectLocalUsesAlloc ownerReg blk.place.allocId
                        st.mirLocals then
                    .fail
                  else if !liveMutSliceValid st.mem blk.place blk.layout then
                    .fail
                  else
                    match execReadBytes st.mem blk.place blk.layout.size
                        blk.layout.alignLog2 with
                    | .error _ => .fail
                    | .ok curBlkBytes =>
                      if !bytesProvSubset newBytes
                          (nonPadBytesOfMask specMask curBlkBytes) then
                        .fail
                      else
                        let targetPlace : MemPlace :=
                          ⟨blk.place.allocId, blk.place.offset + offset⟩
                        match execWriteBytes st.mem targetPlace writeAlignLog2
                            newBytes with
                        | .error _ => .fail
                        | .ok mem' => .ok { st with mem := mem' }
          | _, _ => .fail

/-- Reabsorbs a pinned loan back into `.activeMut` using the exact typed codec
bound inside `LoanPhase.spatialPinned` at freeze time after verifying symbolic
lock coherence, live mutable backing allocation, and codec-independent
non-padding initialization, type compatibility, and exact field byte/provenance
agreement (`valAndBytesMatchTargetSpec false`), keeping the promoted
`LocalSlot.indirect` stack allocation and its `PromotedLocalEntry` live until
`StorageDead` (`deallocatePromotedLocal`). -/
@[expose] def reabsorbPaddedFromMem
    (ctx : BodySpatialCtx)
    (lid : LoanId)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length then .fail
  else if !hasUniqueLoanId lid st.sym.loans then .fail
  else
    match findLoan lid st.sym.loans with
    | none => .fail
    | some e =>
      match e.phase, loanDirectLocal? e.target with
      | .spatialPinned bid pinnedCodec, some ownerReg =>
        match findPaddedSpatialBlock st.memBlocks bid with
        | none => .fail
        | some (blk, restBlocks) =>
          if !pinnedLoanSymCoherent e ownerReg blk restBlocks st.sym then
            .fail
          else
            match mirListGet? st.mirLocalTypes ownerReg with
            | none => .fail
            | some localTy =>
              match targetSpecLayoutAndMask localTy with
              | none => .fail
              | some (specLay, specMask) =>
                let writable : Bool :=
                  match blk.perm with
                  | .readWrite => true
                  | .readOnly => false
                let pinChecksOk : Bool :=
                  Nat.beq blk.originLoan lid &&
                  Nat.beq blk.provenanceTag bid &&
                  witnessMatchesBlock pinnedCodec ownerReg blk &&
                  Nat.beq specLay.size blk.layout.size &&
                  Nat.beq specLay.alignLog2 blk.layout.alignLog2 &&
                  writable &&
                  Nat.beq blk.activeSubSplits 0
                if !pinChecksOk then
                  .fail
                else if !slotMatchesIndirection st.mirLocals ownerReg
                    blk.place ||
                    otherPromotedEntryUsesAlloc ownerReg blk.place.allocId
                      st.promotedLocals ||
                    otherIndirectLocalUsesAlloc ownerReg blk.place.allocId
                      st.mirLocals then
                  .fail
                else if !liveMutSliceValid st.mem blk.place blk.layout then
                  .fail
                else
                  match execReadBytes st.mem blk.place blk.layout.size
                      blk.layout.alignLog2 with
                  | .error _ => .fail
                  | .ok memBytes =>
                    match pinnedCodec.decode
                        [.uninit, .init (.bytes memBytes)] with
                    | none => .fail
                    | some v' =>
                      if !nonPadBytesInitialized specMask memBytes then
                        .fail
                      else if !valCompatWithTargetSpec v' localTy then
                        .fail
                      else if !valAndBytesMatchTargetSpec false localTy v'
                          memBytes then
                        .fail
                      else if !replaceableVal mirValAlg st.sym.loans
                          e.cell.val v' then
                        .fail
                      else
                        let loans' := updateLoan lid
                          (fun x =>
                            ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩)
                          st.sym.loans
                        let sym' : SymState Val :=
                          { st.sym with loans := loans' }
                        .ok { st with sym := sym', memBlocks := restBlocks }
      | _, _ => .fail

/-- Extracts the unique authoritative symbolic `Val` for unpinned local `reg`
in `sym` (either its unborrowed root `.activeMut` loan cell when exclusively
borrowed with no active child loan or region edges, or `sym.locals[reg].val`
when unborrowed with zero active loans or region groups targeting `reg`),
returning `none` whenever `reg` is pinned, shared-borrowed, split-borrowed,
field-path-borrowed, referenced by an active region group, or has active child
loan/region edges. -/
@[expose] def authoritativeSymValForLocal (reg : LocalId)
    (sym : SymState Val) : Option Val :=
  if activeRegionMentionsLocal reg sym.regionGroups then
    none
  else
    let matchingLoans :=
      sym.loans.foldr
        (fun le acc =>
          if !le.phase.isEnded && backTargetMentionsLocal reg le.target then
            le :: acc
          else
            acc)
        []
    match matchingLoans with
    | [] =>
      match mirListGet? sym.locals reg with
      | some cell => if isUnborrowed cell.perm then some cell.val else none
      | none => none
    | [le] =>
      let okRootLoan : Bool :=
        hasUniqueLoanId le.id sym.loans &&
        (match loanDirectLocal? le.target with
         | some r => Nat.beq r reg
         | none => false) &&
        ownerLocalExclusivelyHeldByLoan reg le.id sym &&
        isUnborrowed le.cell.perm &&
        noActiveChildLoanEdgesIn mirValAlg le.id sym.loans &&
        noActiveChildRegionEdges le.id sym.regionGroups &&
        le.phase.isActiveMut
      if okRootLoan then some le.cell.val else none
    | _ :: _ :: _ => none

/-- True iff any active `PaddedSpatialBlock` in `blocks` has `ownerLocal = reg`.
-/
@[expose] def anyBlockTargetsLocal (reg : LocalId)
    (blocks : List PaddedSpatialBlock) : Bool :=
  blocks.foldr (fun b acc => Nat.beq b.ownerLocal reg || acc) false

/-- Extracts the unique `PaddedSpatialBlock` with `ownerLocal = reg` together
with the remaining blocks, returning `none` if absent or duplicated. -/
@[expose] def findUniqueBlockForOwner (blocks : List PaddedSpatialBlock)
    (reg : LocalId) :
    Option (PaddedSpatialBlock × List PaddedSpatialBlock) :=
  let res :=
    blocks.foldr
      (fun b (acc : Bool × Option PaddedSpatialBlock × List PaddedSpatialBlock) =>
        if Nat.beq b.ownerLocal reg then
          match acc.2.1 with
          | some _ => (true, acc.2.1, acc.2.2)
          | none => (acc.1, some b, acc.2.2)
        else
          (acc.1, acc.2.1, b :: acc.2.2))
      (false, none, [])
  if res.1 then none
  else
    match res.2.1 with
    | none => none
    | some found => some (found, res.2.2)

/-- True iff `entry`'s backing allocation is live, zero-offset, matches the
target spec's layout and padding mask, and is either currently pinned by an
authenticated `LoanPhase.spatialPinned` loan in `st.sym.loans` (`mem`
authoritative) or synchronized on all non-padding bytes with
`authoritativeSymValForLocal entry.localReg st.sym`. -/
@[expose] def promotedEntryMemSynced (entry : PromotedLocalEntry)
    (st : PaddedSymMemState) : Bool :=
  Nat.beq entry.place.offset 0 &&
  slotMatchesIndirection st.mirLocals entry.localReg entry.place &&
  !otherPromotedEntryUsesAlloc entry.localReg entry.place.allocId
    st.promotedLocals &&
  !otherIndirectLocalUsesAlloc entry.localReg entry.place.allocId
    st.mirLocals &&
  (match mirListGet? st.mirLocalTypes entry.localReg with
   | some ty => spatialTargetSpecBeq ty entry.localTy
   | none => false) &&
  (match targetSpecLayoutAndMask entry.localTy with
   | some (specLay, specMask) =>
     Nat.beq specLay.size entry.layout.size &&
     Nat.beq specLay.alignLog2 entry.layout.alignLog2 &&
     boolListBeq specMask entry.padMask
   | none => false) &&
  liveMutSliceValid st.mem entry.place entry.layout &&
  if anyBlockTargetsLocal entry.localReg st.memBlocks then
    match findUniquePromotedLocalEntry st.promotedLocals entry.localReg,
          findUniqueBlockForOwner st.memBlocks entry.localReg with
    | some _, some (b, restBlocks) =>
      let writable : Bool :=
        match b.perm with
        | .readWrite => true
        | .readOnly => false
      Nat.beq b.place.allocId entry.place.allocId &&
      Nat.beq b.place.offset entry.place.offset &&
      Nat.beq b.codecId entry.codecId &&
      Nat.beq b.layout.size entry.layout.size &&
      Nat.beq b.layout.alignLog2 entry.layout.alignLog2 &&
      writable &&
      Nat.beq b.activeSubSplits 0 &&
      Nat.beq b.provenanceTag b.blockId &&
      (findPaddedSpatialBlock st.memBlocks b.blockId).isSome &&
      hasUniqueLoanId b.originLoan st.sym.loans &&
      match findLoan b.originLoan st.sym.loans with
      | some le =>
        match le.phase, loanDirectLocal? le.target with
        | .spatialPinned loanBid pinnedCodec, some ownerReg =>
          Nat.beq loanBid b.blockId &&
          Nat.beq ownerReg entry.localReg &&
          pinnedLoanSymCoherent le ownerReg b restBlocks st.sym &&
          witnessMatchesBlock pinnedCodec ownerReg b
        | _, _ => false
      | none => false
    | _, _ => false
  else
    match authoritativeSymValForLocal entry.localReg st.sym with
    | none => false
    | some symVal =>
      match entry.encodeSymToMem symVal with
      | none => false
      | some expectedBytes =>
        if Nat.beq entry.layout.size 0 then
          Nat.beq expectedBytes.length 0 &&
          valAndBytesMatchTargetSpec false entry.localTy symVal []
        else
          match execReadBytes st.mem entry.place entry.layout.size
              entry.layout.alignLog2 with
          | .error _ => false
          | .ok curBytes =>
            nonPadBytesInitialized entry.padMask curBytes &&
            sameAtNonPad entry.padMask curBytes expectedBytes &&
            valAndBytesMatchTargetSpec false entry.localTy symVal curBytes

/-- True iff `locals[reg]` is initialized (`.immediate (some _)` or
`.indirect _`), rejecting `.dead`, `.immediate none`, and out-of-range
indices. -/
@[expose] def mirSlotInitialized (locals : List LocalSlot) (reg : LocalId) :
    Bool :=
  match mirListGet? locals reg with
  | some (.immediate (some _)) | some (.indirect _) => true
  | _ => false

/-- True iff `t` mentions only initialized MIR locals (`mirSlotInitialized`). -/
@[expose] def backTargetOnlyMentionsInitLocals (locals : List LocalSlot)
    (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun s acc =>
      let okStep : Bool :=
        match s with
        | .direct (.localReg r) _ => mirSlotInitialized locals r
        | .lensCall targets _ =>
          targets.foldr
            (fun tp tAcc =>
              match tp.1 with
              | .localReg r => mirSlotInitialized locals r && tAcc
              | .parentLoan _ => tAcc)
            true
        | _ => true
      okStep && acc)
    true

/-- True iff no non-ended loan or active region group in `sym` targets a
`.dead`, `.immediate none`, or out-of-range MIR local in `mirLocals`. -/
@[expose] def noActiveBorrowTargetsDeadOrUninit (mirLocals : List LocalSlot)
    (sym : SymState Val) : Bool :=
  sym.loans.foldr
    (fun le acc =>
      (if le.phase.isEnded then true
       else backTargetOnlyMentionsInitLocals mirLocals le.target) && acc)
    true &&
  sym.regionGroups.foldr
    (fun rg acc =>
      (if !rg.active then true
       else
         rg.inputTargets.foldr
           (fun tp tAcc =>
             match tp.1 with
             | .localReg r => mirSlotInitialized mirLocals r && tAcc
             | .parentLoan _ => tAcc)
           true) && acc)
    true

/-- True iff `sym.locals[reg]` is cleared to `⟨.unit, .unborrowed⟩` with zero
active loans or region groups targeting `reg`. -/
@[expose] def symSlotClearedToUnit (reg : LocalId) (sym : SymState Val) : Bool
    :=
  !activeRegionMentionsLocal reg sym.regionGroups &&
  !sym.loans.foldr
    (fun le acc =>
      (!le.phase.isEnded && backTargetMentionsLocal reg le.target) || acc)
    false &&
  match mirListGet? sym.locals reg with
  | some cell => isUnborrowed cell.perm && mirValBeqAt 8 cell.val .unit
  | none => false

/-- True iff every `LocalSlot.indirect` in `mirLocals` is backed by a unique
matching `PromotedLocalEntry` in `entries`, every `.dead` and `.immediate none`
slot is unpromoted, unpinned, and cleared to `⟨.unit, .unborrowed⟩` in `sym`
with no active borrows (`symSlotClearedToUnit`), and every initialized
`LocalSlot.immediate (some mv)` satisfies
`immValCompatWithTargetSpec mv mirLocalTypes[idx]` and agrees with
`authoritativeSymValForLocal` whenever `sym` holds a unique authoritative value
for that local. -/
@[expose] def everySlotCoherentWithSym (mirLocalTypes : List SpatialTargetSpec)
    (mirLocals : List LocalSlot)
    (entries : List PromotedLocalEntry) (blocks : List PaddedSpatialBlock)
    (sym : SymState Val) : Bool :=
  noActiveBorrowTargetsDeadOrUninit mirLocals sym &&
  (mirLocals.foldr
    (fun slot k idx =>
      let okHere : Bool :=
        match slot with
        | .indirect mp =>
          match findUniquePromotedLocalEntry entries idx with
          | some (e, _) =>
            Nat.beq e.place.allocId mp.allocId &&
            Nat.beq e.place.offset mp.offset
          | none => false
        | .immediate optVal =>
          !hasPromotedLocalEntry idx entries &&
          !anyBlockTargetsLocal idx blocks &&
          match optVal with
          | none => symSlotClearedToUnit idx sym
          | some mv =>
            (match mirListGet? mirLocalTypes idx with
             | some ty => immValCompatWithTargetSpec mv ty
             | none => false) &&
            match authoritativeSymValForLocal idx sym with
            | some sv => mirValBeqAt 8 mv sv
            | none => true
        | .dead =>
          !hasPromotedLocalEntry idx entries &&
          !anyBlockTargetsLocal idx blocks &&
          symSlotClearedToUnit idx sym
        | .partialTuple _ => false
      okHere && k (idx + 1))
    (fun _ => true)
    0)

/-- Structural pre-check verifying that every `LocalSlot.indirect` in
`mirLocals` has a unique matching `PromotedLocalEntry`. -/
@[expose] def everyIndirectSlotTracked (mirLocals : List LocalSlot)
    (entries : List PromotedLocalEntry) : Bool :=
  (mirLocals.foldr
    (fun slot k idx =>
      let okHere : Bool :=
        match slot with
        | .indirect mp =>
          match findUniquePromotedLocalEntry entries idx with
          | some (e, _) =>
            Nat.beq e.place.allocId mp.allocId &&
            Nat.beq e.place.offset mp.offset
          | none => false
        | .dead | .immediate _ | .partialTuple _ => true
      okHere && k (idx + 1))
    (fun _ => true)
    0)

/-- Refreshes every initialized unpromoted `LocalSlot.immediate (some _)` in
`mirLocals` whose `authoritativeSymValForLocal` is `some sv` to `.immediate
(some sv)`. -/
@[expose] def refreshImmediateMirLocals (mirLocals : List LocalSlot)
    (sym : SymState Val) : List LocalSlot :=
  mirLocals.foldr
    (fun slot k idx =>
      let slot' : LocalSlot :=
        match slot with
        | .immediate (some _) =>
          match authoritativeSymValForLocal idx sym with
          | some sv => .immediate (some sv)
          | none => slot
        | _ => slot
      slot' :: k (idx + 1))
    (fun _ => [])
    0

/-- Global authority and synchronization check across captured `BodySpatialCtx`
type authentication (`specsMatchBodyCtx`), all promoted `LocalSlot.indirect`
allocations, active `st.memBlocks` (including verifying that every block owns a
tracked `PromotedLocalEntry` and carries a unique `blockId`), and unpromoted
`LocalSlot.immediate` and `.dead` locals in `st`. -/
@[expose] def allPromotedLocalsMemSynced (ctx : BodySpatialCtx)
    (st : PaddedSymMemState) : Bool :=
  specsMatchBodyCtx ctx st.mirLocalTypes &&
  Nat.beq st.mirLocalTypes.length st.mirLocals.length &&
  Nat.beq st.sym.locals.length st.mirLocals.length &&
  everySlotCoherentWithSym st.mirLocalTypes st.mirLocals st.promotedLocals
    st.memBlocks st.sym &&
  st.memBlocks.foldr
    (fun b acc =>
      hasPromotedLocalEntry b.ownerLocal st.promotedLocals &&
      (findPaddedSpatialBlock st.memBlocks b.blockId).isSome &&
      acc)
    true &&
  st.promotedLocals.foldr
    (fun entry acc => promotedEntryMemSynced entry st && acc)
    true

/-- Refreshes both initialized `LocalSlot.immediate` slots in `st.mirLocals` and
unpinned `PromotedLocalEntry` allocations in `st.mem` from
`authoritativeSymValForLocal`, preserving clean padding bytes when non-padding
bytes already agree and padding carries no provenance. -/
@[expose] def syncPromotedLocalsToMem (ctx : BodySpatialCtx) (st :
    PaddedSymMemState) :
    EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length ||
     !everyIndirectSlotTracked st.mirLocals st.promotedLocals then
    .fail
  else
    let mirLocalsSynced := refreshImmediateMirLocals st.mirLocals st.sym
    let memRes : Option MemoryState :=
      st.promotedLocals.foldr
        (fun entry accOpt =>
          match accOpt with
          | none => none
          | some curMem =>
            if !slotMatchesIndirection mirLocalsSynced entry.localReg
                 entry.place ||
               !liveMutSliceValid curMem entry.place entry.layout then
              none
            else if anyBlockTargetsLocal entry.localReg st.memBlocks then
              if promotedEntryMemSynced entry
                  { st with mirLocals := mirLocalsSynced, mem := curMem } then
                some curMem
              else
                none
            else
              match authoritativeSymValForLocal entry.localReg st.sym with
              | none => none
              | some symVal =>
                match entry.encodeSymToMem symVal with
                | none => none
                | some expectedBytes =>
                  if Nat.beq entry.layout.size 0 then
                    if Nat.beq expectedBytes.length 0 &&
                       valAndBytesMatchTargetSpec false entry.localTy symVal [] then
                      some curMem
                    else
                      none
                  else
                    match execReadBytes curMem entry.place entry.layout.size
                        entry.layout.alignLog2 with
                    | .error _ => none
                    | .ok curBytes =>
                      if nonPadBytesInitialized entry.padMask curBytes &&
                         sameAtNonPad entry.padMask curBytes expectedBytes &&
                         valAndBytesMatchTargetSpec false entry.localTy
                           symVal curBytes then
                        some curMem
                      else
                        match execWriteBytes curMem entry.place
                            entry.layout.alignLog2 expectedBytes with
                        | .ok nextMem => some nextMem
                        | .error _ => none)
        (some st.mem)
    match memRes with
    | none => .fail
    | some memSynced =>
      let st' := { st with mirLocals := mirLocalsSynced, mem := memSynced }
      if allPromotedLocalsMemSynced ctx st' then .ok st' else .fail

/-- Performs a PureLift symbolic place write (`writePlaceVal`), rejecting writes
targeting `.dead` locals or sub-path projections of uninitialized
`.immediate none` locals while allowing whole-local `.localSub reg []`
assignments of `immValCompatWithTargetSpec` values to initialize an unpromoted
`.immediate none` MIR slot, and synchronizes `st.mirLocals` and `st.mem`. -/
@[expose] def writePaddedSymPlace (ctx : BodySpatialCtx) (pe : PlaceExpr)
    (newVal : Val)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length ||
     !noActiveBorrowTargetsDeadOrUninit st.mirLocals st.sym then
    .fail
  else
    match pe with
    | .localSub reg [] =>
      match mirListGet? st.mirLocals reg with
      | some (.immediate none) =>
        if hasPromotedLocalEntry reg st.promotedLocals ||
           anyBlockTargetsLocal reg st.memBlocks then
          .fail
        else
          match mirListGet? st.mirLocalTypes reg with
          | none => .fail
          | some ty =>
            if !immValCompatWithTargetSpec newVal ty then
              .fail
            else
              match writePlaceVal mirValAlg pe newVal st.sym,
                    mirListSet? st.mirLocals reg (.immediate (some newVal)) with
              | some sym', some mirLocalsInit =>
                if !Nat.beq sym'.locals.length st.mirLocals.length then .fail
                else
                  syncPromotedLocalsToMem ctx
                    { st with sym := sym', mirLocals := mirLocalsInit }
              | _, _ => .fail
      | some (.immediate (some _)) | some (.indirect _) =>
        match writePlaceVal mirValAlg pe newVal st.sym with
        | none => .fail
        | some sym' =>
          if !Nat.beq sym'.locals.length st.mirLocals.length then .fail
          else syncPromotedLocalsToMem ctx { st with sym := sym' }
      | some .dead | some (.partialTuple _) | none => .fail
    | .localSub reg (_ :: _) =>
      if !mirSlotInitialized st.mirLocals reg then .fail
      else
        match writePlaceVal mirValAlg pe newVal st.sym with
        | none => .fail
        | some sym' =>
          if !Nat.beq sym'.locals.length st.mirLocals.length then .fail
          else syncPromotedLocalsToMem ctx { st with sym := sym' }
    | .derefSub handleReg _ =>
      if !mirSlotInitialized st.mirLocals handleReg then .fail
      else
        match writePlaceVal mirValAlg pe newVal st.sym with
        | none => .fail
        | some sym' =>
          if !Nat.beq sym'.locals.length st.mirLocals.length then .fail
          else syncPromotedLocalsToMem ctx { st with sym := sym' }

/-- Ends PureLift loan `lid` (`endLoanInState`) after verifying that no active
loan or region group targets a `.dead` or `.immediate none` MIR local, and
synchronizes both initialized `LocalSlot.immediate` MIR locals and unpinned
promoted `LocalSlot.indirect` allocations in `st.mem`. -/
@[expose] def endPaddedLoan (ctx : BodySpatialCtx) (lid : LoanId)
    (st : PaddedSymMemState) : EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length ||
     !Nat.beq st.sym.locals.length st.mirLocals.length ||
     !noActiveBorrowTargetsDeadOrUninit st.mirLocals st.sym then
    .fail
  else
    match endLoanInState mirValAlg lid st.sym with
    | .fail => .fail
    | .ok sym' => syncPromotedLocalsToMem ctx { st with sym := sym' }

/-- Authority-checked MIR primitive operand evaluator over `PaddedSymMemState`:
rejects stale, split-borrowed, shared-borrowed, type-spoofed, or untracked MIR
reads with `.error .unsupported` whenever `!allPromotedLocalsMemSynced ctx st`
(or when copying an `.immediate` local without `authoritativeSymValForLocal`),
rejects `Operand.move` with `.error .unsupported` so MIR moves cannot silently
desynchronize `mirLocals` or `mem` from `sym`, and otherwise delegates directly
to `execEvalPrimitiveOperand ctx.body.locals` (`Trusted.MirSemantics`'s
`evalPrimitiveOperand` over captured `Body.locals`, which continues to report
concrete Rust UB such as dead or uninitialized reads as `.error .undefined`). -/
@[expose] def evalPaddedMirOperand (ctx : BodySpatialCtx) (st :
    PaddedSymMemState)
    (opnd : Operand) : Except FaultKind (Val × PaddedSymMemState) :=
  if !allPromotedLocalsMemSynced ctx st then
    .error .unsupported
  else
    match opnd with
    | .move _ => .error .unsupported
    | .copy place =>
      let immLocked : Bool :=
        match mirListGet? st.mirLocals place.localId with
        | some (.immediate (some _)) =>
          (authoritativeSymValForLocal place.localId st.sym).isNone
        | _ => false
      if immLocked then
        .error .unsupported
      else
        match execEvalPrimitiveOperand ctx.body.locals st.mirLocals st.mem
            opnd with
        | .error k => .error k
        | .ok (v, mirLocals', mem') =>
          .ok (v, { st with mirLocals := mirLocals', mem := mem' })
    | .constant _ =>
      match execEvalPrimitiveOperand ctx.body.locals st.mirLocals st.mem
          opnd with
      | .error k => .error k
      | .ok (v, mirLocals', mem') =>
        .ok (v, { st with mirLocals := mirLocals', mem := mem' })

/-- Deallocates an unpinned, unborrowed promoted `LocalSlot.indirect` stack
allocation upon `StorageDead reg` (`reg ≠ 0`), clearing `sym.locals[reg]` to
`⟨.unit, .unborrowed⟩`, setting `mirLocals[reg] := .dead`, removing `reg` from
`promotedLocals`, and failing closed if `specsMatchBodyCtx` fails, if any active
or pinned loan targets `reg`, or if any symbolic or memory reservoir
(`memBlocks`, `promotedLocals`, `mirLocals`, `sym.locals`, `sym.loans`,
`sym.spatial`, `sym.regionDeposits`, active `sym.regionGroups`, or live
`mem.allocations`) references `place.allocId`. -/
@[expose] def deallocatePromotedLocal
    (ctx : BodySpatialCtx) (reg : LocalId) (st : PaddedSymMemState) :
    EvalOutcome PaddedSymMemState :=
  if !specsMatchBodyCtx ctx st.mirLocalTypes ||
     !Nat.beq st.mirLocalTypes.length st.mirLocals.length then .fail
  else if Nat.beq reg 0 then .fail
  else
    match mirListGet? st.mirLocals reg, mirListGet? st.sym.locals reg with
    | some (.indirect place), some symCell =>
      let nonEndedTargetsReg : Bool :=
        st.sym.loans.foldr
          (fun le acc =>
            (!le.phase.isEnded && backTargetMentionsLocal reg le.target) || acc)
          false
      let safeToDealloc : Bool :=
        Nat.beq place.offset 0 &&
        isUnborrowed symCell.perm &&
        !nonEndedTargetsReg &&
        allocExclusivelyOwnedByLocal reg place.allocId st
      if !safeToDealloc then
        .fail
      else
        match execDeallocateStack st.mem place with
        | .error _ => .fail
        | .ok memDealloc =>
          match mirListSet? st.mirLocals reg .dead,
                mirListSet? st.sym.locals reg ⟨.unit, .unborrowed⟩ with
          | some mirLocals', some symLocals' =>
            .ok { st with
              sym := { st.sym with locals := symLocals' }
              mirLocals := mirLocals'
              mem := memDealloc
              promotedLocals := removePromotedLocalEntry reg st.promotedLocals }
          | _, _ => .fail
    | _, _ => .fail

/-! ### Padded Aggregate and Pointer-Provenance Codecs -/

private theorem bitVec_ofNat_toNat (w : Nat) (x : BitVec w) :
    BitVec.ofNat w x.toNat = x := by
  cases x with
  | ofFin f =>
    cases f with
    | mk v hv =>
      have hMod : Nat.mod v (Nat.pow 2 w) = v := natMod_eq_of_lt hv
      have hFinGen :
          ∀ (a : Nat) (ha : a < Nat.pow 2 w),
            a = v → (Fin.mk a ha : Fin (Nat.pow 2 w)) = Fin.mk v hv := by
        intro a ha hEq
        subst hEq
        rfl
      exact congrArg BitVec.ofFin
        (hFinGen (Nat.mod v (Nat.pow 2 w))
          (Nat.mod_lt v (Nat.pow_pos (Nat.zero_lt_succ 1))) hMod)

private theorem uint8_ofNat_toNat (b : UInt8) :
    UInt8.ofNat b.toNat = b := by
  cases b with
  | ofBitVec bv => exact congrArg UInt8.ofBitVec (bitVec_ofNat_toNat 8 bv)

/-- `(BitVec.ofNat 128 n).toNat = n` whenever `n < bound ≤ 2^128`. -/
theorem bitVec128_ofNat_toNat_lt (n bound : Nat)
    (hLt : n < bound) (hBound : bound ≤ Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n := by
  change Nat.mod n (Nat.pow 2 128) = n
  exact natMod_eq_of_lt (Nat.lt_of_lt_of_le hLt hBound)

private theorem uint8_eq_of_toNat_eq (x y : UInt8) (h : x.toNat = y.toNat) : x = y := by
  have hx := uint8_ofNat_toNat x
  have hy := uint8_ofNat_toNat y
  rw [← hx, ← hy, h]

private theorem allocByteBeq_true_init_val (bx by_ : UInt8) (px py : Option AllocId)
    (h : allocByteBeq (.init bx px) (.init by_ py) = true) : bx = by_ := by
  dsimp only [allocByteBeq] at h
  cases hN : Nat.beq bx.toNat by_.toNat with
  | false =>
    rw [hN] at h
    exact False.elim (boolFalseNeTrue h)
  | true => exact uint8_eq_of_toNat_eq bx by_ (natEq_of_beq bx.toNat by_.toNat hN)

private theorem allocByteBeq_true_init_prov (bx by_ : UInt8) (px py : Option AllocId)
    (h : allocByteBeq (.init bx px) (.init by_ py) = true) : px = py := by
  dsimp only [allocByteBeq] at h
  cases hN : Nat.beq bx.toNat by_.toNat with
  | false => rw [hN] at h; nomatch h
  | true =>
    rw [hN, Bool.true_and] at h
    cases px with
    | none =>
      cases py with
      | none => rfl
      | some _ => nomatch h
    | some a =>
      cases py with
      | none => nomatch h
      | some b => exact congrArg Option.some (natEq_of_beq a b h)

private theorem listReverseAux_len_add {α : Type} :
    ∀ (xs acc : List α), (List.reverseAux xs acc).length = xs.length + acc.length
  | [], _ => (Nat.zero_add _).symm
  | _ :: xs, acc => by
    change (List.reverseAux xs (_ :: acc)).length = (xs.length + 1) + acc.length
    rw [listReverseAux_len_add xs (_ :: acc)]
    change xs.length + (acc.length + 1) = (xs.length + 1) + acc.length
    rw [Nat.add_assoc, Nat.add_comm 1 acc.length, ← Nat.add_assoc]

private theorem execNatOfLeBytes_lt_pow :
    ∀ (xs : List UInt8), execNatOfLeBytes xs < Nat.pow 256 xs.length
  | [] => Nat.zero_lt_succ 0
  | b :: rest => by
    have hB : b.toNat < 256 := b.toBitVec.isLt
    have hRest : execNatOfLeBytes rest < Nat.pow 256 rest.length :=
      execNatOfLeBytes_lt_pow rest
    have hStep1 :
        b.toNat + 256 * execNatOfLeBytes rest <
          256 + 256 * execNatOfLeBytes rest :=
      Nat.add_lt_add_right hB (256 * execNatOfLeBytes rest)
    have hEqMul :
        256 * (execNatOfLeBytes rest + 1) =
          256 * execNatOfLeBytes rest + 256 :=
      Nat.mul_succ 256 (execNatOfLeBytes rest)
    have hComm :
        256 + 256 * execNatOfLeBytes rest =
          256 * execNatOfLeBytes rest + 256 :=
      Nat.add_comm 256 (256 * execNatOfLeBytes rest)
    have hLeMul :
        256 * (execNatOfLeBytes rest + 1) ≤
          256 * Nat.pow 256 rest.length :=
      Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hRest)
    have hPowSucc :
        Nat.pow 256 (rest.length + 1) = 256 * Nat.pow 256 rest.length :=
      Nat.mul_comm (Nat.pow 256 rest.length) 256
    change b.toNat + 256 * execNatOfLeBytes rest <
      Nat.pow 256 (rest.length + 1)
    rw [hPowSucc]
    rw [hComm, ← hEqMul] at hStep1
    exact Nat.lt_of_lt_of_le hStep1 hLeMul

private theorem execDecodeUInt_lt_pow (endian : TargetEndian)
    (xs : List UInt8) :
    execDecodeUInt endian xs < Nat.pow 256 xs.length := by
  cases endian with
  | little => exact execNatOfLeBytes_lt_pow xs
  | big =>
    have hRevLen : xs.reverse.length = xs.length := by
      change (List.reverseAux xs []).length = xs.length
      rw [listReverseAux_len_add xs []]
      rfl
    change execNatOfLeBytes xs.reverse < Nat.pow 256 xs.length
    rw [← hRevLen]
    exact execNatOfLeBytes_lt_pow xs.reverse

private theorem execLeBytesOfNat_execNatOfLeBytes :
    ∀ (xs : List UInt8),
      execLeBytesOfNat xs.length (execNatOfLeBytes xs) = xs
  | [] => rfl
  | b :: rest => by
    change UInt8.ofNat (Nat.mod (b.toNat + 256 * execNatOfLeBytes rest) 256) ::
        execLeBytesOfNat rest.length
          (Nat.div (b.toNat + 256 * execNatOfLeBytes rest) 256) = b :: rest
    have h256 : 0 < 256 := Nat.zero_lt_succ 255
    have hBLt : b.toNat < 256 := b.toBitVec.isLt
    have hMod :
        Nat.mod (b.toNat + 256 * execNatOfLeBytes rest) 256 = b.toNat :=
      Eq.trans (Nat.add_mul_mod_self_left b.toNat 256 (execNatOfLeBytes rest))
        (Nat.mod_eq_of_lt hBLt)
    have hDiv :
        Nat.div (b.toNat + 256 * execNatOfLeBytes rest) 256 =
          execNatOfLeBytes rest := by
      have h1 :
          Nat.div (b.toNat + 256 * execNatOfLeBytes rest) 256 =
            Nat.div b.toNat 256 + execNatOfLeBytes rest :=
        Nat.add_mul_div_left b.toNat (execNatOfLeBytes rest) h256
      have h2 : Nat.div b.toNat 256 = 0 := Nat.div_eq_of_lt hBLt
      rw [h1, h2, Nat.zero_add]
    rw [hMod, uint8_ofNat_toNat b, hDiv,
      execLeBytesOfNat_execNatOfLeBytes rest]

private theorem listReverseAux_reverseAux {α : Type} :
    ∀ (xs acc ys : List α),
      List.reverseAux (List.reverseAux xs acc) ys =
        List.reverseAux acc (xs ++ ys)
  | [], _, _ => rfl
  | x :: xs, acc, ys => listReverseAux_reverseAux xs (x :: acc) ys

private theorem listReverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  change List.reverseAux (List.reverseAux xs []) [] = xs
  rw [listReverseAux_reverseAux xs [] []]
  exact listAppend_nil_right xs

private theorem execEncodeUInt_execDecodeUInt (endian : TargetEndian)
    (xs : List UInt8) :
    execEncodeUInt endian xs.length (execDecodeUInt endian xs) = xs := by
  cases endian with
  | little => exact execLeBytesOfNat_execNatOfLeBytes xs
  | big =>
    have hRevLen : xs.reverse.length = xs.length := by
      change (List.reverseAux xs []).length = xs.length
      rw [listReverseAux_len_add xs []]
      rfl
    change (execLeBytesOfNat xs.length (execNatOfLeBytes xs.reverse)).reverse = xs
    rw [← hRevLen, execLeBytesOfNat_execNatOfLeBytes xs.reverse,
      listReverse_reverse]

private theorem sameAtNonPad_allFalse_refl :
    ∀ (k : Nat) (bs : List AllocByte),
      bs.length = k → sameAtNonPad (List.replicate k false) bs bs = true
  | 0, [], _ => rfl
  | 0, _ :: _, h => nomatch h
  | _ + 1, [], h => nomatch h
  | k + 1, x :: xs, h => by
    injection h with hTail
    change (allocByteBeq x x &&
      sameAtNonPad (List.replicate k false) xs xs) = true
    rw [allocByteBeq_refl x, sameAtNonPad_allFalse_refl k xs hTail]
    rfl

/-- Padded `#[repr(C)]` `(u8, [pad; 3], u32)` payload with 8-byte size and
4-byte alignment (`alignLog2 = 2`). -/
structure U8U32Struct where
  aByte : UInt8
  bVal : BitVec 32

/-- Padding mask for `U8U32Struct` (bytes `1..3` are padding). -/
@[expose] def u8PadU32Mask : List Bool :=
  [false, true, true, true, false, false, false, false]

/-- Encodes `U8U32Struct` into 8 `AllocByte`s with `.uninit` at `1..3`. -/
@[expose] def paddedU8U32Encode (s : U8U32Struct) : List AllocByte :=
  [AllocByte.init s.aByte none, .uninit, .uninit, .uninit] ++
  (execEncodeUInt execProfileTargetEndian 4 s.bVal.toNat).map (fun b => AllocByte.init b none)

/-- Decodes `U8U32Struct` from 8 `AllocByte`s, requiring `prov = none` on all
non-padding bytes and ignoring padding bytes `1..3`. -/
@[expose] def paddedU8U32Decode (bytes : List AllocByte) : Option U8U32Struct :=
  match bytes with
  | [] => none
  | c0 :: r1 =>
    match r1 with
    | [] => none
    | _ :: r2 =>
      match r2 with
      | [] => none
      | _ :: r3 =>
        match r3 with
        | [] => none
        | _ :: r4 =>
          match r4 with
          | [] => none
          | c4 :: r5 =>
            match r5 with
            | [] => none
            | c5 :: r6 =>
              match r6 with
              | [] => none
              | c6 :: r7 =>
                match r7 with
                | [] => none
                | c7 :: r8 =>
                  match r8 with
                  | _ :: _ => none
                  | [] =>
                    match allocByteNoProvOpt c0 with
                    | none => none
                    | some aB =>
                      match allocByteNoProvOpt c4 with
                      | none => none
                      | some b0 =>
                        match allocByteNoProvOpt c5 with
                        | none => none
                        | some b1 =>
                          match allocByteNoProvOpt c6 with
                          | none => none
                          | some b2 =>
                            match allocByteNoProvOpt c7 with
                            | none => none
                            | some b3 =>
                              some ⟨aB,
                                BitVec.ofNat 32
                                  (execDecodeUInt execProfileTargetEndian [b0, b1, b2, b3])⟩

/-- Encodes `U8U32Struct` as a 2-field `Val.tuple` of `(u8, u32)` scalars. -/
@[expose] def paddedU8U32ToSymVal (s : U8U32Struct) : Val :=
  Val.tuple
    [ .scalar ⟨.i8, false, BitVec.ofNat 128 s.aByte.toNat⟩
    , .scalar ⟨.i32, false, BitVec.ofNat 128 s.bVal.toNat⟩ ]

/-- Decodes `U8U32Struct` from a canonical `(u8, u32)` `Val.tuple`. -/
@[expose] def paddedU8U32FromSymVal (v : Val) : Option U8U32Struct :=
  match v with
  | .tuple fs =>
    match fs with
    | [] | [_] | _ :: _ :: _ :: _ => none
    | f0 :: [f1] =>
      match f0 with
      | .scalar sa =>
        match f1 with
        | .scalar sb =>
          match sa.width with
          | .i8 =>
            match sb.width with
            | .i32 =>
              if !sa.signed && Nat.blt sa.bits.toNat 256 &&
                 !sb.signed && Nat.blt sb.bits.toNat 4294967296 then
                some ⟨UInt8.ofNat sa.bits.toNat, BitVec.ofNat 32 sb.bits.toNat⟩
              else
                none
            | .i8 | .i16 | .i64 | .i128 | .isize => none
          | .i16 | .i32 | .i64 | .i128 | .isize => none
        | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
        | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
        | .bytes _ =>
          none
      | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
      | .bytes _ =>
        none
  | .scalar _ | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _
  | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
  | .bytes _ =>
    none

private theorem mirCheckVal_u8_ofNat {n : Nat} (hn : n < 256) :
    mirCheckVal (.scalar ⟨.i8, false, BitVec.ofNat 128 n⟩) (.int .i8 false) =
      true := by
  have hPow128 : 256 ≤ Nat.pow 2 128 := natLe_of_ble 256 (Nat.pow 2 128) rfl
  have hPow8 : (256 : Nat) = Nat.pow 2 8 := rfl
  have hBv128 : (BitVec.ofNat 128 n).toNat = n :=
    bitVec128_ofNat_toNat_lt n 256 hn hPow128
  have hShift0 : Nat.shiftRight n 0 = n := rfl
  have hMod8 : (BitVec.ofNat 8 (Nat.shiftRight n 0)).toNat = n := by
    rw [hShift0]
    change Nat.mod n (Nat.pow 2 8) = n
    rw [← hPow8]
    exact natMod_eq_of_lt hn
  have hTr :
      mirTruncateBits .i8 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
    dsimp only [mirTruncateBits, mirBitWidth]
    rw [hBv128, hMod8]
  have hWf :
      mirScalarWf ⟨.i8, false, BitVec.ofNat 128 n⟩ = true := by
    dsimp only [mirScalarWf]
    rw [hTr]
    dsimp only [BEq.beq]
    exact decide_eq_true (rfl : BitVec.ofNat 128 n = BitVec.ofNat 128 n)
  dsimp only [mirCheckVal, mirValTy?]
  rw [hWf]
  rfl

private theorem mirCheckVal_u32_ofNat {n : Nat} (hn : n < 4294967296) :
    mirCheckVal (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩) (.int .i32 false) =
      true := by
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
    natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hPow32 : (4294967296 : Nat) = Nat.pow 2 32 := rfl
  have hBv128 : (BitVec.ofNat 128 n).toNat = n :=
    bitVec128_ofNat_toNat_lt n 4294967296 hn hPow128
  have hShift0 : Nat.shiftRight n 0 = n := rfl
  have hMod32 : (BitVec.ofNat 32 (Nat.shiftRight n 0)).toNat = n := by
    rw [hShift0]
    change Nat.mod n (Nat.pow 2 32) = n
    rw [← hPow32]
    exact natMod_eq_of_lt hn
  have hTr :
      mirTruncateBits .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
    dsimp only [mirTruncateBits, mirBitWidth]
    rw [hBv128, hMod32]
  have hWf :
      mirScalarWf ⟨.i32, false, BitVec.ofNat 128 n⟩ = true := by
    dsimp only [mirScalarWf]
    rw [hTr]
    dsimp only [BEq.beq]
    exact decide_eq_true (rfl : BitVec.ofNat 128 n = BitVec.ofNat 128 n)
  dsimp only [mirCheckVal, mirValTy?]
  rw [hWf]
  rfl

private theorem listTake_of_len {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.length = n → xs.take n = xs
  | [], 0, _ => rfl
  | _ :: _, 0, h => nomatch h
  | [], _ + 1, h => nomatch h
  | x :: xs, n + 1, h => by
    injection h with hTail
    exact congrArg (List.cons x) (listTake_of_len xs n hTail)

private theorem listDrop_of_len {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.length = n → xs.drop n = []
  | [], 0, _ => rfl
  | _ :: _, 0, h => nomatch h
  | [], _ + 1, h => nomatch h
  | _ :: xs, n + 1, h => by
    injection h with hTail
    exact listDrop_of_len xs n hTail

private theorem sliceAllInitNoProv_map_none (xs : List UInt8) :
    sliceAllInitNoProv (xs.map (fun b => AllocByte.init b none)) = true := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem sliceAllInitOptProv_map_some (xs : List UInt8) (p : AllocId) :
    sliceAllInitOptProv (xs.map (fun b => AllocByte.init b (some p))) (some p) =
      true := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    change (Nat.beq p p &&
      sliceAllInitOptProv (_) (some p)) = true
    rw [natBeq_refl p, Bool.true_and]
    exact ih

/-- Audited `SpatialTargetSpec` for `U8U32Struct` (`#[repr(C)]` `(u8, u32)` at
offsets `0` and `4`). -/
@[expose] def u8U32TargetSpec : SpatialTargetSpec :=
  .reprCAdt 8032 [⟨0, .int .i8 false⟩, ⟨4, .int .i32 false⟩]

/-- `TypedSpatialMemCodec` for `U8U32Struct` (`(u8, [pad; 3], u32)`). -/
@[expose] def paddedU8U32MemCodec : TypedSpatialMemCodec U8U32Struct where
  codecId := 8032
  targetTy := u8U32TargetSpec
  layout := ⟨8, 2⟩
  padMask := u8PadU32Mask
  encodeValToMem := paddedU8U32Encode
  decodeValFromMem := paddedU8U32Decode
  provCheck := fun _ => true
  encodeToSymVal := paddedU8U32ToSymVal
  decodeFromSymVal := paddedU8U32FromSymVal

/-- Decodes an 8-byte `U8U32Struct` slice across arbitrary padding `c1..c3`. -/
theorem paddedU8U32Decode_of_raw4 (aB : UInt8) (c1 c2 c3 : AllocByte)
    (xs : List UInt8) (hLen : xs.length = 4) :
    paddedU8U32Decode ([AllocByte.init aB none, c1, c2, c3] ++ xs.map (fun b => AllocByte.init b none)) =
      some ⟨aB, BitVec.ofNat 32 (execDecodeUInt execProfileTargetEndian xs)⟩ := by
  cases xs with
  | nil => nomatch hLen
  | cons x0 r1 =>
    cases r1 with
    | nil => nomatch hLen
    | cons x1 r2 =>
      cases r2 with
      | nil => nomatch hLen
      | cons x2 r3 =>
        cases r3 with
        | nil => nomatch hLen
        | cons x3 r4 =>
          cases r4 with
          | cons _ _ => nomatch hLen
          | nil => rfl

/-- Four `.init` bytes satisfy `nonPadBytesInitialized` on `[false; 4]`. -/
theorem nonPad_map_init4 (xs : List UInt8) (hLen : xs.length = 4) :
    nonPadBytesInitialized [false, false, false, false]
      (xs.map (fun b => AllocByte.init b none)) = true := by
  cases xs with
  | nil => nomatch hLen
  | cons _ r1 =>
    cases r1 with
    | nil => nomatch hLen
    | cons _ r2 =>
      cases r2 with
      | nil => nomatch hLen
      | cons _ r3 =>
        cases r3 with
        | nil => nomatch hLen
        | cons _ r4 =>
          cases r4 with
          | cons _ _ => nomatch hLen
          | nil => rfl

private theorem sameAtNonPad_u8u32_eq (b1 b2 : List AllocByte)
    (hL1 : b1.length = 8) (hL2 : b2.length = 8)
    (hSame : sameAtNonPad u8PadU32Mask b1 b2 = true) :
    paddedU8U32Decode b1 = paddedU8U32Decode b2 := by
  cases b1 with | nil => nomatch hL1 | cons a0 as1 =>
  cases as1 with | nil => nomatch hL1 | cons a1 as2 =>
  cases as2 with | nil => nomatch hL1 | cons a2 as3 =>
  cases as3 with | nil => nomatch hL1 | cons a3 as4 =>
  cases as4 with | nil => nomatch hL1 | cons a4 as5 =>
  cases as5 with | nil => nomatch hL1 | cons a5 as6 =>
  cases as6 with | nil => nomatch hL1 | cons a6 as7 =>
  cases as7 with | nil => nomatch hL1 | cons a7 as8 =>
  cases as8 with | cons _ _ => nomatch hL1 | nil =>
  cases b2 with | nil => nomatch hL2 | cons c0 cs1 =>
  cases cs1 with | nil => nomatch hL2 | cons c1 cs2 =>
  cases cs2 with | nil => nomatch hL2 | cons c2 cs3 =>
  cases cs3 with | nil => nomatch hL2 | cons c3 cs4 =>
  cases cs4 with | nil => nomatch hL2 | cons c4 cs5 =>
  cases cs5 with | nil => nomatch hL2 | cons c5 cs6 =>
  cases cs6 with | nil => nomatch hL2 | cons c6 cs7 =>
  cases cs7 with | nil => nomatch hL2 | cons c7 cs8 =>
  cases cs8 with | cons _ _ => nomatch hL2 | nil =>
  dsimp only [sameAtNonPad, List.foldr, u8PadU32Mask] at hSame
  cases h0 : allocByteBeq a0 c0 with
  | false => rw [h0] at hSame; exact False.elim (boolFalseNeTrue hSame)
  | true =>
    rw [h0, Bool.true_and] at hSame
    cases h4 : allocByteBeq a4 c4 with
    | false => rw [h4] at hSame; exact False.elim (boolFalseNeTrue hSame)
    | true =>
      rw [h4, Bool.true_and] at hSame
      cases h5 : allocByteBeq a5 c5 with
      | false => rw [h5] at hSame; exact False.elim (boolFalseNeTrue hSame)
      | true =>
        rw [h5, Bool.true_and] at hSame
        cases h6 : allocByteBeq a6 c6 with
        | false => rw [h6] at hSame; exact False.elim (boolFalseNeTrue hSame)
        | true =>
          rw [h6, Bool.true_and, Bool.and_true] at hSame
          cases a0 with
          | uninit =>
            cases c0 with
            | uninit => rfl
            | init _ _ => exact False.elim (boolFalseNeTrue h0)
          | init va0 pa0 =>
            cases c0 with
            | uninit => exact False.elim (boolFalseNeTrue h0)
            | init vc0 pc0 =>
              have eq0 : va0 = vc0 := allocByteBeq_true_init_val va0 vc0 pa0 pc0 h0
              have pr0 : pa0 = pc0 := allocByteBeq_true_init_prov va0 vc0 pa0 pc0 h0
              cases a4 with
              | uninit =>
                cases c4 with
                | uninit => subst eq0; subst pr0; rfl
                | init _ _ => exact False.elim (boolFalseNeTrue h4)
              | init va4 pa4 =>
                cases c4 with
                | uninit => exact False.elim (boolFalseNeTrue h4)
                | init vc4 pc4 =>
                  have eq4 : va4 = vc4 := allocByteBeq_true_init_val va4 vc4 pa4 pc4 h4
                  have pr4 : pa4 = pc4 := allocByteBeq_true_init_prov va4 vc4 pa4 pc4 h4
                  cases a5 with
                  | uninit =>
                    cases c5 with
                    | uninit => subst eq0; subst pr0; subst eq4; subst pr4; rfl
                    | init _ _ => exact False.elim (boolFalseNeTrue h5)
                  | init va5 pa5 =>
                    cases c5 with
                    | uninit => exact False.elim (boolFalseNeTrue h5)
                    | init vc5 pc5 =>
                      have eq5 : va5 = vc5 := allocByteBeq_true_init_val va5 vc5 pa5 pc5 h5
                      have pr5 : pa5 = pc5 := allocByteBeq_true_init_prov va5 vc5 pa5 pc5 h5
                      cases a6 with
                      | uninit =>
                        cases c6 with
                        | uninit =>
                          subst eq0; subst pr0; subst eq4; subst pr4; subst eq5; subst pr5; rfl
                        | init _ _ => exact False.elim (boolFalseNeTrue h6)
                      | init va6 pa6 =>
                        cases c6 with
                        | uninit => exact False.elim (boolFalseNeTrue h6)
                        | init vc6 pc6 =>
                          have eq6 : va6 = vc6 := allocByteBeq_true_init_val va6 vc6 pa6 pc6 h6
                          have pr6 : pa6 = pc6 := allocByteBeq_true_init_prov va6 vc6 pa6 pc6 h6
                          cases a7 with
                          | uninit =>
                            cases c7 with
                            | uninit =>
                              subst eq0; subst pr0; subst eq4; subst pr4
                              subst eq5; subst pr5; subst eq6; subst pr6
                              rfl
                            | init _ _ => exact False.elim (boolFalseNeTrue hSame)
                          | init va7 pa7 =>
                            cases c7 with
                            | uninit => exact False.elim (boolFalseNeTrue hSame)
                            | init vc7 pc7 =>
                              have eq7 : va7 = vc7 :=
                                allocByteBeq_true_init_val va7 vc7 pa7 pc7 hSame
                              have pr7 : pa7 = pc7 :=
                                allocByteBeq_true_init_prov va7 vc7 pa7 pc7 hSame
                              subst eq0; subst pr0; subst eq4; subst pr4
                              subst eq5; subst pr5; subst eq6; subst pr6
                              subst eq7; subst pr7
                              rfl

private theorem u8ScalarEncode_eq (b : UInt8) :
    execEncodeVal execProfileTargetEndian (.int .i8 false)
      (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩) =
      .ok [AllocByte.init b none] := by
  have hBLt : b.toNat < 256 := b.toBitVec.isLt
  have hPow8_128 : 256 ≤ Nat.pow 2 128 := natLe_of_ble 256 (Nat.pow 2 128) rfl
  have hAToNat : (BitVec.ofNat 128 b.toNat).toNat = b.toNat :=
    bitVec128_ofNat_toNat_lt b.toNat 256 hBLt hPow8_128
  dsimp only [execEncodeVal, execByteSize]
  rw [mirCheckVal_u8_ofNat hBLt, ite_bool_false (rfl : (!true) = false),
    hAToNat]
  change Except.ok [AllocByte.init (UInt8.ofNat (Nat.mod b.toNat 256)) none] =
    Except.ok [AllocByte.init b none]
  rw [natMod_eq_of_lt hBLt, uint8_ofNat_toNat b]

private theorem u32ScalarEncode_eq (v : BitVec 32) :
    execEncodeVal execProfileTargetEndian (.int .i32 false)
      (.scalar ⟨.i32, false, BitVec.ofNat 128 v.toNat⟩) =
      .ok ((execEncodeUInt execProfileTargetEndian 4 v.toNat).map
        (fun b => AllocByte.init b none)) := by
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
    natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hBToNat : (BitVec.ofNat 128 v.toNat).toNat = v.toNat :=
    bitVec128_ofNat_toNat_lt v.toNat 4294967296 v.isLt hPow128
  dsimp only [execEncodeVal, execByteSize]
  rw [mirCheckVal_u32_ofNat v.isLt, ite_bool_false (rfl : (!true) = false), hBToNat]

/-- Constructive `LawfulTypedSpatialMemCodec` proof for
`paddedU8U32MemCodec`. -/
theorem paddedU8U32MemCodec_lawful :
    LawfulTypedSpatialMemCodec paddedU8U32MemCodec := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hEncLen : (execEncodeUInt execProfileTargetEndian 4 x.bVal.toNat).length = 4 :=
      execEncodeUInt_length execProfileTargetEndian 4 x.bVal.toNat
    have hMapLen : ((execEncodeUInt execProfileTargetEndian 4 x.bVal.toNat).map
        (fun b => AllocByte.init b none)).length = 4 := by
      rw [listLength_map]
      exact hEncLen
    have hMemLen : (paddedU8U32Encode x).length = 8 := by
      dsimp only [paddedU8U32Encode]
      rw [listLength_append, hMapLen]
      rfl
    have hNonPad : nonPadBytesInitialized u8PadU32Mask (paddedU8U32Encode x) = true := by
      dsimp only [paddedU8U32Encode]
      change nonPadBytesInitialized [false, false, false, false]
        ((execEncodeUInt execProfileTargetEndian 4 x.bVal.toNat).map
          (fun b => AllocByte.init b none)) = true
      exact nonPad_map_init4 _ hEncLen
    have hAByteLt : x.aByte.toNat < 256 := x.aByte.toBitVec.isLt
    have hCompat :
        valCompatWithTargetSpec (paddedU8U32ToSymVal x) u8U32TargetSpec = true := by
      dsimp only [valCompatWithTargetSpec, u8U32TargetSpec, paddedU8U32ToSymVal,
        primFieldValCompat, List.foldr, List.isEmpty]
      rw [mirCheckVal_u8_ofNat hAByteLt, mirCheckVal_u32_ofNat x.bVal.isLt]
      rfl
    have hBytesMatch :
        valAndBytesMatchTargetSpec true u8U32TargetSpec (paddedU8U32ToSymVal x)
          (paddedU8U32Encode x) = true := by
      let map4 :=
        (execEncodeUInt execProfileTargetEndian 4 x.bVal.toNat).map
          (fun b => AllocByte.init b none)
      have hDrop8 : (paddedU8U32Encode x).drop 8 = [] :=
        listDrop_of_len (paddedU8U32Encode x) 8 hMemLen
      have hTake4 : map4.take 4 = map4 := listTake_of_len map4 4 hMapLen
      have hField0 :
          primFieldBytesMatch (.int .i8 false)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 x.aByte.toNat⟩)
            [AllocByte.init x.aByte none] = true := by
        dsimp only [primFieldBytesMatch, execLayoutOfTy, execIntLayout]
        rw [mirCheckVal_u8_ofNat hAByteLt, u8ScalarEncode_eq x.aByte]
        change (true && (true && true &&
          allocBytesListBeq [AllocByte.init x.aByte none]
            [AllocByte.init x.aByte none])) = true
        rw [allocBytesListBeq_refl]
        rfl
      have hField1 :
          primFieldBytesMatch (.int .i32 false)
            (.scalar ⟨.i32, false, BitVec.ofNat 128 x.bVal.toNat⟩)
            (map4.take 4) = true := by
        dsimp only [primFieldBytesMatch, execLayoutOfTy, execIntLayout]
        rw [mirCheckVal_u32_ofNat x.bVal.isLt, u32ScalarEncode_eq x.bVal,
          hTake4]
        change (true && (Nat.beq map4.length 4 && sliceAllInitNoProv map4 &&
          allocBytesListBeq map4 map4)) = true
        rw [hMapLen, sliceAllInitNoProv_map_none, allocBytesListBeq_refl map4]
        rfl
      change
        (true &&
         primFieldBytesMatch (.int .i8 false)
           (.scalar ⟨.i8, false, BitVec.ofNat 128 x.aByte.toNat⟩)
           [AllocByte.init x.aByte none] &&
         (true &&
          primFieldBytesMatch (.int .i32 false)
            (.scalar ⟨.i32, false, BitVec.ofNat 128 x.bVal.toNat⟩)
            (map4.take 4) &&
          (Nat.beq (paddedU8U32Encode x).length 8 &&
           padBytesClean true ((paddedU8U32Encode x).drop 8)))) = true
      rw [hField0, hField1, hMemLen, hDrop8]
      rfl
    have hDecMem : paddedU8U32Decode (paddedU8U32Encode x) = some x := by
      dsimp only [paddedU8U32Encode]
      rw [paddedU8U32Decode_of_raw4 x.aByte .uninit .uninit .uninit _ hEncLen]
      have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
      have hBLtPow : x.bVal.toNat < Nat.pow 256 4 := by
        rw [hPow4]
        exact x.bVal.isLt
      rw [decodeUInt_encodeUInt_of_lt execProfileTargetEndian 4 x.bVal.toNat hBLtPow]
      rw [bitVec_ofNat_toNat 32 x.bVal]
    have hDecSym : paddedU8U32FromSymVal (paddedU8U32ToSymVal x) = some x := by
      dsimp only [paddedU8U32FromSymVal, paddedU8U32ToSymVal]
      have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
        natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
      have hPow8_128 : 256 ≤ Nat.pow 2 128 :=
        natLe_of_ble 256 (Nat.pow 2 128) rfl
      have hAToNat : (BitVec.ofNat 128 x.aByte.toNat).toNat = x.aByte.toNat :=
        bitVec128_ofNat_toNat_lt x.aByte.toNat 256 x.aByte.toBitVec.isLt hPow8_128
      have hBToNat : (BitVec.ofNat 128 x.bVal.toNat).toNat = x.bVal.toNat :=
        bitVec128_ofNat_toNat_lt x.bVal.toNat 4294967296 x.bVal.isLt hPow128
      have hABlt : Nat.blt x.aByte.toNat 256 = true :=
        natBle_of_le (x.aByte.toNat + 1) 256 x.aByte.toBitVec.isLt
      have hBBlt : Nat.blt x.bVal.toNat 4294967296 = true :=
        natBle_of_le (x.bVal.toNat + 1) 4294967296 x.bVal.isLt
      rw [hAToNat, hBToNat, hABlt, hBBlt, Bool.not_false, Bool.true_and,
        Bool.true_and, Bool.and_self, ite_bool_true rfl,
        uint8_ofNat_toNat x.aByte, bitVec_ofNat_toNat 32 x.bVal]
    exact ⟨hMemLen, hNonPad, rfl, hCompat, hBytesMatch, hDecMem, hDecSym⟩
  · intro v x hDec
    cases v with
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _ | bytes _ =>
      nomatch hDec
    | tuple fs =>
      cases fs with
      | nil => nomatch hDec
      | cons f0 r1 =>
        cases r1 with
        | nil => nomatch hDec
        | cons f1 r2 =>
          cases r2 with
          | cons _ _ => nomatch hDec
          | nil =>
            cases f0 with
            | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
            | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
            | bytes _ =>
              nomatch hDec
            | scalar sa =>
              cases f1 with
              | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
              | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
              | bytes _ =>
                nomatch hDec
              | scalar sb =>
                cases sa with
                | mk wa sga ba =>
                  cases sb with
                  | mk wb sgb bb =>
                    cases wa with
                    | i16 | i32 | i64 | i128 | isize => nomatch hDec
                    | i8 =>
                      cases wb with
                      | i8 | i16 | i64 | i128 | isize => nomatch hDec
                      | i32 =>
                        dsimp only [paddedU8U32MemCodec, paddedU8U32FromSymVal] at hDec
                        cases sga with
                        | true => nomatch hDec
                        | false =>
                          cases hABlt : Nat.blt ba.toNat 256 with
                          | false => rw [hABlt] at hDec; nomatch hDec
                          | true =>
                            cases sgb with
                            | true => rw [hABlt] at hDec; nomatch hDec
                            | false =>
                              cases hBBlt : Nat.blt bb.toNat 4294967296 with
                              | false => rw [hABlt, hBBlt] at hDec; nomatch hDec
                              | true =>
                                rw [hABlt, hBBlt, Bool.not_false, Bool.true_and, Bool.true_and,
                                  Bool.and_self, ite_bool_true rfl] at hDec
                                injection hDec with hX
                                subst hX
                                dsimp only [paddedU8U32MemCodec, paddedU8U32ToSymVal]
                                have hALt : ba.toNat < 256 := natLt_of_blt ba.toNat 256 hABlt
                                have hBLt : bb.toNat < 4294967296 :=
                                  natLt_of_blt bb.toNat 4294967296 hBBlt
                                have hPow32 : Nat.pow 2 32 = 4294967296 := rfl
                                have hBLtPow : bb.toNat < Nat.pow 2 32 := by
                                  rw [hPow32]; exact hBLt
                                have hU8 : (UInt8.ofNat ba.toNat).toNat = ba.toNat :=
                                  uint8_toNat_ofNat_lt hALt
                                have hBv32 : (BitVec.ofNat 32 bb.toNat).toNat = bb.toNat := by
                                  change Nat.mod bb.toNat (Nat.pow 2 32) = bb.toNat
                                  exact natMod_eq_of_lt hBLtPow
                                rw [hU8, hBv32, bitVec_ofNat_toNat 128 ba,
                                  bitVec_ofNat_toNat 128 bb]
  · intro bs x hLen _ _ hDec
    cases bs with | nil => nomatch hLen | cons c0 r1 =>
    cases r1 with | nil => nomatch hLen | cons c1 r2 =>
    cases r2 with | nil => nomatch hLen | cons c2 r3 =>
    cases r3 with | nil => nomatch hLen | cons c3 r4 =>
    cases r4 with | nil => nomatch hLen | cons c4 r5 =>
    cases r5 with | nil => nomatch hLen | cons c5 r6 =>
    cases r6 with | nil => nomatch hLen | cons c6 r7 =>
    cases r7 with | nil => nomatch hLen | cons c7 r8 =>
    cases r8 with | cons _ _ => nomatch hLen | nil =>
    cases c0 with
    | uninit => nomatch hDec
    | init aB p0 =>
      cases p0 with
      | some _ => nomatch hDec
      | none =>
        cases c4 with
        | uninit => nomatch hDec
        | init b0 p4 =>
          cases p4 with
          | some _ => nomatch hDec
          | none =>
            cases c5 with
            | uninit => nomatch hDec
            | init b1 p5 =>
              cases p5 with
              | some _ => nomatch hDec
              | none =>
                cases c6 with
                | uninit => nomatch hDec
                | init b2 p6 =>
                  cases p6 with
                  | some _ => nomatch hDec
                  | none =>
                    cases c7 with
                    | uninit => nomatch hDec
                    | init b3 p7 =>
                      cases p7 with
                      | some _ => nomatch hDec
                      | none =>
                        dsimp only [paddedU8U32MemCodec, paddedU8U32Decode,
                          allocByteNoProvOpt] at hDec
                        injection hDec with hX
                        subst hX
                        let raw4 := [b0, b1, b2, b3]
                        have hLtPow :
                            execDecodeUInt execProfileTargetEndian raw4 <
                              Nat.pow 256 4 :=
                          execDecodeUInt_lt_pow execProfileTargetEndian raw4
                        have hPowEq : Nat.pow 256 4 = Nat.pow 2 32 := rfl
                        have hLt32 :
                            execDecodeUInt execProfileTargetEndian raw4 <
                              Nat.pow 2 32 := by
                          rw [← hPowEq]; exact hLtPow
                        have hBv32 :
                            (BitVec.ofNat 32
                              (execDecodeUInt execProfileTargetEndian raw4)).toNat =
                              execDecodeUInt execProfileTargetEndian raw4 := by
                          change Nat.mod _ (Nat.pow 2 32) = _
                          exact natMod_eq_of_lt hLt32
                        have hReenc :
                            execEncodeUInt execProfileTargetEndian 4
                              (BitVec.ofNat 32
                                (execDecodeUInt execProfileTargetEndian raw4)).toNat =
                              raw4 := by
                          rw [hBv32]
                          exact execEncodeUInt_execDecodeUInt
                            execProfileTargetEndian raw4
                        dsimp only [paddedU8U32MemCodec, paddedU8U32Encode]
                        rw [hReenc]
                        change (allocByteBeq (.init aB none) (.init aB none) &&
                          sameAtNonPad (List.replicate 4 false)
                            [.init b0 none, .init b1 none,
                             .init b2 none, .init b3 none]
                            [.init b0 none, .init b1 none,
                             .init b2 none, .init b3 none]) = true
                        rw [allocByteBeq_refl, sameAtNonPad_allFalse_refl 4 _ rfl]
                        rfl
  · intro _ _ hTy
    nomatch hTy
  · intro b1 b2 hL1 hL2 _ _ hSame
    exact sameAtNonPad_u8u32_eq b1 b2 hL1 hL2 hSame

/-! ### Provenance-Carrying Padded Pointer Struct Codec -/

/-- Padded `#[repr(C)]` `(u8, [pad; 7], *mut T)` payload with 16-byte size and
8-byte alignment (`alignLog2 = 3`). -/
structure ProvPtrStruct where
  tagByte : UInt8
  ptrAddr : BitVec 64

/-- Padding mask for `ProvPtrStruct` (bytes `1..7` are padding). -/
@[expose] def provPtrPadMask : List Bool :=
  [false, true, true, true, true, true, true, true,
   false, false, false, false, false, false, false, false]

/-- Audited `SpatialTargetSpec` for `ProvPtrStruct` (`#[repr(C)]`
`(u8, *mut u8)` at offsets `0` and `8`). -/
@[expose] def provPtrTargetSpec : SpatialTargetSpec :=
  .reprCAdt 16064 [⟨0, .int .i8 false⟩, ⟨8, .rawPtr .mut (.int .i8 false)⟩]

/-- Encodes `ProvPtrStruct` into 16 `AllocByte`s with `some expectedProv`. -/
@[expose] def provPtrEncode (expectedProv : AllocId) (s : ProvPtrStruct) : List
    AllocByte :=
  [AllocByte.init s.tagByte none, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] ++
  (execEncodeUInt execProfileTargetEndian 8 s.ptrAddr.toNat).map
    (fun b => AllocByte.init b (some expectedProv))

/-- Decodes `ProvPtrStruct` from 16 `AllocByte`s, ignoring padding `1..7`. -/
@[expose] def provPtrDecode (bytes : List AllocByte) : Option ProvPtrStruct :=
  if !Nat.beq bytes.length 16 then
    none
  else
    match mirListGet? bytes 0 with
    | none => none
    | some c0 =>
      match allocByteValOpt c0 with
      | none => none
      | some tagB =>
        match extractInitRawBytes (bytes.drop 8) with
        | none => none
        | some ptrRaw =>
          some ⟨tagB, BitVec.ofNat 64 (execDecodeUInt execProfileTargetEndian ptrRaw)⟩

/-- Verifies that byte `0` is initialized without provenance, padding bytes
`1..7` carry no provenance, and bytes `8..15` carry `some expectedProv`. -/
@[expose] def provPtrCheck (expectedProv : AllocId) (bytes : List AllocByte) :
    Bool :=
  if !Nat.beq bytes.length 16 then
    false
  else
    match mirListGet? bytes 0 with
    | some (.init _ none) =>
      padBytesClean false ((bytes.drop 1).take 7) &&
      allHaveProv (bytes.drop 8) expectedProv
    | _ => false

/-- Encodes `ProvPtrStruct` as a `(u8, ptr)` `Val.tuple` on `expectedProv`. -/
@[expose] def provPtrToSymVal (expectedProv : AllocId) (s : ProvPtrStruct) : Val
    :=
  Val.tuple
    [ .scalar ⟨.i8, false, BitVec.ofNat 128 s.tagByte.toNat⟩
    , .ptr ⟨some expectedProv, UInt64.ofBitVec s.ptrAddr, .isize⟩ ]

/-- Decodes `ProvPtrStruct` from a canonical `(u8, ptr)` `Val.tuple`. -/
@[expose] def provPtrFromSymVal (expectedProv : AllocId) (v : Val) : Option
    ProvPtrStruct :=
  match v with
  | .tuple fs =>
    match fs with
    | [] | [_] | _ :: _ :: _ :: _ => none
    | f0 :: [f1] =>
      match f0 with
      | .scalar sa =>
        match f1 with
        | .ptr pv =>
          match sa.width with
          | .i8 =>
            match pv.width with
            | .isize =>
              if !sa.signed && Nat.blt sa.bits.toNat 256 &&
                 optAllocIdBeq pv.allocId (some expectedProv) then
                some ⟨UInt8.ofNat sa.bits.toNat, pv.offsetBytes.toBitVec⟩
              else
                none
            | .i8 | .i16 | .i32 | .i64 | .i128 => none
          | .i16 | .i32 | .i64 | .i128 | .isize => none
        | .scalar _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
        | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
        | .bytes _ =>
          none
      | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
      | .bytes _ =>
        none
  | .scalar _ | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _
  | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _ | .optionVal _
  | .bytes _ =>
    none

/-- Provenance-enforcing `TypedSpatialMemCodec` for `ProvPtrStruct` requiring
every byte of the 8-byte pointer field to carry `some expectedProv`. -/
@[expose] def provPtrPaddedMemCodec (expectedProv : AllocId) :
    TypedSpatialMemCodec ProvPtrStruct where
  codecId := 16064
  targetTy := provPtrTargetSpec
  layout := ⟨16, 3⟩
  padMask := provPtrPadMask
  encodeValToMem := provPtrEncode expectedProv
  decodeValFromMem := provPtrDecode
  provCheck := provPtrCheck expectedProv
  encodeToSymVal := provPtrToSymVal expectedProv
  decodeFromSymVal := provPtrFromSymVal expectedProv

/-- Dropping zero elements from `xs` returns `xs`. -/
theorem listDrop_zero {α : Type} (xs : List α) : xs.drop 0 = xs := rfl

private theorem execInitBytes?_cons_init_some (b : UInt8)
    (prov : Option AllocId) (rest : List AllocByte) (bs : List UInt8)
    (h : execInitBytes? rest = some bs) :
    execInitBytes? (.init b prov :: rest) = some (b :: bs) := by
  unfold execInitBytes? at h
  unfold execInitBytes?
  dsimp only [List.foldr]
  rw [h]

private theorem execInitBytes?_cons_init_none (b : UInt8)
    (prov : Option AllocId) (rest : List AllocByte)
    (h : execInitBytes? rest = none) :
    execInitBytes? (.init b prov :: rest) = none := by
  unfold execInitBytes? at h
  unfold execInitBytes?
  dsimp only [List.foldr]
  rw [h]

private theorem allHaveProv_cons_init (b : UInt8) (prov : Option AllocId)
    (rest : List AllocByte) (p : AllocId) :
    allHaveProv (.init b prov :: rest) p =
      (optAllocIdBeq prov (some p) && allHaveProv rest p) := rfl

private theorem sameAtNonPad_cons_false (ps : List Bool) (x : AllocByte)
    (xs : List AllocByte) (y : AllocByte) (ys : List AllocByte) :
    sameAtNonPad (false :: ps) (x :: xs) (y :: ys) =
      (allocByteBeq x y && sameAtNonPad ps xs ys) := rfl

private theorem execInitBytes?_map_init (xs : List UInt8)
    (prov : Option AllocId) :
    execInitBytes? (xs.map (fun b => AllocByte.init b prov)) = some xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [List.map]
    exact execInitBytes?_cons_init_some a prov _ rest ih

private theorem allHaveProv_map_init (xs : List UInt8) (p : AllocId) :
    allHaveProv (xs.map (fun b => AllocByte.init b (some p))) p = true := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [List.map]
    rw [allHaveProv_cons_init]
    dsimp only [optAllocIdBeq]
    rw [natBeq_refl p, ih]
    rfl

private theorem nonPad_map_allFalse (xs : List UInt8) (p : AllocId) (hLen : xs.length = 8) :
    nonPadBytesInitialized [false, false, false, false, false, false, false, false]
      (xs.map (fun b => AllocByte.init b (some p))) = true := by
  cases xs with | nil => nomatch hLen | cons _ r1 =>
  cases r1 with | nil => nomatch hLen | cons _ r2 =>
  cases r2 with | nil => nomatch hLen | cons _ r3 =>
  cases r3 with | nil => nomatch hLen | cons _ r4 =>
  cases r4 with | nil => nomatch hLen | cons _ r5 =>
  cases r5 with | nil => nomatch hLen | cons _ r6 =>
  cases r6 with | nil => nomatch hLen | cons _ r7 =>
  cases r7 with | nil => nomatch hLen | cons _ r8 =>
  cases r8 with | cons _ _ => nomatch hLen | nil =>
  rfl

private theorem extractInitRawBytes_eq_of_sameAtNonPad_allFalse :
    ∀ (mask : List Bool) (xs ys : List AllocByte),
      (∀ b, b ∈ mask → b = false) →
      sameAtNonPad mask xs ys = true →
      extractInitRawBytes xs = extractInitRawBytes ys
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, _, h => False.elim (boolFalseNeTrue h)
  | [], [], _ :: _, _, h => False.elim (boolFalseNeTrue h)
  | true :: _, _, _, hAllFalse, _ =>
    False.elim (boolFalseNeTrue (hAllFalse true (List.Mem.head _)).symm)
  | false :: ps, [], _, _, h => False.elim (boolFalseNeTrue h)
  | false :: ps, _ :: _, [], _, h => False.elim (boolFalseNeTrue h)
  | false :: ps, x :: xs, y :: ys, hAllFalse, h => by
    rw [sameAtNonPad_cons_false] at h
    cases hHead : allocByteBeq x y with
    | false => rw [hHead] at h; exact False.elim (boolFalseNeTrue h)
    | true =>
      rw [hHead, Bool.true_and] at h
      have hTail := extractInitRawBytes_eq_of_sameAtNonPad_allFalse ps xs ys
        (fun b hb => hAllFalse b (List.Mem.tail false hb)) h
      cases x with
      | uninit =>
        cases y with
        | uninit => rfl
        | init _ _ => exact False.elim (boolFalseNeTrue hHead)
      | init vx px =>
        cases y with
        | uninit => exact False.elim (boolFalseNeTrue hHead)
        | init vy py =>
          have hVal := allocByteBeq_true_init_val vx vy px py hHead
          subst hVal
          dsimp only [extractInitRawBytes] at hTail
          dsimp only [extractInitRawBytes]
          cases hRx : execInitBytes? xs with
          | none =>
            rw [hRx] at hTail
            exact (execInitBytes?_cons_init_none vx px xs hRx).trans
              (execInitBytes?_cons_init_none vx py ys hTail.symm).symm
          | some bs =>
            rw [hRx] at hTail
            exact (execInitBytes?_cons_init_some vx px xs bs hRx).trans
              (execInitBytes?_cons_init_some vx py ys bs hTail.symm).symm

private theorem sameAtNonPad_provPtr_eq (b1 b2 : List AllocByte)
    (hL1 : b1.length = 16) (hL2 : b2.length = 16)
    (hSame : sameAtNonPad provPtrPadMask b1 b2 = true) :
    provPtrDecode b1 = provPtrDecode b2 := by
  cases b1 with | nil => nomatch hL1 | cons a0 as1 =>
  cases as1 with | nil => nomatch hL1 | cons _ as2 =>
  cases as2 with | nil => nomatch hL1 | cons _ as3 =>
  cases as3 with | nil => nomatch hL1 | cons _ as4 =>
  cases as4 with | nil => nomatch hL1 | cons _ as5 =>
  cases as5 with | nil => nomatch hL1 | cons _ as6 =>
  cases as6 with | nil => nomatch hL1 | cons _ as7 =>
  cases as7 with | nil => nomatch hL1 | cons _ as8 =>
  cases b2 with | nil => nomatch hL2 | cons c0 cs1 =>
  cases cs1 with | nil => nomatch hL2 | cons _ cs2 =>
  cases cs2 with | nil => nomatch hL2 | cons _ cs3 =>
  cases cs3 with | nil => nomatch hL2 | cons _ cs4 =>
  cases cs4 with | nil => nomatch hL2 | cons _ cs5 =>
  cases cs5 with | nil => nomatch hL2 | cons _ cs6 =>
  cases cs6 with | nil => nomatch hL2 | cons _ cs7 =>
  cases cs7 with | nil => nomatch hL2 | cons _ cs8 =>
  change (allocByteBeq a0 c0 &&
    sameAtNonPad [false, false, false, false, false, false, false, false] as8 cs8) = true at hSame
  cases h0 : allocByteBeq a0 c0 with
  | false => rw [h0] at hSame; exact False.elim (boolFalseNeTrue hSame)
  | true =>
    rw [h0, Bool.true_and] at hSame
    have hDrop : extractInitRawBytes as8 = extractInitRawBytes cs8 := by
      apply extractInitRawBytes_eq_of_sameAtNonPad_allFalse
        [false, false, false, false, false, false, false, false] as8 cs8
      · intro b hb
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb =>
        cases hb with | head _ => rfl | tail _ hb => cases hb
      · exact hSame
    dsimp only [provPtrDecode]
    rw [hL1, hL2]
    dsimp only [mirListGet?, List.foldr, List.drop]
    rw [hDrop]
    cases a0 with
    | uninit =>
      cases c0 with
      | uninit => rfl
      | init _ _ => exact False.elim (boolFalseNeTrue h0)
    | init va0 pa0 =>
      cases c0 with
      | uninit => exact False.elim (boolFalseNeTrue h0)
      | init vc0 pc0 =>
        have eq0 := allocByteBeq_true_init_val va0 vc0 pa0 pc0 h0
        subst eq0
        rfl

private theorem execInitBytes?_len :
    ∀ (bs : List AllocByte) (raw : List UInt8),
      execInitBytes? bs = some raw → raw.length = bs.length
  | [], _, h => by
    injection h with hEq
    subst hEq
    rfl
  | .uninit :: _, _, h => nomatch h
  | .init b prov :: rest, _, h => by
    cases hR : execInitBytes? rest with
    | none =>
      rw [execInitBytes?_cons_init_none b prov rest hR] at h
      nomatch h
    | some r =>
      rw [execInitBytes?_cons_init_some b prov rest r hR] at h
      injection h with hEq
      subst hEq
      exact congrArg Nat.succ (execInitBytes?_len rest r hR)

private theorem execInitBytes?_eq_map_of_allHaveProv (p : AllocId) :
    ∀ (bs : List AllocByte) (raw : List UInt8),
      allHaveProv bs p = true →
      execInitBytes? bs = some raw →
      bs = raw.map (fun b => AllocByte.init b (some p))
  | [], _, _, h => by
    injection h with hEq
    subst hEq
    rfl
  | .uninit :: _, _, hP, _ => nomatch hP
  | .init b optP :: rest, _, hP, hInit => by
    rw [allHaveProv_cons_init] at hP
    cases hOpt : optAllocIdBeq optP (some p) with
    | false => rw [hOpt] at hP; nomatch hP
    | true =>
      rw [hOpt, Bool.true_and] at hP
      have hProvEq : optP = some p := by
        cases optP with
        | none => nomatch hOpt
        | some q => exact congrArg Option.some (natEq_of_beq q p hOpt)
      subst hProvEq
      cases hR : execInitBytes? rest with
      | none =>
        rw [execInitBytes?_cons_init_none b (some p) rest hR] at hInit
        nomatch hInit
      | some r =>
        rw [execInitBytes?_cons_init_some b (some p) rest r hR] at hInit
        injection hInit with hEq
        subst hEq
        exact congrArg (List.cons (.init b (some p)))
          (execInitBytes?_eq_map_of_allHaveProv p rest r hP hR)

private theorem execInitBytes?_eq_map_none :
    ∀ (bs : List AllocByte) (raw : List UInt8),
      sliceAllInitNoProv bs = true →
      execInitBytes? bs = some raw →
      bs = raw.map (fun b => AllocByte.init b none)
  | [], _, _, h => by
    injection h with hEq
    subst hEq
    rfl
  | .uninit :: _, _, hP, _ => nomatch hP
  | .init _ (some _) :: _, _, hP, _ => nomatch hP
  | .init b none :: rest, _, hP, hInit => by
    cases hR : execInitBytes? rest with
    | none =>
      rw [execInitBytes?_cons_init_none b none rest hR] at hInit
      nomatch hInit
    | some r =>
      rw [execInitBytes?_cons_init_some b none rest r hR] at hInit
      injection hInit with hEq
      subst hEq
      exact congrArg (List.cons (.init b none))
        (execInitBytes?_eq_map_none rest r hP hR)

/-- Constructive `LawfulTypedSpatialMemCodec` proof for
`provPtrPaddedMemCodec`. -/
theorem provPtrPaddedMemCodec_lawful (expectedProv : AllocId) :
    LawfulTypedSpatialMemCodec (provPtrPaddedMemCodec expectedProv) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hEncLen : (execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat).length = 8 :=
      execEncodeUInt_length execProfileTargetEndian 8 x.ptrAddr.toNat
    have hMapLen : ((execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat).map
        (fun b => AllocByte.init b (some expectedProv))).length = 8 := by
      rw [listLength_map]
      exact hEncLen
    have hMemLen : (provPtrEncode expectedProv x).length = 16 := by
      dsimp only [provPtrEncode]
      rw [listLength_append, hMapLen]
      rfl
    have hNonPad : nonPadBytesInitialized provPtrPadMask (provPtrEncode expectedProv x) = true := by
      dsimp only [provPtrEncode]
      change nonPadBytesInitialized [false, false, false, false, false, false, false, false]
        ((execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat).map
          (fun b => AllocByte.init b (some expectedProv))) = true
      exact
        (nonPad_map_allFalse (execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat)
          expectedProv hEncLen)
    have hHead0 :
        mirListGet? (provPtrEncode expectedProv x) 0 =
          some (AllocByte.init x.tagByte none) := rfl
    have hPad17 :
        ((provPtrEncode expectedProv x).drop 1).take 7 =
          [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] := rfl
    have hDrop8 :
        (provPtrEncode expectedProv x).drop 8 =
          (execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat).map
            (fun b => AllocByte.init b (some expectedProv)) :=
      listDrop_append_of_len
        [AllocByte.init x.tagByte none, .uninit, .uninit, .uninit,
         .uninit, .uninit, .uninit, .uninit] _ 8 rfl
    have hProv : provPtrCheck expectedProv (provPtrEncode expectedProv x) = true := by
      dsimp only [provPtrCheck]
      rw [hMemLen, ite_bool_false (rfl : (!Nat.beq 16 16) = false),
        hHead0, hPad17, hDrop8]
      change (true && allHaveProv _ expectedProv) = true
      rw [Bool.true_and]
      exact allHaveProv_map_init _ expectedProv
    have hTagLt : x.tagByte.toNat < 256 := x.tagByte.toBitVec.isLt
    have hCompat :
        valCompatWithTargetSpec (provPtrToSymVal expectedProv x)
          provPtrTargetSpec = true := by
      dsimp only [valCompatWithTargetSpec, provPtrTargetSpec,
        provPtrToSymVal, primFieldValCompat, sizedPointeeAdmittedAt,
        natFold, Nat.recCompiled, execLayoutOfTy, execIntLayout,
        List.foldr, List.isEmpty, mirIntWidthBeq]
      rw [mirCheckVal_u8_ofNat hTagLt]
      rfl
    have hBytesMatch :
        valAndBytesMatchTargetSpec true provPtrTargetSpec
          (provPtrToSymVal expectedProv x) (provPtrEncode expectedProv x) =
          true := by
      let map8 :=
        (execEncodeUInt execProfileTargetEndian 8 x.ptrAddr.toNat).map
          (fun b => AllocByte.init b (some expectedProv))
      have hDrop16 : (provPtrEncode expectedProv x).drop 16 = [] :=
        listDrop_of_len (provPtrEncode expectedProv x) 16 hMemLen
      have hTake8 : map8.take 8 = map8 := listTake_of_len map8 8 hMapLen
      have hU8Enc :
          execEncodeVal execProfileTargetEndian (.int .i8 false)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 x.tagByte.toNat⟩) =
            .ok [AllocByte.init x.tagByte none] := u8ScalarEncode_eq x.tagByte
      have hField0 :
          primFieldBytesMatch (.int .i8 false)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 x.tagByte.toNat⟩)
            [AllocByte.init x.tagByte none] = true := by
        dsimp only [primFieldBytesMatch, execLayoutOfTy, execIntLayout]
        rw [mirCheckVal_u8_ofNat hTagLt, hU8Enc]
        change (true && (true && true &&
          allocBytesListBeq [AllocByte.init x.tagByte none]
            [AllocByte.init x.tagByte none])) = true
        rw [allocBytesListBeq_refl]
        rfl
      have hField1 :
          primFieldBytesMatch (.rawPtr .mut (.int .i8 false))
            (.ptr ⟨some expectedProv, UInt64.ofBitVec x.ptrAddr, .isize⟩)
            (map8.take 8) = true := by
        dsimp only [primFieldBytesMatch, sizedPointeeAdmittedAt, natFold,
          Nat.recCompiled, execLayoutOfTy, execIntLayout, mirIntWidthBeq]
        rw [hTake8, hMapLen, sliceAllInitOptProv_map_some _ expectedProv]
        change (true && (true && true && true &&
          allocBytesListBeq map8 map8)) = true
        rw [allocBytesListBeq_refl map8]
        rfl
      change
        (true &&
         primFieldBytesMatch (.int .i8 false)
           (.scalar ⟨.i8, false, BitVec.ofNat 128 x.tagByte.toNat⟩)
           [AllocByte.init x.tagByte none] &&
         (true &&
          primFieldBytesMatch (.rawPtr .mut (.int .i8 false))
            (.ptr ⟨some expectedProv, UInt64.ofBitVec x.ptrAddr, .isize⟩)
            (map8.take 8) &&
          (Nat.beq (provPtrEncode expectedProv x).length 16 &&
           padBytesClean true ((provPtrEncode expectedProv x).drop 16)))) = true
      rw [hField0, hField1, hMemLen, hDrop16]
      rfl
    have hDecMem : provPtrDecode (provPtrEncode expectedProv x) = some x := by
      dsimp only [provPtrDecode, extractInitRawBytes]
      rw [hMemLen, ite_bool_false (rfl : (!Nat.beq 16 16) = false),
        hHead0, hDrop8, execInitBytes?_map_init]
      dsimp only [allocByteValOpt]
      have hPow8 : Nat.pow 256 8 = 18446744073709551616 := rfl
      have hPLt : x.ptrAddr.toNat < Nat.pow 256 8 := by
        rw [hPow8]
        exact x.ptrAddr.isLt
      rw [decodeUInt_encodeUInt_of_lt execProfileTargetEndian 8 x.ptrAddr.toNat hPLt]
      rw [bitVec_ofNat_toNat 64 x.ptrAddr]
    have hDecSym : provPtrFromSymVal expectedProv (provPtrToSymVal expectedProv x) = some x := by
      dsimp only [provPtrFromSymVal, provPtrToSymVal]
      have hPow8_128 : 256 ≤ Nat.pow 2 128 := natLe_of_ble 256 (Nat.pow 2 128) rfl
      have hTagToNat : (BitVec.ofNat 128 x.tagByte.toNat).toNat = x.tagByte.toNat :=
        bitVec128_ofNat_toNat_lt x.tagByte.toNat 256 x.tagByte.toBitVec.isLt hPow8_128
      have hTagBlt : Nat.blt x.tagByte.toNat 256 = true :=
        natBle_of_le (x.tagByte.toNat + 1) 256 x.tagByte.toBitVec.isLt
      have hOptProv : optAllocIdBeq (some expectedProv) (some expectedProv) = true :=
        natBeq_refl expectedProv
      rw [hTagToNat, hTagBlt, Bool.not_false, Bool.true_and, hOptProv, Bool.and_self,
        ite_bool_true rfl, uint8_ofNat_toNat x.tagByte]
    exact ⟨hMemLen, hNonPad, hProv, hCompat, hBytesMatch, hDecMem, hDecSym⟩
  · intro v x hDec
    cases v with
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _ | bytes _ =>
      nomatch hDec
    | tuple fs =>
      cases fs with
      | nil => nomatch hDec
      | cons f0 r1 =>
        cases r1 with
        | nil => nomatch hDec
        | cons f1 r2 =>
          cases r2 with
          | cons _ _ => nomatch hDec
          | nil =>
            cases f0 with
            | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
            | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
            | bytes _ =>
              nomatch hDec
            | scalar sa =>
              cases f1 with
              | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
              | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
              | bytes _ =>
                nomatch hDec
              | ptr pv =>
                cases sa with
                | mk wa sga ba =>
                  cases pv with
                  | mk allocOpt offBytes wp =>
                    cases wa with
                    | i16 | i32 | i64 | i128 | isize => nomatch hDec
                    | i8 =>
                      cases wp with
                      | i8 | i16 | i32 | i64 | i128 => nomatch hDec
                      | isize =>
                        dsimp only [provPtrPaddedMemCodec, provPtrFromSymVal] at hDec
                        cases sga with
                        | true => nomatch hDec
                        | false =>
                          cases hABlt : Nat.blt ba.toNat 256 with
                          | false => rw [hABlt] at hDec; nomatch hDec
                          | true =>
                            cases allocOpt with
                            | none =>
                              rw [hABlt] at hDec
                              nomatch hDec
                            | some pId =>
                              change
                                (if !false && Nat.blt ba.toNat 256 && Nat.beq pId expectedProv then
                                   some ⟨UInt8.ofNat ba.toNat, offBytes.toBitVec⟩
                                 else none) = some x at hDec
                              cases hP : Nat.beq pId expectedProv with
                              | false => rw [hABlt, hP] at hDec; nomatch hDec
                              | true =>
                                rw [hABlt, hP, Bool.not_false, Bool.true_and, Bool.and_self,
                                  ite_bool_true rfl] at hDec
                                injection hDec with hX
                                subst hX
                                have hPEq : pId = expectedProv :=
                                  natEq_of_beq pId expectedProv hP
                                subst hPEq
                                dsimp only [provPtrPaddedMemCodec, provPtrToSymVal]
                                have hALt : ba.toNat < 256 := natLt_of_blt ba.toNat 256 hABlt
                                have hU8 : (UInt8.ofNat ba.toNat).toNat = ba.toNat :=
                                  uint8_toNat_ofNat_lt hALt
                                have hU64 : UInt64.ofBitVec offBytes.toBitVec = offBytes := by
                                  cases offBytes with
                                  | ofBitVec _ => rfl
                                rw [hU8, bitVec_ofNat_toNat 128 ba, hU64]
  · intro bs x hLen _ hProv hDec
    have hL16 : bs.length = 16 := hLen
    cases bs with | nil => nomatch hL16 | cons c0 r1 =>
    cases r1 with | nil => nomatch hL16 | cons p1 r2 =>
    cases r2 with | nil => nomatch hL16 | cons p2 r3 =>
    cases r3 with | nil => nomatch hL16 | cons p3 r4 =>
    cases r4 with | nil => nomatch hL16 | cons p4 r5 =>
    cases r5 with | nil => nomatch hL16 | cons p5 r6 =>
    cases r6 with | nil => nomatch hL16 | cons p6 r7 =>
    cases r7 with | nil => nomatch hL16 | cons p7 tail8 =>
    have hTailLen : tail8.length = 8 := by
      change tail8.length + 8 = 8 + 8 at hL16
      exact Nat.add_right_cancel hL16
    dsimp only [provPtrPaddedMemCodec, provPtrCheck] at hProv
    rw [hL16, ite_bool_false (rfl : (!Nat.beq 16 16) = false)] at hProv
    dsimp only [mirListGet?, List.foldr, List.drop] at hProv
    cases c0 with
    | uninit => nomatch hProv
    | init tagB prov0 =>
      cases prov0 with
      | some _ => nomatch hProv
      | none =>
        change
          (padBytesClean false [p1, p2, p3, p4, p5, p6, p7] &&
            allHaveProv tail8 expectedProv) = true at hProv
        cases hPadClean : padBytesClean false [p1, p2, p3, p4, p5, p6, p7] with
        | false => rw [hPadClean] at hProv; nomatch hProv
        | true =>
          rw [hPadClean, Bool.true_and] at hProv
          dsimp only [provPtrPaddedMemCodec, provPtrDecode,
            extractInitRawBytes] at hDec
          rw [hL16, ite_bool_false (rfl : (!Nat.beq 16 16) = false)] at hDec
          dsimp only [mirListGet?, List.foldr, allocByteValOpt, List.drop] at hDec
          cases hInit : execInitBytes? tail8 with
          | none => rw [hInit] at hDec; nomatch hDec
          | some ptrRaw =>
            rw [hInit] at hDec
            injection hDec with hX
            subst hX
            have hRawLen : ptrRaw.length = 8 := by
              rw [execInitBytes?_len tail8 ptrRaw hInit]
              exact hTailLen
            have hTailEq :
                tail8 = ptrRaw.map (fun b => AllocByte.init b (some expectedProv)) :=
              execInitBytes?_eq_map_of_allHaveProv expectedProv tail8 ptrRaw
                hProv hInit
            have hDecLtPow :
                execDecodeUInt execProfileTargetEndian ptrRaw <
                  Nat.pow 256 ptrRaw.length :=
              execDecodeUInt_lt_pow execProfileTargetEndian ptrRaw
            rw [hRawLen] at hDecLtPow
            have hPow8 : Nat.pow 256 8 = Nat.pow 2 64 := rfl
            have hDecLt64 :
                execDecodeUInt execProfileTargetEndian ptrRaw < Nat.pow 2 64 := by
              rw [← hPow8]; exact hDecLtPow
            have hBv64 :
                (BitVec.ofNat 64
                  (execDecodeUInt execProfileTargetEndian ptrRaw)).toNat =
                  execDecodeUInt execProfileTargetEndian ptrRaw := by
              change Nat.mod _ (Nat.pow 2 64) = _
              exact natMod_eq_of_lt hDecLt64
            have hReenc :
                execEncodeUInt execProfileTargetEndian 8
                  (BitVec.ofNat 64
                    (execDecodeUInt execProfileTargetEndian ptrRaw)).toNat =
                  ptrRaw := by
              rw [hBv64, ← hRawLen]
              exact execEncodeUInt_execDecodeUInt execProfileTargetEndian ptrRaw
            dsimp only [provPtrPaddedMemCodec, provPtrEncode]
            rw [hReenc, ← hTailEq]
            change (allocByteBeq (.init tagB none) (.init tagB none) &&
              sameAtNonPad (List.replicate 8 false) tail8 tail8) = true
            rw [allocByteBeq_refl, sameAtNonPad_allFalse_refl 8 tail8 hTailLen]
            rfl
  · intro _ _ hTy
    nomatch hTy
  · intro b1 b2 hL1 hL2 _ _ hSame
    exact sameAtNonPad_provPtr_eq b1 b2 hL1 hL2 hSame

/-! ### Day-1 `u32` Codec Exercising `encodeVal` and `decodeVal` Agreement -/

/-- Encodes a `BitVec 32` (`u32`) into 4 `AllocByte`s matching
`Trusted.MirSemantics.encodeVal`. -/
@[expose] def u32MemEncode (x : BitVec 32) : List AllocByte :=
  (execEncodeUInt execProfileTargetEndian 4 x.toNat).map
    (fun b => AllocByte.init b none)

/-- Decodes a `BitVec 32` (`u32`) from 4 initialized, provenance-free
`AllocByte`s. -/
@[expose] def u32MemDecode (bs : List AllocByte) : Option (BitVec 32) :=
  if !Nat.beq bs.length 4 || !sliceAllInitNoProv bs then
    none
  else
    match execInitBytes? bs with
    | none => none
    | some raw =>
      some (BitVec.ofNat 32 (execDecodeUInt execProfileTargetEndian raw))

/-- Encodes a `BitVec 32` as a canonical `.int .i32 false` `Val.scalar`. -/
@[expose] def u32MemToSymVal (x : BitVec 32) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 x.toNat⟩

/-- Decodes a `BitVec 32` from a canonical `.int .i32 false` `Val.scalar`. -/
@[expose] def u32MemFromSymVal (v : Val) : Option (BitVec 32) :=
  match v with
  | .scalar sb =>
    match sb.width with
    | .i32 =>
      if !sb.signed && Nat.blt sb.bits.toNat 4294967296 then
        some (BitVec.ofNat 32 sb.bits.toNat)
      else
        none
    | .i8 | .i16 | .i64 | .i128 | .isize => none
  | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _
  | .tuple _ | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .range _ _
  | .optionVal _ | .bytes _ => none

/-- Day-1 `TypedSpatialMemCodec` for `MirTy.int .i32 false` (`u32`). -/
@[expose] def u32MemCodec : TypedSpatialMemCodec (BitVec 32) where
  codecId := 4032
  targetTy := .mirTy (.int .i32 false)
  layout := ⟨4, 2⟩
  padMask := [false, false, false, false]
  encodeValToMem := u32MemEncode
  decodeValFromMem := u32MemDecode
  provCheck := sliceAllInitNoProv
  encodeToSymVal := u32MemToSymVal
  decodeFromSymVal := u32MemFromSymVal

private theorem sliceAllInitNoProv_eq_of_sameAtNonPad_allFalse :
    ∀ (mask : List Bool) (xs ys : List AllocByte),
      (∀ b, b ∈ mask → b = false) →
      sameAtNonPad mask xs ys = true →
      sliceAllInitNoProv xs = sliceAllInitNoProv ys
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, _, h => False.elim (boolFalseNeTrue h)
  | [], [], _ :: _, _, h => False.elim (boolFalseNeTrue h)
  | true :: _, _, _, hAllFalse, _ =>
    False.elim (boolFalseNeTrue (hAllFalse true (List.Mem.head _)).symm)
  | false :: ps, [], _, _, h => False.elim (boolFalseNeTrue h)
  | false :: ps, _ :: _, [], _, h => False.elim (boolFalseNeTrue h)
  | false :: ps, x :: xs, y :: ys, hAllFalse, h => by
    rw [sameAtNonPad_cons_false] at h
    cases hHead : allocByteBeq x y with
    | false => rw [hHead] at h; exact False.elim (boolFalseNeTrue h)
    | true =>
      rw [hHead, Bool.true_and] at h
      have hTail := sliceAllInitNoProv_eq_of_sameAtNonPad_allFalse ps xs ys
        (fun b hb => hAllFalse b (List.Mem.tail false hb)) h
      cases x with
      | uninit =>
        cases y with
        | uninit => rfl
        | init _ _ => exact False.elim (boolFalseNeTrue hHead)
      | init vx px =>
        cases y with
        | uninit => exact False.elim (boolFalseNeTrue hHead)
        | init vy py =>
          have hPr := allocByteBeq_true_init_prov vx vy px py hHead
          subst hPr
          cases px with
          | none => exact hTail
          | some _ => rfl

private theorem u32Mem_evalConstLit_of_lt (n : Nat) (hLt : n < 4294967296) :
    mirEvalConstLit (.int .i32 false) (.scalar (BitVec.ofNat 128 n)) =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩) := by
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
    natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hPow32 : (4294967296 : Nat) = Nat.pow 2 32 := rfl
  have hBv128 : (BitVec.ofNat 128 n).toNat = n :=
    bitVec128_ofNat_toNat_lt n 4294967296 hLt hPow128
  have hShift0 : Nat.shiftRight n 0 = n := rfl
  have hMod32 : (BitVec.ofNat 32 (Nat.shiftRight n 0)).toNat = n := by
    rw [hShift0]
    change Nat.mod n (Nat.pow 2 32) = n
    rw [← hPow32]
    exact natMod_eq_of_lt hLt
  have hTr :
      mirTruncateBits .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
    dsimp only [mirTruncateBits, mirBitWidth]
    rw [hBv128, hMod32]
  have hNe :
      (mirTruncateBits .i32 (BitVec.ofNat 128 n) != BitVec.ofNat 128 n) =
        false := by
    rw [hTr]
    dsimp only [bne, BEq.beq]
    rw [decide_eq_true (rfl : BitVec.ofNat 128 n = BitVec.ofNat 128 n)]
    rfl
  dsimp only [mirEvalConstLit]
  rw [ite_bool_false hNe, hTr]

/-- Constructive `LawfulTypedSpatialMemCodec` proof for Day-1 `u32MemCodec`
(non-vacuously exercising both `Trusted.MirSemantics.encodeVal` and
`Trusted.MirSemantics.decodeVal` agreement). -/
theorem u32MemCodec_lawful : LawfulTypedSpatialMemCodec u32MemCodec := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hEncLen : (execEncodeUInt execProfileTargetEndian 4 x.toNat).length = 4 :=
      execEncodeUInt_length execProfileTargetEndian 4 x.toNat
    have hMemLen : (u32MemEncode x).length = 4 := by
      dsimp only [u32MemEncode]
      rw [listLength_map]
      exact hEncLen
    have hNonPad :
        nonPadBytesInitialized [false, false, false, false]
          (u32MemEncode x) = true :=
      nonPad_map_init4 _ hEncLen
    have hProv : sliceAllInitNoProv (u32MemEncode x) = true :=
      sliceAllInitNoProv_map_none _
    have hCompat :
        valCompatWithTargetSpec (u32MemToSymVal x)
          (.mirTy (.int .i32 false)) = true :=
      mirCheckVal_u32_ofNat x.isLt
    have hBytesMatch :
        valAndBytesMatchTargetSpec true (.mirTy (.int .i32 false))
          (u32MemToSymVal x) (u32MemEncode x) = true := by
      dsimp only [valAndBytesMatchTargetSpec, primFieldBytesMatch,
        execLayoutOfTy, execIntLayout, u32MemToSymVal]
      rw [mirCheckVal_u32_ofNat x.isLt, u32ScalarEncode_eq x]
      change (true && (Nat.beq (u32MemEncode x).length 4 &&
        sliceAllInitNoProv (u32MemEncode x) &&
        allocBytesListBeq (u32MemEncode x) (u32MemEncode x))) = true
      rw [hMemLen, hProv, allocBytesListBeq_refl (u32MemEncode x)]
      rfl
    have hDecMem : u32MemDecode (u32MemEncode x) = some x := by
      dsimp only [u32MemDecode]
      rw [hMemLen, hProv, ite_bool_false (rfl : (!Nat.beq 4 4 || !true) = false)]
      dsimp only [u32MemEncode]
      rw [execInitBytes?_map_init]
      dsimp only
      have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
      have hXLt : x.toNat < Nat.pow 256 4 := by rw [hPow4]; exact x.isLt
      rw [decodeUInt_encodeUInt_of_lt execProfileTargetEndian 4 x.toNat hXLt,
        bitVec_ofNat_toNat 32 x]
    have hDecSym : u32MemFromSymVal (u32MemToSymVal x) = some x := by
      dsimp only [u32MemFromSymVal, u32MemToSymVal]
      have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
        natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
      have hToNat : (BitVec.ofNat 128 x.toNat).toNat = x.toNat :=
        bitVec128_ofNat_toNat_lt x.toNat 4294967296 x.isLt hPow128
      have hBlt : Nat.blt x.toNat 4294967296 = true :=
        natBle_of_le (x.toNat + 1) 4294967296 x.isLt
      rw [hToNat, hBlt, Bool.not_false, Bool.true_and, ite_bool_true rfl,
        bitVec_ofNat_toNat 32 x]
    exact ⟨hMemLen, hNonPad, hProv, hCompat, hBytesMatch, hDecMem, hDecSym⟩
  · intro v x hDec
    cases v with
    | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
    | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bytes _ => nomatch hDec
    | scalar sb =>
      cases sb with
      | mk wb sgb bb =>
        cases wb with
        | i8 | i16 | i64 | i128 | isize => nomatch hDec
        | i32 =>
          dsimp only [u32MemCodec, u32MemFromSymVal] at hDec
          cases sgb with
          | true => nomatch hDec
          | false =>
            cases hBlt : Nat.blt bb.toNat 4294967296 with
            | false => rw [hBlt] at hDec; nomatch hDec
            | true =>
              rw [hBlt, Bool.not_false, Bool.true_and, ite_bool_true rfl] at hDec
              injection hDec with hX
              subst hX
              dsimp only [u32MemCodec, u32MemToSymVal]
              have hBLt : bb.toNat < 4294967296 :=
                natLt_of_blt bb.toNat 4294967296 hBlt
              have hPow32 : Nat.pow 2 32 = 4294967296 := rfl
              have hBLtPow : bb.toNat < Nat.pow 2 32 := by
                rw [hPow32]; exact hBLt
              have hBv32 : (BitVec.ofNat 32 bb.toNat).toNat = bb.toNat := by
                change Nat.mod bb.toNat (Nat.pow 2 32) = bb.toNat
                exact natMod_eq_of_lt hBLtPow
              rw [hBv32, bitVec_ofNat_toNat 128 bb]
  · intro bs x hLen _ hProv hDec
    have hL4 : bs.length = 4 := hLen
    have hNoProv : sliceAllInitNoProv bs = true := hProv
    dsimp only [u32MemCodec, u32MemDecode] at hDec
    rw [hL4, hNoProv, ite_bool_false (rfl : (!Nat.beq 4 4 || !true) = false)] at hDec
    cases hInit : execInitBytes? bs with
    | none => rw [hInit] at hDec; nomatch hDec
    | some raw =>
      rw [hInit] at hDec
      injection hDec with hX
      subst hX
      have hRawLen : raw.length = 4 := by
        rw [execInitBytes?_len bs raw hInit]
        exact hL4
      have hBsEq : bs = raw.map (fun b => AllocByte.init b none) :=
        execInitBytes?_eq_map_none bs raw hNoProv hInit
      have hDecLtPow :
          execDecodeUInt execProfileTargetEndian raw <
            Nat.pow 256 raw.length :=
        execDecodeUInt_lt_pow execProfileTargetEndian raw
      rw [hRawLen] at hDecLtPow
      have hPow4 : Nat.pow 256 4 = Nat.pow 2 32 := rfl
      have hDecLt32 :
          execDecodeUInt execProfileTargetEndian raw < Nat.pow 2 32 := by
        rw [← hPow4]; exact hDecLtPow
      have hBv32 :
          (BitVec.ofNat 32
            (execDecodeUInt execProfileTargetEndian raw)).toNat =
            execDecodeUInt execProfileTargetEndian raw := by
        change Nat.mod _ (Nat.pow 2 32) = _
        exact natMod_eq_of_lt hDecLt32
      have hReenc :
          execEncodeUInt execProfileTargetEndian 4
            (BitVec.ofNat 32
              (execDecodeUInt execProfileTargetEndian raw)).toNat =
            raw := by
        rw [hBv32, ← hRawLen]
        exact execEncodeUInt_execDecodeUInt execProfileTargetEndian raw
      dsimp only [u32MemCodec, u32MemEncode]
      rw [hReenc, ← hBsEq]
      exact sameAtNonPad_allFalse_refl 4 bs hL4
  · intro ty _ hTy _
    injection hTy with hTyEq
    subst hTyEq
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [← execEncodeVal_eq]
      have hEnd : profileTargetEndian = execProfileTargetEndian := rfl
      have hPow128 : 4294967296 ≤ Nat.pow 2 128 :=
        natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
      have hToNat : (BitVec.ofNat 128 x.toNat).toNat = x.toNat :=
        bitVec128_ofNat_toNat_lt x.toNat 4294967296 x.isLt hPow128
      rw [hEnd]
      dsimp only [u32MemCodec, execEncodeVal, execByteSize,
        u32MemToSymVal, u32MemEncode]
      rw [mirCheckVal_u32_ofNat x.isLt,
        ite_bool_false (rfl : (!true) = false), hToNat]
    · intro x
      rw [← execDecodeVal_eq]
      have hEncLen :
          (execEncodeUInt execProfileTargetEndian 4 x.toNat).length = 4 :=
        execEncodeUInt_length execProfileTargetEndian 4 x.toNat
      have hMemLen : (u32MemEncode x).length = 4 := by
        dsimp only [u32MemEncode]; rw [listLength_map]; exact hEncLen
      have hEnd : profileTargetEndian = execProfileTargetEndian := rfl
      rw [hEnd]
      dsimp only [u32MemCodec, execDecodeVal, execDecodeValFallback,
        execLayoutOfTy, execIntLayout]
      rw [hMemLen, ite_bool_false (rfl : (!Nat.beq 4 4) = false),
        ite_bool_false (rfl : Nat.beq 4 0 = false)]
      dsimp only [u32MemEncode]
      rw [execInitBytes?_map_init]
      dsimp only
      have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
      have hXLt : x.toNat < Nat.pow 256 4 := by rw [hPow4]; exact x.isLt
      rw [decodeUInt_encodeUInt_of_lt execProfileTargetEndian 4 x.toNat hXLt,
        u32Mem_evalConstLit_of_lt x.toNat x.isLt]
      rfl
    · intro bs x hLen _ hProv _ hDec
      have hL4 : bs.length = 4 := hLen
      have hNoProv : sliceAllInitNoProv bs = true := hProv
      rw [← execDecodeVal_eq]
      have hEnd : profileTargetEndian = execProfileTargetEndian := rfl
      rw [hEnd]
      dsimp only [u32MemCodec, u32MemDecode] at hDec
      rw [hL4, hNoProv, ite_bool_false (rfl : (!Nat.beq 4 4 || !true) = false)] at hDec
      dsimp only [u32MemCodec, execDecodeVal, execDecodeValFallback,
        execLayoutOfTy, execIntLayout]
      rw [hL4, ite_bool_false (rfl : (!Nat.beq 4 4) = false),
        ite_bool_false (rfl : Nat.beq 4 0 = false)]
      cases hInit : execInitBytes? bs with
      | none => rw [hInit] at hDec; nomatch hDec
      | some raw =>
        rw [hInit] at hDec
        injection hDec with hX
        subst hX
        have hRawLen : raw.length = 4 := by
          rw [execInitBytes?_len bs raw hInit]
          exact hL4
        have hDecLtPow :
            execDecodeUInt execProfileTargetEndian raw <
              Nat.pow 256 raw.length :=
          execDecodeUInt_lt_pow execProfileTargetEndian raw
        rw [hRawLen] at hDecLtPow
        have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
        have hDecLt : execDecodeUInt execProfileTargetEndian raw < 4294967296 := by
          rw [← hPow4]; exact hDecLtPow
        have hPow32 : Nat.pow 2 32 = 4294967296 := rfl
        have hDecLt32 :
            execDecodeUInt execProfileTargetEndian raw < Nat.pow 2 32 := by
          rw [hPow32]; exact hDecLt
        have hBv32 :
            (BitVec.ofNat 32
              (execDecodeUInt execProfileTargetEndian raw)).toNat =
              execDecodeUInt execProfileTargetEndian raw := by
          change Nat.mod (execDecodeUInt execProfileTargetEndian raw)
            (Nat.pow 2 32) = execDecodeUInt execProfileTargetEndian raw
          exact natMod_eq_of_lt hDecLt32
        dsimp only [u32MemToSymVal]
        rw [hBv32, u32Mem_evalConstLit_of_lt _ hDecLt]
  · intro b1 b2 hL1 hL2 _ _ hSame
    have h1 : b1.length = 4 := hL1
    have h2 : b2.length = 4 := hL2
    have hMaskAllFalse :
        ∀ b, b ∈ [false, false, false, false] → b = false := by
      intro b hb
      cases hb with | head _ => rfl | tail _ hb =>
      cases hb with | head _ => rfl | tail _ hb =>
      cases hb with | head _ => rfl | tail _ hb =>
      cases hb with | head _ => rfl | tail _ hb => cases hb
    have hNoProvEq : sliceAllInitNoProv b1 = sliceAllInitNoProv b2 :=
      sliceAllInitNoProv_eq_of_sameAtNonPad_allFalse
        [false, false, false, false] b1 b2 hMaskAllFalse hSame
    have hInitEq : execInitBytes? b1 = execInitBytes? b2 :=
      extractInitRawBytes_eq_of_sameAtNonPad_allFalse
        [false, false, false, false] b1 b2 hMaskAllFalse hSame
    dsimp only [u32MemCodec, u32MemDecode]
    rw [h1, h2, hNoProvEq, hInitEq]

/-! ### Soundness of `BodySpatialCtx` Captured-MIR Type Authentication -/

private theorem boolAnd_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => nomatch h

private theorem boolAnd_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => nomatch h

private theorem boolBeq_eq {b1 b2 : Bool} (h : (b1 == b2) = true) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | nomatch h

private theorem mirIntWidthBeq_sound {w1 w2 : IntWidth}
    (h : mirIntWidthBeq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | nomatch h

private theorem mirMutabilityBeq_sound {m1 m2 : Mutability}
    (h : mirMutabilityBeq m1 m2 = true) : m1 = m2 := by
  cases m1 <;> cases m2 <;> first | rfl | nomatch h

private theorem mirNatListBeq_sound {xs ys : List Nat}
    (h : mirNatListBeq xs ys = true) : xs = ys := by
  revert ys h
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => nomatch h
    | cons y ys =>
      have h1 : (Nat.beq x y && mirNatListBeq xs ys) = true := h
      rw [natEq_of_beq x y (boolAnd_left h1), ih (boolAnd_right h1)]

private theorem mirEnumTagReprBeq_sound {r1 r2 : EnumTagRepr}
    (h : mirEnumTagReprBeq r1 r2 = true) : r1 = r2 := by
  cases r1 with
  | zeroSized =>
    cases r2 with
    | zeroSized => rfl
    | scalar _ _ => nomatch h
  | scalar w1 s1 =>
    cases r2 with
    | zeroSized => nomatch h
    | scalar w2 s2 =>
      dsimp only [mirEnumTagReprBeq] at h
      rw [mirIntWidthBeq_sound (boolAnd_left h), boolBeq_eq (boolAnd_right h)]

private theorem mirEnumTyBeq_sound {e1 e2 : EnumTy}
    (h : mirEnumTyBeq e1 e2 = true) : e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 dsList1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 dsList2 =>
      dsimp only [mirEnumTyBeq] at h
      have h1234 := boolAnd_left h
      have h5 := mirNatListBeq_sound (boolAnd_right h)
      have h123 := boolAnd_left h1234
      have h4 := mirEnumTagReprBeq_sound (boolAnd_right h1234)
      have h12 := boolAnd_left h123
      have h3 := boolBeq_eq (boolAnd_right h123)
      have h1 := natEq_of_beq id1 id2 (boolAnd_left h12)
      have h2 := mirIntWidthBeq_sound (boolAnd_right h12)
      rw [h1, h2, h3, h4, h5]

private theorem mirTyListFoldr_sound {ih : MirTy → MirTy → Bool}
    (hIh : ∀ x y, ih x y = true → x = y) :
    ∀ {fs1 fs2 : List MirTy},
      fs1.foldr
        (fun t1 ihFs rs =>
          match rs with
          | [] => false
          | t2 :: rs' => ih t1 t2 && ihFs rs')
        (fun rs => rs.isEmpty)
        fs2 = true →
      fs1 = fs2 := by
  intro fs1
  induction fs1 with
  | nil =>
    intro fs2 h
    cases fs2 with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons t1 ts1 ihList =>
    intro fs2 h
    cases fs2 with
    | nil => nomatch h
    | cons t2 ts2 =>
      dsimp only [List.foldr] at h
      rw [hIh t1 t2 (boolAnd_left h), ihList (boolAnd_right h)]

/-- Propositional soundness of `mirTyBeqAt`: `mirTyBeqAt d a b = true` implies
`a = b` at every depth bound `d`. -/
theorem mirTyBeqAt_sound (d : Nat) :
    ∀ {a b : MirTy}, mirTyBeqAt d a b = true → a = b := by
  induction d with
  | zero =>
    intro a b h
    dsimp only [mirTyBeqAt, natFold, Nat.recCompiled] at h
    cases a with
    | bool => cases b <;> first | rfl | nomatch h
    | unit => cases b <;> first | rfl | nomatch h
    | never => cases b <;> first | rfl | nomatch h
    | char => cases b <;> first | rfl | nomatch h
    | ordering => cases b <;> first | rfl | nomatch h
    | unsupported => cases b <;> first | rfl | nomatch h
    | int w1 s1 =>
      cases b with
      | int w2 s2 =>
        rw [mirIntWidthBeq_sound (boolAnd_left h), boolBeq_eq (boolAnd_right h)]
      | _ => nomatch h
    | enum e1 =>
      cases b with
      | enum e2 => rw [mirEnumTyBeq_sound h]
      | _ => nomatch h
    | tuple _ | array _ _ | ref _ _ | rawPtr _ _ | slice _ | rangeTo _
    | rangeFrom _
    | range _ | option _ => nomatch h
  | succ d ih =>
    intro a b h
    dsimp only [mirTyBeqAt, natFold, Nat.recCompiled] at h
    cases a with
    | bool => cases b <;> first | rfl | nomatch h
    | unit => cases b <;> first | rfl | nomatch h
    | never => cases b <;> first | rfl | nomatch h
    | char => cases b <;> first | rfl | nomatch h
    | ordering => cases b <;> first | rfl | nomatch h
    | unsupported => cases b <;> first | rfl | nomatch h
    | int w1 s1 =>
      cases b with
      | int w2 s2 =>
        rw [mirIntWidthBeq_sound (boolAnd_left h), boolBeq_eq (boolAnd_right h)]
      | _ => nomatch h
    | enum e1 =>
      cases b with
      | enum e2 => rw [mirEnumTyBeq_sound h]
      | _ => nomatch h
    | tuple fs1 =>
      cases b with
      | tuple fs2 =>
        rw [mirTyListFoldr_sound (fun x y hxy => ih hxy) h]
      | _ => nomatch h
    | ref m1 p1 =>
      cases b with
      | ref m2 p2 =>
        rw [mirMutabilityBeq_sound (boolAnd_left h), ih (boolAnd_right h)]
      | _ => nomatch h
    | rawPtr m1 p1 =>
      cases b with
      | rawPtr m2 p2 =>
        rw [mirMutabilityBeq_sound (boolAnd_left h), ih (boolAnd_right h)]
      | _ => nomatch h
    | slice p1 =>
      cases b with
      | slice p2 => rw [ih h]
      | _ => nomatch h
    | array p1 n1 =>
      cases b with
      | array p2 n2 =>
        rw [natEq_of_beq n1 n2 (boolAnd_left h), ih (boolAnd_right h)]
      | _ => nomatch h
    | rangeTo p1 =>
      cases b with
      | rangeTo p2 => rw [ih h]
      | _ => nomatch h
    | rangeFrom p1 =>
      cases b with
      | rangeFrom p2 => rw [ih h]
      | _ => nomatch h
    | range p1 =>
      cases b with
      | range p2 => rw [ih h]
      | _ => nomatch h
    | option p1 =>
      cases b with
      | option p2 => rw [ih h]
      | _ => nomatch h

/-- Propositional soundness of `mirTyBeq`. -/
theorem mirTyBeq_sound {a b : MirTy} (h : mirTyBeq a b = true) : a = b :=
  mirTyBeqAt_sound 8 h

/-- Propositional soundness of `auditedFieldSpecsBeq`. -/
theorem auditedFieldSpecsBeq_sound {fs1 fs2 : List AuditedFieldSpec}
    (h : auditedFieldSpecsBeq fs1 fs2 = true) : fs1 = fs2 := by
  revert fs2 h
  induction fs1 with
  | nil =>
    intro fs2 h
    cases fs2 with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons f1 r1 ih =>
    intro fs2 h
    cases fs2 with
    | nil => nomatch h
    | cons f2 r2 =>
      dsimp only [auditedFieldSpecsBeq, List.foldr] at h
      have hHead := boolAnd_left h
      have hTail := ih (boolAnd_right h)
      cases f1 with
      | mk off1 ty1 =>
        cases f2 with
        | mk off2 ty2 =>
          dsimp only [auditedFieldSpecBeq] at hHead
          rw [natEq_of_beq off1 off2 (boolAnd_left hHead),
            mirTyBeq_sound (boolAnd_right hHead), hTail]

private theorem specsFoldr_toCapturedMirTy_eq (ctx : BodySpatialCtx) :
    ∀ (capTys : List MirTy) (idx : Nat) (specs : List SpatialTargetSpec),
      capTys.foldr
        (fun capTy k i remSpecs =>
          match remSpecs with
          | [] => false
          | spec :: restSpecs =>
            let okHere : Bool :=
              match spec with
              | .mirTy ty =>
                mirTyBeq capTy ty && !hasAnyAdtEntryForLocal ctx.adtLocals i
              | .reprCAdt adtTag fields =>
                (match capTy with | .unsupported => true | _ => false) &&
                (match findUniqueAdtEntryForLocal ctx.adtLocals i with
                 | some e =>
                   Nat.beq e.adtTag adtTag &&
                   auditedFieldSpecsBeq e.fields fields
                 | none => false)
            okHere && k (i + 1) restSpecs)
        (fun _ remSpecs => match remSpecs with | [] => true | _ :: _ => false)
        idx
        specs = true →
      specs.map SpatialTargetSpec.toCapturedMirTy = capTys := by
  intro capTys
  induction capTys with
  | nil =>
    intro idx specs h
    cases specs with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons capTy restCap ih =>
    intro idx specs h
    cases specs with
    | nil => nomatch h
    | cons spec restSpecs =>
      dsimp only [List.foldr] at h
      have hHere := boolAnd_left h
      have hRest := ih (idx + 1) restSpecs (boolAnd_right h)
      cases spec with
      | mirTy ty =>
        dsimp only [SpatialTargetSpec.toCapturedMirTy, List.map]
        rw [mirTyBeq_sound (boolAnd_left hHere), hRest]
      | reprCAdt tag fields =>
        dsimp only [SpatialTargetSpec.toCapturedMirTy, List.map]
        have hCap := boolAnd_left hHere
        cases capTy with
        | unsupported => rw [hRest]
        | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _
        | rangeFrom _
        | range _ | option _ => nomatch hCap

/-- Whenever `specsMatchBodyCtx ctx specs = true`, projecting `specs` via
`SpatialTargetSpec.toCapturedMirTy` recovers `ctx.body.locals` identically. -/
theorem specsMatchBodyCtx_toCapturedMirTy_eq (ctx : BodySpatialCtx)
    (specs : List SpatialTargetSpec)
    (h : specsMatchBodyCtx ctx specs = true) :
    specs.map SpatialTargetSpec.toCapturedMirTy = ctx.body.locals := by
  dsimp only [specsMatchBodyCtx] at h
  exact specsFoldr_toCapturedMirTy_eq ctx ctx.body.locals 0 specs
    (boolAnd_right h)

private theorem specsFoldr_slot_sound (ctx : BodySpatialCtx) :
    ∀ (capTys : List MirTy) (base off : Nat) (specs : List SpatialTargetSpec)
      (spec : SpatialTargetSpec),
      capTys.foldr
        (fun capTy k i remSpecs =>
          match remSpecs with
          | [] => false
          | s :: restSpecs =>
            let okHere : Bool :=
              match s with
              | .mirTy ty =>
                mirTyBeq capTy ty && !hasAnyAdtEntryForLocal ctx.adtLocals i
              | .reprCAdt adtTag fields =>
                (match capTy with | .unsupported => true | _ => false) &&
                (match findUniqueAdtEntryForLocal ctx.adtLocals i with
                 | some e =>
                   Nat.beq e.adtTag adtTag &&
                   auditedFieldSpecsBeq e.fields fields
                 | none => false)
            okHere && k (i + 1) restSpecs)
        (fun _ remSpecs => match remSpecs with | [] => true | _ :: _ => false)
        base
        specs = true →
      mirListGet? specs off = some spec →
      match spec with
      | .mirTy ty =>
        mirListGet? capTys off = some ty ∧
        hasAnyAdtEntryForLocal ctx.adtLocals (base + off) = false
      | .reprCAdt tag fs =>
        mirListGet? capTys off = some .unsupported ∧
        ∃ e, findUniqueAdtEntryForLocal ctx.adtLocals (base + off) = some e ∧
          e.adtTag = tag ∧ e.fields = fs := by
  intro capTys
  induction capTys with
  | nil =>
    intro base off specs spec h hGet
    cases specs with
    | nil => nomatch hGet
    | cons _ _ => nomatch h
  | cons capTy restCap ih =>
    intro base off specs spec h hGet
    cases specs with
    | nil => nomatch h
    | cons sHead restSpecs =>
      dsimp only [List.foldr] at h
      have hHere := boolAnd_left h
      have hRest := boolAnd_right h
      cases off with
      | zero =>
        have hEqS : sHead = spec := by
          dsimp only [mirListGet?, List.foldr] at hGet
          injection hGet with hE
        subst hEqS
        have hBaseZero : base + 0 = base := rfl
        rw [hBaseZero]
        cases sHead with
        | mirTy ty =>
          have hTyEq := mirTyBeq_sound (boolAnd_left hHere)
          have hNoAdt := boolAnd_right hHere
          refine ⟨by rw [hTyEq]; rfl, ?_⟩
          cases hAny : hasAnyAdtEntryForLocal ctx.adtLocals base with
          | false => rfl
          | true => rw [hAny] at hNoAdt; nomatch hNoAdt
        | reprCAdt tag fs =>
          have hCap := boolAnd_left hHere
          have hAdt := boolAnd_right hHere
          cases capTy with
          | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
          | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _
          | rangeFrom _
          | range _ | option _ => nomatch hCap
          | unsupported =>
            cases hFind : findUniqueAdtEntryForLocal ctx.adtLocals base with
            | none => rw [hFind] at hAdt; nomatch hAdt
            | some e =>
              rw [hFind] at hAdt
              exact ⟨rfl, e, rfl,
                natEq_of_beq e.adtTag tag (boolAnd_left hAdt),
                auditedFieldSpecsBeq_sound (boolAnd_right hAdt)⟩
      | succ off' =>
        have hGetRest : mirListGet? restSpecs off' = some spec := by
          dsimp only [mirListGet?, List.foldr] at hGet
          exact hGet
        have hStep := ih (base + 1) off' restSpecs spec hRest hGetRest
        have hAdd : (base + 1) + off' = base + (off' + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 off']
        have hCapSucc :
            mirListGet? (capTy :: restCap) (off' + 1) =
              mirListGet? restCap off' := rfl
        rw [hCapSucc, ← hAdd]
        exact hStep

/-- Per-slot soundness of `specsMatchBodyCtx`: every `.mirTy ty` in `specs`
equals `ctx.body.locals[reg]` with no `adtLocals` entry, and every
`.reprCAdt tag fs` in `specs` sits at a `MirTy.unsupported` slot of
`ctx.body.locals` authenticated by a unique matching `ctx.adtLocals` entry. -/
theorem specsMatchBodyCtx_slot_sound (ctx : BodySpatialCtx)
    (specs : List SpatialTargetSpec) (reg : LocalId) (spec : SpatialTargetSpec)
    (hMatch : specsMatchBodyCtx ctx specs = true) :
    mirListGet? specs reg = some spec →
    match spec with
    | .mirTy ty =>
      mirListGet? ctx.body.locals reg = some ty ∧
      hasAnyAdtEntryForLocal ctx.adtLocals reg = false
    | .reprCAdt tag fs =>
      mirListGet? ctx.body.locals reg = some .unsupported ∧
      ∃ e, findUniqueAdtEntryForLocal ctx.adtLocals reg = some e ∧
        e.adtTag = tag ∧ e.fields = fs := by
  intro hGet
  dsimp only [specsMatchBodyCtx] at hMatch
  have h0 : 0 + reg = reg := Nat.zero_add reg
  have hStep :=
    specsFoldr_slot_sound ctx ctx.body.locals 0 reg specs spec
      (boolAnd_right hMatch) hGet
  rw [h0] at hStep
  exact hStep

end Anneal.PureLift

end
