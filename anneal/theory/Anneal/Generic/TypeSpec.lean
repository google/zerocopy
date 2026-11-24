-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted.MirAst.Types
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Bytes
public import Anneal.Generic.Syntax

@[expose] public section

namespace Anneal.Generic

open Trusted.MirAst Trusted.MirSemantics

/-!
# Parametric Type Layouts (`Anneal.Generic.TypeSpec`)

Zero-TCB `theory/` layout specifications for open generic type parameters
(`TypeLayoutSpec` in `Type 0`), well-formedness (`WellFormedTypeLayoutSpec`),
byte-level language validity predicates (`ByteRole`, `ByteMatchesRoleBool`,
`allBytesMatchRolesBool`, `LangValid`), and compositional evaluation of open
MIR types (`evalOpenTySpec`) supporting sized scalars, references/raw pointers,
slices (`&[u8]`), arrays, ADTs, and type parameters.

See `Anneal.Generic.OpenSemantics` ("Known modeling gaps") for current pointer
and slice validity modeling simplifications that must be closed before any
future promotion to `trusted/`.
-/

/-- Pointer metadata carried by thin vs. wide references and raw pointers
(abstracting thin pointers alongside slice-length and vtable-id metadata; cf.
`rustc_abi::PointeeInfo` in `compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
inductive PtrMeta where
  | none
  | sliceLen (len : Nat)
  | vtable (id : Nat)

/-- Byte-level scalar validity constraint (`rustc_abi::Scalar::Initialized`
carrying `valid_range: WrappingRange`, plus uninitialized/padding vs.
value-byte distinctions; `compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).

Each variant captures the Rust language-level byte validity rules checked at
both single-byte and whole-scalar span granularity:
- `anyByte`: arbitrary initialized byte (never uninitialized).
- `boolByte`: `0` or `1` (`bool` validity range `0..=1`).
- `charScalar bytePos`: big-endian byte position `0..3` of a `char` whose 4-byte
  word must decode to a Unicode scalar value (`0x0000..=0xD7FF` or
  `0xE000..=0x10FFFF`, `src/types/char.md`).
- `orderingByte`: `255` (`-1_i8`), `0`, or `1` (`core::cmp::Ordering`).
- `intRange min max width`: unsigned scalar bytes decoded at `width` in
  `[min, max]` (`min..=max`).
- `enumDiscr ety`: tag bytes of admitted fieldless enum `ety` resolving to a
  declared variant in `ety.discriminants`.
- `refPtr pointeeAlignLog2 isRef`: pointer byte; when `isRef = true` (`&T` /
  `&mut T`), every byte of the 8-byte pointer must carry provenance
  (`prov = some _`), and its address must be non-zero (`≠ 0`) and aligned to
  `2^pointeeAlignLog2` (`src/behavior-considered-undefined.md`). -/
inductive ScalarValidity where
  | anyByte
  | boolByte
  | charScalar (bytePos : Nat)
  | orderingByte
  | intRange (min max : Nat) (width : IntWidth)
  | enumDiscr (ety : EnumTy)
  | refPtr (pointeeAlignLog2 : Nat) (isRef : Bool)

/-- Structural equality on `ScalarValidity`. -/
noncomputable def ScalarValidity.beq :
    ScalarValidity → ScalarValidity → Bool
  | .anyByte, .anyByte => true
  | .boolByte, .boolByte => true
  | .charScalar p₁, .charScalar p₂ => Nat.beq p₁ p₂
  | .orderingByte, .orderingByte => true
  | .intRange lo₁ hi₁ w₁, .intRange lo₂ hi₂ w₂ =>
      Nat.beq lo₁ lo₂ && Nat.beq hi₁ hi₂ && IntWidth.beq w₁ w₂
  | .enumDiscr e₁, .enumDiscr e₂ => EnumTy.beq e₁ e₂
  | .refPtr a₁ r₁, .refPtr a₂ r₂ => Nat.beq a₁ a₂ && (r₁ == r₂)
  | _, _ => false

/-- Per-byte semantic role within a type representation: either padding (may
hold `AllocByte.uninit`) or a value byte constrained by `ScalarValidity`. -/
inductive ByteRole where
  | padding
  | valueByte (validity : ScalarValidity)

/-- Structural equality on `ByteRole`. -/
noncomputable def ByteRole.beq : ByteRole → ByteRole → Bool
  | .padding, .padding => true
  | .valueByte v₁, .valueByte v₂ => ScalarValidity.beq v₁ v₂
  | _, _ => false

/-- Theoretical maximum Rust object size on a 64-bit target (`isize::MAX`,
`2^63 - 1`, cf. `TargetDataLayout::obj_size_bound`;
`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "The theoretical maximum object size is defined as the maximum positive
> `isize` value." -/
noncomputable def isizeMax : Nat := Nat.pow 2 63 - 1

/-- Maximum Rust ABI alignment exponent (`2^29` bytes per `Align::MAX`,
`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const MAX: Align = Align { pow2: 29 };" -/
noncomputable def maxAlignLog2 : Nat := 29

/-- Abstract parametric type layout specification (`Type 0`), exposing every
layout and byte-validity property observable by generic MIR semantics without
committing to a concrete monomorphic type. `enumTy?` distinguishes fieldless
enums from unit/struct ZSTs during `Val` classification. -/
structure TypeLayoutSpec where
  isSized : Bool
  alignLog2 : Nat
  sizeForMeta : PtrMeta → Option Nat
  inhabited : Bool
  hasUnsafeCell : Bool
  rolesForMeta : PtrMeta → Option (List ByteRole)
  enumTy? : Option EnumTy := none

/-- Repeat `x` `n` times. -/
noncomputable def repeatItem {α : Type} (x : α) : Nat → List α
  | 0 => []
  | n + 1 => x :: repeatItem x n

/-- Repeat list `xs` `m` times (`xs.length * m` total). -/
noncomputable def repeatConcat {α : Type} (xs : List α) : Nat → List α
  | 0 => []
  | m + 1 => xs ++ repeatConcat xs m

/-- Split the first `n` elements from `xs`, returning `none` if shorter. -/
noncomputable def takeSplit? {α : Type} :
    Nat → List α → Option (List α × List α)
  | 0, xs => some ([], xs)
  | _ + 1, [] => none
  | n + 1, x :: xs =>
      match takeSplit? n xs with
      | some (hd, tl) => some (x :: hd, tl)
      | none => none

/-- Verify that every element of `rs` equals `expected` via `ByteRole.beq`. -/
noncomputable def allRolesMatchExact (expected : ByteRole) :
    List ByteRole → Bool
  | [] => true
  | r :: rs => ByteRole.beq r expected && allRolesMatchExact expected rs

/-- Verify that every `AllocByte` in `bs` is initialized with provenance
(`prov = some _`), returning its raw bytes if valid. -/
noncomputable def initProvBytes? : List AllocByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init _ none :: _ => none
  | .init byte (some _) :: rest =>
      match initProvBytes? rest with
      | some bs => some (byte :: bs)
      | none => none

/-- Single-byte validity rule against a `ByteRole` (computable `Bool` check),
enforcing `0/1` for `boolByte`, `-1/0/1` for `orderingByte`, MSB bounds for
`charScalar`, 1-byte range/tag bounds for `.i8` `intRange`/`enumDiscr`, and
mandatory provenance (`prov = some _`) for references (`refPtr _ true`).
Full multi-byte checks for `char`, wider integers/enums, and reference
non-null/alignment are enforced alongside single-byte checks by
`allBytesMatchRolesBool`. -/
noncomputable def ByteMatchesRoleBool (b : AllocByte) (role : ByteRole) :
    Bool :=
  match role with
  | .padding => true
  | .valueByte .anyByte =>
      match b with
      | .init _ _ => true
      | .uninit => false
  | .valueByte .boolByte =>
      match b with
      | .init byte _ => byte == (0 : UInt8) || byte == (1 : UInt8)
      | .uninit => false
  | .valueByte (.charScalar pos) =>
      match b with
      | .init byte _ =>
          if Nat.beq pos 0 then byte == (0 : UInt8)
          else if Nat.beq pos 1 then Nat.ble byte.toNat 0x10
          else true
      | .uninit => false
  | .valueByte .orderingByte =>
      match b with
      | .init byte _ =>
          byte == (255 : UInt8) || byte == (0 : UInt8) || byte == (1 : UInt8)
      | .uninit => false
  | .valueByte (.intRange min max w) =>
      match b with
      | .init byte _ =>
          match w with
          | .i8 => Nat.ble min byte.toNat && Nat.ble byte.toNat max
          | _ => true
      | .uninit => false
  | .valueByte (.enumDiscr ety) =>
      if !enumAdmitted ety then
        false
      else
        match b with
        | .init byte _ =>
            match ety.tagRepr with
            | .scalar .i8 _ =>
                match evalConstLit (.enum ety)
                    (.scalar (BitVec.ofNat 128 byte.toNat)) with
                | .ok _ => true
                | .error _ => false
            | .scalar _ _ => true
            | .zeroSized => false
        | .uninit => false
  | .valueByte (.refPtr _ isRef) =>
      match b with
      | .init _ prov => if isRef then prov.isSome else true
      | .uninit => false

/-- Check a 4-byte big-endian `char` scalar slice against `isUnicodeScalar`. -/
noncomputable def checkCharSpan (bytes : List AllocByte) : Bool :=
  match initBytes? bytes with
  | some raw => isUnicodeScalar (decodeUInt profileTargetEndian raw)
  | none => false

/-- Check a `w.byteSize`-byte integer scalar slice against `[min, max]`. -/
noncomputable def checkIntRangeSpan (min max : Nat)
    (bytes : List AllocByte) : Bool :=
  match initBytes? bytes with
  | some raw =>
      let v := decodeUInt profileTargetEndian raw
      Nat.ble min v && Nat.ble v max
  | none => false

/-- Check a `tagW.byteSize`-byte fieldless enum tag slice via `evalConstLit`.
-/
noncomputable def checkEnumDiscrSpan (ety : EnumTy)
    (bytes : List AllocByte) : Bool :=
  if !enumAdmitted ety then
    false
  else
    match initBytes? bytes with
    | some raw =>
        let bits := BitVec.ofNat 128 (decodeUInt profileTargetEndian raw)
        match evalConstLit (.enum ety) (.scalar bits) with
        | .ok _ => true
        | .error _ => false
    | none => false

/-- Check an 8-byte reference pointer span: every byte must be initialized with
provenance (`prov = some _`), non-null (`addr ≠ 0`), and aligned to `2^align`.
-/
noncomputable def checkRefPtrSpan (alignLog2 : Nat)
    (bytes : List AllocByte) : Bool :=
  match initProvBytes? bytes with
  | some raw =>
      let addr := decodeUInt profileTargetEndian raw
      !Nat.beq addr 0 && Nat.beq (Nat.mod addr (Nat.pow 2 alignLog2)) 0
  | none => false

/-- Fuel-bounded multi-byte role validator verifying both individual byte roles
(`ByteMatchesRoleBool`) and multi-byte scalar spans (`charScalar`, `intRange`,
`enumDiscr`, `refPtr _ true`). -/
noncomputable def allBytesMatchRolesAux :
    Nat → List AllocByte → List ByteRole → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | f + 1, b :: bs, r :: rs =>
      if !ByteMatchesRoleBool b r then
        false
      else
        match r with
        | .valueByte (.charScalar 0) =>
            match takeSplit? 4 (b :: bs), takeSplit? 4 (r :: rs) with
            | some (bSpan, bRest), some (rSpan, rRest) =>
                let expectRoles :=
                  [ .valueByte (.charScalar 0)
                  , .valueByte (.charScalar 1)
                  , .valueByte (.charScalar 2)
                  , .valueByte (.charScalar 3) ]
                List.beq (rSpan.zipWith ByteRole.beq expectRoles)
                  [true, true, true, true] &&
                checkCharSpan bSpan &&
                allBytesMatchRolesAux f bRest rRest
            | _, _ => false
        | .valueByte (.charScalar _) => false
        | .valueByte (.intRange min max w) =>
            match takeSplit? w.byteSize (b :: bs),
                  takeSplit? w.byteSize (r :: rs) with
            | some (bSpan, bRest), some (rSpan, rRest) =>
                allRolesMatchExact (.valueByte (.intRange min max w)) rSpan &&
                checkIntRangeSpan min max bSpan &&
                allBytesMatchRolesAux f bRest rRest
            | _, _ => false
        | .valueByte (.enumDiscr ety) =>
            match ety.tagRepr with
            | .zeroSized => false
            | .scalar tagW _ =>
                match takeSplit? tagW.byteSize (b :: bs),
                      takeSplit? tagW.byteSize (r :: rs) with
                | some (bSpan, bRest), some (rSpan, rRest) =>
                    allRolesMatchExact (.valueByte (.enumDiscr ety)) rSpan &&
                    checkEnumDiscrSpan ety bSpan &&
                    allBytesMatchRolesAux f bRest rRest
                | _, _ => false
        | .valueByte (.refPtr align true) =>
            match takeSplit? 8 (b :: bs), takeSplit? 8 (r :: rs) with
            | some (bSpan, bRest), some (rSpan, rRest) =>
                allRolesMatchExact (.valueByte (.refPtr align true)) rSpan &&
                checkRefPtrSpan align bSpan &&
                allBytesMatchRolesAux f bRest rRest
            | _, _ => false
        | .padding | .valueByte .anyByte | .valueByte .boolByte
        | .valueByte .orderingByte | .valueByte (.refPtr _ false) =>
            allBytesMatchRolesAux f bs rs
  | _ + 1, _, _ => false

/-- Decidable whole-slice validity check matching `bs` against `roles`. -/
noncomputable def allBytesMatchRolesBool (bs : List AllocByte)
    (roles : List ByteRole) : Bool :=
  allBytesMatchRolesAux (bs.length + 1) bs roles

/-- Decidable Rust language-level validity check (`LangValidBool`): requires
`spec.inhabited`, defined `sizeForMeta m`/`rolesForMeta m`, matching byte
length, and `allBytesMatchRolesBool bs roles`. Matches `validity.rs`
uninhabited-layout validation (`throw_validation_failure!`;
`compiler/rustc_const_eval/src/interpret/validity.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "if place.layout.is_uninhabited() {" -/
noncomputable def LangValidBool (spec : TypeLayoutSpec) (m : PtrMeta)
    (bs : List AllocByte) : Bool :=
  spec.inhabited &&
  match spec.sizeForMeta m, spec.rolesForMeta m with
  | some sz, some roles =>
      Nat.beq bs.length sz &&
      Nat.beq roles.length sz &&
      allBytesMatchRolesBool bs roles
  | _, _ => false

/-- Rust language-level validity invariant (`LangValid`). -/
def LangValid (spec : TypeLayoutSpec) (m : PtrMeta)
    (bs : List AllocByte) : Prop :=
  LangValidBool spec m bs = true

/-- Consistency invariant on a `TypeLayoutSpec`:
1. Sized types report `sizeForMeta .none = some sz` and matching-length
   `rolesForMeta .none = some roles`.
2. Every defined `sizeForMeta m = some sz` stays within `isizeMax` and agrees
   in byte length with `rolesForMeta m`.
3. Every defined `rolesForMeta m` agrees with `sizeForMeta m`.
4. Alignment exponent satisfies `alignLog2 ≤ maxAlignLog2`.
5. Inhabited specs admit at least one `LangValid` byte representation (for
   sized specs at `.none`, and for defined unsized slices at `.sliceLen len`),
   blocking vacuous self-contradictory layout specs. -/
def WellFormedTypeLayoutSpec (spec : TypeLayoutSpec) : Prop :=
  (spec.isSized = true →
    ∃ sz : Nat, ∃ roles : List ByteRole,
      spec.sizeForMeta .none = some sz ∧
      spec.rolesForMeta .none = some roles ∧
      roles.length = sz) ∧
  (∀ m : PtrMeta, ∀ sz : Nat,
    spec.sizeForMeta m = some sz →
      sz ≤ isizeMax ∧
      ∃ roles : List ByteRole,
        spec.rolesForMeta m = some roles ∧ roles.length = sz) ∧
  (∀ m : PtrMeta, ∀ roles : List ByteRole,
    spec.rolesForMeta m = some roles →
      ∃ sz : Nat, spec.sizeForMeta m = some sz ∧ roles.length = sz) ∧
  spec.alignLog2 ≤ maxAlignLog2 ∧
  (spec.inhabited = true →
    (spec.isSized = true →
      ∃ bs : List AllocByte, LangValid spec .none bs) ∧
    (spec.isSized = false →
      ∀ len : Nat, ∀ sz : Nat,
        spec.sizeForMeta (.sliceLen len) = some sz →
        ∃ bs : List AllocByte, LangValid spec (.sliceLen len) bs))

/-- Abstract layout specification for `bool` (1 byte, valid `0 | 1`). -/
noncomputable def boolTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 0
  , sizeForMeta := fun m => match m with | .none => some 1 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with | .none => some [.valueByte .boolByte] | _ => none }

/-- Abstract layout specification for `()` (0-byte ZST). -/
noncomputable def unitTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 0
  , sizeForMeta := fun m => match m with | .none => some 0 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m => match m with | .none => some [] | _ => none }

/-- Abstract layout specification for the uninhabited empty type `!`. -/
noncomputable def neverTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 0
  , sizeForMeta := fun m => match m with | .none => some 0 | _ => none
  , inhabited := false
  , hasUnsafeCell := false
  , rolesForMeta := fun m => match m with | .none => some [] | _ => none }

/-- Byte-level `ByteRole` list for integer width `w`: `w.byteSize` value bytes
spanning `[0, 2^w.bitWidth - 1]`. -/
noncomputable def intRoles (w : IntWidth) : List ByteRole :=
  repeatItem (.valueByte (.intRange 0 (Nat.pow 2 w.bitWidth - 1) w)) w.byteSize

/-- Abstract layout specification for integer width `w` using natural
alignment (`intLayout w`) matching 64-bit targets. -/
noncomputable def intTypeLayoutSpec (w : IntWidth) : TypeLayoutSpec :=
  let layout := intLayout w
  { isSized := true
  , alignLog2 := layout.alignLog2
  , sizeForMeta := fun m =>
      match m with | .none => some layout.size | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with
      | .none => some (intRoles w)
      | _ => none }

/-- Byte-level `ByteRole` list for Rust `char` (4 big-endian bytes). -/
noncomputable def charRoles : List ByteRole :=
  [ .valueByte (.charScalar 0)
  , .valueByte (.charScalar 1)
  , .valueByte (.charScalar 2)
  , .valueByte (.charScalar 3) ]

/-- Abstract layout specification for `char`. -/
noncomputable def charTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 2
  , sizeForMeta := fun m => match m with | .none => some 4 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with | .none => some charRoles | _ => none }

/-- Abstract layout specification for `core::cmp::Ordering`. -/
noncomputable def orderingTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 0
  , sizeForMeta := fun m => match m with | .none => some 1 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with | .none => some [.valueByte .orderingByte] | _ => none }

/-- Abstract layout specification for an admitted fieldless enum `ety`. -/
noncomputable def enumTypeLayoutSpec (ety : EnumTy) : Option TypeLayoutSpec :=
  if !enumAdmitted ety then
    none
  else
    match ety.tagRepr with
    | .zeroSized =>
        some
          { isSized := true
          , alignLog2 := 0
          , sizeForMeta := fun m => match m with | .none => some 0 | _ => none
          , inhabited := true
          , hasUnsafeCell := false
          , rolesForMeta := fun m => match m with | .none => some [] | _ => none
          , enumTy? := some ety }
    | .scalar tagW _ =>
        let layout := intLayout tagW
        some
          { isSized := true
          , alignLog2 := layout.alignLog2
          , sizeForMeta := fun m =>
              match m with | .none => some layout.size | _ => none
          , inhabited := true
          , hasUnsafeCell := false
          , rolesForMeta := fun m =>
              match m with
              | .none =>
                  some (repeatItem (.valueByte (.enumDiscr ety)) layout.size)
              | _ => none
          , enumTy? := some ety }

/-- Abstract layout specification for an overflow tuple `(T, bool)` (`w` bits).
-/
noncomputable def overflowPairTypeLayoutSpec (w : IntWidth) : TypeLayoutSpec :=
  let layout := overflowPairLayout w
  let padLen := layout.size - (intLayout w).size - 1
  { isSized := true
  , alignLog2 := layout.alignLog2
  , sizeForMeta := fun m =>
      match m with | .none => some layout.size | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with
      | .none =>
          some
            (intRoles w ++ [.valueByte .boolByte] ++
              repeatItem .padding padLen)
      | _ => none }

/-- Abstract layout specification for a dynamically-sized slice `[T]` whose
sized element has `TypeLayoutSpec` `elemSpec`. -/
noncomputable def sliceTypeLayoutSpec (elemSpec : TypeLayoutSpec) :
    Option TypeLayoutSpec :=
  if !elemSpec.isSized then
    none
  else
    match elemSpec.sizeForMeta .none, elemSpec.rolesForMeta .none with
    | some elemSz, some elemRoles =>
        if elemRoles.length != elemSz || elemSpec.alignLog2 > maxAlignLog2 then
          none
        else
          some
            { isSized := false
            , alignLog2 := elemSpec.alignLog2
            , sizeForMeta := fun m =>
                match m with
                | .sliceLen len =>
                    let total := elemSz * len
                    if total ≤ isizeMax then some total else none
                | _ => none
            , inhabited := true
            , hasUnsafeCell := elemSpec.hasUnsafeCell
            , rolesForMeta := fun m =>
                match m with
                | .sliceLen len =>
                    let total := elemSz * len
                    if total ≤ isizeMax then
                      some (repeatConcat elemRoles len)
                    else
                      none
                | _ => none }
    | _, _ => none

/-- Abstract layout specification for a fixed-length array `[T; len]` whose
sized element has `TypeLayoutSpec` `elemSpec`. -/
noncomputable def arrayTypeLayoutSpec (elemSpec : TypeLayoutSpec) (len : Nat) :
    Option TypeLayoutSpec :=
  if !elemSpec.isSized then
    none
  else
    match elemSpec.sizeForMeta .none, elemSpec.rolesForMeta .none with
    | some elemSz, some elemRoles =>
        let total := elemSz * len
        if elemRoles.length != elemSz || elemSpec.alignLog2 > maxAlignLog2 ||
            total > isizeMax then
          none
        else
          some
            { isSized := true
            , alignLog2 := elemSpec.alignLog2
            , sizeForMeta := fun m =>
                match m with | .none => some total | _ => none
            , inhabited := if len == 0 then true else elemSpec.inhabited
            , hasUnsafeCell := elemSpec.hasUnsafeCell
            , rolesForMeta := fun m =>
                match m with
                | .none => some (repeatConcat elemRoles len)
                | _ => none }
    | _, _ => none

/-- Bit-level layout approximation for a thin or wide reference
(`isRef = true`) or raw pointer (`isRef = false`) pointing to `pointeeSpec`.
References carry `refPtr pointeeSpec.alignLog2 true` roles (requiring
provenance, non-null, and pointee alignment) rather than unconstrained
`.anyByte`, and wide pointers append an 8-byte `isize`-bounded metadata word.

Note: `inhabited := true` is currently set unconditionally without checking
`pointeeSpec.inhabited`, backing-memory dereferenceability, or element-scaled
slice byte-length bounds; see `Anneal.Generic.OpenSemantics` ("Known modeling
gaps") for the requirements before any promotion to `trusted/`. -/
noncomputable def pointerTypeLayoutSpec (pointeeSpec : TypeLayoutSpec)
    (isRef : Bool) : TypeLayoutSpec :=
  let ptrSz : Nat := if pointeeSpec.isSized then 8 else 16
  let ptrRoles : List ByteRole :=
    repeatItem (.valueByte (.refPtr pointeeSpec.alignLog2 isRef)) 8
  let allRoles : List ByteRole :=
    if pointeeSpec.isSized then ptrRoles
    else ptrRoles ++ repeatItem (.valueByte (.intRange 0 isizeMax .isize)) 8
  { isSized := true
  , alignLog2 := 3
  , sizeForMeta := fun m => match m with | .none => some ptrSz | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with
      | .none => some allRoles
      | _ => none }

/-- Parametric type-specification environment mapping nominal ADTs, associated
type projections, open type parameter specs, and safety invariants. -/
structure TypeSpecEnv where
  adtSpecs : AdtDefId → List TypeLayoutSpec → Option TypeLayoutSpec
  assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
    Option TypeLayoutSpec := fun _ _ _ _ => none
  paramSpecs : List TypeLayoutSpec := []
  paramInvs : List (List AllocByte → Prop) := []

/-- Empty `TypeSpecEnv` rejecting unknown nominal ADTs and parameters. -/
noncomputable def emptyTypeSpecEnv : TypeSpecEnv :=
  { adtSpecs := fun _ _ => none
  , assocSpecs := fun _ _ _ _ => none
  , paramSpecs := []
  , paramInvs := [] }

/-- Predicate requiring every parameter layout spec in `paramSpecs` to satisfy
`WellFormedTypeLayoutSpec`. -/
def AllParamSpecsWf : List TypeLayoutSpec → Prop
  | [] => True
  | s :: rest => WellFormedTypeLayoutSpec s ∧ AllParamSpecsWf rest

mutual
  /-- Evaluate an already-normalized `OpenMirTy` to its `TypeLayoutSpec` under
  `env`. -/
  noncomputable def evalNormOpenTySpec (env : TypeSpecEnv) :
      OpenMirTy → Option TypeLayoutSpec
    | .bool => some boolTypeLayoutSpec
    | .int w _ => some (intTypeLayoutSpec w)
    | .unit => some unitTypeLayoutSpec
    | .never => some neverTypeLayoutSpec
    | .char => some charTypeLayoutSpec
    | .ordering => some orderingTypeLayoutSpec
    | .enum ety => enumTypeLayoutSpec ety
    | .tuple [.int w _, .bool] => some (overflowPairTypeLayoutSpec w)
    | .tuple _ => none
    | .slice e =>
        match evalNormOpenTySpec env e with
        | some eSpec => sliceTypeLayoutSpec eSpec
        | none => none
    | .array e len =>
        match evalNormOpenTySpec env e with
        | some eSpec => arrayTypeLayoutSpec eSpec len
        | none => none
    | .adt id args =>
        match evalNormOpenTySpecList env args with
        | some argSpecs => env.adtSpecs id argSpecs
        | none => none
    | .ref _ p =>
        match evalNormOpenTySpec env p with
        | some pSpec => some (pointerTypeLayoutSpec pSpec true)
        | none => none
    | .rawPtr _ p =>
        match evalNormOpenTySpec env p with
        | some pSpec => some (pointerTypeLayoutSpec pSpec false)
        | none => none
    | .param id => openListGet? env.paramSpecs id
    | .assocProj s tr as idx => env.assocSpecs s tr as idx
    | .unsupported => none

  /-- Elementwise layout spec evaluation on `List OpenMirTy`. -/
  noncomputable def evalNormOpenTySpecList (env : TypeSpecEnv) :
      List OpenMirTy → Option (List TypeLayoutSpec)
    | [] => some []
    | x :: xs =>
        match evalNormOpenTySpec env x, evalNormOpenTySpecList env xs with
        | some sx, some sxs => some (sx :: sxs)
        | _, _ => none
end

/-- Normalize associated projections using `reg` and `fuel`, then evaluate
the `TypeLayoutSpec` under `env`. -/
noncomputable def evalOpenTySpec (reg : TraitRegistry) (fuel : Nat)
    (env : TypeSpecEnv) (ty : OpenMirTy) : Option TypeLayoutSpec :=
  evalNormOpenTySpec env (normalizeOpenTy reg fuel ty)

/-- Substitute concrete `TypeLayoutSpec`s, invariants, and optional
associated-type specs into `base`. -/
noncomputable def substTypeSpecEnv (base : TypeSpecEnv)
    (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec := base.assocSpecs) : TypeSpecEnv :=
  { adtSpecs := base.adtSpecs
  , assocSpecs := assocSpecs
  , paramSpecs := paramSpecs
  , paramInvs := paramInvs }

end Anneal.Generic

end
