-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Nat.Div.Basic
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Value Representations (`Trusted.MirSemantics.Bytes`)

How $M_{\text{anneal}}$ turns bit patterns and bytes into values and back:
decoding a scalar bit pattern or zero-sized constant at a MIR type
(`evalConstLit`, shared by constant operands and memory reads), the
endian-parameterized integer byte codec (`encodeUInt`, `decodeUInt`), the
typed byte codec for Day-1 values (`encodeVal`, `decodeVal`), and typed loads
and stores through a memory place (`loadIndirect`, `storeIndirect`,
`deinitIndirect`).
-/

/-- Decode a typed constant literal `ConstLit` into a runtime `Val`, matching
`ScalarInt::try_from_uint` and `ScalarInt::try_to_bool` in
`compiler/rustc_middle/src/ty/consts/int.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.Memory.ScalarInt`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`):

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> "pub fn try_to_bool(self) -> Result<bool, ()> {
>     match self.to_u8() {
>         0 => Ok(false),
>         1 => Ok(true),
>         _ => Err(()),
>     }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

A 1-byte `.bool` scalar whose value is neither `0` nor `1` triggers
`ScalarIntError.invalidBool`, which `Miri.Interpreter.ScalarOps.scalarError`
maps to `.undefinedBehavior`, so `evalConstLit` returns `.error .undefined`.

For fieldless enums (`.enum ety`), constant decoding matches `op_to_const`
(`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:258`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let discr_val = self.int_to_int_or_float(&tag_val, discr_layout).unwrap();
> let discr_bits = discr_val.to_scalar().to_bits(discr_layout.size)?;
> ...
> adt.discriminants(*self.tcx).find(|(_, var)| var.val == discr_bits)
> ...
> .ok_or_else(|| err_ub!(InvalidTag(Scalar::from_uint(tag_bits,
>     tag_layout.size))))?;"

- Admitted 1-variant ZST enums (`ety.tagRepr = .zeroSized`) decode
  `ConstLit.zeroSized` to `.ok (.enumVal ety 0)`.
- Admitted direct-tagged enums (`ety.tagRepr = .scalar tagW tagS`) validate
  that `bits` fits in `tagW`, extend/truncate `bits` to `ety.discrWidth` via
  `tagBitsToDiscrBits`, and resolve the matching declaration index via
  `findDiscrVariant?` (returning `.error .undefined` on an invalid tag bit
  pattern not matching any declared discriminant).
- `char` constants validate that `bits` fits in 4 bytes and is a Unicode
  scalar value (`isUnicodeScalar`), faulting with `.error .undefined` like
  `ScalarIntError.invalidChar` (which `Miri.Interpreter.ScalarOps.scalarError`
  maps to `.undefinedBehavior`).
- `core::cmp::Ordering` constants validate that `bits` fits in 1 byte and is
  one of the tags `255`, `0`, and `1` (`orderingOfTagBits`), faulting with
  `.error .undefined` on any other tag as for a fieldless enum.

`decodeVal` reuses `evalConstLit` to interpret the bytes read from memory, so
constant operands and memory reads apply the same validity checks. -/
noncomputable def evalConstLit : MirTy → ConstLit → Except FaultKind Val
  | .int w s, .scalar bits =>
    if truncateBits w bits != bits then
      .error .unsupported
    else
      .ok (.scalar ⟨w, s, truncateBits w bits⟩)
  | .bool, .scalar bits =>
    if truncateBits .i8 bits != bits then
      .error .unsupported
    else
      let v := UInt8.ofNat (truncateBits .i8 bits).toNat
      if v == 0 then
        .ok (.bool false)
      else if v == 1 then
        .ok (.bool true)
      else
        .error .undefined
  | .unit, .zeroSized => .ok .unit
  | .char, .scalar bits =>
    if truncateBits .i32 bits != bits then
      .error .unsupported
    else if isUnicodeScalar bits.toNat then
      .ok (.char (Char.ofNat bits.toNat))
    else
      .error .undefined
  | .ordering, .scalar bits =>
    if truncateBits .i8 bits != bits then
      .error .unsupported
    else
      match orderingOfTagBits bits.toNat with
      | some ord => .ok (.ordering ord)
      | none => .error .undefined
  | .enum ety, .zeroSized =>
    if isZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW tagS =>
      if !enumAdmitted ety || truncateBits tagW bits != bits then
        .error .unsupported
      else
        let discrBits := tagBitsToDiscrBits tagW tagS ety.discrWidth bits
        match findDiscrVariant? discrBits ety.discriminants with
        | some v => .ok (.enumVal ety v)
        | none => .error .undefined
  | _, _ => .error .unsupported

/-- The low `n` bytes of `value`, least significant byte first (the first `n`
bytes of `u128::to_le_bytes`). -/
noncomputable def leBytesOfNat : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, value =>
    UInt8.ofNat (Nat.mod value 256) :: leBytesOfNat n (Nat.div value 256)

/-- Encode the low `n` bytes of `value` in byte order `endian`, matching
`write_target_uint` in `compiler/rustc_middle/src/mir/interpret/mod.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "match endianness {
>     Endian::Little => target.write(&data.to_le_bytes())?,
>     Endian::Big => target.write(&data.to_be_bytes()[16 - target.len()..])?,
> };"

The last `n` bytes of `to_be_bytes` are the first `n` bytes of `to_le_bytes`
in reverse order. -/
noncomputable def encodeUInt (endian : TargetEndian) (n value : Nat) :
    List UInt8 :=
  match endian with
  | .little => leBytesOfNat n value
  | .big => (leBytesOfNat n value).reverse

/-- The unsigned integer whose little-endian bytes are `bytes`. -/
noncomputable def natOfLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * natOfLeBytes rest

/-- Decode `bytes` as an unsigned integer in byte order `endian`, matching
`read_target_uint` in `compiler/rustc_middle/src/mir/interpret/mod.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let uint = match endianness {
>     Endian::Little => {
>         source.read_exact(&mut buf[..source.len()])?;
>         Ok(u128::from_le_bytes(buf))
>     }
>     Endian::Big => {
>         source.read_exact(&mut buf[16 - source.len()..])?;
>         Ok(u128::from_be_bytes(buf))
>     }
> };" -/
noncomputable def decodeUInt (endian : TargetEndian) (bytes : List UInt8) :
    Nat :=
  match endian with
  | .little => natOfLeBytes bytes
  | .big => natOfLeBytes bytes.reverse

/-- The raw bytes of `bytes` if every byte is initialized, dropping
provenance, or `none` if any byte is uninitialized. Matches the start of
`Allocation::read_scalar` in
`compiler/rustc_middle/src/mir/interpret/allocation.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) for Miri's provenance, whose
offsets are absolute addresses (`OFFSET_IS_ADDR`):

> "// First and foremost, if anything is uninit, bail.
> if let Err(bad) = self.init_mask.is_range_initialized(range) {
>     return Err(AllocError::InvalidUninitBytes(Some(BadBytesAccess {
>         access: range,
>         bad,
>     })));
> }
> ...
> // We are *not* reading a pointer.
> // If we can just ignore provenance or there is none, that's easy.
> if Prov::OFFSET_IS_ADDR || self.provenance.range_empty(range, cx) {
>     // We just strip provenance.
>     return Ok(Scalar::from_uint(bits, range.size));
> }" -/
noncomputable def initBytes? : List AllocByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b _ :: rest =>
    match initBytes? rest with
    | some bs => some (b :: bs)
    | none => none

/-- Encode the Day-1 value `v` of type `ty` as the bytes that
`Allocation::write_scalar`
(`compiler/rustc_middle/src/mir/interpret/allocation.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) stores, in byte order `endian`:

> "let endian = cx.data_layout().endian;
> // Yes we do overwrite all the bytes in `dst`.
> let dst = self.get_bytes_unchecked_for_overwrite(cx, range);
> write_target_uint(endian, dst, bytes).unwrap();"

- `.int w _`: the `w.byteSize` bytes of the scalar's bits.
- `.bool`: one byte, `1` for `true` and `0` for `false`.
- `.char`: the four bytes of the Unicode scalar value (`char` has the size of
  `u32`).
- `.ordering`: the one byte of the `i8` tag (`orderingTagBits`).
- `.unit` and 1-variant `.zeroSized` enums: no bytes.
- `.scalar tagW _` enums: the `tagW.byteSize` low bytes of the variant's
  discriminant (a `TagEncoding::Direct` tag stores the discriminant truncated
  to the tag width).
- Overflow pairs `.tuple [.int w _, .bool]`: the integer's `w.byteSize` bytes,
  the `bool`'s byte, and `w.byteSize - 1` uninitialized padding bytes
  (`overflowPairLayout`), matching `write_immediate_to_mplace_no_validate`'s
  `Immediate::ScalarPair` case
  (`compiler/rustc_const_eval/src/interpret/place.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "// In preparation, if we do *not* later reset the padding, we clear the
  > // entire destination now to ensure that no stray pointer fragments are
  > // being preserved (see <https://github.com/rust-lang/rust/issues/148470>).
  > // We can skip this if there is no padding (e.g. for wide pointers).
  > if !will_later_validate && a_size + b_size != layout.size {
  >     alloc.write_uninit_full();
  > }
  >
  > alloc.write_scalar(alloc_range(Size::ZERO, a_size), a_val)?;
  > alloc.write_scalar(alloc_range(b_offset, b_size), b_val)?;"

  The padding bytes end up uninitialized either way: this write clears them,
  or validation resets them.

Every encoded value byte is initialized and carries no provenance. A value
that is not a well-formed value of `ty` (`checkVal v ty = false`), and any
other `(ty, v)` pair outside the Day-1 fragment, returns
`.error .unsupported`. -/
noncomputable def encodeVal (endian : TargetEndian) (ty : MirTy) (v : Val) :
    Except FaultKind (List AllocByte) :=
  if !checkVal v ty then
    .error .unsupported
  else
    match ty, v with
    | .int w _, .scalar sv =>
      .ok ((encodeUInt endian w.byteSize sv.bits.toNat).map
        (fun b => AllocByte.init b none))
    | .bool, .bool b =>
      .ok [AllocByte.init (if b then 1 else 0) none]
    | .char, .char c =>
      .ok ((encodeUInt endian 4 c.toNat).map (fun b => AllocByte.init b none))
    | .ordering, .ordering ord =>
      .ok ((encodeUInt endian 1 (orderingTagBits ord)).map
        (fun b => AllocByte.init b none))
    | .unit, .unit => .ok []
    | .enum ety, .enumVal _ variant =>
      match ety.tagRepr with
      | .zeroSized => .ok []
      | .scalar tagW _ =>
        match getElem? ety.discriminants variant with
        | some disc =>
          .ok ((encodeUInt endian tagW.byteSize disc).map
            (fun b => AllocByte.init b none))
        | none => .error .unsupported
    | .tuple [.int w _, .bool], .tuple [.scalar sv, .bool b] =>
      .ok ((encodeUInt endian w.byteSize sv.bits.toNat).map
          (fun byte => AllocByte.init byte none) ++
        [AllocByte.init (if b then 1 else 0) none] ++
        List.replicate (w.byteSize - 1) AllocByte.uninit)
    | _, _ => .error .unsupported

/-- Decode the bytes `bytes` of a value of type `ty` in byte order `endian`:
`.ok (some v)` for a valid value `v`, `.ok none` for bytes that do not hold an
initialized value, or a fault.

- `.never`: no valid value exists, so the result is `.ok none` (as for an
  uninitialized `.immediate none` slot of type `.never`, a later use faults
  with `.undefined`).
- Overflow pairs `.tuple [.int w s, .bool]`: the integer from the first
  `w.byteSize` bytes and the `bool` from the next byte, ignoring the padding
  bytes (`read_immediate_from_mplace_raw` reads only the two scalars of a
  `BackendRepr::ScalarPair`); `.ok none` if a value byte is uninitialized.
- Zero-sized types (`.unit` and 1-variant `.zeroSized` enums): the type's
  unique value, via `evalConstLit ty .zeroSized`.
- Other Day-1 types: `.ok none` if any byte is uninitialized (`initBytes?`),
  and otherwise the result of `evalConstLit ty` on the bytes decoded as an
  unsigned integer (`decodeUInt`), which faults with `.undefined` on an
  invalid `bool` byte, an invalid `char`, or an enum or `Ordering` tag that
  matches no discriminant.

A byte count that differs from `layoutOfTy ty`, or a type outside the Day-1
fragment (including an enum that `enumAdmitted` rejects, which has no
layout), returns `.error .unsupported` before any byte is inspected. -/
noncomputable def decodeVal (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  match ty with
  | .never => .ok none
  | .tuple [.int w s, .bool] =>
    if !Nat.beq bytes.length (overflowPairLayout w).size then
      .error .unsupported
    else
      match initBytes? (bytes.take w.byteSize),
          initBytes? ((bytes.drop w.byteSize).take 1) with
      | some intRaw, some boolRaw =>
        match evalConstLit (.int w s)
            (.scalar (BitVec.ofNat 128 (decodeUInt endian intRaw))) with
        | .error k => .error k
        | .ok intVal =>
          match evalConstLit .bool
              (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) with
          | .error k => .error k
          | .ok boolVal => .ok (some (.tuple [intVal, boolVal]))
      | _, _ => .ok none
  | _ =>
    match layoutOfTy ty with
    | none => .error .unsupported
    | some layout =>
      if !Nat.beq bytes.length layout.size then
        .error .unsupported
      else if Nat.beq layout.size 0 then
        match evalConstLit ty .zeroSized with
        | .ok v => .ok (some v)
        | .error k => .error k
      else
        match initBytes? bytes with
        | none => .ok none
        | some raw =>
          match evalConstLit ty
              (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
          | .ok v => .ok (some v)
          | .error k => .error k

/-- Load the value of type `ty` stored at `place`, matching
`read_immediate_from_mplace_raw` and `read_immediate` in
`compiler/rustc_const_eval/src/interpret/operand.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`): `readBytes` checks liveness,
bounds, and alignment, and `decodeVal` checks initialization and validity.
-/
noncomputable def loadIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind (Option Val) :=
  match layoutOfTy ty with
  | none => .error .unsupported
  | some layout =>
    match readBytes mem place layout.size layout.alignLog2 with
    | .error k => .error k
    | .ok bytes => decodeVal profileTargetEndian ty bytes

/-- Store the value `v` of type `ty` at `place`, matching
`write_immediate_to_mplace_no_validate` in
`compiler/rustc_const_eval/src/interpret/place.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`): `encodeVal` produces the bytes
and `writeBytes` checks liveness, bounds, alignment, and mutability. -/
noncomputable def storeIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) (v : Val) : Except FaultKind MemoryState :=
  match layoutOfTy ty with
  | none => .error .unsupported
  | some layout =>
    match encodeVal profileTargetEndian ty v with
    | .error k => .error k
    | .ok bytes => writeBytes mem place layout.alignLog2 bytes

/-- Mark the bytes of a value of type `ty` at `place` uninitialized
(`writeUninit`). $M_{\text{anneal}}$ uses this to deinitialize an indirect
local moved by `Operand.move` (see `evalOperandToSlot`). -/
noncomputable def deinitIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind MemoryState :=
  match layoutOfTy ty with
  | none => .error .unsupported
  | some layout => writeUninit mem place layout.size layout.alignLog2

/-! ## Profile v2 Byte Codec, Indirect Access, and Reference Validity -/

/-- Accumulate uniform provenance across remaining bytes of an encoded pointer. -/
noncomputable def provMatch :
    Option AllocId → List AllocByte → Option (Option AllocId)
  | _, .uninit :: _ => none
  | cur, [] => some cur
  | cur, .init _ p :: rest =>
    let next :=
      match cur, p with
      | some a, some b => if Nat.beq a b then some a else none
      | _, _ => none
    provMatch next rest

/-- Check initialization and extract uniform provenance across `bytes`.
Returns `none` if any byte is `.uninit`, `some (some aid)` if every byte carries
the identical provenance `some aid`, and `some none` if any byte lacks or
disagrees on provenance. -/
noncomputable def readPtrProv? : List AllocByte → Option (Option AllocId)
  | [] => none
  | .uninit :: _ => none
  | .init _ p :: rest => provMatch p rest

/-- Profile v2 constant-literal evaluator (`evalConstLit` extended with
`NonZero<T>` scalar constants). Per `library/core/src/num/nonzero.rs#L99-L100`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`),
> "`NonZero<T>` is guaranteed to have the same layout and bit validity as `T`
> with the exception that the all-zero bit pattern is invalid."
Zero bit patterns yield `.error .undefined`. -/
noncomputable def evalConstLitV2 : MirTy → ConstLit → Except FaultKind Val
  | .nonZero w s, .scalar bits =>
    if truncateBits w bits != bits then
      .error .unsupported
    else
      let trunc := truncateBits w bits
      if Nat.beq trunc.toNat 0 then
        .error .undefined
      else
        .ok (.nonZero ⟨w, s, trunc⟩)
  | ty, lit => evalConstLit ty lit

/-- Profile v2 byte encoder: encodes thin/wide pointers (preserving `allocId`
provenance on the pointer bytes), `RangeTo`/`RangeFrom`, and transparent
`NonZero<T>` integers (same byte representation as `T`,
`library/core/src/num/nonzero.rs#L99-L100`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), delegating all Profile v1 scalar,
enum, and overflow-pair types to `encodeVal`. -/
noncomputable def encodeValV2 (endian : TargetEndian) (ty : MirTy) (v : Val) :
    Except FaultKind (List AllocByte) :=
  if !checkValV2 v ty then
    .error .unsupported
  else
    match ty, v with
    | .rawPtr _ pt, .ptr p | .ref _ pt, .ptr p =>
      if isUnsizedTy pt then
        .error .unsupported
      else
        .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId))
    | .rawPtr _ (.slice _), .slicePtr p len
    | .ref _ (.slice _), .slicePtr p len =>
      .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId) ++
        (encodeUInt endian 8 len.toNat).map
          (fun b => AllocByte.init b none))
    | .rangeTo (.int .isize false), .rangeTo e =>
      .ok ((encodeUInt endian 8 e.toNat).map (fun b => AllocByte.init b none))
    | .rangeFrom (.int .isize false), .rangeFrom s =>
      .ok ((encodeUInt endian 8 s.toNat).map (fun b => AllocByte.init b none))
    | .nonZero w _, .nonZero sv =>
      .ok ((encodeUInt endian w.byteSize sv.bits.toNat).map
        (fun b => AllocByte.init b none))
    | _, _ => encodeVal endian ty v

/-- Profile v2 byte decoder: decodes thin/wide pointers (recovering uniform
byte provenance), `RangeTo`/`RangeFrom`, and `NonZero<T>` (faulting with
`.error .undefined` on the all-zero bit pattern per
`library/core/src/num/nonzero.rs#L99-L100`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), delegating all Profile v1 types
to `decodeVal`. -/
noncomputable def decodeValV2 (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  match ty with
  | .rawPtr _ pt | .ref _ pt =>
    if isUnsizedTy pt then
      match pt with
      | .slice _ =>
        if !Nat.beq bytes.length 16 then
          .error .unsupported
        else
          let pBytes := bytes.take 8
          let lBytes := bytes.drop 8
          match initBytes? pBytes, readPtrProv? pBytes, initBytes? lBytes with
          | some pRaw, some prov, some lRaw =>
            let p : PtrVal := ⟨prov, UInt64.ofNat (decodeUInt endian pRaw), .isize⟩
            let len := UInt64.ofNat (decodeUInt endian lRaw)
            .ok (some (.slicePtr p len))
          | _, _, _ => .ok none
      | _ => .error .unsupported
    else
      if !Nat.beq bytes.length 8 then
        .error .unsupported
      else
        match initBytes? bytes, readPtrProv? bytes with
        | some pRaw, some prov =>
          .ok (some (.ptr ⟨prov, UInt64.ofNat (decodeUInt endian pRaw), .isize⟩))
        | _, _ => .ok none
  | .rangeTo (.int .isize false) =>
    if !Nat.beq bytes.length 8 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some raw => .ok (some (.rangeTo (UInt64.ofNat (decodeUInt endian raw))))
  | .rangeFrom (.int .isize false) =>
    if !Nat.beq bytes.length 8 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some raw => .ok (some (.rangeFrom (UInt64.ofNat (decodeUInt endian raw))))
  | .nonZero w s =>
    if !Nat.beq bytes.length w.byteSize then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some raw =>
        match evalConstLitV2 (.nonZero w s)
            (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k
  | _ => decodeVal endian ty bytes

/-- Profile v2 typed load from `place` in `mem`. -/
noncomputable def loadIndirectV2 (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind (Option Val) :=
  match layoutOfTyV2 ty with
  | none => .error .unsupported
  | some layout =>
    match readBytes mem place layout.size layout.alignLog2 with
    | .error k => .error k
    | .ok bytes => decodeValV2 profileV2TargetEndian ty bytes

/-- Profile v2 typed store into `place` in `mem`. -/
noncomputable def storeIndirectV2 (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) (v : Val) : Except FaultKind MemoryState :=
  match layoutOfTyV2 ty with
  | none => .error .unsupported
  | some layout =>
    match encodeValV2 profileV2TargetEndian ty v with
    | .error k => .error k
    | .ok bytes => writeBytes mem place layout.alignLog2 bytes

/-- Profile v2 indirect local deinitialization (`writeUninit`). -/
noncomputable def deinitIndirectV2 (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind MemoryState :=
  match layoutOfTyV2 ty with
  | none => .error .unsupported
  | some layout => writeUninit mem place layout.size layout.alignLog2

/-- Validate Rust language validity invariants for a `&T`, `&mut T`, `&[u8]`,
or `&mut [u8]` value `v` in `m`: non-null, provenance-backed (except valid
aligned non-null `len = 0` slices), live allocation, bounds, alignment,
mutability for `.mut`, and initialized valid pointee value. -/
noncomputable def refValidInMem (m : MemoryState) (reqMut : Mutability)
    (pointee : MirTy) (v : Val) : Except FaultKind Unit :=
  match pointee, v with
  | .slice (.int w _), .slicePtr p len =>
    let lay := intLayout w
    match sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) lay.size lay.alignLog2 p len with
    | .ok _ => .ok ()
    | .error k => .error k
  | .slice _, _ => .error .unsupported
  | _, .ptr p =>
    match layoutOfTyV2 pointee with
    | none => .error .unsupported
    | some lay =>
      match p.allocId with
      | none =>
        if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 lay.size then
          .error .undefined
        else if !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
          .error .undefined
        else
          match decodeValV2 profileV2TargetEndian pointee [] with
          | .ok (some _) => .ok ()
          | .ok none => .error .undefined
          | .error k => .error k
      | some aid =>
        match findAllocation aid m.allocations with
        | none => .error .undefined
        | some a =>
          if !a.live || !isInBounds a p.offsetBytes.toNat lay.size ||
              !isAligned a p.offsetBytes.toNat lay.alignLog2 then
            .error .undefined
          else if Mutability.beq reqMut .mut && !Mutability.beq a.mutability .mut then
            .error .undefined
          else
            let sliceBytes := (a.bytes.drop p.offsetBytes.toNat).take lay.size
            match decodeValV2 profileV2TargetEndian pointee sliceBytes with
            | .ok (some _) => .ok ()
            | .ok none => .error .undefined
            | .error k => .error k
  | _, _ => .error .unsupported

mutual
  /-- Validate all references inside `v` (including tuple components) against
  `m`. Raw pointers `.rawPtr` are not constrained by reference validity. -/
  noncomputable def refsValidInMem (m : MemoryState) : MirTy → Val → Bool
    | .ref reqMut pt, v =>
      match refValidInMem m reqMut pt v with
      | .ok () => true
      | .error _ => false
    | .tuple ts, .tuple vs => refsValidInMemList m ts vs
    | _, _ => true

  noncomputable def refsValidInMemList (m : MemoryState) :
      List MirTy → List Val → Bool
    | [], [] => true
    | t :: ts, v :: vs => refsValidInMem m t v && refsValidInMemList m ts vs
    | _, _ => false
end

mutual
  /-- Extract provenance-backed `(isMut, allocId, offset, byteSize)` access
  spans for every reference component inside `(ty, v)`. -/
  noncomputable def refAccessSpans :
      MirTy → Val → List (Bool × AllocId × Nat × Nat)
    | .ref reqMut (.slice (.int w _)), .slicePtr p len =>
      let lay := intLayout w
      match p.allocId with
      | some aid => [(Mutability.beq reqMut .mut, aid, p.offsetBytes.toNat, len.toNat * lay.size)]
      | none => []
    | .ref reqMut pt, .ptr p =>
      match layoutOfTyV2 pt, p.allocId with
      | some lay, some aid => [(Mutability.beq reqMut .mut, aid, p.offsetBytes.toNat, lay.size)]
      | _, _ => []
    | .tuple ts, .tuple vs => refAccessSpansList ts vs
    | _, _ => []

  noncomputable def refAccessSpansList :
      List MirTy → List Val → List (Bool × AllocId × Nat × Nat)
    | [], [] => []
    | t :: ts, v :: vs => refAccessSpans t v ++ refAccessSpansList ts vs
    | _, _ => []
end

mutual
  /-- Extract all allocation ids referenced by any `.ref` inside `(ty, v)`. -/
  noncomputable def refAllocIds : MirTy → Val → List AllocId
    | .ref _ (.slice _), .slicePtr p _ =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .ref _ _, .ptr p =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .tuple ts, .tuple vs => refAllocIdsList ts vs
    | _, _ => []

  noncomputable def refAllocIdsList : List MirTy → List Val → List AllocId
    | [], [] => []
    | t :: ts, v :: vs => refAllocIds t v ++ refAllocIdsList ts vs
    | _, _ => []
end

/-- Check that every reference's provenance `allocId` belongs to `cm` (so callee
stack references can never escape past return). -/
noncomputable def refsStayInCallerMem (cm : CallerMemory) (ty : MirTy)
    (v : Val) : Bool :=
  (refAllocIds ty v).all (fun aid => (findAllocation aid cm.allocations).isSome)

noncomputable def spanDisjoint (a b : Bool × AllocId × Nat × Nat) : Bool :=
  let (m1, id1, s1, n1) := a
  let (m2, id2, s2, n2) := b
  if !(m1 || m2) || Nat.beq n1 0 || Nat.beq n2 0 || !Nat.beq id1 id2 then
    true
  else
    Nat.ble (s1 + n1) s2 || Nat.ble (s2 + n2) s1

noncomputable def spanDisjointWith (a : Bool × AllocId × Nat × Nat) :
    List (Bool × AllocId × Nat × Nat) → Bool
  | [] => true
  | b :: rest => spanDisjoint a b && spanDisjointWith a rest

/-- Check pairwise disjointness across active mutable borrow byte spans. -/
noncomputable def spansPairwiseDisjoint :
    List (Bool × AllocId × Nat × Nat) → Bool
  | [] => true
  | a :: rest => spanDisjointWith a rest && spansPairwiseDisjoint rest

end Trusted.MirSemantics

end
