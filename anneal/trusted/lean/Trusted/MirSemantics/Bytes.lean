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
  | _, .rodataBytes _ | _, .rodataRef _ _ _ _ => .error .unsupported
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
`8144389c895da997dbdecaa635e41d6a50be6ffd`): `readBytes` checks alignment
(plus liveness and bounds when `layout.size > 0`), and `decodeVal` checks
initialization and validity. -/
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
and `writeBytes` checks alignment (plus liveness, bounds, and mutability when
`bytes.length > 0`). -/
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

/-- Accumulate uniform provenance across remaining bytes of an encoded pointer.
-/
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

/-- Convert a provenance-free `.rodata` byte into an `AllocByte` with `none`
provenance. -/
noncomputable def rodataByteToAllocByte : RodataByte → AllocByte
  | .uninit => .uninit
  | .init b => .init b none

/-- Encode a list of elements using a fixed element encoder (factored out to
keep `encodeValV2` structurally recursive on `MirTy`). -/
noncomputable def encodeValListWith
    (f : Val → Except FaultKind (List AllocByte)) :
    List Val → Except FaultKind (List AllocByte)
  | [] => .ok []
  | v :: vs =>
    match f v, encodeValListWith f vs with
    | .ok bs, .ok rest => .ok (bs ++ rest)
    | .error k, _ => .error k
    | _, .error k => .error k

/-- Decode `count` fixed-size chunks using element decoder `f` (factored out to
keep `decodeValV2` structurally recursive on `MirTy`). -/
noncomputable def decodeFixedChunks (elemSize : Nat)
    (f : List AllocByte → Except FaultKind (Option Val)) :
    Nat → List AllocByte → Except FaultKind (Option (List Val))
  | 0, bytes => if bytes.isEmpty then .ok (some []) else .error .unsupported
  | count + 1, bytes =>
    match f (bytes.take elemSize),
        decodeFixedChunks elemSize f count (bytes.drop elemSize) with
    | .error k, _ => .error k
    | _, .error k => .error k
    | .ok none, _ => .ok none
    | _, .ok none => .ok none
    | .ok (some v), .ok (some vs) => .ok (some (v :: vs))

/-- Profile v2 byte encoder: encodes fixed-size arrays `[T; N]`, thin/wide
pointers (preserving `allocId` provenance on the pointer bytes),
`RangeTo`/`RangeFrom`, and supported `Option<T>`, delegating all Profile v1
scalar, enum, and overflow-pair types to `encodeVal`.

A wide slice pointer is laid out as the `(ptr, meta)` scalar pair that
`layoutOfTyV2` documents: 8 data-pointer bytes, then 8 bytes of `usize`
length, in `profileV2TargetEndian` order. The pointer bytes store the offset
relative to the allocation and carry its `allocId` as provenance. That is the
CTFE representation
(`compiler/rustc_middle/src/mir/interpret/pointer.rs:166-169`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "impl Provenance for CtfeProvenance {
>     // With the `CtfeProvenance` as provenance, the `offset` is interpreted
>     // *relative to the allocation*, so ptr-to-int casts are not possible
>     // (since we do not know the global physical offset).
>     const OFFSET_IS_ADDR: bool = false;"

At runtime, rustc stores absolute addresses instead. Profile v2 never reads
pointer bytes it wrote back at an integer type: pointees cannot themselves be
pointers (`isSupportedV2LocalTy`), and length and range bytes carry no
provenance.

For addressable `Option<T>` (where both `isSizedNoRefV2Ty inner` and
`isOptionPayloadSupportedV2 inner` hold, verified against `rustc`'s
`layout_of` at capture time; `library/core/src/option.rs:597-606`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
- `Option<bool>`: `bool` has `valid_range: WrappingRange { start: 0, end: 1 }`
  (`compiler/rustc_ty_utils/src/layout.rs:388`); `Niche::reserve` takes
  `move_end` (`is_bool` at `compiler/rustc_abi/src/lib.rs:2067-2068, 2084`),
  setting tag `2` for `None`, `0` for `Some(false)`, and `1` for `Some(true)`.
- `Option<()>`: `None` is declared before `Some`
  (`library/core/src/option.rs:597-606`), so `TagEncoding::Direct` writes
  1-byte `I8` tag `0` for `None` and `1` for `Some(())`
  (`compiler/rustc_abi/src/layout.rs:844,897`).
- Niche-free addressable `Option<inner>` (`.int _ _`): `TagEncoding::Direct`
  writes `0` (`None`) or `1` (`Some`) in `tagBytes = 2^lay.alignLog2` tag
  bytes (`compiler/rustc_abi/src/layout.rs:897,912`), followed by `.uninit`
  payload bytes for `None` or the encoded payload for `Some`. Non-addressable
  `Option<&T>` / `Option<*const/*mut T>` fail closed with `.unsupported`.

An array whose element type has no `layoutOfTyV2` (such as `[Option<bool>; 2]`
nested in another array, which `layoutOfArrayV2` does not lay out) also fails
closed with `.unsupported`, matching `decodeValV2`, which needs the element
layout to split the bytes. -/
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
    | .ref _ (.slice _), .slicePtr p len
    | .ref .shared .str, .slicePtr p len =>
      .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId) ++
        (encodeUInt endian 8 len.toNat).map
          (fun b => AllocByte.init b none))
    -- `Vec` and `Box` handles use a model-internal encoding. Rust leaves the
    -- layout of `Vec` unspecified (`library/alloc/src/vec/mod.rs:312-314`,
    -- `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`): "Most
    -- fundamentally, `Vec` is and always will be a (pointer, capacity, length)
    -- triplet. No more, no less. The order of these fields is completely
    -- unspecified". The encoding is unobservable because Profile v2 admits
    -- no raw pointer to a `Vec` or `Box` (`isSupportedV2LocalTy`), so only
    -- the contracts in `AllocContracts` read and write these bytes.
    | .vec _, .vec p cap len =>
      .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId) ++
        (encodeUInt endian 8 cap.toNat).map
          (fun b => AllocByte.init b none) ++
        (encodeUInt endian 8 len.toNat).map
          (fun b => AllocByte.init b none))
    | .box pt, .boxPtr p none =>
      if isUnsizedTy pt then
        .error .unsupported
      else
        .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId))
    | .box (.slice _), .boxPtr p (some len) =>
      .ok ((encodeUInt endian 8 p.offsetBytes.toNat).map
          (fun b => AllocByte.init b p.allocId) ++
        (encodeUInt endian 8 len.toNat).map
          (fun b => AllocByte.init b none))
    | .rangeTo (.int .isize false), .rangeTo e =>
      .ok ((encodeUInt endian 8 e.toNat).map (fun b => AllocByte.init b none))
    | .rangeFrom (.int .isize false), .rangeFrom s =>
      .ok ((encodeUInt endian 8 s.toNat).map (fun b => AllocByte.init b none))
    | .array elem len, .array vs =>
      if !(layoutOfTyV2 elem).isSome || !Nat.beq vs.length len then
        .error .unsupported
      else
        encodeValListWith (encodeValV2 endian elem) vs
    | .option .bool, .optionVal optV =>
      match optV with
      | none => .ok [AllocByte.init 2 none]
      | some (.bool false) => .ok [AllocByte.init 0 none]
      | some (.bool true) => .ok [AllocByte.init 1 none]
      | _ => .error .unsupported
    | .option .unit, .optionVal optV =>
      match optV with
      | none => .ok [AllocByte.init 0 none]
      | some .unit => .ok [AllocByte.init 1 none]
      | _ => .error .unsupported
    | .option inner, .optionVal optV =>
      if !isSizedNoRefV2Ty inner || !isOptionPayloadSupportedV2 inner then
        .error .unsupported
      else
        match layoutOfTyV2 inner with
        | none => .error .unsupported
        | some lay =>
          let tagBytes := Nat.pow 2 lay.alignLog2
          match optV with
          | none =>
            .ok ((encodeUInt endian tagBytes 0).map
                (fun b => AllocByte.init b none) ++
              List.replicate lay.size .uninit)
          | some innerV =>
            match encodeValV2 endian inner innerV with
            | .error k => .error k
            | .ok payload =>
              .ok ((encodeUInt endian tagBytes 1).map
                  (fun b => AllocByte.init b none) ++
                payload)
    | _, _ => encodeVal endian ty v

/-- Helper for `decodeValV2` on `.rawPtr` and `.ref` types (thin/wide pointers
and slices), factored out so `decodeValV2`'s equation lemma stays free of
`Quot.sound`. -/
noncomputable def decodePtrLikeV2 (endian : TargetEndian) (pt : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  if isUnsizedTy pt then
    match pt with
    | .slice _ | .str =>
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

/-- Profile v2 byte decoder: decodes fixed-size arrays `[T; N]`, thin/wide
pointers (recovering uniform byte provenance), `RangeTo`/`RangeFrom`, and
supported `Option<T>`, delegating all Profile v1 types to `decodeVal`.

This inverts `encodeValV2`. Any uninitialized byte in an active field yields
`.ok none`, and the caller faults with `.undefined`: raw pointers and integers
"must not be obtained from uninitialized memory" (`refsValidInMem` quotes the
rule). If the 8 pointer bytes do not all carry the same `allocId`, the decoded
pointer has no provenance and can be used only for zero-sized accesses. That
choice is conservative. Length and range bytes ignore provenance, as integer
loads do at runtime.

Invalid `Option<bool>`, `Option<()>`, or `TagEncoding::Direct` tags likewise
return `.ok none` (which `loadIndirectV2` and `refValidInMem` reject as
`.error .undefined`, matching `throw_ub!(InvalidTag)` in
`compiler/rustc_const_eval/src/interpret/discriminant.rs:157`).
`Option<&T>`, `Option<&[T]>`, and `Option<*const T>` have no byte layout
(they stay immediate locals), so they fail closed here; `Option<bool>`
accepts `0`, `1`, and niche tag `2`
(`compiler/rustc_abi/src/lib.rs:2060-2068`), and `Option<()>` accepts direct
`I8` tags `0` (`None`) and `1` (`Some(())`)
(`compiler/rustc_abi/src/layout.rs:844,897`; all pinned at `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
noncomputable def decodeValV2 (endian : TargetEndian) :
    MirTy → List AllocByte → Except FaultKind (Option Val)
  | .rawPtr _ .str, _ | .ref .mut .str, _ => .error .unsupported
  | .rawPtr _ pt, bytes => decodePtrLikeV2 endian pt bytes
  | .ref _ pt, bytes => decodePtrLikeV2 endian pt bytes
  | .rangeTo (.int .isize false), bytes =>
    if !Nat.beq bytes.length 8 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some raw =>
        .ok (some (.rangeTo (UInt64.ofNat (decodeUInt endian raw))))
  | .rangeFrom (.int .isize false), bytes =>
    if !Nat.beq bytes.length 8 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some raw =>
        .ok (some (.rangeFrom (UInt64.ofNat (decodeUInt endian raw))))
  -- Inverse of the model-internal `Vec` encoding in `encodeValV2`, which no
  -- program can observe (see the comment there).
  | .vec _, bytes =>
    if !Nat.beq bytes.length 24 then
      .error .unsupported
    else
      let pBytes := bytes.take 8
      let cBytes := (bytes.drop 8).take 8
      let lBytes := bytes.drop 16
      match initBytes? pBytes, readPtrProv? pBytes,
          initBytes? cBytes, initBytes? lBytes with
      | some pRaw, some prov, some cRaw, some lRaw =>
        let p : PtrVal :=
          ⟨prov, UInt64.ofNat (decodeUInt endian pRaw), .isize⟩
        let cap := UInt64.ofNat (decodeUInt endian cRaw)
        let len := UInt64.ofNat (decodeUInt endian lRaw)
        .ok (some (.vec p cap len))
      | _, _, _, _ => .ok none
  | .box pt, bytes =>
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
            let p : PtrVal :=
              ⟨prov, UInt64.ofNat (decodeUInt endian pRaw), .isize⟩
            let len := UInt64.ofNat (decodeUInt endian lRaw)
            .ok (some (.boxPtr p (some len)))
          | _, _, _ => .ok none
      | _ => .error .unsupported
    else
      if !Nat.beq bytes.length 8 then
        .error .unsupported
      else
        match initBytes? bytes, readPtrProv? bytes with
        | some pRaw, some prov =>
          let off := UInt64.ofNat (decodeUInt endian pRaw)
          .ok (some (.boxPtr ⟨prov, off, .isize⟩ none))
        | _, _ => .ok none
  | .option .bool, bytes =>
    if !Nat.beq bytes.length 1 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some [b] =>
        if Nat.beq b.toNat 0 then
          .ok (some (.optionVal (some (.bool false))))
        else if Nat.beq b.toNat 1 then
          .ok (some (.optionVal (some (.bool true))))
        else if Nat.beq b.toNat 2 then .ok (some (.optionVal none))
        else .ok none
      | some _ => .error .unsupported
  | .option .unit, bytes =>
    if !Nat.beq bytes.length 1 then
      .error .unsupported
    else
      match initBytes? bytes with
      | none => .ok none
      | some [b] =>
        if Nat.beq b.toNat 0 then .ok (some (.optionVal none))
        else if Nat.beq b.toNat 1 then .ok (some (.optionVal (some .unit)))
        else .ok none
      | some _ => .error .unsupported
  | .option inner, bytes =>
    if !isSizedNoRefV2Ty inner || !isOptionPayloadSupportedV2 inner then
      .error .unsupported
    else
      match layoutOfTyV2 inner with
      | none => .error .unsupported
      | some lay =>
        let tagBytes := Nat.pow 2 lay.alignLog2
        if !Nat.beq bytes.length (tagBytes + lay.size) then
          .error .unsupported
        else
          match initBytes? (bytes.take tagBytes) with
          | none => .ok none
          | some tagRaw =>
            let tag := decodeUInt endian tagRaw
            if Nat.beq tag 0 then
              .ok (some (.optionVal none))
            else if Nat.beq tag 1 then
              match decodeValV2 endian inner (bytes.drop tagBytes) with
              | .ok (some innerV) => .ok (some (.optionVal (some innerV)))
              | .ok none => .ok none
              | .error k => .error k
            else
              .ok none
  | .array elem len, bytes =>
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some elemLay =>
      if !Nat.beq bytes.length (len * elemLay.size) then
        .error .unsupported
      else
        match decodeFixedChunks elemLay.size (decodeValV2 endian elem) len bytes with
        | .error k => .error k
        | .ok none => .ok none
        | .ok (some vs) => .ok (some (.array vs))
  | ty, bytes => decodeVal endian ty bytes

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

/-- Validate `count` consecutive elements of non-integer sized type `elem` in
`allocBytes` starting at `off` with stride `elemSize`. -/
noncomputable def validateSliceElemsV2 (elem : MirTy)
    (allocBytes : List AllocByte) (elemSize off count : Nat) :
    Except FaultKind Unit :=
  match count with
  | 0 => .ok ()
  | n + 1 =>
    let sliceBytes := (allocBytes.drop off).take elemSize
    match decodeValV2 profileV2TargetEndian elem sliceBytes with
    | .ok (some _) =>
      validateSliceElemsV2 elem allocBytes elemSize (off + elemSize) n
    | .ok none => .error .undefined
    | .error k => .error k

/-- Decode-check `count` consecutive initialized elements of `elem` (`elemSize`
bytes each) inside a contiguous slice buffer. -/
noncomputable def sliceElemsValidV2 (elem : MirTy) (elemSize : Nat) :
    Nat → List AllocByte → Except FaultKind Unit
  | 0, _ => .ok ()
  | count + 1, bs =>
    match decodeValV2 profileV2TargetEndian elem (bs.take elemSize) with
    | .ok (some _) => sliceElemsValidV2 elem elemSize count (bs.drop elemSize)
    | .ok none => .error .undefined
    | .error k => .error k

/-- Check whether `elem` is a plain integer type (where every initialized byte
sequence is a valid value). -/
noncomputable def isIntMirTy : MirTy → Bool
  | .int _ _ => true
  | _ => false

/-- Validate a dangling or zero-length aligned non-null pointer with zero
allocated capacity. -/
noncomputable def zeroCapPtrValidInMem (m : MemoryState) (isMut : Bool)
    (alignLog2 : Nat) (p : PtrVal) : Except FaultKind Unit :=
  match p.allocId with
  | none =>
    let align := Nat.pow 2 alignLog2
    if Nat.beq p.offsetBytes.toNat 0 ||
        !Nat.beq (Nat.mod p.offsetBytes.toNat align) 0 then
      .error .undefined
    else
      .ok ()
  | some aid =>
    match findAllocation aid m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live || !isInBounds a p.offsetBytes.toNat 0 ||
          !isAligned a p.offsetBytes.toNat alignLog2 then
        .error .undefined
      else if isMut && !Mutability.beq a.mutability .mut then
        .error .undefined
      else
        .ok ()

/-- Validate `len` initialized `elem` elements (out of `cap >= len` capacity
slots) at `(p, elem)` in `m`. When `elemSize > 0` and `cap > 0`, `p` must
carry live provenance in `m` covering `[offset, offset + cap * elemSize)` with
alignment `elemAlignLog2`, mutable when `isMut = true`, and valid initialized
element bytes over `[offset, offset + len * elemSize)`. -/
noncomputable def heapBufValidInMem (m : MemoryState) (isMut : Bool)
    (elem : MirTy) (p : PtrVal) (cap len : UInt64) : Except FaultKind Unit :=
  if !IntWidth.beq p.width .isize then
    .error .unsupported
  else
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some lay =>
      if !Nat.ble len.toNat cap.toNat then
        .error .undefined
      else
        let capBytes := cap.toNat * lay.size
        if !Nat.blt capBytes isizeMaxBytes then
          .error .undefined
        else if Nat.beq lay.size 0 then
          match zeroCapPtrValidInMem m isMut lay.alignLog2 p with
          | .error k => .error k
          | .ok () =>
            if Nat.beq len.toNat 0 then
              .ok ()
            else
              match decodeValV2 profileV2TargetEndian elem [] with
              | .ok (some _) => .ok ()
              | .ok none => .error .undefined
              | .error k => .error k
        else if Nat.beq cap.toNat 0 then
          zeroCapPtrValidInMem m isMut lay.alignLog2 p
        else
          match p.allocId with
          | none => .error .undefined
          | some aid =>
            match findAllocation aid m.allocations with
            | none => .error .undefined
            | some a =>
              if !a.live || !isInBounds a p.offsetBytes.toNat capBytes ||
                  !isAligned a p.offsetBytes.toNat lay.alignLog2 then
                .error .undefined
              else if isMut && !Mutability.beq a.mutability .mut then
                .error .undefined
              else
                let lenBytes := len.toNat * lay.size
                let initSlice := (a.bytes.drop p.offsetBytes.toNat).take lenBytes
                if !isSliceAllInit initSlice then
                  .error .undefined
                else if isIntMirTy elem then
                  .ok ()
                else
                  sliceElemsValidV2 elem lay.size len.toNat initSlice

/-- Validate the owned heap buffer of a `Vec<elem>` with `cap` slots (or of a
`Box`, with `cap = len`). In addition to `heapBufValidInMem`, a non-empty
buffer of a non-zero-sized `elem` must start at offset `0` of an allocation
whose size is exactly `cap * size` bytes and whose alignment is exactly the
alignment of `elem`. That is the layout `RawVecInner::current_memory`
reconstructs and passes back to the allocator when the buffer grows, shrinks,
or is freed (`library/alloc/src/raw_vec/mod.rs:633-645`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
>     None
> } else {
> ...
>     let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
>     let layout = Layout::from_size_align_unchecked(alloc_size,
> elem_layout.align());
>     Some((self.ptr.into(), layout))"

(The last three lines are dedented by four spaces, and the
`from_size_align_unchecked` line is wrapped, here.) An allocation of any
other layout is not one the buffer could have been allocated with. -/
noncomputable def ownedHeapBufValidInMem (m : MemoryState) (isMut : Bool)
    (elem : MirTy) (p : PtrVal) (cap len : UInt64) : Except FaultKind Unit :=
  match heapBufValidInMem m isMut elem p cap len with
  | .error k => .error k
  | .ok () =>
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some lay =>
      if Nat.beq lay.size 0 || Nat.beq cap.toNat 0 then
        .ok ()
      else
        match p.allocId with
        | none => .error .undefined
        | some aid =>
          match findAllocation aid m.allocations with
          | none => .error .undefined
          | some a =>
            if !Nat.beq p.offsetBytes.toNat 0 ||
                !Nat.beq a.bytes.length (cap.toNat * lay.size) ||
                !Nat.beq a.alignLog2 lay.alignLog2 then
              .error .undefined
            else
              .ok ()

/-- Validate an owned `Box<pointee>` handle `(p, optLen)` in `m`. -/
noncomputable def boxPointeeValidInMem (m : MemoryState) (isMut : Bool)
    (pointee : MirTy) (p : PtrVal) (optLen : Option UInt64) :
    Except FaultKind Unit :=
  match pointee, optLen with
  | .slice elem, some len => ownedHeapBufValidInMem m isMut elem p len len
  | pt, none =>
    if isUnsizedTy pt then
      .error .unsupported
    else
      ownedHeapBufValidInMem m isMut pt p 1 1
  | _, _ => .error .unsupported

/-- UTF-8 validation state machine over `bs`, structurally recursive on the
byte list. `need` counts the continuation bytes still expected for the current
code point, and `lo`/`hi` bound the next continuation byte (the second byte of
`E0`, `ED`, `F0`, and `F4` sequences is narrowed to exclude overlong
encodings, UTF-16 surrogates, and code points above `U+10FFFF`; every other
continuation byte is `0x80..=0xBF`). -/
noncomputable def validUtf8Go : Nat → Nat → Nat → List UInt8 → Bool
  | 0, _, _, [] => true
  | _ + 1, _, _, [] => false
  | k + 1, lo, hi, b :: rest =>
    Nat.ble lo b.toNat && Nat.ble b.toNat hi && validUtf8Go k 0x80 0xBF rest
  | 0, _, _, b :: rest =>
    let n := b.toNat
    if Nat.blt n 0x80 then validUtf8Go 0 0x80 0xBF rest
    else if Nat.ble 0xC2 n && Nat.ble n 0xDF then validUtf8Go 1 0x80 0xBF rest
    else if Nat.beq n 0xE0 then validUtf8Go 2 0xA0 0xBF rest
    else if Nat.beq n 0xED then validUtf8Go 2 0x80 0x9F rest
    else if Nat.ble 0xE1 n && Nat.ble n 0xEF then validUtf8Go 2 0x80 0xBF rest
    else if Nat.beq n 0xF0 then validUtf8Go 3 0x90 0xBF rest
    else if Nat.ble 0xF1 n && Nat.ble n 0xF3 then validUtf8Go 3 0x80 0xBF rest
    else if Nat.beq n 0xF4 then validUtf8Go 3 0x80 0x8F rest
    else false

/-- Return `true` iff `bs` is a valid UTF-8 byte sequence per RFC 3629 and
`core::str::validations::run_utf8_validation`
(`library/core/src/str/validations.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), rejecting overlong encodings,
UTF-16 surrogates (`U+D800..=U+DFFF`), and code points above `U+10FFFF`. -/
noncomputable def validUtf8Bytes (bs : List UInt8) : Bool :=
  validUtf8Go 0 0x80 0xBF bs

/-- Check whether an already-validated `&str` slice `(p, len)` in `m` contains
valid UTF-8 bytes. -/
noncomputable def strSliceUtf8InMem (m : MemoryState) (p : PtrVal)
    (len : UInt64) : Bool :=
  if Nat.beq len.toNat 0 then
    true
  else
    match p.allocId with
    | none => false
    | some aid =>
      match findAllocation aid m.allocations with
      | none => false
      | some a =>
        let slice := (a.bytes.drop p.offsetBytes.toNat).take len.toNat
        if !Nat.beq slice.length len.toNat then
          false
        else
          match initBytes? slice with
          | none => false
          | some raw => validUtf8Bytes raw

/-- The access span `(true, allocId, offset, cap * size)` of the heap buffer
`(p, cap)` of `elem` slots that a `Vec` or `Box` owns, or `[]` when the buffer
is empty or zero-sized or `p` carries no provenance. A `Vec` or `Box` owns its
buffer uniquely, so the span is mutable. -/
noncomputable def ownedBufAccessSpans (elem : MirTy) (p : PtrVal)
    (cap : UInt64) : List (Bool × AllocId × Nat × Nat) :=
  match layoutOfTyV2 elem, p.allocId with
  | some lay, some aid =>
    if Nat.beq (cap.toNat * lay.size) 0 then
      []
    else
      [(true, aid, p.offsetBytes.toNat, cap.toNat * lay.size)]
  | _, _ => []

/-- The access spans of the heap buffer that an owned `Vec` or `Box` value
`(ty, v)` owns (`ownedBufAccessSpans`), or `[]` for any other value. -/
noncomputable def ownedHandleAccessSpans :
    MirTy → Val → List (Bool × AllocId × Nat × Nat)
  | .vec elem, .vec p cap _ => ownedBufAccessSpans elem p cap
  | .box (.slice elem), .boxPtr p (some len) => ownedBufAccessSpans elem p len
  | .box pt, .boxPtr p none => ownedBufAccessSpans pt p 1
  | _, _ => []

/-- Validate Rust language validity invariants for a `&T`, `&mut T`, `&[T]`,
`&mut [T]`, or `&str` value `v` in `m`: non-null, provenance-backed (except
valid aligned non-null `len = 0` slices / ZSTs), live allocation, bounds,
alignment, mutability for `.mut`, and initialized valid pointee value.

This implements the Reference's validity invariant for references and `str`
(`src/behavior-considered-undefined.md:180-181,195-199,136-143`,
`rust-lang/reference` `ad35aca481751a06afeb23820a672b0f3b11a476`):

> "* A `str` value is treated like `[u8]`, i.e. it must be initialized."

> "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
>   [dangling], and it must point to a valid value (in case of dynamically
>   sized types, using the actual dynamic type of the pointee as determined by
>   the metadata). Note that the last point (about pointing to a valid value)
>   remains a subject of some debate."

> "A reference/pointer is "dangling" if not all of the bytes it [points to]
> are part of the same live allocation (so in particular they all have to be
> part of *some* allocation).
>
> If the [size is 0][zero-sized], then the pointer is trivially never
> "dangling" (even if it is a null pointer)."

Integer slices and `str` delegate to `sliceFromRawPartsCheck`; non-integer
slices reject positive-length uninhabited elements via `isInhabitedV2Ty`,
validate raw bounds, alignment, and mutability via `sliceRefRawCheck`, and
enforce active-field initialization per element via `validateSliceElemsV2`.
A pointer with no provenance is accepted only for a zero-sized pointee or
zero-byte slice span at a non-null aligned address, such as
`NonNull::dangling()`.
The following approximations are intentional and conservative (`.undefined`
where Rust is defined):
- A pointer with provenance into a dead or out-of-bounds allocation is
  rejected even for a zero-sized pointee.
- `&mut` requires a `.mut` allocation even for size 0. rustc's analogous
  validity check runs only in CTFE mode and skips `size == Size::ZERO`
  (`compiler/rustc_const_eval/src/interpret/validity.rs:821-838`).
- The debated "point to a valid value" requirement is enforced. Because
  `ValidEntryArgsV2` assumes it of entry arguments, it also narrows the
  entry quantification (see `ValidEntryArgsV2`). -/
noncomputable def refValidInMem (m : MemoryState) (reqMut : Mutability)
    (pointee : MirTy) (v : Val) : Except FaultKind Unit :=
  match pointee, v with
  | .str, .slicePtr p len =>
    if Mutability.beq reqMut .mut then
      .error .unsupported
    else
      match sliceFromRawPartsCheck m false 1 0 p len with
      | .ok _ => .ok ()
      | .error k => .error k
  | .slice elem, .slicePtr p len =>
    if !isSizedNoRefV2Ty elem then
      .error .unsupported
    else
      match layoutOfTyV2 elem with
      | none => .error .unsupported
      | some lay =>
        let isMut := Mutability.beq reqMut .mut
        match elem with
        | .int _ _ =>
          match sliceFromRawPartsCheck m isMut lay.size lay.alignLog2
              p len with
          | .error k => .error k
          | .ok _ => .ok ()
        | _ =>
          if Nat.blt 0 len.toNat && !isInhabitedV2Ty elem then
            .error .undefined
          else
            match sliceRefRawCheck m isMut lay.size lay.alignLog2 p len with
            | .error k => .error k
            | .ok optAlloc =>
              if Nat.beq len.toNat 0 || Nat.beq lay.size 0 then
                .ok ()
              else
                match optAlloc with
                | none => .error .undefined
                | some a =>
                  validateSliceElemsV2 elem a.bytes lay.size
                    p.offsetBytes.toNat len.toNat
  | .str, _ => .error .unsupported
  | _, .ptr p =>
    if !isSupportedV2PointeeTy pointee && !isHeapHandleTyV2 pointee then
      .error .unsupported
    else
      match layoutOfTyV2 pointee with
      | none => .error .unsupported
      | some lay =>
        match p.allocId with
        | none =>
          if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 lay.size then
            .error .undefined
          else if !Nat.beq
              (Nat.mod p.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
            .error .undefined
          else
            match decodeValV2 profileV2TargetEndian pointee [] with
            | .ok (some decVal) =>
              match pointee, decVal with
              | .vec elem, .vec bufPtr cap len =>
                ownedHeapBufValidInMem m (Mutability.beq reqMut .mut) elem bufPtr
                  cap len
              | .box pt, .boxPtr boxP optLen =>
                boxPointeeValidInMem m (Mutability.beq reqMut .mut) pt boxP optLen
              | _, _ => .ok ()
            | .ok none => .error .undefined
            | .error k => .error k
        | some aid =>
          match findAllocation aid m.allocations with
          | none => .error .undefined
          | some a =>
            if !a.live || !isInBounds a p.offsetBytes.toNat lay.size ||
                !isAligned a p.offsetBytes.toNat lay.alignLog2 then
              .error .undefined
            else if Mutability.beq reqMut .mut &&
                !Mutability.beq a.mutability .mut then
              .error .undefined
            else
              let sliceBytes := (a.bytes.drop p.offsetBytes.toNat).take lay.size
              match decodeValV2 profileV2TargetEndian pointee sliceBytes with
              | .ok (some decVal) =>
                match pointee, decVal with
                | .vec elem, .vec bufPtr cap len =>
                  ownedHeapBufValidInMem m (Mutability.beq reqMut .mut) elem
                    bufPtr cap len
                | .box pt, .boxPtr boxP optLen =>
                  boxPointeeValidInMem m (Mutability.beq reqMut .mut) pt boxP
                    optLen
                | _, _ => .ok ()
              | .ok none => .error .undefined
              | .error k => .error k
  | _, _ => .error .unsupported

mutual
  /-- Validate all references and owned heap handles inside `v` (including
  `Option` and tuple components) against `m`. Raw pointers `.rawPtr` are not
  constrained by reference validity.

  Validity is checked per field and never through a pointer indirection
  (`src/behavior-considered-undefined.md:186-187,176-178`,
  `rust-lang/reference` `ad35aca481751a06afeb23820a672b0f3b11a476`):

  > "* A `struct`, tuple, and array requires all fields/elements to be valid
  >   at their respective type."

  > "* An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer
  >   must be initialized, i.e., must not be obtained from uninitialized
  >   memory."

  The pointee of a raw pointer has no validity requirement, and initialization
  of the raw pointer itself is enforced by `checkValV2` and `decodeValV2`.
  Profile v2 pointees contain no references (`isSupportedV2LocalTy`), so the
  recursion stops at the first reference or owned heap handle. -/
  noncomputable def refsValidInMem (m : MemoryState) : MirTy → Val → Bool
    | .ref reqMut pt, v =>
      match refValidInMem m reqMut pt v with
      | .ok () => true
      | .error _ => false
    | .option inner, .optionVal (some innerV) => refsValidInMem m inner innerV
    | .option _, .optionVal none => true
    | .vec elem, .vec bufPtr cap len =>
      match ownedHeapBufValidInMem m true elem bufPtr cap len with
      | .ok () => true
      | .error _ => false
    | .box pt, .boxPtr boxP optLen =>
      match boxPointeeValidInMem m true pt boxP optLen with
      | .ok () => true
      | .error _ => false
    | .tuple ts, .tuple vs => refsValidInMemList m ts vs
    | .array elem _, .array vs => refsValidInMemArray m elem vs
    | _, _ => true

  noncomputable def refsValidInMemList (m : MemoryState) :
      List MirTy → List Val → Bool
    | [], [] => true
    | t :: ts, v :: vs => refsValidInMem m t v && refsValidInMemList m ts vs
    | _, _ => false

  noncomputable def refsValidInMemArray (m : MemoryState) (elem : MirTy) :
      List Val → Bool
    | [] => true
    | v :: vs => refsValidInMem m elem v && refsValidInMemArray m elem vs
end

mutual
  /-- Extract provenance-backed `(isMut, allocId, offset, byteSize)` access
  spans for every reference component inside `(ty, v)`, and the mutable span of
  the heap buffer of every owned `Vec` or `Box` component
  (`ownedBufAccessSpans`). The buffer behind a reference to a `Vec` or `Box`
  handle is not included; receipts state its disjointness from that handle and
  from every other argument as an assumption. -/
  noncomputable def refAccessSpans :
      MirTy → Val → List (Bool × AllocId × Nat × Nat)
    | .ref reqMut (.slice elem), .slicePtr p len =>
      match layoutOfTyV2 elem, p.allocId with
      | some lay, some aid =>
        [(Mutability.beq reqMut .mut, aid, p.offsetBytes.toNat,
          len.toNat * lay.size)]
      | _, _ => []
    | .ref reqMut .str, .slicePtr p len =>
      match p.allocId with
      | some aid =>
        [(Mutability.beq reqMut .mut, aid, p.offsetBytes.toNat, len.toNat)]
      | none => []
    | .ref reqMut pt, .ptr p =>
      match layoutOfTyV2 pt, p.allocId with
      | some lay, some aid => [(Mutability.beq reqMut .mut, aid, p.offsetBytes.toNat, lay.size)]
      | _, _ => []
    | .option inner, .optionVal (some innerV) => refAccessSpans inner innerV
    | .option _, .optionVal none => []
    | .tuple ts, .tuple vs => refAccessSpansList ts vs
    | .array elem _, .array vs => refAccessSpansArray elem vs
    | ty, v => ownedHandleAccessSpans ty v

  noncomputable def refAccessSpansList :
      List MirTy → List Val → List (Bool × AllocId × Nat × Nat)
    | [], [] => []
    | t :: ts, v :: vs => refAccessSpans t v ++ refAccessSpansList ts vs
    | _, _ => []

  noncomputable def refAccessSpansArray (elem : MirTy) :
      List Val → List (Bool × AllocId × Nat × Nat)
    | [] => []
    | v :: vs => refAccessSpans elem v ++ refAccessSpansArray elem vs
end

mutual
  /-- Extract all allocation ids referenced by any `.ref` inside `(ty, v)`. -/
  noncomputable def refAllocIds : MirTy → Val → List AllocId
    | .ref _ (.slice _), .slicePtr p _
    | .ref _ .str, .slicePtr p _ =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .ref _ _, .ptr p =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .option inner, .optionVal (some innerV) => refAllocIds inner innerV
    | .option _, .optionVal none => []
    | .tuple ts, .tuple vs => refAllocIdsList ts vs
    | .array elem _, .array vs => refAllocIdsArray elem vs
    | _, _ => []

  noncomputable def refAllocIdsList : List MirTy → List Val → List AllocId
    | [], [] => []
    | t :: ts, v :: vs => refAllocIds t v ++ refAllocIdsList ts vs
    | _, _ => []

  noncomputable def refAllocIdsArray (elem : MirTy) : List Val → List AllocId
    | [] => []
    | v :: vs => refAllocIds elem v ++ refAllocIdsArray elem vs
end

mutual
  /-- Extract all allocation ids referenced by any `.ref` or `.rawPtr` inside
  `(ty, v)`. -/
  noncomputable def ptrOrRefAllocIds : MirTy → Val → List AllocId
    | .ref _ (.slice _), .slicePtr p _
    | .rawPtr _ (.slice _), .slicePtr p _
    | .ref _ .str, .slicePtr p _ =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .ref _ _, .ptr p
    | .rawPtr _ _, .ptr p =>
      match p.allocId with
      | some aid => [aid]
      | none => []
    | .option inner, .optionVal (some innerV) => ptrOrRefAllocIds inner innerV
    | .tuple ts, .tuple vs => ptrOrRefAllocIdsList ts vs
    | .array elem _, .array vs => ptrOrRefAllocIdsArray elem vs
    | _, _ => []

  noncomputable def ptrOrRefAllocIdsList : List MirTy → List Val → List AllocId
    | [], [] => []
    | t :: ts, v :: vs => ptrOrRefAllocIds t v ++ ptrOrRefAllocIdsList ts vs
    | _, _ => []

  noncomputable def ptrOrRefAllocIdsArray (elem : MirTy) :
      List Val → List AllocId
    | [] => []
    | v :: vs => ptrOrRefAllocIds elem v ++ ptrOrRefAllocIdsArray elem vs
end

/-- Return `true` when `aid` identifies a callee-allocated immutable `.rodata`
allocation (present in `mem` with `mutability = .shared`, absent from `cm`).
Callee stack allocations always have `mutability = .mut`. -/
noncomputable def isRodataAllocId (cm : CallerMemory) (mem : MemoryState)
    (aid : AllocId) : Bool :=
  match findAllocation aid cm.allocations with
  | some _ => false
  | none =>
    match findAllocation aid mem.allocations with
    | some a => Mutability.beq a.mutability .shared
    | none => false

/-- Check whether any allocation id in `ids` is a callee `.rodata`
allocation. -/
noncomputable def anyRodataAllocId (cm : CallerMemory) (mem : MemoryState) :
    List AllocId → Bool
  | [] => false
  | aid :: rest => isRodataAllocId cm mem aid || anyRodataAllocId cm mem rest

/-- Return `true` when any `.ref` or `.rawPtr` inside `(ty, v)` points into a
callee-allocated immutable `.rodata` allocation. -/
noncomputable def hasEscapingRodataPtr (cm : CallerMemory) (mem : MemoryState)
    (ty : MirTy) (v : Val) : Bool :=
  anyRodataAllocId cm mem (ptrOrRefAllocIds ty v)

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
