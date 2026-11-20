-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Div.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.Layout
import Trusted.MirSemantics.Memory

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
- `.unit` and 1-variant `.zeroSized` enums: no bytes.
- `.scalar tagW _` enums: the `tagW.byteSize` low bytes of the variant's
  discriminant (a `TagEncoding::Direct` tag stores the discriminant truncated
  to the tag width).

Every encoded byte is initialized and carries no provenance. A value that is
not a well-formed value of `ty` (`checkVal v ty = false`), and any other
`(ty, v)` pair outside the Day-1 fragment, returns `.error .unsupported`. -/
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
    | _, _ => .error .unsupported

/-- Decode the bytes `bytes` of a value of type `ty` in byte order `endian`:
`.ok (some v)` for a valid value `v`, `.ok none` for bytes that do not hold an
initialized value, or a fault.

- `.never`: no valid value exists, so the result is `.ok none` (as for an
  uninitialized `.immediate none` slot of type `.never`, a later use faults
  with `.undefined`).
- Zero-sized types (`.unit` and 1-variant `.zeroSized` enums): the type's
  unique value, via `evalConstLit ty .zeroSized`.
- Other Day-1 types: `.ok none` if any byte is uninitialized (`initBytes?`),
  and otherwise the result of `evalConstLit ty` on the bytes decoded as an
  unsigned integer (`decodeUInt`), which faults with `.undefined` on an
  invalid `bool` byte or an enum tag that matches no discriminant.

A byte count that differs from `layoutOfTy ty`, or a type outside the Day-1
fragment (including an enum that `enumAdmitted` rejects, which has no
layout), returns `.error .unsupported` before any byte is inspected. -/
noncomputable def decodeVal (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  match ty with
  | .never => .ok none
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

end Trusted.MirSemantics
