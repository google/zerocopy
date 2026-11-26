-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.BasicAux
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-!
# Endian Wrapper Sealing Markers & `byteorder` Model Semantics

Formal specification for `zerocopy/src/byteorder.rs` (`U16`..`Isize`, `F32`,
`F64` parameterized by `BigEndian` and `LittleEndian`) grounded in the
`u8`-array safety delegation (`byteorder.rs:535-538`):

1. **Selected MIR sealing markers (`CapturedByteorderMatrixSpec`):** Binds the
   175 selected verbatim `only_derive_is_allowed_to_implement_this_trait`
   functions: 7 foundational non-generic `u8` trait markers (`impls.rs` and
   `lib.rs`) plus all 168 concrete `--instantiate` monomorphizations across the
   12 `byteorder` types (`U16`, `U32`, `U64`, `U128`, `Usize`, `I16`, `I32`,
   `I64`, `I128`, `Isize`, `F32`, `F64`), both local endian marker types
   (`byteorder::BigEndian`, `byteorder::LittleEndian`), and all 7 traits
   (`KnownLayout`, `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`,
   `IntoBytes`, `Unaligned`). Methods on `BigEndian`, `LittleEndian`, `Order`,
   and `byteorder::*<O>` (`new`, `get`, `from_bytes`, `to_bytes`, `set`, `fmt`,
   `clone`, `eq`) remain outside `Trusted.MirAst` Profile v1 (`Struct`,
   `Array`, `&T`, `&mut T`, and `Result<(), fmt::Error>`).
2. **Model-side `Trusted.MirSemantics.Bytes` & `Layout` contracts
   (`ByteorderModelSpec`):**
   - *Proved directly on `Trusted.MirSemantics.{Bytes,Layout}`:*
     - `u8` backing layout (`⟨1, 0⟩`, size `1` and `alignLog2 = 0`) and 1-byte
       endian invariance for `decodeUInt`/`encodeUInt`/`decodeVal`;
     - `BigEndian` vs. `LittleEndian` byte-reversal duality on `encodeUInt` /
       `decodeUInt` (`encodeUInt_swapEndian`, `decodeUInt_reverse`, paired via
       the `Spec`-local `swapEndian` helper);
     - exact endian codec round-trip laws (`decodeUInt_encodeUInt`,
       `encodeUInt_decodeUInt`, cross-endian byte reversal
       `encodeUInt_decodeUInt_swap`) alongside concrete 2-, 4-, 8-, and
       16-byte witnesses distinguishing `.big` from `.little`;
     - typed `AllInitBytes` `FromBytes`/`IntoBytes` round-trip soundness over
       `decodeVal`/`encodeVal` for every `TargetEndian`, `signed : Bool`, and
       `w : IntWidth`;
     - native multi-byte scalar size and alignment (`w ≠ .i8 → ∃ l,
       layoutOfTy (.int w signed) = some l ∧ l.size = w.byteSize ∧
       0 < l.alignLog2`); and
     - fail-closed `.unsupported` boundary for `f32`/`f64` `MirTy` plus
       4-byte (`32`-bit) and 8-byte (`64`-bit) raw bit-pattern
       `decodeUInt`/`encodeUInt` and cross-endian byte-reversal round-trip
       theorems across both `TargetEndian` values (modeling raw storage for
       `F32<O>`/`F64<O>`).
   - *`Spec`-local helper definitions:* `swapEndian` (`swapEndian_involutive` is
     a structural lemma on this `Spec`-local helper; `[u8; N]` and
     `#[repr(transparent)]` wrapper layouts themselves are not lowered by
     `Trusted.MirAst` Profile v1).
-/

/-- Canonical `rust-path-v1` identities of the 7 foundational `u8` markers and
168 monomorphized `byteorder::*<BigEndian|LittleEndian>` markers (in canonical
`capture.json` body order). -/
def byteorderMarkerIdentities : List String := [
  "rust-path-v1::_::<impl KnownLayout for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromBytes for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl FromZeros for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Immutable for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl IntoBytes for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl KnownLayout for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl TryFromBytes for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::F32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::F32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::F64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::F64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::I64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::Isize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::Isize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U128<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U128<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U16<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U16<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U32<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U32<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U64<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::U64<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::Usize<byteorder::BigEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::byteorder::_::<impl Unaligned for byteorder::Usize<byteorder::LittleEndian>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for u8>::only_derive_is_allowed_to_implement_this_trait"
]

/-! ## Part 1: Selected MIR Sealing-Marker Contract -/

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition over the 175 selected
zero-argument `u8` and `byteorder` trait sealing markers. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity ∈ byteorderMarkerIdentities ∧ args = []

/-- Asserts that `program.bodies[defId]` has canonical path `identity`, is safe
(`isUnsafe = false`), takes zero arguments (`argumentCount = 0`), satisfies
`ReturnsTotal` returning `()` on `[]`, and steps cleanly to `()` from every
initial `mem : MemoryState` without mutating `mem`. -/
noncomputable def UnitMarkerAt (program : Program) (defId : DefId)
    (identity : String) : Prop :=
  ∃ b : Body,
    Trusted.MirSemantics.getElem? program.bodies defId = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program defId [] .unit ∧
    ∀ mem : MemoryState,
      ∃ s₁ : State,
        Step program
          { frames :=
              [{ defId := defId, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }],
             callerMem := ⟨[]⟩, mem := mem }
          (.step s₁) ∧
        s₁.mem = mem ∧
        Step program s₁ (.done (.returned ⟨.unit, ⟨[]⟩⟩))

/-- MIR contract over all 175 captured `u8` and monomorphized `byteorder`
trait sealing markers: exact body count matching `byteorderMarkerIdentities`
and indexed `UnitMarkerAt` agreement at every `defId`. -/
noncomputable def CapturedByteorderMatrixSpec (program : Program) : Prop :=
  program.bodies.length = byteorderMarkerIdentities.length ∧
  ∀ (defId : DefId) (identity : String),
    Trusted.MirSemantics.getElem? byteorderMarkerIdentities defId =
      some identity →
    UnitMarkerAt program defId identity

/-! ## Part 2: Model-Side Endian Codec, Alignment, and Bit-Validity Spec -/

/-- `Spec`-local byte-order dual pairing `BigEndian` and `LittleEndian`. -/
def swapEndian : TargetEndian → TargetEndian
  | .little => .big
  | .big => .little

/-- `bs` has exact byte length `n` and every byte in `bs` is initialized
(`initBytes? bs = some raw`, stripping pointer provenance as in
`read_scalar`). -/
noncomputable def AllInitBytes (n : Nat) (bs : List AllocByte) : Prop :=
  bs.length = n ∧ ∃ raw : List UInt8, initBytes? bs = some raw

/-- `FromBytes` semantic contract on `Trusted.MirSemantics`: every `w.byteSize`
initialized byte slice `bs` decodes in byte order `endian` to a well-formed
scalar value `sv` of `(.int w signed)`. -/
noncomputable def IntFromBytesEndianSound (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) : Prop :=
  ∀ bs : List AllocByte,
    AllInitBytes w.byteSize bs →
    ∃ sv : ScalarVal,
      decodeVal endian (.int w signed) bs = .ok (some (.scalar sv)) ∧
      checkVal (.scalar sv) (.int w signed) = true

/-- `IntoBytes` semantic contract on `Trusted.MirSemantics`: every well-formed
scalar value of `(.int w signed)` encodes in byte order `endian` to an
initialized, provenance-free byte slice of exact length `w.byteSize` whose
re-decoding recovers `sv`. -/
noncomputable def IntIntoBytesEndianSound (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) : Prop :=
  ∀ sv : ScalarVal,
    checkVal (.scalar sv) (.int w signed) = true →
    ∃ bs : List AllocByte,
      encodeVal endian (.int w signed) (.scalar sv) = .ok bs ∧
      bs.length = w.byteSize ∧
      (∃ raw : List UInt8,
        initBytes? bs = some raw ∧
        bs = raw.map (fun b => AllocByte.init b none)) ∧
      decodeVal endian (.int w signed) bs = .ok (some (.scalar sv))

/-- Model-side endianness, `Spec`-local `swapEndian` duality,
`encodeUInt`/`decodeUInt` round-trips, `IntWidth` `FromBytes`/`IntoBytes`,
native vs. `u8` alignment, and `.unsupported` float plus 4- and 8-byte raw
bit-pattern codec specification. -/
noncomputable def ByteorderModelSpec : Prop :=
  -- 1. `u8` foundation (`⟨1, 0⟩` layout and 1-byte endian invariance)
  layoutOfTy (.int .i8 false) = some ⟨1, 0⟩ ∧
  (∀ (e1 e2 : TargetEndian) (b : UInt8) (v : Nat),
    decodeUInt e1 [b] = b.toNat ∧
    decodeUInt e1 [b] = decodeUInt e2 [b] ∧
    encodeUInt e1 1 v = [UInt8.ofNat (v % 256)] ∧
    decodeVal e1 (.int .i8 false) [AllocByte.init b none] =
      .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩))) ∧
  -- 2. Byte-reversal involution and Big-vs-Little duality
  (∀ e : TargetEndian, swapEndian (swapEndian e) = e) ∧
  (∀ (e : TargetEndian) (n value : Nat),
    (encodeUInt e n value).length = n ∧
    encodeUInt (swapEndian e) n value = (encodeUInt e n value).reverse) ∧
  (∀ (e : TargetEndian) (bs : List UInt8),
    decodeUInt e bs.reverse = decodeUInt (swapEndian e) bs) ∧
  -- 3. Exact endian codec round-trips and cross-endian byte reversal
  (∀ (e : TargetEndian) (n value : Nat),
    decodeUInt e (encodeUInt e n value) = value % Nat.pow 2 (8 * n)) ∧
  (∀ (e : TargetEndian) (n value : Nat),
    value < Nat.pow 2 (8 * n) →
    decodeUInt e (encodeUInt e n value) = value) ∧
  (∀ (e : TargetEndian) (bs : List UInt8),
    encodeUInt e bs.length (decodeUInt e bs) = bs ∧
    encodeUInt e bs.length (decodeUInt (swapEndian e) bs) = bs.reverse) ∧
  -- 4. Concrete 2-, 4-, 8-, and 16-byte Big-vs-Little separation witnesses
  (encodeUInt .big 2 0x0102 = [0x01, 0x02] ∧
    encodeUInt .little 2 0x0102 = [0x02, 0x01] ∧
    encodeUInt .big 2 0x0102 ≠ encodeUInt .little 2 0x0102 ∧
    decodeUInt .big [0x01, 0x02] = 0x0102 ∧
    decodeUInt .little [0x01, 0x02] = 0x0201 ∧
    decodeUInt .big [0x01, 0x02] ≠ decodeUInt .little [0x01, 0x02] ∧
    encodeUInt .big 4 0x01020304 = [0x01, 0x02, 0x03, 0x04] ∧
    encodeUInt .little 4 0x01020304 = [0x04, 0x03, 0x02, 0x01] ∧
    decodeUInt .big [0x01, 0x02, 0x03, 0x04] = 0x01020304 ∧
    decodeUInt .little [0x01, 0x02, 0x03, 0x04] = 0x04030201 ∧
    decodeUInt .big (encodeUInt .little 8 0x0123456789ABCDEF).reverse =
      0x0123456789ABCDEF ∧
    decodeUInt .little (encodeUInt .big 16 0x0123456789ABCDEF).reverse =
      0x0123456789ABCDEF) ∧
  -- 5. Typed `IntWidth` `FromBytes`/`IntoBytes` & `Unaligned` vs. native align
  (∀ (e : TargetEndian) (signed : Bool) (w : IntWidth),
    IntFromBytesEndianSound e signed w ∧
    IntIntoBytesEndianSound e signed w) ∧
  (∀ (w : IntWidth) (signed : Bool),
    w ≠ .i8 →
    ∃ l : LayoutData,
      layoutOfTy (.int w signed) = some l ∧
      l.size = w.byteSize ∧
      0 < l.alignLog2) ∧
  -- 6. Fail-closed float boundary (`F32<O>`/`F64<O>`) and 4/8-byte codecs
  (layoutOfTy .unsupported = none ∧
    (∀ (e : TargetEndian) (bs : List AllocByte),
      decodeVal e .unsupported bs = .error .unsupported) ∧
    (∀ (e : TargetEndian) (bits : Nat),
      bits < Nat.pow 2 32 →
      decodeUInt e (encodeUInt e 4 bits) = bits ∧
      decodeUInt (swapEndian e) (encodeUInt e 4 bits).reverse = bits ∧
      (encodeUInt e 4 bits).length = 4) ∧
    (∀ (e : TargetEndian) (bits : Nat),
      bits < Nat.pow 2 64 →
      decodeUInt e (encodeUInt e 8 bits) = bits ∧
      decodeUInt (swapEndian e) (encodeUInt e 8 bits).reverse = bits ∧
      (encodeUInt e 8 bits).length = 8))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, fun program =>
    CapturedByteorderMatrixSpec program ∧ ByteorderModelSpec⟩

end Spec
