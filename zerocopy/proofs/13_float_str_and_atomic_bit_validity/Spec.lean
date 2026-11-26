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
# Float, `str`, and `Atomic*` Sealing Markers & Model-Side Bit Validity

Formal specification for the 61 selected trait-sealing impls for `f32`, `f64`,
`str`, `AtomicBool`, and the 10 concrete integer `Atomic*` types (`AtomicU8`..
`AtomicIsize`) compiled in `zerocopy/src/impls.rs` under this unit's `cfg` on
`x86_64-unknown-linux-gnu` (excluding `KnownLayout`, generic `AtomicPtr<T>`, and
feature-gated `f16`/`f128`/`simd` impls):

1. **Selected MIR sealing markers (`CapturedFloatStrAtomicMatrixSpec`):** Binds
   the 61 selected verbatim `only_derive_is_allowed_to_implement_this_trait`
   functions in `zerocopy/src/impls.rs` (`10` IEEE float in `impls.rs:81-82`,
   `5` `str` in `impls.rs:165-180`, and `46` `Atomic*` in `impls.rs:454-609`,
   excluding `KnownLayout`, `AtomicPtr<T>`, and feature-gated `f16`/`f128`/
   `simd`) by exact count, canonical `b.identity` path, `b.isUnsafe = false`,
   `b.argumentCount = 0`, total `()` return (`ReturnsTotal`), and
   memory-preserving execution over every `MemoryState`.
2. **Model-side byte-validity, UTF-8, and `UnsafeCell` contracts
   (`FloatStrAtomicBitValiditySpec`):** `<str as TryFromBytes>::is_safe` and
   `impl_for_transmute_from!` `TryFromBytes::is_safe` validator MIR bodies are
   not yet captured, and `Trusted.MirAst.MirTy` currently maps `Float`, `Str`,
   and non-fieldless-enum ADTs (`UnsafeCell`, `Atomic*`) to `.unsupported`
   (`layoutOfTy .unsupported = none`). Part 2 therefore combines:
   - explicit `Spec`-local IEEE `f32`/`f64` layout and `AllocByte` bit-validity
     definitions (`FloatWidth`, `floatLayout`, `FloatValidBytes`) defining
     `AllInitBytes (floatLayout fw).size` acceptance (including `±0.0` and
     NaN byte patterns), excluding `.uninit`, and giving `0 < alignLog2` in
     `floatLayout`, with `FloatFromBytesSound` and `FloatIntoBytesSound`
     relating every valid slice to a bit pattern via the `encodeUInt` /
     `decodeUInt` byte codec;
   - an explicit `Spec`-local RFC 3629 §4 UTF-8 9-state byte DFA (8 live
     states `0..7` plus the rejecting sink `8`)
     (`IsValidUtf8Bytes`) proved equivalent to the 4-width / 8-production
     RFC 3629 head-scalar byte grammar (`ValidUtf8StepDecomp`), establishing
     `StrFromZerosSound`, `StrIntoBytesSound`, multi-byte witnesses, and
     negative `FromBytes` model refutations (`[0xFF]`, lone continuation
     `[0x80]`, overlong NUL `[0xC0, 0x80]`, UTF-8 surrogate `[0xED, 0xA0, 0x80]`
     = `U+D800`, and every positive byte length `n + 1`); and
   - `Trusted.MirSemantics` bit-validity theorems for the backing scalar types
     (`.bool` and `.int w s`), linked to `AtomicBool` and `Atomic{U,I}*` by
     the `Spec`-local assumed correspondence `atomicBackingMirTy` (reflecting
     `core::sync::atomic`'s documented same-size and bit-validity guarantee,
     with `∀ w : IntWidth` also covering `.i128` even though
     `core::sync::atomic` has no 128-bit atomic); the `impls.rs:468-492`
     `Unaligned` argument for the 1-byte atomics (a 1-byte layout whose size
     is a multiple of its alignment has alignment 1); and the contrast that
     primitive `.int w s` for `w ≠ .i8` has alignment above 1; paired with an
     explicit `Spec`-local `SurfaceWrapperKind` / `ContainsUnsafeCell`
     classification (`ImmutableSound` holds for the 5 `UnsafeCell`-free
     families and fails for `UnsafeCell`, `AtomicBool`, and `Atomic{U,I}*`).
-/

/-- Canonical `rust-path-v1` identities of the 61 selected trait sealing markers
for `f32`, `f64`, `str`, and `core::sync::atomic::Atomic*` in
`zerocopy/src/impls.rs` (canonical SCC shard order). -/
def floatStrAtomicMarkerIdentities : List String := [
  "rust-path-v1::impls::_::<impl FromBytes for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl FromBytes for core::sync::atomic::Atomic<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl FromBytes for core::sync::atomic::Atomic<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl FromZeros for core::sync::atomic::Atomic<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl FromZeros for core::sync::atomic::Atomic<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl IntoBytes for core::sync::atomic::Atomic<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl IntoBytes for core::sync::atomic::Atomic<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl TryFromBytes for core::sync::atomic::Atomic<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl TryFromBytes for core::sync::atomic::Atomic<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl FromBytes for core::sync::atomic::Atomic<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl FromBytes for core::sync::atomic::Atomic<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl FromZeros for core::sync::atomic::Atomic<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl FromZeros for core::sync::atomic::Atomic<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl IntoBytes for core::sync::atomic::Atomic<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl IntoBytes for core::sync::atomic::Atomic<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl TryFromBytes for core::sync::atomic::Atomic<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl TryFromBytes for core::sync::atomic::Atomic<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl FromBytes for core::sync::atomic::Atomic<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl FromBytes for core::sync::atomic::Atomic<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl FromZeros for core::sync::atomic::Atomic<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl FromZeros for core::sync::atomic::Atomic<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl IntoBytes for core::sync::atomic::Atomic<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl IntoBytes for core::sync::atomic::Atomic<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl TryFromBytes for core::sync::atomic::Atomic<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl TryFromBytes for core::sync::atomic::Atomic<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl FromBytes for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl FromBytes for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl FromZeros for core::sync::atomic::Atomic<bool>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl FromZeros for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl FromZeros for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl IntoBytes for core::sync::atomic::Atomic<bool>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl IntoBytes for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl IntoBytes for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl TryFromBytes for core::sync::atomic::Atomic<bool>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl TryFromBytes for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl TryFromBytes for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl Unaligned for core::sync::atomic::Atomic<bool>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl Unaligned for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl Unaligned for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl FromBytes for core::sync::atomic::Atomic<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl FromBytes for core::sync::atomic::Atomic<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl FromZeros for core::sync::atomic::Atomic<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl FromZeros for core::sync::atomic::Atomic<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl IntoBytes for core::sync::atomic::Atomic<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl IntoBytes for core::sync::atomic::Atomic<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl TryFromBytes for core::sync::atomic::Atomic<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl TryFromBytes for core::sync::atomic::Atomic<usize>>::only_derive_is_allowed_to_implement_this_trait"
]

/-! ## Part 1: Selected MIR Sealing-Marker Contract -/

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition over the 61 selected
zero-argument trait sealing markers. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity ∈ floatStrAtomicMarkerIdentities ∧ args = []

/-- Asserts that `program.bodies[defId]` has canonical path `identity`, is safe
(`isUnsafe = false`), takes zero arguments (`argumentCount = 0`), satisfies
`ReturnsTotal` returning `()` on `[]`, and steps cleanly to `()` from every
initial `mem : MemoryState` without mutating `mem`. -/
def UnitMarkerAt (program : Program) (defId : DefId)
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
          { frames := [⟨defId, 0, 0, [.immediate none], none, none, none⟩],
             callerMem := ⟨[]⟩, mem := mem }
          (.step s₁) ∧
        s₁.mem = mem ∧
        Step program s₁ (.done (.returned ⟨.unit, ⟨[]⟩⟩))

/-- MIR contract over the 61 selected float, `str`, and `Atomic*` trait sealing
markers: exact body count matching `floatStrAtomicMarkerIdentities` and indexed
`UnitMarkerAt` agreement at every `defId`. -/
def CapturedFloatStrAtomicMatrixSpec (program : Program) : Prop :=
  program.bodies.length = floatStrAtomicMarkerIdentities.length ∧
  ∀ (defId : DefId) (identity : String),
    Trusted.MirSemantics.getElem? floatStrAtomicMarkerIdentities defId =
      some identity →
    UnitMarkerAt program defId identity

/-! ## Part 2: Model-Side Float, UTF-8 `str`, and `Atomic*` Contracts -/

/-- `bs` has exact byte length `n` and every byte in `bs` is initialized
(`initBytes? bs = some raw`, stripping pointer provenance as in `read_scalar`).
-/
def AllInitBytes (n : Nat) (bs : List AllocByte) : Prop :=
  bs.length = n ∧ ∃ raw : List UInt8, initBytes? bs = some raw

/-- Canonical provenance-free all-zero byte slice of length `n`. -/
def zeroAllocBytes (n : Nat) : List AllocByte :=
  List.replicate n (AllocByte.init 0 none)

/-- `FromZeros` semantic contract on `Trusted.MirSemantics`: `ty` has a sized
layout and `layout.size` zero-initialized bytes decode without fault to a
well-formed value of `ty`. -/
def IsFromZeros (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout v,
    layoutOfTy ty = some layout ∧
    decodeVal endian ty (List.replicate layout.size (.init 0 none)) =
      .ok (some v) ∧
    checkVal v ty = true

/-- `FromBytes` semantic contract on `Trusted.MirSemantics`: `ty` has a sized
layout and every initialized byte sequence of length `layout.size` decodes
without fault to a well-formed value of `ty`. -/
def IsFromBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    layoutOfTy ty = some layout ∧
    ∀ (bs : List AllocByte) (raw : List UInt8),
      bs.length = layout.size →
      initBytes? bs = some raw →
      ∃ v, decodeVal endian ty bs = .ok (some v) ∧ checkVal v ty = true

/-- `IntoBytes` semantic contract on `Trusted.MirSemantics`: `ty` has a sized
layout, every well-formed value of `ty` encodes without fault, and every encoded
byte sequence has length `layout.size` with all bytes initialized. -/
def IsIntoBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    layoutOfTy ty = some layout ∧
    (∀ v : Val, checkVal v ty = true → ∃ bs, encodeVal endian ty v = .ok bs) ∧
    (∀ (v : Val) (bs : List AllocByte),
      encodeVal endian ty v = .ok bs →
      bs.length = layout.size ∧
      ∃ raw : List UInt8,
        initBytes? bs = some raw ∧
        bs = raw.map (fun b => AllocByte.init b none))

/-- `Unaligned` semantic contract on `Trusted.MirSemantics`: `ty` has a sized
layout with 1-byte alignment (`alignLog2 = 0`). -/
def IsUnaligned (ty : MirTy) : Prop :=
  ∃ layout, layoutOfTy ty = some layout ∧ layout.alignLog2 = 0

/-- Model-side byte-validity condition matching
`<bool as TryFromBytes>::is_safe` (shared with `AtomicBool` via
`impl_for_transmute_from!`; validator MIR body not captured): initialized 1-byte
sequences decode iff `< 2` and fault otherwise. -/
def BoolTryFromBytesSound (endian : TargetEndian) : Prop :=
  ∀ (bs : List AllocByte) (raw : List UInt8),
    bs.length = 1 →
    initBytes? bs = some raw →
    (decodeUInt endian raw < 2 →
      ∃ b : Bool,
        decodeVal endian .bool bs = .ok (some (.bool b)) ∧
        checkVal (.bool b) .bool = true) ∧
    (2 ≤ decodeUInt endian raw →
      decodeVal endian .bool bs = .error .undefined)

/-! ### Section 2A: Spec-Local IEEE `f32`/`f64` Byte-Validity Model -/

/-- Spec-local two-element IEEE 754 binary floating-point width tag (`false` =
`f32`, `true` = `f64`), defined over `Bool` because `Trusted.MirAst.MirTy`
currently maps `TyKind::Float` to `.unsupported`. -/
abbrev FloatWidth : Type := Bool

/-- IEEE 754 binary32 (`f32`) width selector. -/
def floatF32 : FloatWidth := false

/-- IEEE 754 binary64 (`f64`) width selector. -/
def floatF64 : FloatWidth := true

/-- Spec-local 64-bit natural-aligned `LayoutData` for IEEE `f32` (`4` bytes,
`alignLog2 = 2`) and `f64` (`8` bytes, `alignLog2 = 3`). -/
def floatLayout (fw : FloatWidth) : LayoutData :=
  if fw then ⟨8, 3⟩ else ⟨4, 2⟩

/-- Spec-local IEEE `f32`/`f64` byte-validity predicate over `AllocByte` slices:
every initialized `(floatLayout fw).size`-byte bit pattern (`±0.0`, normalized,
subnormal, `±∞`, and quiet/signaling NaN payloads) is a valid Rust float bit
pattern, whereas any `.uninit` byte is invalid. This is a modeling assumption
(Rust's float types accept every bit pattern), so it is stated as a definition
rather than proved; `FloatFromBytesSound` and `FloatIntoBytesSound` relate it
to the `Trusted.MirSemantics` byte codec. -/
def FloatValidBytes (fw : FloatWidth) (bs : List AllocByte) : Prop :=
  AllInitBytes (floatLayout fw).size bs

/-- Spec-local `FromBytes` law for IEEE `f32`/`f64` over the
`Trusted.MirSemantics` byte codec: every initialized slice `bs` of
`(floatLayout fw).size` bytes is `FloatValidBytes fw`, and its
provenance-stripped bytes `raw` decode via `decodeUInt` in byte order `endian`
to a bit pattern below `2 ^ (8 * (floatLayout fw).size)` whose `encodeUInt`
re-encoding is `raw`. -/
def FloatFromBytesSound (fw : FloatWidth) : Prop :=
  ∀ (endian : TargetEndian) (bs : List AllocByte) (raw : List UInt8),
    bs.length = (floatLayout fw).size →
    initBytes? bs = some raw →
    FloatValidBytes fw bs ∧
    decodeUInt endian raw < Nat.pow 2 (8 * (floatLayout fw).size) ∧
    encodeUInt endian (floatLayout fw).size (decodeUInt endian raw) = raw

/-- Spec-local `IntoBytes` law for IEEE `f32`/`f64` over the
`Trusted.MirSemantics` byte codec: every bit pattern `bits` below
`2 ^ (8 * (floatLayout fw).size)` encodes via `encodeUInt` in byte order
`endian` to initialized, provenance-free bytes that satisfy `FloatValidBytes fw`
(so no `.uninit` padding) and that `decodeUInt` maps back to `bits`. -/
def FloatIntoBytesSound (fw : FloatWidth) : Prop :=
  ∀ (endian : TargetEndian) (bits : Nat),
    bits < Nat.pow 2 (8 * (floatLayout fw).size) →
    FloatValidBytes fw
      ((encodeUInt endian (floatLayout fw).size bits).map
        (fun b => AllocByte.init b none)) ∧
    decodeUInt endian (encodeUInt endian (floatLayout fw).size bits) = bits

/-- Representative IEEE 754 quiet NaN bit pattern (`0x7FC00000` for `f32`,
`0x7FF8000000000000` for `f64`). -/
def floatQuietNanBits (fw : FloatWidth) : Nat :=
  if fw then 0x7FF8000000000000 else 0x7FC00000

/-- Representative IEEE 754 signaling NaN bit pattern (`0x7F800001` for `f32`,
`0x7FF0000000000001` for `f64`). -/
def floatSignalingNanBits (fw : FloatWidth) : Nat :=
  if fw then 0x7FF0000000000001 else 0x7F800001

/-! ### Section 2B: Spec-Local RFC 3629 UTF-8 Byte Validity for `str` -/

/-- Inclusive byte-range check `lo ≤ b.toNat ≤ hi`. -/
def inByteRange (lo hi : Nat) (b : UInt8) : Bool :=
  Nat.ble lo b.toNat && Nat.ble b.toNat hi

/-- Control state codes (`0..8`) of the Unicode Standard Table 3-7 / RFC 3629 §4
well-formed UTF-8 byte DFA (`0` = ready, `1` = 1 continuation byte remaining,
`2` = after `0xE0`, `3` = 2 continuation bytes remaining, `4` = after `0xED`,
`5` = after `0xF0`, `6` = 3 continuation bytes remaining, `7` = after `0xF4`,
`8` = rejecting sink). -/
abbrev Utf8State : Type := Nat

/-- Exact 9-state (`0..7` plus the rejecting sink `8`) RFC 3629 §4 / Unicode
Table 3-7 single-byte transition:
- 1-byte: `0x00..0x7F`
- 2-byte: `0xC2..0xDF` followed by `0x80..0xBF`
- 3-byte: `0xE0` + `0xA0..0xBF` + `0x80..0xBF`;
  `0xE1..0xEC` or `0xEE..0xEF` + 2×`0x80..0xBF`;
  `0xED` + `0x80..0x9F` + `0x80..0xBF` (rejecting `U+D800..U+DFFF` surrogates)
- 4-byte: `0xF0` + `0x90..0xBF` + 2×`0x80..0xBF`;
  `0xF1..0xF3` + 3×`0x80..0xBF`;
  `0xF4` + `0x80..0x8F` + 2×`0x80..0xBF` (rejecting `> U+10FFFF`). -/
def utf8Step (st : Utf8State) (b : UInt8) : Utf8State :=
  if Nat.beq st 0 then
    if Nat.ble b.toNat 0x7F then 0
    else if inByteRange 0xC2 0xDF b then 1
    else if Nat.beq b.toNat 0xE0 then 2
    else if inByteRange 0xE1 0xEC b || inByteRange 0xEE 0xEF b then 3
    else if Nat.beq b.toNat 0xED then 4
    else if Nat.beq b.toNat 0xF0 then 5
    else if inByteRange 0xF1 0xF3 b then 6
    else if Nat.beq b.toNat 0xF4 then 7
    else 8
  else if Nat.beq st 1 then
    if inByteRange 0x80 0xBF b then 0 else 8
  else if Nat.beq st 2 then
    if inByteRange 0xA0 0xBF b then 1 else 8
  else if Nat.beq st 3 then
    if inByteRange 0x80 0xBF b then 1 else 8
  else if Nat.beq st 4 then
    if inByteRange 0x80 0x9F b then 1 else 8
  else if Nat.beq st 5 then
    if inByteRange 0x90 0xBF b then 3 else 8
  else if Nat.beq st 6 then
    if inByteRange 0x80 0xBF b then 3 else 8
  else if Nat.beq st 7 then
    if inByteRange 0x80 0x8F b then 3 else 8
  else
    8

/-- Executable RFC 3629 UTF-8 byte-sequence validity predicate. -/
def IsValidUtf8Bytes (raw : List UInt8) : Bool :=
  Nat.beq (raw.foldl utf8Step 0) 0

/-- Exact 4-width / 8-production RFC 3629 §4 ABNF head-scalar decomposition
(`UTF8-octets`), proved equivalent to `IsValidUtf8Bytes` in
`FloatStrAtomicBitValiditySpec`. -/
def ValidUtf8StepDecomp (raw : List UInt8) : Prop :=
  raw = [] ∨
  (∃ (b₀ : UInt8) (rest : List UInt8),
    raw = b₀ :: rest ∧
    Nat.ble b₀.toNat 0x7F = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₀ b₁ : UInt8) (rest : List UInt8),
    raw = b₀ :: b₁ :: rest ∧
    inByteRange 0xC2 0xDF b₀ = true ∧
    inByteRange 0x80 0xBF b₁ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₁ b₂ : UInt8) (rest : List UInt8),
    raw = 0xE0 :: b₁ :: b₂ :: rest ∧
    inByteRange 0xA0 0xBF b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₀ b₁ b₂ : UInt8) (rest : List UInt8),
    raw = b₀ :: b₁ :: b₂ :: rest ∧
    (inByteRange 0xE1 0xEC b₀ || inByteRange 0xEE 0xEF b₀) = true ∧
    inByteRange 0x80 0xBF b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₁ b₂ : UInt8) (rest : List UInt8),
    raw = 0xED :: b₁ :: b₂ :: rest ∧
    inByteRange 0x80 0x9F b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₁ b₂ b₃ : UInt8) (rest : List UInt8),
    raw = 0xF0 :: b₁ :: b₂ :: b₃ :: rest ∧
    inByteRange 0x90 0xBF b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    inByteRange 0x80 0xBF b₃ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₀ b₁ b₂ b₃ : UInt8) (rest : List UInt8),
    raw = b₀ :: b₁ :: b₂ :: b₃ :: rest ∧
    inByteRange 0xF1 0xF3 b₀ = true ∧
    inByteRange 0x80 0xBF b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    inByteRange 0x80 0xBF b₃ = true ∧
    IsValidUtf8Bytes rest = true) ∨
  (∃ (b₁ b₂ b₃ : UInt8) (rest : List UInt8),
    raw = 0xF4 :: b₁ :: b₂ :: b₃ :: rest ∧
    inByteRange 0x80 0x8F b₁ = true ∧
    inByteRange 0x80 0xBF b₂ = true ∧
    inByteRange 0x80 0xBF b₃ = true ∧
    IsValidUtf8Bytes rest = true)

/-- Spec-local `AllocByte` slice validity for `str`: every byte in `bs` is
initialized (`initBytes? bs = some raw`) and `raw` is well-formed UTF-8. -/
def IsValidUtf8AllocBytes (bs : List AllocByte) : Prop :=
  ∃ raw : List UInt8, initBytes? bs = some raw ∧ IsValidUtf8Bytes raw = true

/-- Spec-local `FromZeros` soundness for `str`: for every byte length `n`,
`zeroAllocBytes n` decodes as `n` valid NUL (`0x00`) ASCII bytes. -/
def StrFromZerosSound : Prop :=
  ∀ n : Nat, IsValidUtf8AllocBytes (zeroAllocBytes n)

/-- Spec-local `IntoBytes` law for `str`, inherited from its `[u8]`
representation: `encodeVal` encodes every `u8` byte `b` to exactly the single
initialized, provenance-free byte `b` (so no `.uninit` padding); re-encoding a
well-formed UTF-8 byte string `raw` byte by byte therefore yields
`raw.map (fun b => AllocByte.init b none)`, which again satisfies
`IsValidUtf8AllocBytes`; and `u8` has 1-byte alignment in
`Trusted.MirSemantics`. -/
def StrIntoBytesSound : Prop :=
  (∀ (endian : TargetEndian) (b : UInt8),
    encodeVal endian (.int .i8 false)
        (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩) =
      .ok [AllocByte.init b none]) ∧
  (∀ raw : List UInt8,
    IsValidUtf8Bytes raw = true →
    IsValidUtf8AllocBytes (raw.map (fun b => AllocByte.init b none))) ∧
  IsUnaligned (.int .i8 false)

/-! ### Section 2C: `Atomic*` Backing Scalars & `UnsafeCell` Classification -/

/-- Spec-local tag indexing the scalar `Atomic*` representations in
`core::sync::atomic` (`none` = `AtomicBool`, `some (w, signed)` =
`Atomic{U,I}*`). -/
abbrev AtomicKind : Type := Option (IntWidth × Bool)

/-- `AtomicBool` selector. -/
def atomicBoolKind : AtomicKind := none

/-- `Atomic{U,I}*` selector for `(w, signed)`. -/
def atomicIntKind (w : IntWidth) (signed : Bool) : AtomicKind :=
  some (w, signed)

/-- Spec-local assumed correspondence mapping `AtomicKind` to the primitive
`Trusted.MirAst.MirTy` (`.bool` or `.int w s`) with the same size and bit
validity, as `core::sync::atomic` documents for every atomic type
(`impls.rs:494-626`; `impls` covers `8`/`16`/`32`/`64`/`isize` on `x86_64`,
excluding `.i128`). The standard library does not promise matching alignment
for the wider atomics, so this correspondence carries only byte-validity
facts (`IsFromZeros`, `IsFromBytes`, `IsIntoBytes`, `BoolTryFromBytesSound`)
and the backing size, never alignment. -/
def atomicBackingMirTy (ak : AtomicKind) : MirTy :=
  match ak with
  | none => .bool
  | some pair => .int pair.1 pair.2

/-- Rust's layout law for a sized type with layout `l`: the size is a multiple
of the alignment `2 ^ l.alignLog2` (Rust Reference, "Size and Alignment": "The
size of a value is always a multiple of its alignment"). The `alignLog2`
encoding already makes the alignment at least 1. -/
def SizeMultipleOfAlign (l : LayoutData) : Prop :=
  Nat.mod l.size (Nat.pow 2 l.alignLog2) = 0

/-- Closed 8-element Spec-local classification of surface wrapper families
(`0..4` = `UnsafeCell`-free families `primitiveScalar`, `ieeeFloat`, `strSlice`,
`nonZeroInt`, `optionNonZeroInt`; `5..7` = `UnsafeCell`-bearing families
`unsafeCell`, `atomicBool`, `atomicInt`). -/
abbrev SurfaceWrapperKind : Type := Fin 8

/-- Plain scalar surface wrapper (`()`, `bool`, `char`, `u8`..`isize`). -/
def wrapperPrimitiveScalar : SurfaceWrapperKind :=
  ⟨0, Nat.zero_lt_succ 7⟩

/-- IEEE floating-point surface wrapper (`f32`, `f64`). -/
def wrapperIeeeFloat : SurfaceWrapperKind :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 6)⟩

/-- UTF-8 string-slice surface wrapper (`str`). -/
def wrapperStrSlice : SurfaceWrapperKind :=
  ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 5))⟩

/-- `core::num::NonZero<T>` surface wrapper. -/
def wrapperNonZeroInt : SurfaceWrapperKind :=
  ⟨3, Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 4)))⟩

/-- `Option<core::num::NonZero<T>>` surface wrapper. -/
def wrapperOptionNonZeroInt : SurfaceWrapperKind :=
  ⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 3))))⟩

/-- `core::cell::UnsafeCell<T>` surface wrapper. -/
def wrapperUnsafeCell : SurfaceWrapperKind :=
  ⟨5, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2)))))⟩

/-- `core::sync::atomic::AtomicBool` surface wrapper. -/
def wrapperAtomicBool : SurfaceWrapperKind :=
  ⟨6, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))))⟩

/-- `core::sync::atomic::Atomic<T>` integer surface wrapper. -/
def wrapperAtomicInt : SurfaceWrapperKind :=
  ⟨7, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))))))⟩

/-- Spec-local interior-mutability predicate: `true` iff the wrapper family
contains `core::cell::UnsafeCell` (`wrapperUnsafeCell`, `wrapperAtomicBool`,
`wrapperAtomicInt`). -/
def ContainsUnsafeCell (k : SurfaceWrapperKind) : Bool :=
  Nat.ble 5 k.val

/-- Spec-local `zerocopy::Immutable` soundness condition: a surface wrapper
family is sound for `Immutable` iff it contains no `UnsafeCell`. -/
def ImmutableSound (k : SurfaceWrapperKind) : Prop :=
  ContainsUnsafeCell k = false

/-! ### Combined Model-Side Specification -/

/-- Complete model-side byte-validity, UTF-8, backing-scalar (`Atomic*`),
alignment, and `UnsafeCell` classification specification. -/
def FloatStrAtomicBitValiditySpec : Prop :=
  -- 0. `Trusted.MirAst.MirTy.unsupported` fail-closed boundary
  layoutOfTy .unsupported = none ∧
  (∀ (endian : TargetEndian) (bs : List AllocByte),
    decodeVal endian .unsupported bs = .error .unsupported) ∧
  -- 1. Spec-local IEEE `f32` and `f64` byte-validity definitions and alignment
  (floatLayout floatF32).size = 4 ∧
  (floatLayout floatF64).size = 8 ∧
  (∀ fw : FloatWidth,
    FloatValidBytes fw (zeroAllocBytes (floatLayout fw).size) ∧
    FloatFromBytesSound fw ∧
    (∀ endian : TargetEndian,
      FloatValidBytes fw
        ((encodeUInt endian (floatLayout fw).size
          (floatQuietNanBits fw)).map (fun b => AllocByte.init b none)) ∧
      FloatValidBytes fw
        ((encodeUInt endian (floatLayout fw).size
          (floatSignalingNanBits fw)).map (fun b => AllocByte.init b none))) ∧
    FloatIntoBytesSound fw ∧
    -- Non-vacuity witnesses: both NaN bit patterns satisfy the
    -- `FloatIntoBytesSound` bound
    floatQuietNanBits fw < Nat.pow 2 (8 * (floatLayout fw).size) ∧
    floatSignalingNanBits fw < Nat.pow 2 (8 * (floatLayout fw).size) ∧
    (∀ bs : List AllocByte, AllocByte.uninit ∈ bs → ¬ FloatValidBytes fw bs) ∧
    0 < (floatLayout fw).alignLog2) ∧
  -- 2. Spec-local RFC 3629 UTF-8 `str` validity, `FromZeros`, `IntoBytes`, and
  --    negative `FromBytes` model refutations
  (∀ raw : List UInt8,
    IsValidUtf8Bytes raw = true ↔ ValidUtf8StepDecomp raw) ∧
  (∀ raw₁ raw₂ : List UInt8,
    IsValidUtf8Bytes raw₁ = true →
    IsValidUtf8Bytes raw₂ = true →
    IsValidUtf8Bytes (raw₁ ++ raw₂) = true) ∧
  StrFromZerosSound ∧
  StrIntoBytesSound ∧
  -- Positive 1-, 2-, 3-, and 4-byte UTF-8 boundary witnesses
  IsValidUtf8Bytes [] = true ∧
  IsValidUtf8Bytes [0x00] = true ∧
  IsValidUtf8Bytes [0x41] = true ∧
  IsValidUtf8Bytes [0x7F] = true ∧
  IsValidUtf8Bytes [0xC2, 0x80] = true ∧
  IsValidUtf8Bytes [0xDF, 0xBF] = true ∧
  IsValidUtf8Bytes [0xE0, 0xA0, 0x80] = true ∧
  IsValidUtf8Bytes [0xE2, 0x82, 0xAC] = true ∧
  IsValidUtf8Bytes [0xED, 0x9F, 0xBF] = true ∧
  IsValidUtf8Bytes [0xEE, 0x80, 0x80] = true ∧
  IsValidUtf8Bytes [0xF0, 0x90, 0x80, 0x80] = true ∧
  IsValidUtf8Bytes [0xF1, 0x80, 0x80, 0x80] = true ∧
  IsValidUtf8Bytes [0xF4, 0x8F, 0xBF, 0xBF] = true ∧
  -- Negative UTF-8 `FromBytes` model refutations (`0xFF`, lone continuation,
  -- overlong NUL `0xC0 0x80`, UTF-16 surrogates `U+D800`/`U+DFFF`, overlong
  -- 3/4-byte, `> U+10FFFF`, truncated, and every positive slice length `n + 1`)
  IsValidUtf8Bytes [0xFF] = false ∧
  IsValidUtf8Bytes [0x80] = false ∧
  IsValidUtf8Bytes [0xC0, 0x80] = false ∧
  IsValidUtf8Bytes [0xC1, 0xBF] = false ∧
  IsValidUtf8Bytes [0xE0, 0x9F, 0xBF] = false ∧
  IsValidUtf8Bytes [0xED, 0xA0, 0x80] = false ∧
  IsValidUtf8Bytes [0xED, 0xBF, 0xBF] = false ∧
  IsValidUtf8Bytes [0xF0, 0x8F, 0xBF, 0xBF] = false ∧
  IsValidUtf8Bytes [0xF4, 0x90, 0x80, 0x80] = false ∧
  IsValidUtf8Bytes [0xE2, 0x82] = false ∧
  (∀ n : Nat,
    AllInitBytes (n + 1) (List.replicate (n + 1) (AllocByte.init 0xFF none)) ∧
    ¬ IsValidUtf8AllocBytes
        (List.replicate (n + 1) (AllocByte.init 0xFF none))) ∧
  -- 3. `Trusted.MirSemantics` bit validity for `Atomic*` backing scalar types
  --    (`atomicBackingMirTy`, Spec-local same-size/bit-validity correspondence)
  (∀ endian : TargetEndian,
    IsFromZeros endian (atomicBackingMirTy atomicBoolKind) ∧
    IsIntoBytes endian (atomicBackingMirTy atomicBoolKind) ∧
    BoolTryFromBytesSound endian ∧
    (decodeVal endian (atomicBackingMirTy atomicBoolKind) [.init 0x02 none] =
        .error .undefined ∧
      ¬ IsFromBytes endian (atomicBackingMirTy atomicBoolKind)) ∧
    (∀ (w : IntWidth) (s : Bool),
      IsFromZeros endian (atomicBackingMirTy (atomicIntKind w s)) ∧
      IsFromBytes endian (atomicBackingMirTy (atomicIntKind w s)) ∧
      IsIntoBytes endian (atomicBackingMirTy (atomicIntKind w s)))) ∧
  -- 3b. `Unaligned` for `AtomicBool`, `AtomicU8`, and `AtomicI8`
  --     (`impls.rs:468-492`): the backing scalar is 1 byte, and any 1-byte
  --     layout whose size is a multiple of its alignment has alignment 1
  --     (`⟨1, 0⟩` witnesses that the hypotheses are satisfiable)
  layoutOfTy (atomicBackingMirTy atomicBoolKind) = some ⟨1, 0⟩ ∧
  (∀ s : Bool,
    layoutOfTy (atomicBackingMirTy (atomicIntKind .i8 s)) = some ⟨1, 0⟩) ∧
  (∀ l : LayoutData, l.size = 1 → SizeMultipleOfAlign l → l.alignLog2 = 0) ∧
  SizeMultipleOfAlign ⟨1, 0⟩ ∧
  -- 3c. Contrast on the primitives themselves (not the atomics): `.int w s`
  --     for `w ≠ .i8` has alignment above 1, so neither it nor the
  --     same-size atomic gets `Unaligned` from the argument above
  (∀ (w : IntWidth) (s : Bool), w ≠ .i8 →
    (∃ layout, layoutOfTy (.int w s) = some layout ∧ 0 < layout.alignLog2) ∧
    ¬ IsUnaligned (.int w s)) ∧
  -- 4. Spec-local `UnsafeCell` interior-mutability `Immutable` exclusion
  ImmutableSound wrapperPrimitiveScalar ∧
  ImmutableSound wrapperIeeeFloat ∧
  ImmutableSound wrapperStrSlice ∧
  ImmutableSound wrapperNonZeroInt ∧
  ImmutableSound wrapperOptionNonZeroInt ∧
  ¬ ImmutableSound wrapperUnsafeCell ∧
  ¬ ImmutableSound wrapperAtomicBool ∧
  ¬ ImmutableSound wrapperAtomicInt

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, fun program =>
    CapturedFloatStrAtomicMatrixSpec program ∧ FloatStrAtomicBitValiditySpec⟩

end Spec
