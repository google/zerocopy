-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-!
# `KnownLayout` Sealing Markers & Model-Side `DstLayout` / `TrailingSliceLayout`

Formal specification for 41 selected concrete non-generic `KnownLayout` trait
sealing markers (`zerocopy/src/lib.rs` and `zerocopy/src/impls.rs`) and a
model-side 64-bit `DstLayout` / `TrailingSliceLayout` / `RoundingAlignAndPhase`
mathematical specification mirroring `zerocopy/src/layout.rs:58-560`,
`layout.rs:4030-4067`, and `zerocopy/src/util/mod.rs:156-255`:

1. **Selected MIR sealing markers (`CapturedKnownLayoutMatrixSpec`):** Binds the
   41 selected concrete `only_derive_is_allowed_to_implement_this_trait` bodies
   compiled under this unit's `cfg` (`29` primitive and `NonZero<*>` types in
   `lib.rs:1221-1227`, `1` `str` in `lib.rs:1267-1270`, and `11` concrete
   `Atomic*` types in `impls.rs:405,463`, excluding generic `impls` such as
   `AtomicPtr<T>`, `LAYOUT` constants, `raw_from_ptr_len`/
   `pointer_to_metadata`, and feature-gated `f16`/`f128`/`simd` items) by exact
   count, canonical `b.identity` path, `b.isUnsafe = false`,
   `b.argumentCount = 0`, total `()` return (`ReturnsTotal`), and
   memory-preserving execution over every `MemoryState`.
2. **Model-side `DstLayout` / `TrailingSliceLayout` / `RoundingAlignAndPhase`
   contracts (`DstLayoutSpec`):** Rust MIR bodies in `layout.rs` and
   `util/mod.rs` are not yet captured because `Struct`, `Enum`, `NonZeroUsize`,
   and `TerminatorKind::Call` remain outside `Trusted.MirAst` Profile v1. Part
   2 pairs `M_anneal`'s 64-bit pointer-size fact
   (`layoutOfTy (.int .isize false) = some ⟨8, 3⟩` and
   `IntWidth.isize.bitWidth = 64`) with explicit `Spec`-local `BitVec 64` and
   `Nat` models (using structural `@Nat.rec` bitwise operators `bitwiseNatRec`
   and `leadingZerosAux` to stay strictly within `["propext"]`-only axioms)
   proving:
   - power-of-two bit-hack equivalence (`0 < x ∧ (x & (x - 1)) = 0`), bit-packed
     `RoundingAlignAndPhase` (`(align | phase) = align + phase`, non-zero
     invariant, `leadingZeros64` highest-set-bit recovery, XOR recovery, `new`/
     `components` round-trip, arbitrary non-zero `components()`/`align()` Kani
     postconditions, and `TrailingSliceLayout::size_offset` OR/ADD equivalence);
   - `util::padding_needed_for` and
     `util::round_down_to_next_multiple_of_alignment`
     Kani postconditions and exact `BitVec 64` equivalence between
     `padding_for_elems`'s modular optimization and its naive contract (plus
     element-count invariance when `align ∣ elem_size`);
   - `TrailingSliceLayout::max_trailing_bytes` agreement with Kani's
     specification, disjoint OR/ADD packing (`aligned_bytes | initial_padding`),
     and exact iff optimality against mathematical `objectSizeNat tb`; and
   - `TrailingSliceLayout::size_for_elems` iff representability / exact value
     and `size_for_elems_unchecked` overflow-freedom under its `# Safety`
     preconditions.
-/

/-- Canonical `rust-path-v1` identities of 41 selected concrete `KnownLayout`
sealing markers in `zerocopy/src/impls.rs:405,463`, `lib.rs:1221-1227`, and
`lib.rs:1267-1270` (canonical SCC shard order). -/
def knownLayoutMarkerIdentities : List String := [
  "rust-path-v1::_::<impl KnownLayout for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for char>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<i128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<u128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for core::num::nonzero::NonZero<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for f32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for f64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for str>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::_::<impl KnownLayout for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl KnownLayout for core::sync::atomic::Atomic<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_16::_::<impl KnownLayout for core::sync::atomic::Atomic<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl KnownLayout for core::sync::atomic::Atomic<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_32::_::<impl KnownLayout for core::sync::atomic::Atomic<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl KnownLayout for core::sync::atomic::Atomic<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_64::_::<impl KnownLayout for core::sync::atomic::Atomic<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl KnownLayout for core::sync::atomic::Atomic<bool>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl KnownLayout for core::sync::atomic::Atomic<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_8::_::<impl KnownLayout for core::sync::atomic::Atomic<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl KnownLayout for core::sync::atomic::Atomic<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::atomics::atomic_ptr::_::<impl KnownLayout for core::sync::atomic::Atomic<usize>>::only_derive_is_allowed_to_implement_this_trait"
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

/-- Non-vacuous identity-keyed safety precondition over the 41 selected
zero-argument `KnownLayout` sealing markers. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity ∈ knownLayoutMarkerIdentities ∧ args = []

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

/-- MIR contract over the 41 selected `KnownLayout` trait sealing markers:
exact body count matching `knownLayoutMarkerIdentities` and indexed
`UnitMarkerAt` agreement at every `defId`. -/
def CapturedKnownLayoutMatrixSpec (program : Program) : Prop :=
  program.bodies.length = knownLayoutMarkerIdentities.length ∧
  ∀ (defId : DefId) (identity : String),
    Trusted.MirSemantics.getElem? knownLayoutMarkerIdentities defId =
      some identity →
    UnitMarkerAt program defId identity

/-! ## Part 2: Model-Side 64-Bit `DstLayout` and `TrailingSliceLayout` -/

/-- `usize` width in bits (`64`) matching `IntWidth.isize.bitWidth`. -/
def usizeBits : Nat := 64

/-- `usize::MAX` (`2^64 - 1`) on 64-bit targets. -/
def usizeMaxNat : Nat := 2 ^ usizeBits - 1

/-- `BitVec 64` representation of `usize::MAX`. -/
def usizeMax64 : BitVec 64 := BitVec.ofNat 64 usizeMaxNat

/-- Bitwise fold over `w` bits defined by total `@Nat.rec` recursion (avoiding
`Nat.bitwise.eq_def` and `Quot.sound` while matching `Nat.bitwise` across low
`w` bits). -/
def bitwiseNatRec (f : Bool → Bool → Bool) (w a b : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun _ _ => 0)
    (fun _ ih x y =>
      2 * ih (x / 2) (y / 2) +
        if f (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1)
        then 1 else 0)
    w a b

/-- `i`-th bit of `a : Nat` (`true` iff bit `i` is `1`). -/
def nthBit (a i : Nat) : Bool :=
  Nat.beq ((a / 2 ^ i) % 2) 1

/-- Spec-local 64-bit bitwise AND (`x & y`). -/
def bv64And (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (bitwiseNatRec and 64 x.toNat y.toNat)

/-- Spec-local 64-bit bitwise OR (`x | y`). -/
def bv64Or (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (bitwiseNatRec or 64 x.toNat y.toNat)

/-- Spec-local 64-bit bitwise XOR (`x ^ y`). -/
def bv64Xor (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (bitwiseNatRec bne 64 x.toNat y.toNat)

/-- Spec-local 64-bit bitwise NOT (`!x`). -/
def bv64Not (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (bitwiseNatRec (fun a _ => !a) 64 x.toNat 0)

/-- Spec-local 64-bit left shift (`x << k`). -/
def bv64Shl (x : BitVec 64) (k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (Nat.shiftLeft x.toNat k)

/-- Spec-local 64-bit wrapping multiplication (`x.wrapping_mul(y)`). -/
def bv64Mul (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat)

/-- Leading-zero scan over low `w` bits via total `@Nat.rec` recursion. -/
def leadingZerosAux (n w : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => if nthBit n k then 0 else 1 + ih)
    w

/-- Number of leading zero bits in a 64-bit `usize` (`leading_zeros()`). -/
def leadingZeros64 (x : BitVec 64) : Nat :=
  leadingZerosAux x.toNat usizeBits

/-- Index of the highest set bit of a non-zero 64-bit `usize`
(`(POINTER_WIDTH_BITS - 1) - x.leading_zeros()` in `layout.rs:119`). -/
def highestSetBit64 (x : BitVec 64) : Nat :=
  63 - leadingZeros64 x

/-- Bit-hack power-of-two predicate (`0 < x ∧ (x & (x - 1)) = 0`). -/
def isPowerOfTwo64 (x : BitVec 64) : Prop :=
  0 < x.toNat ∧ bv64And x (x - BitVec.ofNat 64 1) = BitVec.ofNat 64 0

/-- Checked 64-bit unsigned addition (`a.checked_add(b)`). -/
def checkedAdd64 (a b : BitVec 64) : Option (BitVec 64) :=
  if Nat.ble (a.toNat + b.toNat) usizeMaxNat then
    some (a + b)
  else
    none

/-- Checked 64-bit unsigned subtraction (`a.checked_sub(b)`). -/
def checkedSub64 (a b : BitVec 64) : Option (BitVec 64) :=
  if Nat.ble b.toNat a.toNat then
    some (a - b)
  else
    none

/-- Checked 64-bit unsigned multiplication (`a.checked_mul(b)`). -/
def checkedMul64 (a b : BitVec 64) : Option (BitVec 64) :=
  if Nat.ble (a.toNat * b.toNat) usizeMaxNat then
    some (bv64Mul a b)
  else
    none

/-- Model-side `RoundingAlignAndPhase::new` (`align | phase` at `layout.rs:91`).
-/
def roundingNew64 (align phase : BitVec 64) : BitVec 64 :=
  bv64Or align phase

/-- Model-side `RoundingAlignAndPhase::components` (`layout.rs:104-129`). -/
def roundingComponents64 (encoded : BitVec 64) : BitVec 64 × BitVec 64 :=
  let shift := highestSetBit64 encoded
  let align := bv64Shl (BitVec.ofNat 64 1) shift
  let phase := bv64Xor encoded align
  (align, phase)

/-- Model-side `RoundingAlignAndPhase::align` (`layout.rs:138-147`). -/
def roundingAlign64 (encoded : BitVec 64) : BitVec 64 :=
  (roundingComponents64 encoded).1

/-- Model-side `util::padding_needed_for(len, align)`
(`!(len.wrapping_sub(1)) & (align - 1)` in
`zerocopy/src/util/mod.rs:156-216`). -/
def paddingNeededFor64 (len align : BitVec 64) : BitVec 64 :=
  let mask := align - BitVec.ofNat 64 1
  bv64And (bv64Not (len - BitVec.ofNat 64 1)) mask

/-- Model-side `util::round_down_to_next_multiple_of_alignment(n, align)`
(`n & !(align - 1)` in `zerocopy/src/util/mod.rs:237-255`). -/
def roundDown64 (n align : BitVec 64) : BitVec 64 :=
  let mask := bv64Not (align - BitVec.ofNat 64 1)
  bv64And n mask

/-- Model-side `TrailingSliceLayout::size_offset` (`round_down(size_base, align)
| phase` in `layout.rs:221-234`). -/
def sizeOffset64 (sizeBase align phase : BitVec 64) : BitVec 64 :=
  bv64Or (roundDown64 sizeBase align) phase

/-- Model-side naive `padding_for_elems` contract formula (`layout.rs:352-358`).
-/
def paddingForElemsNaive (sizeBase offset elemSize align phase elems :
    BitVec 64) : BitVec 64 :=
  let trailingBytes := bv64Mul elems elemSize
  let mask := align - BitVec.ofNat 64 1
  let rounded := bv64And ((phase + trailingBytes) + mask) (bv64Not mask)
  let objectSize := sizeBase + rounded
  objectSize - (offset + trailingBytes)

/-- Model-side optimized `TrailingSliceLayout::padding_for_elems` formula
(`layout.rs:360-415`). -/
def paddingForElemsFast (sizeBase offset elemSize align phase elems :
    BitVec 64) : BitVec 64 :=
  let sizeMask := align - BitVec.ofNat 64 1
  let elemRemainder := bv64And elemSize sizeMask
  let trailingRemainder := bv64And (bv64Mul elems elemRemainder) sizeMask
  let roundingInput := phase + trailingRemainder
  let roundingPadding := paddingNeededFor64 roundingInput align
  ((sizeBase + phase) - offset) + roundingPadding

/-- Mathematical `round_up(x, a)` over `ℕ` for `a > 0`. -/
def roundUpNat (x a : Nat) : Nat :=
  if x % a = 0 then x else x + (a - x % a)

/-- Mathematical DST object size formula (`layout.rs:193, 271-273`). -/
def objectSizeNat (sizeBase align phase tb : Nat) : Nat :=
  sizeBase + roundUpNat (phase + tb) align

/-- Model-side `TrailingSliceLayout::max_trailing_bytes` implementation
(`layout.rs:252-341`). -/
def maxTrailingBytesImpl64 (sizeBase align phase available : BitVec 64) :
    Option (BitVec 64) :=
  let roundedPhase :=
    if phase == BitVec.ofNat 64 0 then BitVec.ofNat 64 0 else align
  match checkedAdd64 sizeBase roundedPhase with
  | none => none
  | some minimumSize =>
    match checkedSub64 available minimumSize with
    | none => none
    | some extraBytes =>
      let alignedBytes := roundDown64 extraBytes align
      let initialPadding := roundedPhase - phase
      some (bv64Or alignedBytes initialPadding)

/-- Model-side `proofs::max_trailing_bytes` Kani contract
(`layout.rs:246-251, 4060-4067`). -/
def maxTrailingBytesKaniSpec64 (sizeBase align phase available : BitVec 64) :
    Option (BitVec 64) :=
  match checkedSub64 available sizeBase with
  | none => none
  | some bytes => checkedSub64 (roundDown64 bytes align) phase

/-- Model-side `proofs::slice_dst_size_for_trailing_bytes`
(`layout.rs:4030-4040`). -/
def sliceDstSizeForTrailingBytes64 (sizeBase align phase trailingSize :
    BitVec 64) : Option (BitVec 64) :=
  match checkedAdd64 phase trailingSize with
  | none => none
  | some withoutPadding =>
    let padding := paddingNeededFor64 withoutPadding align
    match checkedAdd64 withoutPadding padding with
    | none => none
    | some rounded => checkedAdd64 sizeBase rounded

/-- Model-side `TrailingSliceLayout::size_for_elems` Kani contract
(`layout.rs:423-426`). -/
def sizeForElemsKaniSpec64 (sizeBase elemSize align phase elems : BitVec 64) :
    Option (BitVec 64) :=
  match checkedMul64 elems elemSize with
  | none => none
  | some bytes => sliceDstSizeForTrailingBytes64 sizeBase align phase bytes

/-- Model-side `TrailingSliceLayout::size_for_elems` implementation
(`layout.rs:427-491`). -/
def sizeForElemsImpl64
    (sizeBase offset elemSize align phase elems : BitVec 64) :
    Option (BitVec 64) :=
  match maxTrailingBytesImpl64 sizeBase align phase usizeMax64 with
  | none => none
  | some maxTrailingBytes =>
    match checkedMul64 elemSize elems with
    | none => none
    | some trailingSize =>
      if maxTrailingBytes.toNat < trailingSize.toNat then
        none
      else
        let trailingEnd := offset + trailingSize
        some (trailingEnd +
          paddingForElemsFast sizeBase offset elemSize align phase elems)

/-- Complete model-side 64-bit `DstLayout` / `TrailingSliceLayout` /
`RoundingAlignAndPhase` specification, grounded in `M_anneal`'s 64-bit
`isize`/`usize` layout. -/
def DstLayoutSpec : Prop :=
  -- 0. Ground 64-bit pointer width in `Trusted.MirSemantics` + differential
  --    concrete boundary checks against `Nat.land`, `Nat.lor`, and `Nat.xor`
  (usizeBits = IntWidth.isize.bitWidth ∧
    layoutOfTy (.int .isize false) = some ⟨8, 3⟩) ∧
  (bv64And (BitVec.ofNat 64 0xF0F0F0F012345678)
      (BitVec.ofNat 64 0x0FF00FF0FEDCBA98) =
    BitVec.ofNat 64 (Nat.land 0xF0F0F0F012345678 0x0FF00FF0FEDCBA98) ∧
   bv64Or (BitVec.ofNat 64 0x8000000000000000)
      (BitVec.ofNat 64 0x7FFFFFFFFFFFFFFF) =
    BitVec.ofNat 64 (Nat.lor 0x8000000000000000 0x7FFFFFFFFFFFFFFF) ∧
   bv64Xor (BitVec.ofNat 64 0x123456789ABCDEF0)
      (BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF) =
    BitVec.ofNat 64 (Nat.xor 0x123456789ABCDEF0 0xFFFFFFFFFFFFFFFF)) ∧
  -- 1. Bit-packed `RoundingAlignAndPhase` & `size_offset` (`layout.rs:58-234`)
  (∀ align : BitVec 64,
    isPowerOfTwo64 align ↔
      ∃ k : Nat, k < 64 ∧ align = BitVec.ofNat 64 (2 ^ k)) ∧
  (∀ (k : Nat) (phase : BitVec 64), k < 64 →
    let align := bv64Shl (BitVec.ofNat 64 1) k
    phase.toNat < align.toNat →
    let encoded := roundingNew64 align phase
    isPowerOfTwo64 align ∧
    align.toNat = 2 ^ k ∧
    encoded = align + phase ∧
    encoded.toNat = align.toNat + phase.toNat ∧
    0 < encoded.toNat ∧
    highestSetBit64 encoded = k ∧
    bv64Shl (BitVec.ofNat 64 1) (highestSetBit64 encoded) = align ∧
    bv64Xor encoded align = phase ∧
    roundingComponents64 encoded = (align, phase) ∧
    roundingAlign64 encoded = align) ∧
  (∀ encoded : BitVec 64, 0 < encoded.toNat →
    let (align, phase) := roundingComponents64 encoded
    isPowerOfTwo64 align ∧
    phase.toNat < align.toNat ∧
    checkedAdd64 align phase = some encoded ∧
    bv64Or align phase = encoded ∧
    align.toNat ≤ encoded.toNat ∧
    encoded.toNat - align.toNat < align.toNat) ∧
  (∀ (sizeBase align phase : BitVec 64),
    isPowerOfTwo64 align → phase.toNat < align.toNat →
    let alignedBase := roundDown64 sizeBase align
    sizeOffset64 sizeBase align phase = alignedBase + phase ∧
    (sizeOffset64 sizeBase align phase).toNat =
      alignedBase.toNat + phase.toNat) ∧
  -- 2. `padding_needed_for`, `round_down`, & `padding_for_elems` equivalence
  (∀ (len align : BitVec 64), isPowerOfTwo64 align →
    (paddingNeededFor64 len align).toNat =
      (if len.toNat % align.toNat = 0 then 0
        else align.toNat - len.toNat % align.toNat) ∧
    (len + paddingNeededFor64 len align).toNat % align.toNat = 0 ∧
    (paddingNeededFor64 len align).toNat < align.toNat) ∧
  (∀ (n align : BitVec 64), isPowerOfTwo64 align →
    (roundDown64 n align).toNat = (n.toNat / align.toNat) * align.toNat ∧
    (roundDown64 n align).toNat ≤ n.toNat ∧
    (roundDown64 n align).toNat % align.toNat = 0 ∧
    n.toNat < (roundDown64 n align).toNat + align.toNat) ∧
  (∀ (sizeBase offset elemSize align phase elems : BitVec 64),
    isPowerOfTwo64 align → phase.toNat < align.toNat →
    paddingForElemsFast sizeBase offset elemSize align phase elems =
      paddingForElemsNaive sizeBase offset elemSize align phase elems ∧
    (elemSize.toNat % align.toNat = 0 →
      paddingForElemsFast sizeBase offset elemSize align phase elems =
        paddingForElemsFast sizeBase offset elemSize align phase
          (BitVec.ofNat 64 0))) ∧
  -- 3. `max_trailing_bytes` iff optimality & disjoint OR/ADD packing
  (∀ (sizeBase align phase available : BitVec 64),
    isPowerOfTwo64 align → phase.toNat < align.toNat →
    maxTrailingBytesImpl64 sizeBase align phase available =
      maxTrailingBytesKaniSpec64 sizeBase align phase available ∧
    ((∃ m, maxTrailingBytesImpl64 sizeBase align phase available = some m) ↔
      objectSizeNat sizeBase.toNat align.toNat phase.toNat 0 ≤
        available.toNat) ∧
    (∀ m : BitVec 64,
      maxTrailingBytesImpl64 sizeBase align phase available = some m →
      (let rp := if phase == BitVec.ofNat 64 0 then BitVec.ofNat 64 0 else align
       let eb := available - (sizeBase + rp)
       let ab := roundDown64 eb align
       let ip := rp - phase
       bv64Or ab ip = ab + ip ∧ ab.toNat + ip.toNat = m.toNat) ∧
      (∀ tb : Nat,
        objectSizeNat sizeBase.toNat align.toNat phase.toNat tb ≤
          available.toNat ↔
          tb ≤ m.toNat))) ∧
  -- 4. `size_for_elems` & `size_for_elems_unchecked` (`layout.rs:423-546`)
  (∀ (sizeBase offset elemSize align phase elems : BitVec 64),
    isPowerOfTwo64 align → phase.toNat < align.toNat →
    sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
      sizeForElemsKaniSpec64 sizeBase elemSize align phase elems ∧
    ((∃ s, sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
        some s) ↔
      (elems.toNat * elemSize.toNat ≤ usizeMaxNat ∧
       objectSizeNat sizeBase.toNat align.toNat phase.toNat
         (elems.toNat * elemSize.toNat) ≤ usizeMaxNat)) ∧
    (∀ s : BitVec 64,
      sizeForElemsImpl64 sizeBase offset elemSize align phase elems = some s →
      s.toNat = objectSizeNat sizeBase.toNat align.toNat phase.toNat
        (elems.toNat * elemSize.toNat)) ∧
    (∀ (trailingSize trailingEnd s : BitVec 64),
      checkedMul64 elems elemSize = some trailingSize →
      checkedAdd64 offset trailingSize = some trailingEnd →
      sizeForElemsImpl64 sizeBase offset elemSize align phase elems = some s →
      trailingEnd ≤ s →
      let pad := paddingForElemsFast sizeBase offset elemSize align phase elems
      elems.toNat * elemSize.toNat = trailingSize.toNat ∧
      trailingSize.toNat ≤ usizeMaxNat ∧
      offset.toNat + trailingSize.toNat = trailingEnd.toNat ∧
      trailingEnd.toNat ≤ usizeMaxNat ∧
      trailingEnd.toNat + pad.toNat = s.toNat ∧
      trailingEnd + pad = s))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, fun program =>
    CapturedKnownLayoutMatrixSpec program ∧ DstLayoutSpec⟩

end Spec
