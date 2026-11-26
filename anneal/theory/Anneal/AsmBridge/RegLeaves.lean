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
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.SimpLemmas

public section

namespace Anneal.AsmBridge.RegLeaves

/-!
# Orthogonal Register Leaf Lenses & Instruction-Scoped Writes (`RegLeaves`)

Zero-TCB (`0` `noncomputable`, `0` `._unsafe_rec`, axioms `⊆ {propext}`, all
leaf-lens theorems `[]` axioms) architectural register leaf algebra for
`core::arch::asm!`:

1. **Byte-granular orthogonal leaf carriers:**
   - `Gp64Leaves` (4 leaves: `b0_8`, `b8_16`, `b16_32`, `b32_64` covering
     `AL`, `AH`, `AX`, `EAX`/`W_i`, `RAX`/`X_i`).
   - `Vec256Leaves` (7 leaves: `b0_8`, `b8_16`, `b16_32`, `b32_64`, `b64_128`,
     `ymm_b128_192`, `ymm_b192_256` covering `B`/`H`/`S`/`D`/`Q`/`XMM`/`YMM`).
   - `Zmm512Leaves` (11 leaves: `lo256` 7 leaves plus 4 upper 64-bit leaves
     `zmm_b256_320`, `zmm_b320_384`, `zmm_b384_448`, `zmm_b448_512`).
2. **Total 3-law lenses (`RegLeafLens`, `ValidRegLeafLens`,
   `DisjointRegLeafLenses`):** Proves `get_put`, `put_get`, `put_put`, and
   exhaustive pairwise `get_put_disjoint` across all 4 GP leaves, all 7
   `Vec256Leaves` leaves, and all 11 `Zmm512Leaves` leaves with zero axioms.
3. **Why unary whole-register lenses fail (`putLowZeroHi_refutes_getPut`):**
   Zero-extending 32-bit writes (`mov eax, ...` / `mov w0, ...`) violate
   `PutGet` over a unary 64-bit register carrier.
4. **Instruction-scoped SIMD/vector writes (`SimdEncoding`,
   `Sub128WriteMode`, `AsmWriteWidth`):** Models `.legacySsePreserveUpper`,
   `.vexZeroUpper`, `.evexZeroUpper512`, and `.aarch64ZeroUpper`, plus
   `.zeroExtendTo128` (`movd`/`vmovd`) vs `.mergeLowLane`
   (`movss`/`vmovss`/`pinsrb`/`vpinsrw`), proving
   `sse_preserves_while_vex_zeros_ymm_hi`, `evex_w256_zeros_zmm_hi256`,
   `x86_movd_zeros_32_to_128`, `movd_vs_vmovss_sub128_asymmetry`, and
   `aapcs64_d8_callee_save_sound_yet_inline_asm_ub`.
-/

/-- 64-bit general-purpose register partitioned into 4 orthogonal byte/word
leaves (`8 + 8 + 16 + 32 = 64` bits). -/
structure Gp64Leaves where
  b0_8   : UInt8
  b8_16  : UInt8
  b16_32 : UInt16
  b32_64 : UInt32

/-- Structural equality on `Gp64Leaves`. -/
@[expose] def Gp64Leaves.beq (x y : Gp64Leaves) : Bool :=
  Nat.beq x.b0_8.toNat y.b0_8.toNat &&
  Nat.beq x.b8_16.toNat y.b8_16.toNat &&
  Nat.beq x.b16_32.toNat y.b16_32.toNat &&
  Nat.beq x.b32_64.toNat y.b32_64.toNat

/-- 256-bit SIMD/vector register partitioned into 7 orthogonal architectural
leaves (`8 + 8 + 16 + 32 + 64 + 64 + 64 = 256` bits). -/
structure Vec256Leaves where
  b0_8         : UInt8
  b8_16        : UInt8
  b16_32       : UInt16
  b32_64       : UInt32
  b64_128      : UInt64
  ymm_b128_192 : UInt64
  ymm_b192_256 : UInt64

/-- All-zero 256-bit vector register. -/
@[expose] def Vec256Leaves.zero : Vec256Leaves :=
  ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Structural equality on `Vec256Leaves`. -/
@[expose] def Vec256Leaves.beq (x y : Vec256Leaves) : Bool :=
  Nat.beq x.b0_8.toNat y.b0_8.toNat &&
  Nat.beq x.b8_16.toNat y.b8_16.toNat &&
  Nat.beq x.b16_32.toNat y.b16_32.toNat &&
  Nat.beq x.b32_64.toNat y.b32_64.toNat &&
  Nat.beq x.b64_128.toNat y.b64_128.toNat &&
  Nat.beq x.ymm_b128_192.toNat y.ymm_b128_192.toNat &&
  Nat.beq x.ymm_b192_256.toNat y.ymm_b192_256.toNat

/-- Upper 256 bits (`[511:256]`) of an AVX-512 `ZMM` register partitioned into
4 orthogonal 64-bit leaves. -/
structure ZmmHi256 where
  zmm_b256_320 : UInt64
  zmm_b320_384 : UInt64
  zmm_b384_448 : UInt64
  zmm_b448_512 : UInt64

/-- All-zero upper 256 bits of a `ZMM` register. -/
@[expose] def ZmmHi256.zero : ZmmHi256 :=
  ⟨0, 0, 0, 0⟩

/-- Structural equality on `ZmmHi256`. -/
@[expose] def ZmmHi256.beq (x y : ZmmHi256) : Bool :=
  Nat.beq x.zmm_b256_320.toNat y.zmm_b256_320.toNat &&
  Nat.beq x.zmm_b320_384.toNat y.zmm_b320_384.toNat &&
  Nat.beq x.zmm_b384_448.toNat y.zmm_b384_448.toNat &&
  Nat.beq x.zmm_b448_512.toNat y.zmm_b448_512.toNat

/-- 512-bit AVX-512 `ZMM` register partitioned into 11 orthogonal leaves
(`lo256` 7 leaves + `hi256` 4 upper 64-bit leaves). -/
structure Zmm512Leaves where
  lo256 : Vec256Leaves
  hi256 : ZmmHi256

/-- Structural equality on `Zmm512Leaves`. -/
@[expose] def Zmm512Leaves.beq (x y : Zmm512Leaves) : Bool :=
  Vec256Leaves.beq x.lo256 y.lo256 && ZmmHi256.beq x.hi256 y.hi256

/-! ## Total 3-Law Register Leaf Lenses -/

/-- Total functional lens focusing on a single register leaf of type `A` inside
register state `S`. -/
structure RegLeafLens (S A : Type) where
  get : S → A
  put : S → A → S

/-- The three lawful lens axioms (`get_put`, `put_get`, `put_put`). -/
structure ValidRegLeafLens {S A : Type} (L : RegLeafLens S A) : Prop where
  get_put : ∀ (s : S) (a : A), L.get (L.put s a) = a
  put_get : ∀ (s : S), L.put s (L.get s) = s
  put_put : ∀ (s : S) (a1 a2 : A), L.put (L.put s a1) a2 = L.put s a2

/-- Pairwise lens orthogonality: writing through `L1` preserves `L2.get`, and
writing through `L2` preserves `L1.get` (`get_put_disjoint`). -/
structure DisjointRegLeafLenses {S A B : Type}
    (L1 : RegLeafLens S A) (L2 : RegLeafLens S B) : Prop where
  get2_put1 : ∀ (s : S) (a : A), L2.get (L1.put s a) = L2.get s
  get1_put2 : ∀ (s : S) (b : B), L1.get (L2.put s b) = L1.get s

/-- Leaf identifiers for `Gp64Leaves`. -/
inductive GpLeafId where
  | b0_8
  | b8_16
  | b16_32
  | b32_64

/-- Value type of each `GpLeafId`. -/
@[expose] def GpLeafTy : GpLeafId → Type
  | .b0_8 => UInt8
  | .b8_16 => UInt8
  | .b16_32 => UInt16
  | .b32_64 => UInt32

/-- Total lens for each leaf of `Gp64Leaves`. -/
@[expose] def gpLeafLens (id : GpLeafId) :
    RegLeafLens Gp64Leaves (GpLeafTy id) :=
  match id with
  | .b0_8 => ⟨Gp64Leaves.b0_8, fun r v => { r with b0_8 := v }⟩
  | .b8_16 => ⟨Gp64Leaves.b8_16, fun r v => { r with b8_16 := v }⟩
  | .b16_32 => ⟨Gp64Leaves.b16_32, fun r v => { r with b16_32 := v }⟩
  | .b32_64 => ⟨Gp64Leaves.b32_64, fun r v => { r with b32_64 := v }⟩

/-- Every `Gp64Leaves` leaf lens satisfies all three lens laws (`[]` axioms). -/
theorem gpLeafLens_valid (id : GpLeafId) :
    ValidRegLeafLens (gpLeafLens id) := by
  cases id with
  | b0_8 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b8_16 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b16_32 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b32_64 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Any two distinct `Gp64Leaves` leaf lenses are pairwise disjoint
(`get_put_disjoint`, `[]` axioms). -/
theorem gpLeafLens_get_put_disjoint (i j : GpLeafId) (hne : i ≠ j) :
    DisjointRegLeafLenses (gpLeafLens i) (gpLeafLens j) := by
  cases i <;> cases j <;>
    first
    | exact False.elim (hne rfl)
    | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Leaf identifiers for `Vec256Leaves`. -/
inductive VecLeafId where
  | b0_8
  | b8_16
  | b16_32
  | b32_64
  | b64_128
  | ymm_b128_192
  | ymm_b192_256

/-- Value type of each `VecLeafId`. -/
@[expose] def VecLeafTy : VecLeafId → Type
  | .b0_8 => UInt8
  | .b8_16 => UInt8
  | .b16_32 => UInt16
  | .b32_64 => UInt32
  | .b64_128 => UInt64
  | .ymm_b128_192 => UInt64
  | .ymm_b192_256 => UInt64

/-- Total lens for each leaf of `Vec256Leaves`. -/
@[expose] def vecLeafLens (id : VecLeafId) :
    RegLeafLens Vec256Leaves (VecLeafTy id) :=
  match id with
  | .b0_8 => ⟨Vec256Leaves.b0_8, fun r v => { r with b0_8 := v }⟩
  | .b8_16 => ⟨Vec256Leaves.b8_16, fun r v => { r with b8_16 := v }⟩
  | .b16_32 => ⟨Vec256Leaves.b16_32, fun r v => { r with b16_32 := v }⟩
  | .b32_64 => ⟨Vec256Leaves.b32_64, fun r v => { r with b32_64 := v }⟩
  | .b64_128 => ⟨Vec256Leaves.b64_128, fun r v => { r with b64_128 := v }⟩
  | .ymm_b128_192 =>
    ⟨Vec256Leaves.ymm_b128_192, fun r v => { r with ymm_b128_192 := v }⟩
  | .ymm_b192_256 =>
    ⟨Vec256Leaves.ymm_b192_256, fun r v => { r with ymm_b192_256 := v }⟩

/-- Every `Vec256Leaves` leaf lens satisfies all three lens laws (`[]` axioms).
-/
theorem vecLeafLens_valid (id : VecLeafId) :
    ValidRegLeafLens (vecLeafLens id) := by
  cases id with
  | b0_8 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b8_16 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b16_32 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b32_64 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | b64_128 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | ymm_b128_192 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | ymm_b192_256 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Any two distinct `Vec256Leaves` leaf lenses are pairwise disjoint
(`get_put_disjoint`, `[]` axioms). -/
theorem vecLeafLens_get_put_disjoint (i j : VecLeafId) (hne : i ≠ j) :
    DisjointRegLeafLenses (vecLeafLens i) (vecLeafLens j) := by
  cases i <;> cases j <;>
    first
    | exact False.elim (hne rfl)
    | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Full 11-leaf identifiers for `Zmm512Leaves` (`lo256` 7 leaves plus 4 upper
64-bit `ZMM` leaves `[511:256]`). -/
inductive ZmmLeafId where
  | lo (id : VecLeafId)
  | zmm_b256_320
  | zmm_b320_384
  | zmm_b384_448
  | zmm_b448_512

/-- Value type of each `ZmmLeafId`. -/
@[expose] def ZmmLeafTy : ZmmLeafId → Type
  | .lo id => VecLeafTy id
  | .zmm_b256_320 => UInt64
  | .zmm_b320_384 => UInt64
  | .zmm_b384_448 => UInt64
  | .zmm_b448_512 => UInt64

/-- Total lens for each of the 11 orthogonal leaves of `Zmm512Leaves`. -/
@[expose] def zmmLeafLens (id : ZmmLeafId) :
    RegLeafLens Zmm512Leaves (ZmmLeafTy id) :=
  match id with
  | .lo vid =>
    ⟨fun z => (vecLeafLens vid).get z.lo256,
     fun z v => { z with lo256 := (vecLeafLens vid).put z.lo256 v }⟩
  | .zmm_b256_320 =>
    ⟨fun z => z.hi256.zmm_b256_320,
     fun z v => { z with hi256 := { z.hi256 with zmm_b256_320 := v } }⟩
  | .zmm_b320_384 =>
    ⟨fun z => z.hi256.zmm_b320_384,
     fun z v => { z with hi256 := { z.hi256 with zmm_b320_384 := v } }⟩
  | .zmm_b384_448 =>
    ⟨fun z => z.hi256.zmm_b384_448,
     fun z v => { z with hi256 := { z.hi256 with zmm_b384_448 := v } }⟩
  | .zmm_b448_512 =>
    ⟨fun z => z.hi256.zmm_b448_512,
     fun z v => { z with hi256 := { z.hi256 with zmm_b448_512 := v } }⟩

/-- Every `Zmm512Leaves` leaf lens (all 11 leaves) satisfies all three lens
laws (`[]` axioms). -/
theorem zmmLeafLens_valid (id : ZmmLeafId) :
    ValidRegLeafLens (zmmLeafLens id) := by
  cases id with
  | lo vid =>
    have hV := vecLeafLens_valid vid
    refine ⟨fun z a => hV.get_put z.lo256 a, ?_, ?_⟩
    · intro z
      dsimp only [zmmLeafLens]
      rw [hV.put_get z.lo256]
    · intro z a1 a2
      dsimp only [zmmLeafLens]
      rw [hV.put_put z.lo256 a1 a2]
  | zmm_b256_320 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | zmm_b320_384 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | zmm_b384_448 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | zmm_b448_512 => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Any two distinct `Zmm512Leaves` leaf lenses across all 11 leaves are
pairwise disjoint (`get_put_disjoint`, `[]` axioms). -/
theorem zmmLeafLens_get_put_disjoint (i j : ZmmLeafId) (hne : i ≠ j) :
    DisjointRegLeafLenses (zmmLeafLens i) (zmmLeafLens j) := by
  cases i with
  | lo vi =>
    cases j with
    | lo vj =>
      have hNeLo : vi ≠ vj := fun h => hne (congrArg ZmmLeafId.lo h)
      have hD := vecLeafLens_get_put_disjoint vi vj hNeLo
      exact ⟨fun z a => hD.get2_put1 z.lo256 a,
             fun z b => hD.get1_put2 z.lo256 b⟩
    | zmm_b256_320 => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    | zmm_b320_384 => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    | zmm_b384_448 => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    | zmm_b448_512 => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | zmm_b256_320 =>
    cases j <;>
      first
      | exact False.elim (hne rfl)
      | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | zmm_b320_384 =>
    cases j <;>
      first
      | exact False.elim (hne rfl)
      | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | zmm_b384_448 =>
    cases j <;>
      first
      | exact False.elim (hne rfl)
      | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | zmm_b448_512 =>
    cases j <;>
      first
      | exact False.elim (hne rfl)
      | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Why Unary Whole-Register Lenses Fail Under Zero-Extending Writes -/

/-- Read the low 32 bits (`EAX`/`W_i`) from `Gp64Leaves`. -/
@[expose] def getLow32 (r : Gp64Leaves) : UInt8 × UInt8 × UInt16 :=
  (r.b0_8, r.b8_16, r.b16_32)

/-- Architectural zero-extending 32-bit write (`mov eax, ...` / `mov w0, ...`):
writes the low 32 bits and zeros `b32_64`. -/
@[expose] def putLowZeroHi (_r : Gp64Leaves)
    (lo32 : UInt8 × UInt8 × UInt16) : Gp64Leaves :=
  { b0_8 := lo32.1, b8_16 := lo32.2.1, b16_32 := lo32.2.2, b32_64 := 0 }

/-- Refutation of unary `PutGet` (`putLowZeroHi` is NOT a lawful lens): writing
back the observed low 32 bits clobbers a non-zero upper 32-bit half `b32_64`
(`[]` axioms). -/
theorem putLowZeroHi_refutes_getPut :
    ¬ (∀ r : Gp64Leaves, putLowZeroHi r (getLow32 r) = r) := by
  intro h
  have hInst := h ⟨1, 2, 3, 42⟩
  have hHi : (0 : UInt32).toNat = (42 : UInt32).toNat :=
    congrArg (fun g => g.b32_64.toNat) hInst
  nomatch hHi

/-! ## Instruction-Scoped SIMD/Vector Writes (`SimdEncoding`, `Sub128WriteMode`,
`AsmWriteWidth`) -/

/-- Instruction encoding governing upper-lane preservation vs zeroing above
bit `128` (and bit `256` on AVX-512). -/
inductive SimdEncoding where
  | legacySsePreserveUpper
  | vexZeroUpper
  | evexZeroUpper512
  | aarch64ZeroUpper

/-- Sub-128-bit lane-write policy distinguishing zero-extending scalar loads
(`movd`/`vmovd`/`movq`/`vmovq`/AArch64 `ldr b/h/s/d`) from low-lane merging
instructions (reg-reg `movss`/`movsd`/`vmovss`/`vmovsd`/`pinsrb`/`vpinsrw`). -/
inductive Sub128WriteMode where
  | zeroExtendTo128
  | mergeLowLane

/-- Architectural operand write width for instruction-scoped register updates.
-/
inductive AsmWriteWidth where
  | w8
  | w16
  | w32
  | w64
  | w128
  | w256
  | w512

/-- Update the low 128-bit lane from `src`, merging preserved `[127:width]` bits
from `mergeSrc` under `.mergeLowLane` (low-lane `index = 0` inserts only;
higher-lane `pinsr*`/`vpinsr*` inserts target their orthogonal leaf via
`vecLeafLens`/`zmmLeafLens`), while leaving `[255:128]` untouched for the outer
encoding layer. -/
@[expose] def writeLow128Lane (mode : Sub128WriteMode) (width : AsmWriteWidth)
    (mergeSrc src : Vec256Leaves) : Vec256Leaves :=
  match mode, width with
  | .zeroExtendTo128, .w8 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := 0, b16_32 := 0, b32_64 := 0, b64_128 := 0 }
  | .zeroExtendTo128, .w16 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := 0, b32_64 := 0,
      b64_128 := 0 }
  | .zeroExtendTo128, .w32 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := src.b16_32,
      b32_64 := 0, b64_128 := 0 }
  | .zeroExtendTo128, .w64 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := src.b16_32,
      b32_64 := src.b32_64, b64_128 := 0 }
  | .mergeLowLane, .w8 =>
    { mergeSrc with b0_8 := src.b0_8 }
  | .mergeLowLane, .w16 =>
    { mergeSrc with b0_8 := src.b0_8, b8_16 := src.b8_16 }
  | .mergeLowLane, .w32 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := src.b16_32 }
  | .mergeLowLane, .w64 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := src.b16_32,
      b32_64 := src.b32_64 }
  | _, .w128 =>
    { mergeSrc with
      b0_8 := src.b0_8, b8_16 := src.b8_16, b16_32 := src.b16_32,
      b32_64 := src.b32_64, b64_128 := src.b64_128 }
  | _, .w256 | _, .w512 => src

/-- Instruction-scoped 256-bit SIMD/vector register write parameterized by
`(SimdEncoding, Sub128WriteMode, AsmWriteWidth)`:
- `r` is the prior destination register value (supplying preserved `[255:128]`
  bits under `.legacySsePreserveUpper`).
- `mergeSrc` is the low-128 lane-merge source (equal to `r` for 2-operand
  legacy SSE `movss`/`movsd`, and equal to the VEX/EVEX `vvvv` `src1` operand
  for 3-operand `vmovss`/`vmovsd`/`vpinsr*`, supplying preserved `[127:width]`
  under `.mergeLowLane`). Only low-lane (`index = 0`) inserts are modeled here;
  higher-lane inserts use `vecLeafLens`/`zmmLeafLens`.
- `src` supplies the written `[width-1:0]` bits.
- Encoding layer on `[255:128]`: `.legacySsePreserveUpper` preserves `r`'s
  `[255:128]`, while `.vexZeroUpper`, `.evexZeroUpper512`, and
  `.aarch64ZeroUpper` zero `[255:128]` for widths `<= 128`. -/
@[expose] def writeVecInsnMode (enc : SimdEncoding) (mode : Sub128WriteMode)
    (width : AsmWriteWidth) (r mergeSrc src : Vec256Leaves) : Vec256Leaves :=
  match width with
  | .w256 | .w512 => src
  | _ =>
    let loUpdated := writeLow128Lane mode width mergeSrc src
    match enc with
    | .legacySsePreserveUpper =>
      { loUpdated with
        ymm_b128_192 := r.ymm_b128_192
        ymm_b192_256 := r.ymm_b192_256 }
    | .vexZeroUpper | .evexZeroUpper512 | .aarch64ZeroUpper =>
      { loUpdated with ymm_b128_192 := 0, ymm_b192_256 := 0 }

/-- Default zero-extending instruction-scoped 256-bit SIMD/vector register
write (`writeVecInsnMode enc .zeroExtendTo128 width r r src`). -/
@[expose] def writeVecInsn (enc : SimdEncoding) (width : AsmWriteWidth)
    (r src : Vec256Leaves) : Vec256Leaves :=
  writeVecInsnMode enc .zeroExtendTo128 width r r src

/-- Instruction-scoped 512-bit `ZMM` register write parameterized by
`(SimdEncoding, Sub128WriteMode, AsmWriteWidth)`, with `r` as prior destination
and `mergeSrc` as the `vvvv` low-128 merge source. -/
@[expose] def writeZmmInsnMode (enc : SimdEncoding) (mode : Sub128WriteMode)
    (width : AsmWriteWidth) (r mergeSrc src : Zmm512Leaves) : Zmm512Leaves :=
  let lo' := writeVecInsnMode enc mode width r.lo256 mergeSrc.lo256 src.lo256
  match enc, width with
  | .legacySsePreserveUpper, .w512 => ⟨lo', src.hi256⟩
  | .legacySsePreserveUpper, _ => ⟨lo', r.hi256⟩
  | .vexZeroUpper, .w512 => ⟨lo', src.hi256⟩
  | .vexZeroUpper, _ => ⟨lo', ZmmHi256.zero⟩
  | .evexZeroUpper512, .w512 => ⟨lo', src.hi256⟩
  | .evexZeroUpper512, _ => ⟨lo', ZmmHi256.zero⟩
  | .aarch64ZeroUpper, .w512 => ⟨lo', src.hi256⟩
  | .aarch64ZeroUpper, _ => ⟨lo', ZmmHi256.zero⟩

/-- Default zero-extending instruction-scoped 512-bit `ZMM` register write. -/
@[expose] def writeZmmInsn (enc : SimdEncoding) (width : AsmWriteWidth)
    (r src : Zmm512Leaves) : Zmm512Leaves :=
  writeZmmInsnMode enc .zeroExtendTo128 width r r src

/-- Legacy SSE 128-bit `XMM` write preserves upper `[255:128]` leaves, whereas
VEX 128-bit `XMM` write zeros `ymm_b128_192` and `ymm_b192_256` (`[]` axioms).
-/
theorem sse_preserves_while_vex_zeros_ymm_hi :
    let init : Vec256Leaves := ⟨1, 2, 3, 4, 5, 888, 999⟩
    let payload : Vec256Leaves := ⟨10, 20, 30, 40, 50, 0, 0⟩
    let s := writeVecInsn .legacySsePreserveUpper .w128 init payload
    let v := writeVecInsn .vexZeroUpper .w128 init payload
    s.b0_8 = 10 ∧ s.b64_128 = 50 ∧
    s.ymm_b128_192 = 888 ∧ s.ymm_b192_256 = 999 ∧
    v.b0_8 = 10 ∧ v.b64_128 = 50 ∧
    v.ymm_b128_192 = 0 ∧ v.ymm_b192_256 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- EVEX 256-bit write writes `[255:0]` and zeros all four upper `[511:256]`
leaves (`hi256`), EVEX 128-bit write zeros `[511:128]`, and legacy SSE 128-bit
write preserves both `[255:128]` and `[511:256]` (`[propext]`). -/
theorem evex_w256_zeros_zmm_hi256 :
    let init : Zmm512Leaves :=
      ⟨⟨1, 2, 3, 4, 5, 888, 999⟩, ⟨101, 202, 303, 404⟩⟩
    let payload : Zmm512Leaves :=
      ⟨⟨10, 20, 30, 40, 50, 60, 70⟩, ⟨555, 666, 777, 888⟩⟩
    let e256 := writeZmmInsn .evexZeroUpper512 .w256 init payload
    let e128 := writeZmmInsn .evexZeroUpper512 .w128 init payload
    let e512 := writeZmmInsn .evexZeroUpper512 .w512 init payload
    let s128 := writeZmmInsn .legacySsePreserveUpper .w128 init payload
    e256.lo256.ymm_b128_192 = 60 ∧ e256.lo256.ymm_b192_256 = 70 ∧
    e256.hi256 = ZmmHi256.zero ∧
    e128.lo256.ymm_b128_192 = 0 ∧ e128.lo256.ymm_b192_256 = 0 ∧
    e128.hi256 = ZmmHi256.zero ∧
    e512.hi256.zmm_b448_512 = 888 ∧
    s128.lo256.ymm_b128_192 = 888 ∧ s128.hi256.zmm_b256_320 = 101 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- x86 `movd xmm, r32` zeros `[127:32]` (`b32_64` and `b64_128`) while legacy
SSE preserves `[255:128]`, whereas VEX `vmovd` additionally zeros `[255:128]`
(`[]` axioms). -/
theorem x86_movd_zeros_32_to_128 :
    let init : Vec256Leaves := ⟨1, 2, 3, 444, 555, 888, 999⟩
    let payload : Vec256Leaves := ⟨7, 8, 9, 111, 222, 333, 444⟩
    let movd := writeVecInsn .legacySsePreserveUpper .w32 init payload
    let vmovd := writeVecInsn .vexZeroUpper .w32 init payload
    movd.b0_8 = 7 ∧ movd.b16_32 = 9 ∧
    movd.b32_64 = 0 ∧ movd.b64_128 = 0 ∧
    movd.ymm_b128_192 = 888 ∧ movd.ymm_b192_256 = 999 ∧
    vmovd.b32_64 = 0 ∧ vmovd.b64_128 = 0 ∧
    vmovd.ymm_b128_192 = 0 ∧ vmovd.ymm_b192_256 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Sub-128-bit zero-extend vs 2-op/3-op merge-low-lane asymmetry:
- `movd` (`.zeroExtendTo128`) zeros `[127:32]` while preserving `r`'s
  `[255:128]`.
- 2-operand reg-reg `movss` (`.legacySsePreserveUpper, .mergeLowLane`,
  `mergeSrc := r`) preserves `r`'s `[127:32]` and `[255:128]`.
- 3-operand reg-reg `vmovss dst, vvvv, src` (`.vexZeroUpper, .mergeLowLane`,
  `mergeSrc := vvvv`) merges `[127:32]` from `vvvv` (not old `r`) and zeros
  `[255:128]`.
- EVEX 3-operand `vmovss` merges `[127:32]` from `vvvv` and zeros `[511:128]`
  (`[propext]`). -/
theorem movd_vs_vmovss_sub128_asymmetry :
    let init : Vec256Leaves := ⟨1, 2, 3, 444, 555, 888, 999⟩
    let vvvv : Vec256Leaves := ⟨11, 22, 33, 600, 700, 777, 666⟩
    let payload : Vec256Leaves := ⟨7, 8, 9, 111, 222, 333, 444⟩
    let movd := writeVecInsnMode .legacySsePreserveUpper .zeroExtendTo128
      .w32 init init payload
    let movss := writeVecInsnMode .legacySsePreserveUpper .mergeLowLane
      .w32 init init payload
    let vmovss := writeVecInsnMode .vexZeroUpper .mergeLowLane
      .w32 init vvvv payload
    let vpinsrb := writeVecInsnMode .vexZeroUpper .mergeLowLane
      .w8 init vvvv payload
    let zInit : Zmm512Leaves := ⟨init, ⟨10, 20, 30, 40⟩⟩
    let zVvvv : Zmm512Leaves := ⟨vvvv, ⟨15, 25, 35, 45⟩⟩
    let zPay : Zmm512Leaves := ⟨payload, ⟨50, 60, 70, 80⟩⟩
    let evexMovss := writeZmmInsnMode .evexZeroUpper512 .mergeLowLane
      .w32 zInit zVvvv zPay
    movd.b32_64 = 0 ∧ movd.b64_128 = 0 ∧ movd.ymm_b128_192 = 888 ∧
    movss.b0_8 = 7 ∧ movss.b32_64 = 444 ∧ movss.b64_128 = 555 ∧
    movss.ymm_b128_192 = 888 ∧
    vmovss.b0_8 = 7 ∧ vmovss.b32_64 = 600 ∧ vmovss.b64_128 = 700 ∧
    vmovss.ymm_b128_192 = 0 ∧ vmovss.ymm_b192_256 = 0 ∧
    vpinsrb.b0_8 = 7 ∧ vpinsrb.b8_16 = 22 ∧ vpinsrb.ymm_b128_192 = 0 ∧
    evexMovss.lo256.b32_64 = 600 ∧ evexMovss.lo256.ymm_b128_192 = 0 ∧
    evexMovss.hi256 = ZmmHi256.zero :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl⟩

/-- AAPCS64 callee-save check on `D8..D15`: only the low 64 bits (`[63:0]`)
must be preserved across a C call boundary. -/
@[expose] def aapcs64D8CalleeSavedOk (pre post : Vec256Leaves) : Bool :=
  Nat.beq post.b0_8.toNat pre.b0_8.toNat &&
  Nat.beq post.b8_16.toNat pre.b8_16.toNat &&
  Nat.beq post.b16_32.toNat pre.b16_32.toNat &&
  Nat.beq post.b32_64.toNat pre.b32_64.toNat

/-- AAPCS64 `D8` callee-save vs Rust `inline_asm` `V8` asymmetry:
- Restoring `D8` via a 64-bit `ldr d8` preserves `[63:0]` (sound across a C
  call: `aapcs64D8CalleeSavedOk = true`), yet zeros `[127:64]` (`b64_128`), so
  full `V8` equality fails (`Vec256Leaves.beq = false`): touching `D8` inside
  `asm!` without declaring `v8` as an operand/clobber is UB.
- Touching `B8` (`ldr b8`, 8-bit zero-extending) clobbers `[63:8]` as well,
  breaking even AAPCS64 `D8` callee-save (`[]` axioms). -/
theorem aapcs64_d8_callee_save_sound_yet_inline_asm_ub :
    let pre : Vec256Leaves := ⟨1, 2, 3, 4, 99, 0, 0⟩
    let postD := writeVecInsn .aarch64ZeroUpper .w64 ⟨0, 0, 0, 0, 777, 0, 0⟩ pre
    let postB := writeVecInsn .aarch64ZeroUpper .w8 pre pre
    aapcs64D8CalleeSavedOk pre postD = true ∧
    Vec256Leaves.beq postD pre = false ∧
    aapcs64D8CalleeSavedOk pre postB = false :=
  ⟨rfl, rfl, rfl⟩

end Anneal.AsmBridge.RegLeaves

end
