/- Copyright 2026 The Fuchsia Authors
 -
 - Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
 - <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
 - license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
 - This file may not be copied, modified, or distributed except according to
 - those terms.
 -/

/-!
# Round 2 Track 1 Probe: `PassMode::Cast` Byte-Masked Register Packing & `ScalarPair` Sub-Word Niche Lowering

This standalone Lean 4.34.1 file mechanizes the core semantic models and
refinement obligations for Track 1 Round 2:

1. **Layer 1A Refinement Infrastructure (`Trusted.*`):**
   Exact replicas of Anneal's trusted preorder, partial-program, language, and
   `Trusted.Compiles` / `Trusted.Compiler.Verified` definitions.

2. **`MaskedWord` and `PassMode::Cast` Byte-Masked Register Packing:**
   Models 64-bit register words carrying a per-bit initialization mask
   (`MaskedWord`), packs and unpacks a padded 8-byte struct (`PaddedStruct`,
   matching `#[repr(C)] struct Padded { a: u8, /* 3 bytes pad */ b: u32 }`),
   and proves that field values round-trip bit-for-bit across `PassMode::Cast`
   regardless of uninitialized padding bits (`unpack_pack_padded_exact`).

3. **`freezeMaskedWord` Target Lowering Refinement vs. Whole-Word Poison:**
   Defines per-bit `freezeMaskedWord` at the `PassMode::Cast` lowering boundary,
   proves that freezing into a hardware `BitVec 64` register refines the
   byte-accurate `PassMode::Cast` semantics (`passModeCast_freeze_compiles`,
   `passModeCast_freeze_verified`), and proves a negative canary demonstrating
   that a naive whole-word `i64` load without per-byte `freeze` is unsound on
   padded structs (`canary_whole_word_poison_on_padding_unsound`).

4. **`BackendRepr::ScalarPair` Projection and Sub-Word Niche Extraction:**
   Models two-register `ScalarPairVal` values (`fst`, `snd`), contrasts
   byte-offset field dispatch (`rustc_codegen_ssa`) with `FieldIdx` dispatch on
   enums whose niche resides in `snd`, and proves universal round-trip
   correctness for sub-word niche discriminant encoding and decoding at
   arbitrary byte offsets (`Fin 8`) in either register
   (`scalarPair_decode_encode_niche_tagged`,
   `scalarPair_decode_encode_niche_untagged`).

5. **Pure-Rust Float Fallback Bit-Manipulation (`fabs` & `copysign`):**
   Mechanizes `core::intrinsics::fabs` and `core::intrinsics::copysignf64` bit
   manipulations (`SIGN_MASK`) and proves that they preserve all exponent and
   payload bits across finite, infinite, and NaN representations.
-/

namespace Trusted

/-- A `Preorder` is a reflexive, transitive relation `le`. -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

/-- A partial program paired with a semantic well-formedness proof. -/
structure Partial (Prog : Type u) (wf : Prog → Prop) where
  prog : Prog
  is_wf : wf prog

/-- A formal language parameterized by its program syntax, well-formedness
predicate, and behavioral preorder. -/
structure Language where
  Prog : Type u
  wf : Prog → Prop
  Beh : Type v
  [beh_preorder : Preorder Beh]
  eval : Partial Prog wf → Beh

attribute [instance] Language.beh_preorder

namespace Language

abbrev ProgWf (L : Language) : Type _ :=
  Partial L.Prog L.wf

end Language

/-- `Compiles L1 L2 compile p1 p2` asserts that `p1` and `p2` are well-formed,
`compile` maps `p1` to `some p2`, and `p2`'s behavior refines `p1`'s behavior. -/
def Compiles
    (L1 L2 : Language)
    (compile : L1.Prog → Option L2.Prog)
    (h_beh : L1.Beh = L2.Beh)
    (p1 : L1.Prog) (p2 : L2.Prog) : Prop :=
  ∃ (h1 : L1.wf p1) (h2 : L2.wf p2),
    compile p1 = some p2 ∧
    (cast h_beh (L1.eval ⟨p1, h1⟩)) ≥ (L2.eval ⟨p2, h2⟩)

namespace Compiler

/-- `Verified` packages `Compiles` at a canonical target witness. -/
def Verified
    (L1 L2 : Language)
    (compile : L1.Prog → Option L2.Prog)
    (h_beh : L1.Beh = L2.Beh)
    (p1 : L1.Prog) : Prop :=
  ∃ p2 : L2.Prog, Compiles L1 L2 compile h_beh p1 p2

end Compiler

end Trusted

namespace Round2Track1

/-!
## Section 1: `MaskedWord` & `PassMode::Cast` Byte-Masked Register Packing

When `rustc` lowers a small aggregate (`size <= 8` bytes under the Rust ABI via
`adjust_for_rust_abi`, or `size <= 16` bytes under System V `x86_64`, AAPCS64
`aarch64`, and LP64D `riscv64`) via `PassMode::Cast`, the aggregate is packed
into one or two 64-bit integer registers (`Reg::i64()`).

Because the aggregate may contain inter-field or trailing padding bytes (for
example, `#[repr(C)] struct Padded { a: u8, b: u32 }`, where bytes 1..3 are
uninitialized padding), `cast_to_maybe_noundef` omits `ArgAttribute::NoUndef`.
`MaskedWord` tracks both the 64-bit data payload (`bits`) and the per-bit
initialization mask (`initMask`, where `1` means initialized and `0` means
uninitialized).
-/

/-- A 64-bit word paired with a per-bit initialization mask (`1` = initialized,
`0` = uninitialized / padding). Isomorphic to an 8-byte slice of `AnMIR`
`AbstractByte` values (`Vellvm` `DTYPE_B 8`). -/
structure MaskedWord where
  bits : BitVec 64
  initMask : BitVec 64
  deriving DecidableEq, Repr

/-- Concrete representation of `#[repr(C)] struct Padded { a: u8, b: u32 }`.
In memory on a 64-bit little-endian target:
- Byte 0 (bits 0..7): `a : BitVec 8` (initialized)
- Bytes 1..3 (bits 8..31): 24 bits of inter-field alignment padding (uninitialized)
- Bytes 4..7 (bits 32..63): `b : BitVec 32` (initialized) -/
structure PaddedStruct where
  a : BitVec 8
  b : BitVec 32
  deriving DecidableEq, Repr

/-- The initialization mask for `PaddedStruct`: bits 0..7 (`a`) and bits 32..63
(`b`) are `1` (initialized), while bits 8..31 (padding) are `0`. -/
def paddedStructInitMask : BitVec 64 :=
  (BitVec.allOnes 8).zeroExtend 64 ||| ((BitVec.allOnes 32).zeroExtend 64 <<< 32)

theorem paddedStructInitMask_eq_hex :
    paddedStructInitMask = 0xFFFF_FFFF_0000_00FF#64 := rfl

/-- Packs `s : PaddedStruct` and arbitrary padding bits `padBits : BitVec 24`
into a 64-bit `MaskedWord` in little-endian byte order. -/
def packStructToMaskedWord (s : PaddedStruct) (padBits : BitVec 24) : MaskedWord :=
  let a64 : BitVec 64 := s.a.zeroExtend 64
  let pad64 : BitVec 64 := (padBits.zeroExtend 64) <<< 8
  let b64 : BitVec 64 := (s.b.zeroExtend 64) <<< 32
  { bits := a64 ||| pad64 ||| b64
  , initMask := paddedStructInitMask }

/-- Unpacks a `PaddedStruct` from a `MaskedWord`. Succeeds if and only if all
field bits required by `paddedStructInitMask` (bytes 0 and 4..7) are marked
initialized in `w.initMask`; uninitialized padding bits (bytes 1..3) are
ignored. -/
def unpackStructFromMaskedWord (w : MaskedWord) : Option PaddedStruct :=
  if (w.initMask &&& paddedStructInitMask) == paddedStructInitMask then
    some
      { a := w.bits.truncate 8
      , b := (w.bits >>> 32).truncate 32 }
  else
    none

theorem pack_bits_extract_a (s : PaddedStruct) (padBits : BitVec 24) :
    (packStructToMaskedWord s padBits).bits.truncate 8 = s.a := by
  ext i hi
  simp [packStructToMaskedWord]

theorem pack_bits_extract_b (s : PaddedStruct) (padBits : BitVec 24) :
    ((packStructToMaskedWord s padBits).bits >>> 32).truncate 32 = s.b := by
  ext i hi
  have ha_out : s.a.getLsbD (32 + i) = false :=
    BitVec.getLsbD_of_ge s.a (32 + i) (by omega)
  have hp_out : padBits.getLsbD (32 + i - 8) = false :=
    BitVec.getLsbD_of_ge padBits (32 + i - 8) (by omega)
  have h1 : decide (32 + i < 64) = true := decide_eq_true (by omega)
  have h2 : decide (32 + i < 32) = false := decide_eq_false (by omega)
  have h3 : decide (i < 64) = true := decide_eq_true (by omega)
  simp [packStructToMaskedWord, ha_out, hp_out, h1, h2, h3, hi]

theorem pack_initMask_satisfies_padded (s : PaddedStruct) (padBits : BitVec 24) :
    ((packStructToMaskedWord s padBits).initMask &&& paddedStructInitMask) ==
      paddedStructInitMask := by
  simp only [packStructToMaskedWord, paddedStructInitMask]
  rfl

/-- **Universal Round-Trip Theorem for `PassMode::Cast` Packing:**
Packing any `s : PaddedStruct` with any uninitialized padding bits
`padBits : BitVec 24` into a `MaskedWord` and unpacking it recovers `some s`
bit-for-bit. -/
theorem unpack_pack_padded_exact (s : PaddedStruct) (padBits : BitVec 24) :
    unpackStructFromMaskedWord (packStructToMaskedWord s padBits) = some s := by
  unfold unpackStructFromMaskedWord
  have h_mask :
      ((packStructToMaskedWord s padBits).initMask &&& paddedStructInitMask ==
        paddedStructInitMask) = true :=
    pack_initMask_satisfies_padded s padBits
  rw [h_mask]
  simp only [ite_true]
  rw [pack_bits_extract_a, pack_bits_extract_b]

/-- Changing the underlying padding bits does not affect the unpacked struct. -/
theorem unpack_pack_padding_irrelevant
    (s : PaddedStruct) (pad1 pad2 : BitVec 24) :
    unpackStructFromMaskedWord (packStructToMaskedWord s pad1) =
      unpackStructFromMaskedWord (packStructToMaskedWord s pad2) := by
  rw [unpack_pack_padded_exact, unpack_pack_padded_exact]

/-!
## Section 2: `freezeMaskedWord` Refinement (`Trusted.Compiles`) vs. Whole-Word Poison

At the target lowering boundary (`AnSSA` / `AnLLVM` / `cg_clif`), a
`PassMode::Cast` register must be represented as a concrete hardware register
`BitVec 64` (where every bit is defined). Inserting per-bit `freeze`
(`freezeMaskedWord oracle w`) nondeterministically replaces uninitialized bits
(`initMask = 0`) with bits from `oracle : BitVec 64` while preserving every
initialized bit (`initMask = 1`).
-/

/-- Per-bit `freeze` of a `MaskedWord` using a nondeterministic bit oracle
`oracle : BitVec 64`. Initialized bits (`initMask = 1`) are taken from `w.bits`;
uninitialized bits (`initMask = 0`) are filled from `oracle`. -/
def freezeMaskedWord (oracle : BitVec 64) (w : MaskedWord) : BitVec 64 :=
  (w.bits &&& w.initMask) ||| (oracle &&& ~~~w.initMask)

/-- Embeds a frozen hardware `BitVec 64` register back into `MaskedWord` with
all 64 bits marked initialized. -/
def frozenToMaskedWord (raw : BitVec 64) : MaskedWord :=
  { bits := raw
  , initMask := 0xFFFF_FFFF_FFFF_FFFF#64 }

/-- Freezing a `MaskedWord` preserves all bits marked initialized in
`w.initMask`. -/
theorem freezeMaskedWord_preserves_initialized_bits
    (oracle : BitVec 64) (w : MaskedWord) :
    (freezeMaskedWord oracle w) &&& w.initMask = w.bits &&& w.initMask := by
  ext i hi
  simp [freezeMaskedWord]
  cases w.initMask[i] <;> simp

/-- Unpacking a frozen `MaskedWord` produced by packing `s : PaddedStruct`
recovers `some s` for every possible nondeterministic `oracle : BitVec 64` and
every `padBits : BitVec 24`. -/
theorem unpack_frozen_pack_padded_exact
    (s : PaddedStruct) (padBits : BitVec 24) (oracle : BitVec 64) :
    unpackStructFromMaskedWord
        (frozenToMaskedWord (freezeMaskedWord oracle (packStructToMaskedWord s padBits))) =
      some s := by
  let w := packStructToMaskedWord s padBits
  have h_pres := freezeMaskedWord_preserves_initialized_bits oracle w
  unfold unpackStructFromMaskedWord frozenToMaskedWord
  have h_mask :
      ((0xFFFF_FFFF_FFFF_FFFF#64 &&& paddedStructInitMask) ==
        paddedStructInitMask) = true := rfl
  rw [h_mask]
  simp only [ite_true]
  congr 1
  have ha : (freezeMaskedWord oracle w).truncate 8 = s.a := by
    rw [← pack_bits_extract_a s padBits]
    ext i hi
    have h_bit := congrArg (fun x : BitVec 64 => x[i]) h_pres
    have h_lt8 : decide (i < 8) = true := decide_eq_true hi
    have h_init : w.initMask[i] = true := by
      simp only [w, packStructToMaskedWord, paddedStructInitMask,
        BitVec.zeroExtend_eq_setWidth, BitVec.getElem_or,
        BitVec.getElem_setWidth, BitVec.getLsbD_allOnes, h_lt8,
        Bool.true_or]
    simp only [BitVec.getElem_and, h_init, Bool.and_true] at h_bit
    simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
    exact h_bit
  have hb : ((freezeMaskedWord oracle w) >>> 32).truncate 32 = s.b := by
    rw [← pack_bits_extract_b s padBits]
    ext i hi
    have h_bit := congrArg (fun x : BitVec 64 => (x >>> 32)[i]) h_pres
    have h_init : w.initMask.getLsbD (32 + i) = true := by
      have h1 : decide (32 + i < 64) = true := decide_eq_true (by omega)
      have h2 : decide (32 + i < 32) = false := decide_eq_false (by omega)
      have h3 : decide (i < 64) = true := decide_eq_true (by omega)
      have h4 : decide (i < 32) = true := decide_eq_true hi
      simp only [w, packStructToMaskedWord, paddedStructInitMask,
        BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_or,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_allOnes, h1, h2, h3, h4, Nat.add_sub_cancel_left,
        Bool.true_and, Bool.not_false, Bool.or_true]
    simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_and, h_init,
      Bool.and_true] at h_bit
    simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth,
      BitVec.getLsbD_ushiftRight]
    exact h_bit
  rw [ha, hb]

/-!
### Connecting `PassMode::Cast` Freeze Lowering to `Trusted.Compiles`

We now package the source `AnMIR` byte-masked `PassMode::Cast` semantics and
the target `AnSSA`/`AnLLVM` frozen-register semantics as instances of
`Trusted.Language`, and prove `Trusted.Compiles` and
`Trusted.Compiler.Verified`.
-/

/-- Behavioral domain for `PassMode::Cast` struct passing:
`none` represents undefined behavior / poison failure (top of the refinement
preorder, refined by everything), while `some s` represents deterministic
delivery of `s : PaddedStruct`. -/
abbrev CastBeh := Option PaddedStruct

/-- Refinement preorder on `CastBeh`: `b_tgt ≤ b_src` iff `b_src = none` (source
UB can be refined by any target behavior) or `b_tgt = b_src`. -/
instance : Trusted.Preorder CastBeh where
  le b_tgt b_src := b_src = none ∨ b_tgt = b_src
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hbc with rfl | rfl
    · exact Or.inl rfl
    · exact hab

/-- Source program for `PassMode::Cast` marshaling: a `PaddedStruct` paired with
arbitrary uninitialized padding bits `padBits : BitVec 24`. -/
structure CastSourceProg where
  val : PaddedStruct
  padBits : BitVec 24
  deriving DecidableEq, Repr

/-- Source language (`AnMIR` byte-accurate `PassMode::Cast`): packs the struct
into a `MaskedWord` and unpacks it on the callee side. -/
def CastSourceLang : Trusted.Language where
  Prog := CastSourceProg
  wf _ := True
  Beh := CastBeh
  eval p :=
    unpackStructFromMaskedWord
      (packStructToMaskedWord p.prog.val p.prog.padBits)

/-- Target program (`AnSSA` / `AnLLVM` with boundary `freeze`): holds the packed
`MaskedWord` and freezes it into a hardware `BitVec 64` register using `oracle`
before callee unpacking. -/
structure CastTargetProg where
  word : MaskedWord
  deriving DecidableEq, Repr

/-- Target language parameterized by the hardware `freeze` nondeterminism oracle
`oracle : BitVec 64`. -/
def CastTargetLang (oracle : BitVec 64) : Trusted.Language where
  Prog := CastTargetProg
  wf _ := True
  Beh := CastBeh
  eval p :=
    unpackStructFromMaskedWord
      (frozenToMaskedWord (freezeMaskedWord oracle p.prog.word))

/-- Compiler pass lowering `CastSourceProg` to `CastTargetProg`. -/
def compilePassModeCast (p : CastSourceProg) : Option CastTargetProg :=
  some { word := packStructToMaskedWord p.val p.padBits }

/-- **Refinement Theorem (`Trusted.Compiles`):**
Lowering `PassMode::Cast` via `freezeMaskedWord` satisfies `Trusted.Compiles`
for every `oracle : BitVec 64` and every source program `p : CastSourceProg`. -/
theorem passModeCast_freeze_compiles
    (oracle : BitVec 64) (p : CastSourceProg) :
    Trusted.Compiles
      CastSourceLang
      (CastTargetLang oracle)
      compilePassModeCast
      rfl
      p
      { word := packStructToMaskedWord p.val p.padBits } := by
  refine ⟨trivial, trivial, rfl, ?_⟩
  change (CastSourceLang.eval ⟨p, trivial⟩) = none ∨
    (CastTargetLang oracle).eval
      ⟨{ word := packStructToMaskedWord p.val p.padBits }, trivial⟩ =
    CastSourceLang.eval ⟨p, trivial⟩
  right
  simp only [CastSourceLang, CastTargetLang]
  rw [unpack_frozen_pack_padded_exact, unpack_pack_padded_exact]

/-- **End-to-End Verification Theorem (`Trusted.Compiler.Verified`):**
Every `PassMode::Cast` source program is verified under `freezeMaskedWord`
lowering across all hardware `freeze` realizations `oracle : BitVec 64`. -/
theorem passModeCast_freeze_verified
    (oracle : BitVec 64) (p : CastSourceProg) :
    Trusted.Compiler.Verified
      CastSourceLang
      (CastTargetLang oracle)
      compilePassModeCast
      rfl
      p :=
  ⟨{ word := packStructToMaskedWord p.val p.padBits },
    passModeCast_freeze_compiles oracle p⟩

/-!
### Negative Canary: Naive Whole-Word Integer Load Without `freeze` Is Unsound

In formal LLVM IR semantics (`Vellvm` `MemoryBytes.v:726-733` and `Alive2`
`ir/memory.cpp:743-776`), a whole-word integer load (`load i64, ptr %scratch`)
returns a non-poison integer word if and only if **all 8 bytes** in the 64-bit
word are initialized (`w.initMask == 0xFFFF_FFFF_FFFF_FFFF#64`). If any padding
byte is uninitialized, the entire `i64` word becomes `poison` (`none`).
-/

/-- Naive whole-word integer load without per-byte `freeze`: requires all 64
bits of `w.initMask` to be `1`, returning `none` (whole-word poison) if any
padding byte is uninitialized. -/
def wholeWordLoadWithoutFreeze (w : MaskedWord) : Option (BitVec 64) :=
  if w.initMask == 0xFFFF_FFFF_FFFF_FFFF#64 then
    some w.bits
  else
    none

/-- Naive target language that lowers `PassMode::Cast` to a whole-word `i64`
load without inserting `freeze`. -/
def NaiveWholeWordTargetLang : Trusted.Language where
  Prog := CastTargetProg
  wf _ := True
  Beh := CastBeh
  eval p :=
    match wholeWordLoadWithoutFreeze p.prog.word with
    | some raw => unpackStructFromMaskedWord (frozenToMaskedWord raw)
    | none => none

/-- **Negative Canary Theorem:**
For any `PaddedStruct`, `wholeWordLoadWithoutFreeze` on the packed `MaskedWord`
yields `none` (whole-word poison), and therefore `compilePassModeCast` fails to
satisfy `Trusted.Compiles` into `NaiveWholeWordTargetLang`. -/
theorem canary_whole_word_poison_on_padding_unsound (p : CastSourceProg) :
    wholeWordLoadWithoutFreeze (packStructToMaskedWord p.val p.padBits) = none ∧
    ¬ Trusted.Compiles
        CastSourceLang
        NaiveWholeWordTargetLang
        compilePassModeCast
        rfl
        p
        { word := packStructToMaskedWord p.val p.padBits } := by
  constructor
  · unfold wholeWordLoadWithoutFreeze packStructToMaskedWord paddedStructInitMask
    rfl
  · rintro ⟨_, _, _, h_refines⟩
    change (CastSourceLang.eval ⟨p, trivial⟩) = none ∨
      NaiveWholeWordTargetLang.eval
        ⟨{ word := packStructToMaskedWord p.val p.padBits }, trivial⟩ =
      CastSourceLang.eval ⟨p, trivial⟩ at h_refines
    have h_src : CastSourceLang.eval ⟨p, trivial⟩ = some p.val := by
      simp only [CastSourceLang]
      exact unpack_pack_padded_exact p.val p.padBits
    have h_tgt :
        NaiveWholeWordTargetLang.eval
          ⟨{ word := packStructToMaskedWord p.val p.padBits }, trivial⟩ = none := by
      simp only [NaiveWholeWordTargetLang, wholeWordLoadWithoutFreeze,
        packStructToMaskedWord, paddedStructInitMask]
      rfl
    rw [h_src, h_tgt] at h_refines
    rcases h_refines with h_absurd | h_absurd
    · nomatch h_absurd
    · nomatch h_absurd

/-!
## Section 3: `BackendRepr::ScalarPair` in `AnSSA` & Sub-Word Niche Extraction

We resolve Track 3 Open Questions 1 and 3:
1. **Byte-Offset vs. `FieldIdx` Projection on `ScalarPair`:**
   In `rustc_abi::LayoutData`, a `BackendRepr::ScalarPair { a, b, b_offset }`
   places scalar `a` at byte offset `0` and scalar `b` at byte offset
   `b_offset > 0`. For a niche-encoded enum (`TagEncoding::Niche`),
   `layout.variants` always sets `tag_field := FieldIdx(0)`, while
   `layout.fields` is `FieldsShape::Arbitrary { offsets: [niche_offset] }`
   (`compiler/rustc_abi/src/layout.rs:734-749`). When the niche is inside the
   second scalar (`niche_offset == b_offset`), `tag_field` has index `0` but
   byte offset `b_offset > 0`! Therefore, `AnSSA` must dispatch `ScalarPair`
   projections by **byte offset** (`offset == 0` vs. `offset == b_offset`, as in
   `rustc_codegen_ssa`'s `OperandRef::extract_field`), never by raw
   `FieldIdx.as_u32()`.
2. **Sub-Word Niche Discriminant Extraction and Encoding:**
   When a `ScalarPair` or cast register pair `(fst, snd)` holds a sub-word niche
   tag at byte offset `byteOff : Fin 8` within `fst` (`inSnd = false`) or `snd`
   (`inSnd = true`), extracting `((reg >>> (byteOff * 8)) &&& 0xFF) : BitVec 8`
   and applying modular wrapping niche decoding `(tag - nicheStart) ≤ᵤ nicheSpan`
   round-trips every tagged and untagged variant while preserving all other
   bytes in both registers.
-/

/-- Two-register representation of a `BackendRepr::ScalarPair` value in `AnSSA`. -/
structure ScalarPairVal where
  fst : BitVec 64
  snd : BitVec 64
  deriving DecidableEq, Repr

/-- Byte-offset-dispatched `ScalarPair` projection (`rustc_codegen_ssa`
`OperandRef::extract_field`, `compiler/rustc_codegen_ssa/src/mir/operand.rs:408-420`):
routes offset `0` to `pair.fst` and `bOffset` (`bOffset > 0`) to `pair.snd`. -/
def extractScalarPairByOffset
    (pair : ScalarPairVal) (bOffset : Nat) (fieldOffset : Nat) : Option (BitVec 64) :=
  if fieldOffset == 0 then
    some pair.fst
  else if fieldOffset == bOffset then
    some pair.snd
  else
    none

/-- Raw `FieldIdx`-dispatched `ScalarPair` projection (`0 => fst`, `1 => snd`),
which is only valid for direct 2-tuples without leading 1-ZSTs and fails on
multi-variant niche enums where `tag_field = FieldIdx(0)` has
`niche_offset = b_offset`. -/
def extractScalarPairByFieldIdx
    (pair : ScalarPairVal) (fieldIdx : Nat) : Option (BitVec 64) :=
  match fieldIdx with
  | 0 => some pair.fst
  | 1 => some pair.snd
  | _ => none

/-- **Canary Theorem (Track 3 Open Question 1):**
When an enum with `BackendRepr::ScalarPair` has its niche in the second scalar
(`bOffset = 8`, `tag_field = FieldIdx(0)`, `fieldOffset = 8`), raw `FieldIdx`
dispatch reads `pair.fst` (the payload union scalar) instead of `pair.snd` (the
niche scalar), whereas byte-offset dispatch reads `pair.snd`. -/
theorem canary_fieldIdx_projection_mismatch_on_niche_in_snd :
    let pair : ScalarPairVal := { fst := 0xDEAD_BEEF_CAFE_BABE#64, snd := 0#64 }
    let tagFieldIdx : Nat := 0
    let bOffset : Nat := 8
    let tagFieldByteOffset : Nat := bOffset
    extractScalarPairByOffset pair bOffset tagFieldByteOffset = some pair.snd ∧
    extractScalarPairByFieldIdx pair tagFieldIdx = some pair.fst ∧
    extractScalarPairByOffset pair bOffset tagFieldByteOffset ≠
      extractScalarPairByFieldIdx pair tagFieldIdx := by
  decide

/-- Extracts the byte at `byteOff : Fin 8` from a 64-bit register. -/
def extractByteAt (word : BitVec 64) (byteOff : Fin 8) : BitVec 8 :=
  (word >>> (byteOff.val * 8)).truncate 8

/-- Replaces the byte at `byteOff : Fin 8` in `word : BitVec 64` with
`b : BitVec 8`, preserving all other 7 bytes. -/
def insertByteAt (word : BitVec 64) (byteOff : Fin 8) (b : BitVec 8) : BitVec 64 :=
  let shift : Nat := byteOff.val * 8
  let clearMask : BitVec 64 := ~~~(((BitVec.allOnes 8).zeroExtend 64) <<< shift)
  let b64 : BitVec 64 := (b.zeroExtend 64) <<< shift
  (word &&& clearMask) ||| b64

/-- Extracts the byte at `(inSnd, byteOff)` from a `ScalarPairVal`. -/
def extractScalarPairByte
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) : BitVec 8 :=
  let reg := if inSnd then pair.snd else pair.fst
  extractByteAt reg byteOff

/-- Writes `b : BitVec 8` into `(inSnd, byteOff)` of a `ScalarPairVal`,
preserving the other register and all other 7 bytes of the selected register. -/
def insertScalarPairByte
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) (b : BitVec 8) : ScalarPairVal :=
  if inSnd then
    { pair with snd := insertByteAt pair.snd byteOff b }
  else
    { pair with fst := insertByteAt pair.fst byteOff b }

/-- Universal bit-exact round-trip for `extractByteAt` after `insertByteAt`
across all `byteOff : Fin 8`, `word : BitVec 64`, and `b : BitVec 8`. -/
theorem extractByteAt_insertByteAt_exact
    (word : BitVec 64) (byteOff : Fin 8) (b : BitVec 8) :
    extractByteAt (insertByteAt word byteOff b) byteOff = b := by
  ext j hj
  rcases byteOff with ⟨k, hk⟩
  have h1 : decide (k * 8 + j < 64) = true := decide_eq_true (by omega)
  have h2 : decide (k * 8 + j < k * 8) = false := decide_eq_false (by omega)
  have h3 : k * 8 + j - k * 8 = j := by omega
  have h4 : decide (j < 64) = true := decide_eq_true (by omega)
  have h5 : decide (j < 8) = true := decide_eq_true hj
  simp only [extractByteAt, insertByteAt, BitVec.truncate_eq_setWidth,
    BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1, h2, h3, h4, h5,
    Bool.true_and, Bool.not_false, Bool.not_true, Bool.and_false,
    Bool.false_or]
  rfl

/-- Writing a byte into `byteOff` preserves all other 7 bytes (`otherOff ≠ byteOff`)
in the 64-bit register. -/
theorem extractByteAt_insertByteAt_other_bytes_preserved
    (word : BitVec 64) (byteOff otherOff : Fin 8) (b : BitVec 8)
    (h_ne : otherOff ≠ byteOff) :
    extractByteAt (insertByteAt word byteOff b) otherOff =
      extractByteAt word otherOff := by
  ext j hj
  rcases byteOff with ⟨k, hk⟩
  rcases otherOff with ⟨m, hm⟩
  have h_km : m ≠ k := by
    intro h_eq
    apply h_ne
    subst h_eq
    rfl
  have h1 : decide (m * 8 + j < 64) = true := decide_eq_true (by omega)
  by_cases h_lt : m < k
  · have h2 : decide (m * 8 + j < k * 8) = true := decide_eq_true (by omega)
    simp only [extractByteAt, insertByteAt, BitVec.truncate_eq_setWidth,
      BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, h1, h2,
      Bool.true_and, Bool.not_true, Bool.false_and, Bool.not_false,
      Bool.and_true, Bool.or_false]
  · have h_gt : k < m := by omega
    have h2 : decide (m * 8 + j < k * 8) = false := decide_eq_false (by omega)
    have h3 : decide (m * 8 + j - k * 8 < 64) = true := decide_eq_true (by omega)
    have h4 : decide (m * 8 + j - k * 8 < 8) = false := decide_eq_false (by omega)
    have h_b_out : b.getLsbD (m * 8 + j - k * 8) = false :=
      BitVec.getLsbD_of_ge b (m * 8 + j - k * 8) (by omega)
    simp only [extractByteAt, insertByteAt, BitVec.truncate_eq_setWidth,
      BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1, h2, h3, h4, h_b_out,
      Bool.true_and, Bool.not_false, Bool.and_true, Bool.or_false]

/-- Writing a byte into `(inSnd, byteOff)` and reading it back recovers `b`
for both registers (`inSnd = false` and `inSnd = true`) and all 8 sub-word byte
offsets. -/
theorem extractScalarPairByte_insertScalarPairByte_exact
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) (b : BitVec 8) :
    extractScalarPairByte (insertScalarPairByte pair inSnd byteOff b) inSnd byteOff = b := by
  cases inSnd <;>
    exact extractByteAt_insertByteAt_exact _ byteOff b

/-- Writing a byte into `(inSnd, byteOff)` leaves the other register completely
unchanged. -/
theorem insertScalarPairByte_preserves_other_reg
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) (b : BitVec 8) :
    (if inSnd then (insertScalarPairByte pair inSnd byteOff b).fst else
      (insertScalarPairByte pair inSnd byteOff b).snd) =
    (if inSnd then pair.fst else pair.snd) := by
  cases inSnd <;> rfl

/-!
### Sub-Word Niche Discriminant Encoding and Decoding on `ScalarPairVal`

Following `rustc_codegen_ssa::mir::place::codegen_get_discriminant`
(`compiler/rustc_codegen_ssa/src/mir/place.rs:342-403`) and
`rustc_codegen_cranelift::discriminant::codegen_get_discriminant`
(`compiler/rustc_codegen_cranelift/src/discriminant.rs:95-153`), we model an
enum with `BackendRepr::ScalarPair` (or packed into two 64-bit registers) whose
1-byte niche scalar resides in register `inSnd` at sub-word byte offset
`byteOff : Fin 8`.

As a concrete running specification with wrapping niche range (`nicheStart >
nicheEnd` unsigned), consider an enum with 4 variants (`Fin 4`):
- `untaggedVariant = 1`: holds a sub-word `u8` payload valid in `1..=253`
  (so `0`, `254`, and `255` are niche values, forming the wrapping interval
  `[nicheStart = 254, nicheEnd = 0]` of length `nicheSpan = 2` in `BitVec 8`!).
- Tagged variants `0`, `2`, `3`: encoded at niche tags `254`, `255`, `0`.
-/

/-- Wrapping 8-bit niche start (`254#8`). -/
def subwordNicheStart : BitVec 8 := 254#8

/-- Wrapping 8-bit niche span (`2#8`, covering tags `254`, `255`, `0`). -/
def subwordNicheSpan : BitVec 8 := 2#8

/-- Untagged payload variant index (`1`). -/
def subwordUntaggedVariant : BitVec 8 := 1#8

/-- Encodes a variant index `v : BitVec 8` (`v < 4`, `v ≠ 1`) into its sub-word
niche tag at `(inSnd, byteOff)` within `pair : ScalarPairVal`. -/
def encodeScalarPairSubwordNiche
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) (v : BitVec 8) : ScalarPairVal :=
  let idx : BitVec 8 := if v.ult subwordUntaggedVariant then v else v - 1#8
  let nicheTag : BitVec 8 := subwordNicheStart + idx
  insertScalarPairByte pair inSnd byteOff nicheTag

/-- Decodes the active variant index (`0..3`) from `(inSnd, byteOff)` of
`pair : ScalarPairVal` using wrapping modular subtraction `tag - nicheStart` and
unsigned comparison `≤ᵤ nicheSpan`. -/
def decodeScalarPairSubwordNiche
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) : BitVec 8 :=
  let tag : BitVec 8 := extractScalarPairByte pair inSnd byteOff
  let rel : BitVec 8 := tag - subwordNicheStart
  if rel.ule subwordNicheSpan then
    if rel.ult subwordUntaggedVariant then rel else rel + 1#8
  else
    subwordUntaggedVariant

/-- Helper lemma: modular niche decoding recovers any tagged variant `v < 4`
with `v ≠ 1` from its encoded byte. -/
theorem decode_encode_subword_niche_byte
    (v : BitVec 8) (hv_bound : v.ult 4#8 = true) (hv_tagged : v ≠ subwordUntaggedVariant) :
    let idx := if v.ult subwordUntaggedVariant then v else v - 1#8
    let tag := subwordNicheStart + idx
    let rel := tag - subwordNicheStart
    (if rel.ule subwordNicheSpan then
      if rel.ult subwordUntaggedVariant then rel else rel + 1#8
    else
      subwordUntaggedVariant) = v := by
  rcases v with ⟨⟨val, hlt⟩⟩
  have hbound : val < 4 := by
    change decide (val < 4) = true at hv_bound
    exact of_decide_eq_true hv_bound
  have hne : val ≠ 1 := by
    intro h1
    apply hv_tagged
    subst h1
    rfl
  have hcases : val = 0 ∨ val = 2 ∨ val = 3 := by omega
  rcases hcases with rfl | rfl | rfl <;> decide +revert

/-- **Universal Round-Trip Theorem for Tagged Variants in `ScalarPair`:**
For every `pair : ScalarPairVal`, register choice `inSnd : Bool`, sub-word byte
offset `byteOff : Fin 8`, and tagged variant `v` (`v < 4`, `v ≠ 1`), encoding
`v` into `(inSnd, byteOff)` and decoding recovers `v`. -/
theorem scalarPair_decode_encode_niche_tagged
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8) (v : BitVec 8)
    (hv_bound : v.ult 4#8 = true) (hv_tagged : v ≠ subwordUntaggedVariant) :
    decodeScalarPairSubwordNiche
        (encodeScalarPairSubwordNiche pair inSnd byteOff v) inSnd byteOff = v := by
  unfold decodeScalarPairSubwordNiche encodeScalarPairSubwordNiche
  rw [extractScalarPairByte_insertScalarPairByte_exact]
  exact decode_encode_subword_niche_byte v hv_bound hv_tagged

/-- **Universal Round-Trip Theorem for Untagged Payload Variants in `ScalarPair`:**
For every `pair : ScalarPairVal`, register choice `inSnd : Bool`, and sub-word
byte offset `byteOff : Fin 8`, if the payload byte at `(inSnd, byteOff)` lies in
the valid untagged range `1..=253`, `decodeScalarPairSubwordNiche` returns
`subwordUntaggedVariant` (`1#8`). -/
theorem scalarPair_decode_encode_niche_untagged
    (pair : ScalarPairVal) (inSnd : Bool) (byteOff : Fin 8)
    (h_lo : (1#8).ule (extractScalarPairByte pair inSnd byteOff) = true)
    (h_hi : (extractScalarPairByte pair inSnd byteOff).ule 253#8 = true) :
    decodeScalarPairSubwordNiche pair inSnd byteOff = subwordUntaggedVariant := by
  unfold decodeScalarPairSubwordNiche subwordNicheStart subwordNicheSpan subwordUntaggedVariant
  dsimp only
  generalize extractScalarPairByte pair inSnd byteOff = tag at h_lo h_hi ⊢
  rcases tag with ⟨⟨val, hlt⟩⟩
  have h1 : 1 ≤ val := by
    change decide (1 ≤ val) = true at h_lo
    exact of_decide_eq_true h_lo
  have h253 : val ≤ 253 := by
    change decide (val ≤ 253) = true at h_hi
    exact of_decide_eq_true h_hi
  have hcond : (BitVec.ofFin ⟨val, hlt⟩ - 254#8).ule 2#8 = false := by
    change decide (((256 - 254 + val) % 256) ≤ 2) = false
    rw [decide_eq_false_iff_not]
    omega
  rw [hcond]
  rfl

/-!
## Section 4: Pure-Rust Float Fallback Intrinsics (`fabs` & `copysignf64`)

In `library/core/src/intrinsics/mod.rs:3497-3544`, `fabs` and `copysignf*` have
pure-Rust fallback bodies operating on the IEEE 754 representation via
`to_bits`, `from_bits`, and `SIGN_MASK`:
- `fabs(x)` computes `T::from_bits(x.to_bits() & !T::SIGN_MASK)`
- `copysignf64(x, y)` computes
  `f64::from_bits((x.to_bits() & !f64::SIGN_MASK) | (y.to_bits() & f64::SIGN_MASK))`

We prove that these pure-Rust bit-manipulation bodies satisfy the exact IEEE
754-2019 `abs` and `copySign` bit-level specifications across all 64-bit
floating-point bit patterns (including `-0.0`, `+0.0`, $\pm\infty$, quiet NaNs,
and signaling NaNs with arbitrary payload bits).
-/

/-- IEEE 754 `binary64` (`f64`) sign mask (`1 << 63`). -/
def f64SignMask : BitVec 64 :=
  (1#64) <<< 63

theorem f64SignMask_eq_hex :
    f64SignMask = 0x8000_0000_0000_0000#64 := rfl

/-- Pure-Rust fallback bit operation for `core::intrinsics::fabs::<f64>`. -/
def fabsBits64 (x : BitVec 64) : BitVec 64 :=
  x &&& ~~~f64SignMask

/-- Pure-Rust fallback bit operation for `core::intrinsics::copysignf64`. -/
def copysignBits64 (x y : BitVec 64) : BitVec 64 :=
  (x &&& ~~~f64SignMask) ||| (y &&& f64SignMask)

/-- `fabsBits64` always clears the sign bit (bit 63) and preserves all 63
exponent and significand/NaN-payload bits (bits 0..62). -/
theorem fabsBits64_spec (x : BitVec 64) :
    (fabsBits64 x).msb = false ∧
    (fabsBits64 x).truncate 63 = x.truncate 63 := by
  constructor
  · simp [fabsBits64, f64SignMask, BitVec.msb_eq_getLsbD_last]
  · ext i hi
    have h63 : decide (i < 63) = true := decide_eq_true hi
    have h64 : decide (i < 64) = true := decide_eq_true (by omega)
    simp only [fabsBits64, f64SignMask, BitVec.truncate_eq_setWidth,
      BitVec.getElem_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, h63, h64, Bool.not_true, Bool.false_and,
      Bool.and_false, Bool.not_false, Bool.and_true]

/-- `copysignBits64 x y` takes its sign bit (bit 63) from `y` and all 63
exponent and significand/NaN-payload bits (bits 0..62) from `x`. -/
theorem copysignBits64_spec (x y : BitVec 64) :
    (copysignBits64 x y).msb = y.msb ∧
    (copysignBits64 x y).truncate 63 = x.truncate 63 := by
  constructor
  · simp [copysignBits64, f64SignMask, BitVec.msb_eq_getLsbD_last]
  · ext i hi
    have h63 : decide (i < 63) = true := decide_eq_true hi
    have h64 : decide (i < 64) = true := decide_eq_true (by omega)
    simp only [copysignBits64, f64SignMask, BitVec.truncate_eq_setWidth,
      BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, h63, h64, Bool.not_true,
      Bool.false_and, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.or_false]

/-- `fabsBits64 x` is bit-identical to `copysignBits64 x 0` (`+0.0`). -/
theorem fabsBits64_eq_copysign_posZero (x : BitVec 64) :
    fabsBits64 x = copysignBits64 x 0#64 := by
  ext i hi
  simp [fabsBits64, copysignBits64, f64SignMask]

/-!
## Section 5: Axiom Audit (`#guard_msgs in #print axioms`)

Every theorem in this probe is verified free of `sorryAx` and
`Lean.ofReduceBool`.
-/

/-- info: 'Round2Track1.unpack_pack_padded_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unpack_pack_padded_exact

/-- info: 'Round2Track1.freezeMaskedWord_preserves_initialized_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms freezeMaskedWord_preserves_initialized_bits

/-- info: 'Round2Track1.unpack_frozen_pack_padded_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpack_frozen_pack_padded_exact

/-- info: 'Round2Track1.passModeCast_freeze_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms passModeCast_freeze_compiles

/-- info: 'Round2Track1.passModeCast_freeze_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms passModeCast_freeze_verified

/-- info: 'Round2Track1.canary_whole_word_poison_on_padding_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary_whole_word_poison_on_padding_unsound

/-- info: 'Round2Track1.canary_fieldIdx_projection_mismatch_on_niche_in_snd' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_fieldIdx_projection_mismatch_on_niche_in_snd

/-- info: 'Round2Track1.extractByteAt_insertByteAt_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extractByteAt_insertByteAt_exact

/-- info: 'Round2Track1.extractByteAt_insertByteAt_other_bytes_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms extractByteAt_insertByteAt_other_bytes_preserved

/-- info: 'Round2Track1.extractScalarPairByte_insertScalarPairByte_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms extractScalarPairByte_insertScalarPairByte_exact

/-- info: 'Round2Track1.scalarPair_decode_encode_niche_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scalarPair_decode_encode_niche_tagged

/-- info: 'Round2Track1.scalarPair_decode_encode_niche_untagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scalarPair_decode_encode_niche_untagged

/-- info: 'Round2Track1.fabsBits64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fabsBits64_spec

/-- info: 'Round2Track1.copysignBits64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copysignBits64_spec

end Round2Track1
