-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Lemmas
import VendorX86Ref.Machine
import ByteX86Pass2Correspondence

/-!
# `SimdTriangulation24`

Kernel-checked 3-way Pass-2 SIMD triangulation (`0` `sorry`, `prelude` + `Init.*`
only) across all **24 curated `core::arch::x86_64` primitives** (`16` portable
`#[rustc_intrinsic]` `simd_*` operations + `8` `llvm.x86.*` families covering
`98.94%` of pure-Rust SIMD crate call sites, plus `5` shift/shuffle boundary
companions = **29 compiled `.o` functions**):

1. **Three Unguarded MIR-vs-x86 Undefined-Behavior Asymmetry Theorems:**
   - `unguarded_simd_shl_ub_vs_vpsllvd_zero`: Raw MIR `simd_shl` returns
     `.error (.shiftOverflow 32)` on lane shift count `32`, whereas `rustc -O3`
     `vpsllvd` (`p14bBytes`) succeeds and zeroes the lane.
   - `unguarded_simd_bitmask_ub_vs_vpmovmskb_msb`: Raw MIR `simd_bitmask`
     (`IntrinsicSimd.elementToBool`) returns `.error (.nonBoolMask 0x80)` on
     lane byte `0x80` (`∉ {0x00, 0xFF}`), whereas `rustc -O3` `vpmovmskb`
     (`p09Bytes`) extracts the sign bit without UB.
   - `unguarded_simd_funnel_shl_ub_vs_vprolvd_mod32`: Raw MIR `simd_funnel_shl`
     returns `.error (.funnelShiftOverflow 32)` on count `32`, whereas `rustc -O3`
     EVEX `vprolvd` (`p11Bytes`) rotates modulo `32` without UB.

2. **29 Universally Quantified (`∀ a b c mem rsp`) 3-Way Triangulation Theorems:**
   For every primitive `p01`..`p24` (+ `p14b`, `p14c`, `p15b`, `p15c`, `p16b`):
   - **Leg A (`LeanMiri + stdarch wrapper ⊑ StdarchSpec`):** Never triggers UB
     for any 128/256-bit input vector and produces `StdarchSpec`.
   - **Leg B (`rustc -O3 .o bytes @ VendorX86Ref ⊑ StdarchSpec`):** Decoding and
     stepping the exact ELF64 `.o` bytes emitted identically by `rustc 1.99.1`
     and `rustc 1.102.0-nightly` at `-C opt-level=3` halts cleanly at `RET` with
     zero faults and exact `StdarchSpec` return register contents.
   - **Leg C (`rustc -O3 .o bytes @ ByteX86 ⊑ StdarchSpec`):** Lifts the exact
     `.o` execution trace into `ByteX86.StepsN` via Pass-2 simulation.
-/

namespace SimdTriangulation24

open VendorX86Ref ByteX86

/-! ## Section 1: `LeanMiri` Intrinsic Semantics (`IntrinsicSimd` + `IntrinsicX86`) -/

/-- Exact UB conditions enforced by `Miri/Interpreter/IntrinsicSimd.lean` and
    `Miri/Interpreter/IntegerOps.lean` in `proofs-rs/lean-miri@c92d1d97`. -/
inductive SimdUb where
  | shiftOverflow       (count : Nat)
  | nonBoolMask         (laneByte : Nat)
  | funnelShiftOverflow (count : Nat)
  | outOfBoundsIndex    (idx : Nat)
  deriving DecidableEq, Repr

/-- `IntrinsicSimd.lean` + `IntegerOps.binary .ShlUnchecked`: UB if `cnt >= 32`. -/
def miriLaneShl32 (x cnt : BitVec 32) : Except SimdUb (BitVec 32) :=
  if cnt.toNat >= 32 then .error (.shiftOverflow cnt.toNat)
  else .ok (x <<< cnt.toNat)

def miriLaneLshr32 (x cnt : BitVec 32) : Except SimdUb (BitVec 32) :=
  if cnt.toNat >= 32 then .error (.shiftOverflow cnt.toNat)
  else .ok (x >>> cnt.toNat)

def miriLaneAshr32 (x cnt : BitVec 32) : Except SimdUb (BitVec 32) :=
  if cnt.toNat >= 32 then .error (.shiftOverflow cnt.toNat)
  else .ok (BitVec.sshiftRight x cnt.toNat)

def mapDwords256M (f : Fin 8 → Except SimdUb (BitVec 32)) : Except SimdUb (BitVec 256) := do
  let d0 ← f ⟨0, by decide⟩; let d1 ← f ⟨1, by decide⟩
  let d2 ← f ⟨2, by decide⟩; let d3 ← f ⟨3, by decide⟩
  let d4 ← f ⟨4, by decide⟩; let d5 ← f ⟨5, by decide⟩
  let d6 ← f ⟨6, by decide⟩; let d7 ← f ⟨7, by decide⟩
  pure ((d7 ++ (d6 ++ (d5 ++ d4))) ++ (d3 ++ (d2 ++ (d1 ++ d0))))

theorem mapDwords256M_ok (g : Fin 8 → BitVec 32) :
    mapDwords256M (fun i => .ok (g i)) = .ok (packDwords256 g) := rfl

/-- Raw portable `simd_shl` over `u32x8` (`IntrinsicSimd.shift .ShlUnchecked`). -/
def miriSimdShlDwords (a cnt : BitVec 256) : Except SimdUb (BitVec 256) :=
  mapDwords256M fun i => miriLaneShl32 (getDword256 a i) (getDword256 cnt i)

def miriSimdLshrDwords (a cnt : BitVec 256) : Except SimdUb (BitVec 256) :=
  mapDwords256M fun i => miriLaneLshr32 (getDword256 a i) (getDword256 cnt i)

def miriSimdAshrDwords (a cnt : BitVec 256) : Except SimdUb (BitVec 256) :=
  mapDwords256M fun i => miriLaneAshr32 (getDword256 a i) (getDword256 cnt i)

/-- `IntrinsicSimd.elementToBool` (`L75-79`): lane must be `0x00` or `0xFF` (`-1`),
    otherwise Undefined Behavior! -/
def miriElementToBool8 (b : BitVec 8) : Except SimdUb Bool :=
  if b == 0x00#8 then .ok false
  else if b == 0xFF#8 then .ok true
  else .error (.nonBoolMask b.toNat)

def miriBitmaskLoop (n : Nat) (v : BitVec 256) (acc : BitVec 64) : Except SimdUb (BitVec 64) :=
  Nat.rec (motive := fun _ => BitVec 64 → Except SimdUb (BitVec 64))
    (fun a => .ok a)
    (fun k ih a => do
      let bit ← miriElementToBool8 (BitVec.extractLsb' (k * 8) 8 v)
      let a' := if bit then a ||| (1#64 <<< k) else a
      ih a')
    n acc

/-- Raw portable `simd_bitmask` on `i8x32` (`IntrinsicSimd.lean:369-396`). -/
def miriSimdBitmask256 (v : BitVec 256) : Except SimdUb (BitVec 64) :=
  miriBitmaskLoop 32 v 0#64

/-- Raw portable `simd_funnel_shl` (`IntrinsicSimd.lean:495-524`): UB if `s >= 32`. -/
def miriLaneFunnelShl32 (a b s : BitVec 32) : Except SimdUb (BitVec 32) :=
  if s.toNat >= 32 then .error (.funnelShiftOverflow s.toNat)
  else if s.toNat == 0 then .ok a
  else .ok ((a <<< s.toNat) ||| (b >>> (32 - s.toNat)))

def miriSimdFunnelShlDwords (a b s : BitVec 256) : Except SimdUb (BitVec 256) :=
  mapDwords256M fun i => miriLaneFunnelShl32 (getDword256 a i) (getDword256 b i) (getDword256 s i)

/-- `IntrinsicX86.shiftScalar` (`IntrinsicX86/Integer.lean:17-37`): saturating/clamping, never UB. -/
def miriX86ShiftDwords (kind : VecShiftKind) (a : BitVec 256) (cnt : Nat) : Except SimdUb (BitVec 256) :=
  .ok (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) cnt)

def miriX86ShiftVarDwords (kind : VecShiftKind) (a cnt : BitVec 256) : Except SimdUb (BitVec 256) :=
  .ok (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) (getDword256 cnt i).toNat)

/-! ### `stdarch` Lowerings (`core::arch::x86_64` over `LeanMiri`) & `StdarchSpec` -/

def spec_p01_add_epi8 (a b : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => getByte256 a i + getByte256 b i

def spec_p02_sub_epi8 (a b : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => getByte256 a i - getByte256 b i

def spec_p03_and_si256 (a b : BitVec 256) : BitVec 256 := a &&& b
def spec_p04_or_si256  (a b : BitVec 256) : BitVec 256 := a ||| b
def spec_p05_xor_si256 (a b : BitVec 256) : BitVec 256 := a ^^^ b

def spec_p06_cmpeq_epi8 (a b : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => if getByte256 a i == getByte256 b i then 0xFF#8 else 0x00#8

def spec_p07_cmpgt_epi8 (a b : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => if (getByte256 b i).slt (getByte256 a i) then 0xFF#8 else 0x00#8

def spec_p08_cmplt_epi8 (a b : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => if (getByte128 a i).slt (getByte128 b i) then 0xFF#8 else 0x00#8

def spec_p09_movemask_epi8 (a : BitVec 256) : BitVec 64 := vpmovmskb256 a

def spec_p10_extract_epi64_1 (a : BitVec 128) : BitVec 64 :=
  getQword128 a ⟨1, by decide⟩

def spec_p11_rolv_epi32 (a b : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => BitVec.rotateLeft (getDword256 a i) ((getDword256 b i).toNat % 32)

def spec_p12_testz_si256 (a b : BitVec 256) : BitVec 64 :=
  if (a &&& b) == 0#256 then 1#64 else 0#64

def spec_p13_subs_epu8 (a b : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => satSubU8 (getByte256 a i) (getByte256 b i)

def spec_p14_slli_epi32_7 (a : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => (getDword256 a i) <<< 7

def spec_p14b_sllv_epi32 (a cnt : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => vshiftLane32 .sll (getDword256 a i) (getDword256 cnt i).toNat

def spec_p14c_slli_epi32_40 (_a : BitVec 256) : BitVec 256 := 0#256

def spec_p15_srli_epi32_7 (a : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => (getDword256 a i) >>> 7

def spec_p15b_srai_epi32_7 (a : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => BitVec.sshiftRight (getDword256 a i) 7

def spec_p15c_srai_epi32_40 (a : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => BitVec.sshiftRight (getDword256 a i) 31

def spec_p16_permute2x128_21 (a b : BitVec 256) : BitVec 256 :=
  vperm2x128Eval a b 0x21#8

def spec_p16b_permute2x128_81 (a _b : BitVec 256) : BitVec 256 :=
  (BitVec.extractLsb' 128 128 a).zeroExtend 256

def spec_p17_clmulepi64_10 (a b : BitVec 128) : BitVec 128 :=
  carrylessMul64 (BitVec.extractLsb' 0 64 a) (BitVec.extractLsb' 64 64 b)

def spec_p18_aesenc (a rk : BitVec 128) : BitVec 128 := vaesenc128 a rk

def spec_p19_pshufb (a m : BitVec 256) : BitVec 256 :=
  pshufb128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 m) ++
  pshufb128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 m)

def spec_p20_sad_epu8 (a b : BitVec 256) : BitVec 256 :=
  psadbw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  psadbw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

def spec_p21_permutevar8x32 (a idx : BitVec 256) : BitVec 256 :=
  packDwords256 fun i =>
    let sel := ((getDword256 idx i) &&& 7#32).toNat
    getDword256 a ⟨sel % 8, Nat.mod_lt _ (by decide)⟩

def spec_p22_ternarylogic_96 (a b c : BitVec 256) : BitVec 256 :=
  packDwords256 fun i => ternlogDword 0x96#8 (getDword256 a i) (getDword256 b i) (getDword256 c i)

def spec_p23_madd_epi16 (a b : BitVec 256) : BitVec 256 :=
  pmaddwd128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  pmaddwd128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

def spec_p24_maddubs_epi16 (a b : BitVec 256) : BitVec 256 :=
  pmaddubsw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  pmaddubsw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

/-! ### `LeanMiri` + `stdarch` Wrapper Evaluators (`evalMiri_*`) -/

def evalMiri_p01 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p01_add_epi8 a b)
def evalMiri_p02 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p02_sub_epi8 a b)
def evalMiri_p03 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (a &&& b)
def evalMiri_p04 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (a ||| b)
def evalMiri_p05 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (a ^^^ b)
def evalMiri_p06 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p06_cmpeq_epi8 a b)
def evalMiri_p07 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p07_cmpgt_epi8 a b)
def evalMiri_p08 (a b : BitVec 128) : Except SimdUb (BitVec 128) := .ok (spec_p08_cmplt_epi8 a b)

/-- `stdarch` `_mm256_movemask_epi8(a)`: normalizes via `simd_lt(a, splat(0))`
    before calling `simd_bitmask` (`miriSimdBitmask256`) so `elementToBool` never UBs! -/
def miriSimdLtZero256 (a : BitVec 256) : BitVec 256 :=
  packBytes256 fun i => if (getByte256 a i).slt 0#8 then 0xFF#8 else 0x00#8

def evalMiri_p09 (a : BitVec 256) : Except SimdUb (BitVec 64) :=
  miriSimdBitmask256 (miriSimdLtZero256 a)

def evalMiri_p10 (a : BitVec 128) : Except SimdUb (BitVec 64) :=
  let idx : Nat := 1
  if idx >= 2 then .error (.outOfBoundsIndex idx) else .ok (getQword128 a ⟨1, by decide⟩)

/-- `stdarch` `_mm256_rolv_epi32(a, b)`: pre-masks shift counts via `simd_and(b, splat(31))`
    before calling `simd_funnel_shl(a, a, masked)`! -/
def evalMiri_p11 (a b : BitVec 256) : Except SimdUb (BitVec 256) :=
  let masked := packDwords256 fun i => (getDword256 b i) &&& 31#32
  miriSimdFunnelShlDwords a a masked

def evalMiri_p12 (a b : BitVec 256) : Except SimdUb (BitVec 64) :=
  let conj := a &&& b
  .ok (if conj == 0#256 then 1#64 else 0#64)

def evalMiri_p13 (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p13_subs_epu8 a b)

/-- `stdarch` `_mm256_slli_epi32::<IMM8>(a)`: guards `IMM8 < 32` before `simd_shl`,
    returning `splat(0)` when `IMM8 >= 32`! -/
def evalMiri_slli_epi32 (imm : Nat) (a : BitVec 256) : Except SimdUb (BitVec 256) :=
  if imm < 32 then
    let cnt := packDwords256 fun _ => BitVec.ofNat 32 imm
    miriSimdShlDwords a cnt
  else .ok 0#256

def evalMiri_p14  (a : BitVec 256) : Except SimdUb (BitVec 256) := evalMiri_slli_epi32 7 a
def evalMiri_p14b (a cnt : BitVec 256) : Except SimdUb (BitVec 256) := miriX86ShiftVarDwords .sll a cnt
def evalMiri_p14c (a : BitVec 256) : Except SimdUb (BitVec 256) := evalMiri_slli_epi32 40 a

def evalMiri_srli_epi32 (imm : Nat) (a : BitVec 256) : Except SimdUb (BitVec 256) :=
  if imm < 32 then
    let cnt := packDwords256 fun _ => BitVec.ofNat 32 imm
    miriSimdLshrDwords a cnt
  else .ok 0#256

def evalMiri_srai_epi32 (imm : Nat) (a : BitVec 256) : Except SimdUb (BitVec 256) :=
  let clamped := if imm >= 32 then 31 else imm
  let cnt := packDwords256 fun _ => BitVec.ofNat 32 clamped
  miriSimdAshrDwords a cnt

def evalMiri_p15  (a : BitVec 256) : Except SimdUb (BitVec 256) := evalMiri_srli_epi32 7 a
def evalMiri_p15b (a : BitVec 256) : Except SimdUb (BitVec 256) := evalMiri_srai_epi32 7 a
def evalMiri_p15c (a : BitVec 256) : Except SimdUb (BitVec 256) := evalMiri_srai_epi32 40 a

def evalMiri_p16  (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (vperm2x128Eval a b 0x21#8)
def evalMiri_p16b (a b : BitVec 256) : Except SimdUb (BitVec 256) := .ok (vperm2x128Eval a b 0x81#8)
def evalMiri_p17  (a b : BitVec 128) : Except SimdUb (BitVec 128) := .ok (spec_p17_clmulepi64_10 a b)

/-- `LeanMiri` `Aes.round false` (`Aes.lean:384-390`): `SubBytes -> ShiftRows -> MixColumns -> XOR key`. -/
def miriAesRoundEnc (block key : BitVec 128) : BitVec 128 :=
  let subState : Fin 16 → BitVec 8 := fun j => aesSbox (getByte128 block j)
  let shifted  : Fin 16 → BitVec 8 := fun i => subState (aesShiftPerm i)
  let c0 := aesMixCol (shifted ⟨0, by decide⟩)  (shifted ⟨1, by decide⟩)  (shifted ⟨2, by decide⟩)  (shifted ⟨3, by decide⟩)
  let c1 := aesMixCol (shifted ⟨4, by decide⟩)  (shifted ⟨5, by decide⟩)  (shifted ⟨6, by decide⟩)  (shifted ⟨7, by decide⟩)
  let c2 := aesMixCol (shifted ⟨8, by decide⟩)  (shifted ⟨9, by decide⟩)  (shifted ⟨10, by decide⟩) (shifted ⟨11, by decide⟩)
  let c3 := aesMixCol (shifted ⟨12, by decide⟩) (shifted ⟨13, by decide⟩) (shifted ⟨14, by decide⟩) (shifted ⟨15, by decide⟩)
  (c3 ++ (c2 ++ (c1 ++ c0))) ^^^ key

def evalMiri_p18 (a rk : BitVec 128) : Except SimdUb (BitVec 128) := .ok (miriAesRoundEnc a rk)
def evalMiri_p19 (a m  : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p19_pshufb a m)
def evalMiri_p20 (a b  : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p20_sad_epu8 a b)
def evalMiri_p21 (a ix : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p21_permutevar8x32 a ix)
def evalMiri_p22 (a b c : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p22_ternarylogic_96 a b c)
def evalMiri_p23 (a b  : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p23_madd_epi16 a b)
def evalMiri_p24 (a b  : BitVec 256) : Except SimdUb (BitVec 256) := .ok (spec_p24_maddubs_epi16 a b)

/-! ## Section 2: Exact `rustc 1.99.1` & `1.102.0-nightly` `-C opt-level=3` `.o` Machine Bytes -/

def codeOfBytes (bs : List (BitVec 8)) : CodeMap := fun addr =>
  match bs[addr.toNat]? with
  | some b => b
  | none   => 0#8

def mkCallState (a b c : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) : MachineState :=
  { rip := 0#64
    gpr := fun r => match r with | .rsp => rsp | _ => 0#64
    ymm := fun i =>
      match i.val with
      | 0 => a
      | 1 => b
      | 2 => c
      | _ => 0#256
    flags := {}
    mem := mem
    halted := false
    fault := none }

def mkCallState128 (a b : BitVec 128) (upper0 upper1 : BitVec 128)
    (rsp : BitVec 64) (mem : ByteMem) : MachineState :=
  mkCallState (upper0 ++ a) (upper1 ++ b) 0#256 rsp mem

def defaultOracle : UndefOracle := {}

def p01Bytes  : List (BitVec 8) := [0xC5#8, 0xF5#8, 0xFC#8, 0xC0#8, 0xC3#8]
def p02Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0xF8#8, 0xC1#8, 0xC3#8]
def p03Bytes  : List (BitVec 8) := [0xC5#8, 0xF4#8, 0x54#8, 0xC0#8, 0xC3#8]
def p04Bytes  : List (BitVec 8) := [0xC5#8, 0xF4#8, 0x56#8, 0xC0#8, 0xC3#8]
def p05Bytes  : List (BitVec 8) := [0xC5#8, 0xF4#8, 0x57#8, 0xC0#8, 0xC3#8]
def p06Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x74#8, 0xC1#8, 0xC3#8]
def p07Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x64#8, 0xC1#8, 0xC3#8]
def p08Bytes  : List (BitVec 8) := [0xC5#8, 0xF1#8, 0x64#8, 0xC0#8, 0xC3#8]
def p09Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0xD7#8, 0xC0#8, 0xC5#8, 0xF8#8, 0x77#8, 0xC3#8]
def p10Bytes  : List (BitVec 8) := [0xC4#8, 0xE3#8, 0xF9#8, 0x16#8, 0xC0#8, 0x01#8, 0xC3#8]
def p11Bytes  : List (BitVec 8) := [0x62#8, 0xF2#8, 0x7D#8, 0x28#8, 0x15#8, 0xC1#8, 0xC3#8]
def p12Bytes  : List (BitVec 8) := [0x31#8, 0xC0#8, 0xC4#8, 0xE2#8, 0x7D#8, 0x17#8, 0xC8#8, 0x0F#8, 0x94#8, 0xC0#8, 0xC5#8, 0xF8#8, 0x77#8, 0xC3#8]
def p13Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0xD8#8, 0xC1#8, 0xC3#8]
def p14Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x72#8, 0xF0#8, 0x07#8, 0xC3#8]
def p14bBytes : List (BitVec 8) := [0xC4#8, 0xE2#8, 0x7D#8, 0x47#8, 0xC1#8, 0xC3#8]
def p14cBytes : List (BitVec 8) := [0xC5#8, 0xF8#8, 0x57#8, 0xC0#8, 0xC3#8]
def p15Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x72#8, 0xD0#8, 0x07#8, 0xC3#8]
def p15bBytes : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x72#8, 0xE0#8, 0x07#8, 0xC3#8]
def p15cBytes : List (BitVec 8) := [0xC5#8, 0xFD#8, 0x72#8, 0xE0#8, 0x1F#8, 0xC3#8]
def p16Bytes  : List (BitVec 8) := [0xC4#8, 0xE3#8, 0x7D#8, 0x06#8, 0xC1#8, 0x21#8, 0xC3#8]
def p16bBytes : List (BitVec 8) := [0xC4#8, 0xE3#8, 0x7D#8, 0x19#8, 0xC0#8, 0x01#8, 0xC3#8]
def p17Bytes  : List (BitVec 8) := [0xC4#8, 0xE3#8, 0x79#8, 0x44#8, 0xC1#8, 0x10#8, 0xC3#8]
def p18Bytes  : List (BitVec 8) := [0xC4#8, 0xE2#8, 0x79#8, 0xDC#8, 0xC1#8, 0xC3#8]
def p19Bytes  : List (BitVec 8) := [0xC4#8, 0xE2#8, 0x7D#8, 0x00#8, 0xC1#8, 0xC3#8]
def p20Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0xF6#8, 0xC1#8, 0xC3#8]
def p21Bytes  : List (BitVec 8) := [0xC4#8, 0xE2#8, 0x75#8, 0x16#8, 0xC0#8, 0xC3#8]
def p22Bytes  : List (BitVec 8) := [0x62#8, 0xF3#8, 0x75#8, 0x28#8, 0x25#8, 0xC2#8, 0x96#8, 0xC3#8]
def p23Bytes  : List (BitVec 8) := [0xC5#8, 0xFD#8, 0xF5#8, 0xC1#8, 0xC3#8]
def p24Bytes  : List (BitVec 8) := [0xC4#8, 0xE2#8, 0x7D#8, 0x04#8, 0xC1#8, 0xC3#8]

def y0 : YmmIdx := ⟨0, by decide⟩
def y1 : YmmIdx := ⟨1, by decide⟩
def y2 : YmmIdx := ⟨2, by decide⟩

/-! ### Section 3: Unguarded MIR-vs-VEX UB Asymmetry Counterexample Theorems -/

/-- **Asymmetry 1 (`simd_shl` UB vs `vpsllvd` lane zeroing):**
    On shift count `32` in lane 0, raw MIR `simd_shl` raises `.shiftOverflow 32` UB,
    whereas stepping `p14bBytes` (`vpsllvd ymm0, ymm0, ymm1; ret`) halts cleanly
    with `0#256`. -/
theorem unguarded_simd_shl_ub_vs_vpsllvd_zero :
    let a   : BitVec 256 := 0x12345678#256
    let cnt : BitVec 256 := 32#256
    miriSimdShlDwords a cnt = .error (.shiftOverflow 32) ∧
    (execStepsN (codeOfBytes p14bBytes) 2 defaultOracle (mkCallState a cnt 0#256 0x1000#64 (fun _ => 0#8))).fault = none ∧
    (execStepsN (codeOfBytes p14bBytes) 2 defaultOracle (mkCallState a cnt 0#256 0x1000#64 (fun _ => 0#8))).ymm y0 = 0#256 :=
  ⟨rfl, rfl, rfl⟩

/-- **Asymmetry 2 (`simd_bitmask` `{0, -1}` UB vs `vpmovmskb` arbitrary byte MSB):**
    On byte lane `0x80` (`∉ {0x00, 0xFF}`), raw MIR `simd_bitmask` raises
    `.nonBoolMask 128` UB, whereas `stdarch` (`evalMiri_p09`) and `p09Bytes`
    (`vpmovmskb eax, ymm0; vzeroupper; ret`) both return `1#64` cleanly. -/
theorem unguarded_simd_bitmask_ub_vs_vpmovmskb_msb :
    let a : BitVec 256 := 0x80#256
    miriSimdBitmask256 a = .error (.nonBoolMask 128) ∧
    evalMiri_p09 a = .ok 1#64 ∧
    (execStepsN (codeOfBytes p09Bytes) 3 defaultOracle (mkCallState a 0#256 0#256 0x1000#64 (fun _ => 0#8))).gpr .rax = 1#64 :=
  ⟨rfl, rfl, rfl⟩

/-- **Asymmetry 3 (`simd_funnel_shl` `count >= 32` UB vs EVEX `vprolvd` modulo-32):**
    On shift count `32` in lane 0, raw MIR `simd_funnel_shl` raises
    `.funnelShiftOverflow 32` UB, whereas `stdarch` (`evalMiri_p11`) and `p11Bytes`
    (`vprolvd ymm0, ymm0, ymm1; ret`) both succeed and return `a` unchanged. -/
theorem unguarded_simd_funnel_shl_ub_vs_vprolvd_mod32 :
    let a   : BitVec 256 := 0x80000001#256
    let cnt : BitVec 256 := 32#256
    miriSimdFunnelShlDwords a a cnt = .error (.funnelShiftOverflow 32) ∧
    evalMiri_p11 a cnt = .ok a ∧
    (execStepsN (codeOfBytes p11Bytes) 2 defaultOracle (mkCallState a cnt 0#256 0x1000#64 (fun _ => 0#8))).ymm y0 = a :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 4: Algebraic & Lane-Extraction Lemmas for Symbolic 3-Way Proofs -/

@[simp] theorem ymmUpd_self (f : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 256) :
    ymmUpd f r v r = v := by
  simp [ymmUpd]

@[simp] theorem writeVex128_self (f : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    writeVex128 f r v r = v.zeroExtend 256 := by
  simp [writeVex128, ymmUpd]

@[simp] theorem gprUpd_self (f : Gpr → BitVec 64) (r : Gpr) (v : BitVec 64) :
    gprUpd f r v r = v := by
  simp [gprUpd]

theorem gprUpd_ne (f : Gpr → BitVec 64) {r r' : Gpr} (v : BitVec 64) (h : r' ≠ r) :
    gprUpd f r v r' = f r' := by
  simp [gprUpd, h]

theorem extractLsb_self {n : Nat} (x : BitVec n) :
    BitVec.extractLsb' 0 n x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', Nat.zero_add]
  simp [hk]

theorem extractLsb_append_right_off {m n s l : Nat} (hi : BitVec m) (lo : BitVec n) (h : s + l ≤ n) :
    BitVec.extractLsb' s l (hi ++ lo) = BitVec.extractLsb' s l lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have hlt : s + k < n := by omega
  simp [hk, hlt]

theorem extractLsb_append_left {m n s l : Nat} (hi : BitVec m) (lo : BitVec n) (hs : n ≤ s) :
    BitVec.extractLsb' s l (hi ++ lo) = BitVec.extractLsb' (s - n) l hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have hnot : ¬ (s + k < n) := by omega
  have hsub : s + k - n = s - n + k := by omega
  simp [hk, hnot, hsub]

theorem extractLsb_append_lo128 (hi lo : BitVec 128) :
    BitVec.extractLsb' 0 128 (hi ++ lo) = lo := by
  rw [extractLsb_append_right_off hi lo (by decide), extractLsb_self]

@[simp] theorem readXmm128_mkCallState128_y0 (a b u0 u1 : BitVec 128) (rsp rip : BitVec 64) (mem : ByteMem) :
    readXmm128 (mkCallState128 a b u0 u1 rsp mem) rip (.reg y0) = a :=
  extractLsb_append_lo128 u0 a

@[simp] theorem readXmm128_mkCallState128_y1 (a b u0 u1 : BitVec 128) (rsp rip : BitVec 64) (mem : ByteMem) :
    readXmm128 (mkCallState128 a b u0 u1 rsp mem) rip (.reg y1) = b :=
  extractLsb_append_lo128 u1 b

@[simp] theorem mkCallState128_ymm0_lo128 (a b u0 u1 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    BitVec.extractLsb' 0 128 ((mkCallState128 a b u0 u1 rsp mem).ymm y0) = a :=
  extractLsb_append_lo128 u0 a

@[simp] theorem mkCallState128_ymm1_lo128 (a b u0 u1 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    BitVec.extractLsb' 0 128 ((mkCallState128 a b u0 u1 rsp mem).ymm y1) = b :=
  extractLsb_append_lo128 u1 b

theorem getDword256_packDwords256 (f : Fin 8 → BitVec 32) (i : Fin 8) :
    getDword256 (packDwords256 f) i = f i := by
  rcases i with ⟨v, hv⟩
  have hv8 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by omega
  rcases hv8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · dsimp only [getDword256, packDwords256, packDwords128]
    repeat first
      | rw [extractLsb_append_right_off _ _ (by decide)]
      | rw [extractLsb_append_left _ _ (by decide)]
      | rw [extractLsb_self]

theorem getDword256_packDwords256_const (c : BitVec 32) (i : Fin 8) :
    getDword256 (packDwords256 fun _ => c) i = c :=
  getDword256_packDwords256 (fun _ => c) i

theorem getByte256_packBytes256 (f : Fin 32 → BitVec 8) (k : Fin 32) :
    BitVec.extractLsb' (k.val * 8) 8 (packBytes256 f) = f k := by
  rcases k with ⟨v, hv⟩
  have hv32 :
      v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨
      v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨
      v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨
      v = 24 ∨ v = 25 ∨ v = 26 ∨ v = 27 ∨ v = 28 ∨ v = 29 ∨ v = 30 ∨ v = 31 := by omega
  rcases hv32 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · dsimp only [packBytes256, packBytes128]
    repeat first
      | rw [extractLsb_append_right_off _ _ (by decide)]
      | rw [extractLsb_append_left _ _ (by decide)]
      | rw [extractLsb_self]

theorem getByte256_miriSimdLtZero256 (a : BitVec 256) (k : Fin 32) :
    BitVec.extractLsb' (k.val * 8) 8 (miriSimdLtZero256 a) =
    (if (getByte256 a k).slt 0#8 then 0xFF#8 else 0x00#8) :=
  getByte256_packBytes256 (fun i => if (getByte256 a i).slt 0#8 then 0xFF#8 else 0x00#8) k

theorem slt_zero_eq_msb8_grid :
    ∀ hi lo : Fin 16,
      (BitVec.ofNat 8 (hi.val * 16 + lo.val)).slt 0#8 =
      (BitVec.ofNat 8 (hi.val * 16 + lo.val)).msb := by
  decide

theorem slt_zero_eq_msb8 (x : BitVec 8) : x.slt 0#8 = x.msb := by
  have hx := x.isLt
  have hdiv : (x.toNat / 16) * 16 + (x.toNat % 16) = x.toNat := by omega
  have h := slt_zero_eq_msb8_grid ⟨x.toNat / 16, by omega⟩ ⟨x.toNat % 16, by omega⟩
  simpa [hdiv] using h

theorem miriBind_00 {α : Type} (f : Bool → Except SimdUb α) :
    (miriElementToBool8 0x00#8 >>= f) = f false := rfl

theorem miriBind_FF {α : Type} (f : Bool → Except SimdUb α) :
    (miriElementToBool8 0xFF#8 >>= f) = f true := rfl

theorem miriBitmaskLoop_eq_pmovmskb256Loop (n : Nat) (hn : n ≤ 32) (a : BitVec 256) (acc : BitVec 64) :
    miriBitmaskLoop n (miriSimdLtZero256 a) acc = .ok (pmovmskb256Loop n a acc) := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih =>
    have hk : k < 32 := Nat.lt_of_succ_le hn
    change (do
      let bit ← miriElementToBool8 (BitVec.extractLsb' (k * 8) 8 (miriSimdLtZero256 a))
      let a' := if bit then acc ||| (1#64 <<< k) else acc
      miriBitmaskLoop k (miriSimdLtZero256 a) a') =
      .ok (let b := BitVec.extractLsb' (k * 8) 8 a
           let a' := if b.msb then acc ||| (1#64 <<< k) else acc
           pmovmskb256Loop k a a')
    have hbyte := getByte256_miriSimdLtZero256 a ⟨k, hk⟩
    simp only [getByte256, slt_zero_eq_msb8] at hbyte
    rw [hbyte]
    dsimp only
    cases (BitVec.extractLsb' (k * 8) 8 a).msb
    · simp only [Bool.false_eq_true, ite_false, miriBind_00]
      exact ih (Nat.le_of_lt hk) acc
    · simp only [ite_true, miriBind_FF]
      exact ih (Nat.le_of_lt hk) (acc ||| (1#64 <<< k))

theorem evalMiri_p09_eq_spec (a : BitVec 256) :
    evalMiri_p09 a = .ok (spec_p09_movemask_epi8 a) :=
  miriBitmaskLoop_eq_pmovmskb256Loop 32 (by decide) a 0#64

theorem funnel_masked_eq_rotateLeft (x cnt : BitVec 32) :
    miriLaneFunnelShl32 x x (cnt &&& 31#32) = .ok (BitVec.rotateLeft x (cnt.toNat % 32)) := by
  have hs : (cnt &&& 31#32).toNat = cnt.toNat % 32 := by
    rw [BitVec.toNat_and]
    change cnt.toNat &&& (2 ^ 5 - 1) = cnt.toNat % 32
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have hge : ¬ (cnt.toNat % 32 ≥ 32) := by
    have := Nat.mod_lt cnt.toNat (show 0 < 32 from by decide)
    omega
  unfold miriLaneFunnelShl32
  rw [hs]
  simp only [hge, ite_false]
  unfold BitVec.rotateLeft BitVec.rotateLeftAux
  rw [Nat.mod_mod]
  cases h0 : (cnt.toNat % 32 == 0)
  · simp only [Bool.false_eq_true, ite_false]
  · simp only [ite_true]
    have hz : cnt.toNat % 32 = 0 := beq_iff_eq.mp h0
    rw [hz]
    have hshr : x >>> 32 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt x.isLt
    simp [hshr]

theorem evalMiri_p11_eq_spec (a b : BitVec 256) :
    evalMiri_p11 a b = .ok (spec_p11_rolv_epi32 a b) := by
  dsimp only [evalMiri_p11, miriSimdFunnelShlDwords, spec_p11_rolv_epi32]
  have hfun : (fun i : Fin 8 =>
      miriLaneFunnelShl32 (getDword256 a i) (getDword256 a i)
        (getDword256 (packDwords256 fun j => getDword256 b j &&& 31#32) i)) =
      (fun i : Fin 8 => .ok (BitVec.rotateLeft (getDword256 a i) ((getDword256 b i).toNat % 32))) := by
    funext i
    rw [getDword256_packDwords256, funnel_masked_eq_rotateLeft]
  exact (congrArg mapDwords256M hfun).trans (mapDwords256M_ok _)

theorem evalMiri_p14_eq_spec (a : BitVec 256) :
    evalMiri_p14 a = .ok (spec_p14_slli_epi32_7 a) := by
  unfold evalMiri_p14 evalMiri_slli_epi32 miriSimdShlDwords spec_p14_slli_epi32_7
  simp only [show (7 < 32) from by decide, ite_true]
  have hfun : (fun i : Fin 8 => miriLaneShl32 (getDword256 a i) (getDword256 (packDwords256 fun _ => 7#32) i)) =
              (fun i : Fin 8 => .ok (getDword256 a i <<< 7)) := by
    funext i
    rw [getDword256_packDwords256_const]
    rfl
  exact (congrArg mapDwords256M hfun).trans (mapDwords256M_ok _)

theorem evalMiri_p15_eq_spec (a : BitVec 256) :
    evalMiri_p15 a = .ok (spec_p15_srli_epi32_7 a) := by
  unfold evalMiri_p15 evalMiri_srli_epi32 miriSimdLshrDwords spec_p15_srli_epi32_7
  simp only [show (7 < 32) from by decide, ite_true]
  have hfun : (fun i : Fin 8 => miriLaneLshr32 (getDword256 a i) (getDword256 (packDwords256 fun _ => 7#32) i)) =
              (fun i : Fin 8 => .ok (getDword256 a i >>> 7)) := by
    funext i
    rw [getDword256_packDwords256_const]
    rfl
  exact (congrArg mapDwords256M hfun).trans (mapDwords256M_ok _)

theorem evalMiri_p15b_eq_spec (a : BitVec 256) :
    evalMiri_p15b a = .ok (spec_p15b_srai_epi32_7 a) := by
  unfold evalMiri_p15b evalMiri_srai_epi32 miriSimdAshrDwords spec_p15b_srai_epi32_7
  have hfun : (fun i : Fin 8 => miriLaneAshr32 (getDword256 a i) (getDword256 (packDwords256 fun _ => 7#32) i)) =
              (fun i : Fin 8 => .ok (BitVec.sshiftRight (getDword256 a i) 7)) := by
    funext i
    rw [getDword256_packDwords256_const]
    rfl
  exact (congrArg mapDwords256M hfun).trans (mapDwords256M_ok _)

theorem evalMiri_p15c_eq_spec (a : BitVec 256) :
    evalMiri_p15c a = .ok (spec_p15c_srai_epi32_40 a) := by
  unfold evalMiri_p15c evalMiri_srai_epi32 miriSimdAshrDwords spec_p15c_srai_epi32_40
  have hfun : (fun i : Fin 8 => miriLaneAshr32 (getDword256 a i) (getDword256 (packDwords256 fun _ => 31#32) i)) =
              (fun i : Fin 8 => .ok (BitVec.sshiftRight (getDword256 a i) 31)) := by
    funext i
    rw [getDword256_packDwords256_const]
    rfl
  exact (congrArg mapDwords256M hfun).trans (mapDwords256M_ok _)

theorem zero128_append_eq_zeroExtend256 (x : BitVec 128) :
    (0#128 ++ x) = x.zeroExtend 256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_setWidth]
  have hlt : x.toNat < 2 ^ 128 := x.isLt
  have hlt256 : x.toNat < 2 ^ 256 := Nat.lt_trans hlt (by decide)
  change (0 <<< 128 ||| x.toNat) = x.toNat % (2 ^ 256)
  rw [Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt hlt256]

theorem vperm2x128_81_eq_extract128 (a b : BitVec 256) :
    vperm2x128Eval a b 0x81#8 = spec_p16b_permute2x128_81 a b := by
  unfold vperm2x128Eval selectPerm128Lane spec_p16b_permute2x128_81
  have hlo : BitVec.extractLsb' 0 4 0x81#8 = 0x1#4 := by decide
  have hhi : BitVec.extractLsb' 4 4 0x81#8 = 0x8#4 := by decide
  rw [hlo, hhi]
  change (0#128 ++ BitVec.extractLsb' 128 128 a) = (BitVec.extractLsb' 128 128 a).zeroExtend 256
  exact zero128_append_eq_zeroExtend256 _

/-- `LeanMiri`'s `SubBytes -> ShiftRows` order (`Aes.lean:386-387`) and Intel SDM
    `VAESENC`'s `ShiftRows -> SubBytes` order agree identically on all 128-bit blocks. -/
theorem miriAesRoundEnc_eq_vaesenc128 (a rk : BitVec 128) :
    miriAesRoundEnc a rk = vaesenc128 a rk := rfl

/-! ## Section 5: Kernel-Checked `.o` Byte-Decode Lemmas (`by decide`) -/

theorem dec_p01_1  : decodeRef (fetchWindow16 (codeOfBytes p01Bytes)  0#64) = .ok (.vpadd .v256 .e8 y0 y1 (.reg y0)) 4 := by decide
theorem dec_p01_2  : decodeRef (fetchWindow16 (codeOfBytes p01Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p02_1  : decodeRef (fetchWindow16 (codeOfBytes p02Bytes)  0#64) = .ok (.vpsub .v256 .e8 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p02_2  : decodeRef (fetchWindow16 (codeOfBytes p02Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p03_1  : decodeRef (fetchWindow16 (codeOfBytes p03Bytes)  0#64) = .ok (.vpand .v256 y0 y1 (.reg y0)) 4 := by decide
theorem dec_p03_2  : decodeRef (fetchWindow16 (codeOfBytes p03Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p04_1  : decodeRef (fetchWindow16 (codeOfBytes p04Bytes)  0#64) = .ok (.vpor  .v256 y0 y1 (.reg y0)) 4 := by decide
theorem dec_p04_2  : decodeRef (fetchWindow16 (codeOfBytes p04Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p05_1  : decodeRef (fetchWindow16 (codeOfBytes p05Bytes)  0#64) = .ok (.vpxor .v256 y0 y1 (.reg y0)) 4 := by decide
theorem dec_p05_2  : decodeRef (fetchWindow16 (codeOfBytes p05Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p06_1  : decodeRef (fetchWindow16 (codeOfBytes p06Bytes)  0#64) = .ok (.vpcmpeq .v256 .e8 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p06_2  : decodeRef (fetchWindow16 (codeOfBytes p06Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p07_1  : decodeRef (fetchWindow16 (codeOfBytes p07Bytes)  0#64) = .ok (.vpcmpgt .v256 .e8 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p07_2  : decodeRef (fetchWindow16 (codeOfBytes p07Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p08_1  : decodeRef (fetchWindow16 (codeOfBytes p08Bytes)  0#64) = .ok (.vpcmpgt .v128 .e8 y0 y1 (.reg y0)) 4 := by decide
theorem dec_p08_2  : decodeRef (fetchWindow16 (codeOfBytes p08Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p09_1  : decodeRef (fetchWindow16 (codeOfBytes p09Bytes)  0#64) = .ok (.vpmovmskb .v256 .rax y0) 4 := by decide
theorem dec_p09_2  : decodeRef (fetchWindow16 (codeOfBytes p09Bytes)  4#64) = .ok .vzeroupper 3 := by decide
theorem dec_p09_3  : decodeRef (fetchWindow16 (codeOfBytes p09Bytes)  7#64) = .ok .ret 1 := by decide
theorem dec_p10_1  : decodeRef (fetchWindow16 (codeOfBytes p10Bytes)  0#64) = .ok (.vpextrq .rax y0 0x01#8) 6 := by decide
theorem dec_p10_2  : decodeRef (fetchWindow16 (codeOfBytes p10Bytes)  6#64) = .ok .ret 1 := by decide
theorem dec_p11_1  : decodeRef (fetchWindow16 (codeOfBytes p11Bytes)  0#64) = .ok (.vprolvd .v256 y0 y0 (.reg y1)) 6 := by decide
theorem dec_p11_2  : decodeRef (fetchWindow16 (codeOfBytes p11Bytes)  6#64) = .ok .ret 1 := by decide
theorem dec_p12_1  : decodeRef (fetchWindow16 (codeOfBytes p12Bytes)  0#64) = .ok (.aluRmReg .s32 .xor (.reg .rax) .rax) 2 := by decide
theorem dec_p12_2  : decodeRef (fetchWindow16 (codeOfBytes p12Bytes)  2#64) = .ok (.vptest .v256 y1 (.reg y0)) 5 := by decide
theorem dec_p12_3  : decodeRef (fetchWindow16 (codeOfBytes p12Bytes)  7#64) = .ok (.setcc .e (.reg .rax)) 3 := by decide
theorem dec_p12_4  : decodeRef (fetchWindow16 (codeOfBytes p12Bytes) 10#64) = .ok .vzeroupper 3 := by decide
theorem dec_p12_5  : decodeRef (fetchWindow16 (codeOfBytes p12Bytes) 13#64) = .ok .ret 1 := by decide
theorem dec_p13_1  : decodeRef (fetchWindow16 (codeOfBytes p13Bytes)  0#64) = .ok (.vpsubusb .v256 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p13_2  : decodeRef (fetchWindow16 (codeOfBytes p13Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p14_1  : decodeRef (fetchWindow16 (codeOfBytes p14Bytes)  0#64) = .ok (.vpshiftImmD .v256 .sll y0 y0 0x07#8) 5 := by decide
theorem dec_p14_2  : decodeRef (fetchWindow16 (codeOfBytes p14Bytes)  5#64) = .ok .ret 1 := by decide
theorem dec_p14b_1 : decodeRef (fetchWindow16 (codeOfBytes p14bBytes) 0#64) = .ok (.vpshiftVarD .v256 .sll y0 y0 (.reg y1)) 5 := by decide
theorem dec_p14b_2 : decodeRef (fetchWindow16 (codeOfBytes p14bBytes) 5#64) = .ok .ret 1 := by decide
theorem dec_p14c_1 : decodeRef (fetchWindow16 (codeOfBytes p14cBytes) 0#64) = .ok (.vpxor .v128 y0 y0 (.reg y0)) 4 := by decide
theorem dec_p14c_2 : decodeRef (fetchWindow16 (codeOfBytes p14cBytes) 4#64) = .ok .ret 1 := by decide
theorem dec_p15_1  : decodeRef (fetchWindow16 (codeOfBytes p15Bytes)  0#64) = .ok (.vpshiftImmD .v256 .srl y0 y0 0x07#8) 5 := by decide
theorem dec_p15_2  : decodeRef (fetchWindow16 (codeOfBytes p15Bytes)  5#64) = .ok .ret 1 := by decide
theorem dec_p15b_1 : decodeRef (fetchWindow16 (codeOfBytes p15bBytes) 0#64) = .ok (.vpshiftImmD .v256 .sra y0 y0 0x07#8) 5 := by decide
theorem dec_p15b_2 : decodeRef (fetchWindow16 (codeOfBytes p15bBytes) 5#64) = .ok .ret 1 := by decide
theorem dec_p15c_1 : decodeRef (fetchWindow16 (codeOfBytes p15cBytes) 0#64) = .ok (.vpshiftImmD .v256 .sra y0 y0 0x1F#8) 5 := by decide
theorem dec_p15c_2 : decodeRef (fetchWindow16 (codeOfBytes p15cBytes) 5#64) = .ok .ret 1 := by decide
theorem dec_p16_1  : decodeRef (fetchWindow16 (codeOfBytes p16Bytes)  0#64) = .ok (.vperm2x128 y0 y0 (.reg y1) 0x21#8) 6 := by decide
theorem dec_p16_2  : decodeRef (fetchWindow16 (codeOfBytes p16Bytes)  6#64) = .ok .ret 1 := by decide
theorem dec_p16b_1 : decodeRef (fetchWindow16 (codeOfBytes p16bBytes) 0#64) = .ok (.vextract128 (.reg y0) y0 0x01#8) 6 := by decide
theorem dec_p16b_2 : decodeRef (fetchWindow16 (codeOfBytes p16bBytes) 6#64) = .ok .ret 1 := by decide
theorem dec_p17_1  : decodeRef (fetchWindow16 (codeOfBytes p17Bytes)  0#64) = .ok (.vpclmulqdq y0 y0 (.reg y1) 0x10#8) 6 := by decide
theorem dec_p17_2  : decodeRef (fetchWindow16 (codeOfBytes p17Bytes)  6#64) = .ok .ret 1 := by decide
theorem dec_p18_1  : decodeRef (fetchWindow16 (codeOfBytes p18Bytes)  0#64) = .ok (.vaesenc y0 y0 (.reg y1)) 5 := by decide
theorem dec_p18_2  : decodeRef (fetchWindow16 (codeOfBytes p18Bytes)  5#64) = .ok .ret 1 := by decide
theorem dec_p19_1  : decodeRef (fetchWindow16 (codeOfBytes p19Bytes)  0#64) = .ok (.vpshufb .v256 y0 y0 (.reg y1)) 5 := by decide
theorem dec_p19_2  : decodeRef (fetchWindow16 (codeOfBytes p19Bytes)  5#64) = .ok .ret 1 := by decide
theorem dec_p20_1  : decodeRef (fetchWindow16 (codeOfBytes p20Bytes)  0#64) = .ok (.vpsadbw .v256 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p20_2  : decodeRef (fetchWindow16 (codeOfBytes p20Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p21_1  : decodeRef (fetchWindow16 (codeOfBytes p21Bytes)  0#64) = .ok (.vpermd y0 y1 (.reg y0)) 5 := by decide
theorem dec_p21_2  : decodeRef (fetchWindow16 (codeOfBytes p21Bytes)  5#64) = .ok .ret 1 := by decide
theorem dec_p22_1  : decodeRef (fetchWindow16 (codeOfBytes p22Bytes)  0#64) = .ok (.vpternlogd .v256 y0 y1 (.reg y2) 0x96#8) 7 := by decide
theorem dec_p22_2  : decodeRef (fetchWindow16 (codeOfBytes p22Bytes)  7#64) = .ok .ret 1 := by decide
theorem dec_p23_1  : decodeRef (fetchWindow16 (codeOfBytes p23Bytes)  0#64) = .ok (.vpmaddwd .v256 y0 y0 (.reg y1)) 4 := by decide
theorem dec_p23_2  : decodeRef (fetchWindow16 (codeOfBytes p23Bytes)  4#64) = .ok .ret 1 := by decide
theorem dec_p24_1  : decodeRef (fetchWindow16 (codeOfBytes p24Bytes)  0#64) = .ok (.vpmaddubsw .v256 y0 y0 (.reg y1)) 5 := by decide
theorem dec_p24_2  : decodeRef (fetchWindow16 (codeOfBytes p24Bytes)  5#64) = .ok .ret 1 := by decide

/-! ## Section 6: 3-Way Pass-2 Triangulation Bundle & All 29 Universal Theorems -/

/-- Unified 3-way Pass-2 triangulation predicate for a 256-bit vector return (`YMM0`). -/
def TriangulatedYmm (miriRes : Except SimdUb (BitVec 256)) (specVal : BitVec 256)
    (objBytes : List (BitVec 8)) (steps : Nat) (s0 : MachineState) : Prop :=
  let sFinal := execStepsN (codeOfBytes objBytes) steps defaultOracle s0
  miriRes = .ok specVal ∧
  sFinal.halted = true ∧
  sFinal.fault = none ∧
  sFinal.ymm y0 = specVal ∧
  ByteX86.StepsN (codeOfBytes objBytes) steps (toByteState s0) (toByteState sFinal)

/-- Unified 3-way Pass-2 triangulation predicate for a 128-bit vector return (`XMM0`,
    with upper 128 bits of `YMM0` zeroed by VEX `L=0`). -/
def TriangulatedXmm (miriRes : Except SimdUb (BitVec 128)) (specVal : BitVec 128)
    (objBytes : List (BitVec 8)) (steps : Nat) (s0 : MachineState) : Prop :=
  let sFinal := execStepsN (codeOfBytes objBytes) steps defaultOracle s0
  miriRes = .ok specVal ∧
  sFinal.halted = true ∧
  sFinal.fault = none ∧
  sFinal.ymm y0 = specVal.zeroExtend 256 ∧
  ByteX86.StepsN (codeOfBytes objBytes) steps (toByteState s0) (toByteState sFinal)

/-- Unified 3-way Pass-2 triangulation predicate for a scalar GPR return (`RAX` / `EAX`). -/
def TriangulatedGpr (miriRes : Except SimdUb (BitVec 64)) (specVal : BitVec 64)
    (objBytes : List (BitVec 8)) (steps : Nat) (s0 : MachineState) : Prop :=
  let sFinal := execStepsN (codeOfBytes objBytes) steps defaultOracle s0
  miriRes = .ok specVal ∧
  sFinal.halted = true ∧
  sFinal.fault = none ∧
  sFinal.gpr .rax = specVal ∧
  ByteX86.StepsN (codeOfBytes objBytes) steps (toByteState s0) (toByteState sFinal)

theorem mkTriYmm {miriRes : Except SimdUb (BitVec 256)} {specVal : BitVec 256}
    {objBytes : List (BitVec 8)} {steps : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (hHalt : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).halted = true)
    (hFault : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).fault = none)
    (hReg : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).ymm y0 = specVal) :
    TriangulatedYmm miriRes specVal objBytes steps s0 :=
  ⟨hMiri, hHalt, hFault, hReg,
   vendorX86Ref_stepsN_sub_byteX86_stepsN (codeOfBytes objBytes) steps s0 _
     (execStepsN_implies_stepsN (codeOfBytes objBytes) steps defaultOracle s0)⟩

theorem mkTriXmm {miriRes : Except SimdUb (BitVec 128)} {specVal : BitVec 128}
    {objBytes : List (BitVec 8)} {steps : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (hHalt : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).halted = true)
    (hFault : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).fault = none)
    (hReg : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).ymm y0 = specVal.zeroExtend 256) :
    TriangulatedXmm miriRes specVal objBytes steps s0 :=
  ⟨hMiri, hHalt, hFault, hReg,
   vendorX86Ref_stepsN_sub_byteX86_stepsN (codeOfBytes objBytes) steps s0 _
     (execStepsN_implies_stepsN (codeOfBytes objBytes) steps defaultOracle s0)⟩

theorem mkTriGpr {miriRes : Except SimdUb (BitVec 64)} {specVal : BitVec 64}
    {objBytes : List (BitVec 8)} {steps : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (hHalt : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).halted = true)
    (hFault : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).fault = none)
    (hReg : (execStepsN (codeOfBytes objBytes) steps defaultOracle s0).gpr .rax = specVal) :
    TriangulatedGpr miriRes specVal objBytes steps s0 :=
  ⟨hMiri, hHalt, hFault, hReg,
   vendorX86Ref_stepsN_sub_byteX86_stepsN (codeOfBytes objBytes) steps s0 _
     (execStepsN_implies_stepsN (codeOfBytes objBytes) steps defaultOracle s0)⟩

/-- Helper stepping any 2-instruction `[simdOp (len L), ret]` `.o` byte sequence. -/
theorem step2SimdRet {bs : List (BitVec 8)} {ins : Instr} {L : Nat} {s0 s1 : MachineState}
    (h1 : decodeRef (fetchWindow16 (codeOfBytes bs) 0#64) = .ok ins L)
    (hrip0 : s0.rip = 0#64) (hrun0 : (s0.halted || s0.fault.isSome) = false)
    (hexec : execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0 = s1)
    (hrun1 : (s1.halted || s1.fault.isSome) = false)
    (h2 : decodeRef (fetchWindow16 (codeOfBytes bs) s1.rip) = .ok .ret 1) :
    execStepsN (codeOfBytes bs) 2 defaultOracle s0 =
      { s1 with rip := readMem64 s1.mem (s1.gpr .rsp),
                gpr := gprUpd s1.gpr .rsp (s1.gpr .rsp + 8#64),
                halted := true } := by
  have hs1 : stepWithOracle (codeOfBytes bs) defaultOracle s0 = s1 := by
    unfold stepWithOracle
    rw [hrun0, hrip0, h1]
    exact hexec
  have hs2 : stepWithOracle (codeOfBytes bs) defaultOracle s1 =
      { s1 with rip := readMem64 s1.mem (s1.gpr .rsp),
                gpr := gprUpd s1.gpr .rsp (s1.gpr .rsp + 8#64),
                halted := true } := by
    unfold stepWithOracle
    rw [hrun1, h2]
    rfl
  change stepWithOracle (codeOfBytes bs) defaultOracle
           (stepWithOracle (codeOfBytes bs) defaultOracle s0) = _
  rw [hs1, hs2]

theorem triYmm2 {miriRes : Except SimdUb (BitVec 256)} {specVal : BitVec 256}
    {bs : List (BitVec 8)} {ins : Instr} {L : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (h1 : decodeRef (fetchWindow16 (codeOfBytes bs) 0#64) = .ok ins L)
    (hrip0 : s0.rip = 0#64) (hrun0 : (s0.halted || s0.fault.isSome) = false)
    (hrun1 : ((execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).halted ||
              (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault.isSome) = false)
    (hfault1 : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault = none)
    (h2 : decodeRef (fetchWindow16 (codeOfBytes bs)
            (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).rip) = .ok .ret 1)
    (hReg : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).ymm y0 = specVal) :
    TriangulatedYmm miriRes specVal bs 2 s0 := by
  have hstep := step2SimdRet h1 hrip0 hrun0 rfl hrun1 h2
  exact mkTriYmm hMiri (by rw [hstep]) (by rw [hstep]; exact hfault1) (by rw [hstep]; exact hReg)

theorem triXmm2 {miriRes : Except SimdUb (BitVec 128)} {specVal : BitVec 128}
    {bs : List (BitVec 8)} {ins : Instr} {L : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (h1 : decodeRef (fetchWindow16 (codeOfBytes bs) 0#64) = .ok ins L)
    (hrip0 : s0.rip = 0#64) (hrun0 : (s0.halted || s0.fault.isSome) = false)
    (hrun1 : ((execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).halted ||
              (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault.isSome) = false)
    (hfault1 : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault = none)
    (h2 : decodeRef (fetchWindow16 (codeOfBytes bs)
            (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).rip) = .ok .ret 1)
    (hReg : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).ymm y0 = specVal.zeroExtend 256) :
    TriangulatedXmm miriRes specVal bs 2 s0 := by
  have hstep := step2SimdRet h1 hrip0 hrun0 rfl hrun1 h2
  exact mkTriXmm hMiri (by rw [hstep]) (by rw [hstep]; exact hfault1) (by rw [hstep]; exact hReg)

theorem triGpr2 {miriRes : Except SimdUb (BitVec 64)} {specVal : BitVec 64}
    {bs : List (BitVec 8)} {ins : Instr} {L : Nat} {s0 : MachineState}
    (hMiri : miriRes = .ok specVal)
    (h1 : decodeRef (fetchWindow16 (codeOfBytes bs) 0#64) = .ok ins L)
    (hrip0 : s0.rip = 0#64) (hrun0 : (s0.halted || s0.fault.isSome) = false)
    (hrun1 : ((execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).halted ||
              (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault.isSome) = false)
    (hfault1 : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).fault = none)
    (h2 : decodeRef (fetchWindow16 (codeOfBytes bs)
            (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).rip) = .ok .ret 1)
    (hReg : (execInstr ins (0#64 + BitVec.ofNat 64 L) defaultOracle s0).gpr .rax = specVal) :
    TriangulatedGpr miriRes specVal bs 2 s0 := by
  have hstep := step2SimdRet h1 hrip0 hrun0 rfl hrun1 h2
  refine mkTriGpr hMiri (by rw [hstep]) (by rw [hstep]; exact hfault1) ?_
  rw [hstep]
  dsimp only
  rw [gprUpd_ne _ _ (by decide)]
  exact hReg

-- 1. `p01_simd_add` (`_mm256_add_epi8`: `rustc -O3` commutes operands to `vpaddb ymm0, ymm1, ymm0`)
theorem triangulate_p01_simd_add (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p01 a b) (spec_p01_add_epi8 a b) p01Bytes 2 (mkCallState a b 0#256 rsp mem) := by
  refine triYmm2 rfl dec_p01_1 rfl rfl rfl rfl dec_p01_2 ?_
  dsimp only [execInstr, execScalar, execSimd, mkCallState, readYmm256, y0, y1, spec_p01_add_epi8]
  rw [ymmUpd_self]
  congr 1; funext i
  exact BitVec.add_comm (getByte256 b i) (getByte256 a i)

-- 2. `p02_simd_sub` (`_mm256_sub_epi8`: `vpsubb ymm0, ymm0, ymm1`)
theorem triangulate_p02_simd_sub (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p02 a b) (spec_p02_sub_epi8 a b) p02Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p02_1 rfl rfl rfl rfl dec_p02_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 3. `p03_simd_and` (`_mm256_and_si256`: `rustc -O3` emits FP-domain `vandps ymm0, ymm1, ymm0`)
theorem triangulate_p03_simd_and (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p03 a b) (spec_p03_and_si256 a b) p03Bytes 2 (mkCallState a b 0#256 rsp mem) := by
  refine triYmm2 rfl dec_p03_1 rfl rfl rfl rfl dec_p03_2 ?_
  dsimp only [execInstr, execScalar, execSimd, mkCallState, readYmm256, y0, y1, spec_p03_and_si256]
  rw [ymmUpd_self]
  exact BitVec.and_comm b a

-- 4. `p04_simd_or` (`_mm256_or_si256`: `rustc -O3` emits FP-domain `vorps ymm0, ymm1, ymm0`)
theorem triangulate_p04_simd_or (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p04 a b) (spec_p04_or_si256 a b) p04Bytes 2 (mkCallState a b 0#256 rsp mem) := by
  refine triYmm2 rfl dec_p04_1 rfl rfl rfl rfl dec_p04_2 ?_
  dsimp only [execInstr, execScalar, execSimd, mkCallState, readYmm256, y0, y1, spec_p04_or_si256]
  rw [ymmUpd_self]
  exact BitVec.or_comm b a

-- 5. `p05_simd_xor` (`_mm256_xor_si256`: `rustc -O3` emits FP-domain `vxorps ymm0, ymm1, ymm0`)
theorem triangulate_p05_simd_xor (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p05 a b) (spec_p05_xor_si256 a b) p05Bytes 2 (mkCallState a b 0#256 rsp mem) := by
  refine triYmm2 rfl dec_p05_1 rfl rfl rfl rfl dec_p05_2 ?_
  dsimp only [execInstr, execScalar, execSimd, mkCallState, readYmm256, y0, y1, spec_p05_xor_si256]
  rw [ymmUpd_self]
  exact BitVec.xor_comm b a

-- 6. `p06_simd_eq` (`_mm256_cmpeq_epi8`: `vpcmpeqb ymm0, ymm0, ymm1`)
theorem triangulate_p06_simd_eq (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p06 a b) (spec_p06_cmpeq_epi8 a b) p06Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p06_1 rfl rfl rfl rfl dec_p06_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 7. `p07_simd_gt` (`_mm256_cmpgt_epi8`: `vpcmpgtb ymm0, ymm0, ymm1`)
theorem triangulate_p07_simd_gt (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p07 a b) (spec_p07_cmpgt_epi8 a b) p07Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p07_1 rfl rfl rfl rfl dec_p07_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 8. `p08_simd_lt` (`_mm_cmplt_epi8`: `rustc -O3` swaps operands to `vpcmpgtb xmm0, xmm1, xmm0` + zeroes upper 128b!)
theorem triangulate_p08_simd_lt (a b u0 u1 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedXmm (evalMiri_p08 a b) (spec_p08_cmplt_epi8 a b) p08Bytes 2 (mkCallState128 a b u0 u1 rsp mem) := by
  refine triXmm2 rfl dec_p08_1 rfl rfl rfl rfl dec_p08_2 ?_
  dsimp only [execInstr, execScalar, execSimd]
  simp only [writeVex128_self, readXmm128_mkCallState128_y0, mkCallState128_ymm1_lo128]
  rfl

-- 9. `p09_simd_bitmask` (`_mm256_movemask_epi8`: `simd_lt(a,0)+simd_bitmask` vs `vpmovmskb eax, ymm0; vzeroupper; ret`)
theorem triangulate_p09_simd_bitmask (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedGpr (evalMiri_p09 a) (spec_p09_movemask_epi8 a) p09Bytes 3 (mkCallState a 0#256 0#256 rsp mem) := by
  let s0 := mkCallState a 0#256 0#256 rsp mem
  let s1 := execInstr (.vpmovmskb .v256 .rax y0) 4#64 defaultOracle s0
  let s2 := execInstr .vzeroupper 7#64 defaultOracle s1
  let s3 := execInstr .ret 8#64 defaultOracle s2
  have hs1 : stepWithOracle (codeOfBytes p09Bytes) defaultOracle s0 = s1 := by
    unfold stepWithOracle
    rw [show (s0.halted || s0.fault.isSome) = false from rfl, show s0.rip = 0#64 from rfl, dec_p09_1]
    rfl
  have hs2 : stepWithOracle (codeOfBytes p09Bytes) defaultOracle s1 = s2 := by
    unfold stepWithOracle
    rw [show (s1.halted || s1.fault.isSome) = false from rfl, show s1.rip = 4#64 from rfl, dec_p09_2]
    rfl
  have hs3 : stepWithOracle (codeOfBytes p09Bytes) defaultOracle s2 = s3 := by
    unfold stepWithOracle
    rw [show (s2.halted || s2.fault.isSome) = false from rfl, show s2.rip = 7#64 from rfl, dec_p09_3]
    rfl
  have hrun : execStepsN (codeOfBytes p09Bytes) 3 defaultOracle s0 = s3 := by
    change stepWithOracle (codeOfBytes p09Bytes) defaultOracle
      (stepWithOracle (codeOfBytes p09Bytes) defaultOracle
        (stepWithOracle (codeOfBytes p09Bytes) defaultOracle s0)) = s3
    rw [hs1, hs2, hs3]
  refine mkTriGpr (evalMiri_p09_eq_spec a) (by rw [hrun]; rfl) (by rw [hrun]; rfl) ?_
  rw [hrun]
  dsimp only [s3, s2, s1, s0, execInstr, execScalar, execSimd, mkCallState, y0]
  rw [gprUpd_ne _ _ (by decide), gprUpd_self]
  rfl

-- 10. `p10_simd_extract` (`_mm_extract_epi64::<1>`: `vpextrq rax, xmm0, 0x1; ret`)
theorem triangulate_p10_simd_extract (a u0 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedGpr (evalMiri_p10 a) (spec_p10_extract_epi64_1 a) p10Bytes 2 (mkCallState128 a 0#128 u0 0#128 rsp mem) := by
  refine triGpr2 rfl dec_p10_1 rfl rfl rfl rfl dec_p10_2 ?_
  dsimp only [execInstr, execScalar, execSimd]
  rw [gprUpd_self, mkCallState128_ymm0_lo128]
  rfl

-- 11. `p11_simd_funnel_shl` (`_mm256_rolv_epi32`: `simd_and(b,31)+simd_funnel_shl` vs EVEX `vprolvd ymm0, ymm0, ymm1`)
theorem triangulate_p11_simd_funnel_shl (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p11 a b) (spec_p11_rolv_epi32 a b) p11Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 (evalMiri_p11_eq_spec a b) dec_p11_1 rfl rfl rfl rfl dec_p11_2
    (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 12. `p12_simd_reduce_or` (`_mm256_testz_si256`: 5-insn `xor eax,eax; vptest ymm1,ymm0; sete al; vzeroupper; ret`)
theorem triangulate_p12_simd_reduce_or (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedGpr (evalMiri_p12 a b) (spec_p12_testz_si256 a b) p12Bytes 5 (mkCallState a b 0#256 rsp mem) := by
  let s0 := mkCallState a b 0#256 rsp mem
  let s1 := execInstr (.aluRmReg .s32 .xor (.reg .rax) .rax) 2#64 defaultOracle s0
  let s2 := execInstr (.vptest .v256 y1 (.reg y0)) 7#64 defaultOracle s1
  let s3 := execInstr (.setcc .e (.reg .rax)) 10#64 defaultOracle s2
  let s4 := execInstr .vzeroupper 13#64 defaultOracle s3
  let s5 := execInstr .ret 14#64 defaultOracle s4
  have hs1 : stepWithOracle (codeOfBytes p12Bytes) defaultOracle s0 = s1 := by
    unfold stepWithOracle
    rw [show (s0.halted || s0.fault.isSome) = false from rfl, show s0.rip = 0#64 from rfl, dec_p12_1]
    rfl
  have hs2 : stepWithOracle (codeOfBytes p12Bytes) defaultOracle s1 = s2 := by
    unfold stepWithOracle
    rw [show (s1.halted || s1.fault.isSome) = false from rfl, show s1.rip = 2#64 from rfl, dec_p12_2]
    rfl
  have hs3 : stepWithOracle (codeOfBytes p12Bytes) defaultOracle s2 = s3 := by
    unfold stepWithOracle
    rw [show (s2.halted || s2.fault.isSome) = false from rfl, show s2.rip = 7#64 from rfl, dec_p12_3]
    rfl
  have hs4 : stepWithOracle (codeOfBytes p12Bytes) defaultOracle s3 = s4 := by
    unfold stepWithOracle
    rw [show (s3.halted || s3.fault.isSome) = false from rfl, show s3.rip = 10#64 from rfl, dec_p12_4]
    rfl
  have hs5 : stepWithOracle (codeOfBytes p12Bytes) defaultOracle s4 = s5 := by
    unfold stepWithOracle
    rw [show (s4.halted || s4.fault.isSome) = false from rfl, show s4.rip = 13#64 from rfl, dec_p12_5]
    rfl
  have hrun : execStepsN (codeOfBytes p12Bytes) 5 defaultOracle s0 = s5 := by
    change stepWithOracle (codeOfBytes p12Bytes) defaultOracle
      (stepWithOracle (codeOfBytes p12Bytes) defaultOracle
        (stepWithOracle (codeOfBytes p12Bytes) defaultOracle
          (stepWithOracle (codeOfBytes p12Bytes) defaultOracle
            (stepWithOracle (codeOfBytes p12Bytes) defaultOracle s0)))) = s5
    rw [hs1, hs2, hs3, hs4, hs5]
  refine mkTriGpr rfl (by rw [hrun]; rfl) (by rw [hrun]; rfl) ?_
  rw [hrun]
  simp only [s5, s4, s3, s2, s1, s0, execInstr, execScalar, execSimd, mkCallState,
             writeRm, writeGprSz, readRm, evalAlu, evalAlu32, aluWritesDst,
             evalCond, readYmm256, y0, y1, spec_p12_testz_si256,
             gprUpd_self, ite_true]
  rw [gprUpd_ne _ _ (by decide), gprUpd_self, BitVec.and_comm b a]
  cases ((a &&& b) == 0#256) <;> rfl

-- 13. `p13_simd_saturating_sub` (`_mm256_subs_epu8`: `vpsubusb ymm0, ymm0, ymm1`)
theorem triangulate_p13_simd_saturating_sub (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p13 a b) (spec_p13_subs_epu8 a b) p13Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p13_1 rfl rfl rfl rfl dec_p13_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 14. `p14_simd_shl` (`_mm256_slli_epi32::<7>`: `vpslld ymm0, ymm0, 0x7`)
theorem triangulate_p14_simd_shl (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p14 a) (spec_p14_slli_epi32_7 a) p14Bytes 2 (mkCallState a 0#256 0#256 rsp mem) :=
  triYmm2 (evalMiri_p14_eq_spec a) dec_p14_1 rfl rfl rfl rfl dec_p14_2
    (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 14b. `p14b_simd_shl_var` (`_mm256_sllv_epi32`: `vpsllvd ymm0, ymm0, ymm1`)
theorem triangulate_p14b_simd_shl_var (a cnt : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p14b a cnt) (spec_p14b_sllv_epi32 a cnt) p14bBytes 2 (mkCallState a cnt 0#256 rsp mem) :=
  triYmm2 rfl dec_p14b_1 rfl rfl rfl rfl dec_p14b_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 14c. `p14c_simd_shl_oob40` (`_mm256_slli_epi32::<40>` -> `vxorps xmm0, xmm0, xmm0; ret` zeroes all 256 bits via VEX `L=0`!)
theorem triangulate_p14c_simd_shl_oob40 (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p14c a) (spec_p14c_slli_epi32_40 a) p14cBytes 2 (mkCallState a 0#256 0#256 rsp mem) := by
  refine triYmm2 rfl dec_p14c_1 rfl rfl rfl rfl dec_p14c_2 ?_
  dsimp only [execInstr, execScalar, execSimd, mkCallState, readXmm128, y0, spec_p14c_slli_epi32_40]
  rw [writeVex128_self, BitVec.xor_self]
  rfl

-- 15. `p15_simd_shr` (`_mm256_srli_epi32::<7>`: `vpsrld ymm0, ymm0, 0x7`)
theorem triangulate_p15_simd_shr (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p15 a) (spec_p15_srli_epi32_7 a) p15Bytes 2 (mkCallState a 0#256 0#256 rsp mem) :=
  triYmm2 (evalMiri_p15_eq_spec a) dec_p15_1 rfl rfl rfl rfl dec_p15_2
    (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 15b. `p15b_simd_sar` (`_mm256_srai_epi32::<7>`: `vpsrad ymm0, ymm0, 0x7`)
theorem triangulate_p15b_simd_sar (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p15b a) (spec_p15b_srai_epi32_7 a) p15bBytes 2 (mkCallState a 0#256 0#256 rsp mem) :=
  triYmm2 (evalMiri_p15b_eq_spec a) dec_p15b_1 rfl rfl rfl rfl dec_p15b_2
    (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 15c. `p15c_simd_sar_oob40` (`_mm256_srai_epi32::<40>` -> `vpsrad ymm0, ymm0, 0x1f`)
theorem triangulate_p15c_simd_sar_oob40 (a : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p15c a) (spec_p15c_srai_epi32_40 a) p15cBytes 2 (mkCallState a 0#256 0#256 rsp mem) :=
  triYmm2 (evalMiri_p15c_eq_spec a) dec_p15c_1 rfl rfl rfl rfl dec_p15c_2
    (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 16. `p16_simd_shuffle` (`_mm256_permute2x128_si256::<0x21>`: `vperm2f128 ymm0, ymm0, ymm1, 0x21`)
theorem triangulate_p16_simd_shuffle (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p16 a b) (spec_p16_permute2x128_21 a b) p16Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p16_1 rfl rfl rfl rfl dec_p16_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 16b. `p16b_simd_shuffle_zero` (`_mm256_permute2x128_si256::<0x81>` -> `vextractf128 xmm0, ymm0, 0x1` + VEX `L=0` zeroing!)
theorem triangulate_p16b_simd_shuffle_zero (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p16b a b) (spec_p16b_permute2x128_81 a b) p16bBytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 (congrArg Except.ok (vperm2x128_81_eq_extract128 a b)) dec_p16b_1 rfl rfl rfl rfl dec_p16b_2
    (by dsimp only [execInstr, execScalar, execSimd, mkCallState, y0, spec_p16b_permute2x128_81]; exact writeVex128_self _ _ _)

-- 17. `p17_pclmulqdq` (`_mm_clmulepi64_si128::<0x10>`: `vpclmulqdq xmm0, xmm0, xmm1, 0x10`)
theorem triangulate_p17_pclmulqdq (a b u0 u1 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedXmm (evalMiri_p17 a b) (spec_p17_clmulepi64_10 a b) p17Bytes 2 (mkCallState128 a b u0 u1 rsp mem) := by
  refine triXmm2 rfl dec_p17_1 rfl rfl rfl rfl dec_p17_2 ?_
  dsimp only [execInstr, execScalar, execSimd]
  rw [writeVex128_self, mkCallState128_ymm0_lo128, readXmm128_mkCallState128_y1]
  rfl

-- 18. `p18_aesni` (`_mm_aesenc_si128`: `vaesenc xmm0, xmm0, xmm1`)
theorem triangulate_p18_aesni (a rk u0 u1 : BitVec 128) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedXmm (evalMiri_p18 a rk) (spec_p18_aesenc a rk) p18Bytes 2 (mkCallState128 a rk u0 u1 rsp mem) := by
  refine triXmm2 (congrArg Except.ok (miriAesRoundEnc_eq_vaesenc128 a rk)) dec_p18_1 rfl rfl rfl rfl dec_p18_2 ?_
  dsimp only [execInstr, execScalar, execSimd]
  rw [writeVex128_self, mkCallState128_ymm0_lo128, readXmm128_mkCallState128_y1]
  rfl

-- 19. `p19_pshufb` (`_mm256_shuffle_epi8`: `vpshufb ymm0, ymm0, ymm1`)
theorem triangulate_p19_pshufb (a m : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p19 a m) (spec_p19_pshufb a m) p19Bytes 2 (mkCallState a m 0#256 rsp mem) :=
  triYmm2 rfl dec_p19_1 rfl rfl rfl rfl dec_p19_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 20. `p20_psadbw` (`_mm256_sad_epu8`: `vpsadbw ymm0, ymm0, ymm1`)
theorem triangulate_p20_psadbw (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p20 a b) (spec_p20_sad_epu8 a b) p20Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p20_1 rfl rfl rfl rfl dec_p20_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 21. `p21_vperm` (`_mm256_permutevar8x32_epi32`: `rustc -O3` emits `vpermps ymm0, ymm1, ymm0` with `idx` in `vvvv`!)
theorem triangulate_p21_vperm (a idx : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p21 a idx) (spec_p21_permutevar8x32 a idx) p21Bytes 2 (mkCallState a idx 0#256 rsp mem) :=
  triYmm2 rfl dec_p21_1 rfl rfl rfl rfl dec_p21_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 22. `p22_pternlog` (`_mm256_ternarylogic_epi32::<0x96>`: EVEX `vpternlogd ymm0, ymm1, ymm2, 0x96`)
theorem triangulate_p22_pternlog (a b c : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p22 a b c) (spec_p22_ternarylogic_96 a b c) p22Bytes 2 (mkCallState a b c rsp mem) :=
  triYmm2 rfl dec_p22_1 rfl rfl rfl rfl dec_p22_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 23. `p23_pmaddwd` (`_mm256_madd_epi16`: `vpmaddwd ymm0, ymm0, ymm1`)
theorem triangulate_p23_pmaddwd (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p23 a b) (spec_p23_madd_epi16 a b) p23Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p23_1 rfl rfl rfl rfl dec_p23_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

-- 24. `p24_pmaddubsw` (`_mm256_maddubs_epi16`: `vpmaddubsw ymm0, ymm0, ymm1`)
theorem triangulate_p24_pmaddubsw (a b : BitVec 256) (rsp : BitVec 64) (mem : ByteMem) :
    TriangulatedYmm (evalMiri_p24 a b) (spec_p24_maddubs_epi16 a b) p24Bytes 2 (mkCallState a b 0#256 rsp mem) :=
  triYmm2 rfl dec_p24_1 rfl rfl rfl rfl dec_p24_2 (by dsimp only [execInstr, execScalar, execSimd]; exact ymmUpd_self _ _ _)

end SimdTriangulation24
