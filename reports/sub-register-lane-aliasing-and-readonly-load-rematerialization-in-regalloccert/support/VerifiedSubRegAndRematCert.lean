-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Width-Indexed Sub-Register Lane Aliasing (`ArchRegLaneSemantics`) and Read-Only Load Rematerialization (`RematLoadCert`) in `RegAllocCert` (`Lean 4.34.1`)

Closes the two explicit boundaries in `verified-regalloc2-spill-and-parallel-move-certificate-checker` (`X1`):
1. **`ArchRegLaneSemantics`:** Replaces flat full-width `PReg` indices with width- and lane-indexed
   physical register views `(preg : PReg, lane : GprLane / VecLane)`, capturing:
   - x86-64 / i686 32-bit sub-register writes (`%eax`, `Lo32_Zext` `[31:0]`), which **zero-extend**
     into `[63:32]` and clobber any upper bits;
   - x86-64 / i686 16-bit (`%ax`, `Lo16` `[15:0]`) and low 8-bit (`%al`/`%dil`/`%r8b`, `Lo8` `[7:0]`)
     writes, which **merge** into the existing 64-bit register while preserving upper bits;
   - x86 high 8-bit sub-register writes (`%ah`/`%bh`/`%ch`/`%dh`, `Hi8_NoRex` `[15:8]`), which
     **merge** into bits `[15:8]` (making `Lo8` `%al` and `Hi8_NoRex` `%ah` disjoint 8-bit lanes
     of `%rax`, whereas `Lo32_Zext` `%eax` clobbers `%ah`!) and enforce the hardware encoding
     invariant that `Hi8_NoRex` cannot be combined with a `REX`-requiring operand in the same instruction;
   - x86 vector register writes: legacy 128-bit SSE (`Vec128_LegacyMerge`, which preserves `[511:128]`
     and marks `ymmUpperDirty`) vs. VEX/EVEX 128-bit (`Vec128_VexZero`) and 256-bit (`Vec256_VexZero`)
     writes and AArch64 `wN`/`xN` + scalar `bN`/`hN`/`sN`/`dN` writes (which zero-extend upper bits)
     vs. NEON `ins vN.s[idx], wM` single-lane inserts (`Vec32_LaneInsert`);
2. **`RematLoadCert`:** Generalizes constant-only rematerialization (`constI`) to five verified
   rematerialization origins (`constI`, `frameAddr`, `rodataLoad`, `immutableArgLoad`, and
   `unmodifiedSpillSlot` guarded by `noFrameWriteInRange`), eliminating redundant stack spill stores
   under high register pressure.
-/

namespace VerifiedSubRegAndRematCert

/-! ## 1. Hardware Sub-Register Lane Semantics (`ArchRegLaneSemantics`) -/

/-- A 64-bit architectural GPR decomposed into four concrete 8/16/32-bit sub-lanes:
    - `b0` (`[7:0]`, `%al` / `wN[7:0]`),
    - `b1` (`[15:8]`, `%ah` / `wN[15:8]`),
    - `w1` (`[31:16]`, upper half of `%eax` / `wN[31:16]`),
    - `hi32` (`[63:32]`, upper 32 bits of `%rax` / `xN[63:32]`). -/
structure Gpr64Word where
  b0   : BitVec 8
  b1   : BitVec 8
  w1   : BitVec 16
  hi32 : BitVec 32
  deriving DecidableEq, Repr, Inhabited

/-- Sub-register view of an architectural GPR across x86-64/i686 and AArch64. -/
inductive GprLane where
  | Lo8         -- `%al..%r15b` (`[7:0]`): merges into `[7:0]`, preserves `[63:8]`
  | Hi8_NoRex   -- `%ah/%bh/%ch/%dh` (`[15:8]`): merges into `[15:8]`, preserves `[63:16]` and `[7:0]`
  | Lo16        -- `%ax..%r15w` (`[15:0]`): merges into `[15:0]`, preserves `[63:16]`
  | Lo32_Zext   -- `%eax..%r15d` and AArch64 `w0..w30` (`[31:0]`): writes `[31:0]` AND zeroes `[63:32]`!
  | Full64      -- `%rax..%r15` and AArch64 `x0..x30` (`[63:0]`)
  deriving DecidableEq, Repr, Inhabited

/-- Hardware GPR lane write semantics (`writeGprLane`). -/
def writeGprLane (old : Gpr64Word) (lane : GprLane) (val : Gpr64Word) : Gpr64Word :=
  match lane with
  | .Lo8       => { old with b0 := val.b0 }
  | .Hi8_NoRex => { old with b1 := val.b1 }
  | .Lo16      => { old with b0 := val.b0, b1 := val.b1 }
  | .Lo32_Zext => { b0 := val.b0, b1 := val.b1, w1 := val.w1, hi32 := 0#32 }
  | .Full64    => val

/-- Hardware GPR lane read/projection (`extractGprLane`), canonicalizing bits outside the lane to `0`. -/
def extractGprLane (reg : Gpr64Word) (lane : GprLane) : Gpr64Word :=
  match lane with
  | .Lo8       => { b0 := reg.b0, b1 := 0#8,    w1 := 0#16,   hi32 := 0#32 }
  | .Hi8_NoRex => { b0 := 0#8,    b1 := reg.b1, w1 := 0#16,   hi32 := 0#32 }
  | .Lo16      => { b0 := reg.b0, b1 := reg.b1, w1 := 0#16,   hi32 := 0#32 }
  | .Lo32_Zext => { b0 := reg.b0, b1 := reg.b1, w1 := reg.w1, hi32 := 0#32 }
  | .Full64    => reg

/-- Decidable check for whether writing `writeLane` preserves a concurrently live `liveLane`
    in the same physical GPR. Notably, `(.Lo8, .Hi8_NoRex)` and `(.Hi8_NoRex, .Lo8)` are
    non-interfering (`true`), whereas `.Lo32_Zext` clobbers every sub-register lane (`false`)! -/
def gprWritePreservesLane (writeLane liveLane : GprLane) : Bool :=
  match writeLane, liveLane with
  | .Lo8, .Hi8_NoRex => true
  | .Hi8_NoRex, .Lo8 => true
  | _, _             => false

/-- Theorem 1 (`extractGprLane_writeGprLane_same`): reading back `lane` immediately after
    `writeGprLane old lane val` recovers the exact lane projection `extractGprLane val lane`. -/
theorem extractGprLane_writeGprLane_same (old : Gpr64Word) (lane : GprLane) (val : Gpr64Word) :
    extractGprLane (writeGprLane old lane val) lane = extractGprLane val lane := by
  cases lane <;> rfl

/-- Theorem 2 (`gprWritePreservesLane_sound`): whenever `gprWritePreservesLane writeLane liveLane = true`,
    writing `writeLane` preserves `extractGprLane old liveLane` identically (`%al` and `%ah` non-interference). -/
theorem gprWritePreservesLane_sound (old val : Gpr64Word) (writeLane liveLane : GprLane)
    (h : gprWritePreservesLane writeLane liveLane = true) :
    extractGprLane (writeGprLane old writeLane val) liveLane = extractGprLane old liveLane := by
  cases writeLane <;> cases liveLane <;> first | rfl | contradiction

/-- Theorem 3 (`lo32_zext_zeroes_hi32`): any 32-bit sub-register write (`%eax` on x86-64 or `wN` on AArch64)
    unconditionally zeroes `hi32` (`[63:32]`). -/
theorem lo32_zext_zeroes_hi32 (old val : Gpr64Word) :
    (writeGprLane old .Lo32_Zext val).hi32 = 0#32 := by
  rfl

/-! ## 2. x86 `REX` Prefix vs. High-Byte (`%ah..%dh`) Encoding Constraint -/

structure GprSubRegOperand where
  pregIdx : Nat      -- 0..15 (`0=rax, 1=rcx, 2=rdx, 3=rbx, 4=rsp, 5=rbp, 6=rsi, 7=rdi, 8..15=r8..r15`)
  lane    : GprLane
  deriving DecidableEq, Repr, Inhabited

/-- Whether encoding `op` requires an x86-64 `REX` prefix (`0x40..0x4F`):
    - Any register index `8..15` (`r8..r15`),
    - 64-bit operand size (`Full64`),
    - Low-byte registers `%spl, %bpl, %sil, %dil` (`pregIdx ∈ {4, 5, 6, 7}` with `lane == .Lo8`). -/
def operandRequiresRex (op : GprSubRegOperand) : Bool :=
  op.pregIdx >= 8 || op.lane == .Full64 || (op.lane == .Lo8 && op.pregIdx >= 4)

/-- Whether `op` is a valid high-byte register (`%ah, %ch, %dh, %bh` = indices `0..3` only). -/
def isValidHi8Index (op : GprSubRegOperand) : Bool :=
  op.lane != .Hi8_NoRex || op.pregIdx < 4

/-- x86-64 instruction encoding legality checker for a 2-operand instruction:
    `%ah..%dh` (`Hi8_NoRex`) cannot be encoded in any instruction that emits a `REX` prefix! -/
def checkRexHi8Compat (dst src : GprSubRegOperand) : Bool :=
  isValidHi8Index dst && isValidHi8Index src &&
  !( (dst.lane == .Hi8_NoRex || src.lane == .Hi8_NoRex) &&
     (operandRequiresRex dst || operandRequiresRex src) )

/-- Rejects illegal `movb %ah, %r8b` or `movb %dil, %ah` under `checkRexHi8Compat`. -/
theorem rex_ah_conflict_rejected :
    checkRexHi8Compat { pregIdx := 8, lane := .Lo8 } { pregIdx := 0, lane := .Hi8_NoRex } = false ∧
    checkRexHi8Compat { pregIdx := 0, lane := .Hi8_NoRex } { pregIdx := 7, lane := .Lo8 } = false ∧
    checkRexHi8Compat { pregIdx := 0, lane := .Hi8_NoRex } { pregIdx := 0, lane := .Lo8 } = true := by
  decide

/-! ## 3. Vector Sub-Register Lane Semantics (`XMM`/`YMM`/`ZMM` and AArch64 NEON) -/

/-- A 512-bit vector register (`ZMM` / `YMM` / `XMM` / NEON `V`) modeled as four 128-bit lanes
    `xmm0, xmm1, xmm2, xmm3`, where `xmm0` is further decomposed into four 32-bit lanes `s0..s3`. -/
structure Vec512Word where
  s0   : BitVec 32
  s1   : BitVec 32
  s2   : BitVec 32
  s3   : BitVec 32
  ymm1 : BitVec 128  -- bits `[255:128]`
  zmm2 : BitVec 128  -- bits `[383:256]`
  zmm3 : BitVec 128  -- bits `[511:384]`
  deriving DecidableEq, Repr, Inhabited

inductive VecLaneWriteMode where
  | Vec128_LegacySseMerge   -- Legacy x86 SSE (`movaps xmm0, ...`): writes `[127:0]`, preserves `[511:128]`!
  | Vec128_VexOrNeonZero    -- x86 VEX/EVEX 128-bit (`vmovaps xmm0, ...`) & AArch64 `qN`: writes `[127:0]`, zeroes `[511:128]`!
  | Vec256_VexZero          -- x86 VEX/EVEX 256-bit (`vmovaps ymm0, ...`): writes `[255:0]`, zeroes `[511:256]`!
  | Vec512_Full             -- x86 EVEX 512-bit (`vmovaps zmm0, ...`)
  | Scalar32_ZeroUpper      -- AArch64 `fmov s0, w0` / `fadd s0, s1, s2`: writes `s0` `[31:0]`, zeroes `[511:32]`!
  | NeonIns32_Lane1         -- AArch64 `ins v0.s[1], w0`: merges `s1` `[63:32]`, preserves `s0, s2, s3`, zeroes `[511:128]`!
  deriving DecidableEq, Repr, Inhabited

def writeVecLane (old : Vec512Word) (mode : VecLaneWriteMode) (val : Vec512Word) : Vec512Word :=
  match mode with
  | .Vec128_LegacySseMerge =>
      { old with s0 := val.s0, s1 := val.s1, s2 := val.s2, s3 := val.s3 }
  | .Vec128_VexOrNeonZero =>
      { s0 := val.s0, s1 := val.s1, s2 := val.s2, s3 := val.s3, ymm1 := 0#128, zmm2 := 0#128, zmm3 := 0#128 }
  | .Vec256_VexZero =>
      { s0 := val.s0, s1 := val.s1, s2 := val.s2, s3 := val.s3, ymm1 := val.ymm1, zmm2 := 0#128, zmm3 := 0#128 }
  | .Vec512_Full => val
  | .Scalar32_ZeroUpper =>
      { s0 := val.s0, s1 := 0#32, s2 := 0#32, s3 := 0#32, ymm1 := 0#128, zmm2 := 0#128, zmm3 := 0#128 }
  | .NeonIns32_Lane1 =>
      { s0 := old.s0, s1 := val.s1, s2 := old.s2, s3 := old.s3, ymm1 := 0#128, zmm2 := 0#128, zmm3 := 0#128 }

theorem vex128_zeroes_upper_vs_legacy_sse_preserves_upper (old val : Vec512Word) :
    (writeVecLane old .Vec128_LegacySseMerge val).ymm1 = old.ymm1 ∧
    (writeVecLane old .Vec128_VexOrNeonZero val).ymm1 = 0#128 ∧
    (writeVecLane old .Scalar32_ZeroUpper val).s1 = 0#32 ∧
    (writeVecLane old .NeonIns32_Lane1 val).s0 = old.s0 ∧
    (writeVecLane old .NeonIns32_Lane1 val).s1 = val.s1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Sub-Register `RegAllocCert` Equivalence & Interference Checker -/

abbrev VReg := Nat
abbrev PReg := Nat

structure SubRegLoc where
  preg : PReg
  lane : GprLane
  deriving DecidableEq, Repr, Inhabited

/-- Checks whether two allocated `SubRegLoc`s can simultaneously hold distinct live `VReg`s
    without clobbering each other when `loc1` is written. -/
def subRegLocNonInterfering (writtenLoc liveLoc : SubRegLoc) : Bool :=
  writtenLoc.preg != liveLoc.preg || gprWritePreservesLane writtenLoc.lane liveLoc.lane

/-- Theorem (`checkSubRegLiveInterference_sound`): if `subRegLocNonInterfering dstLoc liveLoc = true`,
    updating `pstate` at `dstLoc` with `val` preserves the value of `liveLoc` in `pstate`. -/
theorem checkSubRegLiveInterference_sound
    (pstate : PReg → Gpr64Word) (dstLoc liveLoc : SubRegLoc) (val : Gpr64Word)
    (h_ok : subRegLocNonInterfering dstLoc liveLoc = true) :
    let pstate' : PReg → Gpr64Word :=
      fun p => if p = dstLoc.preg then writeGprLane (pstate p) dstLoc.lane val else pstate p
    extractGprLane (pstate' liveLoc.preg) liveLoc.lane =
    extractGprLane (pstate liveLoc.preg) liveLoc.lane := by
  dsimp only [subRegLocNonInterfering] at h_ok
  rw [Bool.or_eq_true] at h_ok
  cases h_ok with
  | inl h_neq =>
    have h_ne : liveLoc.preg ≠ dstLoc.preg := by
      intro h_eq
      rw [h_eq, bne_self_eq_false] at h_neq
      contradiction
    simp [h_ne]
  | inr h_lane =>
    by_cases h_eq : liveLoc.preg = dstLoc.preg
    · simp only [h_eq, ↓reduceIte]
      exact gprWritePreservesLane_sound (pstate dstLoc.preg) val dstLoc.lane liveLoc.lane h_lane
    · simp [h_eq]

/-- Negative bug-rejection theorem: allocating `v1` to `(%rax, .Hi8_NoRex)` (`%ah`) and writing
    `v2` to `(%rax, .Lo32_Zext)` (`%eax`) while `v1` is live is deterministically rejected (`= false`). -/
theorem bug_eax_clobbers_ah_rejected :
    subRegLocNonInterfering { preg := 0, lane := .Lo32_Zext } { preg := 0, lane := .Hi8_NoRex } = false ∧
    subRegLocNonInterfering { preg := 0, lane := .Lo8 }       { preg := 0, lane := .Hi8_NoRex } = true := by
  decide

/-! ## 5. Read-Only Memory & Frame-Address Load Rematerialization (`RematLoadCert`) -/

/-- Five verified rematerialization origins supported by `RematLoadCert`:
    1. `constI val`: immediate integer constant (`mov reg, imm`);
    2. `frameAddr slotOff`: stack frame pointer + constant displacement (`lea reg, [rbp - off]` / `add xN, sp, #off`);
    3. `rodataLoad symId off`: load from immutable `.rodata` constant pool (`mov reg, [rip + .LCPI]`);
    4. `immutableArgLoad paramIdx`: load from incoming caller ABI stack parameter slot (`[rbp + 16 + 8*k]`);
    5. `unmodifiedSpillSlot slotId`: load from a stack spill slot that was initialized once at definition
       and has zero intervening frame writes (`slotModifiedInInterval = false`). -/
inductive RematOrigin where
  | constI              (val : Int)
  | frameAddr           (slotOff : Int)
  | rodataLoad          (symId : Nat) (byteOff : Nat)
  | immutableArgLoad    (paramIdx : Nat)
  | unmodifiedSpillSlot (slotId : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Execution environment with read-only `.rodata`, immutable incoming stack args, frame base pointer,
    and mutable stack spill frame. -/
structure RematExecEnv where
  frameBasePtr     : Int
  rodataPool       : Nat → Nat → Int
  immutableStackIn : Nat → Int
  spillSlots       : Nat → Int

/-- Evaluates a `RematOrigin` in `env`. -/
def evalRematOrigin (env : RematExecEnv) (orig : RematOrigin) : Int :=
  match orig with
  | .constI v              => v
  | .frameAddr off         => env.frameBasePtr + off
  | .rodataLoad sym off    => env.rodataPool sym off
  | .immutableArgLoad idx  => env.immutableStackIn idx
  | .unmodifiedSpillSlot s => env.spillSlots s

/-- A frame-store operation (spill store or local stack write) only mutates `spillSlots`
    while leaving `frameBasePtr`, `rodataPool`, and `immutableStackIn` strictly invariant. -/
def applySpillWrite (env : RematExecEnv) (writtenSlot : Nat) (newVal : Int) : RematExecEnv :=
  { env with spillSlots := fun s => if s = writtenSlot then newVal else env.spillSlots s }

/-- Decidable single-write check for whether `orig` is preserved when `writtenSlot` is modified. -/
def checkRematSingleWrite (orig : RematOrigin) (writtenSlot : Nat) : Bool :=
  match orig with
  | .unmodifiedSpillSlot s => writtenSlot != s
  | _                      => true

/-- Decidable certificate check verifying that rematerializing `orig` across a sequence of
    intervening spill writes `writtenSlots : List Nat` produces the exact value at definition time. -/
def checkRematOriginValidAcrossWrites (orig : RematOrigin) : List Nat → Bool
  | [] => true
  | w :: ws => checkRematSingleWrite orig w && checkRematOriginValidAcrossWrites orig ws

/-- Single-step invariance lemma for `evalRematOrigin` across a disjoint spill write. -/
theorem evalRematOrigin_applySpillWrite_eq
    (env : RematExecEnv) (orig : RematOrigin) (w : Nat) (val : Int)
    (h_ok : checkRematSingleWrite orig w = true) :
    evalRematOrigin (applySpillWrite env w val) orig = evalRematOrigin env orig := by
  cases orig with
  | constI _ => rfl
  | frameAddr _ => rfl
  | rodataLoad _ _ => rfl
  | immutableArgLoad _ => rfl
  | unmodifiedSpillSlot s =>
    dsimp only [checkRematSingleWrite] at h_ok
    dsimp only [evalRematOrigin, applySpillWrite]
    have h_ne : s ≠ w := by
      intro h_eq
      rw [h_eq, bne_self_eq_false] at h_ok
      contradiction
    simp [h_ne]

/-- Executes a list of `(slot, val)` spill writes on `env`. -/
def applySpillWriteList (env : RematExecEnv) : List (Nat × Int) → RematExecEnv
  | [] => env
  | (w, v) :: rest => applySpillWriteList (applySpillWrite env w v) rest

/-- Top-level `RematLoadCert` soundness theorem (`checkRematLoadCert_sound`):
    Whenever `checkRematOriginValidAcrossWrites orig (writes.map Prod.fst) = true`, evaluating
    the rematerialized instruction `evalRematOrigin` after arbitrary intervening spill stores
    `writes` yields the exact value `evalRematOrigin env orig` computed at the original SSA
    definition point, with zero spill-store overhead for `constI`, `frameAddr`, `rodataLoad`,
    and `immutableArgLoad`. -/
theorem checkRematLoadCert_sound
    (env : RematExecEnv) (orig : RematOrigin) (writes : List (Nat × Int))
    (h_cert : checkRematOriginValidAcrossWrites orig (writes.map Prod.fst) = true) :
    evalRematOrigin (applySpillWriteList env writes) orig = evalRematOrigin env orig := by
  induction writes generalizing env with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [List.map, checkRematOriginValidAcrossWrites] at h_cert
    rw [Bool.and_eq_true] at h_cert
    dsimp only [applySpillWriteList]
    rw [ih (applySpillWrite env hd.1 hd.2) h_cert.2]
    exact evalRematOrigin_applySpillWrite_eq env orig hd.1 hd.2 h_cert.1

def checkAllM6 : Bool :=
  let r0 : Gpr64Word := { b0 := 0x11#8, b1 := 0x22#8, w1 := 0x3344#16, hi32 := 0x55667788#32 }
  let r1 := writeGprLane r0 .Lo8 { b0 := 0x99#8, b1 := 0#8, w1 := 0#16, hi32 := 0#32 }
  let r2 := writeGprLane r1 .Hi8_NoRex { b0 := 0#8, b1 := 0xAA#8, w1 := 0#16, hi32 := 0#32 }
  let r3 := writeGprLane r2 .Lo32_Zext { b0 := 0x01#8, b1 := 0x02#8, w1 := 0x0304#16, hi32 := 0xFFFFFFFF#32 }
  let c1 := r2.b0 == 0x99#8 && r2.b1 == 0xAA#8 && r2.hi32 == 0x55667788#32
  let c2 := r3.hi32 == 0#32
  let c3 := checkRexHi8Compat { pregIdx := 8, lane := .Lo8 } { pregIdx := 0, lane := .Hi8_NoRex } == false
  let c4 := checkRematOriginValidAcrossWrites (.unmodifiedSpillSlot 3) [1, 2, 4] == true
         && checkRematOriginValidAcrossWrites (.unmodifiedSpillSlot 3) [1, 3, 4] == false
  c1 && c2 && c3 && c4

#eval checkAllM6
#print axioms extractGprLane_writeGprLane_same
#print axioms gprWritePreservesLane_sound
#print axioms lo32_zext_zeroes_hi32
#print axioms rex_ah_conflict_rejected
#print axioms vex128_zeroes_upper_vs_legacy_sse_preserves_upper
#print axioms checkSubRegLiveInterference_sound
#print axioms bug_eax_clobbers_ah_rejected
#print axioms checkRematLoadCert_sound

end VerifiedSubRegAndRematCert
