prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.Int.DivMod.Basic
import Init.Data.List.Basic

/-!
# Hot-Loop Operational Semantics and Reference Specifications (`LoopCegisBase`)

Tactic-free `prelude` + `Init.*`-only foundation defining operational instruction
execution and pure reference specifications across six representative SIMD and
assembly hot-loop archetypes:
1. `ByteSumUnroll4`: 4x-unrolled SIMD byte sum (`vpsadbw` + `vpaddq`, `U = 64` B,
   dual vector accumulators `acc0`, `acc1`).
2. `DotMaddubsUnroll2`: 2x-unrolled AVX2 `vpmaddubsw` + `vpmaddwd` dot product
   (`U = 64` B, dual `ymm0`/`ymm1` + register-pinned `ymm2 = ones16`).
3. `PipelinedMac`: Software-pipelined 64-bit multiply-accumulate (`U = 1` word,
   pipeline lag `mu = 1` with prologue preload and epilogue stage drain).
4. `AdcLimbCarry`: Arbitrary-length multi-limb 64-bit `adc` carry-chain loop
   (`U = 1` limb, loop-carried `RFLAGS.CF` invariant).
5. `MemchrEarlyExit`: 16-byte chunked SIMD `memchr` scanner (`vpcmpeqb` +
   `vpmovmskb` + `tzcnt`, data-dependent early exit).
6. `CtCmovScan`: Branchless `cmove` constant-time table scan (functional
   equivalence + 2-safety `LeakEvent` trace invariance).

Zero tactics (`by`), zero `Std.*` or `Lean.*` imports, and zero axioms.
-/

namespace LoopCegisBase

def W64 : Nat := 18446744073709551616
def M32 : Nat := 4294967296

def b2n (b : Bool) : Nat :=
  match b with
  | true  => 1
  | false => 0

inductive LeakEvent where
  | memLoad (addr : Nat)
  | branch  (taken : Bool) (target : Nat)
  deriving DecidableEq

-- ============================================================================
-- 1. Loop 1: 4x-Unrolled SIMD Byte Sum (`vpsadbw` + `vpaddq`, `U = 64` B)
-- ============================================================================

def sumBytesRange (mem : Nat → Nat) (base : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (sumBytesRange mem base k + (mem (base + k) % 256)) % W64

def sad16Chunk (mem : Nat → Nat) (addr : Nat) : Nat :=
  ((mem addr % 256) + (mem (addr + 1) % 256) + (mem (addr + 2) % 256) + (mem (addr + 3) % 256) +
   (mem (addr + 4) % 256) + (mem (addr + 5) % 256) + (mem (addr + 6) % 256) + (mem (addr + 7) % 256) +
   (mem (addr + 8) % 256) + (mem (addr + 9) % 256) + (mem (addr + 10) % 256) + (mem (addr + 11) % 256) +
   (mem (addr + 12) % 256) + (mem (addr + 13) % 256) + (mem (addr + 14) % 256) + (mem (addr + 15) % 256))

structure ByteSumState where
  pc     : Nat
  halted : Bool
  rdi    : Nat
  rdx    : Nat
  rcx    : Nat
  acc0   : Nat
  acc1   : Nat
  rax    : Nat
  mem    : Nat → Nat

def stepByteSumUnroll4 (s : ByteSumState) : ByteSumState :=
  if s.halted then s
  else
    match s.pc with
    | 0 => { s with pc := 1, acc0 := 0, acc1 := 0, rcx := 0 }
    | 1 =>
      if s.rcx < s.rdx then
        let c0 := sad16Chunk s.mem (s.rdi + s.rcx)
        let c1 := sad16Chunk s.mem (s.rdi + s.rcx + 16)
        let c2 := sad16Chunk s.mem (s.rdi + s.rcx + 32)
        let c3 := sad16Chunk s.mem (s.rdi + s.rcx + 48)
        { s with
          pc   := 1
          acc0 := (s.acc0 + c0 + c2) % W64
          acc1 := (s.acc1 + c1 + c3) % W64
          rcx  := s.rcx + 64 }
      else
        { s with pc := 2, rax := (s.acc0 + s.acc1) % W64 }
    | _ => { s with halted := true }

def runByteSumUnroll4 : Nat → ByteSumState → ByteSumState
  | 0, s => s
  | fuel + 1, s => runByteSumUnroll4 fuel (stepByteSumUnroll4 s)

-- ============================================================================
-- 2. Loop 2: 2x-Unrolled `vpmaddubsw` + `vpmaddwd` Dot Product (`U = 64` B)
-- ============================================================================

def s8ToInt (b : Nat) : Int :=
  let m := b % 256
  if m < 128 then Int.ofNat m else Int.ofNat m - 256

def clampI16 (x : Int) : Int :=
  match (-32768) - x with
  | .ofNat 0 => -32768
  | .ofNat (_ + 1) => -32768
  | .negSucc _ =>
    match x - 32767 with
    | .ofNat 0 => 32767
    | .ofNat (_ + 1) => 32767
    | .negSucc _ => x

def intMod32 (x : Int) : Nat :=
  let m32 : Int := 4294967296
  Int.toNat ((x % m32 + m32) % m32)

def maddPairAt (mem : Nat → Nat) (aPtr bPtr off : Nat) : Int :=
  let u0 := Int.ofNat (mem (aPtr + off) % 256)
  let u1 := Int.ofNat (mem (aPtr + off + 1) % 256)
  let s0 := s8ToInt (mem (bPtr + off))
  let s1 := s8ToInt (mem (bPtr + off + 1))
  clampI16 (u0 * s0 + u1 * s1)

def dotChunk32Int (mem : Nat → Nat) (aPtr bPtr : Nat) : Nat → Int
  | 0 => 0
  | p + 1 => dotChunk32Int mem aPtr bPtr p + maddPairAt mem aPtr bPtr (2 * p)

def dotChunk32Mod32 (mem : Nat → Nat) (aPtr bPtr : Nat) (scaleOnes : Nat) : Nat :=
  -- `scaleOnes` models register `ymm2` (`1` when `ymm2 = ones16`, else scaled!)
  intMod32 (dotChunk32Int mem aPtr bPtr 16 * Int.ofNat scaleOnes)

def dotBlocks64Spec (mem : Nat → Nat) (aBase bBase : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    (dotBlocks64Spec mem aBase bBase k +
      dotChunk32Mod32 mem (aBase + 64 * k) (bBase + 64 * k) 1 +
      dotChunk32Mod32 mem (aBase + 64 * k + 32) (bBase + 64 * k + 32) 1) % M32

structure DotUnroll2State where
  pc       : Nat
  halted   : Bool
  ymmDirty : Bool
  rdi      : Nat
  rsi      : Nat
  rdx      : Nat
  rcx      : Nat
  ymm0Sum  : Nat
  ymm1Sum  : Nat
  ymm2Ones : Nat
  rax      : Nat
  mem      : Nat → Nat

def stepDotUnroll2 (s : DotUnroll2State) : DotUnroll2State :=
  if s.halted then s
  else
    match s.pc with
    | 0 =>
      if s.rdx = 0 then
        { s with pc := 2, ymm0Sum := 0, ymm1Sum := 0, ymmDirty := true }
      else
        { s with
          pc       := 1
          ymmDirty := true
          ymm0Sum  := 0
          ymm1Sum  := 0
          ymm2Ones := 1
          rdx      := 64 * s.rdx
          rcx      := 0 }
    | 1 =>
      if s.rcx < s.rdx then
        let d0 := dotChunk32Mod32 s.mem (s.rdi + s.rcx) (s.rsi + s.rcx) s.ymm2Ones
        let d1 := dotChunk32Mod32 s.mem (s.rdi + s.rcx + 32) (s.rsi + s.rcx + 32) s.ymm2Ones
        { s with
          pc      := 1
          ymm0Sum := (s.ymm0Sum + d0) % M32
          ymm1Sum := (s.ymm1Sum + d1) % M32
          rcx     := s.rcx + 64 }
      else
        { s with pc := 2 }
    | 2 =>
      -- Horizontal epilogue reduction + `vzeroupper`
      { s with pc := 3, ymmDirty := false, rax := (s.ymm0Sum + s.ymm1Sum) % M32 }
    | _ =>
      { s with halted := true }

def runDotUnroll2 : Nat → DotUnroll2State → DotUnroll2State
  | 0, s => s
  | fuel + 1, s => runDotUnroll2 fuel (stepDotUnroll2 s)

-- ============================================================================
-- 3. Loop 3: Software-Pipelined 64-Bit MAC (`U = 1`, Pipeline Lag `mu = 1`)
-- ============================================================================

def macPrefixSpec (aMem bMem : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (macPrefixSpec aMem bMem k + ((aMem k % W64) * (bMem k % W64)) % W64) % W64

structure PipelinedMacState where
  pc     : Nat
  halted : Bool
  n      : Nat
  idx    : Nat
  acc    : Nat
  stage  : Nat
  rax    : Nat
  aMem   : Nat → Nat
  bMem   : Nat → Nat

def stepPipelinedMac (s : PipelinedMacState) : PipelinedMacState :=
  if s.halted then s
  else
    match s.pc with
    | 0 =>
      if s.n = 0 then
        { s with pc := 3, rax := 0 }
      else
        -- Prologue preloads pipeline stage 0 (`idx := 1`, `acc := 0`, `stage := a[0]*b[0]`)
        { s with
          pc    := 1
          idx   := 1
          acc   := 0
          stage := ((s.aMem 0 % W64) * (s.bMem 0 % W64)) % W64 }
    | 1 =>
      if s.idx < s.n then
        { s with
          pc    := 1
          acc   := (s.acc + s.stage) % W64
          stage := ((s.aMem s.idx % W64) * (s.bMem s.idx % W64)) % W64
          idx   := s.idx + 1 }
      else
        -- Epilogue drains final pipelined product
        { s with pc := 3, rax := (s.acc + s.stage) % W64 }
    | _ =>
      { s with halted := true }

def runPipelinedMac : Nat → PipelinedMacState → PipelinedMacState
  | 0, s => s
  | fuel + 1, s => runPipelinedMac fuel (stepPipelinedMac s)

-- ============================================================================
-- 4. Loop 4: Multi-Limb 64-Bit `adc` Carry-Chain Loop (`U = 1`, `RFLAGS.CF`)
-- ============================================================================

def powW64 : Nat → Nat
  | 0 => 1
  | k + 1 => powW64 k * W64

def limbsVal (mem : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => limbsVal mem k + (mem k % W64) * powW64 k

def memUpd (m : Nat → Nat) (idx val : Nat) : Nat → Nat :=
  fun x => if x = idx then val % W64 else m x

structure AdcLoopState where
  pc     : Nat
  halted : Bool
  n      : Nat
  idx    : Nat
  cf     : Bool
  rax    : Nat
  aMem   : Nat → Nat
  bMem   : Nat → Nat
  outMem : Nat → Nat

def stepAdcLoop (s : AdcLoopState) : AdcLoopState :=
  if s.halted then s
  else
    match s.pc with
    | 0 => { s with pc := 1, idx := 0, cf := false }
    | 1 =>
      if s.idx < s.n then
        let sum := (s.aMem s.idx % W64) + (s.bMem s.idx % W64) + b2n s.cf
        let lo  := sum % W64
        let cf' := decide (sum ≥ W64)
        { s with
          pc     := 1
          idx    := s.idx + 1
          cf     := cf'
          outMem := memUpd s.outMem s.idx lo }
      else
        { s with pc := 2, rax := b2n s.cf }
    | _ => { s with halted := true }

def runAdcLoop : Nat → AdcLoopState → AdcLoopState
  | 0, s => s
  | fuel + 1, s => runAdcLoop fuel (stepAdcLoop s)

-- ============================================================================
-- 5. Loop 5: 16-Byte SIMD `memchr` Early-Exit Scanner (`vpcmpeqb`+`vpmovmskb`)
-- ============================================================================

def findByteFrom (mem : Nat → Nat) (base needle idx rem : Nat) : Nat :=
  match rem with
  | 0 => idx
  | r + 1 =>
    if mem (base + idx) % 256 = needle % 256 then idx
    else findByteFrom mem base needle (idx + 1) r

def memchrSpec (mem : Nat → Nat) (base totalBytes needle : Nat) : Nat :=
  findByteFrom mem base needle 0 totalBytes

def noMatchBefore (mem : Nat → Nat) (base needle : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    noMatchBefore mem base needle k &&
    decide (mem (base + k) % 256 ≠ needle % 256)

def movemask16From (mem : Nat → Nat) (addr needle off : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 =>
    let b := if mem (addr + off) % 256 = needle % 256 then 1 else 0
    b + 2 * movemask16From mem addr needle (off + 1) r

def ctz16 (mask : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 =>
    if mask % 2 = 1 then 0
    else 1 + ctz16 (mask / 2) r

structure MemchrState where
  pc     : Nat
  halted : Bool
  base   : Nat
  blocks : Nat
  needle : Nat
  k      : Nat
  rax    : Nat
  mem    : Nat → Nat

def stepMemchr (s : MemchrState) : MemchrState :=
  if s.halted then s
  else
    match s.pc with
    | 0 => { s with pc := 1, k := 0 }
    | 1 =>
      if s.k < s.blocks then
        let m := movemask16From s.mem (s.base + 16 * s.k) s.needle 0 16
        if m = 0 then
          { s with pc := 1, k := s.k + 1 }
        else
          -- Data-dependent early exit via `tzcnt`!
          { s with pc := 2, rax := 16 * s.k + ctz16 m 16 }
      else
        { s with pc := 2, rax := 16 * s.blocks }
    | _ => { s with halted := true }

def runMemchr : Nat → MemchrState → MemchrState
  | 0, s => s
  | fuel + 1, s => runMemchr fuel (stepMemchr s)

-- ============================================================================
-- 6. Loop 6: Branchless `cmove` Constant-Time Scan (`Functional + 2-Safety`)
-- ============================================================================

def ctScanSpec (table : Nat → Nat) (n target : Nat) : Nat :=
  if target < n then table target % W64 else 0

structure CtScanState where
  pc     : Nat
  halted : Bool
  base   : Nat
  n      : Nat
  target : Nat
  k      : Nat
  rax    : Nat
  table  : Nat → Nat
  leak   : List LeakEvent

def stepCtScan (s : CtScanState) : CtScanState :=
  if s.halted then s
  else
    match s.pc with
    | 0 => { s with pc := 1, k := 0, rax := 0 }
    | 1 =>
      if s.k < s.n then
        let elem := s.table s.k % W64
        let sel  := if s.k = s.target then elem else s.rax
        { s with
          pc   := 1
          k    := s.k + 1
          rax  := sel
          leak := s.leak ++ [.memLoad (s.base + 8 * s.k), .branch true 1] }
      else
        { s with pc := 2, leak := s.leak ++ [.branch false 2] }
    | _ => { s with halted := true }

def runCtScan : Nat → CtScanState → CtScanState
  | 0, s => s
  | fuel + 1, s => runCtScan fuel (stepCtScan s)

end LoopCegisBase
