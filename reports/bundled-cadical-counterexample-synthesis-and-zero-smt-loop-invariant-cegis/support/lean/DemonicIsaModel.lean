prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

/-!
# Demonic Machine-Code Equivalence and 2-Safety Leakage Foundation

Tactic-free `prelude` + `Init.*`-only specification layer modeling the four sources
of machine-code (`MIR <-> ISA`) demonic and relational nondeterminism:
1. `pageMisalign ∈ [0, 4096)`: arbitrary sub-page pointer alignment detecting
   unaligned SIMD loads (`vmovdqu`) that cross into an unmapped `PROT_NONE` page.
2. `slackBytes`: demonic out-of-slice memory bytes inside the same mapped page
   beyond `[ptr, ptr + len)` (`DemonicGranuleLoad`).
3. `bsfUndefDst` & `imulUndefZf`: architecturally undefined destination registers
   (`bsf` on zero source) and `RFLAGS` (`ZF` after `imul`), per Intel SDM Vol. 2A.
4. `CtLeakEquiv`: 2-safety hyperproperty requiring secret-independent `LeakEvent`
   branch and memory-address traces alongside functional correctness.

Zero tactics (`by`), zero `Std.*` or `Lean.*` imports, and zero axioms.
-/

namespace DemonicIsaModel

def W64 : Nat := 18446744073709551616
def M32 : Nat := 4294967296
def M16 : Nat := 65536

structure DemonicEnv where
  pageMisalign : Nat
  slackBytes   : List Nat
  bsfUndefDst  : Nat
  imulUndefZf  : Bool
  deriving DecidableEq

def allBytesLt256 : List Nat → Bool
  | [] => true
  | b :: bs => decide (b < 256) && allBytesLt256 bs

def ValidDemonic (d : DemonicEnv) : Bool :=
  decide (d.pageMisalign < 4096) &&
  decide (d.bsfUndefDst < W64) &&
  allBytesLt256 d.slackBytes

inductive FaultKind where
  | unmappedPageCross (pageOffset loadWidth sliceLen : Nat)
  | undefArchState    (tag : Nat)
  deriving DecidableEq

inductive IsaOutcome (Out : Type) where
  | ok    (val : Out)
  | fault (kind : FaultKind)
  deriving DecidableEq

def TotalMirAsmEquiv {In Out : Type}
    (pre : In → Bool)
    (mirSpec : In → Out)
    (asmExec : In → DemonicEnv → IsaOutcome Out) : Prop :=
  ∀ (x : In) (d : DemonicEnv),
    pre x = true → ValidDemonic d = true →
    asmExec x d = .ok (mirSpec x)

inductive LeakEvent where
  | branch (taken : Bool)
  | memAcc (addr : Nat)
  deriving DecidableEq

structure CtKernel (Pub Sec Out : Type) where
  pre  : Pub → Sec → Bool
  spec : Pub → Sec → Out
  exec : Pub → Sec → Out × List LeakEvent

def CtLeakEquiv {Pub Sec Out : Type} (k : CtKernel Pub Sec Out) : Prop :=
  (∀ p s, k.pre p s = true → (k.exec p s).1 = k.spec p s) ∧
  (∀ p s1 s2, k.pre p s1 = true → k.pre p s2 = true →
    (k.exec p s1).2 = (k.exec p s2).2)

-- ============================================================================
-- Unified Demonic Granule Load (`vmovdqu` / SWAR unaligned load semantics)
-- ============================================================================

def listGetZero : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x % 256
  | _ :: xs, n + 1 => listGetZero xs n

def crossesUnmappedPage (mis len width : Nat) : Bool :=
  match Nat.beq width 0 with
  | true => false
  | false =>
    match Nat.beq len 0 with
    | true => decide (mis + width > 4096)
    | false =>
      decide (len < width) &&
      decide ((mis + len - 1) / 4096 < (mis + width - 1) / 4096)

def readGranuleBytesAux (slice slack : List Nat) (len idx rem : Nat) : List Nat :=
  match rem with
  | 0 => []
  | r + 1 =>
    let b := if idx < len then listGetZero slice idx else listGetZero slack (idx - len)
    b :: readGranuleBytesAux slice slack len (idx + 1) r

def demonicLoadGranule (slice : List Nat) (d : DemonicEnv) (width : Nat) :
    IsaOutcome (List Nat) :=
  let len := slice.length
  match crossesUnmappedPage d.pageMisalign len width with
  | true  => .fault (.unmappedPageCross d.pageMisalign width len)
  | false => .ok (readGranuleBytesAux slice d.slackBytes len 0 width)

def packLeBytes : List Nat → Nat
  | [] => 0
  | b :: bs => (b % 256) + 256 * packLeBytes bs

-- ============================================================================
-- Bug 1: `vpmaddubsw` Signed `i16` Saturation (`255 * (64 + 65) = 32895 > 32767`)
-- ============================================================================

structure MaddubsIn where
  u0 : Nat
  u1 : Nat
  s0 : Int
  s1 : Int
  deriving DecidableEq

def intLe (a b : Int) : Bool :=
  match b - a with
  | .ofNat _   => true
  | .negSucc _ => false

def maddubsPre (x : MaddubsIn) : Bool :=
  decide (x.u0 < 256) && decide (x.u1 < 256) &&
  intLe (-64) x.s0 && intLe x.s0 64 &&
  intLe (-65) x.s1 && intLe x.s1 65

def clampI16 (v : Int) : Int :=
  if intLe v (-32768) then -32768
  else if intLe 32767 v then 32767
  else v

def maddubsMirSpec (x : MaddubsIn) : Int :=
  Int.ofNat x.u0 * x.s0 + Int.ofNat x.u1 * x.s1

def maddubsAsmBuggy (x : MaddubsIn) (_d : DemonicEnv) : IsaOutcome Int :=
  .ok (clampI16 (Int.ofNat x.u0 * x.s0 + Int.ofNat x.u1 * x.s1))

-- ============================================================================
-- Bug 2: SWAR `count_zero_bytes` Mycroft Cross-Byte Borrow Bleed
-- ============================================================================

def countZeroBytesAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, w =>
    let b := w % 256
    (if b = 0 then 1 else 0) + countZeroBytesAux k (w / 256)

def popcntBytesHighBits : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, w =>
    let b := (w / 128) % 2
    b + popcntBytesHighBits k (w / 256)

def swarCountPre (x : Nat) : Bool := decide (x < W64)

def swarCountMirSpec (x : Nat) : Nat := countZeroBytesAux 8 x

def c0101 : Nat := 0x0101010101010101
def c8080 : Nat := 0x8080808080808080

def swarCountAsmBuggy (x : Nat) (_d : DemonicEnv) : IsaOutcome Nat :=
  let sub := (x + W64 - (c0101 % W64)) % W64
  let notX := (W64 - 1) - (x % W64)
  let mask := Nat.land (Nat.land sub notX) c8080
  .ok (popcntBytesHighBits 8 mask)

-- ============================================================================
-- Bug 3: `bsf` vs `tzcnt` Undefined Destination Register on Zero Input
-- ============================================================================

def ctz64Aux : Nat → Nat → Nat
  | 0, _ => 64
  | k + 1, w =>
    if w % 2 = 1 then 64 - (k + 1)
    else ctz64Aux k (w / 2)

def bsfPre (x : Nat) : Bool := decide (x < W64)

def bsfMirSpec (x : Nat) : Nat :=
  if x = 0 then 64 else ctz64Aux 64 x

def bsfAsmBuggy (x : Nat) (d : DemonicEnv) : IsaOutcome Nat :=
  if x = 0 then .ok d.bsfUndefDst else .ok (ctz64Aux 64 x)

-- ============================================================================
-- Bug 4: Branching on `ZF` (`jz` / `sete`) Immediately After `imul`
-- ============================================================================

structure ImulPair where
  a : Nat
  b : Nat
  deriving DecidableEq

def imulZfPre (p : ImulPair) : Bool :=
  decide (p.a < W64) && decide (p.b < W64)

def imulZfMirSpec (p : ImulPair) : Bool :=
  decide ((p.a * p.b) % W64 = 0)

def imulZfAsmBuggy (_p : ImulPair) (d : DemonicEnv) : IsaOutcome Bool :=
  .ok d.imulUndefZf

-- ============================================================================
-- Bug 5: Unguarded `vmovdqu` Crossing `PROT_NONE` Page Boundary (`len == 0`)
-- ============================================================================

def vmovdquHeadPre (slice : List Nat) : Bool :=
  decide (slice.length ≤ 32) && allBytesLt256 slice

def vmovdquHeadMirSpec (slice : List Nat) : Nat :=
  match slice with
  | [] => 0
  | b :: _ => b % 256

def vmovdquHeadAsmBuggy (slice : List Nat) (d : DemonicEnv) : IsaOutcome Nat :=
  match demonicLoadGranule slice d 32 with
  | .fault fk => .fault fk
  | .ok bytes =>
    if slice.length = 0 then .ok 0 else .ok (listGetZero bytes 0)

-- ============================================================================
-- Bug 6: Off-by-One Tail Shift Mask Reading 1 Demonic Slack Byte
-- ============================================================================

def tailMaskPre (slice : List Nat) : Bool :=
  decide (1 ≤ slice.length) && decide (slice.length ≤ 7) && allBytesLt256 slice

def tailMaskMirSpec (slice : List Nat) : Nat :=
  packLeBytes slice

def tailMaskAsmBuggy (slice : List Nat) (d : DemonicEnv) : IsaOutcome Nat :=
  let dAligned : DemonicEnv := { d with pageMisalign := 0 }
  match demonicLoadGranule slice dAligned 8 with
  | .fault fk => .fault fk
  | .ok bytes =>
    let raw64 := packLeBytes bytes
    -- Bug: shifts by `(7 - len) * 8` instead of `(8 - len) * 8`, keeping `len + 1` bytes!
    let keepBits := (slice.length + 1) * 8
    let mask := Nat.shiftLeft 1 keepBits - 1
    .ok (Nat.land raw64 mask)

-- ============================================================================
-- Bug 7: Optimistic `vpmovmskb` Early-Exit 2-Safety `LeakTrace` Violation
-- ============================================================================

def eqBytes16 : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as_, b :: bs => decide (a % 256 = b % 256) && eqBytes16 as_ bs
  | _, _ => false

def movemaskEq16Aux : List Nat → List Nat → Nat → Nat
  | a :: as_, b :: bs, bit =>
    (if a % 256 = b % 256 then bit else 0) + movemaskEq16Aux as_ bs (bit * 2)
  | _, _, _ => 0

def ctVpmovmskbKernel : CtKernel (List Nat) (List Nat) Bool :=
  { pre := fun pub sec =>
      decide (pub.length = 16) && decide (sec.length = 16) &&
      allBytesLt256 pub && allBytesLt256 sec
    spec := fun pub sec => eqBytes16 pub sec
    exec := fun pub sec =>
      let m := movemaskEq16Aux pub sec 1
      -- Functionally exact fast-path `if m == 0xffff { return true } else { return false }`
      -- that leaks secret tag equality through a conditional branch event!
      if m = 65535 then (true, [.branch true])
      else (false, [.branch false]) }

-- ============================================================================
-- Bug 8: 64-Bit `pclmulqdq` CRC-64 2-Lane Fold Polynomial Constant Bit-Flip
-- ============================================================================

structure ClmulPair where
  h : Nat
  l : Nat
  deriving DecidableEq

def clmul64Aux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | k + 1, a, b, acc =>
    let acc' := if a % 2 = 1 then Nat.xor acc b else acc
    clmul64Aux k (a / 2) (b * 2) acc'

def clmul64 (a b : Nat) : Nat := clmul64Aux 64 (a % W64) (b % W64) 0

def crcK1 : Nat := 0x42f0e1eba9ea3693
def crcK2Ref : Nat := 0x9d6c98236f552e17
-- 1-bit flip at bit 62 (`0x9d6c... ^ (1 <<< 62) = 0xdd6c...`)
def crcK2Bug : Nat := 0xdd6c98236f552e17

def clmulFoldPre (p : ClmulPair) : Bool :=
  decide (p.h < W64) && decide (p.l < W64)

def clmulFoldMirSpec (p : ClmulPair) : Nat :=
  Nat.xor (clmul64 p.h crcK1) (clmul64 p.l crcK2Ref)

def clmulFoldAsmBuggy (p : ClmulPair) (_d : DemonicEnv) : IsaOutcome Nat :=
  .ok (Nat.xor (clmul64 p.h crcK1) (clmul64 p.l crcK2Bug))

-- ============================================================================
-- Bug 9: `mulx` + `adcx`/`adox` Dual Carry-Chain Flag Swap
-- ============================================================================

structure AdxMac2In where
  t0 : Nat
  t1 : Nat
  a0 : Nat
  a1 : Nat
  b  : Nat
  deriving DecidableEq

def adxMac2Pre (x : AdxMac2In) : Bool :=
  decide (x.t0 < W64) && decide (x.t1 < W64) &&
  decide (x.a0 < W64) && decide (x.a1 < W64) && decide (x.b < W64)

def adxMac2MirSpec (x : AdxMac2In) : Nat × Nat × Nat :=
  let total := (x.t0 + x.t1 * W64) + (x.a0 + x.a1 * W64) * x.b
  (total % W64, (total / W64) % W64, (total / (W64 * W64)) % W64)

def adxMac2AsmBuggy (x : AdxMac2In) (_d : DemonicEnv) : IsaOutcome (Nat × Nat × Nat) :=
  let p0 := x.a0 * x.b
  let lo0 := p0 % W64
  let hi0 := p0 / W64
  let s0 := lo0 + x.t0
  let out0 := s0 % W64
  let cf1 := s0 / W64
  let p1 := x.a1 * x.b
  let lo1 := p1 % W64
  let hi1 := p1 / W64
  let u1 := hi0 + lo1 + cf1
  let r9 := u1 % W64
  let cf2 := u1 / W64
  let v1 := r9 + x.t1
  let out1 := v1 % W64
  let of2 := v1 / W64
  -- Bug: `adox rax, r9; adox rax, rcx` uses `of2` instead of `cf2` and clears `of`, dropping `cf2`!
  let w1 := hi1 + of2
  let out2 := w1 % W64
  .ok (out0, out1, out2)

-- ============================================================================
-- Bug 10: `vpshufb` Control-Byte Bit-7 Zeroing (`idx = 0x80` Clears Lane)
-- ============================================================================

structure PshufbIn where
  lut0 : Nat
  idx0 : Nat
  deriving DecidableEq

def pshufbPre (x : PshufbIn) : Bool :=
  decide (x.lut0 < 256) && decide (x.idx0 < 256)

def pshufbMirSpec (x : PshufbIn) : Nat :=
  if x.idx0 % 16 = 0 then x.lut0 else 0

def pshufbAsmBuggy (x : PshufbIn) (_d : DemonicEnv) : IsaOutcome Nat :=
  -- `vpshufb` clears result byte when bit 7 (`>= 128`) of control byte is set!
  if x.idx0 ≥ 128 then .ok 0
  else if x.idx0 % 16 = 0 then .ok x.lut0
  else .ok 0

-- ============================================================================
-- Bug 11: `vminss` Asymmetric Operand Swap on `(-0.0, +0.0)` and `(qNaN, x)`
-- ============================================================================

structure F32Pair where
  aBits : Nat
  bBits : Nat
  deriving DecidableEq

def f32Pre (p : F32Pair) : Bool :=
  decide (p.aBits < M32) && decide (p.bBits < M32)

def f32IsNaN (bits : Nat) : Bool :=
  let exp := (bits / 8388608) % 256
  let frac := bits % 8388608
  decide (exp = 255) && decide (frac > 0)

def f32IsZero (bits : Nat) : Bool :=
  decide (bits % 2147483648 = 0)

def f32Lt (a b : Nat) : Bool :=
  if f32IsNaN a || f32IsNaN b then false
  else if f32IsZero a && f32IsZero b then false
  else
    let sa := (a / 2147483648) % 2
    let sb := (b / 2147483648) % 2
    let ma := a % 2147483648
    let mb := b % 2147483648
    if sa = 1 && sb = 0 then true
    else if sa = 0 && sb = 1 then false
    else if sa = 0 then decide (ma < mb)
    else decide (mb < ma)

/-- Exact x86 `vminss dst, a, b` (`a < b ? a : b`, returning `b` on tie or NaN). -/
def vminss32 (a b : Nat) : Nat :=
  if f32Lt a b then a else b

def vminssMirSpec (p : F32Pair) : Nat := vminss32 p.aBits p.bBits

def vminssAsmBuggy (p : F32Pair) (_d : DemonicEnv) : IsaOutcome Nat :=
  .ok (vminss32 p.bBits p.aBits)

-- ============================================================================
-- Bug 12: BMI2 `bzhi` Count `>= 64` Saturation vs Modular Shift `(1 << (n % 64)) - 1`
-- ============================================================================

structure BzhiIn where
  x : Nat
  n : Nat
  deriving DecidableEq

def bzhiPre (inp : BzhiIn) : Bool :=
  decide (inp.x < W64) && decide (inp.n < 256)

def bzhiMirSpec (inp : BzhiIn) : Nat :=
  let idx := inp.n % 256
  if idx ≥ 64 then inp.x
  else inp.x % (Nat.shiftLeft 1 idx)

def bzhiAsmBuggy (inp : BzhiIn) (_d : DemonicEnv) : IsaOutcome Nat :=
  let sh := inp.n % 64
  let mask := Nat.shiftLeft 1 sh - 1
  .ok (Nat.land inp.x mask)

-- ============================================================================
-- Formal Class I (Reachable Code Bug) vs Class II (Unreachable Invariant Gap)
-- ============================================================================

structure LoopTriageState where
  idx : Nat
  lim : Nat
  acc : Nat
  deriving DecidableEq

def triageLoopStep (s : LoopTriageState) : LoopTriageState :=
  { idx := s.idx + 32, lim := s.lim, acc := (s.acc + 1) % W64 }

def triageLoopGuard (s : LoopTriageState) : Bool := decide (s.idx < s.lim)

/-- Over-specific micro-trace invariant (`idx <= 64`) falsified at `idx = 64, lim = 96`,
    while healthy loop satisfies `TotalMirAsmEquiv` on all `lim = 32 * blocks`! -/
def candidateInvCoincidental (s : LoopTriageState) : Bool :=
  decide (s.idx % 32 = 0) && decide (s.idx ≤ 64)

def StepInductive (inv guard : LoopTriageState → Bool)
    (step : LoopTriageState → LoopTriageState) : Prop :=
  ∀ s : LoopTriageState, inv s = true → guard s = true → inv (step s) = true

def runTriageLoop : Nat → LoopTriageState → LoopTriageState
  | 0, s => s
  | fuel + 1, s =>
    if triageLoopGuard s then runTriageLoop fuel (triageLoopStep s) else s

def triageHealthyPre (blocks : Nat) : Bool := decide (blocks ≤ 8)
def triageHealthySpec (blocks : Nat) : Nat := blocks
def triageHealthyExec (blocks : Nat) (_d : DemonicEnv) : IsaOutcome Nat :=
  .ok (runTriageLoop 16 ⟨0, 32 * blocks, 0⟩).acc

end DemonicIsaModel
