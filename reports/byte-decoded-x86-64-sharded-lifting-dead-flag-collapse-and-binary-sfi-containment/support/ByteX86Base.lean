prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Lemmas

/-!
Unified `prelude` + `Init.*` x86-64 byte-level machine model (`0` `partial`,
`0` `opaque`, `0` `sorry`, `0` custom axioms) mechanizing:
1. True byte-addressed memory (`ByteMem := BitVec 64 → BitVec 8`) with 8-byte
   little-endian `readMem64` / `writeMem64` roundtrip & disjointness theorems,
   plus `and rsp, -32` dynamic stack realignment arithmetic;
2. 6-flag `RFlags` (`CF, PF, AF, ZF, SF, OF`) with 8-bit `parity8` and normative
   demonic undefined-flag nondeterminism (`UndefFlags`) across `XOR`/`AND`/`OR`/`TEST`,
   `SHL`/`SHR`, `IMUL`, `BSF`, and `TZCNT`;
3. Two-stage variable-length (`1..15` byte) x86-64 byte decoder (`decodeX64`)
   handling legacy prefixes, REX nullification, consecutive REX precedence,
   VEX2/VEX3 `#UD` prefix exclusions, `LOCK` `#UD` legality, 15-byte `#GP(0)`
   enforcement, ModR/M + SIB + `disp8`/`disp32` + `[rip + disp32]`, and a
   universal prefix-invariance / determinism theorem (`decodeX64_prefix_invariant`);
4. Balanced `ByteCodeTree` 16-byte fetch-window operational semantics (`stepX64`,
   `runX64`), backward `DeadFlagCollapse` + Unexposed Private Stack-Frame
   Separation (`checkByteLeaf_sound`), and loop-invariant-free decidable Binary
   SFI Containment (`checkSfiTree_preserves_rust_host_safety`).
-/

namespace ByteX86

/-! ## Section 1: Architectural Registers, Byte Memory, and Demonic `RFLAGS` -/

inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def regOfNat (n : Nat) : Reg :=
  match n % 16 with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

def regUpd (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

theorem regUpd_eq (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) :
    regUpd regs r v r = v := by
  dsimp [regUpd]; simp

theorem regUpd_ne (regs : Reg → BitVec 64) {r r' : Reg} (h : r' ≠ r) (v : BitVec 64) :
    regUpd regs r v r' = regs r' := by
  dsimp [regUpd]; simp [h]

/-- Six architectural status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  deriving DecidableEq, Repr

/-- Per-step demonic hardware choice for architecturally undefined status flags. -/
abbrev UndefFlags := RFlags

/-- Liveness bitmask over `{CF, PF, AF, ZF, SF, OF}` for backward `DeadFlagCollapse`. -/
abbrev FlagMask := RFlags

def FlagMask.dead : FlagMask := {}

def FlagMask.orMask (a b : FlagMask) : FlagMask :=
  { cf := a.cf || b.cf, pf := a.pf || b.pf, af := a.af || b.af,
    zf := a.zf || b.zf, sf := a.sf || b.sf, of := a.of || b.of }

def FlagsAgreeOn (m : FlagMask) (f1 f2 : RFlags) : Prop :=
  (m.cf = true → f1.cf = f2.cf) ∧
  (m.pf = true → f1.pf = f2.pf) ∧
  (m.af = true → f1.af = f2.af) ∧
  (m.zf = true → f1.zf = f2.zf) ∧
  (m.sf = true → f1.sf = f2.sf) ∧
  (m.of = true → f1.of = f2.of)

theorem flagsAgreeOn_dead (f1 f2 : RFlags) : FlagsAgreeOn FlagMask.dead f1 f2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; cases h)

theorem flagsAgreeOn_refl (m : FlagMask) (f : RFlags) : FlagsAgreeOn m f f :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Exact x86 8-bit even parity flag (`PF = 1` iff low byte has an even number of 1-bits). -/
def parity8 (lo : BitVec 8) : Bool :=
  !(lo.getLsbD 0 ^^ lo.getLsbD 1 ^^ lo.getLsbD 2 ^^ lo.getLsbD 3 ^^
    lo.getLsbD 4 ^^ lo.getLsbD 5 ^^ lo.getLsbD 6 ^^ lo.getLsbD 7)

/-- Byte-addressed 64-bit linear memory (`BitVec 64 → BitVec 8`). -/
abbrev ByteMem := BitVec 64 → BitVec 8

def memUpd8 (m : ByteMem) (a : BitVec 64) (b : BitVec 8) : ByteMem :=
  fun a' => if a' = a then b else m a'

theorem memUpd8_eq (m : ByteMem) (a : BitVec 64) (b : BitVec 8) :
    memUpd8 m a b a = b := by
  dsimp [memUpd8]; simp

theorem memUpd8_ne (m : ByteMem) {a a' : BitVec 64} (h : a' ≠ a) (b : BitVec 8) :
    memUpd8 m a b a' = m a' := by
  dsimp [memUpd8]; simp [h]

def byteOf64 (v : BitVec 64) (k : Nat) : BitVec 8 :=
  BitVec.extractLsb' (k * 8) 8 v

def pack8Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ (b6 ++ (b5 ++ (b4 ++ (b3 ++ (b2 ++ (b1 ++ b0))))))

theorem pack8_byteOf64 (v : BitVec 64) :
    pack8Bytes (byteOf64 v 0) (byteOf64 v 1) (byteOf64 v 2) (byteOf64 v 3)
               (byteOf64 v 4) (byteOf64 v 5) (byteOf64 v 6) (byteOf64 v 7) = v := by
  dsimp [pack8Bytes, byteOf64]
  have s1 : BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v = BitVec.extractLsb' 0 16 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s2 : BitVec.extractLsb' 16 8 v ++ BitVec.extractLsb' 0 16 v = BitVec.extractLsb' 0 24 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s3 : BitVec.extractLsb' 24 8 v ++ BitVec.extractLsb' 0 24 v = BitVec.extractLsb' 0 32 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s4 : BitVec.extractLsb' 32 8 v ++ BitVec.extractLsb' 0 32 v = BitVec.extractLsb' 0 40 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s5 : BitVec.extractLsb' 40 8 v ++ BitVec.extractLsb' 0 40 v = BitVec.extractLsb' 0 48 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s6 : BitVec.extractLsb' 48 8 v ++ BitVec.extractLsb' 0 48 v = BitVec.extractLsb' 0 56 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s7 : BitVec.extractLsb' 56 8 v ++ BitVec.extractLsb' 0 56 v = BitVec.extractLsb' 0 64 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  rw [s1, s2, s3, s4, s5, s6, s7]
  exact BitVec.extractLsb'_eq_self

def readMem64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  pack8Bytes (m (a + 0#64)) (m (a + 1#64)) (m (a + 2#64)) (m (a + 3#64))
             (m (a + 4#64)) (m (a + 5#64)) (m (a + 6#64)) (m (a + 7#64))

def writeMem64 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m0 := memUpd8 m  (a + 0#64) (byteOf64 v 0)
  let m1 := memUpd8 m0 (a + 1#64) (byteOf64 v 1)
  let m2 := memUpd8 m1 (a + 2#64) (byteOf64 v 2)
  let m3 := memUpd8 m2 (a + 3#64) (byteOf64 v 3)
  let m4 := memUpd8 m3 (a + 4#64) (byteOf64 v 4)
  let m5 := memUpd8 m4 (a + 5#64) (byteOf64 v 5)
  let m6 := memUpd8 m5 (a + 6#64) (byteOf64 v 6)
  memUpd8 m6 (a + 7#64) (byteOf64 v 7)

def readMem32Sext64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  let w32 : BitVec 32 := m (a + 3#64) ++ (m (a + 2#64) ++ (m (a + 1#64) ++ m (a + 0#64)))
  (if (w32 &&& 0x80000000#32) != 0#32 then 0xFFFFFFFF#32 else 0#32) ++ w32

def readMem32Zext64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  let w32 : BitVec 32 := m (a + 3#64) ++ (m (a + 2#64) ++ (m (a + 1#64) ++ m (a + 0#64)))
  w32.zeroExtend 64

theorem add_const64_ne (a : BitVec 64) {c1 c2 : BitVec 64} (hne : c1 ≠ c2) :
    a + c1 ≠ a + c2 := by
  intro heq
  have hsub : (a + c1) - a = (a + c2) - a := congrArg (fun x => x - a) heq
  rw [BitVec.add_comm a c1, BitVec.add_sub_cancel,
      BitVec.add_comm a c2, BitVec.add_sub_cancel] at hsub
  exact hne hsub

/-- Unconditional 8-byte little-endian store-then-load roundtrip on `ByteMem`. -/
theorem readMem64_writeMem64_same (m : ByteMem) (a : BitVec 64) (v : BitVec 64) :
    readMem64 (writeMem64 m a v) a = v := by
  dsimp [readMem64, writeMem64]
  repeat first
    | rw [memUpd8_eq]
    | rw [memUpd8_ne _ (add_const64_ne a (by decide))]
  exact pack8_byteOf64 v

/-- Any single byte outside `[a + 0 .. a + 7]` is preserved by `writeMem64`. -/
theorem writeMem64_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 64)
    (h : ∀ k, k < 8 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem64 m a v b = m b := by
  dsimp [writeMem64]
  rw [memUpd8_ne _ (h 7 (by decide)),
      memUpd8_ne _ (h 6 (by decide)),
      memUpd8_ne _ (h 5 (by decide)),
      memUpd8_ne _ (h 4 (by decide)),
      memUpd8_ne _ (h 3 (by decide)),
      memUpd8_ne _ (h 2 (by decide)),
      memUpd8_ne _ (h 1 (by decide)),
      memUpd8_ne _ (h 0 (by decide))]

/-- Disjoint 8-byte little-endian accesses commute cleanly. -/
theorem readMem64_writeMem64_disjoint (m : ByteMem) (a b : BitVec 64) (v : BitVec 64)
    (hdisj : ∀ j, j < 8 → ∀ k, k < 8 → a + BitVec.ofNat 64 j ≠ b + BitVec.ofNat 64 k) :
    readMem64 (writeMem64 m b v) a = readMem64 m a := by
  dsimp [readMem64]
  rw [writeMem64_byte_ne m b (a + 0#64) v (hdisj 0 (by decide)),
      writeMem64_byte_ne m b (a + 1#64) v (hdisj 1 (by decide)),
      writeMem64_byte_ne m b (a + 2#64) v (hdisj 2 (by decide)),
      writeMem64_byte_ne m b (a + 3#64) v (hdisj 3 (by decide)),
      writeMem64_byte_ne m b (a + 4#64) v (hdisj 4 (by decide)),
      writeMem64_byte_ne m b (a + 5#64) v (hdisj 5 (by decide)),
      writeMem64_byte_ne m b (a + 6#64) v (hdisj 6 (by decide)),
      writeMem64_byte_ne m b (a + 7#64) v (hdisj 7 (by decide))]

/-! ### `and rsp, -32` Dynamic Realignment Arithmetic (`0` `omega`, `Init.*`-only) -/

theorem and_mask32_eq_shift (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFE0#64) = ((x >>> 5) <<< 5) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  have hcheck : ∀ (j : Fin 64),
      (0xFFFFFFFFFFFFFFE0#64).getLsbD j.val = (!(decide (j.val < 5)) && decide (j.val < 64)) := by
    decide
  rw [hcheck ⟨i, hi⟩]
  cases h5 : decide (i < 5) with
  | true => simp
  | false =>
    have hge : 5 ≤ i := Nat.not_lt.mp (of_decide_eq_false h5)
    have hadd : 5 + (i - 5) = i := Nat.add_sub_cancel' hge
    simp [hi, hadd]

theorem and_31_toNat (x : BitVec 64) : (x &&& 31#64).toNat = x.toNat % 32 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 5

theorem and_31_lt_32 (x : BitVec 64) : (x &&& 31#64).toNat < 32 := by
  rw [and_31_toNat]
  exact Nat.mod_lt x.toNat (by decide)

theorem and_mask32_eq_sub_rem (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFE0#64) = x - (x &&& 31#64) := by
  apply Eq.symm
  apply (BitVec.sub_eq_iff_eq_add).mpr
  apply Eq.symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and_mask32_eq_shift, and_31_toNat,
      BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hdiv_le : (x.toNat / 32) * 32 ≤ x.toNat := Nat.div_mul_le_self x.toNat 32
  have hdiv_lt : (x.toNat / 32) * 32 < 2 ^ 64 := Nat.lt_of_le_of_lt hdiv_le x.isLt
  rw [Nat.mod_eq_of_lt hdiv_lt]
  have hsum : (x.toNat / 32) * 32 + x.toNat % 32 = x.toNat := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x.toNat 32
  rw [hsum, Nat.mod_eq_of_lt x.isLt]

/-! ## Section 2: Real Variable-Length (`1..15` Byte) x86-64 Byte Decoder -/

inductive AluOp where
  | add | sub | xor | and | or | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp where
  | shl | shr
  deriving DecidableEq, Repr

inductive CondCode where
  | e | ne | b | ae | be | a
  deriving DecidableEq, Repr

/-- Addressing mode decoded from ModR/M + optional SIB + disp0/disp8/disp32. -/
inductive MemAddr where
  | baseDisp (base : Reg) (index : Option (Reg × Nat)) (disp : BitVec 64)
  | ripRel   (disp : BitVec 64)
  deriving DecidableEq, Repr

/-- Decoded x86-64 instruction AST covering real GCC `-O2`/`-O3 -mavx2` `.o` and SFI idioms. -/
inductive X64Instr where
  | nop
  | endbr64
  | vzeroupper
  | movRR64    (dst src : Reg)
  | movRR32    (dst src : Reg)               -- zero-extends 32-bit result to 64-bit
  | movImm64   (dst : Reg) (imm : BitVec 64)
  | movImm32   (dst : Reg) (imm : BitVec 32) -- zero-extends to 64-bit (`mov eax, imm32`)
  | load64     (dst : Reg) (addr : MemAddr)
  | store64    (addr : MemAddr) (src : Reg)
  | load32Zext (dst : Reg) (addr : MemAddr)
  | load32Sext (dst : Reg) (addr : MemAddr)  -- `movsxd` (`0x63`) for `.rodata` jump tables
  | lea64      (dst : Reg) (addr : MemAddr)
  | aluRR64    (op : AluOp) (dst src : Reg)
  | aluImm64   (op : AluOp) (dst : Reg) (imm : BitVec 64)
  | aluRR32    (op : AluOp) (dst src : Reg)
  | aluImm32   (op : AluOp) (dst : Reg) (imm : BitVec 32)
  | shiftImm64 (op : ShiftOp) (dst : Reg) (cnt : Nat)
  | imulRR64   (dst src : Reg)
  | bsf64      (dst src : Reg)
  | tzcnt64    (dst src : Reg)
  | xchg64        (r1 r2 : Reg)
  | xchg32        (r1 r2 : Reg)
  | xchg16        (r1 r2 : Reg)
  | lockAdd64     (addr : MemAddr) (src : Reg)
  | lockAddImm64  (addr : MemAddr) (imm : BitVec 64)
  | lockCmpxchg64 (addr : MemAddr) (src : Reg)
  | push64        (src : Reg)
  | pop64         (dst : Reg)
  | leave64
  | jmpRel        (rel : BitVec 64)
  | jccRel        (cc : CondCode) (rel : BitVec 64)
  | jmpReg        (target : Reg)
  | ret
  | int3
  | ud2
  deriving DecidableEq, Repr

inductive DecodeFault where
  | truncated
  | gpLenExceeded
  | gpRing3Priv
  | udIllegalLock
  | udIllegalVexPrefix
  | udExplicit
  | unsupported
  deriving DecidableEq, Repr

inductive DecodeOutcome where
  | ok    (ins : X64Instr) (len : Nat)
  | fault (f : DecodeFault)
  deriving DecidableEq, Repr

inductive RepPfx where
  | none | f2 | f3
  deriving DecidableEq, Repr

structure PrefixState where
  hasLock    : Bool := false
  rep        : RepPfx := .none
  has66      : Bool := false
  has67      : Bool := false
  hasSeg     : Bool := false
  hasNotrack : Bool := false
  rex        : Option UInt8 := none
  deriving DecidableEq, Repr

def isLegacyPrefix (b : UInt8) : Bool :=
  b == 0xF0 || b == 0xF2 || b == 0xF3 || b == 0x66 || b == 0x67 ||
  b == 0x2E || b == 0x3E || b == 0x64 || b == 0x65

def isRexPrefix (b : UInt8) : Bool :=
  (b &&& 0xF0) == 0x40

def rexW (r : Option UInt8) : Bool :=
  match r with | some b => (b &&& 0x08) != 0 | none => false

def rexR (r : Option UInt8) : Nat :=
  match r with | some b => if (b &&& 0x04) != 0 then 8 else 0 | none => 0

def rexX (r : Option UInt8) : Nat :=
  match r with | some b => if (b &&& 0x02) != 0 then 8 else 0 | none => 0

def rexB (r : Option UInt8) : Nat :=
  match r with | some b => if (b &&& 0x01) != 0 then 8 else 0 | none => 0

def stepPrefix (ps : PrefixState) (b : UInt8) : PrefixState :=
  if b == 0xF0 then { ps with hasLock := true, rex := none }
  else if b == 0xF2 then { ps with rep := .f2, rex := none }
  else if b == 0xF3 then { ps with rep := .f3, rex := none }
  else if b == 0x66 then { ps with has66 := true, rex := none }
  else if b == 0x67 then { ps with has67 := true, rex := none }
  else if b == 0x3E then { ps with hasNotrack := true, rex := none }
  else { ps with hasSeg := true, rex := none }

def scanPrefixes : Nat → PrefixState → Nat → List UInt8 → Option (PrefixState × Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, ps, consumed, [] => some (ps, consumed, [])
  | fuel + 1, ps, consumed, b :: rest =>
      if isLegacyPrefix b then
        scanPrefixes fuel (stepPrefix ps b) (consumed + 1) rest
      else if isRexPrefix b then
        scanPrefixes fuel { ps with rex := some b } (consumed + 1) rest
      else
        some (ps, consumed, b :: rest)

theorem scanPrefixes_append_nonempty :
    ∀ (fuel : Nat) (ps ps' : PrefixState) (c c' : Nat) (bs body sfx : List UInt8),
      scanPrefixes fuel ps c bs = some (ps', c', body) →
      body ≠ [] →
      c' + body.length = c + bs.length ∧
      scanPrefixes fuel ps c (bs ++ sfx) = some (ps', c', body ++ sfx)
  | 0, _, _, _, _, _, _, _, h, _ => nomatch h
  | _ + 1, _, _, _, _, [], _, _, h, hne => by
    dsimp [scanPrefixes] at h
    injection h with h1
    injection h1 with _ h2
    injection h2 with _ hbody
    exact False.elim (hne hbody.symm)
  | fuel + 1, ps, ps', c, c', b :: rest, body, sfx, h, hne => by
    dsimp [scanPrefixes] at h ⊢
    revert h
    cases isLegacyPrefix b with
    | true =>
      intro h; dsimp at h ⊢
      have ih := scanPrefixes_append_nonempty fuel (stepPrefix ps b) ps' (c + 1) c' rest body sfx h hne
      refine ⟨?_, ih.2⟩
      rw [ih.1]
      show c + 1 + rest.length = c + (rest.length + 1)
      rw [Nat.add_assoc c 1 rest.length, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
    | false =>
      dsimp
      cases isRexPrefix b with
      | true =>
        intro h; dsimp at h ⊢
        have ih := scanPrefixes_append_nonempty fuel { ps with rex := some b } ps' (c + 1) c' rest body sfx h hne
        refine ⟨?_, ih.2⟩
        rw [ih.1]
        show c + 1 + rest.length = c + (rest.length + 1)
        rw [Nat.add_assoc c 1 rest.length, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
      | false =>
        intro h; dsimp at h ⊢
        injection h with h1
        injection h1 with hps h2
        injection h2 with hc hbody
        subst hps hc hbody
        exact ⟨rfl, rfl⟩

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- 8-element stride list length (`1/8`th `List.rec` depth in kernel/elaborator `whnf`,
    scaling cleanly past `1,500`-byte leaves under default `maxRecDepth = 512`). -/
def lenTR {α : Type} : List α → Nat
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => 8 + lenTR rest
  | _ :: rest => 1 + lenTR rest
  | [] => 0

theorem lenTR_eq_length {α : Type} : ∀ (xs : List α), lenTR xs = xs.length
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => by
    show 8 + lenTR rest = rest.length + 8
    rw [lenTR_eq_length rest, Nat.add_comm]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _] | [_, _, _] | [_, _] | [_] | [] => rfl

theorem listGet?_append_left {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length → listGet? (xs ++ ys) i = listGet? xs i
  | [], _, _, h => nomatch h
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h => listGet?_append_left xs ys i (Nat.lt_of_succ_lt_succ h)

/-- ModR/M (+ optional SIB + disp0/disp8/disp32) byte count starting at `modrmIdx`. -/
def modrmLenAt (body : List UInt8) (modrmIdx : Nat) : Option Nat :=
  match listGet? body modrmIdx with
  | none => none
  | some modrm =>
    let modBits := (modrm >>> 6) &&& 0x03
    let rmBits  := modrm &&& 0x07
    if modBits == 3 then some 1
    else if rmBits == 4 then
      match listGet? body (modrmIdx + 1) with
      | none => none
      | some sib =>
        let baseBits := sib &&& 0x07
        if modBits == 0 then
          if baseBits == 5 then some 6 else some 2
        else if modBits == 1 then some 3
        else some 6
    else
      if modBits == 0 then
        if rmBits == 5 then some 5 else some 1
      else if modBits == 1 then some 2
      else some 5

theorem modrmLenAt_ge (body : List UInt8) (idx n : Nat)
    (h : modrmLenAt body idx = some n) : 1 ≤ n := by
  dsimp [modrmLenAt] at h
  cases h0 : listGet? body idx with
  | none => rw [h0] at h; nomatch h
  | some modrm =>
    rw [h0] at h; dsimp at h
    split at h
    · injection h with h'; subst h'; decide
    · split at h
      · cases h1 : listGet? body (idx + 1) with
        | none => rw [h1] at h; nomatch h
        | some sib =>
          rw [h1] at h; dsimp at h
          repeat (first | split at h | (injection h with h'; subst h'; decide))
      · repeat (first | split at h | (injection h with h'; subst h'; decide))

theorem modrmLenAt_append (body sfx : List UInt8) (idx n : Nat)
    (h : modrmLenAt body idx = some n) (hle : idx + n ≤ body.length) :
    modrmLenAt (body ++ sfx) idx = some n := by
  have hge1 : 1 ≤ n := modrmLenAt_ge body idx n h
  have hlt0 : idx < body.length := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hge1) hle
  dsimp [modrmLenAt] at h ⊢
  rw [listGet?_append_left body sfx idx hlt0]
  revert h
  cases listGet? body idx with
  | none => intro h; nomatch h
  | some modrm =>
    dsimp
    cases (((modrm >>> 6) &&& 3) == 3) with
    | true => intro h; exact h
    | false =>
      dsimp
      cases ((modrm &&& 7) == 4) with
      | false => intro h; exact h
      | true =>
        dsimp
        cases h1 : listGet? body (idx + 1) with
        | none => intro h; nomatch h
        | some sib =>
          intro h; dsimp at h
          have hge2 : 2 ≤ n := by
            repeat (first | split at h | (injection h with h'; subst h'; decide))
          have hlt1 : idx + 1 < body.length :=
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 2) idx)
              (Nat.le_trans (Nat.add_le_add_left hge2 idx) hle)
          rw [listGet?_append_left body sfx (idx + 1) hlt1, h1]
          exact h

/-- Flat ILD opcode classification avoiding nested `if-else` blowup. -/
inductive IldKind where
  | fixed1
  | fixed2
  | fixed5
  | fixed9
  | modrm1 (immBytes : Nat)
  | vex2
  | esc0F
  deriving DecidableEq, Repr

def classifyOpc (hasRexW : Bool) (opc : UInt8) : IldKind :=
  if opc == 0x90 || opc == 0xC3 || opc == 0xC9 || opc == 0xCC ||
     (opc >= 0x50 && opc <= 0x5F) then .fixed1
  else if opc == 0xEB || (opc >= 0x70 && opc <= 0x7F) then .fixed2
  else if opc == 0x05 || opc == 0x25 || opc == 0xE9 then .fixed5
  else if opc >= 0xB8 && opc <= 0xBF then
    if hasRexW then .fixed9 else .fixed5
  else if opc == 0x01 || opc == 0x03 || opc == 0x09 || opc == 0x0B ||
          opc == 0x21 || opc == 0x23 || opc == 0x29 || opc == 0x2B ||
          opc == 0x31 || opc == 0x33 || opc == 0x39 || opc == 0x3B ||
          opc == 0x63 || opc == 0x85 || opc == 0x89 || opc == 0x8B ||
          opc == 0x8D || opc == 0xD1 || opc == 0xFF then .modrm1 0
  else if opc == 0x83 || opc == 0xC1 || opc == 0x6B then .modrm1 1
  else if opc == 0x81 || opc == 0xC7 || opc == 0x69 then .modrm1 4
  else if opc == 0xC5 then .vex2
  else if opc == 0x0F then .esc0F
  else .fixed1

inductive Esc0FKind where
  | fixed2 | fixed6 | modrm2
  deriving DecidableEq, Repr

def classifyEsc0F (opc2 : UInt8) : Esc0FKind :=
  if opc2 == 0x0B then .fixed2
  else if opc2 >= 0x80 && opc2 <= 0x8F then .fixed6
  else if opc2 == 0x1E || opc2 == 0x1F || opc2 == 0xAF ||
          opc2 == 0xB1 || opc2 == 0xBC then .modrm2
  else .fixed2

def ildBodyLen (ps : PrefixState) (body : List UInt8) : Option Nat :=
  match listGet? body 0 with
  | none => none
  | some opc =>
    match classifyOpc (rexW ps.rex) opc with
    | .fixed1 => some 1
    | .fixed2 => some 2
    | .fixed5 => some 5
    | .fixed9 => some 9
    | .modrm1 immB =>
      match modrmLenAt body 1 with
      | some m => some ((1 + m) + immB)
      | none   => none
    | .vex2 =>
      match listGet? body 1, listGet? body 2 with
      | some _, some vopc =>
        if vopc == 0x77 then some 3
        else
          match modrmLenAt body 3 with
          | some m => some (3 + m)
          | none   => none
      | _, _ => none
    | .esc0F =>
      match listGet? body 1 with
      | none => none
      | some opc2 =>
        match classifyEsc0F opc2 with
        | .fixed2 => some 2
        | .fixed6 => some 6
        | .modrm2 =>
          match modrmLenAt body 2 with
          | some m => some (2 + m)
          | none   => none

theorem ildBodyLen_pos (ps : PrefixState) (body : List UInt8) (n : Nat)
    (h : ildBodyLen ps body = some n) : 1 ≤ n := by
  dsimp [ildBodyLen] at h
  revert h
  cases listGet? body 0 with
  | none => intro h; nomatch h
  | some opc =>
    dsimp
    cases classifyOpc (rexW ps.rex) opc with
    | fixed1 | fixed2 | fixed5 | fixed9 =>
      intro h; injection h with hn; subst hn; decide
    | modrm1 immB =>
      dsimp
      cases modrmLenAt body 1 with
      | none => intro h; nomatch h
      | some m =>
        intro h; injection h with hn; subst hn
        exact Nat.le_trans (Nat.le_add_right 1 m) (Nat.le_add_right (1 + m) immB)
    | vex2 =>
      dsimp
      cases listGet? body 1 with
      | none => intro h; nomatch h
      | some _ =>
        cases listGet? body 2 with
        | none => intro h; nomatch h
        | some vopc =>
          dsimp
          cases (vopc == 0x77) with
          | true => intro h; injection h with hn; subst hn; decide
          | false =>
            dsimp
            cases modrmLenAt body 3 with
            | none => intro h; nomatch h
            | some m =>
              intro h; injection h with hn; subst hn
              exact Nat.le_trans (by decide : 1 ≤ 3) (Nat.le_add_right 3 m)
    | esc0F =>
      dsimp
      cases listGet? body 1 with
      | none => intro h; nomatch h
      | some opc2 =>
        dsimp
        cases classifyEsc0F opc2 with
        | fixed2 | fixed6 => intro h; injection h with hn; subst hn; decide
        | modrm2 =>
          dsimp
          cases modrmLenAt body 2 with
          | none => intro h; nomatch h
          | some m =>
            intro h; injection h with hn; subst hn
            exact Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_right 2 m)

theorem ildBodyLen_append (ps : PrefixState) (body sfx : List UInt8) (n : Nat)
    (h : ildBodyLen ps body = some n) (hle : n ≤ body.length) :
    ildBodyLen ps (body ++ sfx) = some n := by
  have hpos : 1 ≤ n := ildBodyLen_pos ps body n h
  have hlt0 : 0 < body.length := Nat.lt_of_lt_of_le hpos hle
  dsimp [ildBodyLen] at h ⊢
  rw [listGet?_append_left body sfx 0 hlt0]
  revert h
  cases listGet? body 0 with
  | none => intro h; nomatch h
  | some opc =>
    dsimp
    cases classifyOpc (rexW ps.rex) opc with
    | fixed1 | fixed2 | fixed5 | fixed9 => intro h; exact h
    | modrm1 immB =>
      dsimp
      cases hm : modrmLenAt body 1 with
      | none => intro h; nomatch h
      | some m =>
        intro h; injection h with hn; subst hn
        have hmle : 1 + m ≤ body.length := Nat.le_trans (Nat.le_add_right (1 + m) immB) hle
        rw [modrmLenAt_append body sfx 1 m hm hmle]
    | vex2 =>
      dsimp
      cases hb1 : listGet? body 1 with
      | none => intro h; nomatch h
      | some b1 =>
        cases hb2 : listGet? body 2 with
        | none => intro h; nomatch h
        | some vopc =>
          dsimp
          cases hv77 : (vopc == 0x77) with
          | true =>
            intro h; dsimp at h; injection h with hn; subst hn
            rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 3) hle),
                listGet?_append_left body sfx 2 (Nat.lt_of_lt_of_le (by decide : 2 < 3) hle),
                hb1, hb2]; dsimp; rw [hv77]; rfl
          | false =>
            dsimp
            cases hm : modrmLenAt body 3 with
            | none => intro h; nomatch h
            | some m =>
              intro h; injection h with hn; subst hn
              have h3 : 3 ≤ body.length := Nat.le_trans (Nat.le_add_right 3 m) hle
              rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 3) h3),
                  listGet?_append_left body sfx 2 (Nat.lt_of_lt_of_le (by decide : 2 < 3) h3),
                  hb1, hb2]; dsimp; rw [hv77]; dsimp
              rw [modrmLenAt_append body sfx 3 m hm hle]
    | esc0F =>
      dsimp
      cases hb1 : listGet? body 1 with
      | none => intro h; nomatch h
      | some opc2 =>
        dsimp
        cases he : classifyEsc0F opc2 with
        | fixed2 =>
          intro h; injection h with hn; subst hn
          rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) hle), hb1]
          dsimp; rw [he]
        | fixed6 =>
          intro h; injection h with hn; subst hn
          have h2 : 2 ≤ body.length := Nat.le_trans (by decide : 2 ≤ 6) hle
          rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) h2), hb1]
          dsimp; rw [he]
        | modrm2 =>
          dsimp
          cases hm : modrmLenAt body 2 with
          | none => intro h; nomatch h
          | some m =>
            intro h; injection h with hn; subst hn
            have h2 : 2 ≤ body.length := Nat.le_trans (Nat.le_add_right 2 m) hle
            rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) h2), hb1]
            dsimp; rw [he]; dsimp
            rw [modrmLenAt_append body sfx 2 m hm hle]


/-! ### Stage 2 Exact-Length Opcode & ModR/M/SIB Body Parser -/

def u8ToBV8 (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

def readBV32LE (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  u8ToBV8 b3 ++ (u8ToBV8 b2 ++ (u8ToBV8 b1 ++ u8ToBV8 b0))

def readBV64LE (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : BitVec 64 :=
  pack8Bytes (u8ToBV8 b0) (u8ToBV8 b1) (u8ToBV8 b2) (u8ToBV8 b3)
             (u8ToBV8 b4) (u8ToBV8 b5) (u8ToBV8 b6) (u8ToBV8 b7)

def sext8To64 (b : UInt8) : BitVec 64 :=
  let v := u8ToBV8 b
  (if (v &&& 0x80#8) != 0#8 then 0xFFFFFFFFFFFFFF#56 else 0#56) ++ v

def sext8To32 (b : UInt8) : BitVec 32 :=
  let v := u8ToBV8 b
  (if (v &&& 0x80#8) != 0#8 then 0xFFFFFF#24 else 0#24) ++ v

def sext32To64 (b0 b1 b2 b3 : UInt8) : BitVec 64 :=
  let w := readBV32LE b0 b1 b2 b3
  (if (w &&& 0x80000000#32) != 0#32 then 0xFFFFFFFF#32 else 0#32) ++ w

/-- Parse ModR/M + optional SIB + disp0/disp8/disp32 from `bs`, returning
    `(regField, Sum.inl rmReg | Sum.inr memAddr, remainingBytes)`. -/
def parseModRM (ps : PrefixState) (bs : List UInt8) :
    Option (Reg × (Reg ⊕ MemAddr) × List UInt8) :=
  match bs with
  | [] => none
  | modrm :: rest =>
    let modBits := (modrm >>> 6) &&& 0x03
    let regIdx  := rexR ps.rex + ((modrm >>> 3) &&& 0x07).toNat
    let rmBits  := modrm &&& 0x07
    let reg     := regOfNat regIdx
    let rmReg   := regOfNat (rexB ps.rex + rmBits.toNat)
    if modBits == 3 then
      some (reg, .inl rmReg, rest)
    else if rmBits == 4 then
      match rest with
      | [] => none
      | sib :: rest1 =>
        let scaleBits := (sib >>> 6) &&& 0x03
        let idxNum    := rexX ps.rex + ((sib >>> 3) &&& 0x07).toNat
        let idxOpt    := if idxNum == 4 then none else some (regOfNat idxNum, 1 <<< scaleBits.toNat)
        let baseBits  := sib &&& 0x07
        let baseReg   := regOfNat (rexB ps.rex + baseBits.toNat)
        if modBits == 0 then
          if baseBits == 5 then none
          else some (reg, .inr (.baseDisp baseReg idxOpt 0#64), rest1)
        else if modBits == 1 then
          match rest1 with
          | d8 :: rest2 => some (reg, .inr (.baseDisp baseReg idxOpt (sext8To64 d8)), rest2)
          | [] => none
        else
          match rest1 with
          | b0 :: b1 :: b2 :: b3 :: rest2 =>
            some (reg, .inr (.baseDisp baseReg idxOpt (sext32To64 b0 b1 b2 b3)), rest2)
          | _ => none
    else
      if modBits == 0 then
        if rmBits == 5 then
          match rest with
          | b0 :: b1 :: b2 :: b3 :: rest1 =>
            some (reg, .inr (.ripRel (sext32To64 b0 b1 b2 b3)), rest1)
          | _ => none
        else
          some (reg, .inr (.baseDisp rmReg none 0#64), rest)
      else if modBits == 1 then
        match rest with
        | d8 :: rest1 => some (reg, .inr (.baseDisp rmReg none (sext8To64 d8)), rest1)
        | [] => none
      else
        match rest with
        | b0 :: b1 :: b2 :: b3 :: rest1 =>
          some (reg, .inr (.baseDisp rmReg none (sext32To64 b0 b1 b2 b3)), rest1)
        | _ => none

def aluOpOfExt (ext : UInt8) : Option AluOp :=
  match ext with
  | 0 => some .add
  | 1 => some .or
  | 4 => some .and
  | 5 => some .sub
  | 6 => some .xor
  | 7 => some .cmp
  | _ => none

def ccOfLowNibble (n : UInt8) : Option CondCode :=
  match n with
  | 0x2 => some .b
  | 0x3 => some .ae
  | 0x4 => some .e
  | 0x5 => some .ne
  | 0x6 => some .be
  | 0x7 => some .a
  | _   => none

inductive BodyParseResult where
  | okIns (ins : X64Instr)
  | err   (f : DecodeFault)
  deriving DecidableEq, Repr

def parseAluMR (ps : PrefixState) (op : AluOp) (rest : List UInt8) : BodyParseResult :=
  if ps.rep != .none then .err .unsupported
  else match parseModRM ps rest with
  | some (reg, .inl rm, []) =>
    if ps.hasLock then .err .udIllegalLock
    else if rexW ps.rex then .okIns (.aluRR64 op rm reg)
    else if !ps.has66 then .okIns (.aluRR32 op rm reg)
    else .err .unsupported
  | some (reg, .inr addr, []) =>
    if ps.hasLock then
      if op == .add && rexW ps.rex && !ps.has67 then .okIns (.lockAdd64 addr reg)
      else .err .unsupported
    else .err .unsupported
  | _ => .err .unsupported

def parseAluRM (ps : PrefixState) (op : AluOp) (rest : List UInt8) : BodyParseResult :=
  if ps.hasLock then .err .udIllegalLock
  else if ps.rep != .none then .err .unsupported
  else match parseModRM ps rest with
  | some (reg, .inl rm, []) =>
    if rexW ps.rex then .okIns (.aluRR64 op reg rm)
    else if !ps.has66 then .okIns (.aluRR32 op reg rm)
    else .err .unsupported
  | _ => .err .unsupported

/-- Stage 2 exact-slice opcode parser (`exactBody.length = bLen`). -/
def parseExactBody (ps : PrefixState) (exactBody : List UInt8) : BodyParseResult :=
  match exactBody with
  | [] => .err .truncated
  | opc :: rest =>
    if opc == 0xC5 then
      if ps.hasLock || ps.has66 || ps.rep != .none || ps.rex.isSome then
        .err .udIllegalVexPrefix
      else match rest with
      | [_, 0x77] => .okIns .vzeroupper
      | _ => .err .unsupported
    else if opc == 0xC4 then
      if ps.hasLock || ps.has66 || ps.rep != .none || ps.rex.isSome then
        .err .udIllegalVexPrefix
      else .err .unsupported
    else if opc == 0x90 then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none then .err .unsupported
      else if rexB ps.rex == 0 then .okIns .nop
      else if rexW ps.rex then .okIns (.xchg64 .r8 .rax)
      else if !ps.has66 then .okIns (.xchg32 .r8 .rax)
      else .okIns (.xchg16 .r8 .rax)
    else if opc == 0xFA then
      if ps.hasLock then .err .udIllegalLock else .err .gpRing3Priv
    else if opc == 0xC3 then
      if ps.hasLock then .err .udIllegalLock else .okIns .ret
    else if opc == 0xC9 then
      if ps.hasLock then .err .udIllegalLock else .okIns .leave64
    else if opc == 0xCC then
      if ps.hasLock then .err .udIllegalLock else .okIns .int3
    else if opc >= 0x50 && opc <= 0x57 then
      if ps.hasLock then .err .udIllegalLock
      else .okIns (.push64 (regOfNat (rexB ps.rex + (opc - 0x50).toNat)))
    else if opc >= 0x58 && opc <= 0x5F then
      if ps.hasLock then .err .udIllegalLock
      else .okIns (.pop64 (regOfNat (rexB ps.rex + (opc - 0x58).toNat)))
    else if opc >= 0xB8 && opc <= 0xBF then
      if ps.hasLock then .err .udIllegalLock
      else
        let dst := regOfNat (rexB ps.rex + (opc - 0xB8).toNat)
        if rexW ps.rex then
          match rest with
          | [b0, b1, b2, b3, b4, b5, b6, b7] =>
            .okIns (.movImm64 dst (readBV64LE b0 b1 b2 b3 b4 b5 b6 b7))
          | _ => .err .unsupported
        else if !ps.has66 then
          match rest with
          | [b0, b1, b2, b3] => .okIns (.movImm32 dst (readBV32LE b0 b1 b2 b3))
          | _ => .err .unsupported
        else .err .unsupported
    else if opc == 0xEB then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [d8] => .okIns (.jmpRel (sext8To64 d8))
      | _ => .err .unsupported
    else if opc == 0xE9 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] => .okIns (.jmpRel (sext32To64 b0 b1 b2 b3))
      | _ => .err .unsupported
    else if opc >= 0x70 && opc <= 0x7F then
      if ps.hasLock then .err .udIllegalLock
      else match ccOfLowNibble (opc - 0x70), rest with
      | some cc, [d8] => .okIns (.jccRel cc (sext8To64 d8))
      | _, _ => .err .unsupported
    else if opc == 0x05 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] =>
        if rexW ps.rex then .okIns (.aluImm64 .add .rax (sext32To64 b0 b1 b2 b3))
        else if !ps.has66 then .okIns (.aluImm32 .add .rax (readBV32LE b0 b1 b2 b3))
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x25 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] =>
        if rexW ps.rex then .okIns (.aluImm64 .and .rax (sext32To64 b0 b1 b2 b3))
        else if !ps.has66 then .okIns (.aluImm32 .and .rax (readBV32LE b0 b1 b2 b3))
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x89 then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (src, .inl dst, []) =>
        if rexW ps.rex then .okIns (.movRR64 dst src)
        else if !ps.has66 then .okIns (.movRR32 dst src)
        else .err .unsupported
      | some (src, .inr addr, []) =>
        if rexW ps.rex then .okIns (.store64 addr src)
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x8B then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inl src, []) =>
        if rexW ps.rex then .okIns (.movRR64 dst src)
        else if !ps.has66 then .okIns (.movRR32 dst src)
        else .err .unsupported
      | some (dst, .inr addr, []) =>
        if rexW ps.rex then .okIns (.load64 dst addr)
        else if !ps.has66 then .okIns (.load32Zext dst addr)
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x63 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex || ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inr addr, []) => .okIns (.load32Sext dst addr)
      | _ => .err .unsupported
    else if opc == 0x8D then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex || ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inr addr, []) => .okIns (.lea64 dst addr)
      | _ => .err .unsupported
    else if opc == 0x01 then parseAluMR ps .add rest
    else if opc == 0x03 then parseAluRM ps .add rest
    else if opc == 0x09 then parseAluMR ps .or  rest
    else if opc == 0x0B then parseAluRM ps .or  rest
    else if opc == 0x21 then parseAluMR ps .and rest
    else if opc == 0x23 then parseAluRM ps .and rest
    else if opc == 0x29 then parseAluMR ps .sub rest
    else if opc == 0x2B then parseAluRM ps .sub rest
    else if opc == 0x31 then parseAluMR ps .xor rest
    else if opc == 0x33 then parseAluRM ps .xor rest
    else if opc == 0x39 then parseAluMR ps .cmp rest
    else if opc == 0x3B then parseAluRM ps .cmp rest
    else if opc == 0x85 then parseAluMR ps .test rest
    else if opc == 0x83 then
      match parseModRM ps rest with
      | some (_, .inl rm, [imm8]) =>
        if ps.hasLock then .err .udIllegalLock
        else match listGet? rest 0 with
        | some modrm =>
          match aluOpOfExt ((modrm >>> 3) &&& 0x07) with
          | some op =>
            if rexW ps.rex then .okIns (.aluImm64 op rm (sext8To64 imm8))
            else if !ps.has66 then .okIns (.aluImm32 op rm (sext8To32 imm8))
            else .err .unsupported
          | none => .err .unsupported
        | none => .err .unsupported
      | some (_, .inr addr, [imm8]) =>
        match listGet? rest 0 with
        | some modrm =>
          match aluOpOfExt ((modrm >>> 3) &&& 0x07) with
          | some .add =>
            if ps.hasLock && rexW ps.rex && !ps.has67 then
              .okIns (.lockAddImm64 addr (sext8To64 imm8))
            else .err .unsupported
          | some .cmp =>
            if ps.hasLock then .err .udIllegalLock else .err .unsupported
          | _ => .err .unsupported
        | none => .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x81 then
      if ps.hasLock then .err .udIllegalLock
      else match parseModRM ps rest with
      | some (_, .inl rm, [b0, b1, b2, b3]) =>
        match listGet? rest 0 with
        | some modrm =>
          match aluOpOfExt ((modrm >>> 3) &&& 0x07) with
          | some op =>
            if rexW ps.rex then .okIns (.aluImm64 op rm (sext32To64 b0 b1 b2 b3))
            else if !ps.has66 then .okIns (.aluImm32 op rm (readBV32LE b0 b1 b2 b3))
            else .err .unsupported
          | none => .err .unsupported
        | none => .err .unsupported
      | _ => .err .unsupported
    else if opc == 0xC1 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex then .err .unsupported
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, [cnt8]), some modrm =>
        let ext := (modrm >>> 3) &&& 0x07
        if ext == 4 then .okIns (.shiftImm64 .shl rm (cnt8 &&& 0x3F).toNat)
        else if ext == 5 then .okIns (.shiftImm64 .shr rm (cnt8 &&& 0x3F).toNat)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0xD1 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex then .err .unsupported
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, []), some modrm =>
        let ext := (modrm >>> 3) &&& 0x07
        if ext == 4 then .okIns (.shiftImm64 .shl rm 1)
        else if ext == 5 then .okIns (.shiftImm64 .shr rm 1)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0xFF then
      if ps.hasLock then .err .udIllegalLock
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, []), some modrm =>
        if ((modrm >>> 3) &&& 0x07) == 4 then .okIns (.jmpReg rm)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0x0F then
      match rest with
      | [] => .err .truncated
      | opc2 :: rest2 =>
        if opc2 == 0x0B then .err .udExplicit
        else if opc2 == 0x1E then
          if ps.hasLock then .err .udIllegalLock
          else match rest2 with
          | [0xFA] =>
            if ps.rep == .f3 && ps.rex.isNone then .okIns .endbr64
            else if ps.rep == .none then .okIns .nop
            else .err .unsupported
          | [0xFB] =>
            if (ps.rep == .f3 && ps.rex.isNone) || ps.rep == .none then .okIns .nop
            else .err .unsupported
          | _ => .err .unsupported
        else if opc2 == 0xB1 then
          if !rexW ps.rex || ps.rep != .none || ps.has67 then .err .unsupported
          else match parseModRM ps rest2 with
          | some (src, .inr addr, []) =>
            if ps.hasLock then .okIns (.lockCmpxchg64 addr src)
            else .err .unsupported
          | some (_, .inl _, []) =>
            if ps.hasLock then .err .udIllegalLock else .err .unsupported
          | _ => .err .unsupported
        else if opc2 == 0x1F then
          if ps.hasLock then .err .udIllegalLock
          else if ps.rep != .none then .err .unsupported
          else match parseModRM ps rest2, listGet? rest2 0 with
          | some (_, _, []), some modrm =>
            if ((modrm >>> 3) &&& 0x07) == 0 then .okIns .nop
            else .err .unsupported
          | _, _ => .err .unsupported
        else if opc2 >= 0x80 && opc2 <= 0x8F then
          if ps.hasLock then .err .udIllegalLock
          else match ccOfLowNibble (opc2 - 0x80), rest2 with
          | some cc, [b0, b1, b2, b3] => .okIns (.jccRel cc (sext32To64 b0 b1 b2 b3))
          | _, _ => .err .unsupported
        else if opc2 == 0xAF then
          if ps.hasLock then .err .udIllegalLock
          else if !rexW ps.rex || ps.rep != .none then .err .unsupported
          else match parseModRM ps rest2 with
          | some (dst, .inl src, []) => .okIns (.imulRR64 dst src)
          | _ => .err .unsupported
        else if opc2 == 0xBC then
          if ps.hasLock then .err .udIllegalLock
          else if !rexW ps.rex then .err .unsupported
          else match parseModRM ps rest2 with
          | some (dst, .inl src, []) =>
            if ps.rep == .f3 then .okIns (.tzcnt64 dst src)
            else if ps.rep == .none then .okIns (.bsf64 dst src)
            else .err .unsupported
          | _ => .err .unsupported
        else .err .unsupported
    else
      .err .unsupported

/-- Total fuel-bounded (`fuel = 16`) two-stage x86-64 byte decoder. -/
def decodeX64 (bs : List UInt8) : DecodeOutcome :=
  match scanPrefixes 16 {} 0 bs with
  | none => .fault .gpLenExceeded
  | some (ps, pfxLen, body) =>
    match ildBodyLen ps body with
    | none => .fault .truncated
    | some bLen =>
      let exactBody := body.take bLen
      if exactBody.length < bLen then .fault .truncated
      else if pfxLen + bLen > 15 then .fault .gpLenExceeded
      else match parseExactBody ps exactBody with
      | .okIns ins => .ok ins (pfxLen + bLen)
      | .err flt   => .fault flt

/-- Every decoded `.ok ins len` consumes `1 ≤ len ≤ 15` bytes and `len ≤ bs.length`. -/
theorem decodeX64_len_bounds {bs : List UInt8} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 bs = .ok ins len) :
    1 ≤ len ∧ len ≤ 15 ∧ len ≤ bs.length := by
  dsimp [decodeX64] at hok
  revert hok
  cases hs : scanPrefixes 16 {} 0 bs with
  | none => intro h; nomatch h
  | some triple =>
    rcases triple with ⟨ps, pfxLen, body⟩
    dsimp
    cases hi : ildBodyLen ps body with
    | none => intro h; nomatch h
    | some bLen =>
      dsimp
      cases hlt : decide ((body.take bLen).length < bLen) with
      | true =>
        intro h
        simp only [of_decide_eq_true hlt, ite_true] at h
        nomatch h
      | false =>
        have hge : bLen ≤ (body.take bLen).length := Nat.not_lt.mp (of_decide_eq_false hlt)
        have hbody_ge : bLen ≤ body.length :=
          Nat.le_trans hge (List.length_take_le' bLen body)
        have hbpos : 1 ≤ bLen := ildBodyLen_pos ps body bLen hi
        have hne : body ≠ [] := by
          intro heq; subst heq
          have : 1 ≤ 0 := Nat.le_trans hbpos hbody_ge
          nomatch this
        have hscan := scanPrefixes_append_nonempty 16 {} ps 0 pfxLen bs body [] hs hne
        cases hgt15 : decide (pfxLen + bLen > 15) with
        | true =>
          intro h
          simp only [of_decide_eq_false hlt, of_decide_eq_true hgt15, ite_false, ite_true] at h
          nomatch h
        | false =>
          intro h
          have ht1 := of_decide_eq_false hlt
          have ht2 := of_decide_eq_false hgt15
          simp only [ht1, ht2, ite_false] at h
          revert h
          cases parseExactBody ps (body.take bLen) with
          | err _ => intro h; nomatch h
          | okIns _ =>
            intro h; injection h with _ hlen_eq; subst hlen_eq
            refine ⟨Nat.le_trans hbpos (Nat.le_add_left bLen pfxLen), Nat.not_lt.mp ht2, ?_⟩
            have hbs : pfxLen + body.length = bs.length := by
              have t := hscan.1; rw [Nat.zero_add] at t; exact t
            rw [← hbs]
            exact Nat.add_le_add_left hbody_ge pfxLen

/-- Universal prefix-invariance / determinism theorem for variable-length x86-64 decoding:
    if `pfx` decodes to `.ok ins len` and `pfx.length = len`, appending ANY trailing byte
    sequence `sfx` decodes to the exact same `.ok ins len` without unfolding `parseExactBody`! -/
theorem decodeX64_prefix_invariant {pfx : List UInt8} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 pfx = .ok ins len) (sfx : List UInt8) :
    decodeX64 (pfx ++ sfx) = .ok ins len := by
  dsimp [decodeX64] at hok ⊢
  revert hok
  cases hs : scanPrefixes 16 {} 0 pfx with
  | none => intro h; nomatch h
  | some triple =>
    rcases triple with ⟨ps, pfxLen, body⟩
    dsimp
    cases hi : ildBodyLen ps body with
    | none => intro h; nomatch h
    | some bLen =>
      dsimp
      cases hlt : decide ((body.take bLen).length < bLen) with
      | true =>
        intro h
        simp only [of_decide_eq_true hlt, ite_true] at h
        nomatch h
      | false =>
        have ht1 := of_decide_eq_false hlt
        have hge : bLen ≤ (body.take bLen).length := Nat.not_lt.mp ht1
        have hbody_ge : bLen ≤ body.length := Nat.le_trans hge (List.length_take_le' bLen body)
        have hbpos : 1 ≤ bLen := ildBodyLen_pos ps body bLen hi
        have hne : body ≠ [] := by
          intro heq; subst heq
          have : 1 ≤ 0 := Nat.le_trans hbpos hbody_ge
          nomatch this
        have hscan := scanPrefixes_append_nonempty 16 {} ps 0 pfxLen pfx body sfx hs hne
        rw [hscan.2]; dsimp
        rw [ildBodyLen_append ps body sfx bLen hi hbody_ge]; dsimp
        rw [List.take_append_of_le_length hbody_ge]
        intro h
        exact h

-- Kernel `rfl` cross-checks against the live Intel Xeon silicon specimens in `sandsifter_page_oracle.py`
-- and real `gcc 15.2.0 -O2` `.o` encodings:
example : decodeX64 [0xF3, 0x0F, 0x1E, 0xFA] = .ok .endbr64 4 := rfl
example : decodeX64 [0x0F, 0x1E, 0xFA] = .ok .nop 3 := rfl
example : decodeX64 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] = .ok .nop 11 := rfl
example : decodeX64 (List.replicate 14 0x66 ++ [0x90]) = .ok .nop 15 := rfl
example : decodeX64 (List.replicate 15 0x66 ++ [0x90]) = .fault .gpLenExceeded := rfl
example : decodeX64 [0x41, 0x90] = .ok (.xchg32 .r8 .rax) 2 := rfl
example : decodeX64 [0x41, 0x40, 0x90] = .ok .nop 3 := rfl
example : decodeX64 [0x40, 0x41, 0x90] = .ok (.xchg32 .r8 .rax) 3 := rfl
example : decodeX64 [0x41, 0x66, 0x90] = .ok .nop 3 := rfl
example : decodeX64 [0x66, 0x41, 0x90] = .ok (.xchg16 .r8 .rax) 3 := rfl
example : decodeX64 [0x48, 0x67, 0x01, 0xF0] = .ok (.aluRR32 .add .rax .rsi) 4 := rfl
example : decodeX64 [0x67, 0x48, 0x01, 0xF0] = .ok (.aluRR64 .add .rax .rsi) 4 := rfl
example : decodeX64 [0xF0, 0x48, 0x01, 0x07] = .ok (.lockAdd64 (.baseDisp .rdi none 0#64) .rax) 4 := rfl
example : decodeX64 [0xF0, 0x48, 0x01, 0xF0] = .fault .udIllegalLock := rfl
example : decodeX64 [0xF0, 0x48, 0x8B, 0x07] = .fault .udIllegalLock := rfl
example : decodeX64 [0xC5, 0xF8, 0x77] = .ok .vzeroupper 3 := rfl
example : decodeX64 [0x2E, 0xC5, 0xF8, 0x77] = .ok .vzeroupper 4 := rfl
example : decodeX64 [0x66, 0xC5, 0xF8, 0x77] = .fault .udIllegalVexPrefix := rfl
example : decodeX64 [0x48, 0xC5, 0xF8, 0x77] = .fault .udIllegalVexPrefix := rfl
example : decodeX64 [0xF0, 0xC5, 0xF8, 0x77] = .fault .udIllegalVexPrefix := rfl
example : decodeX64 [0x48, 0x0F, 0xBC, 0xD1] = .ok (.bsf64 .rdx .rcx) 4 := rfl
example : decodeX64 [0xF3, 0x48, 0x0F, 0xBC, 0xD1] = .ok (.tzcnt64 .rdx .rcx) 5 := rfl
example : decodeX64 [0x48, 0x83, 0xE4, 0xE0] = .ok (.aluImm64 .and .rsp 0xFFFFFFFFFFFFFFE0#64) 4 := rfl
example : decodeX64 [0x48, 0x89, 0x44, 0x24, 0x08] = .ok (.store64 (.baseDisp .rsp none 8#64) .rax) 5 := rfl
example : decodeX64 [0x4F, 0x8D, 0x04, 0x40] = .ok (.lea64 .r8 (.baseDisp .r8 (some (.r8, 2)) 0#64)) 4 := rfl
example : decodeX64 [0x3E, 0xFF, 0xE0] = .ok (.jmpReg .rax) 3 := rfl


/-! ## Section 3: `ByteCodeTree` Operational Semantics, `DeadFlagCollapse`, & Private Stack Separation -/

/-- Balanced binary tree of raw machine-code byte chunks (`O(log B)` byte lookup). -/
inductive ByteCodeTree where
  | leaf (bytes : List UInt8)
  | node (leftBytes : Nat) (l r : ByteCodeTree)

def ByteCodeTree.getByte? : ByteCodeTree → Nat → Option UInt8
  | .leaf bs, off => listGet? bs off
  | .node lsz l r, off =>
    if off < lsz then l.getByte? off else r.getByte? (off - lsz)

/-- Fetch up to `k` consecutive code bytes starting at `rip` (stopping at unmapped boundary). -/
def fetchBytes (t : ByteCodeTree) : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, rip =>
    match t.getByte? rip with
    | none => []
    | some b => b :: fetchBytes t k (rip + 1)

def fetchWindow16 (t : ByteCodeTree) (rip : Nat) : List UInt8 :=
  fetchBytes t 16 rip

theorem fetchBytes_prefix :
    ∀ (pfx : List UInt8) (t : ByteCodeTree) (k addr : Nat),
      pfx.length ≤ k →
      (∀ i, i < pfx.length → t.getByte? (addr + i) = listGet? pfx i) →
      ∃ sfx, fetchBytes t k addr = pfx ++ sfx
  | [], t, k, addr, _, _ => ⟨fetchBytes t k addr, rfl⟩
  | _ :: _, _, 0, _, hle, _ => nomatch hle
  | b :: bs, t, k + 1, addr, hle, hget => by
    have h0 : t.getByte? addr = some b := by
      have t0 := hget 0 (Nat.zero_lt_succ bs.length)
      rw [Nat.add_zero] at t0
      exact t0
    have hle' : bs.length ≤ k := Nat.le_of_succ_le_succ hle
    have hget' : ∀ i, i < bs.length → t.getByte? ((addr + 1) + i) = listGet? bs i := by
      intro i hi
      have ti := hget (i + 1) (Nat.succ_lt_succ hi)
      rw [Nat.add_assoc addr 1 i, Nat.add_comm 1 i]
      exact ti
    rcases fetchBytes_prefix bs t k (addr + 1) hle' hget' with ⟨sfx, hsfx⟩
    refine ⟨sfx, ?_⟩
    dsimp [fetchBytes]
    rw [h0]; dsimp
    rw [hsfx]

/-- Machine state over byte-indexed `rip`, 16 64-bit GPRs, 6 status flags, and `ByteMem`. -/
structure X64State where
  rip    : Nat
  regs   : Reg → BitVec 64
  flags  : RFlags
  mem    : ByteMem
  halted : Bool := false
  fault  : Bool := false

structure X64ObjImage where
  code : ByteCodeTree

def evalAddr (s : X64State) (nextRip : Nat) : MemAddr → BitVec 64
  | .baseDisp base none disp => s.regs base + disp
  | .baseDisp base (some (idx, scale)) disp =>
    s.regs base + s.regs idx * BitVec.ofNat 64 scale + disp
  | .ripRel disp => BitVec.ofNat 64 nextRip + disp

def aluVal64 (op : AluOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add => a + b
  | .sub | .cmp => a - b
  | .xor => a ^^^ b
  | .and | .test => a &&& b
  | .or  => a ||| b

def evalAluFlags64 (op : AluOp) (a b : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res := aluVal64 op a b
  let pf  := parity8 (byteOf64 res 0)
  let zf  := res == 0#64
  let sf  := res.msb
  match op with
  | .add =>
    let cf := decide (a.toNat + b.toNat ≥ 2 ^ 64)
    let af := decide ((a &&& 0xF#64).toNat + (b &&& 0xF#64).toNat ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .sub | .cmp =>
    let cf := decide (a.toNat < b.toNat)
    let af := decide ((a &&& 0xF#64).toNat < (b &&& 0xF#64).toNat)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .xor | .and | .or | .test =>
    -- Intel SDM Vol. 2: logical operations clear CF/OF, set SF/ZF/PF, leave AF undefined!
    (res, { cf := false, pf, af := nd.af, zf, sf, of := false })

def evalAluFlags32 (op : AluOp) (a32 b32 : BitVec 32) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res32 : BitVec 32 :=
    match op with
    | .add => a32 + b32
    | .sub | .cmp => a32 - b32
    | .xor => a32 ^^^ b32
    | .and | .test => a32 &&& b32
    | .or  => a32 ||| b32
  let res64 := res32.zeroExtend 64
  let pf := parity8 (BitVec.extractLsb' 0 8 res32)
  let zf := res32 == 0#32
  let sf := res32.msb
  match op with
  | .add =>
    let cf := decide (a32.toNat + b32.toNat ≥ 2 ^ 32)
    let af := decide ((a32 &&& 0xF#32).toNat + (b32 &&& 0xF#32).toNat ≥ 16)
    let of := (a32.msb == b32.msb) && (res32.msb != a32.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .sub | .cmp =>
    let cf := decide (a32.toNat < b32.toNat)
    let af := decide ((a32 &&& 0xF#32).toNat < (b32 &&& 0xF#32).toNat)
    let of := (a32.msb != b32.msb) && (res32.msb != a32.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .xor | .and | .or | .test =>
    (res64, { cf := false, pf, af := nd.af, zf, sf, of := false })

def shiftVal64 (op : ShiftOp) (a : BitVec 64) (cnt : Nat) : BitVec 64 :=
  let c := cnt % 64
  match op with
  | .shl => a <<< c
  | .shr => a >>> c

def evalShift64 (op : ShiftOp) (a : BitVec 64) (cnt : Nat) (oldF : RFlags) (nd : UndefFlags) :
    BitVec 64 × RFlags :=
  let c := cnt % 64
  if c == 0 then (a, oldF)
  else
    let res := shiftVal64 op a cnt
    let cfBit := match op with | .shl => a.getLsbD (64 - c) | .shr => a.getLsbD (c - 1)
    let ofBit := if c == 1 then (match op with | .shl => res.msb != cfBit | .shr => a.msb) else nd.of
    (res, { cf := cfBit, pf := parity8 (byteOf64 res 0), af := nd.af,
            zf := res == 0#64, sf := res.msb, of := ofBit })

def sext64ValTo128 (v : BitVec 64) : BitVec 128 :=
  (if (v &&& 0x8000000000000000#64) != 0#64 then 0xFFFFFFFFFFFFFFFF#64 else 0#64) ++ v

def evalImul64 (a b : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res := a * b
  let p128 : BitVec 128 := sext64ValTo128 a * sext64ValTo128 b
  let ovf : Bool := p128 != sext64ValTo128 res
  -- Intel SDM Vol. 2 + Intel Xeon silicon measurement (`0 * 7` -> `ZF = 0, PF = 1`):
  -- IMUL sets CF and OF, leaving SF, ZF, AF, PF architecturally undefined!
  (res, { cf := ovf, pf := nd.pf, af := nd.af, zf := nd.zf, sf := nd.sf, of := ovf })

def ctzLoop : Nat → Nat → BitVec 64 → Nat
  | 0, acc, _ => acc
  | fuel + 1, idx, x =>
    if x.getLsbD idx then idx else ctzLoop fuel (idx + 1) x

def ctz64 (x : BitVec 64) : Nat := ctzLoop 64 0 x

def evalBsf64 (oldDst src : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  if src == 0#64 then
    (oldDst, { cf := nd.cf, pf := nd.pf, af := nd.af, zf := true, sf := nd.sf, of := nd.of })
  else
    (BitVec.ofNat 64 (ctz64 src),
     { cf := nd.cf, pf := nd.pf, af := nd.af, zf := false, sf := nd.sf, of := nd.of })

def evalTzcnt64 (src : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res := BitVec.ofNat 64 (ctz64 src)
  (res, { cf := src == 0#64, pf := nd.pf, af := nd.af, zf := res == 0#64, sf := nd.sf, of := nd.of })

def evalCond (cc : CondCode) (f : RFlags) : Bool :=
  match cc with
  | .e  => f.zf
  | .ne => !f.zf
  | .b  => f.cf
  | .ae => !f.cf
  | .be => f.cf || f.zf
  | .a  => !f.cf && !f.zf

def aluWritesDst : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- Single-step x86-64 small-step transition decoding directly from the 16-byte fetch window
    at `s.rip` and advancing `s.rip` by the exact decoded byte length `len ∈ 1..15`. -/
def stepX64 (img : X64ObjImage) (nd : UndefFlags) (s : X64State) : X64State :=
  if s.halted || s.fault then s
  else
    match decodeX64 (fetchWindow16 img.code s.rip) with
    | .fault _ => { s with fault := true }
    | .ok ins len =>
      let nextRip := s.rip + len
      match ins with
      | .nop | .endbr64 | .vzeroupper =>
        { s with rip := nextRip }
      | .movRR64 dst src =>
        { s with rip := nextRip, regs := regUpd s.regs dst (s.regs src) }
      | .movRR32 dst src =>
        let zext := (BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64
        { s with rip := nextRip, regs := regUpd s.regs dst zext }
      | .movImm64 dst imm =>
        { s with rip := nextRip, regs := regUpd s.regs dst imm }
      | .movImm32 dst imm32 =>
        { s with rip := nextRip, regs := regUpd s.regs dst (imm32.zeroExtend 64) }
      | .load64 dst addr =>
        let ea := evalAddr s nextRip addr
        { s with rip := nextRip, regs := regUpd s.regs dst (readMem64 s.mem ea) }
      | .store64 addr src =>
        let ea := evalAddr s nextRip addr
        { s with rip := nextRip, mem := writeMem64 s.mem ea (s.regs src) }
      | .load32Zext dst addr =>
        let ea := evalAddr s nextRip addr
        { s with rip := nextRip, regs := regUpd s.regs dst (readMem32Zext64 s.mem ea) }
      | .load32Sext dst addr =>
        let ea := evalAddr s nextRip addr
        { s with rip := nextRip, regs := regUpd s.regs dst (readMem32Sext64 s.mem ea) }
      | .lea64 dst addr =>
        let ea := evalAddr s nextRip addr
        { s with rip := nextRip, regs := regUpd s.regs dst ea }
      | .aluRR64 op dst src =>
        let (res, fl) := evalAluFlags64 op (s.regs dst) (s.regs src) nd
        let regs' := if aluWritesDst op then regUpd s.regs dst res else s.regs
        { s with rip := nextRip, regs := regs', flags := fl }
      | .aluImm64 op dst imm =>
        let (res, fl) := evalAluFlags64 op (s.regs dst) imm nd
        let regs' := if aluWritesDst op then regUpd s.regs dst res else s.regs
        { s with rip := nextRip, regs := regs', flags := fl }
      | .aluRR32 op dst src =>
        let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
        let b32 := BitVec.extractLsb' 0 32 (s.regs src)
        let (res64, fl) := evalAluFlags32 op a32 b32 nd
        let regs' := if aluWritesDst op then regUpd s.regs dst res64 else s.regs
        { s with rip := nextRip, regs := regs', flags := fl }
      | .aluImm32 op dst imm32 =>
        let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
        let (res64, fl) := evalAluFlags32 op a32 imm32 nd
        let regs' := if aluWritesDst op then regUpd s.regs dst res64 else s.regs
        { s with rip := nextRip, regs := regs', flags := fl }
      | .shiftImm64 op dst cnt =>
        let (res, fl) := evalShift64 op (s.regs dst) cnt s.flags nd
        { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
      | .imulRR64 dst src =>
        let (res, fl) := evalImul64 (s.regs dst) (s.regs src) nd
        { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
      | .bsf64 dst src =>
        let (res, fl) := evalBsf64 (s.regs dst) (s.regs src) nd
        { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
      | .tzcnt64 dst src =>
        let (res, fl) := evalTzcnt64 (s.regs src) nd
        { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
      | .xchg64 r1 r2 =>
        let v1 := s.regs r1
        let v2 := s.regs r2
        { s with rip := nextRip, regs := regUpd (regUpd s.regs r1 v2) r2 v1 }
      | .xchg32 r1 r2 =>
        let v1 := (BitVec.extractLsb' 0 32 (s.regs r1)).zeroExtend 64
        let v2 := (BitVec.extractLsb' 0 32 (s.regs r2)).zeroExtend 64
        { s with rip := nextRip, regs := regUpd (regUpd s.regs r1 v2) r2 v1 }
      | .xchg16 r1 r2 =>
        let v1 := (BitVec.extractLsb' 16 48 (s.regs r1)) ++ (BitVec.extractLsb' 0 16 (s.regs r2))
        let v2 := (BitVec.extractLsb' 16 48 (s.regs r2)) ++ (BitVec.extractLsb' 0 16 (s.regs r1))
        { s with rip := nextRip, regs := regUpd (regUpd s.regs r1 v1) r2 v2 }
      | .lockAdd64 addr src =>
        let ea := evalAddr s nextRip addr
        let (res, fl) := evalAluFlags64 .add (readMem64 s.mem ea) (s.regs src) nd
        { s with rip := nextRip, mem := writeMem64 s.mem ea res, flags := fl }
      | .lockAddImm64 addr imm =>
        let ea := evalAddr s nextRip addr
        let (res, fl) := evalAluFlags64 .add (readMem64 s.mem ea) imm nd
        { s with rip := nextRip, mem := writeMem64 s.mem ea res, flags := fl }
      | .lockCmpxchg64 addr src =>
        let ea := evalAddr s nextRip addr
        let dstVal := readMem64 s.mem ea
        let (_, fl) := evalAluFlags64 .cmp (s.regs .rax) dstVal nd
        if s.regs .rax == dstVal then
          { s with rip := nextRip, mem := writeMem64 s.mem ea (s.regs src), flags := fl }
        else
          { s with rip := nextRip, regs := regUpd s.regs .rax dstVal, flags := fl }
      | .push64 src =>
        let v := s.regs src
        let rsp' := s.regs .rsp - 8#64
        { s with rip := nextRip, regs := regUpd s.regs .rsp rsp', mem := writeMem64 s.mem rsp' v }
      | .pop64 dst =>
        let rsp0 := s.regs .rsp
        let v := readMem64 s.mem rsp0
        let regs1 := regUpd s.regs .rsp (rsp0 + 8#64)
        { s with rip := nextRip, regs := regUpd regs1 dst v }
      | .leave64 =>
        let rbp0 := s.regs .rbp
        let savedRbp := readMem64 s.mem rbp0
        let regs1 := regUpd s.regs .rsp (rbp0 + 8#64)
        { s with rip := nextRip, regs := regUpd regs1 .rbp savedRbp }
      | .jmpRel rel =>
        { s with rip := (BitVec.ofNat 64 nextRip + rel).toNat }
      | .jccRel cc rel =>
        if evalCond cc s.flags then
          { s with rip := (BitVec.ofNat 64 nextRip + rel).toNat }
        else
          { s with rip := nextRip }
      | .jmpReg tgt =>
        { s with rip := (s.regs tgt).toNat }
      | .ret =>
        { s with halted := true }
      | .int3 | .ud2 =>
        { s with fault := true }

/-- Multi-step execution parameterized by a demonic hardware choice stream `nd : Nat → UndefFlags`. -/
def runX64 (img : X64ObjImage) : Nat → (Nat → UndefFlags) → X64State → X64State
  | 0, _, s => s
  | n + 1, nd, s => runX64 img n (fun k => nd (k + 1)) (stepX64 img (nd 0) s)

theorem runX64_zero (img : X64ObjImage) (nd : Nat → UndefFlags) (s : X64State) :
    runX64 img 0 nd s = s := rfl

theorem runX64_succ (img : X64ObjImage) (n : Nat) (nd : Nat → UndefFlags) (s : X64State) :
    runX64 img (n + 1) nd s = runX64 img n (fun k => nd (k + 1)) (stepX64 img (nd 0) s) := rfl

theorem runX64_add (img : X64ObjImage) :
    ∀ (m n : Nat) (nd : Nat → UndefFlags) (s : X64State),
      runX64 img (m + n) nd s = runX64 img n (fun k => nd (k + m)) (runX64 img m nd s)
  | 0, n, nd, s => by
    rw [Nat.zero_add]
    have hnd : (fun k => nd (k + 0)) = nd := funext (fun k => congrArg nd (Nat.add_zero k))
    rw [hnd]; rfl
  | m + 1, n, nd, s => by
    rw [Nat.succ_add, runX64_succ, runX64_succ]
    have ih := runX64_add img m n (fun k => nd (k + 1)) (stepX64 img (nd 0) s)
    have hnd : (fun k => nd (k + m + 1)) = (fun k => nd (k + (m + 1))) :=
      funext (fun k => congrArg nd (Nat.add_assoc k m 1))
    rw [ih, hnd]

/-- Unconditional kernel WHNF cutpoint firewall (`Inductive`, opaque to delta reduction). -/
structure CutBox (tag : Nat) (P : Prop) : Prop where
  val : P

/-- Negative-control theorem: reading `ZF` immediately after `imul rax, rsi` (`48 0f af c6; 74 08`)
    diverges across valid demonic hardware flag choices (`nd.zf = false` as observed on Intel
    Ice Lake-SP Xeon for `0 * 7 = 0` vs. `nd.zf = true`), proving `DeadFlagCollapse` MUST reject
    live-out undefined flags! -/
def imulJeImg : X64ObjImage :=
  { code := .leaf [0x48, 0x0F, 0xAF, 0xC6, 0x74, 0x08, 0xC3] }

theorem imul_je_diverges_under_demonic_flags :
    let m0 : ByteMem := fun _ => 0#8
    let regs0 : Reg → BitVec 64 := fun r => if r == .rax then 0#64 else if r == .rsi then 7#64 else 0#64
    let s0 : X64State := { rip := 0, regs := regs0, flags := {}, mem := m0 }
    let ndIntel : Nat → UndefFlags := fun _ => { pf := true, zf := false }
    let ndAlt   : Nat → UndefFlags := fun _ => { pf := false, zf := true }
    (runX64 imulJeImg 2 ndIntel s0).rip = 6 ∧
    (runX64 imulJeImg 2 ndAlt   s0).rip = 14 := by
  decide

/-! ### Unexposed Private Stack-Frame Separation & Slot Byte-Disjointness (`0` `omega`) -/

def spillSlotAddr (rsp : BitVec 64) (slot : Nat) : BitVec 64 :=
  rsp + BitVec.ofNat 64 (slot * 8)

/-- Byte `a` lies outside the `maxSlots` 8-byte spill array `[rsp .. rsp + maxSlots * 8)`. -/
def OutsideSpillRange (rsp : BitVec 64) (maxSlots : Nat) (a : BitVec 64) : Prop :=
  maxSlots * 8 ≤ (a - rsp).toNat

/-- Caller/Kripke private stack envelope `[rspEntry - maxEnv, rspEntry)`:
    `a = rspEntry - d` with `1 ≤ d ≤ maxEnv`. -/
def InStackEnvelope (rspEntry : BitVec 64) (maxEnv : Nat) (a : BitVec 64) : Prop :=
  let d := (rspEntry - a).toNat
  1 ≤ d ∧ d ≤ maxEnv

theorem slot_byte_offset_div8 {i b : Nat} (hb : b < 8) :
    (i * 8 + b) / 8 = i := by
  have h1 : (b + 8 * i) / 8 = b / 8 + i := Nat.add_mul_div_left b i (by decide : 0 < 8)
  rw [Nat.mul_comm i 8, Nat.add_comm (8 * i) b, h1, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem slot_bytes_disjoint (rsp : BitVec 64) {maxSlots i j : Nat}
    (hbound : maxSlots * 8 < 2 ^ 64)
    (hi : i < maxSlots) (hj : j < maxSlots) (hne : i ≠ j) :
    ∀ b1, b1 < 8 → ∀ b2, b2 < 8 →
      spillSlotAddr rsp i + BitVec.ofNat 64 b1 ≠ spillSlotAddr rsp j + BitVec.ofNat 64 b2 := by
  intro b1 hb1 b2 hb2 heq
  dsimp [spillSlotAddr] at heq
  rw [BitVec.add_assoc, BitVec.add_assoc] at heq
  have hsub : (rsp + (BitVec.ofNat 64 (i * 8) + BitVec.ofNat 64 b1)) - rsp =
              (rsp + (BitVec.ofNat 64 (j * 8) + BitVec.ofNat 64 b2)) - rsp :=
    congrArg (fun x => x - rsp) heq
  rw [BitVec.add_comm rsp _, BitVec.add_sub_cancel,
      BitVec.add_comm rsp _, BitVec.add_sub_cancel] at hsub
  have hi_lt : i * 8 + b1 < 2 ^ 64 := by
    have hle : i + 1 ≤ maxSlots := hi
    have hm : (i + 1) * 8 ≤ maxSlots * 8 := Nat.mul_le_mul_right 8 hle
    rw [Nat.add_mul, Nat.one_mul] at hm
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb1 (i * 8)) (Nat.le_trans hm (Nat.le_of_lt hbound))
  have hj_lt : j * 8 + b2 < 2 ^ 64 := by
    have hle : j + 1 ≤ maxSlots := hj
    have hm : (j + 1) * 8 ≤ maxSlots * 8 := Nat.mul_le_mul_right 8 hle
    rw [Nat.add_mul, Nat.one_mul] at hm
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb2 (j * 8)) (Nat.le_trans hm (Nat.le_of_lt hbound))
  have hnat : ((BitVec.ofNat 64 (i * 8) + BitVec.ofNat 64 b1)).toNat =
              ((BitVec.ofNat 64 (j * 8) + BitVec.ofNat 64 b2)).toNat :=
    congrArg BitVec.toNat hsub
  have hi8 : i * 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right (i * 8) b1) hi_lt
  have hj8 : j * 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right (j * 8) b2) hj_lt
  have hb1_64 : b1 < 2 ^ 64 := Nat.lt_trans hb1 (by decide)
  have hb2_64 : b2 < 2 ^ 64 := Nat.lt_trans hb2 (by decide)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi8, Nat.mod_eq_of_lt hb1_64, Nat.mod_eq_of_lt hi_lt,
      BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hj8, Nat.mod_eq_of_lt hb2_64, Nat.mod_eq_of_lt hj_lt] at hnat
  have hdiv : (i * 8 + b1) / 8 = (j * 8 + b2) / 8 := congrArg (· / 8) hnat
  rw [slot_byte_offset_div8 hb1, slot_byte_offset_div8 hb2] at hdiv
  exact hne hdiv

theorem outside_spill_byte_ne (rsp a : BitVec 64) {maxSlots slot : Nat}
    (hbound : maxSlots * 8 < 2 ^ 64)
    (hout : OutsideSpillRange rsp maxSlots a)
    (hslot : slot < maxSlots) :
    ∀ k, k < 8 → a ≠ spillSlotAddr rsp slot + BitVec.ofNat 64 k := by
  intro k hk heq
  subst heq
  unfold OutsideSpillRange spillSlotAddr at hout
  rw [BitVec.add_assoc, BitVec.add_comm rsp _, BitVec.add_sub_cancel] at hout
  have hsl_lt : slot * 8 + k < maxSlots * 8 := by
    have hm : (slot + 1) * 8 ≤ maxSlots * 8 := Nat.mul_le_mul_right 8 hslot
    rw [Nat.add_mul, Nat.one_mul] at hm
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (slot * 8)) hm
  have hsl_64 : slot * 8 + k < 2 ^ 64 := Nat.lt_trans hsl_lt hbound
  have hs8_64 : slot * 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ k) hsl_64
  have hk_64  : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hs8_64, Nat.mod_eq_of_lt hk_64, Nat.mod_eq_of_lt hsl_64] at hout
  exact Nat.not_lt_of_ge hout hsl_lt

/-- Private Stack-Frame Separation under dynamic `and rsp, -32` realignment:
    If prologue executes `push rbp; mov rbp, rsp; and rsp, -32; sub rsp, allocBytes`,
    yielding `rspAligned = ((rspEntry - 8) &&& -32) - allocBytes`, then EVERY byte outside
    `InStackEnvelope rspEntry (8 + 31 + allocBytes)` AND all 8 saved `rbp` bytes at
    `[rspEntry - 8 .. rspEntry - 1]` automatically satisfy `OutsideSpillRange rspAligned maxSlots`
    whenever `maxSlots * 8 ≤ allocBytes` and `8 + 31 + allocBytes < 2^63`! -/
theorem realigned_frame_envelope_separation
    (rspEntry a : BitVec 64) (allocBytes maxSlots : Nat)
    (hslots : maxSlots * 8 ≤ allocBytes)
    (henv_bound : 39 + allocBytes < 2 ^ 63)
    (hnot_env : ¬ InStackEnvelope rspEntry (39 + allocBytes) a) :
    let rspAligned := ((rspEntry - 8#64) &&& 0xFFFFFFFFFFFFFFE0#64) - BitVec.ofNat 64 allocBytes
    OutsideSpillRange rspAligned maxSlots a := by
  intro rspAligned
  unfold OutsideSpillRange
  cases hlt : decide ((a - rspAligned).toNat < maxSlots * 8) with
  | false => exact Nat.not_lt.mp (of_decide_eq_false hlt)
  | true =>
    exfalso
    have hoff_lt : (a - rspAligned).toNat < maxSlots * 8 := of_decide_eq_true hlt
    let pad := ((rspEntry - 8#64) &&& 31#64).toNat
    have hpad_lt : pad < 32 := and_31_lt_32 (rspEntry - 8#64)
    have halign : ((rspEntry - 8#64) &&& 0xFFFFFFFFFFFFFFE0#64) =
        (rspEntry - 8#64) - ((rspEntry - 8#64) &&& 31#64) :=
      and_mask32_eq_sub_rem (rspEntry - 8#64)
    let totalDrop : Nat := 8 + pad + allocBytes
    have htd_le : totalDrop ≤ 39 + allocBytes := by
      have hp31 : pad ≤ 31 := Nat.le_of_lt_succ hpad_lt
      have h8p : 8 + pad ≤ 39 := Nat.add_le_add_left hp31 8
      exact Nat.add_le_add_right h8p allocBytes
    have htd_64 : totalDrop < 2 ^ 64 :=
      Nat.lt_trans (Nat.lt_of_le_of_lt htd_le henv_bound) (by decide)
    have hrsp_eq : rspAligned = rspEntry - BitVec.ofNat 64 totalDrop := by
      dsimp [rspAligned, totalDrop]
      rw [halign]
      have hrem_eq : ((rspEntry - 8#64) &&& 31#64) = BitVec.ofNat 64 pad := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hpad_lt (by decide))]
      have h8_eq : (8#64 : BitVec 64) = BitVec.ofNat 64 8 := rfl
      rw [hrem_eq, h8_eq, BitVec.sub_sub, BitVec.sub_sub,
          ← BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    let off := (a - rspAligned).toNat
    have hoff_le_alloc : off < allocBytes := Nat.lt_of_lt_of_le hoff_lt hslots
    have hoff_le_td : off ≤ totalDrop :=
      Nat.le_trans (Nat.le_of_lt hoff_le_alloc) (Nat.le_add_left allocBytes (8 + pad))
    have ha_eq : a = rspAligned + BitVec.ofNat 64 off := by
      have hb : BitVec.ofNat 64 off = a - rspAligned := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a - rspAligned).isLt]
      rw [hb, BitVec.add_comm, BitVec.sub_add_cancel]
    have hdiff : rspEntry - a = BitVec.ofNat 64 (totalDrop - off) := by
      rw [ha_eq, hrsp_eq]
      apply (BitVec.sub_eq_iff_eq_add).mpr
      have hsum_bv : BitVec.ofNat 64 (totalDrop - off) + BitVec.ofNat 64 off = BitVec.ofNat 64 totalDrop := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hoff_le_td]
      rw [← BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (totalDrop - off)) _,
          BitVec.add_assoc, hsum_bv, BitVec.sub_add_cancel]
    have h_in_env : InStackEnvelope rspEntry (39 + allocBytes) a := by
      unfold InStackEnvelope
      dsimp only
      rw [hdiff, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le totalDrop off) htd_64)]
      have hge1 : 1 ≤ totalDrop - off := by
        have hlt_td : off < totalDrop :=
          Nat.lt_of_lt_of_le hoff_le_alloc (Nat.le_add_left allocBytes (8 + pad))
        exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt_td)
      have hle_env : totalDrop - off ≤ 39 + allocBytes :=
        Nat.le_trans (Nat.sub_le totalDrop off) htd_le
      exact ⟨hge1, hle_env⟩
    exact hnot_env h_in_env

/-! ### Backward `DeadFlagCollapse` + Sharded `ByteCodeTree` Lifting (`checkByteLeaf_sound`) -/

structure LiftedX64State where
  regs  : Reg → BitVec 64
  slots : Nat → BitVec 64
  flags : RFlags

def AbstractsLeaf (maxSlots : Nat) (live : FlagMask) (s : X64State) (l : LiftedX64State) : Prop :=
  s.halted = false ∧
  s.fault = false ∧
  (∀ r, s.regs r = l.regs r) ∧
  (∀ slot, slot < maxSlots → readMem64 s.mem (spillSlotAddr (s.regs .rsp) slot) = l.slots slot) ∧
  FlagsAgreeOn live s.flags l.flags

/-- Collapsed pure SSA-like lifted instruction where dead `RFLAGS` (both deterministic `parity8`
    and demonic `UndefFlags`) and byte-memory stack-spill aliasing are completely erased! -/
inductive CollapsedOp where
  | nop
  | movRR64        (dst src : Reg)
  | movRR32        (dst src : Reg)
  | movImm64       (dst : Reg) (imm : BitVec 64)
  | movImm32       (dst : Reg) (imm : BitVec 32)
  | leaBaseDisp    (dst base : Reg) (idx : Option (Reg × Nat)) (disp : BitVec 64)
  | spillStore     (slot : Nat) (src : Reg)
  | spillLoad      (dst : Reg) (slot : Nat)
  | aluRR64Dead    (op : AluOp) (dst src : Reg)
  | aluImm64Dead   (op : AluOp) (dst : Reg) (imm : BitVec 64)
  | aluRR64Live    (op : AluOp) (dst src : Reg)
  | aluImm64Live   (op : AluOp) (dst : Reg) (imm : BitVec 64)
  | shiftImm64Dead (op : ShiftOp) (dst : Reg) (cnt : Nat)
  | imulRR64Dead   (dst src : Reg)
  deriving DecidableEq, Repr

def evalAluDetFlags64 (op : AluOp) (a b : BitVec 64) : BitVec 64 × RFlags :=
  evalAluFlags64 op a b {}

def stepCollapsedOp (cop : CollapsedOp) (l : LiftedX64State) : LiftedX64State :=
  match cop with
  | .nop => l
  | .movRR64 dst src => { l with regs := regUpd l.regs dst (l.regs src) }
  | .movRR32 dst src =>
    { l with regs := regUpd l.regs dst ((BitVec.extractLsb' 0 32 (l.regs src)).zeroExtend 64) }
  | .movImm64 dst imm => { l with regs := regUpd l.regs dst imm }
  | .movImm32 dst imm32 => { l with regs := regUpd l.regs dst (imm32.zeroExtend 64) }
  | .leaBaseDisp dst base none disp =>
    { l with regs := regUpd l.regs dst (l.regs base + disp) }
  | .leaBaseDisp dst base (some (idx, sc)) disp =>
    { l with regs := regUpd l.regs dst (l.regs base + l.regs idx * BitVec.ofNat 64 sc + disp) }
  | .spillStore slot src =>
    { l with slots := fun k => if k = slot then l.regs src else l.slots k }
  | .spillLoad dst slot =>
    { l with regs := regUpd l.regs dst (l.slots slot) }
  | .aluRR64Dead op dst src =>
    let res := aluVal64 op (l.regs dst) (l.regs src)
    let regs' := if aluWritesDst op then regUpd l.regs dst res else l.regs
    { l with regs := regs' }
  | .aluImm64Dead op dst imm =>
    let res := aluVal64 op (l.regs dst) imm
    let regs' := if aluWritesDst op then regUpd l.regs dst res else l.regs
    { l with regs := regs' }
  | .aluRR64Live op dst src =>
    let (res, fl) := evalAluDetFlags64 op (l.regs dst) (l.regs src)
    let regs' := if aluWritesDst op then regUpd l.regs dst res else l.regs
    { l with regs := regs', flags := fl }
  | .aluImm64Live op dst imm =>
    let (res, fl) := evalAluDetFlags64 op (l.regs dst) imm
    let regs' := if aluWritesDst op then regUpd l.regs dst res else l.regs
    { l with regs := regs', flags := fl }
  | .shiftImm64Dead op dst cnt =>
    { l with regs := regUpd l.regs dst (shiftVal64 op (l.regs dst) cnt) }
  | .imulRR64Dead dst src =>
    { l with regs := regUpd l.regs dst (l.regs dst * l.regs src) }

def evalCollapsedOps : List CollapsedOp → LiftedX64State → LiftedX64State
  | [], l => l
  | cop :: rest, l => evalCollapsedOps rest (stepCollapsedOp cop l)

def copTouchesReg (r : Reg) : CollapsedOp → Bool
  | .nop | .spillStore _ _ => false
  | .movRR64 d _ | .movRR32 d _ | .movImm64 d _ | .movImm32 d _
  | .leaBaseDisp d _ _ _ | .spillLoad d _ | .shiftImm64Dead _ d _ | .imulRR64Dead d _ => d == r
  | .aluRR64Dead op d _ | .aluImm64Dead op d _ | .aluRR64Live op d _ | .aluImm64Live op d _ =>
    aluWritesDst op && (d == r)

def copsTouchReg (r : Reg) : List CollapsedOp → Bool
  | [] => false
  | c :: cs => copTouchesReg r c || copsTouchReg r cs

theorem reg_beq_refl (r : Reg) : (r == r) = true := by
  cases r <;> rfl

theorem stepCollapsedOp_untouched_reg (r : Reg) (cop : CollapsedOp) (l : LiftedX64State)
    (h : copTouchesReg r cop = false) :
    (stepCollapsedOp cop l).regs r = l.regs r := by
  cases cop with
  | nop | spillStore _ _ => rfl
  | movRR64 d _ | movRR32 d _ | movImm64 d _ | movImm32 d _
  | spillLoad d _ | shiftImm64Dead _ d _ | imulRR64Dead d _ =>
    dsimp [copTouchesReg] at h
    have hne : r ≠ d := fun e => by subst e; rw [reg_beq_refl r] at h; nomatch h
    dsimp [stepCollapsedOp]; exact regUpd_ne l.regs hne _
  | leaBaseDisp d b idx disp =>
    dsimp [copTouchesReg] at h
    have hne : r ≠ d := fun e => by subst e; rw [reg_beq_refl r] at h; nomatch h
    cases idx <;> (dsimp [stepCollapsedOp]; exact regUpd_ne l.regs hne _)
  | aluRR64Dead op d _ | aluImm64Dead op d _ | aluRR64Live op d _ | aluImm64Live op d _ =>
    dsimp [copTouchesReg, stepCollapsedOp] at h ⊢
    revert h
    cases aluWritesDst op with
    | false => intro _; rfl
    | true =>
      intro h
      have hne : r ≠ d := fun e => by subst e; rw [reg_beq_refl r] at h; nomatch h
      exact regUpd_ne l.regs hne _

theorem evalCollapsedOps_untouched_reg (r : Reg) :
    ∀ (cops : List CollapsedOp) (l : LiftedX64State),
      copsTouchReg r cops = false →
      (evalCollapsedOps cops l).regs r = l.regs r
  | [], _ => fun _ => rfl
  | c :: cs, l => fun h => by
    dsimp [copsTouchReg] at h
    have hc := Bool.or_eq_false_iff.mp h
    dsimp [evalCollapsedOps]
    rw [evalCollapsedOps_untouched_reg r cs (stepCollapsedOp c l) hc.2]
    exact stepCollapsedOp_untouched_reg r c l hc.1

/-- Check that an ALU op's undefined flags (`AF` on `.xor`/`.and`/`.or`/`.test`) are NOT live-out. -/
def aluNoLiveUndef (op : AluOp) (liveOut : FlagMask) : Bool :=
  match op with
  | .add | .sub | .cmp => true
  | .xor | .and | .or | .test => !liveOut.af

theorem evalAluFlags64_agree_det {op : AluOp} {a b : BitVec 64} {liveOut : FlagMask}
    (hok : aluNoLiveUndef op liveOut = true) (nd : UndefFlags) :
    FlagsAgreeOn liveOut (evalAluFlags64 op a b nd).2 (evalAluDetFlags64 op a b).2 := by
  cases op <;> dsimp [aluNoLiveUndef, evalAluFlags64, evalAluDetFlags64] at hok ⊢
  · exact flagsAgreeOn_refl _ _
  · exact flagsAgreeOn_refl _ _
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro haf; rw [haf] at hok; nomatch hok
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro haf; rw [haf] at hok; nomatch hok
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro haf; rw [haf] at hok; nomatch hok
  · exact flagsAgreeOn_refl _ _
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro haf; rw [haf] at hok; nomatch hok

def decodeSlotDisp? (maxSlots : Nat) : MemAddr → Option Nat
  | .baseDisp .rsp none disp =>
    let d := disp.toNat
    let slot := d / 8
    if d % 8 == 0 && slot < maxSlots && disp == BitVec.ofNat 64 (slot * 8) then some slot
    else none
  | _ => none

def addrUsesNoRip : MemAddr → Option (Reg × Option (Reg × Nat) × BitVec 64)
  | .baseDisp base idx disp =>
    -- Enforce Unexposed Private Stack-Frame Separation: `lea` never reads `.rsp`!
    let idxNoRsp := match idx with | none => true | some (ir, _) => decide (ir ≠ .rsp)
    if decide (base ≠ .rsp) && idxNoRsp then some (base, idx, disp) else none
  | .ripRel _ => none

/-- Single-instruction backward `DeadFlagCollapse` + `NoRspEscape` stack-slot promotion! -/
def collapseOneInstr (maxSlots : Nat) (ins : X64Instr) (liveOut : FlagMask) :
    Option (FlagMask × CollapsedOp) :=
  match ins with
  | .nop | .endbr64 | .vzeroupper => some (liveOut, .nop)
  | .movRR64 dst src =>
    if decide (dst ≠ .rsp) && decide (src ≠ .rsp) then some (liveOut, .movRR64 dst src) else none
  | .movRR32 dst src =>
    if decide (dst ≠ .rsp) && decide (src ≠ .rsp) then some (liveOut, .movRR32 dst src) else none
  | .movImm64 dst imm =>
    if decide (dst ≠ .rsp) then some (liveOut, .movImm64 dst imm) else none
  | .movImm32 dst imm32 =>
    if decide (dst ≠ .rsp) then some (liveOut, .movImm32 dst imm32) else none
  | .lea64 dst addr =>
    if decide (dst ≠ .rsp) then
      match addrUsesNoRip addr with
      | some (base, idx, disp) => some (liveOut, .leaBaseDisp dst base idx disp)
      | none => none
    else none
  | .store64 addr src =>
    if decide (src ≠ .rsp) then
      match decodeSlotDisp? maxSlots addr with
      | some slot => some (liveOut, .spillStore slot src)
      | none => none
    else none
  | .load64 dst addr =>
    if decide (dst ≠ .rsp) then
      match decodeSlotDisp? maxSlots addr with
      | some slot => some (liveOut, .spillLoad dst slot)
      | none => none
    else none
  | .aluRR64 op dst src =>
    if decide (dst ≠ .rsp) && decide (src ≠ .rsp) then
      if liveOut == FlagMask.dead then some (FlagMask.dead, .aluRR64Dead op dst src)
      else if aluNoLiveUndef op liveOut then some (FlagMask.dead, .aluRR64Live op dst src)
      else none
    else none
  | .aluImm64 op dst imm =>
    if decide (dst ≠ .rsp) then
      if liveOut == FlagMask.dead then some (FlagMask.dead, .aluImm64Dead op dst imm)
      else if aluNoLiveUndef op liveOut then some (FlagMask.dead, .aluImm64Live op dst imm)
      else none
    else none
  | .shiftImm64 op dst cnt =>
    -- When `liveOut == FlagMask.dead`, shift flags (both `cnt=0` pass-through and `cnt>0`
    -- demonic `nd.af`/`nd.of`) are 100% dead, collapsing to pure `shiftVal64`!
    if decide (dst ≠ .rsp) && liveOut == FlagMask.dead then
      some (FlagMask.dead, .shiftImm64Dead op dst cnt)
    else none
  | .imulRR64 dst src =>
    if decide (dst ≠ .rsp) && decide (src ≠ .rsp) && liveOut == FlagMask.dead then
      some (FlagMask.dead, .imulRR64Dead dst src)
    else none
  | _ => none

/-- Decode a raw variable-length x86-64 byte block into `(insBytes, ins)` pairs using `fuel`. -/
def decodeByteBlock : Nat → List UInt8 → Option (List (List UInt8 × X64Instr))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs =>
    match decodeX64 bs with
    | .fault _ => none
    | .ok ins len =>
      let pfx := bs.take len
      if len == 0 || pfx.length < len || decodeX64 pfx != .ok ins pfx.length then none
      else
        match decodeByteBlock fuel (bs.drop len) with
        | none => none
        | some rest => some ((pfx, ins) :: rest)

/-- Backward liveness pass over a decoded instruction list from `liveExit`. -/
def collapseDecodedList (maxSlots : Nat) (liveExit : FlagMask) :
    List (List UInt8 × X64Instr) → Option (FlagMask × List CollapsedOp)
  | [] => some (liveExit, [])
  | (_, ins) :: rest =>
    match collapseDecodedList maxSlots liveExit rest with
    | none => none
    | some (liveMid, copsRest) =>
      match collapseOneInstr maxSlots ins liveMid with
      | none => none
      | some (liveIn, cop) => some (liveIn, cop :: copsRest)

/-- Full reflected leaf compiler: variable-length byte decode + backward `DeadFlagCollapse` +
    `PrivateStackSep` slot promotion in one pass (`fuel = 128` instructions per leaf)! -/
def compileByteLeaf (maxSlots : Nat) (liveExit : FlagMask) (leafBytes : List UInt8) :
    Option (FlagMask × List CollapsedOp) :=
  match decodeByteBlock 128 leafBytes with
  | none => none
  | some decoded => collapseDecodedList maxSlots liveExit decoded

/-- Kernel-primitive GMP comparisons (`Nat.ble`, `0` Peano recursion depth at arbitrary offsets). -/
@[inline] def natLeB (x y : Nat) : Bool := Nat.ble x y
@[inline] def natLtB (x y : Nat) : Bool := Nat.ble (x + 1) y
@[inline] def natEqB (x y : Nat) : Bool := Nat.ble x y && Nat.ble y x

theorem natLeB_true {x y : Nat} (h : natLeB x y = true) : x ≤ y :=
  Nat.le_of_ble_eq_true h

theorem natLtB_true {x y : Nat} (h : natLtB x y = true) : x < y :=
  Nat.le_of_ble_eq_true h

theorem natEqB_true {x y : Nat} (h : natEqB x y = true) : x = y := by
  have hc := Bool.and_eq_true_iff.mp h
  exact Nat.le_antisymm (Nat.le_of_ble_eq_true hc.1) (Nat.le_of_ble_eq_true hc.2)

theorem natEqB_refl (x : Nat) : natEqB x x = true := by
  have ht : Nat.ble x x = true := Eq.mpr (@Nat.ble_eq x x) (Nat.le_refl x)
  dsimp [natEqB]; rw [ht]; rfl

/-- Path selector locating a concrete byte-chunk leaf inside `ByteCodeTree` in `O(log B)`. -/
inductive TreePath where
  | here
  | goLeft  (p : TreePath)
  | goRight (p : TreePath)

def checkLeafBytesAt : ByteCodeTree → TreePath → Nat → List UInt8 → Bool
  | .leaf bs, .here, base, target =>
    natEqB base 0 && decide (bs = target)
  | .node lsz l _, .goLeft p, base, target =>
    natLeB (base + lenTR target) lsz && checkLeafBytesAt l p base target
  | .node lsz _ r, .goRight p, base, target =>
    natLeB lsz base && checkLeafBytesAt r p (base - lsz) target
  | _, _, _, _ => false

theorem checkLeafBytesAt_here (bs : List UInt8) :
    checkLeafBytesAt (.leaf bs) .here 0 bs = true := by
  dsimp [checkLeafBytesAt]
  rw [natEqB_refl 0, decide_eq_true rfl]
  rfl

theorem checkLeafBytesAt_goLeft {lsz base : Nat} {l r : ByteCodeTree} {p : TreePath} {bs : List UInt8}
    (hle : natLeB (base + lenTR bs) lsz = true)
    (hsub : checkLeafBytesAt l p base bs = true) :
    checkLeafBytesAt (.node lsz l r) (.goLeft p) base bs = true := by
  dsimp [checkLeafBytesAt]; rw [hle, hsub]; rfl

theorem checkLeafBytesAt_goRight {lsz base subBase : Nat} {l r : ByteCodeTree} {p : TreePath} {bs : List UInt8}
    (hge : natLeB lsz base = true)
    (hsub_eq : base - lsz = subBase)
    (hsub : checkLeafBytesAt r p subBase bs = true) :
    checkLeafBytesAt (.node lsz l r) (.goRight p) base bs = true := by
  subst hsub_eq
  dsimp [checkLeafBytesAt]; rw [hge, hsub]; rfl

theorem checkLeafBytesAt_getByte? :
    ∀ (t : ByteCodeTree) (p : TreePath) (base : Nat) (bs : List UInt8) (off : Nat),
      checkLeafBytesAt t p base bs = true →
      off < bs.length →
      t.getByte? (base + off) = listGet? bs off
  | .leaf b, .here, base, bs, off, hchk, _ => by
    dsimp [checkLeafBytesAt] at hchk
    have h := Bool.and_eq_true_iff.mp hchk
    have hb0 : base = 0 := natEqB_true h.1
    have hbs : b = bs := of_decide_eq_true h.2
    subst hb0 hbs
    rw [Nat.zero_add]; rfl
  | .node lsz l _, .goLeft p, base, bs, off, hchk, hoff => by
    dsimp [checkLeafBytesAt] at hchk
    have h := Bool.and_eq_true_iff.mp hchk
    have hle : base + bs.length ≤ lsz := by
      have h' := natLeB_true h.1
      rw [lenTR_eq_length] at h'
      exact h'
    have hlt : base + off < lsz := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff base) hle
    dsimp [ByteCodeTree.getByte?]
    simp only [hlt, ite_true]
    exact checkLeafBytesAt_getByte? l p base bs off h.2 hoff
  | .node lsz _ r, .goRight p, base, bs, off, hchk, hoff => by
    dsimp [checkLeafBytesAt] at hchk
    have h := Bool.and_eq_true_iff.mp hchk
    have hge : lsz ≤ base := natLeB_true h.1
    have hnlt : ¬ (base + off < lsz) :=
      Nat.not_lt_of_ge (Nat.le_trans hge (Nat.le_add_right base off))
    dsimp [ByteCodeTree.getByte?]
    simp only [hnlt, ite_false]
    rw [Nat.sub_add_comm hge]
    exact checkLeafBytesAt_getByte? r p (base - lsz) bs off h.2 hoff
  | .leaf _, .goLeft _, _, _, _, hchk, _ => nomatch hchk
  | .leaf _, .goRight _, _, _, _, hchk, _ => nomatch hchk
  | .node _ _ _, .here, _, _, _, hchk, _ => nomatch hchk


/-! ### Section 3B: Soundness of `compileByteLeaf` (`checkByteLeaf_sound`) -/

theorem listGet?_append_right {α : Type} :
    ∀ (xs ys : List α) (i : Nat), listGet? (xs ++ ys) (xs.length + i) = listGet? ys i
  | [], _, i => by rw [List.nil_append, List.length_nil, Nat.zero_add]
  | _ :: xs, ys, i => by
    show listGet? (_ :: (xs ++ ys)) ((xs.length + 1) + i) = listGet? ys i
    rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]
    exact listGet?_append_right xs ys i

def concatDecodedBytes : List (List UInt8 × X64Instr) → List UInt8
  | [] => []
  | (pfx, _) :: rest => pfx ++ concatDecodedBytes rest

def AllChunksValid : List (List UInt8 × X64Instr) → Prop
  | [] => True
  | (pfx, ins) :: rest => decodeX64 pfx = .ok ins pfx.length ∧ AllChunksValid rest

theorem decodeByteBlock_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (decoded : List (List UInt8 × X64Instr)),
      decodeByteBlock fuel bs = some decoded →
      concatDecodedBytes decoded = bs ∧ AllChunksValid decoded
  | 0, [], decoded, h => by
    injection h with hd; subst hd; exact ⟨rfl, trivial⟩
  | _ + 1, [], decoded, h => by
    injection h with hd; subst hd; exact ⟨rfl, trivial⟩
  | 0, _ :: _, _, h => nomatch h
  | fuel + 1, b :: bs, decoded, h => by
    dsimp [decodeByteBlock] at h
    revert h
    cases decodeX64 (b :: bs) with
    | fault _ => intro h; nomatch h
    | ok ins len =>
      dsimp
      let pfx := (b :: bs).take len
      cases hbad : (len == 0 || decide (pfx.length < len) || (decodeX64 pfx != .ok ins pfx.length)) with
      | true => intro h; nomatch h
      | false =>
        cases hrest : decodeByteBlock fuel ((b :: bs).drop len) with
        | none => intro h; nomatch h
        | some rest =>
          intro h; injection h with hd; subst hd
          have ih := decodeByteBlock_sound fuel ((b :: bs).drop len) rest hrest
          have hb1 : (len == 0 || decide (pfx.length < len)) = false ∧
                     (decodeX64 pfx != .ok ins pfx.length) = false :=
            Bool.or_eq_false_iff.mp hbad
          have hpfx_ok : decodeX64 pfx = .ok ins pfx.length := by
            have hbeq : (decodeX64 pfx == .ok ins pfx.length) = true := by
              cases heq : (decodeX64 pfx == .ok ins pfx.length) with
              | true => rfl
              | false =>
                have hf := hb1.2
                dsimp [bne] at hf
                rw [heq] at hf
                nomatch hf
            exact of_decide_eq_true hbeq
          refine ⟨?_, ⟨hpfx_ok, ih.2⟩⟩
          dsimp [concatDecodedBytes]
          rw [ih.1]
          exact List.take_append_drop len (b :: bs)

theorem shiftVal64_agree_evalShift64 (op : ShiftOp) (a : BitVec 64) (cnt : Nat)
    (oldF : RFlags) (nd : UndefFlags) :
    (evalShift64 op a cnt oldF nd).1 = shiftVal64 op a cnt := by
  dsimp [evalShift64, shiftVal64]
  cases hc : decide (cnt % 64 = 0) with
  | false =>
    have hne : (cnt % 64 == 0) = false := by
      cases heq : (cnt % 64 == 0) with
      | false => rfl
      | true => exact False.elim ((of_decide_eq_false hc) (of_decide_eq_true heq))
    rw [hne]; rfl
  | true =>
    have hz : cnt % 64 = 0 := of_decide_eq_true hc
    have hb : (cnt % 64 == 0) = true := decide_eq_true hz
    rw [hb]; dsimp
    rw [hz]
    cases op with
    | shl => exact (BitVec.shiftLeft_zero a).symm
    | shr => exact (BitVec.ushiftRight_zero a).symm

theorem evalAluFlags64_fst (op : AluOp) (a b : BitVec 64) (nd : UndefFlags) :
    (evalAluFlags64 op a b nd).1 = aluVal64 op a b := by
  cases op <;> rfl

theorem addrUsesNoRip_spec {addr : MemAddr} {base : Reg} {idx : Option (Reg × Nat)} {disp : BitVec 64}
    (h : addrUsesNoRip addr = some (base, idx, disp)) :
    addr = .baseDisp base idx disp := by
  cases addr with
  | ripRel _ => nomatch h
  | baseDisp b i d =>
    dsimp [addrUsesNoRip] at h
    revert h
    cases (decide (b ≠ .rsp) && match i with | none => true | some (ir, _) => decide (ir ≠ .rsp)) with
    | false => intro h; nomatch h
    | true =>
      intro h; injection h with h1; injection h1 with hb h2; injection h2 with hi hd
      subst hb hi hd; rfl

theorem decodeSlotDisp?_spec {maxSlots : Nat} {addr : MemAddr} {slot : Nat}
    (h : decodeSlotDisp? maxSlots addr = some slot) :
    slot < maxSlots ∧ addr = .baseDisp .rsp none (BitVec.ofNat 64 (slot * 8)) := by
  cases addr with
  | ripRel _ => nomatch h
  | baseDisp b idx disp =>
    cases b with
    | rsp =>
      cases idx with
      | some _ => nomatch h
      | none =>
        dsimp [decodeSlotDisp?] at h
        revert h
        cases hcond : ((disp.toNat % 8 == 0 && decide (disp.toNat / 8 < maxSlots)) &&
                       (disp == BitVec.ofNat 64 ((disp.toNat / 8) * 8))) with
        | false => intro h; nomatch h
        | true =>
          intro h; injection h with hs; subst hs
          have hc1 := Bool.and_eq_true_iff.mp hcond
          have hc2 := Bool.and_eq_true_iff.mp hc1.1
          exact ⟨of_decide_eq_true hc2.2, congrArg (MemAddr.baseDisp .rsp none) (of_decide_eq_true hc1.2)⟩
    | _ => nomatch h

/-- Single-instruction backward simulation for `collapseOneInstr` across ALL demonic `nd0`. -/
theorem step_collapseOne_sound {maxSlots : Nat} {img : X64ObjImage}
    {pfx : List UInt8} {ins : X64Instr} {liveIn liveOut : FlagMask} {cop : CollapsedOp}
    {s : X64State} {l : LiftedX64State} (nd0 : UndefFlags)
    (hbound : maxSlots * 8 < 2 ^ 64)
    (hpfx_dec : decodeX64 pfx = .ok ins pfx.length)
    (hwin_bytes : ∀ i, i < pfx.length → img.code.getByte? (s.rip + i) = listGet? pfx i)
    (hcol : collapseOneInstr maxSlots ins liveOut = some (liveIn, cop))
    (habs : AbstractsLeaf maxSlots liveIn s l) :
    let s' := stepX64 img nd0 s
    s'.rip = s.rip + pfx.length ∧
    s'.regs .rsp = s.regs .rsp ∧
    (∀ a, OutsideSpillRange (s.regs .rsp) maxSlots a → s'.mem a = s.mem a) ∧
    AbstractsLeaf maxSlots liveOut s' (stepCollapsedOp cop l) := by
  rcases habs with ⟨hnh, hnf, hregs, hslots, hflags⟩
  have hlen_le15 : pfx.length ≤ 15 := (decodeX64_len_bounds hpfx_dec).2.1
  have hlen_le16 : pfx.length ≤ 16 := Nat.le_trans hlen_le15 (by decide)
  rcases fetchBytes_prefix pfx img.code 16 s.rip hlen_le16 hwin_bytes with ⟨sfx, hsfx⟩
  have hdec_win : decodeX64 (fetchWindow16 img.code s.rip) = .ok ins pfx.length := by
    dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hpfx_dec sfx
  dsimp only
  cases ins with
  | nop =>
    dsimp [collapseOneInstr] at hcol
    injection hcol with hp; injection hp with hl hcop; subst hl hcop
    have hst : stepX64 img nd0 s = { s with rip := s.rip + pfx.length } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    rw [hst]; exact ⟨rfl, rfl, fun _ _ => rfl, hnh, hnf, hregs, hslots, hflags⟩
  | endbr64 =>
    dsimp [collapseOneInstr] at hcol
    injection hcol with hp; injection hp with hl hcop; subst hl hcop
    have hst : stepX64 img nd0 s = { s with rip := s.rip + pfx.length } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    rw [hst]; exact ⟨rfl, rfl, fun _ _ => rfl, hnh, hnf, hregs, hslots, hflags⟩
  | vzeroupper =>
    dsimp [collapseOneInstr] at hcol
    injection hcol with hp; injection hp with hl hcop; subst hl hcop
    have hst : stepX64 img nd0 s = { s with rip := s.rip + pfx.length } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    rw [hst]; exact ⟨rfl, rfl, fun _ _ => rfl, hnh, hnf, hregs, hslots, hflags⟩
  | movRR64 dst src =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst (s.regs src) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : (decide (dst ≠ .rsp) && decide (src ≠ .rsp)) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hdst : dst ≠ .rsp := of_decide_eq_true (Bool.and_eq_true_iff.mp hok).1
      rw [hst]
      have hrsp : regUpd s.regs dst (s.regs src) .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
      · intro r; dsimp [stepCollapsedOp, regUpd]; rw [hregs r, hregs src]
      · intro sl hsl; dsimp [stepCollapsedOp]; rw [hrsp]; exact hslots sl hsl
  | movRR32 dst src =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length,
                 regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : (decide (dst ≠ .rsp) && decide (src ≠ .rsp)) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hdst : dst ≠ .rsp := of_decide_eq_true (Bool.and_eq_true_iff.mp hok).1
      rw [hst]
      have hrsp : regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
      · intro r; dsimp [stepCollapsedOp, regUpd]; rw [hregs r, hregs src]
      · intro sl hsl; dsimp [stepCollapsedOp]; rw [hrsp]; exact hslots sl hsl
  | movImm64 dst imm =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst imm } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (dst ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hdst : dst ≠ .rsp := of_decide_eq_true hok
      rw [hst]
      have hrsp : regUpd s.regs dst imm .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
      · intro r; dsimp [stepCollapsedOp, regUpd]; rw [hregs r]
      · intro sl hsl; dsimp [stepCollapsedOp]; rw [hrsp]; exact hslots sl hsl
  | movImm32 dst imm32 =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst (imm32.zeroExtend 64) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (dst ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hdst : dst ≠ .rsp := of_decide_eq_true hok
      rw [hst]
      have hrsp : regUpd s.regs dst (imm32.zeroExtend 64) .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
      · intro r; dsimp [stepCollapsedOp, regUpd]; rw [hregs r]
      · intro sl hsl; dsimp [stepCollapsedOp]; rw [hrsp]; exact hslots sl hsl
  | lea64 dst addr =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst (evalAddr s (s.rip + pfx.length) addr) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (dst ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      cases ha : addrUsesNoRip addr with
      | none => intro h; nomatch h
      | some triple =>
        rcases triple with ⟨base, idx, disp⟩
        intro h; injection h with hp; injection hp with hl hcop; subst hl hcop
        have hdst : dst ≠ .rsp := of_decide_eq_true hok
        have haddr_eq := addrUsesNoRip_spec ha
        subst haddr_eq
        rw [hst]
        cases idx with
        | none =>
          have hrsp : regUpd s.regs dst (s.regs base + disp) .rsp = s.regs .rsp :=
            regUpd_ne s.regs (fun e => hdst e.symm) _
          dsimp [AbstractsLeaf, stepCollapsedOp, evalAddr]
          refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
          · intro r; dsimp [regUpd]; rw [hregs r, hregs base]
          · intro sl hsl; rw [hrsp]; exact hslots sl hsl
        | some pair =>
          rcases pair with ⟨ir, sc⟩
          have hrsp : regUpd s.regs dst (s.regs base + s.regs ir * BitVec.ofNat 64 sc + disp) .rsp = s.regs .rsp :=
            regUpd_ne s.regs (fun e => hdst e.symm) _
          dsimp [AbstractsLeaf, stepCollapsedOp, evalAddr]
          refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
          · intro r; dsimp [regUpd]; rw [hregs r, hregs base, hregs ir]
          · intro sl hsl; rw [hrsp]; exact hslots sl hsl
  | store64 addr src =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length,
                 mem := writeMem64 s.mem (evalAddr s (s.rip + pfx.length) addr) (s.regs src) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (src ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      cases hsl_opt : decodeSlotDisp? maxSlots addr with
      | none => intro h; nomatch h
      | some slot =>
        intro h; injection h with hp; injection hp with hl hcop; subst hl hcop
        rcases decodeSlotDisp?_spec hsl_opt with ⟨hslot_lt, haddr_eq⟩
        subst haddr_eq
        rw [hst]
        have hea : evalAddr s (s.rip + pfx.length) (.baseDisp .rsp none (BitVec.ofNat 64 (slot * 8))) =
            spillSlotAddr (s.regs .rsp) slot := rfl
        rw [hea]
        refine ⟨rfl, rfl, ?_, hnh, hnf, hregs, ?_, hflags⟩
        · intro a hout
          exact writeMem64_byte_ne s.mem (spillSlotAddr (s.regs .rsp) slot) a (s.regs src)
            (outside_spill_byte_ne (s.regs .rsp) a hbound hout hslot_lt)
        · intro sl hsl
          dsimp [stepCollapsedOp]
          cases hdec : decide (sl = slot) with
          | true =>
            have heq : sl = slot := of_decide_eq_true hdec
            subst heq; simp only [ite_true]
            rw [readMem64_writeMem64_same, hregs src]
          | false =>
            have hne_sl : sl ≠ slot := of_decide_eq_false hdec
            simp only [hne_sl, ite_false]
            rw [readMem64_writeMem64_disjoint s.mem _ _ (s.regs src)
              (slot_bytes_disjoint (s.regs .rsp) hbound hsl hslot_lt hne_sl)]
            exact hslots sl hsl
  | load64 dst addr =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length,
                 regs := regUpd s.regs dst (readMem64 s.mem (evalAddr s (s.rip + pfx.length) addr)) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (dst ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      cases hsl_opt : decodeSlotDisp? maxSlots addr with
      | none => intro h; nomatch h
      | some slot =>
        intro h; injection h with hp; injection hp with hl hcop; subst hl hcop
        have hdst : dst ≠ .rsp := of_decide_eq_true hok
        rcases decodeSlotDisp?_spec hsl_opt with ⟨hslot_lt, haddr_eq⟩
        subst haddr_eq
        rw [hst]
        have hea : evalAddr s (s.rip + pfx.length) (.baseDisp .rsp none (BitVec.ofNat 64 (slot * 8))) =
            spillSlotAddr (s.regs .rsp) slot := rfl
        rw [hea]
        have hrsp : regUpd s.regs dst (readMem64 s.mem (spillSlotAddr (s.regs .rsp) slot)) .rsp = s.regs .rsp :=
          regUpd_ne s.regs (fun e => hdst e.symm) _
        refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, hflags⟩
        · intro r; dsimp [stepCollapsedOp, regUpd]; rw [hregs r, hslots slot hslot_lt]
        · intro sl hsl; dsimp [stepCollapsedOp]; rw [hrsp]; exact hslots sl hsl
  | aluRR64 op dst src =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length,
                 regs := if aluWritesDst op then regUpd s.regs dst (aluVal64 op (s.regs dst) (s.regs src)) else s.regs,
                 flags := (evalAluFlags64 op (s.regs dst) (s.regs src) nd0).2 } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]; dsimp
      rw [evalAluFlags64_fst]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : (decide (dst ≠ .rsp) && decide (src ≠ .rsp)) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      have hdst : dst ≠ .rsp := of_decide_eq_true (Bool.and_eq_true_iff.mp hok).1
      have hrsp_alu : (if aluWritesDst op then regUpd s.regs dst (aluVal64 op (s.regs dst) (s.regs src)) else s.regs) .rsp = s.regs .rsp := by
        cases aluWritesDst op with
        | false => rfl
        | true => exact regUpd_ne s.regs (fun e => hdst e.symm) _
      cases hdead : (liveOut == FlagMask.dead) with
      | true =>
        intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
        have hlo : liveOut = FlagMask.dead := of_decide_eq_true hdead
        subst hlo
        rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp]
        refine ⟨rfl, hrsp_alu, fun _ _ => rfl, hnh, hnf, ?_, ?_, flagsAgreeOn_dead _ _⟩
        · intro r
          cases aluWritesDst op with
          | false => dsimp; exact hregs r
          | true => dsimp [regUpd]; rw [hregs r, hregs dst, hregs src]
        · intro sl hsl; rw [hrsp_alu]; exact hslots sl hsl
      | false =>
        dsimp
        cases hnu : aluNoLiveUndef op liveOut with
        | false => intro h; nomatch h
        | true =>
          intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
          rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp, evalAluDetFlags64]
          rw [evalAluFlags64_fst]
          refine ⟨rfl, hrsp_alu, fun _ _ => rfl, hnh, hnf, ?_, ?_, ?_⟩
          · intro r
            cases aluWritesDst op with
            | false => dsimp; exact hregs r
            | true => dsimp [regUpd]; rw [hregs r, hregs dst, hregs src]
          · intro sl hsl; rw [hrsp_alu]; exact hslots sl hsl
          · rw [hregs dst, hregs src]
            exact evalAluFlags64_agree_det hnu nd0
  | aluImm64 op dst imm =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + pfx.length,
                 regs := if aluWritesDst op then regUpd s.regs dst (aluVal64 op (s.regs dst) imm) else s.regs,
                 flags := (evalAluFlags64 op (s.regs dst) imm nd0).2 } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]; dsimp
      rw [evalAluFlags64_fst]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : decide (dst ≠ .rsp) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      have hdst : dst ≠ .rsp := of_decide_eq_true hok
      have hrsp_alu : (if aluWritesDst op then regUpd s.regs dst (aluVal64 op (s.regs dst) imm) else s.regs) .rsp = s.regs .rsp := by
        cases aluWritesDst op with
        | false => rfl
        | true => exact regUpd_ne s.regs (fun e => hdst e.symm) _
      cases hdead : (liveOut == FlagMask.dead) with
      | true =>
        intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
        have hlo : liveOut = FlagMask.dead := of_decide_eq_true hdead
        subst hlo
        rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp]
        refine ⟨rfl, hrsp_alu, fun _ _ => rfl, hnh, hnf, ?_, ?_, flagsAgreeOn_dead _ _⟩
        · intro r
          cases aluWritesDst op with
          | false => dsimp; exact hregs r
          | true => dsimp [regUpd]; rw [hregs r, hregs dst]
        · intro sl hsl; rw [hrsp_alu]; exact hslots sl hsl
      | false =>
        dsimp
        cases hnu : aluNoLiveUndef op liveOut with
        | false => intro h; nomatch h
        | true =>
          intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
          rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp, evalAluDetFlags64]
          rw [evalAluFlags64_fst]
          refine ⟨rfl, hrsp_alu, fun _ _ => rfl, hnh, hnf, ?_, ?_, ?_⟩
          · intro r
            cases aluWritesDst op with
            | false => dsimp; exact hregs r
            | true => dsimp [regUpd]; rw [hregs r, hregs dst]
          · intro sl hsl; rw [hrsp_alu]; exact hslots sl hsl
          · rw [hregs dst]
            exact evalAluFlags64_agree_det hnu nd0
  | shiftImm64 op dst cnt =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalShift64 op (s.regs dst) cnt s.flags nd0
         { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : (decide (dst ≠ .rsp) && (liveOut == FlagMask.dead)) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hc := Bool.and_eq_true_iff.mp hok
      have hdst : dst ≠ .rsp := of_decide_eq_true hc.1
      have hlo : liveOut = FlagMask.dead := of_decide_eq_true hc.2
      subst hlo
      rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp]
      have hsv := shiftVal64_agree_evalShift64 op (s.regs dst) cnt s.flags nd0
      have hrsp : regUpd s.regs dst (evalShift64 op (s.regs dst) cnt s.flags nd0).1 .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, flagsAgreeOn_dead _ _⟩
      · intro r; dsimp [regUpd]; rw [hsv, hregs r, hregs dst]
      · intro sl hsl; rw [hrsp]; exact hslots sl hsl
  | imulRR64 dst src =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalImul64 (s.regs dst) (s.regs src) nd0
         { s with rip := s.rip + pfx.length, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec_win]
    dsimp [collapseOneInstr] at hcol
    revert hcol
    cases hok : ((decide (dst ≠ .rsp) && decide (src ≠ .rsp)) && (liveOut == FlagMask.dead)) with
    | false => intro h; nomatch h
    | true =>
      intro h; dsimp at h; injection h with hp; injection hp with hl hcop; subst hl hcop
      have hc1 := Bool.and_eq_true_iff.mp hok
      have hc2 := Bool.and_eq_true_iff.mp hc1.1
      have hdst : dst ≠ .rsp := of_decide_eq_true hc2.1
      have hlo : liveOut = FlagMask.dead := of_decide_eq_true hc1.2
      subst hlo
      rw [hst]; dsimp [AbstractsLeaf, stepCollapsedOp, evalImul64]
      have hrsp : regUpd s.regs dst (s.regs dst * s.regs src) .rsp = s.regs .rsp :=
        regUpd_ne s.regs (fun e => hdst e.symm) _
      refine ⟨rfl, hrsp, fun _ _ => rfl, hnh, hnf, ?_, ?_, flagsAgreeOn_dead _ _⟩
      · intro r; dsimp [regUpd]; rw [hregs r, hregs dst, hregs src]
      · intro sl hsl; rw [hrsp]; exact hslots sl hsl
  | load32Zext _ _ | load32Sext _ _ | aluRR32 _ _ _ | aluImm32 _ _ _
  | bsf64 _ _ | tzcnt64 _ _ | xchg64 _ _ | xchg32 _ _ | xchg16 _ _
  | lockAdd64 _ _ | lockAddImm64 _ _ | lockCmpxchg64 _ _
  | push64 _ | pop64 _ | leave64 | jmpRel _ | jccRel _ _ | jmpReg _ | ret | int3 | ud2 =>
    dsimp [collapseOneInstr] at hcol; nomatch hcol

theorem collapseDecodedList_sound {maxSlots : Nat} {img : X64ObjImage}
    (hbound : maxSlots * 8 < 2 ^ 64) :
    ∀ (decoded : List (List UInt8 × X64Instr)) (liveIn liveExit : FlagMask)
      (cops : List CollapsedOp) (nd : Nat → UndefFlags) (s : X64State) (l : LiftedX64State),
      AllChunksValid decoded →
      (∀ i, i < (concatDecodedBytes decoded).length →
        img.code.getByte? (s.rip + i) = listGet? (concatDecodedBytes decoded) i) →
      collapseDecodedList maxSlots liveExit decoded = some (liveIn, cops) →
      AbstractsLeaf maxSlots liveIn s l →
      let sf := runX64 img cops.length nd s
      sf.rip = s.rip + (concatDecodedBytes decoded).length ∧
      sf.regs .rsp = s.regs .rsp ∧
      (∀ a, OutsideSpillRange (s.regs .rsp) maxSlots a → sf.mem a = s.mem a) ∧
      AbstractsLeaf maxSlots liveExit sf (evalCollapsedOps cops l)
  | [], liveIn, liveExit, cops, _, s, l, _, _, hcol, habs => by
    dsimp [collapseDecodedList] at hcol
    injection hcol with hp; injection hp with hl hc; subst hl hc
    dsimp [concatDecodedBytes, List.length, runX64, evalCollapsedOps]
    exact ⟨rfl, rfl, fun _ _ => rfl, habs⟩
  | (pfx, ins) :: rest, liveIn, liveExit, cops, nd, s, l, hval, hbytes, hcol, habs => by
    dsimp [collapseDecodedList] at hcol
    revert hcol
    cases hrest_col : collapseDecodedList maxSlots liveExit rest with
    | none => intro h; nomatch h
    | some pairMid =>
      rcases pairMid with ⟨liveMid, copsRest⟩
      dsimp
      cases hone : collapseOneInstr maxSlots ins liveMid with
      | none => intro h; nomatch h
      | some pairIn =>
        rcases pairIn with ⟨liveIn', cop⟩
        intro h; injection h with hp; injection hp with hl hc; subst hl hc
        have hpfx_win : ∀ i, i < pfx.length → img.code.getByte? (s.rip + i) = listGet? pfx i := by
          intro i hi
          have hlt : i < (pfx ++ concatDecodedBytes rest).length := by
            rw [List.length_append]
            exact Nat.lt_of_lt_of_le hi (Nat.le_add_right pfx.length _)
          have hb := hbytes i hlt
          dsimp [concatDecodedBytes] at hb
          rw [listGet?_append_left pfx (concatDecodedBytes rest) i hi] at hb
          exact hb
        have hstep := step_collapseOne_sound (nd 0) hbound hval.1 hpfx_win hone habs
        rcases hstep with ⟨hrip1, hrsp1, hmem1, habs1⟩
        have hrest_bytes : ∀ i, i < (concatDecodedBytes rest).length →
            img.code.getByte? ((stepX64 img (nd 0) s).rip + i) = listGet? (concatDecodedBytes rest) i := by
          intro i hi
          rw [hrip1, Nat.add_assoc]
          have hlt : pfx.length + i < (pfx ++ concatDecodedBytes rest).length := by
            rw [List.length_append]
            exact Nat.add_lt_add_left hi pfx.length
          have hb := hbytes (pfx.length + i) hlt
          dsimp [concatDecodedBytes] at hb
          rw [listGet?_append_right pfx (concatDecodedBytes rest) i] at hb
          exact hb
        have ih := collapseDecodedList_sound hbound rest liveMid liveExit copsRest
          (fun k => nd (k + 1)) (stepX64 img (nd 0) s) (stepCollapsedOp cop l)
          hval.2 hrest_bytes hrest_col habs1
        rcases ih with ⟨hrip2, hrsp2, hmem2, habs2⟩
        dsimp only [List.length_cons, runX64, evalCollapsedOps]
        refine ⟨?_, ?_, ?_, habs2⟩
        · dsimp [concatDecodedBytes]; rw [List.length_append, hrip2, hrip1, Nat.add_assoc]
        · rw [hrsp2, hrsp1]
        · intro a hout
          have hout1 : OutsideSpillRange ((stepX64 img (nd 0) s).regs .rsp) maxSlots a := by
            rw [hrsp1]; exact hout
          rw [hmem2 a hout1, hmem1 a hout]

/-- End-to-End Sharded Byte-Decoded Lifting + `DeadFlagCollapse` + Private Stack Separation Theorem:
    Verifies a variable-length (`1..15` byte) x86-64 leaf inside `ByteCodeTree` via two `O(log B + |leaf|)`
    `rfl` checks (`checkLeafBytesAt` and `compileByteLeaf`), universally quantified over ALL demonic
    hardware flag streams `nd : Nat → UndefFlags`! -/
theorem checkByteLeaf_sound {maxSlots : Nat} {img : X64ObjImage}
    {path : TreePath} {leafBase : Nat} {leafBytes : List UInt8}
    {liveIn liveExit : FlagMask} {cops : List CollapsedOp}
    (hbound : maxSlots * 8 < 2 ^ 64)
    (htree : checkLeafBytesAt img.code path leafBase leafBytes = true)
    (hcomp : compileByteLeaf maxSlots liveExit leafBytes = some (liveIn, cops)) :
    ∀ (nd : Nat → UndefFlags) (s : X64State) (l : LiftedX64State),
      s.rip = leafBase →
      AbstractsLeaf maxSlots liveIn s l →
      let sf := runX64 img (lenTR cops) nd s
      sf.rip = leafBase + lenTR leafBytes ∧
      sf.regs .rsp = s.regs .rsp ∧
      (∀ a, OutsideSpillRange (s.regs .rsp) maxSlots a → sf.mem a = s.mem a) ∧
      AbstractsLeaf maxSlots liveExit sf (evalCollapsedOps cops l) := by
  intro nd s l hrip habs
  dsimp [compileByteLeaf] at hcomp
  revert hcomp
  cases hdec : decodeByteBlock 128 leafBytes with
  | none => intro h; nomatch h
  | some decoded =>
    intro hcomp
    rcases decodeByteBlock_sound 128 leafBytes decoded hdec with ⟨hcat, hval⟩
    have hbytes : ∀ i, i < (concatDecodedBytes decoded).length →
        img.code.getByte? (s.rip + i) = listGet? (concatDecodedBytes decoded) i := by
      intro i hi
      rw [hcat] at hi ⊢
      rw [hrip]
      exact checkLeafBytesAt_getByte? img.code path leafBase leafBytes i htree hi
    have res := collapseDecodedList_sound hbound decoded liveIn liveExit cops nd s l hval hbytes hcomp habs
    dsimp only at res
    rw [hcat, hrip, ← lenTR_eq_length cops, ← lenTR_eq_length leafBytes] at res
    exact res
