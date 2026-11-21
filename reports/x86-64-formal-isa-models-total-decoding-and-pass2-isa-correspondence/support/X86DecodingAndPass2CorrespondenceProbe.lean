/-
Standalone Lean 4.34.1 (`Init.*`-only, zero `partial def`, zero `sorry`,
zero custom axioms) mechanization comparing:
  Part 1: Direct total structural x86-64 decoding vs. witness-checked
          parameterized encoding (including encoding multiplicity, prefix
          precedence, REX nullification, `REX.B` + `0x90`, `LOCK` `#UD`
          legality, 15-byte `#GP(0)` limit, and an ambiguity negative control).
  Part 2: Two-model Pass-2 ISA correspondence (`I_ref ⊆ I_anneal`) with
          per-opcode staged support gates, demonic nondeterminism refinement
          (x86 undefined flags, RVV `vta`/`vma` agnostic bits, `LR`/`SC`
          spurious failure, quiet-NaN payload propagation), poison-vs-choice
          fault trade-offs, and a narrow-model unsoundness negative control.
-/

namespace X86DecodingAndPass2Probe

/-! ## Part 1: Total x86-64 Decoding vs. Witness-Checked Encoding -/

abbrev Reg4 := Fin 16

inductive X64Instr where
  | nop
  | xchg32 (r1 r2 : Reg4)
  | xchg64 (r1 r2 : Reg4)
  | addRR64 (dst src : Reg4)
  | addImm64 (dst : Reg4) (imm32 : UInt32)
  | lockAddMem64 (base src : Reg4)
  | endbr64
  | bsf64 (dst src : Reg4)
  | tzcnt64 (dst src : Reg4)
  deriving DecidableEq, Repr

inductive DecodeFault where
  | truncated
  | gpLenExceeded
  | udIllegalLock
  | unsupported
  deriving DecidableEq, Repr

inductive DecodeOutcome where
  | ok (ins : X64Instr) (len : Nat)
  | fault (k : DecodeFault)
  deriving DecidableEq, Repr

/-- Group-1 repeat prefix state (last-wins between `0xF2` and `0xF3`). -/
inductive RepPfx where
  | none | f2 | f3
  deriving DecidableEq, Repr

structure PrefixState where
  hasLock : Bool := false
  rep     : RepPfx := .none
  has66   : Bool := false
  has67   : Bool := false
  hasCS   : Bool := false
  rex     : Option UInt8 := none
  deriving DecidableEq, Repr

def isLegacyPrefix (b : UInt8) : Bool :=
  b == 0xF0 || b == 0xF2 || b == 0xF3 || b == 0x66 || b == 0x67 || b == 0x2E

def isRexPrefix (b : UInt8) : Bool :=
  (b &&& 0xF0) == 0x40

def rexW (r : Option UInt8) : Bool :=
  match r with | some b => (b &&& 0x08) != 0 | none => false

def rexR (r : Option UInt8) : Nat :=
  match r with | some b => if (b &&& 0x04) != 0 then 8 else 0 | none => 0

def rexB (r : Option UInt8) : Nat :=
  match r with | some b => if (b &&& 0x01) != 0 then 8 else 0 | none => 0

def mkReg4 (hi : Nat) (lo : UInt8) : Reg4 :=
  ⟨(hi + (lo &&& 0x07).toNat) % 16, Nat.mod_lt _ (by decide)⟩

def readUInt32LE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

def signExtend8To32 (b : UInt8) : UInt32 :=
  if (b &&& 0x80) != 0 then 0xFFFFFF00 ||| b.toUInt32 else b.toUInt32

/-- Structurally recursive prefix scanner bounded by `fuel` (no `partial def`).
    Models Intel SDM / ACL2 `get-prefixes`:
    - `0xF0` (`LOCK`) is tracked independently of `0xF2`/`0xF3` (`last-wins`).
    - Any legacy prefix appearing *after* a `REX` byte nullifies the prior `REX`. -/
def scanPrefixes : Nat → PrefixState → Nat → List UInt8 → Option (PrefixState × Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, ps, consumed, [] => some (ps, consumed, [])
  | fuel + 1, ps, consumed, b :: rest =>
      if isLegacyPrefix b then
        let ps' : PrefixState :=
          if b == 0xF0 then { ps with hasLock := true, rex := none }
          else if b == 0xF2 then { ps with rep := .f2, rex := none }
          else if b == 0xF3 then { ps with rep := .f3, rex := none }
          else if b == 0x66 then { ps with has66 := true, rex := none }
          else if b == 0x67 then { ps with has67 := true, rex := none }
          else { ps with hasCS := true, rex := none }
        scanPrefixes fuel ps' (consumed + 1) rest
      else if isRexPrefix b then
        scanPrefixes fuel { ps with rex := some b } (consumed + 1) rest
      else
        some (ps, consumed, b :: rest)

def checkLen15 (total : Nat) (ins : X64Instr) : DecodeOutcome :=
  if total ≤ 15 then .ok ins total else .fault .gpLenExceeded

/-- Decode the post-prefix opcode + ModR/M/SIB/disp/imm body.
    Uses flat `match opc` dispatch (not chained `if-else-if`) so Lean generates
    O(1) equational lemmas per opcode without 2^k branch explosion. -/
def decodeBody (ps : PrefixState) (pfxLen : Nat) (body : List UInt8) : DecodeOutcome :=
  match body with
  | [] => .fault .truncated
  | opc :: rest =>
      match opc with
      -- 0x90: NOP iff REX.B = 0; otherwise XCHG r8d/r8, eax/rax!
      | 0x90 =>
        if ps.hasLock then .fault .udIllegalLock
        else if ps.rep != .none then .fault .unsupported
        else if rexB ps.rex == 0 then checkLen15 (pfxLen + 1) .nop
        else if rexW ps.rex then checkLen15 (pfxLen + 1) (.xchg64 ⟨8, by decide⟩ ⟨0, by decide⟩)
        else checkLen15 (pfxLen + 1) (.xchg32 ⟨8, by decide⟩ ⟨0, by decide⟩)
      -- 0x01: ADD r/m64, r64 (MR) or LOCK ADD [r64], r64
      | 0x01 =>
        if !rexW ps.rex || ps.rep != .none || ps.has67 then .fault .unsupported
        else match rest with
        | [] => .fault .truncated
        | modrm :: _ =>
            let modBits := (modrm >>> 6) &&& 0x03
            let reg := mkReg4 (rexR ps.rex) (modrm >>> 3)
            let rm  := mkReg4 (rexB ps.rex) modrm
            if modBits == 3 then
              if ps.hasLock then .fault .udIllegalLock
              else checkLen15 (pfxLen + 2) (.addRR64 rm reg)
            else if modBits == 0 && (modrm &&& 0x07) != 4 && (modrm &&& 0x07) != 5 then
              if ps.hasLock then checkLen15 (pfxLen + 2) (.lockAddMem64 rm reg)
              else .fault .unsupported
            else .fault .unsupported
      -- 0x03: ADD r64, r/m64 (RM) -- alternate register-register encoding!
      | 0x03 =>
        if ps.hasLock then .fault .udIllegalLock
        else if !rexW ps.rex || ps.rep != .none || ps.has67 then .fault .unsupported
        else match rest with
        | [] => .fault .truncated
        | modrm :: _ =>
            let modBits := (modrm >>> 6) &&& 0x03
            let reg := mkReg4 (rexR ps.rex) (modrm >>> 3)
            let rm  := mkReg4 (rexB ps.rex) modrm
            if modBits == 3 then checkLen15 (pfxLen + 2) (.addRR64 reg rm)
            else .fault .unsupported
      -- 0x05: ADD RAX, imm32 (short accumulator form)
      | 0x05 =>
        if ps.hasLock then .fault .udIllegalLock
        else if !rexW ps.rex || ps.rep != .none then .fault .unsupported
        else match rest with
        | b0 :: b1 :: b2 :: b3 :: _ =>
            checkLen15 (pfxLen + 5) (.addImm64 ⟨0, by decide⟩ (readUInt32LE b0 b1 b2 b3))
        | _ => .fault .truncated
      -- 0x81 /0: ADD r64, imm32
      | 0x81 =>
        if ps.hasLock then .fault .udIllegalLock
        else if !rexW ps.rex || ps.rep != .none then .fault .unsupported
        else match rest with
        | modrm :: b0 :: b1 :: b2 :: b3 :: _ =>
            let modBits := (modrm >>> 6) &&& 0x03
            let regExt  := (modrm >>> 3) &&& 0x07
            let rm      := mkReg4 (rexB ps.rex) modrm
            if modBits == 3 && regExt == 0 then
              checkLen15 (pfxLen + 6) (.addImm64 rm (readUInt32LE b0 b1 b2 b3))
            else .fault .unsupported
        | _ => .fault .truncated
      -- 0x83 /0: ADD r64, sign_ext(imm8)
      | 0x83 =>
        if ps.hasLock then .fault .udIllegalLock
        else if !rexW ps.rex || ps.rep != .none then .fault .unsupported
        else match rest with
        | modrm :: imm8 :: _ =>
            let modBits := (modrm >>> 6) &&& 0x03
            let regExt  := (modrm >>> 3) &&& 0x07
            let rm      := mkReg4 (rexB ps.rex) modrm
            if modBits == 3 && regExt == 0 then
              checkLen15 (pfxLen + 3) (.addImm64 rm (signExtend8To32 imm8))
            else .fault .unsupported
        | _ => .fault .truncated
      -- 0x0F two-byte escape: ENDBR64 (F3 0F 1E FA), multi-byte NOP (0F 1F ...), BSF/TZCNT (0F BC)
      | 0x0F =>
        match rest with
        | [] => .fault .truncated
        | opc2 :: rest2 =>
            match opc2 with
            | 0x1E =>
              if ps.hasLock then .fault .udIllegalLock
              else match rest2 with
              | 0xFA :: _ =>
                  if ps.rep == .f3 && ps.rex == none then checkLen15 (pfxLen + 3) .endbr64
                  else .fault .unsupported
              | [] => .fault .truncated
              | _ => .fault .unsupported
            | 0x1F =>
              if ps.hasLock then .fault .udIllegalLock
              else if ps.rep != .none then .fault .unsupported
              else match rest2 with
              | 0x00 :: _ => checkLen15 (pfxLen + 3) .nop
              | 0x44 :: 0x00 :: 0x00 :: _ => checkLen15 (pfxLen + 5) .nop
              | 0x80 :: 0x00 :: 0x00 :: 0x00 :: 0x00 :: _ => checkLen15 (pfxLen + 7) .nop
              | 0x84 :: 0x00 :: 0x00 :: 0x00 :: 0x00 :: 0x00 :: _ => checkLen15 (pfxLen + 8) .nop
              | _ => .fault .unsupported
            | 0xBC =>
              if ps.hasLock then .fault .udIllegalLock
              else if !rexW ps.rex then .fault .unsupported
              else match rest2 with
              | modrm :: _ =>
                  let modBits := (modrm >>> 6) &&& 0x03
                  let reg := mkReg4 (rexR ps.rex) (modrm >>> 3)
                  let rm  := mkReg4 (rexB ps.rex) modrm
                  if modBits == 3 then
                    if ps.rep == .f3 then checkLen15 (pfxLen + 3) (.tzcnt64 reg rm)
                    else if ps.rep == .none then checkLen15 (pfxLen + 3) (.bsf64 reg rm)
                    else .fault .unsupported
                  else .fault .unsupported
              | [] => .fault .truncated
            | _ => .fault .unsupported
      | _ => .fault .unsupported

/-- Architecture (a): Direct total structural x86-64 decoder (`Init.*`-only).
    Uses fuel `16` so up to 15 prefix bytes are scanned and any >15-byte
    encoding deterministically yields `.fault .gpLenExceeded`. -/
def decodeDirect (bs : List UInt8) : DecodeOutcome :=
  match scanPrefixes 16 {} 0 bs with
  | none => .fault .gpLenExceeded
  | some (ps, pfxLen, body) => decodeBody ps pfxLen body

-- Concrete verification of real-compiler and adversarial specimens via `rfl`
example : decodeDirect [0x48, 0x01, 0xF0] = .ok (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) 3 := rfl
example : decodeDirect [0x48, 0x03, 0xC6] = .ok (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) 3 := rfl
example : decodeDirect [0x48, 0x05, 0x01, 0x00, 0x00, 0x00] = .ok (.addImm64 ⟨0, by decide⟩ 1) 6 := rfl
example : decodeDirect [0x48, 0x81, 0xC0, 0x01, 0x00, 0x00, 0x00] = .ok (.addImm64 ⟨0, by decide⟩ 1) 7 := rfl
example : decodeDirect [0x48, 0x83, 0xC0, 0x01] = .ok (.addImm64 ⟨0, by decide⟩ 1) 4 := rfl
example : decodeDirect [0x90] = .ok .nop 1 := rfl
example : decodeDirect [0x48, 0x90] = .ok .nop 2 := rfl
example : decodeDirect [0x41, 0x90] = .ok (.xchg32 ⟨8, by decide⟩ ⟨0, by decide⟩) 2 := rfl
example : decodeDirect [0x49, 0x90] = .ok (.xchg64 ⟨8, by decide⟩ ⟨0, by decide⟩) 2 := rfl
-- Exact 11-byte alignment NOP emitted by `gcc 15.2.0 -O2` (`loop_with_align_nops+6a`):
example : decodeDirect [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] = .ok .nop 11 := rfl
example : decodeDirect [0xF3, 0x0F, 0x1E, 0xFA] = .ok .endbr64 4 := rfl
example : decodeDirect [0xF0, 0x48, 0x01, 0x07] = .ok (.lockAddMem64 ⟨7, by decide⟩ ⟨0, by decide⟩) 4 := rfl
example : decodeDirect [0xF0, 0x48, 0x01, 0xF0] = .fault .udIllegalLock := rfl
example : decodeDirect [0x48, 0x0F, 0xBC, 0xD1] = .ok (.bsf64 ⟨2, by decide⟩ ⟨1, by decide⟩) 4 := rfl
example : decodeDirect [0xF3, 0x48, 0x0F, 0xBC, 0xD1] = .ok (.tzcnt64 ⟨2, by decide⟩ ⟨1, by decide⟩) 5 := rfl
-- 15-byte legal NOP vs 16-byte `#GP(0)`
example : decodeDirect (List.replicate 14 0x66 ++ [0x90]) = .ok .nop 15 := rfl
example : decodeDirect (List.replicate 15 0x66 ++ [0x90]) = .fault .gpLenExceeded := rfl
-- REX nullified before legacy 0x67 -> not 64-bit add
example : decodeDirect [0x48, 0x67, 0x01, 0xF0] = .fault .unsupported := rfl

/-! ### Architecture (b): Canonical vs. Hint-Parameterized Witness-Checked Encoder -/

def rexByte (w r b : Bool) : UInt8 :=
  (0x40 : UInt8) ||| (if w then (0x08 : UInt8) else 0) ||| (if r then (0x04 : UInt8) else 0) ||| (if b then (0x01 : UInt8) else 0)

def modrmRegReg (reg rm : Reg4) : UInt8 :=
  (0xC0 : UInt8) ||| (((reg.val % 8).toUInt8) <<< 3) ||| (rm.val % 8).toUInt8

def modrmMem0 (reg rm : Reg4) : UInt8 :=
  (((reg.val % 8).toUInt8) <<< 3) ||| (rm.val % 8).toUInt8

def encodeUInt32LE (v : UInt32) : List UInt8 :=
  [ v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8 ]

/-- Naive canonical-only encoder (one fixed encoding per `X64Instr`). -/
def encodeCanonical : X64Instr → Option (List UInt8)
  | .nop => some [0x90]
  | .xchg32 ⟨8, _⟩ ⟨0, _⟩ => some [0x41, 0x90]
  | .xchg64 ⟨8, _⟩ ⟨0, _⟩ => some [0x49, 0x90]
  | .addRR64 dst src =>
      some [rexByte true (src.val ≥ 8) (dst.val ≥ 8), 0x01, modrmRegReg src dst]
  | .addImm64 dst imm =>
      some ([rexByte true false (dst.val ≥ 8), 0x81, modrmRegReg ⟨0, by decide⟩ dst] ++ encodeUInt32LE imm)
  | .lockAddMem64 base src =>
      if base.val % 8 == 4 || base.val % 8 == 5 then none
      else some [0xF0, rexByte true (src.val ≥ 8) (base.val ≥ 8), 0x01, modrmMem0 src base]
  | .endbr64 => some [0xF3, 0x0F, 0x1E, 0xFA]
  | .bsf64 dst src =>
      some [rexByte true (dst.val ≥ 8) (src.val ≥ 8), 0x0F, 0xBC, modrmRegReg dst src]
  | .tzcnt64 dst src =>
      some [0xF3, rexByte true (dst.val ≥ 8) (src.val ≥ 8), 0x0F, 0xBC, modrmRegReg dst src]
  | _ => none

/-- Canonical-only encoding fails to match valid compiler-emitted encodings such
    as alternate direction-bit `0x03` and GCC's 11-byte alignment NOP. -/
theorem canonical_encoder_misses_alternate_encodings :
    encodeCanonical (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) ≠ some [0x48, 0x03, 0xC6] ∧
    decodeDirect [0x48, 0x03, 0xC6] = .ok (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) 3 ∧
    encodeCanonical .nop ≠ some [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] ∧
    decodeDirect [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] = .ok .nop 11 := by
  decide

/-- Encoding-mode hint supplied by an untrusted disassembler to a kernel-verified
    parameterized encoder (`Architecture (b)`). -/
inductive EncHint where
  | nop90 (pad66Count : Nat) (rexW : Bool) (emitRex : Bool)
  | nop0F1F84 (pad66Count : Nat) (hasCS : Bool)
  | addRR_01
  | addRR_03
  | addImm_05
  | addImm_81
  | addImm_83 (imm8 : UInt8)
  | canonical
  deriving DecidableEq, Repr

/-- Parameterized witness encoder enforcing all architectural legality side
    conditions (including `≤ 15` bytes, `REX.B = 0` on NOP, sign-extension
    agreement on `0x83`, and register-vs-memory `LOCK` legality). -/
def encodeWithHint (ins : X64Instr) (h : EncHint) : Option (List UInt8) :=
  let raw : Option (List UInt8) :=
    match ins, h with
    | .nop, .nop90 pad66 w emitRex =>
        let p66 := List.replicate pad66 0x66
        let rex := if emitRex then [rexByte w false false] else []
        some (p66 ++ rex ++ [0x90])
    | .nop, .nop0F1F84 pad66 hasCS =>
        let p66 := List.replicate pad66 0x66
        let cs  := if hasCS then [0x2E] else []
        some (p66 ++ cs ++ [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    | .addRR64 dst src, .addRR_01 =>
        some [rexByte true (src.val ≥ 8) (dst.val ≥ 8), 0x01, modrmRegReg src dst]
    | .addRR64 dst src, .addRR_03 =>
        some [rexByte true (dst.val ≥ 8) (src.val ≥ 8), 0x03, modrmRegReg dst src]
    | .addImm64 dst imm, .addImm_05 =>
        if dst.val == 0 then some ([0x48, 0x05] ++ encodeUInt32LE imm) else none
    | .addImm64 dst imm, .addImm_81 =>
        some ([rexByte true false (dst.val ≥ 8), 0x81, modrmRegReg ⟨0, by decide⟩ dst] ++ encodeUInt32LE imm)
    | .addImm64 dst imm, .addImm_83 b =>
        if signExtend8To32 b == imm then
          some [rexByte true false (dst.val ≥ 8), 0x83, modrmRegReg ⟨0, by decide⟩ dst, b]
        else none
    | i, .canonical => encodeCanonical i
    | _, _ => none
  match raw with
  | some bs => if bs.length ≤ 15 then some bs else none
  | none => none

/-- Witness-checked encoding covers all real compiler multiplicity variants. -/
theorem encodeWithHint_covers_multiplicity :
    encodeWithHint (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) .addRR_01 = some [0x48, 0x01, 0xF0] ∧
    encodeWithHint (.addRR64 ⟨0, by decide⟩ ⟨6, by decide⟩) .addRR_03 = some [0x48, 0x03, 0xC6] ∧
    encodeWithHint (.addImm64 ⟨0, by decide⟩ 1) .addImm_05 = some [0x48, 0x05, 0x01, 0x00, 0x00, 0x00] ∧
    encodeWithHint (.addImm64 ⟨0, by decide⟩ 1) .addImm_81 = some [0x48, 0x81, 0xC0, 0x01, 0x00, 0x00, 0x00] ∧
    encodeWithHint (.addImm64 ⟨0, by decide⟩ 1) (.addImm_83 1) = some [0x48, 0x83, 0xC0, 0x01] ∧
    encodeWithHint .nop (.nop0F1F84 2 true) = some [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] ∧
    encodeWithHint .nop (.nop90 14 false false) = some (List.replicate 14 0x66 ++ [0x90]) ∧
    encodeWithHint .nop (.nop90 15 false false) = none := by
  decide

/-! ### Soundness Proof: Prefix-Linearity & Witness-to-Decoder Equivalence -/

/-- Helper lemma: scanning `k` copies of `0x66` advances prefix state cleanly. -/
theorem scanPrefixes_rep66 (k : Nat) (fuel : Nat) (ps : PrefixState) (n : Nat) (tail : List UInt8)
    (h_fuel : k < fuel) :
    scanPrefixes fuel ps n (List.replicate k 0x66 ++ tail) =
      scanPrefixes (fuel - k) (if k = 0 then ps else { ps with has66 := true, rex := none }) (n + k) tail := by
  induction k generalizing fuel ps n with
  | zero =>
      simp
  | succ k ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have h_step0 :
              scanPrefixes (f + 1) ps n (List.replicate (k + 1) 0x66 ++ tail) =
                scanPrefixes f { ps with has66 := true, rex := none } (n + 1) (List.replicate k 0x66 ++ tail) := rfl
          rw [h_step0]
          have h_f : k < f := by omega
          rw [ih f { ps with has66 := true, rex := none } (n + 1) h_f]
          have h_sub : f + 1 - (k + 1) = f - k := by omega
          have h_add : n + 1 + k = n + (k + 1) := by omega
          rw [h_sub, h_add]
          cases k <;> simp

/-- Bit-algebra roundtrip for `mkReg4` on `rexByte` / `modrmRegReg`. -/
private theorem mkReg4_rex_modrm_reg (reg rm : Reg4) :
    mkReg4 (rexR (some (rexByte true (reg.val ≥ 8) (rm.val ≥ 8)))) (modrmRegReg reg rm >>> 3) = reg := by
  revert reg rm
  decide

private theorem mkReg4_rex_modrm_rm (reg rm : Reg4) :
    mkReg4 (rexB (some (rexByte true (reg.val ≥ 8) (rm.val ≥ 8)))) (modrmRegReg reg rm) = rm := by
  revert reg rm
  decide

private theorem mkReg4_rex_mem0_reg (reg rm : Reg4) :
    mkReg4 (rexR (some (rexByte true (reg.val ≥ 8) (rm.val ≥ 8)))) (modrmMem0 reg rm >>> 3) = reg := by
  revert reg rm
  decide

private theorem mkReg4_rex_mem0_rm (reg rm : Reg4) :
    mkReg4 (rexB (some (rexByte true (reg.val ≥ 8) (rm.val ≥ 8)))) (modrmMem0 reg rm) = rm := by
  revert reg rm
  decide

private theorem modBits_modrmRegReg (reg rm : Reg4) :
    ((modrmRegReg reg rm >>> 6) &&& 0x03) = 3 := by
  revert reg rm
  decide

private theorem modBits_modrmMem0 (reg rm : Reg4) :
    ((modrmMem0 reg rm >>> 6) &&& 0x03) = 0 := by
  revert reg rm
  decide

private theorem regExt_modrmRegReg_zero (rm : Reg4) :
    ((modrmRegReg 0 rm >>> 3) &&& 0x07) = 0 := by
  revert rm
  decide

private theorem mkReg4_rex_modrm_rm_zero (rm : Reg4) :
    mkReg4 (rexB (some (rexByte true false (rm.val ≥ 8)))) (modrmRegReg 0 rm) = rm := by
  revert rm
  decide

private theorem isRex_rexByte (w r b : Bool) : isRexPrefix (rexByte w r b) = true := by
  cases w <;> cases r <;> cases b <;> decide

private theorem notLegacy_rexByte (w r b : Bool) : isLegacyPrefix (rexByte w r b) = false := by
  cases w <;> cases r <;> cases b <;> decide

private theorem rexW_rexByte (w r b : Bool) : rexW (some (rexByte w r b)) = w := by
  cases w <;> cases r <;> cases b <;> decide

private theorem rexB_rexByte_false (w r : Bool) : rexB (some (rexByte w r false)) = 0 := by
  cases w <;> cases r <;> decide

private theorem scanPrefixes_rex (f : Nat) (ps : PrefixState) (n : Nat)
    (w r b : Bool) (tail : List UInt8) :
    scanPrefixes (f + 1) ps n (rexByte w r b :: tail) =
      scanPrefixes f { ps with rex := some (rexByte w r b) } (n + 1) tail := by
  cases w <;> cases r <;> cases b <;> rfl

private theorem scanPrefixes_stop (f : Nat) (ps : PrefixState) (n : Nat)
    (opc : UInt8) (tail : List UInt8)
    (h1 : isLegacyPrefix opc = false) (h2 : isRexPrefix opc = false) :
    scanPrefixes (f + 1) ps n (opc :: tail) = some (ps, n, opc :: tail) := by
  simp [scanPrefixes, h1, h2]

private theorem readUInt32LE_encodeUInt32LE (v : UInt32) :
    readUInt32LE v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  unfold readUInt32LE
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) |||
    ((v >>> 16).toUInt8.toUInt32 <<< 16) ||| ((v >>> 24).toUInt8.toUInt32 <<< 24)).toNat = v.toNat
  apply Nat.eq_of_testBit_eq
  intro i
  have hlt : v.toNat < 2 ^ 32 := v.toBitVec.isLt
  have h_sh : ∀ (a k : UInt32), (a <<< k).toNat = (a.toNat <<< (k.toNat % 32)) % 2 ^ 32 := by
    intro a k; simp [UInt32.toNat_shiftLeft]
  have h_shr : ∀ (a k : UInt32), (a >>> k).toNat = a.toNat >>> (k.toNat % 32) := by
    intro a k; simp [UInt32.toNat_shiftRight]
  have h_u8 : ∀ (a : UInt32), a.toUInt8.toUInt32.toNat = a.toNat % 2 ^ 8 := by
    intro a; simp
  have h8 : (8 : UInt32).toNat % 32 = 8 := rfl
  have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
  have h24 : (24 : UInt32).toNat % 32 = 24 := rfl
  simp only [UInt32.toNat_or, h_sh, h_u8, h_shr, h8, h16, h24,
             Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h32 : i < 32
  · have hcases : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) := by omega
    rcases hcases with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have ha : ¬ (8 ≤ i) := by omega
      have hb : ¬ (16 ≤ i) := by omega
      have hc : ¬ (24 ≤ i) := by omega
      simp [h32, h0, ha, hb, hc]
    · have ha : ¬ (i < 8) := by omega
      have hb : i - 8 < 8 := by omega
      have hc : ¬ (16 ≤ i) := by omega
      have hd : ¬ (24 ≤ i) := by omega
      have he : 8 + (i - 8) = i := by omega
      simp [h32, ha, h1, hb, hc, hd, he]
    · have ha : ¬ (i < 8) := by omega
      have hb : ¬ (i - 8 < 8) := by omega
      have hc : i - 16 < 8 := by omega
      have hd : ¬ (24 ≤ i) := by omega
      have he : 16 + (i - 16) = i := by omega
      simp [h32, ha, hb, h1, hc, hd, he]
    · have ha : ¬ (i < 8) := by omega
      have hb : ¬ (i - 8 < 8) := by omega
      have hc : ¬ (i - 16 < 8) := by omega
      have hd : i - 24 < 8 := by omega
      have he : 24 + (i - 24) = i := by omega
      simp [h32, ha, hb, hc, h1, hd, he]
  · have ha : ¬ (i < 8) := by omega
    have hfalse : v.toNat.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h32, ha, hfalse]

/-- Key Theorem 1 (Soundness of Hint-Parameterized Witness Encoder w.r.t.
    Direct Structural Decoder, with arbitrary trailing code bytes `rest`):
    Every `(ins, h)` accepted by `encodeWithHint` decodes under `decodeDirect`
    with ANY trailing suffix `rest` to `ins` and exact length `bs.length`! -/
theorem encodeWithHint_sound_wrt_decodeDirect
    (ins : X64Instr) (h : EncHint) (bs rest : List UInt8)
    (h_enc : encodeWithHint ins h = some bs) :
    decodeDirect (bs ++ rest) = .ok ins bs.length := by
  unfold encodeWithHint at h_enc
  cases ins with
  | nop =>
      cases h with
      | nop90 pad66 w emitRex =>
          cases emitRex with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at h_enc
              split at h_enc
              · rename_i h_len
                injection h_enc with h_bs; subst h_bs
                simp only [List.length_append, List.length_replicate, List.length_singleton] at h_len ⊢
                have h_k : pad66 < 16 := by omega
                unfold decodeDirect
                rw [List.append_assoc, List.singleton_append,
                    scanPrefixes_rep66 pad66 16 {} 0 (0x90 :: rest) h_k]
                have h_rem : 16 - pad66 = (15 - pad66) + 1 := by omega
                rw [h_rem, scanPrefixes_stop _ _ _ 0x90 rest rfl rfl]
                cases pad66 <;> simp [decodeBody, rexB, checkLen15] <;> omega
              · cases h_enc
          | true =>
              simp only [↓reduceIte] at h_enc
              split at h_enc
              · rename_i h_len
                injection h_enc with h_bs; subst h_bs
                simp only [List.length_append, List.length_replicate, List.length_singleton] at h_len ⊢
                have h_k : pad66 < 16 := by omega
                unfold decodeDirect
                rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append,
                    scanPrefixes_rep66 pad66 16 {} 0 (rexByte w false false :: 0x90 :: rest) h_k]
                have h_rem : 16 - pad66 = (14 - pad66) + 2 := by omega
                rw [h_rem, scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x90 rest rfl rfl]
                cases pad66 <;> simp [decodeBody, rexB_rexByte_false, checkLen15] <;> omega
              · cases h_enc
      | nop0F1F84 pad66 hasCS =>
          cases hasCS with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at h_enc
              split at h_enc
              · rename_i h_len
                injection h_enc with h_bs; subst h_bs
                simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h_len ⊢
                have h_k : pad66 < 16 := by omega
                unfold decodeDirect
                rw [List.append_assoc, List.cons_append,
                    scanPrefixes_rep66 pad66 16 {} 0 _ h_k]
                have h_rem : 16 - pad66 = (15 - pad66) + 1 := by omega
                rw [h_rem, scanPrefixes_stop _ _ _ 0x0F _ rfl rfl]
                have h15 : 0 + pad66 + 8 ≤ 15 := by omega
                cases pad66 <;> simp [decodeBody, checkLen15] <;> omega
              · cases h_enc
          | true =>
              simp only [↓reduceIte] at h_enc
              split at h_enc
              · rename_i h_len
                injection h_enc with h_bs; subst h_bs
                simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h_len ⊢
                have h_k : pad66 < 16 := by omega
                unfold decodeDirect
                rw [List.append_assoc, List.append_assoc, List.singleton_append, List.cons_append,
                    scanPrefixes_rep66 pad66 16 {} 0 _ h_k]
                have h_rem : 16 - pad66 = (14 - pad66) + 2 := by omega
                rw [h_rem]
                have h_cs : ∀ (f : Nat) (ps : PrefixState) (n : Nat) (tl : List UInt8),
                    scanPrefixes (f + 1) ps n (0x2E :: tl) =
                      scanPrefixes f { ps with hasCS := true, rex := none } (n + 1) tl :=
                  fun _ _ _ _ => rfl
                rw [h_cs, scanPrefixes_stop _ _ _ 0x0F _ rfl rfl]
                cases pad66 <;> simp [decodeBody, checkLen15] <;> omega
              · cases h_enc
      | canonical =>
          simp only [encodeCanonical] at h_enc
          injection h_enc with h_bs; subst h_bs; rfl
      | _ => cases h_enc
  | xchg32 r1 r2 =>
      cases h with
      | canonical =>
          by_cases h1 : r1 = ⟨8, by decide⟩ ∧ r2 = ⟨0, by decide⟩
          · rcases h1 with ⟨rfl, rfl⟩
            simp only [encodeCanonical] at h_enc
            injection h_enc with h_bs; subst h_bs; rfl
          · have hnone : encodeCanonical (.xchg32 r1 r2) = none := by
              clear h_enc; revert r1 r2 h1; decide
            simp [hnone] at h_enc
      | _ => cases h_enc
  | xchg64 r1 r2 =>
      cases h with
      | canonical =>
          by_cases h1 : r1 = ⟨8, by decide⟩ ∧ r2 = ⟨0, by decide⟩
          · rcases h1 with ⟨rfl, rfl⟩
            simp only [encodeCanonical] at h_enc
            injection h_enc with h_bs; subst h_bs; rfl
          · have hnone : encodeCanonical (.xchg64 r1 r2) = none := by
              clear h_enc; revert r1 r2 h1; decide
            simp [hnone] at h_enc
      | _ => cases h_enc
  | addRR64 dst src =>
      cases h with
      | addRR_01 =>
          simp only [] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x01 _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, mkReg4_rex_modrm_reg,
                mkReg4_rex_modrm_rm, checkLen15]
      | addRR_03 =>
          simp only [] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x03 _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, mkReg4_rex_modrm_reg,
                mkReg4_rex_modrm_rm, checkLen15]
      | canonical =>
          simp only [encodeCanonical] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x01 _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, mkReg4_rex_modrm_reg,
                mkReg4_rex_modrm_rm, checkLen15]
      | _ => cases h_enc
  | addImm64 dst imm =>
      cases h with
      | addImm_05 =>
          by_cases h0 : dst.val = 0
          · have h_eq : dst = ⟨0, by decide⟩ := Fin.ext h0
            subst h_eq
            simp only [encodeUInt32LE, beq_self_eq_true, ↓reduceIte] at h_enc
            injection h_enc with h_bs; subst h_bs
            unfold decodeDirect
            simp only [List.cons_append, List.nil_append]
            have h48 : scanPrefixes 16 {} 0 (0x48 :: 0x05 :: imm.toUInt8 :: (imm >>> 8).toUInt8 ::
                (imm >>> 16).toUInt8 :: (imm >>> 24).toUInt8 :: rest) =
                scanPrefixes 15 { rex := some 0x48 } 1 (0x05 :: imm.toUInt8 :: (imm >>> 8).toUInt8 ::
                (imm >>> 16).toUInt8 :: (imm >>> 24).toUInt8 :: rest) := rfl
            have hrw : rexW (some 0x48) = true := rfl
            rw [h48, scanPrefixes_stop _ _ _ 0x05 _ rfl rfl]
            simp [decodeBody, hrw, readUInt32LE_encodeUInt32LE, checkLen15]
          · simp [h0] at h_enc
      | addImm_81 =>
          simp only [encodeUInt32LE] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x81 _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, regExt_modrmRegReg_zero,
                mkReg4_rex_modrm_rm_zero, readUInt32LE_encodeUInt32LE, checkLen15]
      | addImm_83 b =>
          by_cases hs : signExtend8To32 b = imm
          · simp only [hs, beq_self_eq_true, ↓reduceIte] at h_enc
            injection h_enc with h_bs; subst h_bs
            unfold decodeDirect
            simp only [List.cons_append, List.nil_append]
            rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x83 _ rfl rfl]
            simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, regExt_modrmRegReg_zero,
                  mkReg4_rex_modrm_rm_zero, hs, checkLen15]
          · simp [hs] at h_enc
      | canonical =>
          simp only [encodeCanonical, encodeUInt32LE] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x81 _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, regExt_modrmRegReg_zero,
                mkReg4_rex_modrm_rm_zero, readUInt32LE_encodeUInt32LE, checkLen15]
      | _ => cases h_enc
  | lockAddMem64 base src =>
      cases h with
      | canonical =>
          by_cases hbad : (base.val % 8 == 4 || base.val % 8 == 5) = true
          · simp [encodeCanonical, hbad] at h_enc
          · simp only [encodeCanonical, hbad, Bool.false_eq_true, ↓reduceIte] at h_enc
            injection h_enc with h_bs; subst h_bs
            have h_rm4 : (modrmMem0 src base &&& 0x07) ≠ 4 := by
              revert src base hbad; decide
            have h_rm5 : (modrmMem0 src base &&& 0x07) ≠ 5 := by
              revert src base hbad; decide
            unfold decodeDirect
            simp only [List.cons_append, List.nil_append]
            have hf0 : ∀ (tl : List UInt8),
                scanPrefixes 16 {} 0 (0xF0 :: tl) = scanPrefixes 15 { hasLock := true, rex := none } 1 tl :=
              fun _ => rfl
            rw [hf0, scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x01 _ rfl rfl]
            simp [decodeBody, rexW_rexByte, modBits_modrmMem0, mkReg4_rex_mem0_reg,
                  mkReg4_rex_mem0_rm, h_rm4, h_rm5, checkLen15]
      | _ => cases h_enc
  | endbr64 =>
      cases h with
      | canonical =>
          simp only [encodeCanonical] at h_enc
          injection h_enc with h_bs; subst h_bs; rfl
      | _ => cases h_enc
  | bsf64 dst src =>
      cases h with
      | canonical =>
          simp only [encodeCanonical] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          rw [scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x0F _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, mkReg4_rex_modrm_reg,
                mkReg4_rex_modrm_rm, checkLen15]
      | _ => cases h_enc
  | tzcnt64 dst src =>
      cases h with
      | canonical =>
          simp only [encodeCanonical] at h_enc
          injection h_enc with h_bs; subst h_bs
          unfold decodeDirect
          simp only [List.cons_append, List.nil_append]
          have hf3 : ∀ (tl : List UInt8),
              scanPrefixes 16 {} 0 (0xF3 :: tl) = scanPrefixes 15 { rep := .f3, rex := none } 1 tl :=
            fun _ => rfl
          rw [hf3, scanPrefixes_rex, scanPrefixes_stop _ _ _ 0x0F _ rfl rfl]
          simp [decodeBody, rexW_rexByte, modBits_modrmRegReg, mkReg4_rex_modrm_reg,
                mkReg4_rex_modrm_rm, checkLen15]
      | _ => cases h_enc

/-- Key Theorem 2 (Unambiguity / Functionality of Witness-Checked Encoding):
    Even across overlapping prefixes and trailing code bytes (`bs₁ ++ rest₁ = bs₂ ++ rest₂`),
    two valid encoding witnesses for the same byte stream MUST decode to the
    exact same instruction and identical byte length! -/
theorem encodeWithHint_unambiguous
    {i₁ i₂ : X64Instr} {h₁ h₂ : EncHint} {bs₁ bs₂ rest₁ rest₂ : List UInt8}
    (he₁ : encodeWithHint i₁ h₁ = some bs₁)
    (he₂ : encodeWithHint i₂ h₂ = some bs₂)
    (h_stream : bs₁ ++ rest₁ = bs₂ ++ rest₂) :
    i₁ = i₂ ∧ bs₁.length = bs₂.length := by
  have d₁ := encodeWithHint_sound_wrt_decodeDirect i₁ h₁ bs₁ rest₁ he₁
  have d₂ := encodeWithHint_sound_wrt_decodeDirect i₂ h₂ bs₂ rest₂ he₂
  rw [h_stream] at d₁
  rw [d₁] at d₂
  injection d₂ with hi hlen
  exact ⟨hi, hlen⟩

/-- Negative Control: an under-constrained witness encoder that allows ANY
    REX byte `0x40..0x4F` before `0x90` (forgetting `REX.B = 0`) is AMBIGUOUS:
    the identical byte stream `[0x41, 0x90]` is accepted both as `.nop` AND as
    `.xchg32 r8d, eax`, allowing an untrusted prover to forge a `nop` proof for
    an instruction that actually mutates `rax` and `r8`! -/
def buggyEncodeWithHint (ins : X64Instr) (rexByteOpt : Option UInt8) : Option (List UInt8) :=
  match ins, rexByteOpt with
  | .nop, some b => if isRexPrefix b then some [b, 0x90] else none
  | .xchg32 ⟨8, _⟩ ⟨0, _⟩, none => some [0x41, 0x90]
  | _, _ => none

theorem buggy_witness_checker_ambiguous_on_41_90 :
    buggyEncodeWithHint .nop (some 0x41) = some [0x41, 0x90] ∧
    buggyEncodeWithHint (.xchg32 ⟨8, by decide⟩ ⟨0, by decide⟩) none = some [0x41, 0x90] ∧
    X64Instr.nop ≠ X64Instr.xchg32 ⟨8, by decide⟩ ⟨0, by decide⟩ := by
  decide

/-! ## Part 2: Generalized Two-Model Pass-2 ISA Correspondence (`I_ref ⊆ I_anneal`)

Demonstrates:
1. Per-opcode staged support gate lifting to universal multi-step one-way
   behavioral refinement (`RefBehavior → AnnealBehavior`) and sound
   `SatisfiesPost` transfer (`SatisfiesPost_anneal → SatisfiesPost_ref`).
2. ISA-level nondeterminism across four real hardware phenomena:
   - x86 undefined flags (`BSF`/`SHL`/`MUL`),
   - RVV `vta=1` tail-agnostic lanes (`undisturbed ∨ all-1s`),
   - RISC-V `LR`/`SC` spurious reservation failure,
   - IEEE-754 quiet-NaN payload propagation.
3. Why symmetric `↔` equivalence fails against a narrow/deterministic `I_ref`
   (such as `opencompl/sail-riscv-lean`'s hardcoded `vta = undisturbed`), while
   one-way refinement `I_ref ⊆ I_anneal` succeeds.
4. Poison-fault vs. demonic-bit-choice trade-off for x86 undefined flags:
   poison preserves `SatisfiesPost` transfer while breaking reverse fault equivalence.
5. Negative control: copying a narrow concrete `I_ref` into `I_anneal` proves
   false properties violated by normative hardware.
-/

inductive IsaOp where
  | add64                 -- deterministic, in-scope
  | bsf64                 -- x86 undefined flags (`CF` undef; `dest` undef if src=0), in-scope
  | shl64                 -- x86 undefined `OF` when shift > 1, in-scope
  | rvvAddVta             -- RVV `vta=1` tail-agnostic (`undisturbed` or `all-1s`), in-scope
  | scWord                -- RISC-V `SC` (may spuriously fail even when reserved), in-scope
  | faddNan               -- quiet NaN payload nondeterminism, in-scope
  | unmodeledExt          -- out-of-scope extension (e.g. AMX / SME), gated to `.unsupported`
  deriving DecidableEq, Repr

def SupportedOp : IsaOp → Bool
  | .unmodeledExt => false
  | _ => true

/-- Architectural state abstraction covering GPRs, x86 flags (with optional poison),
    RVV tail lane, LR/SC reservation bit, and FP result lane. -/
structure IsaState where
  pc       : Nat
  regA     : BitVec 64
  regB     : BitVec 64
  flagCF   : Option Bool   -- `none` used only by poison variant; `some b` in bit-choice variant
  flagOF   : Option Bool
  rvvTail  : BitVec 64
  reserved : Bool
  fpLane   : BitVec 64
  deriving DecidableEq, Repr

/-- Explicit demonic choice oracle for ISA-level nondeterminism. -/
structure IsaChoice where
  undefBit1   : Bool
  undefBit2   : Bool
  undefWord   : BitVec 64
  vtaAllOnes  : Bool       -- `false` = undisturbed, `true` = all-1s (`0xFFFF...`)
  scSpurious  : Bool       -- `true` = spurious SC failure even if `reserved = true`
  nanPayload  : BitVec 51  -- quiet NaN payload (bit 51 forced to 1)
  deriving DecidableEq, Repr

inductive IsaFault where
  | archTrap    -- architectural fault (`#UD`, `#DE`, `#GP`, misaligned)
  | undefined   -- UB / poison read
  | unsupported -- staged support gate (out-of-scope opcode)
  deriving DecidableEq, Repr

inductive IsaStepResult where
  | step (s' : IsaState)
  | done (out : BitVec 64)
  | fault (k : IsaFault)
  deriving DecidableEq, Repr

abbrev IsaProg := Nat → Option IsaOp

def quietNaN (payload : BitVec 51) : BitVec 64 :=
  (0x7FF8000000000000#64) ||| (payload.zeroExtend 64)

/-- Normative wide `I_anneal` (demonic bit choice on all architectural nondeterminism,
    fail-closed `.fault .unsupported` on out-of-scope opcodes). -/
def evalAnnealOp (op : IsaOp) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match op with
  | .add64 =>
      .step { s with pc := s.pc + 1, regA := s.regA + s.regB }
  | .bsf64 =>
      let res := if s.regB == 0#64 then c.undefWord else 0#64
      .step { s with pc := s.pc + 1, regA := res, flagCF := some c.undefBit1, flagOF := some c.undefBit2 }
  | .shl64 =>
      let cnt := s.regB.toNat % 64
      let newOF := if cnt == 0 then s.flagOF else if cnt == 1 then some false else some c.undefBit1
      .step { s with pc := s.pc + 1, regA := s.regA <<< cnt, flagOF := newOF }
  | .rvvAddVta =>
      let tail := if c.vtaAllOnes then 0xFFFFFFFFFFFFFFFF#64 else s.rvvTail
      .step { s with pc := s.pc + 1, regA := s.regA + s.regB, rvvTail := tail }
  | .scWord =>
      let ok := s.reserved && !c.scSpurious
      .step { s with pc := s.pc + 1, regA := if ok then 0#64 else 1#64, reserved := false }
  | .faddNan =>
      .step { s with pc := s.pc + 1, fpLane := quietNaN c.nanPayload }
  | .unmodeledExt =>
      .fault .unsupported

def evalAnnealStep (p : IsaProg) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match p s.pc with
  | none => .done s.regA
  | some op => evalAnnealOp op c s

/-- Reference model `I_ref`: covers `unmodeledExt` as a real step, and models a
    *narrower* concrete RVV `vta` implementation (like `opencompl/sail-riscv-lean`,
    which hardcodes `AGNOSTIC` to undisturbed `s.rvvTail`) plus canonical NaN `0`. -/
def evalRefNarrowOp (op : IsaOp) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match op with
  | .add64 =>
      .step { s with pc := s.pc + 1, regA := s.regA + s.regB }
  | .bsf64 =>
      let res := if s.regB == 0#64 then c.undefWord else 0#64
      .step { s with pc := s.pc + 1, regA := res, flagCF := some c.undefBit1, flagOF := some c.undefBit2 }
  | .shl64 =>
      let cnt := s.regB.toNat % 64
      let newOF := if cnt == 0 then s.flagOF else if cnt == 1 then some false else some c.undefBit1
      .step { s with pc := s.pc + 1, regA := s.regA <<< cnt, flagOF := newOF }
  | .rvvAddVta =>
      -- Narrow concrete reference (hardcodes undisturbed, ignores `c.vtaAllOnes`)
      .step { s with pc := s.pc + 1, regA := s.regA + s.regB, rvvTail := s.rvvTail }
  | .scWord =>
      let ok := s.reserved && !c.scSpurious
      .step { s with pc := s.pc + 1, regA := if ok then 0#64 else 1#64, reserved := false }
  | .faddNan =>
      -- Narrow concrete reference (always emits canonical quiet NaN with payload 0)
      .step { s with pc := s.pc + 1, fpLane := quietNaN 0#51 }
  | .unmodeledExt =>
      -- Out-of-scope instruction IS implemented in `I_ref`, gated in `I_anneal`
      .step { s with pc := s.pc + 1, regA := s.regA ^^^ s.regB }

def evalRefStep (p : IsaProg) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match p s.pc with
  | none => .done s.regA
  | some op => evalRefNarrowOp op c s

/-- Generic small-step transition, reachability, well-formedness, behavior,
    divergence, and partial-correctness specification (`SatisfiesPost`),
    matching `Trusted.MirSemantics` in `joshlf/anneal`. -/
def StepOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s : IsaState) (res : IsaStepResult) : Prop :=
  ∃ c : IsaChoice, eval p c s = res

inductive ReachesOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) : IsaState → IsaState → Prop where
  | refl (s : IsaState) : ReachesOf eval p s s
  | tail {s₁ s₂ s₃ : IsaState} :
      ReachesOf eval p s₁ s₂ → StepOf eval p s₂ (.step s₃) → ReachesOf eval p s₁ s₃

def ReachesResOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s₀ : IsaState) (res : IsaStepResult) : Prop :=
  ∃ s : IsaState, ReachesOf eval p s₀ s ∧ StepOf eval p s res

def WellFormedOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s₀ : IsaState) : Prop :=
  ∀ k : IsaFault, ¬ ReachesResOf eval p s₀ (.fault k)

def BehaviorOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s₀ : IsaState) (out : BitVec 64) : Prop :=
  ReachesResOf eval p s₀ (.done out)

def DivergesOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s₀ : IsaState) : Prop :=
  ∃ trace : Nat → IsaState,
    trace 0 = s₀ ∧ ∀ n, StepOf eval p (trace n) (.step (trace (n + 1)))

def SatisfiesPostOf (eval : IsaProg → IsaChoice → IsaState → IsaStepResult)
    (p : IsaProg) (s₀ : IsaState) (post : BitVec 64 → Prop) : Prop :=
  WellFormedOf eval p s₀ ∧ ∀ out, BehaviorOf eval p s₀ out → post out

/-- Per-opcode one-way refinement obligation (the exact unit that can be proved
    independently per opcode / extension module in Pass-2 CI!):
    For every supported opcode `op`, every transition of `I_ref` is witnessed by
    some admissible choice `c'` in `I_anneal`. -/
theorem per_opcode_ref_refined_by_anneal (op : IsaOp) (h_sup : SupportedOp op = true)
    (s : IsaState) (c : IsaChoice) :
    ∃ c' : IsaChoice, evalAnnealOp op c' s = evalRefNarrowOp op c s := by
  cases op with
  | add64 => exact ⟨c, rfl⟩
  | bsf64 => exact ⟨c, rfl⟩
  | shl64 => exact ⟨c, rfl⟩
  | rvvAddVta => exact ⟨{ c with vtaAllOnes := false }, rfl⟩
  | scWord => exact ⟨c, rfl⟩
  | faddNan => exact ⟨{ c with nanPayload := 0#51 }, rfl⟩
  | unmodeledExt => simp [SupportedOp] at h_sup

/-- Lifting lemma: if a state `s` does not fault in `I_anneal`, then any `I_ref`
    step from `s` is also an `I_anneal` step (out-of-scope opcodes are ruled out
    by `I_anneal`'s fail-closed `.fault .unsupported`). -/
theorem step_ref_to_anneal_of_no_fault (p : IsaProg) (s : IsaState) (res : IsaStepResult)
    (h_nofault : ∀ k, ¬ StepOf evalAnnealStep p s (.fault k))
    (h_ref : StepOf evalRefStep p s res) :
    StepOf evalAnnealStep p s res := by
  obtain ⟨c, hc⟩ := h_ref
  unfold evalRefStep at hc
  cases hp : p s.pc with
  | none =>
      rw [hp] at hc
      exact ⟨c, by simp [evalAnnealStep, hp, hc]⟩
  | some op =>
      rw [hp] at hc
      cases hsup : SupportedOp op with
      | true =>
          obtain ⟨c', hc'⟩ := per_opcode_ref_refined_by_anneal op hsup s c
          exact ⟨c', by simp [evalAnnealStep, hp, hc', hc]⟩
      | false =>
          cases op with
          | unmodeledExt =>
              exfalso
              exact h_nofault .unsupported ⟨c, by simp [evalAnnealStep, hp, evalAnnealOp]⟩
          | _ => simp [SupportedOp] at hsup

theorem reaches_ref_to_anneal (p : IsaProg) (s₀ s : IsaState)
    (h_wf : WellFormedOf evalAnnealStep p s₀)
    (h_reach : ReachesOf evalRefStep p s₀ s) :
    ReachesOf evalAnnealStep p s₀ s := by
  induction h_reach with
  | refl => exact .refl s₀
  | @tail s₁ s₂ _ hstep ih =>
      have h_nf : ∀ k, ¬ StepOf evalAnnealStep p s₁ (.fault k) := fun k hs =>
        h_wf k ⟨s₁, ih, hs⟩
      exact .tail ih (step_ref_to_anneal_of_no_fault p s₁ (.step s₂) h_nf hstep)

/-- Key Theorem 3 (Staged-Gate Pass-2 One-Way Correspondence `I_ref ⊆ I_anneal`):
    Per-opcode correspondence over `SupportedOp` lifts universally to:
    (1) UB/fault-freedom transfer (`WellFormed_anneal → WellFormed_ref`),
    (2) behavior inclusion (`Behavior_ref ⊆ Behavior_anneal`),
    (3) divergence inclusion (`Diverges_ref → Diverges_anneal`), and
    (4) sound `SatisfiesPost` transfer (`SatisfiesPost_anneal → SatisfiesPost_ref`). -/
theorem pass2_isa_correspondence_and_post_transfer (p : IsaProg) (s₀ : IsaState) :
    (WellFormedOf evalAnnealStep p s₀ →
      WellFormedOf evalRefStep p s₀ ∧
      (∀ out, BehaviorOf evalRefStep p s₀ out → BehaviorOf evalAnnealStep p s₀ out) ∧
      (DivergesOf evalRefStep p s₀ → DivergesOf evalAnnealStep p s₀)) ∧
    (∀ post, SatisfiesPostOf evalAnnealStep p s₀ post → SatisfiesPostOf evalRefStep p s₀ post) := by
  have h_main : WellFormedOf evalAnnealStep p s₀ →
      WellFormedOf evalRefStep p s₀ ∧
      (∀ out, BehaviorOf evalRefStep p s₀ out → BehaviorOf evalAnnealStep p s₀ out) ∧
      (DivergesOf evalRefStep p s₀ → DivergesOf evalAnnealStep p s₀) := by
    intro h_wf
    refine ⟨?_, ?_, ?_⟩
    · intro k ⟨s, hr, hstep⟩
      have hrA := reaches_ref_to_anneal p s₀ s h_wf hr
      have h_nf : ∀ k', ¬ StepOf evalAnnealStep p s (.fault k') := fun k' hs =>
        h_wf k' ⟨s, hrA, hs⟩
      exact h_wf k ⟨s, hrA, step_ref_to_anneal_of_no_fault p s (.fault k) h_nf hstep⟩
    · intro out ⟨s, hr, hstep⟩
      have hrA := reaches_ref_to_anneal p s₀ s h_wf hr
      have h_nf : ∀ k', ¬ StepOf evalAnnealStep p s (.fault k') := fun k' hs =>
        h_wf k' ⟨s, hrA, hs⟩
      exact ⟨s, hrA, step_ref_to_anneal_of_no_fault p s (.done out) h_nf hstep⟩
    · intro ⟨trace, h0, hsteps⟩
      have hreach_all : ∀ n, ReachesOf evalRefStep p s₀ (trace n) := by
        intro n; induction n with
        | zero => rw [h0]; exact .refl s₀
        | succ n ih => exact .tail ih (hsteps n)
      refine ⟨trace, h0, fun n => ?_⟩
      have hrA := reaches_ref_to_anneal p s₀ (trace n) h_wf (hreach_all n)
      have h_nf : ∀ k', ¬ StepOf evalAnnealStep p (trace n) (.fault k') := fun k' hs =>
        h_wf k' ⟨trace n, hrA, hs⟩
      exact step_ref_to_anneal_of_no_fault p (trace n) (.step (trace (n + 1))) h_nf (hsteps n)
  refine ⟨h_main, ?_⟩
  intro post ⟨h_wf, h_post⟩
  obtain ⟨h_rwf, h_beh, _⟩ := h_main h_wf
  exact ⟨h_rwf, fun out hout => h_post out (h_beh out hout)⟩

/-- Key Theorem 4 (Why Symmetric `↔` Fails Under Narrow Concrete `I_ref`):
    For a program observing the RVV `vta=1` tail lane (`evalTailStep`),
    `I_ref ⊆ I_anneal` holds, whereas `I_anneal ⊆ I_ref` (symmetric `↔`) is
    provably FALSE because `I_anneal` admits `all-1s` while narrow `I_ref`
    hardcodes undisturbed `0`. -/
def evalAnnealTailOut (p : IsaProg) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match p s.pc with
  | none => .done s.rvvTail
  | some op => evalAnnealOp op c s

def evalRefTailOut (p : IsaProg) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match p s.pc with
  | none => .done s.rvvTail
  | some op => evalRefNarrowOp op c s

def vtaProg : IsaProg
  | 0 => some .rvvAddVta
  | _ => none

def initZeroState : IsaState :=
  { pc := 0, regA := 1#64, regB := 2#64, flagCF := some false, flagOF := some false,
    rvvTail := 0#64, reserved := true, fpLane := 0#64 }

theorem symmetric_vta_iff_false :
    BehaviorOf evalAnnealTailOut vtaProg initZeroState 0xFFFFFFFFFFFFFFFF#64 ∧
    ¬ BehaviorOf evalRefTailOut vtaProg initZeroState 0xFFFFFFFFFFFFFFFF#64 := by
  constructor
  · let c1 : IsaChoice :=
      { undefBit1 := false, undefBit2 := false, undefWord := 0#64,
        vtaAllOnes := true, scSpurious := false, nanPayload := 0#51 }
    let s1 : IsaState := { initZeroState with pc := 1, regA := 3#64, rvvTail := 0xFFFFFFFFFFFFFFFF#64 }
    refine ⟨s1, .tail (.refl _) ⟨c1, by rfl⟩, ⟨c1, by rfl⟩⟩
  · rintro ⟨s, hr, ⟨c, hc⟩⟩
    -- Any reachable state from `initZeroState` under narrow `evalRefTailOut` has `rvvTail = 0`
    have h_inv : ∀ s', ReachesOf evalRefTailOut vtaProg initZeroState s' → s'.rvvTail = 0#64 := by
      intro s' h
      induction h with
      | refl => rfl
      | @tail s₁ s₂ _ hst ih =>
          obtain ⟨c', hc'⟩ := hst
          unfold evalRefTailOut at hc'
          cases hp : vtaProg s₁.pc with
          | none => rw [hp] at hc'; cases hc'
          | some op =>
              rw [hp] at hc'
              cases hpc : s₁.pc with
              | zero =>
                  rw [hpc] at hp; simp [vtaProg] at hp; subst hp
                  simp [evalRefNarrowOp] at hc'
                  rw [← hc']; exact ih
              | succ n =>
                  rw [hpc] at hp; simp [vtaProg] at hp
    have htail := h_inv s hr
    unfold evalRefTailOut at hc
    cases hp : vtaProg s.pc with
    | none =>
        rw [hp] at hc
        injection hc with hdone
        rw [htail] at hdone
        exact absurd hdone (by decide)
    | some op =>
        rw [hp] at hc
        cases op <;> simp [evalRefNarrowOp] at hc

/-- Key Theorem 5 (Negative Control — Narrow `I_anneal` Unsound Against Hardware):
    If `I_anneal` copies narrow `sail-riscv-lean` (`rvvTail` hardcoded undisturbed),
    it proves `post (out) := (out = 0#64)` for `vtaProg`, which normative hardware
    (choosing `vtaAllOnes = true`) VIOLATES! -/
theorem narrow_anneal_proves_false_hardware_property :
    SatisfiesPostOf evalRefTailOut vtaProg initZeroState (fun out => out = 0#64) ∧
    ¬ SatisfiesPostOf evalAnnealTailOut vtaProg initZeroState (fun out => out = 0#64) := by
  constructor
  · have h_inv : ∀ s', ReachesOf evalRefTailOut vtaProg initZeroState s' → s'.rvvTail = 0#64 := by
      intro s' h
      induction h with
      | refl => rfl
      | @tail s₁ s₂ _ hst ih =>
          obtain ⟨c', hc'⟩ := hst
          unfold evalRefTailOut at hc'
          cases hpc : s₁.pc with
          | zero =>
              simp [vtaProg, hpc, evalRefNarrowOp] at hc'
              rw [← hc']; exact ih
          | succ n =>
              simp [vtaProg, hpc] at hc'
    refine ⟨?_, ?_⟩
    · intro k ⟨s, _, ⟨c, hc⟩⟩
      unfold evalRefTailOut at hc
      cases hpc : s.pc <;> simp [vtaProg, hpc, evalRefNarrowOp] at hc
    · intro out ⟨s, hr, ⟨c, hc⟩⟩
      have htail := h_inv s hr
      unfold evalRefTailOut at hc
      cases hpc : s.pc with
      | zero => simp [vtaProg, hpc, evalRefNarrowOp] at hc
      | succ n =>
          simp [vtaProg, hpc] at hc
          rw [← hc, htail]
  · intro ⟨_, hpost⟩
    have h_bad := hpost 0xFFFFFFFFFFFFFFFF#64 symmetric_vta_iff_false.1
    exact absurd h_bad (by decide)

/-- Key Theorem 6 (Poison-Fault vs. Demonic-Bit-Choice for x86 Undefined Flags):
    If `I_anneal` marks undefined `CF` after `BSF` as poison (`none`) and faults
    (`.fault .undefined`) when a subsequent `JC` reads it, while `I_ref` draws a
    nondeterministic bit `some c.undefBit1`, then:
    - `WellFormed_poison → WellFormed_ref` STILL HOLDS (sound!),
    - YET bidirectional `FaultEquivalence` (`PoisonFault ↔ RefFault`) FAILS! -/
inductive FlagProgOp | bsf | readCF
  deriving DecidableEq

def evalPoisonStep (prog : Nat → Option FlagProgOp) (_c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match prog s.pc with
  | none => .done s.regA
  | some .bsf => .step { s with pc := s.pc + 1, flagCF := none }
  | some .readCF =>
      match s.flagCF with
      | none => .fault .undefined
      | some b => .step { s with pc := s.pc + 1, regA := if b then 1#64 else 0#64 }

def evalBitChoiceRefStep (prog : Nat → Option FlagProgOp) (c : IsaChoice) (s : IsaState) : IsaStepResult :=
  match prog s.pc with
  | none => .done s.regA
  | some .bsf => .step { s with pc := s.pc + 1, flagCF := some c.undefBit1 }
  | some .readCF =>
      match s.flagCF with
      | none => .fault .undefined
      | some b => .step { s with pc := s.pc + 1, regA := if b then 1#64 else 0#64 }

def bsfThenReadCF : Nat → Option FlagProgOp
  | 0 => some .bsf
  | 1 => some .readCF
  | _ => none

theorem poison_breaks_reverse_fault_equiv :
    (∃ s, ReachesOf (fun _ => evalPoisonStep bsfThenReadCF) (fun _ => none) initZeroState s ∧
          StepOf (fun _ => evalPoisonStep bsfThenReadCF) (fun _ => none) s (.fault .undefined)) ∧
    (∀ s, ReachesOf (fun _ => evalBitChoiceRefStep bsfThenReadCF) (fun _ => none) initZeroState s →
          ¬ StepOf (fun _ => evalBitChoiceRefStep bsfThenReadCF) (fun _ => none) s (.fault .undefined)) := by
  let c0 : IsaChoice :=
    { undefBit1 := false, undefBit2 := false, undefWord := 0#64,
      vtaAllOnes := false, scSpurious := false, nanPayload := 0#51 }
  constructor
  · let s1 : IsaState := { initZeroState with pc := 1, flagCF := none }
    refine ⟨s1, .tail (.refl _) ⟨c0, by rfl⟩, ⟨c0, by rfl⟩⟩
  · have h_some : ∀ s,
        ReachesOf (fun _ => evalBitChoiceRefStep bsfThenReadCF) (fun _ => none) initZeroState s →
        s.flagCF.isSome = true := by
      intro s hr
      induction hr with
      | refl => rfl
      | @tail s₁ s₂ _ hst ih =>
          obtain ⟨c, hc⟩ := hst
          cases hpc : s₁.pc with
          | zero =>
              simp [evalBitChoiceRefStep, bsfThenReadCF, hpc] at hc
              rw [← hc]; rfl
          | succ n =>
              cases n with
              | zero =>
                  cases hcf : s₁.flagCF with
                  | none => simp [hcf] at ih
                  | some b =>
                      simp [evalBitChoiceRefStep, bsfThenReadCF, hpc, hcf] at hc
                      rw [← hc]; simp
              | succ m =>
                  simp [evalBitChoiceRefStep, bsfThenReadCF, hpc] at hc
    intro s hr ⟨c, hc⟩
    have hs := h_some s hr
    cases hpc : s.pc with
    | zero => simp [evalBitChoiceRefStep, bsfThenReadCF, hpc] at hc
    | succ n =>
        cases n with
        | zero =>
            cases hcf : s.flagCF with
            | none => simp [hcf] at hs
            | some b => simp [evalBitChoiceRefStep, bsfThenReadCF, hpc, hcf] at hc
        | succ m => simp [evalBitChoiceRefStep, bsfThenReadCF, hpc] at hc

end X86DecodingAndPass2Probe

#print axioms X86DecodingAndPass2Probe.canonical_encoder_misses_alternate_encodings
#print axioms X86DecodingAndPass2Probe.encodeWithHint_covers_multiplicity
#print axioms X86DecodingAndPass2Probe.encodeWithHint_sound_wrt_decodeDirect
#print axioms X86DecodingAndPass2Probe.encodeWithHint_unambiguous
#print axioms X86DecodingAndPass2Probe.buggy_witness_checker_ambiguous_on_41_90
#print axioms X86DecodingAndPass2Probe.pass2_isa_correspondence_and_post_transfer
#print axioms X86DecodingAndPass2Probe.symmetric_vta_iff_false
#print axioms X86DecodingAndPass2Probe.narrow_anneal_proves_false_hardware_property
#print axioms X86DecodingAndPass2Probe.poison_breaks_reverse_fault_equiv
