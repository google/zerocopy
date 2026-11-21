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
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Lemmas
import Init.Data.List.Basic
import Init.Omega
import ByteX86Gcc
import RustFfiSpecs

/-!
# `UntrustedCObjHints`

Untrusted (`0` TCB LOC) certificate checker and CFG/SIMD/pointer-bump proof
combinators for compiled C `.o` $\equiv$ safe-Rust equivalence (`0` `sorry`,
`0` `isPartial` via `@Nat.rec`, `0` axioms):

1. **`Pass1GmpLrat` (`checkLratPass1Clean`):** Peano-free 8-way `OctTrie` GMP
   bitset LRAT UNSAT checker (`0` `._unsafe_rec` constants) verifying bundled
   `CaDiCaL 2.1.2` (`--lrat --no-elim --binary=false`) loop-step and epilogue
   certificates via `by rfl`.
2. **Reflected Straight-Line Basic-Block Lifting (`decodeSeqAt` / `runFrom`):**
   Replaces `m` steps of `ByteX86Gcc.runX64` on a concrete ELF64 `.o`
   `X64ObjImage` with `execInstrSeq` in a single rewrite (`by rfl` concrete
   decode, zero symbolic byte re-decoding).
3. **Shrink-Wrapped `sp_delta(pc)` `PrivateStackSep`, Counterless Pointer-Bump
   Schedules, Barrett `65521`, Non-`restrict` Overlap Discharge, & SIMD Tiers:**
   Reusable lemmas for `32B` AVX2, `16B` Legacy/VEX SSE2, `8B` `mov bh, bl` +
   `vpshuflw`, and `1B` scalar loops/epilogues.
-/

namespace UntrustedCObjHints

open ByteX86Gcc
open RustFfiSpecs

/-! ## Section 1: `@Nat.rec` GMP Bitset `OctTrie` LRAT Checker (`0` `._unsafe_rec`) -/

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

inductive OctTrie (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 c4 c5 c6 c7 : OctTrie α)

def octGet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) : Option α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur i =>
      match cur with
      | .empty => none
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => v
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c0 nxt | false => ih c1 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c2 nxt | false => ih c3 nxt
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c4 nxt | false => ih c5 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c6 nxt | false => ih c7 nxt)
    fuel t idx

def octSet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) (valOpt : Option α) : OctTrie α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α → OctTrie α)
    (fun cur _ _ => cur)
    (fun _ ih cur i v =>
      match cur with
      | .empty =>
        match Nat.beq i 0 with
        | true => .node v .empty .empty .empty .empty .empty .empty .empty .empty
        | false =>
          let nxt := Nat.shiftRight i 3
          match ih .empty nxt v with
          | .empty => .empty
          | .node sv s0 s1 s2 s3 s4 s5 s6 s7 =>
            let sn := OctTrie.node sv s0 s1 s2 s3 s4 s5 s6 s7
            match Nat.beq (Nat.land i 4) 0 with
            | true =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none sn .empty .empty .empty .empty .empty .empty .empty
                | false => .node none .empty sn .empty .empty .empty .empty .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty sn .empty .empty .empty .empty .empty
                | false => .node none .empty .empty .empty sn .empty .empty .empty .empty
            | false =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty sn .empty .empty .empty
                | false => .node none .empty .empty .empty .empty .empty sn .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty .empty .empty sn .empty
                | false => .node none .empty .empty .empty .empty .empty .empty .empty sn
      | .node v0 c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => .node v c0 c1 c2 c3 c4 c5 c6 c7
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c0 nxt v with | .empty => .node v0 .empty c1 c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c1 c2 c3 c4 c5 c6 c7
              | false => match ih c1 nxt v with | .empty => .node v0 c0 .empty c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c2 c3 c4 c5 c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c2 nxt v with | .empty => .node v0 c0 c1 .empty c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c3 c4 c5 c6 c7
              | false => match ih c3 nxt v with | .empty => .node v0 c0 c1 c2 .empty c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c4 c5 c6 c7
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c4 nxt v with | .empty => .node v0 c0 c1 c2 c3 .empty c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c5 c6 c7
              | false => match ih c5 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 .empty c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c6 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 .empty c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c7
              | false => match ih c7 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 c6 .empty | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 c6 (.node sv s0 s1 s2 s3 s4 s5 s6 s7))
    fuel t idx valOpt

inductive MaskStream where | mk (mask : Nat) (rest : Nat)
inductive PropStream where | mk (ok : Bool) (rest : Nat)
inductive DelStream  where | mk (db : OctTrie Nat) (rest : Nat)
inductive RunState   where | running (db : OctTrie Nat) | proved | failed

def readMaskU16 (cnt s0 : Nat) : MaskStream :=
  @Nat.rec (fun _ => Nat → Nat → MaskStream)
    (fun s acc => .mk acc s)
    (fun _ ih s acc =>
      let lit := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      let acc' := Nat.lor acc (Nat.shiftLeft 1 lit)
      match Nat.beq acc' 0, Nat.beq s' 0 with
      | true, true   => ih 0 0
      | true, false  => ih s' 0
      | false, true  => ih 0 acc'
      | false, false => ih s' acc')
    cnt s0 0

def propHintsU16 (oDepth : Nat) (clauses : OctTrie Nat) (cnt falsified0 s0 : Nat) : PropStream :=
  @Nat.rec (fun _ => Nat → Nat → PropStream)
    (fun _ s => .mk false s)
    (fun k ih falsified s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octGet oDepth clauses cid with
      | none => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
      | some mask =>
        let rem := Nat.xor mask (Nat.land mask falsified)
        match Nat.beq rem 0 with
        | true => .mk true (Nat.shiftRight s' (Nat.mul 16 k))
        | false =>
          match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
          | false => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
          | true =>
            let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
              | true  => Nat.shiftLeft rem 1
              | false => Nat.shiftRight rem 1
            let falsified' := Nat.lor falsified negRaw
            match Nat.beq falsified' 0 with
            | true  => ih 0 s'
            | false => ih falsified' s')
    cnt falsified0 s0

def delIdsU16 (oDepth cnt : Nat) (db0 : OctTrie Nat) (s0 : Nat) : DelStream :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → DelStream)
    (fun db s => .mk db s)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octSet oDepth db cid none with
      | .empty => ih .empty s'
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s')
    cnt db0 s0

def initChunkU16 (oDepth fuel : Nat) (db0 : OctTrie Nat) (s0 : Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → OctTrie Nat)
    (fun db _ => db)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s1  := Nat.shiftRight s 16
      match Nat.beq cid 0 with
      | true => db
      | false =>
        let cLen := Nat.land s1 0xffff
        let s2   := Nat.shiftRight s1 16
        match readMaskU16 cLen s2 with
        | .mk m s3 =>
          match octSet oDepth db cid (some m) with
          | .empty => ih .empty s3
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s3)
    fuel db0 s0

def runChunkU16 (oDepth fuel : Nat) (st0 : RunState) (s0 : Nat) : RunState :=
  @Nat.rec (fun _ => RunState → Nat → RunState)
    (fun st _ => st)
    (fun _ ih st s =>
      match st with
      | .proved => .proved
      | .failed => .failed
      | .running db =>
        let tag := Nat.land s 0xffff
        let s1  := Nat.shiftRight s 16
        match Nat.beq tag 0 with
        | true => .running db
        | false =>
          match Nat.beq tag 1 with
          | true =>
            let cid  := Nat.land s1 0xffff
            let cLen := Nat.land (Nat.shiftRight s1 16) 0xffff
            let hLen := Nat.land (Nat.shiftRight s1 32) 0xffff
            let s4   := Nat.shiftRight s1 48
            match readMaskU16 cLen s4 with
            | .mk targetMask s5 =>
              match propHintsU16 oDepth db hLen targetMask s5 with
              | .mk false _ => .failed
              | .mk true s6 =>
                match Nat.beq targetMask 0 with
                | true => .proved
                | false =>
                  match octSet oDepth db cid (some targetMask) with
                  | .empty => ih (.running .empty) s6
                  | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) s6
          | false =>
            match Nat.beq tag 2 with
            | true =>
              let dLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match delIdsU16 oDepth dLen db s2 with
              | .mk db' s3 => ih (.running db') s3
            | false =>
              let hLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match propHintsU16 oDepth db hLen 0 s2 with
              | .mk true _  => .proved
              | .mk false _ => .failed)
    fuel st0 s0

def initStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (db0 : OctTrie Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => StepTree Nat → OctTrie Nat → OctTrie Nat)
    (fun _ db => db)
    (fun _ ih t db =>
      match t with
      | .empty => db
      | .leaf s => initChunkU16 oDepth 40 db s
      | .branch l r =>
        match ih l db with
        | .empty => ih r .empty
        | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.node v c0 c1 c2 c3 c4 c5 c6 c7))
    treeFuel t0 db0

def runStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (st0 : RunState) : RunState :=
  @Nat.rec (fun _ => StepTree Nat → RunState → RunState)
    (fun _ _ => .failed)
    (fun _ ih t st =>
      match t with
      | .empty => st
      | .leaf s => runChunkU16 oDepth 40 st s
      | .branch l r =>
        match ih l st with
        | .proved => .proved
        | .failed => .failed
        | .running db =>
          match db with
          | .empty => ih r (.running .empty)
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)))
    treeFuel t0 st0

def checkLratPass1Clean (oDepth : Nat) (initTree stepsTree : StepTree Nat) : Bool :=
  match initStreamTree oDepth 18 initTree .empty with
  | .empty => false
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
    match runStreamTree oDepth 18 stepsTree (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) with
    | .proved => true
    | _ => false

/-- Synthesized `.o` equivalence certificate descriptor combining:
    - Inferred pointer-bump unroll stride `unrollStride`
    - Maximum stack-frame reservation `maxNegSpDelta` (`0` or `16`)
    - Dead-flag-collapse branch vs. killed flag site counts
    - `Pass1GmpLrat` UNSAT certificate from bundled `CaDiCaL 2.1.2` -/
structure CObjEquivCert where
  unrollStride     : Nat
  maxNegSpDelta    : Nat
  liveFlagBranches : Nat
  killedFlagSites  : Nat
  oDepth           : Nat
  stepInitTree     : StepTree Nat
  stepProofTree    : StepTree Nat

def checkCObjEquivCert (c : CObjEquivCert) (expStride expStack : Nat) : Bool :=
  Nat.beq c.unrollStride expStride &&
  Nat.beq c.maxNegSpDelta expStack &&
  Nat.ble 1 c.liveFlagBranches &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

/-! ## Section 2: `runFrom` Splitting & Reflected Basic-Block Lifting (`decodeSeqAt`) -/

def runFrom (cmap : CodeMap) (steps idx0 : Nat) (nd : Nat → UndefChoice) (s0 : X64State) : X64State :=
  Nat.rec (motive := fun _ => Nat → X64State → X64State)
    (fun _ s => s)
    (fun _ ih idx s => ih (idx + 1) (stepX64 cmap (nd idx) s))
    steps idx0 s0

theorem runX64_eq_runFrom (img : X64ObjImage) (steps : Nat) (nd : Nat → UndefChoice) (s0 : X64State) :
    runX64 img steps nd s0 = runFrom (objCodeMap img) steps 0 nd s0 := rfl

@[simp] theorem runFrom_zero (cmap : CodeMap) (idx : Nat) (nd : Nat → UndefChoice) (s : X64State) :
    runFrom cmap 0 idx nd s = s := rfl

theorem runFrom_succ (cmap : CodeMap) (k idx : Nat) (nd : Nat → UndefChoice) (s : X64State) :
    runFrom cmap (k + 1) idx nd s = runFrom cmap k (idx + 1) nd (stepX64 cmap (nd idx) s) := rfl

theorem runFrom_add (cmap : CodeMap) (m n : Nat) :
    ∀ (idx : Nat) (nd : Nat → UndefChoice) (s : X64State),
      runFrom cmap (m + n) idx nd s = runFrom cmap n (idx + m) nd (runFrom cmap m idx nd s) := by
  induction m with
  | zero =>
    intro idx nd s
    simp [Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    intro idx nd s
    rw [show k + 1 + n = (k + n) + 1 by omega]
    rw [runFrom_succ, runFrom_succ, ih (idx + 1) nd (stepX64 cmap (nd idx) s)]
    rw [show idx + 1 + k = idx + (k + 1) by omega]

theorem step_at_concrete {cmap : CodeMap} {rip : BitVec 64} {ins : X64Instr} {len : Nat}
    (hdec : decodeX64 (fetchWindow16 cmap rip) = .ok ins len)
    (ch : UndefChoice) (s : X64State)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = rip) :
    stepX64 cmap ch s = execByteInstr ins (rip + BitVec.ofNat 64 len) ch s := by
  unfold stepX64
  rw [ifFalse (by simp [hrun, hnf]), hrip, hdec]

def isNonBranchingNormal : X64Instr → Bool
  | .ret64 | .ud2 | .cli | .jmpRel _ | .jccRel _ _ => false
  | _ => true

theorem writeByteRm8_preserves_ctrl (s : X64State) (nextRip : BitVec 64) (dst : X64Rm8) (v : BitVec 8) :
    (writeByteRm8 s nextRip dst v).halted = s.halted ∧
    (writeByteRm8 s nextRip dst v).fault = s.fault ∧
    (writeByteRm8 s nextRip dst v).rip = s.rip := by
  cases dst <;> exact ⟨rfl, rfl, rfl⟩

theorem writeByteRm_preserves_ctrl (sz : OpSize) (s : X64State) (nextRip : BitVec 64)
    (dst : X64Rm) (v : BitVec 64) :
    (writeByteRm sz s nextRip dst v).halted = s.halted ∧
    (writeByteRm sz s nextRip dst v).fault = s.fault ∧
    (writeByteRm sz s nextRip dst v).rip = s.rip := by
  cases dst with
  | reg _ => exact ⟨rfl, rfl, rfl⟩
  | mem _ => cases sz <;> exact ⟨rfl, rfl, rfl⟩

theorem execByteInstr_normal_props {ins : X64Instr} (hnorm : isNonBranchingNormal ins = true)
    (nextRip : BitVec 64) (ch : UndefChoice) (s : X64State) :
    (execByteInstr ins nextRip ch s).halted = s.halted ∧
    (execByteInstr ins nextRip ch s).fault = s.fault ∧
    (execByteInstr ins nextRip ch s).rip = nextRip := by
  have hrm8 : ∀ (st : X64State) d v,
      st.halted = s.halted → st.fault = s.fault → st.rip = nextRip →
      (writeByteRm8 st nextRip d v).halted = s.halted ∧
      (writeByteRm8 st nextRip d v).fault = s.fault ∧
      (writeByteRm8 st nextRip d v).rip = nextRip := by
    intro st d v h1 h2 h3; cases d <;> exact ⟨h1, h2, h3⟩
  have hrm : ∀ sz (st : X64State) d v,
      st.halted = s.halted → st.fault = s.fault → st.rip = nextRip →
      (writeByteRm sz st nextRip d v).halted = s.halted ∧
      (writeByteRm sz st nextRip d v).fault = s.fault ∧
      (writeByteRm sz st nextRip d v).rip = nextRip := by
    intro sz st d v h1 h2 h3; cases d with
    | reg _ => exact ⟨h1, h2, h3⟩
    | mem _ => cases sz <;> exact ⟨h1, h2, h3⟩
  cases ins with
  | ret64 | ud2 | cli | jmpRel _ | jccRel _ _ => simp [isNonBranchingNormal] at hnorm
  | mov8Store d _ | mov8Imm d _ | setcc8 _ d =>
    exact hrm8 _ _ _ rfl rfl rfl
  | alu8RmReg op d _ | alu8Imm op d _ =>
    dsimp only [execByteInstr]
    by_cases hc : (op == .cmp || op == .test) = true
    · rw [ifTrue hc]; exact ⟨rfl, rfl, rfl⟩
    · rw [ifFalse hc]; rcases hrm8 { s with rip := nextRip } d _ rfl rfl rfl with ⟨a, b, c⟩; exact ⟨a, b, c⟩
  | movStore sz d _ | movRmImm32 sz d _ | unaryRm sz _ d | shiftImm sz _ d _ =>
    dsimp only [execByteInstr]
    rcases hrm sz { s with rip := nextRip } d _ rfl rfl rfl with ⟨a, b, c⟩; exact ⟨a, b, c⟩
  | xchg sz _ d =>
    dsimp only [execByteInstr]
    rcases hrm sz { s with rip := nextRip } d _ rfl rfl rfl with ⟨a, b, c⟩; exact ⟨a, b, c⟩
  | aluRmReg sz op d _ | aluImm sz op d _ =>
    dsimp only [execByteInstr]
    by_cases hc : (op == .cmp || op == .test) = true
    · rw [ifTrue hc]; exact ⟨rfl, rfl, rfl⟩
    · rw [ifFalse hc]; rcases hrm sz { s with rip := nextRip } d _ rfl rfl rfl with ⟨a, b, c⟩; exact ⟨a, b, c⟩
  | bsf _ _ _ =>
    dsimp only [execByteInstr]; split <;> exact ⟨rfl, rfl, rfl⟩
  | simdMovLoad m _ _ | simdExtend m _ _ _ | simdBroadcastB m _ _ | simdBroadcastQ m _ _ =>
    cases m <;> exact ⟨rfl, rfl, rfl⟩
  | simdMovStore m dst _ =>
    cases dst <;> cases m <;> exact ⟨rfl, rfl, rfl⟩
  | simdMovqStore _ dst _ | simdExtract128 dst _ _ =>
    dsimp only [execByteInstr]; cases dst <;> exact ⟨rfl, rfl, rfl⟩
  | simdMovXToGpr _ is64 dst _ =>
    exact hrm _ _ dst _ rfl rfl rfl
  | _ =>
    exact ⟨rfl, rfl, rfl⟩

def execInstrSeq (fuel : Nat) (seq : List (X64Instr × BitVec 64)) (idx0 : Nat)
    (nd : Nat → UndefChoice) (s0 : X64State) : X64State :=
  Nat.rec (motive := fun _ => List (X64Instr × BitVec 64) → Nat → X64State → X64State)
    (fun _ _ s => s)
    (fun _ ih xs idx s =>
      match xs with
      | [] => s
      | (ins, nextRip) :: rest =>
        ih rest (idx + 1) (execByteInstr ins nextRip (nd idx) s))
    fuel seq idx0 s0

@[simp] theorem execInstrSeq_zero (seq : List (X64Instr × BitVec 64)) (idx : Nat)
    (nd : Nat → UndefChoice) (s : X64State) :
    execInstrSeq 0 seq idx nd s = s := rfl

theorem execInstrSeq_succ_cons (k : Nat) (ins : X64Instr) (nextRip : BitVec 64)
    (rest : List (X64Instr × BitVec 64)) (idx : Nat) (nd : Nat → UndefChoice) (s : X64State) :
    execInstrSeq (k + 1) ((ins, nextRip) :: rest) idx nd s =
      execInstrSeq k rest (idx + 1) nd (execByteInstr ins nextRip (nd idx) s) := rfl

def decodeSeqAt (cmap : CodeMap) (count : Nat) (rip0 : BitVec 64) :
    Option (List (X64Instr × BitVec 64)) :=
  Nat.rec (motive := fun _ => BitVec 64 → Option (List (X64Instr × BitVec 64)))
    (fun _ => some [])
    (fun _ ih rip =>
      match decodeX64 (fetchWindow16 cmap rip) with
      | .fault _ => none
      | .ok ins len =>
        if isNonBranchingNormal ins then
          let nextRip := rip + BitVec.ofNat 64 len
          match ih nextRip with
          | none => none
          | some rest => some ((ins, nextRip) :: rest)
        else none)
    count rip0

theorem decodeSeqAt_zero (cmap : CodeMap) (rip : BitVec 64) :
    decodeSeqAt cmap 0 rip = some [] := rfl

theorem decodeSeqAt_succ (cmap : CodeMap) (k : Nat) (rip : BitVec 64) :
    decodeSeqAt cmap (k + 1) rip =
      match decodeX64 (fetchWindow16 cmap rip) with
      | .fault _ => none
      | .ok ins len =>
        if isNonBranchingNormal ins then
          let nextRip := rip + BitVec.ofNat 64 len
          match decodeSeqAt cmap k nextRip with
          | none => none
          | some rest => some ((ins, nextRip) :: rest)
        else none := rfl

theorem decode_at_win {cmap : CodeMap} {rip : BitVec 64} {w : List (BitVec 8)}
    {ins : X64Instr} {len : Nat}
    (hw : fetchWindow16 cmap rip = w)
    (hd : decodeX64 w = .ok ins len) :
    decodeX64 (fetchWindow16 cmap rip) = .ok ins len := by
  rw [hw]; exact hd

theorem decode_at_win_eq {cmap : CodeMap} {rip : BitVec 64} {w : List (BitVec 8)}
    {ins1 ins2 : X64Instr} {len : Nat}
    (hw : fetchWindow16 cmap rip = w)
    (hd : decodeX64 w = .ok ins1 len)
    (heq : ins1 = ins2) :
    decodeX64 (fetchWindow16 cmap rip) = .ok ins2 len := by
  rw [hw, ← heq]; exact hd

theorem decodeSeqAt_step {cmap : CodeMap} {k : Nat} {rip nextRip : BitVec 64}
    {w : List (BitVec 8)} {ins : X64Instr} {len : Nat}
    {rest : List (X64Instr × BitVec 64)}
    (hw : fetchWindow16 cmap rip = w)
    (hd : decodeX64 w = .ok ins len)
    (hn : isNonBranchingNormal ins = true)
    (hrip : rip + BitVec.ofNat 64 len = nextRip)
    (hrest : decodeSeqAt cmap k nextRip = some rest) :
    decodeSeqAt cmap (k + 1) rip = some ((ins, nextRip) :: rest) := by
  rw [decodeSeqAt_succ, hw, hd]
  dsimp only
  rw [ifTrue hn, hrip, hrest]

theorem decodeSeqAt_step_eq {cmap : CodeMap} {k : Nat} {rip nextRip : BitVec 64}
    {w : List (BitVec 8)} {ins1 ins2 : X64Instr} {len : Nat}
    {rest : List (X64Instr × BitVec 64)}
    (hw : fetchWindow16 cmap rip = w)
    (hd : decodeX64 w = .ok ins1 len)
    (heq : ins1 = ins2)
    (hn : isNonBranchingNormal ins2 = true)
    (hrip : rip + BitVec.ofNat 64 len = nextRip)
    (hrest : decodeSeqAt cmap k nextRip = some rest) :
    decodeSeqAt cmap (k + 1) rip = some ((ins2, nextRip) :: rest) := by
  subst heq
  exact decodeSeqAt_step hw hd hn hrip hrest

/-- **Reflected Straight-Line Basic-Block Lifting (`runFrom_of_decodeSeqAt`):**
    Once `decodeSeqAt cmap count rip0 = some seq` is checked on the concrete `.o`
    bytes (`by rfl`), `count` steps of `runFrom` collapse in one step to
    `execInstrSeq seq` without re-decoding bytes across symbolic states. -/
theorem runFrom_of_decodeSeqAt {cmap : CodeMap} {count : Nat} :
    ∀ {rip0 : BitVec 64} {seq : List (X64Instr × BitVec 64)},
      decodeSeqAt cmap count rip0 = some seq →
      ∀ (idx : Nat) (nd : Nat → UndefChoice) (s : X64State),
      s.halted = false → s.fault = false → s.rip = rip0 →
      runFrom cmap count idx nd s = execInstrSeq count seq idx nd s ∧
      (execInstrSeq count seq idx nd s).halted = false ∧
      (execInstrSeq count seq idx nd s).fault = false := by
  induction count with
  | zero =>
    intro rip0 seq hdec idx nd s hrun hnf _
    dsimp [decodeSeqAt] at hdec
    injection hdec with hseq
    subst hseq
    exact ⟨rfl, hrun, hnf⟩
  | succ k ih =>
    intro rip0 seq hdec idx nd s hrun hnf hrip
    rw [decodeSeqAt_succ] at hdec
    cases hd1 : decodeX64 (fetchWindow16 cmap rip0) with
    | fault fk => rw [hd1] at hdec; nomatch hdec
    | ok ins len =>
      rw [hd1] at hdec
      dsimp only at hdec
      by_cases hnorm : isNonBranchingNormal ins = true
      · rw [ifTrue hnorm] at hdec
        cases hdRest : decodeSeqAt cmap k (rip0 + BitVec.ofNat 64 len) with
        | none => rw [hdRest] at hdec; nomatch hdec
        | some rest =>
          rw [hdRest] at hdec
          injection hdec with hseq
          subst hseq
          rw [runFrom_succ, step_at_concrete hd1 (nd idx) s hrun hnf hrip, execInstrSeq_succ_cons]
          rcases execByteInstr_normal_props hnorm (rip0 + BitVec.ofNat 64 len) (nd idx) s with ⟨hrun1, hnf1, hrip1⟩
          rw [hrun] at hrun1
          rw [hnf] at hnf1
          exact ih hdRest (idx + 1) nd _ hrun1 hnf1 hrip1
      · rw [ifFalse hnorm] at hdec; nomatch hdec

/-! ## Section 3: Pointer-Bump Schedules, Stack Framing, Barrett `65521`, & SIMD Lemmas -/

theorem bv64_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem bv64_add_ofNat_assoc (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, bv64_ofNat_add]

theorem ptr_offset_toNat {ptr : BitVec 64} {k len : Nat}
    (hnw : NoWrapSlice ptr len) (hk : k ≤ len) :
    (ptr + BitVec.ofNat 64 k).toNat = ptr.toNat + k := by
  unfold NoWrapSlice at hnw
  have hk64 : k < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

theorem ptr_offset_ne {ptr : BitVec 64} {i j len : Nat}
    (hnw : NoWrapSlice ptr len) (hi : i ≤ len) (hj : j ≤ len) (hne : i ≠ j) :
    ptr + BitVec.ofNat 64 i ≠ ptr + BitVec.ofNat 64 j := by
  intro heq
  have h1 := ptr_offset_toNat hnw hi
  have h2 := ptr_offset_toNat hnw hj
  rw [heq] at h1
  omega

theorem cmp_sub_zero_false_of_ne {a b : BitVec 64} (hne : a ≠ b) :
    (a - b == 0#64) = false := by
  cases h : a - b == 0#64
  · rfl
  · exfalso
    have heq : a - b = 0#64 := eq_of_beq h
    have hab : a = b := by
      have h1 : (a - b) + b = 0#64 + b := congrArg (· + b) heq
      simpa [BitVec.sub_add_cancel] using h1
    exact hne hab

@[simp] theorem cmp_sub_self_zero (a : BitVec 64) : (a - a == 0#64) = true := by
  simp [BitVec.sub_self]

theorem test64_self_zero_eq (x : BitVec 64) :
    (x &&& x == 0#64) = decide (x.toNat = 0) := by
  rw [BitVec.and_self]
  cases h : x == 0#64
  · have hne : x ≠ 0#64 := by intro hx; subst hx; simp at h
    have htn : x.toNat ≠ 0 := by
      intro hz; apply hne; apply BitVec.eq_of_toNat_eq; simp [hz]
    simp [htn]
  · have heq : x = 0#64 := eq_of_beq h
    subst heq; rfl

/-- Exact 8-byte `writeMem64` / `readMem64` roundtrip for arbitrary 64-bit pointer `p`
    (needed for `push rbp`, `push rbx`, `mov rbx, [rbp-8]`, and `leave`). -/
theorem bv64_add_small_ne (p : BitVec 64) {i j : Nat} (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := by
  intro heq
  have hsub : (p + BitVec.ofNat 64 i) - p = (p + BitVec.ofNat 64 j) - p := congrArg (· - p) heq
  have hcancel : ∀ x : BitVec 64, (p + x) - p = x := by
    intro x
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_add]
    omega
  rw [hcancel, hcancel] at hsub
  have hti : (BitVec.ofNat 64 i).toNat = (BitVec.ofNat 64 j).toNat := congrArg BitVec.toNat hsub
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at hti
  exact hne hti

theorem append_extractLsb_split {a b : Nat} {w : Nat} (hw : a + b ≤ w) (s : Nat)
    (hs : s + (a + b) ≤ w) (v : BitVec w) :
    BitVec.extractLsb' (s + b) a v ++ BitVec.extractLsb' s b v = BitVec.extractLsb' s (a + b) v := by
  have _ := hw; have _ := hs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases hlt : i < b
  · simp [hlt, hi]
  · have hlt2 : i - b < a := by omega
    have hsum : s + b + (i - b) = s + i := by omega
    simp [hlt, hlt2, hi, hsum]

theorem pack8Bytes_byteOf64 (v : BitVec 64) :
    pack8Bytes (byteOf64 v 0) (byteOf64 v 1) (byteOf64 v 2) (byteOf64 v 3)
               (byteOf64 v 4) (byteOf64 v 5) (byteOf64 v 6) (byteOf64 v 7) = v := by
  unfold pack8Bytes byteOf64
  change BitVec.extractLsb' 56 8 v ++ (BitVec.extractLsb' 48 8 v ++ (BitVec.extractLsb' 40 8 v ++
    (BitVec.extractLsb' 32 8 v ++ (BitVec.extractLsb' 24 8 v ++ (BitVec.extractLsb' 16 8 v ++
    (BitVec.extractLsb' (0 + 8) 8 v ++ BitVec.extractLsb' 0 8 v)))))) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' 56 8 v ++ (BitVec.extractLsb' 48 8 v ++ (BitVec.extractLsb' 40 8 v ++
    (BitVec.extractLsb' 32 8 v ++ (BitVec.extractLsb' 24 8 v ++
    (BitVec.extractLsb' (0 + 16) 8 v ++ BitVec.extractLsb' 0 16 v))))) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' 56 8 v ++ (BitVec.extractLsb' 48 8 v ++ (BitVec.extractLsb' 40 8 v ++
    (BitVec.extractLsb' 32 8 v ++
    (BitVec.extractLsb' (0 + 24) 8 v ++ BitVec.extractLsb' 0 24 v)))) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' 56 8 v ++ (BitVec.extractLsb' 48 8 v ++ (BitVec.extractLsb' 40 8 v ++
    (BitVec.extractLsb' (0 + 32) 8 v ++ BitVec.extractLsb' 0 32 v))) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' 56 8 v ++ (BitVec.extractLsb' 48 8 v ++
    (BitVec.extractLsb' (0 + 40) 8 v ++ BitVec.extractLsb' 0 40 v)) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' 56 8 v ++
    (BitVec.extractLsb' (0 + 48) 8 v ++ BitVec.extractLsb' 0 48 v) = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v]
  change BitVec.extractLsb' (0 + 56) 8 v ++ BitVec.extractLsb' 0 56 v = v
  rw [append_extractLsb_split (by decide) 0 (by decide) v, extractLsb_self]

theorem pack8Bytes_eq_of_bytes {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8} {v : BitVec 64}
    (h0 : b0 = byteOf64 v 0) (h1 : b1 = byteOf64 v 1)
    (h2 : b2 = byteOf64 v 2) (h3 : b3 = byteOf64 v 3)
    (h4 : b4 = byteOf64 v 4) (h5 : b5 = byteOf64 v 5)
    (h6 : b6 = byteOf64 v 6) (h7 : b7 = byteOf64 v 7) :
    pack8Bytes b0 b1 b2 b3 b4 b5 b6 b7 = v := by
  subst h0 h1 h2 h3 h4 h5 h6 h7
  exact pack8Bytes_byteOf64 v

theorem writeMem64_at_offset (m : ByteMem) (p v : BitVec 64) (j : Nat) (hj : j < 8) :
    writeMem64 m p v (p + BitVec.ofNat 64 j) = byteOf64 v j := by
  unfold writeMem64
  have ne : ∀ a b : Nat, a < 8 → b < 8 → a ≠ b → p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b :=
    fun a b ha hb hab => bv64_add_small_ne p (by omega) (by omega) hab
  match j with
  | 0 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 0) = _
    rw [memUpd8_ne _ (ne 0 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 6 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 5 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 4 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 3 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 2 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 0 1 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 1 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 1) = _
    rw [memUpd8_ne _ (ne 1 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 1 6 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 1 5 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 1 4 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 1 3 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 1 2 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 2 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 2) = _
    rw [memUpd8_ne _ (ne 2 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 2 6 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 2 5 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 2 4 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 2 3 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 3 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 3) = _
    rw [memUpd8_ne _ (ne 3 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 3 6 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 3 5 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 3 4 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 4 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 4) = _
    rw [memUpd8_ne _ (ne 4 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 4 6 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 4 5 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 5 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 5) = _
    rw [memUpd8_ne _ (ne 5 7 (by decide) (by decide) (by decide)),
        memUpd8_ne _ (ne 5 6 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 6 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 6) = _
    rw [memUpd8_ne _ (ne 6 7 (by decide) (by decide) (by decide)),
        memUpd8_eq]
  | 7 =>
    change memUpd8 _ (p + BitVec.ofNat 64 7) _ (p + BitVec.ofNat 64 7) = _
    rw [memUpd8_eq]
  | _ + 8 => omega

theorem readMem64_writeMem64_same (m : ByteMem) (p v : BitVec 64) :
    readMem64 (writeMem64 m p v) p = v := by
  unfold readMem64
  rw [writeMem64_at_offset m p v 0 (by decide),
      writeMem64_at_offset m p v 1 (by decide),
      writeMem64_at_offset m p v 2 (by decide),
      writeMem64_at_offset m p v 3 (by decide),
      writeMem64_at_offset m p v 4 (by decide),
      writeMem64_at_offset m p v 5 (by decide),
      writeMem64_at_offset m p v 6 (by decide),
      writeMem64_at_offset m p v 7 (by decide),
      pack8Bytes_byteOf64]

theorem writeMem64_outside (m : ByteMem) (p v addr : BitVec 64)
    (hout : ∀ j : Nat, j < 8 → addr ≠ p + BitVec.ofNat 64 j) :
    writeMem64 m p v addr = m addr := by
  unfold writeMem64
  rw [memUpd8_ne _ (hout 7 (by decide)),
      memUpd8_ne _ (hout 6 (by decide)),
      memUpd8_ne _ (hout 5 (by decide)),
      memUpd8_ne _ (hout 4 (by decide)),
      memUpd8_ne _ (hout 3 (by decide)),
      memUpd8_ne _ (hout 2 (by decide)),
      memUpd8_ne _ (hout 1 (by decide)),
      memUpd8_ne _ (hout 0 (by decide))]

theorem readMem64_congr {m1 m2 : ByteMem} {p : BitVec 64}
    (h : ∀ j : Nat, j < 8 → m1 (p + BitVec.ofNat 64 j) = m2 (p + BitVec.ofNat 64 j)) :
    readMem64 m1 p = readMem64 m2 p := by
  unfold readMem64
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- Shrink-wrapped stack separation (`sp_delta(pc) ∈ {0, -8, -16}`):
    when `16 ≤ rsp0.toNat`, the two 8-byte slots `[rsp0 - 8, rsp0)` and
    `[rsp0 - 16, rsp0 - 8)` are mutually disjoint, lie strictly inside
    `InPrivateStackWindow · rsp0 16`, and never alias any slice satisfying
    `DisjointFromStack ptr len rsp0 16`. -/
theorem stack16_slots_private_and_disjoint {rsp0 : BitVec 64} (hrsp : 16 ≤ rsp0.toNat) :
    (∀ j : Nat, j < 8 → InPrivateStackWindow ((rsp0 - 8#64) + BitVec.ofNat 64 j) rsp0 16) ∧
    (∀ j : Nat, j < 8 → InPrivateStackWindow ((rsp0 - 16#64) + BitVec.ofNat 64 j) rsp0 16) ∧
    (∀ i j : Nat, i < 8 → j < 8 → (rsp0 - 8#64) + BitVec.ofNat 64 i ≠ (rsp0 - 16#64) + BitVec.ofNat 64 j) := by
  have hr8 : (rsp0 - 8#64).toNat = rsp0.toNat - 8 := by
    simp [BitVec.toNat_sub]; omega
  have hr16 : (rsp0 - 16#64).toNat = rsp0.toNat - 16 := by
    simp [BitVec.toNat_sub]; omega
  have hlt64 := rsp0.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    unfold InPrivateStackWindow
    have ht : ((rsp0 - 8#64) + BitVec.ofNat 64 j).toNat = rsp0.toNat - 8 + j := by
      simp [BitVec.toNat_add, hr8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
      omega
    omega
  · intro j hj
    unfold InPrivateStackWindow
    have ht : ((rsp0 - 16#64) + BitVec.ofNat 64 j).toNat = rsp0.toNat - 16 + j := by
      simp [BitVec.toNat_add, hr16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
      omega
    omega
  · intro i j hi hj heq
    have h1 : ((rsp0 - 8#64) + BitVec.ofNat 64 i).toNat = rsp0.toNat - 8 + i := by
      simp [BitVec.toNat_add, hr8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      omega
    have h2 : ((rsp0 - 16#64) + BitVec.ofNat 64 j).toNat = rsp0.toNat - 16 + j := by
      simp [BitVec.toNat_add, hr16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
      omega
    rw [heq] at h1
    omega

theorem slice_addr_not_in_private_stack {ptr rsp0 : BitVec 64} {len stackReserve i : Nat}
    (hnw : NoWrapSlice ptr len)
    (hdisj : DisjointFromStack ptr len rsp0 stackReserve)
    (hi : i < len) :
    ¬ InPrivateStackWindow (ptr + BitVec.ofNat 64 i) rsp0 stackReserve := by
  unfold DisjointFromStack at hdisj
  unfold InPrivateStackWindow
  have ht := ptr_offset_toNat hnw (by omega : i ≤ len)
  omega

theorem bv64_sub_toNat_of_le {a b : BitVec 64} (hle : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  have heq : 2 ^ 64 - b.toNat + a.toNat = (a.toNat - b.toNat) + 1 * 2 ^ 64 := by omega
  rw [heq, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem bv64_sub_toNat_of_lt {a b : BitVec 64} (hlt : a.toNat < b.toNat) :
    (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  exact Nat.mod_eq_of_lt (by omega)

theorem bv32_sub_toNat_of_le {a b : BitVec 32} (hle : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  have heq : 2 ^ 32 - b.toNat + a.toNat = (a.toNat - b.toNat) + 1 * 2 ^ 32 := by omega
  rw [heq, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Adler-32 Magic-Constant Barrett Reduction (`barrett65521_step`):**
    GCC `15.2.0 -O2`/`-O3` replaces `% 65521u` with `imul r64, 0x80078071; shr r64, 47;
    imul r32, q32, 0xfff1; sub s32, r32`. For all `s.toNat ≤ 196560` (covering both
    `a + buf[i] ≤ 65790` and `b + a' ≤ 131055`), this computes exact `s.toNat % 65521`. -/
theorem barrett65521_step (s : BitVec 64) (hs : s.toNat ≤ 196560) :
    let q64 := (s * 0x80078071#64) >>> 47
    let q32 := BitVec.extractLsb' 0 32 q64
    let s32 := BitVec.extractLsb' 0 32 s
    let rem := s32 - q32 * 0xFFF1#32
    rem = BitVec.ofNat 32 (s.toNat % 65521) ∧ rem.toNat < 65521 := by
  dsimp only
  have hmul_bound : s.toNat * 2147975281 < 2 ^ 64 := by
    have hle : s.toNat * 2147975281 ≤ 196560 * 2147975281 := Nat.mul_le_mul_right 2147975281 hs
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hmul_no_wrap : (s * 0x80078071#64).toNat = s.toNat * 2147975281 := by
    rw [BitVec.toNat_mul]
    have hc : (0x80078071#64 : BitVec 64).toNat = 2147975281 := rfl
    rw [hc]
    exact Nat.mod_eq_of_lt hmul_bound
  have hshr : ((s * 0x80078071#64) >>> 47).toNat = (s.toNat * 2147975281) / 140737488355328 := by
    rw [BitVec.toNat_ushiftRight, hmul_no_wrap, Nat.shiftRight_eq_div_pow]
  have hdiv := Nat.div_add_mod s.toNat 65521
  have hmod_lt := Nat.mod_lt s.toNat (by decide : 0 < 65521)
  have hq_le : s.toNat / 65521 ≤ 2 := by
    omega
  have hr_le : s.toNat % 65521 ≤ 65520 := by
    omega
  have hq_eq : (s.toNat * 2147975281) / 140737488355328 = s.toNat / 65521 := by
    let q := s.toNat / 65521
    let r := s.toNat % 65521
    have hexpand : s.toNat * 2147975281 =
        (31073 * q + r * 2147975281) + 140737488355328 * q := by
      have hsr : s.toNat = 65521 * q + r := hdiv.symm
      have hmagic : 65521 * 2147975281 = 31073 + 140737488355328 := rfl
      calc s.toNat * 2147975281
        _ = (65521 * q + r) * 2147975281 := by rw [← hsr]
        _ = (65521 * 2147975281) * q + r * 2147975281 := by
            rw [Nat.add_mul, Nat.mul_right_comm 65521 q 2147975281]
        _ = (31073 + 140737488355328) * q + r * 2147975281 := by rw [hmagic]
        _ = (31073 * q + 140737488355328 * q) + r * 2147975281 := by rw [Nat.add_mul]
        _ = (31073 * q + r * 2147975281) + 140737488355328 * q := by
            rw [Nat.add_assoc, Nat.add_comm (140737488355328 * q), ← Nat.add_assoc]
    have hremLt : 31073 * q + r * 2147975281 < 140737488355328 := by
      have h1 : 31073 * q ≤ 31073 * 2 := Nat.mul_le_mul_left 31073 hq_le
      have h2 : r * 2147975281 ≤ 65520 * 2147975281 := Nat.mul_le_mul_right 2147975281 hr_le
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide)
    rw [hexpand, Nat.add_mul_div_left _ _ (by decide : 0 < 140737488355328),
        Nat.div_eq_of_lt hremLt, Nat.zero_add]
  have hq32 : (BitVec.extractLsb' 0 32 ((s * 0x80078071#64) >>> 47)).toNat = s.toNat / 65521 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hshr, hq_eq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hq_le (by decide))
  have hs32 : (BitVec.extractLsb' 0 32 s).toNat = s.toNat := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hs (by decide))
  have hprod_le : (s.toNat / 65521) * 65521 ≤ 2 * 65521 := Nat.mul_le_mul_right 65521 hq_le
  have hprod32 : (BitVec.extractLsb' 0 32 ((s * 0x80078071#64) >>> 47) * 0xFFF1#32).toNat =
      (s.toNat / 65521) * 65521 := by
    rw [BitVec.toNat_mul, hq32]
    have hc32 : (0xFFF1#32 : BitVec 32).toNat = 65521 := rfl
    rw [hc32]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hprod_le (by decide))
  have hle_prod : (BitVec.extractLsb' 0 32 ((s * 0x80078071#64) >>> 47) * 0xFFF1#32).toNat ≤
      (BitVec.extractLsb' 0 32 s).toNat := by
    rw [hprod32, hs32]; omega
  have hrem_bound : s.toNat % 65521 < 2 ^ 32 := Nat.lt_trans hmod_lt (by decide)
  have hrem_eq : BitVec.extractLsb' 0 32 s -
      BitVec.extractLsb' 0 32 ((s * 0x80078071#64) >>> 47) * 0xFFF1#32 =
      BitVec.ofNat 32 (s.toNat % 65521) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv32_sub_toNat_of_le hle_prod, hs32, hprod32, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrem_bound]
    omega
  refine ⟨hrem_eq, ?_⟩
  rw [hrem_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem_bound]
  exact hmod_lt

/-- **Non-`restrict` Runtime Pointer-Overlap Check Discharge (`disjoint_slices_discharges_gcc_overlap_guard`):**
    GCC `-O3 -mavx2` emits `lea rax, [rdi - 1]; sub rax, rsi; cmp rax, 0x1e; jbe fallback`
    to guard 32-byte AVX2 vectorization when `dst` and `src` lack C `restrict`. Under
    safe-Rust `DisjointSlices dst len src len` (`len ≥ 32`, `0 < dst.toNat`, `src.toNat + 31 < 2^64`),
    `((dst - 1) - src).toNat > 30` holds unconditionally! -/
theorem disjoint_slices_discharges_gcc_overlap_guard {dst src : BitVec 64} {len : Nat} :
    NoWrapSlice dst len → NoWrapSlice src len →
    DisjointSlices dst len src len →
    32 ≤ len → 0 < dst.toNat → src.toNat + 31 < 2 ^ 64 →
    30 < ((dst + 0xFFFFFFFFFFFFFFFF#64) - src).toNat := by
  intro hnwD hnwS hdisj hlen hdstPos hsrcBound
  unfold NoWrapSlice at hnwD hnwS
  unfold DisjointSlices at hdisj
  have hneg1 : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = -1#64 := rfl
  rw [hneg1, ← BitVec.sub_eq_add_neg]
  have hone : (1#64 : BitVec 64).toNat = 1 := rfl
  have hdm1 : (dst - 1#64).toNat = dst.toNat - 1 := by
    rw [bv64_sub_toNat_of_le (by rw [hone]; omega), hone]
  rcases hdisj with hleft | hright
  · have hlt : (dst - 1#64).toNat < src.toNat := by rw [hdm1]; omega
    rw [bv64_sub_toNat_of_lt hlt, hdm1]
    omega
  · have hle : src.toNat ≤ (dst - 1#64).toNat := by rw [hdm1]; omega
    rw [bv64_sub_toNat_of_le hle, hdm1]
    omega

/-- **High-Byte `88 df` (`mov bh, bl`) + `vpshuflw` 8-Byte Key Broadcast (`mov_bh_bl_pshuflw_splat8`):**
    Proves that zero-extending `key : BitVec 8` into `ebx`, executing `mov bh, bl`
    (`writeSubReg8 ... (.hi8 .rbx)`), moving `ebx` to `xmm2`, and shuffling low 16-bit
    words with `imm = 0x00` (`pshuflw128`) produces 8 replicated copies of `key` in
    `bits[63:0]`. -/
theorem byteOf64_splat8 (key : BitVec 8) (j : Nat) (hj : j < 8) :
    byteOf64 ((key ++ key) ++ ((key ++ key) ++ ((key ++ key) ++ (key ++ key)))) j = key := by
  unfold byteOf64
  match j with
  | 0 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_self]
  | 1 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | 2 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_self]
  | 3 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | 4 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  | 5 =>
    rw [extractLsb_append_right_off _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_self]
  | 6 =>
    rw [extractLsb_append_left _ _ (by decide), extractLsb_append_right_off _ _ (by decide),
        extractLsb_self]
  | 7 =>
    rw [extractLsb_append_left _ _ (by decide), extractLsb_append_left _ _ (by decide),
        extractLsb_self]
  | _ + 8 => omega

theorem mov_bh_bl_pshuflw_splat8 (regs : Reg → BitVec 64) (key : BitVec 8) (j : Nat) (hj : j < 8) :
    let r1 := writeRegSz .s32 regs .rbx (key.zeroExtend 64)
    let r2 := writeSubReg8 r1 (.hi8 .rbx) (readSubReg8 r1 (.lo8 .rbx))
    let x2 := (readRegSz .s32 r2 .rbx).zeroExtend 128
    let x0 := pshuflw128 x2 0x00#8
    byteOf64 (BitVec.extractLsb' 0 64 x0) j = key := by
  dsimp only [writeRegSz, readSubReg8, writeSubReg8, readRegSz]
  rw [regUpd_eq, regUpd_eq]
  have hw0 : BitVec.extractLsb' 0 16
      (BitVec.zeroExtend 128
        (BitVec.zeroExtend 64
          (BitVec.extractLsb' 0 32
            (BitVec.extractLsb' 16 48 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key))) ++
             (BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key))) ++
              BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key)))))))) = key ++ key := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    unfold BitVec.zeroExtend
    simp only [Nat.zero_add, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8, hi, show i < 32 by omega, show i < 64 by omega, show i < 128 by omega]
    · have h16 : i < 16 := hi
      have hsub : i - 8 < 8 := by omega
      simp [h8, h16, hsub, show i < 32 by omega, show i < 64 by omega, show i < 128 by omega,
            show i - 8 < 32 by omega, show i - 8 < 64 by omega]
  have hi0 : ((BitVec.extractLsb' (2 * 0) 2 0x00#8).toNat % 4) * 16 = 0 := rfl
  have hi1 : ((BitVec.extractLsb' (2 * 1) 2 0x00#8).toNat % 4) * 16 = 0 := rfl
  have hi2 : ((BitVec.extractLsb' (2 * 2) 2 0x00#8).toNat % 4) * 16 = 0 := rfl
  have hi3 : ((BitVec.extractLsb' (2 * 3) 2 0x00#8).toNat % 4) * 16 = 0 := rfl
  have hx0 : BitVec.extractLsb' 0 64
      (pshuflw128
        (BitVec.zeroExtend 128
          (BitVec.zeroExtend 64
            (BitVec.extractLsb' 0 32
              (BitVec.extractLsb' 16 48 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key))) ++
               (BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key))) ++
                BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 key))))))))
        0x00#8) =
      (key ++ key) ++ ((key ++ key) ++ ((key ++ key) ++ (key ++ key))) := by
    unfold pshuflw128 getWord128
    dsimp only
    rw [hi0, hi1, hi2, hi3, hw0, extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  rw [hx0]
  exact byteOf64_splat8 key j hj

/-! ## Section 4: Pure-`Bool` Reflected Instruction & Basic-Block Decode (`0` `maxRecDepth`) -/

def bvEq {w : Nat} (a b : BitVec w) : Bool := Nat.beq a.toNat b.toNat

theorem bvEq_sound {w : Nat} {a b : BitVec w} (h : bvEq a b = true) : a = b :=
  BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h)

def ymmEq (a b : YmmIdx) : Bool := Nat.beq a.val b.val

theorem ymmEq_sound {a b : YmmIdx} (h : ymmEq a b = true) : a = b :=
  Fin.ext (Nat.eq_of_beq_eq_true h)

def boolEq (a b : Bool) : Bool :=
  match a, b with
  | false, false => true
  | true, true => true
  | _, _ => false

theorem boolEq_sound {a b : Bool} (h : boolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

def optRegEq : Option Reg → Option Reg → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

theorem optRegEq_sound {a b : Option Reg} (h : optRegEq a b = true) : a = b := by
  cases a <;> cases b <;> dsimp [optRegEq] at h
  · rfl
  · nomatch h
  · nomatch h
  · exact congrArg some (eq_of_beq h)

def optIdxEq : Option (Reg × Nat) → Option (Reg × Nat) → Bool
  | none, none => true
  | some (r1, s1), some (r2, s2) => (r1 == r2) && Nat.beq s1 s2
  | _, _ => false

theorem optIdxEq_sound {a b : Option (Reg × Nat)} (h : optIdxEq a b = true) : a = b := by
  cases a with
  | none => cases b with | none => rfl | some _ => nomatch h
  | some p1 =>
    cases b with
    | none => nomatch h
    | some p2 =>
      rcases p1 with ⟨r1, s1⟩; rcases p2 with ⟨r2, s2⟩
      dsimp [optIdxEq] at h
      have h12 := Bool.and_eq_true_iff.mp h
      rw [eq_of_beq h12.1, Nat.eq_of_beq_eq_true h12.2]

def addrEq (a b : X64Addr) : Bool :=
  optRegEq a.base b.base && optIdxEq a.index b.index &&
  bvEq a.disp b.disp && boolEq a.ripRel b.ripRel

theorem addrEq_sound {a b : X64Addr} (h : addrEq a b = true) : a = b := by
  rcases a with ⟨b1, i1, d1, r1⟩
  rcases b with ⟨b2, i2, d2, r2⟩
  dsimp [addrEq] at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  rw [optRegEq_sound h3.1, optIdxEq_sound h3.2, bvEq_sound h2.2, boolEq_sound h1.2]

def rmEq : X64Rm → X64Rm → Bool
  | .reg r1, .reg r2 => r1 == r2
  | .mem a1, .mem a2 => addrEq a1 a2
  | _, _ => false

theorem rmEq_sound {a b : X64Rm} (h : rmEq a b = true) : a = b := by
  cases a <;> cases b <;> dsimp [rmEq] at h
  · exact congrArg X64Rm.reg (eq_of_beq h)
  · nomatch h
  · nomatch h
  · exact congrArg X64Rm.mem (addrEq_sound h)

def rm8Eq : X64Rm8 → X64Rm8 → Bool
  | .reg8 r1, .reg8 r2 => r1 == r2
  | .mem8 a1, .mem8 a2 => addrEq a1 a2
  | _, _ => false

theorem rm8Eq_sound {a b : X64Rm8} (h : rm8Eq a b = true) : a = b := by
  cases a <;> cases b <;> dsimp [rm8Eq] at h
  · exact congrArg X64Rm8.reg8 (eq_of_beq h)
  · nomatch h
  · nomatch h
  · exact congrArg X64Rm8.mem8 (addrEq_sound h)

def xmmRmEq : X64XmmRm → X64XmmRm → Bool
  | .reg y1, .reg y2 => ymmEq y1 y2
  | .mem a1, .mem a2 => addrEq a1 a2
  | _, _ => false

theorem xmmRmEq_sound {a b : X64XmmRm} (h : xmmRmEq a b = true) : a = b := by
  cases a <;> cases b <;> dsimp [xmmRmEq] at h
  · exact congrArg X64XmmRm.reg (ymmEq_sound h)
  · nomatch h
  · nomatch h
  · exact congrArg X64XmmRm.mem (addrEq_sound h)

structure FlatInstr where
  tag   : Nat
  sz    : OpSize := .s64
  alu   : AluOp := .add
  sh    : ShiftOp := .rol
  un    : UnaryOp := .inc
  cc    : Cond := .e
  sm    : SimdMode := .legacy128
  ew    : VecElem := .e8
  uo    : VecUnpackOp := .lbw
  eo    : VecExtendOp := .zxbw
  b1    : Bool := false
  b2    : Bool := false
  r1    : Reg := .rax
  sr    : SubReg8 := .lo8 .rax
  rm    : X64Rm := .reg .rax
  rm8   : X64Rm8 := .reg8 (.lo8 .rax)
  xrm   : X64XmmRm := .reg ⟨0, by decide⟩
  addr  : X64Addr := {}
  y1    : YmmIdx := ⟨0, by decide⟩
  y2    : YmmIdx := ⟨0, by decide⟩
  imm64 : BitVec 64 := 0#64
  imm8  : BitVec 8 := 0#8

def flatEq (a b : FlatInstr) : Bool :=
  Nat.beq a.tag b.tag && (a.sz == b.sz) && (a.alu == b.alu) && (a.sh == b.sh) &&
  (a.un == b.un) && (a.cc == b.cc) && (a.sm == b.sm) && (a.ew == b.ew) &&
  (a.uo == b.uo) && (a.eo == b.eo) && boolEq a.b1 b.b1 && boolEq a.b2 b.b2 &&
  (a.r1 == b.r1) && (a.sr == b.sr) && rmEq a.rm b.rm && rm8Eq a.rm8 b.rm8 &&
  xmmRmEq a.xrm b.xrm && addrEq a.addr b.addr && ymmEq a.y1 b.y1 && ymmEq a.y2 b.y2 &&
  bvEq a.imm64 b.imm64 && bvEq a.imm8 b.imm8

theorem flatEq_sound {a b : FlatInstr} (h : flatEq a b = true) : a = b := by
  rcases a with ⟨t1, sz1, al1, sh1, un1, cc1, sm1, ew1, uo1, eo1, b11, b21, rg1, sr1, rm1, rm81, xr1, ad1, y11, y21, i641, i81⟩
  rcases b with ⟨t2, sz2, al2, sh2, un2, cc2, sm2, ew2, uo2, eo2, b12, b22, rg2, sr2, rm2, rm82, xr2, ad2, y12, y22, i642, i82⟩
  dsimp only [flatEq] at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩
  rw [Nat.eq_of_beq_eq_true h1, eq_of_beq h2, eq_of_beq h3, eq_of_beq h4,
      eq_of_beq h5, eq_of_beq h6, eq_of_beq h7, eq_of_beq h8,
      eq_of_beq h9, eq_of_beq h10, boolEq_sound h11, boolEq_sound h12,
      eq_of_beq h13, eq_of_beq h14, rmEq_sound h15, rm8Eq_sound h16,
      xmmRmEq_sound h17, addrEq_sound h18, ymmEq_sound h19, ymmEq_sound h20,
      bvEq_sound h21, bvEq_sound h22]

def encodeInstr : X64Instr → FlatInstr
  | .nop => { tag := 0 }
  | .endbr64 => { tag := 1 }
  | .vzeroupper => { tag := 2 }
  | .ud2 => { tag := 3 }
  | .cli => { tag := 4 }
  | .mov8Load d s => { tag := 5, sr := d, rm8 := s }
  | .mov8Store d s => { tag := 6, rm8 := d, sr := s }
  | .mov8Imm d i => { tag := 7, rm8 := d, imm8 := i }
  | .alu8RmReg o d s => { tag := 8, alu := o, rm8 := d, sr := s }
  | .alu8RegRm o d s => { tag := 9, alu := o, sr := d, rm8 := s }
  | .alu8Imm o d i => { tag := 10, alu := o, rm8 := d, imm8 := i }
  | .setcc8 c d => { tag := 11, cc := c, rm8 := d }
  | .movzx8 z d s => { tag := 12, sz := z, r1 := d, rm8 := s }
  | .movzx16 z d s => { tag := 13, sz := z, r1 := d, rm := s }
  | .movsx8 z d s => { tag := 14, sz := z, r1 := d, rm8 := s }
  | .movsx16 z d s => { tag := 15, sz := z, r1 := d, rm := s }
  | .movsxd d s => { tag := 16, r1 := d, rm := s }
  | .movLoad z d s => { tag := 17, sz := z, r1 := d, rm := s }
  | .movStore z d s => { tag := 18, sz := z, rm := d, r1 := s }
  | .movImm z d i => { tag := 19, sz := z, r1 := d, imm64 := i }
  | .movRmImm32 z d i => { tag := 20, sz := z, rm := d, imm64 := i }
  | .lea z d a => { tag := 21, sz := z, r1 := d, addr := a }
  | .xchg z r m => { tag := 22, sz := z, r1 := r, rm := m }
  | .aluRmReg z o d s => { tag := 23, sz := z, alu := o, rm := d, r1 := s }
  | .aluRegRm z o d s => { tag := 24, sz := z, alu := o, r1 := d, rm := s }
  | .aluImm z o d i => { tag := 25, sz := z, alu := o, rm := d, imm64 := i }
  | .unaryRm z o d => { tag := 26, sz := z, un := o, rm := d }
  | .shiftImm z o d c => { tag := 27, sz := z, sh := o, rm := d, imm8 := c }
  | .imul2 z d s => { tag := 28, sz := z, r1 := d, rm := s }
  | .imul3 z d s i => { tag := 29, sz := z, r1 := d, rm := s, imm64 := i }
  | .bsf z d s => { tag := 30, sz := z, r1 := d, rm := s }
  | .push64 s => { tag := 31, r1 := s }
  | .pop64 d => { tag := 32, r1 := d }
  | .leave64 => { tag := 33 }
  | .ret64 => { tag := 34 }
  | .jmpRel r => { tag := 35, imm64 := r }
  | .jccRel c r => { tag := 36, cc := c, imm64 := r }
  | .simdMovLoad m d s => { tag := 37, sm := m, y1 := d, xrm := s }
  | .simdMovStore m d s => { tag := 38, sm := m, xrm := d, y1 := s }
  | .simdMovqLoad v d s => { tag := 39, b1 := v, y1 := d, xrm := s }
  | .simdMovqStore v d s => { tag := 40, b1 := v, xrm := d, y1 := s }
  | .simdMovGprToX v q d s => { tag := 41, b1 := v, b2 := q, y1 := d, rm := s }
  | .simdMovXToGpr v q d s => { tag := 42, b1 := v, b2 := q, rm := d, y1 := s }
  | .simdBitwise m o d a b => { tag := 43, sm := m, alu := o, y1 := d, y2 := a, xrm := b }
  | .simdAdd m e d a b => { tag := 44, sm := m, ew := e, y1 := d, y2 := a, xrm := b }
  | .simdSub m e d a b => { tag := 45, sm := m, ew := e, y1 := d, y2 := a, xrm := b }
  | .simdCmpeq m e d a b => { tag := 46, sm := m, ew := e, y1 := d, y2 := a, xrm := b }
  | .simdCmpgt m e d a b => { tag := 47, sm := m, ew := e, y1 := d, y2 := a, xrm := b }
  | .simdUnpack m o d a b => { tag := 48, sm := m, uo := o, y1 := d, y2 := a, xrm := b }
  | .simdExtend m o d s => { tag := 49, sm := m, eo := o, y1 := d, xrm := s }
  | .simdBroadcastB m d s => { tag := 50, sm := m, y1 := d, xrm := s }
  | .simdBroadcastQ m d s => { tag := 51, sm := m, y1 := d, xrm := s }
  | .simdPmullw m d a b => { tag := 52, sm := m, y1 := d, y2 := a, xrm := b }
  | .simdPmulhuw m d a b => { tag := 53, sm := m, y1 := d, y2 := a, xrm := b }
  | .simdPmulld m d a b => { tag := 54, sm := m, y1 := d, y2 := a, xrm := b }
  | .simdPmaddwd m d a b => { tag := 55, sm := m, y1 := d, y2 := a, xrm := b }
  | .simdPsrldq m d s i => { tag := 56, sm := m, y1 := d, y2 := s, imm8 := i }
  | .simdPsrlqImm m d s i => { tag := 57, sm := m, y1 := d, y2 := s, imm8 := i }
  | .simdPshufd m d s i => { tag := 58, sm := m, y1 := d, xrm := s, imm8 := i }
  | .simdPshuflw m d s i => { tag := 59, sm := m, y1 := d, xrm := s, imm8 := i }
  | .simdExtract128 d s i => { tag := 60, xrm := d, y1 := s, imm8 := i }
  | .simdPerm2i128 d a b i => { tag := 61, y1 := d, y2 := a, xrm := b, imm8 := i }

def decodeInstr (f : FlatInstr) : Option X64Instr :=
  match f.tag with
  | 0  => some .nop
  | 1  => some .endbr64
  | 2  => some .vzeroupper
  | 3  => some .ud2
  | 4  => some .cli
  | 5  => some (.mov8Load f.sr f.rm8)
  | 6  => some (.mov8Store f.rm8 f.sr)
  | 7  => some (.mov8Imm f.rm8 f.imm8)
  | 8  => some (.alu8RmReg f.alu f.rm8 f.sr)
  | 9  => some (.alu8RegRm f.alu f.sr f.rm8)
  | 10 => some (.alu8Imm f.alu f.rm8 f.imm8)
  | 11 => some (.setcc8 f.cc f.rm8)
  | 12 => some (.movzx8 f.sz f.r1 f.rm8)
  | 13 => some (.movzx16 f.sz f.r1 f.rm)
  | 14 => some (.movsx8 f.sz f.r1 f.rm8)
  | 15 => some (.movsx16 f.sz f.r1 f.rm)
  | 16 => some (.movsxd f.r1 f.rm)
  | 17 => some (.movLoad f.sz f.r1 f.rm)
  | 18 => some (.movStore f.sz f.rm f.r1)
  | 19 => some (.movImm f.sz f.r1 f.imm64)
  | 20 => some (.movRmImm32 f.sz f.rm f.imm64)
  | 21 => some (.lea f.sz f.r1 f.addr)
  | 22 => some (.xchg f.sz f.r1 f.rm)
  | 23 => some (.aluRmReg f.sz f.alu f.rm f.r1)
  | 24 => some (.aluRegRm f.sz f.alu f.r1 f.rm)
  | 25 => some (.aluImm f.sz f.alu f.rm f.imm64)
  | 26 => some (.unaryRm f.sz f.un f.rm)
  | 27 => some (.shiftImm f.sz f.sh f.rm f.imm8)
  | 28 => some (.imul2 f.sz f.r1 f.rm)
  | 29 => some (.imul3 f.sz f.r1 f.rm f.imm64)
  | 30 => some (.bsf f.sz f.r1 f.rm)
  | 31 => some (.push64 f.r1)
  | 32 => some (.pop64 f.r1)
  | 33 => some .leave64
  | 34 => some .ret64
  | 35 => some (.jmpRel f.imm64)
  | 36 => some (.jccRel f.cc f.imm64)
  | 37 => some (.simdMovLoad f.sm f.y1 f.xrm)
  | 38 => some (.simdMovStore f.sm f.xrm f.y1)
  | 39 => some (.simdMovqLoad f.b1 f.y1 f.xrm)
  | 40 => some (.simdMovqStore f.b1 f.xrm f.y1)
  | 41 => some (.simdMovGprToX f.b1 f.b2 f.y1 f.rm)
  | 42 => some (.simdMovXToGpr f.b1 f.b2 f.rm f.y1)
  | 43 => some (.simdBitwise f.sm f.alu f.y1 f.y2 f.xrm)
  | 44 => some (.simdAdd f.sm f.ew f.y1 f.y2 f.xrm)
  | 45 => some (.simdSub f.sm f.ew f.y1 f.y2 f.xrm)
  | 46 => some (.simdCmpeq f.sm f.ew f.y1 f.y2 f.xrm)
  | 47 => some (.simdCmpgt f.sm f.ew f.y1 f.y2 f.xrm)
  | 48 => some (.simdUnpack f.sm f.uo f.y1 f.y2 f.xrm)
  | 49 => some (.simdExtend f.sm f.eo f.y1 f.xrm)
  | 50 => some (.simdBroadcastB f.sm f.y1 f.xrm)
  | 51 => some (.simdBroadcastQ f.sm f.y1 f.xrm)
  | 52 => some (.simdPmullw f.sm f.y1 f.y2 f.xrm)
  | 53 => some (.simdPmulhuw f.sm f.y1 f.y2 f.xrm)
  | 54 => some (.simdPmulld f.sm f.y1 f.y2 f.xrm)
  | 55 => some (.simdPmaddwd f.sm f.y1 f.y2 f.xrm)
  | 56 => some (.simdPsrldq f.sm f.y1 f.y2 f.imm8)
  | 57 => some (.simdPsrlqImm f.sm f.y1 f.y2 f.imm8)
  | 58 => some (.simdPshufd f.sm f.y1 f.xrm f.imm8)
  | 59 => some (.simdPshuflw f.sm f.y1 f.xrm f.imm8)
  | 60 => some (.simdExtract128 f.xrm f.y1 f.imm8)
  | 61 => some (.simdPerm2i128 f.y1 f.y2 f.xrm f.imm8)
  | _  => none

theorem decode_encode_instr (x : X64Instr) : decodeInstr (encodeInstr x) = some x := by
  cases x <;> rfl

def instrEq (a b : X64Instr) : Bool :=
  flatEq (encodeInstr a) (encodeInstr b)

theorem instrEq_sound {a b : X64Instr} (h : instrEq a b = true) : a = b := by
  have hf : encodeInstr a = encodeInstr b := flatEq_sound h
  have hd := congrArg decodeInstr hf
  rw [decode_encode_instr, decode_encode_instr] at hd
  injection hd

def checkDecodeAt (cmap : CodeMap) (rip : BitVec 64) (ins : X64Instr) (len : Nat) : Bool :=
  match decodeX64 (fetchWindow16 cmap rip) with
  | .ok ins' len' => instrEq ins' ins && Nat.beq len' len
  | .fault _ => false

theorem decodeAt_of_check {cmap : CodeMap} {rip : BitVec 64} {ins : X64Instr} {len : Nat}
    (h : checkDecodeAt cmap rip ins len = true) :
    decodeX64 (fetchWindow16 cmap rip) = .ok ins len := by
  unfold checkDecodeAt at h
  cases hd : decodeX64 (fetchWindow16 cmap rip) with
  | fault fk => rw [hd] at h; nomatch h
  | ok ins' len' =>
    rw [hd] at h
    have h12 := Bool.and_eq_true_iff.mp h
    rw [instrEq_sound h12.1, Nat.eq_of_beq_eq_true h12.2]

def checkDecodeSeqFuel (cmap : CodeMap) (fuel : Nat) (rip0 : BitVec 64)
    (seq0 : List (X64Instr × BitVec 64)) : Bool :=
  @Nat.rec (fun _ => BitVec 64 → List (X64Instr × BitVec 64) → Bool)
    (fun _ xs => match xs with | [] => true | _ :: _ => false)
    (fun _ ih rip xs =>
      match xs with
      | [] => true
      | (ins, nextRip) :: rest =>
        match decodeX64 (fetchWindow16 cmap rip) with
        | .ok ins' len =>
          instrEq ins' ins &&
          isNonBranchingNormal ins &&
          bvEq (rip + BitVec.ofNat 64 len) nextRip &&
          ih nextRip rest
        | .fault _ => false)
    fuel rip0 seq0

def checkDecodeSeqAt (cmap : CodeMap) (rip0 : BitVec 64)
    (seq : List (X64Instr × BitVec 64)) : Bool :=
  checkDecodeSeqFuel cmap seq.length rip0 seq

theorem decodeSeqAt_of_check_aux {cmap : CodeMap} {seq : List (X64Instr × BitVec 64)} :
    ∀ {rip0 : BitVec 64},
      checkDecodeSeqAt cmap rip0 seq = true →
      decodeSeqAt cmap seq.length rip0 = some seq := by
  induction seq with
  | nil =>
    intro rip0 _
    rfl
  | cons hd tl ih =>
    intro rip0 h
    rcases hd with ⟨ins, nextRip⟩
    change (match decodeX64 (fetchWindow16 cmap rip0) with
      | .ok ins' len =>
        instrEq ins' ins &&
        isNonBranchingNormal ins &&
        bvEq (rip0 + BitVec.ofNat 64 len) nextRip &&
        checkDecodeSeqAt cmap nextRip tl
      | .fault _ => false) = true at h
    cases hdec : decodeX64 (fetchWindow16 cmap rip0) with
    | fault fk => rw [hdec] at h; nomatch h
    | ok ins' len =>
      rw [hdec] at h
      have h1 := Bool.and_eq_true_iff.mp h
      have h2 := Bool.and_eq_true_iff.mp h1.1
      have h3 := Bool.and_eq_true_iff.mp h2.1
      have hins : ins' = ins := instrEq_sound h3.1
      have hnorm : isNonBranchingNormal ins = true := h3.2
      have hrip : rip0 + BitVec.ofNat 64 len = nextRip := bvEq_sound h2.2
      have hrest : decodeSeqAt cmap tl.length nextRip = some tl := ih h1.2
      rw [hins] at hdec
      change decodeSeqAt cmap (tl.length + 1) rip0 = some ((ins, nextRip) :: tl)
      rw [decodeSeqAt_succ, hdec]
      dsimp only
      rw [ifTrue hnorm, hrip, hrest]

theorem decodeSeqAt_of_check {cmap : CodeMap} {n : Nat} {rip0 : BitVec 64}
    {seq : List (X64Instr × BitVec 64)}
    (hn : seq.length = n)
    (h : checkDecodeSeqAt cmap rip0 seq = true) :
    decodeSeqAt cmap n rip0 = some seq := by
  subst hn
  exact decodeSeqAt_of_check_aux h

/-! ## Section 5: O(1) Symbolic `execByteInstr` Step Rewrite Lemmas -/

theorem zext8_32_64_eq (b : BitVec 8) :
    (BitVec.extractLsb' 0 32 (b.zeroExtend 64)).zeroExtend 64 = b.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  have hlt := b.isLt
  unfold BitVec.zeroExtend
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]

theorem zext16_32_64_eq (w : BitVec 16) :
    (BitVec.extractLsb' 0 32 (w.zeroExtend 64)).zeroExtend 64 = w.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  have hlt := w.isLt
  unfold BitVec.zeroExtend
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64)]

theorem zext32_extract32_eq (x : BitVec 32) :
    BitVec.extractLsb' 0 32 (x.zeroExtend 64) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  unfold BitVec.zeroExtend
  simp [hi, show i < 64 by omega]

theorem exec_nop (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr .nop nr ch s = { s with rip := nr } := rfl

theorem exec_vzeroupper (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr .vzeroupper nr ch s = { s with rip := nr, ymms := vzeroUpperAll s.ymms } := rfl

theorem exec_movImm_s64 (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movImm .s64 dst imm) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst imm } := rfl

theorem exec_movImm_s32 (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movImm .s32 dst imm) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 imm).zeroExtend 64) } := rfl

theorem exec_movStore_s64_reg (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movStore .s64 (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs src) } := rfl

theorem exec_movStore_s32_reg (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movStore .s32 (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeByteRm, writeRegSz, readRegSz]
  rw [zext32_extract32_eq]

theorem exec_movLoad_s64_mem (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movLoad .s64 dst (.mem a)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (readMem64 s.mem (evalByteAddr s nr a)) } := rfl

theorem exec_movzx8_s32_mem (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movzx8 .s32 dst (.mem8 a)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((s.mem (evalByteAddr s nr a)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeRegSz, readByteRm8, readMem8]
  rw [zext8_32_64_eq]

theorem exec_movzx8_s32_lo8 (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movzx8 .s32 dst (.reg8 (.lo8 src))) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 8 (s.regs src)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeRegSz, readByteRm8, readSubReg8]
  rw [zext8_32_64_eq]

theorem exec_movzx16_s32_reg (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movzx16 .s32 dst (.reg src)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 16 (s.regs src)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeRegSz, readByteRm, readRegSz]
  have h16 : BitVec.extractLsb' 0 16 ((BitVec.extractLsb' 0 16 (s.regs src)).zeroExtend 64) =
      BitVec.extractLsb' 0 16 (s.regs src) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; unfold BitVec.zeroExtend
    simp [hi, show i < 64 by omega]
  rw [h16, zext16_32_64_eq]

theorem exec_movzx16_s32_mem (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movzx16 .s32 dst (.mem a)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((readMem16 s.mem (evalByteAddr s nr a)).zeroExtend 64) } := by
  dsimp only [execByteInstr, writeRegSz, readByteRm]
  have h16 : BitVec.extractLsb' 0 16 ((readMem16 s.mem (evalByteAddr s nr a)).zeroExtend 64) =
      readMem16 s.mem (evalByteAddr s nr a) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; unfold BitVec.zeroExtend
    simp [hi, show i < 64 by omega]
  rw [h16, zext16_32_64_eq]

theorem exec_movsx8_s64_mem (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.movsx8 .s64 dst (.mem8 a)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (sext8To64 (s.mem (evalByteAddr s nr a))) } := rfl

theorem exec_mov8Store_mem_lo8 (a : X64Addr) (src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.mov8Store (.mem8 a) (.lo8 src)) nr ch s =
      { s with rip := nr, mem := memUpd8 s.mem (evalByteAddr s nr a) (BitVec.extractLsb' 0 8 (s.regs src)) } := rfl

theorem exec_lea_s64 (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.lea .s64 dst a) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (evalByteAddr s nr a) } := rfl

theorem exec_lea_s32 (dst : Reg) (a : X64Addr) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.lea .s32 dst a) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (evalByteAddr s nr a)).zeroExtend 64) } := rfl

theorem exec_aluImm_s64_add (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluImm .s64 .add (.reg dst) imm) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst + imm),
               flags := (evalAluN (by decide) .add (s.regs dst) imm s.flags ch.flags).2 } := rfl

theorem exec_aluImm_s64_and (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluImm .s64 .and (.reg dst) imm) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst &&& imm),
               flags := (evalAluN (by decide) .and (s.regs dst) imm s.flags ch.flags).2 } := rfl

theorem exec_aluImm_s32_add (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluImm .s32 .add (.reg dst) imm) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) + BitVec.extractLsb' 0 32 imm).zeroExtend 64),
               flags := (evalAluN (by decide) .add (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 imm) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  rw [ifFalse (by decide), zext32_extract32_eq, zext32_extract32_eq]
  rfl

theorem exec_aluRmReg_s64_add (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s64 .add (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst + s.regs src),
               flags := (evalAluN (by decide) .add (s.regs dst) (s.regs src) s.flags ch.flags).2 } := rfl

theorem exec_aluRmReg_s64_sub (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s64 .sub (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst - s.regs src),
               flags := (evalAluN (by decide) .sub (s.regs dst) (s.regs src) s.flags ch.flags).2 } := rfl

theorem exec_aluRmReg_s64_xor (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s64 .xor (.reg dst) src) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst ^^^ s.regs src),
               flags := (evalAluN (by decide) .xor (s.regs dst) (s.regs src) s.flags ch.flags).2 } := rfl

theorem exec_aluRmReg_s32_add (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .add (.reg dst) src) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) + BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64),
               flags := (evalAluN (by decide) .add (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 (s.regs src)) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  rw [ifFalse (by decide), zext32_extract32_eq, zext32_extract32_eq, zext32_extract32_eq]
  rfl

theorem exec_aluRmReg_s32_sub (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .sub (.reg dst) src) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) - BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64),
               flags := (evalAluN (by decide) .sub (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 (s.regs src)) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  rw [ifFalse (by decide), zext32_extract32_eq, zext32_extract32_eq, zext32_extract32_eq]
  rfl

theorem exec_aluRmReg_s32_xor (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .xor (.reg dst) src) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) ^^^ BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64),
               flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 (s.regs src)) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  rw [ifFalse (by decide), zext32_extract32_eq, zext32_extract32_eq, zext32_extract32_eq]
  rfl

theorem exec_aluRmReg_s32_xor_self (dst : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .xor (.reg dst) dst) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst 0#64,
               flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 (s.regs dst)) s.flags ch.flags).2 } := by
  rw [exec_aluRmReg_s32_xor, BitVec.xor_self]
  rfl

theorem exec_aluRmReg_s32_or (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .or (.reg dst) src) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) ||| BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64),
               flags := (evalAluN (by decide) .or (BitVec.extractLsb' 0 32 (s.regs dst)) (BitVec.extractLsb' 0 32 (s.regs src)) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  rw [ifFalse (by decide), zext32_extract32_eq, zext32_extract32_eq, zext32_extract32_eq]
  rfl

theorem exec_aluRmReg_s64_cmp (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s64 .cmp (.reg dst) src) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .cmp (s.regs dst) (s.regs src) s.flags ch.flags).2 } := rfl

theorem exec_aluImm_s64_cmp (dst : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluImm .s64 .cmp (.reg dst) imm) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .cmp (s.regs dst) imm s.flags ch.flags).2 } := rfl

theorem exec_aluRmReg_s64_test (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s64 .test (.reg dst) src) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .test (s.regs dst) (s.regs src) s.flags ch.flags).2 } := rfl

theorem exec_alu8Imm_cmp_lo8 (dst : Reg) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.alu8Imm .cmp (.reg8 (.lo8 dst)) imm) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .cmp (BitVec.extractLsb' 0 8 (s.regs dst)) imm s.flags ch.flags).2 } := rfl

theorem exec_alu8Imm_test_lo8 (dst : Reg) (imm : BitVec 8) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.alu8Imm .test (.reg8 (.lo8 dst)) imm) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 (s.regs dst)) imm s.flags ch.flags).2 } := rfl

theorem exec_imul2_s64_reg (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.imul2 .s64 dst (.reg src)) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst * s.regs src),
               flags := (evalImulSz .s64 (s.regs dst) (s.regs src) ch.flags).2 } := rfl

theorem exec_imul2_s32_reg (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.imul2 .s32 dst (.reg src)) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) * BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64),
               flags := (evalImulSz .s32 ((BitVec.extractLsb' 0 32 (s.regs dst)).zeroExtend 64) ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) ch.flags).2 } := by
  dsimp only [execByteInstr, evalImulSz, readByteRm, readRegSz, writeRegSz]
  rw [zext32_extract32_eq, zext32_extract32_eq, zext32_extract32_eq]

theorem exec_imul3_s32_reg (dst src : Reg) (imm nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.imul3 .s32 dst (.reg src) imm) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs src) * BitVec.extractLsb' 0 32 imm).zeroExtend 64),
               flags := (evalImulSz .s32 ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) imm ch.flags).2 } := by
  dsimp only [execByteInstr, evalImulSz, readByteRm, readRegSz, writeRegSz]
  rw [zext32_extract32_eq, zext32_extract32_eq]

theorem exec_shiftImm_s64_shr (dst : Reg) (cnt : BitVec 8) (hc : (cnt.toNat &&& 63) ≠ 0)
    (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.shiftImm .s64 .shr (.reg dst) cnt) nr ch s =
      { s with rip := nr, regs := regUpd s.regs dst (s.regs dst >>> (cnt.toNat &&& 63)),
               flags := (evalShiftSz .s64 .shr (s.regs dst) cnt s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalShiftSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  have hbeq : ((cnt.toNat &&& 63) == 0) = false := by
    cases h : ((cnt.toNat &&& 63) == 0)
    · rfl
    · exact absurd (eq_of_beq h) hc
  simp only [show (OpSize.s64 == OpSize.s64) = true from rfl, ite_true, hbeq, Bool.false_eq_true, ite_false]

theorem exec_shiftImm_s32_shr (dst : Reg) (cnt : BitVec 8) (hc : (cnt.toNat &&& 31) ≠ 0)
    (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.shiftImm .s32 .shr (.reg dst) cnt) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) >>> (cnt.toNat &&& 31)).zeroExtend 64),
               flags := (evalShiftSz .s32 .shr ((BitVec.extractLsb' 0 32 (s.regs dst)).zeroExtend 64) cnt s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalShiftSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  have hbeq : ((cnt.toNat &&& 31) == 0) = false := by
    cases h : ((cnt.toNat &&& 31) == 0)
    · rfl
    · exact absurd (eq_of_beq h) hc
  simp only [show (OpSize.s32 == OpSize.s64) = false from rfl, Bool.false_eq_true, ite_false, hbeq, zext32_extract32_eq]

theorem exec_shiftImm_s32_shl (dst : Reg) (cnt : BitVec 8) (hc : (cnt.toNat &&& 31) ≠ 0)
    (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.shiftImm .s32 .shl (.reg dst) cnt) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs dst) <<< (cnt.toNat &&& 31)).zeroExtend 64),
               flags := (evalShiftSz .s32 .shl ((BitVec.extractLsb' 0 32 (s.regs dst)).zeroExtend 64) cnt s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalShiftSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  have hbeq : ((cnt.toNat &&& 31) == 0) = false := by
    cases h : ((cnt.toNat &&& 31) == 0)
    · rfl
    · exact absurd (eq_of_beq h) hc
  simp only [show (OpSize.s32 == OpSize.s64) = false from rfl, Bool.false_eq_true, ite_false, hbeq, zext32_extract32_eq]

theorem exec_shiftImm_s32_rol (dst : Reg) (cnt : BitVec 8) (hc : (cnt.toNat &&& 31) ≠ 0)
    (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.shiftImm .s32 .rol (.reg dst) cnt) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst ((BitVec.rotateLeft (BitVec.extractLsb' 0 32 (s.regs dst)) (cnt.toNat &&& 31)).zeroExtend 64),
               flags := (evalShiftSz .s32 .rol ((BitVec.extractLsb' 0 32 (s.regs dst)).zeroExtend 64) cnt s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalShiftSz, readByteRm, readRegSz, writeByteRm, writeRegSz]
  have hbeq : ((cnt.toNat &&& 31) == 0) = false := by
    cases h : ((cnt.toNat &&& 31) == 0)
    · rfl
    · exact absurd (eq_of_beq h) hc
  simp only [show (OpSize.s32 == OpSize.s64) = false from rfl, Bool.false_eq_true, ite_false, hbeq, zext32_extract32_eq]

theorem cmp_flags_zf {w : Nat} (hw : 0 < w) (a b : BitVec w) (fl undef : RFlags) :
    (evalAluN hw .cmp a b fl undef).2.zf = (a - b == 0#w) := rfl

theorem cmp_flags_cf {w : Nat} (hw : 0 < w) (a b : BitVec w) (fl undef : RFlags) :
    (evalAluN hw .cmp a b fl undef).2.cf = decide (a.toNat < b.toNat) := rfl

theorem test_flags_zf {w : Nat} (hw : 0 < w) (a b : BitVec w) (fl undef : RFlags) :
    (evalAluN hw .test a b fl undef).2.zf = (a &&& b == 0#w) := rfl

theorem test_flags_sf {w : Nat} (hw : 0 < w) (a b : BitVec w) (fl undef : RFlags) :
    (evalAluN hw .test a b fl undef).2.sf = (a &&& b).msb := rfl

theorem test_flags_of {w : Nat} (hw : 0 < w) (a b : BitVec w) (fl undef : RFlags) :
    (evalAluN hw .test a b fl undef).2.of = false := rfl

theorem evalByteAddr_base (s : X64State) (nr : BitVec 64) (r : Reg) :
    evalByteAddr s nr { base := some r } = s.regs r := by
  dsimp [evalByteAddr]; simp [BitVec.add_zero]

theorem evalByteAddr_base_disp (s : X64State) (nr : BitVec 64) (r : Reg) (d : BitVec 64) :
    evalByteAddr s nr { base := some r, disp := d } = s.regs r + d := by
  dsimp [evalByteAddr]; simp [BitVec.add_zero]

theorem evalByteAddr_base_idx0 (s : X64State) (nr : BitVec 64) (rb ri : Reg) :
    evalByteAddr s nr { base := some rb, index := some (ri, 0) } = s.regs rb + s.regs ri := by
  dsimp [evalByteAddr]; simp [BitVec.add_zero]

theorem evalByteAddr_base_idx0_disp (s : X64State) (nr : BitVec 64) (rb ri : Reg) (d : BitVec 64) :
    evalByteAddr s nr { base := some rb, index := some (ri, 0), disp := d } = (s.regs rb + s.regs ri) + d := by
  dsimp [evalByteAddr]; simp

theorem evalByteAddr_base_idx1 (s : X64State) (nr : BitVec 64) (rb ri : Reg) :
    evalByteAddr s nr { base := some rb, index := some (ri, 1) } = s.regs rb + (s.regs ri <<< 1) := by
  dsimp [evalByteAddr]; simp [BitVec.add_zero]

theorem evalByteAddr_base_idx1_disp (s : X64State) (nr : BitVec 64) (rb ri : Reg) (d : BitVec 64) :
    evalByteAddr s nr { base := some rb, index := some (ri, 1), disp := d } = (s.regs rb + (s.regs ri <<< 1)) + d := by
  dsimp [evalByteAddr]

def isCallerSaved : Reg → Bool
  | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
  | _ => false

theorem regUpd_caller_preserves_cs {s0 : X64State} {regs : Reg → BitVec 64}
    {r : Reg} {v : BitVec 64} (hr : isCallerSaved r = true)
    (h1 : regs .rsp = s0.regs .rsp) (h2 : regs .rbx = s0.regs .rbx)
    (h3 : regs .rbp = s0.regs .rbp) (h4 : regs .r12 = s0.regs .r12)
    (h5 : regs .r13 = s0.regs .r13) (h6 : regs .r14 = s0.regs .r14)
    (h7 : regs .r15 = s0.regs .r15) :
    regUpd regs r v .rsp = s0.regs .rsp ∧ regUpd regs r v .rbx = s0.regs .rbx ∧
    regUpd regs r v .rbp = s0.regs .rbp ∧ regUpd regs r v .r12 = s0.regs .r12 ∧
    regUpd regs r v .r13 = s0.regs .r13 ∧ regUpd regs r v .r14 = s0.regs .r14 ∧
    regUpd regs r v .r15 = s0.regs .r15 := by
  cases r <;> try (simp [isCallerSaved] at hr)
  all_goals
    exact ⟨by rw [regUpd_ne _ (by decide), h1], by rw [regUpd_ne _ (by decide), h2],
           by rw [regUpd_ne _ (by decide), h3], by rw [regUpd_ne _ (by decide), h4],
           by rw [regUpd_ne _ (by decide), h5], by rw [regUpd_ne _ (by decide), h6],
           by rw [regUpd_ne _ (by decide), h7]⟩

theorem cs_step_caller {s0 : X64State} {regs : Reg → BitVec 64} {r : Reg} {v : BitVec 64}
    (hr : isCallerSaved r = true)
    (h : regs .rsp = s0.regs .rsp ∧ regs .rbx = s0.regs .rbx ∧ regs .rbp = s0.regs .rbp ∧
         regs .r12 = s0.regs .r12 ∧ regs .r13 = s0.regs .r13 ∧ regs .r14 = s0.regs .r14 ∧
         regs .r15 = s0.regs .r15) :
    regUpd regs r v .rsp = s0.regs .rsp ∧ regUpd regs r v .rbx = s0.regs .rbx ∧
    regUpd regs r v .rbp = s0.regs .rbp ∧ regUpd regs r v .r12 = s0.regs .r12 ∧
    regUpd regs r v .r13 = s0.regs .r13 ∧ regUpd regs r v .r14 = s0.regs .r14 ∧
    regUpd regs r v .r15 = s0.regs .r15 :=
  regUpd_caller_preserves_cs hr h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem exec_jcc_taken {cc : Cond} {rel nr : BitVec 64} {ch : UndefChoice} {s : X64State}
    (h : evalCond cc s.flags = true) :
    execByteInstr (.jccRel cc rel) nr ch s = { s with rip := nr + rel } := by
  dsimp only [execByteInstr]; rw [ifTrue h]

theorem exec_jcc_fall {cc : Cond} {rel nr : BitVec 64} {ch : UndefChoice} {s : X64State}
    (h : evalCond cc s.flags = false) :
    execByteInstr (.jccRel cc rel) nr ch s = { s with rip := nr } := by
  dsimp only [execByteInstr]; rw [h]; simp only [Bool.false_eq_true, ite_false]

theorem exec_jmp {rel nr : BitVec 64} {ch : UndefChoice} {s : X64State} :
    execByteInstr (.jmpRel rel) nr ch s = { s with rip := nr + rel } := rfl

theorem exec_jcc_taken_eq {cc : Cond} {rel nr : BitVec 64} (target : BitVec 64)
    {ch : UndefChoice} {s : X64State}
    (h : evalCond cc s.flags = true) (ht : bvEq (nr + rel) target = true) :
    execByteInstr (.jccRel cc rel) nr ch s = { s with rip := target } := by
  dsimp only [execByteInstr]; rw [ifTrue h, bvEq_sound ht]

theorem exec_jcc_fall_eq {cc : Cond} {rel nr : BitVec 64} (target : BitVec 64)
    {ch : UndefChoice} {s : X64State}
    (h : evalCond cc s.flags = false) (ht : bvEq nr target = true) :
    execByteInstr (.jccRel cc rel) nr ch s = { s with rip := target } := by
  dsimp only [execByteInstr]; rw [h]; simp only [Bool.false_eq_true, ite_false, bvEq_sound ht]

theorem stepX64_of_halted (cmap : CodeMap) (ch : UndefChoice) (s : X64State)
    (h : s.halted = true) : stepX64 cmap ch s = s := by
  unfold stepX64; simp [h]

theorem runFrom_halted_const (cmap : CodeMap) (k idx : Nat) (nd : Nat → UndefChoice) (s : X64State)
    (h : s.halted = true) : runFrom cmap k idx nd s = s := by
  induction k generalizing idx with
  | zero => rfl
  | succ m ih => rw [runFrom_succ, stepX64_of_halted cmap (nd idx) s h, ih]

theorem exec_jmp_eq {rel nr target : BitVec 64} {ch : UndefChoice} {s : X64State}
    (ht : bvEq (nr + rel) target = true) :
    execByteInstr (.jmpRel rel) nr ch s = { s with rip := target } := by
  dsimp only [execByteInstr]; rw [bvEq_sound ht]

theorem exec_ret (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr .ret64 nr ch s = { s with halted := true } := rfl

theorem evalCond_ne_of_zf_true {f : RFlags} (h : f.zf = true) : evalCond .ne f = false := by
  dsimp [evalCond]; rw [h]; rfl

theorem evalCond_ne_of_zf_false {f : RFlags} (h : f.zf = false) : evalCond .ne f = true := by
  dsimp [evalCond]; rw [h]; rfl

theorem evalCond_e_of_zf_true {f : RFlags} (h : f.zf = true) : evalCond .e f = true := h

theorem evalCond_e_of_zf_false {f : RFlags} (h : f.zf = false) : evalCond .e f = false := h

theorem evalCond_a_of_flags {f : RFlags} : evalCond .a f = (!f.cf && !f.zf) := rfl

theorem evalCond_be_of_flags {f : RFlags} : evalCond .be f = (f.cf || f.zf) := rfl

theorem evalCond_b_of_flags {f : RFlags} : evalCond .b f = f.cf := rfl

theorem evalCond_ae_of_flags {f : RFlags} : evalCond .ae f = !f.cf := rfl

theorem step_at_concrete_eq {cmap : CodeMap} {rip : BitVec 64} (nextRip : BitVec 64) {ins : X64Instr} {len : Nat}
    (hdec : decodeX64 (fetchWindow16 cmap rip) = .ok ins len)
    (hnext : bvEq (rip + BitVec.ofNat 64 len) nextRip = true)
    (ch : UndefChoice) (s : X64State)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = rip) :
    stepX64 cmap ch s = execByteInstr ins nextRip ch s := by
  rw [step_at_concrete hdec ch s hrun hnf hrip, bvEq_sound hnext]

theorem rustFnv1a64From_def (m : ByteMem) (p : BitVec 64) (n : Nat) (acc : BitVec 64) :
    rustFnv1a64From m p n acc =
    Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
      (fun _ a => a) (fun _ ih q a => ih (q + 1#64) (fnv1aStep a (m q))) n p acc := rfl

theorem rustFnv1a64From_zero (m : ByteMem) (p acc : BitVec 64) :
    rustFnv1a64From m p 0 acc = acc := rfl

theorem rustFnv1a64From_succ (m : ByteMem) (p acc : BitVec 64) (n : Nat) :
    rustFnv1a64From m p (n + 1) acc = rustFnv1a64From m (p + 1#64) n (fnv1aStep acc (m p)) := by
  rw [rustFnv1a64From_def, rustFnv1a64From_def]

theorem rustChecksumRolFrom_def (m : ByteMem) (p : BitVec 64) (n : Nat) (acc : BitVec 32) :
    rustChecksumRolFrom m p n acc =
    Nat.rec (motive := fun _ => BitVec 64 → BitVec 32 → BitVec 32)
      (fun _ a => a) (fun _ ih q a => ih (q + 1#64) (rolXorStep a (m q))) n p acc := rfl

theorem rustChecksumRolFrom_zero (m : ByteMem) (p : BitVec 64) (acc : BitVec 32) :
    rustChecksumRolFrom m p 0 acc = acc := rfl

theorem rustChecksumRolFrom_succ (m : ByteMem) (p : BitVec 64) (acc : BitVec 32) (n : Nat) :
    rustChecksumRolFrom m p (n + 1) acc = rustChecksumRolFrom m (p + 1#64) n (rolXorStep acc (m p)) := by
  rw [rustChecksumRolFrom_def, rustChecksumRolFrom_def]

theorem rustAdler32Loop_def (m : ByteMem) (p : BitVec 64) (n : Nat) (a b : BitVec 32) :
    rustAdler32Loop m p n a b =
    Nat.rec (motive := fun _ => BitVec 64 → BitVec 32 × BitVec 32 → BitVec 32 × BitVec 32)
      (fun _ ab => ab) (fun _ ih q ab => ih (q + 1#64) (adlerStep ab (m q))) n p (a, b) := rfl

theorem rustAdler32Loop_zero (m : ByteMem) (p : BitVec 64) (a b : BitVec 32) :
    rustAdler32Loop m p 0 a b = (a, b) := rfl

theorem rustAdler32Loop_succ (m : ByteMem) (p : BitVec 64) (a b : BitVec 32) (n : Nat) :
    rustAdler32Loop m p (n + 1) a b =
      let ab := adlerStep (a, b) (m p)
      rustAdler32Loop m (p + 1#64) n ab.1 ab.2 := by
  rw [rustAdler32Loop_def, rustAdler32Loop_def]

theorem rustDotU8U16From_def (m : ByteMem) (pa pb : BitVec 64) (n : Nat) (s : BitVec 32) :
    rustDotU8U16From m pa pb n s =
    Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 32 → BitVec 32)
      (fun _ _ acc => acc)
      (fun _ ih qa qb acc => ih (qa + 1#64) (qb + 2#64) (dotStepU8U16 acc (m qa) (readMem16 m qb)))
      n pa pb s := rfl

theorem rustDotU8U16From_zero (m : ByteMem) (pa pb : BitVec 64) (s : BitVec 32) :
    rustDotU8U16From m pa pb 0 s = s := rfl

theorem rustDotU8U16From_succ (m : ByteMem) (pa pb : BitVec 64) (s : BitVec 32) (n : Nat) :
    rustDotU8U16From m pa pb (n + 1) s =
      rustDotU8U16From m (pa + 1#64) (pb + 2#64) n (dotStepU8U16 s (m pa) (readMem16 m pb)) := by
  rw [rustDotU8U16From_def, rustDotU8U16From_def]

theorem rustSumU8From_def (m : ByteMem) (p : BitVec 64) (n : Nat) (acc : BitVec 64) :
    rustSumU8From m p n acc =
    Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
      (fun _ a => a) (fun _ ih q a => ih (q + 1#64) (a + (m q).zeroExtend 64)) n p acc := rfl

theorem rustSumU8From_zero (m : ByteMem) (p acc : BitVec 64) :
    rustSumU8From m p 0 acc = acc := rfl

theorem rustSumU8From_succ (m : ByteMem) (p acc : BitVec 64) (n : Nat) :
    rustSumU8From m p (n + 1) acc = rustSumU8From m (p + 1#64) n (acc + (m p).zeroExtend 64) := by
  rw [rustSumU8From_def, rustSumU8From_def]

end UntrustedCObjHints
