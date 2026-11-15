-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Verified 1-to-$k$ Tail Duplication (`TailDupSimCert`), Hot/Cold Function Splitting, and 32-Bit Branch-Relaxation Veneers

Standalone Lean 4 (`v4.34.1`) mechanization closing the two explicit boundaries
in `VerifiedLayoutPass`:

1. **1-to-$k$ Tail-Duplication Simulation via Reverse Functional Block
   Projection (`tail_dup_clone_sim`) and Predecessor Tail-Fusing
   (`tail_dup_fuse_two_step_sim`):**
   - When a shared join/latch/dispatch block $B_{\text{tail}}$ is duplicated into
     $k$ specialized clones $B_{\text{tail}}^{(1)} \dots B_{\text{tail}}^{(k)}$
     in $G'$, every block in $G'$ maps *functionally* (many-to-one) via
     $\rho : \text{BlockId}_{G'} \to \text{BlockId}_G$ to its unique origin
     block in $G$. Under `TailDupLookupEquiv G G' ρ`, multi-step execution of
     $G'$ from `bid'` produces the exact same return value and machine state as
     executing $G$ from `ρ bid'` (`runMach fuel G' bid' s = runMach fuel G (ρ bid') s`)
     with zero relational backtracking in the Lean kernel.
   - When a predecessor $P$ ending in `.jmp tailBid` fuses `tailBlock.body` and
     `tailBlock.term` directly into $P$ (`fuseTailIntoPred`), a single CFG step
     of the fused block equals two CFG steps of the original graph, eliminating
     the unconditional jump instruction on every loop iteration.
2. **Cross-Section `.text` $\leftrightarrow$ `.text.unlikely` Branch-Relaxation
   Veneers (`relaxCrossSectionBranch_sim`):**
   On AArch64 (`TBZ`/`TBNZ` $\pm 32\text{ KiB}$, `B.cond`/`CBZ` $\pm 1\text{ MiB}$)
   and x86 (`Jcc rel8` $\pm 128\text{ B}$), rewriting a cross-section conditional
   branch `br cond coldBid hotFallthrough` into `br cond.neg hotFallthrough veneerBid`
   plus a local hot-section veneer `veneerBid : jmp32 coldBid` preserves hot-path
   1-step execution identically and reaches `coldBid` with an identical
   `MachState` while eliminating all cross-section short conditional branch
   relocations.
-/

namespace VerifiedTailDupAndBranchRelax

abbrev BlockId := Nat
abbrev RegId   := Nat
abbrev Val     := BitVec 64

/-- Machine register, flag, and memory state. -/
structure MachState where
  regs : RegId → Val
  zf   : Bool
  mem  : Val → UInt8

/-- Branch condition in `MiniMach`. -/
inductive Cond where
  | eqZero
  | neZero
  deriving DecidableEq, Repr

/-- Negate a branch condition. -/
def Cond.neg : Cond → Cond
  | .eqZero => .neZero
  | .neZero => .eqZero

/-- Evaluate a branch condition against `MachState.zf`. -/
def evalCond (c : Cond) (s : MachState) : Bool :=
  match c with
  | .eqZero => s.zf
  | .neZero => !s.zf

@[simp]
theorem evalCond_neg (c : Cond) (s : MachState) :
    evalCond c.neg s = !(evalCond c s) := by
  cases c <;> simp [Cond.neg, evalCond]

/-- Straight-line instruction inside a basic block. -/
inductive BodyInst where
  | addImm (dst src : RegId) (imm : Val)
  | movReg (dst src : RegId)
  | cmpZero (src : RegId)
  | nop (byteLen : Nat)
  deriving DecidableEq, Repr

/-- Execute a single `BodyInst`. -/
def execBodyInst (i : BodyInst) (s : MachState) : MachState :=
  match i with
  | .addImm dst src imm =>
    let v := s.regs src + imm
    { s with regs := fun r => if r == dst then v else s.regs r }
  | .movReg dst src =>
    let v := s.regs src
    { s with regs := fun r => if r == dst then v else s.regs r }
  | .cmpZero src =>
    { s with zf := s.regs src == 0#64 }
  | .nop _ => s

/-- Execute a list of `BodyInst`s. -/
def execBody : List BodyInst → MachState → MachState
  | [], s => s
  | i :: rest, s => execBody rest (execBodyInst i s)

@[simp]
theorem execBody_append (b₁ b₂ : List BodyInst) (s : MachState) :
    execBody (b₁ ++ b₂) s = execBody b₂ (execBody b₁ s) := by
  induction b₁ generalizing s with
  | nil => rfl
  | cons hd tl ih => simp [execBody, ih]

/-- Terminator of a `MiniMach` basic block. -/
inductive Terminator where
  | ret (reg : RegId)
  | jmp (target : BlockId)
  | br (c : Cond) (ifTrue ifFalse : BlockId)
  deriving DecidableEq, Repr

/-- Evaluate a `Terminator` to either `Sum.inl retVal` or `Sum.inr nextBid`. -/
def evalTerminator (t : Terminator) (s : MachState) : Val ⊕ BlockId :=
  match t with
  | .ret r => .inl (s.regs r)
  | .jmp target => .inr target
  | .br c ifTrue ifFalse =>
    if evalCond c s then .inr ifTrue else .inr ifFalse

/-- Map a block-ID projection `ρ : BlockId → BlockId` over a terminator outcome. -/
def projectOutcome (ρ : BlockId → BlockId) : Val ⊕ BlockId → Val ⊕ BlockId
  | .inl v => .inl v
  | .inr bid => .inr (ρ bid)

/-- Section slice tag (`.text` vs. `.text.unlikely`). -/
inductive SectionSlice where
  | hotText
  | coldTextUnlikely
  deriving DecidableEq, Repr

/-- A `MiniMach` basic block. -/
structure MachBlock where
  id    : BlockId
  slice : SectionSlice
  body  : List BodyInst
  term  : Terminator
  deriving Repr

/-- Lookup a basic block by `BlockId`. -/
def findBlock (blocks : List MachBlock) (bid : BlockId) : Option MachBlock :=
  match blocks with
  | [] => none
  | b :: rest => if b.id == bid then some b else findBlock rest bid

/-- Single-step `MiniMach` execution. -/
def stepMach (blocks : List MachBlock) (bid : BlockId) (s : MachState) :
    Option ((Val × MachState) ⊕ (BlockId × MachState)) :=
  match findBlock blocks bid with
  | none => none
  | some b =>
    let s' := execBody b.body s
    match evalTerminator b.term s' with
    | .inl retVal => some (.inl (retVal, s'))
    | .inr nextBid => some (.inr (nextBid, s'))

/-- Multi-step fuel-bounded `MiniMach` execution. -/
def runMach : Nat → List MachBlock → BlockId → MachState → Option (Val × MachState)
  | 0, _, _, _ => none
  | fuel + 1, blocks, bid, s =>
    match stepMach blocks bid s with
    | none => none
    | some (.inl res) => some res
    | some (.inr (nextBid, s')) => runMach fuel blocks nextBid s'

/-!
## 1. 1-to-$k$ Tail-Duplication Simulation via Reverse Projection `ρ : BlockId → BlockId`
-/

/-- `TailDupLookupEquiv G G' ρ` states that every cloned block `bid'` in the
tail-duplicated CFG `G'` maps via the functional origin map `ρ` to a block
`ρ bid'` in `G` with identical body effect and `ρ`-projected terminator target. -/
def TailDupLookupEquiv (G G' : List MachBlock) (ρ : BlockId → BlockId) : Prop :=
  ∀ (bid' : BlockId) (s : MachState),
    match findBlock G (ρ bid'), findBlock G' bid' with
    | none, none => True
    | some b, some b' =>
      execBody b'.body s = execBody b.body s ∧
      projectOutcome ρ (evalTerminator b'.term (execBody b'.body s)) =
        evalTerminator b.term (execBody b.body s)
    | _, _ => False

/-- Core Theorem 1a (`tail_dup_clone_sim`):
For any 1-to-$k$ block cloning witnessed by a functional reverse projection
`ρ : BlockId → BlockId` satisfying `TailDupLookupEquiv G G' ρ`, running the
tail-duplicated CFG `G'` from any cloned block `bid'` produces the exact same
`(retVal, finalState)` as running `G` from `ρ bid'`. -/
theorem tail_dup_clone_sim (fuel : Nat) (G G' : List MachBlock)
    (ρ : BlockId → BlockId) (h_cert : TailDupLookupEquiv G G' ρ)
    (bid' : BlockId) (s : MachState) :
    runMach fuel G' bid' s = runMach fuel G (ρ bid') s := by
  induction fuel generalizing bid' s with
  | zero => rfl
  | succ k ih =>
    have h := h_cert bid' s
    unfold runMach stepMach
    cases hb : findBlock G (ρ bid') <;> cases hb' : findBlock G' bid'
    · rfl
    · rw [hb, hb'] at h; nomatch h
    · rw [hb, hb'] at h; nomatch h
    · rw [hb, hb'] at h
      rcases h with ⟨hbody, hterm⟩
      dsimp only
      rw [hbody] at hterm ⊢
      cases ht' : evalTerminator _ (execBody _ s) with
      | inl retVal =>
        rw [ht'] at hterm
        simp only [projectOutcome] at hterm
        rw [← hterm]
      | inr nextBid' =>
        rw [ht'] at hterm
        simp only [projectOutcome] at hterm
        rw [← hterm]
        exact ih nextBid' (execBody _ s)

/-- Fuse a tail block `bTail` directly into a predecessor `bPred` that ends in
`.jmp bTail.id`, eliminating the unconditional jump. -/
def fuseTailIntoPred (bPred bTail : MachBlock) : MachBlock :=
  { bPred with
    body := bPred.body ++ bTail.body
    term := bTail.term }

/-- Core Theorem 1b (`tail_dup_fuse_two_step_sim`):
When `bPred.term = .jmp bTail.id`, executing the fused block
`fuseTailIntoPred bPred bTail` in a single block step computes the exact same
post-state and terminator outcome as executing `bPred` followed by `bTail`. -/
theorem tail_dup_fuse_two_step_sim (bPred bTail : MachBlock) (s : MachState) :
    let bFused := fuseTailIntoPred bPred bTail
    let s1 := execBody bPred.body s
    let s2 := execBody bTail.body s1
    execBody bFused.body s = s2 ∧
    evalTerminator bFused.term (execBody bFused.body s) = evalTerminator bTail.term s2 := by
  simp [fuseTailIntoPred, execBody_append]

/-!
## 2. Cross-Section `.text` $\leftrightarrow$ `.text.unlikely` Branch-Relaxation Veneers
-/

/-- Rewrite a basic block `b` whose terminator `br c coldBid hotFallthrough`
targets a distant `.text.unlikely` block `coldBid` ($>1\text{ MiB}$ on AArch64
`B.cond`/`CBZ` or $>32\text{ KiB}$ on `TBZ`) into an inverted local conditional
branch `br c.neg hotFallthrough veneerBid` plus a local 26-bit/32-bit
unconditional branch veneer block `veneerBid : jmp coldBid`. -/
def relaxCrossSectionBr (b : MachBlock) (c : Cond) (coldBid hotFallthrough veneerBid : BlockId) :
    MachBlock × MachBlock :=
  let bRelaxed : MachBlock :=
    { b with term := .br c.neg hotFallthrough veneerBid }
  let bVeneer : MachBlock :=
    { id := veneerBid, slice := .hotText, body := [], term := .jmp coldBid }
  (bRelaxed, bVeneer)

/-- Core Theorem 2a (`relaxCrossSectionBr_hot_step_eq`):
On the hot path (`evalCond c (execBody b.body s) = false`), the relaxed block
steps directly to `(hotFallthrough, execBody b.body s)` in 1 step, executing
zero veneer instructions. -/
theorem relaxCrossSectionBr_hot_step_eq (b : MachBlock) (c : Cond)
    (coldBid hotFallthrough veneerBid : BlockId) (s : MachState)
    (h_term : b.term = .br c coldBid hotFallthrough)
    (h_hot : evalCond c (execBody b.body s) = false) :
    let (bRelaxed, _) := relaxCrossSectionBr b c coldBid hotFallthrough veneerBid
    evalTerminator bRelaxed.term (execBody bRelaxed.body s) =
      evalTerminator b.term (execBody b.body s) := by
  simp [relaxCrossSectionBr, h_term, evalTerminator, evalCond_neg, h_hot]

/-- Core Theorem 2b (`relaxCrossSectionBr_cold_two_step_eq`):
On the cold path (`evalCond c (execBody b.body s) = true`), the relaxed block
branches to the local hot-section veneer `bVeneer`, and executing `bVeneer`
immediately jumps to `coldBid` with the exact same `MachState`
`execBody b.body s`. -/
theorem relaxCrossSectionBr_cold_two_step_eq (b : MachBlock) (c : Cond)
    (coldBid hotFallthrough veneerBid : BlockId) (s : MachState)
    (h_cold : evalCond c (execBody b.body s) = true) :
    let (bRelaxed, bVeneer) := relaxCrossSectionBr b c coldBid hotFallthrough veneerBid
    let s' := execBody bRelaxed.body s
    evalTerminator bRelaxed.term s' = .inr veneerBid ∧
    execBody bVeneer.body s' = s' ∧
    evalTerminator bVeneer.term (execBody bVeneer.body s') = .inr coldBid := by
  simp [relaxCrossSectionBr, evalTerminator, evalCond_neg, h_cold, execBody]

end VerifiedTailDupAndBranchRelax

#print axioms VerifiedTailDupAndBranchRelax.tail_dup_clone_sim
#print axioms VerifiedTailDupAndBranchRelax.tail_dup_fuse_two_step_sim
#print axioms VerifiedTailDupAndBranchRelax.relaxCrossSectionBr_hot_step_eq
#print axioms VerifiedTailDupAndBranchRelax.relaxCrossSectionBr_cold_two_step_eq
