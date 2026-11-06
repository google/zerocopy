-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Stage 3 Verification Architecture & Kernel Reduction Scaling Benchmark Suite

This self-contained Lean 4 module empirically benchmarks the three candidate
Stage 3 verification architectures for Anneal's MIR pipeline across both
`leanprover/lean4:v4.28.0` (and `v4.28.0-rc1`) and `leanprover/lean4:v4.34.1`:

1. **Architecture A — Unjoined Tree-Unrolled Small-Step Deduction:**
   Recursively splits on each branch in a $K$-diamond CFG without join-point
   state canonicalization or `execNormal_join` merging, demonstrating
   exponential $\Theta(2^K)$ growth in proof term size, tactic elaboration, and
   kernel type-checking time.
2. **Architecture B — Block-Modular Symbolic Execution (`execNormal_join` +
   Canonicalized State):**
   Canonicalizes dead branch temporaries via `Stmt.storageDead` (setting dead
   locals to `none`) and merges diamond arms at each reconvergence block via
   `execNormal_join` / `execNormal_diamond_step`, achieving linear $\Theta(K)$
   scaling in diamond count while exposing per-statement tactic elaboration and
   proof-term linear overhead on $N$-statement chains ($N \in \{16, 32, 64, 128\}$).
3. **Architecture C — Total Computational Reflection (`checkBodySym` +
   `checkBodySym_sound`):**
   Verifies a total boolean symbolic/abstract evaluator `checkBodySym` once and
   discharges individual functions by a single `rfl` kernel reduction with a
   constant-size proof term (`dag_objs = 30`, `tree_nodes = 43`).
4. **Kernel WHNF Environment Representation Benchmark (`ClosureLocals` vs.
   `ListLocals`):**
   Compares `Trusted/MirSemantics.lean`'s closure-based local environment
   (`Nat → Option Nat`, which accumulates $O(N)$ nested lambda closures and
   incurs $\Theta(N^2)$ kernel WHNF reduction, exceeding default `maxRecDepth`
   at $N = 200$) against a spine-strict `List (Option Nat)` environment
   ($\Theta(N \cdot L)$ linear kernel WHNF reduction).
-/

namespace AnnealBench

-- ============================================================================
-- Section 1: Core Lowered MIR AST & Operational Semantics
-- ============================================================================

abbrev LocalEnv := List (Option Nat)

def getLocal : LocalEnv → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getLocal xs i

def setLocal : LocalEnv → Nat → Option Nat → Option LocalEnv
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setLocal xs i v with
    | some xs' => some (x :: xs')
    | none => none

inductive Stmt where
  | assignConst (dst : Nat) (val : Nat)
  | assignAddConst (dst : Nat) (src : Nat) (c : Nat)
  | storageDead (dst : Nat)
  deriving DecidableEq, Repr

def evalStmt (st : Stmt) (env : LocalEnv) : Option LocalEnv :=
  match st with
  | .assignConst dst val => setLocal env dst (some val)
  | .assignAddConst dst src c =>
    match getLocal env src with
    | some v => setLocal env dst (some (v + c))
    | none => none
  | .storageDead dst => setLocal env dst none

def evalStmts : List Stmt → LocalEnv → Option LocalEnv
  | [], env => some env
  | st :: rest, env =>
    match evalStmt st env with
    | some env' => evalStmts rest env'
    | none => none

inductive Term where
  | ret
  | goto (target : Nat)
  | branch (bit : Nat) (tTarget : Nat) (fTarget : Nat)
  deriving DecidableEq, Repr

structure BasicBlock where
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr

abbrev MirBody := List BasicBlock

def getBlock : MirBody → Nat → Option BasicBlock
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: bs, i + 1 => getBlock bs i

structure MirState where
  bb : Nat
  locals : LocalEnv
  deriving DecidableEq, Repr

/-- Small-step normal execution reaching a `ret` terminator satisfying `post`. -/
inductive ExecNormal (b : MirBody) (oracle : Nat → Bool) :
    MirState → (MirState → Prop) → Prop where
  | ret {s : MirState} {stmts : List Stmt} {locals' : LocalEnv} {post : MirState → Prop} :
      getBlock b s.bb = some { stmts := stmts, term := .ret } →
      evalStmts stmts s.locals = some locals' →
      post { bb := s.bb, locals := locals' } →
      ExecNormal b oracle s post
  | goto {s : MirState} {stmts : List Stmt} {target : Nat}
      {locals' : LocalEnv} {post : MirState → Prop} :
      getBlock b s.bb = some { stmts := stmts, term := .goto target } →
      evalStmts stmts s.locals = some locals' →
      ExecNormal b oracle { bb := target, locals := locals' } post →
      ExecNormal b oracle s post
  | branch {s : MirState} {stmts : List Stmt} {bit tTarget fTarget : Nat}
      {locals' : LocalEnv} {post : MirState → Prop} :
      getBlock b s.bb = some { stmts := stmts, term := .branch bit tTarget fTarget } →
      evalStmts stmts s.locals = some locals' →
      ExecNormal b oracle
        { bb := if oracle bit then tTarget else fTarget, locals := locals' } post →
      ExecNormal b oracle s post

/-- Bounded multi-block execution reaching an intermediate cut/join predicate `mid`. -/
inductive ExecPath (b : MirBody) (oracle : Nat → Bool) :
    MirState → (MirState → Prop) → Prop where
  | reach {s : MirState} {mid : MirState → Prop} :
      mid s → ExecPath b oracle s mid
  | goto {s : MirState} {stmts : List Stmt} {target : Nat}
      {locals' : LocalEnv} {mid : MirState → Prop} :
      getBlock b s.bb = some { stmts := stmts, term := .goto target } →
      evalStmts stmts s.locals = some locals' →
      ExecPath b oracle { bb := target, locals := locals' } mid →
      ExecPath b oracle s mid
  | branch {s : MirState} {stmts : List Stmt} {bit tTarget fTarget : Nat}
      {locals' : LocalEnv} {mid : MirState → Prop} :
      getBlock b s.bb = some { stmts := stmts, term := .branch bit tTarget fTarget } →
      evalStmts stmts s.locals = some locals' →
      ExecPath b oracle
        { bb := if oracle bit then tTarget else fTarget, locals := locals' } mid →
      ExecPath b oracle s mid

/-- Whole-body safety obligation universally quantified over branch choices. -/
def BodySafe (b : MirBody) (initLocals : LocalEnv) : Prop :=
  ∀ (oracle : Nat → Bool),
    ExecNormal b oracle { bb := 0, locals := initLocals } (fun _ => True)

-- ============================================================================
-- Section 2: Structural Deduction Rules (Architectures A and B)
-- ============================================================================

/-- Architecture A's unjoined branch split rule: duplicates the continuation
    proof across `tTarget` and `fTarget` without merging at the join block. -/
theorem execNormal_branch_split {b : MirBody} {oracle : Nat → Bool}
    {bb bit tTarget fTarget : Nat} {stmts : List Stmt}
    {locals locals' : LocalEnv} {post : MirState → Prop}
    (hHdr : getBlock b bb = some { stmts := stmts, term := .branch bit tTarget fTarget })
    (hEval : evalStmts stmts locals = some locals')
    (hT : ExecNormal b oracle { bb := tTarget, locals := locals' } post)
    (hF : ExecNormal b oracle { bb := fTarget, locals := locals' } post) :
    ExecNormal b oracle { bb := bb, locals := locals } post := by
  apply ExecNormal.branch hHdr hEval
  cases oracle bit
  · exact hF
  · exact hT

/-- Architecture B's compositional join rule (`execNormal_join`): composes a
    multi-block path reaching cut predicate `mid` with a single continuation
    proof from `mid` to `post`. -/
theorem execNormal_join {b : MirBody} {oracle : Nat → Bool} {s : MirState}
    {mid post : MirState → Prop}
    (h1 : ExecPath b oracle s mid)
    (h2 : ∀ s', mid s' → ExecNormal b oracle s' post) :
    ExecNormal b oracle s post := by
  induction h1 with
  | reach hmid => exact h2 _ hmid
  | goto hblk heval _ ih => exact ExecNormal.goto hblk heval (ih h2)
  | branch hblk heval _ ih => exact ExecNormal.branch hblk heval (ih h2)

theorem execNormal_join_eq {b : MirBody} {oracle : Nat → Bool}
    {s joinState : MirState} {post : MirState → Prop}
    (h1 : ExecPath b oracle s (fun s' => s' = joinState))
    (h2 : ExecNormal b oracle joinState post) :
    ExecNormal b oracle s post :=
  execNormal_join h1 (fun _ hEq => hEq ▸ h2)

/-- Block-modular diamond step derived from `execNormal_join_eq`: proves both
    arms of a diamond once to a common canonicalized `joinLocals` at `joinBb`,
    then continues linearly from `{ bb := joinBb, locals := joinLocals }`. -/
theorem execNormal_diamond_step {b : MirBody} {oracle : Nat → Bool}
    {bb bit tTarget fTarget joinBb : Nat}
    {stmts tStmts fStmts : List Stmt}
    {locals midLocals joinLocals : LocalEnv}
    {post : MirState → Prop}
    (hHdr : getBlock b bb = some { stmts := stmts, term := .branch bit tTarget fTarget })
    (hHdrEval : evalStmts stmts locals = some midLocals)
    (hT : getBlock b tTarget = some { stmts := tStmts, term := .goto joinBb })
    (hTEval : evalStmts tStmts midLocals = some joinLocals)
    (hF : getBlock b fTarget = some { stmts := fStmts, term := .goto joinBb })
    (hFEval : evalStmts fStmts midLocals = some joinLocals)
    (hCont : ExecNormal b oracle { bb := joinBb, locals := joinLocals } post) :
    ExecNormal b oracle { bb := bb, locals := locals } post := by
  refine execNormal_join_eq ?_ hCont
  apply ExecPath.branch hHdr hHdrEval
  cases oracle bit
  · exact ExecPath.goto hF hFEval (ExecPath.reach rfl)
  · exact ExecPath.goto hT hTEval (ExecPath.reach rfl)

-- ============================================================================
-- Section 3: Architecture C — Total Computational Reflection (`checkBodySym`)
-- ============================================================================

def checkDiamondJoin (b : MirBody) (tTarget fTarget : Nat) (locals' : LocalEnv) :
    Option MirState :=
  match getBlock b tTarget, getBlock b fTarget with
  | some tBlk, some fBlk =>
    match tBlk.term, fBlk.term with
    | .goto tNext, .goto fNext =>
      match evalStmts tBlk.stmts locals', evalStmts fBlk.stmts locals' with
      | some tLocs, some fLocs =>
        if tNext == fNext && tLocs == fLocs then
          some { bb := tNext, locals := tLocs }
        else
          none
      | _, _ => none
    | _, _ => none
  | _, _ => none

theorem checkDiamondJoin_sound {b : MirBody} {oracle : Nat → Bool}
    {bb bit tTarget fTarget : Nat} {stmts : List Stmt}
    {locals locals' : LocalEnv} {joinState : MirState} {post : MirState → Prop}
    (hHdr : getBlock b bb = some { stmts := stmts, term := .branch bit tTarget fTarget })
    (hHdrEval : evalStmts stmts locals = some locals')
    (hJoin : checkDiamondJoin b tTarget fTarget locals' = some joinState)
    (hCont : ExecNormal b oracle joinState post) :
    ExecNormal b oracle { bb := bb, locals := locals } post := by
  unfold checkDiamondJoin at hJoin
  cases hTBlk : getBlock b tTarget with
  | none => simp [hTBlk] at hJoin
  | some tBlk =>
    cases hFBlk : getBlock b fTarget with
    | none => simp [hTBlk, hFBlk] at hJoin
    | some fBlk =>
      simp only [hTBlk, hFBlk] at hJoin
      cases hTTerm : tBlk.term with
      | ret => simp [hTTerm] at hJoin
      | branch _ _ _ => simp [hTTerm] at hJoin
      | goto tNext =>
        cases hFTerm : fBlk.term with
        | ret => simp [hTTerm, hFTerm] at hJoin
        | branch _ _ _ => simp [hTTerm, hFTerm] at hJoin
        | goto fNext =>
          simp only [hTTerm, hFTerm] at hJoin
          cases hTEval : evalStmts tBlk.stmts locals' with
          | none => simp [hTEval] at hJoin
          | some tLocs =>
            cases hFEval : evalStmts fBlk.stmts locals' with
            | none => simp [hTEval, hFEval] at hJoin
            | some fLocs =>
              simp only [hTEval, hFEval] at hJoin
              split at hJoin
              · rename_i hCond
                simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hCond hJoin
                rcases hCond with ⟨rfl, rfl⟩
                subst hJoin
                have hTFull : getBlock b tTarget = some { stmts := tBlk.stmts, term := .goto tNext } := by
                  cases tBlk; subst hTTerm; exact hTBlk
                have hFFull : getBlock b fTarget = some { stmts := fBlk.stmts, term := .goto tNext } := by
                  cases fBlk; subst hFTerm; exact hFBlk
                exact execNormal_diamond_step hHdr hHdrEval hTFull hTEval hFFull hFEval hCont
              · contradiction

/-- Total boolean symbolic/abstract evaluator with diamond join merging. -/
def checkBodySym : Nat → MirBody → MirState → Bool
  | 0, _, _ => false
  | fuel + 1, b, s =>
    match getBlock b s.bb with
    | none => false
    | some blk =>
      match evalStmts blk.stmts s.locals with
      | none => false
      | some locals' =>
        match blk.term with
        | .ret => true
        | .goto target => checkBodySym fuel b { bb := target, locals := locals' }
        | .branch _ tTarget fTarget =>
          match checkDiamondJoin b tTarget fTarget locals' with
          | some joinState => checkBodySym fuel b joinState
          | none =>
            checkBodySym fuel b { bb := tTarget, locals := locals' } &&
            checkBodySym fuel b { bb := fTarget, locals := locals' }

/-- Soundness theorem for Architecture C: reduces `BodySafe b initLocals` to a
    single boolean reflection equation `checkBodySym fuel b s = true`. -/
theorem checkBodySym_sound :
    ∀ (fuel : Nat) (b : MirBody) (s : MirState),
      checkBodySym fuel b s = true →
      ∀ (oracle : Nat → Bool), ExecNormal b oracle s (fun _ => True)
  | 0, _, _, h, _ => by contradiction
  | fuel + 1, b, s, h, oracle => by
    unfold checkBodySym at h
    cases hBlk : getBlock b s.bb with
    | none => simp [hBlk] at h
    | some blk =>
      cases hEval : evalStmts blk.stmts s.locals with
      | none => simp [hBlk, hEval] at h
      | some locals' =>
        simp only [hBlk, hEval] at h
        cases hTerm : blk.term with
        | ret =>
          have hBlkFull : getBlock b s.bb = some { stmts := blk.stmts, term := .ret } := by
            cases blk; subst hTerm; exact hBlk
          exact ExecNormal.ret hBlkFull hEval trivial
        | goto target =>
          simp only [hTerm] at h
          have hBlkFull : getBlock b s.bb = some { stmts := blk.stmts, term := .goto target } := by
            cases blk; subst hTerm; exact hBlk
          exact ExecNormal.goto hBlkFull hEval
            (checkBodySym_sound fuel b { bb := target, locals := locals' } h oracle)
        | branch bit tTarget fTarget =>
          simp only [hTerm] at h
          have hBlkFull : getBlock b s.bb = some { stmts := blk.stmts, term := .branch bit tTarget fTarget } := by
            cases blk; subst hTerm; exact hBlk
          cases hJoin : checkDiamondJoin b tTarget fTarget locals' with
          | some joinState =>
            simp only [hJoin] at h
            exact checkDiamondJoin_sound hBlkFull hEval hJoin
              (checkBodySym_sound fuel b joinState h oracle)
          | none =>
            simp only [hJoin, Bool.and_eq_true] at h
            apply ExecNormal.branch hBlkFull hEval
            cases oracle bit
            · exact checkBodySym_sound fuel b { bb := fTarget, locals := locals' } h.2 oracle
            · exact checkBodySym_sound fuel b { bb := tTarget, locals := locals' } h.1 oracle

-- ============================================================================
-- Section 4: Synthetic CFG Families & Proof Tactics
-- ============================================================================

/-- Synthetic $K$-diamond CFG where each diamond arm writes a branch-local
    temporary (`local 1`) and then clears it via `Stmt.storageDead 1` so both
    arms converge to the same canonicalized `LocalEnv` at block `3*d + 3`. -/
def mkDiamondBlocks (k : Nat) : List BasicBlock :=
  let rec loop (d : Nat) (acc : List BasicBlock) : List BasicBlock :=
    match d with
    | 0 => acc
    | rem + 1 =>
      let idx := k - 1 - rem
      let base := 3 * idx
      let hdr : BasicBlock := {
        stmts := [.assignAddConst 0 0 1],
        term := .branch idx (base + 1) (base + 2)
      }
      let tArm : BasicBlock := {
        stmts := [.assignConst 1 (idx + 1), .assignAddConst 0 0 2, .storageDead 1],
        term := .goto (base + 3)
      }
      let fArm : BasicBlock := {
        stmts := [.assignConst 1 (idx + 100), .assignAddConst 0 0 2, .storageDead 1],
        term := .goto (base + 3)
      }
      loop rem (acc ++ [hdr, tArm, fArm])
  loop k [] ++ [{ stmts := [.assignConst 1 0], term := .ret }]

/-- Uncanonicalized $K$-diamond CFG omitting `Stmt.storageDead 1`, leaving
    distinct dead temporary values in `local 1` along each of the $2^K$ paths. -/
def mkDiamondUncanonBlocks (k : Nat) : List BasicBlock :=
  let rec loop (d : Nat) (acc : List BasicBlock) : List BasicBlock :=
    match d with
    | 0 => acc
    | rem + 1 =>
      let idx := k - 1 - rem
      let base := 3 * idx
      let hdr : BasicBlock := {
        stmts := [.assignAddConst 0 0 1],
        term := .branch idx (base + 1) (base + 2)
      }
      let tArm : BasicBlock := {
        stmts := [.assignAddConst 1 1 1, .assignAddConst 0 0 2],
        term := .goto (base + 3)
      }
      let fArm : BasicBlock := {
        stmts := [.assignAddConst 1 1 2, .assignAddConst 0 0 2],
        term := .goto (base + 3)
      }
      loop rem (acc ++ [hdr, tArm, fArm])
  loop k [] ++ [{ stmts := [.assignConst 1 0], term := .ret }]

/-- Straight-line $N$-block chain CFG for measuring per-step symbolic execution
    scaling across $N \in \{16, 32, 64, 128\}$. -/
def mkChainBlocks (n : Nat) : List BasicBlock :=
  (List.range n).map (fun i => {
    stmts := [.assignAddConst 0 0 1],
    term := .goto (i + 1)
  }) ++ [{ stmts := [.assignConst 1 0], term := .ret }]

def defaultInitLocals : LocalEnv := [some 0, some 0]

syntax "step_arch_a" : tactic
macro_rules
  | `(tactic| step_arch_a) =>
    `(tactic|
      first
      | exact ExecNormal.ret rfl rfl trivial
      | (refine ExecNormal.goto rfl rfl ?_; step_arch_a)
      | (refine execNormal_branch_split rfl rfl ?_ ?_ <;> step_arch_a))

syntax "step_arch_b_diamond" : tactic
macro_rules
  | `(tactic| step_arch_b_diamond) =>
    `(tactic|
      first
      | exact ExecNormal.ret rfl rfl trivial
      | (refine execNormal_diamond_step rfl rfl rfl rfl rfl rfl ?_; step_arch_b_diamond))

syntax "step_arch_b_chain" : tactic
macro_rules
  | `(tactic| step_arch_b_chain) =>
    `(tactic|
      first
      | exact ExecNormal.ret rfl rfl trivial
      | (refine ExecNormal.goto rfl rfl ?_; step_arch_b_chain))

-- ============================================================================
-- Section 5: Kernel WHNF Environment Representation Benchmark
--            (ClosureLocals `Nat → Option Nat` vs. Spine-Strict `ListLocals`)
-- ============================================================================

structure AssignStmt where
  dst : Nat
  src1 : Nat
  src2 : Nat

/-- Generates $N$ sequential binary-addition assignments over $L = 16$ locals,
    reading function parameter `local 0` (initialized once at entry) and the
    most recently updated local `1 + ((k + 14) % 15)`. -/
def mkEnvBenchStmts (n : Nat) : List AssignStmt :=
  (List.range n).map (fun k =>
    { dst := 1 + (k % 15), src1 := 0, src2 := 1 + ((k + 14) % 15) })

abbrev ClosureLocals := Nat → Option Nat

def updateClosure (env : ClosureLocals) (k : Nat) (v : Option Nat) : ClosureLocals :=
  fun i => if i == k then v else env i

def evalStmtsClosure (stmts : List AssignStmt) (env : ClosureLocals) : Option ClosureLocals :=
  match stmts with
  | [] => some env
  | st :: rest =>
    match env st.src1, env st.src2 with
    | some v1, some v2 =>
      evalStmtsClosure rest (updateClosure env st.dst (some (v1 + v2 + 1)))
    | _, _ => none

def checkClosureEnv (n : Nat) : Bool :=
  let init : ClosureLocals := fun i => if i < 16 then some 1 else none
  match evalStmtsClosure (mkEnvBenchStmts n) init with
  | some finalEnv =>
    (finalEnv 0).isSome && (finalEnv 1).isSome && (finalEnv 8).isSome && (finalEnv 15).isSome
  | none => false

def evalStmtsList (stmts : List AssignStmt) (env : LocalEnv) : Option LocalEnv :=
  match stmts with
  | [] => some env
  | st :: rest =>
    match getLocal env st.src1, getLocal env st.src2 with
    | some v1, some v2 =>
      match setLocal env st.dst (some (v1 + v2 + 1)) with
      | some env' => evalStmtsList rest env'
      | none => none
    | _, _ => none

def checkListEnv (n : Nat) : Bool :=
  let init : LocalEnv := List.replicate 16 (some 1)
  match evalStmtsList (mkEnvBenchStmts n) init with
  | some finalEnv =>
    (getLocal finalEnv 0).isSome && (getLocal finalEnv 1).isSome &&
    (getLocal finalEnv 8).isSome && (getLocal finalEnv 15).isSome
  | none => false

-- ============================================================================
-- Section 6: Proof Term Size Introspection & Representative Instances
-- ============================================================================

partial def exprTreeNodes : Lean.Expr → Nat
  | .app f a => 1 + exprTreeNodes f + exprTreeNodes a
  | .lam _ t b _ => 1 + exprTreeNodes t + exprTreeNodes b
  | .forallE _ t b _ => 1 + exprTreeNodes t + exprTreeNodes b
  | .letE _ t v b _ => 1 + exprTreeNodes t + exprTreeNodes v + exprTreeNodes b
  | .mdata _ e => 1 + exprTreeNodes e
  | .proj _ _ e => 1 + exprTreeNodes e
  | _ => 1

open Lean Meta in
def printProofMetrics (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  match info.value? (allowOpaque := true) with
  | some val =>
    let dagObjs ← val.numObjs
    let treeNodes := exprTreeNodes val
    IO.println s!"METRIC {declName}: dag_objs={dagObjs} tree_nodes={treeNodes}"
  | none =>
    IO.println s!"METRIC {declName}: no_value"

@[reducible] def diamondCfg1 : MirBody := mkDiamondBlocks 1
@[reducible] def diamondCfg2 : MirBody := mkDiamondBlocks 2
@[reducible] def diamondCfg4 : MirBody := mkDiamondBlocks 4
@[reducible] def diamondCfg6 : MirBody := mkDiamondBlocks 6
@[reducible] def diamondCfg8 : MirBody := mkDiamondBlocks 8
@[reducible] def diamondCfg10 : MirBody := mkDiamondBlocks 10

@[reducible] def uncanonCfg1 : MirBody := mkDiamondUncanonBlocks 1
@[reducible] def uncanonCfg2 : MirBody := mkDiamondUncanonBlocks 2
@[reducible] def uncanonCfg4 : MirBody := mkDiamondUncanonBlocks 4
@[reducible] def uncanonCfg6 : MirBody := mkDiamondUncanonBlocks 6

@[reducible] def chainCfg16 : MirBody := mkChainBlocks 16
@[reducible] def chainCfg32 : MirBody := mkChainBlocks 32
@[reducible] def chainCfg64 : MirBody := mkChainBlocks 64
@[reducible] def chainCfg128 : MirBody := mkChainBlocks 128

set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

-- Architecture A instances on canonicalized diamonds (K = 1, 2, 4, 6)
theorem archA_diamond1 : BodySafe diamondCfg1 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_diamond1
theorem archA_diamond2 : BodySafe diamondCfg2 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_diamond2
theorem archA_diamond4 : BodySafe diamondCfg4 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_diamond4
theorem archA_diamond6 : BodySafe diamondCfg6 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_diamond6

-- Architecture A instances on uncanonicalized diamonds (K = 1, 2, 4, 6)
theorem archA_uncanon1 : BodySafe uncanonCfg1 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_uncanon1
theorem archA_uncanon2 : BodySafe uncanonCfg2 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_uncanon2
theorem archA_uncanon4 : BodySafe uncanonCfg4 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_uncanon4
theorem archA_uncanon6 : BodySafe uncanonCfg6 defaultInitLocals := by intro oracle; step_arch_a
#eval printProofMetrics ``archA_uncanon6

-- Architecture B instances (K = 1, 2, 4, 6, 8, 10 and chains N = 16, 32, 64, 128)
theorem archB_diamond1 : BodySafe diamondCfg1 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond1
theorem archB_diamond2 : BodySafe diamondCfg2 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond2
theorem archB_diamond4 : BodySafe diamondCfg4 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond4
theorem archB_diamond6 : BodySafe diamondCfg6 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond6
theorem archB_diamond8 : BodySafe diamondCfg8 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond8
theorem archB_diamond10 : BodySafe diamondCfg10 defaultInitLocals := by intro oracle; step_arch_b_diamond
#eval printProofMetrics ``archB_diamond10

theorem archB_chain16 : BodySafe chainCfg16 defaultInitLocals := by intro oracle; step_arch_b_chain
#eval printProofMetrics ``archB_chain16
theorem archB_chain32 : BodySafe chainCfg32 defaultInitLocals := by intro oracle; step_arch_b_chain
#eval printProofMetrics ``archB_chain32
theorem archB_chain64 : BodySafe chainCfg64 defaultInitLocals := by intro oracle; step_arch_b_chain
#eval printProofMetrics ``archB_chain64
theorem archB_chain128 : BodySafe chainCfg128 defaultInitLocals := by intro oracle; step_arch_b_chain
#eval printProofMetrics ``archB_chain128

-- Architecture C instances (K = 1, 2, 4, 6, 8, 10 and chains N = 16, 32, 64, 128)
theorem archC_diamond1 : BodySafe diamondCfg1 defaultInitLocals := checkBodySym_sound 8 diamondCfg1 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond1
theorem archC_diamond2 : BodySafe diamondCfg2 defaultInitLocals := checkBodySym_sound 12 diamondCfg2 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond2
theorem archC_diamond4 : BodySafe diamondCfg4 defaultInitLocals := checkBodySym_sound 20 diamondCfg4 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond4
theorem archC_diamond6 : BodySafe diamondCfg6 defaultInitLocals := checkBodySym_sound 28 diamondCfg6 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond6
theorem archC_diamond8 : BodySafe diamondCfg8 defaultInitLocals := checkBodySym_sound 36 diamondCfg8 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond8
theorem archC_diamond10 : BodySafe diamondCfg10 defaultInitLocals := checkBodySym_sound 44 diamondCfg10 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_diamond10

theorem archC_chain16 : BodySafe chainCfg16 defaultInitLocals := checkBodySym_sound 20 chainCfg16 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_chain16
theorem archC_chain32 : BodySafe chainCfg32 defaultInitLocals := checkBodySym_sound 36 chainCfg32 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_chain32
theorem archC_chain64 : BodySafe chainCfg64 defaultInitLocals := checkBodySym_sound 68 chainCfg64 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_chain64
theorem archC_chain128 : BodySafe chainCfg128 defaultInitLocals := checkBodySym_sound 132 chainCfg128 { bb := 0, locals := defaultInitLocals } rfl
#eval printProofMetrics ``archC_chain128

-- Environment Representation instances (N = 20, 50, 100, 200)
theorem env_closure_20 : checkClosureEnv 20 = true := rfl
#eval printProofMetrics ``env_closure_20
theorem env_closure_50 : checkClosureEnv 50 = true := rfl
#eval printProofMetrics ``env_closure_50
theorem env_closure_100 : checkClosureEnv 100 = true := rfl
#eval printProofMetrics ``env_closure_100
theorem env_closure_200 : checkClosureEnv 200 = true := rfl
#eval printProofMetrics ``env_closure_200

theorem env_list_20 : checkListEnv 20 = true := rfl
#eval printProofMetrics ``env_list_20
theorem env_list_50 : checkListEnv 50 = true := rfl
#eval printProofMetrics ``env_list_50
theorem env_list_100 : checkListEnv 100 = true := rfl
#eval printProofMetrics ``env_list_100
theorem env_list_200 : checkListEnv 200 = true := rfl
#eval printProofMetrics ``env_list_200

end AnnealBench
