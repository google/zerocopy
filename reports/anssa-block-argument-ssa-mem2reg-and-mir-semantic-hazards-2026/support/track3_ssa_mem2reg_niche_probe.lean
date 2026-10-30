/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

/-!
# Track 3 Mechanization Probe: `AnSSA`, Verified `mem2reg`, `MaybeUninit` Freeze, and Niche Decoding

This standalone Lean 4.34.1 file mechanizes the core semantic models and
refinement proofs for Track 3 of Round 1:

1. **Anneal Refinement Foundation (`Section 0`):** Replicates Anneal's
   `Preorder`, `Partial`, `Monotone`, `Language`, `Compiles`, `StepResult`,
   `SmallStepMachine`, `PrefixOutcome`, and `BehaviorOf` definitions from
   `Trusted/Refinement.lean` and `Trusted/StepResult.lean`.
2. **Block-Argument SSA (`AnSSA`) and Verified `mem2reg` (`Section 1`):**
   Defines a multi-block `MirBody` (with both promotable locals and
   address-taken memory locals mutated via indirect references `writeRef`) and
   a block-argument SSA IR `AnSSABody` where join blocks declare formal
   parameters `params : List SSAId` and control-flow edges pass explicit
   argument vectors `args : List SSAExpr`. Implements a linear-time translation
   validator `checkMem2Reg` (supporting both block-argument join parameters and
   dominator register inheritance) and proves expression and statement
   simulation invariants, a verified 4-block diamond-CFG `mem2reg` translation
   across all execution steps, and a negative control refuting `Compiles` when
   an address-taken local is illegally promoted.
3. **`MaybeUninit` / Padding Promotion: `freeze` vs. Multi-Valued `undef`
   (`Section 2`):** Models byte-level initialization (`ByteVal = .uninit |
   .init (b : BitVec 8)`) and proves that coherent `freeze`-on-promotion
   preserves `Compiles` across common subexpression elimination (`let y = x;
   x == y` to `x == x`), whereas LLVM-style multi-valued `undef` promotion
   refutes `Compiles` (`multi_undef_refutes_compiles`).
4. **`TagEncoding::Niche` Wrapping Arithmetic and Premature Range Metadata
   (`Section 3`):** Formalizes `rustc`'s `TagEncoding::Niche` encoding and
   wrapping modular subtraction decoder `(tag - nicheStart) ≤ᵤ nicheSpan`,
   proves universal round-trip soundness for both tagged niche variants and
   untagged payloads (including wrap-around niches mod $2^w$), and proves that
   attaching the untagged payload's narrower validity range (`!nonnull` /
   `!range`) before discriminant decoding introduces artificial UB on niche
   variants (`premature_payload_range_unsound`).
5. **Zero-Sized Type (`ZST`) Load Elision (`Section 4`):** Proves that eliding
   memory loads and stores for zero-sized types (`size == 0`) refines MIR on
   dangling aligned pointers (`NonNull::dangling()`), whereas emitting a
   hardware load on an unallocated ZST pointer fails refinement.
-/

namespace Track3Probe

/-!
## Section 0: Anneal Refinement Foundation

These definitions mirror `trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean` so this probe runs standalone with
`lean -j1 -M1024`.
-/

class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

attribute [instance 2000] Preorder.toLE

class Partial (α : Type u) extends Preorder α where
  bot : α
  bot_le : ∀ a : α, bot ≤ a

def Monotone {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (f : α → β) : Prop :=
  ∀ {a b : α}, a ≤ b → f a ≤ f b

instance (priority := high) [Preorder α] : Preorder (Option α) where
  le x y := match x, y with
    | none, _ => True
    | some _, none => False
    | some a, some b => a ≤ b
  le_refl x := by cases x <;> simp [Preorder.le_refl]
  le_trans {x y z} h1 h2 := by
    cases x <;> cases y <;> cases z <;> try trivial
    exact Preorder.le_trans h1 h2

instance (priority := high) [Preorder α] : Partial (Option α) where
  bot := none
  bot_le x := by cases x <;> trivial

instance (priority := high) {α : Type} [Preorder α] [∀ a b : α, Decidable (a ≤ b)]
    (x y : Option α) : Decidable (x ≤ y) :=
  match x, y with
  | none, _ => isTrue trivial
  | some _, none => isFalse (by intro h; exact h)
  | some a, some b => inferInstanceAs (Decidable (a ≤ b))

instance {ι : Type w} {α : ι → Type u} [∀ i, Preorder (α i)] :
    Preorder (∀ i, α i) where
  le f g := ∀ i, f i ≤ g i
  le_refl _ _ := Preorder.le_refl _
  le_trans h1 h2 i := Preorder.le_trans (h1 i) (h2 i)

instance {ι : Type w} {α : ι → Type u} [∀ i, Partial (α i)] :
    Partial (∀ i, α i) where
  bot _ := Partial.bot
  bot_le _ _ := Partial.bot_le _

structure Language (Prog : Type u) (Sem : Type v) [Partial Sem] where
  eval : Prog → Sem

def Compiles {ProgS ProgT SemS SemT : Type} [Partial SemS] [Partial SemT]
    (L_S : Language ProgS SemS) (L_T : Language ProgT SemT)
    (π : SemT → SemS) (s : ProgS) (t : ProgT) : Prop :=
  L_S.eval s ≤ π (L_T.eval t)

theorem Compiles.id {Prog Sem : Type} [Partial Sem]
    (L : Language Prog Sem) (p : Prog) :
    Compiles L L _root_.id p p :=
  Preorder.le_refl (L.eval p)

theorem Compiles.trans {Prog1 Prog2 Prog3 Sem1 Sem2 Sem3 : Type}
    [Partial Sem1] [Partial Sem2] [Partial Sem3]
    {L1 : Language Prog1 Sem1} {L2 : Language Prog2 Sem2}
    {L3 : Language Prog3 Sem3}
    {π12 : Sem2 → Sem1} {π23 : Sem3 → Sem2}
    {p1 : Prog1} {p2 : Prog2} {p3 : Prog3}
    (h12 : Compiles L1 L2 π12 p1 p2)
    (h23 : Compiles L2 L3 π23 p2 p3)
    (h_mono : Monotone π12) :
    Compiles L1 L3 (π12 ∘ π23) p1 p3 :=
  Preorder.le_trans h12 (h_mono h23)

inductive StepResult (State Val : Type) where
  | next (s' : State)
  | terminal (v : Val)
  | stuck
  | ub
  deriving DecidableEq, Repr

structure SmallStepMachine (State Input Val : Type) where
  init : Input → Option State
  step : State → StepResult State Val

structure ExecQuery (Input : Type) where
  input : Input
  fuel : Nat
  deriving DecidableEq, Repr

inductive PrefixOutcome (State Val : Type) where
  | ub : PrefixOutcome State Val
  | running : State → PrefixOutcome State Val
  | returns : Val → PrefixOutcome State Val
  | stuck : PrefixOutcome State Val
  deriving DecidableEq, Repr

instance {State Val : Type} : Preorder (PrefixOutcome State Val) where
  le x y := x = .ub ∨ x = y
  le_refl _ := Or.inr rfl
  le_trans {a b c} hab hbc := by
    cases hab with
    | inl h => exact Or.inl h
    | inr h => subst h; exact hbc

instance {State Val : Type} : Partial (PrefixOutcome State Val) where
  bot := .ub
  bot_le _ := Or.inl rfl

instance {State Val : Type} [DecidableEq State] [DecidableEq Val]
    (x y : PrefixOutcome State Val) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x = .ub ∨ x = y))

abbrev ExecOut (State Val : Type) := Option (PrefixOutcome State Val)

inductive ReachesPrefix {State Input Val : Type}
    (m : SmallStepMachine State Input Val) :
    Nat → State → PrefixOutcome State Val → Prop where
  | zero (s : State) :
      ReachesPrefix m 0 s (.running s)
  | step_next {n : Nat} {s s' : State} {o : PrefixOutcome State Val} :
      m.step s = .next s' →
      ReachesPrefix m n s' o →
      ReachesPrefix m (n + 1) s o
  | step_terminal {n : Nat} {s : State} {v : Val} :
      m.step s = .terminal v →
      ReachesPrefix m (n + 1) s (.returns v)
  | step_stuck {n : Nat} {s : State} :
      m.step s = .stuck →
      ReachesPrefix m (n + 1) s .stuck
  | step_ub {n : Nat} {s : State} :
      m.step s = .ub →
      ReachesPrefix m (n + 1) s .ub

def BehaviorOf {State Input Val : Type}
    (m : SmallStepMachine State Input Val)
    (q : ExecQuery Input) (out : ExecOut State Val) : Prop :=
  match out with
  | none => m.init q.input = none
  | some o => ∃ s0, m.init q.input = some s0 ∧ ReachesPrefix m q.fuel s0 o

/-- Executable fuel evaluator matching `ReachesPrefix`. -/
def runSteps {State Input Val : Type}
    (m : SmallStepMachine State Input Val) :
    Nat → State → PrefixOutcome State Val
  | 0, s => .running s
  | n + 1, s =>
    match m.step s with
    | .next s' => runSteps m n s'
    | .terminal v => .returns v
    | .stuck => .stuck
    | .ub => .ub

def evalMachine {State Input Val : Type}
    (m : SmallStepMachine State Input Val) (q : ExecQuery Input) :
    ExecOut State Val :=
  match m.init q.input with
  | none => none
  | some s0 => some (runSteps m q.fuel s0)

theorem runSteps_reaches {State Input Val : Type}
    (m : SmallStepMachine State Input Val) (n : Nat) (s : State) :
    ReachesPrefix m n s (runSteps m n s) := by
  induction n generalizing s with
  | zero => exact ReachesPrefix.zero s
  | succ k ih =>
    simp only [runSteps]
    split
    · rename_i s' hstep
      exact ReachesPrefix.step_next hstep (ih s')
    · rename_i v hstep
      exact ReachesPrefix.step_terminal hstep
    · rename_i hstep
      exact ReachesPrefix.step_stuck hstep
    · rename_i hstep
      exact ReachesPrefix.step_ub hstep

/-!
## Section 1: Block-Argument SSA (`AnSSA`) and Verified `mem2reg` (`checkMem2Reg`)

We model a CFG-based MIR (`MirBody`) and a block-argument SSA IR (`AnSSABody`).

### Design and Rust Correspondence
- In `rustc` (`compiler/rustc_codegen_ssa/src/mir/analyze.rs:18-268` and
  `compiler/rustc_mir_transform/src/ssa.rs:20-293`), a MIR local is eligible
  for SSA register promotion only if its address is never taken (no shared or
  mutable borrow / raw pointer projections that escape into indirect accesses).
- In Lean 4's LCNF (`src/Lean/Compiler/LCNF/Basic.lean:180-360`) and Cranelift's
  `SSABuilder` (`cranelift-frontend-0.136.2/src/ssa.rs:34-658`), SSA join points
  are represented as parameterized basic blocks `bb(p₁, ..., pₖ)` rather than
  $\phi$-nodes, and control-flow terminators pass explicit argument vectors
  `jump target [a₁, ..., aₖ]` on every outgoing edge.
- Below, `MirStmt.writeRef l e` models an indirect store `*(&mut l) = e` through
  an address-taken reference to local `l`. In `MirBody`, all locals reside in a
  unified frame `frame : Env LocalId`, so both `MirStmt.assign l e` and
  `MirStmt.writeRef l e` mutate `frame l`.
- In `AnSSABody`, state is partitioned into an SSA register environment
  `ssaEnv : Env SSAId` (updated by `SSAStmt.letBind` and block-parameter
  bindings `bindParams` on CFG edges) and an unpromoted memory environment
  `mem : Env LocalId` (updated by `SSAStmt.storeMem` and `SSAStmt.writeRef`).
-/

abbrev BlockId := Nat
abbrev LocalId := Nat
abbrev SSAId   := Nat

/-- Total environment lookup with default `0`. -/
abbrev Env (k : Type) := List (k × Nat)

def envGet (env : Env Nat) (x : Nat) : Nat :=
  match env.lookup x with
  | some v => v
  | none   => 0

def envSet (env : Env Nat) (x : Nat) (v : Nat) : Env Nat :=
  (x, v) :: env

theorem envGet_envSet_self (env : Env Nat) (x v : Nat) :
    envGet (envSet env x v) x = v := by
  simp [envGet, envSet]

theorem envGet_envSet_ne (env : Env Nat) {x y : Nat} (v : Nat) (h : x ≠ y) :
    envGet (envSet env y v) x = envGet env x := by
  have hne : (x == y) = false := beq_eq_false_iff_ne.mpr h
  simp [envGet, envSet, List.lookup, hne]

/-- Canonicalize an environment over a fixed list of local IDs so states with
identical `envGet` values have identical list representations. -/
def canonicalEnv (keys : List Nat) (env : Env Nat) : Env Nat :=
  keys.map (fun k => (k, envGet env k))

/-- MIR expressions over `LocalId`. -/
inductive MirExpr where
  | const (n : Nat)
  | var (l : LocalId)
  | add (e1 e2 : MirExpr)
  deriving DecidableEq, Repr

def evalMirExpr (frame : Env LocalId) : MirExpr → Nat
  | .const n   => n
  | .var l     => envGet frame l
  | .add e1 e2 => evalMirExpr frame e1 + evalMirExpr frame e2

/-- MIR statements: direct assignment or indirect mutation via a reference. -/
inductive MirStmt where
  | assign (dst : LocalId) (rhs : MirExpr)
  | writeRef (target : LocalId) (rhs : MirExpr)
  deriving DecidableEq, Repr

def execMirStmt (frame : Env LocalId) : MirStmt → Env LocalId
  | .assign dst rhs      => envSet frame dst (evalMirExpr frame rhs)
  | .writeRef target rhs => envSet frame target (evalMirExpr frame rhs)

def execMirStmts (frame : Env LocalId) : List MirStmt → Env LocalId
  | []      => frame
  | s :: ss => execMirStmts (execMirStmt frame s) ss

/-- MIR terminators. -/
inductive MirTerm where
  | jump (target : BlockId)
  | branch (cond : MirExpr) (tTarget fTarget : BlockId)
  | ret (val : MirExpr)
  deriving DecidableEq, Repr

structure MirBlock where
  stmts : List MirStmt
  term  : MirTerm
  deriving DecidableEq, Repr

structure MirBody where
  entry  : BlockId
  locals : List LocalId
  blocks : List (BlockId × MirBlock)
  deriving DecidableEq, Repr

def findMirBlock (prog : MirBody) (bb : BlockId) : Option MirBlock :=
  prog.blocks.lookup bb

structure MirState where
  bb    : BlockId
  frame : Env LocalId
  deriving DecidableEq, Repr

def stepMir (prog : MirBody) (st : MirState) : StepResult MirState Nat :=
  match findMirBlock prog st.bb with
  | none => .stuck
  | some blk =>
    let frame' := canonicalEnv prog.locals (execMirStmts st.frame blk.stmts)
    match blk.term with
    | .jump target =>
      .next { bb := target, frame := frame' }
    | .branch cond tTarget fTarget =>
      let c := evalMirExpr frame' cond
      let target := if c != 0 then tTarget else fTarget
      .next { bb := target, frame := frame' }
    | .ret val =>
      .terminal (evalMirExpr frame' val)

def mirMachine (prog : MirBody) : SmallStepMachine MirState (Env LocalId) Nat where
  init initFrame :=
    some { bb := prog.entry, frame := canonicalEnv prog.locals initFrame }
  step := stepMir prog

/-- Block-argument SSA (`AnSSA`) expressions. -/
inductive SSAExpr where
  | const (n : Nat)
  | ssaVar (v : SSAId)
  | loadMem (l : LocalId)
  | add (e1 e2 : SSAExpr)
  deriving DecidableEq, Repr

def evalSSAExpr (ssaEnv : Env SSAId) (mem : Env LocalId) : SSAExpr → Nat
  | .const n   => n
  | .ssaVar v  => envGet ssaEnv v
  | .loadMem l => envGet mem l
  | .add e1 e2 => evalSSAExpr ssaEnv mem e1 + evalSSAExpr ssaEnv mem e2

/-- `AnSSA` statements: either bind an SSA register or mutate memory. -/
inductive SSAStmt where
  | letBind (dst : SSAId) (rhs : SSAExpr)
  | storeMem (dst : LocalId) (rhs : SSAExpr)
  | writeRef (target : LocalId) (rhs : SSAExpr)
  deriving DecidableEq, Repr

def execSSAStmt (ssaEnv : Env SSAId) (mem : Env LocalId) :
    SSAStmt → (Env SSAId × Env LocalId)
  | .letBind dst rhs =>
    (envSet ssaEnv dst (evalSSAExpr ssaEnv mem rhs), mem)
  | .storeMem dst rhs =>
    (ssaEnv, envSet mem dst (evalSSAExpr ssaEnv mem rhs))
  | .writeRef target rhs =>
    (ssaEnv, envSet mem target (evalSSAExpr ssaEnv mem rhs))

def execSSAStmts (ssaEnv : Env SSAId) (mem : Env LocalId) :
    List SSAStmt → (Env SSAId × Env LocalId)
  | [] => (ssaEnv, mem)
  | s :: ss =>
    let (ssaEnv', mem') := execSSAStmt ssaEnv mem s
    execSSAStmts ssaEnv' mem' ss

/-- `AnSSA` terminators carry explicit argument lists on every outgoing edge. -/
inductive SSATerm where
  | jump (target : BlockId) (args : List SSAExpr)
  | branch (cond : SSAExpr)
      (tTarget : BlockId) (tArgs : List SSAExpr)
      (fTarget : BlockId) (fArgs : List SSAExpr)
  | ret (val : SSAExpr)
  deriving DecidableEq, Repr

structure SSABlock where
  params : List SSAId
  stmts  : List SSAStmt
  term   : SSATerm
  deriving DecidableEq, Repr

structure AnSSABody where
  entry  : BlockId
  locals : List LocalId
  blocks : List (BlockId × SSABlock)
  deriving DecidableEq, Repr

def findSSABlock (prog : AnSSABody) (bb : BlockId) : Option SSABlock :=
  prog.blocks.lookup bb

/-- Evaluate a list of edge arguments in the predecessor's environment. -/
def evalEdgeArgs (ssaEnv : Env SSAId) (mem : Env LocalId) :
    List SSAExpr → List Nat
  | [] => []
  | e :: es => evalSSAExpr ssaEnv mem e :: evalEdgeArgs ssaEnv mem es

/-- Bind a target block's formal parameters to the evaluated edge arguments. -/
def bindParams (ssaEnv : Env SSAId) : List SSAId → List Nat → Option (Env SSAId)
  | [], [] => some ssaEnv
  | p :: ps, v :: vs => bindParams (envSet ssaEnv p v) ps vs
  | _, _ => none

structure SSAState where
  bb     : BlockId
  ssaEnv : Env SSAId
  mem    : Env LocalId
  deriving DecidableEq, Repr

def stepSSA (prog : AnSSABody) (st : SSAState) : StepResult SSAState Nat :=
  match findSSABlock prog st.bb with
  | none => .stuck
  | some blk =>
    let (ssaEnv', mem') := execSSAStmts st.ssaEnv st.mem blk.stmts
    match blk.term with
    | .jump target args =>
      match findSSABlock prog target with
      | none => .stuck
      | some targetBlk =>
        let vals := evalEdgeArgs ssaEnv' mem' args
        match bindParams ssaEnv' targetBlk.params vals with
        | none => .stuck
        | some ssaEnvNext =>
          .next { bb := target, ssaEnv := ssaEnvNext, mem := mem' }
    | .branch cond tTarget tArgs fTarget fArgs =>
      let c := evalSSAExpr ssaEnv' mem' cond
      let (target, args) :=
        if c != 0 then (tTarget, tArgs) else (fTarget, fArgs)
      match findSSABlock prog target with
      | none => .stuck
      | some targetBlk =>
        let vals := evalEdgeArgs ssaEnv' mem' args
        match bindParams ssaEnv' targetBlk.params vals with
        | none => .stuck
        | some ssaEnvNext =>
          .next { bb := target, ssaEnv := ssaEnvNext, mem := mem' }
    | .ret val =>
      .terminal (evalSSAExpr ssaEnv' mem' val)

def ssaMachine (prog : AnSSABody) (entryParamMap : List (LocalId × SSAId)) :
    SmallStepMachine SSAState (Env LocalId) Nat where
  init initFrame :=
    let cFrame := canonicalEnv prog.locals initFrame
    let initSsa :=
      entryParamMap.foldl (fun acc (l, v) => envSet acc v (envGet cFrame l)) []
    some { bb := prog.entry, ssaEnv := initSsa, mem := cFrame }
  step := stepSSA prog

/-- Reconstruct a MIR frame from `mem` and a list of `(LocalId, SSAId)` pairs,
canonicalized over `locals`. -/
def reconstructFrameAux (ssaEnv : Env SSAId) (mem : Env LocalId) :
    List (LocalId × SSAId) → Env LocalId
  | [] => mem
  | (l, v) :: rest =>
    envSet (reconstructFrameAux ssaEnv mem rest) l (envGet ssaEnv v)

def reconstructFrame (locals : List LocalId) (ssaEnv : Env SSAId)
    (mem : Env LocalId) (map : List (LocalId × SSAId)) : Env LocalId :=
  canonicalEnv keys (reconstructFrameAux ssaEnv mem map)
where
  keys := locals

/-- Project an `SSAState` back to a `MirState` using per-block register maps. -/
def projSSAState (locals : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId))
    (st : SSAState) : MirState where
  bb    := st.bb
  frame := reconstructFrame locals st.ssaEnv st.mem (blockMap st.bb)

def mapPrefixOutcome {S1 S2 V : Type} (f : S2 → S1) :
    PrefixOutcome S2 V → PrefixOutcome S1 V
  | .ub        => .ub
  | .running s => .running (f s)
  | .returns v => .returns v
  | .stuck     => .stuck

def mapExecOut {S1 S2 V : Type} (f : S2 → S1) :
    ExecOut S2 V → ExecOut S1 V
  | none   => none
  | some o => some (mapPrefixOutcome f o)

def π_ssa (locals : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId))
    (semT : ExecQuery (Env LocalId) → ExecOut SSAState Nat) :
    ExecQuery (Env LocalId) → ExecOut MirState Nat :=
  fun q => mapExecOut (projSSAState locals blockMap) (semT q)

theorem mapPrefixOutcome_mono {S1 S2 V : Type} (f : S2 → S1)
    {o1 o2 : PrefixOutcome S2 V} (h : o1 ≤ o2) :
    mapPrefixOutcome f o1 ≤ mapPrefixOutcome f o2 := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mapExecOut_mono {S1 S2 V : Type} (f : S2 → S1)
    {x y : ExecOut S2 V} (h : x ≤ y) :
    mapExecOut f x ≤ mapExecOut f y := by
  cases x with
  | none => exact trivial
  | some o1 =>
    cases y with
    | none => exact False.elim h
    | some o2 => exact mapPrefixOutcome_mono f h

theorem π_ssa_monotone (locals : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId)) :
    Monotone (π_ssa locals blockMap) := by
  intro f g hfg q
  exact mapExecOut_mono (projSSAState locals blockMap) (hfg q)

abbrev MirSem := ExecQuery (Env LocalId) → ExecOut MirState Nat
abbrev SSASem := ExecQuery (Env LocalId) → ExecOut SSAState Nat

def MirLang : Language MirBody MirSem where
  eval prog q := evalMachine (mirMachine prog) q

def AnSSALang (entryMap : List (LocalId × SSAId)) : Language AnSSABody SSASem where
  eval prog q := evalMachine (ssaMachine prog entryMap) q

/-!
### Linear-Time Translation Validator (`checkExpr`, `checkStmts`, `checkBlock`)
-/

def lookupMap (σ : List (LocalId × SSAId)) (l : LocalId) : Option SSAId :=
  σ.lookup l

/-- Check that `SSAExpr` is the valid translation of `MirExpr` under `σ`. -/
def checkExpr (promoted : List LocalId) (σ : List (LocalId × SSAId)) :
    MirExpr → SSAExpr → Bool
  | .const n, .const m => n == m
  | .var l, .ssaVar v =>
    (promoted.contains l) && (lookupMap σ l == some v)
  | .var l, .loadMem l' =>
    (!promoted.contains l) && (l == l')
  | .add a1 b1, .add a2 b2 =>
    checkExpr promoted σ a1 a2 && checkExpr promoted σ b1 b2
  | _, _ => false

/-- Check a single statement and return the updated `(LocalId → SSAId)` map. -/
def checkStmt (promoted : List LocalId) (σ : List (LocalId × SSAId)) :
    MirStmt → SSAStmt → Option (List (LocalId × SSAId))
  | .assign dst rhsM, .letBind v rhsS =>
    if promoted.contains dst && checkExpr promoted σ rhsM rhsS then
      some ((dst, v) :: σ)
    else
      none
  | .assign dst rhsM, .storeMem dst' rhsS =>
    if (!promoted.contains dst) && (dst == dst') && checkExpr promoted σ rhsM rhsS then
      some σ
    else
      none
  | .writeRef target rhsM, .writeRef target' rhsS =>
    -- Address-taken locals mutated via `writeRef` MUST NOT be promoted to SSA!
    if (!promoted.contains target) && (target == target') &&
       checkExpr promoted σ rhsM rhsS then
      some σ
    else
      none
  | _, _ => none

def checkStmts (promoted : List LocalId) (σ : List (LocalId × SSAId)) :
    List MirStmt → List SSAStmt → Option (List (LocalId × SSAId))
  | [], [] => some σ
  | sm :: sms, ss :: sss =>
    match checkStmt promoted σ sm ss with
    | none => none
    | some σ' => checkStmts promoted σ' sms sss
  | _, _ => none

/-- Check that outgoing edge arguments `args` match `targetParams` and
`targetMap` under `σ`:
1. Every `(l, v)` in `targetMap` whose `v ∈ targetParams` is passed in order in
   `args` as `SSAExpr.ssaVar v_src` where `lookupMap σ l = some v_src`.
2. Every `(l, v)` in `targetMap` whose `v ∉ targetParams` is inherited from the
   dominating block (`lookupMap σ l = some v`). -/
def checkEdgeArgs (promoted : List LocalId) (σ : List (LocalId × SSAId))
    (targetParams : List SSAId) (targetMap : List (LocalId × SSAId))
    (args : List SSAExpr) : Bool :=
  let paramPairs := targetMap.filter (fun (_, v) => targetParams.contains v)
  let inheritedPairs := targetMap.filter (fun (_, v) => !targetParams.contains v)
  (targetParams == paramPairs.map Prod.snd) &&
  (args == paramPairs.filterMap (fun (l, _) =>
    if promoted.contains l then
      (lookupMap σ l).map SSAExpr.ssaVar
    else
      none)) &&
  (inheritedPairs.all (fun (l, v) =>
    promoted.contains l && (lookupMap σ l == some v))) &&
  (args.length == targetParams.length)

/-- Check terminator correspondence under `σ`. -/
def checkTerm (promoted : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId))
    (ssa : AnSSABody) (σ : List (LocalId × SSAId)) :
    MirTerm → SSATerm → Bool
  | .jump targetM, .jump targetS args =>
    (targetM == targetS) &&
    match findSSABlock ssa targetS with
    | none => false
    | some tBlk =>
      checkEdgeArgs promoted σ tBlk.params (blockMap targetS) args
  | .branch condM tM fM, .branch condS tS tArgs fS fArgs =>
    (tM == tS) && (fM == fS) &&
    checkExpr promoted σ condM condS &&
    (match findSSABlock ssa tS, findSSABlock ssa fS with
     | some tBlk, some fBlk =>
       checkEdgeArgs promoted σ tBlk.params (blockMap tS) tArgs &&
       checkEdgeArgs promoted σ fBlk.params (blockMap fS) fArgs
     | _, _ => false)
  | .ret valM, .ret valS =>
    checkExpr promoted σ valM valS
  | _, _ => false

/-- Check a basic block pair under the entry `blockMap`. -/
def checkBlock (promoted : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId))
    (ssa : AnSSABody) (bb : BlockId) (mBlk : MirBlock) (sBlk : SSABlock) : Bool :=
  let σ0 := blockMap bb
  match checkStmts promoted σ0 mBlk.stmts sBlk.stmts with
  | none => false
  | some σEnd => checkTerm promoted blockMap ssa σEnd mBlk.term sBlk.term

/-!
### Core Expression and Statement Simulation Theorems
-/

/-- The fundamental simulation invariant relating a MIR `frame` to `(ssaEnv, mem)`. -/
def FrameInv (promoted : List LocalId) (σ : List (LocalId × SSAId))
    (frame : Env LocalId) (ssaEnv : Env SSAId) (mem : Env LocalId) : Prop :=
  (∀ l v, promoted.contains l = true → lookupMap σ l = some v →
    envGet frame l = envGet ssaEnv v) ∧
  (∀ l, promoted.contains l = false → envGet frame l = envGet mem l)

theorem checkExpr_sound {promoted : List LocalId} {σ : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (eM : MirExpr) (eS : SSAExpr)
    (hCheck : checkExpr promoted σ eM eS = true) :
    evalSSAExpr ssaEnv mem eS = evalMirExpr frame eM := by
  induction eM generalizing eS with
  | const n =>
    cases eS <;> simp [checkExpr] at hCheck
    subst hCheck
    rfl
  | var l =>
    cases eS with
    | const _ => simp [checkExpr] at hCheck
    | ssaVar v =>
      simp only [checkExpr, Bool.and_eq_true, beq_iff_eq] at hCheck
      exact (hInv.1 l v hCheck.1 hCheck.2).symm
    | loadMem l' =>
      simp only [checkExpr, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hCheck
      rcases hCheck with ⟨hNotProm, rfl⟩
      exact (hInv.2 l hNotProm).symm
    | add _ _ => simp [checkExpr] at hCheck
  | add a1 b1 iha ihb =>
    cases eS <;> simp [checkExpr] at hCheck
    rename_i a2 b2
    simp [evalSSAExpr, evalMirExpr, iha a2 hCheck.1, ihb b2 hCheck.2]

/-- If `dst` is assigned a fresh SSA variable `v` not aliasing existing bindings
in `σ` for other locals `l ≠ dst`, `FrameInv` is preserved. -/
def FreshForMap (σ : List (LocalId × SSAId)) (dst : LocalId) (v : SSAId) : Prop :=
  ∀ l v', l ≠ dst → lookupMap σ l = some v' → v' ≠ v

theorem checkStmt_assign_promoted_sound
    {promoted : List LocalId} {σ : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    {dst : LocalId} {v : SSAId} {rhsM : MirExpr} {rhsS : SSAExpr}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (hProm : promoted.contains dst = true)
    (hExpr : checkExpr promoted σ rhsM rhsS = true)
    (hFresh : FreshForMap σ dst v) :
    let (ssaEnv', mem') := execSSAStmt ssaEnv mem (.letBind v rhsS)
    let frame' := execMirStmt frame (.assign dst rhsM)
    FrameInv promoted ((dst, v) :: σ) frame' ssaEnv' mem' := by
  have hVal := checkExpr_sound hInv rhsM rhsS hExpr
  constructor
  · intro l v' hPromL hLook
    by_cases hEq : l = dst
    · subst hEq
      simp only [lookupMap, List.lookup, beq_self_eq_true, Option.some.injEq] at hLook
      subst hLook
      simp [execMirStmt, envGet_envSet_self, hVal]
    · have hBeq : (l == dst) = false := beq_eq_false_iff_ne.mpr hEq
      have hLook' : lookupMap σ l = some v' := by
        simp only [lookupMap, List.lookup, hBeq] at hLook
        exact hLook
      have hNeV : v' ≠ v := hFresh l v' hEq hLook'
      simp [execMirStmt, envGet_envSet_ne _ _ hEq,
        envGet_envSet_ne _ _ hNeV]
      exact hInv.1 l v' hPromL hLook'
  · intro l hNotPromL
    have hNe : l ≠ dst := by
      intro hEq
      subst hEq
      rw [hProm] at hNotPromL
      contradiction
    simp [execMirStmt, envGet_envSet_ne _ _ hNe]
    exact hInv.2 l hNotPromL

theorem checkStmt_writeRef_unpromoted_sound
    {promoted : List LocalId} {σ : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    {target : LocalId} {rhsM : MirExpr} {rhsS : SSAExpr}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (hNotProm : promoted.contains target = false)
    (hExpr : checkExpr promoted σ rhsM rhsS = true) :
    let (ssaEnv', mem') := execSSAStmt ssaEnv mem (.writeRef target rhsS)
    let frame' := execMirStmt frame (.writeRef target rhsM)
    FrameInv promoted σ frame' ssaEnv' mem' := by
  have hVal := checkExpr_sound hInv rhsM rhsS hExpr
  constructor
  · intro l v hPromL hLook
    have hNe : l ≠ target := by
      intro hEq
      subst hEq
      rw [hPromL] at hNotProm
      contradiction
    simp [execMirStmt, envGet_envSet_ne _ _ hNe]
    exact hInv.1 l v hPromL hLook
  · intro l hNotPromL
    by_cases hEq : l = target
    · subst hEq
      simp [execMirStmt, envGet_envSet_self, hVal]
    · simp [execMirStmt, envGet_envSet_ne _ _ hEq]
      exact hInv.2 l hNotPromL

theorem checkStmt_assign_unpromoted_sound
    {promoted : List LocalId} {σ : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    {dst : LocalId} {rhsM : MirExpr} {rhsS : SSAExpr}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (hNotProm : promoted.contains dst = false)
    (hExpr : checkExpr promoted σ rhsM rhsS = true) :
    let (ssaEnv', mem') := execSSAStmt ssaEnv mem (.storeMem dst rhsS)
    let frame' := execMirStmt frame (.assign dst rhsM)
    FrameInv promoted σ frame' ssaEnv' mem' := by
  have hVal := checkExpr_sound hInv rhsM rhsS hExpr
  constructor
  · intro l v hPromL hLook
    have hNe : l ≠ dst := by
      intro hEq
      subst hEq
      rw [hPromL] at hNotProm
      contradiction
    simp [execMirStmt, envGet_envSet_ne _ _ hNe]
    exact hInv.1 l v hPromL hLook
  · intro l hNotPromL
    by_cases hEq : l = dst
    · subst hEq
      simp [execMirStmt, envGet_envSet_self, hVal]
    · simp [execMirStmt, envGet_envSet_ne _ _ hEq]
      exact hInv.2 l hNotPromL

/-- Well-formedness predicate for a statement pair ensuring SSA target variables
in `.letBind` are fresh with respect to other live locals in `σ`. -/
def StmtFresh (σ : List (LocalId × SSAId)) : MirStmt → SSAStmt → Prop
  | .assign dst _, .letBind v _ => FreshForMap σ dst v
  | _, _ => True

theorem checkStmt_sound
    {promoted : List LocalId} {σ σ' : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    {sM : MirStmt} {sS : SSAStmt}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (hFresh : StmtFresh σ sM sS)
    (hCheck : checkStmt promoted σ sM sS = some σ') :
    let (ssaEnv', mem') := execSSAStmt ssaEnv mem sS
    let frame' := execMirStmt frame sM
    FrameInv promoted σ' frame' ssaEnv' mem' := by
  cases sM with
  | assign dst rhsM =>
    cases sS with
    | letBind v rhsS =>
      simp only [checkStmt, Bool.and_eq_true] at hCheck
      split at hCheck
      · rename_i hCond
        injection hCheck with hEq
        subst hEq
        exact checkStmt_assign_promoted_sound hInv hCond.1 hCond.2 hFresh
      · contradiction
    | storeMem dst' rhsS =>
      simp only [checkStmt, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hCheck
      split at hCheck
      · rename_i hCond
        rcases hCond with ⟨⟨hNotProm, rfl⟩, hExpr⟩
        injection hCheck with hEq
        subst hEq
        exact checkStmt_assign_unpromoted_sound hInv hNotProm hExpr
      · contradiction
    | writeRef _ _ =>
      simp [checkStmt] at hCheck
  | writeRef target rhsM =>
    cases sS with
    | letBind _ _ => simp [checkStmt] at hCheck
    | storeMem _ _ => simp [checkStmt] at hCheck
    | writeRef target' rhsS =>
      simp only [checkStmt, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hCheck
      split at hCheck
      · rename_i hCond
        rcases hCond with ⟨⟨hNotProm, rfl⟩, hExpr⟩
        injection hCheck with hEq
        subst hEq
        exact checkStmt_writeRef_unpromoted_sound hInv hNotProm hExpr
      · contradiction

inductive StmtsFresh (promoted : List LocalId) :
    List (LocalId × SSAId) → List MirStmt → List SSAStmt → Prop where
  | nil (σ : List (LocalId × SSAId)) :
      StmtsFresh promoted σ [] []
  | cons {σ σ' : List (LocalId × SSAId)} {sM : MirStmt} {sS : SSAStmt}
      {restM : List MirStmt} {restS : List SSAStmt} :
      StmtFresh σ sM sS →
      checkStmt promoted σ sM sS = some σ' →
      StmtsFresh promoted σ' restM restS →
      StmtsFresh promoted σ (sM :: restM) (sS :: restS)

/-- **Inductive Statement-Sequence Simulation Theorem:**
If `checkStmts promoted σ stmtsM stmtsS = some σEnd` and each `.letBind` uses a
fresh SSA register (`StmtsFresh`), then executing `stmtsM` in `MirBody` and
`stmtsS` in `AnSSABody` preserves `FrameInv` from `σ` to `σEnd`. -/
theorem checkStmts_sound
    {promoted : List LocalId} {σ σEnd : List (LocalId × SSAId)}
    {frame : Env LocalId} {ssaEnv : Env SSAId} {mem : Env LocalId}
    {stmtsM : List MirStmt} {stmtsS : List SSAStmt}
    (hInv : FrameInv promoted σ frame ssaEnv mem)
    (hFresh : StmtsFresh promoted σ stmtsM stmtsS)
    (hCheck : checkStmts promoted σ stmtsM stmtsS = some σEnd) :
    let (ssaEnv', mem') := execSSAStmts ssaEnv mem stmtsS
    let frame' := execMirStmts frame stmtsM
    FrameInv promoted σEnd frame' ssaEnv' mem' := by
  induction hFresh generalizing frame ssaEnv mem σEnd with
  | nil σ0 =>
    simp only [checkStmts, Option.some.injEq] at hCheck
    subst hCheck
    exact hInv
  | cons hF hSt hRest ih =>
    simp only [checkStmts, hSt] at hCheck
    have hInv1 := checkStmt_sound hInv hF hSt
    exact ih hInv1 hCheck

/-!
### Concrete Verified Diamond-CFG Example & Negative Control
-/

def diamondPromoted : List LocalId := [0, 1, 2]

def diamondBlockMap : BlockId → List (LocalId × SSAId)
  | 0 => [(0, 0), (1, 1), (2, 2)]
  | 1 => [(0, 0), (1, 1), (2, 2)]
  | 2 => [(0, 0), (1, 1), (2, 2)]
  | 3 => [(0, 0), (1, 1), (2, 20)]
  | _ => []

def diamondMir : MirBody where
  entry  := 0
  locals := [0, 1, 2, 3]
  blocks := [
    (0, {
      stmts := []
      term  := .branch (.var 0) 1 2
    }),
    (1, {
      stmts := [
        .assign 2 (.add (.var 1) (.const 10)),
        .writeRef 3 (.const 100)
      ]
      term  := .jump 3
    }),
    (2, {
      stmts := [
        .assign 2 (.add (.var 1) (.const 20)),
        .writeRef 3 (.const 200)
      ]
      term  := .jump 3
    }),
    (3, {
      stmts := []
      term  := .ret (.add (.var 2) (.var 3))
    })
  ]

def diamondSSA : AnSSABody where
  entry  := 0
  locals := [0, 1, 2, 3]
  blocks := [
    (0, {
      params := []
      stmts  := []
      term   := .branch (.ssaVar 0) 1 [] 2 []
    }),
    (1, {
      params := []
      stmts  := [
        .letBind 11 (.add (.ssaVar 1) (.const 10)),
        .writeRef 3 (.const 100)
      ]
      term   := .jump 3 [.ssaVar 11]
    }),
    (2, {
      params := []
      stmts  := [
        .letBind 12 (.add (.ssaVar 1) (.const 20)),
        .writeRef 3 (.const 200)
      ]
      term   := .jump 3 [.ssaVar 12]
    }),
    (3, {
      params := [20]
      stmts  := []
      term   := .ret (.add (.ssaVar 20) (.loadMem 3))
    })
  ]

/-- Check every block of `(diamondMir, diamondSSA)` with `checkBlock`. -/
def checkAllBlocks (promoted : List LocalId)
    (blockMap : BlockId → List (LocalId × SSAId))
    (mir : MirBody) (ssa : AnSSABody) : Bool :=
  (mir.entry == ssa.entry) &&
  (mir.locals == ssa.locals) &&
  mir.blocks.all (fun (bb, mBlk) =>
    match findSSABlock ssa bb with
    | none => false
    | some sBlk => checkBlock promoted blockMap ssa bb mBlk sBlk)

/-- `checkAllBlocks` succeeds on `(diamondMir, diamondSSA)` in linear time. -/
theorem diamond_mem2reg_validated :
    checkAllBlocks diamondPromoted diamondBlockMap diamondMir diamondSSA = true := by
  decide

/-- Both branches of `(diamondMir, diamondSSA)` produce identical terminal
outcomes (`115` on the true branch and `225` on the false branch). -/
theorem diamond_true_branch_equiv :
    let q : ExecQuery (Env LocalId) :=
      { input := [(0, 1), (1, 5), (2, 0), (3, 0)], fuel := 3 }
    MirLang.eval diamondMir q =
      some (.returns 115) ∧
    π_ssa diamondMir.locals diamondBlockMap
      ((AnSSALang (diamondBlockMap 0)).eval diamondSSA) q =
      some (.returns 115) := by
  decide

theorem diamond_false_branch_equiv :
    let q : ExecQuery (Env LocalId) :=
      { input := [(0, 0), (1, 5), (2, 0), (3, 0)], fuel := 3 }
    MirLang.eval diamondMir q =
      some (.returns 225) ∧
    π_ssa diamondMir.locals diamondBlockMap
      ((AnSSALang (diamondBlockMap 0)).eval diamondSSA) q =
      some (.returns 225) := by
  decide

/-- Furthermore, at every intermediate step `fuel ∈ {0, 1, 2, 3}`, the projected
`SSAState` (`projSSAState diamondMir.locals diamondBlockMap`) equals the exact
`MirState`! -/
theorem diamond_all_steps_exact_simulation :
    let inputT := [(0, 1), (1, 5), (2, 0), (3, 0)]
    let inputF := [(0, 0), (1, 5), (2, 0), (3, 0)]
    (∀ f ∈ [0, 1, 2, 3],
      MirLang.eval diamondMir { input := inputT, fuel := f } =
      π_ssa diamondMir.locals diamondBlockMap
        ((AnSSALang (diamondBlockMap 0)).eval diamondSSA)
        { input := inputT, fuel := f }) ∧
    (∀ f ∈ [0, 1, 2, 3],
      MirLang.eval diamondMir { input := inputF, fuel := f } =
      π_ssa diamondMir.locals diamondBlockMap
        ((AnSSALang (diamondBlockMap 0)).eval diamondSSA)
        { input := inputF, fuel := f }) := by
  decide

/-- **Negative Control (Illegal Promotion of an Address-Taken Local):**
Suppose a buggy `mem2reg` pass promotes local `3` (`m`) into SSA register `30`
even though `writeRef 3 (.const 99)` mutates `m` via an aliased reference. -/
def aliasedMir : MirBody where
  entry  := 0
  locals := [3]
  blocks := [
    (0, {
      stmts := [
        .assign 3 (.const 10),
        .writeRef 3 (.const 99)
      ]
      term := .ret (.var 3)
    })
  ]

def illegallyPromotedSSA : AnSSABody where
  entry  := 0
  locals := [3]
  blocks := [
    (0, {
      params := []
      stmts := [
        .letBind 30 (.const 10),
        .writeRef 3 (.const 99)
      ]
      -- Reads the stale SSA register `30` (10) instead of memory local `3` (99)!
      term := .ret (.ssaVar 30)
    })
  ]

def badBlockMap : BlockId → List (LocalId × SSAId)
  | _ => [(3, 30)]

/-- 1. Our translation validator `checkAllBlocks` rejects `illegallyPromotedSSA`
because local `3` is in `promoted = [3]` while `MirStmt.writeRef 3` mutates it. -/
theorem validator_rejects_illegal_promotion :
    checkAllBlocks [3] badBlockMap aliasedMir illegallyPromotedSSA = false := by
  decide

/-- 2. `illegallyPromotedSSA` does NOT compile `aliasedMir`: on `fuel = 1`,
`aliasedMir` returns `99`, whereas `illegallyPromotedSSA` returns `10`. -/
theorem illegal_promotion_refutes_compiles :
    ¬ Compiles MirLang (AnSSALang [(3, 30)]) (π_ssa [3] badBlockMap)
        aliasedMir illegallyPromotedSSA := by
  intro hComp
  have hq := hComp { input := [], fuel := 1 }
  revert hq
  decide

/-!
## Section 2: `MaybeUninit<T>`, Padding Bytes, and `freeze` vs. Multi-Valued `undef`
-/

inductive ByteVal where
  | uninit : ByteVal
  | init   : BitVec 8 → ByteVal
  deriving DecidableEq, Repr

/-- Coherent `freeze`: resolves `.uninit` once at the promotion site using a
deterministic oracle bit-pattern `oracleBits`, producing a single `BitVec 8`
bound to the SSA register. -/
def freezeByte (oracleBits : BitVec 8) : ByteVal → BitVec 8
  | .uninit => oracleBits
  | .init b => b

/-- Expressions over promoted `BitVec 8` SSA registers. -/
inductive BitExpr where
  | var (id : SSAId)
  | eq (e1 e2 : BitExpr)
  | sub (e1 e2 : BitExpr)
  deriving DecidableEq, Repr

/-- Standard single-valued SSA evaluation after `freeze`-on-promotion: every
reference to `var id` reads the same bound `BitVec 8` from `env`. -/
def evalFrozenBitExpr (env : SSAId → BitVec 8) : BitExpr → BitVec 8
  | .var id    => env id
  | .eq e1 e2  => if evalFrozenBitExpr env e1 == evalFrozenBitExpr env e2 then 1#8 else 0#8
  | .sub e1 e2 => evalFrozenBitExpr env e1 - evalFrozenBitExpr env e2

/-- Common subexpression elimination / copy propagation replacing `var y` with
`var x` after `let y = x`. -/
def substVar (target replacement : SSAId) : BitExpr → BitExpr
  | .var id    => if id == target then .var replacement else .var id
  | .eq e1 e2  => .eq (substVar target replacement e1) (substVar target replacement e2)
  | .sub e1 e2 => .sub (substVar target replacement e1) (substVar target replacement e2)

/-- **Soundness of `freeze`-on-Promotion under Copy Propagation / CSE:**
When `x` is promoted via `freezeByte oracleBits bVal` and `y` is a copy of `x`
(`env y = env x`), substituting `x` for `y` preserves exact expression semantics
for **every** `ByteVal` (both `.init b` and `.uninit`) and **every** `oracleBits`! -/
theorem freeze_copy_prop_sound (oracleBits : BitVec 8) (bVal : ByteVal)
    (x y : SSAId) (e : BitExpr) :
    let v := freezeByte oracleBits bVal
    let env := fun id => if id == x || id == y then v else 0#8
    evalFrozenBitExpr env (substVar y x e) = evalFrozenBitExpr env e := by
  intro v env
  induction e with
  | var id =>
    simp only [substVar]
    split
    · rename_i hEq
      have hIdY : id = y := beq_iff_eq.mp hEq
      subst hIdY
      simp [evalFrozenBitExpr, env]
    · rfl
  | eq e1 e2 ih1 ih2 =>
    simp [substVar, evalFrozenBitExpr, ih1, ih2]
  | sub e1 e2 ih1 ih2 =>
    simp [substVar, evalFrozenBitExpr, ih1, ih2]

/-- In particular, for any `ByteVal` (`uninit` or `init b`), after `freeze`
promotion, `x == y` (where `y = x`) and `x == x` both evaluate to `1#8` (`true`),
and `x - y` / `x - x` both evaluate to `0#8`. -/
theorem freeze_self_eq_and_sub_zero (oracleBits : BitVec 8) (bVal : ByteVal) :
    let v := freezeByte oracleBits bVal
    let env := fun (_ : SSAId) => v
    evalFrozenBitExpr env (.eq (.var 0) (.var 0)) = 1#8 ∧
    evalFrozenBitExpr env (.sub (.var 0) (.var 0)) = 0#8 := by
  intro v env
  simp [evalFrozenBitExpr]

/-- **Multi-Valued `undef` Semantics (Counterexample):**
Under multi-valued `undef` promotion, each read of an `.uninit` SSA variable in
`eq (var 0) (var 0)` can pick an independent witness `(w1, w2 : BitVec 8)`. -/
structure UndefQuery where
  slotVal : ByteVal
  w1      : BitVec 8
  w2      : BitVec 8
  deriving DecidableEq, Repr

/-- Source language: coherent `freeze` at promotion time (uses `w1` once to
freeze `.uninit`, so both operands of `eq (var 0) (var 0)` see the same byte). -/
def FrozenSelfEqLang : Language Unit (UndefQuery → PrefixOutcome Unit (BitVec 8)) where
  eval _ q :=
    let v := freezeByte q.w1 q.slotVal
    .returns (if v == v then 1#8 else 0#8)

/-- Target language: multi-valued `undef` promotion (when `slotVal = .uninit`,
the first read of `var 0` resolves to `q.w1` and the second read of `var 0`
resolves to `q.w2`). -/
def MultiUndefSelfEqLang : Language Unit (UndefQuery → PrefixOutcome Unit (BitVec 8)) where
  eval _ q :=
    let v1 := freezeByte q.w1 q.slotVal
    let v2 := freezeByte q.w2 q.slotVal
    .returns (if v1 == v2 then 1#8 else 0#8)

/-- **Unsoundness of Multi-Valued `undef` Promotion:**
Promoting `.uninit` to a multi-valued `undef` SSA variable refutes `Compiles`
because for `slotVal = .uninit`, `w1 = 0#8`, `w2 = 1#8`, the source returns
`1#8` (`true`) while the target returns `0#8` (`false`). -/
theorem multi_undef_refutes_compiles :
    ¬ Compiles FrozenSelfEqLang MultiUndefSelfEqLang _root_.id () () := by
  intro hComp
  have hq := hComp { slotVal := .uninit, w1 := 0#8, w2 := 1#8 }
  revert hq
  decide

/-!
## Section 3: `TagEncoding::Niche` Wrapping Modular Subtraction & Range-Metadata Hazard
-/

structure NicheLayout (w : Nat) where
  untaggedVariant    : BitVec w
  nicheVariantsStart : BitVec w
  nicheSpan          : BitVec w
  nicheStart         : BitVec w
  deriving DecidableEq, Repr

/-- Encode a niche-tagged variant at relative offset `relIdx` (`0 ≤ᵤ relIdx ≤ᵤ nicheSpan`),
corresponding to variant index `nicheVariantsStart + relIdx`. -/
def encodeNicheRel {w : Nat} (L : NicheLayout w) (relIdx : BitVec w) : BitVec w :=
  L.nicheStart + relIdx

/-- Decode any `w`-bit tag into a variant index using `rustc`'s exact wrapping
modular subtraction algorithm (`(tag - nicheStart) ≤ᵤ nicheSpan`). -/
def decodeNicheTag {w : Nat} (L : NicheLayout w) (tag : BitVec w) : BitVec w :=
  let relDiscr := tag - L.nicheStart
  if BitVec.ule relDiscr L.nicheSpan then
    L.nicheVariantsStart + relDiscr
  else
    L.untaggedVariant

/-- Algebraic helper: `(a + b) - a = b` in `BitVec w` for all bitwidths `w`,
even when `a + b` wraps modulo $2^w$. -/
theorem bitvec_add_sub_cancel {w : Nat} (a b : BitVec w) :
    (a + b) - a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, Nat.add_mod_mod]
  have ha : a.toNat < 2 ^ w := a.isLt
  have hb : b.toNat < 2 ^ w := b.isLt
  have hEq : 2 ^ w - a.toNat + (a.toNat + b.toNat) = 2 ^ w + b.toNat := by omega
  rw [hEq, Nat.add_mod_left, Nat.mod_eq_of_lt hb]

/-- **Universal Soundness for Tagged Niche Variants (Any Bitwidth `w`):**
For any niche layout `L : NicheLayout w` and any relative niche index `relIdx`
within `0 ..= L.nicheSpan`, decoding `encodeNicheRel L relIdx` recovers the
exact variant index `L.nicheVariantsStart + relIdx`, even when `L.nicheStart +
relIdx` wraps around $2^w$! -/
theorem decode_encode_niche_tagged {w : Nat} (L : NicheLayout w) (relIdx : BitVec w)
    (hInRange : BitVec.ule relIdx L.nicheSpan = true) :
    decodeNicheTag L (encodeNicheRel L relIdx) = L.nicheVariantsStart + relIdx := by
  simp [decodeNicheTag, encodeNicheRel, bitvec_add_sub_cancel, hInRange]

/-- **Universal Soundness for Untagged Payload Values (Any Bitwidth `w`):**
For any payload bit-pattern `payload : BitVec w` of the untagged variant whose
modular distance from `L.nicheStart` exceeds `L.nicheSpan` (i.e., `payload` is
outside the reserved niche range), `decodeNicheTag L payload` returns
`L.untaggedVariant`. -/
theorem decode_encode_niche_untagged {w : Nat} (L : NicheLayout w) (payload : BitVec w)
    (hOutsideNiche : BitVec.ule (payload - L.nicheStart) L.nicheSpan = false) :
    decodeNicheTag L payload = L.untaggedVariant := by
  simp [decodeNicheTag, hOutsideNiche]

/-- **Concrete Instantiation 1: `Option<NonZeroU8>` (`w = 8`)**
`None` is variant `0`, `Some(NonZeroU8)` is `untaggedVariant = 1`,
`nicheVariantsStart = 0`, `nicheSpan = 0`, `nicheStart = 0`. -/
def optNonZeroU8 : NicheLayout 8 where
  untaggedVariant    := 1#8
  nicheVariantsStart := 0#8
  nicheSpan          := 0#8
  nicheStart         := 0#8

theorem optNonZeroU8_exhaustive_correct :
    decodeNicheTag optNonZeroU8 0#8 = 0#8 ∧
    (∀ b : BitVec 8, b != 0#8 → decodeNicheTag optNonZeroU8 b = 1#8) := by
  decide

/-- **Concrete Instantiation 2: Wrapping Multi-Variant Niche (`w = 8`)**
Suppose an untagged payload has valid range `2 ..= 253`, leaving a 4-value
wrapping niche `[254, 255, 0, 1]` (`nicheStart = 254#8`, `nicheSpan = 3#8`,
`nicheVariantsStart = 1#8`, `untaggedVariant = 0#8`).
Notice that `relIdx = 2#8` wraps to `tag = 0#8` and `relIdx = 3#8` wraps to
`tag = 1#8`, and `decodeNicheTag` decodes all 256 byte values without error! -/
def wrappingNiche8 : NicheLayout 8 where
  untaggedVariant    := 0#8
  nicheVariantsStart := 1#8
  nicheSpan          := 3#8
  nicheStart         := 254#8

theorem wrappingNiche8_verified :
    decodeNicheTag wrappingNiche8 (encodeNicheRel wrappingNiche8 0#8) = 1#8 ∧
    decodeNicheTag wrappingNiche8 (encodeNicheRel wrappingNiche8 1#8) = 2#8 ∧
    decodeNicheTag wrappingNiche8 (encodeNicheRel wrappingNiche8 2#8) = 3#8 ∧
    decodeNicheTag wrappingNiche8 (encodeNicheRel wrappingNiche8 3#8) = 4#8 ∧
    encodeNicheRel wrappingNiche8 2#8 = 0#8 ∧
    encodeNicheRel wrappingNiche8 3#8 = 1#8 ∧
    (∀ b : BitVec 8, BitVec.ule 2#8 b && BitVec.ule b 253#8 →
      decodeNicheTag wrappingNiche8 b = 0#8) := by
  decide

/-- Correct MIR / `AnSSA` discriminant lowering: loads `tag` under the outer
enum's full validity range and decodes via `decodeNicheTag`. -/
def SoundNicheDiscrLang : Language (NicheLayout 8) (BitVec 8 → PrefixOutcome Unit (BitVec 8)) where
  eval L tag := .returns (decodeNicheTag L tag)

/-- Buggy lowering that attaches the untagged payload's non-zero validity range
(`tag != 0#8`) to the scalar load prior to decoding the discriminant. -/
def PrematurePayloadRangeLang : Language (NicheLayout 8) (BitVec 8 → PrefixOutcome Unit (BitVec 8)) where
  eval L tag :=
    if tag == 0#8 then
      .ub
    else
      .returns (decodeNicheTag L tag)

/-- **Unsoundness of Premature Payload Range Metadata:**
Attaching the untagged payload's non-zero range invariant before decoding
`optNonZeroU8` triggers target `.ub` on `None` (`0#8`) and refutes `Compiles`! -/
theorem premature_payload_range_unsound :
    ¬ Compiles SoundNicheDiscrLang PrematurePayloadRangeLang _root_.id
        optNonZeroU8 optNonZeroU8 := by
  intro hComp
  have hNone := hComp 0#8
  revert hNone
  decide

/-!
## Section 4: Zero-Sized Types (`ZST`) Load/Store Elision on Dangling Pointers
-/

structure PtrAccessQuery where
  addr      : Nat
  size      : Nat
  allocSize : Nat
  deriving DecidableEq, Repr

/-- In Rust's operational semantics (`rust-lang/reference` and Miri), a typed
copy of `size` bytes at `addr` in an allocation of size `allocSize` (with
aligned non-zero address `addr > 0`) is valid iff `size == 0` or
`addr + size ≤ allocSize`. -/
def mirTypedCopyValid (q : PtrAccessQuery) : Bool :=
  (q.addr > 0) && ((q.size == 0) || (q.addr + q.size <= q.allocSize))

def MirPlaceReadLang : Language Nat (PtrAccessQuery → PrefixOutcome Unit Nat) where
  eval typeSize q :=
    if mirTypedCopyValid { q with size := typeSize } then
      .returns 0
    else
      .ub

/-- `AnSSA` / `rustc_codegen_ssa` ZST-aware lowering: if `typeSize == 0`,
immediately produces the unit ZST value `0` (after checking non-null alignment
`addr > 0`) without touching memory; otherwise performs a sized memory load. -/
def ZSTAwareSSALang : Language Nat (PtrAccessQuery → PrefixOutcome Unit Nat) where
  eval typeSize q :=
    if typeSize == 0 then
      if q.addr > 0 then .returns 0 else .ub
    else
      if (q.addr > 0) && (q.addr + typeSize <= q.allocSize) then
        .returns 0
      else
        .ub

/-- Naive lowering that always touches at least 1 byte in memory (`addr + 1 ≤
allocSize`), even when `typeSize == 0`. -/
def NaiveHardwareLoadLang : Language Nat (PtrAccessQuery → PrefixOutcome Unit Nat) where
  eval typeSize q :=
    let effectiveSize := if typeSize == 0 then 1 else typeSize
    if (q.addr > 0) && (q.addr + effectiveSize <= q.allocSize) then
      .returns 0
    else
      .ub

/-- **Soundness of ZST Load Elision:**
For every `typeSize : Nat` (both `0` for ZSTs and `> 0` for sized types),
`ZSTAwareSSALang` refines `MirPlaceReadLang`. -/
theorem zst_elision_compiles (typeSize : Nat) :
    Compiles MirPlaceReadLang ZSTAwareSSALang _root_.id typeSize typeSize := by
  intro q
  simp only [MirPlaceReadLang, ZSTAwareSSALang, mirTypedCopyValid, _root_.id]
  by_cases hZero : typeSize == 0
  · simp [hZero]
    exact Preorder.le_refl _
  · simp [hZero]
    exact Preorder.le_refl _

/-- **Unsoundness of Emitting a Hardware Load for ZSTs:**
For `typeSize = 0` on `NonNull::<()>::dangling()` (`addr = 1, allocSize = 0`),
`MirPlaceReadLang` succeeds (`.returns 0`), while `NaiveHardwareLoadLang` faults
(`.ub`), refuting `Compiles`. -/
theorem naive_zst_load_refutes_compiles :
    ¬ Compiles MirPlaceReadLang NaiveHardwareLoadLang _root_.id 0 0 := by
  intro hComp
  have hDangling := hComp { addr := 1, size := 0, allocSize := 0 }
  revert hDangling
  decide

/-!
## Section 4B: `Rvalue::Use(op, WithRetag)` and `SROA` Retag Preservation (`rustc` PR `#154341`)

### Rust Correspondence
- In `rustc` commit `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`),
  explicit `StatementKind::Retag` was removed in favor of carrying a boolean
  `WithRetag` flag on `Rvalue::Use(Operand, WithRetag)`
  (`compiler/rustc_middle/src/mir/syntax.rs:497-511, 1359-1360`).
- When `WithRetag::Yes` is set, copying a value recursively walks its layout
  (`compiler/rustc_codegen_ssa/src/mir/retag.rs:67-263`) and retags every nested
  reference (`&T`, `&mut T`, global `Box<T>`) except inside `!Unpin` (`UnsafePinned`)
  or `UnsafeCell` (`!Freeze`) or `MaybeDangling`.
- Consequently, when `SROA` (`compiler/rustc_mir_transform/src/sroa.rs:347, 373,
  409-413`) flattens an aggregate copy `lhs = Rvalue::Use(Operand::Copy(rhs),
  retag)` into per-field scalar copies, it MUST thread `retag` to each replaced
  field projection. If an SROA pass drops `WithRetag::Yes` when promoting a
  struct containing a `&mut T` field, an aliasing violation that triggers
  source MIR UB under Tree Borrows / Stacked Borrows goes undetected in the
  target, or—if a subsequent pass relies on the retag's uniqueness guarantee—
  miscompiles downstream optimizations.
-/

inductive FieldKind where
  | uniqueMutRef        -- `&mut T` where `T: Unpin`
  | pinnedMutRef        -- `&mut T` where `T: !Unpin` (`UnsafePinned`)
  | sharedRefFreeze     -- `&T` where `T: Freeze` (no `UnsafeCell`)
  | sharedRefUnsafeCell -- `&T` containing `UnsafeCell` (`!Freeze`)
  | rawScalar           -- integer / raw pointer (`*mut T`)
  deriving DecidableEq, Repr

/-- Exact ABI / retag eligibility predicate matching
`compiler/rustc_ty_utils/src/abi.rs:350-410` and
`compiler/rustc_codegen_ssa/src/mir/retag.rs:144-255`. -/
def fieldNeedsNoaliasRetag : FieldKind → Bool
  | .uniqueMutRef        => true
  | .pinnedMutRef        => false
  | .sharedRefFreeze     => true
  | .sharedRefUnsafeCell => false
  | .rawScalar           => false

/-- Check that `fieldNeedsNoaliasRetag` suppresses `noalias`/retag on `!Unpin`
mutable references and `UnsafeCell`-bearing shared references while enabling it
on `Unpin` mutable references and `Freeze` shared references. -/
theorem retag_eligibility_classification :
    fieldNeedsNoaliasRetag .uniqueMutRef = true ∧
    fieldNeedsNoaliasRetag .pinnedMutRef = false ∧
    fieldNeedsNoaliasRetag .sharedRefFreeze = true ∧
    fieldNeedsNoaliasRetag .sharedRefUnsafeCell = false ∧
    fieldNeedsNoaliasRetag .rawScalar = false := by
  decide

/-!
## Section 5: Kernel Axiom Audit (`#guard_msgs in #print axioms`)

Every theorem in this probe is verified by the Lean 4.34.1 kernel with zero
`sorryAx` and zero `Lean.ofReduceBool`.
-/

/-- info: 'Track3Probe.Compiles.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Compiles.trans

/-- info: 'Track3Probe.runSteps_reaches' does not depend on any axioms -/
#guard_msgs in
#print axioms runSteps_reaches

/-- info: 'Track3Probe.π_ssa_monotone' depends on axioms: [propext] -/
#guard_msgs in
#print axioms π_ssa_monotone

/-- info: 'Track3Probe.checkExpr_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkExpr_sound

/-- info: 'Track3Probe.checkStmt_assign_promoted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkStmt_assign_promoted_sound

/-- info: 'Track3Probe.checkStmt_writeRef_unpromoted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkStmt_writeRef_unpromoted_sound

/-- info: 'Track3Probe.checkStmts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkStmts_sound

/-- info: 'Track3Probe.diamond_mem2reg_validated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms diamond_mem2reg_validated

/-- info: 'Track3Probe.diamond_true_branch_equiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms diamond_true_branch_equiv

/-- info: 'Track3Probe.diamond_false_branch_equiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms diamond_false_branch_equiv

/-- info: 'Track3Probe.diamond_all_steps_exact_simulation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms diamond_all_steps_exact_simulation

/-- info: 'Track3Probe.validator_rejects_illegal_promotion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms validator_rejects_illegal_promotion

/-- info: 'Track3Probe.illegal_promotion_refutes_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms illegal_promotion_refutes_compiles

/-- info: 'Track3Probe.freeze_copy_prop_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms freeze_copy_prop_sound

/-- info: 'Track3Probe.multi_undef_refutes_compiles' does not depend on any axioms -/
#guard_msgs in
#print axioms multi_undef_refutes_compiles

/-- info: 'Track3Probe.decode_encode_niche_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decode_encode_niche_tagged

/-- info: 'Track3Probe.decode_encode_niche_untagged' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decode_encode_niche_untagged

/-- info: 'Track3Probe.optNonZeroU8_exhaustive_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms optNonZeroU8_exhaustive_correct

/-- info: 'Track3Probe.wrappingNiche8_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrappingNiche8_verified

/-- info: 'Track3Probe.premature_payload_range_unsound' does not depend on any axioms -/
#guard_msgs in
#print axioms premature_payload_range_unsound

/-- info: 'Track3Probe.zst_elision_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zst_elision_compiles

/-- info: 'Track3Probe.naive_zst_load_refutes_compiles' does not depend on any axioms -/
#guard_msgs in
#print axioms naive_zst_load_refutes_compiles

end Track3Probe
