import Toy.PlaceEval.Lang

/-!
# Small-step semantics, behaviours and refinement

For a fixed allocation mode the language is deterministic. Runs are explored by a
fuel-indexed iteration `run n`; the four behaviours (termination, UB after a finite
trace, silent divergence, reactive divergence) are defined from finite prefixes of the
run. A run that reaches a refused oracle choice (`blocked`) has no behaviour.

A semantics `Sem` is either `fresh` (behaviours of every oracle `ω`, i.e. a
nondeterministic choice of non-overlapping addresses) or `slots s` (the deterministic
static slot assignment `s`). Refinement is prefix-preserving: UB after trace `t` in the
source admits every target behaviour whose trace extends `t`.
-/

namespace Toy.PlaceEval

/-- A configuration: current label, the statements of that block still to run, state. -/
structure Cfg where
  lbl : Label
  rest : List Stmt
  st : State
deriving DecidableEq, Repr

/-- The configuration at the entry of block `b`. -/
def Prog.entry (P : Prog) (b : Label) (st : State) : Cfg := ⟨b, (P.blk b).stmts, st⟩

/-- The configuration at program point `(l, i)` (before the `i`-th statement of block
`l`; `i ≥` the number of statements denotes the terminator). -/
def Prog.at (P : Prog) (l : Label) (i : Nat) (st : State) : Cfg :=
  ⟨l, (P.blk l).stmts.drop i, st⟩

/-- Allocate the locals `xs` that have no storage markers in `P`, in order. -/
def allocEntry (mode : AllocMode) (P : Prog) : List Local → State → Option State
  | [], st => some st
  | x :: xs, st =>
    if P.hasMarkers x then allocEntry mode P xs st
    else (allocate mode st x (P.layout x)).bind (allocEntry mode P xs)

/-- The initial state: empty memory, every local unallocated, then every local without
storage markers allocated (in index order). `none` if an oracle choice is refused. -/
def Prog.initState (mode : AllocMode) (P : Prog) : Option State :=
  allocEntry mode P (List.range P.locals.length)
    ⟨⟨[], []⟩, List.replicate P.locals.length none⟩

/-- The label a `switchInt` on value `n` jumps to. -/
def selectTarget : List (Nat × Label) → Label → Nat → Label
  | [], ow, _ => ow
  | (v, b) :: arms, ow, n => if n = v then b else selectTarget arms ow n

/-- Result of one step. -/
inductive StepResult where
  | next (ev : Option Nat) (c : Cfg)
  | halt (st : State)
  | ub
  | block

/-- One small step. -/
def step (mode : AllocMode) (P : Prog) (c : Cfg) : StepResult :=
  match c.rest with
  | s :: rest =>
    match execStmt mode P c.st s with
    | .ok ev st' => .next ev ⟨c.lbl, rest, st'⟩
    | .ub => .ub
    | .block => .block
  | [] =>
    match (P.blk c.lbl).term with
    | .goto b => .next none (P.entry b c.st)
    | .switchInt o arms ow =>
      match o.evalInt c.st with
      | some n => .next none (P.entry (selectTarget arms ow n) c.st)
      | none => .ub
    | .halt => .halt c.st
    | .unreachable => .ub

/-- Outcome of a run with bounded fuel. -/
inductive Outcome where
  | done (t : List Nat) (st : State)
  | ub (t : List Nat)
  | running (c : Cfg) (t : List Nat)
  | blocked
deriving DecidableEq, Repr

/-- Prepend an optional emitted value to an outcome's trace. -/
def Outcome.cons (ev : Option Nat) : Outcome → Outcome
  | .done t s => .done (ev.toList ++ t) s
  | .ub t => .ub (ev.toList ++ t)
  | .running c t => .running c (ev.toList ++ t)
  | .blocked => .blocked

/-- The trace of an outcome (empty for `blocked`). -/
def Outcome.trace : Outcome → List Nat
  | .done t _ => t
  | .ub t => t
  | .running _ t => t
  | .blocked => []

/-- Whether the outcome is still running. -/
def Outcome.isRunning : Outcome → Bool
  | .running _ _ => true
  | _ => false

/-- `run mode P n c`: up to `n` steps from `c`. -/
def run (mode : AllocMode) (P : Prog) : Nat → Cfg → Outcome
  | 0, c => .running c []
  | n + 1, c =>
    match step mode P c with
    | .next ev c' => (run mode P n c').cons ev
    | .halt s => .done [] s
    | .ub => .ub []
    | .block => .blocked

/-- Behaviours: termination after trace `t`, UB after trace `t`, silent divergence after
emitting exactly `t`, reactive divergence emitting `f 0, f 1, …`. -/
inductive Beh where
  | term (t : List Nat)
  | wrong (t : List Nat)
  | div (t : List Nat)
  | react (f : Nat → Nat)

/-- The first `k` values of an infinite sequence. -/
def prefixOf (f : Nat → Nat) (k : Nat) : List Nat := (List.range k).map f

/-- The behaviours of the run from configuration `c` under a fixed allocation mode. -/
def HasBehFrom (mode : AllocMode) (P : Prog) (c : Cfg) : Beh → Prop
  | .term t => ∃ n s, run mode P n c = .done t s
  | .wrong t => ∃ n, run mode P n c = .ub t
  | .div t => (∀ n, (run mode P n c).isRunning = true) ∧
      ∃ N, ∀ n, N ≤ n → (run mode P n c).trace = t
  | .react f => (∀ n, (run mode P n c).isRunning = true) ∧
      ∀ k, ∃ n, (run mode P n c).trace = prefixOf f k

/-- Behaviours of `P` under a fixed allocation mode: from the initial state, if the
entry allocations are not refused. -/
def HasBehIn (mode : AllocMode) (P : Prog) (b : Beh) : Prop :=
  ∃ st0, P.initState mode = some st0 ∧ HasBehFrom mode P (P.entry 0 st0) b

/-- Semantics: nondeterministic fresh addresses, or a static slot assignment. -/
inductive Sem where
  | fresh
  | slots (s : Local → Nat)

/-- The allocation mode of a semantics for oracle `ω` (ignored by `slots`). -/
def Sem.mode : Sem → (Nat → Nat) → AllocMode
  | .fresh, ω => .fresh ω
  | .slots s, _ => .slots s

/-- The behaviours of `P` under semantics `S`: those of some oracle. -/
def HasBeh (S : Sem) (P : Prog) (b : Beh) : Prop := ∃ ω, HasBehIn (S.mode ω) P b

/-- `t` is a finite prefix of the trace of behaviour `b`. -/
def Beh.HasPrefix : Beh → List Nat → Prop
  | .term u, t => t <+: u
  | .wrong u, t => t <+: u
  | .div u, t => t <+: u
  | .react f, t => t = prefixOf f t.length

/-- Prefix-preserving improvement: `bt = bs`, or `bs` is UB after a prefix of `bt`'s
trace. -/
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t

/-- Refinement across semantics: every behaviour of `tgt` under `St` improves some
behaviour of `src` under `Ss`. -/
def RefinesAcross (Ss : Sem) (src : Prog) (St : Sem) (tgt : Prog) : Prop :=
  ∀ bt, HasBeh St tgt bt → ∃ bs, HasBeh Ss src bs ∧ ImprovesPP bt bs

/-- `RefinesPP S src tgt`: `tgt` refines `src` under semantics `S` (prefix-preserving). -/
def RefinesPP (S : Sem) (src tgt : Prog) : Prop := RefinesAcross S src S tgt

/-- Prefix-preserving equivalence: refinement in both directions. -/
def EquivPP (S : Sem) (p q : Prog) : Prop := RefinesPP S p q ∧ RefinesPP S q p

/-- `ReachableAt S P l i st`: for some oracle, the run of `P` reaches program point
`(l, i)` in state `st`. -/
def ReachableAt (S : Sem) (P : Prog) (l : Label) (i : Nat) (st : State) : Prop :=
  ∃ ω st0 n t, P.initState (S.mode ω) = some st0 ∧
    run (S.mode ω) P n (P.entry 0 st0) = .running (P.at l i st) t

/-- The run from `c` reaches UB after emitting exactly `t`, for some oracle. -/
def GoesWrongFrom (S : Sem) (P : Prog) (c : Cfg) (t : List Nat) : Prop :=
  ∃ ω n, run (S.mode ω) P n c = .ub t

/-- `UBFree S P`: no behaviour of `P` is UB (the semantic property; a checker's verdict is
a separate notion, `ExactUBChecker`). -/
def UBFree (S : Sem) (P : Prog) : Prop := ∀ t, ¬ HasBeh S P (.wrong t)

/-- `ExactUBChecker S chk`: the Boolean verdict `chk P` is `true` exactly for the programs
that are `UBFree S`. -/
def ExactUBChecker (S : Sem) (chk : Prog → Bool) : Prop := ∀ P, chk P = true ↔ UBFree S P

end Toy.PlaceEval
