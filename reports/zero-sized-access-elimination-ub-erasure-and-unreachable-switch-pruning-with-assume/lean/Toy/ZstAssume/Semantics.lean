import Toy.ZstAssume.Syntax

/-!
# Small-step semantics, behaviours, refinement and weakest preconditions

The language is deterministic: from each configuration there is exactly one run.
Runs are explored by a fuel-indexed iteration `run n` of the step function; the four
behaviours (termination, UB after a finite trace, silent divergence after a finite
trace, and reactive divergence with an infinite trace) are defined from all finite
prefixes of the run, without coinduction.

Two UB disciplines are defined, and both appear in theorem names:
* *prefix-preserving* (`PP`): UB after trace `t` admits every behaviour whose trace
  extends `t` (CompCert-style "goes wrong after `t`");
* *whole-trace* (`WT`): UB anywhere in a run admits every behaviour for that input.
-/

namespace Toy.ZstAssume

/-- A configuration: the current block label, the statements of that block that
remain to execute, and the state. When `rest = []` the terminator executes next. -/
structure Cfg where
  lbl : Label
  rest : List Stmt
  st : State

/-- The configuration at the entry of block `b`. -/
def Prog.entry (P : Prog) (b : Label) (st : State) : Cfg := ⟨b, (P.blk b).stmts, st⟩

/-- The initial configuration for input state `σ`: the entry of block `0`. -/
def Prog.init (P : Prog) (σ : State) : Cfg := P.entry 0 σ

/-- The configuration at program point `(l, i)` (before the `i`-th statement of block
`l`; `i ≥` the number of statements denotes the terminator) in state `st`. -/
def Prog.at (P : Prog) (l : Label) (i : Nat) (st : State) : Cfg :=
  ⟨l, (P.blk l).stmts.drop i, st⟩

/-- The label a `switch` on value `x` jumps to: the first arm whose value is `x`,
otherwise `ow`. -/
def selectTarget : List (Int × Label) → Label → Int → Label
  | [], ow, _ => ow
  | (v, b) :: arms, ow, x => if x = v then b else selectTarget arms ow x

/-- Result of one step: a successor configuration with an optional emitted value,
normal termination in a final state, or UB. -/
inductive StepResult where
  | next (out : Option Int) (c : Cfg)
  | halt (s : State)
  | ub

/-- Execute one statement: `none` is UB; otherwise the optional emitted value and the
new state. -/
def execStmt (K : ZContract) (stmt : Stmt) (s : State) : Option (Option Int × State) :=
  match stmt with
  | .emit e => some (some (e.eval s), s)
  | .assign x e => some (none, s.set x (e.eval s))
  | other => if other.pre K s then some (none, s) else none

/-- One small step of program `P` under zero-size contract `K`. -/
def step (K : ZContract) (P : Prog) (c : Cfg) : StepResult :=
  match c.rest with
  | stmt :: rest =>
      match execStmt K stmt c.st with
      | some (o, s') => .next o ⟨c.lbl, rest, s'⟩
      | none => .ub
  | [] =>
      match (P.blk c.lbl).term with
      | .goto b => .next none (P.entry b c.st)
      | .switch x arms ow => .next none (P.entry (selectTarget arms ow (c.st.locals x)) c.st)
      | .unreachable => .ub
      | .halt => .halt c.st

/-- Outcome of running with bounded fuel: terminated (trace, final state), UB after a
trace, or still running (reached configuration, trace so far). -/
inductive Outcome where
  | done (t : List Int) (s : State)
  | ub (t : List Int)
  | running (c : Cfg) (t : List Int)

/-- Prepend an optional emitted value to the trace of an outcome. -/
def Outcome.cons (o : Option Int) : Outcome → Outcome
  | .done t s => .done (o.toList ++ t) s
  | .ub t => .ub (o.toList ++ t)
  | .running c t => .running c (o.toList ++ t)

/-- The trace of an outcome. -/
def Outcome.trace : Outcome → List Int
  | .done t _ => t
  | .ub t => t
  | .running _ t => t

/-- Whether the outcome is still running. -/
def Outcome.isRunning : Outcome → Bool
  | .running _ _ => true
  | _ => false

/-- `run K P n c`: perform up to `n` steps from `c`. -/
def run (K : ZContract) (P : Prog) : Nat → Cfg → Outcome
  | 0, c => .running c []
  | n + 1, c =>
      match step K P c with
      | .next o c' => (run K P n c').cons o
      | .halt s => .done [] s
      | .ub => .ub []

/-- Behaviours. `term t`: terminates after emitting `t`. `wrong t`: reaches UB after
emitting `t`. `div t`: runs forever, emitting exactly `t` in total. `react f`: runs
forever, emitting the infinite sequence `f 0, f 1, …`. Behaviours record emitted
values only: `term t` forgets the final state (locals and memory), so refinement and
equivalence below say nothing about final states, whereas `wp` does observe them. -/
inductive Beh where
  | term (t : List Int)
  | wrong (t : List Int)
  | div (t : List Int)
  | react (f : Nat → Int)

/-- The first `k` values of an infinite sequence. -/
def prefixOf (f : Nat → Int) (k : Nat) : List Int := (List.range k).map f

/-- The behaviours of the run from configuration `c`. Each step emits at most one
value. That exactly one behaviour holds from every configuration is proved
separately (`hasBehFrom_exists`, `hasBehFrom_unique`). -/
def HasBehFrom (K : ZContract) (P : Prog) (c : Cfg) : Beh → Prop
  | .term t => ∃ n s, run K P n c = .done t s
  | .wrong t => ∃ n, run K P n c = .ub t
  | .div t => (∀ n, (run K P n c).isRunning = true) ∧
      ∃ N, ∀ n, N ≤ n → (run K P n c).trace = t
  | .react f => (∀ n, (run K P n c).isRunning = true) ∧
      ∀ k, ∃ n, (run K P n c).trace = prefixOf f k

/-- The behaviours of program `P` on input state `σ`. -/
def HasBeh (K : ZContract) (P : Prog) (σ : State) (b : Beh) : Prop :=
  HasBehFrom K P (P.init σ) b

/-- The run from `c` reaches UB after emitting exactly `t`. -/
def GoesWrongFrom (K : ZContract) (P : Prog) (c : Cfg) (t : List Int) : Prop :=
  ∃ n, run K P n c = .ub t

/-- `t` is a (finite) prefix of the trace of behaviour `b`. -/
def Beh.HasPrefix : Beh → List Int → Prop
  | .term u, t => t <+: u
  | .wrong u, t => t <+: u
  | .div u, t => t <+: u
  | .react f, t => t = prefixOf f t.length

/-- Prefix-preserving improvement: the target behaviour `bt` equals the source
behaviour `bs`, or `bs` is UB after a prefix of `bt`'s trace. -/
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t

/-- Whole-trace improvement: `bt = bs`, or `bs` is UB (after any trace). -/
def ImprovesWT (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t

/-- `RefinesPP K src tgt`: the target `tgt` refines the source `src` under the
prefix-preserving UB discipline — on every input, every target behaviour improves
some source behaviour. -/
def RefinesPP (K : ZContract) (src tgt : Prog) : Prop :=
  ∀ σ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesPP bt bs

/-- `RefinesWT K src tgt`: the target `tgt` refines the source `src` under the
whole-trace UB discipline. -/
def RefinesWT (K : ZContract) (src tgt : Prog) : Prop :=
  ∀ σ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesWT bt bs

/-- Prefix-preserving equivalence: refinement in both directions. -/
def EquivPP (K : ZContract) (p q : Prog) : Prop := RefinesPP K p q ∧ RefinesPP K q p

/-- Whole-trace equivalence: refinement in both directions. -/
def EquivWT (K : ZContract) (p q : Prog) : Prop := RefinesWT K p q ∧ RefinesWT K q p

/-- `ReachableAt K P l i st`: for some input, the run of `P` reaches program point
`(l, i)` in state `st` (without UB or termination before it). This includes runs
that reach UB later. -/
def ReachableAt (K : ZContract) (P : Prog) (l : Label) (i : Nat) (st : State) : Prop :=
  ∃ σ n t, run K P n (P.init σ) = .running (P.at l i st) t

/-- `UBFree K P`: no input makes `P` reach UB (the semantic property; a checker's
verdict is a separate notion). -/
def UBFree (K : ZContract) (P : Prog) : Prop :=
  ∀ σ t, ¬ HasBeh K P σ (.wrong t)

/-- Total-correctness weakest precondition from a configuration: the run terminates
without UB, and the postcondition holds of the emitted trace and the final state.
It is demonic: UB and divergence (silent or not) both make it false. With the UB-on-false
`assume`, the rules are `wp (assume c) Q = c ∧ wp Q` (`wpFrom_assume`) and
`wp unreachable Q = False` (`wpFrom_unreachable`), as for `assert c` and `abort` in
Dijkstra-style calculi. Partial correctness (`wlp`) is not defined here. -/
def wpFrom (K : ZContract) (P : Prog) (Q : List Int → State → Prop) (c : Cfg) : Prop :=
  ∃ n t s, run K P n c = .done t s ∧ Q t s

/-- Total-correctness weakest precondition of a program on input `σ`. -/
def wp (K : ZContract) (P : Prog) (Q : List Int → State → Prop) (σ : State) : Prop :=
  wpFrom K P Q (P.init σ)

/-- `FactOnDefinedRuns K P l i F`: the state predicate `F` holds at program point
`(l, i)` on every run that never reaches UB (a "UB-derived fact" when it fails on some
run that later reaches UB). The condition is on the whole run: a run reaching `(l, i)`
is excluded if it reaches UB at any later point, also after emitting further values.
Every predicate holds vacuously for a program all of whose runs reach UB
(`factOnDefinedRuns_unreach`). -/
def FactOnDefinedRuns (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (F : State → Prop) : Prop :=
  ∀ σ st, (∃ n t, run K P n (P.init σ) = .running (P.at l i st) t) →
    (∀ t, ¬ HasBeh K P σ (.wrong t)) → F st

end Toy.ZstAssume
