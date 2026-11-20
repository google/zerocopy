# Symbolic execution soundness, path merging, and fuel bounds over a toy CFG (Lean 4)

## Summary

A toy CFG language with a fuel-indexed interpreter and a forking symbolic executor, with 20 kernel-checked results (Lean 4, no Mathlib) on when "every symbolic leaf passes" implies "every concrete run passes", what path merging and simplification must preserve, and how much fuel loop-free CFGs need:

1. **eval-subst-agrees** (theorem, T0; `eval_subst`): With no hypotheses, symbolically evaluating an expression in a symbolic store and interpreting the result under a valuation gives the same value as evaluating the expression concretely in the store obtained by instantiating the symbolic store under that valuation.
2. **per-path-soundness** (theorem, T0; `symExec_leaf_sound`): For every leaf that the forking symbolic executor `symExec` produces at fuel `f`, and every valuation satisfying that leaf's path condition, the concrete run at the same fuel `f` from the corresponding input has exactly the leaf's instantiated outcome (same final store, same panic location, or fuel exhaustion).
3. **path-coverage** (theorem, T0; `symExec_exhaustive`, `symExec_pairwise_disjoint`): With no hypotheses, at every fuel the path conditions of the leaves of `symExec` cover every valuation, and any two leaves at distinct list positions have path conditions that are never true together.
4. **leaf-check-transfer** (theorem, T1; `exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve`, `exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax`): For an arbitrary leaf list (not necessarily produced by `symExec`), per-leaf soundness at fuel `f`, exhaustiveness, and a passing strict (respectively lax) leaf check together imply that every concrete run at fuel `f` returns with a store satisfying `Q` (respectively returns with `Q` or runs out of fuel); each of the three conditions is necessary and disjointness is not needed.
5. **lax-success-iff-concrete-success-or-out-of-fuel-same-fuel** (characterization, T0; `provesLax_iff_forall_exec_okWithOrOutOfFuel`): With no hypotheses, the lax check on `symExec p f` passes exactly when every concrete run at fuel `f` either returns with a store satisfying `Q` or runs out of fuel, which is bounded safety at that fuel and says nothing about larger fuels.
6. **dropping-path-conditions-is-conservative** (theorem, T0; `leavesProve_of_leavesProve_dropPcs`, `dropPcs_false_alarm`): Replacing every path condition by `true` can only make the strict leaf check harder to pass: if the erased leaves pass, the original leaves pass, but not conversely.
7. **guarded-merge-sound** (theorem, T0; `guardedMerge_sound`): If two guarded symbolic states are each sound for the same reference and the same continuation, their merge `(c₁ ∨ c₂, x ↦ ite c₁ (σ₁ x) (σ₂ x))` is sound for them too, with no assumption that `c₁` and `c₂` are disjoint.
8. **merge-leaves-preserve-soundness-and-exhaustiveness** (theorem, T0; `mergeLeaf_preserves_leavesSound`, `mergeLeaf_leavesExhaustive_iff`): Replacing the first two successful leaves of a leaf list by their guarded merge preserves per-leaf soundness (the converse fails: see the separately proved counterexample `mergeLeaf_leavesSound_converse_fails`, quoted under **Boundaries**) and neither gains nor loses exhaustiveness, without assuming disjoint path conditions.
9. **unguarded-merge-spurious-success** (counterexample, T1; `unguardedMerge_spurious_success`): Counterexample: merging the two branch leaves of a diamond CFG without an `ite` guard yields an exhaustive leaf list that passes the strict check for `x1 = x0 + 1`, although from input `x0 = 5` the concrete run ends with `x1 = 7`.
10. **merge-behaviour-coverage-needs-agreement-on-overlap** (theorem, T1; `guardedMerge_preserves_covers_of_agree_on_overlap`): For a possibly many-valued behaviour relation and a common continuation, replacing the first two states of a covering list by their guarded merge keeps the list covering provided the two states agree, through the continuation, wherever both guards hold; without that agreement a behaviour can be lost.
11. **concrete-fuel-monotonicity** (theorem, T0; `exec_fuel_mono`): If a concrete run at fuel `f` does not run out of fuel, then the run at every fuel `f' ≥ f` has exactly the same outcome.
12. **strict-success-monotone-in-fuel** (theorem, T0; `provesStrict_mono`, `exec_okWith_of_provesStrict_of_le`): If the strict check passes at fuel `f`, it passes at every fuel `f' ≥ f`, and every concrete run at fuel `f'` returns with a store satisfying `Q`.
13. **out-of-fuel-is-not-success** (counterexample, T1; `provesLax_loopThenAssertFalse_but_panics`, `provesLax_selfLoop_every_fuel_but_never_returns`): Counterexample: accepting out-of-fuel leaves as success "proves" postcondition `False` for a loop that panics after three iterations (at fuel 4) and for an infinite loop (at every fuel).
14. **loop-free-fuel-bound-sufficient** (theorem, T1; `acyclic_exec_ne_outOfFuel_of_fuelBound_le`): For every acyclic CFG (some ranking of blocks strictly increases along every edge between existing blocks), every fuel at least `#statements + #blocks` is enough: no concrete run runs out of fuel.
15. **straight-line-fuel-bound-minimal** (theorem, T1; `straightLine_fuelBound_le_of_exec_ok`, `straightLine_exec_ok_iff_fuelBound_minimal`): For nonempty straight-line CFGs, a run that returns needs at least `#statements + #blocks` fuel, and it returns a store `s` at some fuel exactly when it returns `s` at that fuel and runs out of fuel at every smaller one.
16. **simplifier-soundness-characterization** (characterization, T1; `simpSoundUnder_iff_preserves_guardedSound`): A term simplifier preserves interpretation under every valuation satisfying path condition `c` if and only if rewriting every term of a state guarded by `c` (leaving `c` itself unchanged) preserves guarded soundness for every result type, reference and continuation.
17. **path-specific-simplification-breaks-merge** (counterexample, T1; `pathSimp_after_merge_breaks_soundness`): Counterexample: the rewrite `x0 ↦ 0`, sound under one branch's path condition, breaks soundness when applied to the guarded merge of both branches, because it also rewrites the merge guard; from `x0 = 5` the rewritten leaf claims `x1 = 1` while the run ends with `x1 = 7`.
18. **strict-success-iff-concrete-success-same-fuel** (characterization, T0; `provesStrict_iff_forall_exec_okWith`): With no hypotheses (cyclic CFGs allowed), the strict check on `symExec p f` passes exactly when every concrete run at the same fuel `f` returns with a store satisfying `Q`.
19. **loop-free-completeness-at-fuel-bound** (characterization, T1; `acyclic_provesStrict_fuelBound_iff_forall_exists_fuel`): For acyclic CFGs, the strict check at fuel `#statements + #blocks` passes exactly when every input has some fuel at which its concrete run returns with a store satisfying `Q`.
20. **lax-check-equals-strict-for-acyclic-at-fuel-bound** (characterization, T1; `acyclic_provesLax_iff_provesStrict_of_fuelBound_le`): For acyclic CFGs at every fuel `f ≥ #statements + #blocks`, the lax check (out-of-fuel leaves accepted) and the strict check on `symExec p f` coincide.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

What each result does **not** show is listed first under **Boundaries** (non-claims per result), followed by stronger conclusions that are not established and the escape hatches. All results are about the toy model described under **Applicability**; none is a theorem about a real verifier.

## Applicability

**What is examined.** A self-contained Lean 4 model (namespace `Toy.SymEx`, library `ToySymEx`) of a
control-flow graph language, a fuel-indexed concrete interpreter, and a forking symbolic executor,
together with kernel-checked theorems relating them. Every claim of the form "Lean proves X" in
this report is about these definitions only. The subjects in `REPORT.json` are the Lean toolchain
that checks the proofs, and the papers, tool documentation and preprints cited as prior art: the
report compares its statements with what those sources state, and they are not examined as
software.

**Model fidelity: this is a toy model.** The definitions are meant to capture the core of a
verifier that symbolically executes a MIR-style CFG (basic blocks with statements, `goto` /
`switchInt` / `return` terminators) and checks a postcondition on every leaf, as bounded model
checkers and symbolic executors do. Known gaps, each of which a transfer argument would have to
address separately:

- Values are dynamically typed mathematical integers and booleans; every operation is total and
  coercing (`+` uses `Val.toInt`; `ite`, `assert` and path conditions use `Val.toBool`, where
  nonzero integers are true). There is no overflow, no type error, no undefined behaviour.
- `Term.eq` is structural equality of values, while conditions are read through `Val.toBool`, so
  Boolean identities such as `(c == true) = c` fail for non-Boolean `c`.
- No heap, pointers, references, function calls, nondeterminism, concurrency or I/O.
- One variable namespace: symbolic input `x` is the initial value of local `x`
  (`SymStore.init = Term.var`); uninitialized locals and havoc (fresh values mid-run) are not
  modelled.
- `assert` is a statement inside a block costing one unit of fuel, unlike MIR's `Assert`
  terminator. A failing `assert` at statement `i` of block `b` panics at `⟨b, i⟩`; a jump to a
  missing block `b'` panics at the sentinel location `⟨b', 0⟩` (also for an empty CFG, with
  `b' = 0`), and the symbolic executor uses the same convention.
- Fuel accounting: one unit per statement and per terminator (including `return`); entering a
  block is free. All fuel numbers (`fuelBound p = #statements + #blocks`) are relative to this
  accounting.
- The symbolic executor never prunes, simplifies or merges; leaves with unsatisfiable path
  conditions are kept. Merging and simplification are studied as separate operators on guarded
  states and leaf lists.
- Leaf checks quantify semantically over all valuations, i.e. they model an ideal (sound and
  complete) solver. Solver incompleteness, timeouts and encodings are out of scope.

Relating any of this to a real verifier (Kani, CBMC, KLEE, a MIR-based tool) is a separate
modelling argument that this package does not provide. Where a card discusses a real system, the
discussion is labelled `Basis: derived (modeling bridge)` and states its reasoning and what it
does not establish.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib, no other Lake
dependency (`lean/lakefile.toml` declares one `[[lean_lib]]` and no `[[require]]`). Statement and
closure hashes are computed from Lean's `repr` of kernel expressions and are specific to this
toolchain; a different Lean version may print the same statement differently.

**Layout.** `lean/ToySymEx/Basic.lean` (all definitions the main statements depend on),
`Programs.lean` (concrete example CFGs and valuations), `Lemmas.lean` (supporting lemmas,
including the escape hatches in Boundaries), `Examples.lean` (proved positive and negative
examples for the definitions), `Statements.lean` (the main theorems), `Proofs.lean` (proof
infrastructure used only inside proofs), `Counterexamples.lean` (tightness counterexamples,
non-vacuity witnesses, positive controls).

## Findings

Each result below gives: tier; the Lean statement quoted from the source; an unfolded reading (definitions expanded by hand as a reading aid; the quoted Lean is authoritative); the plain claim; the hypothesis ledger; the depth label; the non-vacuity witness (or, for counterexample results, the positive control); prior art; the design question it informs; and its basis. Unless stated otherwise every Lean name lives in namespace `Toy.SymEx` and every theorem is fully proved and kernel-checked. Non-claims are collected under **Boundaries**.

### Core definitions

Quoted verbatim from `lean/ToySymEx/Basic.lean`; every main statement and its definition closure is built from these.

The connectives are encoded with `ite`: `Term.not a = ite a ff tt`, `Term.and a b = ite a b ff`, `Term.or a b = ite a tt b`, where `tt` / `ff` are the Boolean literals and `int k` is an integer literal. `Var := Nat`, `Store := Var → Val`, `Valuation := Var → Val`, `SymStore := Var → Term`, `Cfg := List Block` (block 0 is the entry).

```lean
/-- Runtime values: mathematical integers and booleans. Operations coerce
(`Val.toInt`, `Val.toBool`) so that evaluation is total; type errors are out of
scope for this model. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Integer view of a value (`true ↦ 1`, `false ↦ 0`), used by `+`. -/
def Val.toInt : Val → Int
  | .int i => i
  | .bool b => if b then 1 else 0

/-- Truth view of a value (nonzero integers are true), used by `ite`, `assert`,
and path conditions. -/
def Val.toBool : Val → Bool
  | .int i => i != 0
  | .bool b => b

/-- Update one local of a concrete store. -/
def Store.set (st : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else st y

/-- Terms. The same syntax serves as program expressions (where `var x` reads
local `x`) and as symbolic values (where `var x` is the symbolic input
variable `x`). -/
inductive Term where
  | var (x : Var)
  | lit (v : Val)
  | add (a b : Term)
  | eq (a b : Term)
  | ite (c t e : Term)
  deriving DecidableEq, Repr, Inhabited

/-- Interpretation of a term under a valuation (or, for program expressions,
under a concrete store). `eq` is structural equality of values. -/
def eval (ρ : Valuation) : Term → Val
  | var x => ρ x
  | lit v => v
  | add a b => .int ((eval ρ a).toInt + (eval ρ b).toInt)
  | eq a b => .bool (decide (eval ρ a = eval ρ b))
  | ite c t e => if (eval ρ c).toBool then eval ρ t else eval ρ e

/-- Simultaneous substitution of terms for variables. Symbolic evaluation of a
program expression in a symbolic store `σ` is `e.subst σ`. -/
def subst (σ : Var → Term) : Term → Term
  | var x => σ x
  | lit v => lit v
  | add a b => add (subst σ a) (subst σ b)
  | eq a b => eq (subst σ a) (subst σ b)
  | ite c t e => ite (subst σ c) (subst σ t) (subst σ e)

/-- Replace one variable by a term (a path-condition-driven rewrite such as
"under `x == 0`, replace `x` by `0`"). -/
def substVar (x : Var) (t : Term) : Term → Term :=
  subst (fun y => if y = x then t else var y)

/-- A Boolean term `c` holds under `ρ` when it evaluates to a true value. -/
def holds (c : Term) (ρ : Valuation) : Prop := (c.eval ρ).toBool = true

/-- `c` is satisfiable. -/
def Sat (c : Term) : Prop := ∃ ρ, holds c ρ

/-- `c₁` and `c₂` are never true together (their conjunction is unsatisfiable). -/
def Disjoint (c₁ c₂ : Term) : Prop := ∀ ρ, ¬ (holds c₁ ρ ∧ holds c₂ ρ)

/-- Statements: assignment to a local, and assertion (panics when false). -/
inductive Stmt where
  | assign (x : Var) (e : Term)
  | assert (e : Term)
  deriving DecidableEq, Repr

/-- Block terminators. `switchInt x targets otherwise` jumps to the block of the
first `(v, b)` in `targets` with `x = v`, and to `otherwise` if there is none. -/
inductive Terminator where
  | goto (b : Nat)
  | switchInt (x : Var) (targets : List (Val × Nat)) (otherwise : Nat)
  | ret
  deriving DecidableEq, Repr

/-- A basic block: straight-line statements followed by a terminator. -/
structure Block where
  stmts : List Stmt
  term : Terminator
  deriving DecidableEq, Repr

/-- A program location: block index and statement index within the block. -/
structure Loc where
  blk : Nat
  idx : Nat
  deriving DecidableEq, Repr

/-- Concrete outcomes of a fuel-bounded run. -/
inductive Outcome where
  | ok (st : Store)
  | panic (loc : Loc)
  | outOfFuel

/-- The block a `switchInt` selects for scrutinee value `v`. -/
def select (v : Val) : List (Val × Nat) → Nat → Nat
  | [], d => d
  | (w, b) :: rest, d => if v = w then b else select v rest d

/-- Successor block indices named by a terminator. -/
def Terminator.targetsOf : Terminator → List Nat
  | .goto b => [b]
  | .switchInt _ tgts d => tgts.map Prod.snd ++ [d]
  | .ret => []

/-- Concrete fuel-indexed interpreter. `runBlock p fuel b i ss t st` executes the
remaining statements `ss` (the first of which is statement `i` of block `b`),
then the terminator `t`. Every statement and every terminator consumes one unit
of fuel; entering a block is free. A failing `assert` at location `(b, i)` yields
`panic ⟨b, i⟩`. A jump to a nonexistent block `b'` yields `panic ⟨b', 0⟩` (a
convention; well-formed CFGs never do this). -/
def runBlock (p : Cfg) : Nat → Nat → Nat → List Stmt → Terminator → Store → Outcome
  | 0, _, _, _, _, _ => .outOfFuel
  | f + 1, b, i, .assign x e :: ss, t, st => runBlock p f b (i + 1) ss t (st.set x (e.eval st))
  | f + 1, b, i, .assert e :: ss, t, st =>
      if (e.eval st).toBool then runBlock p f b (i + 1) ss t st else .panic ⟨b, i⟩
  | _ + 1, _, _, [], .ret, st => .ok st
  | f + 1, _, _, [], .goto b', st =>
      match p[b']? with
      | some blk => runBlock p f b' 0 blk.stmts blk.term st
      | none => .panic ⟨b', 0⟩
  | f + 1, _, _, [], .switchInt x tgts d, st =>
      match p[select (st x) tgts d]? with
      | some blk => runBlock p f (select (st x) tgts d) 0 blk.stmts blk.term st
      | none => .panic ⟨select (st x) tgts d, 0⟩

/-- Run a CFG from its entry block with the given fuel and initial store. -/
def exec (p : Cfg) (fuel : Nat) (st : Store) : Outcome :=
  match p[0]? with
  | some blk => runBlock p fuel 0 0 blk.stmts blk.term st
  | none => .panic ⟨0, 0⟩

/-- The initial symbolic store: local `x` holds the symbolic input variable `x`. -/
def SymStore.init : SymStore := Term.var

/-- Update one local of a symbolic store. -/
def SymStore.set (σ : SymStore) (x : Var) (t : Term) : SymStore :=
  fun y => if y = x then t else σ y

/-- Instantiate a symbolic store under a valuation, giving a concrete store. -/
def SymStore.inst (σ : SymStore) (ρ : Valuation) : Store := fun x => (σ x).eval ρ

/-- Symbolic outcomes recorded at the leaves of symbolic execution. -/
inductive SymOutcome where
  | ok (σ : SymStore)
  | panic (loc : Loc)
  | outOfFuel
  deriving Inhabited

/-- Instantiate a symbolic outcome under a valuation. -/
def SymOutcome.inst : SymOutcome → Valuation → Outcome
  | .ok σ, ρ => .ok (σ.inst ρ)
  | .panic l, _ => .panic l
  | .outOfFuel, _ => .outOfFuel

/-- A leaf of symbolic execution: a path condition and the outcome on that path. -/
structure Leaf where
  pc : Term
  res : SymOutcome
  deriving Inhabited

/-- Forking at `switchInt` with symbolic scrutinee `s` under path condition `c`:
one `(path condition, target)` pair per target, in order, plus the `otherwise`
branch. Branch `j` carries `s == vⱼ` and the negations of all earlier tests. -/
def forkSwitch (s : Term) : List (Val × Nat) → Nat → Term → List (Term × Nat)
  | [], d, c => [(c, d)]
  | (v, b) :: rest, d, c =>
      (Term.and c (Term.eq s (Term.lit v)), b) ::
        forkSwitch s rest d (Term.and c (Term.not (Term.eq s (Term.lit v))))

/-- Forking symbolic executor, mirroring `runBlock` step for step and fuel unit
for fuel unit. Assignments update the symbolic store; an `assert e` forks a
panic leaf (path condition `c ∧ ¬e`) and continues under `c ∧ e`; `switchInt`
forks via `forkSwitch`. No path is pruned, even when its path condition is
unsatisfiable. -/
def symBlock (p : Cfg) : Nat → Nat → Nat → List Stmt → Terminator → Term → SymStore → List Leaf
  | 0, _, _, _, _, c, _ => [⟨c, .outOfFuel⟩]
  | f + 1, b, i, .assign x e :: ss, t, c, σ => symBlock p f b (i + 1) ss t c (σ.set x (e.subst σ))
  | f + 1, b, i, .assert e :: ss, t, c, σ =>
      ⟨Term.and c (Term.not (e.subst σ)), .panic ⟨b, i⟩⟩ ::
        symBlock p f b (i + 1) ss t (Term.and c (e.subst σ)) σ
  | _ + 1, _, _, [], .ret, c, σ => [⟨c, .ok σ⟩]
  | f + 1, _, _, [], .goto b', c, σ =>
      match p[b']? with
      | some blk => symBlock p f b' 0 blk.stmts blk.term c σ
      | none => [⟨c, .panic ⟨b', 0⟩⟩]
  | f + 1, _, _, [], .switchInt x tgts d, c, σ =>
      (forkSwitch (σ x) tgts d c).flatMap fun cb =>
        match p[cb.2]? with
        | some blk => symBlock p f cb.2 0 blk.stmts blk.term cb.1 σ
        | none => [⟨cb.1, .panic ⟨cb.2, 0⟩⟩]

/-- Symbolic execution of a CFG from its entry block, path condition `true`,
and the initial symbolic store. -/
def symExec (p : Cfg) (fuel : Nat) : List Leaf :=
  match p[0]? with
  | some blk => symBlock p fuel 0 0 blk.stmts blk.term Term.tt SymStore.init
  | none => [⟨Term.tt, .panic ⟨0, 0⟩⟩]

/-- Concrete success: the run returned and its final store satisfies `Q`. -/
def OkWith (Q : Store → Prop) : Outcome → Prop
  | .ok st => Q st
  | _ => False

/-- Concrete success or fuel exhaustion (bounded safety at this fuel): the run
did not panic within the given fuel, and if it returned then `Q` holds. This is
not Hoare-style partial correctness: a run counted here may still panic after
more steps. -/
def OkWithOrOutOfFuel (Q : Store → Prop) : Outcome → Prop
  | .ok st => Q st
  | .outOfFuel => True
  | .panic _ => False

/-- The strict leaf check: on every leaf, every valuation satisfying the leaf's
path condition gives a successful outcome satisfying `Q`. `outOfFuel` and
`panic` leaves fail the check unless their path condition is unsatisfiable. -/
def LeavesProve (L : List Leaf) (Q : Store → Prop) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)

/-- The lax leaf check: like `LeavesProve`, but `outOfFuel` leaves are accepted
("fuel exhaustion read as success"). -/
def LeavesProveLax (L : List Leaf) (Q : Store → Prop) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWithOrOutOfFuel Q (l.res.inst ρ)

/-- Strict symbolic success of `p` at fuel `f` for postcondition `Q`. -/
def ProvesStrict (p : Cfg) (f : Nat) (Q : Store → Prop) : Prop :=
  LeavesProve (symExec p f) Q

/-- Lax symbolic "success" of `p` at fuel `f` (out-of-fuel leaves accepted). -/
def ProvesLax (p : Cfg) (f : Nat) (Q : Store → Prop) : Prop :=
  LeavesProveLax (symExec p f) Q

/-- Per-leaf soundness of a leaf list for `p` at fuel `f`: for every leaf and
every valuation satisfying its path condition, the concrete run from the
instantiated initial store with the same fuel has exactly the leaf's outcome. -/
def LeavesSound (p : Cfg) (f : Nat) (L : List Leaf) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → exec p f (SymStore.init.inst ρ) = l.res.inst ρ

/-- Exhaustiveness (coverage) of a leaf list: every valuation satisfies the path
condition of at least one leaf. -/
def LeavesExhaustive (L : List Leaf) : Prop :=
  ∀ ρ, ∃ l ∈ L, holds l.pc ρ

/-- Erase every path condition (replace it by `true`). -/
def dropPcs (L : List Leaf) : List Leaf := L.map fun l => ⟨Term.tt, l.res⟩

/-- A guarded symbolic state `(c, σ)` is sound for a reference `R` (what the
concrete semantics produces from each valuation) and a continuation `K` (what the
remaining computation produces from a concrete store at the merge point) when
every valuation satisfying `c` has `R ρ = K (σ.inst ρ)`. For final leaves,
`R ρ = exec p f (init.inst ρ)` and `K = Outcome.ok`; for a join point, `K` runs
the rest of the program from that point with the remaining fuel. -/
def GuardedSound {α : Type} (R : Valuation → α) (K : Store → α) (c : Term) (σ : SymStore) : Prop :=
  ∀ ρ, holds c ρ → R ρ = K (σ.inst ρ)

/-- The guarded merge of two stores: `x ↦ ite c₁ (σ₁ x) (σ₂ x)`. -/
def mergeStore (c₁ : Term) (σ₁ σ₂ : SymStore) : SymStore :=
  fun x => Term.ite c₁ (σ₁ x) (σ₂ x)

/-- Merge two successful leaves `(c₁, σ₁)`, `(c₂, σ₂)` into
`(c₁ ∨ c₂, x ↦ ite c₁ (σ₁ x) (σ₂ x))`. -/
def mergeLeaf (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore) : Leaf :=
  ⟨Term.or c₁ c₂, .ok (mergeStore c₁ σ₁ σ₂)⟩

/-- The unguarded "merge" that keeps `σ₁` (a shortcut, not a sound merge). -/
def mergeLeafUnguarded (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (_σ₂ : SymStore) : Leaf :=
  ⟨Term.or c₁ c₂, .ok σ₁⟩

/-- A set of guarded states (with common continuation `K`) covers a behaviour
relation `B` when every behaviour `a` of every valuation `ρ` is produced by some
state whose guard holds at `ρ`. `B` may relate one valuation to several
behaviours (nondeterminism, or several visits of one program point). -/
def Covers {α : Type} (B : Valuation → α → Prop) (K : Store → α) (L : List (Term × SymStore)) : Prop :=
  ∀ ρ a, B ρ a → ∃ cs ∈ L, holds cs.1 ρ ∧ K (cs.2.inst ρ) = a

/-- A term simplifier `S` is sound under path condition `c` when it preserves
interpretation under every valuation satisfying `c`. -/
def SimpSoundUnder (c : Term) (S : Term → Term) : Prop :=
  ∀ t ρ, holds c ρ → (S t).eval ρ = t.eval ρ

/-- Acyclicity of the block graph: some ranking of block indices strictly
increases along every edge between existing blocks. On a finite graph this is
equivalent to having no cycle. Edges that name a nonexistent block are not
constrained, because such a jump ends the run with a panic. -/
def Acyclic (p : Cfg) : Prop :=
  ∃ rank : Nat → Nat, ∀ i (h : i < p.length), ∀ b ∈ (p[i]'h).term.targetsOf,
    b < p.length → rank i < rank b

/-- Forward-edge numbering, a decidable sufficient condition for `Acyclic`:
every successor named by the terminator of block `i` has index strictly greater
than `i` (the identity ranking works). Acyclic CFGs whose blocks are not
numbered in topological order fail it. -/
def ForwardEdges (p : Cfg) : Prop :=
  ∀ i (h : i < p.length), ∀ b ∈ (p[i]'h).term.targetsOf, i < b

/-- Straight-line: nonempty, block `i` ends in `goto (i+1)` except the last
block, which ends in `return`. Such a CFG has no branches and no unreachable
blocks. -/
def StraightLine (p : Cfg) : Prop :=
  p ≠ [] ∧ ∀ i (h : i < p.length),
    (p[i]'h).term = if i + 1 < p.length then .goto (i + 1) else .ret

/-- The fuel bound `#statements + #blocks`. -/
def fuelBound (p : Cfg) : Nat := (p.map fun blk => blk.stmts.length).sum + p.length
```

### Example programs, valuations and helper definitions

Every concrete program, valuation, postcondition and helper term that appears in a quoted counterexample, witness or positive-control statement below, quoted verbatim (files `Programs.lean`, `Examples.lean`, `Counterexamples.lean`).

```lean
-- Programs.lean
/-- Straight-line, two blocks, three statements:
`b0: x1 := x0 + 1; assert (x1 == x1); goto b1` and `b1: x2 := x1 + x1; return`. -/
def exStraight : Cfg :=
  [ ⟨[.assign 1 (add (var 0) (int 1)), .assert (eq (var 1) (var 1))], .goto 1⟩,
    ⟨[.assign 2 (add (var 1) (var 1))], .ret⟩ ]

-- Programs.lean
/-- A diamond: `b0: switchInt x0 [0 ↦ b1] otherwise b2`;
`b1: x1 := x0 + 1; goto b3`; `b2: x1 := x0 + 2; goto b3`; `b3: return`. -/
def exDiamond : Cfg :=
  [ ⟨[], .switchInt 0 [(.int 0, 1)] 2⟩,
    ⟨[.assign 1 (add (var 0) (int 1))], .goto 3⟩,
    ⟨[.assign 1 (add (var 0) (int 2))], .goto 3⟩,
    ⟨[], .ret⟩ ]

-- Programs.lean
/-- Panics exactly when `x0 = 0`: `b0: assert (¬ (x0 == 0)); return`. -/
def exPanicIfZero : Cfg :=
  [ ⟨[.assert (Term.not (eq (var 0) (int 0)))], .ret⟩ ]

-- Programs.lean
/-- `b0: assert true; return` — its symbolic panic leaf is infeasible. -/
def exAssertTrue : Cfg :=
  [ ⟨[.assert tt], .ret⟩ ]

-- Programs.lean
/-- An infinite loop: `b0: goto b0`. -/
def exSelfLoop : Cfg :=
  [ ⟨[], .goto 0⟩ ]

-- Programs.lean
/-- A loop that runs exactly three times, then fails an assertion:
`b0: x1 := 0; goto b1`; `b1: switchInt x1 [3 ↦ b3] otherwise b2`;
`b2: x1 := x1 + 1; goto b1`; `b3: assert false; return`. -/
def exLoopThenAssertFalse : Cfg :=
  [ ⟨[.assign 1 (int 0)], .goto 1⟩,
    ⟨[], .switchInt 1 [(.int 3, 3)] 2⟩,
    ⟨[.assign 1 (add (var 1) (int 1))], .goto 1⟩,
    ⟨[.assert ff], .ret⟩ ]

-- Programs.lean
/-- The same three-iteration loop, but returning normally:
`b3: return`. Every input terminates after 13 steps. -/
def exLoop3 : Cfg :=
  [ ⟨[.assign 1 (int 0)], .goto 1⟩,
    ⟨[], .switchInt 1 [(.int 3, 3)] 2⟩,
    ⟨[.assign 1 (add (var 1) (int 1))], .goto 1⟩,
    ⟨[], .ret⟩ ]

-- Programs.lean
/-- An acyclic CFG whose blocks are not numbered in topological order:
`b0: goto b2`; `b1: return`; `b2: goto b1`. -/
def exDag : Cfg :=
  [ ⟨[], .goto 2⟩,
    ⟨[], .ret⟩,
    ⟨[], .goto 1⟩ ]

-- Programs.lean
/-- A CFG with an unreachable block: `b0: return`; `b1: return`. -/
def exDeadBlock : Cfg :=
  [ ⟨[], .ret⟩,
    ⟨[], .ret⟩ ]

-- Programs.lean
/-- Returns quickly when `x0 = 0` and slowly otherwise:
`b0: switchInt x0 [0 ↦ b1] otherwise b2`; `b1: x1 := 1; return`;
`b2: x1 := 1; x2 := 2; return`. At fuel 3 the first branch returns and the
second runs out of fuel. -/
def exHalfDone : Cfg :=
  [ ⟨[], .switchInt 0 [(.int 0, 1)] 2⟩,
    ⟨[.assign 1 (int 1)], .ret⟩,
    ⟨[.assign 1 (int 1), .assign 2 (int 2)], .ret⟩ ]

-- Programs.lean
/-- Valuation with every input `0`. -/
def ρ0 : Valuation := fun _ => .int 0

-- Programs.lean
/-- Valuation with input `x0 = 5` and every other input `0`. -/
def ρ5 : Valuation := fun x => if x = 0 then .int 5 else .int 0

-- Examples.lean
/-- Path condition of the `x0 = 0` branch of `exDiamond`. -/
def dc₁ : Term := Term.and tt (eq (var 0) (int 0))

-- Examples.lean
/-- Path condition of the `x0 ≠ 0` branch of `exDiamond`. -/
def dc₂ : Term := Term.and tt (Term.not (eq (var 0) (int 0)))

-- Examples.lean
/-- Final symbolic store of the `x0 = 0` branch: `x1 ↦ x0 + 1`. -/
def dσ₁ : SymStore := SymStore.init.set 1 (add (var 0) (int 1))

-- Examples.lean
/-- Final symbolic store of the `x0 ≠ 0` branch: `x1 ↦ x0 + 2`. -/
def dσ₂ : SymStore := SymStore.init.set 1 (add (var 0) (int 2))

-- Examples.lean
/-- Path condition of the success leaf of `exPanicIfZero`. -/
def pzOkPc : Term := Term.and tt (Term.not (eq (var 0) (int 0)))

-- Examples.lean
/-- Postcondition used with `exDiamond`: `x1 ≠ x0`. -/
def QneDiamond : Store → Prop := fun st => st 1 ≠ st 0

-- Examples.lean
/-- Reference for `exDiamond` at fuel 4. -/
def Rdia : Valuation → Outcome := fun ρ => exec exDiamond 4 (SymStore.init.inst ρ)

-- Counterexamples.lean
/-- Postcondition `True`. -/
def Qtrue : Store → Prop := fun _ => True

-- Counterexamples.lean
/-- Postcondition `x1 = x0 + 1`. -/
def Qplus1 : Store → Prop := fun st => st 1 = .int ((st 0).toInt + 1)

-- Counterexamples.lean
/-- Postcondition `x1 = 1`. -/
def Qx1eq1 : Store → Prop := fun st => st 1 = .int 1

-- Counterexamples.lean
/-- Two behaviours (`1` and `2`) for every valuation. -/
def B₁₂ : Valuation → Val → Prop := fun _ a => a = .int 1 ∨ a = .int 2

-- Counterexamples.lean
/-- Observe local `0`. -/
def K₀ : Store → Val := fun st => st 0

-- Counterexamples.lean
/-- Constant store `1`. -/
def s₁ : SymStore := fun _ => int 1

-- Counterexamples.lean
/-- Constant store `2`. -/
def s₂ : SymStore := fun _ => int 2

-- Counterexamples.lean
/-- Store that increments local `0`. -/
def σx0plus1 : SymStore := SymStore.init.set 0 (add (var 0) (int 1))
```

### Results

#### 1. Symbolic expression evaluation agrees with concrete evaluation (`eval-subst-agrees`)

- **Kind:** theorem. **Tier:** T0. Standard substitution lemma (on paper: de Boer and Bonsangue 2021, Lemma 2.1); the expression-level core of every symbolic-execution correctness proof.
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.eval_subst` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Symbolic evaluation of a program expression (`e.subst σ`) interpreted under
`ρ` agrees with concrete evaluation of `e` in the instantiated store `σ.inst ρ`. -/
theorem eval_subst (σ : SymStore) (ρ : Valuation) (e : Term) :
    (e.subst σ).eval ρ = e.eval (σ.inst ρ)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
(e.subst σ).eval ρ = e.eval (fun x => (σ x).eval ρ)
```

**Plain claim.** For every symbolic store sigma, valuation rho and expression e, with no hypotheses: interpreting the symbolic evaluation e.subst sigma under rho gives the same value as evaluating e concretely in the instantiated store sigma.inst rho.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** No hypotheses; a concrete instance (x1 + x1 in the x0 = 0 branch store at x0 = 5) is checked by decide.

`Toy.SymEx.nonvacuity_eval_subst` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_eval_subst :
    ((add (var 1) (var 1)).subst dσ₁).eval ρ5 = (add (var 1) (var 1)).eval (dσ₁.inst ρ5)
```

**Prior art.**

- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Lemma 2.1 (substitution) is the same commutation of substitution with evaluation, for a while language, on paper.
- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. Introduces symbolic execution with symbolic inputs, symbolic stores and path conditions accumulated at branches.

**Design question.** Which property must a symbolic expression evaluator satisfy so that one symbolic store can stand for every concrete store it describes?

Basis: execution (Lean kernel check) — `eval_subst` (axioms: `propext`).

#### 2. Per-path soundness of the forking symbolic executor (`per-path-soundness`)

- **Kind:** theorem. **Tier:** T0. Correctness of forking symbolic execution with respect to concrete execution is classical (King 1976; de Boer and Bonsangue 2021, Theorem 2.3, on paper) and has been mechanized for other languages (Porncharoenwase et al. 2022 in Lean; Vogels et al. 2015 in Coq; Aissat et al. 2016 in Isabelle); here it is restated for a fuel-indexed CFG with panic locations.
- **Depth:** `substantive`.

**Lean statement.**

`Toy.SymEx.symExec_leaf_sound` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Per-path soundness: for every leaf produced by `symExec p f` and every
valuation `ρ` satisfying the leaf's path condition, the concrete run of `p` from
the `ρ`-instantiated initial store with the same fuel `f` has exactly the leaf's
outcome instantiated at `ρ` (same final store, or panic at the same location,
or fuel exhaustion). -/
theorem symExec_leaf_sound (p : Cfg) (f : Nat) (l : Leaf) (hl : l ∈ symExec p f)
    (ρ : Valuation) (hpc : holds l.pc ρ) :
    exec p f (SymStore.init.inst ρ) = l.res.inst ρ
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
l ∈ symExec p f → (l.pc.eval ρ).toBool = true →
  exec p f (fun x => ρ x) = l.res.inst ρ
-- SymOutcome.inst: .ok σ ↦ .ok (fun x => (σ x).eval ρ); .panic loc ↦ .panic loc;
--                  .outOfFuel ↦ .outOfFuel
```

**Plain claim.** For every CFG p, fuel f, leaf l produced by symExec p f, and valuation rho satisfying l's path condition, the concrete run of p from the rho-instantiated initial store with the same fuel f has exactly l's outcome instantiated at rho: the same final store, or a panic at the same location, or fuel exhaustion.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hl : l ∈ symExec p f` | only leaves produced by the executor are claimed sound | tight: counterexample `symExec_leaf_sound_needs_membership` |
| `hpc : holds l.pc ρ` | a leaf describes only the inputs that follow its path; ignoring this yields a spurious success | tight: counterexample `symExec_leaf_sound_needs_pc` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.symExec_leaf_sound_needs_membership` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hl`: a leaf that `symExec` does not produce (`(true, ok init)`)
satisfies `hpc` at `ρ0`, yet the concrete run panics. -/
theorem symExec_leaf_sound_needs_membership :
    holds Term.tt ρ0 ∧
      exec exPanicIfZero 2 (SymStore.init.inst ρ0) ≠ SymOutcome.inst (.ok SymStore.init) ρ0
```

`Toy.SymEx.symExec_leaf_sound_needs_pc` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hpc`: the success leaf of `exPanicIfZero` is produced by
`symExec`, its path condition fails at `ρ0`, and there the concrete run panics
while the leaf records success (a spurious success if the path condition is
ignored). -/
theorem symExec_leaf_sound_needs_pc :
    (⟨pzOkPc, .ok SymStore.init⟩ : Leaf) ∈ symExec exPanicIfZero 2 ∧ ¬ holds pzOkPc ρ0 ∧
      exec exPanicIfZero 2 (SymStore.init.inst ρ0) ≠ SymOutcome.inst (.ok SymStore.init) ρ0
```

**Non-vacuity witness.** The x0 = 0 leaf of the diamond CFG exDiamond at fuel 4 with valuation rho0 (all inputs 0).

`Toy.SymEx.nonvacuity_symExec_leaf_sound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- All hypotheses of `symExec_leaf_sound` hold for the `x0 = 0` leaf of
`exDiamond` at `ρ0`. -/
theorem nonvacuity_symExec_leaf_sound :
    (⟨dc₁, .ok dσ₁⟩ : Leaf) ∈ symExec exDiamond 4 ∧ holds dc₁ ρ0
```

**Prior art.**

- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Pen-and-paper account for a while language: a symbolic transition system that takes both branches of every conditional without a feasibility check is related to a concrete operational semantics by Theorem 2.3 (correctness) and Theorem 2.4 (completeness); there is no fuel.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.
- F. Vogels, B. Jacobs, F. Piessens, 'Featherweight VeriFast', Logical Methods in Computer Science 11(3:19), 2015, doi:10.2168/LMCS-11(3:19)2015. Coq-mechanized soundness proof for the symbolic execution of a core of the VeriFast verifier (separation logic): a successful symbolic run implies safety of all concrete runs.
- R. Aissat, F. Voisin, B. Wolff, 'Infeasible paths elimination by symbolic execution techniques: proof of correctness and preservation of paths', Archive of Formal Proofs, August 2016 (isa-afp.org/entries/InfPathElimination.html). Isabelle/HOL mechanization relating symbolic execution over control-flow graphs to concrete paths, including correctness of infeasible-path elimination.
- S. Keuchel, S. Huyghebaert, G. Lukyanov, D. Devriese, 'Verified symbolic execution with Kripke specification monads (and no meta-programming)', Proc. ACM Program. Lang. 6(ICFP), Article 97, 2022, doi:10.1145/3547628. A Coq-mechanized symbolic verification-condition generator written as an interpreter in a backward predicate-transformer monad; soundness is proved, completeness is explicitly not a goal. A different architecture from the forward, leaf-enumerating executor here.
- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. Introduces symbolic execution with symbolic inputs, symbolic stores and path conditions accumulated at branches.

**Design question.** What exactly does one leaf of a forking symbolic executor guarantee about the concrete runs it describes, at a fixed fuel?

Basis: execution (Lean kernel check) — `symExec_leaf_sound` (axioms: `Quot.sound`, `propext`).

#### 3. Leaves cover every input and are pairwise disjoint (`path-coverage`)

- **Kind:** theorem. **Tier:** T0. The leaves of a non-pruning symbolic execution tree partition the input space; folklore since King 1976, restated here per fuel.
- **Depth:** `substantive`.

**Lean statements.**

`Toy.SymEx.symExec_exhaustive` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Exhaustiveness: at every fuel, every valuation satisfies the path condition
of at least one leaf of `symExec p f`. -/
theorem symExec_exhaustive (p : Cfg) (f : Nat) (ρ : Valuation) :
    ∃ l ∈ symExec p f, holds l.pc ρ
```

`Toy.SymEx.symExec_pairwise_disjoint` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Pairwise disjointness: at every fuel, the path conditions of any two leaves
at distinct positions of `symExec p f` are never true together. -/
theorem symExec_pairwise_disjoint (p : Cfg) (f : Nat) :
    (symExec p f).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
∀ ρ, ∃ l ∈ symExec p f, (l.pc.eval ρ).toBool = true
(symExec p f).Pairwise (fun l₁ l₂ =>
  ∀ ρ, ¬ ((l₁.pc.eval ρ).toBool = true ∧ (l₂.pc.eval ρ).toBool = true))
```

**Plain claim.** For every CFG p and every fuel f, with no hypotheses: every valuation satisfies the path condition of at least one leaf of symExec p f, and the path conditions of any two leaves at distinct list positions are never simultaneously true.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** exDiamond at fuel 4: two leaves, x0 = 0 and x0 != 0, covering and disjoint.

`Toy.SymEx.nonvacuity_path_coverage` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Instance: the two `exDiamond` leaves cover every input and are disjoint. -/
theorem nonvacuity_path_coverage :
    (∀ ρ, ∃ l ∈ symExec exDiamond 4, holds l.pc ρ) ∧
      (symExec exDiamond 4).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc) ∧
      (symExec exDiamond 4).length = 2
```

**Prior art.**

- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. Introduces symbolic execution with symbolic inputs, symbolic stores and path conditions accumulated at branches; its executor forks at a conditional only when neither pc ⊃ q nor pc ⊃ ¬q holds (p. 387), so it does not create branches already known to be infeasible, whereas symExec here keeps every branch.
- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Pen-and-paper account for a while language: a symbolic transition system that takes both branches of every conditional without a feasibility check is related to a concrete operational semantics by Theorem 2.3 (correctness) and Theorem 2.4 (completeness); there is no fuel. It does not state pairwise disjointness of path conditions by list position (the second half of this card, symExec_pairwise_disjoint).
- R. Aissat, F. Voisin, B. Wolff, 'Infeasible paths elimination by symbolic execution techniques: proof of correctness and preservation of paths', Archive of Formal Proofs, August 2016 (isa-afp.org/entries/InfPathElimination.html). Isabelle/HOL mechanization relating symbolic execution over control-flow graphs to concrete paths, including correctness of infeasible-path elimination.
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Surveys path conditions, state merging (Section 5.6) and constraint reduction. Its Section 1.2 uses 'soundness' and 'completeness' in the bug-finding sense (soundness: no false negatives, every unsafe input is found); the cards here use the verification sense (a passing check implies concrete success). (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)

**Design question.** Do the leaves of a non-pruning forking executor account for every input, and for each input exactly once?

Basis: execution (Lean kernel check) — `symExec_exhaustive` (axioms: `Quot.sound`, `propext`); `symExec_pairwise_disjoint` (axioms: `Quot.sound`, `propext`).

#### 4. From leaf checks to concrete runs: soundness + exhaustiveness + check (`leaf-check-transfer`)

- **Kind:** theorem. **Tier:** T1. Folklore made precise: isolates exactly three conditions on an arbitrary leaf list (per-leaf soundness, exhaustiveness, the check), shows each is needed, and shows disjointness is not. Mechanized soundness results exist for specific executors (Porncharoenwase et al. 2022; Vogels et al. 2015) but not, as far as found, this decomposition for arbitrary leaf lists.
- **Depth:** `definitional`.

**Lean statements.**

`Toy.SymEx.exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Strict transfer: if a leaf list `L` is per-leaf sound for `p` at fuel `f`,
exhaustive, and every leaf passes the strict check for `Q`, then every concrete
run of `p` at fuel `f` returns with a final store satisfying `Q`. -/
theorem exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve (p : Cfg) (f : Nat)
    (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProve L Q)
    (ρ : Valuation) :
    OkWith Q (exec p f (SymStore.init.inst ρ))
```

`Toy.SymEx.exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Lax transfer: as above, but with the lax check (out-of-fuel leaves accepted);
the conclusion weakens to "returns with `Q`, or runs out of fuel". -/
theorem exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax (p : Cfg)
    (f : Nat) (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProveLax L Q)
    (ρ : Valuation) :
    OkWithOrOutOfFuel Q (exec p f (SymStore.init.inst ρ))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
hsound : ∀ l ∈ L, ∀ ρ, holds l.pc ρ → exec p f (fun x => ρ x) = l.res.inst ρ
hexh   : ∀ ρ, ∃ l ∈ L, holds l.pc ρ
hprove : ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)            -- strict
         ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWithOrOutOfFuel Q (l.res.inst ρ) -- lax
goal   : OkWith Q (exec p f (fun x => ρ x))   -- resp. OkWithOrOutOfFuel
-- OkWith Q (.ok st) = Q st, OkWith Q _ = False;
-- OkWithOrOutOfFuel Q: .ok st ↦ Q st, .outOfFuel ↦ True, .panic _ ↦ False
```

**Plain claim.** For any leaf list L for CFG p at fuel f (not necessarily produced by symExec): if every leaf is sound for p at f (LeavesSound), the path conditions are exhaustive (LeavesExhaustive), and every leaf passes the strict check for Q, then every concrete run at fuel f returns with Q; with the lax check (out-of-fuel leaves accepted) the conclusion is 'returns with Q or runs out of fuel'.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hsound : LeavesSound p f L` | each leaf must describe the concrete outcome on its path; a leaf (true, ok) for a panicking program is otherwise accepted | tight: counterexample `transfer_needs_leavesSound` |
| `hexh : LeavesExhaustive L` | the checked leaves must cover all inputs; keeping only the success leaf (whose path condition is not valid) gives a spurious success | tight: counterexample `transfer_needs_exhaustive` |
| `hprove : LeavesProve L Q (resp. LeavesProveLax L Q)` | the leaf check itself | tight: counterexample `transfer_needs_leaf_check` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.transfer_needs_leavesSound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hsound`: `[(true, ok init)]` is exhaustive and passes both
checks for `True`, but `exPanicIfZero` panics at `ρ0`. -/
theorem transfer_needs_leavesSound :
    LeavesExhaustive [⟨tt, .ok SymStore.init⟩] ∧
      LeavesProve [⟨tt, .ok SymStore.init⟩] Qtrue ∧
      LeavesProveLax [⟨tt, .ok SymStore.init⟩] Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0))
```

`Toy.SymEx.transfer_needs_exhaustive` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hexh`: keeping only the success leaf of `exPanicIfZero` (whose
path condition is not valid) gives a sound list that passes both checks, but the
program panics at `ρ0`. -/
theorem transfer_needs_exhaustive :
    LeavesSound exPanicIfZero 2 [⟨pzOkPc, .ok SymStore.init⟩] ∧
      LeavesProve [⟨pzOkPc, .ok SymStore.init⟩] Qtrue ∧
      LeavesProveLax [⟨pzOkPc, .ok SymStore.init⟩] Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0))
```

`Toy.SymEx.transfer_needs_leaf_check` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hprove`: the leaves of `exPanicIfZero` are sound and
exhaustive, the check fails, and so does the conclusion. -/
theorem transfer_needs_leaf_check :
    LeavesSound exPanicIfZero 2 (symExec exPanicIfZero 2) ∧
      LeavesExhaustive (symExec exPanicIfZero 2) ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0))
```

**Non-vacuity witness.** The leaves of exDiamond at fuel 4 with postcondition x1 != x0 satisfy all hypotheses (both variants).

`Toy.SymEx.nonvacuity_transfer` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_transfer :
    LeavesSound exDiamond 4 (symExec exDiamond 4) ∧ LeavesExhaustive (symExec exDiamond 4) ∧
      LeavesProve (symExec exDiamond 4) QneDiamond ∧
      LeavesProveLax (symExec exDiamond 4) QneDiamond
```

**Prior art.**

- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.
- F. Vogels, B. Jacobs, F. Piessens, 'Featherweight VeriFast', Logical Methods in Computer Science 11(3:19), 2015, doi:10.2168/LMCS-11(3:19)2015. Coq-mechanized soundness proof for the symbolic execution of a core of the VeriFast verifier (separation logic): a successful symbolic run implies safety of all concrete runs.
- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Pen-and-paper account for a while language: a symbolic transition system that takes both branches of every conditional without a feasibility check is related to a concrete operational semantics by Theorem 2.3 (correctness) and Theorem 2.4 (completeness); there is no fuel.
- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. Introduces symbolic execution with symbolic inputs, symbolic stores and path conditions accumulated at branches.

**Design question.** Which properties of a leaf list must a verifier establish before 'every leaf passes' may be read as 'every run succeeds'?

Basis: execution (Lean kernel check) — `exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve` (axioms: `propext`); `exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax` (axioms: `propext`).

#### 5. Lax check = bounded safety at the same fuel (`lax-success-iff-concrete-success-or-out-of-fuel-same-fuel`)

- **Kind:** characterization. **Tier:** T0. Correctness plus completeness of symbolic execution at a fixed fuel, in the form that accepts fuel exhaustion; the lax counterpart of strict-success-iff-concrete-success-same-fuel (cf. de Boer and Bonsangue 2021 for an unbounded version, Porncharoenwase et al. 2022, Theorem 9, for a fuel-bounded evaluator given enough fuel).
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.provesLax_iff_forall_exec_okWithOrOutOfFuel` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Lax symbolic success at fuel `f` (every leaf of `symExec p f`, under every
valuation satisfying its path condition, returns with `Q` or is out of fuel;
panic leaves are rejected) holds if and only if every concrete run at the same
fuel `f` returns with `Q` or runs out of fuel (bounded safety at fuel `f`). -/
theorem provesLax_iff_forall_exec_okWithOrOutOfFuel (p : Cfg) (f : Nat) (Q : Store → Prop) :
    ProvesLax p f Q ↔ ∀ ρ, OkWithOrOutOfFuel Q (exec p f (SymStore.init.inst ρ))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
(∀ l ∈ symExec p f, ∀ ρ, holds l.pc ρ → OkWithOrOutOfFuel Q (l.res.inst ρ)) ↔
  ∀ ρ, OkWithOrOutOfFuel Q (exec p f (fun x => ρ x))
```

**Plain claim.** For every CFG p, fuel f and postcondition Q, with no hypotheses: the lax check on symExec p f passes (every leaf, under every valuation satisfying its path condition, returns with a store satisfying Q or is out of fuel; panic leaves are rejected) if and only if every concrete run of p at fuel f either returns with a store satisfying Q or runs out of fuel, i.e. no input panics within f steps and every input that returns within f steps satisfies Q.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** exHalfDone at fuel 3 with postcondition x1 = 1: both sides hold, the strict check fails, input x0 = 0 returns with x1 = 1 and input x0 = 5 runs out of fuel.

`Toy.SymEx.nonvacuity_provesLax_iff` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Both sides of the lax characterization hold non-trivially for `exHalfDone` at
fuel 3 with the satisfiable postcondition `x1 = 1`: the lax check passes, the
strict check fails, the input `x0 = 0` returns with `x1 = 1`, and the input
`x0 = 5` runs out of fuel. -/
theorem nonvacuity_provesLax_iff :
    ProvesLax exHalfDone 3 Qx1eq1 ∧
      (∀ ρ, OkWithOrOutOfFuel Qx1eq1 (exec exHalfDone 3 (SymStore.init.inst ρ))) ∧
      ¬ ProvesStrict exHalfDone 3 Qx1eq1 ∧
      OkWith Qx1eq1 (exec exHalfDone 3 (SymStore.init.inst ρ0)) ∧
      exec exHalfDone 3 (SymStore.init.inst ρ5) = .outOfFuel
```

**Prior art.**

- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Pen-and-paper account for a while language: a symbolic transition system that takes both branches of every conditional without a feasibility check is related to a concrete operational semantics by Theorem 2.3 (correctness) and Theorem 2.4 (completeness); there is no fuel; its completeness theorem is existential reachability of finite computations, not an equivalence at a fixed fuel.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.

**Design question.** What exactly does a fuel-bounded symbolic check that accepts out-of-fuel leaves establish about concrete runs?

Basis: execution (Lean kernel check) — `provesLax_iff_forall_exec_okWithOrOutOfFuel` (axioms: `Quot.sound`, `propext`).

#### 6. Erasing path conditions only strengthens the strict check (`dropping-path-conditions-is-conservative`)

- **Kind:** theorem. **Tier:** T0. Elementary consequence of the definitions (weakening a universal antecedent); recorded as a reference point because it corrects a tempting misreading. No source states it separately.
- **Depth:** `definitional`.

**Lean statements.**

`Toy.SymEx.leavesProve_of_leavesProve_dropPcs` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Erasing path conditions only strengthens the strict leaf check: if the
leaves with every path condition replaced by `true` pass, the original leaves
pass. -/
theorem leavesProve_of_leavesProve_dropPcs (L : List Leaf) (Q : Store → Prop)
    (h : LeavesProve (dropPcs L) Q) : LeavesProve L Q
```

`Toy.SymEx.dropPcs_false_alarm` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- The converse fails (dropping path conditions causes false alarms):
`exAssertTrue` passes the strict check, but not after dropping path conditions,
because its infeasible panic leaf becomes feasible. -/
theorem dropPcs_false_alarm :
    LeavesProve (symExec exAssertTrue 2) Qtrue ∧
      ¬ LeavesProve (dropPcs (symExec exAssertTrue 2)) Qtrue
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
-- dropPcs L = L.map (fun l => ⟨tt, l.res⟩) and holds tt ρ is true, so the hypothesis is
(∀ l ∈ L, ∀ ρ, OkWith Q (l.res.inst ρ)) → ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)
```

**Plain claim.** For every leaf list L and postcondition Q: if the leaves with every path condition replaced by true pass the strict check for Q, then the original leaves pass it. The converse fails: the leaves of exAssertTrue (assert true; return) pass the strict check for True, but after erasing path conditions they do not, because the infeasible panic leaf becomes feasible.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h : LeavesProve (dropPcs L) Q` | the check on the erased leaves (hypothesis of `leavesProve_of_leavesProve_dropPcs`) | tight: counterexample `leavesProve_dropPcs_needed` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.leavesProve_dropPcs_needed` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `h`: neither the dropped nor the original check passes for
`exPanicIfZero`. -/
theorem leavesProve_dropPcs_needed :
    ¬ LeavesProve (dropPcs (symExec exPanicIfZero 2)) Qtrue ∧
      ¬ LeavesProve (symExec exPanicIfZero 2) Qtrue
```

**Non-vacuity witness.** The exDiamond leaves with path conditions erased still pass for x1 != x0 (both branch stores satisfy it for every input).

`Toy.SymEx.nonvacuity_leavesProve_dropPcs` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_leavesProve_dropPcs : LeavesProve (dropPcs (symExec exDiamond 4)) QneDiamond
```

**Prior art.**

- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Surveys path conditions, state merging (Section 5.6) and constraint reduction. Its Section 1.2 uses 'soundness' and 'completeness' in the bug-finding sense (soundness: no false negatives, every unsafe input is found); the cards here use the verification sense (a passing check implies concrete success). (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)

**Design question.** Is it safe for a verifier to check a leaf's outcome without restricting to the leaf's path condition, and what does it cost?

Basis: execution (Lean kernel check) — `leavesProve_of_leavesProve_dropPcs` (axioms: `Quot.sound`, `propext`); `dropPcs_false_alarm` (axioms: `Quot.sound`, `propext`).

#### 7. The ite-guarded merge is sound without disjoint guards (`guarded-merge-sound`)

- **Kind:** theorem. **Tier:** T0. The ite merge rule of Kuznetsov et al. (PLDI 2012), stated for an arbitrary reference and continuation; merging soundness is mechanized in Lean for a different language by Porncharoenwase et al. (2022).
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.guardedMerge_sound` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Guarded merge soundness: if `(c₁, σ₁)` and `(c₂, σ₂)` are both sound for the
same reference `R` and the same continuation `K`, then
`(c₁ ∨ c₂, x ↦ ite c₁ (σ₁ x) (σ₂ x))` is sound for `R` and `K`. No disjointness
of `c₁` and `c₂` is assumed; the merged store selects `σ₁` wherever `c₁` holds,
so the overlap is resolved by the `ite` guard. -/
theorem guardedMerge_sound {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    GuardedSound R K (Term.or c₁ c₂) (mergeStore c₁ σ₁ σ₂)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
h₁   : ∀ ρ, holds c₁ ρ → R ρ = K (fun x => (σ₁ x).eval ρ)
h₂   : ∀ ρ, holds c₂ ρ → R ρ = K (fun x => (σ₂ x).eval ρ)
goal : ∀ ρ, holds (ite c₁ tt c₂) ρ → R ρ = K (fun x => (ite c₁ (σ₁ x) (σ₂ x)).eval ρ)
```

**Plain claim.** For any reference R (what the concrete semantics yields from each valuation) and any single continuation K (what the rest of the computation yields from a concrete store at the merge point): if guarded states (c1, sigma1) and (c2, sigma2) are both sound for R and K, then the merged state (c1 or c2, x -> ite c1 (sigma1 x) (sigma2 x)) is sound for R and K, with no assumption that c1 and c2 are disjoint.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h₁ : GuardedSound R K c₁ σ₁` | the first state must be sound | tight: counterexample `guardedMerge_needs_first_sound` |
| `h₂ : GuardedSound R K c₂ σ₂` | the second state must be sound | tight: counterexample `guardedMerge_needs_second_sound` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.guardedMerge_needs_first_sound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `h₁`: with an unsound first state the merge is unsound. -/
theorem guardedMerge_needs_first_sound :
    GuardedSound Rdia Outcome.ok dc₂ dσ₂ ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₂ dσ₂)
```

`Toy.SymEx.guardedMerge_needs_second_sound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `h₂`: with an unsound second state the merge is unsound. -/
theorem guardedMerge_needs_second_sound :
    GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₁)
```

**Non-vacuity witness.** The two branch states of exDiamond (disjoint guards), and an overlapping pair (the x0 = 0 branch state and the merged state), with R the concrete run at fuel 4 and K = Outcome.ok.

`Toy.SymEx.nonvacuity_guardedMerge_sound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Both hypotheses hold for the two branch states of `exDiamond` (disjoint
guards) and also for an overlapping pair: the first branch state and the merged
state, whose guards `dc₁` and `dc₁ ∨ dc₂` overlap. -/
theorem nonvacuity_guardedMerge_sound :
    (GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧ GuardedSound Rdia Outcome.ok dc₂ dσ₂) ∧
      (GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
        GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₂) ∧
        ¬ Disjoint dc₁ (Term.or dc₁ dc₂))
```

**Prior art.**

- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. Section 1 merges (X<0, [x=0]) and (X>=0, [x=5]) into (true, [x = ite(X<0, 0, 5)]); Algorithm 1 (Section 2.1), line 20, replaces two similar worklist states at the same location l by (l, pc' or pc'', lambda v. ite(pc', s'[v], s''[v])). mergeLeaf / mergeStore is this rule, and merging at one location corresponds to the shared continuation K. The paper's concrete semantics is deterministic and it gives no mechanized proof.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.
- S. Swords, J. Davis, 'Bit-blasting ACL2 theorems', ACL2 Workshop 2011, EPTCS 70, pp. 84-102, doi:10.4204/EPTCS.70.7. GL, a symbolic-execution framework whose proof procedure is verified in ACL2; its symbolic objects include if-then-else objects (:g-ite test then . else), a guarded representation of merged values.
- E. Torlak, R. Bodik, 'A lightweight symbolic virtual machine for solver-aided host languages', PLDI 2014, pp. 530-541, doi:10.1145/2594291.2594340. Rosette's symbolic virtual machine combines symbolic execution and bounded model checking with type-driven state merging at control-flow joins; not mechanized.
- T. Avgerinos, A. Rebert, S. K. Cha, D. Brumley, 'Enhancing symbolic execution with veritesting', ICSE 2014, pp. 1083-1094, doi:10.1145/2568225.2568293. Alternates dynamic and static symbolic execution and merges paths within a bounded static region; an engineering source for merging in practice, without a soundness proof. (Bibliographic record and abstract checked; the full text was not inspected.)
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Surveys path conditions, state merging (Section 5.6) and constraint reduction. Its Section 1.2 uses 'soundness' and 'completeness' in the bug-finding sense (soundness: no false negatives, every unsafe input is found); the cards here use the verification sense (a passing check implies concrete success). (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)

**Design question.** Is the ite-guarded merge of two sound states at a join point sound, and does it require the path conditions to be disjoint?

Basis: execution (Lean kernel check) — `guardedMerge_sound` (axioms: `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — Kuznetsov et al. (PLDI 2012, Algorithm 1, line 20) merge two worklist states at one location into `(l, pc' ∨ pc'', λv. ite(pc', s'[v], s''[v]))`, which has the shape of `mergeLeaf` / `mergeStore`; merging at one location corresponds to the shared continuation `K`. Reasoning: if an engine's states, guards and stores are faithfully abstracted by `GuardedSound` with one continuation for the merge point, this theorem says its merge step preserves soundness without a disjointness side condition. Not established: that any particular engine (KLEE-based merging, Rosette, veritesting) implements exactly this rule, or that its merged states have a common continuation (same remaining code and same remaining budget).

#### 8. Merging leaves preserves soundness and exhaustiveness (`merge-leaves-preserve-soundness-and-exhaustiveness`)

- **Kind:** theorem. **Tier:** T0. Leaf-list instance of the guarded merge rule; a reference point for executors that merge leaves.
- **Depth:** `shallow`.

**Lean statements.**

`Toy.SymEx.mergeLeaf_preserves_leavesSound` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Merging two successful leaves at the front of a per-leaf sound leaf list
keeps it per-leaf sound. (The converse fails: `mergeLeaf_leavesSound_converse_fails`.) -/
theorem mergeLeaf_preserves_leavesSound (p : Cfg) (f : Nat) (c₁ : Term) (σ₁ : SymStore)
    (c₂ : Term) (σ₂ : SymStore) (rest : List Leaf)
    (hs : LeavesSound p f (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)) :
    LeavesSound p f (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest)
```

`Toy.SymEx.mergeLeaf_leavesExhaustive_iff` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Merging two successful leaves at the front of a leaf list neither gains nor
loses exhaustiveness. -/
theorem mergeLeaf_leavesExhaustive_iff (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List Leaf) :
    LeavesExhaustive (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) ↔
      LeavesExhaustive (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
-- mergeLeaf c₁ σ₁ c₂ σ₂ = ⟨ite c₁ tt c₂, .ok (fun x => ite c₁ (σ₁ x) (σ₂ x))⟩
LeavesSound p f (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest) → LeavesSound p f (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest)
LeavesExhaustive (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) ↔ LeavesExhaustive (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)
```

**Plain claim.** Replacing two successful leaves (c1, ok sigma1), (c2, ok sigma2) at the front of a leaf list by their guarded merge keeps the list per-leaf sound for p at f if it was, and leaves exhaustiveness unchanged in both directions (the merged list is exhaustive if and only if the original is); neither statement assumes the two path conditions are disjoint.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hs : LeavesSound p f (⟨c₁, ok σ₁⟩ :: ⟨c₂, ok σ₂⟩ :: rest)` | soundness of the list before merging (hypothesis of `mergeLeaf_preserves_leavesSound`) | tight: counterexample `mergeLeaf_needs_leavesSound` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.mergeLeaf_needs_leavesSound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hs`: an exhaustive list whose first leaf is unsound (the
`x0 ≠ 0` store under the `x0 = 0` guard) merges into an unsound leaf. -/
theorem mergeLeaf_needs_leavesSound :
    ¬ LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₂⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [⟨dc₁, .ok dσ₂⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      ¬ LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₂ dc₂ dσ₂]
```

**Non-vacuity witness.** The two leaves of exDiamond at fuel 4 are sound and exhaustive.

`Toy.SymEx.nonvacuity_mergeLeaf` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_mergeLeaf :
    LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩]
```

**Prior art.**

- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. Section 1 merges (X<0, [x=0]) and (X>=0, [x=5]) into (true, [x = ite(X<0, 0, 5)]); Algorithm 1 (Section 2.1), line 20, replaces two similar worklist states at the same location l by (l, pc' or pc'', lambda v. ite(pc', s'[v], s''[v])). mergeLeaf / mergeStore is this rule, and merging at one location corresponds to the shared continuation K. The paper's concrete semantics is deterministic and it gives no mechanized proof.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.

**Design question.** Can a symbolic executor replace two successful leaves by their guarded merge without invalidating the hypotheses of leaf-check-transfer?

Basis: execution (Lean kernel check) — `mergeLeaf_preserves_leavesSound` (axioms: `Quot.sound`, `propext`); `mergeLeaf_leavesExhaustive_iff` (axioms: `propext`).

#### 9. Counterexample: an unguarded merge gives a spurious success (`unguarded-merge-spurious-success`)

- **Kind:** counterexample. **Tier:** T1. Folklore failure mode made concrete and kernel-checked.
- **Depth:** `definitional`.

**Lean statement.**

`Toy.SymEx.unguardedMerge_spurious_success` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- The unguarded merge of the two sound `exDiamond` leaves is exhaustive and
passes the strict check for `x1 = x0 + 1`; at the input `x0 = 5`, whose path
condition `c₁ ∨ c₂` holds, the unguarded leaf claims `x1 = 6` while the concrete
run ends with `x1 = 7`: a spurious success. -/
theorem unguardedMerge_spurious_success :
    LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂] ∧
      LeavesProve [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂] Qplus1 ∧
      holds (Term.or dc₁ dc₂) ρ5 ∧ dσ₁.inst ρ5 1 = .int 6 ∧
      (∃ st, exec exDiamond 4 (SymStore.init.inst ρ5) = .ok st ∧ st 1 = .int 7) ∧
      ¬ OkWith Qplus1 (exec exDiamond 4 (SymStore.init.inst ρ5)) ∧
      ¬ LeavesSound exDiamond 4 [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂]
```

**Plain claim.** Merging the two sound branch leaves of the diamond CFG without an ite guard (keeping the first branch's store, x1 = x0 + 1, under path condition c1 or c2) gives an exhaustive leaf list that passes the strict check for x1 = x0 + 1; at the input x0 = 5, which satisfies c1 or c2, the unguarded leaf claims x1 = 6 while the concrete run ends with x1 = 7. This is a spurious success, and the unguarded leaf is not sound.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity.** Not applicable (counterexample). The statement is about concrete programs and valuations, so it is its own instance.

**Positive control** (a nearby setting where the failure does not occur):

`Toy.SymEx.guardedMerge_rejects_Qplus1` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Positive control: the guarded merge of the same leaves is sound and the
strict check correctly rejects `x1 = x0 + 1`. -/
theorem guardedMerge_rejects_Qplus1 :
    LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] ∧
      ¬ LeavesProve [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] Qplus1
```

**Prior art.**

- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. Section 1 merges (X<0, [x=0]) and (X>=0, [x=5]) into (true, [x = ite(X<0, 0, 5)]); Algorithm 1 (Section 2.1), line 20, replaces two similar worklist states at the same location l by (l, pc' or pc'', lambda v. ite(pc', s'[v], s''[v])). mergeLeaf / mergeStore is this rule, and merging at one location corresponds to the shared continuation K. The paper's concrete semantics is deterministic and it gives no mechanized proof.
- E. Torlak, R. Bodik, 'A lightweight symbolic virtual machine for solver-aided host languages', PLDI 2014, pp. 530-541, doi:10.1145/2594291.2594340. Rosette's symbolic virtual machine combines symbolic execution and bounded model checking with type-driven state merging at control-flow joins; not mechanized.

**Design question.** Can a merge keep one branch's store under the disjunction of both path conditions?

Basis: execution (Lean kernel check) — `unguardedMerge_spurious_success` (axioms: `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — An engine that merges branch states by keeping one branch's store under the disjoined path condition is exposed to the same spurious success. Reasoning: the counterexample needs only the two sound branch states of a two-way branch and the unguarded combination. Not established: that any named engine merges this way.

#### 10. Coverage of many-valued behaviour needs agreement on the overlap (`merge-behaviour-coverage-needs-agreement-on-overlap`)

- **Kind:** theorem. **Tier:** T1. Makes precise when overlapping path conditions are harmful: only when a merged pair would have to represent two different behaviours at one valuation.
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.guardedMerge_preserves_covers_of_agree_on_overlap` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Coverage under merging: for a possibly many-valued behaviour relation `B`,
merging the first two guarded states of a covering list keeps it covering
provided the two states agree (through `K`) wherever both guards hold. -/
theorem guardedMerge_preserves_covers_of_agree_on_overlap {α : Type}
    (B : Valuation → α → Prop) (K : Store → α) (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List (Term × SymStore))
    (hcov : Covers B K ((c₁, σ₁) :: (c₂, σ₂) :: rest))
    (hagree : ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)) :
    Covers B K ((Term.or c₁ c₂, mergeStore c₁ σ₁ σ₂) :: rest)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
hcov : ∀ ρ a, B ρ a → ∃ cs ∈ (c₁, σ₁) :: (c₂, σ₂) :: rest, holds cs.1 ρ ∧ K (cs.2.inst ρ) = a
goal : ∀ ρ a, B ρ a →
  ∃ cs ∈ (ite c₁ tt c₂, fun x => ite c₁ (σ₁ x) (σ₂ x)) :: rest, holds cs.1 ρ ∧ K (cs.2.inst ρ) = a
```

**Plain claim.** For a possibly many-valued behaviour relation B and a common continuation K: if a list of guarded states covers B (every behaviour of every valuation is produced by some state whose guard holds) and the first two states agree through K wherever both guards hold, then replacing them by their guarded merge still covers B.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hcov : Covers B K ((c₁, σ₁) :: (c₂, σ₂) :: rest)` | coverage before merging | tight: counterexample `covers_merge_needs_covers` |
| `hagree : ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)` | on the overlap the merged state keeps sigma1, so sigma2's behaviour must coincide | tight: counterexample `overlapping_merge_loses_behaviour` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.covers_merge_needs_covers` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hcov`: agreement holds trivially for two copies of one state,
but a non-covering list stays non-covering after merging. -/
theorem covers_merge_needs_covers :
    (∀ ρ, holds dc₁ ρ → holds dc₁ ρ → Outcome.ok (dσ₁.inst ρ) = Outcome.ok (dσ₁.inst ρ)) ∧
      ¬ Covers (fun ρ o => Rdia ρ = o) Outcome.ok [(Term.or dc₁ dc₁, mergeStore dc₁ dσ₁ dσ₁)]
```

`Toy.SymEx.overlapping_merge_loses_behaviour` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hagree`: two fully overlapping guarded states cover both
behaviours; their guarded merge produces only behaviour `1`. -/
theorem overlapping_merge_loses_behaviour :
    Covers B₁₂ K₀ [(tt, s₁), (tt, s₂)] ∧
      ¬ Covers B₁₂ K₀ [(Term.or tt tt, mergeStore tt s₁ s₂)]
```

**Non-vacuity witness.** B has two behaviours (1 and 2) at every valuation; the merged pair (true, constant 1) and (x0 = 0, x0 := x0 + 1) has genuinely overlapping guards and different stores that agree through K = 'read local 0' on the overlap; the unmerged state (true, constant 2) carries the second behaviour.

`Toy.SymEx.nonvacuity_covers_merge` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- All hypotheses hold with genuine overlap: the behaviour relation `B₁₂` has
two behaviours at every valuation; the two states to be merged, `(tt, s₁)` and
`(dc₁, σx0plus1)`, have overlapping guards (both hold at `ρ0`) and different
stores (they differ at `ρ5`), yet agree through `K₀` on the overlap; the second
behaviour is carried by the unmerged state `(tt, s₂)`. -/
theorem nonvacuity_covers_merge :
    Covers B₁₂ K₀ [(tt, s₁), (dc₁, σx0plus1), (tt, s₂)] ∧
      (∀ ρ, holds tt ρ → holds dc₁ ρ → K₀ (σx0plus1.inst ρ) = K₀ (s₁.inst ρ)) ∧
      holds tt ρ0 ∧ holds dc₁ ρ0 ∧ B₁₂ ρ0 (.int 1) ∧ B₁₂ ρ0 (.int 2) ∧
      s₁.inst ρ5 0 ≠ σx0plus1.inst ρ5 0
```

**Prior art.**

- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. Section 1 merges (X<0, [x=0]) and (X>=0, [x=5]) into (true, [x = ite(X<0, 0, 5)]); Algorithm 1 (Section 2.1), line 20, replaces two similar worklist states at the same location l by (l, pc' or pc'', lambda v. ite(pc', s'[v], s''[v])). mergeLeaf / mergeStore is this rule, and merging at one location corresponds to the shared continuation K. The paper's concrete semantics is deterministic; it does not consider many-valued behaviour relations, and is cited only as the source of the merge operator.
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Surveys path conditions, state merging (Section 5.6) and constraint reduction. Its Section 1.2 uses 'soundness' and 'completeness' in the bug-finding sense (soundness: no false negatives, every unsafe input is found); the cards here use the verification sense (a passing check implies concrete success). (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)

**Design question.** When symbolic states stand for several behaviours per input (nondeterminism, or repeated visits of a program point), what must hold for an ite merge not to lose behaviours?

Basis: execution (Lean kernel check) — `guardedMerge_preserves_covers_of_agree_on_overlap` (axioms: `Quot.sound`, `propext`).

#### 11. Concrete fuel monotonicity (`concrete-fuel-monotonicity`)

- **Kind:** theorem. **Tier:** T0. Standard property of fuel-indexed (clocked) interpreters; stated and proved in HOL4 by Owens et al. (ESOP 2016, Section 3.4).
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.exec_fuel_mono` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Concrete fuel monotonicity: a run that does not exhaust fuel `f` has the
same outcome at every larger fuel. -/
theorem exec_fuel_mono (p : Cfg) (f f' : Nat) (st : Store)
    (hne : exec p f st ≠ .outOfFuel) (hle : f ≤ f') :
    exec p f' st = exec p f st
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
exec p f st ≠ .outOfFuel → f ≤ f' → exec p f' st = exec p f st
```

**Plain claim.** For every CFG p, store st and fuels f <= f': if the run with fuel f does not run out of fuel, then the run with fuel f' has exactly the same outcome.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hne : exec p f st ≠ outOfFuel` | an out-of-fuel outcome may change with more fuel | tight: counterexample `exec_fuel_mono_needs_ne_outOfFuel` |
| `hle : f ≤ f'` | less fuel can turn a result into fuel exhaustion | tight: counterexample `exec_fuel_mono_needs_le` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.exec_fuel_mono_needs_ne_outOfFuel` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hne`: at fuel 4 `exStraight` runs out of fuel; at fuel 5 it
returns. -/
theorem exec_fuel_mono_needs_ne_outOfFuel :
    4 ≤ 5 ∧ exec exStraight 5 ρ5 ≠ exec exStraight 4 ρ5
```

`Toy.SymEx.exec_fuel_mono_needs_le` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hle`: fuel can not be decreased. -/
theorem exec_fuel_mono_needs_le :
    exec exStraight 5 ρ5 ≠ .outOfFuel ∧ exec exStraight 4 ρ5 ≠ exec exStraight 5 ρ5
```

**Non-vacuity witness.** exStraight from x0 = 5 returns at fuel 5; compare with fuel 6.

`Toy.SymEx.nonvacuity_exec_fuel_mono` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_exec_fuel_mono : exec exStraight 5 ρ5 ≠ .outOfFuel ∧ 5 ≤ 6
```

**Prior art.**

- S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan, 'Functional big-step semantics', ESOP 2016, LNCS 9632, pp. 589-615, doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) big-step semantics in HOL4; Section 3.4 states clock monotonicity: if evaluation does not time out at a given clock, every increment of the clock gives the same result. exec_fuel_mono is the same property for the interpreter here.

**Design question.** Can the verdict of a fuel-indexed interpreter change when more fuel is supplied?

Basis: execution (Lean kernel check) — `exec_fuel_mono` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### 12. Strict symbolic success is monotone in fuel (`strict-success-monotone-in-fuel`)

- **Kind:** theorem. **Tier:** T0. Corollary of per-path soundness, path coverage, concrete fuel monotonicity and same-fuel completeness, all T0.
- **Depth:** `shallow`.

**Lean statements.**

`Toy.SymEx.provesStrict_mono` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Strict symbolic success is monotone in fuel: if it holds at fuel `f`, it
holds at every fuel `f' ≥ f`. -/
theorem provesStrict_mono (p : Cfg) (f f' : Nat) (Q : Store → Prop)
    (h : ProvesStrict p f Q) (hle : f ≤ f') :
    ProvesStrict p f' Q
```

`Toy.SymEx.exec_okWith_of_provesStrict_of_le` (`lean/ToySymEx/Statements.lean`):

```lean
/-- Strict symbolic success at fuel `f` implies concrete success (return with
`Q`) at every fuel `f' ≥ f`, from every input. -/
theorem exec_okWith_of_provesStrict_of_le (p : Cfg) (f f' : Nat) (Q : Store → Prop)
    (h : ProvesStrict p f Q) (hle : f ≤ f') (ρ : Valuation) :
    OkWith Q (exec p f' (SymStore.init.inst ρ))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
-- ProvesStrict p f Q = ∀ l ∈ symExec p f, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)
ProvesStrict p f Q → f ≤ f' → ProvesStrict p f' Q
ProvesStrict p f Q → f ≤ f' → ∀ ρ, OkWith Q (exec p f' (fun x => ρ x))
```

**Plain claim.** For every CFG p, postcondition Q and fuels f <= f': if the strict check passes at fuel f (every leaf of symExec p f, under every valuation satisfying its path condition, returns with a store satisfying Q), then it also passes at fuel f', and the concrete run from every input at fuel f' returns with a store satisfying Q.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h : ProvesStrict p f Q` | strict symbolic success at the smaller fuel | tight: counterexample `provesStrict_mono_needs_provesStrict` |
| `hle : f ≤ f'` | success at fuel f does not transfer to smaller fuel | tight: counterexample `provesStrict_mono_needs_le` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.provesStrict_mono_needs_provesStrict` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `h` (for both `provesStrict_mono` and
`exec_okWith_of_provesStrict_of_le`): with `f = f' = 2`, `exPanicIfZero` fails
the strict check and its run from `ρ0` panics. -/
theorem provesStrict_mono_needs_provesStrict :
    2 ≤ 2 ∧ ¬ ProvesStrict exPanicIfZero 2 Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0))
```

`Toy.SymEx.provesStrict_mono_needs_le` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hle`: `exDiamond` passes the strict check at fuel 4 but not at
fuel 3, where its run from `ρ0` runs out of fuel. -/
theorem provesStrict_mono_needs_le :
    ProvesStrict exDiamond 4 QneDiamond ∧ ¬ ProvesStrict exDiamond 3 QneDiamond ∧
      ¬ OkWith QneDiamond (exec exDiamond 3 (SymStore.init.inst ρ0))
```

**Non-vacuity witness.** exDiamond at fuel 4 with x1 != x0, and f' = 5.

`Toy.SymEx.nonvacuity_provesStrict_mono` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_provesStrict_mono : ProvesStrict exDiamond 4 QneDiamond ∧ 4 ≤ 5
```

**Prior art.**

- S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan, 'Functional big-step semantics', ESOP 2016, LNCS 9632, pp. 589-615, doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) big-step semantics in HOL4; Section 3.4 states clock monotonicity: if evaluation does not time out at a given clock, every increment of the clock gives the same result. exec_fuel_mono is the same property for the interpreter here.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.

**Design question.** Once a strict symbolic check passes at some fuel, can raising the fuel ever invalidate it?

Basis: execution (Lean kernel check) — `provesStrict_mono` (axioms: `Classical.choice`, `Quot.sound`, `propext`); `exec_okWith_of_provesStrict_of_le` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### 13. Counterexample: accepting out-of-fuel leaves proves False (`out-of-fuel-is-not-success`)

- **Kind:** counterexample. **Tier:** T1. Folklore (bounded model checkers report unwinding-assertion failures for this reason) made concrete and kernel-checked.
- **Depth:** `definitional`.

**Lean statements.**

`Toy.SymEx.provesLax_loopThenAssertFalse_but_panics` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Treating `outOfFuel` as success "proves" that the assertion failure after a
three-iteration loop never happens (and even postcondition `False`) at fuel 4,
yet with fuel 13 every input panics at that assertion. -/
theorem provesLax_loopThenAssertFalse_but_panics :
    ProvesLax exLoopThenAssertFalse 4 (fun _ => False) ∧
      ∀ ρ, exec exLoopThenAssertFalse 13 (SymStore.init.inst ρ) = .panic ⟨3, 0⟩
```

`Toy.SymEx.provesLax_selfLoop_every_fuel_but_never_returns` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Treating `outOfFuel` as success "proves" postcondition `False` for the
infinite loop at every fuel, although no run ever returns. -/
theorem provesLax_selfLoop_every_fuel_but_never_returns :
    (∀ f, ProvesLax exSelfLoop f (fun _ => False)) ∧
      ∀ f ρ, exec exSelfLoop f (SymStore.init.inst ρ) = .outOfFuel
```

**Plain claim.** Accepting out-of-fuel leaves as success 'proves' at fuel 4 that a CFG which loops three times and then executes assert false satisfies even postcondition False, although with fuel 13 every input panics at that assert; and it 'proves' postcondition False for an infinite loop at every fuel, although at every fuel every run exhausts its fuel (it neither returns nor panics).

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity.** Not applicable (counterexample). The statement is about concrete programs and valuations, so it is its own instance.

**Positive control** (a nearby setting where the failure does not occur):

`Toy.SymEx.provesStrict_rejects_out_of_fuel` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Positive control: the strict check rejects both programs. -/
theorem provesStrict_rejects_out_of_fuel :
    ¬ ProvesStrict exLoopThenAssertFalse 4 Qtrue ∧ ∀ f, ¬ ProvesStrict exSelfLoop f Qtrue
```

**Prior art.**

- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384, 2023. States that successful verification with loop-unwinding bounds is unsound unless the bounds amount to complete unwinding, and that unwinding assertions restore soundness by failing when a bound is insufficient; treating fuel exhaustion as failure plays the same role here. (Checked against the arXiv version only; no archival venue record was used.)
- Kani Rust Verifier documentation, 'Loops, unwinding, and bounds' (docs/src/tutorial-loop-unwinding.md in the model-checking/kani repository; latest commit touching that file when consulted: 21f3a2884e65c4c29465515a0117123cb8392814). States that when the #[kani::unwind] bound is too low, Kani reports a failed 'unwinding assertion' and leaves other properties 'undetermined'; tool documentation of the practice of not counting an exhausted bound as success.
- E. Clarke, D. Kroening, F. Lerda, 'A tool for checking ANSI-C programs', TACAS 2004, LNCS 2988, pp. 168-176, doi:10.1007/978-3-540-24730-2_15. Introduces the CBMC bounded model checker for C; cited for the tool and its bounded exploration only. (Bibliographic record checked; the publisher full text was not inspected.)

**Design question.** May a fuel-bounded symbolic verifier count paths that run out of fuel as verified?

Basis: execution (Lean kernel check) — `provesLax_loopThenAssertFalse_but_panics` (axioms: `propext`); `provesLax_selfLoop_every_fuel_but_never_returns` (axioms: `propext`).

Basis: derived (modeling bridge) — Fuel exhaustion here plays the role of an exhausted loop-unwinding bound in bounded model checkers: CBMC fails an unwinding assertion when the bound is insufficient (Kroening et al. 2023), and the Kani documentation shows a failed "unwinding assertion" and "undetermined" properties when `#[kani::unwind]` is too low. Reasoning: in this model, counting an exhausted budget as success admits postcondition `False`, which is the failure those tool behaviours exclude. Not established: that either tool's unwinding bound corresponds to this fuel accounting, or any property of their implementations.

#### 14. Fuel #statements + #blocks suffices for acyclic CFGs (`loop-free-fuel-bound-sufficient`)

- **Kind:** theorem. **Tier:** T1. Folklore bound (a run of an acyclic CFG visits each block at most once) made precise for this fuel accounting (one unit per statement and per terminator); no source found that states this exact bound.
- **Depth:** `substantive`.

**Lean statement.**

`Toy.SymEx.acyclic_exec_ne_outOfFuel_of_fuelBound_le` (`lean/ToySymEx/Statements.lean`):

```lean
/-- For acyclic CFGs, fuel `fuelBound p = #statements + #blocks` suffices: no
run exhausts it. -/
theorem acyclic_exec_ne_outOfFuel_of_fuelBound_le (p : Cfg) (f : Nat) (st : Store)
    (hacyc : Acyclic p) (hf : fuelBound p ≤ f) :
    exec p f st ≠ .outOfFuel
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
-- Acyclic p = ∃ rank : Nat → Nat, ∀ i (h : i < p.length), ∀ b ∈ p[i].term.targetsOf,
--              b < p.length → rank i < rank b
-- fuelBound p = (p.map (·.stmts.length)).sum + p.length
Acyclic p → fuelBound p ≤ f → exec p f st ≠ .outOfFuel
```

**Plain claim.** For every acyclic CFG p (some ranking of blocks strictly increases along every edge between existing blocks; the blocks need not be numbered in topological order), every store st and every fuel f >= fuelBound p = #statements + #blocks: the concrete run does not run out of fuel.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hacyc : Acyclic p` | a cycle allows unboundedly many steps | tight: counterexample `acyclic_fuelBound_needs_acyclic` |
| `hf : fuelBound p ≤ f` | the bound itself | tight: counterexample `acyclic_fuelBound_needs_bound` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.acyclic_fuelBound_needs_acyclic` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hacyc`: the self-loop has `fuelBound = 1` but runs out of fuel. -/
theorem acyclic_fuelBound_needs_acyclic :
    ¬ Acyclic exSelfLoop ∧ fuelBound exSelfLoop ≤ 1 ∧ exec exSelfLoop 1 ρ0 = .outOfFuel
```

`Toy.SymEx.acyclic_fuelBound_needs_bound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hf`: one unit below the bound, `exStraight` runs out of fuel. -/
theorem acyclic_fuelBound_needs_bound :
    Acyclic exStraight ∧ exec exStraight 4 ρ5 = .outOfFuel
```

**Non-vacuity witness.** exDiamond (forward edges, fuelBound 6) with fuel 6, and exDag (acyclic, not numbered in topological order, fuelBound 3) with fuel 3.

`Toy.SymEx.nonvacuity_acyclic_fuelBound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Both hypotheses hold for `exDiamond` (forward edges) and for `exDag`
(acyclic but not numbered in topological order). -/
theorem nonvacuity_acyclic_fuelBound :
    (Acyclic exDiamond ∧ fuelBound exDiamond ≤ 6) ∧
      (Acyclic exDag ∧ ¬ ForwardEdges exDag ∧ fuelBound exDag ≤ 3)
```

**Prior art.**

- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384, 2023. States that successful verification with loop-unwinding bounds is unsound unless the bounds amount to complete unwinding, and that unwinding assertions restore soundness by failing when a bound is insufficient; treating fuel exhaustion as failure plays the same role here. (Checked against the arXiv version only; no archival venue record was used.)
- E. Clarke, D. Kroening, F. Lerda, 'A tool for checking ANSI-C programs', TACAS 2004, LNCS 2988, pp. 168-176, doi:10.1007/978-3-540-24730-2_15. Introduces the CBMC bounded model checker for C; cited for the tool and its bounded exploration only. (Bibliographic record checked; the publisher full text was not inspected.)

**Design question.** How much fuel suffices for a bounded executor to finish every run of an acyclic CFG?

Basis: execution (Lean kernel check) — `acyclic_exec_ne_outOfFuel_of_fuelBound_le` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — For loop-free code, a bounded checker or a step-budgeted symbolic executor is exhaustive once its budget covers every path; CBMC (Clarke et al. 2004; Kroening et al. 2023) relies on complete unwinding for this. Reasoning: this card fixes a sufficient budget for one specific accounting (one unit per statement and per terminator, entering a block free). Not established: the number `#statements + #blocks` for CBMC, Kani, MIR or any real accounting; a real tool needs its own bound.

#### 15. Fuel #statements + #blocks is exactly minimal for straight-line CFGs (`straight-line-fuel-bound-minimal`)

- **Kind:** theorem. **Tier:** T1. Folklore made precise; no source found that states the exact #statements + #blocks minimal bound for straight-line CFGs.
- **Depth:** `shallow`.

**Lean statements.**

`Toy.SymEx.straightLine_fuelBound_le_of_exec_ok` (`lean/ToySymEx/Statements.lean`):

```lean
/-- For straight-line CFGs, a run that returns needs at least
`fuelBound p = #statements + #blocks` fuel. -/
theorem straightLine_fuelBound_le_of_exec_ok (p : Cfg) (f : Nat) (st s : Store)
    (hsl : StraightLine p) (hok : exec p f st = .ok s) :
    fuelBound p ≤ f
```

`Toy.SymEx.straightLine_exec_ok_iff_fuelBound_minimal` (`lean/ToySymEx/Statements.lean`):

```lean
/-- For straight-line CFGs, `fuelBound p` is the exact minimal fuel of every run
that returns: a run returns `s` at some fuel if and only if it returns `s` at
fuel `fuelBound p` and runs out of fuel at every smaller fuel. -/
theorem straightLine_exec_ok_iff_fuelBound_minimal (p : Cfg) (st s : Store)
    (hsl : StraightLine p) :
    (∃ f, exec p f st = .ok s) ↔
      (exec p (fuelBound p) st = .ok s ∧ ∀ f' < fuelBound p, exec p f' st = .outOfFuel)
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
-- StraightLine p = p ≠ [] ∧ ∀ i (h : i < p.length),
--   p[i].term = if i + 1 < p.length then .goto (i + 1) else .ret
StraightLine p → exec p f st = .ok s → fuelBound p ≤ f
StraightLine p → ((∃ f, exec p f st = .ok s) ↔
  exec p (fuelBound p) st = .ok s ∧ ∀ f' < fuelBound p, exec p f' st = .outOfFuel)
```

**Plain claim.** For every straight-line CFG p (nonempty; block i ends in goto i+1 and the last block returns), store st and fuel f: if the run with fuel f returns, then f >= fuelBound p = #statements + #blocks; moreover the run returns a store s at some fuel if and only if it returns s at fuel fuelBound p and runs out of fuel at every smaller fuel, so fuelBound p is the exact minimal fuel for runs that return.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hsl : StraightLine p` | with branches a run may skip blocks, and an unreachable block adds to fuelBound without being executed (hypothesis of `straightLine_fuelBound_le_of_exec_ok`, `straightLine_exec_ok_iff_fuelBound_minimal`) | tight: counterexample `straightLine_fuelBound_needs_straightLine` |
| `hok : exec p f st = ok s` | a run that panics stops early and needs less fuel (hypothesis of `straightLine_fuelBound_le_of_exec_ok`) | tight: counterexample `straightLine_fuelBound_needs_ok` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.straightLine_fuelBound_needs_straightLine` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hsl`, for both straight-line theorems. With a branch
(`exDiamond` from `ρ0`), the run returns after 4 steps, below `fuelBound = 6`;
with an unreachable block (`exDeadBlock`), the run returns after 1 step, below
`fuelBound = 2`. In both cases the run returns, the lower bound fails, and so
does the exact-minimality equivalence. -/
theorem straightLine_fuelBound_needs_straightLine :
    (∃ s, exec exDiamond 4 ρ0 = .ok s ∧ ¬ fuelBound exDiamond ≤ 4 ∧
      ¬ (exec exDiamond (fuelBound exDiamond) ρ0 = .ok s ∧
        ∀ f' < fuelBound exDiamond, exec exDiamond f' ρ0 = .outOfFuel)) ∧
    (∃ s, exec exDeadBlock 1 ρ0 = .ok s ∧ ¬ fuelBound exDeadBlock ≤ 1 ∧
      ¬ (exec exDeadBlock (fuelBound exDeadBlock) ρ0 = .ok s ∧
        ∀ f' < fuelBound exDeadBlock, exec exDeadBlock f' ρ0 = .outOfFuel))
```

`Toy.SymEx.straightLine_fuelBound_needs_ok` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hok` (lower bound only): a straight-line run that panics needs
less fuel. -/
theorem straightLine_fuelBound_needs_ok :
    StraightLine exPanicIfZero ∧ exec exPanicIfZero 1 ρ0 = .panic ⟨0, 0⟩ ∧
      ¬ fuelBound exPanicIfZero ≤ 1
```

**Non-vacuity witness.** exStraight (3 statements, 2 blocks) from x0 = 5 returns at fuel 5 = fuelBound and runs out of fuel at every smaller fuel.

`Toy.SymEx.nonvacuity_straightLine_fuelBound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- All hypotheses of both straight-line theorems hold for `exStraight` from
`x0 = 5`: it returns at fuel 5 = `fuelBound` and runs out of fuel below. -/
theorem nonvacuity_straightLine_fuelBound :
    StraightLine exStraight ∧ (∃ s, exec exStraight 5 ρ5 = .ok s) ∧ fuelBound exStraight = 5 ∧
      ∀ f' < 5, exec exStraight f' ρ5 = .outOfFuel
```

**Prior art.**

- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384, 2023. States that successful verification with loop-unwinding bounds is unsound unless the bounds amount to complete unwinding, and that unwinding assertions restore soundness by failing when a bound is insufficient; treating fuel exhaustion as failure plays the same role here. (Checked against the arXiv version only; no archival venue record was used.)

**Design question.** Is fuelBound tight, and for which CFGs?

Basis: execution (Lean kernel check) — `straightLine_fuelBound_le_of_exec_ok` (axioms: `Quot.sound`, `propext`); `straightLine_exec_ok_iff_fuelBound_minimal` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — Same bridge as the sufficiency card: the exact minimal budget is a property of this accounting only. Not established: any minimality claim for a real tool or for CFGs with branches (where the bound is not minimal: `exDiamond`) or unreachable blocks (`exDeadBlock`).

#### 16. Exact criterion for sound term simplification (`simplifier-soundness-characterization`)

- **Kind:** characterization. **Tier:** T1. Folklore criterion (simplify modulo the path condition) stated as an exact equivalence; the sufficiency direction has mechanized instances in other architectures (Keuchel et al. 2022), the necessity direction is not stated there.
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.simpSoundUnder_iff_preserves_guardedSound` (`lean/ToySymEx/Statements.lean`):

```lean
/-- A term simplifier `S` is sound under path condition `c` (preserves
interpretation under every valuation satisfying `c`) if and only if rewriting
every term of a guarded state with `S` preserves guarded soundness for every
result type, reference and continuation. The path condition itself is not
rewritten. -/
theorem simpSoundUnder_iff_preserves_guardedSound (c : Term) (S : Term → Term) :
    SimpSoundUnder c S ↔
      ∀ (α : Type) (R : Valuation → α) (K : Store → α) (σ : SymStore),
        GuardedSound R K c σ → GuardedSound R K c (fun x => S (σ x))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
(∀ t ρ, holds c ρ → (S t).eval ρ = t.eval ρ) ↔
  ∀ (α : Type) (R : Valuation → α) (K : Store → α) (σ : SymStore),
    (∀ ρ, holds c ρ → R ρ = K (fun x => (σ x).eval ρ)) →
    (∀ ρ, holds c ρ → R ρ = K (fun x => (S (σ x)).eval ρ))
```

**Plain claim.** A term simplifier S preserves interpretation under every valuation satisfying path condition c (SimpSoundUnder c S) if and only if, for every result type, reference R, continuation K and symbolic store sigma, rewriting every term of sigma with S (leaving c unchanged) turns a state (c, sigma) that is sound for R and K into one that is still sound.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Rewriting x0 to 0 is sound under the path condition x0 = 0 and unsound under true.

`Toy.SymEx.nonvacuity_simpSoundUnder` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_simpSoundUnder :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧ ¬ SimpSoundUnder tt (Term.substVar 0 (int 0))
```

**Prior art.**

- S. Keuchel, S. Huyghebaert, G. Lukyanov, D. Devriese, 'Verified symbolic execution with Kripke specification monads (and no meta-programming)', Proc. ACM Program. Lang. 6(ICFP), Article 97, 2022, doi:10.1145/3547628. Its Coq-mechanized symbolic executor simplifies path conditions and prunes unreachable paths through a solver interface, and its soundness proof rests on the correctness of that interface; a mechanized instance of the 'sound simplification' direction in a different architecture.
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Section 6 (constraint reduction) describes implied value concretization, as used by KLEE: once the path condition forces a variable to a value, the variable is replaced by that value on that path. (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)
- C. Cadar, D. Dunbar, D. Engler, 'KLEE: Unassisted and automatic generation of high-coverage tests for complex systems programs', OSDI 2008, pp. 209-224. The symbolic executor that uses implied value concretization (per Baldoni et al., Section 6); cited for the practice, not for a proof. Section 3.3 (query optimization) of the paper itself describes implied value concretization: once a path-condition constraint fixes a variable (x + 1 = 10 gives x = 9), the concrete value is written back for that path. Full text: https://www.usenix.org/legacy/events/osdi08/tech/full_papers/cadar/cadar.pdf.

**Design question.** Under which condition may a symbolic executor rewrite the terms of a state using facts implied by its path condition?

Basis: execution (Lean kernel check) — `simpSoundUnder_iff_preserves_guardedSound` (axioms: `Quot.sound`).

Basis: derived (modeling bridge) — Implied value concretization (KLEE, OSDI 2008, Section 3.3) is a path-condition-driven rewrite of the kind modelled by `SimpSoundUnder` and `Term.substVar`. Reasoning: the card says such a rewrite is safe for a state exactly when it preserves interpretation under that state's own path condition. Not established: anything about KLEE's implementation, which writes concrete values back to per-path memory and is not modelled here.

#### 17. Counterexample: a branch-specific rewrite after merging is unsound (`path-specific-simplification-breaks-merge`)

- **Kind:** counterexample. **Tier:** T1. Folklore failure mode made concrete.
- **Depth:** `definitional`.

**Lean statement.**

`Toy.SymEx.pathSimp_after_merge_breaks_soundness` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Simplifying with a fact that holds on only one path (`x0 = 0`, sound under
`dc₁`) after merging breaks soundness of the merged leaf. The rewrite also
reaches the merge guard: `x0 ↦ 0` turns `dc₁` into a condition that holds at
`x0 = 5`, so at that input the rewritten leaf selects the first branch and
claims `x1 = 1`, while the concrete run ends with `x1 = 7`. -/
theorem pathSimp_after_merge_breaks_soundness :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧
      LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] ∧
      ¬ holds dc₁ ρ5 ∧ holds (Term.substVar 0 (int 0) dc₁) ρ5 ∧
      holds (Term.or dc₁ dc₂) ρ5 ∧
      SymStore.inst (fun x => Term.substVar 0 (int 0) (mergeStore dc₁ dσ₁ dσ₂ x)) ρ5 1 = .int 1 ∧
      (∃ st, exec exDiamond 4 (SymStore.init.inst ρ5) = .ok st ∧ st 1 = .int 7) ∧
      ¬ LeavesSound exDiamond 4
        [⟨Term.or dc₁ dc₂, .ok (fun x => Term.substVar 0 (int 0) (mergeStore dc₁ dσ₁ dσ₂ x))⟩]
```

**Plain claim.** The rewrite x0 -> 0 is sound under the x0 = 0 branch's path condition c1, but applied to every term of the guarded merge of the two diamond branches (a sound leaf guarded by c1 or c2) it breaks soundness. It also rewrites the merge guard c1 inside each ite into a condition that holds at x0 = 5, where c1 does not; so at x0 = 5 the rewritten merged leaf selects the first branch and claims x1 = 1, while the concrete run ends with x1 = 7.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity.** Not applicable (counterexample). The statement is about concrete programs and valuations, so it is its own instance.

**Positive control** (a nearby setting where the failure does not occur):

`Toy.SymEx.pathSimp_before_merge_sound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Positive control: simplifying inside the `dc₁` branch before merging keeps
the merged leaf sound. -/
theorem pathSimp_before_merge_sound :
    LeavesSound exDiamond 4
      [mergeLeaf dc₁ (fun x => Term.substVar 0 (int 0) (dσ₁ x)) dc₂ dσ₂]
```

**Prior art.**

- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. Section 1 merges (X<0, [x=0]) and (X>=0, [x=5]) into (true, [x = ite(X<0, 0, 5)]); Algorithm 1 (Section 2.1), line 20, replaces two similar worklist states at the same location l by (l, pc' or pc'', lambda v. ite(pc', s'[v], s''[v])). mergeLeaf / mergeStore is this rule, and merging at one location corresponds to the shared continuation K. The paper's concrete semantics is deterministic and it gives no mechanized proof.
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502). Section 6 (constraint reduction) describes implied value concretization, as used by KLEE: once the path condition forces a variable to a value, the variable is replaced by that value on that path. (Section content checked via the arXiv version; the journal record via its DOI landing metadata.)
- C. Cadar, D. Dunbar, D. Engler, 'KLEE: Unassisted and automatic generation of high-coverage tests for complex systems programs', OSDI 2008, pp. 209-224. The symbolic executor that uses implied value concretization (per Baldoni et al., Section 6); cited for the practice, not for a proof. Section 3.3 (query optimization) of the paper itself describes implied value concretization: once a path-condition constraint fixes a variable (x + 1 = 10 gives x = 9), the concrete value is written back for that path. Full text: https://www.usenix.org/legacy/events/osdi08/tech/full_papers/cadar/cadar.pdf.

**Design question.** Can facts learned on one branch be used to simplify a merged state?

Basis: execution (Lean kernel check) — `pathSimp_after_merge_breaks_soundness` (axioms: `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — The same bridge as the simplifier card: a branch-specific concretization applied after merging is unsafe in this model, while applying it to each branch before merging is sound (`pathSimp_before_merge_sound`, `guardedMerge_sound_of_simp_branches`). Not established: that any engine performs the unsafe order.

#### 18. Strict check = concrete success at the same fuel (`strict-success-iff-concrete-success-same-fuel`)

- **Kind:** characterization. **Tier:** T0. Correctness plus completeness of symbolic execution, restated at a fixed fuel (cf. de Boer and Bonsangue 2021, Theorems 2.3 and 2.4, unbounded and on paper; Porncharoenwase et al. 2022, Theorems 5 and 9, mechanized in Lean for a fuel-bounded evaluator given enough fuel).
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.provesStrict_iff_forall_exec_okWith` (`lean/ToySymEx/Statements.lean`):

```lean
/-- At a fixed fuel, strict symbolic success is equivalent to concrete success
(return with `Q`) from every input at that same fuel. No acyclicity needed. -/
theorem provesStrict_iff_forall_exec_okWith (p : Cfg) (f : Nat) (Q : Store → Prop) :
    ProvesStrict p f Q ↔ ∀ ρ, OkWith Q (exec p f (SymStore.init.inst ρ))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
(∀ l ∈ symExec p f, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)) ↔
  ∀ ρ, OkWith Q (exec p f (fun x => ρ x))
```

**Plain claim.** For every CFG p (cycles allowed), fuel f and postcondition Q, with no hypotheses: the strict check on symExec p f passes if and only if the concrete run from every input at the same fuel f returns with a store satisfying Q.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** exDiamond at fuel 4 with x1 != x0, and the three-iteration loop exLoop3 (not acyclic) at fuel 13 with postcondition True.

`Toy.SymEx.nonvacuity_provesStrict_iff` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Instances of the same-fuel characterization: `exDiamond` at fuel 4, and the
three-iteration loop `exLoop3` (not acyclic) at fuel 13, where both sides
hold. -/
theorem nonvacuity_provesStrict_iff :
    ProvesStrict exDiamond 4 QneDiamond ∧ ¬ Acyclic exLoop3 ∧ ProvesStrict exLoop3 13 Qtrue ∧
      (∀ ρ, OkWith Qtrue (exec exLoop3 13 (SymStore.init.inst ρ)))
```

**Prior art.**

- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). Pen-and-paper account for a while language: a symbolic transition system that takes both branches of every conditional without a feasibility check is related to a concrete operational semantics by Theorem 2.3 (correctness) and Theorem 2.4 (completeness); there is no fuel; its completeness theorem is existential reachability of finite computations, not an equivalence at a fixed fuel.
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. Lean-mechanized semantics S_c of symbolic evaluation with state merging, parameterized by a 'symbolic factory'; Theorem 5 proves S_c sound and complete with respect to the concrete semantics, and Theorem 9 proves the fuel-bounded reference evaluator Leanette sound and complete with respect to S_c given enough fuel. The closest existing mechanization; its setting (a small functional language, merging inside the evaluator) differs from the CFG model here.
- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. Introduces symbolic execution with symbolic inputs, symbolic stores and path conditions accumulated at branches.

**Design question.** Is a strict symbolic check at a fixed fuel complete as well as sound?

Basis: execution (Lean kernel check) — `provesStrict_iff_forall_exec_okWith` (axioms: `Quot.sound`, `propext`).

#### 19. Completeness for acyclic CFGs at fuel #statements + #blocks (`loop-free-completeness-at-fuel-bound`)

- **Kind:** characterization. **Tier:** T1. Folklore (bounded exploration is complete for loop-free code) made precise with the explicit bound #statements + #blocks.
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.acyclic_provesStrict_fuelBound_iff_forall_exists_fuel` (`lean/ToySymEx/Statements.lean`):

```lean
/-- For acyclic CFGs, strict symbolic success at fuel `fuelBound p` is
equivalent to: every input has some fuel at which the concrete run returns with
`Q`. -/
theorem acyclic_provesStrict_fuelBound_iff_forall_exists_fuel (p : Cfg) (Q : Store → Prop)
    (hacyc : Acyclic p) :
    ProvesStrict p (fuelBound p) Q ↔
      ∀ ρ, ∃ f, OkWith Q (exec p f (SymStore.init.inst ρ))
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
Acyclic p →
  ((∀ l ∈ symExec p (fuelBound p), ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)) ↔
    ∀ ρ, ∃ f, OkWith Q (exec p f (fun x => ρ x)))
```

**Plain claim.** For every acyclic CFG p (some ranking of blocks strictly increases along every edge between existing blocks) and postcondition Q: the strict check at fuel fuelBound p = #statements + #blocks passes if and only if every input has some fuel at which the concrete run returns with a store satisfying Q.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hacyc : Acyclic p` | with a cycle, every input may return yet need more than fuelBound p steps | tight: counterexample `acyclic_completeness_needs_acyclic` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.acyclic_completeness_needs_acyclic` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hacyc`: every input of the three-iteration loop returns (at
fuel 13), but the strict check fails at `fuelBound exLoop3 = 6`. -/
theorem acyclic_completeness_needs_acyclic :
    ¬ Acyclic exLoop3 ∧ (∀ ρ, ∃ f, OkWith Qtrue (exec exLoop3 f (SymStore.init.inst ρ))) ∧
      ¬ ProvesStrict exLoop3 (fuelBound exLoop3) Qtrue
```

**Non-vacuity witness.** exDiamond is acyclic and passes the strict check for x1 != x0 at fuelBound 6.

`Toy.SymEx.nonvacuity_acyclic_completeness` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_acyclic_completeness :
    Acyclic exDiamond ∧ ProvesStrict exDiamond (fuelBound exDiamond) QneDiamond
```

**Prior art.**

- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384, 2023. States that successful verification with loop-unwinding bounds is unsound unless the bounds amount to complete unwinding, and that unwinding assertions restore soundness by failing when a bound is insufficient; treating fuel exhaustion as failure plays the same role here. (Checked against the arXiv version only; no archival venue record was used.)
- E. Clarke, D. Kroening, F. Lerda, 'A tool for checking ANSI-C programs', TACAS 2004, LNCS 2988, pp. 168-176, doi:10.1007/978-3-540-24730-2_15. Introduces the CBMC bounded model checker for C; cited for the tool and its bounded exploration only. (Bibliographic record checked; the publisher full text was not inspected.)

**Design question.** For acyclic CFGs, can a single fuel value make the strict symbolic check complete?

Basis: execution (Lean kernel check) — `acyclic_provesStrict_fuelBound_iff_forall_exists_fuel` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — Bounded exploration is complete for loop-free code once the bound is large enough (the reason complete unwinding makes CBMC's bounded verification sound). Reasoning: this card states the model-level equivalence at an explicit bound. Not established: anything about the tools.

#### 20. Lax and strict checks coincide for acyclic CFGs at the bound (`lax-check-equals-strict-for-acyclic-at-fuel-bound`)

- **Kind:** characterization. **Tier:** T1. Folklore (with a sufficient unwinding bound, unwinding assertions cannot fail) made precise for this model.
- **Depth:** `shallow`.

**Lean statement.**

`Toy.SymEx.acyclic_provesLax_iff_provesStrict_of_fuelBound_le` (`lean/ToySymEx/Statements.lean`):

```lean
/-- For acyclic CFGs at any fuel `f ≥ fuelBound p`, the lax check (out-of-fuel
leaves accepted) and the strict check coincide: no satisfiable out-of-fuel leaf
remains. -/
theorem acyclic_provesLax_iff_provesStrict_of_fuelBound_le (p : Cfg) (f : Nat)
    (Q : Store → Prop) (hacyc : Acyclic p) (hf : fuelBound p ≤ f) :
    ProvesLax p f Q ↔ ProvesStrict p f Q
```

**Unfolded reading** (hand-expanded; not a Lean declaration):

```text
Acyclic p → fuelBound p ≤ f →
  ((∀ l ∈ symExec p f, ∀ ρ, holds l.pc ρ → OkWithOrOutOfFuel Q (l.res.inst ρ)) ↔
   (∀ l ∈ symExec p f, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)))
```

**Plain claim.** For every acyclic CFG p, postcondition Q and fuel f >= fuelBound p: the lax check on symExec p f (out-of-fuel leaves accepted) passes if and only if the strict check passes.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hacyc : Acyclic p` | with a cycle, every feasible path may still be looping at fuel fuelBound p, so the lax check passes vacuously while the strict check fails | tight: counterexample `acyclic_lax_iff_strict_needs_acyclic` |
| `hf : fuelBound p ≤ f` | below the bound a feasible path can run out of fuel | tight: counterexample `acyclic_lax_iff_strict_needs_bound` |

Each counterexample states that every other hypothesis holds and the conclusion fails:

`Toy.SymEx.acyclic_lax_iff_strict_needs_acyclic` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hacyc`: the loop followed by `assert false` has
`fuelBound = 7`; at fuel 7 every feasible path is still looping, so the lax check
passes even for postcondition `False`, while the strict check fails. -/
theorem acyclic_lax_iff_strict_needs_acyclic :
    ¬ Acyclic exLoopThenAssertFalse ∧ fuelBound exLoopThenAssertFalse ≤ 7 ∧
      ProvesLax exLoopThenAssertFalse 7 (fun _ => False) ∧
      ¬ ProvesStrict exLoopThenAssertFalse 7 (fun _ => False)
```

`Toy.SymEx.acyclic_lax_iff_strict_needs_bound` (`lean/ToySymEx/Counterexamples.lean`):

```lean
/-- Tightness of `hf`: below the bound, the acyclic `exStraight` passes the lax
check for `False` at fuel 4 but fails the strict check. -/
theorem acyclic_lax_iff_strict_needs_bound :
    Acyclic exStraight ∧ ProvesLax exStraight 4 (fun _ => False) ∧
      ¬ ProvesStrict exStraight 4 (fun _ => False)
```

**Non-vacuity witness.** exDiamond (acyclic, fuelBound 6) at fuel 6 with x1 != x0, where both checks pass.

`Toy.SymEx.nonvacuity_acyclic_lax_iff_strict` (`lean/ToySymEx/Counterexamples.lean`):

```lean
theorem nonvacuity_acyclic_lax_iff_strict :
    Acyclic exDiamond ∧ fuelBound exDiamond ≤ 6 ∧ ProvesStrict exDiamond 6 QneDiamond ∧
      ProvesLax exDiamond 6 QneDiamond
```

**Prior art.**

- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384, 2023. States that successful verification with loop-unwinding bounds is unsound unless the bounds amount to complete unwinding, and that unwinding assertions restore soundness by failing when a bound is insufficient; treating fuel exhaustion as failure plays the same role here. (Checked against the arXiv version only; no archival venue record was used.)
- Kani Rust Verifier documentation, 'Loops, unwinding, and bounds' (docs/src/tutorial-loop-unwinding.md in the model-checking/kani repository; latest commit touching that file when consulted: 21f3a2884e65c4c29465515a0117123cb8392814). States that when the #[kani::unwind] bound is too low, Kani reports a failed 'unwinding assertion' and leaves other properties 'undetermined'; tool documentation of the practice of not counting an exhausted bound as success.

**Design question.** When is accepting out-of-fuel leaves harmless?

Basis: execution (Lean kernel check) — `acyclic_provesLax_iff_provesStrict_of_fuelBound_le` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

Basis: derived (modeling bridge) — This is the model-level form of the practice that unwinding assertions cannot fail once the unwinding bound is sufficient (CBMC; Kani documentation). Reasoning: for acyclic CFGs at fuel at least `fuelBound`, no satisfiable out-of-fuel leaf remains, so accepting or rejecting such leaves makes no difference. Not established: anything about the tools' bounds or implementations.

## Boundaries

### Non-claims (per result)

Each list says what the result does **not** establish. Read it together with the plain claim.

**1. `eval-subst-agrees`**

- Only for this term language (variables, literals, +, structural ==, ite) with total coercing operations; a language with partial operations (division, overflow traps, type errors) needs a side condition that is not modelled.
- Conditions are read through Val.toBool (nonzero integers are true) while Term.eq is structural equality of values, so Boolean identities such as (c == true) = c fail for non-Boolean c (proved example in Examples.lean); a simplifier must respect this.
- Symbolic input x stands for the initial value of local x (SymStore.init = var); uninitialized locals and havoc (fresh unconstrained values in the middle of a run) are not modelled.
- Says nothing about statements, control flow or fuel; those are per-path soundness.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**2. `per-path-soundness`**

- Equality is with the concrete run at the same fuel; it says nothing about other fuels (see concrete-fuel-monotonicity).
- An outOfFuel leaf only says the concrete run also runs out of fuel at that fuel; it says nothing about termination or safety at larger fuel.
- A panic location is (block, statement index) for a failing assert; for a jump to a nonexistent block b' (and for an empty CFG, with b' = 0) the location ⟨b', 0⟩ is a sentinel meaning 'missing block b'', not statement 0 of block b'. The executor and the interpreter use the same convention.
- Does not say that every leaf is reachable: leaves with unsatisfiable path conditions are produced (no pruning) and are vacuously sound.
- The executor here never simplifies, prunes, or merges; soundness of executors that do is a separate question (see the merge and simplification cards).
- Symbolic input x stands for the initial value of local x (SymStore.init = var); uninitialized locals and havoc (fresh unconstrained values in the middle of a run) are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**3. `path-coverage`**

- Disjointness quantifies over list positions (List.Pairwise), not over semantic reachability: an unsatisfiable leaf is disjoint from everything, and duplicate unsatisfiable leaves are tolerated.
- Leaves with unsatisfiable path conditions are kept; neither half makes every leaf satisfiable.
- Disjointness is not needed for transferring leaf checks to concrete runs (leaf-check-transfer uses only exhaustiveness); it is recorded because it holds and supports counting arguments.
- Exhaustiveness is for this executor, which records every branch condition and prunes nothing; an executor that prunes or deduplicates leaves keeps exhaustiveness only if it removes leaves whose path conditions are unsatisfiable (or covered by kept leaves), which needs a solver soundness argument that is not modelled.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**4. `leaf-check-transfer`**

- Pairwise disjointness of path conditions is not a hypothesis and is not needed.
- The conclusion is about the same fuel f only: the strict variant gives no information about other fuels by itself (strict-success-monotone-in-fuel adds larger fuels), and the lax variant gives neither termination nor safety at larger fuel (out-of-fuel-is-not-success).
- A failing check does not by itself show that a concrete run fails: only a failing leaf whose path condition is satisfiable, in a sound list, witnesses a concrete failure.
- The theorem does not construct L; for L = symExec p f the hypotheses hsound and hexh are per-path-soundness and path-coverage.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**5. `lax-success-iff-concrete-success-or-out-of-fuel-same-fuel`**

- This is bounded safety at fuel f, not Hoare-style partial correctness: a lax pass at fuel 4 coexists with a panic after 13 steps (out-of-fuel-is-not-success).
- Says nothing about runs at other fuels; the lax check is not monotone in fuel (out-of-fuel-is-not-success).
- With postcondition False both sides degenerate to 'every run runs out of fuel at f'; that is not a proof of anything about returning runs.
- Reference point: the forward direction is leaf-check-transfer instantiated with per-path-soundness and path-coverage; the backward direction is per-path-soundness alone.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**6. `dropping-path-conditions-is-conservative`**

- Erasing path conditions cannot by itself produce a spurious verification success, but concluding concrete success still needs the original list to be per-leaf sound and exhaustive: then the erased check passing implies the original check passing, which implies concrete success by leaf-check-transfer (derived by composing the two cards).
- For bug finding the direction reverses: erasing path conditions produces spurious panic reports (false alarms), as dropPcs_false_alarm shows.
- Erased leaves are not per-leaf sound (dropPcs_not_leavesSound in Examples.lean), so leaf-check-transfer cannot be applied to dropPcs L directly.
- Erasing the path condition of only some leaves, checking leaves that do not cover all inputs, or erasing the guard inside a merge are different shortcuts and can give spurious success (leaf-check-transfer, unguarded-merge-spurious-success).
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**7. `guarded-merge-sound`**

- Disjointness is not needed because the merged store selects sigma1 wherever c1 holds and sigma2 only where c1 fails and c2 holds; the proof never uses agreement on the overlap. The same argument works for a many-valued behaviour relation (guardedMerge_sound_rel in Lemmas.lean). That two states sound for one reference agree on their overlap (agree_on_overlap_of_guardedSound) is a consequence, relevant to behaviour coverage (merge-behaviour-coverage-needs-agreement-on-overlap), not the reason merging is sound.
- Both states must be sound for the same continuation K, which models 'same program point and same remaining fuel'. Merging states that reach a join point with different step counts or remaining fuel (for example across loop iterations) is not covered and would need fuel alignment.
- Says nothing about behaviour coverage of a many-valued relation; there overlap matters (merge-behaviour-coverage-needs-agreement-on-overlap).
- Says nothing about solver cost or term growth, which is what state-merging heuristics trade off.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**8. `merge-leaves-preserve-soundness-and-exhaustiveness`**

- Soundness is preserved, not reflected: an unsound second leaf whose guard is covered by the first guard disappears in the merge (mergeLeaf_leavesSound_converse_fails in Counterexamples.lean).
- 'Exhaustiveness' here is LeavesExhaustive (every valuation satisfies some path condition), not behaviour coverage of a many-valued relation (Covers in merge-behaviour-coverage-needs-agreement-on-overlap), which can fail for overlapping merges.
- The statements name the first two leaves, but LeavesSound and LeavesExhaustive depend only on list membership (leavesSound_of_subset, leavesExhaustive_of_subset in Lemmas.lean), so any two leaves can be merged after reordering.
- Panic and out-of-fuel leaves are not merged by this operator.
- Pairwise disjointness of the list is neither assumed nor concluded.
- Reference point: the soundness half is guarded-merge-sound with R the concrete run and K = Outcome.ok.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**9. `unguarded-merge-spurious-success`**

- Shows one failing instance; it does not classify all unsound merge operators.
- Escape hatch: dropping the guard is harmless when, wherever c2 holds, sigma1 and sigma2 are indistinguishable through the continuation K, for example when they differ only in locals that K never reads (unguardedMerge_sound_of_agree_on_second_guard in Lemmas.lean).
- The guarded merge of the same leaves is sound and correctly fails the check (guardedMerge_rejects_Qplus1).
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**10. `merge-behaviour-coverage-needs-agreement-on-overlap`**

- 'Coverage' here is Covers B K L (behaviour coverage), not LeavesExhaustive (path-condition exhaustiveness, merge-leaves-preserve-soundness-and-exhaustiveness).
- hagree relaxes disjointness of the merged pair only: overlapping guards are allowed when the two states produce the same behaviour on the overlap. It does not let one state represent several behaviours. If every pair of states in a covering list agrees on its overlap (in particular if all guards are pairwise disjoint), the covered relation has at most one behaviour per valuation (covers_pairwise_agree_single_valued in Lemmas.lean); several behaviours at one valuation must come from states that are not merged with each other.
- Because mergeStore keeps sigma1 on the overlap, merging is asymmetric: without hagree, sigma2's behaviours on the overlap are lost (overlapping_merge_loses_behaviour).
- Sufficient conditions for hagree, proved separately and not part of this card's claim: disjoint guards (agree_on_overlap_of_disjoint) and two states sound for one single-valued reference (agree_on_overlap_of_guardedSound).
- The behaviour relation is abstract; the toy CFG semantics is deterministic, where hagree is automatic for sound states.
- Says nothing about whether a merged state's later exploration recovers a lost behaviour.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**11. `concrete-fuel-monotonicity`**

- Relies on the interpreter being deterministic; for a nondeterministic clocked semantics, more fuel can expose additional behaviours.
- Says nothing about how much fuel is needed (see the fuel-bound cards).
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**12. `strict-success-monotone-in-fuel`**

- Requires the strict check: the lax check is not monotone in fuel (it passes at fuel 4 and fails at fuel 13 for the loop of out-of-fuel-is-not-success).
- Says nothing about the size of the leaf list, the size of path conditions, or the cost of checking at the larger fuel.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**13. `out-of-fuel-is-not-success`**

- The lax check is still meaningful as bounded safety at a fixed fuel (lax-success-iff-concrete-success-or-out-of-fuel-same-fuel); the failure is reading it as success, as Hoare-style partial correctness, or as a statement about other fuels.
- Escape hatches: (1) the strict check rejects both programs (provesStrict_rejects_out_of_fuel), and a strict pass transfers to every larger fuel (strict-success-monotone-in-fuel); (2) for acyclic CFGs at fuel >= fuelBound p the lax and strict checks coincide (lax-check-equals-strict-for-acyclic-at-fuel-bound); (3) discharging loops by invariants instead of fuel is not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**14. `loop-free-fuel-bound-sufficient`**

- The bound is not minimal for CFGs with branches or unreachable blocks: every block counts toward fuelBound even if no run visits it; minimality is only stated for straight-line code.
- Acyclic does not constrain edges to nonexistent blocks; such a jump ends the run with a panic, which is not fuel exhaustion.
- The bound depends on this fuel accounting; entering a block is free and every statement and terminator costs one unit.
- ForwardEdges (successor index greater than block index) is a decidable sufficient condition for Acyclic (acyclic_of_forwardEdges); deciding Acyclic itself is not provided.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**15. `straight-line-fuel-bound-minimal`**

- Minimality is for runs that return; for inputs that panic less fuel suffices, and if every input panics the minimal sufficient fuel is smaller than fuelBound.
- The exact-minimality equivalence combines the lower bound with sufficiency for acyclic CFGs (straight-line CFGs are acyclic: acyclic_of_straightLine in Lemmas.lean) and concrete fuel monotonicity.
- The number #statements + #blocks reflects this model's accounting (each terminator, including return, costs one unit; entering a block is free).
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**16. `simplifier-soundness-characterization`**

- S rewrites the store terms of a single guarded state under that state's own path condition; applying a rewrite that is sound under c1 to a merged state guarded by c1 or c2 is unsound (path-specific-simplification-breaks-merge).
- Known not to apply to rewriting the path condition itself: a rewrite that is sound under c can turn c into a weaker condition and break soundness (simp_pathCondition_breaks_guardedSound in Counterexamples.lean: x0 -> 0 turns x0 = 0 into a condition that also holds at x0 = 5). Simplifying a path condition needs a separate argument (for example, that the new condition is equivalent to the old one).
- The right-hand side quantifies over all result types, references and continuations. For one fixed continuation the equivalence fails (simpSound_iff_fails_for_fixed_continuation in Counterexamples.lean: with a constant continuation every rewrite preserves soundness). The backward direction needs only the single instance result type Val, K = 'read local 0', and a constant store.
- Conditions are read through Val.toBool (nonzero integers are true) while Term.eq is structural equality of values, so Boolean identities such as (c == true) = c fail for non-Boolean c (proved example in Examples.lean); a simplifier must respect this.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**17. `path-specific-simplification-breaks-merge`**

- One instance; the general rule is simplifier-soundness-characterization applied with the correct path condition.
- Escape hatch: path-specific simplification stays sound if it is applied to each branch's store before merging, under that branch's path condition, leaving the merge guard unrewritten (guardedMerge_sound_of_simp_branches in Lemmas.lean; the instance x0 -> 0 in the x0 = 0 branch is the positive control pathSimp_before_merge_sound).
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**18. `strict-success-iff-concrete-success-same-fuel`**

- The equivalence is at one fuel. 'Every input returns at some fuel' does not give strict success at any single fuel for CFGs with cycles (loop-free-completeness-at-fuel-bound and its counterexample).
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Neither side says which leaves are feasible, and the leaf list is not pruned or merged, so the size of the check is not bounded by the number of feasible paths.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**19. `loop-free-completeness-at-fuel-bound`**

- Acyclic is graph acyclicity, so CFGs whose blocks are not numbered in topological order are covered; edges to nonexistent blocks are unconstrained (they panic), and unreachable blocks still count toward fuelBound p.
- The counterexample loop runs a fixed three iterations; a loop whose iteration count depends on the input without a uniform bound is not exhibited here (the term language has no order comparison).
- For CFGs with cycles, beyond the counterexample, whether some other single fuel makes the strict check complete is not examined.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

**20. `lax-check-equals-strict-for-acyclic-at-fuel-bound`**

- Derived, not stated in Lean: at such fuel no out-of-fuel leaf of symExec p f has a satisfiable path condition (per-path-soundness with loop-free-fuel-bound-sufficient).
- Says nothing about CFGs with cycles; there the lax check can pass at every fuel while no run returns (out-of-fuel-is-not-success).
- The equivalence is between the two checks at the same fuel; it does not say either check passes.
- The leaf checks quantify over every valuation satisfying a path condition, which models an ideal solver; a verifier that decides path conditions with an SMT solver adds solver soundness (and, for completeness claims, solver completeness) assumptions that are not modelled.
- Toy model only: a CFG of blocks with assignment and assert statements and goto/switchInt/return terminators over dynamically typed Int/Bool values with total coercing operations; no heap, pointers, calls, overflow, undefined behaviour, nondeterminism or concurrency. Transfer to any real verifier is a separate modelling argument that this package does not provide.

### Attractive stronger conclusions that are not established

- That any real verifier or symbolic executor (Kani, CBMC, KLEE, Rosette, a MIR-based tool) is sound, complete, or uses these definitions. All transfer to real systems is `derived (modeling bridge)` prose, not a theorem.
- That a passing lax check implies termination, or safety at any larger fuel: lax success at fuel `f` is bounded safety at `f` only (`out-of-fuel-is-not-success`).
- That per-path soundness or the same-fuel characterizations say anything about fuels other than `f`; moving between fuels needs `concrete-fuel-monotonicity`, `strict-success-monotone-in-fuel`, or acyclicity.
- That merge soundness implies preservation of behaviour coverage for many-valued behaviour relations: coverage additionally needs agreement on the overlap (`overlapping_merge_loses_behaviour`).
- That merging is reflected: a merged leaf list can be sound while the unmerged list is not (`mergeLeaf_leavesSound_converse_fails` in `Counterexamples.lean`).
- That `#statements + #blocks` is the minimal sufficient fuel beyond straight-line CFGs that return: it is not minimal with branches or unreachable blocks, and panicking runs need less.
- That rewriting the path condition itself with a sound-under-`c` simplifier is safe: it can break guarded soundness (`simp_pathCondition_breaks_guardedSound` in `Counterexamples.lean`).
- That a simplifier sound for one fixed continuation is sound: the characterization needs all result types, references and continuations (`simpSound_iff_fails_for_fixed_continuation` in `Counterexamples.lean`).
- That checking leaves with a real (incomplete) solver inherits these results: the checks here are semantic.

### Escape hatches (proved)

Proved lemmas that say which hypotheses can be weakened or replaced, and in which form a counterexample result stops applying. Quoted from `lean/ToySymEx/Lemmas.lean`.

- `unguardedMerge_sound_of_agree_on_second_guard` (`Lemmas.lean`, axioms: `propext`): An unguarded merge (keep `σ₁` under `c₁ ∨ c₂`) is sound when `σ₁` agrees with `σ₂` through `K` wherever `c₂` holds; this is the hypothesis whose absence `unguarded-merge-spurious-success` exploits.

```lean
/-- When dropping the merge guard is harmless: keeping `σ₁` under `c₁ ∨ c₂` is
sound if, wherever `c₂` holds, `σ₁` and `σ₂` are indistinguishable through
the continuation `K` (for example, they differ only in locals that `K` never
reads). -/
theorem unguardedMerge_sound_of_agree_on_second_guard {α : Type} (R : Valuation → α)
    (K : Store → α) (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂)
    (hag : ∀ ρ, holds c₂ ρ → K (σ₁.inst ρ) = K (σ₂.inst ρ)) :
    GuardedSound R K (Term.or c₁ c₂) σ₁
```

- `guardedMerge_sound_of_simp_branches` (`Lemmas.lean`, axioms: `Quot.sound`, `propext`): Simplifying each branch with a simplifier sound under that branch's own path condition and then merging is sound; this is the safe order that `path-specific-simplification-breaks-merge` contrasts with.

```lean
/-- Path-specific simplification stays sound when it is applied to each branch
before merging, under that branch's own path condition, and the merge guard is
left unchanged. -/
theorem guardedMerge_sound_of_simp_branches {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore) (S₁ S₂ : Term → Term)
    (hS₁ : SimpSoundUnder c₁ S₁) (hS₂ : SimpSoundUnder c₂ S₂)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    GuardedSound R K (Term.or c₁ c₂) (mergeStore c₁ (fun x => S₁ (σ₁ x)) (fun x => S₂ (σ₂ x)))
```

- `guardedMerge_sound_rel` (`Lemmas.lean`, axioms: `Quot.sound`, `propext`): The guarded merge stays sound for a many-valued behaviour relation (soundness, as opposed to coverage, needs no agreement on the overlap).

```lean
/-- Merge soundness for a possibly many-valued behaviour relation `B`: if every
behaviour produced by each state under its guard is allowed by `B`, so is every
behaviour produced by the guarded merge. No disjointness and no agreement on
the overlap is needed, because the merged store selects `σ₁` wherever `c₁`
holds. -/
theorem guardedMerge_sound_rel {α : Type} (B : Valuation → α → Prop) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : ∀ ρ, holds c₁ ρ → B ρ (K (σ₁.inst ρ)))
    (h₂ : ∀ ρ, holds c₂ ρ → B ρ (K (σ₂.inst ρ))) :
    ∀ ρ, holds (Term.or c₁ c₂) ρ → B ρ (K ((mergeStore c₁ σ₁ σ₂).inst ρ))
```

- `agree_on_overlap_of_disjoint` (`Lemmas.lean`, axioms: none): Disjoint guards discharge the agreement hypothesis of `merge-behaviour-coverage-needs-agreement-on-overlap`.

```lean
/-- Disjoint guards agree on their (empty) overlap. -/
theorem agree_on_overlap_of_disjoint {α : Type} (K : Store → α) (c₁ : Term) (σ₁ : SymStore)
    (c₂ : Term) (σ₂ : SymStore) (h : Disjoint c₁ c₂) :
    ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)
```

- `agree_on_overlap_of_guardedSound` (`Lemmas.lean`, axioms: none): Two states sound for the same single-valued reference agree on their overlap, discharging the agreement hypothesis.

```lean
/-- Two states sound for the same single-valued reference agree (through `K`)
wherever both guards hold. This is a consequence of soundness; the proof of
merge soundness does not need it. -/
theorem agree_on_overlap_of_guardedSound {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)
```

- `acyclic_provesLax_iff_provesStrict_of_fuelBound_le` (`Statements.lean`, axioms: `Classical.choice`, `Quot.sound`, `propext`): For acyclic CFGs at fuel at least `fuelBound`, accepting out-of-fuel leaves is harmless; this is the escape hatch for `out-of-fuel-is-not-success` (card `lax-check-equals-strict-for-acyclic-at-fuel-bound`).

```lean
/-- For acyclic CFGs at any fuel `f ≥ fuelBound p`, the lax check (out-of-fuel
leaves accepted) and the strict check coincide: no satisfiable out-of-fuel leaf
remains. -/
theorem acyclic_provesLax_iff_provesStrict_of_fuelBound_le (p : Cfg) (f : Nat)
    (Q : Store → Prop) (hacyc : Acyclic p) (hf : fuelBound p ≤ f) :
    ProvesLax p f Q ↔ ProvesStrict p f Q
```

- `acyclic_of_forwardEdges` (`Lemmas.lean`, axioms: none): Decidable sufficient condition for `Acyclic`.

```lean
theorem acyclic_of_forwardEdges (p : Cfg) (h : ForwardEdges p) : Acyclic p
```

- `acyclic_of_straightLine` (`Lemmas.lean`, axioms: `Quot.sound`, `propext`): Straight-line CFGs are acyclic, so the acyclic results apply to them.

```lean
theorem acyclic_of_straightLine (p : Cfg) (hsl : StraightLine p) : Acyclic p
```

- `leavesSound_of_subset` (`Lemmas.lean`, axioms: `propext`): Per-leaf soundness depends only on membership, so the merge lemmas, stated for the first two leaves, apply to any two leaves after reordering.

```lean
theorem leavesSound_of_subset (p : Cfg) (f : Nat) {L L' : List Leaf}
    (hsub : ∀ l, l ∈ L' → l ∈ L) (hs : LeavesSound p f L) : LeavesSound p f L'
```

- `leavesExhaustive_of_subset` (`Lemmas.lean`, axioms: none): Exhaustiveness is monotone under adding leaves (membership only).

```lean
theorem leavesExhaustive_of_subset {L L' : List Leaf}
    (hsub : ∀ l, l ∈ L → l ∈ L') (he : LeavesExhaustive L) : LeavesExhaustive L'
```

### Supporting negative and boundary lemmas (proved)

Proved lemmas that the non-claims and the list of stronger conclusions above cite by name. They are not results of this package: they are not listed in `results.json`, so their statements are quoted here but are not hash-pinned in `audit/statements.json`; their axioms are recorded in `audit/axioms.json` with every other library declaration. Quoted from the named files under `lean/ToySymEx/` (doc comment and statement; proofs omitted).

- `dropPcs_not_leavesSound` (`lean/ToySymEx/Examples.lean`, axioms: `propext`): Erasing path conditions destroys per-leaf soundness, so `leaf-check-transfer` cannot be applied to `dropPcs L` directly (cited under `dropping-path-conditions-is-conservative`).

```lean
/-- `dropPcs`, negative: erased leaves are not per-leaf sound (the erased
panic leaf of `exAssertTrue` claims a panic on every input). -/
theorem dropPcs_not_leavesSound :
    ¬ LeavesSound exAssertTrue 2 (dropPcs (symExec exAssertTrue 2))
```

- `mergeLeaf_leavesSound_converse_fails` (`lean/ToySymEx/Counterexamples.lean`, axioms: `Quot.sound`, `propext`): The converse of `mergeLeaf_preserves_leavesSound` fails: a merged leaf list can be per-leaf sound while the unmerged list is not (cited under `merge-leaves-preserve-soundness-and-exhaustiveness`).

```lean
/-- The converse of `mergeLeaf_preserves_leavesSound` fails: an unsound second
leaf whose guard is covered by the first guard disappears in the merge. -/
theorem mergeLeaf_leavesSound_converse_fails :
    ¬ LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₁, .ok dσ₂⟩] ∧
      LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₁ dσ₂]
```

- `covers_pairwise_agree_single_valued` (`lean/ToySymEx/Lemmas.lean`, axioms: `propext`): A list whose states pairwise agree on their overlaps covers at most one behaviour per valuation (cited under `merge-behaviour-coverage-needs-agreement-on-overlap`).

```lean
/-- If every pair of guarded states in a covering list agrees (through `K`) on
the overlap of their guards — in particular, if the guards are pairwise
disjoint — then the covered relation has at most one behaviour per valuation.
So a genuinely many-valued relation can only be covered by a list in which
some pair of overlapping states disagrees. -/
theorem covers_pairwise_agree_single_valued {α : Type}
    (B : Valuation → α → Prop) (K : Store → α) (L : List (Term × SymStore))
    (hcov : Covers B K L)
    (hpw : L.Pairwise (fun cs₁ cs₂ => ∀ ρ, holds cs₁.1 ρ → holds cs₂.1 ρ →
      K (cs₂.2.inst ρ) = K (cs₁.2.inst ρ))) :
    ∀ ρ a₁ a₂, B ρ a₁ → B ρ a₂ → a₁ = a₂
```

- `simp_pathCondition_breaks_guardedSound` (`lean/ToySymEx/Counterexamples.lean`, axioms: `Quot.sound`, `propext`): Rewriting the path condition itself with a simplifier that is sound under it can break guarded soundness (cited under `simplifier-soundness-characterization`).

```lean
/-- Rewriting the path condition itself with a simplifier that is sound under
that path condition can break soundness: `x0 ↦ 0` turns `dc₁` (`x0 = 0`) into a
condition that also holds at `x0 = 5`. -/
theorem simp_pathCondition_breaks_guardedSound :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧ GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
      holds (Term.substVar 0 (int 0) dc₁) ρ5 ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.substVar 0 (int 0) dc₁) dσ₁
```

- `simpSound_iff_fails_for_fixed_continuation` (`lean/ToySymEx/Counterexamples.lean`, axioms: none): For one fixed (constant) continuation, the characterization's equivalence fails (cited under `simplifier-soundness-characterization`).

```lean
/-- For one fixed continuation the equivalence fails: with a constant
continuation every rewrite preserves guarded soundness, including one that is
not sound under the path condition. -/
theorem simpSound_iff_fails_for_fixed_continuation :
    ¬ SimpSoundUnder tt (Term.substVar 0 (int 0)) ∧
      ∀ (R : Valuation → Unit) (σ : SymStore),
        GuardedSound R (fun _ => ()) tt σ →
          GuardedSound R (fun _ => ()) tt (fun x => Term.substVar 0 (int 0) (σ x))
```

### Tightness status `unknown`

None. All 22 hypotheses of the 20 results are `tight`, each with a proved counterexample in canonical form (every other hypothesis holds and the conclusion fails).

### Disproved or dropped statements

None. Every main statement listed under **Findings** is proved as stated; no statement was found false and none was dropped.

### Not examined

- **Not examined:** merging two states whose remaining fuel differs (not expressible with one continuation `K`).
- **Not examined:** soundness of path pruning (dropping leaves with unsatisfiable path conditions); the model has no solver.
- **Not examined:** a loop whose iteration count depends on the input without a uniform bound but which terminates on every input; the term language has no order comparison, so such a loop is not expressible in the obvious way.
- **Not examined:** a decision procedure for `Acyclic`; `ForwardEdges` (every successor index is larger than the block index) is a decidable sufficient condition (`acyclic_of_forwardEdges`).
- **Not examined:** heap, pointers, calls, overflow, undefined behaviour, nondeterminism, concurrency.

## Evidence

Observed 2026-11-20: build, axiom audit and hash computation under Lean `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API `repos/leanprover/lean4/git/refs/tags/v4.34.1`; the local binary reports the same commit). No Mathlib; no Lake dependencies.

**Axiom audit.** `audit/axioms.json` records, for each of the 673 declarations of the `ToySymEx` library, the axioms reported by Lean's `collectAxioms`; every declaration uses only a subset of `propext`, `Classical.choice`, `Quot.sound`. No Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`.

**Statement and closure hashes.** For every Lean name a result references (main theorems, tightness counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records the SHA-256 of Lean's `repr` of the statement's type (`statement_sha256`) and the SHA-256 of its definition closure (`closure_sha256`): the newline-joined, sorted lines `name : repr(type)` (followed by ` := repr(value)` for non-theorems) of every library-local constant reachable from the statement through types, definition values and inductive constructors, with theorem bodies excluded. The table repeats those records.

| Theorem | Role | Axioms | `statement_sha256` | `closure_sha256` (closure size) |
| :--- | :--- | :--- | :--- | :--- |
| `acyclic_exec_ne_outOfFuel_of_fuelBound_le` | main (loop-free-fuel-bound-sufficient) | `Classical.choice`, `Quot.sound`, `propext` | `764fafff876873c4c7f1711061072998ec92a5a779b1832ad092a4a24df6dd31` | `387d3fd798c5aad3df23c43d80759257f460fe5b5dd6814478a9a9ed78a7597e` (69) |
| `acyclic_provesLax_iff_provesStrict_of_fuelBound_le` | main (lax-check-equals-strict-for-acyclic-at-fuel-bound) | `Classical.choice`, `Quot.sound`, `propext` | `61bb519163330648508fb8f0e49a6e12a9a0ba11c0629896bffdf49369586ffb` | `1f469eb868ef6bb9dff79a3bf35c5e117493924707e84ff3f70eb4ef95987e25` (103) |
| `acyclic_provesStrict_fuelBound_iff_forall_exists_fuel` | main (loop-free-completeness-at-fuel-bound) | `Classical.choice`, `Quot.sound`, `propext` | `d591762ae7c7cffcf23ecef7853a8851c77de48b44fe34320a6238837bbc880b` | `ec2904a1fb78ee7164ca812e1243609b12e9de45e9059352d6aefa2576efa169` (107) |
| `dropPcs_false_alarm` | main (dropping-path-conditions-is-conservative) | `Quot.sound`, `propext` | `c7518ee239b9c74d2e903bab8514413d650030d3cd76991b4de04ec4b3236563` | `340b8b63b79f445c8257ad8f484561ca45c60cf1ebdb9544446906f2cacbb719` (97) |
| `eval_subst` | main (eval-subst-agrees) | `propext` | `4a21283feb2baf1b3389ba78ca9f8a96b035e3d6b04a26571ab9dcfbebe20e20` | `d05eb0ba0ea6b6119bdbf30df1694c5d1303fba534fd89fdc1f6dea9927084ad` (38) |
| `exec_fuel_mono` | main (concrete-fuel-monotonicity) | `Classical.choice`, `Quot.sound`, `propext` | `44ea3135e29a9704216260a8537e000a9303a666b9219a37af0a088b7827f890` | `3dc71c059347a1a4ba3e14707e0039bfdcaafa819162cd34f6bd0010a244f2cb` (65) |
| `exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax` | main (leaf-check-transfer) | `propext` | `468e55aa08d2eed1fd710b8dc97abb7a7e8489c6c5c29c0f9bda5b4750cfb376` | `fd200066b72161cf3b2f5dc8c40e7b743e872264d3fac83f87797f7c29415c61` (88) |
| `exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve` | main (leaf-check-transfer) | `propext` | `73af9a0e60d51b90959f592c3a1f1bcecbb29572acf28c887ff5aaaaa5cf22c3` | `aff494ca9596f80828f3c87bbef361d4386f54bac3be6483078327b014f3ab7a` (90) |
| `exec_okWith_of_provesStrict_of_le` | main (strict-success-monotone-in-fuel) | `Classical.choice`, `Quot.sound`, `propext` | `15fc3a35c06a164d5c5f431cc20d63c89c1814f6464e6703425827a852728f26` | `a5d3ef8252d89ddfde80fd9552eddafeff112de3754d4a53d43d9ca45ac2bf69` (103) |
| `guardedMerge_preserves_covers_of_agree_on_overlap` | main (merge-behaviour-coverage-needs-agreement-on-overlap) | `Quot.sound`, `propext` | `ff94e5362528f7665130d070fb27f52d5661d9785302d9f3196184143f765c61` | `f3c38c5635be023a866c21779821159095597ef483e324fab878612851c50106` (41) |
| `guardedMerge_sound` | main (guarded-merge-sound) | `Quot.sound`, `propext` | `255116691e0f4f2394002a9a9099a87953342b413d7a97f4a719ae835d30e637` | `28c817837d91fafcfda60b3509abc2cde71a0546e0c51f8ee0a2c816a1fd7f99` (41) |
| `leavesProve_of_leavesProve_dropPcs` | main (dropping-path-conditions-is-conservative) | `Quot.sound`, `propext` | `5d0fc8ec6274070e5096828b0075e7791ac733162487e0327e2667d3981ee336` | `8f0035262b231d70f07764b0ecb36939cd3ba125b15a0dbacbb849af38995efa` (64) |
| `mergeLeaf_leavesExhaustive_iff` | main (merge-leaves-preserve-soundness-and-exhaustiveness) | `propext` | `61b75560c8c91064301ce4de2277a74b69a606a05e00a730a5ab4c4c1b4c2bc0` | `9ae807f92e7e271c4387f11839dbaf216c711cf7087d791d959b4fad64ea765b` (49) |
| `mergeLeaf_preserves_leavesSound` | main (merge-leaves-preserve-soundness-and-exhaustiveness) | `Quot.sound`, `propext` | `c7a2c6b3b13d47d926e5aa8bb4908bf5d963b8d42bab2a33ed643e9f7b6385af` | `802e5e87d2d329e5cb886b9685bc220756842334c453ed1c2ea6a3a8a864e4b0` (86) |
| `pathSimp_after_merge_breaks_soundness` | main (path-specific-simplification-breaks-merge) | `Quot.sound`, `propext` | `ecff7aaec929d053c4f547f69dee8c62144aecea15e8b846a8696708991112ba` | `60bb56294aebf68c794ef9e29d4b6c56b0633a5cf4f57c4a8d6b86de83c4e017` (101) |
| `provesLax_iff_forall_exec_okWithOrOutOfFuel` | main (lax-success-iff-concrete-success-or-out-of-fuel-same-fuel) | `Quot.sound`, `propext` | `cc9d5f2b73abc5aebce46bca55925544fcbabb53052616abf52ceb16682927ea` | `7d7e4f9f6f171f13f9c1ee44fbd8b1a63e5bb93997450bbb9745eb7005c40885` (101) |
| `provesLax_loopThenAssertFalse_but_panics` | main (out-of-fuel-is-not-success) | `propext` | `0c6d0ee1c257f517d939fbc8302d32f18cb04512343202a2b9a8b5c01600398f` | `8ae63db67b8f88bee19e159bfd3ecc8c9e72ab0de5ca8fad4c8d8406bfbdd508` (103) |
| `provesLax_selfLoop_every_fuel_but_never_returns` | main (out-of-fuel-is-not-success) | `propext` | `66233b74fca7d0089cd87ec324c3e98770420fd2ab4f7e5c542ed1f4a31c2d5f` | `b0c50062ed50cda1fda2d2259da03b6c584676b07d069f721931884e06249c29` (102) |
| `provesStrict_iff_forall_exec_okWith` | main (strict-success-iff-concrete-success-same-fuel) | `Quot.sound`, `propext` | `47bf166ead8175efad12b3cd1745b68279812db1713ebf56984c3e23c08e1876` | `a5d3ef8252d89ddfde80fd9552eddafeff112de3754d4a53d43d9ca45ac2bf69` (103) |
| `provesStrict_mono` | main (strict-success-monotone-in-fuel) | `Classical.choice`, `Quot.sound`, `propext` | `d32ae277f41965907a61ad96de67f9708638fcccd7093ab5cd85930a303a6570` | `4c8e12b5b726d1498af146b9ea38d783950feff07b3bb31c4dc94ddb8e86045f` (95) |
| `simpSoundUnder_iff_preserves_guardedSound` | main (simplifier-soundness-characterization) | `Quot.sound` | `0bc74efaca538125870e47e1e5f13844daad1e4e51ef082a405606aa914228f4` | `8d07442baa9e959912fe3aa8a6909be870b7cda4903d70f56934ee20d713da7b` (39) |
| `straightLine_exec_ok_iff_fuelBound_minimal` | main (straight-line-fuel-bound-minimal) | `Classical.choice`, `Quot.sound`, `propext` | `1dfc0f5f8c1948725bc41ef672304e37533df6377fb5d2fa273e6e860a7b0541` | `b1a3ce5649b7738e5a2ab3280733690275ad5f5d734070934591c35cd3cac512` (67) |
| `straightLine_fuelBound_le_of_exec_ok` | main (straight-line-fuel-bound-minimal) | `Quot.sound`, `propext` | `13016069b280d5244221568c4c48f6ee1a0cc2b17a5b5c47a3073e9601067fe2` | `b1a3ce5649b7738e5a2ab3280733690275ad5f5d734070934591c35cd3cac512` (67) |
| `symExec_exhaustive` | main (path-coverage) | `Quot.sound`, `propext` | `3a2480f229b17cf9333aa0da34286866e3204d516fd3d518f272c436fbd8c41b` | `12165ead3505e4556414a86762c366beafd74b65284b59a7305017cfabac7db3` (76) |
| `symExec_leaf_sound` | main (per-path-soundness) | `Quot.sound`, `propext` | `c0fb156afbbc9efb1383af3b9a60a6b23b211327d72c601bc740f2689778bbc2` | `64d6ee233ffaa50571d7ad53da1b5283e4b935d1c53c94fd5e4290c583e0a8a4` (95) |
| `symExec_pairwise_disjoint` | main (path-coverage) | `Quot.sound`, `propext` | `0606498bf0feb3032e722ef220a799af141ca105ef2ea797af65e0136760d921` | `d1ce94370bd43e330dcc9d3acb0250bb802a7c3f986251869db0ef4859880950` (77) |
| `unguardedMerge_spurious_success` | main (unguarded-merge-spurious-success) | `Quot.sound`, `propext` | `ef79afa3ae69dbadd69267b87b9c46555e42ebdeed6f4b3640efe83b421074a6` | `e05a26fd6e9ca6aa173a4cdfd7255388bc30de9d37dabfe989c8a34fd0eb10a6` (105) |
| `acyclic_completeness_needs_acyclic` | counterexample for `hacyc` (loop-free-completeness-at-fuel-bound) | `Quot.sound`, `propext` | `355d282185a517fc517f60a646f64b852fb1d7ba79338e8dbde7313aa123c247` | `829ef599c9d4b3051a75995f86f4aa013967e7da29c410bbcbb5731a72814e19` (110) |
| `acyclic_fuelBound_needs_acyclic` | counterexample for `hacyc` (loop-free-fuel-bound-sufficient) | `Quot.sound`, `propext` | `f2f674263f3e40e9ed1be46136c9910d9c73a81c266bb0b9496ac919324cf345` | `f55c02292e0fd968e1f560650dbe462851411c5f323ac81a780c4673ab18e0ef` (71) |
| `acyclic_fuelBound_needs_bound` | counterexample for `hf` (loop-free-fuel-bound-sufficient) | `propext` | `41e1595b7b4cefbc3aefbf026d7854256cefc2e5f4b50375c4470c88bd7c527a` | `a8d6924302036271b4e6abea23dae1ce40f145df14b17174520b7db22f160b9d` (71) |
| `acyclic_lax_iff_strict_needs_acyclic` | counterexample for `hacyc` (lax-check-equals-strict-for-acyclic-at-fuel-bound) | `Quot.sound`, `propext` | `7e93756c4733d9ca3ca8d33691b38cda536966e4b85a34a3f1fae1a4e16cf90e` | `d32628da6d2bcc1acebd55dbc17ea161522736c8282a4115e7919abda9edb3a3` (105) |
| `acyclic_lax_iff_strict_needs_bound` | counterexample for `hf` (lax-check-equals-strict-for-acyclic-at-fuel-bound) | `Quot.sound`, `propext` | `d73de356a3873960a6d8f080faa8108ddb69f1f745a9121ad6e2f6f08123ffc4` | `20015216b02f0ce387dfd0e04c815f35808c1f2a57fd4a3e7039ddd07cf3f23d` (104) |
| `covers_merge_needs_covers` | counterexample for `hcov` (merge-behaviour-coverage-needs-agreement-on-overlap) | `propext` | `5e9e13ef58957ec692a327fb36b46942b2274e55591140c979f95b87805a0af6` | `1b7fada718e3b6c9a3ca8ea170674329cd6dee4425856e38f6f3f1d0296852a5` (81) |
| `exec_fuel_mono_needs_le` | counterexample for `hle` (concrete-fuel-monotonicity) | `propext` | `01111b6b5e2e9aebafa2ad262a11970761eeae77e0b1ea1074ea33f90c208c31` | `49bac07d6a014dc407b6ac42b43bc77cb7300ab19cd138ae08efb1155f436faa` (68) |
| `exec_fuel_mono_needs_ne_outOfFuel` | counterexample for `hne` (concrete-fuel-monotonicity) | `propext` | `cd33c336b4b4786af597ea3fb2f82be099ba782638c823389b5d31e0ac0e8541` | `49bac07d6a014dc407b6ac42b43bc77cb7300ab19cd138ae08efb1155f436faa` (68) |
| `guardedMerge_needs_first_sound` | counterexample for `h₁` (guarded-merge-sound) | `Quot.sound`, `propext` | `6e1d0ac0ec29ce4e9851217e1c2fc4693e4fa01ad9a59fb800bf0999f34892e2` | `e1c74ae7cfa0c6a40c4386530bffcad784e28f07a45ce5603a509903a6e4f80b` (83) |
| `guardedMerge_needs_second_sound` | counterexample for `h₂` (guarded-merge-sound) | `Quot.sound`, `propext` | `adc3fac14a33662b4d0e67774f9a69d8584b7d31b48a8d74b7b1bc5d6a6ed7f8` | `1b5124a7a6fd311960cba190e914bdb6a259306b53e19b0e79e8912e5a7e4525` (83) |
| `guardedMerge_rejects_Qplus1` | positive control (unguarded-merge-spurious-success) | `Quot.sound`, `propext` | `cf740ac0aad868ab16ab47757833f70274d3a9f7c0e3eee9070d40accda7fe8d` | `46f953c3b5cfd698c6fe16a9f44604f28333b02f8e73eff0791178c7c20fc3f4` (104) |
| `leavesProve_dropPcs_needed` | counterexample for `h` (dropping-path-conditions-is-conservative) | `Quot.sound`, `propext` | `f51a211a4d9122a8dea0ae0cfdd188f3921a0928cfb4c4a6b81c6dd68cf061e1` | `5f1d7a10212392b1806577b862e8c7809be6c67b7ccdb321165b6ae2fa15f96d` (98) |
| `mergeLeaf_needs_leavesSound` | counterexample for `hs` (merge-leaves-preserve-soundness-and-exhaustiveness) | `propext` | `d38c339ac845d310598d18f16fe871ca68e4dd25be35151b5ccf4544459909d0` | `862a1508193471579136580a7b64e75e521bc06fccf84c17d21bcb511f7df238` (96) |
| `nonvacuity_acyclic_completeness` | non-vacuity (loop-free-completeness-at-fuel-bound) | `Quot.sound`, `propext` | `96b18f9ddebb11b4b25c2017494a8dea28530a5c4a85f1b37f02e2796697c225` | `46d762ea3a29399e6f8460999ced403bb1e25279d316d933c661f7790ddcaa52` (102) |
| `nonvacuity_acyclic_fuelBound` | non-vacuity (loop-free-fuel-bound-sufficient) | `propext` | `227dd6d8a30f16788cd8a9025eeb1e1d836982541adcf4bd24320a590cb4eeab` | `4d2e11aea680f5c0471abdb45c05f6063c2d8737543cee1f858e87a3620e9cfa` (32) |
| `nonvacuity_acyclic_lax_iff_strict` | non-vacuity (lax-check-equals-strict-for-acyclic-at-fuel-bound) | `Quot.sound`, `propext` | `a474aa77927a0773d17d0ebe16fd8e16360efc0d6a59b25189b65ccfc88b9406` | `c2c73f14c491eac65f532aee4639d7ac97fe51e9f342cdb9c8b6daa639dfff72` (106) |
| `nonvacuity_covers_merge` | non-vacuity (merge-behaviour-coverage-needs-agreement-on-overlap) | `propext` | `5a406e70a9a00289db318b5da06ce716e1fac8af9b37627358fe3eb57adffdc7` | `c6ad457d242431da77761d7bcf4f65e2c831d52d92d9d921bbdf3f539dbb7f21` (52) |
| `nonvacuity_eval_subst` | non-vacuity (eval-subst-agrees) | none | `bea0e88dd0cf22e808410f79f2b33891e032b6caaa68357454720d40ebf724f9` | `d337222c50485ceb1bafe6e742f9dfb6a13c48746548769292ddd2ec2f4c407b` (43) |
| `nonvacuity_exec_fuel_mono` | non-vacuity (concrete-fuel-monotonicity) | `propext` | `fc1e560b5e80c2098618f7db99ed48ee7a469ad6f5d6db5d49648ddd82d4af66` | `49bac07d6a014dc407b6ac42b43bc77cb7300ab19cd138ae08efb1155f436faa` (68) |
| `nonvacuity_guardedMerge_sound` | non-vacuity (guarded-merge-sound) | `Quot.sound`, `propext` | `f51eb88dff1d2aa7e592aad469353844700685b7cb93562cde21e64228e2855f` | `f085b0ffcda5708bd6c7a2c36eff4dc4e162751b2415699aed23b3038621add3` (85) |
| `nonvacuity_leavesProve_dropPcs` | non-vacuity (dropping-path-conditions-is-conservative) | `Quot.sound`, `propext` | `8b5a9762c7962c61aa2c8218b78dfd95820d97401227d9589d34e209844e0694` | `332412d517e0cd3b6c27244d4fcc13ac711a3ad08b74329907a98e3fc49e0ff9` (98) |
| `nonvacuity_mergeLeaf` | non-vacuity (merge-leaves-preserve-soundness-and-exhaustiveness) | `Quot.sound`, `propext` | `b29964385dc58c1a94ace9a276176759860fe8b7b3b456ca74289a8ffa69e461` | `f0a81bd4fb3768d225159368aaaa9acbaf094f7aadf6c5e2bfdcc02e5ae77314` (94) |
| `nonvacuity_path_coverage` | non-vacuity (path-coverage) | `propext` | `ddf9708b1c8bd74b47ee8617c4cd3d0baf11cb9ce32c7041bf9a26fe311c6197` | `7d300c6536b8db14637dfa24386ce7a4675eb2f0e3193878ef003dc3d6e60d92` (79) |
| `nonvacuity_provesLax_iff` | non-vacuity (lax-success-iff-concrete-success-or-out-of-fuel-same-fuel) | `Quot.sound`, `propext` | `1ae2c2a1dc1a98c8a692b94c67dce3b736997448d7e71736eac9367441740b55` | `14dcdbf436753c2af7427ddf320ea56e7188edcdea5f47474cb07b0660f2c20e` (112) |
| `nonvacuity_provesStrict_iff` | non-vacuity (strict-success-iff-concrete-success-same-fuel) | `Quot.sound`, `propext` | `38e01605e9ea32c358338a4593fff48785315e55656aefbaa5f009c08babb852` | `91eb76c572bb29838c25d9ff9d5701d1a4a131bc4ad445cacc270583c35cd5d6` (111) |
| `nonvacuity_provesStrict_mono` | non-vacuity (strict-success-monotone-in-fuel) | `Quot.sound`, `propext` | `f3e92cdb0dea3e8876d9673f99e1eaf1914d51e0fa187b45132e8c7c98f29e9f` | `05e622305bae1fd4e11661c3fcec59d30d5549d3fe74198656289c810bd86504` (98) |
| `nonvacuity_simpSoundUnder` | non-vacuity (simplifier-soundness-characterization) | `propext` | `5fed746f0be0ae587a15dbabc5eb25961bc90a64dac619e4bafe1d7a95d61690` | `800773a68e3accb2d6a4cc64b1c549afba519ed2c351c2266bb344da808cd23b` (43) |
| `nonvacuity_straightLine_fuelBound` | non-vacuity (straight-line-fuel-bound-minimal) | `Classical.choice`, `Quot.sound`, `propext` | `99991ce36a6008e9eaa2be88fb8336ce8c84d00d97914274047f07d526607fd0` | `cf199277d40833a9be43577075333a0110530eb8c18585ac40ee35777a4a0699` (70) |
| `nonvacuity_symExec_leaf_sound` | non-vacuity (per-path-soundness) | `propext` | `77844bb3b9351c0b6a29e6322d04136c3336093d83fd103b0ce578a618183f9b` | `7350ec972461380d7e2dcf34451934d691cf9c3b24d80f5a592f2fccf5b6617b` (80) |
| `nonvacuity_transfer` | non-vacuity (leaf-check-transfer) | `Quot.sound`, `propext` | `d2ded3eb55625b38f9782941c4a5e48a976cb44a100abb2e142af8b161a5d9c6` | `daff8873513c1a4b571dcb170f13e253894993b939cc8bb0b8f56b30a36fb74b` (110) |
| `overlapping_merge_loses_behaviour` | counterexample for `hagree` (merge-behaviour-coverage-needs-agreement-on-overlap) | `propext` | `66fc486444eeaab280639f1b8477a3586d47b0b21e7e24328d0a59c26c95c748` | `e54ae75882cf0e70e6a661da5cf02914b97f1e8f33f5ce9bddc4fb4ca78b05ff` (46) |
| `pathSimp_before_merge_sound` | positive control (path-specific-simplification-breaks-merge) | `Quot.sound`, `propext` | `b914b7a5ba6f9097a50df2f7cb28d27e117192483b641827de9f208b0a61ed4a` | `19177205a7f76ca0d9b40f2df687daf6aff1d65d0f0da8a81677f2ac1771df01` (99) |
| `provesStrict_mono_needs_le` | counterexample for `hle` (strict-success-monotone-in-fuel) | `Quot.sound`, `propext` | `0c2fa2b55a5cd11f47719aec8f239de4322756e3ae39a7f4b7af32876f44e4c4` | `788faffe2c318693932cfd02c801be11176e63eb3a24e45bc0f82124f7b29bca` (107) |
| `provesStrict_mono_needs_provesStrict` | counterexample for `h` (strict-success-monotone-in-fuel) | `propext` | `dbd8188175a2b23027a6c06c1808f5184605ac16c6a01a5a760cfb110d81d80d` | `82976c79bebb5a31392841ea2a5137fde09ded6df8b7d5c7dee22d51a133cb6c` (107) |
| `provesStrict_rejects_out_of_fuel` | positive control (out-of-fuel-is-not-success) | `Quot.sound`, `propext` | `dcaaf5efe2164e07dc305ca187cdde451e3c82076d1b1c8b1048b409f2871e82` | `36e6dc14b6d448c2600618cbe14ce2ad67da2e21ad1f24d1fe3e7d24e6a9a3a4` (99) |
| `straightLine_fuelBound_needs_ok` | counterexample for `hok` (straight-line-fuel-bound-minimal) | `propext` | `868c5b7c41c5eddc4c4fa8965056713b025c4903118f863d31bbe5c4dd932808` | `39802392d8c45f585cdcc8c0ecc37576311b5ad159b9028eb432bf98dc415f7e` (73) |
| `straightLine_fuelBound_needs_straightLine` | counterexample for `hsl` (straight-line-fuel-bound-minimal) | `propext` | `c7f7404ece6247d6a81cf49e408bdefc0051e996e125e990b8ecd6452d726d99` | `de1359720c32b14e3b1e77c33f083b2443aecb3a36332e0d76e4bae91070b64f` (70) |
| `symExec_leaf_sound_needs_membership` | counterexample for `hl` (per-path-soundness) | `propext` | `927539022d094b90353659e47325711dd1a892b4372831821a8fb497b1571e55` | `8983e999ecbe5cc1259a2f42089ca6160e4cac16d31340408e43fa4b63d19302` (83) |
| `symExec_leaf_sound_needs_pc` | counterexample for `hpc` (per-path-soundness) | `propext` | `e603051cecf675bc56798932c660e87a146c8f1265c3375db592a6c34140e0ff` | `6192d083a5965677c72fa7de2e97fc8cd07dfb3fb5ca4134b584e1f19e87aa98` (97) |
| `transfer_needs_exhaustive` | counterexample for `hexh` (leaf-check-transfer) | `propext` | `8f4ba4fb102070d3962894a3a6e13306f79a5c857928dc1d3c02d3c91322c09c` | `31c6ed69cfedc2c40dd9409f328e283565c056d3e74b325018aaa4e7b123d76d` (101) |
| `transfer_needs_leaf_check` | counterexample for `hprove` (leaf-check-transfer) | `propext` | `4e5977e739feecca601fc0d13a0fbbf33d9bc0e25382fba515f30bd52a72e68d` | `78e462ef7d8b21342bdcf1c9d5f9e9b03baa1143e6e2c4823a77c03533cead88` (109) |
| `transfer_needs_leavesSound` | counterexample for `hsound` (leaf-check-transfer) | `propext` | `376ba9258ba68193ecef899cac5cc74b3a2b9fc65653e30603ecce5bcd06b884` | `cac6ee7f4ed92ad75cefa1225d83942b91e224b194dfa130548e3e6f34a72c43` (99) |

**Primary sources.** Exact records of every source cited under **Findings**, with how each was checked.

- J. C. King, 'Symbolic execution and program testing', Communications of the ACM 19(7):385-394, July 1976, doi:10.1145/360248.360252. *Full text inspected (archival PDF); bibliographic record re-confirmed.*
- F. S. de Boer, M. Bonsangue, 'Symbolic execution formally explained', Formal Aspects of Computing 33(4-5):617-636, 2021, doi:10.1007/s00165-020-00527-y (open access). *Full open-access text inspected (Lemma 2.1, Corollary 2.2, Theorems 2.3 and 2.4); it does not state list-position pairwise disjointness, fixed-fuel equivalences or fuel bounds.*
- S. Porncharoenwase, L. Nelson, X. Wang, E. Torlak, 'A formal foundation for symbolic evaluation with merging', Proc. ACM Program. Lang. 6(POPL), Article 47, 2022, doi:10.1145/3498709. *Full open-access text inspected (Theorems 5 and 9).*
- F. Vogels, B. Jacobs, F. Piessens, 'Featherweight VeriFast', Logical Methods in Computer Science 11(3:19), 2015, doi:10.2168/LMCS-11(3:19)2015 (also arXiv:1507.07697). *Bibliographic record and abstract checked; cited for its Coq soundness proof only.*
- R. Aissat, F. Voisin, B. Wolff, 'Infeasible paths elimination by symbolic execution techniques: proof of correctness and preservation of paths', Archive of Formal Proofs, August 2016 (entry date 2016-08-18; ISSN 2150-914x), https://isa-afp.org/entries/InfPathElimination.html. *Entry page and document outline checked. The entry page is updated with each archive release; its entry date and the archive ISSN are the stable coordinates recorded in `REPORT.json`.*
- S. Keuchel, S. Huyghebaert, G. Lukyanov, D. Devriese, 'Verified symbolic execution with Kripke specification monads (and no meta-programming)', Proc. ACM Program. Lang. 6(ICFP), Article 97, 2022, doi:10.1145/3547628. *Full open-access text inspected (soundness only; completeness explicitly not a goal).*
- R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, 'A survey of symbolic execution techniques', ACM Computing Surveys 51(3), Article 50, pp. 50:1-50:39, 2018, doi:10.1145/3182657 (arXiv:1610.00502v3). *Section content checked via the arXiv version (v3) only; the journal volume, article number and pages via the DOI record.*
- V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, 'Efficient state merging in symbolic execution', PLDI 2012, pp. 193-204, doi:10.1145/2254064.2254088. *Full author PDF inspected (Section 1 example; Algorithm 1, line 20).*
- S. Swords, J. Davis, 'Bit-blasting ACL2 theorems', ACL2 Workshop 2011, EPTCS 70, pp. 84-102, doi:10.4204/EPTCS.70.7 (arXiv:1110.4676). *Full open-access text inspected (the `:g-ite` symbolic objects).*
- E. Torlak, R. Bodik, 'A lightweight symbolic virtual machine for solver-aided host languages', PLDI 2014, pp. 530-541, doi:10.1145/2594291.2594340. *Full text inspected.*
- T. Avgerinos, A. Rebert, S. K. Cha, D. Brumley, 'Enhancing symbolic execution with veritesting', ICSE 2014, pp. 1083-1094, doi:10.1145/2568225.2568293. *Bibliographic record and abstract checked only; full text not inspected.*
- S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan, 'Functional big-step semantics', ESOP 2016, LNCS 9632, pp. 589-615, doi:10.1007/978-3-662-49498-1_23. *Full text inspected (Section 3.4, clock monotonicity).*
- D. Kroening, P. Schrammel, M. Tautschnig, 'CBMC: The C Bounded Model Checker', arXiv:2302.02384v1, 2023. *Checked against the arXiv version (v1, the only version) only (no archival venue record used).*
- E. Clarke, D. Kroening, F. Lerda, 'A tool for checking ANSI-C programs', TACAS 2004, LNCS 2988, pp. 168-176, doi:10.1007/978-3-540-24730-2_15. *Bibliographic record checked only; the publisher full text was not inspected.*
- Kani Rust Verifier documentation, 'Loops, unwinding, and bounds', repository model-checking/kani, path docs/src/tutorial-loop-unwinding.md, commit 21f3a2884e65c4c29465515a0117123cb8392814 (committed 2025-12-10). *Raw file at that commit inspected: the `#[kani::unwind(1)]` example reports "Failed Checks: unwinding assertion loop 0" and "1 of 67 failed (66 undetermined)".*
- C. Cadar, D. Dunbar, D. Engler, 'KLEE: Unassisted and automatic generation of high-coverage tests for complex systems programs', OSDI 2008, pp. 209-224, https://www.usenix.org/legacy/events/osdi08/tech/full_papers/cadar/cadar.pdf (SHA-256 of the PDF as retrieved on 2026-11-20: `59594fde5ff5b6c654410fb37d7ed3f8132d41f16dd15421dd58d38bcd90d621`). *Full text inspected (Section 3.3, "Implied Value Concretization").*

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. Nothing else is downloaded: the Lean project has no dependencies.

**Full check (primary).** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory and never modifies the package. It (1) runs `lake build`; (2) rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration; (3) writes and runs a small Lean audit program that computes, with `Lean.collectAxioms`, the axioms of every declaration in the `ToySymEx` library and fails on anything beyond `propext`, `Classical.choice`, `Quot.sound`; and (4) for every Lean name referenced by `results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s) recomputes `statement_sha256` = SHA-256 of `toString (repr type)` and `closure_sha256` = SHA-256 of the newline-joined sorted closure lines described under **Evidence**, and compares both (and the closure size) with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff all checks pass. Hashes are toolchain-specific: run it with the pinned toolchain.

**Narrow manual checks.** Build and print the axioms of the main theorems directly:

```sh
cd lean
lake build
cat > /tmp/ToySymExAxioms.lean <<'EOF'
import ToySymEx
#print axioms Toy.SymEx.eval_subst
#print axioms Toy.SymEx.symExec_leaf_sound
#print axioms Toy.SymEx.symExec_exhaustive
#print axioms Toy.SymEx.symExec_pairwise_disjoint
#print axioms Toy.SymEx.exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve
#print axioms Toy.SymEx.exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax
#print axioms Toy.SymEx.provesLax_iff_forall_exec_okWithOrOutOfFuel
#print axioms Toy.SymEx.leavesProve_of_leavesProve_dropPcs
#print axioms Toy.SymEx.dropPcs_false_alarm
#print axioms Toy.SymEx.guardedMerge_sound
#print axioms Toy.SymEx.mergeLeaf_preserves_leavesSound
#print axioms Toy.SymEx.mergeLeaf_leavesExhaustive_iff
#print axioms Toy.SymEx.unguardedMerge_spurious_success
#print axioms Toy.SymEx.guardedMerge_preserves_covers_of_agree_on_overlap
#print axioms Toy.SymEx.exec_fuel_mono
#print axioms Toy.SymEx.provesStrict_mono
#print axioms Toy.SymEx.exec_okWith_of_provesStrict_of_le
#print axioms Toy.SymEx.provesLax_loopThenAssertFalse_but_panics
#print axioms Toy.SymEx.provesLax_selfLoop_every_fuel_but_never_returns
#print axioms Toy.SymEx.acyclic_exec_ne_outOfFuel_of_fuelBound_le
#print axioms Toy.SymEx.straightLine_fuelBound_le_of_exec_ok
#print axioms Toy.SymEx.straightLine_exec_ok_iff_fuelBound_minimal
#print axioms Toy.SymEx.simpSoundUnder_iff_preserves_guardedSound
#print axioms Toy.SymEx.pathSimp_after_merge_breaks_soundness
#print axioms Toy.SymEx.provesStrict_iff_forall_exec_okWith
#print axioms Toy.SymEx.acyclic_provesStrict_fuelBound_iff_forall_exists_fuel
#print axioms Toy.SymEx.acyclic_provesLax_iff_provesStrict_of_fuelBound_le
EOF
lake env lean /tmp/ToySymExAxioms.lean
```

Each line of output must list at most `propext`, `Classical.choice`, `Quot.sound`; the expected sets are the ones in the **Evidence** table. To re-read a statement, `#check @Toy.SymEx.<name>` in the same file prints it; compare with the quotation under **Findings**.

**What a passing run establishes.** That the quoted statements, with the quoted definitions, are kernel-checked under the pinned toolchain with standard axioms only. It does not re-establish any `derived (modeling bridge)` claim, and it does not check the prior-art records.
