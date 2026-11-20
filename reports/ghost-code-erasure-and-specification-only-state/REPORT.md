# Ghost code erasure and specification-only state: a kernel-checked toy model in Lean 4

## Summary

This package is a Lean 4 mechanization, in a small deterministic while-language with real
and ghost (specification-only) variables, ghost blocks, run-time assertions, and loops, of when
deleting ghost code ("erasure") preserves a program's real-observable behaviour, when Hoare
triples about real variables survive erasure, and how erasability relates to ghost-to-real
noninterference. Throughout, `erase P` deletes ghost blocks and assignments to ghost
variables, the erased program starts from any store `τ` with the same real part as the
original's initial store `σ` (its ghost part is arbitrary), and the four restrictions are:
**R1** `GhostWritesGhost P` (ghost blocks assign only ghost variables), **R2**
`RealReadsReal P` (real statements read no ghost variable, through data or control),
**R3a** `GhostNoDivergeFrom P σ` (no ghost block started on the run of `P` from `σ` diverges;
it may fail), and **R3b** `GhostNoFailFrom P σ` (no ghost block started on that run fails; it
may diverge). All 18 results are kernel-checked with no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`; every hypothesis of every result is tight (a fully proved
counterexample drops it and refutes the conclusion).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers such as **1.A** are labels local to this report):

- **1.A** Under R1 and R2 alone, if the original terminates normally from `σ`, then the erased
  program from `τ` terminates normally with the same final real store; if the original fails or
  diverges, nothing is promised (refinement with failure and divergence as bottom).
- **1.B** Under R1, R2 and R3a, unless the original fails from `σ`, every real behaviour of the
  erased program from `τ` is one of the original's (refinement with only failure as bottom); in
  this deterministic language, divergence of the original is therefore preserved.
- **1.C** Under R1, R2 and R3b, unless the original diverges from `σ`, every real behaviour of the
  erased program from `τ` is one of the original's (refinement with only divergence as bottom);
  failure of the original is therefore preserved.
- **1.D** Under R1, R2, R3a and R3b along the run from `σ`, the original from `σ` and the erased
  program from `τ` have exactly the same real behaviours (same final real store, or both fail,
  or both diverge); with R3a and R3b from every initial state this gives `ErasureExact P`.
- **2.1** A ghost write to a real variable (`ghost { x := 1 }`, which satisfies R2, R3a, R3b)
  breaks even the weakest refinement of 1.A.
- **2.2** A real statement that reads a ghost variable, through control
  (`ghost { g := 1 }; if g then x := 1 else skip`) or data (`ghost { g := 1 }; x := g`), breaks
  the refinement of 1.A and exactness even when R1, R3a, R3b hold.
- **2.3** A diverging ghost block (`ghost { while 1 do skip }`, which satisfies R1, R2, R3b) makes
  the erased program terminate where the original diverges: behaviour inclusion, refinement up to
  failure, and exactness fail; refinement up to divergence still holds.
- **2.4** A failing ghost assertion (`ghost { assert 0 }`, which satisfies R1, R2, R3a) makes the
  original fail where the erased program terminates: refinement up to divergence and exactness
  fail; refinement up to failure still holds.
- **3.A** A partial-correctness triple *with safety* about real variables that holds for the
  original transfers to the erased program under R1, R2 and, for each real precondition state,
  R3a from at least one initial store with that real part; R3b is not needed because the triple's
  no-failure clause implies it on precondition states. A corollary requires R3a from every initial
  store satisfying the precondition.
- **3.B** A total-correctness triple about real variables transfers to the erased program under R1
  and R2 alone, because a valid total triple forces every ghost block it reaches to terminate
  normally.
- **3.D** A *weak* partial-correctness triple (failure and divergence both vacuous) transfers under
  R1, R2 and, for each real precondition state, R3a and R3b at one common initial store; the two
  conditions taken at different stores do not suffice.
- **4.A** Exact erasability is equivalent to termination- and failure-sensitive ghost-to-real
  noninterference of the program together with agreement of the program and its erasure when both
  start from the same full store.
- **4.B** Ghost-to-real noninterference does not imply exact erasability, not even together with R1
  and R2 (`ghost { x := 1 }`; `ghost { while x do skip }`).
- **4.C** Agreement of a program with its erasure from the same full store does not imply exact
  erasability (`x := g`).
- **4.D** R1, R2, and R3a and R3b on runs from every initial state imply ghost-to-real
  noninterference that is sensitive to termination and failure.
- **4.E** R1 and R2 alone imply only abort-insensitive noninterference: two normally terminating
  runs from states with the same real part end with the same real part; failure and divergence are
  not compared.
- **4.F** R1 and R2 do not give termination-sensitive noninterference: `ghost { while g do skip }`
  terminates or diverges depending on the initial ghost value (a termination channel).
- **4.G** Under R2, exact erasability is equivalent to agreement of the program with its erasure
  from the same full store.

What these results do **not** show is listed first under **Boundaries**: in particular, the model
is a toy language (no heap, procedures, nondeterminism, concurrency, exceptions, or ghost types),
the restrictions are sufficient conditions and none is claimed necessary for any individual
program, and every statement about Dafny, Why3 or other real verifiers is a modeling bridge, not a
kernel-checked fact.

## Applicability

**Model fidelity.** This is a toy model (namespace `Toy.Ghost`, Lean library `ToyGhost`), not a
mirror of any production definition. It is meant to capture the ghost-code discipline of
deductive verifiers such as Dafny and Why3: ghost variables that exist only for verification,
ghost blocks that update them or state lemmas (a lemma call is modelled as a ghost assertion, an
inductive ghost proof as a ghost loop), run-time checks that survive compilation (a real
`assert`, like Dafny's `expect`), and compilation that deletes all ghost code. The language is
deterministic and sequential; variables are integers (every type is inhabited); expression
evaluation is total; assertion failure is fatal and uncatchable; divergence is "out of fuel for
every fuel bound" of a fuel-indexed interpreter. Known gaps with respect to real verifiers: no
procedures or recursion, no heap or aliasing, no ghost fields, no ghost functions inside
specifications, no `assume` statements or unverified axioms, no empty ghost types or witness
checks, no existential choice, no catchable exceptions or early exits from a ghost block, no
nondeterministic choice, and no concurrency. The erased program is modelled as a program over the
same full stores whose ghost part is arbitrary, rather than as a program over real-only stores.
Under R2 the two readings agree: the erased program then mentions no ghost variable
(`noGhostVars_erase_of_realReadsReal`) and its real behaviour depends only on the real part of its
initial store (`erase_rbehaves_congr_of_realReadsReal`). Results that depend on the encoding say so
(4.C, and the non-claims of 2.2 and 4.G).

**Specifications.** Hoare triples (`SafePartialTriple`, `WeakPartialTriple`, `TotalTriple`) are
semantic validity statements over pre- and postconditions on the real part of the store; they are
not derivability in a Hoare logic or verification-condition generator, and ghost parameters or
ghost return values in specifications are not modelled.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (release commit
`5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib and no `Std` imports. The
Lake project in `lean/` has a single library target `ToyGhost` and no dependencies.

**Subjects and their relation.** The Lean toolchain release is the checker of every theorem. The
papers, the Security Foundations textbook, the Dafny reference manual and the Why3 documentation
listed in `REPORT.json` are prior art and the systems the toy model is meant to reflect; they were
consulted only at the sections and records named under **Evidence**, and no verifier was run.

Basis: derived (modeling bridge). Any reading of these results as facts about Dafny, Why3 or
another verifier assumes that its ghost discipline restricted to this sublanguage amounts to
R1–R3 and that its compiler erases exactly ghost blocks and ghost assignments; neither assumption
is checked here (see the cited manual sections under **Evidence**).

## Findings

### Model

All definitions below are quoted verbatim from the Lean sources in `lean/ToyGhost/` (namespace
`Toy.Ghost`), including their documentation comments. Every result's statement hash and
definition-closure hash under **Evidence** covers exactly these definitions as they occur in the
statement's closure.

#### Syntax and stores (`ToyGhost/Language.lean`)

```lean
/-- Program variables. `real i` is an ordinary executable variable; `ghost i` is a
specification-only variable that erasure removes. -/
inductive Var where
  | real (i : Nat)
  | ghost (i : Nat)
  deriving DecidableEq, Repr

/-- A store gives every variable, real or ghost, an integer value. -/
abbrev Store := Var → Int

/-- A real store: the values of the real variables only. This is what an observer
of the erased program can see. -/
abbrev RStore := Nat → Int

/-- The real projection of a store: forget all ghost variables. -/
def realPart (σ : Store) : RStore := fun i => σ (.real i)

/-- Pointwise update of one variable. -/
def Store.update (σ : Store) (x : Var) (v : Int) : Store :=
  fun y => if y = x then v else σ y

/-- Integer expressions. Comparisons return `1` for true and `0` for false; a
condition is true when it evaluates to a nonzero value. -/
inductive Expr where
  | lit (n : Int)
  | var (x : Var)
  | add (a b : Expr)
  | sub (a b : Expr)
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Expression evaluation in a store (total; no run-time errors in expressions). -/
def Expr.eval : Expr → Store → Int
  | .lit n, _ => n
  | .var x, σ => σ x
  | .add a b, σ => a.eval σ + b.eval σ
  | .sub a b, σ => a.eval σ - b.eval σ
  | .lt a b, σ => if a.eval σ < b.eval σ then 1 else 0
  | .eq a b, σ => if a.eval σ = b.eval σ then 1 else 0

/-- `e.ReadsOnlyReal`: the expression mentions no ghost variable (syntactic). -/
def Expr.ReadsOnlyReal : Expr → Prop
  | .lit _ => True
  | .var (.real _) => True
  | .var (.ghost _) => False
  | .add a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .sub a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .lt a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .eq a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal

/-- Statements.

* `assert e` fails when `e` evaluates to `0`. Outside a ghost block it models a
  run-time check that survives erasure; inside a ghost block it models a
  specification assertion (for example a lemma call) that erasure deletes.
* `loop c b` is `while c do b`.
* `ghost s` marks `s` (with everything nested in it) as ghost code. In the original
  program a ghost block simply executes `s`. -/
inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | assert (e : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  | loop (c : Expr) (body : Stmt)
  | ghost (s : Stmt)
  deriving Repr
```

A statement is **ghost** if it is a `ghost` block (with everything nested in it) or an
assignment to a ghost variable; every other statement is **real**. This follows Dafny's ghost
inference, in which an assignment is ghost when all variables it updates are ghost, and it lets
erasure delete ghost variables entirely.

#### Semantics (`ToyGhost/Semantics.lean`)

```lean
/-- Result of a finished execution. -/
inductive Outcome where
  | ok (σ : Store)
  | fail

/-- Sequential composition of a partial result with a continuation. -/
def Outcome.bind : Option Outcome → (Store → Option Outcome) → Option Outcome
  | some (.ok σ), k => k σ
  | some .fail, _ => some .fail
  | none, _ => none

/-- Fuel-indexed big-step interpreter. Every construct consumes one unit of fuel. -/
def run : Nat → Stmt → Store → Option Outcome
  | 0, _, _ => none
  | _ + 1, .skip, σ => some (.ok σ)
  | _ + 1, .assign x e, σ => some (.ok (σ.update x (e.eval σ)))
  | _ + 1, .assert e, σ => if e.eval σ = 0 then some .fail else some (.ok σ)
  | n + 1, .seq s t, σ => Outcome.bind (run n s σ) (run n t)
  | n + 1, .ite c s t, σ => if c.eval σ = 0 then run n t σ else run n s σ
  | n + 1, .loop c b, σ =>
      if c.eval σ = 0 then some (.ok σ) else Outcome.bind (run n b σ) (run n (.loop c b))
  | n + 1, .ghost s, σ => run n s σ

/-- Complete behaviours of a deterministic program from one initial state. -/
inductive Behaviour where
  | term (σ : Store)
  | fail
  | diverge

/-- Real-observable behaviours: final real store, failure, or divergence. -/
inductive RBehaviour where
  | term (r : RStore)
  | fail
  | diverge

/-- `Behaves s σ b`: running `s` from `σ` has behaviour `b`. -/
def Behaves (s : Stmt) (σ : Store) : Behaviour → Prop
  | .term σ' => ∃ n, run n s σ = some (.ok σ')
  | .fail => ∃ n, run n s σ = some .fail
  | .diverge => ∀ n, run n s σ = none

/-- `s` fails (an assertion is violated) when run from `σ`. -/
def Fails (s : Stmt) (σ : Store) : Prop := Behaves s σ .fail

/-- `s` diverges (runs out of fuel for every fuel bound) when run from `σ`. -/
def Diverges (s : Stmt) (σ : Store) : Prop := Behaves s σ .diverge

/-- Forget the ghost part of a behaviour. -/
def Behaviour.real : Behaviour → RBehaviour
  | .term σ => .term (realPart σ)
  | .fail => .fail
  | .diverge => .diverge

/-- `RBehaves s σ rb`: running `s` from `σ` has real-observable behaviour `rb`. -/
def RBehaves (s : Stmt) (σ : Store) (rb : RBehaviour) : Prop :=
  ∃ b, Behaves s σ b ∧ b.real = rb
```

Proved basic facts: `run_mono` (fuel monotonicity), `Behaves.unique` (determinism: at most one
behaviour from each state), `Behaves.exists` (totality: at least one behaviour; proved
classically), `RBehaves.iff_of_behaves` (`Behaves s σ b0 → (RBehaves s σ rb ↔ rb = b0.real)`:
once one behaviour is known, the real-observable behaviours are exactly its projection). Running out of fuel for one bound is not divergence
(`behaves_example_fuel_zero`).

#### Erasure and the restrictions (`ToyGhost/Ghost.lean`)

```lean
/-- Erasure: delete ghost blocks and assignments to ghost variables. Real
assignments, assertions, sequencing, and real control flow are kept with their
expressions unchanged.

Encoding choice: `erase P` is again a `Stmt` and is run on a full `Store`. If `P`
violates R2, `erase P` still reads ghost variables (for example `erase (x := g)` is
`x := g`); a compiler targeting real stores only would reject such a program
instead. Under R2 the erased program mentions no ghost variable
(`noGhostVars_erase_of_realReadsReal`) and its real behaviour depends only on the
real part of the initial store (`erase_rbehaves_congr_of_realReadsReal`), so it can
be read as a program over real stores. -/
def erase : Stmt → Stmt
  | .skip => .skip
  | .assign (.real i) e => .assign (.real i) e
  | .assign (.ghost _) _ => .skip
  | .assert e => .assert e
  | .seq s t => .seq (erase s) (erase t)
  | .ite c s t => .ite c (erase s) (erase t)
  | .loop c b => .loop c (erase b)
  | .ghost _ => .skip

/-- `WritesOnlyGhost s`: every assignment anywhere in `s` (including inside nested
ghost blocks) targets a ghost variable. -/
def WritesOnlyGhost : Stmt → Prop
  | .skip => True
  | .assign (.real _) _ => False
  | .assign (.ghost _) _ => True
  | .assert _ => True
  | .seq s t => WritesOnlyGhost s ∧ WritesOnlyGhost t
  | .ite _ s t => WritesOnlyGhost s ∧ WritesOnlyGhost t
  | .loop _ b => WritesOnlyGhost b
  | .ghost s => WritesOnlyGhost s

/-- Restriction R1, `GhostWritesGhost P`: every ghost block of `P` writes only ghost
variables. (Assignments to ghost variables outside ghost blocks are ghost
statements that write a ghost variable by construction.) -/
def GhostWritesGhost : Stmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .assert _ => True
  | .seq s t => GhostWritesGhost s ∧ GhostWritesGhost t
  | .ite _ s t => GhostWritesGhost s ∧ GhostWritesGhost t
  | .loop _ b => GhostWritesGhost b
  | .ghost s => WritesOnlyGhost s

/-- Restriction R2, `RealReadsReal P`: no real statement of `P` reads a ghost
variable, through data or through control. Ghost statements (ghost blocks and
assignments to ghost variables) may read anything. -/
def RealReadsReal : Stmt → Prop
  | .skip => True
  | .assign (.real _) e => e.ReadsOnlyReal
  | .assign (.ghost _) _ => True
  | .assert e => e.ReadsOnlyReal
  | .seq s t => RealReadsReal s ∧ RealReadsReal t
  | .ite c s t => c.ReadsOnlyReal ∧ RealReadsReal s ∧ RealReadsReal t
  | .loop c b => c.ReadsOnlyReal ∧ RealReadsReal b
  | .ghost _ => True

/-- `GhostReach Q n P σ`: every *outermost* ghost block that the run of `P` from `σ`
starts within fuel `n` satisfies `Q` at the state in which it starts. Ghost blocks
nested inside a ghost block are covered only through `Q` applied to the enclosing
block. Assignments and assertions impose nothing here because expression
evaluation is total in this language (it cannot fail or diverge). -/
def GhostReach (Q : Stmt → Store → Prop) : Nat → Stmt → Store → Prop
  | 0, _, _ => True
  | _ + 1, .skip, _ => True
  | _ + 1, .assign _ _, _ => True
  | _ + 1, .assert _, _ => True
  | n + 1, .seq s t, σ =>
      GhostReach Q n s σ ∧ ∀ σ', run n s σ = some (.ok σ') → GhostReach Q n t σ'
  | n + 1, .ite c s t, σ => if c.eval σ = 0 then GhostReach Q n t σ else GhostReach Q n s σ
  | n + 1, .loop c b, σ =>
      if c.eval σ = 0 then True else
        GhostReach Q n b σ ∧ ∀ σ', run n b σ = some (.ok σ') → GhostReach Q n (.loop c b) σ'
  | _ + 1, .ghost s, σ => Q s σ

/-- Restriction R3a (per run), `GhostNoDivergeFrom P σ`: every ghost block started
during the run of `P` from `σ` does not diverge from the state in which it starts;
it terminates normally or fails. (A failing ghost block such as `ghost { assert 0 }`
satisfies this condition; failure is excluded separately by `GhostNoFailFrom`.) -/
def GhostNoDivergeFrom (P : Stmt) (σ : Store) : Prop :=
  ∀ n, GhostReach (fun g τ => ¬ Diverges g τ) n P σ

/-- Restriction R3b (per run), `GhostNoFailFrom P σ`: every ghost block started
during the run of `P` from `σ` does not fail from the state in which it starts;
it terminates normally or diverges. -/
def GhostNoFailFrom (P : Stmt) (σ : Store) : Prop :=
  ∀ n, GhostReach (fun g τ => ¬ Fails g τ) n P σ

/-- `GhostBlocksSatisfy Q P`: every *outermost* ghost block of `P` satisfies `Q` from
*every* state (a static, context-free condition). Ghost blocks nested inside a ghost
block are not checked individually; they are covered by `Q` on the enclosing block. -/
def GhostBlocksSatisfy (Q : Stmt → Store → Prop) : Stmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .assert _ => True
  | .seq s t => GhostBlocksSatisfy Q s ∧ GhostBlocksSatisfy Q t
  | .ite _ s t => GhostBlocksSatisfy Q s ∧ GhostBlocksSatisfy Q t
  | .loop _ b => GhostBlocksSatisfy Q b
  | .ghost s => ∀ σ, Q s σ

/-- Static variant of R3a: no outermost ghost block diverges from any state. -/
def GhostBlocksNoDiverge (P : Stmt) : Prop := GhostBlocksSatisfy (fun g τ => ¬ Diverges g τ) P

/-- Static variant of R3b: no outermost ghost block fails from any state. -/
def GhostBlocksNoFail (P : Stmt) : Prop := GhostBlocksSatisfy (fun g τ => ¬ Fails g τ) P

/-- `NoGhostVars s`: `s` mentions no ghost variable at all (read or written),
including inside ghost blocks. A ghost block that mentions only real variables,
such as `ghost { skip }`, is admitted; whether `s` contains ghost blocks is a
separate question (`NoGhostCode`). -/
def NoGhostVars : Stmt → Prop
  | .skip => True
  | .assign (.real _) e => e.ReadsOnlyReal
  | .assign (.ghost _) _ => False
  | .assert e => e.ReadsOnlyReal
  | .seq s t => NoGhostVars s ∧ NoGhostVars t
  | .ite c s t => c.ReadsOnlyReal ∧ NoGhostVars s ∧ NoGhostVars t
  | .loop c b => c.ReadsOnlyReal ∧ NoGhostVars b
  | .ghost s => NoGhostVars s

/-- `NoGhostCode s`: `s` contains no ghost block and no assignment to a ghost
variable. -/
def NoGhostCode : Stmt → Prop
  | .skip => True
  | .assign (.real _) _ => True
  | .assign (.ghost _) _ => False
  | .assert _ => True
  | .seq s t => NoGhostCode s ∧ NoGhostCode t
  | .ite _ s t => NoGhostCode s ∧ NoGhostCode t
  | .loop _ b => NoGhostCode b
  | .ghost _ => False
```

*Intent.* R1 (`GhostWritesGhost`) says ghost code does not write real state. R2
(`RealReadsReal`) says real code does not read ghost state, neither through data (right-hand
sides, assertion expressions) nor through control (the condition of a real `if` or `while`). R3a
and R3b (`GhostNoDivergeFrom`, `GhostNoFailFrom`) constrain only the ghost blocks that the run of
`P` from `σ` actually starts, in the state where each starts: this is the condition a verifier
establishes for ghost code in context. The static variants `GhostBlocksNoDiverge` and
`GhostBlocksNoFail` demand the same from every state; they imply the per-run conditions
(`ghostNoDivergeFrom_of_ghostBlocksNoDiverge`, `ghostNoFailFrom_of_ghostBlocksNoFail`) and are
strictly stronger (`demo_not_ghostBlocksNoFail`, `ghostBlocksNoDiverge_example_neg_guarded`).
R3a admits failing ghost blocks (`ghostNoDivergeFrom_example_pos_failing`), so R3a and R3b are
independent. Structural facts (proved): `Expr.eval_congr_of_readsOnlyReal`
(`e.ReadsOnlyReal → realPart σ = realPart τ → e.eval σ = e.eval τ`: an expression that reads no
ghost variable evaluates equally in stores with the same real part),
`noGhostVars_erase_of_realReadsReal` (under R2 the erased program mentions no ghost variable),
`rbehaves_congr_of_noGhostVars` and `erase_rbehaves_congr_of_realReadsReal` (under R2 the real
behaviour of `erase P` depends only on the real part of its initial store), `noGhostCode_erase`
(`NoGhostCode (erase P)`, where `NoGhostCode s` says that `s` contains no ghost block and no
assignment to a ghost variable: erasure removes all ghost code), `erase_eq_self_of_noGhostCode`
(`NoGhostCode P → erase P = P`: erasure leaves a program without ghost code unchanged), and
`erase_erase` (`erase (erase P) = erase P`: erasure is idempotent).

#### Behavioural relations and specifications (`ToyGhost/Specs.lean`)

```lean
/-- Bottom set "abort": failure and divergence (the refinement-calculus `abort`). -/
def abortBot (b : RBehaviour) : Prop := b = .fail ∨ b = .diverge

/-- Bottom set containing only failure. -/
def failBot (b : RBehaviour) : Prop := b = .fail

/-- Bottom set containing only divergence. -/
def divBot (b : RBehaviour) : Prop := b = .diverge

/-- `RefinesUpTo Bot A σ C τ` ("`C` from `τ` refines `A` from `σ` up to `Bot`"):
either `A` from `σ` has a behaviour in `Bot` (which any behaviour refines), or
every real behaviour of `C` from `τ` is a real behaviour of `A` from `σ`.

`A` is the abstract (original) program, `C` the concrete (erased) one. With
`Bot = abortBot` this is the total-correctness refinement order of the refinement
calculus (Back and von Wright, *Refinement Calculus*, 1998), in which failure and
divergence are both bottom. In this deterministic language the `∀ b` clause says
that the unique behaviour of `C` equals that of `A`. -/
def RefinesUpTo (Bot : RBehaviour → Prop) (A : Stmt) (σ : Store) (C : Stmt) (τ : Store) : Prop :=
  (∃ a, Bot a ∧ RBehaves A σ a) ∨ ∀ b, RBehaves C τ b → RBehaves A σ b

/-- Partial correctness *with safety* (semantic validity, not derivability in a
proof system): from every state whose real part satisfies `Pre`, `s` does not fail
(no assertion, real or ghost, is violated), and if it terminates normally its final
real part satisfies `Post`. Divergence satisfies every triple; failure satisfies
none. `Pre` and `Post` are predicates on real stores, so the triple is "about real
variables" and the initial ghost values are universally quantified. Compare
`WeakPartialTriple`, in which failure is also vacuous. -/
def SafePartialTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ¬ Fails s σ ∧ ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')

/-- Weak (classical) partial correctness: from every state whose real part satisfies
`Pre`, if `s` terminates normally its final real part satisfies `Post`. Both
divergence and failure satisfy every weak triple. -/
def WeakPartialTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')

/-- Total correctness (semantic validity): from every state whose real part
satisfies `Pre`, `s` terminates normally in a state whose real part satisfies
`Post`. -/
def TotalTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ∃ σ', Behaves s σ (.term σ') ∧ Post (realPart σ')

/-- Termination-sensitive noninterference from ghost to real: the real-observable
behaviour of `P` (final real store, failure, divergence) does not depend on the
initial values of ghost variables. -/
def GhostToRealNI (P : Stmt) : Prop :=
  ∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves P τ b

/-- Abort-insensitive noninterference from ghost to real (the analogue of
termination-insensitive noninterference in a language that can also fail):
whenever two runs from states with equal real parts both terminate normally, their
final real parts agree. Neither failure nor divergence is compared, so both the
termination channel and the failure channel are ignored. -/
def GhostToRealNI_AbortInsensitive (P : Stmt) : Prop :=
  ∀ σ τ σ' τ', realPart σ = realPart τ → Behaves P σ (.term σ') → Behaves P τ (.term τ') →
    realPart σ' = realPart τ'

/-- `ErasureExact P`: for all initial states `σ`, `τ` with the same real part, the
real-observable behaviours of `P` from `σ` and of `erase P` from `τ` coincide. The
erased program starts from an *arbitrary* ghost part, modelling that ghost
variables no longer exist after erasure. -/
def ErasureExact (P : Stmt) : Prop :=
  ∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b

/-- `ErasureAgrees P`: `P` and `erase P` have the same real-observable behaviour
when started from the *same* full store. -/
def ErasureAgrees (P : Stmt) : Prop :=
  ∀ σ b, RBehaves P σ b ↔ RBehaves (erase P) σ b
```

*Direction convention.* In every refinement statement the original program `P` is the abstract
side `A`, started from `σ`, and `erase P` is the concrete side `C`, started from any `τ` with the
same real part. The proved lemma `refinesUpTo_abortBot_iff` unfolds the weakest form in this
deterministic language:

```lean
theorem refinesUpTo_abortBot_iff {A C : Stmt} {σ τ : Store} :
    RefinesUpTo abortBot A σ C τ ↔
      ∀ σ', Behaves A σ (.term σ') → ∃ τ', Behaves C τ (.term τ') ∧ realPart τ' = realPart σ'
```

#### Concrete programs

`x = real 0`, `y = real 1`, `g = ghost 0`; `σ0 = fun _ => 0` (the all-zero store);
`σ0g = σ0.update g 1` (same real part as `σ0`, ghost `g = 1`). Conditions are true when nonzero.
Programs are defined in `ToyGhost/Programs.lean` except `realReadsGhost`, `ceGhostCopiesGhost`,
`ghostAssertG` (`Noninterference.lean`), `guardedGhostSpin`, `loopDemo` (`DefExamples.lean`), and
`ghostAssertX0`, `ghostFailOrSpin` (`HoareExamples.lean`).

| name | program | role |
| --- | --- | --- |
| `spin` | `while 1 do skip` | diverges |
| `ceGhostWritesReal` | `ghost { x := 1 }` | violates R1 only |
| `ceImplicitFlow` | `ghost { g := 1 }; if g then x := 1 else skip` | violates R2 only (control) |
| `ceDataFlow` | `ghost { g := 1 }; x := g` | violates R2 only (data) |
| `ceGhostDiverges` | `ghost { while 1 do skip }` | violates R3a only |
| `ceGhostFails` | `ghost { assert 0 }` | violates R3b only |
| `pcGhostWritesGhost` | `ghost { g := 1 }` | control for R1 |
| `pcRealBranch` | `ghost { g := 1 }; if x then x := 1 else skip` | control for R2 |
| `pcRealDataFlow` | `ghost { g := 1 }; x := y` | control for the data-flow variant of 2.2 |
| `pcGhostTerminatingLoop` | `ghost { while 0 do skip }` | control for R3a |
| `pcGhostPassingAssert` | `ghost { assert 1 }` | control for R3b |
| `ghostSpinOnG` | `ghost { while g do skip }` | termination channel |
| `ghostSpinOnX` | `ghost { while x do skip }` | noninterfering, R1 and R2 hold, not exactly erasable |
| `ghostSpinThenSetX` | `ghost { while g do skip }; x := 1` | existential versus all-states R3a in 3.A |
| `realReadsGhost` | `x := g` | reads a ghost variable, contains no ghost statement |
| `ceGhostCopiesGhost` | `ghost { x := g }` | R1 needed for noninterference |
| `ghostAssertG` | `ghost { assert g }` | failure channel |
| `ghostAssertX0` | `ghost { assert x = 0 }` | R3b dispensable for 3.A |
| `guardedGhostSpin` | `x := 0; ghost { while x do skip }` | per-run versus static R3a |
| `ghostThenSpin` | `ghost { g := 1 }; while 1 do skip` | diverging witness for 1.B |
| `ghostThenRealFail` | `ghost { g := 1 }; assert 0` | real-failing witness for 1.C |
| `ghostFailOrSpin` | `ghost { if g then assert 0 else while 1 do skip }` | R3a and R3b at different stores do not suffice for 3.D |
| `demo` | `x := 3; ghost { g := x + 1 }; y := x + x; ghost { assert g = x + 1 }` | main non-vacuity witness |
| `loopDemo` | `x := 0; while x < 3 do { x := x + 1; ghost { assert 0 < x } }` | witness with a ghost assertion inside a real loop |

#### Definition examples (`ToyGhost/DefExamples.lean`, all proved)

Each core definition has proved intended positive and negative examples:

| definition | positive examples | negative examples |
| --- | --- | --- |
| `realPart` | `realPart_example_ghost_update_invisible` | `realPart_example_real_update_visible` |
| `Expr.ReadsOnlyReal` | `readsOnlyReal_example_pos` (`x + 1`) | `readsOnlyReal_example_neg` (`g`), `readsOnlyReal_example_neg_nested` (`x < g`) |
| `Behaves`, `Fails`, `Diverges` | `behaves_example_term`, `behaves_example_fail`, `behaves_example_diverge` | `behaves_example_spin_never_terminates`, `behaves_example_skip_never_fails`, `behaves_example_fuel_zero` (fuel exhaustion is not divergence) |
| `RBehaves` | `rbehaves_example_ghost_write_invisible` | `rbehaves_example_real_write_visible` |
| `erase` | `erase_example_ghost_block`, `erase_example_ghost_assign`, `erase_example_demo` | `erase_example_keeps_real_assign`, `erase_example_keeps_real_assert` |
| `GhostWritesGhost` (R1) | `ghostWritesGhost_example_pos`, `ghostWritesGhost_example_pos_real_write_outside_ghost` | `ghostWritesGhost_example_neg`, `ghostWritesGhost_example_neg_nested` |
| `RealReadsReal` (R2) | `realReadsReal_example_pos`, `realReadsReal_example_pos_ghost_assign` (ghost statements may read ghost variables) | `realReadsReal_example_neg_implicit_flow`, `realReadsReal_example_neg_data_flow`, `realReadsReal_example_neg_real_assert` |
| `GhostNoDivergeFrom` (R3a) | `ghostNoDivergeFrom_example_pos`, `ghostNoDivergeFrom_example_pos_guarded`, `ghostNoDivergeFrom_example_pos_failing` (a failing ghost block does not diverge) | `ghostNoDivergeFrom_example_neg` |
| `GhostNoFailFrom` (R3b) | `ghostNoFailFrom_example_pos` (`demo`: its ghost assertion holds on every run), `ghostNoFailFrom_example_pos_loop` (`loopDemo`, from every state) | `ghostNoFailFrom_example_neg` |
| `GhostBlocksNoDiverge`, `GhostBlocksNoFail` | `ghostBlocksNoDiverge_example_pos`, `ghostBlocksNoFail_example_pos` | `ghostBlocksNoDiverge_example_neg`, `ghostBlocksNoDiverge_example_neg_guarded`, `ghostBlocksNoFail_example_neg` (`demo`), `loopDemo_not_ghostBlocksNoFail` |
| `NoGhostVars`, `NoGhostCode` | `noGhostVars_example_pos`, `noGhostVars_example_pos_ghost_skip`, `noGhostCode_example_pos` (`erase demo`) | `noGhostVars_example_neg`, `noGhostVars_example_neg_real_reads_ghost`, `noGhostCode_example_neg` (`demo`), `noGhostCode_example_neg_ghost_skip` |
| bottom sets | `abortBot_example_pos`, `failBot_example_pos`, `divBot_example_pos` | `abortBot_example_neg`, `failBot_example_neg`, `divBot_example_neg` |
| `RefinesUpTo` | `refinesUpTo_refl`, `refinesUpTo_example_pos` | `refinesUpTo_example_neg`, `refinesUpTo_example_neg_direction` |
| `SafePartialTriple` | `safePartialTriple_example_pos`, `safePartialTriple_example_pos_vacuous` (divergence satisfies every triple) | `safePartialTriple_example_neg_safety` (failure violates every triple), `safePartialTriple_example_neg_post` |
| `WeakPartialTriple` | `weakPartialTriple_example_pos`, `weakPartialTriple_example_pos_vacuous_fail` (failure satisfies every weak triple) | `weakPartialTriple_example_neg_post` |
| `TotalTriple` | `totalTriple_example_pos` | `totalTriple_example_neg_divergence` |
| `GhostToRealNI` | `ghostToRealNI_example_pos` | `ghostToRealNI_example_neg`, `ghostToRealNI_example_neg_termination_channel` |
| `GhostToRealNI_AbortInsensitive` | `ghostToRealNI_abortInsensitive_example_pos` (`ghostSpinOnG`), `ghostToRealNI_abortInsensitive_example_pos_failure_channel` (`ghostAssertG`) | `ghostToRealNI_abortInsensitive_example_neg` (`x := g`) |
| `ErasureExact` | `erasureExact_example_pos` | `erasureExact_example_neg` |
| `ErasureAgrees` | `erasureAgrees_example_pos` (`x := g`) | `erasureAgrees_example_neg` |

### Results

Common notation: `P : Stmt`; R1 = `GhostWritesGhost P`; R2 = `RealReadsReal P`;
R3a = `GhostNoDivergeFrom P σ`; R3b = `GhostNoFailFrom P σ`; `hστ : realPart σ = realPart τ`.
Depth labels: `definitional` (unfolds definitions), `shallow` (a short argument from proved
lemmas or a concrete evaluation), `substantive` (a real induction or simulation argument). Where a
result is derived from another, its depth is relative to that result and a note gives the
cumulative depth in parentheses. Identifiers are not contiguous (there is no 3.C).

### Result 1: erasure soundness, graded by restriction

#### 1.A — R1 and R2 alone: erasure refines the original up to failure and divergence

- **Kind:** theorem. **Tier:** T0. Re-derivation: the Rocq-mechanized pub_slice_fwd_correct (Security Foundations, StaticIFC) is the same forward simulation between a program and its public slice; here the discipline is R1 + R2 instead of a flow typing, and assertion failure is added and folded into the bottom set.
- **Plain claim:** If ghost blocks write only ghost variables (R1) and real statements read no ghost variable (R2), then whenever the original program terminates normally from σ, the erased program started from any τ with the same real part terminates normally with the same final real store; if the original fails or diverges nothing is promised (the erased program refines the original with failure and divergence as bottom).
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) :
    RefinesUpTo abortBot P σ (erase P) τ
```

By `refinesUpTo_abortBot_iff` (quoted under *Model*), the conclusion is equivalent to

```lean
∀ σ', Behaves P σ (.term σ') →
  ∃ τ', Behaves (erase P) τ (.term τ') ∧ realPart τ' = realPart σ'
```

that is: if the original terminates normally from `σ`, the erased program terminates normally
from `τ` with the same final real store. Nothing is said when the original fails or diverges.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.erase_refinesUpTo_abortBot_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.erase_refinesUpTo_abortBot_needs_realReadsReal` |
| `hστ : realPart σ = realPart τ` | Both runs start from the same real state; the erased run's ghost part is arbitrary. | tight | `Toy.Ghost.erase_refinesUpTo_abortBot_needs_same_realPart` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** substantive
- **Non-vacuity witness:** demo = x := 3; ghost { g := x + 1 }; y := x + x; ghost { assert g = x + 1 }, from σ0, erased run from σ0g (different ghost part). Lean: `Toy.Ghost.demo_satisfies_erasure_hypotheses`.
- **Prior art:** [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [BvW98] Back-von Wright 1998 (full records under **Evidence**).
- **Design question:** What do the two flow restrictions alone (no ghost writes to real state, no ghost reads in real code) guarantee about erasure, and in which refinement direction?
- **Non-claims:** see **Boundaries**, result 1.A, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 1.B — Adding R3a: refinement up to failure only

- **Kind:** theorem. **Tier:** T1. Folklore made precise: that ghost code must not diverge and that its assertions must hold is stated by Filliâtre-Gondelman-Paskevich (paper proof by bisimulation for an ML-style language) and enforced by Dafny and Why3; the mechanized slice results in Security Foundations assume a static termination-ensuring typing and have no failure outcome. The graded form (failure and divergence separated as bottoms) with per-run conditions was not found mechanized in the sources checked.
- **Plain claim:** Under R1, R2, and R3a (no ghost block that the run of the original from σ starts diverges; ghost blocks may fail), either the original fails from σ, or every real behaviour of the erased program from any τ with the same real part (normal termination with its final real store, failure, divergence) is a real behaviour of the original from σ; because the language is deterministic and total, it follows that divergence of the original is preserved by erasure.
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) (hT : GhostNoDivergeFrom P σ) :
    RefinesUpTo failBot P σ (erase P) τ
```

With `failBot b := b = .fail`, the conclusion unfolds to

```lean
(∃ a, a = .fail ∧ RBehaves P σ a) ∨ ∀ b, RBehaves (erase P) τ b → RBehaves P σ b
```

and `hT` unfolds to `∀ n, GhostReach (fun g τ => ¬ Diverges g τ) n P σ`. So either the original
fails from `σ`, or every real behaviour of the erased program from `τ` (normal termination with a
given real store, failure, or divergence) is a real behaviour of the original from `σ`.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.erase_refinesUpTo_failBot_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.erase_refinesUpTo_failBot_needs_realReadsReal` |
| `hστ : realPart σ = realPart τ` | Both runs start from the same real state; the erased run's ghost part is arbitrary. | tight | `Toy.Ghost.erase_refinesUpTo_failBot_needs_same_realPart` |
| `hT : GhostNoDivergeFrom P σ` | R3a: no ghost block started on the run of P from σ diverges (it terminates normally or fails). | tight | `Toy.Ghost.erase_refinesUpTo_failBot_needs_ghostNoDivergeFrom` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** substantive
- **Non-vacuity witness:** demo (terminating) from σ0 with the erased run from σ0g; ghost { g := 1 }; while 1 do skip (diverging, so the divergence case is exercised) from σ0. Lean: `Toy.Ghost.demo_satisfies_erasure_hypotheses`, `Toy.Ghost.ghostThenSpin_satisfies_erasure_hypotheses`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [Dafny] Dafny Reference Manual v4.11.0; [Why3] Why3 1.9.0 documentation; [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026) (full records under **Evidence**).
- **Design question:** Is non-divergence of ghost code needed for erasure to preserve divergence? Yes; the hypothesis is tight.
- **Non-claims:** see **Boundaries**, result 1.B, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 1.C — Adding R3b: refinement up to divergence only

- **Kind:** theorem. **Tier:** T1. Folklore made precise: that ghost code must not diverge and that its assertions must hold is stated by Filliâtre-Gondelman-Paskevich (paper proof by bisimulation for an ML-style language) and enforced by Dafny and Why3; the mechanized slice results in Security Foundations assume a static termination-ensuring typing and have no failure outcome. The graded form (failure and divergence separated as bottoms) with per-run conditions was not found mechanized in the sources checked.
- **Plain claim:** Under R1, R2, and R3b (no ghost block that the run of the original from σ starts fails; ghost blocks may diverge), either the original diverges from σ, or every real behaviour of the erased program from any τ with the same real part is a real behaviour of the original from σ; because the language is deterministic and total, it follows that failure of the original is preserved by erasure.
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) (hF : GhostNoFailFrom P σ) :
    RefinesUpTo divBot P σ (erase P) τ
```

With `divBot b := b = .diverge`, the conclusion unfolds to

```lean
(∃ a, a = .diverge ∧ RBehaves P σ a) ∨ ∀ b, RBehaves (erase P) τ b → RBehaves P σ b
```

and `hF` unfolds to `∀ n, GhostReach (fun g τ => ¬ Fails g τ) n P σ`. So either the original
diverges from `σ`, or every real behaviour of the erased program from `τ` is a real behaviour of
the original from `σ`.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.erase_refinesUpTo_divBot_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.erase_refinesUpTo_divBot_needs_realReadsReal` |
| `hστ : realPart σ = realPart τ` | Both runs start from the same real state; the erased run's ghost part is arbitrary. | tight | `Toy.Ghost.erase_refinesUpTo_divBot_needs_same_realPart` |
| `hF : GhostNoFailFrom P σ` | R3b: no ghost block started on the run of P from σ fails (it terminates normally or diverges). | tight | `Toy.Ghost.erase_refinesUpTo_divBot_needs_ghostNoFailFrom` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** substantive
- **Non-vacuity witness:** demo (terminating) from σ0 with the erased run from σ0g; ghost { g := 1 }; assert 0 (fails at a real assertion, so the failure case is exercised) from σ0. Lean: `Toy.Ghost.demo_satisfies_erasure_hypotheses`, `Toy.Ghost.ghostThenRealFail_satisfies_erasure_hypotheses`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [Dafny] Dafny Reference Manual v4.11.0; [Why3] Why3 1.9.0 documentation; [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026) (full records under **Evidence**).
- **Design question:** Is 'ghost assertions hold' needed for erasure to preserve failures of real run-time checks? Yes; tight.
- **Non-claims:** see **Boundaries**, result 1.C, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 1.D — R1, R2, R3a, R3b: exact preservation of real behaviour

- **Kind:** theorem. **Tier:** T1. Folklore made precise: that ghost code must not diverge and that its assertions must hold is stated by Filliâtre-Gondelman-Paskevich (paper proof by bisimulation for an ML-style language) and enforced by Dafny and Why3; the mechanized slice results in Security Foundations assume a static termination-ensuring typing and have no failure outcome. The graded form (failure and divergence separated as bottoms) with per-run conditions was not found mechanized in the sources checked. Filliâtre-Gondelman-Paskevich prove the corresponding exactness result on paper for GhostML; Security Foundations mechanizes exactness of public slices (pub_slice_tsni) for terminating, failure-free Imp under a static typing.
- **Plain claim:** Under R1, R2, R3a and R3b (the last two along the run of the original from σ), the original program from σ and the erased program from any τ with the same real part have exactly the same real-observable behaviour: both terminate with the same final real store, or both fail, or both diverge. Global form (second Lean name): if R3a and R3b hold on runs from every initial state, then ErasureExact P.
- **Lean statements:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
-- primary form
theorem erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ)
    (hT : GhostNoDivergeFrom P σ) (hF : GhostNoFailFrom P σ) :
    ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b
```

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
-- second form
theorem erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, GhostNoDivergeFrom P σ) (hF : ∀ σ, GhostNoFailFrom P σ) :
    ErasureExact P
```

The first form states `∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b` for the given `σ`,
`τ`. The second form's conclusion `ErasureExact P` unfolds to

```lean
∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b
```

with R3a and R3b required from every initial state. The first form is obtained from 1.B and 1.C
using determinism (`rbehaves_iff_of_refinesUpTo_failBot_of_refinesUpTo_divBot`).

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.erase_rbehaves_iff_needs_ghostWritesGhost`, `Toy.Ghost.erasureExact_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.erase_rbehaves_iff_needs_realReadsReal`, `Toy.Ghost.erasureExact_needs_realReadsReal` |
| `hστ : realPart σ = realPart τ` | Both runs start from the same real state; the erased run's ghost part is arbitrary (per-run form only; ErasureExact quantifies over such pairs). | tight | `Toy.Ghost.erase_rbehaves_iff_needs_same_realPart` |
| `hT : GhostNoDivergeFrom P σ  (global form: ∀ σ, GhostNoDivergeFrom P σ)` | R3a: no ghost block started on the run of P from σ diverges (it terminates normally or fails). | tight | `Toy.Ghost.erase_rbehaves_iff_needs_ghostNoDivergeFrom`, `Toy.Ghost.erasureExact_needs_ghostNoDivergeFrom` |
| `hF : GhostNoFailFrom P σ  (global form: ∀ σ, GhostNoFailFrom P σ)` | R3b: no ghost block started on the run of P from σ fails (it terminates normally or diverges). | tight | `Toy.Ghost.erase_rbehaves_iff_needs_ghostNoFailFrom`, `Toy.Ghost.erasureExact_needs_ghostNoFailFrom` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given 1.B and 1.C (combined by rbehaves_iff_of_refinesUpTo_failBot_of_refinesUpTo_divBot, which uses determinism and totality); substantive overall. The global form is a one-line corollary.)
- **Non-vacuity witness:** demo from σ0 with the erased run from σ0g; demo and loopDemo satisfy the global hypotheses. Lean: `Toy.Ghost.demo_satisfies_erasure_hypotheses`, `Toy.Ghost.demo_satisfies_global_erasure_hypotheses`, `Toy.Ghost.loopDemo_satisfies_global_erasure_hypotheses`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [Dafny] Dafny Reference Manual v4.11.0; [Why3] Why3 1.9.0 documentation; [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026) (full records under **Evidence**).
- **Design question:** Which restrictions on ghost code make erasure exactly semantics-preserving? R1, R2, R3a and R3b together; dropping any one admits a counterexample program (this is not necessity for each program).
- **Non-claims:** see **Boundaries**, result 1.D, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom`, `Toy.Ghost.erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). If a verifier's compiler deletes exactly ghost blocks and
assignments to ghost variables, and its checks imply R1, R2 (and R3a, R3b where used) on programs of
this sublanguage, then compiled programs relate to the verified ones as stated here. The
restrictions match the conditions stated in the abstracts of [FGP14] and [FGP16] (ghost code cannot
mutate regular data or diverge) and the Dafny and Why3 rules quoted under **Evidence**; that
correspondence is read from those documents and is not checked.

### Result 2: each restriction is needed

#### 2.1 — Counterexample: ghost code writes a real variable

- **Kind:** counterexample. **Tier:** T0. Elementary instance of the restriction 'ghost code cannot mutate regular data' (Filliâtre-Gondelman-Paskevich).
- **Plain claim:** The program ghost { x := 1 } satisfies R2, R3a and R3b from every state, yet from the all-zero store the original ends with x = 1 and the erased program with x = 0, so even refinement up to failure and divergence (the conclusion of 1.A) fails: a ghost write to a real variable breaks erasure.
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem ghostWriteToReal_breaks_erasure :
    RealReadsReal ceGhostWritesReal ∧ (∀ σ, GhostNoDivergeFrom ceGhostWritesReal σ) ∧
      (∀ σ, GhostNoFailFrom ceGhostWritesReal σ) ∧
      RBehaves ceGhostWritesReal σ0 (.term (realPart (σ0.update x 1))) ∧
      RBehaves (erase ceGhostWritesReal) σ0 (.term (realPart σ0)) ∧
      realPart (σ0.update x 1) ≠ realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0
```

`ceGhostWritesReal` is `ghost { x := 1 }`. From the all-zero store `σ0` the original ends with
`x = 1` and the erased program (`skip`) with `x = 0` (`realPart (σ0.update x 1) ≠ realPart σ0`);
R2, R3a and R3b hold from every state. The last conjunct negates the conclusion of 1.A.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instance; see plain claim.
- **Positive control:** `Toy.Ghost.pcGhostWritesGhost_erasureExact`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [Dafny] Dafny Reference Manual v4.11.0 (full records under **Evidence**).
- **Design question:** What goes wrong when ghost code may write real state.
- **Non-claims:** see **Boundaries**, result 2.1, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostWriteToReal_breaks_erasure`; axioms: `Quot.sound`, `propext`.

#### 2.2 — Counterexample: real code reads a ghost variable (control or data)

- **Kind:** counterexample. **Tier:** T0. Elementary instances of the restriction 'ghost data cannot participate in regular computations' (Filliâtre-Gondelman-Paskevich), through control and through data.
- **Plain claim:** A real statement reading a ghost value breaks erasure, through control or through data: ghost { g := 1 }; if g then x := 1 else skip, and ghost { g := 1 }; x := g, satisfy R1, R3a and R3b from every state, yet from the all-zero store refinement up to failure and divergence fails, and erasure is not exact. From the all-zero store each original ends with x = 1 and its erasure, which reads the initial ghost value 0, with x = 0. The control-flow theorem states these two runs and the difference of their real parts as conjuncts; the data-flow theorem states only the resulting failures of refinement and of exactness, and evaluates the two runs inside its proof.
- **Lean statements:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
-- primary form
theorem implicitFlow_breaks_erasure :
    GhostWritesGhost ceImplicitFlow ∧ (∀ σ, GhostNoDivergeFrom ceImplicitFlow σ) ∧
      (∀ σ, GhostNoFailFrom ceImplicitFlow σ) ∧
      RBehaves ceImplicitFlow σ0 (.term (realPart ((σ0.update g 1).update x 1))) ∧
      RBehaves (erase ceImplicitFlow) σ0 (.term (realPart σ0)) ∧
      realPart ((σ0.update g 1).update x 1) ≠ realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 ∧
      ¬ ErasureExact ceImplicitFlow
```

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
-- second form
theorem dataFlow_breaks_erasure :
    GhostWritesGhost ceDataFlow ∧ (∀ σ, GhostNoDivergeFrom ceDataFlow σ) ∧
      (∀ σ, GhostNoFailFrom ceDataFlow σ) ∧
      ¬ RefinesUpTo abortBot ceDataFlow σ0 (erase ceDataFlow) σ0 ∧
      ¬ ErasureExact ceDataFlow
```

`ceImplicitFlow` is `ghost { g := 1 }; if g then x := 1 else skip` (control flow) and `ceDataFlow` is
`ghost { g := 1 }; x := g` (data flow). Both satisfy R1, and R3a and R3b from every state. From
`σ0` the erased program reads the initial ghost value `0`, so its final `x` differs from the
original's; both the conclusion of 1.A (`RefinesUpTo abortBot`) and `ErasureExact` fail.
`implicitFlow_breaks_erasure` records the two runs from `σ0` (its `RBehaves` conjuncts) and the
inequality of their real parts in its statement. `dataFlow_breaks_erasure` states only
`¬ RefinesUpTo abortBot ceDataFlow σ0 (erase ceDataFlow) σ0` and `¬ ErasureExact ceDataFlow`;
the runs from `σ0` (original ending with `x = 1`, erasure with `x = 0`) are evaluated inside its
proof and are not part of its statement.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instances; see plain claim.
- **Positive control:** `Toy.Ghost.pcRealBranch_erasureExact`, `Toy.Ghost.pcRealDataFlow_erasureExact`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [Dafny] Dafny Reference Manual v4.11.0 (full records under **Evidence**).
- **Design question:** What goes wrong when real code may read ghost state, through data or through control (implicit flow).
- **Non-claims:** see **Boundaries**, result 2.2, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.implicitFlow_breaks_erasure`, `Toy.Ghost.dataFlow_breaks_erasure`; axioms: `propext`.

#### 2.3 — Counterexample: ghost code diverges

- **Kind:** counterexample. **Tier:** T0. Elementary instance of the restriction 'ghost code cannot diverge' (Filliâtre-Gondelman-Paskevich).
- **Plain claim:** The program ghost { while 1 do skip } satisfies R1, R2 and R3b; from every state the original diverges and the erased program terminates, so the erased program has a real behaviour the original lacks: behaviour inclusion, refinement up to failure, and exactness all fail, while refinement up to divergence holds.
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem ghostDivergence_breaks_erasure (σ : Store) :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      GhostNoFailFrom ceGhostDiverges σ ∧
      Diverges ceGhostDiverges σ ∧ Behaves (erase ceGhostDiverges) σ (.term σ) ∧
      ¬ (∀ b, RBehaves (erase ceGhostDiverges) σ b → RBehaves ceGhostDiverges σ b) ∧
      ¬ RefinesUpTo failBot ceGhostDiverges σ (erase ceGhostDiverges) σ ∧
      ¬ ErasureExact ceGhostDiverges ∧
      RefinesUpTo divBot ceGhostDiverges σ (erase ceGhostDiverges) σ
```

`ceGhostDiverges` is `ghost { while 1 do skip }`; it satisfies R1, R2, and R3b from every `σ`. The
original diverges from every `σ`, while `erase ceGhostDiverges = skip` terminates in `σ`. Hence
behaviour inclusion fails, the conclusion of 1.B (`RefinesUpTo failBot`) fails, `ErasureExact`
fails, and the conclusion of 1.C (`RefinesUpTo divBot`) still holds.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instance.
- **Positive control:** `Toy.Ghost.pcGhostTerminatingLoop_erasureExact`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [Why3] Why3 1.9.0 documentation; [Dafny] Dafny Reference Manual v4.11.0 (full records under **Evidence**).
- **Design question:** What goes wrong when ghost code may diverge: the erased program terminates where the original diverged.
- **Non-claims:** see **Boundaries**, result 2.3, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostDivergence_breaks_erasure`; axioms: `propext`.

#### 2.4 — Counterexample: a ghost assertion fails

- **Kind:** counterexample. **Tier:** T0. Elementary counterexample, companion to 2.1-2.3.
- **Plain claim:** The program ghost { assert 0 } satisfies R1, R2 and R3a; from every state the original fails and the erased program terminates, so refinement up to divergence and exactness fail, while refinement up to failure holds.
- **Lean statement:**

```lean
-- ToyGhost/Erasure.lean, namespace Toy.Ghost
theorem ghostFailure_breaks_erasure (σ : Store) :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      GhostNoDivergeFrom ceGhostFails σ ∧
      Fails ceGhostFails σ ∧ Behaves (erase ceGhostFails) σ (.term σ) ∧
      ¬ RefinesUpTo divBot ceGhostFails σ (erase ceGhostFails) σ ∧
      ¬ ErasureExact ceGhostFails ∧
      RefinesUpTo failBot ceGhostFails σ (erase ceGhostFails) σ
```

`ceGhostFails` is `ghost { assert 0 }`; it satisfies R1, R2, and R3a from every `σ`. The original
fails from every `σ`, while `erase ceGhostFails = skip` terminates in `σ`. Hence the conclusion of
1.C (`RefinesUpTo divBot`) and `ErasureExact` fail, and the conclusion of 1.B
(`RefinesUpTo failBot`) still holds.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instance.
- **Positive control:** `Toy.Ghost.pcGhostPassingAssert_erasureExact`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [Dafny] Dafny Reference Manual v4.11.0 (full records under **Evidence**).
- **Design question:** What goes wrong when ghost assertions may fail: a failure of the original disappears after erasure.
- **Non-claims:** see **Boundaries**, result 2.4, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostFailure_breaks_erasure`; axioms: `propext`.

Basis: derived (modeling bridge). Each counterexample is a program of the toy language. That a
verifier lacking the corresponding check would miscompile an analogous program is an inference
from the model; the Dafny and Why3 rules quoted under **Evidence** describe checks that exclude
programs of these shapes, but no verifier was run.

### Result 3: Hoare triples about real variables survive erasure

#### 3.A — Partial-correctness triples with safety survive erasure

- **Kind:** theorem. **Tier:** T1. Folklore made precise: auxiliary-variable elimination for partial correctness goes back to Owicki-Gries and earlier work on auxiliary variables, for auxiliary code made of assignments (which always terminate); Filliâtre-Gondelman-Paskevich require ghost code to terminate. The transfer theorem for ghost blocks with loops and assertions, with the exact hypothesis sets below, was not found mechanized in the sources checked.
- **Plain claim:** If a partial-correctness triple with safety {Pre} P {Post} about real variables (from precondition states P does not fail, and its normally terminating runs satisfy Post) holds for the original program, possibly thanks to ghost code, and R1 and R2 hold, and for every real precondition state some initial store with that real part has no diverging ghost block on its run (R3a), then the same triple holds for the erased program (corollary: the same with R3a required from every initial store whose real part satisfies Pre). R3b is not a hypothesis because the triple's safety clause implies it on precondition states.
- **Lean statements:**

```lean
-- ToyGhost/Hoare.lean, namespace Toy.Ghost
-- primary form
theorem safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ)
    (h : SafePartialTriple Pre P Post) : SafePartialTriple Pre (erase P) Post
```

```lean
-- ToyGhost/Hoare.lean, namespace Toy.Ghost
-- second form
theorem safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, Pre (realPart σ) → GhostNoDivergeFrom P σ)
    (h : SafePartialTriple Pre P Post) : SafePartialTriple Pre (erase P) Post
```

`SafePartialTriple Pre s Post` unfolds to

```lean
∀ σ, Pre (realPart σ) → ¬ Fails s σ ∧ ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')
```

Both forms conclude this for `s := erase P` from the same for `s := P`. The primary form requires
R3a for **one** initial store per real precondition state (`hT : ∀ r, Pre r → ∃ σ, realPart σ = r ∧
GhostNoDivergeFrom P σ`); the corollary requires it for **every** initial store whose real part
satisfies `Pre` (`hT : ∀ σ, Pre (realPart σ) → GhostNoDivergeFrom P σ`).

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.safePartialTriple_erase_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.safePartialTriple_erase_needs_realReadsReal` |
| `hT : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ` | R3a for one initial store per real precondition state. A diverging ghost 'lemma' makes any partial-correctness triple hold. The stronger all-states obligation (∀ σ, Pre (realPart σ) → GhostNoDivergeFrom P σ), which is what a verifier ignorant of initial ghost values establishes, implies it (exists_of_forall_pre) and gives the corollary safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom (second Lean name); the existential form is strictly weaker (safePartialTriple_exists_ghostNoDivergeFrom_strictly_weaker). This ledger entry is for the primary (existential) statement; the corollary replaces hT by the ∀ σ obligation. | tight | `Toy.Ghost.safePartialTriple_erase_needs_ghostNoDivergeFrom` |
| `h : SafePartialTriple Pre P Post` | The triple proved for the original program. It bundles safety (¬ Fails P σ on precondition states); that clause yields R3b on those states (ghostNoFailFrom_of_safePartialTriple), which is why R3b is not a separate hypothesis. With weak partial correctness instead, R3b is needed (3.D, weakPartialTriple_erase_fails_without_ghostNoFailFrom). | tight | `Toy.Ghost.safePartialTriple_erase_needs_safePartialTriple` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given 1.B; substantive overall.)
- **Non-vacuity witness:** {True} demo {y = 6}, with R3a from the store with ghost part 0. This witness (safePartialTriple_erase_hypotheses_satisfiable) and the hypothesis ledger of this card, including the tightness counterexamples for hW, hR and h, correspond to the primary statement (safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom), whose R3a hypothesis is the existential hT : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ. The corollary (safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom) instead carries the all-states obligation ∀ σ, Pre (realPart σ) → GhostNoDivergeFrom P σ, which is sufficient (it implies hT by exists_of_forall_pre) but not minimal (safePartialTriple_exists_ghostNoDivergeFrom_strictly_weaker); its hypotheses hold for {True} demo {y = 6} by demo_satisfies_global_erasure_hypotheses together with safePartialTriple_demo. Lean: `Toy.Ghost.safePartialTriple_erase_hypotheses_satisfiable`.
- **Prior art:** [OG76] Owicki-Gries 1976; [Jones10] Jones 2010; [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [Why3] Why3 1.9.0 documentation (full records under **Evidence**).
- **Design question:** What must a verifier check about ghost code so that partial-correctness proofs (with safety) survive erasure: no ghost writes to real state, no ghost reads in real code, and non-divergence of ghost code in context.
- **Non-claims:** see **Boundaries**, result 3.A, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom`, `Toy.Ghost.safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 3.B — Total-correctness triples survive erasure under R1 and R2 alone

- **Kind:** theorem. **Tier:** T1. Folklore made precise: auxiliary-variable elimination for partial correctness goes back to Owicki-Gries and earlier work on auxiliary variables, for auxiliary code made of assignments (which always terminate); Filliâtre-Gondelman-Paskevich require ghost code to terminate. The transfer theorem for ghost blocks with loops and assertions, with the exact hypothesis sets below, was not found mechanized in the sources checked.
- **Plain claim:** A total-correctness triple about real variables that holds for the original program holds for the erased program under R1 and R2 alone; no separate ghost-termination or ghost-assertion hypothesis is needed, because a valid total triple already forces every ghost block reached from a precondition state to terminate normally (ghostTotalFrom_of_totalTriple).
- **Lean statement:**

```lean
-- ToyGhost/Hoare.lean, namespace Toy.Ghost
theorem totalTriple_erase_of_ghostWritesGhost_of_realReadsReal
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (h : TotalTriple Pre P Post) : TotalTriple Pre (erase P) Post
```

`TotalTriple Pre s Post` unfolds to

```lean
∀ σ, Pre (realPart σ) → ∃ σ', Behaves s σ (.term σ') ∧ Post (realPart σ')
```

and the theorem derives it for `erase P` from the same for `P` under R1 and R2 only.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.totalTriple_erase_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.totalTriple_erase_needs_realReadsReal` |
| `h : TotalTriple Pre P Post` | The total-correctness triple valid for the original program; its termination clause covers the ghost blocks. | tight | `Toy.Ghost.totalTriple_erase_needs_totalTriple` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given 1.A; substantive overall.)
- **Non-vacuity witness:** {True} demo {y = 6} in total correctness. Lean: `Toy.Ghost.totalTriple_erase_hypotheses_satisfiable`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [OG76] Owicki-Gries 1976 (full records under **Evidence**).
- **Design question:** Once total correctness of the original program, ghost code included, has been established, does erasure need any further ghost hypothesis? No: R1 and R2 suffice. Ghost non-divergence still matters for partial correctness (3.A, 3.D), for exact erasure of non-terminating runs (1.B, 1.D, 2.3), and for termination-sensitive noninterference (4.D, 4.F).
- **Non-claims:** see **Boundaries**, result 3.B, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.totalTriple_erase_of_ghostWritesGhost_of_realReadsReal`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 3.D — Weak partial-correctness triples need R3a and R3b at a common store

- **Kind:** theorem. **Tier:** T1. Folklore made precise: auxiliary-variable elimination for partial correctness goes back to Owicki-Gries and earlier work on auxiliary variables, for auxiliary code made of assignments (which always terminate); Filliâtre-Gondelman-Paskevich require ghost code to terminate. The transfer theorem for ghost blocks with loops and assertions, with the exact hypothesis sets below, was not found mechanized in the sources checked.
- **Plain claim:** If a weak partial-correctness triple {Pre} P {Post} about real variables (only normally terminating runs from precondition states must satisfy Post; failure and divergence are vacuous) holds for the original program, and R1 and R2 hold, and for every real precondition state some initial store with that real part has no diverging and no failing ghost block on its run (R3a and R3b at the same store), then the same weak triple holds for the erased program.
- **Lean statement:**

```lean
-- ToyGhost/Hoare.lean, namespace Toy.Ghost
theorem weakPartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom_ghostNoFailFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hG : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ ∧ GhostNoFailFrom P σ)
    (h : WeakPartialTriple Pre P Post) : WeakPartialTriple Pre (erase P) Post
```

`WeakPartialTriple Pre s Post` unfolds to

```lean
∀ σ, Pre (realPart σ) → ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')
```

(failure and divergence both satisfy it). The ghost hypothesis `hG` demands, for each real
precondition state `r`, one initial store with real part `r` from which R3a **and** R3b both hold.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1: ghost blocks assign only ghost variables (ghost code must not change real state). | tight | `Toy.Ghost.weakPartialTriple_erase_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2: real statements read no ghost variable, through data or control (no implicit flow from ghost to real). | tight | `Toy.Ghost.weakPartialTriple_erase_needs_realReadsReal` |
| `hG : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ ∧ GhostNoFailFrom P σ` | R3a and R3b at one common initial store per real precondition state. Each half is needed: ghost { assert 0 } satisfies the R3a half and ghost { while 1 do skip } the R3b half, and both refute the conclusion. | tight | `Toy.Ghost.weakPartialTriple_erase_needs_ghostNoFailFrom`, `Toy.Ghost.weakPartialTriple_erase_needs_ghostNoDivergeFrom` |
| `h : WeakPartialTriple Pre P Post` | The weak triple valid for the original program. | tight | `Toy.Ghost.weakPartialTriple_erase_needs_weakPartialTriple` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given 1.D (hence 1.B and 1.C); substantive overall.)
- **Non-vacuity witness:** {True} demo {y = 6} weakly, with R3a and R3b from the store with ghost part 0. Lean: `Toy.Ghost.weakPartialTriple_erase_hypotheses_satisfiable`.
- **Prior art:** [OG76] Owicki-Gries 1976; [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [FGP16] Filliâtre-Gondelman-Paskevich, FMSD 2016; [Why3] Why3 1.9.0 documentation (full records under **Evidence**).
- **Design question:** If the specification logic treats assertion failure as vacuous (classical partial correctness), what must a verifier check about ghost code for proofs to survive erasure? In addition to 3.A's conditions, that ghost assertions hold.
- **Non-claims:** see **Boundaries**, result 3.D, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.weakPartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom_ghostNoFailFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Reading these as statements about a verifier assumes that its
verified specification denotes the corresponding semantic triple over the real state and that its
compiler erases exactly ghost blocks and ghost assignments; proof rules and verification-condition
generation are not modelled.

### Result 4: erasure and ghost-to-real noninterference

#### 4.A — Exact erasability = ghost-to-real noninterference + agreement with the erasure

- **Kind:** characterization. **Tier:** T0. A definitional congruence: it holds with any program transformation in place of erase and does not unfold the semantics.
- **Plain claim:** Exact erasability of a program is equivalent to the conjunction of termination-sensitive noninterference from ghost to real of the program itself (its real behaviour, including failure and divergence, does not depend on initial ghost values) and agreement of the program with its erasure when both start from the same full store.
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem erasureExact_iff_ghostToRealNI_and_erasureAgrees (P : Stmt) :
    ErasureExact P ↔ GhostToRealNI P ∧ ErasureAgrees P
```

Unfolding the three definitions:

```lean
(∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b) ↔
  (∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves P τ b) ∧
  (∀ σ b, RBehaves P σ b ↔ RBehaves (erase P) σ b)
```

The middle line (`GhostToRealNI`) compares failure and divergence as well as final real stores, so
it is termination- and failure-sensitive.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `GhostToRealNI P (for ⇐)` | Ghost inputs do not influence real behaviour. | tight | `Toy.Ghost.erasureAgrees_not_sufficient_for_erasureExact` |
| `ErasureAgrees P (for ⇐)` | Running the ghost code does not change real behaviour relative to skipping it. | tight | `Toy.Ghost.ghostToRealNI_not_sufficient_for_erasureExact` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** definitional
- **Non-vacuity witness:** ghost { g := 1 } satisfies both sides. Lean: `Toy.Ghost.pcGhostWritesGhost_erasureExact`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014; [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [SM03] Sabelfeld-Myers 2003 (full records under **Evidence**).
- **Design question:** In what precise sense is erasability noninterference from ghost to real?
- **Non-claims:** see **Boundaries**, result 4.A, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erasureExact_iff_ghostToRealNI_and_erasureAgrees`; axioms: none.

#### 4.B — Noninterference alone does not give exact erasability

- **Kind:** counterexample. **Tier:** T0. Analogue of the Rocq-mechanized pub_slice_secure_com2_incorrect (Security Foundations, StaticIFC): a noninterferent program whose public slice is not correct.
- **Plain claim:** Noninterference from ghost to real does not imply exact erasability, even together with R1 and R2: ghost { x := 1 } is termination-sensitively noninterfering yet erasing it changes the result; and ghost { while x do skip }, whose termination depends only on the real variable x, satisfies R1, R2 and termination-sensitive noninterference, yet its erasure terminates where it diverges.
- **Lean statements:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
-- primary form
theorem ghostToRealNI_not_sufficient_for_erasureExact :
    GhostToRealNI ceGhostWritesReal ∧ ¬ ErasureExact ceGhostWritesReal
```

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
-- second form
theorem ghostSpinOnX_ghostToRealNI_not_erasureExact :
    GhostWritesGhost ghostSpinOnX ∧ RealReadsReal ghostSpinOnX ∧
      GhostToRealNI ghostSpinOnX ∧ ¬ ErasureExact ghostSpinOnX
```

First theorem: `ghost { x := 1 }` (`ceGhostWritesReal`) is `GhostToRealNI` but not `ErasureExact`.
Second theorem: `ghost { while x do skip }` (`ghostSpinOnX`), whose termination depends only on the
real variable `x`, satisfies R1, R2 and `GhostToRealNI`, but its erasure `skip` terminates from
states with `x ≠ 0`, where the original diverges.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instances.
- **Positive control:** `Toy.Ghost.pcGhostWritesGhost_erasureExact`.
- **Prior art:** [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014 (full records under **Evidence**).
- **Design question:** Why erasability needs more than ghost-to-real noninterference: ghost code must also neither write real state nor diverge.
- **Non-claims:** see **Boundaries**, result 4.B, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostToRealNI_not_sufficient_for_erasureExact`, `Toy.Ghost.ghostSpinOnX_ghostToRealNI_not_erasureExact`; axioms: `Quot.sound`, `propext`.

#### 4.C — Agreement with the erasure alone does not give exact erasability

- **Kind:** counterexample. **Tier:** T0. Elementary counterexample.
- **Plain claim:** Agreement of a program with its erasure from the same full store does not imply exact erasability: x := g has no ghost statements, so it agrees with its erasure, but its result depends on the ghost input, which no longer exists after erasure.
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem erasureAgrees_not_sufficient_for_erasureExact :
    ErasureAgrees realReadsGhost ∧ ¬ ErasureExact realReadsGhost
```

`realReadsGhost` is `x := g`. It contains no ghost statement, so `erase realReadsGhost` is the same
program and `ErasureAgrees` holds; but the program run from `σ0` ends with `x = 0` while its
erasure run from `σ0g` (same real part, `g = 1`) ends with `x = 1`, so `ErasureExact` fails.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instance.
- **Positive control:** `Toy.Ghost.pcGhostWritesGhost_realReadsReal_erasureAgrees_erasureExact`, `Toy.Ghost.erasureExact_iff_erasureAgrees_of_realReadsReal`.
- **Prior art:** [FGP14] Filliâtre-Gondelman-Paskevich, CAV 2014 (full records under **Evidence**).
- **Design question:** Why real code must not read ghost state even when no ghost statement is erased.
- **Non-claims:** see **Boundaries**, result 4.C, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erasureAgrees_not_sufficient_for_erasureExact`; axioms: `Quot.sound`, `propext`.

#### 4.D — R1-R3 imply termination- and failure-sensitive noninterference

- **Kind:** theorem. **Tier:** T0. Re-derivation: termination-sensitive noninterference under a discipline that also ensures termination of secret-dependent code is mechanized in Rocq (ts_well_typed_tsni, Security Foundations); the failure channel is the analogous case for assertions.
- **Plain claim:** R1, R2 and, on runs from every initial state, R3a and R3b imply noninterference from ghost to real that is sensitive to termination and failure: the final real store, failure, and divergence do not depend on initial ghost values.
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem ghostToRealNI_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, GhostNoDivergeFrom P σ) (hF : ∀ σ, GhostNoFailFrom P σ) : GhostToRealNI P
```

`GhostToRealNI P` unfolds to

```lean
∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves P τ b
```

where `b` ranges over normal termination with a given final real store, failure, and divergence.
R3a and R3b are required on runs from every initial state.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1. | tight | `Toy.Ghost.ghostToRealNI_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2. | tight | `Toy.Ghost.ghostToRealNI_needs_realReadsReal` |
| `hT : ∀ σ, GhostNoDivergeFrom P σ` | R3a everywhere (closes the termination channel). | tight | `Toy.Ghost.ghostToRealNI_needs_ghostNoDivergeFrom` |
| `hF : ∀ σ, GhostNoFailFrom P σ` | R3b everywhere (closes the failure channel). | tight | `Toy.Ghost.ghostToRealNI_needs_ghostNoFailFrom` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** definitional (Definitional given the global form of 1.D and 4.A; substantive overall.)
- **Non-vacuity witness:** demo satisfies all four hypotheses. Lean: `Toy.Ghost.demo_satisfies_global_erasure_hypotheses`.
- **Prior art:** [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [VIS96] Volpano-Irvine-Smith 1996; [SM03] Sabelfeld-Myers 2003 (full records under **Evidence**).
- **Design question:** The ghost restrictions as an information-flow discipline with ghost = high and real = low.
- **Non-claims:** see **Boundaries**, result 4.D, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostToRealNI_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 4.E — R1 and R2 imply only abort-insensitive noninterference

- **Kind:** theorem. **Tier:** T0. Re-derivation: soundness of Volpano-Irvine-Smith typing for termination-insensitive noninterference is mechanized in Isabelle/HOL (Snelting-Wasserrab, AFP VolpanoSmith) and in Rocq (cf_well_typed_noninterferent, Security Foundations); R1 + R2 is the analogous discipline here.
- **Plain claim:** R1 and R2 alone, the analogue of a Volpano-Irvine-Smith secure-flow discipline with ghost = high and real = low, give abort-insensitive noninterference: two runs from states with the same real part that both terminate normally end with the same real part. Neither the failure channel nor the termination channel is covered.
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem ghostToRealNI_abortInsensitive_of_ghostWritesGhost_of_realReadsReal
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P) : GhostToRealNI_AbortInsensitive P
```

`GhostToRealNI_AbortInsensitive P` unfolds to

```lean
∀ σ τ σ' τ', realPart σ = realPart τ → Behaves P σ (.term σ') → Behaves P τ (.term τ') →
  realPart σ' = realPart τ'
```

Only pairs of normally terminating runs are compared.

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hW : GhostWritesGhost P` | R1. | tight | `Toy.Ghost.ghostToRealNI_abortInsensitive_needs_ghostWritesGhost` |
| `hR : RealReadsReal P` | R2. | tight | `Toy.Ghost.ghostToRealNI_abortInsensitive_needs_realReadsReal` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given 1.A (plus determinism); substantive overall.)
- **Non-vacuity witness:** demo satisfies R1 and R2. Lean: `Toy.Ghost.demo_satisfies_erasure_hypotheses`.
- **Prior art:** [VIS96] Volpano-Irvine-Smith 1996; [SW08] Snelting-Wasserrab 2008 (AFP); [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [SM03] Sabelfeld-Myers 2003 (full records under **Evidence**).
- **Design question:** What the flow restrictions give without termination restrictions.
- **Non-claims:** see **Boundaries**, result 4.E, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostToRealNI_abortInsensitive_of_ghostWritesGhost_of_realReadsReal`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

#### 4.F — Counterexample: R1 and R2 leave a termination channel

- **Kind:** counterexample. **Tier:** T0. The termination channel of secure-flow typing is textbook: Volpano-Smith 1997 give a typing that eliminates covert flows through nontermination, Sabelfeld-Myers 2003 survey the termination-insensitive versus termination-sensitive distinction, and the channel is mechanized in Rocq (termination_leak, tini_secure_termination_leak, tsni_insecure_termination_leak in Security Foundations).
- **Plain claim:** R1 and R2 do not give termination-sensitive noninterference: ghost { while g do skip } satisfies both, its ghost block never fails, and it terminates from σ0 (g = 0) and diverges from σ0g (g = 1), two states with the same real part (a termination channel).
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI :
    GhostWritesGhost ghostSpinOnG ∧ RealReadsReal ghostSpinOnG ∧
      realPart σ0 = realPart σ0g ∧ Behaves ghostSpinOnG σ0 (.term σ0) ∧
      Diverges ghostSpinOnG σ0g ∧ (∀ σ, GhostNoFailFrom ghostSpinOnG σ) ∧
      ¬ GhostToRealNI ghostSpinOnG
```

`ghostSpinOnG` is `ghost { while g do skip }`. It satisfies R1 and R2, its ghost block never fails
(R3b from every state), it terminates from `σ0` (where `g = 0`) and diverges from `σ0g` (where
`g = 1`), and `σ0` and `σ0g` have the same real part; hence `GhostToRealNI` fails.

- **Hypothesis ledger:** none; this is a concrete counterexample, stated as a conjunction of the properties the instance satisfies and the conclusion that fails.
- **Depth:** shallow
- **Non-vacuity witness:** Concrete instance.
- **Positive control:** `Toy.Ghost.ghostToRealNI_abortInsensitive_ghostSpinOnG`.
- **Prior art:** [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026); [SM03] Sabelfeld-Myers 2003; [VS97] Volpano-Smith 1997 (full records under **Evidence**).
- **Design question:** Why ghost termination is the ghost-code counterpart of closing the termination channel.
- **Non-claims:** see **Boundaries**, result 4.F, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI`; axioms: `Quot.sound`, `propext`.

#### 4.G — Under R2, exact erasability = agreement with the erasure

- **Kind:** characterization. **Tier:** T0. Restates the standard fact that a program mentioning no high variable is noninterferent, combined with 4.A.
- **Plain claim:** Under R2 (real code reads no ghost variable), exact erasability of P is equivalent to agreement of P with erase P from the same full store, because the erased program then mentions no ghost variable and its real behaviour depends only on the real part of its initial store.
- **Lean statement:**

```lean
-- ToyGhost/Noninterference.lean, namespace Toy.Ghost
theorem erasureExact_iff_erasureAgrees_of_realReadsReal {P : Stmt} (hR : RealReadsReal P) :
    ErasureExact P ↔ ErasureAgrees P
```

Under `RealReadsReal P`, the statement unfolds to

```lean
(∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b) ↔
  (∀ σ b, RBehaves P σ b ↔ RBehaves (erase P) σ b)
```

- **Hypothesis ledger:**

| hypothesis | purpose | tightness | counterexample |
| --- | --- | --- | --- |
| `hR : RealReadsReal P` | R2: makes the erased program independent of ghost state (erase_rbehaves_congr_of_realReadsReal). | tight | `Toy.Ghost.erasureExact_iff_erasureAgrees_needs_realReadsReal` |

  Each counterexample theorem states that all other hypotheses hold for a concrete instance and the conclusion fails.
- **Depth:** shallow (Shallow given rbehaves_congr_of_noGhostVars (a fuel induction); substantive overall.)
- **Non-vacuity witness:** ghost { g := 1 } satisfies R2 and both sides. Lean: `Toy.Ghost.pcGhostWritesGhost_realReadsReal_erasureAgrees_erasureExact`.
- **Prior art:** [SM03] Sabelfeld-Myers 2003; [SF] Hriţcu-Kim, *Security Foundations* (Software Foundations vol. 7, 2026) (full records under **Evidence**).
- **Design question:** Under R2, the only remaining question for exact erasure is whether running the ghost code changes real behaviour relative to skipping it.
- **Non-claims:** see **Boundaries**, result 4.G, and the non-claims shared by all results.

Basis: execution (Lean kernel check). `lake build` checks `Toy.Ghost.erasureExact_iff_erasureAgrees_of_realReadsReal`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Reading R1 and R2 as an information-flow discipline with ghost =
high and real = low is an analogy to secure-flow typings such as [VIS96]; the differences are listed
in the non-claims of 4.E. The noninterference notions are the standard termination-sensitive and
termination-insensitive ones of [SM03], extended here with a failure outcome.

## Boundaries

### Non-claims

These are what the results do **not** show. Non-claims that apply to several results are listed once with the results they apply to; `results.json` repeats them in every card.

#### Shared non-claims

- *(all results)* Toy model, and R1, R2, R3a, R3b are not shown sufficient for sound ghost erasure in richer languages or verifiers: deterministic sequential while-language with only inhabited Int variables, total expressions (Expr.eval cannot fail or diverge), fatal uncatchable assert failure, no procedures or recursion (a ghost lemma call is an inline ghost block), no heap, no ghost fields, no ghost functions inside specifications, no nondeterministic choice, no concurrency. It does not address empty or uninhabited ghost types (witness checks), assume statements or unverified axioms, witnessless existential choice, mutable heap aliasing between ghost and real references, catchable exceptions or early exits (return, break) escaping a ghost block, or concurrent interleavings. Transfer to Dafny or Why3 is a modeling bridge, not a kernel-checked fact.
- *(results 1.A, 1.B, 1.C, 1.D, 3.A, 3.B, 3.D)* R1 and R2 are syntactic sufficient conditions: they inspect unreachable code too, and they require an explicit ghost { ... } block around any conditional or loop whose guard reads a ghost variable, so they reject e.g. if g then g := 0 else g := 1, which Dafny's ghost inference (reference manual section 12.3) treats as a ghost statement and a Volpano-Irvine-Smith-style flow typing accepts. R3a and R3b are semantic and constrain only ghost blocks that the run reaches. None of R1, R2, R3a, R3b is claimed necessary for any individual program to be erasable: ghost { x := x }, x := g - g, and unreachable ghost code can be erasable while violating one of them; tightness means only that dropping a restriction admits some counterexample program.
- *(results 1.A, 1.B, 1.C, 1.D)* Erasure is compared only on real-observable behaviour (final real store, failure, divergence); execution step counts, fuel consumption, and timing are not preserved and not compared (a ghost block consumes fuel in the original semantics, its erased skip takes one unit).
- *(results 2.2, 4.C, 4.G)* erase P is again a Stmt run on a full Store. For R2-violating programs, erase P still reads ghost variables (erase (x := g) = x := g) and executes at all only because of this encoding; a compiler targeting real stores would reject it. Under R2 the erased program ignores the ghost part of its store (erase_rbehaves_congr_of_realReadsReal).
- *(results 3.A, 3.B, 3.D)* SafePartialTriple, WeakPartialTriple, and TotalTriple are semantic validity statements, not derivability in a Hoare logic or verification-condition generator; these results do not establish soundness of any proof system or VC translation.
- *(results 3.A, 3.B, 3.D)* Because Pre and Post are predicates on RStore only, initial ghost variables are universally quantified (effectively uninitialized) at entry; these results do not transfer specifications whose preconditions or postconditions mention ghost parameters, ghost return values, or ghost model state.

#### Non-claims of individual results

- **1.A**
  - Does not say the erased program fails when the original fails, or diverges when the original diverges; both are false (ghostFailure_breaks_erasure, ghostDivergence_breaks_erasure).
  - Does not give the converse direction (erased terminates implies original terminates).
  - R1 and R2 are syntactic sufficient conditions; they are not claimed necessary for any particular program.
  - Unfolds to plain termination preservation only because the language is deterministic (refinesUpTo_abortBot_iff).
- **1.B**
  - Says nothing when the original fails: an erased failing ghost assertion lets the erased program do anything.
  - R3a is required only along the actual run from σ, not from every state; it is not claimed to be the weakest sufficient condition. R3a means 'does not diverge', not 'terminates normally': a failing ghost block satisfies it.
  - The corollary that divergence of the original is preserved by erasure relies on determinism (Behaves.unique) and totality (Behaves.exists); in a nondeterministic language RefinesUpTo failBot would allow the erased program to drop a possible diverging branch in favour of a terminating one.
- **1.C**
  - Says nothing when the original diverges: an erased diverging ghost block lets the erased program terminate.
  - R3b is required only along the actual run from σ.
  - The corollary that failure of the original is preserved relies on determinism and totality. The theorem formalizes no failure-blame relation identifying which assert failed; that the preserved failure comes from a real run-time check is an informal reading of the fact that erase P contains no ghost code (noGhostCode_erase).
- **1.D**
  - Compares real behaviours only; final ghost values are not compared.
  - Exactness uses determinism and totality; with nondeterministic choice only refinement forms would be expected (not examined).
  - In the per-run form R3a and R3b are assumed only on the run from σ; nothing is said about ghost code safety from other states. The global form needs them from every initial state, which is weaker than the static GhostBlocksNoDiverge / GhostBlocksNoFail (these imply it) but stronger than what 3.A needs.
- **2.1**
  - Shows only that R1 cannot be dropped; it does not show that every ghost write to real state is observable (a write of the value already present would not be).
  - Does not model indirect mutation of real state through mutable heap aliasing (ghost code changing real memory without syntactically assigning a real variable).
- **2.2**
  - Does not show that every real statement syntactically mentioning a ghost variable breaks erasure: escape hatches include branches with identical real effects (if g then x := 1 else x := 1), ghost-independent expressions (x := g - g), and unreachable code (if 0 then ... ).
- **2.3**
  - Does not show that every ghost loop breaks erasure: terminating ghost loops are erased exactly (positive control), and a ghost loop that diverges only from states the run never reaches satisfies R3a (ghostNoDivergeFrom_example_pos_guarded), so 1.D applies to it.
- **2.4**
  - Does not show that every program containing a failing ghost assertion breaks erasure: unreachable ghost assertions (if 0 then ghost { assert 0 } else skip) and assertions masked by earlier real failure or divergence (assert 0; ghost { assert 0 }) do not violate R3b along the run and do not break exact erasure.
  - R3a holds for this program because R3a excludes only divergence; a failing ghost block counts as non-diverging.
- **3.A**
  - Does not transfer in the other direction (from the erased program to the original).
  - The triple includes safety; for weak partial correctness, in which failure is also vacuous, a failing ghost assertion would 'prove anything' and R3b is needed (3.D).
  - R3b holding globally is not implied by the hypotheses (safePartialTriple_transfer_without_global_ghostNoFail); it is only implied on precondition states.
- **3.B**
  - Omitting a separate ghost-termination hypothesis does not mean a total-correctness verifier can skip proving termination of ghost code: TotalTriple Pre P Post is semantic termination of P including its ghost blocks, so establishing it still requires every reachable ghost loop or lemma to terminate.
  - Transfer is one-way from P to erase P: TotalTriple Pre (erase P) Post does not imply TotalTriple Pre P Post (erase ceGhostDiverges and erase ceGhostFails satisfy {True} · {True} while the originals do not; totalTriple_erase_not_converse).
  - Does not license skipping termination checks of ghost code when only partial correctness is proved (3.A's counterexample for hT).
- **3.D**
  - R3a and R3b at possibly different stores for the same real state are not sufficient (weakPartialTriple_erase_split_ghost_conditions_insufficient: ghost { if g then assert 0 else while 1 do skip }); the common-store form is not claimed minimal.
  - Does not transfer in the other direction.
- **4.A**
  - Noninterference here is a semantic property of the original program only; it is not the syntactic R1 + R2 discipline.
  - Does not say that a noninterfering program can always be made erasable.
  - This is a definitional encoding equivalence whose right-hand side still mentions erase P, not an erasure-free characterization of erasability.
  - ErasureAgrees is meaningful for R2-violating programs (such as x := g) only because erase P is run on a full Store with ghost variables retained; over real stores it would not be expressible without R2. Under R2, ErasureAgrees P alone is equivalent to ErasureExact P (4.G).
- **4.B**
  - Does not say noninterference is irrelevant; by 4.A it is one of the two conjuncts of exact erasability.
  - Escape hatch: under all of R1, R2, R3a and R3b exact erasure holds (global form of 1.D); R1 alone or R1 with R2 does not close the gap (second program).
  - Concerns the syntactic deletion erase, not semantics-aware program transformations.
- **4.C**
  - Depends on modelling the erased program's ghost part as arbitrary; under a semantics that kept ghost initial values, this program would count as erasable.
  - Escape hatch: under R2, erase P mentions no ghost variable (noGhostVars_erase_of_realReadsReal), so ErasureAgrees P alone implies both GhostToRealNI P and ErasureExact P (4.G).
- **4.D**
  - Noninterference is strictly weaker than erasability (4.B).
  - Covers only the final real store, failure, and divergence; not timing, step counts, or other side channels. R1-R3 are not claimed necessary for noninterference of any particular program.
- **4.E**
  - Says nothing about the divergence channel (4.F: ghost { while g do skip }) or the failure channel (ghost { assert g }: ghostAssertG_abortInsensitive_not_ghostToRealNI, ghostToRealNI_needs_ghostNoFailFrom).
  - R1 + R2 is an analogue of, not identical to, the Volpano-Irvine-Smith typing: here ghost code is marked explicitly and a real if on a ghost value is rejected outright, whereas a secure-flow typing would accept it when both branches write only high variables.
- **4.F**
  - The same program is abort-insensitively noninterfering (positive control); only the termination channel is shown here (the failure channel: ghostToRealNI_needs_ghostNoFailFrom).
  - Escape hatch: adding R3a and R3b everywhere restores termination- and failure-sensitive noninterference (4.D).
  - Does not show that every diverging ghost loop creates a termination channel: ghost { while x do skip }, guarded by a real variable, is GhostToRealNI while still breaking exact erasure (4.B).
- **4.G**
  - Does not remove the need for R1 and R3: ErasureAgrees itself fails for ghost writes to real state (2.1), diverging ghost code (2.3), and failing ghost assertions (2.4).

#### Attractive stronger conclusions that are not established

- That R1, R2, R3a, R3b are **necessary** for erasability of a given program: they are sufficient
  syntactic (R1, R2) and semantic (R3a, R3b) conditions; tightness means only that dropping one of
  them admits some counterexample program.
- That "erasable" and "ghost-to-real noninterferent" are the same property: 4.B and 4.C refute both
  directions of the bare equivalence; the exact relation is 4.A.
- That ghost termination is irrelevant once a program is verified: it is irrelevant for total
  correctness (3.B) but needed for partial correctness (3.A, 3.D), for exact erasure of
  non-terminating runs (1.B, 1.D, 2.3), and for termination-sensitive noninterference (4.D, 4.F).
- That any of these results holds for Dafny, Why3, or another verifier: every such reading is a
  modeling bridge (see the `Basis: derived (modeling bridge)` lines under **Findings**).

### Escape hatches

Which added hypotheses defeat each counterexample (each is a proved result of this package):

- **2.1** (ghost write to real state): adding R1 restores 1.A (R2 already holds).
- **2.2** (real code reads ghost state): adding R2 restores 1.A (R1 already holds); the data-flow
  positive control `pcRealDataFlow_erasureExact` shows that reading a real variable instead is
  exactly erasable.
- **2.3** (diverging ghost code): adding R3a restores 1.B; even without it, 1.C (refinement up to
  divergence) holds, as the theorem itself states.
- **2.4** (failing ghost assertion): adding R3b restores 1.C; even without it, 1.B (refinement up
  to failure) holds, as the theorem itself states.
- **4.B** (noninterference without exactness): adding agreement with the erasure (`ErasureAgrees`)
  gives exactness by 4.A; adding R3a and R3b from every state to R1 and R2 gives exactness by 1.D.
- **4.C** (agreement without exactness): adding ghost-to-real noninterference gives exactness by
  4.A; adding R2 gives exactness by 4.G.
- **4.F** (termination channel): adding R3a and R3b on runs from every initial state restores
  termination- and failure-sensitive noninterference (4.D). R3a alone does not close the failure
  channel: `ghost { assert g }` satisfies R1, R2 and R3a from every state and is not
  `GhostToRealNI` (`ghostAssertG_abortInsensitive_not_ghostToRealNI`).

### Tightness status

Every hypothesis of every theorem in this package is `tight`, with a fully proved counterexample
named in its hypothesis ledger. No hypothesis is labelled `harmless` or `unknown`.

### Not examined

- Nondeterministic languages (`havoc`, nondeterministic choice): the refinement relation
  `RefinesUpTo` is phrased in the general form, but only deterministic programs are examined, and
  with unbounded nondeterminism "out of fuel for every bound" would no longer characterize
  divergence.
- A formal secure-flow typing judgement compared with R1 + R2 (only the informal differences in the
  non-claims of 4.E are recorded).
- The converse transfer of 3.A (from the erased program back to the original) is not stated or
  proved. With R1, R2, and R3a and R3b from every initial state it would follow from the global form
  of 1.D (derived reasoning, not a kernel-checked result of this package).
- Execution cost: step counts, fuel consumption, and timing are not compared.

### Disproved or dropped statements

None. Every statement of this package was proved as stated; no statement was found false, and none
was left unproved or removed.

## Evidence

### Kernel-check record

- **Toolchain:** `leanprover/lean4:v4.34.1`, release commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (the commit of tag `v4.34.1` in `leanprover/lean4`,
  read from the GitHub API, and the commit reported by `lean --version` of the toolchain used).
  Core Lean only; the Lake project has no dependencies.
- **Build:** `lake build` in `lean/` succeeds from a clean checkout with no errors and no warnings (observed 2026-11-20).
- **Source hygiene:** no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, or `unsafe`,
  and no `axiom` or `opaque` declarations, in any Lean source.
- **Axioms:** all 678 declarations of the `ToyGhost` modules depend only on `propext`, `Classical.choice`, `Quot.sound` (459 with no axioms; 135 with `propext`; 65 with `Quot.sound`, `propext`; 19 with `Classical.choice`, `Quot.sound`, `propext`). The per-declaration record is `audit/axioms.json`.
- **Statement hashes:** for each Lean name referenced by `results.json`, the statement hash is
  the SHA-256 of the Lean `repr` of its type, and the closure hash is the SHA-256 of the sorted,
  newline-joined list of entries `c : <repr of type>` (plus ` := <repr of value>` for non-theorems)
  over every constant of the `ToyGhost` modules reachable from the statement through types,
  definition values and inductive constructors (theorem bodies excluded). Values are recorded in
  `audit/statements.json`; `lean/RevalidationAudit.lean` prints the hashed text (see
  **Revalidation**).

| Lean name (namespace `Toy.Ghost`) | role | axioms | statement SHA-256 | closure SHA-256 | closure size |
| --- | --- | --- | --- | --- | --- |
| `dataFlow_breaks_erasure` | 2.2 result | propext | `49aa9563a81a21c4a54b7a1309647bc398062c3a5e36f817d42df36041deefe2` | `db96f423c523a6d98db3881b6b0e9f57df5c999c31d14d549d730ac6bf2c8c43` | 92 |
| `demo_satisfies_erasure_hypotheses` | 1.A non-vacuity; 1.B non-vacuity; 1.C non-vacuity; 1.D non-vacuity; 4.E non-vacuity | Quot.sound, propext | `83b066d9ee76327aa2c4e9104bd3644149d2f81cba29f66fbd91b273250d3c2e` | `bba77c8672449a8e6e1e764c59bb172beaba26a046522f9cf92a4b7216b9b51d` | 88 |
| `demo_satisfies_global_erasure_hypotheses` | 1.D non-vacuity; 4.D non-vacuity | propext | `54b8f1a8e2732f403ae9c57f2c9c76ff4ffea3acf069e97594f9ed7988775ca3` | `5f9f8b1e23f89d8d842a4fc643694c0638671769fe19420121d3f872e48ba8c9` | 84 |
| `erase_rbehaves_iff_needs_ghostNoDivergeFrom` | 1.D counterexample for `hT` | propext | `133074c0439552662c0a75c1a06de30ea9983c2d562c51901604f1c2e71a6557` | `ca7f3815af8f8a2e75522cd704f88d33864397c7959d6a14746f6cd3b5551075` | 91 |
| `erase_rbehaves_iff_needs_ghostNoFailFrom` | 1.D counterexample for `hF` | propext | `e9a06a02daa1ec8f57433e9ca7d123d15f88b39fb82667f866694913ddd5228c` | `51068b01f2ee183f6120dd2428f855a7529195f4b72ad2525b2f7c86ee94493b` | 90 |
| `erase_rbehaves_iff_needs_ghostWritesGhost` | 1.D counterexample for `hW` | Quot.sound, propext | `d71ee251556d376e8640107dca6a73bb1d5288396fc2b733197b9ed7d85679ae` | `59512049efae39f1a10bfd66fbaa2824757fc6cfa076923e82138079621eab5f` | 88 |
| `erase_rbehaves_iff_needs_realReadsReal` | 1.D counterexample for `hR` | propext | `f32f12b1d02a1ef1ade2f8294f3e9ea50def6d33def017e5f2dd4e6d106dcaa1` | `b8fd0c3c74c142e18b92e1df13845489e0b225bb0f0795564dae6c7f8712efcc` | 89 |
| `erase_rbehaves_iff_needs_same_realPart` | 1.D counterexample for `hστ` | Quot.sound, propext | `fe9cfd0765c3a943c46220a1950a9a07570bed16389f5ac1fad43f83384344e2` | `cdd638b38b98c3e3c6653f469e993847b81931444100496e602e0b7278ee1384` | 92 |
| `erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom` | 1.D result | Classical.choice, Quot.sound, propext | `dbcb2492e93a385bf60a684d3dbc55922bf2f9d1fd1eac7636fb20aa8f8b8471` | `0d611f7c707e84884053f9e17b4bba490264d7c39fed100e32004b903a8d5b11` | 90 |
| `erase_refinesUpTo_abortBot_needs_ghostWritesGhost` | 1.A counterexample for `hW` | Quot.sound, propext | `996e2978cb7d603b03b8fbe67a443ff7a321eca29ba5be8176ef9b57bd30e76d` | `0dbd93a772113ba0d2eaa4bc12a52bbc669a5952d3dea80a90238c70212daff2` | 83 |
| `erase_refinesUpTo_abortBot_needs_realReadsReal` | 1.A counterexample for `hR` | propext | `ff134714bf71c5895098534146b59549326ff0575df53060f959a04ff3cb4a18` | `15fdff958edcadfa079db98468d8db05b7106f71019e95aa5fa693e99fe47455` | 84 |
| `erase_refinesUpTo_abortBot_needs_same_realPart` | 1.A counterexample for `hστ` | Quot.sound, propext | `7e81f2860dc55119fa05db931f37d284ba96c5880cee47d9eb133f51169ca2d5` | `de299022adfb111a7d36485c8b21c8c876beceab9f931c9fa162044a2a4a4bf2` | 87 |
| `erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal` | 1.A result | Classical.choice, Quot.sound, propext | `a8065e672f63d99b29e4022aeb4b1e5fb650e2ccf057e9e6c1aed5459c78aa72` | `4df0f6433496f62f6cb3eb04eca98cf449cb2f5018781e9ef2f101c2130dab7b` | 85 |
| `erase_refinesUpTo_divBot_needs_ghostNoFailFrom` | 1.C counterexample for `hF` | propext | `5c28882502dc4bc388fc60466cda824bcc802fecce12135928a58eceeb30e76c` | `0cd65bf08e22278ba7b926f856f0ec2eeba6073428f1104a344756913cff7405` | 87 |
| `erase_refinesUpTo_divBot_needs_ghostWritesGhost` | 1.C counterexample for `hW` | Quot.sound, propext | `dc3204c7341e5c20fea7fed37cc4f998b62b57e21795971cd6d826eb8fe69dcb` | `b1a379a97a052a5012d00654fb0b5f3672a4fffa766a9ff7ecb43d7df8d695a1` | 88 |
| `erase_refinesUpTo_divBot_needs_realReadsReal` | 1.C counterexample for `hR` | propext | `785b10ff73c6de09de529ce941ec169b1f141b247d20d218c9267af30fe07d9e` | `953f5fb201c6ba9fb88d2965acb714bbef6ebb88b6df7a7ac5ac72b38ece2715` | 89 |
| `erase_refinesUpTo_divBot_needs_same_realPart` | 1.C counterexample for `hστ` | Quot.sound, propext | `bfd6f30a830a4780b577fa7c377e07f5739136079eebfd330c4e7b88e10d07ef` | `c882bbbca8419d849f8f33e74a3990124ef0ff3cf6f83e10638a61822fd06f0b` | 92 |
| `erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom` | 1.C result | Classical.choice, Quot.sound, propext | `c68c111fc1ddad23ff171502a1ef9473bc2765d1927c16e735f115bc74ea2add` | `79ffc47e773889dd2c2be580558c49335290f0a6508f35d487c3667dc3c331cf` | 90 |
| `erase_refinesUpTo_failBot_needs_ghostNoDivergeFrom` | 1.B counterexample for `hT` | propext | `c5119f36a3ca5fcad7feeeb502fb3676b40dfaf9df001b2b03bfffc7107184d5` | `0b245f587a697b5fb99d7b8f3efc981ae6bed639482aedb21ca591d8558f36c7` | 88 |
| `erase_refinesUpTo_failBot_needs_ghostWritesGhost` | 1.B counterexample for `hW` | Quot.sound, propext | `6fba931ccdd197a54f43778b164cecb13b587b7f008c30e2ab3270ddc7c33936` | `fce729d4b70107df98c71db4b5af569fc940b3684d53471b6f95b9f4fc56f1bf` | 88 |
| `erase_refinesUpTo_failBot_needs_realReadsReal` | 1.B counterexample for `hR` | propext | `14d75c213202318d4b2370d6d8e299a18daf78bd7444baca8e39b9d7c9e9c6f0` | `8b67832f8a52f7a8b1af85e223d5607ffba0770ebf8fbe318eab807c89f6e9fe` | 89 |
| `erase_refinesUpTo_failBot_needs_same_realPart` | 1.B counterexample for `hστ` | Quot.sound, propext | `80cf611d8f3421470c94369806d76e9a0bf1d00b58166cf6469e14ba2ab9442b` | `7399809f0a8815da3c00ebd0190b77f443d95f383d4245eb737c5dcc6314c95e` | 92 |
| `erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom` | 1.B result | Classical.choice, Quot.sound, propext | `cf6c9502998475db78aeb01c82bb5bc25144e8b8eb4c743f05fa494b369ce5de` | `72783818ecfa5ff43ae6aa88e8649fbf19a35b1dbaa677e2baa97c69623dc946` | 90 |
| `erasureAgrees_not_sufficient_for_erasureExact` | 4.A counterexample for `GhostToRealNI P (for ⇐)`; 4.C result | Quot.sound, propext | `79734d7b356d488cdb396a0ad1e3737ae5a6ceb0b582c4860f8bc1e5c7be7d11` | `08f40880cc93827a3fd79c826ee4bd39aebacf24596ab27b538207cfc0b30d1c` | 78 |
| `erasureExact_iff_erasureAgrees_needs_realReadsReal` | 4.G counterexample for `hR` | Quot.sound, propext | `79734d7b356d488cdb396a0ad1e3737ae5a6ceb0b582c4860f8bc1e5c7be7d11` | `08f40880cc93827a3fd79c826ee4bd39aebacf24596ab27b538207cfc0b30d1c` | 78 |
| `erasureExact_iff_erasureAgrees_of_realReadsReal` | 4.C positive control; 4.G result | Classical.choice, Quot.sound, propext | `752fbfa1d1c2615ef64a4828ed0b1ceb56ae8f91e2cb8e4dce2019a8365add91` | `851ff3712d7e30b07bde27c74cc65a06c1b61408a555d55232909f70bc7d6c5c` | 80 |
| `erasureExact_iff_ghostToRealNI_and_erasureAgrees` | 4.A result | none | `6d0754e82a3ed9752ba6afbf66bbe37fa1ee383dcd547dc55a6b9cd422942721` | `2abe46cfafe4f1eb90ed82e4957c3c9d0fe722baf886a2ff8d4f9e58fc349798` | 76 |
| `erasureExact_needs_ghostNoDivergeFrom` | 1.D counterexample for `hT` | propext | `9d82e95daac52f258484ed7e63c9c9319a91021bc4e558dea5c51452db62d6b7` | `26b2457f17553aa581f50d5f11ba60ee94116f1a3e09d90eed55c9a0df321fd7` | 91 |
| `erasureExact_needs_ghostNoFailFrom` | 1.D counterexample for `hF` | propext | `34e58be28b9e32c8b215f0c5e5741af8caaf7fed1ec38ba8465a2a26951e12a9` | `1529a96655390c89aac34d9526f12da866c8d6e9687503ffced11a09b7582cd7` | 90 |
| `erasureExact_needs_ghostWritesGhost` | 1.D counterexample for `hW` | Quot.sound, propext | `1cf6f6f3ce6468cd221c65f956128e6a579ee72411c44de9e9fabeaf067e2610` | `3f3d0f34054b547e6d2f3fdfa38c0cf0d60981bead46d06322413684594865dd` | 88 |
| `erasureExact_needs_realReadsReal` | 1.D counterexample for `hR` | propext | `8f16d2a16be1190af315561fc4f37454f7a3ed3121320b68b66113385dccdca8` | `d010b8015e3e13e6dfbbc99637413cd18ae3a10d02cfb7a49ea4e8243d4d5664` | 89 |
| `erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom` | 1.D result | Classical.choice, Quot.sound, propext | `ad3ce9cb654676c4b47f68abd8b51f70e8913c4e27f6ba64d85dd16d84726c56` | `d18a9a6bfedb257040282af19ccf215d42cc2ab65f45738230862a95b7f98759` | 91 |
| `ghostDivergence_breaks_erasure` | 2.3 result | propext | `bb002060e233065bf06b6e5e917a68e1e504346a6e49a9a7703690cc8a196adc` | `639630fbea741e0329abf40a60a777cf7800558fa3edadb2861342d4effa109a` | 95 |
| `ghostFailure_breaks_erasure` | 2.4 result | propext | `3651c35ac1d91c282b46bc09f0696875ba778f81dfd1a4826a7bb12554919443` | `1fdb59803d7e60fe3df139307690fdb796daffb9494af4cf37ecfbfff8d849c9` | 94 |
| `ghostSpinOnX_ghostToRealNI_not_erasureExact` | 4.B result | propext | `3a2406adb8f27be7bbd21db51b0d6940bf9b39d50a0ad7348e48b590e17a5e02` | `2ef7958974bc162e9541831ef140fa42311cd02e24276223216ac3702f5401e5` | 87 |
| `ghostThenRealFail_satisfies_erasure_hypotheses` | 1.C non-vacuity | Quot.sound, propext | `8cdefe6a6724594b03edb4c770c44ce7487a60e5a6955b2f3f95c7bdfaed0e6f` | `548b3c0fced2e345aa305fb344c5f286d6cea76767022c07e37b65f56a60695b` | 87 |
| `ghostThenSpin_satisfies_erasure_hypotheses` | 1.B non-vacuity | Quot.sound, propext | `5912a4630bde06ac123f2fa7f4e6eb482afbbff7bb8c16478e44c55c3c6d8447` | `cb78e3d91f7f49291581b9772c98c54aa5a0a3888d7b48e9c8bfbd7b443fc502` | 88 |
| `ghostToRealNI_abortInsensitive_ghostSpinOnG` | 4.F positive control | none | `cc20efdb5ada08c02d63875153703497fc5f9897c98123cf969de5c05dbe2b1e` | `4d74eb7662c2c97cd5c197de4cd78c224c758a644b18b6b1620305bee61c3629` | 64 |
| `ghostToRealNI_abortInsensitive_needs_ghostWritesGhost` | 4.E counterexample for `hW` | Quot.sound, propext | `3b688214279d8f4711c8bad2eb508d9efced5eefca1256bf5343e78c34c6b234` | `69122929b5b92792553a5f70b5b1fd77910dabfc1b9595aba92fa884221e9e2e` | 74 |
| `ghostToRealNI_abortInsensitive_needs_realReadsReal` | 4.E counterexample for `hR` | Quot.sound, propext | `8c99fd82a43b10e8fbf5fab529bd8ea33f5784411e2e3d957eeb5e9db49800d7` | `f5ec61d4a70ca5c4336dc9b26e5de4fbad4822593aedea923b677ff3327e863a` | 74 |
| `ghostToRealNI_abortInsensitive_of_ghostWritesGhost_of_realReadsReal` | 4.E result | Classical.choice, Quot.sound, propext | `567b884b23389e2e12ffde89e3f0e4941209378f5a9747d7ead6bb7f5212a0a6` | `3cf33e54b13ee4f7cda3ef097ce4c704e41fadb180fc06ef3a1ae052c536e755` | 76 |
| `ghostToRealNI_needs_ghostNoDivergeFrom` | 4.D counterexample for `hT` | Quot.sound, propext | `48e9085e038f076cf3f94365568d5d6e1ffd4943983295cf4ddde28424ea35a9` | `56c5029bc53fecf6e1da20c4b65214b58d302e9af587b627772af8fd9e8c4980` | 89 |
| `ghostToRealNI_needs_ghostNoFailFrom` | 4.D counterexample for `hF` | Quot.sound, propext | `7e2eea79f2fc2b23c4556a2e6d51e14d401abed8d21f8d2cd3e50c4bb8a37593` | `c93313532fe09e8e068021a79b54a242eda76e1bdeaafb2408731163b2e18dfc` | 89 |
| `ghostToRealNI_needs_ghostWritesGhost` | 4.D counterexample for `hW` | Quot.sound, propext | `2391ef9e04e4fb0d51ec561337fa9c2b8ee7c2ba87fd06e1c22a9cd109032c4b` | `928531d6b567bb911adf7a75eb8b7af00da2168bd2d7c0c9937237bf63e7beac` | 87 |
| `ghostToRealNI_needs_realReadsReal` | 4.D counterexample for `hR` | Quot.sound, propext | `3e1ccc5f325da0b5866266adf5ebb5d0de9a4aeb721bf1337d10b810e3d42b0f` | `caabda01d8e9e9cd43911043ae7a2ff924e4346c1bbfdcc8ac600b3133efce8b` | 87 |
| `ghostToRealNI_not_sufficient_for_erasureExact` | 4.A counterexample for `ErasureAgrees P (for ⇐)`; 4.B result | Quot.sound, propext | `c8ca5add839da436c2aa2f9b11c892d581ef7b12628e4f672c0d5273c2b9e988` | `bd0a18ae5755d8842d922c2f962438385b31f7cdb9bb7ac698499262c186b6d5` | 77 |
| `ghostToRealNI_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom` | 4.D result | Classical.choice, Quot.sound, propext | `200c15579a2c04f062aa168bdc0d2823b3b3f1b29783ac52130ceaa35f0f32ff` | `3aca17d2699a7d12652b9b6153c6c27ffe137c88839ede5511675d5d4a4c6c90` | 89 |
| `ghostWriteToReal_breaks_erasure` | 2.1 result | Quot.sound, propext | `2111c1d939eeacfad65fa8b1e56fe7a96af8b9d8d49feea755408bc5ae06b105` | `b4dbaddc4be001115dec7474d07d60f8bea7c82b8de114c2f9b06e405b3ac038` | 90 |
| `ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI` | 4.F result | Quot.sound, propext | `2efcad11666124bcfdc916d8bb5ee9c0ba8fdcfb6fbbc6543b81b9f813aca9ee` | `bf0dae4337eef2fbdff27333190d778fa3c80db4e6cce727fe4dc66d6cc17d30` | 92 |
| `implicitFlow_breaks_erasure` | 2.2 result | propext | `6c987b6e5b5558419f99122e98bb00f7b1bfc825163bd9cb14536c3812f8c407` | `899a1f0e373635145af3a50814b244b95b9faf67e25c830f69dca9714e252e18` | 92 |
| `loopDemo_satisfies_global_erasure_hypotheses` | 1.D non-vacuity | Quot.sound, propext | `13d473758c002087b4ff98f4bbd173b5cb6f7b842b60e2879758b12f9941398d` | `2becfeaa68282ade26d0ea697e7015dfceefacfa2c15e0c568b42aa91a9780ad` | 83 |
| `pcGhostPassingAssert_erasureExact` | 2.4 positive control | propext | `993a0a7dbf9d2a370c9167fb2adce96a49b85eeef0de3c9ac1e8000351420fb1` | `7615d28e045283430e3ef437c9452c936d9c875c9f927d9708aa7ca7f476c8ac` | 75 |
| `pcGhostTerminatingLoop_erasureExact` | 2.3 positive control | propext | `a9a756ead0a158474f2a014aaed44a31e660f9c2062dc6b1f9dedfcb2daebe01` | `7f34dc5aa2270cb4b0b830fa014c07105da39787c7f04505c1355f4a7d29528a` | 75 |
| `pcGhostWritesGhost_erasureExact` | 2.1 positive control; 4.A non-vacuity; 4.B positive control | Quot.sound, propext | `f3d1db0fff276dce3707348d29a58beac25ccbac060a1aea998da8eb3dc63d6e` | `be41e4b04a30c251c41f27622944a6c6f56f85965e19be75cbde6bb55118f2cb` | 76 |
| `pcGhostWritesGhost_realReadsReal_erasureAgrees_erasureExact` | 4.C positive control; 4.G non-vacuity | Quot.sound, propext | `f75155044cafff78074fe19ad7b311a02bd63cbc2488c2a8150c7fa5f23f85ca` | `571f5de3dcd0f974f51fb4f9e4b82642cbc60ab50aee96a8dac9194ad5a44167` | 82 |
| `pcRealBranch_erasureExact` | 2.2 positive control | Quot.sound, propext | `9997d892f3d716ee968d3148181223164b7b5a545609611910a50532b52bf61e` | `f027c3fb56ac66edc75a1163ac38c61e0e045f41f0af9c2ca81a5fe3bf3bb139` | 77 |
| `pcRealDataFlow_erasureExact` | 2.2 positive control | Quot.sound, propext | `f76a2ce56aadf859409d4a30ca41bc39032e6f2e9b190593363d2e395f1f653b` | `ed285390a56d365d9cd50eb62a0f521b4074c6a22b45e571ca3d108ecb82cf0f` | 78 |
| `safePartialTriple_erase_hypotheses_satisfiable` | 3.A non-vacuity | propext | `fcfb11dfdb31164a373adde0696850d8f957159a8b32709660deb84af5a9d54b` | `44c11dcfe8b0b6c79f725253c17c89f22a72052489e15bc6a730166a2c645f88` | 88 |
| `safePartialTriple_erase_needs_ghostNoDivergeFrom` | 3.A counterexample for `hT` | propext | `dc2da37f59548da87d0dc74e5b63c8608a7afaa60a18c58645be368c9f9b8759` | `71431a94ab32cde8518e87793b4708d8f6d85548cc4a5e408ab821a4c1732506` | 88 |
| `safePartialTriple_erase_needs_ghostWritesGhost` | 3.A counterexample for `hW` | propext | `05b694424302fb0375b8bf9f4e47f69a65140b90460a006f34a7e7f0d3b01fca` | `3d4939de35ac77ffee1341e3dc7db32eff548cfc99e78653e295b36dd7aa0f40` | 83 |
| `safePartialTriple_erase_needs_realReadsReal` | 3.A counterexample for `hR` | propext | `54a648011ce1f712fc95ff03113448602fc53142b09eb6905218eb55d5e6466d` | `5de7f6ec4ed3cd2976e0b43a983ce18efdc1af726dd1273ff57e8e6b7fb96b0c` | 84 |
| `safePartialTriple_erase_needs_safePartialTriple` | 3.A counterexample for `h` | none | `480bf3fc1809cddc3acd22e31ad81dfc25d2ef27762e257fba3b89bbd8827304` | `137e8fc71eaa5833105673d107429b86188437cb66382374984dc189572b2cd4` | 86 |
| `safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom` | 3.A result | Classical.choice, Quot.sound, propext | `2c558c78b68583a0dac03c5272a97d7d0d39bb239c99da664f3ffdd83dbc93bc` | `13248c5e687bfec844431eebc70a54853bf66c23a3d8f0a11831ea719103fdae` | 84 |
| `safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom` | 3.A result | Classical.choice, Quot.sound, propext | `99469f3aa6b4f7b6db8c927b1dc474bd3c6cc51ef700d2598aaa8dd833a75717` | `13248c5e687bfec844431eebc70a54853bf66c23a3d8f0a11831ea719103fdae` | 84 |
| `totalTriple_erase_hypotheses_satisfiable` | 3.B non-vacuity | none | `7a4bfb5c5109039331e6ed7b2e66197c41258870e83dbc253548be3603756b80` | `aa314b1c1196cdfb1e7756c0dcb67ebd6a31ee5c1c2502e3e04c6c2e2c01aef3` | 82 |
| `totalTriple_erase_needs_ghostWritesGhost` | 3.B counterexample for `hW` | propext | `300a9968570395da872aa3b517b9967463af5c7abf30371c62c413cf6fa56de2` | `059ac6ea7b86c7aece91537dad0b8bf3ea97b86b1b46fe6144dc8cf0d54cc7cb` | 77 |
| `totalTriple_erase_needs_realReadsReal` | 3.B counterexample for `hR` | propext | `f4970e37946fb9b2470bf55b84680f5b3f2b36602ce132cf266f5ff4adcb3b48` | `3a2dbd577d86c745d20a8e5ef392545e8cbcef3ae8bb5e62d6da83921f6f5146` | 78 |
| `totalTriple_erase_needs_totalTriple` | 3.B counterexample for `h` | none | `def65710dc1dc2e9b6c113e17cb07dc4e65b61a952555722270fe3f5c5692927` | `ac615b4882e0791303ee6b697d2fc6585aa2799c82dbeb8a4bd97ada765d4b2f` | 80 |
| `totalTriple_erase_of_ghostWritesGhost_of_realReadsReal` | 3.B result | Classical.choice, Quot.sound, propext | `4ff7f906897ab3bf09ac3125bb5a327d1ce8c39a882883e5015d4cec1d6a6829` | `454e038d8c24436d70d5b8ed96470d4e6adacbd4cd05c5faa46fc62b48ae31fe` | 78 |
| `weakPartialTriple_erase_hypotheses_satisfiable` | 3.D non-vacuity | propext | `9cc844f222785540f29355dfa680e2fa5b52a5b62a6878b1d0ff295aae0b3456` | `69fa88380c60258b537bffc6da299bc2ee0681e42c9f120c8c596f553429c8b0` | 89 |
| `weakPartialTriple_erase_needs_ghostNoDivergeFrom` | 3.D counterexample for `hG` | propext | `6bbe1109643c4583e45f0ff431aae7254564ba23df05147289e2a1895da3ac97` | `ca8a0601a8cada7997d128f4fee99f9a0c685f004d16d5c41aeffed11cbde927` | 87 |
| `weakPartialTriple_erase_needs_ghostNoFailFrom` | 3.D counterexample for `hG` | propext | `4db42736bf5ba5a53ac310f8a817c08466fba03e6eb601760fed1a8d2c3688ef` | `a30e1ccc4f0f9bc8cf6aac29ab4c96a85dabc2c05ff551a31195358582c8f307` | 86 |
| `weakPartialTriple_erase_needs_ghostWritesGhost` | 3.D counterexample for `hW` | propext | `535be9f132ce2eccf258017ec648381241e8716fb2b95b93df4ca5298bac308a` | `9add293b20f2779c0e836febc4c14292a13e9be8195797881ed0ae4dc93d2e7a` | 84 |
| `weakPartialTriple_erase_needs_realReadsReal` | 3.D counterexample for `hR` | propext | `c4222e27c0bbced524d53bea5ad8f9cf31cda0dbb2444b07c9f0d1a9db821896` | `365bbe4d0b7f322a3bdd603deab7e6c29af2bc170a0ebb4ad864b54aba295100` | 85 |
| `weakPartialTriple_erase_needs_weakPartialTriple` | 3.D counterexample for `h` | none | `f5bba6e7d3808d471d46b703cc15ec938ab23baf826ae5198e0d542bdd9242ef` | `34b2c69a646252aa658e01f9105df81680615d9c6da4b791aeaf1802e698f535` | 87 |
| `weakPartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom_ghostNoFailFrom` | 3.D result | Classical.choice, Quot.sound, propext | `77b4cf52e98d740a49c4fcd24e7f791a53eef5792176b135daba98e23ae651d3` | `3554bff01cffe92fbc98490434df2378631c40c25674d04b3cc5634b71d14261` | 85 |

### Primary sources

Records were checked on 2026-11-20 at the places stated in each entry. Where only a record or abstract was checked, the entry says so, and the cards cite the source only for what was checked.

- **[SF]** C. Hriţcu, Y. Kim (B. C. Pierce, ed.). Security Foundations. Software Foundations, Volume 7, Version 1.2, electronic textbook, 2026, https://softwarefoundations.cis.upenn.edu/secf-1.2/ (version-pinned release URL; its title page reads 'Version 1.2 (2026-08-24 10:14, Rocq 9.0.0 or later)'; on 2026-11-20 the moving alias secf-current/ served the same text for the title page and the chapters StaticIFC and Noninterference; citation data from its Preface; chapters StaticIFC and Noninterference checked at the source, proofs of the theorems named here end in Qed). Rocq mechanization for the Imp language: pub_slice replaces assignments to secret variables and secret-guarded conditionals and loops by skip; pub_slice_fwd_correct (for programs typed with the noninterference typing, a terminating run of c from s is matched by a terminating run of the slice from any publicly equivalent t, ending in publicly equivalent states); pub_slice_bwd_correct and pub_slice_tsni (the converse correspondence under a termination-sensitive typing); pub_slice_secure_com2_incorrect (a noninterferent program whose slice is not correct); cf_well_typed_noninterferent and ni_well_typed_noninterferent (termination-insensitive noninterference of well-typed programs); ts_well_typed_tsni (termination-sensitive noninterference); termination_leak, tini_secure_termination_leak, tsni_insecure_termination_leak (a secret-guarded diverging loop is termination-insensitively but not termination-sensitively secure). These theorems are stated over terminating evaluations and have no failure outcome; ghost code is modelled there as the secret part of a labelled program. *(cited by 1.A, 1.B, 1.C, 1.D, 4.A, 4.B, 4.D, 4.E, 4.F, 4.G)*
- **[FGP14]** J.-C. Filliâtre, L. Gondelman, A. Paskevich. The Spirit of Ghost Code. In: Computer Aided Verification (CAV 2014), LNCS 8559, Springer, pp. 1-16. DOI 10.1007/978-3-319-08867-9_1; HAL hal-00873187. Verified at the publisher and HAL: the abstract states that ghost data cannot participate in regular computations and ghost code cannot mutate regular data or diverge, and that ghost-code erasure is defined for an ML-style language with mutable state and proved safe using bisimulation. *(cited by 1.A, 1.B, 1.C, 1.D, 2.1, 2.2, 2.3, 2.4, 3.A, 3.B, 3.D, 4.A, 4.B, 4.C)*
- **[FGP16]** J.-C. Filliâtre, L. Gondelman, A. Paskevich. The Spirit of Ghost Code. Formal Methods in System Design 48(3):152-174, 2016. DOI 10.1007/s10703-016-0243-x; HAL hal-01396864 (extended version; same abstract claims, verified at HAL). *(cited by 1.A, 1.B, 1.C, 1.D, 3.A, 3.B, 3.D)*
- **[BvW98]** R.-J. Back, J. von Wright. Refinement Calculus: A Systematic Introduction. Springer, 1998. DOI 10.1007/978-1-4612-1674-2 (bibliographic data verified at the publisher). Source of the refinement order in which abort is bottom, used here for RefinesUpTo with abortBot. *(cited by 1.A)*
- **[Dafny]** Dafny Reference Manual, v4.11.0 release snapshot, https://dafny.org/v4.11.0/DafnyRef/DafnyRef. Section 12.3 'Ghost Inference': assert statements, calls to ghost methods and lemmas, if/while statements whose condition contains ghost expressions (together with their bodies), and assignments all of whose updated variables are ghost are ghost statements; expect statements are always non-ghost; updating a non-ghost variable in a ghost context is an error. Section 7.1.3 'Decreases Clause': loops and compiled methods, but not functions and not ghost methods (including lemmas), can be declared possibly non-terminating with 'decreases *'. Section 1: specifications and ghost constructs are used only during verification and are omitted from executable code. *(cited by 1.B, 1.C, 1.D, 2.1, 2.2, 2.3, 2.4)*
- **[Why3]** Why3 1.9.0 documentation (https://www.why3.org/doc/; these URLs track the current release, pages observed as 'Why3 1.9.0 documentation'). Chapter 6 'The WhyML Language Reference' (syntaxref.html; extracted text SHA-256 3bd49df651ad5675c198b32ebde82a3118722ecb8433fb12deae604665bda601), section 6.4.1 'Ghost expressions': ghost code is removed from the final code intended for execution, and thus cannot affect the computation of the program results nor the content of the observable memory; section 6.5.5 'Function declarations': program functions marked partial can produce observable effects unaccounted by their specification, and thus cannot be used in ghost code. Chapter 8 'The VC Generators' (vcgen.html; extracted text SHA-256 27a03509f0da8995d6e34942d8f67cf294c1f3a6805937a90efcf19e410f2ecf), section 8.2.2 'Ignoring checks for termination': by default Why3 generates VCs for the termination of loops and recursive calls; section 8.4 'Lemma Functions': a lemma function must have no side effects, be provably terminating, and return unit. *(cited by 1.B, 1.C, 1.D, 2.3, 3.A, 3.D)*
- **[OG76]** S. Owicki, D. Gries. An axiomatic proof technique for parallel programs I. Acta Informatica 6:319-340, 1976. DOI 10.1007/BF00268134 (bibliographic data and summary verified at the publisher: Hoare's partial-correctness system extended to parallel programs). Cited as a standard early use of auxiliary variables in program proofs; the wording of its auxiliary-variable rule was not checked at the source. It is not the origin of auxiliary variables: its reference list includes M. Clint, Program proving: Coroutines, Acta Informatica 2:50-63, 1973, DOI 10.1007/BF00571463, and Jones (2010) cites P. Lucas, Two constructive realizations of the block concept and their equivalence, IBM Laboratory Vienna TR 25.085, 1968 (both reference lists verified at the publisher; the earlier works themselves were not read). *(cited by 3.A, 3.B, 3.D)*
- **[Jones10]** C. B. Jones. The Role of Auxiliary Variables in the Formal Development of Concurrent Programs. In: A. W. Roscoe, C. B. Jones, K. R. Wood (eds.), Reflections on the Work of C.A.R. Hoare, Springer, London, 2010, pp. 167-187. DOI 10.1007/978-1-84882-912-1_8 (abstract verified at the publisher: auxiliary variables are useful but can undermine compositionality; the chapter recommends constraints on their use). *(cited by 3.A)*
- **[SM03]** A. Sabelfeld, A. C. Myers. Language-based information-flow security. IEEE Journal on Selected Areas in Communications 21(1):5-19, 2003. DOI 10.1109/JSAC.2002.806121 (bibliographic data verified at dblp; cited as the standard survey for the termination-insensitive versus termination-sensitive distinction; its content was not re-read at the source). *(cited by 4.A, 4.D, 4.E, 4.F, 4.G)*
- **[VIS96]** D. Volpano, C. Irvine, G. Smith. A Sound Type System for Secure Flow Analysis. Journal of Computer Security 4(2/3):167-188 (dblp; Crossref lists pp. 167-187), 1996. DOI 10.3233/JCS-1996-42-304 (bibliographic data verified at dblp and Crossref; publisher page not reachable). *(cited by 4.D, 4.E)*
- **[SW08]** G. Snelting, D. Wasserrab. A Correctness Proof for the Volpano/Smith Security Typing System. Archive of Formal Proofs, entry dated 2008-09-02, https://www.isa-afp.org/entries/VolpanoSmith.html (verified: for a while-language, typeability implies noninterference stated as: low-equivalent initial states lead to low-equivalent final states, i.e. a statement about terminating executions). *(cited by 4.E)*
- **[VS97]** D. Volpano, G. Smith. Eliminating Covert Flows with Minimum Typings. Proc. 10th IEEE Computer Security Foundations Workshop (CSFW 1997), pp. 156-169 (dblp; IEEE Xplore lists pp. 156-168). DOI 10.1109/CSFW.1997.596807. Abstract verified at IEEE Xplore: a type system that eliminates two kinds of covert flows in an imperative language, one arising from nontermination and one from partial operations that raise exceptions, by limiting the sources of nontermination to constructs with minimum typings; a mutual progress theorem states that no two executions of a well-typed program can be distinguished on the basis of nontermination versus abnormal termination. The body of the paper was not read. *(cited by 4.F)*

Further sources mentioned only as context, not read: M. Clint, *Program proving: Coroutines*, Acta
Informatica 2:50-63, 1973, DOI 10.1007/BF00571463, and P. Lucas, *Two constructive realizations of
the block concept and their equivalence*, IBM Laboratory Vienna TR 25.085, 1968 (both appear in the
reference lists of [OG76] and [Jones10], checked at the publisher). Novelty: no result is claimed
novel (no T3 tier).

### Support material

- `lean/` — the Lake project (`lakefile.toml`, `lean-toolchain`, `ToyGhost.lean`, `ToyGhost/*.lean`),
  plus `lean/RevalidationAudit.lean`, which is outside the library target.
- `results.json` — the machine-readable cards (one object per result).
- `audit/axioms.json`, `audit/statements.json` — the recorded axiom sets and hashes.
- `support/revalidate.py` — the revalidation program described below.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and
`python3`. Nothing else is needed; the commands below do not modify the package.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, runs `lake build`, rejects `sorry`, `admit`,
`native_decide` and `axiom` declarations in the Lean sources, computes the axioms of every
declaration of the `ToyGhost` modules with `Lean.collectAxioms` (allowing only `propext`,
`Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by
`results.json` or recorded in `audit/statements.json`, the statement hash (SHA-256 of the `repr` of
the type) and the closure hash (SHA-256 of the sorted, newline-joined closure entries described
under **Evidence**), comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits
with status 0 iff every check passes.

**Manual check with the package's own audit file.** Equivalent, step by step:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/toyghost_audit.txt
grep -c '^AXIOMS ' /tmp/toyghost_audit.txt      # number of declarations audited
cd ..
python3 - <<'EOF'
import hashlib, json
rec = json.load(open('audit/statements.json'))['statements']
axr = json.load(open('audit/axioms.json'))['declarations']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = 0
for line in open('/tmp/toyghost_audit.txt'):
    if line.startswith('AXIOMS '):
        d = json.loads(line[len('AXIOMS '):])
        if set(d['axioms']) - allowed or sorted(d['axioms']) != axr.get(d['name']):
            bad += 1; print('axioms differ:', d['name'], d['axioms'])
    elif line.startswith('STATEMENT '):
        d = json.loads(line[len('STATEMENT '):])
        if d.get('missing'):
            bad += 1; print('missing:', d['name']); continue
        got = {'statement_sha256': hashlib.sha256(d['type_repr'].encode()).hexdigest(),
               'closure_sha256': hashlib.sha256('\n'.join(d['closure']).encode()).hexdigest(),
               'closure_size': len(d['closure'])}
        if rec.get(d['name']) != got:
            bad += 1; print('hash differs:', d['name'])
print('OK' if bad == 0 else f'{bad} differences')
EOF
```

`RevalidationAudit.lean` prints one `AXIOMS` line per package declaration and one `STATEMENT` line,
with the exact hashed text, per Lean name referenced by `results.json`; its header comment
describes the format.

**What a passing check establishes.** That the theorems named in this report are kernel-checked
under the pinned toolchain with the standard axioms only, and that their statements and every
definition they depend on are byte-for-byte (at the level of Lean `repr`) the ones recorded here.
It does not re-establish any modeling-bridge claim. If a definition changes, the closure hashes of
every statement that reaches it change, and the cards of those results must be re-read; if only a
proof changes, the hashes stay the same.
