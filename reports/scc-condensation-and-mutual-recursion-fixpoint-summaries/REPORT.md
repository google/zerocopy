# SCC condensation and mutual-recursion fixpoint summaries: a Lean 4 toy model of bottom-up solving, its failure modes, certificates, and termination measures

## Summary

This package states and kernel-checks, in Lean 4 without Mathlib, twenty results about splitting a whole-program system of recursive summary equations along the strongly connected components (SCCs) of its call graph. Thirteen are general theorems and characterizations (backed by nineteen Lean theorems); seven are concrete counterexample results (backed by eight Lean theorems) that pin down what goes wrong when a hypothesis is violated. The model is a finite call graph `E : Graph n` on the functions `Fin n`, a block map `comp : Fin n → Fin k` (a candidate SCC decomposition), a list `order` of blocks, and per-function summaries that are bit vectors `Fin m → Bool`, ordered pointwise (`Le`); a transfer `F` maps a whole summary vector to a new one. Monotonicity (`Monotone F`) and call-locality (`RespectsCalls E F`: the equation of `f` reads only the summaries of the callees of `f`) are separate, named hypotheses wherever they are used. `bottomUpLfp` / `bottomUpGfp` process `order` once, solving each listed block by `fuel` rounds of Kleene iteration of its own equations from the empty (full) set while every other summary is held fixed. Every `tight` hypothesis of every general result has a proved counterexample in which all other hypotheses hold and the conclusion fails, and every result has a proved non-vacuity instance. No result is claimed novel: eighteen are re-derivations (`T0`) and two are folklore made precise (`T1`).

- **scc-check** (`checkScc_eq_true_iff_isSccDecomp`, `reachFrom_eq_true_iff_reach_of_pred_le`). For every call graph `E` and block map `comp`, the Boolean checker `checkScc E comp` returns `true` exactly when `comp` is a valid SCC decomposition (same block iff mutually reachable); the fuel-bounded closure `reachFrom E f fuel` it is built from computes reachability exactly whenever `fuel ≥ n - 1`, and can miss reachable functions with less fuel.
- **scc-char** (`isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic`). A block map is a valid SCC decomposition exactly when (a) any two functions in the same block are mutually reachable in the whole graph and (b) the condensation (blocks, with an edge `c → d` for every call from block `c` into a different block `d`) is acyclic; neither conjunct can be dropped.
- **topo-order** (`condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order`). The condensation is acyclic exactly when some duplicate-free list of blocks contains the block of every function and is callees-first (for every call between different blocks, both blocks occur and the callee's block occurs strictly earlier).
- **kleene-bound** (`iter_bot_isLeastFixpoint_of_monotone_of_height_le`, `iter_top_isGreatestFixpoint_of_monotone_of_height_le`). For a monotone transfer on summary vectors with `n` functions and `m` bits per function, at least `n * m` rounds of iteration from the all-false vector give the least fixpoint and at least `n * m` rounds from the all-true vector give the greatest fixpoint; monotonicity and the round bound are each necessary.
- **bottomup-lfp** (`bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`). If `F` is monotone and call-local, then for every block map (not necessarily an SCC decomposition) and every covering callees-first list of blocks, single-pass bottom-up with inner fuel at least `n * m`, started from all-false, returns the global least fixpoint of `F`; each of these five hypotheses is necessary.
- **bottomup-gfp** (`bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`). Under the same five hypotheses, single-pass bottom-up with greatest inner fixpoints, started from all-true, returns the global greatest fixpoint of `F`; each hypothesis is necessary.
- **bottomup-one-sided** (`bottomUpLfp_le_of_monotone_of_prefixpoint`, `le_bottomUpGfp_of_monotone_of_postfixpoint`). For monotone `F`, the single-pass least computation lies below every prefixpoint of `F` (in particular below the least fixpoint) for every block map, every list of blocks and every fuel, and the single-pass greatest computation lies above every postfixpoint (in particular above the greatest fixpoint): an unchecked decomposition or order can only lose facts in the least case and only gain facts in the greatest case.
- **bottomup-mixed** (`bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`, `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint`). Under the hypotheses of `bottomup-lfp`, for every per-block choice of least or greatest inner fixpoint and every start vector, single-pass bottom-up computes the unique vector in which each block is the least (resp. greatest) fixpoint of its own equations with all other blocks frozen at their values in that vector (`HierSolution`); every such vector is a fixpoint of `F` lying between the least and the greatest fixpoint.
- **mixed-neither** (`mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp`, `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp`). On a two-function instance with a valid SCC decomposition, a callees-first order and enough fuel, solving the callee block with its least fixpoint and the caller block with its greatest (and, for a second transfer, the reverse) yields a fixpoint that is neither the least nor the greatest fixpoint of the whole system.
- **merge-convex** (`convex_merge_not_scc_still_lfp_and_gfp`). Merging two functions that are not mutually reachable (along the path `0 → 1 → 2`) gives a block map that is not an SCC decomposition, yet it still admits a covering callees-first order with a genuine cross-block call, and single-pass bottom-up over it returns the global least and greatest fixpoints of two monotone call-local transfers.
- **merge-nonconvex** (`nonconvex_merge_wrong_in_both_orders`). Merging the endpoints of the path `0 → 1 → 2` admits no callees-first order, and single-pass bottom-up then returns a wrong least fixpoint and a wrong greatest fixpoint in both duplicate-free orders, while the SCC decomposition in callees-first order is right (positive control: the order `[0, 1, 0]`, which solves the merged block twice, is right).
- **split-scc** (`split_scc_wrong_lfp_and_gfp_in_both_orders`). Splitting the 2-cycle `0 ⇄ 1` into singleton blocks admits no callees-first order, and with two bits per function single-pass bottom-up then returns a wrong least fixpoint and a wrong greatest fixpoint in both duplicate-free orders, while the one-block SCC decomposition is right (positive control: the order `[0, 1, 0]` is right).
- **caller-first** (`valid_scc_caller_first_order_wrong_lfp_and_gfp`). A valid SCC decomposition of `0 → 1` processed in the covering but caller-first order `[0, 1]` gives a wrong least and a wrong greatest fixpoint for monotone call-local transfers, while the callees-first order `[1, 0]` is right (positive control: `[0, 1, 0]` is right).
- **lex-iff** (`lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks`, `terminates_of_lexDecreasing`). If the block rank is injective on the blocks actually used, the lexicographic measure that maps a configuration `(f, x)` to `(rank (comp f), inner f x)` (the rank of the block of `f`, then the inner measure of `f` at `x`) decreases along every configuration-level call exactly when every intra-block call decreases the inner measure and every cross-block call goes to a block of strictly smaller rank; and whenever the lexicographic measure decreases along every call, every call chain is finite (no injectivity needed).
- **termination-intra** (`terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease`). If the condensation of `E` under `comp` is acyclic and every configuration-level call follows an edge of `E`, then strict decrease of an inner measure on intra-block calls alone implies that every call chain is finite; no block rank has to be supplied; each of the three hypotheses is necessary.
- **inner-alone** (`inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout`). For a valid SCC decomposition and a call relation with unbounded cross-block fan-out, the inner measure decreases on every intra-block call but not on the cross-block calls, and no measure from configurations into `Nat` decreases along every call, yet the relation terminates and the lexicographic measure `(block rank, state)` decreases (positive control: with bounded fan-out a `Nat` measure exists).
- **prefix-postfix-sound** (`le_of_monotone_of_isLeastFixpoint_of_prefixpoint`, `le_of_monotone_of_isGreatestFixpoint_of_postfixpoint`). For monotone `F`, any untrusted vector `σ` with `F σ ≤ σ` (a prefixpoint) lies above the least fixpoint, and any `σ` with `σ ≤ F σ` (a postfixpoint) lies below the greatest fixpoint; each of the three hypotheses of each half is necessary.
- **checks-not-exact** (`prefix_and_postfix_checks_pass_but_not_extremal`). For the identity equation on one self-recursive function with one bit, both the all-true and the all-false vector pass both the prefixpoint and the postfixpoint check, yet all-true is not the least fixpoint and all-false is not the greatest: one-sided checks do not certify extremality.
- **ranked-cert** (`isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified`). For monotone `F`, a prefixpoint `σ` together with a ranking of its bits in which every set bit is produced by `F` applied to the strictly lower-ranked part of `σ` is exactly the least fixpoint of `F`; each of the three hypotheses is necessary.
- **ranked-cert-complete** (`prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint`). For monotone `F`, the least fixpoint always has such a certificate: it is a prefixpoint, it is ranked-justified by `kleeneRank F` (the first Kleene round at which each bit appears), and every rank is below `n * m`; each of the two hypotheses is necessary.

The single most important limitation: the bottom-up theorems require a *covering callees-first order* (`Covers` and `CalleesFirst`), not a valid SCC decomposition. An SCC decomposition is neither sufficient (a valid decomposition in the wrong order fails, `caller-first`) nor necessary (a non-SCC merge that keeps the condensation acyclic works, `merge-convex`); and when blocks use different signs (least for some, greatest for others), the result is the coordinatewise block-extremal solution, which in general is neither the least nor the greatest fixpoint (`mixed-neither`). Everything is proved for a toy model: finite powerset summaries of fixed width, an explicit finite call graph, and a single pass with a fixed inner fuel. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real summary-based interprocedural analyses, SCC-ordered equation solvers, or termination provers for mutually recursive definitions (the `derived (modeling bridge)` lines argue applications separately). What each result does **not** show is listed first under **Boundaries** (and in the `non_claims` field of each card in `results.json`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** The definitions capture the shape of three engineering practices that split recursive definitions along the strongly connected components of a call graph:

1. **SCC-structured fixpoint solving of summary equations**, as in summary-based interprocedural analyses that compute one summary per function bottom-up over the call graph, and in solvers that order a system of monotone equations by the SCCs of its dependency graph (Bourdoncle 1993 for nested-SCC iteration strategies; Cleaveland and Steffen 1993 and Mader 1997 for block-wise solving of least/greatest fixpoint equation blocks).
2. **Checking untrusted results** instead of recomputing them: an SCC decomposition or processing order supplied by an untrusted producer, and summary vectors supplied without a proof of extremality (prefixpoint/postfixpoint checks, ranking certificates).
3. **Termination of mutual recursion** by a lexicographic measure (rank of the SCC, measure inside the SCC), as in termination provers for mutually recursive function definitions and in dependency-graph methods for term rewriting.

It does not model any particular analyzer, compiler, proof assistant or termination prover. The known gaps:

- **Call graphs** are explicit finite Boolean relations `Graph n := Fin n → Fin n → Bool` over a fixed set of functions. Indirect calls, higher-order functions, dynamic linking and call-graph construction are not modeled; whenever a result is applied, the given graph is assumed to over-approximate every call (`RespectsCalls` on the equation side, `CallsInGraph` on the termination side).
- **Summaries** are elements of the finite powerset lattice `Fin n → (Fin m → Bool)` ordered pointwise (`Le`), of height `n * m`. There are no infinite-height domains, no widening, no context-sensitive summaries (one value per function, not per calling context or per input), and no relational summaries beyond what `m` bits can encode. The lattice is fixed: results about general complete lattices are cited as prior art but not proved here.
- **Transfers** are arbitrary total functions `Summ n m → Summ n m` on whole summary vectors; `Monotone` and `RespectsCalls` are separate hypotheses. The two fixture families `disjT` (seed bits plus unary-premise copy rules; join-preserving) and `conjT` (allowed bits intersected with dependency bits) are special cases used only by examples and counterexamples; no theorem assumes them.
- **The algorithm** is `bottomUp`: a single pass over a given list of blocks, one block solve per list entry, each by exactly `fuel` rounds of Kleene iteration of the block operator from the empty or full set. Worklist solving, chaotic or asynchronous iteration, incremental re-analysis, iteration to stability and widening are not modeled, and no complexity bound is claimed. No SCC algorithm (Tarjan, Kosaraju, Gabow) is verified; `checkScc` is a specification-level checker that recomputes reachability for every ordered pair of functions.
- **Mixed signs** (least for some blocks, greatest for others) are interpreted by coordinatewise block-extremality (`HierSolution`). This coincides with nested-substitution semantics of Boolean or fixpoint equation systems only in the absence of cyclic dependencies between blocks of different signs, which `CalleesFirst` and `RespectsCalls` rule out; alternating fixpoints (modal mu-calculus, parity games) are not covered.
- **Termination** is stated for an abstract configuration-level call relation `Calls n S := Fin n × S → Fin n × S → Prop` (function, argument state) with `Nat`-valued inner measures and `Nat`-valued block ranks; `Terminates C` means every configuration is accessible for the converse of `C` (no infinite call chain). Program semantics, evaluation order, nested recursion and non-`Nat` measures are not modeled.
- **Universe and logic.** State types `S` in the termination part are in `Type` (universe level 0). Several proofs are classical (`Classical.choice` appears in some axiom sets). The summary-level operations (`bottomUp`, `checkScc`, `kleeneRank` and the fixture transfers) are computable, and most concrete instances are proved by kernel evaluation (`decide`).
- **Fixtures** are graphs on one to three functions with one or two bits per function; see the fixture table under **Findings**.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib, no `Std` import, no Lake dependencies. The Lake project is `lean/` (library root `Toy`, namespace `Toy.Scc`, modules `Graph`, `Lattice`, `BottomUp`, `Decomp`, `Fixpoint`, `Transfer`, `Termination`, plus `Checks`, which re-derives each dropped hypothesis from its tightness counterexample, and `Audit`, a build-time axiom audit). The results were checked only under this toolchain; behaviour under other Lean versions was not examined.

**Relationship of the subjects.** The Lean toolchain is the checker of every theorem. The papers listed in `REPORT.json` are prior-art sources for the known results restated here; the Lean statements are restatements in this package's vocabulary (finite powerset summaries, explicit block maps and orders), not mechanizations of the papers' own formal systems.

**Relationship to the order-theoretic core of abstract interpretation.** This package does not formalize the order-theoretic core of abstract interpretation for a single transformer (Galois connections, best abstract transformers, transfer of abstract post-fixpoints to concrete least fixpoints, Kleene iteration under an abstract height bound, widening). It starts where that core stops: it takes a monotone transfer on a finite powerset lattice as given (for example, an abstract transformer whose soundness has been established separately) and asks how the resulting whole-program equation system may be split along call-graph SCCs, solved block by block, checked without recomputation, and accompanied by a termination argument. It depends on no other formalization. In particular, `kleene-bound` here is a statement about the concrete powerset lattice of `n * m` bits (counting set bits), not an instance of a general Kleene theorem for an arbitrary order of bounded height; and nothing here concerns abstraction, concretization or widening.

Basis: derived (modeling bridge). Applying a result to a real system requires checking that the system's summary domain, equations, call graph and solving strategy instantiate these definitions: summaries in a finite powerset lattice ordered by inclusion (or an encoding of a finite lattice into bits that preserves the order used by the equations); a monotone transfer; a call graph that over-approximates every read of a summary (`RespectsCalls`); a block map and order that satisfy `Covers` and `CalleesFirst`; and a per-block inner iteration of at least the lattice height (or iteration to stability, which the proofs show is reached by then). Each card under **Findings** states its own bridge.

## Findings

All theorem statements below are quoted verbatim from the Lean sources. Each quote is preceded by a comment `-- <file>:<first>-<last>` naming the quoted source lines, and runs from the keyword `theorem` (or from its doc comment, where one is shown) through the end of the statement; proofs are omitted. Every declaration is in the namespace `Toy.Scc`, which the quotes, like the sources, do not write. Implicit arguments that the statement fixes appear as the source writes them, for example `Covers (idComp (n := 2)) [1, 0]`. Definitions and fixtures are quoted from the sources in the same way, with their full bodies and their doc comments; anonymous examples are shown as in the source with their proofs elided, without a line reference. Every `Toy.Scc` declaration named anywhere in this report is defined or quoted in it (key definitions and fixtures in this section, definition examples under **Definition examples**, card theorems on the cards, and everything else under **Other declarations named in this report** at the end of this section). *Unfolded (prose)* blocks are hand-written elementary readings of the quoted statements, not Lean terms, in which `≤` on summary vectors is bitwise inclusion (`Le`).

The card fields **Plain claim**, hypothesis names and purposes, **Depth**, **Non-vacuity witness**, **Tier justification**, **Prior art** and **Design question** are reproduced verbatim from `results.json`; there, ASCII spellings such as `sigma`, `mu`, `nu`, `<=` and `->` stand for `σ`, `μ`, `ν`, `≤` and `→`.

### Key definitions

Lean source excerpts (doc comments included; the `Decidable` instances that accompany some propositions are omitted). `Relation.TransGen` (transitive closure), `List.idxOf`, `List.finRange` and `Acc` are from core Lean.

#### Call graphs, reachability and SCC decompositions (`Toy.Scc.Graph`)

```lean
-- lean/Toy/Scc/Graph.lean:39-41
/-- A finite call graph on the functions `Fin n`: `E f g = true` iff `f` contains
a call to `g`.  This models the (static) call graph of a whole program. -/
abbrev Graph (n : Nat) := Fin n → Fin n → Bool

-- lean/Toy/Scc/Graph.lean:43-47
/-- Reflexive-transitive reachability in the call graph: `Reach E f g` iff there is
a call chain (of length `≥ 0`) from `f` to `g`. -/
inductive Reach {n : Nat} (E : Graph n) : Fin n → Fin n → Prop
  | refl (f : Fin n) : Reach E f f
  | step {f g h : Fin n} : E f g = true → Reach E g h → Reach E f h

-- lean/Toy/Scc/Graph.lean:58-60
/-- A set of functions (as a Boolean predicate) closed under calls. -/
def ClosedUnder {n : Nat} (E : Graph n) (S : Fin n → Bool) : Prop :=
  ∀ x y, S x = true → E x y = true → S y = true

-- lean/Toy/Scc/Graph.lean:72-74
/-- One step of forward expansion of a set of reached functions. -/
def reachStep {n : Nat} (E : Graph n) (S : Fin n → Bool) : Fin n → Bool :=
  fun g => S g || (List.finRange n).any fun h => S h && E h g

-- lean/Toy/Scc/Graph.lean:76-80
/-- `reachFrom E f fuel` is the set of functions reachable from `f` by call chains
of length at most `fuel` (fuel-bounded closure). -/
def reachFrom {n : Nat} (E : Graph n) (f : Fin n) : Nat → Fin n → Bool
  | 0 => fun g => decide (g = f)
  | k + 1 => reachStep E (reachFrom E f k)

-- lean/Toy/Scc/Graph.lean:82-83
/-- Decidable reachability: the fuel-bounded closure with fuel `n`. -/
def reachB {n : Nat} (E : Graph n) (f g : Fin n) : Bool := reachFrom E f n g

-- lean/Toy/Scc/Graph.lean:125-130
/-- `comp : Fin n → Fin k` is a (valid) SCC decomposition of `E`: two functions lie in
the same block exactly when they are mutually reachable.  This is the textbook
definition of the partition into strongly connected components, with blocks named
by `Fin k` (block names need not all be used). -/
def IsSccDecomp {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ f g, comp f = comp g ↔ (Reach E f g ∧ Reach E g f)

-- lean/Toy/Scc/Graph.lean:132-135
/-- Every block is mutually reachable inside the whole graph ("no over-merging").
Reachability is taken in all of `E`, not in the subgraph induced by the block. -/
def BlocksMutuallyReachable {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ f g, comp f = comp g → Reach E f g ∧ Reach E g f

-- lean/Toy/Scc/Graph.lean:137-140
/-- An edge of the condensation: some call crosses from block `c` to a different
block `d`. -/
def CondEdge {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) (c d : Fin k) : Prop :=
  c ≠ d ∧ ∃ f g, comp f = c ∧ comp g = d ∧ E f g = true

-- lean/Toy/Scc/Graph.lean:142-145
/-- The condensation (the quotient graph on blocks, keeping only edges between
distinct blocks) has no cycle. -/
def CondensationAcyclic {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ c, ¬ Relation.TransGen (CondEdge E comp) c c

-- lean/Toy/Scc/Graph.lean:147-151
/-- The decidable SCC checker: compares block equality with mutual reachability as
computed by the fuel-bounded closure, for all pairs. -/
def checkScc {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Bool :=
  (List.finRange n).all fun f => (List.finRange n).all fun g =>
    decide (comp f = comp g) == (reachB E f g && reachB E g f)

-- lean/Toy/Scc/Graph.lean:193-197
/-- Position of a block in a processing order: the index of its first occurrence
(`List.idxOf`), and `order.length` if the block does not occur.  The definition of
`CalleesFirst` below requires the blocks it compares to occur, so this out-of-range
value never decides a comparison there. -/
def pos {k : Nat} (order : List (Fin k)) (c : Fin k) : Nat := order.idxOf c

-- lean/Toy/Scc/Graph.lean:214-216
/-- The order mentions the block of every function. -/
def Covers {n k : Nat} (comp : Fin n → Fin k) (order : List (Fin k)) : Prop :=
  ∀ f, comp f ∈ order

-- lean/Toy/Scc/Graph.lean:230-238
/-- Callees first (a reverse topological order of the condensation): for every call
that crosses blocks, both endpoint blocks occur in `order`, and the callee's block
first occurs strictly earlier than the caller's block.  Blocks that take part in no
cross-block call are not constrained; `Covers` separately requires every function's
block to occur. -/
def CalleesFirst {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) (order : List (Fin k)) :
    Prop :=
  ∀ f g, E f g = true → comp f ≠ comp g →
    comp f ∈ order ∧ comp g ∈ order ∧ pos order (comp g) < pos order (comp f)
```

#### Summaries, transfers and fixpoints (`Toy.Scc.Lattice`)

```lean
-- lean/Toy/Scc/Lattice.lean:16-18
/-- An abstract value: a subset of `Fin m` given as a bit vector (the powerset
lattice of `Fin m` ordered by inclusion). -/
abbrev Val (m : Nat) := Fin m → Bool

-- lean/Toy/Scc/Lattice.lean:20-21
/-- A summary vector: one abstract value per function. -/
abbrev Summ (n m : Nat) := Fin n → Val m

-- lean/Toy/Scc/Lattice.lean:23-24
/-- A transfer function on summary vectors (one equation per function). -/
abbrev Transfer (n m : Nat) := Summ n m → Summ n m

-- lean/Toy/Scc/Lattice.lean:26-27
/-- The pointwise inclusion order on summary vectors. -/
def Le {n m : Nat} (σ τ : Summ n m) : Prop := ∀ f i, σ f i = true → τ f i = true

-- lean/Toy/Scc/Lattice.lean:32-33
/-- Least summary vector (every function summarized by the empty set). -/
def bot {n m : Nat} : Summ n m := fun _ _ => false

-- lean/Toy/Scc/Lattice.lean:34-35
/-- Greatest summary vector. -/
def top {n m : Nat} : Summ n m := fun _ _ => true

-- lean/Toy/Scc/Lattice.lean:66-67
/-- Monotonicity of a transfer function. -/
def Monotone {n m : Nat} (F : Transfer n m) : Prop := ∀ σ τ, Le σ τ → Le (F σ) (F τ)

-- lean/Toy/Scc/Lattice.lean:69-72
/-- Locality: the equation of `f` reads only the summaries of the callees of `f`
(this is what makes a transfer function "follow the call graph"). -/
def RespectsCalls {n m : Nat} (E : Graph n) (F : Transfer n m) : Prop :=
  ∀ σ τ f, (∀ g, E f g = true → σ g = τ g) → F σ f = F τ f

-- lean/Toy/Scc/Lattice.lean:76-78
/-- `σ` is the least fixpoint of `F` (least among all fixpoints). -/
def IsLeastFixpoint {n m : Nat} (F : Transfer n m) (σ : Summ n m) : Prop :=
  F σ = σ ∧ ∀ τ, F τ = τ → Le σ τ

-- lean/Toy/Scc/Lattice.lean:80-82
/-- `σ` is the greatest fixpoint of `F` (greatest among all fixpoints). -/
def IsGreatestFixpoint {n m : Nat} (F : Transfer n m) (σ : Summ n m) : Prop :=
  F σ = σ ∧ ∀ τ, F τ = τ → Le τ σ

-- lean/Toy/Scc/Lattice.lean:84-87
/-- `k`-fold iteration (Kleene iteration when started at `bot` or `top`). -/
def iter {α : Type} (g : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iter g k (g a)

-- lean/Toy/Scc/Lattice.lean:246-254
/-- Disjunctive transfer with unary-premise rules: bit `i` of `f` holds if it is a seed
(`c f i`) or if some single dependency bit `(g, j)` with `d f i g j` holds.  Every rule
has at most one premise, so these transfers preserve joins (they are additive);
multi-premise Horn clauses such as `σ g₁ j₁ ∧ σ g₂ j₂ → σ f i` are monotone but are not
of this form.  Least fixpoints of such transfers are reachability-style facts. -/
def disjT {n m : Nat} (c : Fin n → Fin m → Bool) (d : Fin n → Fin m → Fin n → Fin m → Bool) :
    Transfer n m :=
  fun σ f i => c f i || (List.finRange n).any fun g => (List.finRange m).any fun j =>
    d f i g j && σ g j

-- lean/Toy/Scc/Lattice.lean:256-261
/-- Conjunctive transfer: bit `i` of `f` holds if it is allowed by `c` and every dependency
bit holds.  Greatest fixpoints of such transfers are safety-invariant-style facts. -/
def conjT {n m : Nat} (c : Fin n → Fin m → Bool) (d : Fin n → Fin m → Fin n → Fin m → Bool) :
    Transfer n m :=
  fun σ f i => c f i && (List.finRange n).all fun g => (List.finRange m).all fun j =>
    !d f i g j || σ g j
```

#### The bottom-up algorithm and hierarchical solutions (`Toy.Scc.BottomUp`)

```lean
-- lean/Toy/Scc/BottomUp.lean:15-19
/-- The block operator: the equations of block `c` (taken from `F`), with every summary
outside block `c` frozen to its value in `σ`. -/
def blockOp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (c : Fin k)
    (σ : Summ n m) : Transfer n m :=
  fun τ f => if comp f = c then F τ f else σ f

-- lean/Toy/Scc/BottomUp.lean:21-25
/-- Starting point of the inner iteration for block `c`: block `c` reset to the empty
set (`least = true`) or to the full set (`least = false`); other blocks from `σ`. -/
def blockInit {n m k : Nat} (comp : Fin n → Fin k) (c : Fin k) (least : Bool)
    (σ : Summ n m) : Summ n m :=
  fun f => if comp f = c then (fun _ => !least) else σ f

-- lean/Toy/Scc/BottomUp.lean:27-30
/-- Solve block `c` by `fuel` rounds of Kleene iteration of its block operator. -/
def solveBlock {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (fuel : Nat)
    (least : Bool) (c : Fin k) (σ : Summ n m) : Summ n m :=
  iter (blockOp F comp c σ) fuel (blockInit comp c least σ)

-- lean/Toy/Scc/BottomUp.lean:32-37
/-- The bottom-up algorithm: one pass over `order`, performing one block solve per list
entry (a block listed twice is solved twice), with the least (`sign c = true`) or
greatest (`sign c = false`) inner fixpoint, starting from the summary vector `init`. -/
def bottomUp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (sign : Fin k → Bool)
    (order : List (Fin k)) (fuel : Nat) (init : Summ n m) : Summ n m :=
  order.foldl (fun σ c => solveBlock F comp fuel (sign c) c σ) init

-- lean/Toy/Scc/BottomUp.lean:39-42
/-- Bottom-up least fixpoint: every block solved with its least inner fixpoint, start `bot`. -/
def bottomUpLfp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Summ n m :=
  bottomUp F comp (fun _ => true) order fuel bot

-- lean/Toy/Scc/BottomUp.lean:44-48
/-- Bottom-up greatest fixpoint: every block solved with its greatest inner fixpoint,
start `top`. -/
def bottomUpGfp {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Summ n m :=
  bottomUp F comp (fun _ => false) order fuel top

-- lean/Toy/Scc/BottomUp.lean:52-58
/-- `σ` solves block `c` extremally: restricted to block `c`, `σ` is the least
(`least = true`) or greatest (`least = false`) fixpoint of the block operator whose
frozen outside values are taken from `σ` itself. -/
def BlockExtremal {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k) (c : Fin k)
    (least : Bool) (σ : Summ n m) : Prop :=
  blockOp F comp c σ σ = σ ∧
    ∀ τ, blockOp F comp c σ τ = τ → (if least then Le σ τ else Le τ σ)

-- lean/Toy/Scc/BottomUp.lean:60-73
/-- Coordinatewise block-extremality for the sign assignment `sign`: every block `c` is
the least (`sign c = true`) or greatest (`sign c = false`) fixpoint of its own equations
when all other blocks are frozen, as constants, to their values in `σ`.

This is *not* the general semantics of hierarchical (nested) fixpoint equation systems,
such as Boolean equation systems, where blocks are ordered and the solution of an inner
block, as a function of the outer variables, is substituted into the outer blocks.  The
two notions agree when no block depends on a block of a later position (for example
under `CalleesFirst` and `RespectsCalls`); with cyclic dependencies between blocks of
different signs, `HierSolution` can have several solutions
(`hierSolution_swapT_gCycle_mixSign_not_unique`). -/
def HierSolution {n m k : Nat} (F : Transfer n m) (comp : Fin n → Fin k)
    (sign : Fin k → Bool) (σ : Summ n m) : Prop :=
  ∀ c, BlockExtremal F comp c (sign c) σ
```

#### Ranking certificates (`Toy.Scc.Fixpoint`)

```lean
-- lean/Toy/Scc/Fixpoint.lean:383-385
/-- The part of `σ` whose bits have rank strictly below `k`. -/
def below {n m : Nat} (σ : Summ n m) (r : Fin n → Fin m → Nat) (k : Nat) : Summ n m :=
  fun f i => σ f i && decide (r f i < k)

-- lean/Toy/Scc/Fixpoint.lean:387-393
/-- A ranking certificate for `σ`: every set bit of `σ` is produced by one application of
`F` to the strictly lower-ranked part of `σ`.  This is a well-founded derivation witness;
checking it evaluates `F` on the vectors `below σ r k`, one per distinct rank value `k`
of a set bit. -/
def RankedJustified {n m : Nat} (F : Transfer n m) (σ : Summ n m)
    (r : Fin n → Fin m → Nat) : Prop :=
  ∀ f i, σ f i = true → F (below σ r (r f i)) f i = true

-- lean/Toy/Scc/Fixpoint.lean:399-403
/-- The canonical ranking: `kleeneRank F f i` is the least `k < n * m` such that bit `(f, i)`
is set in the Kleene iterate `F^(k+1)(bot)` (that is, after `k + 1` rounds), and `0` if
there is no such `k` (in particular for bits that are never set). -/
def kleeneRank {n m : Nat} (F : Transfer n m) (f : Fin n) (i : Fin m) : Nat :=
  ((List.range (n * m)).find? fun k => iter F (k + 1) bot f i).getD 0
```

#### Configuration-level calls and termination (`Toy.Scc.Termination`)

```lean
-- lean/Toy/Scc/Termination.lean:14-16
/-- A configuration-level call relation: `C (f, x) (g, y)` means that `f` running on
argument state `x` makes a call to `g` with argument state `y`. -/
abbrev Calls (n : Nat) (S : Type) := Fin n × S → Fin n × S → Prop

-- lean/Toy/Scc/Termination.lean:18-21
/-- Every configuration-level call follows an edge of the call graph (the call graph
over-approximates the calls the program can make). -/
def CallsInGraph {n : Nat} {S : Type} (E : Graph n) (C : Calls n S) : Prop :=
  ∀ a b, C a b → E a.1 b.1 = true

-- lean/Toy/Scc/Termination.lean:23-26
/-- Calls inside a block strictly decrease the inner measure. -/
def IntraDecrease {n k : Nat} {S : Type} (comp : Fin n → Fin k) (inner : Fin n → S → Nat)
    (C : Calls n S) : Prop :=
  ∀ a b, C a b → comp a.1 = comp b.1 → inner b.1 b.2 < inner a.1 a.2

-- lean/Toy/Scc/Termination.lean:28-31
/-- Calls across blocks go to a block of strictly smaller rank. -/
def InterRankDecrease {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (C : Calls n S) : Prop :=
  ∀ a b, C a b → comp a.1 ≠ comp b.1 → rank (comp b.1) < rank (comp a.1)

-- lean/Toy/Scc/Termination.lean:33-34
/-- Strict lexicographic order on pairs of naturals. -/
def LexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

-- lean/Toy/Scc/Termination.lean:36-40
/-- The lexicographic measure of a configuration `(f, x)`: the rank of the block of `f`,
then the inner measure of `f` at `x`. -/
def lexMeasure {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (inner : Fin n → S → Nat) (a : Fin n × S) : Nat × Nat :=
  (rank (comp a.1), inner a.1 a.2)

-- lean/Toy/Scc/Termination.lean:42-45
/-- The lexicographic measure strictly decreases along every call. -/
def LexDecreasing {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (inner : Fin n → S → Nat) (C : Calls n S) : Prop :=
  ∀ a b, C a b → LexLt (lexMeasure rank comp inner b) (lexMeasure rank comp inner a)

-- lean/Toy/Scc/Termination.lean:47-50
/-- Every call chain is finite: every configuration is accessible for the converse of
the call relation. -/
def Terminates {n : Nat} {S : Type} (C : Calls n S) : Prop :=
  ∀ a, Acc (fun b a => C a b) a
```

What they capture. `IsSccDecomp E comp` is the textbook partition into strongly connected components, with blocks named by `Fin k` (block names need not all be used). `BlocksMutuallyReachable` takes reachability in the whole graph, not in the subgraph induced by a block. `CondEdge`/`CondensationAcyclic` describe the quotient graph on blocks without self-loops. `checkScc` is a decision procedure that compares block equality with mutual reachability for every ordered pair of functions; it is a specification-level checker, not an SCC algorithm. `pos order c` is the index of the first occurrence of `c` (and `order.length` when `c` does not occur; `CalleesFirst` requires both compared blocks to occur, so this value never decides a comparison). `CalleesFirst` constrains only blocks that take part in cross-block calls; `Covers` separately requires the block of every function to occur. `Le` is the bitwise inclusion order, so `Summ n m` is the powerset lattice of `n * m` bits; `Monotone` and `RespectsCalls` are this package's own definitions (not Mathlib's). `IsLeastFixpoint`/`IsGreatestFixpoint` are stated independently of any iteration. `blockOp F comp c σ` keeps the equations of block `c` and freezes every other function at its value in `σ`; `bottomUp` performs one block solve per list entry (a block listed twice is solved twice). `HierSolution` is coordinatewise block-extremality; its doc comment explains why it is not the general nested semantics of fixpoint equation systems. `RankedJustified F σ r` requires every set bit of `σ` to be produced by one application of `F` to the strictly lower-ranked part of `σ`. `Terminates C` is accessibility of every configuration for the converse of `C`, i.e. absence of infinite call chains.

Every core proposition and checker (`Reach`, `reachB`, `IsSccDecomp`, `BlocksMutuallyReachable`, `CondensationAcyclic`, `checkScc`, `Covers`, `CalleesFirst`, `Le`, `Monotone`, `RespectsCalls`, `IsLeastFixpoint`, `IsGreatestFixpoint`, `HierSolution`, `RankedJustified`, `CallsInGraph`, `IntraDecrease`, `InterRankDecrease`, `LexDecreasing`, `Terminates`) has proved positive and negative examples, and `bottomUpLfp`, `bottomUpGfp` and `kleeneRank` have proved evaluation examples; they are quoted under **Definition examples** below, after the fixtures they use. The remaining definitions (`ClosedUnder`, `reachStep`, `reachFrom`, `CondEdge`, `pos`, `iter`, `disjT`, `conjT`, `blockOp`, `blockInit`, `solveBlock`, `bottomUp`, `BlockExtremal`, `below`, `Calls`, `LexLt`, `lexMeasure`) are auxiliary; they are exercised through the examples, witnesses and theorems that use them, without separate positive and negative examples.

### Fixtures

| Fixture | Shape | Used by |
| --- | --- | --- |
| `gPath`, `gCycle`, `gEmpty`, `gLoop`, `gPath3`, `gMix`, `gPathLoop1` | `0 → 1`; `0 ⇄ 1`; no calls; one self-loop; `0 → 1 → 2`; `0 → 0, 0 → 1, 1 → 1`; `0 → 1, 1 → 1` | all cards |
| `idComp`, `oneComp` | singleton blocks; one block | all cards |
| `mergeComp3`, `convexMerge3` | on `0 → 1 → 2`: blocks `{0, 2}, {1}`; blocks `{0, 1}, {2}` | `merge-nonconvex`, `merge-convex` |
| `chainLfpT`, `chainGfpT` | on `0 → 1`, one bit: `F 1 = {0}, F 0 = σ 1`; `F 1 = ∅, F 0 = σ 1` | `kleene-bound`, bottom-up cards, `caller-first`, certificates |
| `idT`, `negT`, `topT`, `botT` | identity on one bit; negation (not monotone, no fixpoint); constant `top`; constant `bot` | tightness counterexamples, `checks-not-exact` |
| `nmLfpT`, `nmGfpT`, `nmRankT` | non-monotone one-function transfers with two bits | monotonicity counterexamples of the checking cards |
| `seedCopyT` | on `0 → 1`, two bits: `F 1 = {0}`, `F 0 = σ 1`; unique fixpoint `seedCopyFix` | `kleene-bound`, `bottomup-one-sided`, `prefix-postfix-sound` |
| `mixLfpT`, `mixGfpT`, `mixT`, `mixRevT`, `swapT` | on `gMix` (and `swapT` on `gCycle`), one bit | bottom-up cards, `mixed-neither`, `bottomup-mixed` |
| `chain3LfpT`, `chain3GfpT` | on `0 → 1 → 2`, one bit | `merge-convex`, `merge-nonconvex` |
| `splitLfpT`, `splitGfpT`, `splitOneBitT` | on `0 ⇄ 1`, two bits (one bit for `splitOneBitT`) | `split-scc` |
| `cPath`, `cCycle`, `cLoop`, `cCount`, `cJump`, `cUnbounded` | configuration-level call relations | termination cards |

Lean source excerpts:

#### Graphs

```lean
-- lean/Toy/Scc/Graph.lean:265-266
/-- `0 → 1`. -/
def gPath : Graph 2 := fun f g => decide (f.val = 0 ∧ g.val = 1)
-- lean/Toy/Scc/Graph.lean:267-268
/-- `0 → 1 → 0`. -/
def gCycle : Graph 2 := fun f g => decide (f ≠ g)
-- lean/Toy/Scc/Graph.lean:269-270
/-- No calls. -/
def gEmpty : Graph 2 := fun _ _ => false
-- lean/Toy/Scc/Graph.lean:271-272
/-- One self-recursive function. -/
def gLoop : Graph 1 := fun _ _ => true
-- lean/Toy/Scc/Graph.lean:273-274
/-- `0 → 1 → 2`. -/
def gPath3 : Graph 3 := fun f g => decide (g.val = f.val + 1)
-- lean/Toy/Scc/Graph.lean:275-276
/-- `0 → 0`, `0 → 1`, `1 → 1`. -/
def gMix : Graph 2 := fun f g => decide (f.val ≤ g.val)
-- lean/Toy/Scc/Graph.lean:277-278
/-- `0 → 1`, `1 → 1` (a caller and a self-recursive callee). -/
def gPathLoop1 : Graph 2 := fun _ g => decide (g.val = 1)
```

#### Block maps and sign assignments

```lean
-- lean/Toy/Scc/Graph.lean:280-281
/-- Identity decomposition (every function its own block). -/
def idComp {n : Nat} : Fin n → Fin n := fun f => f
-- lean/Toy/Scc/Graph.lean:282-283
/-- Everything in one block. -/
def oneComp {n : Nat} : Fin n → Fin 1 := fun _ => 0
-- lean/Toy/Scc/Graph.lean:284-285
/-- Merges the endpoints of `0 → 1 → 2` into block `0`; `1` is block `1`. -/
def mergeComp3 : Fin 3 → Fin 2 := fun f => if f.val = 1 then 1 else 0
-- lean/Toy/Scc/Graph.lean:286-288
/-- Merges the first two functions of `0 → 1 → 2` into block `0`; `2` is block `1`
(a merge along the path that keeps the condensation acyclic). -/
def convexMerge3 : Fin 3 → Fin 2 := fun f => if f.val = 2 then 1 else 0
-- lean/Toy/Scc/BottomUp.lean:436-437
/-- Sign assignment on two blocks: block `1` least, block `0` greatest. -/
def mixSign : Fin 2 → Bool := fun c => decide (c.val = 1)
-- lean/Toy/Scc/Transfer.lean:371-373
/-- Sign assignment: the callee block `1` uses its greatest fixpoint, the caller block `0`
its least. -/
def revSign : Fin 2 → Bool := fun c => decide (c.val = 0)
```

#### Transfers

```lean
-- lean/Toy/Scc/Lattice.lean:308-310
/-- On `gPath` (`0 → 1`): `F 1 = {0}`, `F 0 = σ 1`.  Least fixpoint: everything. -/
def chainLfpT : Transfer 2 1 :=
  disjT (fun f _ => decide (f.val = 1)) (fun f _ g _ => decide (f.val = 0 ∧ g.val = 1))
-- lean/Toy/Scc/Lattice.lean:312-314
/-- On `gPath`: `F 1 = ∅`, `F 0 = σ 1`.  Greatest fixpoint: nothing. -/
def chainGfpT : Transfer 2 1 :=
  conjT (fun f _ => decide (f.val = 0)) (fun f _ g _ => decide (f.val = 0 ∧ g.val = 1))
-- lean/Toy/Scc/Lattice.lean:316-317
/-- On `gLoop`: the identity equation `σ 0 = σ 0` (least fixpoint `bot`, greatest `top`). -/
def idT : Transfer 1 1 := disjT (fun _ _ => false) (fun _ i _ j => decide (i = j))
-- lean/Toy/Scc/Lattice.lean:319-320
/-- On `gLoop`: negation, which is not monotone and has no fixpoint. -/
def negT : Transfer 1 1 := fun σ f i => !σ f i
-- lean/Toy/Scc/Lattice.lean:322-323
/-- Constant `top` (reads nothing). -/
def topT {n m : Nat} : Transfer n m := fun _ => top
-- lean/Toy/Scc/Fixpoint.lean:28-29
/-- Constant `bot` (reads nothing). -/
def botT {n m : Nat} : Transfer n m := fun _ => bot
-- lean/Toy/Scc/Fixpoint.lean:15-17
/-- A non-monotone single-function transfer with two bits:
`F σ = ∅` if `σ 0 = {0}`, and `F σ = {0, 1}` otherwise.  Unique fixpoint `top`. -/
def nmLfpT : Transfer 1 2 := fun σ _ _ => !(σ 0 0 && !σ 0 1)
-- lean/Toy/Scc/Fixpoint.lean:19-21
/-- A non-monotone single-function transfer with two bits:
`F σ = {0, 1}` if `σ 0 = {1}`, and `F σ = ∅` otherwise.  Unique fixpoint `bot`. -/
def nmGfpT : Transfer 1 2 := fun σ _ _ => !σ 0 0 && σ 0 1
-- lean/Toy/Scc/Fixpoint.lean:23-26
/-- A non-monotone single-function transfer with two bits:
bit 0 is `¬σ 0 0 ∨ σ 0 1`, bit 1 is `σ 0 1`.  Unique fixpoint `top`, but Kleene
iteration from `bot` oscillates between `∅` and `{0}`. -/
def nmRankT : Transfer 1 2 := fun σ _ i => if i.val = 0 then !σ 0 0 || σ 0 1 else σ 0 1
-- lean/Toy/Scc/Fixpoint.lean:36-40
/-- On `gPath` (`0 → 1`) with two bits: `F 1 = {0}`, `F 0 = σ 1` (bitwise copy).
Least and greatest fixpoint: `{0}` for both functions (`seedCopyFix`). -/
def seedCopyT : Transfer 2 2 :=
  disjT (fun f i => decide (f.val = 1 ∧ i.val = 0))
    (fun f i g j => decide (f.val = 0 ∧ g.val = 1 ∧ j = i))
-- lean/Toy/Scc/Transfer.lean:128-131
/-- On `gMix` (`0 → 0`, `0 → 1`, `1 → 1`): `F 0 = σ 0 ∪ σ 1`, `F 1 = {0} ∪ σ 1`
(both blocks recursive; least fixpoint: everything). -/
def mixLfpT : Transfer 2 1 :=
  disjT (fun f _ => decide (f.val = 1)) (fun f _ g _ => decide (f.val ≤ g.val))
-- lean/Toy/Scc/Transfer.lean:133-135
/-- On `gMix`: `F 0 = σ 0 ∩ σ 1`, `F 1 = ∅` (greatest fixpoint: nothing). -/
def mixGfpT : Transfer 2 1 :=
  conjT (fun f _ => decide (f.val = 0)) (fun f _ g _ => decide (f.val ≤ g.val))
-- lean/Toy/Scc/Transfer.lean:295-296
/-- On `gMix` (`0 → 0`, `0 → 1`, `1 → 1`): `F 0 = σ 0 ∪ σ 1`, `F 1 = σ 1`. -/
def mixT : Transfer 2 1 := disjT (fun _ _ => false) (fun f _ g _ => decide (f.val ≤ g.val))
-- lean/Toy/Scc/Transfer.lean:368-369
/-- On `gMix`: `F 0 = σ 0 ∩ σ 1`, `F 1 = σ 1`. -/
def mixRevT : Transfer 2 1 := conjT (fun _ _ => true) (fun f _ g _ => decide (f.val ≤ g.val))
-- lean/Toy/Scc/BottomUp.lean:439-440
/-- On the 2-cycle: `F 0 = σ 1`, `F 1 = σ 0`. -/
def swapT : Transfer 2 1 := disjT (fun _ _ => false) (fun f _ g _ => decide (f ≠ g))
-- lean/Toy/Scc/Transfer.lean:402-404
/-- On `0 → 1 → 2`: `F 2 = {0}`, `F 1 = σ 2`, `F 0 = σ 1` (least fixpoint: everything). -/
def chain3LfpT : Transfer 3 1 :=
  disjT (fun f _ => decide (f.val = 2)) (fun f _ g _ => decide (g.val = f.val + 1))
-- lean/Toy/Scc/Transfer.lean:406-408
/-- On `0 → 1 → 2`: `F 2 = ∅`, `F 1 = σ 2`, `F 0 = σ 1` (greatest fixpoint: nothing). -/
def chain3GfpT : Transfer 3 1 :=
  conjT (fun f _ => decide (f.val ≠ 2)) (fun f _ g _ => decide (g.val = f.val + 1))
-- lean/Toy/Scc/Transfer.lean:480-484
/-- On the 2-cycle with two bits: function `f` seeds bit `f` and copies the other bit
from the other function.  Least fixpoint: everything. -/
def splitLfpT : Transfer 2 2 :=
  disjT (fun f i => decide (f.val = i.val))
    (fun f i g j => decide (f.val ≠ i.val ∧ g.val = i.val ∧ j = i))
-- lean/Toy/Scc/Transfer.lean:486-490
/-- Dual: function `f` forbids bit `f` and copies the other bit from the other function.
Greatest fixpoint: nothing. -/
def splitGfpT : Transfer 2 2 :=
  conjT (fun f i => decide (f.val ≠ i.val))
    (fun f i g j => decide (f.val ≠ i.val ∧ g.val = i.val ∧ j = i))
-- lean/Toy/Scc/Transfer.lean:523-526
/-- The three monotone maps `Bool → Bool`: constant `false` (`a = 0`), constant `true`
(`a = 1`), identity (`a = 2`). -/
def oneBitCase (a : Fin 3) (x : Bool) : Bool :=
  if a.val = 0 then false else if a.val = 1 then true else x
-- lean/Toy/Scc/Transfer.lean:528-532
/-- One bit per function on the 2-cycle: `F 0 = oneBitCase a (σ 1)`, `F 1 = oneBitCase b (σ 0)`.
These nine transfers are all the monotone transfers on `Summ 2 1` that read only callees
in the 2-cycle. -/
def splitOneBitT (a b : Fin 3) : Transfer 2 1 :=
  fun σ f _ => if f.val = 0 then oneBitCase a (σ 1 0) else oneBitCase b (σ 0 0)
```

#### Summary vectors

```lean
-- lean/Toy/Scc/Fixpoint.lean:31-32
/-- The vector `{0}` for a single function with two bits. -/
def only0 : Summ 1 2 := fun _ i => decide (i.val = 0)
-- lean/Toy/Scc/Fixpoint.lean:33-34
/-- The vector `{1}` for a single function with two bits. -/
def only1 : Summ 1 2 := fun _ i => decide (i.val = 1)
-- lean/Toy/Scc/Fixpoint.lean:42-43
/-- `{0}` for both functions: the unique fixpoint of `seedCopyT`. -/
def seedCopyFix : Summ 2 2 := fun _ i => decide (i.val = 0)
-- lean/Toy/Scc/Fixpoint.lean:44-46
/-- `σ 0 = {0, 1}`, `σ 1 = {0}`: a prefixpoint of `seedCopyT` strictly between its least
fixpoint and `top`. -/
def seedCopyPre : Summ 2 2 := fun f i => decide (i.val = 0 ∨ f.val = 0)
-- lean/Toy/Scc/Fixpoint.lean:47-49
/-- `σ 0 = ∅`, `σ 1 = {0}`: a postfixpoint of `seedCopyT` strictly between `bot` and its
greatest fixpoint. -/
def seedCopyPost : Summ 2 2 := fun f i => decide (f.val = 1 ∧ i.val = 0)
-- lean/Toy/Scc/Transfer.lean:298-299
/-- The vector `σ 0 = {0}`, `σ 1 = ∅`. -/
def mixResult : Summ 2 1 := fun f _ => decide (f.val = 0)
-- lean/Toy/Scc/Transfer.lean:375-376
/-- The vector `σ 0 = ∅`, `σ 1 = {0}`. -/
def revResult : Summ 2 1 := fun f _ => decide (f.val = 1)
```

#### Configuration-level call relations

```lean
-- lean/Toy/Scc/Termination.lean:65-66
/-- One call from `0` to `1` (unit state). -/
def cPath : Calls 2 Unit := fun a b => a.1 = 0 ∧ b.1 = 1
-- lean/Toy/Scc/Termination.lean:67-68
/-- `0` and `1` call each other forever (unit state). -/
def cCycle : Calls 2 Unit := fun a b => a.1 ≠ b.1
-- lean/Toy/Scc/Termination.lean:69-70
/-- One function calls itself forever (unit state). -/
def cLoop : Calls 1 Unit := fun _ _ => True
-- lean/Toy/Scc/Termination.lean:71-72
/-- Self-recursion on a counter that decreases by one. -/
def cCount : Calls 1 Nat := fun a b => b.2 + 1 = a.2
-- lean/Toy/Scc/Termination.lean:73-74
/-- One call from `(0, 0)` to `(1, 5)`. -/
def cJump : Calls 2 Nat := fun a b => a = (0, 0) ∧ b = (1, 5)
-- lean/Toy/Scc/Termination.lean:75-78
/-- On `gPathLoop1`: `0` on state `0` calls `1` on any state `y` (unbounded fan-out across
blocks), and `1` on state `y + 1` calls itself on state `y`. -/
def cUnbounded : Calls 2 Nat :=
  fun a b => (a = (0, 0) ∧ b.1 = 1) ∨ (a.1 = 1 ∧ b.1 = 1 ∧ b.2 + 1 = a.2)
```

### Definition examples

Statements of the positive and negative examples, in source order (anonymous `example`s as in the source with proofs elided; named theorems and definitions quoted verbatim with their source lines). Every one is kernel-checked.

#### `Toy.Scc.Graph`

```lean
-- `Reach`: positive and negative examples.
example : Reach gPath 0 1
example : ¬ Reach gPath 1 0
```

```lean
-- lean/Toy/Scc/Graph.lean:296
theorem reach_gPath3_0_2 : Reach gPath3 0 2
-- lean/Toy/Scc/Graph.lean:299
theorem not_reach_gPath3_2_0 : ¬ Reach gPath3 2 0
```

```lean
-- `reachB`: positive and negative examples.
example : reachB gPath3 0 2 = true
example : reachB gPath3 2 0 = false
```

```lean
-- lean/Toy/Scc/Graph.lean:308
-- `IsSccDecomp`: positive examples (certified, fully proved).
theorem isSccDecomp_gPath_id : IsSccDecomp gPath idComp
-- lean/Toy/Scc/Graph.lean:310
theorem isSccDecomp_gCycle_one : IsSccDecomp gCycle oneComp
-- lean/Toy/Scc/Graph.lean:312
theorem isSccDecomp_gMix_id : IsSccDecomp gMix idComp
-- lean/Toy/Scc/Graph.lean:314
theorem isSccDecomp_gPath3_id : IsSccDecomp gPath3 idComp
-- lean/Toy/Scc/Graph.lean:316
theorem isSccDecomp_gPathLoop1_id : IsSccDecomp gPathLoop1 idComp
-- lean/Toy/Scc/Graph.lean:319
theorem reach_gCycle (f g : Fin 2) : Reach gCycle f g
-- lean/Toy/Scc/Graph.lean:325-326
-- `IsSccDecomp`: negative examples.
/-- Splitting the 2-cycle is not an SCC decomposition. -/
theorem not_isSccDecomp_gCycle_id : ¬ IsSccDecomp gCycle idComp
-- lean/Toy/Scc/Graph.lean:329-330
/-- Merging `0 → 1` into one block is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath_one : ¬ IsSccDecomp gPath oneComp
-- lean/Toy/Scc/Graph.lean:335-336
/-- Merging the endpoints of `0 → 1 → 2` is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath3_merge : ¬ IsSccDecomp gPath3 mergeComp3
-- lean/Toy/Scc/Graph.lean:339-340
/-- Merging `0` and `1` of `0 → 1 → 2` is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath3_convexMerge : ¬ IsSccDecomp gPath3 convexMerge3
```

```lean
-- `BlocksMutuallyReachable`: positive and negative examples.
example : BlocksMutuallyReachable gCycle idComp
example : ¬ BlocksMutuallyReachable gPath oneComp
-- `CondensationAcyclic`: positive and negative examples.
example : CondensationAcyclic gPath idComp
```

```lean
-- lean/Toy/Scc/Graph.lean:356
theorem not_condensationAcyclic_gCycle_id : ¬ CondensationAcyclic gCycle idComp
```

```lean
-- `checkScc`: accepts and rejects.
example : checkScc gPath idComp = true
example : checkScc gCycle idComp = false
example : checkScc gPath oneComp = false
-- `Covers` and `CalleesFirst`: positive and negative examples.
example : Covers (idComp (n := 2)) [1, 0]
example : ¬ Covers (idComp (n := 2)) [1]
example : CalleesFirst gPath idComp [1, 0]
example : ¬ CalleesFirst gPath idComp [0, 1]
```

```lean
-- lean/Toy/Scc/Graph.lean:372-374
/-- Non-covering negative examples: a list that omits the caller block, or the callee
block, of a cross-block call is not callees-first. -/
theorem not_calleesFirst_gPath_omitted_caller : ¬ CalleesFirst gPath idComp [1]
-- lean/Toy/Scc/Graph.lean:375
theorem not_calleesFirst_gPath_omitted_callee : ¬ CalleesFirst gPath idComp [0]
```

```lean
/-- Non-covering positive example: a block with no cross-block calls need not be listed
for `CalleesFirst` (but `Covers` fails). -/
example : CalleesFirst gLoop oneComp [] ∧ ¬ Covers (oneComp (n := 1)) []
/-- A duplicate entry is allowed: positions are first occurrences. -/
example : CalleesFirst gPath idComp [1, 0, 1]
```

```lean
-- lean/Toy/Scc/Graph.lean:382-384
/-- No order whatsoever is callees-first for the split 2-cycle. -/
theorem not_calleesFirst_gCycle_id (order : List (Fin 2)) :
    ¬ CalleesFirst gCycle idComp order
-- lean/Toy/Scc/Graph.lean:391-393
/-- No order whatsoever is callees-first for the non-convex merge of `0 → 1 → 2`. -/
theorem not_calleesFirst_gPath3_merge (order : List (Fin 2)) :
    ¬ CalleesFirst gPath3 mergeComp3 order
```

#### `Toy.Scc.Lattice`

```lean
-- `Le`: positive and negative examples.
example : Le (bot : Summ 2 1) top
example : ¬ Le (top : Summ 2 1) bot
-- `Monotone`: positive and negative examples.
example : Monotone chainLfpT
```

```lean
-- lean/Toy/Scc/Lattice.lean:357
theorem not_monotone_negT : ¬ Monotone negT
```

```lean
-- `RespectsCalls`: positive and negative examples.
example : RespectsCalls gPath chainLfpT
```

```lean
-- lean/Toy/Scc/Lattice.lean:364-365
/-- On the call-free graph, `chainLfpT` reads a non-callee. -/
theorem not_respectsCalls_gEmpty_chainLfpT : ¬ RespectsCalls gEmpty chainLfpT
-- lean/Toy/Scc/Lattice.lean:372
-- `IsLeastFixpoint` / `IsGreatestFixpoint`: positive and negative examples.
theorem isLeastFixpoint_chainLfpT_top : IsLeastFixpoint chainLfpT top
-- lean/Toy/Scc/Lattice.lean:377
theorem isGreatestFixpoint_chainGfpT_bot : IsGreatestFixpoint chainGfpT bot
-- lean/Toy/Scc/Lattice.lean:382
theorem isLeastFixpoint_idT_bot : IsLeastFixpoint idT bot
-- lean/Toy/Scc/Lattice.lean:384
theorem isGreatestFixpoint_idT_top : IsGreatestFixpoint idT top
-- lean/Toy/Scc/Lattice.lean:387
theorem not_isLeastFixpoint_idT_top : ¬ IsLeastFixpoint idT top
-- lean/Toy/Scc/Lattice.lean:389
theorem not_isGreatestFixpoint_idT_bot : ¬ IsGreatestFixpoint idT bot
```

#### `Toy.Scc.BottomUp`

```lean
-- `bottomUpLfp` / `bottomUpGfp` on `0 → 1` with callees first.
example : bottomUpLfp chainLfpT idComp [1, 0] 2 = top
example : bottomUpGfp chainGfpT idComp [1, 0] 2 = bot
-- ... and with the caller first.
example : bottomUpLfp chainLfpT idComp [0, 1] 2 ≠ top
```

```lean
-- lean/Toy/Scc/BottomUp.lean:421
-- `BlockExtremal` / `HierSolution`: positive and negative examples.
theorem hierSolution_chainLfpT_top : HierSolution chainLfpT idComp (fun _ => true) top
-- lean/Toy/Scc/BottomUp.lean:424
theorem hierSolution_idT_bot_least : HierSolution idT oneComp (fun _ => true) bot
-- lean/Toy/Scc/BottomUp.lean:427
theorem hierSolution_idT_top_greatest : HierSolution idT oneComp (fun _ => false) top
-- lean/Toy/Scc/BottomUp.lean:430-431
/-- `top` is a fixpoint of `idT` but not its least-signed hierarchical solution. -/
theorem not_hierSolution_idT_top_least : ¬ HierSolution idT oneComp (fun _ => true) top
-- lean/Toy/Scc/BottomUp.lean:436-437
/-- Sign assignment on two blocks: block `1` least, block `0` greatest. -/
def mixSign : Fin 2 → Bool := fun c => decide (c.val = 1)
-- lean/Toy/Scc/BottomUp.lean:439-440
/-- On the 2-cycle: `F 0 = σ 1`, `F 1 = σ 0`. -/
def swapT : Transfer 2 1 := disjT (fun _ _ => false) (fun f _ g _ => decide (f ≠ g))
-- lean/Toy/Scc/BottomUp.lean:442
theorem swapT_monotone : Monotone swapT
-- lean/Toy/Scc/BottomUp.lean:443
theorem swapT_respectsCalls : RespectsCalls gCycle swapT
-- lean/Toy/Scc/BottomUp.lean:445-451
/-- With a cyclic dependency between a greatest-signed block (`0`) and a least-signed block
(`1`), coordinatewise block-extremality is not unique: both `bot` and `top` are
hierarchical solutions.  (Nested-substitution semantics of the equation system
`ν X₀ = X₁; μ X₁ = X₀`, with `X₀` outermost, has the single solution `top`.) -/
theorem hierSolution_swapT_gCycle_mixSign_not_unique :
    HierSolution swapT idComp mixSign bot ∧ HierSolution swapT idComp mixSign top ∧
      (bot : Summ 2 1) ≠ top
-- lean/Toy/Scc/BottomUp.lean:455-457
/-- A summary vector that is not even a fixpoint is never a hierarchical solution. -/
theorem not_hierSolution_chainLfpT_bot (sign : Fin 2 → Bool) :
    ¬ HierSolution chainLfpT idComp sign bot
```

#### `Toy.Scc.Fixpoint`

```lean
-- `RankedJustified`: positive and negative examples.
example : RankedJustified chainLfpT top (fun f _ => if f.val = 1 then 0 else 1)
example : ¬ RankedJustified chainLfpT top (fun _ _ => 0)
example : ¬ RankedJustified idT top (fun _ _ => 0)
example : kleeneRank chainLfpT 0 0 = 1 ∧ kleeneRank chainLfpT 1 0 = 0
```

#### `Toy.Scc.Termination`

```lean
-- `CallsInGraph`, `IntraDecrease`, `InterRankDecrease`, `LexDecreasing`, `Terminates`:
-- positive and negative examples.
example : CallsInGraph gPath cPath
example : ¬ CallsInGraph gEmpty cPath
example : IntraDecrease oneComp (fun _ x => x) cCount
example : ¬ IntraDecrease oneComp (fun _ _ => 0) cLoop
example : InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cPath
example : ¬ InterRankDecrease (fun _ : Fin 2 => 0) idComp cPath
example : LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ (_ : Unit) => 0) cPath
example : ¬ LexDecreasing (fun _ : Fin 1 => 0) oneComp (fun _ _ => 0) cLoop
example : Terminates cCount
example : ¬ Terminates cLoop
```

### SCC decompositions and processing orders

#### scc-check — `checkScc_eq_true_iff_isSccDecomp`, `reachFrom_eq_true_iff_reach_of_pred_le`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** substantive. **Module:** `Toy.Scc.Decomp`.
- **Plain claim.** For every call graph E on Fin n and every block map comp : Fin n -> Fin k, the Boolean checker checkScc E comp, which compares "same block" with mutual reachability computed by the fuel-n closure reachB for all ordered pairs of functions, returns true exactly when comp is a valid SCC decomposition (same block iff mutually reachable); the underlying closure reachFrom E f fuel computes reachability exactly whenever fuel >= n - 1.

```lean
-- lean/Toy/Scc/Decomp.lean:90-91
theorem checkScc_eq_true_iff_isSccDecomp {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) :
    checkScc E comp = true ↔ IsSccDecomp E comp

-- lean/Toy/Scc/Decomp.lean:44-45
theorem reachFrom_eq_true_iff_reach_of_pred_le {n : Nat} (E : Graph n) (f g : Fin n)
    {fuel : Nat} (hfuel : n - 1 ≤ fuel) : reachFrom E f fuel g = true ↔ Reach E f g
```

*Unfolded (prose)*

```text
For every n, k, E : Fin n → Fin n → Bool and comp : Fin n → Fin k:
  checkScc E comp = true  ↔  ∀ f g, (comp f = comp g ↔ Reach E f g ∧ Reach E g f),
where checkScc tests, for all ordered pairs (f, g), decide (comp f = comp g) == (reachB E f g && reachB E g f),
and reachB E f g := reachFrom E f n g (fuel n).
Closure lemma: for every fuel with n - 1 ≤ fuel,  reachFrom E f fuel g = true ↔ (there is a call chain f →* g in E),
where reachFrom E f 0 = {f} and reachFrom E f (k+1) = reachFrom E f k ∪ {g | some h ∈ reachFrom E f k has E h g}.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hfuel : n - 1 <= fuel (closure lemma only; the checker theorem has no hypotheses)` | A shortest call chain has at most n - 1 edges; with less fuel the closure misses reachable functions. | tight: counterexample `reachFrom_tight_fuel` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Decomp.lean:109-110
theorem reachFrom_tight_fuel :
    ¬ (3 - 1 ≤ 1) ∧ ¬ (reachFrom gPath3 0 1 2 = true ↔ Reach gPath3 0 2)
```

- **Depth.** substantive. Completeness of the bounded closure uses a counting argument: the reached sets grow with the fuel, every step that is not closed under calls adds a function, so by fuel n - 1 the set is closed under calls or contains every function. Given that, the checker equivalence is a case analysis.
- **Non-vacuity witness** (`checkScc_nonvacuous`, `reachFrom_nonvacuous`). checkScc accepts the singleton-block decomposition of 0 -> 1, which is a valid SCC decomposition, and rejects both the split 2-cycle and the one-block merge of 0 -> 1, which are invalid; with fuel 2 = n - 1 the closure finds 0 ->* 2 in 0 -> 1 -> 2 and excludes 2 ->* 0.

```lean
-- lean/Toy/Scc/Decomp.lean:124-127
theorem checkScc_nonvacuous :
    (checkScc gPath idComp = true ∧ IsSccDecomp gPath idComp) ∧
      (checkScc gCycle idComp = false ∧ ¬ IsSccDecomp gCycle idComp) ∧
      (checkScc gPath oneComp = false ∧ ¬ IsSccDecomp gPath oneComp)

-- lean/Toy/Scc/Decomp.lean:117-119
theorem reachFrom_nonvacuous :
    3 - 1 ≤ 2 ∧ reachFrom gPath3 0 2 2 = true ∧ Reach gPath3 0 2 ∧
      reachFrom gPath3 2 2 0 = false ∧ ¬ Reach gPath3 2 0
```

- **Tier justification.** Textbook graph theory (reachability by bounded closure; SCCs as classes of mutual reachability), restated as a decidable checker in this vocabulary. Verified SCC algorithms exist in several proof assistants (prior art).
- **Prior art.**
  - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160, 1972, doi:10.1137/0201010. Linear-time algorithm for the strongly connected components of a directed graph; the SCC partition itself is the background notion formalized here.
  - P. Lammich, "Verified efficient implementation of Gabow's strongly connected component algorithm", Interactive Theorem Proving (ITP 2014), LNCS 8558, pp. 325-340, doi:10.1007/978-3-319-08970-6_21; Archive of Formal Proofs entry Gabow_SCC, https://www.isa-afp.org/entries/Gabow_SCC.html (2014). A verified SCC algorithm in Isabelle/HOL; this package verifies no algorithm, only a specification-level checker.
  - R. Chen, C. Cohen, J.-J. Levy, S. Merz, L. Thery, "Formal proofs of Tarjan's strongly connected components algorithm in Why3, Coq and Isabelle", ITP 2019, LIPIcs 141, article 13, doi:10.4230/LIPIcs.ITP.2019.13. Mechanized correctness proofs of Tarjan's SCC algorithm in three proof systems.
  - rocq-community/tarjan, https://github.com/rocq-community/tarjan, commit 34fe042cc482e65d27bc68b455d922d47da81c9d: Coq (Mathematical Components) formalization of Tarjan's and Kosaraju's SCC algorithms.
  - P. Lammich, R. Neumann, "A framework for verifying depth-first search algorithms", CPP 2015, pp. 137-146, doi:10.1145/2676724.2693165; Archive of Formal Proofs entry DFS_Framework, whose example theories include Tarjan's SCC algorithm. Mechanized DFS-based graph algorithms in Isabelle/HOL.
  - S. Merz, V. Trelat, "Correctness of a set-based algorithm for computing strongly connected components of a graph", Archive of Formal Proofs entry SCC_Bloemen_Sequential, August 17, 2022. An Isabelle/HOL proof of a set-based sequential SCC algorithm.
  - Lean 4, release v4.34.1 (the toolchain of this package): module src/Lean/Util/SCC.lean (Lean.SCC.scc, documented as a simple implementation of Tarjan's algorithm) is used by partitionPreDefs in src/Lean/Elab/PreDefinition/Main.lean to split mutually recursive definitions into SCC blocks. It is unverified program code, not a theorem.
- **Design question.** Which conditions must an SCC-boundary checker verify to accept an untrusted SCC decomposition? This card gives an exact, specification-level decision procedure for SCC validity itself (one reachability check per ordered pair of functions).

Basis: execution (Lean kernel check). `checkScc_eq_true_iff_isSccDecomp`, `reachFrom_eq_true_iff_reach_of_pred_le` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `checkScc_eq_true_iff_isSccDecomp`: `Classical.choice`, `Quot.sound`, `propext`; `reachFrom_eq_true_iff_reach_of_pred_le`: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A tool that receives a block map from an untrusted SCC algorithm can accept it exactly when `checkScc` (or any checker equivalent to it) accepts. The transfer to a real checker requires that its call graph is the same finite relation and that it computes reachability with at least `n - 1` closure steps (or to saturation). Nothing is said about the cost of the check or about the SCC algorithm that produced the map.

#### scc-char — `isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** shallow. **Module:** `Toy.Scc.Decomp`.
- **Plain claim.** A block map comp is a valid SCC decomposition of E exactly when (a) any two functions in the same block are mutually reachable in the whole graph E and (b) the condensation, the graph on blocks with an edge c -> d whenever c differs from d and some function of block c calls some function of block d, has no cycle.

```lean
-- lean/Toy/Scc/Decomp.lean:135-137
theorem isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic {n k : Nat}
    (E : Graph n) (comp : Fin n → Fin k) :
    IsSccDecomp E comp ↔ BlocksMutuallyReachable E comp ∧ CondensationAcyclic E comp
```

*Unfolded (prose)*

```text
IsSccDecomp E comp  ↔  (∀ f g, comp f = comp g → f →* g ∧ g →* f)            -- (a), reachability in all of E
                     ∧ (¬∃ c, c →⁺ c in the graph CondEdge E comp),       -- (b)
where CondEdge E comp c d := c ≠ d ∧ ∃ f g, comp f = c ∧ comp g = d ∧ E f g = true.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `right-hand conjunct (b): CondensationAcyclic E comp` | Rules out splitting an SCC across several blocks; without it, (a) alone does not characterize SCC decompositions. | tight: counterexample `sccChar_tight_acyclic` |
| `right-hand conjunct (a): BlocksMutuallyReachable E comp` | Rules out merging functions that are not mutually reachable; without it, (b) alone does not characterize SCC decompositions. | tight: counterexample `sccChar_tight_mutual` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Decomp.lean:184-186
theorem sccChar_tight_acyclic :
    BlocksMutuallyReachable gCycle idComp ∧ ¬ CondensationAcyclic gCycle idComp ∧
      ¬ IsSccDecomp gCycle idComp

-- lean/Toy/Scc/Decomp.lean:192-194
theorem sccChar_tight_mutual :
    CondensationAcyclic gEmpty oneComp ∧ ¬ BlocksMutuallyReachable gEmpty oneComp ∧
      ¬ IsSccDecomp gEmpty oneComp
```

- **Depth.** shallow. Lifting condensation paths to call chains and projecting call chains to condensation paths, one induction each.
- **Non-vacuity witness** (`sccChar_nonvacuous`). The singleton decomposition of 0 -> 0, 0 -> 1, 1 -> 1 satisfies both sides; its condensation has the edge 0 -> 1 and both blocks are recursive.

```lean
-- lean/Toy/Scc/Decomp.lean:203-205
theorem sccChar_nonvacuous :
    IsSccDecomp gMix idComp ∧ BlocksMutuallyReachable gMix idComp ∧
      CondensationAcyclic gMix idComp ∧ CondEdge gMix idComp 0 1
```

- **Tier justification.** Standard graph theory: the SCC partition is the finest partition into mutually reachable blocks, and its condensation is acyclic.
- **Prior art.**
  - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160, 1972, doi:10.1137/0201010. Linear-time algorithm for the strongly connected components of a directed graph; the SCC partition itself is the background notion formalized here.
  - R. Chen, C. Cohen, J.-J. Levy, S. Merz, L. Thery, "Formal proofs of Tarjan's strongly connected components algorithm in Why3, Coq and Isabelle", ITP 2019, LIPIcs 141, article 13, doi:10.4230/LIPIcs.ITP.2019.13. Mechanized correctness proofs of Tarjan's SCC algorithm in three proof systems.
  - rocq-community/tarjan, commit 34fe042cc482e65d27bc68b455d922d47da81c9d, theories/acyclic.v, lemma sccs_acyclicE (sccs_acyclic = acyclic g, where sccs_acyclic states that every class of the SCC partition is acyclic): a related mechanized link between SCCs and acyclicity, for the graph itself rather than for a condensation by an arbitrary block map.
- **Design question.** Splits SCC validity into an edge-local part that an order can certify (acyclic condensation, see topo-order) and a reachability part (mutual reachability inside blocks), so a checker can verify only the part it needs.

Basis: execution (Lean kernel check). `isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A checker can split SCC validity into an edge-local part (acyclic condensation, certifiable by an order, see `topo-order`) and a reachability part (mutual reachability inside each block). A decomposition that is only checked for acyclicity may merge non-mutually-reachable functions (as in `merge-convex`), which is harmless for single-pass solving but not an SCC decomposition.

#### topo-order — `condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** substantive. **Module:** `Toy.Scc.Decomp`.
- **Plain claim.** The condensation of E under comp is acyclic exactly when there is a duplicate-free list of blocks that contains the block of every function and is callees-first: for every call between functions in different blocks, both blocks occur in the list and the callee's block occurs strictly earlier than the caller's block.

```lean
-- lean/Toy/Scc/Decomp.lean:214-217
theorem condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order {n k : Nat}
    (E : Graph n) (comp : Fin n → Fin k) :
    CondensationAcyclic E comp ↔
      ∃ order : List (Fin k), order.Nodup ∧ Covers comp order ∧ CalleesFirst E comp order
```

*Unfolded (prose)*

```text
CondensationAcyclic E comp  ↔  ∃ order : List (Fin k),
    order has no duplicates
  ∧ (∀ f, comp f ∈ order)
  ∧ (∀ f g, E f g = true → comp f ≠ comp g →
        comp f ∈ order ∧ comp g ∈ order ∧ idxOf order (comp g) < idxOf order (comp f)).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `order.Nodup (inside the existential)` | Strengthens the existence side (a duplicate-free order exists); the right-to-left direction does not use it. | harmless |
| `Covers comp order (inside the existential)` | Strengthens the existence side (the order lists every function's block); the right-to-left direction does not use it. | harmless |

- **Depth.** substantive. Constructs the order: the blocks sorted (List.mergeSort) by their number of strict condensation descendants, a quantity that strictly decreases along every condensation edge when the condensation is acyclic. The right-to-left direction is the helper condensationAcyclic_of_calleesFirst.
- **Non-vacuity witness** (`topoOrder_nonvacuous`). For 0 -> 1 with singleton blocks, the condensation is acyclic and [1, 0] is a duplicate-free covering callees-first order; for the split 2-cycle both sides fail.

```lean
-- lean/Toy/Scc/Decomp.lean:263-268
theorem topoOrder_nonvacuous :
    (CondensationAcyclic gPath idComp ∧
        ([1, 0] : List (Fin 2)).Nodup ∧ Covers (idComp (n := 2)) [1, 0] ∧
          CalleesFirst gPath idComp [1, 0]) ∧
      (¬ CondensationAcyclic gCycle idComp ∧
        ∀ order : List (Fin 2), ¬ CalleesFirst gCycle idComp order)
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Graph.lean:247-248
theorem condensationAcyclic_of_calleesFirst {n k : Nat} {E : Graph n} {comp : Fin n → Fin k}
    {order : List (Fin k)} (h : CalleesFirst E comp order) : CondensationAcyclic E comp

-- lean/Toy/Scc/Graph.lean:225-227
theorem pos_injective_on_used_blocks_of_covers {n k : Nat} {comp : Fin n → Fin k}
    {order : List (Fin k)} (h : Covers comp order) :
    ∀ f g, pos order (comp f) = pos order (comp g) → comp f = comp g

-- lean/Toy/Scc/Graph.lean:374
theorem not_calleesFirst_gPath_omitted_caller : ¬ CalleesFirst gPath idComp [1]

-- lean/Toy/Scc/Graph.lean:375
theorem not_calleesFirst_gPath_omitted_callee : ¬ CalleesFirst gPath idComp [0]
```

- **Tier justification.** Existence of a topological order of a finite acyclic graph (Kahn 1962; mechanized in Coq, see prior art), restated for the condensation in callees-first form.
- **Prior art.**
  - A. B. Kahn, "Topological sorting of large networks", Communications of the ACM 5(11):558-562, 1962, doi:10.1145/368996.369025. Constructs a topological order of any finite acyclic directed graph.
  - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160, 1972, doi:10.1137/0201010. Linear-time algorithm for the strongly connected components of a directed graph; the SCC partition itself is the background notion formalized here.
  - rocq-community/tarjan, commit 34fe042cc482e65d27bc68b455d922d47da81c9d: theories/kosaraju.v, lemma tseq_correct (the computed sequence tseq is topologically sorted and contains every node), and theories/acyclic_tsorted.v, lemma tseq_connect_before (in an acyclic graph, connect g x y implies that x comes before y in tseq). A mechanized existence-and-construction of a topological order on vertices of a finite acyclic graph.
  - AbsInt/CompCert, https://github.com/AbsInt/CompCert, commit 2685140bf72c959446981fb99b5e44a8975021bc, lib/Postorder.v (theorem postorder_correct): a Coq-verified postorder numbering of a directed graph.
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
- **Design question.** An untrusted producer can supply (comp, order) and a checker can verify CalleesFirst edge-locally (membership and one position comparison per cross-block call) instead of recomputing reachability; this card says that no acyclic decomposition is lost by requiring such an order.

Basis: execution (Lean kernel check). `condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). An untrusted producer can ship `(comp, order)`; a checker verifies `Covers` and `CalleesFirst` with one membership test per function and one position comparison per cross-block call. The theorem says no acyclic decomposition is lost by insisting on such an order. Tarjan's algorithm, for example, emits SCCs in reverse topological order of the condensation (callees first when edges point from caller to callee), so a tool using it obtains a candidate order for free; that such an order satisfies `CalleesFirst` and `Covers` is a property of the algorithm that is not proved here, and the checker does not rely on it.

### Kleene iteration and single-pass bottom-up solving

#### kleene-bound — `iter_bot_isLeastFixpoint_of_monotone_of_height_le`, `iter_top_isGreatestFixpoint_of_monotone_of_height_le`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** substantive. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For a monotone transfer F on summary vectors Fin n -> (Fin m -> Bool) ordered pointwise, at least n*m rounds of iteration from the all-false vector give the least fixpoint of F, and at least n*m rounds from the all-true vector give the greatest fixpoint (n*m, the number of bits, is the height of this lattice).

```lean
-- lean/Toy/Scc/Fixpoint.lean:173-175
theorem iter_bot_isLeastFixpoint_of_monotone_of_height_le {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {fuel : Nat} (hfuel : n * m ≤ fuel) :
    IsLeastFixpoint F (iter F fuel bot)

-- lean/Toy/Scc/Fixpoint.lean:183-185
theorem iter_top_isGreatestFixpoint_of_monotone_of_height_le {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {fuel : Nat} (hfuel : n * m ≤ fuel) :
    IsGreatestFixpoint F (iter F fuel top)
```

*Unfolded (prose)*

```text
For F : (Fin n → Fin m → Bool) → (Fin n → Fin m → Bool) with σ ≤ τ → F σ ≤ F τ (pointwise ≤ on bits), and n * m ≤ fuel:
  Fᶠᵘᵉˡ(all-false) is a fixpoint of F and lies below every fixpoint of F;
  Fᶠᵘᵉˡ(all-true)  is a fixpoint of F and lies above every fixpoint of F.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Without monotonicity a transfer may have no fixpoint at all. | tight: counterexample `kleeneLfp_tight_monotone`, `kleeneGfp_tight_monotone` |
| `hfuel : n * m <= fuel` | n*m is the height of the lattice; fewer rounds can stop before the chain stabilizes. | tight: counterexample `kleeneLfp_tight_fuel`, `kleeneGfp_tight_fuel` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Fixpoint.lean:191-192
theorem kleeneLfp_tight_monotone :
    1 * 1 ≤ 1 ∧ ¬ Monotone negT ∧ ¬ IsLeastFixpoint negT (iter negT 1 bot)

-- lean/Toy/Scc/Fixpoint.lean:199-200
theorem kleeneGfp_tight_monotone :
    1 * 1 ≤ 1 ∧ ¬ Monotone negT ∧ ¬ IsGreatestFixpoint negT (iter negT 1 top)

-- lean/Toy/Scc/Fixpoint.lean:195-196
theorem kleeneLfp_tight_fuel :
    Monotone chainLfpT ∧ ¬ (2 * 1 ≤ 1) ∧ ¬ IsLeastFixpoint chainLfpT (iter chainLfpT 1 bot)

-- lean/Toy/Scc/Fixpoint.lean:203-205
theorem kleeneGfp_tight_fuel :
    Monotone chainGfpT ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsGreatestFixpoint chainGfpT (iter chainGfpT 1 top)
```

- **Depth.** substantive. Counting argument: along the monotone Kleene chain every round that is not yet fixed strictly increases (resp. decreases) the number of set bits, which lies between 0 and n*m.
- **Non-vacuity witness** (`kleene_nonvacuous`). The monotone transfer seedCopyT on 0 -> 1 with two bits per function (n*m = 4): after 4 rounds from either end the iteration reaches the unique fixpoint, after 1 round it has not.

```lean
-- lean/Toy/Scc/Fixpoint.lean:209-212
theorem kleene_nonvacuous :
    Monotone seedCopyT ∧ 2 * 2 ≤ 4 ∧ iter seedCopyT 4 bot = seedCopyFix ∧
      iter seedCopyT 4 top = seedCopyFix ∧ iter seedCopyT 1 bot ≠ seedCopyFix ∧
      iter seedCopyT 1 top ≠ seedCopyFix
```

- **Tier justification.** Kleene iteration on a finite-height lattice (Kleene 1952; Cousot and Cousot 1979; textbook in Nielson, Nielson and Hankin 1999), restated for summary vectors.
- **Prior art.**
  - S. C. Kleene, Introduction to Metamathematics, Van Nostrand, 1952, Section 66, Theorem XXVI (first recursion theorem): the least solution of a recursive functional equation is the union of the iterates of the functional starting from the empty function.
  - P. Cousot, R. Cousot, "Constructive versions of Tarski's fixed point theorems", Pacific Journal of Mathematics 82(1):43-57, 1979, doi:10.2140/pjm.1979.82.43. Characterizes the extremal fixpoints of a monotone map on a complete lattice as limits of (in general transfinite) iteration sequences; on the finite lattices here the iteration is finite and bounded by the height.
  - F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999, doi:10.1007/978-3-662-03811-6. Textbook account of monotone frameworks: under the ascending chain condition, iteration from the bottom element stabilizes at the least fixpoint (widening is used otherwise).
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints. It is an existence result; the iteration bound of this card does not come from it.
- **Design question.** Bounds the work of each per-SCC inner iteration and justifies a fixed fuel in a checked implementation.

Basis: execution (Lean kernel check). `iter_bot_isLeastFixpoint_of_monotone_of_height_le`, `iter_top_isGreatestFixpoint_of_monotone_of_height_le` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `iter_bot_isLeastFixpoint_of_monotone_of_height_le`: `Classical.choice`, `Quot.sound`, `propext`; `iter_top_isGreatestFixpoint_of_monotone_of_height_le`: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A per-block or whole-program fixpoint iteration over a finite powerset domain of `n * m` bits may stop after `n * m` rounds (or earlier at stability) and return the extremal fixpoint, provided the transfer is monotone. For domains that are not finite powersets, the bound is the lattice height, which this package does not prove; for infinite-height domains no bound exists and widening is needed.

#### bottomup-lfp — `bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** If F is monotone and the equation of each function reads only the summaries of its callees in E, then for any block map comp and any list of blocks that contains every function's block and is callees-first, one pass over the list (one block solve per list entry), solving each block by at least n*m rounds of Kleene iteration from the empty set with all other summaries frozen and starting from the all-false vector, yields the global least fixpoint of F.

```lean
-- lean/Toy/Scc/Transfer.lean:74-78
theorem bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) :
    IsLeastFixpoint F (bottomUpLfp F comp order fuel)
```

*Unfolded (prose)*

```text
Assume F monotone; F σ f depends only on σ g for callees g of f (E f g = true); every function's block occurs in order;
for every call f → g with comp f ≠ comp g, both blocks occur in order and comp g first occurs strictly before comp f; n * m ≤ fuel.
Let σ₀ = all-false and, for each entry c of order in turn, σ ← (blockOp F comp c σ)ᶠᵘᵉˡ(σ with block c reset to ∅),
where blockOp F comp c σ τ f = (if comp f = c then F τ f else σ f).
Then the final σ satisfies F σ = σ and σ ≤ τ for every τ with F τ = τ.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Needed for least fixpoints to exist and for the inner iteration to converge to them. | tight: counterexample `bottomUpLfp_tight_monotone` |
| `hresp : RespectsCalls E F` | Ties the equations to the call graph; otherwise an equation may read a block that is solved later. | tight: counterexample `bottomUpLfp_tight_respectsCalls` |
| `hcover : Covers comp order` | Every block must be solved at least once (a block without cross-block calls is not forced into the order by CalleesFirst). | tight: counterexample `bottomUpLfp_tight_covers` |
| `hfirst : CalleesFirst E comp order` | Callee blocks must be final before their callers are solved. | tight: counterexample `bottomUpLfp_tight_calleesFirst` |
| `hfuel : n * m <= fuel` | The inner iteration must reach the block's least fixpoint. | tight: counterexample `bottomUpLfp_tight_fuel` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Transfer.lean:84-87
theorem bottomUpLfp_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ IsLeastFixpoint negT (bottomUpLfp negT oneComp [0] 1)

-- lean/Toy/Scc/Transfer.lean:91-94
theorem bottomUpLfp_tight_respectsCalls :
    Monotone chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainLfpT ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2)

-- lean/Toy/Scc/Transfer.lean:100-103
theorem bottomUpLfp_tight_covers :
    Monotone (topT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (topT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ IsLeastFixpoint (topT (n := 1) (m := 1)) (bottomUpLfp (topT (n := 1) (m := 1)) oneComp [] 1)

-- lean/Toy/Scc/Transfer.lean:107-110
theorem bottomUpLfp_tight_calleesFirst :
    Monotone chainLfpT ∧ RespectsCalls gPath chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2)

-- lean/Toy/Scc/Transfer.lean:121-124
theorem bottomUpLfp_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainLfpT ∧ RespectsCalls gCycle chainLfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT oneComp [0] 1)
```

- **Depth.** shallow. Depth is measured relative to the other cards of this package. Given bottomup-mixed (the pass computes the unique hierarchical solution), the global least fixpoint (kleene-bound) is an all-least hierarchical solution, because its meet with any block fixpoint is a prefixpoint (prefix-postfix-sound); uniqueness identifies the two. The induction along the order is in bottomup-mixed.
- **Non-vacuity witness** (`bottomUpLfp_nonvacuous`). The graph 0 -> 0, 0 -> 1, 1 -> 1 with singleton blocks (a condensation edge and two recursive blocks), order [1, 0], fuel 2, and the monotone callee-local transfer F(0) = sigma(0) union sigma(1), F(1) = {0} union sigma(1).

```lean
-- lean/Toy/Scc/Transfer.lean:144-147
theorem bottomUpLfp_nonvacuous :
    IsSccDecomp gMix idComp ∧ Monotone mixLfpT ∧ RespectsCalls gMix mixLfpT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      CondEdge gMix idComp 0 1 ∧ gMix 0 0 = true ∧ gMix 1 1 = true
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Transfer.lean:17-19
theorem hierSolution_of_isLeastFixpoint {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    (comp : Fin n → Fin k) {μ : Summ n m} (hμ : IsLeastFixpoint F μ) :
    HierSolution F comp (fun _ => true) μ

-- lean/Toy/Scc/BottomUp.lean:302-306
theorem hierSolution_bottomUp {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat} (hmono : Monotone F)
    (hresp : RespectsCalls E F) (hcover : Covers comp order) (hfirst : CalleesFirst E comp order)
    (hfuel : n * m ≤ fuel) (sign : Fin k → Bool) (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init)

-- lean/Toy/Scc/BottomUp.lean:351-354
theorem hierSolution_unique {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} (hresp : RespectsCalls E F)
    (hfirst : CalleesFirst E comp order) {sign : Fin k → Bool} {σ σ' : Summ n m}
    (h : HierSolution F comp sign σ) (h' : HierSolution F comp sign σ') : σ = σ'
```

- **Tier justification.** Known: solving the SCCs of a dependency graph in reverse topological order, each by fixpoint iteration, yields the least solution of a monotone equation system (Bekic's theorem in DAG form; SCC-structured iteration strategies; block-wise solving of alternation-free equation systems). Restated here for arbitrary block maps, with every hypothesis shown necessary.
- **Prior art.**
  - H. Bekic, "Definable operations in general algebras, and the theory of automata and flowcharts", 1969 report, reprinted in C. B. Jones (ed.), Programming Languages and Their Definition, LNCS 177, Springer, 1984, pp. 30-55, doi:10.1007/BFb0048939. Source of Bekic's theorem: a simultaneous least fixpoint can be computed as nested single least fixpoints. It concerns least fixpoints only; the per-block decomposition here is a DAG-shaped instance.
  - G. Winskel, The Formal Semantics of Programming Languages, MIT Press, 1993, Section 10.1 (Bekic's theorem). Textbook statement and proof of Bekic's theorem for least fixpoints.
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
  - R. Cleaveland, B. Steffen, "A linear-time model-checking algorithm for the alternation-free modal mu-calculus", Formal Methods in System Design 2(2):121-147, 1993, doi:10.1007/BF01383878. Model checking by translation into equational blocks of least and greatest fixpoint equations in the alternation-free case, solved block by block.
  - M. G. Burke, "An interval-based approach to exhaustive and incremental interprocedural data-flow analysis", ACM Transactions on Programming Languages and Systems 12(3):341-395, 1990, doi:10.1145/78969.78963. Interval-based (structure-directed) interprocedural data-flow analysis, as opposed to iterating over the whole program.
  - M. Sharir, A. Pnueli, "Two approaches to interprocedural data flow analysis", in S. S. Muchnick and N. D. Jones (eds.), Program Flow Analysis: Theory and Applications, Prentice-Hall, 1981, pp. 189-233. The functional approach computes for each procedure a summary function (a transformer on the data-flow lattice, so summaries are context-dependent) as the solution of an equation system, by iterative (worklist-style) solving; the second approach uses call strings. This package abstracts only the shape of per-procedure summary equations, with one summary value per function, and studies a single pass in a fixed block order rather than worklist solving.
  - T. Reps, S. Horwitz, M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", POPL 1995, pp. 49-61, doi:10.1145/199448.199462. IFDS: finite distributive subset problems as realizable-path reachability, solved by tabulation over path and summary edges; context sensitivity (the exploded supergraph) is not modeled here.
  - P. Cousot, "Asynchronous iterative methods for solving a fixed point system of monotone equations in a complete lattice", Research Report R.R. 88, Laboratoire IMAG, Universite scientifique et medicale de Grenoble, September 1977. Asynchronous (chaotic) iteration solves systems of monotone equations; this package instead studies a single pass in a fixed block order, where the order matters.
  - J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy, D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966. A static analyzer (Verasco) proved sound in Coq; fixpoint-based analysis in a verified setting, at the level of a whole analyzer rather than this package's abstract block decomposition.
- **Design question.** When is bottom-up composition of per-SCC fixpoints equal to the whole-program fixpoint, and which conditions does an SCC-boundary checker need so that an untrusted decomposition can be accepted? Answer for least fixpoints: monotone, callee-local transfers, a covering callees-first order and sufficient inner fuel suffice; SCC minimality is not needed.

Basis: execution (Lean kernel check). `bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A summary-based analysis that solves the call-graph blocks once, in callees-first order, with a monotone transfer whose equations read only callee summaries and an inner iteration of at least the lattice height (or to stability) computes the whole-program least fixpoint, for any block map with a covering callees-first order; an SCC decomposition is not required. Real analyses with context-sensitive summaries, widening, or equations that read non-callee state (globals, the heap via callers) do not instantiate `RespectsCalls` over the plain call graph without additional modeling.

#### bottomup-gfp — `bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** Under the same hypotheses as bottomup-lfp (monotone, callee-local F; a covering callees-first list of blocks; inner fuel at least n*m), one pass over the list (one block solve per list entry), solving each block by Kleene iteration from the full set with all other summaries frozen and starting from the all-true vector, yields the global greatest fixpoint of F.

```lean
-- lean/Toy/Scc/Transfer.lean:154-158
theorem bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) :
    IsGreatestFixpoint F (bottomUpGfp F comp order fuel)
```

*Unfolded (prose)*

```text
Same hypotheses as bottomup-lfp. Let σ₀ = all-true and solve each listed block from the full set
(σ with block c reset to all-true). Then the final σ satisfies F σ = σ and τ ≤ σ for every τ with F τ = τ.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Needed for greatest fixpoints to exist and for the inner iteration to converge to them. | tight: counterexample `bottomUpGfp_tight_monotone` |
| `hresp : RespectsCalls E F` | Ties the equations to the call graph. | tight: counterexample `bottomUpGfp_tight_respectsCalls` |
| `hcover : Covers comp order` | Every block must be solved at least once. | tight: counterexample `bottomUpGfp_tight_covers` |
| `hfirst : CalleesFirst E comp order` | Callee blocks must be final before their callers are solved. | tight: counterexample `bottomUpGfp_tight_calleesFirst` |
| `hfuel : n * m <= fuel` | The inner iteration must reach the block's greatest fixpoint. | tight: counterexample `bottomUpGfp_tight_fuel` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Transfer.lean:171-174
theorem bottomUpGfp_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ IsGreatestFixpoint negT (bottomUpGfp negT oneComp [0] 1)

-- lean/Toy/Scc/Transfer.lean:178-181
theorem bottomUpGfp_tight_respectsCalls :
    Monotone chainGfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainGfpT ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2)

-- lean/Toy/Scc/Transfer.lean:189-192
theorem bottomUpGfp_tight_covers :
    Monotone (botT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (botT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ IsGreatestFixpoint (botT (n := 1) (m := 1)) (bottomUpGfp (botT (n := 1) (m := 1)) oneComp [] 1)

-- lean/Toy/Scc/Transfer.lean:196-199
theorem bottomUpGfp_tight_calleesFirst :
    Monotone chainGfpT ∧ RespectsCalls gPath chainGfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2)

-- lean/Toy/Scc/Transfer.lean:203-206
theorem bottomUpGfp_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainGfpT ∧ RespectsCalls gCycle chainGfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT oneComp [0] 1)
```

- **Depth.** shallow. Dual of bottomup-lfp: given bottomup-mixed, the global greatest fixpoint is an all-greatest hierarchical solution because its join with any block fixpoint is a postfixpoint (prefix-postfix-sound).
- **Non-vacuity witness** (`bottomUpGfp_nonvacuous`). The graph 0 -> 0, 0 -> 1, 1 -> 1 with singleton blocks, order [1, 0], fuel 2, and the monotone callee-local transfer F(0) = sigma(0) intersect sigma(1), F(1) = empty.

```lean
-- lean/Toy/Scc/Transfer.lean:211-214
theorem bottomUpGfp_nonvacuous :
    IsSccDecomp gMix idComp ∧ Monotone mixGfpT ∧ RespectsCalls gMix mixGfpT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      CondEdge gMix idComp 0 1 ∧ gMix 0 0 = true ∧ gMix 1 1 = true
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Transfer.lean:44-46
theorem hierSolution_of_isGreatestFixpoint {n m k : Nat} {F : Transfer n m} (hmono : Monotone F)
    (comp : Fin n → Fin k) {ν : Summ n m} (hν : IsGreatestFixpoint F ν) :
    HierSolution F comp (fun _ => false) ν

-- lean/Toy/Scc/BottomUp.lean:302-306
theorem hierSolution_bottomUp {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat} (hmono : Monotone F)
    (hresp : RespectsCalls E F) (hcover : Covers comp order) (hfirst : CalleesFirst E comp order)
    (hfuel : n * m ≤ fuel) (sign : Fin k → Bool) (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init)

-- lean/Toy/Scc/BottomUp.lean:351-354
theorem hierSolution_unique {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} (hresp : RespectsCalls E F)
    (hfirst : CalleesFirst E comp order) {sign : Fin k → Bool} {σ σ' : Summ n m}
    (h : HierSolution F comp sign σ) (h' : HierSolution F comp sign σ') : σ = σ'
```

- **Tier justification.** Dual of bottomup-lfp; block-wise solving of greatest-fixpoint equation blocks is known from alternation-free equation systems. Restated here with every hypothesis shown necessary.
- **Prior art.**
  - R. Cleaveland, B. Steffen, "A linear-time model-checking algorithm for the alternation-free modal mu-calculus", Formal Methods in System Design 2(2):121-147, 1993, doi:10.1007/BF01383878. Model checking by translation into equational blocks of least and greatest fixpoint equations in the alternation-free case, solved block by block.
  - A. Mader, Verification of Modal Properties Using Boolean Equation Systems, Edition versal 8, Bertz Verlag, Berlin, 1997, ISBN 3-929470-58-6 (PhD thesis, TU Munchen). Boolean equation systems with least and greatest fixpoint equations, their semantics, and Gauss elimination; the solution in general depends on the order of the equations.
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints.
- **Design question.** When is bottom-up composition of per-SCC greatest fixpoints equal to the whole-program greatest fixpoint? Answer: under the same conditions as for least fixpoints.

Basis: execution (Lean kernel check). `bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Same bridge as `bottomup-lfp`, for greatest-fixpoint (must-, safety-style) summaries solved from the full set.

#### bottomup-one-sided — `bottomUpLfp_le_of_monotone_of_prefixpoint`, `le_bottomUpGfp_of_monotone_of_postfixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For monotone F, the single-pass bottom-up least computation (start all-false) lies below every prefixpoint of F, in particular below the least fixpoint, for every block map, every list of blocks (callees-first or not, covering or not) and every fuel; dually, the single-pass greatest computation (start all-true) lies above every postfixpoint, in particular above the greatest fixpoint.

```lean
-- lean/Toy/Scc/Fixpoint.lean:220-222
theorem bottomUpLfp_le_of_monotone_of_prefixpoint {n m k : Nat} {F : Transfer n m}
    (hmono : Monotone F) {τ : Summ n m} (hpre : Le (F τ) τ) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Le (bottomUpLfp F comp order fuel) τ

-- lean/Toy/Scc/Fixpoint.lean:242-244
theorem le_bottomUpGfp_of_monotone_of_postfixpoint {n m k : Nat} {F : Transfer n m}
    (hmono : Monotone F) {τ : Summ n m} (hpost : Le τ (F τ)) (comp : Fin n → Fin k)
    (order : List (Fin k)) (fuel : Nat) : Le τ (bottomUpGfp F comp order fuel)
```

*Unfolded (prose)*

```text
For monotone F, every τ with F τ ≤ τ, every comp, every order (any list of blocks) and every fuel:
  bottomUpLfp F comp order fuel ≤ τ.
Dually, for every τ with τ ≤ F τ:  τ ≤ bottomUpGfp F comp order fuel.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Without it a single application of F can jump above a prefixpoint (or below a postfixpoint). | tight: counterexample `oneSidedLfp_tight_monotone`, `oneSidedGfp_tight_monotone` |
| `hpre : F tau <= tau (resp. hpost : tau <= F tau)` | Identifies the bound tau; an arbitrary vector is not a bound. | tight: counterexample `oneSidedLfp_tight_prefixpoint`, `oneSidedGfp_tight_postfixpoint` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Fixpoint.lean:262-264
theorem oneSidedLfp_tight_monotone :
    ¬ Monotone nmLfpT ∧ Le (nmLfpT only0) only0 ∧
      ¬ Le (bottomUpLfp nmLfpT oneComp [0] 1) only0

-- lean/Toy/Scc/Fixpoint.lean:272-274
theorem oneSidedGfp_tight_monotone :
    ¬ Monotone nmGfpT ∧ Le only1 (nmGfpT only1) ∧
      ¬ Le only1 (bottomUpGfp nmGfpT oneComp [0] 1)

-- lean/Toy/Scc/Fixpoint.lean:267-269
theorem oneSidedLfp_tight_prefixpoint :
    Monotone (topT (n := 1) (m := 1)) ∧ ¬ Le (topT (bot : Summ 1 1)) bot ∧
      ¬ Le (bottomUpLfp (topT (n := 1) (m := 1)) oneComp [0] 1) bot

-- lean/Toy/Scc/Fixpoint.lean:277-279
theorem oneSidedGfp_tight_postfixpoint :
    Monotone (botT (n := 1) (m := 1)) ∧ ¬ Le (top : Summ 1 1) (botT top) ∧
      ¬ Le top (bottomUpGfp (botT (n := 1) (m := 1)) oneComp [0] 1)
```

- **Depth.** shallow. Induction over the order and the inner iterations, keeping the invariant "current vector <= tau" (resp. ">=").
- **Non-vacuity witness** (`oneSided_nonvacuous`). The monotone transfer seedCopyT on 0 -> 1 with two bits per function, a prefixpoint other than all-true and a postfixpoint other than all-false, exercised at the caller-first order [0, 1], where the single-pass least result is strictly below the least fixpoint and the greatest result strictly above the greatest fixpoint.

```lean
-- lean/Toy/Scc/Fixpoint.lean:286-293
theorem oneSided_nonvacuous :
    Monotone seedCopyT ∧ Le (seedCopyT seedCopyPre) seedCopyPre ∧ seedCopyPre ≠ top ∧
      Le seedCopyPost (seedCopyT seedCopyPost) ∧ seedCopyPost ≠ bot ∧
      ¬ CalleesFirst gPath idComp [0, 1] ∧
      bottomUpLfp seedCopyT idComp [0, 1] 4 ≠ seedCopyFix ∧
      Le (bottomUpLfp seedCopyT idComp [0, 1] 4) seedCopyFix ∧
      bottomUpGfp seedCopyT idComp [0, 1] 4 ≠ seedCopyFix ∧
      Le seedCopyFix (bottomUpGfp seedCopyT idComp [0, 1] 4)
```

- **Tier justification.** An instance of Park induction (iterates of a monotone map from the bottom stay below every prefixpoint), applied to the single-pass bottom-up algorithm.
- **Prior art.**
  - D. M. R. Park, "Fixpoint induction and proofs of program properties", in B. Meltzer and D. Michie (eds.), Machine Intelligence 5, Edinburgh University Press, 1969 (some catalogs list 1970), pp. 59-78. Fixpoint induction: the least fixpoint of a monotone map lies below every prefixpoint (Park induction).
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints.
- **Design question.** Tells a checker in which direction an unchecked order or decomposition can go wrong: single-pass least results can only lose facts and single-pass greatest results can only gain facts.

Basis: execution (Lean kernel check). `bottomUpLfp_le_of_monotone_of_prefixpoint`, `le_bottomUpGfp_of_monotone_of_postfixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `bottomUpLfp_le_of_monotone_of_prefixpoint`: `propext`; `le_bottomUpGfp_of_monotone_of_postfixpoint`: `propext`.

Basis: derived (modeling bridge). If a tool does not check its decomposition or order, a least-fixpoint (may-fact) summary computed by one pass can only miss facts relative to the least fixpoint, and a greatest-fixpoint (must-fact) summary can only contain extra facts relative to the greatest fixpoint. Whether a missed or extra fact is a soundness problem depends on how the client reads the summary, which this card does not decide.

#### bottomup-mixed — `bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`, `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** substantive. **Modules:** `Toy.Scc.Transfer`, `Toy.Scc.BottomUp`.
- **Plain claim.** Under the hypotheses of bottomup-lfp, for every per-block sign assignment (least or greatest inner fixpoint per block) and every start vector, single-pass bottom-up computes a vector in which every block is the least (resp. greatest) fixpoint of that block's equations when all other blocks are frozen, as constants, at their values in the same vector (HierSolution, coordinatewise block-extremality), and no other vector has this property. Every vector with this property is a fixpoint of F and lies between the least and the greatest fixpoint of F.

```lean
-- lean/Toy/Scc/Transfer.lean:222-228
theorem bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le {n m k : Nat} {E : Graph n}
    {F : Transfer n m} {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat}
    (hmono : Monotone F) (hresp : RespectsCalls E F) (hcover : Covers comp order)
    (hfirst : CalleesFirst E comp order) (hfuel : n * m ≤ fuel) (sign : Fin k → Bool)
    (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init) ∧
      ∀ σ, HierSolution F comp sign σ → σ = bottomUp F comp sign order fuel init

-- lean/Toy/Scc/BottomUp.lean:84-87
theorem le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint {n m k : Nat}
    {F : Transfer n m} {comp : Fin n → Fin k} {sign : Fin k → Bool} {μ ν σ : Summ n m}
    (hμ : IsLeastFixpoint F μ) (hν : IsGreatestFixpoint F ν)
    (h : HierSolution F comp sign σ) : Le μ σ ∧ Le σ ν

-- lean/Toy/Scc/BottomUp.lean:76-77
theorem HierSolution.fixpoint {n m k : Nat} {F : Transfer n m} {comp : Fin n → Fin k}
    {sign : Fin k → Bool} {σ : Summ n m} (h : HierSolution F comp sign σ) : F σ = σ
```

`HierSolution.fixpoint` is listed among this card's result names (it supplies the clause "every vector with this property is a fixpoint of F"); its statement and closure are hashed with the card's other theorems.

*Unfolded (prose)*

```text
Under the hypotheses of bottomup-lfp, for every sign : Fin k → Bool and every start vector init, with
σ* := bottomUp F comp sign order fuel init (block c solved from ∅ if sign c = true, from the full set otherwise):
  (1) ∀ c, blockOp F comp c σ* σ* = σ*  ∧  ∀ τ, blockOp F comp c σ* τ = τ → (if sign c then σ* ≤ τ else τ ≤ σ*);
  (2) every σ satisfying (1) in place of σ* equals σ*.
Betweenness (no hypothesis on F beyond those stated): if σ satisfies (1), μ is the least and ν the greatest fixpoint of F,
then μ ≤ σ ≤ ν; and HierSolution.fixpoint: if σ satisfies (1), then F σ = σ.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Needed for block-level extremal fixpoints to exist. | tight: counterexample `bottomUpHier_tight_monotone` |
| `hresp : RespectsCalls E F` | Ties the equations to the call graph. | tight: counterexample `bottomUpHier_tight_respectsCalls` |
| `hcover : Covers comp order` | Every block must be solved. | tight: counterexample `bottomUpHier_tight_covers` |
| `hfirst : CalleesFirst E comp order` | Callee blocks must be final first; this also excludes cyclic dependencies between blocks of different signs, under which uniqueness fails (shown at a mixed sign assignment). | tight: counterexample `bottomUpHier_tight_calleesFirst` |
| `hfuel : n * m <= fuel` | Inner iterations must converge. | tight: counterexample `bottomUpHier_tight_fuel` |
| `betweenness lemma, h : HierSolution F comp sign sigma` | Without it sigma need not be a fixpoint, hence need not lie between the extremal fixpoints. | tight: counterexample `hierBetween_tight_hierSolution` |
| `betweenness lemma, hmu : IsLeastFixpoint F mu` | Identifies the lower bound; another fixpoint need not be below sigma. | tight: counterexample `hierBetween_tight_least` |
| `betweenness lemma, hnu : IsGreatestFixpoint F nu` | Identifies the upper bound; another fixpoint need not be above sigma. | tight: counterexample `hierBetween_tight_greatest` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Transfer.lean:239-244
theorem bottomUpHier_tight_monotone :
    ¬ Monotone negT ∧ RespectsCalls gLoop negT ∧ Covers (oneComp (n := 1)) [0] ∧
      CalleesFirst gLoop oneComp [0] ∧ 1 * 1 ≤ 1 ∧
      ¬ (HierSolution negT oneComp (fun _ => true) (bottomUp negT oneComp (fun _ => true) [0] 1 bot) ∧
        ∀ σ, HierSolution negT oneComp (fun _ => true) σ →
          σ = bottomUp negT oneComp (fun _ => true) [0] 1 bot)

-- lean/Toy/Scc/Transfer.lean:248-254
theorem bottomUpHier_tight_respectsCalls :
    Monotone chainLfpT ∧ Covers (idComp (n := 2)) [0, 1] ∧ CalleesFirst gEmpty idComp [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ RespectsCalls gEmpty chainLfpT ∧
      ¬ (HierSolution chainLfpT idComp (fun _ => true)
            (bottomUp chainLfpT idComp (fun _ => true) [0, 1] 2 bot) ∧
        ∀ σ, HierSolution chainLfpT idComp (fun _ => true) σ →
          σ = bottomUp chainLfpT idComp (fun _ => true) [0, 1] 2 bot)

-- lean/Toy/Scc/Transfer.lean:259-265
theorem bottomUpHier_tight_covers :
    Monotone (topT (n := 1) (m := 1)) ∧ RespectsCalls gLoop (topT (m := 1)) ∧
      CalleesFirst gLoop oneComp [] ∧ 1 * 1 ≤ 1 ∧ ¬ Covers (oneComp (n := 1)) [] ∧
      ¬ (HierSolution (topT (n := 1) (m := 1)) oneComp (fun _ => true)
            (bottomUp (topT (n := 1) (m := 1)) oneComp (fun _ => true) [] 1 bot) ∧
        ∀ σ, HierSolution (topT (n := 1) (m := 1)) oneComp (fun _ => true) σ →
          σ = bottomUp (topT (n := 1) (m := 1)) oneComp (fun _ => true) [] 1 bot)

-- lean/Toy/Scc/Transfer.lean:272-277
theorem bottomUpHier_tight_calleesFirst :
    Monotone swapT ∧ RespectsCalls gCycle swapT ∧ Covers (idComp (n := 2)) [0, 1] ∧
      2 * 1 ≤ 2 ∧ ¬ CalleesFirst gCycle idComp [0, 1] ∧
      ¬ (HierSolution swapT idComp mixSign (bottomUp swapT idComp mixSign [0, 1] 2 bot) ∧
        ∀ σ, HierSolution swapT idComp mixSign σ →
          σ = bottomUp swapT idComp mixSign [0, 1] 2 bot)

-- lean/Toy/Scc/Transfer.lean:283-289
theorem bottomUpHier_tight_fuel :
    IsSccDecomp gCycle oneComp ∧ Monotone chainLfpT ∧ RespectsCalls gCycle chainLfpT ∧
      Covers (oneComp (n := 2)) [0] ∧ CalleesFirst gCycle oneComp [0] ∧ ¬ (2 * 1 ≤ 1) ∧
      ¬ (HierSolution chainLfpT oneComp (fun _ => true)
            (bottomUp chainLfpT oneComp (fun _ => true) [0] 1 bot) ∧
        ∀ σ, HierSolution chainLfpT oneComp (fun _ => true) σ →
          σ = bottomUp chainLfpT oneComp (fun _ => true) [0] 1 bot)

-- lean/Toy/Scc/Transfer.lean:340-343
theorem hierBetween_tight_hierSolution :
    IsLeastFixpoint chainLfpT top ∧ IsGreatestFixpoint chainLfpT top ∧
      ¬ HierSolution chainLfpT idComp (fun _ => true) bot ∧
      ¬ (Le (top : Summ 2 1) bot ∧ Le (bot : Summ 2 1) top)

-- lean/Toy/Scc/Transfer.lean:351-354
theorem hierBetween_tight_least :
    ¬ IsLeastFixpoint idT top ∧ IsGreatestFixpoint idT top ∧
      HierSolution idT oneComp (fun _ => true) bot ∧
      ¬ (Le (top : Summ 1 1) bot ∧ Le (bot : Summ 1 1) top)

-- lean/Toy/Scc/Transfer.lean:361-364
theorem hierBetween_tight_greatest :
    IsLeastFixpoint idT bot ∧ ¬ IsGreatestFixpoint idT bot ∧
      HierSolution idT oneComp (fun _ => false) top ∧
      ¬ (Le (bot : Summ 1 1) top ∧ Le (top : Summ 1 1) bot)
```

- **Depth.** substantive. Existence by induction along the order (a block solved at its first occurrence stays solved when later blocks change, because CalleesFirst forbids it from reading them, and re-solving an already solved block changes nothing); uniqueness by strong induction on block positions; both use the inner-iteration bound for arbitrary start vectors. The betweenness lemma is immediate from HierSolution.fixpoint.
- **Non-vacuity witness** (`bottomUpHier_nonvacuous`, `hierBetween_nonvacuous`). The graph 0 -> 0, 0 -> 1, 1 -> 1, singleton blocks, order [1, 0], with the mixed sign assignment mixSign (callee block 1 least, caller block 0 greatest); for the betweenness lemma, the hierarchical solution of mixed-neither, strictly between the least and greatest fixpoint.

```lean
-- lean/Toy/Scc/Transfer.lean:323-325
theorem bottomUpHier_nonvacuous :
    Monotone mixT ∧ RespectsCalls gMix mixT ∧ Covers (idComp (n := 2)) [1, 0] ∧
      CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧ mixSign 1 = true ∧ mixSign 0 = false

-- lean/Toy/Scc/Transfer.lean:330-332
theorem hierBetween_nonvacuous :
    IsLeastFixpoint mixT bot ∧ IsGreatestFixpoint mixT top ∧
      HierSolution mixT idComp mixSign mixResult ∧ mixResult ≠ bot ∧ mixResult ≠ top
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/BottomUp.lean:302-306
theorem hierSolution_bottomUp {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} {fuel : Nat} (hmono : Monotone F)
    (hresp : RespectsCalls E F) (hcover : Covers comp order) (hfirst : CalleesFirst E comp order)
    (hfuel : n * m ≤ fuel) (sign : Fin k → Bool) (init : Summ n m) :
    HierSolution F comp sign (bottomUp F comp sign order fuel init)

-- lean/Toy/Scc/BottomUp.lean:351-354
theorem hierSolution_unique {n m k : Nat} {E : Graph n} {F : Transfer n m}
    {comp : Fin n → Fin k} {order : List (Fin k)} (hresp : RespectsCalls E F)
    (hfirst : CalleesFirst E comp order) {sign : Fin k → Bool} {σ σ' : Summ n m}
    (h : HierSolution F comp sign σ) (h' : HierSolution F comp sign σ') : σ = σ'

-- lean/Toy/Scc/BottomUp.lean:449-451
theorem hierSolution_swapT_gCycle_mixSign_not_unique :
    HierSolution swapT idComp mixSign bot ∧ HierSolution swapT idComp mixSign top ∧
      (bot : Summ 2 1) ≠ top
```

- **Tier justification.** Alternation-free equation systems with least and greatest blocks solved in dependency order are known (Cleaveland and Steffen 1993; Mader 1997; mechanized operations on such systems in Neele and van de Pol 2024). Restated here for the single-pass bottom-up algorithm and coordinatewise block-extremality.
- **Prior art.**
  - R. Cleaveland, B. Steffen, "A linear-time model-checking algorithm for the alternation-free modal mu-calculus", Formal Methods in System Design 2(2):121-147, 1993, doi:10.1007/BF01383878. Model checking by translation into equational blocks of least and greatest fixpoint equations in the alternation-free case, solved block by block.
  - A. Mader, Verification of Modal Properties Using Boolean Equation Systems, Edition versal 8, Bertz Verlag, Berlin, 1997, ISBN 3-929470-58-6 (PhD thesis, TU Munchen). Boolean equation systems with least and greatest fixpoint equations, their semantics, and Gauss elimination; the solution in general depends on the order of the equations.
  - T. Neele, J. van de Pol, "Operations on fixpoint equation systems", Logical Methods in Computer Science 20(3), paper 5, 2024, doi:10.46298/lmcs-20(3:5)2024 (arXiv:2304.07162); replication package with Coq and PVS proofs, doi:10.5281/zenodo.7828484. Operations such as substitution and reordering on fixpoint equation systems with least and greatest equations over complete lattices, with computer-checked proofs.
  - H. Seidl, "Fast and simple nested fixpoints", Information Processing Letters 59(6):303-308, 1996, doi:10.1016/0020-0190(96)00130-5. Solving nested least/greatest fixpoint equation systems over finite lattices.
  - H. Bekic, "Definable operations in general algebras, and the theory of automata and flowcharts", 1969 report, reprinted in C. B. Jones (ed.), Programming Languages and Their Definition, LNCS 177, Springer, 1984, pp. 30-55, doi:10.1007/BFb0048939. Source of Bekic's theorem: a simultaneous least fixpoint can be computed as nested single least fixpoints. It concerns least fixpoints only; the per-block decomposition here is a DAG-shaped instance.
- **Design question.** If one SCC is summarized by a least fixpoint and a caller SCC by a greatest fixpoint, what does the combined result mean? It is the unique coordinatewise block-extremal solution: a fixpoint of the whole system between the least and greatest fixpoints, but in general neither.

Basis: execution (Lean kernel check). `bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`, `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint`, `HierSolution.fixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le`: `Classical.choice`, `Quot.sound`, `propext`; `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint`: `Quot.sound`, `propext`; `HierSolution.fixpoint`: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A tool that summarizes some blocks by least and others by greatest fixpoints, solved once in callees-first order, computes the unique coordinatewise block-extremal solution, a fixpoint between the least and greatest fixpoints. The meaning of the combined result depends on the sign assignment and on the block map; it coincides with nested (Boolean/fixpoint equation system) semantics only because callees-first order and call-locality rule out cyclic cross-sign dependencies.

#### mixed-neither — `mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp`, `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp`

- **Tier:** T1 (folklore made precise: known informally, not mechanized). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** On the call graph 0 -> 0, 0 -> 1, 1 -> 1 with one bit per function, singleton blocks (a valid SCC decomposition), the callees-first order [1, 0], inner fuel 2 = n*m and start vector all-false: (i) for F(0) = sigma(0) union sigma(1), F(1) = sigma(1), solving the callee block {1} with its least fixpoint and the caller block {0} with its greatest gives sigma(0) = {0}, sigma(1) = empty; (ii) for F(0) = sigma(0) intersect sigma(1), F(1) = sigma(1), solving the callee block with its greatest fixpoint and the caller block with its least gives sigma(0) = empty, sigma(1) = {0}. In both cases the result is the hierarchical solution and a fixpoint of F, but neither the least fixpoint (all-false) nor the greatest fixpoint (all-true); both transfers are monotone and callee-local.

```lean
-- lean/Toy/Scc/Transfer.lean:307-313
theorem mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp :
    IsSccDecomp gMix idComp ∧ Monotone mixT ∧ RespectsCalls gMix mixT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      bottomUp mixT idComp mixSign [1, 0] 2 bot = mixResult ∧
      HierSolution mixT idComp mixSign mixResult ∧ mixT mixResult = mixResult ∧
      IsLeastFixpoint mixT bot ∧ IsGreatestFixpoint mixT top ∧
      ¬ IsLeastFixpoint mixT mixResult ∧ ¬ IsGreatestFixpoint mixT mixResult

-- lean/Toy/Scc/Transfer.lean:385-391
theorem mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp :
    IsSccDecomp gMix idComp ∧ Monotone mixRevT ∧ RespectsCalls gMix mixRevT ∧
      Covers (idComp (n := 2)) [1, 0] ∧ CalleesFirst gMix idComp [1, 0] ∧ 2 * 1 ≤ 2 ∧
      bottomUp mixRevT idComp revSign [1, 0] 2 bot = revResult ∧
      HierSolution mixRevT idComp revSign revResult ∧ mixRevT revResult = revResult ∧
      IsLeastFixpoint mixRevT bot ∧ IsGreatestFixpoint mixRevT top ∧
      ¬ IsLeastFixpoint mixRevT revResult ∧ ¬ IsGreatestFixpoint mixRevT revResult
```

*Unfolded (prose)*

```text
On gMix (0 → 0, 0 → 1, 1 → 1), one bit per function, blocks idComp, order [1, 0], fuel 2, start all-false:
  (i)  mixT:    F 0 = σ 0 ∪ σ 1, F 1 = σ 1; block 1 least, block 0 greatest (mixSign) ⇒ result σ 0 = {0}, σ 1 = ∅ (mixResult);
  (ii) mixRevT: F 0 = σ 0 ∩ σ 1, F 1 = σ 1; block 1 greatest, block 0 least (revSign) ⇒ result σ 0 = ∅, σ 1 = {0} (revResult).
In both cases the result is the hierarchical solution and a fixpoint, the least fixpoint is all-false, the greatest is all-true,
and the result is neither.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computations checked by decide plus certified hierarchical solutions.
- **Non-vacuity witness** (`mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp`, `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp`). The instances themselves; all hypotheses of bottomup-mixed hold there (stated in the theorems). Its statement is the card theorem quoted above.

- Nearby setting where the conclusion fails (no separate Lean theorem): with a uniform sign assignment the single-pass result *is* the least (all blocks least) or the greatest (all blocks greatest) fixpoint, by `bottomup-lfp` / `bottomup-gfp`.

- **Tier justification.** Concrete, kernel-checked instances of a known pitfall (a sign mixture computes neither global extremal fixpoint), for both mixture directions; the general characterization is bottomup-mixed.
- **Prior art.**
  - R. Cleaveland, B. Steffen, "A linear-time model-checking algorithm for the alternation-free modal mu-calculus", Formal Methods in System Design 2(2):121-147, 1993, doi:10.1007/BF01383878. Model checking by translation into equational blocks of least and greatest fixpoint equations in the alternation-free case, solved block by block.
  - A. Mader, Verification of Modal Properties Using Boolean Equation Systems, Edition versal 8, Bertz Verlag, Berlin, 1997, ISBN 3-929470-58-6 (PhD thesis, TU Munchen). Boolean equation systems with least and greatest fixpoint equations, their semantics, and Gauss elimination; the solution in general depends on the order of the equations.
  - T. Neele, J. van de Pol, "Operations on fixpoint equation systems", Logical Methods in Computer Science 20(3), paper 5, 2024, doi:10.46298/lmcs-20(3:5)2024 (arXiv:2304.07162); replication package with Coq and PVS proofs, doi:10.5281/zenodo.7828484. Operations such as substitution and reordering on fixpoint equation systems with least and greatest equations over complete lattices, with computer-checked proofs.
- **Design question.** Shows concretely that mixing least and greatest per-SCC fixpoints, in either direction, computes neither global fixpoint; the exact object is given by bottomup-mixed.

Basis: execution (Lean kernel check). `mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp`, `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp`: `Quot.sound`, `propext`; `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp`: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A tool that mixes least and greatest per-block fixpoints must not report the result as the whole-program least or greatest fixpoint, even with a valid SCC decomposition and a callees-first order.

### Decompositions and orders that break, or do not break, single-pass solving

#### merge-convex — `convex_merge_not_scc_still_lfp_and_gfp`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** On the path 0 -> 1 -> 2, merging 0 and 1 (not mutually reachable) into one block, with 2 in its own block, is not an SCC decomposition, yet [1, 0] is a covering callees-first order with a genuine cross-block call (1 -> 2), and single-pass bottom-up over the merged block map with inner fuel 3 = n*m computes the global least fixpoint of F(2) = {0}, F(1) = sigma(2), F(0) = sigma(1) and the global greatest fixpoint of F(2) = empty, F(1) = sigma(2), F(0) = sigma(1); both transfers are monotone and callee-local.

```lean
-- lean/Toy/Scc/Transfer.lean:423-430
theorem convex_merge_not_scc_still_lfp_and_gfp :
    ¬ IsSccDecomp gPath3 convexMerge3 ∧ IsSccDecomp gPath3 idComp ∧
      Monotone chain3LfpT ∧ RespectsCalls gPath3 chain3LfpT ∧
      Monotone chain3GfpT ∧ RespectsCalls gPath3 chain3GfpT ∧
      Covers convexMerge3 [1, 0] ∧ CalleesFirst gPath3 convexMerge3 [1, 0] ∧
      CondEdge gPath3 convexMerge3 0 1 ∧ 3 * 1 ≤ 3 ∧
      IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT convexMerge3 [1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT convexMerge3 [1, 0] 3)
```

*Unfolded (prose)*

```text
On gPath3 (0 → 1 → 2), convexMerge3 puts 0 and 1 in block 0 and 2 in block 1 (0 and 1 are not mutually reachable).
convexMerge3 is not an SCC decomposition, but [1, 0] covers it and is callees-first, the condensation has the edge 0 → 1,
and with fuel 3 = n * m: bottomUpLfp chain3LfpT convexMerge3 [1, 0] 3 is the least fixpoint of chain3LfpT
(F 2 = {0}, F 1 = σ 2, F 0 = σ 1) and bottomUpGfp chain3GfpT convexMerge3 [1, 0] 3 is the greatest fixpoint of chain3GfpT
(F 2 = ∅, F 1 = σ 2, F 0 = σ 1).
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computation checked by decide plus certified Kleene iterates.
- **Non-vacuity witness** (`convex_merge_not_scc_still_lfp_and_gfp`). The instance itself. Its statement is the card theorem quoted above.

- This card is a positive instance (a non-SCC block map that works). The nearby settings where single-pass solving fails are `merge-nonconvex` (a merge that destroys every callees-first order) and `caller-first` (a valid decomposition in a wrong order).

- **Tier justification.** Kernel-checked instance refuting the stronger reading that bottom-up composition needs a valid SCC decomposition; the positive statement is bottomup-lfp and bottomup-gfp.
- **Prior art.**
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
- **Design question.** An SCC-boundary checker for fixpoint composition need not check minimality (mutual reachability inside blocks); checking a covering callees-first order suffices (bottomup-lfp, bottomup-gfp).

Basis: execution (Lean kernel check). `convex_merge_not_scc_still_lfp_and_gfp` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A checker for single-pass bottom-up solving can accept coarser decompositions than SCCs (for example blocks chosen for parallelism or caching) as long as they admit a covering callees-first order; the instance shows that SCC validity itself is not what single-pass correctness needs.

#### merge-nonconvex — `nonconvex_merge_wrong_in_both_orders`

- **Tier:** T1 (folklore made precise: known informally, not mechanized). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** Merging the endpoints 0 and 2 of the path 0 -> 1 -> 2 (not mutually reachable) into one block, with 1 in its own block, admits no callees-first order; with inner fuel 3 = n*m, single-pass bottom-up then returns a wrong least fixpoint for F(2) = {0}, F(1) = sigma(2), F(0) = sigma(1) and a wrong greatest fixpoint for the dual transfer F(2) = empty, F(1) = sigma(2), F(0) = sigma(1), in both duplicate-free orders [0, 1] and [1, 0], while the SCC decomposition processed in the callees-first order [2, 1, 0] is right.

```lean
-- lean/Toy/Scc/Transfer.lean:445-455
theorem nonconvex_merge_wrong_in_both_orders :
    ¬ Reach gPath3 2 0 ∧ mergeComp3 0 = mergeComp3 2 ∧ ¬ IsSccDecomp gPath3 mergeComp3 ∧
      (∀ order, ¬ CalleesFirst gPath3 mergeComp3 order) ∧
      Monotone chain3LfpT ∧ RespectsCalls gPath3 chain3LfpT ∧
      Monotone chain3GfpT ∧ RespectsCalls gPath3 chain3GfpT ∧
      ¬ IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [0, 1] 3) ∧
      ¬ IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [1, 0] 3) ∧
      ¬ IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [0, 1] 3) ∧
      ¬ IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [1, 0] 3) ∧
      IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT idComp [2, 1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT idComp [2, 1, 0] 3)
```

*Unfolded (prose)*

```text
On gPath3 (0 → 1 → 2), mergeComp3 puts 0 and 2 in block 0 and 1 in block 1. Then 2 does not reach 0, the merge is not an
SCC decomposition, and no list of blocks is callees-first. With fuel 3: for chain3LfpT the single-pass least result is not the
least fixpoint for order [0, 1] nor for [1, 0]; for chain3GfpT the single-pass greatest result is not the greatest fixpoint for
either order; with idComp and order [2, 1, 0] both are right.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computation checked by decide; the absence of a callees-first order is a short arithmetic argument over all lists.
- **Non-vacuity witness** (`nonconvex_merge_wrong_in_both_orders`). The instance itself. Its statement is the card theorem quoted above.

- Positive control (`nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp`): with the same non-convex merge, the order `[0, 1, 0]`, which solves the merged block a second time after the middle block, gives the least and the greatest fixpoint, so the failure is a single-pass phenomenon of the duplicate-free orders, not of the block map alone.

```lean
-- lean/Toy/Scc/Transfer.lean:469-471
theorem nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint chain3LfpT (bottomUpLfp chain3LfpT mergeComp3 [0, 1, 0] 3) ∧
      IsGreatestFixpoint chain3GfpT (bottomUpGfp chain3GfpT mergeComp3 [0, 1, 0] 3)
```

- **Tier justification.** Concrete kernel-checked instance correcting an over-general folk claim ("merging is always sound, just not minimal").
- **Prior art.**
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
  - P. Cousot, "Asynchronous iterative methods for solving a fixed point system of monotone equations in a complete lattice", Research Report R.R. 88, Laboratoire IMAG, Universite scientifique et medicale de Grenoble, September 1977. Asynchronous (chaotic) iteration solves systems of monotone equations; this package instead studies a single pass in a fixed block order, where the order matters.
- **Design question.** Single-pass composition is sound for a merged decomposition only if the merged blocks still admit a covering callees-first order (acyclic condensation); a checker must verify the order, not merely that blocks are unions of SCCs.

Basis: execution (Lean kernel check). `nonconvex_merge_wrong_in_both_orders` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A tool that merges SCCs into larger blocks (for example to batch work) must re-check that the merged blocks admit a covering callees-first order; merging blocks that are not adjacent in the condensation can create a cycle and break single-pass solving.

#### split-scc — `split_scc_wrong_lfp_and_gfp_in_both_orders`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** Splitting the 2-cycle 0 <-> 1 into singleton blocks admits no callees-first order; with two bits per function and inner fuel 4 = n*m, single-pass bottom-up gives a wrong least fixpoint in both duplicate-free orders [0, 1] and [1, 0] for the transfer in which function f seeds bit f and copies the other bit from the other function, and a wrong greatest fixpoint in both duplicate-free orders for the dual transfer in which f forbids bit f and copies the other bit; the one-block SCC decomposition gives the right ones.

```lean
-- lean/Toy/Scc/Transfer.lean:503-513
theorem split_scc_wrong_lfp_and_gfp_in_both_orders :
    ¬ IsSccDecomp gCycle idComp ∧ IsSccDecomp gCycle oneComp ∧
      (∀ order, ¬ CalleesFirst gCycle idComp order) ∧
      Monotone splitLfpT ∧ RespectsCalls gCycle splitLfpT ∧
      Monotone splitGfpT ∧ RespectsCalls gCycle splitGfpT ∧
      ¬ IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [0, 1] 4) ∧
      ¬ IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [1, 0] 4) ∧
      ¬ IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [0, 1] 4) ∧
      ¬ IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [1, 0] 4) ∧
      IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT oneComp [0] 4) ∧
      IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT oneComp [0] 4)
```

*Unfolded (prose)*

```text
On gCycle (0 → 1 → 0), idComp splits the SCC {0, 1}; no list is callees-first. With two bits per function and fuel 4:
splitLfpT (f seeds bit f and copies the other bit from the other function) and splitGfpT (f forbids bit f and copies the other
bit) are monotone and call-local, and the single-pass least (resp. greatest) result is wrong for both [0, 1] and [1, 0];
the one-block decomposition oneComp with order [0] gives the least and greatest fixpoints.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computation checked by decide.
- **Non-vacuity witness** (`split_scc_wrong_lfp_and_gfp_in_both_orders`). The instance itself. Its statement is the card theorem quoted above.

- Positive control (`split_scc_order_0_1_0_recovers_lfp_and_gfp`): with the same split, the order `[0, 1, 0]` gives the least and the greatest fixpoint on these transfers. This is not a general repair: with more bits or longer cycles more repetitions can be needed, and no general statement about repeated entries is proved.

```lean
-- lean/Toy/Scc/Transfer.lean:576-578
theorem split_scc_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint splitLfpT (bottomUpLfp splitLfpT idComp [0, 1, 0] 4) ∧
      IsGreatestFixpoint splitGfpT (bottomUpGfp splitGfpT idComp [0, 1, 0] 4)
```

- **Tier justification.** Concrete kernel-checked instance of a known pitfall (splitting an SCC breaks one-pass solving).
- **Prior art.**
  - R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160, 1972, doi:10.1137/0201010. Linear-time algorithm for the strongly connected components of a directed graph; the SCC partition itself is the background notion formalized here.
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
- **Design question.** SCCs must not be split. A checker that verifies a covering callees-first order rejects every split automatically, because no such order exists (topo-order, scc-char).

Basis: execution (Lean kernel check). `split_scc_wrong_lfp_and_gfp_in_both_orders` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A tool must not split an SCC across blocks when solving in one pass; a checker of covering callees-first orders rejects every split automatically, because no such order exists for a split SCC (`topo-order`, `scc-char`).

#### caller-first — `valid_scc_caller_first_order_wrong_lfp_and_gfp`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Transfer`.
- **Plain claim.** With the valid SCC decomposition of 0 -> 1 (singleton blocks), the monotone callee-local transfers F(1) = {0}, F(0) = sigma(1) and F(1) = empty, F(0) = sigma(1), inner fuel 2 = n*m, and the covering but caller-first order [0, 1], single-pass bottom-up gives a wrong least fixpoint for the first transfer and a wrong greatest fixpoint for the second; the callees-first order [1, 0] gives the right ones.

```lean
-- lean/Toy/Scc/Transfer.lean:589-596
theorem valid_scc_caller_first_order_wrong_lfp_and_gfp :
    IsSccDecomp gPath idComp ∧ Monotone chainLfpT ∧ RespectsCalls gPath chainLfpT ∧
      Monotone chainGfpT ∧ RespectsCalls gPath chainGfpT ∧ 2 * 1 ≤ 2 ∧
      Covers (idComp (n := 2)) [0, 1] ∧ ¬ CalleesFirst gPath idComp [0, 1] ∧
      ¬ IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1] 2) ∧
      ¬ IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1] 2) ∧
      IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [1, 0] 2) ∧
      IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [1, 0] 2)
```

*Unfolded (prose)*

```text
On gPath (0 → 1), idComp is a valid SCC decomposition and [0, 1] covers it but is not callees-first. With fuel 2,
bottomUpLfp chainLfpT idComp [0, 1] 2 is not the least fixpoint of chainLfpT (F 1 = {0}, F 0 = σ 1) and
bottomUpGfp chainGfpT idComp [0, 1] 2 is not the greatest fixpoint of chainGfpT (F 1 = ∅, F 0 = σ 1);
with the callees-first order [1, 0] both are right.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computation checked by decide.
- **Non-vacuity witness** (`valid_scc_caller_first_order_wrong_lfp_and_gfp`). The instance itself. Its statement is the card theorem quoted above.

- Positive control (`caller_first_order_0_1_0_recovers_lfp_and_gfp`): with the same decomposition, the order `[0, 1, 0]` (caller, callee, caller again) gives the least and the greatest fixpoint.

```lean
-- lean/Toy/Scc/Transfer.lean:607-609
theorem caller_first_order_0_1_0_recovers_lfp_and_gfp :
    IsLeastFixpoint chainLfpT (bottomUpLfp chainLfpT idComp [0, 1, 0] 2) ∧
      IsGreatestFixpoint chainGfpT (bottomUpGfp chainGfpT idComp [0, 1, 0] 2)
```

- **Tier justification.** Reference point: a minimal kernel-checked instance of a known pitfall. Its content overlaps the hfirst tightness counterexamples of bottomup-lfp and bottomup-gfp; it is kept as a stand-alone card so that the pitfall can be cited directly.
- **Prior art.**
  - F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704. Iteration strategies based on weak topological orderings of the dependency graph (nested SCC structure with widening points); the condensation-level callees-first order studied here corresponds to the outermost level of such a strategy, without widening and without nested components.
  - M. G. Burke, "An interval-based approach to exhaustive and incremental interprocedural data-flow analysis", ACM Transactions on Programming Languages and Systems 12(3):341-395, 1990, doi:10.1145/78969.78963. Interval-based (structure-directed) interprocedural data-flow analysis, as opposed to iterating over the whole program.
- **Design question.** Reference point for SCC-boundary checkers: the order must be checked as well as (or instead of) the decomposition.

Basis: execution (Lean kernel check). `valid_scc_caller_first_order_wrong_lfp_and_gfp` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A checker must verify the processing order, not just the decomposition: a valid SCC decomposition processed in the wrong order already gives wrong results.

### Termination of mutual recursion

#### lex-iff — `lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks`, `terminates_of_lexDecreasing`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** shallow. **Module:** `Toy.Scc.Termination`.
- **Plain claim.** For a configuration-level call relation C on (function, state) pairs, a block map comp, an inner measure, and a rank on blocks that is injective on the blocks used by comp, the lexicographic measure that maps a configuration (f, x) to (rank of the block of f, inner measure of f at x) strictly decreases along every call exactly when every call within a block strictly decreases the inner measure and every call across blocks goes to a block of strictly smaller rank; and whenever this lexicographic measure decreases along every call, every call chain is finite.

```lean
-- lean/Toy/Scc/Termination.lean:216-220
theorem lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks
    {n k : Nat} {S : Type} {rank : Fin k → Nat} {comp : Fin n → Fin k}
    {inner : Fin n → S → Nat} {C : Calls n S}
    (hinj : ∀ f g, rank (comp f) = rank (comp g) → comp f = comp g) :
    LexDecreasing rank comp inner C ↔ IntraDecrease comp inner C ∧ InterRankDecrease rank comp C

-- lean/Toy/Scc/Termination.lean:234-236
theorem terminates_of_lexDecreasing {n k : Nat} {S : Type} {rank : Fin k → Nat}
    {comp : Fin n → Fin k} {inner : Fin n → S → Nat} {C : Calls n S}
    (h : LexDecreasing rank comp inner C) : Terminates C
```

*Unfolded (prose)*

```text
Let μ(f, x) := (rank (comp f), inner f x), compared lexicographically (LexLt p q := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)).
If rank (comp f) = rank (comp g) → comp f = comp g for all f, g, then
  (∀ a b, C a b → μ b <lex μ a)  ↔  (∀ a b, C a b → comp a.1 = comp b.1 → inner b.1 b.2 < inner a.1 a.2)
                                    ∧ (∀ a b, C a b → comp a.1 ≠ comp b.1 → rank (comp b.1) < rank (comp a.1)).
Termination half (no injectivity): (∀ a b, C a b → μ b <lex μ a) → every configuration is accessible for the converse of C.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hinj : forall f g, rank (comp f) = rank (comp g) -> comp f = comp g (rank injective on used blocks; equivalence only)` | Otherwise a call between two different blocks of equal rank can be paid for by the inner measure, so the left side holds while the cross-block rank condition fails. | tight: counterexample `lexIff_tight_injective` |
| `h : LexDecreasing rank comp inner C (termination half only)` | Without a decreasing measure the call relation can loop. | tight: counterexample `lexTerminates_tight_lexDecreasing` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Termination.lean:264-269
theorem lexIff_tight_injective :
    ¬ (∀ f g : Fin 2, (fun _ : Fin 2 => 0) (idComp f) = (fun _ : Fin 2 => 0) (idComp g) →
        idComp f = idComp g) ∧
      ¬ (LexDecreasing (fun _ : Fin 2 => 0) idComp (fun f (_ : Unit) => 1 - f.val) cPath ↔
        IntraDecrease idComp (fun f (_ : Unit) => 1 - f.val) cPath ∧
          InterRankDecrease (fun _ : Fin 2 => 0) idComp cPath)

-- lean/Toy/Scc/Termination.lean:291-293
theorem lexTerminates_tight_lexDecreasing :
    ¬ LexDecreasing (fun _ : Fin 1 => 0) oneComp (fun _ (_ : Unit) => 0) cLoop ∧
      ¬ Terminates cLoop
```

- **Depth.** shallow. The equivalence is a case analysis on the lexicographic order (close to definitional); the termination half uses well-foundedness of the lexicographic order on Nat x Nat from core Lean.
- **Non-vacuity witness** (`lexIff_nonvacuous`, `lexTerminates_nonvacuous`). The call relation cUnbounded on 0 -> 1, 1 -> 1 (block 1 recurses on a decreasing counter, block 0 calls block 1 with any state) with ranks 1 and 0 and inner measure the state: intra-block calls exist and decrease, and the cross-block calls go to the lower rank.

```lean
-- lean/Toy/Scc/Termination.lean:278-283
theorem lexIff_nonvacuous :
    (∀ f g : Fin 2, 1 - (idComp f).val = 1 - (idComp g).val → idComp f = idComp g) ∧
      LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded ∧
      IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cUnbounded ∧
      cUnbounded (1, 1) (1, 0) ∧ cUnbounded (0, 0) (1, 7)

-- lean/Toy/Scc/Termination.lean:299-300
theorem lexTerminates_nonvacuous :
    LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Termination.lean:253-257
theorem lexDecreasing_pos_iff_of_covers {n k : Nat} {S : Type} {comp : Fin n → Fin k}
    {order : List (Fin k)} {inner : Fin n → S → Nat} {C : Calls n S}
    (hcover : Covers comp order) :
    LexDecreasing (pos order) comp inner C ↔
      IntraDecrease comp inner C ∧ InterRankDecrease (pos order) comp C

-- lean/Toy/Scc/Graph.lean:225-227
theorem pos_injective_on_used_blocks_of_covers {n k : Nat} {comp : Fin n → Fin k}
    {order : List (Fin k)} (h : Covers comp order) :
    ∀ f g, pos order (comp f) = pos order (comp g) → comp f = comp g
```

- **Tier justification.** The lexicographic order on pairs of naturals and its well-foundedness are textbook; restated for a (block rank, inner measure) measure on configurations.
- **Prior art.**
  - L. Bulwahn, A. Krauss, T. Nipkow, "Finding lexicographic orders for termination proofs in Isabelle/HOL", TPHOLs 2007, LNCS 4732, pp. 38-53, doi:10.1007/978-3-540-74591-4_5. Automated search for lexicographic combinations of measures in termination proofs, including mutual recursion; the lexicographic shape studied here is one such combination.
  - A. Krauss, "Partial and nested recursive function definitions in higher-order logic", Journal of Automated Reasoning 44(4):303-336, 2010, doi:10.1007/s10817-009-9157-2. The Isabelle/HOL function package, including termination proofs for mutually recursive definitions via well-founded call relations.
- **Design question.** Termination checking for mutual recursion: exactly which per-call obligations a lexicographic (block rank, inner measure) argument decomposes into, and that such an argument proves termination.

Basis: execution (Lean kernel check). `lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks`, `terminates_of_lexDecreasing` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks`: `propext`; `terminates_of_lexDecreasing`: none.

Basis: derived (modeling bridge). A termination checker for mutual recursion that ranks SCCs (for example by their position in a covering order, `lexDecreasing_pos_iff_of_covers`) and checks an inner measure per SCC proves termination exactly when its per-call obligations (inner decrease within a block, rank decrease across blocks) hold. Real termination provers work with call relations derived from program semantics; the bridge requires that the configuration-level relation `C` over-approximates the real calls.

#### termination-intra — `terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Termination`.
- **Plain claim.** If the condensation of the call graph E under comp is acyclic and every configuration-level call follows an edge of E, then strict decrease of an inner measure on calls within blocks alone implies that every call chain is finite; no rank on blocks has to be supplied or checked.

```lean
-- lean/Toy/Scc/Termination.lean:308-311
theorem terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease
    {n k : Nat} {S : Type} {E : Graph n} {comp : Fin n → Fin k} {inner : Fin n → S → Nat}
    {C : Calls n S} (hacyc : CondensationAcyclic E comp) (hin : CallsInGraph E C)
    (hdec : IntraDecrease comp inner C) : Terminates C
```

*Unfolded (prose)*

```text
If the condensation of E under comp has no cycle, every call C (f, x) (g, y) has E f g = true, and every call with
comp f = comp g has inner g y < inner f x, then every configuration is accessible for the converse of C
(there is no infinite call chain).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hacyc : CondensationAcyclic E comp` | Otherwise calls can cycle between blocks without ever being intra-block. | tight: counterexample `terminationIntra_tight_acyclic` |
| `hin : CallsInGraph E C` | The call graph must over-approximate the actual calls; otherwise acyclicity of E says nothing about C. | tight: counterexample `terminationIntra_tight_callsInGraph` |
| `hdec : IntraDecrease comp inner C` | Recursion within a block must be well-founded. | tight: counterexample `terminationIntra_tight_intraDecrease` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Termination.lean:320-322
theorem terminationIntra_tight_acyclic :
    CallsInGraph gCycle cCycle ∧ IntraDecrease idComp (fun _ (_ : Unit) => 0) cCycle ∧
      ¬ CondensationAcyclic gCycle idComp ∧ ¬ Terminates cCycle

-- lean/Toy/Scc/Termination.lean:327-329
theorem terminationIntra_tight_callsInGraph :
    CondensationAcyclic gEmpty idComp ∧ IntraDecrease idComp (fun _ (_ : Unit) => 0) cCycle ∧
      ¬ CallsInGraph gEmpty cCycle ∧ ¬ Terminates cCycle

-- lean/Toy/Scc/Termination.lean:335-337
theorem terminationIntra_tight_intraDecrease :
    CondensationAcyclic gLoop oneComp ∧ CallsInGraph gLoop cLoop ∧
      ¬ IntraDecrease oneComp (fun _ (_ : Unit) => 0) cLoop ∧ ¬ Terminates cLoop
```

- **Depth.** shallow. Depth is measured relative to the other cards of this package: topo-order supplies a covering callees-first order, whose positions form a block rank under which the lexicographic measure decreases, and lex-iff (terminates_of_lexDecreasing) concludes.
- **Non-vacuity witness** (`terminationIntra_nonvacuous`). The call relation cUnbounded on 0 -> 1, 1 -> 1 with singleton blocks: a condensation edge, a genuinely recursive callee block, and unbounded cross-block fan-out.

```lean
-- lean/Toy/Scc/Termination.lean:343-346
theorem terminationIntra_nonvacuous :
    CondensationAcyclic gPathLoop1 idComp ∧ CondEdge gPathLoop1 idComp 0 1 ∧
      CallsInGraph gPathLoop1 cUnbounded ∧ IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      cUnbounded (1, 1) (1, 0)
```

- **Tier justification.** Known from termination analysis: with dependency graphs, termination can be shown separately per cycle or SCC (Arts and Giesl 2000), mechanized in Isabelle/HOL (IsaFoR/CeTA); restated for configuration-level calls over an arbitrary block map with acyclic condensation.
- **Prior art.**
  - T. Arts, J. Giesl, "Termination of term rewriting using dependency pairs", Theoretical Computer Science 236(1-2):133-178, 2000, doi:10.1016/S0304-3975(99)00207-8. Dependency graphs: termination can be shown separately for each cycle of an estimated dependency graph (later formulated as a processor on its SCCs); the analogue here is per-block decrease over an acyclic condensation.
  - R. Thiemann, C. Sternagel, "Certification of termination proofs using CeTA", TPHOLs 2009, LNCS 5674, pp. 452-468, doi:10.1007/978-3-642-03359-9_31. IsaFoR, an Isabelle/HOL formalization including dependency pairs and dependency graphs, from which the certifier CeTA is generated.
  - P. Manolios, D. Vroon, "Termination analysis with calling context graphs", CAV 2006, LNCS 4144, pp. 401-414, doi:10.1007/11817963_36. Termination analysis of (mutually) recursive functions via calling context graphs and per-context measures.
  - A. Krauss, "Partial and nested recursive function definitions in higher-order logic", Journal of Automated Reasoning 44(4):303-336, 2010, doi:10.1007/s10817-009-9157-2. The Isabelle/HOL function package, including termination proofs for mutually recursive definitions via well-founded call relations.
  - L. Bulwahn, A. Krauss, T. Nipkow, "Finding lexicographic orders for termination proofs in Isabelle/HOL", TPHOLs 2007, LNCS 4732, pp. 38-53, doi:10.1007/978-3-540-74591-4_5. Automated search for lexicographic combinations of measures in termination proofs, including mutual recursion; the lexicographic shape studied here is one such combination.
- **Design question.** A verifier that accepts a decomposition with acyclic condensation (for example a checked SCC decomposition) need only check per-SCC measures; the cross-SCC part is implied.

Basis: execution (Lean kernel check). `terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A verifier that has checked an acyclic condensation (for example via a checked SCC decomposition and order) needs only per-block decreasing measures; the cross-block part of the termination argument is implied. This requires that the call graph over-approximates every configuration-level call (`CallsInGraph`).

#### inner-alone — `inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Termination`.
- **Plain claim.** For the valid SCC decomposition of 0 -> 1, 1 -> 1 and the call relation cUnbounded, in which function 0 at state 0 calls function 1 at every state y and function 1 at state y + 1 calls itself at state y, the inner measure "state" decreases on every intra-block call but not on the cross-block calls (for example (0, 0) calls (1, 5)), and no measure from configurations into Nat decreases along every call at all; yet the call relation terminates and the lexicographic measure (block rank, state) with ranks 1 for block 0 and 0 for block 1 decreases along every call.

```lean
-- lean/Toy/Scc/Termination.lean:358-364
theorem inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout :
    IsSccDecomp gPathLoop1 idComp ∧ CallsInGraph gPathLoop1 cUnbounded ∧
      IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      ¬ (∀ a b, cUnbounded a b → b.2 < a.2) ∧
      (∀ μ : Fin 2 × Nat → Nat, ¬ ∀ a b, cUnbounded a b → μ b < μ a) ∧
      LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded ∧
      Terminates cUnbounded
```

*Unfolded (prose)*

```text
gPathLoop1: 0 → 1, 1 → 1; idComp is an SCC decomposition. cUnbounded: (0, 0) calls (1, y) for every y, and (1, y + 1)
calls (1, y). Every call follows an edge; the only intra-block calls (1, y + 1) → (1, y) decrease the state; but
not every call decreases the state (e.g. (0, 0) → (1, 5)); no μ : Fin 2 × Nat → Nat decreases along every call;
the lexicographic measure with rank 1 - c (block 0 ↦ 1, block 1 ↦ 0) and inner measure the state decreases along every
call; and cUnbounded terminates.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Short direct proofs; the absence of a Nat-valued measure follows because the measure of (1, y) is at least y while it must stay below the measure of (0, 0) for all y.
- **Non-vacuity witness** (`inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout`). The instance itself. Its statement is the card theorem quoted above.

- Positive control (`cJump_has_nat_measure`): for `cJump`, which makes the single cross-block call `(0, 0) → (1, 5)` (bounded fan-out), a measure into `Nat` that decreases along every call exists; it is the unbounded fan-out of `cUnbounded` that rules out every `Nat`-valued measure.

```lean
-- lean/Toy/Scc/Termination.lean:206
theorem cJump_has_nat_measure : ∃ μ : Fin 2 × Nat → Nat, ∀ a b, cJump a b → μ b < μ a
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Termination.lean:190-191
theorem no_nat_measure_cUnbounded :
    ∀ μ : Fin 2 × Nat → Nat, ¬ ∀ a b, cUnbounded a b → μ b < μ a

-- lean/Toy/Scc/Termination.lean:161
theorem terminates_cUnbounded : Terminates cUnbounded
```

- **Tier justification.** Concrete kernel-checked instance of a standard fact: a terminating relation with infinite branching can have well-founded height beyond omega, so no measure into Nat exists, while a lexicographic pair does.
- **Prior art.**
  - L. Bulwahn, A. Krauss, T. Nipkow, "Finding lexicographic orders for termination proofs in Isabelle/HOL", TPHOLs 2007, LNCS 4732, pp. 38-53, doi:10.1007/978-3-540-74591-4_5. Automated search for lexicographic combinations of measures in termination proofs, including mutual recursion; the lexicographic shape studied here is one such combination.
  - A. Krauss, "Partial and nested recursive function definitions in higher-order logic", Journal of Automated Reasoning 44(4):303-336, 2010, doi:10.1007/s10817-009-9157-2. The Isabelle/HOL function package, including termination proofs for mutually recursive definitions via well-founded call relations.
- **Design question.** A termination checker that insists on one measure into Nat cannot accept every terminating mutually recursive program with per-SCC measures: unbounded cross-SCC argument growth can rule out every Nat-valued measure, while the pair (block rank, inner measure) still decreases. Per-SCC checking over an acyclic condensation (termination-intra) or a lexicographic measure (lex-iff) avoids this.

Basis: execution (Lean kernel check). `inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A termination checker that insists on a single measure into `Nat` can reject terminating mutually recursive programs whose cross-SCC calls pass unbounded arguments; per-SCC measures combined lexicographically with the SCC rank (or `termination-intra`) still succeed.

### Checking untrusted summaries

#### prefix-postfix-sound — `le_of_monotone_of_isLeastFixpoint_of_prefixpoint`, `le_of_monotone_of_isGreatestFixpoint_of_postfixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For monotone F on summary vectors, any untrusted vector sigma with F sigma <= sigma (a prefixpoint) lies above the least fixpoint of F, and any sigma with sigma <= F sigma (a postfixpoint) lies below the greatest fixpoint; both checks compare F sigma with sigma function by function and need no decomposition.

```lean
-- lean/Toy/Scc/Fixpoint.lean:300-302
theorem le_of_monotone_of_isLeastFixpoint_of_prefixpoint {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {μ σ : Summ n m} (hμ : IsLeastFixpoint F μ) (hpre : Le (F σ) σ) :
    Le μ σ

-- lean/Toy/Scc/Fixpoint.lean:312-314
theorem le_of_monotone_of_isGreatestFixpoint_of_postfixpoint {n m : Nat} {F : Transfer n m}
    (hmono : Monotone F) {ν σ : Summ n m} (hν : IsGreatestFixpoint F ν) (hpost : Le σ (F σ)) :
    Le σ ν
```

*Unfolded (prose)*

```text
For monotone F, μ the least fixpoint and any σ:  F σ ≤ σ → μ ≤ σ.
For monotone F, ν the greatest fixpoint and any σ:  σ ≤ F σ → σ ≤ ν.
(≤ is bitwise inclusion for every function; checking F σ ≤ σ needs one evaluation of F and a bit comparison.)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | For non-monotone F a prefixpoint can miss part of the least fixpoint (dually for postfixpoints). | tight: counterexample `prefixSound_tight_monotone`, `postfixSound_tight_monotone` |
| `hmu : IsLeastFixpoint F mu (resp. hnu : IsGreatestFixpoint F nu)` | Identifies which fixpoint is bounded; another fixpoint need not be. | tight: counterexample `prefixSound_tight_least`, `postfixSound_tight_greatest` |
| `hpre : F sigma <= sigma (resp. hpost : sigma <= F sigma)` | This is the check; an arbitrary vector need not bound the fixpoint. | tight: counterexample `prefixSound_tight_prefixpoint`, `postfixSound_tight_postfixpoint` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Fixpoint.lean:324-326
theorem prefixSound_tight_monotone :
    ¬ Monotone nmLfpT ∧ IsLeastFixpoint nmLfpT top ∧ Le (nmLfpT only0) only0 ∧
      ¬ Le top only0

-- lean/Toy/Scc/Fixpoint.lean:329-331
theorem postfixSound_tight_monotone :
    ¬ Monotone nmGfpT ∧ IsGreatestFixpoint nmGfpT bot ∧ Le only1 (nmGfpT only1) ∧
      ¬ Le only1 bot

-- lean/Toy/Scc/Fixpoint.lean:335-336
theorem prefixSound_tight_least :
    Monotone idT ∧ ¬ IsLeastFixpoint idT top ∧ Le (idT bot) bot ∧ ¬ Le (top : Summ 1 1) bot

-- lean/Toy/Scc/Fixpoint.lean:347-348
theorem postfixSound_tight_greatest :
    Monotone idT ∧ ¬ IsGreatestFixpoint idT bot ∧ Le top (idT top) ∧ ¬ Le (top : Summ 1 1) bot

-- lean/Toy/Scc/Fixpoint.lean:340-342
theorem prefixSound_tight_prefixpoint :
    Monotone chainLfpT ∧ IsLeastFixpoint chainLfpT top ∧ ¬ Le (chainLfpT bot) bot ∧
      ¬ Le (top : Summ 2 1) bot

-- lean/Toy/Scc/Fixpoint.lean:352-354
theorem postfixSound_tight_postfixpoint :
    Monotone chainGfpT ∧ IsGreatestFixpoint chainGfpT bot ∧ ¬ Le top (chainGfpT top) ∧
      ¬ Le (top : Summ 2 1) bot
```

- **Depth.** shallow. The meet of all prefixpoints is shown to be a fixpoint (and dually the join of all postfixpoints), then compared with the given extremal fixpoint.
- **Non-vacuity witness** (`prefixPostfixSound_nonvacuous`). The monotone transfer seedCopyT on 0 -> 1 with two bits per function: its least fixpoint is not all-false and the prefixpoint is strictly between it and all-true; its greatest fixpoint is not all-true and the postfixpoint is strictly between all-false and it.

```lean
-- lean/Toy/Scc/Fixpoint.lean:360-365
theorem prefixPostfixSound_nonvacuous :
    Monotone seedCopyT ∧ IsLeastFixpoint seedCopyT seedCopyFix ∧
      Le (seedCopyT seedCopyPre) seedCopyPre ∧ seedCopyFix ≠ bot ∧
      seedCopyPre ≠ seedCopyFix ∧ seedCopyPre ≠ top ∧
      IsGreatestFixpoint seedCopyT seedCopyFix ∧ Le seedCopyPost (seedCopyT seedCopyPost) ∧
      seedCopyFix ≠ top ∧ seedCopyPost ≠ seedCopyFix ∧ seedCopyPost ≠ bot
```

- **Tier justification.** Park induction and its dual (Park 1969; Tarski 1955), restated for summary vectors; also available in Lean core and Mathlib for complete lattices.
- **Prior art.**
  - D. M. R. Park, "Fixpoint induction and proofs of program properties", in B. Meltzer and D. Michie (eds.), Machine Intelligence 5, Edinburgh University Press, 1969 (some catalogs list 1970), pp. 59-78. Fixpoint induction: the least fixpoint of a monotone map lies below every prefixpoint (Park induction).
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints.
  - Lean 4, release v4.34.1: src/Init/Internal/Order/Basic.lean, theorem Lean.Order.lfp_le_of_le (f x <= x implies lfp f <= x, documented as the Park induction principle) for complete lattices in Lean core.
  - Mathlib, https://github.com/leanprover-community/mathlib4, commit a205649cf4e6ce1ae4ef6f0a3466f58a30fcdd22, Mathlib/Order/FixedPoints.lean: OrderHom.lfp_le (f a <= a implies lfp f <= a) and OrderHom.le_gfp (a <= f a implies a <= gfp f).
  - AbsInt/CompCert, commit 2685140bf72c959446981fb99b5e44a8975021bc, backend/Kildall.v: a Coq-verified dataflow solver whose result satisfies the dataflow inequations (theorem fixpoint_solution), the inequation form of a summary check.
- **Design question.** Summary checking without recomputation: a prefixpoint check certifies an over-approximation of the least fixpoint and a postfixpoint check an under-approximation of the greatest.

Basis: execution (Lean kernel check). `le_of_monotone_of_isLeastFixpoint_of_prefixpoint`, `le_of_monotone_of_isGreatestFixpoint_of_postfixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorems: `le_of_monotone_of_isLeastFixpoint_of_prefixpoint`: `Classical.choice`, `Quot.sound`, `propext`; `le_of_monotone_of_isGreatestFixpoint_of_postfixpoint`: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A consumer that receives untrusted summary vectors can check them with one evaluation of the transfer: a passing prefixpoint check certifies an over-approximation of the least fixpoint (sound for may-facts), a passing postfixpoint check an under-approximation of the greatest fixpoint (sound for must-facts). Monotonicity of the transfer must be established separately.

#### checks-not-exact — `prefix_and_postfix_checks_pass_but_not_extremal`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For one self-recursive function with the identity equation sigma(0) = sigma(0) over one bit (monotone and callee-local), the all-true and the all-false vector both pass the prefixpoint and the postfixpoint check (both are fixpoints), yet the all-true vector is not the least fixpoint and the all-false vector is not the greatest.

```lean
-- lean/Toy/Scc/Fixpoint.lean:374-377
theorem prefix_and_postfix_checks_pass_but_not_extremal :
    Monotone idT ∧ RespectsCalls gLoop idT ∧
      (Le (idT top) top ∧ Le top (idT top) ∧ ¬ IsLeastFixpoint idT top) ∧
      (Le (idT bot) bot ∧ Le bot (idT bot) ∧ ¬ IsGreatestFixpoint idT bot)
```

*Unfolded (prose)*

```text
On gLoop with idT (σ 0 = σ 0, one bit): idT is monotone and call-local;
top satisfies F top ≤ top and top ≤ F top but is not the least fixpoint;
bot satisfies F bot ≤ bot and bot ≤ F bot but is not the greatest fixpoint.
```

**Hypothesis ledger.** None: this is a concrete counterexample result, so the theorem itself states every condition of the instance.

- **Depth.** shallow. Finite computation checked by decide.
- **Non-vacuity witness** (`prefix_and_postfix_checks_pass_but_not_extremal`). The instance itself. Its statement is the card theorem quoted above.

- Nearby setting where the conclusion fails (no separate Lean theorem): a prefixpoint that additionally carries a ranking certificate *is* the least fixpoint (`ranked-cert`); `rankedCert_tight_ranking` shows that `top` here has no such certificate.

- **Tier justification.** Reference point: a standard example, checked in the kernel. Its content overlaps the hmu/hnu tightness counterexamples of prefix-postfix-sound and the hrank counterexample of ranked-cert; it is kept as a stand-alone card so that the limitation can be cited directly.
- **Prior art.**
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints.
  - D. M. R. Park, "Fixpoint induction and proofs of program properties", in B. Meltzer and D. Michie (eds.), Machine Intelligence 5, Edinburgh University Press, 1969 (some catalogs list 1970), pp. 59-78. Fixpoint induction: the least fixpoint of a monotone map lies below every prefixpoint (Park induction).
- **Design question.** Reference point: one-sided checks cannot replace recomputation or a stronger certificate when exact summaries are required.

Basis: execution (Lean kernel check). `prefix_and_postfix_checks_pass_but_not_extremal` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A consumer that needs exact least or greatest summaries (for example for optimization decisions that depend on the absence of a fact) cannot rely on prefixpoint or postfixpoint checks alone.

#### ranked-cert — `isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For monotone F, if an untrusted summary vector sigma is a prefixpoint (F sigma <= sigma) and comes with a ranking r of its bits such that every set bit (f, i) is produced by F applied to the part of sigma whose bits have rank strictly below r(f, i), then sigma is exactly the least fixpoint of F.

```lean
-- lean/Toy/Scc/Fixpoint.lean:431-433
theorem isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified {n m : Nat}
    {F : Transfer n m} (hmono : Monotone F) {σ : Summ n m} {r : Fin n → Fin m → Nat}
    (hpre : Le (F σ) σ) (hrank : RankedJustified F σ r) : IsLeastFixpoint F σ
```

*Unfolded (prose)*

```text
For monotone F, σ and r : Fin n → Fin m → Nat: if F σ ≤ σ and, for every set bit (f, i) of σ,
F (below σ r (r f i)) f i = true, where below σ r k keeps exactly the bits (g, j) of σ with r g j < k, then
F σ = σ and σ ≤ τ for every fixpoint τ of F.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | Without it, justification from lower-ranked facts does not propagate. | tight: counterexample `rankedCert_tight_monotone` |
| `hpre : F sigma <= sigma` | Without it sigma can miss facts of the least fixpoint. | tight: counterexample `rankedCert_tight_prefixpoint` |
| `hrank : RankedJustified F sigma r` | Without it sigma can contain unjustified (self-supporting) facts; in the counterexample no ranking at all justifies them. | tight: counterexample `rankedCert_tight_ranking` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Fixpoint.lean:450-452
theorem rankedCert_tight_monotone :
    ¬ Monotone negT ∧ Le (negT top) top ∧ RankedJustified negT top (fun _ _ => 0) ∧
      ¬ IsLeastFixpoint negT top

-- lean/Toy/Scc/Fixpoint.lean:455-458
theorem rankedCert_tight_prefixpoint :
    Monotone (topT (n := 1) (m := 1)) ∧ ¬ Le (topT (bot : Summ 1 1)) bot ∧
      RankedJustified (topT (n := 1) (m := 1)) bot (fun _ _ => 0) ∧
      ¬ IsLeastFixpoint (topT (n := 1) (m := 1)) bot

-- lean/Toy/Scc/Fixpoint.lean:463-465
theorem rankedCert_tight_ranking :
    Monotone idT ∧ Le (idT top) top ∧ (∀ r, ¬ RankedJustified idT top r) ∧
      ¬ IsLeastFixpoint idT top
```

- **Depth.** shallow. Strong induction on the rank.
- **Non-vacuity witness** (`rankedCert_nonvacuous`). The chain transfer on 0 -> 1 with sigma all-true, rank 0 for function 1 and rank 1 for function 0.

```lean
-- lean/Toy/Scc/Fixpoint.lean:468-470
theorem rankedCert_nonvacuous :
    Monotone chainLfpT ∧ Le (chainLfpT top) top ∧
      RankedJustified chainLfpT top (fun f _ => if f.val = 1 then 0 else 1)
```

- **Tier justification.** Known: well-founded derivations (stages) certify membership in least fixpoints (Aczel 1977), and certifying model checkers use rank-based certificates for least-fixpoint properties (Namjoshi 2001). Restated as a local certificate for summary vectors.
- **Prior art.**
  - P. Aczel, "An introduction to inductive definitions", in J. Barwise (ed.), Handbook of Mathematical Logic, North-Holland, 1977, pp. 739-782, doi:10.1016/S0049-237X(08)71120-0. Stages of monotone inductive definitions; ranking a fact by the stage at which it first appears is the idea behind kleeneRank.
  - K. S. Namjoshi, "Certifying model checkers", CAV 2001, LNCS 2102, pp. 2-13, doi:10.1007/3-540-44585-4_2. A model checker emits a deductive proof that is checked independently by simple, non-fixpoint methods; proof system for mu-calculus properties, in which least-fixpoint properties are certified with well-founded ranks.
  - L. Tan, R. Cleaveland, "Evidence-based model checking", CAV 2002, LNCS 2404, pp. 455-470, doi:10.1007/3-540-45657-0_37. Checker-independent evidence (proof structures) for fixpoint properties.
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. Monotone maps on complete lattices have least and greatest fixpoints, the least being the meet of all prefixpoints and the greatest the join of all postfixpoints.
- **Design question.** Exact summary checking without running a fixpoint iteration: least-fixpoint summaries can be certified exactly by attaching a rank to each fact (subject to the cost caveat in the non-claims).

Basis: execution (Lean kernel check). `isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). A producer can attach a rank to every derived fact so that a consumer certifies exact least-fixpoint summaries without running a fixpoint iteration. The checking cost is one evaluation of the transfer per distinct rank value of a set bit, plus the prefixpoint check, under this model's evaluation of whole-vector transfers.

#### ranked-cert-complete — `prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.Scc.Fixpoint`.
- **Plain claim.** For monotone F, the least fixpoint mu has a complete ranking certificate: mu is a prefixpoint, it is ranked-justified by kleeneRank F, and every rank is below n*m. Here kleeneRank F f i is the least k < n*m such that bit (f, i) is set after k + 1 Kleene rounds from all-false, and 0 if there is no such k (in particular for bits that are never set, which the certificate does not use).

```lean
-- lean/Toy/Scc/Fixpoint.lean:476-479
theorem prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint
    {n m : Nat} {F : Transfer n m} (hmono : Monotone F) {μ : Summ n m}
    (hμ : IsLeastFixpoint F μ) :
    Le (F μ) μ ∧ RankedJustified F μ (kleeneRank F) ∧ ∀ f i, kleeneRank F f i < n * m
```

*Unfolded (prose)*

```text
For monotone F and its least fixpoint μ:
  F μ ≤ μ,
  for every set bit (f, i) of μ:  F (below μ (kleeneRank F) (kleeneRank F f i)) f i = true,
  for all f, i:  kleeneRank F f i < n * m,
where kleeneRank F f i is the least k < n * m with bit (f, i) set in F^(k+1)(all-false), and 0 if there is none.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone F` | For non-monotone F Kleene iteration can oscillate, so first-appearance ranks justify nothing. | tight: counterexample `rankedComplete_tight_monotone` |
| `hmu : IsLeastFixpoint F mu` | Only the least fixpoint is justified; other fixpoints contain self-supporting facts. | tight: counterexample `rankedComplete_tight_least` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
-- lean/Toy/Scc/Fixpoint.lean:546-549
theorem rankedComplete_tight_monotone :
    ¬ Monotone nmRankT ∧ IsLeastFixpoint nmRankT top ∧
      ¬ (Le (nmRankT top) top ∧ RankedJustified nmRankT top (kleeneRank nmRankT) ∧
        ∀ f i, kleeneRank nmRankT f i < 1 * 2)

-- lean/Toy/Scc/Fixpoint.lean:554-557
theorem rankedComplete_tight_least :
    Monotone idT ∧ idT top = top ∧ ¬ IsLeastFixpoint idT top ∧
      ¬ (Le (idT top) top ∧ RankedJustified idT top (kleeneRank idT) ∧
        ∀ f i, kleeneRank idT f i < 1 * 1)
```

- **Depth.** shallow. Given kleene-bound, mu is the Kleene iterate after n*m rounds, and every bit set after k + 1 rounds is produced by F from the bits set after k rounds, which all have smaller kleeneRank; the rest is bookkeeping about List.find?.
- **Non-vacuity witness** (`rankedComplete_nonvacuous`). The chain transfer on 0 -> 1 with its least fixpoint (all-true), whose two bits get the different ranks 0 and 1.

```lean
-- lean/Toy/Scc/Fixpoint.lean:562-564
theorem rankedComplete_nonvacuous :
    Monotone chainLfpT ∧ IsLeastFixpoint chainLfpT top ∧
      kleeneRank chainLfpT 1 0 = 0 ∧ kleeneRank chainLfpT 0 0 = 1
```

- **Supporting lemmas** (proved; recorded in `supporting_lean`; their statements are not separately hashed):

```lean
-- lean/Toy/Scc/Fixpoint.lean:418-419
theorem kleeneRank_lt_height {n m : Nat} (F : Transfer n m) (f : Fin n) (i : Fin m) :
    kleeneRank F f i < n * m
```

- **Tier justification.** Stage ranking of inductive definitions (Aczel 1977) and completeness of rank-based certificates for least fixpoints (Namjoshi 2001), restated for summary vectors with an explicit bound.
- **Prior art.**
  - P. Aczel, "An introduction to inductive definitions", in J. Barwise (ed.), Handbook of Mathematical Logic, North-Holland, 1977, pp. 739-782, doi:10.1016/S0049-237X(08)71120-0. Stages of monotone inductive definitions; ranking a fact by the stage at which it first appears is the idea behind kleeneRank.
  - K. S. Namjoshi, "Certifying model checkers", CAV 2001, LNCS 2102, pp. 2-13, doi:10.1007/3-540-44585-4_2. A model checker emits a deductive proof that is checked independently by simple, non-fixpoint methods; proof system for mu-calculus properties, in which least-fixpoint properties are certified with well-founded ranks.
- **Design question.** Completeness of the ranking certificate: requiring certificates loses no least-fixpoint summary, and ranks fit in [0, n*m).

Basis: execution (Lean kernel check). `prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Requiring ranking certificates loses no least-fixpoint summary, and ranks fit in `[0, n * m)`; a producer can compute them by recording the first Kleene round at which each bit appears.

### Other declarations named in this report

Every `Toy.Scc` declaration named anywhere in this report is defined or quoted in it. The following helper definitions and proved statements are named in the text above (mostly in the verbatim card fields or in quoted doc comments) and are not quoted elsewhere.

Proved statements:

```lean
-- lean/Toy/Scc/Lattice.lean:118-119
theorem isGreatestFixpoint_of_iter_fixed {n m : Nat} {F : Transfer n m} (hmono : Monotone F)
    {k : Nat} (hfix : F (iter F k top) = iter F k top) : IsGreatestFixpoint F (iter F k top)

-- lean/Toy/Scc/Lattice.lean:113-114
theorem isLeastFixpoint_of_iter_fixed {n m : Nat} {F : Transfer n m} (hmono : Monotone F)
    {k : Nat} (hfix : F (iter F k bot) = iter F k bot) : IsLeastFixpoint F (iter F k bot)

-- lean/Toy/Scc/Termination.lean:144-145
theorem lexDecreasing_cUnbounded :
    LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded

-- lean/Toy/Scc/Transfer.lean:566-571
theorem split_scc_one_bit_some_duplicate_free_order_correct :
    ∀ a b : Fin 3,
      (bottomUpLfp (splitOneBitT a b) idComp [0, 1] 2 = iter (splitOneBitT a b) 2 bot ∨
        bottomUpLfp (splitOneBitT a b) idComp [1, 0] 2 = iter (splitOneBitT a b) 2 bot) ∧
      (bottomUpGfp (splitOneBitT a b) idComp [0, 1] 2 = iter (splitOneBitT a b) 2 top ∨
        bottomUpGfp (splitOneBitT a b) idComp [1, 0] 2 = iter (splitOneBitT a b) 2 top)
```

## Boundaries

### Non-claims

What each result does **not** show (verbatim from the `non_claims` field of each card in `results.json`).

**scc-check**

- Not an efficient algorithm. checkScc evaluates reachB for all n^2 ordered pairs of functions, and each reachB query re-evaluates unmemoized functional closures across fuel = n steps, costing up to about (n+1)^n operations as written; "n^2 queries" counts reachB invocations, not graph-edge inspections. It is a specification-level decision procedure, not Tarjan's algorithm.
- It decides whether a given block map is an SCC decomposition; it does not compute one.
- It checks comp against the given graph E only; it says nothing about whether E over-approximates the calls of a real program.
- Block names need not be contiguous or all used. The checker certifies no processing order (see topo-order).
- For accepting a decomposition for bottom-up fixpoint computation, full SCC validity is stronger than needed (see bottomup-lfp and merge-convex).

**scc-char**

- Mutual reachability in (a) is taken in the whole graph E, not in the subgraph induced by a block, and (a) alone does not make a block strongly connected as an induced subgraph: in the 3-cycle 0 -> 1 -> 2 -> 0, the block {0, 2} (with {1} a separate block) satisfies (a), but its induced subgraph has only the edge 2 -> 0. Such blocks are excluded by (b). No induced-subgraph characterization is stated.
- CondensationAcyclic ignores intra-block edges and self-loops (CondEdge requires c != d); an acyclic condensation allows arbitrary recursion inside each block.
- No algorithm or complexity bound is given for checking either conjunct.
- The forward direction contains the textbook fact that the condensation of the SCC partition is acyclic. The converse shows that acyclicity alone already forces maximality (no SCC is split).
- It does not say that bottom-up fixpoint computation needs an SCC decomposition; it does not (merge-convex).

**topo-order**

- Existence only: the order constructed in the proof (sorted by descendant counts) is not, for example, the order in which Tarjan's algorithm emits components, and nothing is said about efficiency.
- CalleesFirst compares first occurrences (List.idxOf) and requires both blocks of every cross-block call to occur in the list. Blocks that take part in no cross-block call need not occur (Covers requires that separately). Lists with repeated blocks satisfy CalleesFirst when their first occurrences do, but the existence side provides a duplicate-free list.
- The right-to-left direction holds for every callees-first list, covering or not (helper condensationAcyclic_of_calleesFirst).
- Together with scc-char this implies that every valid SCC decomposition has a covering callees-first order; that combination is not stated as a separate theorem.
- For a covering order, the position pos order is injective on the blocks used by comp (pos_injective_on_used_blocks_of_covers), so it can serve as the block rank in lex-iff (lexDecreasing_pos_iff_of_covers).

**kleene-bound**

- Only for the per-function powerset lattices Fin m -> Bool. Nothing is claimed for other finite lattices, for infinite-height domains, or for widening.
- n*m is a worst-case bound; its tightness is shown only at n = 2, m = 1. Nothing is claimed about typical iteration counts.
- An implementation need not always run all n*m iterations: any earlier iterate k with F(F^k(bot)) = F^k(bot) (resp. from top) is already the exact least (resp. greatest) fixpoint (isLeastFixpoint_of_iter_fixed, isGreatestFixpoint_of_iter_fixed).
- The height bound n*m = log_2(|Summ n m|) relies on Summ n m being a Boolean powerset; arbitrary finite lattices of cardinality N can have chains of length N - 1.
- This is the inner-iteration bound used by bottomup-lfp, bottomup-gfp, bottomup-mixed and ranked-cert-complete.

**bottomup-lfp**

- The block map comp need not be an SCC decomposition: any block map with a covering callees-first order works (card merge-convex). Conversely, a valid SCC decomposition processed in an order that is not callees-first fails (card caller-first).
- The claim is about one pass over the list, with one block solve per list entry; a block that occurs twice is solved again, which is harmless under these hypotheses. Nothing is claimed about worklist or chaotic iteration, or about re-processing blocks until stable.
- Transfers are arbitrary monotone maps on the finite powerset lattice Fin n -> (Fin m -> Bool). Although the concrete fixtures in this package are disjunctive transfers with unary-premise rules (disjT, join-preserving) or conjunctive transfers (conjT, meet-preserving), Monotone F also covers non-distributive transfers, such as multi-premise Horn clauses combined disjunctively with other rules (a fact that needs two callee facts simultaneously, or another one). Nothing is claimed for non-monotone transfers or infinite-height domains.
- Under widening on infinite-height domains nothing is claimed; in particular coarsening blocks (merge-convex) is not claimed to preserve results there, since widening operators are in general neither monotone nor associative and their results depend on widening-point placement.
- The model has one summary value per function. It does not model call strings, the IFDS exploded supergraph, or summaries parameterized by calling context. A relational (input-output) summary over a finite domain D can be encoded by letting Fin m index pairs in D x D; the package does not develop this encoding.
- Direction of dependency: RespectsCalls E F requires caller equations to read only callee summaries (bottom-up summary synthesis, where E f g = true means f calls g). Forward caller-to-callee analyses (such as reachable entry states propagated from entry points) depend on callers (the transpose graph E^T) and therefore require callers-first order rather than callees-first.
- Static call-graph assumption: if indirect calls (closures, function pointers, virtual/trait-method calls) are resolved during the fixpoint analysis itself rather than over-approximated ahead of time in E, RespectsCalls E F fails against the incomplete static graph.
- The fuel bound n*m is sufficient, not optimal; a per-block bound (block size times m) would also suffice but is not stated.
- Nothing is claimed about running time or about how the order is produced; RespectsCalls must hold for the same graph E that the order is checked against.

**bottomup-gfp**

- The block map comp need not be an SCC decomposition: any block map with a covering callees-first order works (card merge-convex). Conversely, a valid SCC decomposition processed in an order that is not callees-first fails (card caller-first).
- The claim is about one pass over the list, with one block solve per list entry; a block that occurs twice is solved again, which is harmless under these hypotheses. Nothing is claimed about worklist or chaotic iteration, or about re-processing blocks until stable.
- Transfers are arbitrary monotone maps on the finite powerset lattice Fin n -> (Fin m -> Bool). Although the concrete fixtures in this package are disjunctive transfers with unary-premise rules (disjT, join-preserving) or conjunctive transfers (conjT, meet-preserving), Monotone F also covers non-distributive transfers, such as multi-premise Horn clauses combined disjunctively with other rules (a fact that needs two callee facts simultaneously, or another one). Nothing is claimed for non-monotone transfers or infinite-height domains.
- Under widening on infinite-height domains nothing is claimed; in particular coarsening blocks (merge-convex) is not claimed to preserve results there, since widening operators are in general neither monotone nor associative and their results depend on widening-point placement.
- The model has one summary value per function. It does not model call strings, the IFDS exploded supergraph, or summaries parameterized by calling context. A relational (input-output) summary over a finite domain D can be encoded by letting Fin m index pairs in D x D; the package does not develop this encoding.
- Direction of dependency: RespectsCalls E F requires caller equations to read only callee summaries (bottom-up summary synthesis, where E f g = true means f calls g). Forward caller-to-callee analyses (such as reachable entry states propagated from entry points) depend on callers (the transpose graph E^T) and therefore require callers-first order rather than callees-first.
- Static call-graph assumption: if indirect calls (closures, function pointers, virtual/trait-method calls) are resolved during the fixpoint analysis itself rather than over-approximated ahead of time in E, RespectsCalls E F fails against the incomplete static graph.
- The fuel bound n*m is sufficient, not optimal; a per-block bound (block size times m) would also suffice but is not stated.
- Nothing is claimed about running time or about how the order is produced; RespectsCalls must hold for the same graph E that the order is checked against.
- Greatest fixpoints here are lattice objects; whether they are the intended safety invariants of a real program is a modeling question not addressed.

**bottomup-one-sided**

- It does not say that the result is close to the fixpoint; with a bad order or decomposition it can be strictly below the least fixpoint (merge-nonconvex, split-scc, caller-first).
- Without Covers, CalleesFirst, and n*m <= fuel, the returned vector need not be a fixpoint or prefixpoint of F; for a may-analysis whose soundness requires F(sigma) <= sigma, an under-approximating result below lfp(F) is unsound.
- One-sidedness relies on starting from bot (for bottomUpLfp) or top (for bottomUpGfp) and resetting each visited block in blockInit; warm-starting bottomUp from a cached arbitrary vector init != bot (resp. init != top) can exceed a prefixpoint (resp. fall below a postfixpoint) when order is non-covering or non-callees-first (for example, with the empty order bottomUp returns init unchanged).
- RespectsCalls is not assumed and not needed.
- Nothing is claimed about mixed sign assignments.

**bottomup-mixed**

- It does not say that a mixture equals the least or the greatest fixpoint; in general it is neither (mixed-neither).
- The hierarchical solution depends on comp and sign: merging blocks that carry different signs changes the object computed.
- HierSolution defines coordinatewise block-extremality (freezing other blocks to the candidate vector sigma as constants). It coincides with standard nested-substitution Boolean/Fixpoint Equation System semantics (and has a unique solution) only because CalleesFirst + RespectsCalls rules out inter-block cycles; on cyclic cross-sign dependencies (such as nu X_0 = X_1, mu X_1 = X_0), HierSolution admits multiple solutions whereas nested mu/nu semantics has a unique solution. Kernel-checked instance: for F(0) = sigma(1), F(1) = sigma(0) on the 2-cycle with block 0 greatest and block 1 least, both all-false and all-true are hierarchical solutions (hierSolution_swapT_gCycle_mixSign_not_unique); the nested system with X_0 outermost has the single solution all-true.
- Uniqueness is among hierarchical solutions for the given comp and sign, not among all fixpoints of F.
- Nothing is claimed for alternating fixpoints (cyclic dependencies between blocks of different signs, as in the modal mu-calculus or parity games).

**mixed-neither**

- Instances only: it does not say that every mixture differs from both extremal fixpoints for every transfer.
- It says nothing about mixtures in which a block depends on a block processed later (cyclic dependencies between blocks of different signs).

**merge-convex**

- It shows only that SCC validity is not necessary for correctness. It does not say that coarser blocks are free: inner iterations range over more functions.
- It applies to merges that keep a covering callees-first order. Merges that create a condensation cycle break single-pass bottom-up (merge-nonconvex).
- Nothing is claimed for analyses with widening, where merging blocks can change the result.

**merge-nonconvex**

- Only duplicate-free orders are refuted. Re-solving the merged block after the middle block (the list [0, 1, 0]) gives both the least and the greatest fixpoint on this instance (nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp).
- Existential: it does not claim that every non-convex merge fails for every transfer.
- The wrong least result is still below the least fixpoint (bottomup-one-sided): the failure loses facts and never invents them.

**split-scc**

- Only duplicate-free orders [0, 1] and [1, 0] are refuted; passing the non-duplicate-free list [0, 1, 0] to bottomUpLfp / bottomUpGfp on this instance reaches the exact global least and greatest fixpoints (split_scc_order_0_1_0_recovers_lfp_and_gfp).
- Two bits are used on purpose. With one bit per function on the split 2-cycle, each of the nine transfers F(0) in {empty, full, sigma(1)}, F(1) in {empty, full, sigma(0)} is computed correctly (least and greatest fixpoint) by at least one of the two duplicate-free orders (split_scc_one_bit_some_duplicate_free_order_correct, stated as equality with the Kleene iterate at the height, which is the extremal fixpoint by kleene-bound). That these nine are all the monotone callee-local one-bit transfers on the 2-cycle is a short argument (a monotone map Bool -> Bool is constant or the identity), not a theorem of the package.
- Single pass only; re-processing blocks until stable is not addressed.

**caller-first**

- A valid SCC decomposition does not make the processing order irrelevant; the order must be checked separately.
- Escape hatches: re-solving the caller after the callee (the list [0, 1, 0]) gives both extremal fixpoints on this instance (caller_first_order_0_1_0_recovers_lfp_and_gfp), and iterating blocks until stable is not addressed. Transfers that read no callee summaries (for example constant transfers) are computed correctly in every order.
- When a caller-first order fails for a monotone F, the least result is still below every prefixpoint and the greatest result above every postfixpoint (bottomup-one-sided).

**lex-iff**

- No SCC property of comp is assumed or used.
- Only the left-to-right direction of the equivalence needs injectivity on used blocks; injectivity on unused block names is not required.
- It says nothing about how to find the rank or the inner measure. The static call graph does not appear; termination-intra shows that with an acyclic condensation no rank needs to be supplied.
- The position of a block in a covering order qualifies as a rank (lexDecreasing_pos_iff_of_covers), so an order from topo-order can be used directly.
- Calls n S uses a single Type 0 state space S shared across all Fin n functions and requires termination from every configuration (f, x) : Fin n x S; mutually recursive functions with distinct parameter types must sum-inject them into S, and precondition-dependent termination must restrict the call relation C to states satisfying each function's precondition.
- Measures are pairs of naturals ordered lexicographically; other well-founded orders are not considered.

**termination-intra**

- Termination of the modeled call relation (finite call chains), not termination of loops or other non-call steps of a program.
- It requires the static call graph to cover all calls (CallsInGraph); unresolved indirect calls break it.
- comp need not be an SCC decomposition; an acyclic condensation suffices, and every SCC decomposition has one (scc-char).
- No bound on the length of call chains is given.
- Calls n S uses a single Type 0 state space S shared across all Fin n functions and requires termination from every configuration (f, x) : Fin n x S; mutually recursive functions with distinct parameter types must sum-inject them into S, and precondition-dependent termination must restrict the call relation C to states satisfying each function's precondition.

**inner-alone**

- It does not contradict termination-intra: the call relation terminates.
- The absence of a measure into Nat depends on unbounded fan-out across blocks. With bounded branching a measure into Nat can exist even though the unmodified inner measure increases across blocks (cJump_has_nat_measure: a single call from (0, 0) to (1, 5)). A terminating call relation in which every configuration makes only finitely many calls always has a measure into Nat (Konig's lemma); that fact is not formalized here.
- The lexicographic pair avoids bounding how much the state can grow across blocks; it is one sufficient choice, not the only possible global measure (ordinal-valued measures also work).
- Calls n S uses a single Type 0 state space S shared across all Fin n functions and requires termination from every configuration (f, x) : Fin n x S; mutually recursive functions with distinct parameter types must sum-inject them into S, and precondition-dependent termination must restrict the call relation C to states satisfying each function's precondition.

**prefix-postfix-sound**

- Neither check implies equality with the extremal fixpoint, and passing both checks does not either (checks-not-exact).
- Being above the least fixpoint is soundness only for analyses that read summaries as may-facts; the card states a lattice fact only.
- Dually, passing the postfixpoint check sigma <= F(sigma) guarantees only sigma <= gfp(F) (an under-approximation of the greatest fixpoint), which is conservative only when summaries represent positive safety/must invariants and is unsound if consumed negatively or as a may-summary.
- Both checks validate sigma solely against the mathematical operator F; they do not verify that F soundly abstracts concrete program execution or indirect calls.
- Here the least fixpoint is defined as least among all fixpoints (IsLeastFixpoint), not as the meet of all prefixpoints; the proof shows that for monotone F on this finite lattice the meet of all prefixpoints is a fixpoint, so the two agree.

**checks-not-exact**

- It does not say that exact certification is impossible: a ranking certificate pins down the least fixpoint (ranked-cert).

**ranked-cert**

- Only least fixpoints. No certificate for greatest fixpoints is formalized; a dual certificate on unset bits is plausible but not stated.
- Over an opaque whole-vector operator F : Summ n m -> Summ n m, checking RankedJustified invokes F once per set bit of sigma (up to n*m calls, plus one call for F(sigma) <= sigma) - the same worst-case number of whole-vector F evaluations as recomputing lfp(F) from bot via kleene-bound. Certificate checking is asymptotically cheaper than recomputation only when single-coordinate queries F tau f i can be evaluated sparsely/locally. (Evaluations can be shared between bits of equal rank, since below sigma r k depends only on k; no cost model is formalized.)
- Neither RespectsCalls nor any decomposition is assumed.

**ranked-cert-complete**

- kleeneRank is computed by Kleene iteration: producing the certificate costs a fixpoint computation; only checking it avoids one.
- Nothing is claimed about greatest fixpoints.
- Ranks are below n*m; no smaller bound is claimed.

### Escape hatches

The counterexample results are impossibility-style statements about specific instances; these are the hypotheses whose change defeats them, each established in Lean by the named theorem:

- **`caller-first`, `merge-nonconvex`, `split-scc`** (single-pass bottom-up gives wrong extremal fixpoints): repeating blocks in the order, as in `[0, 1, 0]`, recovers the right answers on these instances (`caller_first_order_0_1_0_recovers_lfp_and_gfp`, `nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp`, `split_scc_order_0_1_0_recovers_lfp_and_gfp`). Duplicate entries are allowed by `bottomUp` and by `CalleesFirst`, whose positions are first occurrences; no general theorem about how many repetitions suffice is proved. For `split-scc`, the instance uses two bits per function because one bit is not enough for a failure in both duplicate-free orders: for each of the nine one-bit transfers `splitOneBitT a b` on the split 2-cycle (each equation is constant empty, constant full, or a copy of the other function's bit), at least one of the orders `[0, 1]`, `[1, 0]` returns the Kleene iterate at the height from all-false, and at least one (possibly the other) returns the Kleene iterate at the height from all-true (`split_scc_one_bit_some_duplicate_free_order_correct`); these iterates are the least and greatest fixpoints by `kleene-bound`. That these nine transfers are all the monotone call-local one-bit transfers on the 2-cycle is a remark, not a Lean theorem.
- **`inner-alone`** (no `Nat`-valued measure exists): bounded cross-block fan-out (`cJump_has_nat_measure`) or a lexicographic measure (`lexDecreasing_cUnbounded`, `terminates_of_lexDecreasing`) defeats the impossibility.
- **`mixed-neither`** (a mixture is neither extremal fixpoint): uniform signs (`bottomup-lfp`, `bottomup-gfp`) defeat it.
- **`checks-not-exact`** (one-sided checks do not certify extremality): a ranking certificate (`ranked-cert`) defeats it for least fixpoints. No certificate for exact greatest fixpoints is formalized.
- **`bottomup-one-sided`** is a soundness-direction statement, not an impossibility; its conclusion holds for every block map and order and fails without monotonicity or without the prefixpoint (postfixpoint) premise.

### Tightness status

Of the 40 hypotheses listed on the cards, 38 are `tight`, with 45 kernel-checked counterexample theorems in total (some hypotheses of two-part cards have one counterexample per part); 2 are `harmless` and 0 are `unknown`. The harmless ones are the two conditions inside the existential of `topo-order` (`order.Nodup` and `Covers comp order`): they strengthen the right-hand side of an equivalence whose left-to-right direction constructs an order satisfying them and whose right-to-left direction does not use them (`condensationAcyclic_of_calleesFirst` derives acyclicity from `CalleesFirst` alone), so dropping either leaves a true equivalence. The module `Toy.Scc.Checks` re-derives, for every tightness counterexample, the negation of exactly the dropped hypothesis from the counterexample and the main theorem, and instantiates every main theorem at its non-vacuity witness.

### Disproved, dropped, and not examined

- **Not examined:** infinite-height or non-powerset lattices, widening and narrowing; context-sensitive or relational summaries; worklist, chaotic or incremental solvers and iteration to stability; complexity of `checkScc`, of `bottomUp` or of certificate checking beyond the evaluation counts stated in non-claims; correctness of any SCC algorithm (Tarjan, Kosaraju, Gabow) or of call-graph construction; nested SCC structure (weak topological orders) inside blocks; alternating fixpoints (cyclic dependencies between least and greatest blocks) beyond the non-uniqueness example `hierSolution_swapT_gCycle_mixSign_not_unique`; exact certificates for greatest fixpoints; termination measures into ordinals other than `Nat` and lexicographic pairs of naturals; nested recursion.
- **Known not to apply:** single-pass bottom-up with a covering but caller-first order (`caller-first`), with split SCCs (`split-scc`), and with merges that admit no callees-first order (`merge-nonconvex`); uniqueness of `HierSolution` under cyclic cross-sign dependencies (`hierSolution_swapT_gCycle_mixSign_not_unique`).
- **Unknown:** none of the stated hypotheses has `unknown` tightness.
- **Disproved or dropped statements:** none.

## Evidence

Basis: execution (Lean kernel check), observed 2026-11-20.

**Toolchain.** `leanprover/lean4` release `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The tag was resolved on 2026-11-20 with the GitHub API (`GET /repos/leanprover/lean4/git/ref/tags/v4.34.1` returns an object of type `commit` with this SHA), and the installed toolchain reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

**Build and audit.** `lake build` of a fresh copy of `lean/` succeeds with no errors and no `sorry` warnings; the build-time module `Toy.Scc.Audit` prints `AUDIT OK: 525 declarations checked; exactly 0 depend on sorryAx, all of them allowed main results; no non-standard axioms.` (it also counts compiler-generated auxiliary declarations). The Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `#exit` or `Lean.ofReduce*`. An axiom audit over all 433 non-internal declarations defined in the `Toy` modules (via `Lean.collectAxioms`) finds only `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`. Every Lean name referenced in `results.json` exists.

**Statement hashes.** For every Lean name referenced in `results.json` in the fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and the `counterexample` of each hypothesis (93 names), `audit/statements.json` records `statement_sha256` = SHA-256 of `toString (repr ci.type)` (the `Lean.Expr` of the statement), and `closure_sha256` = SHA-256 of the newline-joined, sorted list of entries `name : repr type [:= repr value]` for all constants of the `Toy` modules reachable from the statement's type through types, through values of non-theorems, and through constructors of inductive types (theorem proofs are excluded); `closure_size` is the number of entries. Names listed only in `supporting_lean` are not hashed. The programs under **Revalidation** recompute both hashes.

Main results:

| Card | Theorem | Axioms | `statement_sha256` | `closure_sha256` (closure size) |
| --- | --- | --- | --- | --- |
| scc-check | `checkScc_eq_true_iff_isSccDecomp` | `Classical.choice`, `Quot.sound`, `propext` | `dac3f7640dd1ed26cae43772c33d2da463cc42c14dfd5afe2fdad33e713df5e9` | `20f02b494f80806f0b44f4fa0459a30833469d77e311ee3db7a1725173ac4124` (11) |
| scc-check | `reachFrom_eq_true_iff_reach_of_pred_le` | `Classical.choice`, `Quot.sound`, `propext` | `84bff2d55fda16413afe9e7851d9c70a74e71ecb6341b34be39c82967ea93eaa` | `5e8e271bc1378ba0d76eec11106af5c5f21d854d1104c899c926b5df6bf66d68` (8) |
| scc-char | `isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic` | `Classical.choice`, `Quot.sound`, `propext` | `2abed94d7405bc88047e5e7e66a4f7d4a45424c3832e44240d02b9638efed025` | `9c22a09145b8dba923c81f9652bd564b738a80ea67e124e8fee9aec723c4fc8c` (8) |
| topo-order | `condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order` | `Classical.choice`, `Quot.sound`, `propext` | `4c474036e9afbfff86ad1506ef9305f3ae5af63c5f104cfcb829ad6a095ebb47` | `ce75beb2d6aeb927e7b8a2543abe024bd49b71ffef6ec792f9ac66aa19939efb` (6) |
| kleene-bound | `iter_bot_isLeastFixpoint_of_monotone_of_height_le` | `Classical.choice`, `Quot.sound`, `propext` | `8e37324ca6b2bcd57171b54c91a1fc98fbea7c6016ef01f8efd8b19d09362705` | `2eb1ddd554b0a0c6142b527d5c3d09d92dede72af0b275f929c0d0a47805e327` (10) |
| kleene-bound | `iter_top_isGreatestFixpoint_of_monotone_of_height_le` | `Classical.choice`, `Quot.sound`, `propext` | `7e3252e7b7fe178d45b403bff90358d177b3ec219a912fb499456dba13c79627` | `63160a965bc520bdedc322928c3088e4788f3a18e20f3ca49bd17ffa82cd36b4` (10) |
| bottomup-lfp | `bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le` | `Classical.choice`, `Quot.sound`, `propext` | `08f844b80023af417ee6ecf1bed7b34c2f013a6773bec764559f6c8e16825569` | `ca20098755991bf8d68cfcefc42e588da02fc4425d39d257685c8ef7caa8974f` (20) |
| bottomup-gfp | `bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le` | `Classical.choice`, `Quot.sound`, `propext` | `9db86956c703b2e4992a396f14ce6fedd90d00dfaa259bdd49f79902097dd54a` | `9e220fe0f232eb6738eb5d3b75cfbe87ace6d8ca1635ce93b6a5b7942e684ba7` (20) |
| bottomup-one-sided | `bottomUpLfp_le_of_monotone_of_prefixpoint` | `propext` | `843625ac4b7d0468ef95ed64cfc2c5d52e5d9a0ff6cc694cceec2d1b550cf3d5` | `ec0f9be8dad6db44fa183d9c6e6e42059ec684214621562da2b3fa98445aab0a` (14) |
| bottomup-one-sided | `le_bottomUpGfp_of_monotone_of_postfixpoint` | `propext` | `aa307b3303c8723a3294cd2541260c6fa983e1adfc656b55ce3744947728c749` | `325e10136348f1bad3cb2d70bce39e03537ea1da9dc98ecbd948c753b019a116` (14) |
| bottomup-mixed | `bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le` | `Classical.choice`, `Quot.sound`, `propext` | `0382c9000153dd6af8392329285c8bedea1461dbef0054cc1c3b3feace5eae32` | `c7fce17c2942f21b31f1b3c12fb1194c1fb266c32318bd97b8d4918537df1258` (19) |
| bottomup-mixed | `le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint` | `Quot.sound`, `propext` | `56030653b0f51289a0c302657a3a0c801c6fe655ea7af11d941e528f114d64b1` | `f0bdf4ef47ac5bd1a37279012284fcb30a4bfe11ca1306bca543a61c3e52efb9` (9) |
| bottomup-mixed | `HierSolution.fixpoint` | `Quot.sound`, `propext` | `dd5e94d42565a2c28b80612df532ff82e329af9684cc0ba3e2b5c6ab99d21779` | `26af1c0b50e38d0fc40faa87e355b9f842e25bfb1a90b90c53e4c51f443e1c6c` (7) |
| mixed-neither | `mixed_lfp_callee_gfp_caller_neither_lfp_nor_gfp` | `Quot.sound`, `propext` | `e1c372ddd53edcf379825626d82fc8199dd5136d307b006547caa9f4aa0b8ab8` | `cc0093ba09a5cb8cd267ac74ae2e35c142c313f340e4c8b715717029899cdc36` (33) |
| mixed-neither | `mixed_gfp_callee_lfp_caller_neither_lfp_nor_gfp` | `Quot.sound`, `propext` | `21e68d12190040f86a5fe3c813e715f884cdbc229c2a3c2e13af240259f1c4d3` | `ffd9612eff40bce5fbf971ff75d6a2470517adae0a8266ee876c7d7f0b1da145` (33) |
| merge-convex | `convex_merge_not_scc_still_lfp_and_gfp` | `Quot.sound`, `propext` | `68654aad2720ac8dbf75e06c50f8fb8a6d245c739925675db0996d603fa4140e` | `d7a68bb60815971651622510f4a0ac2d081fdb2ca159a6a5ae90472a522bdec1` (36) |
| merge-nonconvex | `nonconvex_merge_wrong_in_both_orders` | `Quot.sound`, `propext` | `8c0880a88998934a98b1f56d7e93b85f5d61f15b7eb842531da99b2e66e4cb19` | `ade8c1aa006e35647a33a56625006518bd71caf2ecacc60d89eed0d4dc367ace` (34) |
| split-scc | `split_scc_wrong_lfp_and_gfp_in_both_orders` | `Quot.sound`, `propext` | `fc9a8e972f2659db85597e015fd90c5f203dfb3eb76fa2c90140e2d9c43203ed` | `848e4b017140ef442b80b2916b2c90b5440fcc2c664ee4efdea174151cc2b8ba` (34) |
| caller-first | `valid_scc_caller_first_order_wrong_lfp_and_gfp` | `Quot.sound`, `propext` | `33cc6235e43b401c34d34068a91ef7c28f306a06f90d520537576ee82f251eba` | `f10b8b1bbb0cacaa719c49b24d43e872afe3449d90171a1d1004a827fcba167e` (33) |
| lex-iff | `lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks` | `propext` | `80d474735a38028b96e4a0fa64a7150d6cf9f3f31fbd7620639f4dbe767a6fb4` | `8176857b999b202ba331f2ae4c2cd32a4a938a812dac8da2619c9277ddf5bcf3` (6) |
| lex-iff | `terminates_of_lexDecreasing` | none | `797266e048486ea681d40e86482be742537fa5627f0e751706f606519f8b4c7d` | `dd93e2f28ff4f244c47b9c29476d421995a0d79d5b1eb6d6fdbf2d569b4fe869` (5) |
| termination-intra | `terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease` | `Classical.choice`, `Quot.sound`, `propext` | `72f1f8dc295f308c78f54d2714735d0fcde9aad781492f3f684a9bc450db6b1f` | `435c79321aa0cdb3a0b0804bdd03f4cb4054941f194c674b085d2a0bd2270008` (7) |
| inner-alone | `inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout` | `Quot.sound`, `propext` | `7526ea49f638d50f67d9630c89384a15d28338a805f1e797dc3523c75d1ee12b` | `ccb2373216c347a53b47dab7cfbfaf09a63f9e15aff19be072e253a8a2214bab` (16) |
| prefix-postfix-sound | `le_of_monotone_of_isLeastFixpoint_of_prefixpoint` | `Classical.choice`, `Quot.sound`, `propext` | `0a00465fc3a068deed1c9ffc123f9018aa11391f2976050cffe45915ba8ad152` | `1cf25b870cf7eeeb762a1d624f9c73b94ca86b152775ccdfdb07f2d062dedd37` (6) |
| prefix-postfix-sound | `le_of_monotone_of_isGreatestFixpoint_of_postfixpoint` | `Classical.choice`, `Quot.sound`, `propext` | `7be0dbedf97c1dcc92cd8cee80b79bc0c6fd1ad92ff6cd87fb31066c7af9efaa` | `a0abc8f2d2ce5b585aef4dcd7d9817694029789a5fe17192b010daf0f43d53cf` (6) |
| checks-not-exact | `prefix_and_postfix_checks_pass_but_not_extremal` | `Quot.sound`, `propext` | `55c87fcdab1917bac1ab3b122fa735313dfc322a475d90f710254c573bc759dc` | `d6bfa8471a9d05d780aecc1d9fbf41892e232d29d9f0018b194bebe19d6bf92c` (14) |
| ranked-cert | `isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified` | `Quot.sound`, `propext` | `fb1d353a906178531be0fa8b5c096246d380c56f1fd7bd7719393c2af2e50e98` | `353196571c9b154f145ac6c9266e2070b6a59d7a68a5a8c4eae81ac3ad9ee9b7` (8) |
| ranked-cert-complete | `prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint` | `Classical.choice`, `Quot.sound`, `propext` | `0e7082f40e2d7a44a8756144ac2c7fa36282bf51698806cbb45fbb02f720073a` | `9102d60f0efbae5554fabe5192fa96749b30309afd4cdf417819afcb1bc4669a` (13) |

Counterexamples, non-vacuity witnesses and positive controls (names that are also main results are listed above):

| Declaration | Role | Axioms | `statement_sha256` | `closure_sha256` (closure size) |
| --- | --- | --- | --- | --- |
| `bottomUpGfp_nonvacuous` | bottomup-gfp non-vacuity | `Quot.sound`, `propext` | `ed92c60c499a6d76432515a21466f669571b308cb266533e6bac6194ba40a3ba` | `22ab04219eb0502fcf5a624691ea8e399c217821b7886b9665f48f234e9f44e6` (19) |
| `bottomUpGfp_tight_calleesFirst` | bottomup-gfp tight `hfirst` | `Quot.sound`, `propext` | `31ce8082bcd3c2d0ce272f568b4f8e5d9e959a4d97f07ff80bbee635c6de3ece` | `18bd83d7094224192cebe71c38f05f85ca6ea372e619fe0f272e3aad938fd94d` (24) |
| `bottomUpGfp_tight_covers` | bottomup-gfp tight `hcover` | `Quot.sound`, `propext` | `192d12242f6a8dfd458ed09dc21d4e0cb504cbd8e41ccc32c49ab0c59cd68389` | `d5c0433ad99838b924c0e508b40395224fea3f35669bf208af44e53cde5b7ced` (25) |
| `bottomUpGfp_tight_fuel` | bottomup-gfp tight `hfuel` | `Quot.sound`, `propext` | `3815b367a2eedd21ee46286d93d2ac9bf18c70c7259dcbada8ecf2d15e4cf768` | `a7d2714da68654fd79ab688898186e3ede372622d0d1f92b43686f77704bcfdb` (29) |
| `bottomUpGfp_tight_monotone` | bottomup-gfp tight `hmono` | `Quot.sound`, `propext` | `0296195790f7dc2a7ce0f5206f19aa29a0d4152e0b9ed4e95878b90c9a8ddbeb` | `411a95265faf8dd91d4db2ed7e4885069ba806cbfea401f6797ee6890007a6d8` (24) |
| `bottomUpGfp_tight_respectsCalls` | bottomup-gfp tight `hresp` | `Quot.sound`, `propext` | `d7721c27447a72427fca2dfe748aae3ef69bebdf8db9948f066bd00dfadfd43e` | `61abb65e897b21c248ade3a24c4ee15264e109fe532e868ab1a1a4567d017b71` (24) |
| `bottomUpHier_nonvacuous` | bottomup-mixed non-vacuity | `Quot.sound`, `propext` | `df952c80936a9fd209c244fb83ab64c58a6a1a8fae042314a8c5d40e0aa17577` | `f348dbba7de36f2ea2221353e097adaae30572a41c70b46f620cf932b4afb556` (15) |
| `bottomUpHier_tight_calleesFirst` | bottomup-mixed tight `hfirst` | `Quot.sound`, `propext` | `b3b63a7de7372f611f0c2226734575dc93550d1954fbcf49865c5d453a68382b` | `d3cead5a258f59ef563537d17d2acc42574ba5847a334444cdc35ea839585dd1` (25) |
| `bottomUpHier_tight_covers` | bottomup-mixed tight `hcover` | `Quot.sound`, `propext` | `4e2ae483d8438e0f50739db97f11c0ae7eeedc9ec354a5ad9064faeef46dc566` | `7e1f269d6c4ed1e4823b8494a6823e2c629e94270fb452f12558104b56b57fcd` (25) |
| `bottomUpHier_tight_fuel` | bottomup-mixed tight `hfuel` | `Quot.sound`, `propext` | `a635792afa62e8730042ee7a8e47a515f7b38d0747f8fe20fd55cbd2ac28b79e` | `23f90ea5e207efdd2cd0b237e0c98f6c4be2fdb62dffedb2ed95d1ab66b75204` (29) |
| `bottomUpHier_tight_monotone` | bottomup-mixed tight `hmono` | `Quot.sound`, `propext` | `d12295d940d826cacf702479ba234868d0d29e2cb31120e70f2cc1b0b2895af9` | `d3c0919bcb7c976449cbf099b8c1cd097dca52a10a0d6686d024e94932c0a367` (24) |
| `bottomUpHier_tight_respectsCalls` | bottomup-mixed tight `hresp` | `Quot.sound`, `propext` | `12fc60f09c5a8619b2307188fb19da5c9bb1441354ae390e0e31598642e4f24a` | `4a9b1bfbcb3c09ddc52773646129b41bf8a34769e72f53d50a143c99b2ea4509` (24) |
| `bottomUpLfp_nonvacuous` | bottomup-lfp non-vacuity | `Quot.sound`, `propext` | `6b35a256b86b68a63ce511bb8158b55fb45ab278c50ff4e3e142a9bc449873ae` | `11bf56c82ef5f0b77a550663c20b7a4be25986b63a285740adb40744e15a6c0d` (19) |
| `bottomUpLfp_tight_calleesFirst` | bottomup-lfp tight `hfirst` | `Quot.sound`, `propext` | `792dada47a97a37ce3e41bb6a6148b0efc0eb8a51f9031f9cd8b1b5216480ab8` | `c9942b5d5e9d6f5b63aefe694323808cd9e16b18e6191da2e9fcadb4eac0d479` (24) |
| `bottomUpLfp_tight_covers` | bottomup-lfp tight `hcover` | `Quot.sound`, `propext` | `bfdcf719a92a54e3a3ad15d40cf3d03e7ffe4749527a277643f04a1958e945c9` | `8aeeac3ad456364bb4a95342c727f5776953c577a757f7f3038703b2fafd5491` (25) |
| `bottomUpLfp_tight_fuel` | bottomup-lfp tight `hfuel` | `Quot.sound`, `propext` | `9ed1555dd345b71bcd83d2be0d58b7fad67a815db551de70076bfad42b7f060b` | `131f7e52204469b701e1284112b10c8ddfa9e81ede3a9ca9f9153193c7e63724` (29) |
| `bottomUpLfp_tight_monotone` | bottomup-lfp tight `hmono` | `Quot.sound`, `propext` | `3353230dae8b7fa12483c03467ced7023ac2360968c07667f42adc5815c94946` | `3a0437eee96e9f9ca0891095f17af1a9c091db7765e03c4aed9a806084c596fd` (24) |
| `bottomUpLfp_tight_respectsCalls` | bottomup-lfp tight `hresp` | `Quot.sound`, `propext` | `32b520283ce21aa10a9640b0fa587f1f3696946ee6cccd8afd923c601be7b3ca` | `a20ced676234bf310281d5b2bc6cd1809d2a7626fc4e15e09a8d1a98fc6194d3` (24) |
| `caller_first_order_0_1_0_recovers_lfp_and_gfp` | caller-first positive control | `Quot.sound`, `propext` | `1294e051ffc7fca0ee4d6120f39b7c3f87c52a985fb683740d87ecbf64038158` | `354f9978da15e7037dba552ae2db54b5c432058f4a241e2dc92a7daf4c7dff1d` (22) |
| `checkScc_nonvacuous` | scc-check non-vacuity | `Quot.sound`, `propext` | `86e52824d14d144c3b8bbc326e4c2b26223244e2841de0cc58c7db06c9b56624` | `8dfb3ba3a0321ddda774a4554cb6e7abbc1000da603b1ddd4b12e36d96fe1f5f` (16) |
| `cJump_has_nat_measure` | inner-alone positive control | `propext` | `14cf0c19c8deef726ab44254d600c23fa599f3d14270fdd83f114e078dc8ec6a` | `7da95aa8f4fce9e8a1d658473d78c19cb94172312a8bbf86befb1e71b16507e9` (3) |
| `hierBetween_nonvacuous` | bottomup-mixed non-vacuity | `Quot.sound`, `propext` | `3eab970e9805ef4839b35097147700abc65ac42b80357a465640b8e3f52f9eff` | `c9be5078eeeabcaaeea0f4dd8476991fc70cea5efe15e5de9a0b3d35609bef1a` (16) |
| `hierBetween_tight_greatest` | bottomup-mixed tight `betweenness lemma, hnu` | `Quot.sound`, `propext` | `1a984dd0434a528da204d12b4d91fa1d4e29f2b7b75900a500f76b41ae11d68c` | `328055942ff2e60ebf05ae4f286b9d0883acf185d89e1901447724736a120c55` (15) |
| `hierBetween_tight_hierSolution` | bottomup-mixed tight `betweenness lemma, h` | `Quot.sound`, `propext` | `e2e774590f5439ce6556983da0b8555231cba1dad04c9294be9530068e6b1f34` | `1d85e871fccb1e53c5c9e345b5480da94983e347ec8cb56f79f782ffac7b6802` (14) |
| `hierBetween_tight_least` | bottomup-mixed tight `betweenness lemma, hmu` | `Quot.sound`, `propext` | `4cddd956be5fa25c9351b24a86fb390fcbfc5ee0173eb0d43f42a1b30c9a5b17` | `328055942ff2e60ebf05ae4f286b9d0883acf185d89e1901447724736a120c55` (15) |
| `kleene_nonvacuous` | kleene-bound non-vacuity | `Quot.sound`, `propext` | `3d762620c938f1d4d628f91162bc9e7e0c65687bfbbf9c20540c4fb91ab5cfde` | `8f619f959c008e801fe5eb23b40a09df6cdb78bf02380c977165a33a03e52f7a` (13) |
| `kleeneGfp_tight_fuel` | kleene-bound tight `hfuel` | `Quot.sound`, `propext` | `80f6c0350b24bbed61d2a92ecf22d092cdeebb1a59f396d08884301a81cba58f` | `ac18ab1735c22c10f7dcabd592303da861ec5543446b5d3e54ba09113c1399b0` (12) |
| `kleeneGfp_tight_monotone` | kleene-bound tight `hmono` | `propext` | `035e48f6a9afe8c2fa756bde5f4fccd15e27f0efb4f9bc0c49c977f34c9a0001` | `375d80ca845ec933b3b6c1f55bc942c9637ef1023affcf03bf7f5b2311f5e770` (11) |
| `kleeneLfp_tight_fuel` | kleene-bound tight `hfuel` | `Quot.sound`, `propext` | `a066a8261c0708f67fe805a6b3efcf25c107a55f637ad83a3d2db34c427634a2` | `e3d0e3b668eca4acaa6f91fade46aad34bbc4106fd7a926d09c28e2ec4243b1a` (12) |
| `kleeneLfp_tight_monotone` | kleene-bound tight `hmono` | `propext` | `d4ee9a7c2ec66698cc3b58234cb0f4d43fafdec2088be675d38f9a00ffbeb2a8` | `29029f8b9e642a67d017970740209c0f924c7a9163b276550460ee8b582745ea` (11) |
| `lexIff_nonvacuous` | lex-iff non-vacuity | `Quot.sound`, `propext` | `5e0f4c7d1b0c37b3f0e22ed36f45e98e9350eac383f26dc91393c31b276dd5f4` | `54545d7b4a3674c7e3ac1af34beb3a0f90d25658dfd452cdbdfd6041461b2a74` (9) |
| `lexIff_tight_injective` | lex-iff tight `hinj` | `propext` | `d0ed335ba7a48e62faa67a368dcb811caf56bd10dca77aa9fc03d18903940aa6` | `d6371f464d32844835c1fad7d8bf4cc67fbf380114ef2629425ed435948a57d0` (9) |
| `lexTerminates_nonvacuous` | lex-iff non-vacuity | `Quot.sound`, `propext` | `19eceaedda1e9c87f1117d1d66311430acb8cd2db751723fb5cc9ebe486cb16a` | `fb817a170f68c3db03de3d695d5c41d6e3ce17517f7ea75aafda4353a9140090` (7) |
| `lexTerminates_tight_lexDecreasing` | lex-iff tight `h` | `propext` | `4dec8822fc8d57b36ca74888a138b61618aa3637f8b37c9184e471f66e9da9fb` | `4a0abfba3b1935fe7001d68276c56e707f337a4834705cea71433683c96a6ec0` (8) |
| `nonconvex_merge_order_0_1_0_recovers_lfp_and_gfp` | merge-nonconvex positive control | `Quot.sound`, `propext` | `d6c67f8e735c2442d46605bf63bbabc537ae44cfe4ec5cf3ca95db69ca6181f0` | `c860f0464fbfd9db52766c7a860f882df2e6d65417fbc3d5f865807033cdf030` (23) |
| `oneSided_nonvacuous` | bottomup-one-sided non-vacuity | `Quot.sound`, `propext` | `f0bbc7b0f1ed199650ffdef81e27b4662be13582d9fc951368f5bffaff6fe8ee` | `4c9209fe7d549d7fa0d2eafcb7969858865bca4adb054b356f46b407e1ffb20c` (26) |
| `oneSidedGfp_tight_monotone` | bottomup-one-sided tight `hmono` | `propext` | `aef5269d27e69e63fb957ed476299a53b9f2314b35a1ef24620c423ca3c545ff` | `b3a4b36aa5f2b7bf4c0b593407b2367f88edb88ae6665ec75be955d8213d29fc` (20) |
| `oneSidedGfp_tight_postfixpoint` | bottomup-one-sided tight `hpost` | `propext` | `5a327eef4aa56a0ba3be68526acba3eedb04d012e47e824625c8cae33ba2a768` | `a5d5b6f216ca8bf6d06a71e84b2898cc7aae329f07759113f0d3baf24dd4e001` (18) |
| `oneSidedLfp_tight_monotone` | bottomup-one-sided tight `hmono` | `propext` | `069804b19df3451c1366b79baddee18f35342958d6cc9429d932e281f9eae739` | `cd8439c68e752095cfe91ed12cbf8799d94efb232704f2b108288c90dcc0f7ab` (20) |
| `oneSidedLfp_tight_prefixpoint` | bottomup-one-sided tight `hpre` | `propext` | `1d5f7d396f11dd634ced891ec9c6d3edd937036b7141022b1e516873f151f665` | `66656773a3f4b1fce7f4a15c04da74c02e3490ed91956fee139c78c523bb21da` (18) |
| `postfixSound_tight_greatest` | prefix-postfix-sound tight `hnu` | `Quot.sound`, `propext` | `9426f770d198d4e5afa3815cf9a5ca3f9552357af3a5d3eb39388a9c9b4baf00` | `2407a3626458e0ba97d94dcf9e1859e61a37494d6aae8d74a82456f6c602a6d8` (10) |
| `postfixSound_tight_monotone` | prefix-postfix-sound tight `hmono` | `Quot.sound`, `propext` | `a69f1584223d5cc1a70307260715d2506610f1d566e145cdb9165bb3377a574e` | `48b6b100b78d004a3ed332637063ad6f53f6cd72307580204259168af2a551c1` (11) |
| `postfixSound_tight_postfixpoint` | prefix-postfix-sound tight `hpost` | `Quot.sound`, `propext` | `05da2529d0b0037d1143e7fbcd56da5fe24da80fb19481e11ed650ccd0061a34` | `2cc1b0ca519a7b19e16e6e3eab5395a25f8bdaa097922fd902d97e2743dec859` (10) |
| `prefixPostfixSound_nonvacuous` | prefix-postfix-sound non-vacuity | `Quot.sound`, `propext` | `d3acf86593998b6ea1bae5e763aa300d87f8910e63b7baa0094bb0462a08e469` | `d27bf04602875b1e8b1789a8fa455a717813b5bc1fc8a89ab139b26f8eb25089` (14) |
| `prefixSound_tight_least` | prefix-postfix-sound tight `hmu` | `Quot.sound`, `propext` | `5f938849b6745de4ec32971dee44efb1f89ad3a38536e49cd13c3212881bd3f1` | `6bef65e4bb63818cedfafd5e142be868f90dfb51052c28bc6b34792275a5675b` (10) |
| `prefixSound_tight_monotone` | prefix-postfix-sound tight `hmono` | `Quot.sound`, `propext` | `966634e173d5cec99aadadbd001c556aeb91c03a5f53620a4c751b52d52665a1` | `6733c615e7ceaf2db9a8b2660fe688f4103c30a0cdf64929396ed23d942a18d5` (11) |
| `prefixSound_tight_prefixpoint` | prefix-postfix-sound tight `hpre` | `Quot.sound`, `propext` | `27502aaad74bbfce54fb8f12505660f63f439cc6ab57dc99c4972fde485ef048` | `77ae43900b6d6c95b47aef6c8bcee5e3c22bf1c48f02e5f2cf450c65e0732699` (10) |
| `rankedCert_nonvacuous` | ranked-cert non-vacuity | `Quot.sound`, `propext` | `8bea6e78a670d34e34d0b43106b50436912cad7f69786f6573c9c8e2d73cfcaf` | `0140f2ec0d95f50a277c5831e72393c4a5be53f6a6a696c6d71b2cc825f7fd47` (10) |
| `rankedCert_tight_monotone` | ranked-cert tight `hmono` | `propext` | `b6ee2348608fbb346995ae606a67ad3ef646d33f123a5834c7ab6b96db55b7e3` | `22425cc224e391815346fea12db69866759d1d7014a216cf60769861b54787a1` (10) |
| `rankedCert_tight_prefixpoint` | ranked-cert tight `hpre` | `Quot.sound`, `propext` | `2496d785a3f96ac498dde58c7dd32b4b0add3488e5ced480560a9c7f26624ea7` | `ea71fc50760c690f42c0ae9d69797237a3420458c7263c90d1dddf215f57a0ac` (11) |
| `rankedCert_tight_ranking` | ranked-cert tight `hrank` | `Quot.sound`, `propext` | `d2d5c0855739bc041cace26dfd5affbfb5a598679bbba7d8081c45768a37b32d` | `babede77dcc6354c61e8854af59e11965b72780d9b71ab1e84c904235a60b36b` (11) |
| `rankedComplete_nonvacuous` | ranked-cert-complete non-vacuity | `Quot.sound`, `propext` | `94f3648cda954260a31ead5fab9c1b41f4573de178c0a47d34b0449a1b5f84c9` | `1286fe1d0170692fb21bf2613e98efa45e45f140206e13f2ecedee802a2da251` (14) |
| `rankedComplete_tight_least` | ranked-cert-complete tight `hmu` | `Quot.sound`, `propext` | `de01d4af13ff7eea753214e3e94344b3c612551c04482fc86fcbd67def6be036` | `3494d1b9116d2d613607325b2665a024e352daee28c09c4c89a182cacac1f2a5` (16) |
| `rankedComplete_tight_monotone` | ranked-cert-complete tight `hmono` | `Quot.sound`, `propext` | `24c948d683c0a5e41c3ca3cf0c74640706f359006d21c8384026a2deb91cf4dd` | `56a61ed4673fcab6426da7ce6f2edbfc08c271176f166f6a5a6ad95f647d2645` (17) |
| `reachFrom_nonvacuous` | scc-check non-vacuity | `propext` | `8a0e2db632b2a7d747516bccda40209b688aa0f1005d5e67c91721053df26029` | `694b586fecc2f838a01557c6b478a609b56c04849386f949d553bc4fefa0bc07` (9) |
| `reachFrom_tight_fuel` | scc-check tight `hfuel` | `propext` | `c32a52afedffc922a983fd7ff4960922780a9355b712c72ae46d51ed5d122940` | `694b586fecc2f838a01557c6b478a609b56c04849386f949d553bc4fefa0bc07` (9) |
| `sccChar_nonvacuous` | scc-char non-vacuity | `Quot.sound`, `propext` | `3906acbd3aa8e594dea70d1325c1eba48cecd17d2597db70054f5c03be253f3f` | `433e4bae6ecf0b289aa0196a4dfcbcc213cd7e39af2edc76acb074abc9bcf171` (10) |
| `sccChar_tight_acyclic` | scc-char tight `right-hand conjunct (b)` | `propext` | `beef74125692ef4be329fdfeb22549dbbc6cd2dc8f6541f2252d20d0aea110a5` | `3eed499183b39c57bf44a563044e0dc7ec1e6dbf757fc8053ad528cc2ec40c53` (10) |
| `sccChar_tight_mutual` | scc-char tight `right-hand conjunct (a)` | `propext` | `54406ceb341eeb9e9bcc6e11b674d4177b9fe469bb0af52e28836c3b33210395` | `c708d9c6eb2102149b8d7b990b26b174b547d78f342f79aa2ee883a7e96eb5f1` (11) |
| `split_scc_order_0_1_0_recovers_lfp_and_gfp` | split-scc positive control | `Quot.sound`, `propext` | `5f4c87e0c952bd4b2b5d26886e82d17a3cd2c1e864cfa99980e98db5a2d758d8` | `21289a96858302defddd836c0d77687492c5a63a6b6939ca6912e56e54a801b2` (22) |
| `terminationIntra_nonvacuous` | termination-intra non-vacuity | `Quot.sound`, `propext` | `e4d5f5c369525455a26ab7b0d254d6193f04d203d37313cf9d99a064813c36c4` | `d3681aae4daf9442fefe4d0c8776cdd0afe6d9b0f778c6d246f6312201ba1fb1` (10) |
| `terminationIntra_tight_acyclic` | termination-intra tight `hacyc` | `Quot.sound`, `propext` | `0c8e16d86068696b6344d10b9783a85bc566b28ec463ebc796cad3fa04e8fd59` | `d279e9d550d486e310646d1d4cef36ab2733a98a2c57186831c2ae271d7dae1e` (10) |
| `terminationIntra_tight_callsInGraph` | termination-intra tight `hin` | `Quot.sound`, `propext` | `ccf999a6dd72fd3f5c0cfe4a11174560a88c6723c9f0cbbddc17d8dcaa45fb17` | `a86ae8a7e83e96bf50c62e34f89fb3c8e20c90db42d2b4346e136be603193053` (10) |
| `terminationIntra_tight_intraDecrease` | termination-intra tight `hdec` | `propext` | `4e733856645d5fc3e4c55dddf0baff0693d31a904b69711a11fd35992aa21fcd` | `e6c2d64e943f2936b117e0c535fe77304202a814b624644457467255f861a71c` (11) |
| `topoOrder_nonvacuous` | topo-order non-vacuity | `Quot.sound`, `propext` | `0f09880e9a3ddb65b077a9fbb4729385613e0d83162bc228dae36a3127fa0852` | `2c6067a591d94064a604d58c207d1a01bc2501f4e91f8194115bc369a784fc70` (9) |

Other quoted theorems (supporting lemmas, definition examples, boundary examples), axioms: `condensationAcyclic_of_calleesFirst`: none; `hierSolution_bottomUp`: `Classical.choice`, `Quot.sound`, `propext`; `hierSolution_chainLfpT_top`: `Quot.sound`, `propext`; `hierSolution_idT_bot_least`: `Quot.sound`, `propext`; `hierSolution_idT_top_greatest`: `Quot.sound`, `propext`; `hierSolution_of_isGreatestFixpoint`: `Classical.choice`, `Quot.sound`, `propext`; `hierSolution_of_isLeastFixpoint`: `Classical.choice`, `Quot.sound`, `propext`; `hierSolution_swapT_gCycle_mixSign_not_unique`: `Quot.sound`, `propext`; `hierSolution_unique`: `Quot.sound`, `propext`; `isGreatestFixpoint_chainGfpT_bot`: `Quot.sound`, `propext`; `isGreatestFixpoint_idT_top`: `Quot.sound`, `propext`; `isGreatestFixpoint_of_iter_fixed`: none; `isLeastFixpoint_chainLfpT_top`: `Quot.sound`, `propext`; `isLeastFixpoint_idT_bot`: `Quot.sound`, `propext`; `isLeastFixpoint_of_iter_fixed`: `propext`; `isSccDecomp_gCycle_one`: `Quot.sound`, `propext`; `isSccDecomp_gMix_id`: `Quot.sound`, `propext`; `isSccDecomp_gPath3_id`: `Quot.sound`, `propext`; `isSccDecomp_gPathLoop1_id`: `Quot.sound`, `propext`; `isSccDecomp_gPath_id`: `Quot.sound`, `propext`; `kleeneRank_lt_height`: `Quot.sound`, `propext`; `lexDecreasing_cUnbounded`: `Quot.sound`, `propext`; `lexDecreasing_pos_iff_of_covers`: `Classical.choice`, `Quot.sound`, `propext`; `no_nat_measure_cUnbounded`: `Quot.sound`, `propext`; `not_calleesFirst_gCycle_id`: `Quot.sound`, `propext`; `not_calleesFirst_gPath3_merge`: `Quot.sound`, `propext`; `not_calleesFirst_gPath_omitted_callee`: `propext`; `not_calleesFirst_gPath_omitted_caller`: `propext`; `not_condensationAcyclic_gCycle_id`: `propext`; `not_hierSolution_chainLfpT_bot`: `Quot.sound`, `propext`; `not_hierSolution_idT_top_least`: `Quot.sound`, `propext`; `not_isGreatestFixpoint_idT_bot`: `Quot.sound`, `propext`; `not_isLeastFixpoint_idT_top`: `Quot.sound`, `propext`; `not_isSccDecomp_gCycle_id`: `propext`; `not_isSccDecomp_gPath3_convexMerge`: `propext`; `not_isSccDecomp_gPath3_merge`: `propext`; `not_isSccDecomp_gPath_one`: `propext`; `not_monotone_negT`: `propext`; `not_reach_gPath3_2_0`: `propext`; `not_respectsCalls_gEmpty_chainLfpT`: `propext`; `pos_injective_on_used_blocks_of_covers`: `Classical.choice`, `Quot.sound`, `propext`; `reach_gCycle`: `propext`; `reach_gPath3_0_2`: `propext`; `split_scc_one_bit_some_duplicate_free_order_correct`: `Quot.sound`, `propext`; `swapT_monotone`: `Quot.sound`, `propext`; `swapT_respectsCalls`: `Quot.sound`, `propext`; `terminates_cUnbounded`: `Quot.sound`, `propext`. These names carry no recorded statement hash; like every declaration of the package, each uses at most `propext`, `Classical.choice` and `Quot.sound` (see `audit/axioms.json`).

**Primary sources.** Exact records as cited on the cards. Verification scope (as of 2026-11-20): the bibliographic metadata (title, authors, venue, volume, issue, pages, year) of every DOI below was confirmed either against Crossref (Tarjan, Lammich 2014, Bourdoncle, Cousot and Cousot 1979, Bekić, Reps et al., Bulwahn et al.) or against the publisher landing page reached through `doi.org` (Chen et al., Tarski, Cleaveland and Steffen, Neele and van de Pol including the arXiv identifier and the Zenodo record, Krauss, Thiemann and Sternagel, Manolios and Vroon, Namjoshi, Tan and Cleaveland, and the title of Nielson, Nielson and Hankin); for Kahn, Burke, Lammich and Neumann, Jourdan et al., Seidl, Arts and Giesl and Aczel (whose publisher landing pages were not available) and for the records without DOI (Kleene, Winskel, Sharir and Pnueli, Cousot 1977, Mader, Park, the Archive of Formal Proofs entries), against bibliographic databases and publisher or author pages. The pinned repository commits and the cited declarations were checked at the source: `rocq-community/tarjan` at `34fe042cc482e65d27bc68b455d922d47da81c9d` (`theories/acyclic.v`: `Definition sccs_acyclic := all [pred c | class_acyclic c] (scc_seq g)` and `Lemma sccs_acyclicE : sccs_acyclic = acyclic g`; `theories/kosaraju.v`: `Lemma tseq_correct : TS[tseq] /\ forall x, x \in tseq`; `theories/acyclic_tsorted.v`: `Lemma tseq_connect_before`), `AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc` (`lib/Postorder.v`: `Theorem postorder_correct`; `backend/Kildall.v`: `Theorem fixpoint_solution`), `leanprover-community/mathlib4` at `a205649cf4e6ce1ae4ef6f0a3466f58a30fcdd22` (`Mathlib/Order/FixedPoints.lean`: `theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a` and `theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ f.gfp`, in namespace `OrderHom`), and the Lean `v4.34.1` sources installed with the toolchain (`src/lean/Lean/Util/SCC.lean`: module doc "Very simple implementation of Tarjan's SCC algorithm", `def scc`; `src/lean/Lean/Elab/PreDefinition/Main.lean`: `private def partitionPreDefs`, which calls `SCC.scc`; `src/lean/Init/Internal/Order/Basic.lean`: `theorem lfp_le_of_le`, documented as "Park induction principle for least fixpoint"). Content attributions to papers and books (what each source contains, beyond its bibliographic record) are as stated on each card and have not been verified against the full texts; a reader relying on one should check it at the source.

- R. E. Tarjan, "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1(2):146-160, 1972, doi:10.1137/0201010.
- A. B. Kahn, "Topological sorting of large networks", Communications of the ACM 5(11):558-562, 1962, doi:10.1145/368996.369025.
- F. Bourdoncle, "Efficient chaotic iteration strategies with widenings", Formal Methods in Programming and Their Applications (FMPA 1993), LNCS 735, pp. 128-141, doi:10.1007/BFb0039704.
- S. C. Kleene, Introduction to Metamathematics, Van Nostrand, 1952, Section 66, Theorem XXVI (first recursion theorem).
- P. Cousot and R. Cousot, "Constructive versions of Tarski's fixed point theorems", Pacific Journal of Mathematics 82(1):43-57, 1979, doi:10.2140/pjm.1979.82.43.
- F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer, 1999, doi:10.1007/978-3-662-03811-6.
- A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285.
- H. Bekić, "Definable operations in general algebras, and the theory of automata and flowcharts", 1969 report, reprinted in C. B. Jones (ed.), Programming Languages and Their Definition, LNCS 177, Springer, 1984, pp. 30-55, doi:10.1007/BFb0048939.
- G. Winskel, The Formal Semantics of Programming Languages, MIT Press, 1993, Section 10.1 (Bekić's theorem).
- R. Cleaveland and B. Steffen, "A linear-time model-checking algorithm for the alternation-free modal mu-calculus", Formal Methods in System Design 2(2):121-147, 1993, doi:10.1007/BF01383878.
- A. Mader, Verification of Modal Properties Using Boolean Equation Systems, Edition versal 8, Bertz Verlag, Berlin, 1997, ISBN 3-929470-58-6.
- T. Neele and J. van de Pol, "Operations on fixpoint equation systems", Logical Methods in Computer Science 20(3), 2024, doi:10.46298/lmcs-20(3:5)2024 (arXiv:2304.07162); replication package, doi:10.5281/zenodo.7828484.
- H. Seidl, "Fast and simple nested fixpoints", Information Processing Letters 59(6):303-308, 1996, doi:10.1016/0020-0190(96)00130-5.
- M. G. Burke, "An interval-based approach to exhaustive and incremental interprocedural data-flow analysis", ACM Transactions on Programming Languages and Systems 12(3):341-395, 1990, doi:10.1145/78969.78963.
- M. Sharir and A. Pnueli, "Two approaches to interprocedural data flow analysis", in S. S. Muchnick and N. D. Jones (eds.), Program Flow Analysis: Theory and Applications, Prentice-Hall, 1981, pp. 189-233.
- T. Reps, S. Horwitz and M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", POPL 1995, pp. 49-61, doi:10.1145/199448.199462.
- P. Cousot, "Asynchronous iterative methods for solving a fixed point system of monotone equations in a complete lattice", Research Report R.R. 88, Laboratoire IMAG, Université scientifique et médicale de Grenoble, September 1977.
- J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy and D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966.
- D. M. R. Park, "Fixpoint induction and proofs of program properties", in B. Meltzer and D. Michie (eds.), Machine Intelligence 5, Edinburgh University Press, 1969, pp. 59-78.
- L. Bulwahn, A. Krauss and T. Nipkow, "Finding lexicographic orders for termination proofs in Isabelle/HOL", TPHOLs 2007, LNCS 4732, pp. 38-53, doi:10.1007/978-3-540-74591-4_5.
- A. Krauss, "Partial and nested recursive function definitions in higher-order logic", Journal of Automated Reasoning 44(4):303-336, 2010, doi:10.1007/s10817-009-9157-2.
- T. Arts and J. Giesl, "Termination of term rewriting using dependency pairs", Theoretical Computer Science 236(1-2):133-178, 2000, doi:10.1016/S0304-3975(99)00207-8.
- R. Thiemann and C. Sternagel, "Certification of termination proofs using CeTA", TPHOLs 2009, LNCS 5674, pp. 452-468, doi:10.1007/978-3-642-03359-9_31.
- P. Manolios and D. Vroon, "Termination analysis with calling context graphs", CAV 2006, LNCS 4144, pp. 401-414, doi:10.1007/11817963_36.
- P. Aczel, "An introduction to inductive definitions", in J. Barwise (ed.), Handbook of Mathematical Logic, North-Holland, 1977, pp. 739-782, doi:10.1016/S0049-237X(08)71120-0.
- K. S. Namjoshi, "Certifying model checkers", CAV 2001, LNCS 2102, pp. 2-13, doi:10.1007/3-540-44585-4_2.
- L. Tan and R. Cleaveland, "Evidence-based model checking", CAV 2002, LNCS 2404, pp. 455-470, doi:10.1007/3-540-45657-0_37.
- P. Lammich, "Verified efficient implementation of Gabow's strongly connected component algorithm", ITP 2014, LNCS 8558, pp. 325-340, doi:10.1007/978-3-319-08970-6_21; Archive of Formal Proofs entry Gabow_SCC, https://www.isa-afp.org/entries/Gabow_SCC.html.
- R. Chen, C. Cohen, J.-J. Lévy, S. Merz and L. Théry, "Formal proofs of Tarjan's strongly connected components algorithm in Why3, Coq and Isabelle", ITP 2019, LIPIcs 141, article 13, doi:10.4230/LIPIcs.ITP.2019.13.
- P. Lammich and R. Neumann, "A framework for verifying depth-first search algorithms", CPP 2015, pp. 137-146, doi:10.1145/2676724.2693165; Archive of Formal Proofs entry DFS_Framework.
- S. Merz and V. Trélat, "Correctness of a set-based algorithm for computing strongly connected components of a graph", Archive of Formal Proofs entry SCC_Bloemen_Sequential, 2022.
- rocq-community/tarjan, https://github.com/rocq-community/tarjan, commit 34fe042cc482e65d27bc68b455d922d47da81c9d.
- AbsInt/CompCert, https://github.com/AbsInt/CompCert, commit 2685140bf72c959446981fb99b5e44a8975021bc.
- Mathlib, https://github.com/leanprover-community/mathlib4, commit a205649cf4e6ce1ae4ef6f0a3466f58a30fcdd22 (cited for comparison only; not a dependency).
- Lean 4, https://github.com/leanprover/lean4, release v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52 (the toolchain; also cited for `Lean.SCC.scc`, `partitionPreDefs` and `Lean.Order.lfp_le_of_le`).

## Revalidation

Requires `elan` (the file `lean/lean-toolchain` selects `leanprover/lean4:v4.34.1`, which `elan` installs on first use) and `python3`. The primary check is one command, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` (a self-contained Python 3 script with no dependencies beyond the standard library) never modifies the package. It scans the Lean sources, builds a copy of `lean/` in a temporary directory, and checks, in this order:

1. No Lean source under `lean/` contains `sorry`, `admit` or `native_decide`, or declares an `axiom` (comments are stripped before the scan).
2. `lake build` of the copy succeeds.
3. Every non-internal declaration of the `Toy` modules depends only on `propext`, `Classical.choice` and `Quot.sound`, as computed by `Lean.collectAxioms` in a generated audit file that imports `Toy`.
4. For every Lean name referenced in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and the `counterexample` of each hypothesis) and every name recorded in `audit/statements.json`, the declaration exists, and its hashes equal the recorded ones. Exactly what is hashed: `statement_sha256` is the SHA-256 of `toString (repr ci.type)`, the `Lean.Expr` of the statement; `closure_sha256` is the SHA-256 of the newline-joined, sorted list of entries `name : repr type`, followed by ` := repr value` for constants that are not theorems, over all constants of the `Toy` modules reachable from the statement's type through types, through values of non-theorems, and through constructors of inductive types (theorem proofs are excluded); `closure_size` is the number of entries. Names listed only in `supporting_lean` are not hashed.

Expected output for this package:

```text
ok   lake build
ok   axioms (433 declarations)
ok   statement hashes (93 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

The exit status is 0 exactly when every check passes. The build, axiom and hash checks can also be run by hand with `lake` and `python3` only, as follows.

Build, from the package directory:

```sh
cd lean
lake build                      # must end with: Build completed successfully (12 jobs).
```

Axiom audit, run from `lean/` (fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`, or on any `axiom`/`opaque` declaration); expected output `AXIOM_AUDIT_OK 433 declarations; axioms within propext, Classical.choice, Quot.sound`:

```sh
cat > /tmp/AxiomAudit.lean <<'EOF'
import Lean
import Toy
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      if (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]! && !n.isInternal then
        if ci matches .axiomInfo _ || ci matches .opaqueInfo _ then
          throwError "{n} is an axiom or opaque declaration"
        for a in (← collectAxioms n) do
          unless allowed.contains a do throwError "{n} depends on {a}"
        checked := checked + 1
    | none => pure ()
  IO.println s!"AXIOM_AUDIT_OK {checked} declarations; axioms within propext, Classical.choice, Quot.sound"
EOF
lake env lean /tmp/AxiomAudit.lean
```

For a readable per-theorem record, `#print axioms Toy.Scc.<name>` for any name in the Evidence tables prints the same axiom sets.

Statement and closure hashes, run from `lean/` (the commands below write and remove a temporary `names.txt` there); expected output `{"checked": 93, "mismatches": []}`:

```sh
cat > /tmp/names.py <<'EOF'
import json, sys
names = set()
def add(v):
    if isinstance(v, str):
        names.add(v)
    elif v:
        names.update(v)
for r in json.load(open(sys.argv[1])):
    for k in ("lean", "lean_names", "nonvacuity_witness_lean", "positive_control_lean"):
        add(r.get(k))
    for h in r["hypotheses"]:
        add(h.get("counterexample"))
print("\n".join(sorted(names)))
EOF
cat > /tmp/hashes.py <<'EOF'
import hashlib, json, sys
out = {}
for l in sys.stdin:
    if l.startswith("{"):
        d = json.loads(l)
        out[d["name"]] = {
            "statement_sha256": hashlib.sha256(d["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(d["closure"]).encode()).hexdigest(),
            "closure_size": len(d["closure"]),
        }
ref = json.load(open(sys.argv[1]))["statements"]
bad = sorted(n for n in set(ref) | set(out) if ref.get(n) != out.get(n))
print(json.dumps({"checked": len(out), "mismatches": bad}))
sys.exit(1 if bad else 0)
EOF
cat > /tmp/StatementHashes.lean <<'EOF'
import Lean
import Toy
open Lean Elab Command

/-- Constants defined in a module of the `Toy` library. -/
def inToy (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

/-- `Toy` constants reachable from the given names through types, and through
values of non-theorems, plus constructors of inductive types. -/
partial def closure (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n || !inToy env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let vs := match ci.value? (allowOpaque := true) with
        | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
        | none => []
      let ks := match ci with
        | .inductInfo iv => iv.ctors
        | _ => []
      closure env (ci.type.getUsedConstants.toList ++ vs ++ ks ++ rest) acc

def line (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
      (match cc.value? (allowOpaque := true) with
       | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
       | none => "")
  | none => c.toString

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := ((← IO.FS.readFile "names.txt").splitOn "\n").filter (· ≠ "")
  for s in names do
    let n := s.toName
    let some ci := env.find? n | throwError "missing {n}"
    let cl := (closure env ci.type.getUsedConstants.toList {}).toList.map (line env)
    IO.println (Json.mkObj [("name", toJson s), ("type_repr", toJson (toString (repr ci.type))),
      ("closure", toJson (cl.toArray.qsort (· < ·)))]).compress
EOF
python3 /tmp/names.py ../results.json > names.txt
lake env lean /tmp/StatementHashes.lean | python3 /tmp/hashes.py ../audit/statements.json
rm names.txt
```

A change of any statement or of any definition it depends on changes its hashes; a change confined to proofs or doc comments does not. The checks establish only kernel validity, axiom usage and statement identity; the modeling bridges and the prior-art attributions must be re-checked by reading.
