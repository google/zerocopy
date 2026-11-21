# SSA φ placement, dominance frontiers, join sets, and out-of-SSA copy problems: a kernel-checked toy model in Lean 4

## Summary

This package states and proves, in Lean 4 with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, 22 results about a toy model of static single assignment (SSA) form: where φ-functions must be placed (join sets `J(S)` versus iterated dominance frontiers `DF⁺(S)`, judged by per-block reaching definitions), the value correctness of SSA construction by `DF⁺` placement plus dominator-tree renaming, and when replacing φ-functions by copies at the ends of predecessor blocks is a correct out-of-SSA translation (critical edges, parallel versus sequential copies, exit modeling, the lost-copy and swap problems).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (each is the result's full plain-language claim; Lean statements, hypothesis ledgers and witnesses are under Findings):

1. **`join-subset-iterated-df-of-all-reachable`** (theorem, T0). In a finite CFG in which every node is reachable from the entry, for every set S of nodes, every join node of S (a node at which two nonnull walks starting at two distinct nodes of S converge in Cytron et al.'s sense) lies in the iterated dominance frontier DF+(S).
2. **`iterated-df-subset-join-of-entry-mem`** (theorem, T0). In a finite CFG in which every node is reachable from the entry and no edge enters the entry, for every set S of nodes that contains the entry, every node of the iterated dominance frontier DF+(S) is a join node of S.
3. **`join-eq-iterated-df-of-entry-mem`** (characterization, T0). In a finite CFG in which every node is reachable from the entry and no edge enters the entry, for every set S of nodes that contains the entry, the join set J(S) equals the iterated dominance frontier DF+(S).
4. **`join-union-join-subset-join`** (theorem, T2). In every finite CFG and for every set S of nodes, J(S u J(S)) is contained in J(S): a node at which walks from two distinct nodes of S or of J(S) converge is already a join node of S.
5. **`single-reaching-def-of-join-closed`** (theorem, T1). In every finite CFG, for definition blocks D and a phi placement P with J(D u P) contained in P (join closure), at the top of every block without a phi, the entry included, at most one definition point of D u P reaches (singleReachingDefAll_of_joinClosed); in particular this holds at every non-entry block without a phi (singleReachingDef_of_joinClosed).
6. **`join-closed-of-single-reaching-def`** (theorem, T1). In a finite CFG with no edge into the entry, if at the top of every non-entry block without a phi at most one definition point of D u P reaches, then J(D u P) is contained in P (joinClosed_of_entryNoPreds_of_singleReachingDef). In every finite CFG, if at the top of every block without a phi, the entry included, at most one definition point of D u P reaches (SingleReachingDefAll), then J(D u P) is contained in P (joinClosed_of_singleReachingDefAll).
7. **`single-reaching-def-at-join`** (theorem, T2). In every finite CFG and for every set D of definition blocks, placing phis at J(D) leaves at most one definition point of D u J(D) reaching the top of every non-entry block without a phi.
8. **`single-reaching-def-at-iterated-df-of-all-reachable`** (theorem, T0). In a finite CFG in which every node is reachable from the entry, for every set D of definition blocks, placing phis at DF+(D) leaves at most one definition point of D u DF+(D) reaching the top of every non-entry block without a phi.
9. **`exists-reaches-top-of-entry-mem`** (theorem, T1). In every finite CFG, if the entry is a definition point, then for every placement P some definition point of D u P reaches the top of every reachable non-entry block.
10. **`exists-unique-reaches-top-at-iterated-df`** (theorem, T0). In a finite CFG in which every node is reachable from the entry, for definition blocks D containing the entry, at the top of every non-entry block outside DF+(D) exactly one definition point of D u DF+(D) reaches.
11. **`reaches-top-iff-nearest-sdom-def-at-iterated-df`** (characterization, T0). In a finite CFG in which every node is reachable from the entry, for every set D of definition blocks, every block b outside DF+(D), and every block u, u reaches the top of b as a definition point of D u DF+(D) if and only if u is the nearest definition point of D u DF+(D) strictly dominating b (both sides require u to lie in D u DF+(D)).
12. **`join-subset-of-single-reaching-def`** (theorem, T0). In a finite CFG with no edge into the entry, every phi placement P under which at most one definition point of D u P reaches the top of every non-entry block without a phi contains J(D).
13. **`ssa-construct-preserves-values`** (theorem, T0). For a source program in which no block reachable from the entry has an edge into the entry, whose assigned variables all lie in vars, with a phi placement equal to DF+ of each variable's definition points (entry included) and a renaming source that picks, at every reachable non-entry block without a phi for x, the nearest strictly dominating definition point of x (phis included), and an SSA initial store that holds each variable's initial value in its entry name: on every walk from the entry with last block b, (1) on entry to b every variable's source value equals the value of the SSA name the construction reads for an upward-exposed use at b, and (2) after b's body every variable's source value equals the value of its live-out SSA name at b. The acyclic corollary replaces the entry hypothesis by acyclicity.
14. **`ssa-construct-single-assignment`** (theorem, T0). For every source program, placement, and renaming source, if the list vars has no duplicates then the constructed program is in static single-assignment form (every SSA name has at most one static definition, a phi destination or an instruction destination), and no phi or instruction defines an entry name (x, entry, 0).
15. **`naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ`** (theorem, T2). For every SSA program in which every predecessor of a block carrying phis has that block as its only successor, the naive translation with parallel copies satisfies, along every walk with last block b: (a) on entry to b (after b's phis in the SSA program) the two stores are equal on all variables, and (b) if no successor of b carries phis, the stores are also equal after b's body.
16. **`naive-out-of-ssa-parallel-eq-of-no-critical-edges`** (theorem, T0). For every SSA program whose CFG has no critical edges and whose phis occur only at blocks with two distinct predecessors, the naive translation with parallel copies satisfies conclusions (a) and (b) of naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ along every walk.
17. **`naive-out-of-ssa-sequential-eq-of-seq-safe`** (theorem, T1). For every SSA program in which every predecessor of a block carrying phis has that block as its only successor and in which, for every pair of blocks (p, b) (including non-edges, since SsaProg.phis supplies total operand functions), no phi destination of b is the destination or the p-operand of a later phi of b (SeqSafe (P.phiMoves p b)), the naive translation with sequential copies in phi order satisfies conclusions (a) and (b) of the parallel theorem along every walk. At the level of one move list: SeqSafe moves executed one at a time have the effect of the parallel copy.
18. **`naive-out-of-ssa-block-end-needs-exit-edge`** (counterexample, T0). On the lost-copy loop 0 -> 1, 1 -> 1 without an exit block (the return of x2 at the end of block 1 not modeled as an edge), every predecessor of the phi block has a single successor, no edge is critical, and the block-entry stores agree on the walk [0, 1, 1], but at the end of block 1 the naive translation with parallel copies has x2 = 3 while the SSA program has x2 = 2.
19. **`swap-sequential-either-order-wrong`** (counterexample, T0). On the swap loop (a1 := 1, b1 := 2; header phis a2 = phi(a1, b2), b2 = phi(b1, a2); back edge split by a latch block), after one back-edge traversal the SSA program has (a2, b2) = (2, 1), while the naive translation with sequential copies gives (2, 2) in phi order [a2, b2] and (1, 1) in phi order [b2, a2].
20. **`swap-temp-sequence-correct`** (theorem, T0). On every walk of the swap CFG, the out-of-SSA program swapTempProg (block 0: a1 := 1; b1 := 2; a2 := a1; b2 := b1; latch block 2: t := a2; a2 := b2; b2 := t) agrees with the swap SSA program on entry to the last block on every variable other than the temporary t.
21. **`lost-copy-naive-miscompiles`** (counterexample, T0). On Briggs et al.'s lost-copy loop (CFG 0 -> 1, 1 -> 1, 1 -> 2; x1 := 1; x2 = phi(x1, x3); x3 := x2 + 1; the exit reads x2), on the walk [0, 1, 1, 2] the source returns 2 and the SSA program has x2 = 2 at the exit, but the naive translation has x2 = 3 with parallel copies and with sequential copies.
22. **`lost-copy-split-fixes`** (theorem, T0). For every number k of back-edge traversals (the loop body runs k + 1 >= 1 times) and every initial store, the naive parallel-copy translation of the lost-copy program on the CFG with the critical edge 1 -> 1 split by a new block 3 reaches the exit with the same store as the SSA program on the original CFG.

What each result does **not** show is listed first under Boundaries (Non-claims), card by card. These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about LLVM, Cranelift, rustc, or any other compiler. Connections to real compilers are separate `derived (modeling bridge)` claims under Applicability and in the affected cards.

## Applicability

**Model fidelity.** Everything here is a toy model (namespace `Toy.Ssa`). The definitions are meant to capture the control-flow graph (CFG) of one procedure, Cytron et al.'s notions of dominance, dominance frontier, iterated dominance frontier and path convergence, per-block reaching definitions of one variable, and two compiler passes over a tiny imperative language: SSA construction and naive out-of-SSA translation. Known gaps:

- A CFG is a Boolean adjacency relation on `Fin n` with a designated entry: a simple directed graph, so parallel edges between the same two blocks (for example switch arms with one target that carry different φ operands) are collapsed.
- There is no built-in exit block: a return, halt or exceptional exit out of block `p` appears in the model as an edge from `p` to an explicit exit block, or not at all. The out-of-SSA block-end results depend on this (`naive-out-of-ssa-block-end-needs-exit-edge`).
- Dominance is the semantic all-walks notion (`Dom G a b`: every walk from the entry to `b` contains `a`); it holds vacuously at blocks unreachable from the entry. No dominator-tree or dominance-frontier algorithm is modeled or verified.
- Programs are per-block lists of assignments `x := e` over natural-number variables and values, with expressions built from literals, variables and `+`. Blocks have no terminator instructions, so a branch that reads a variable overwritten by copies appended at the end of its block is not modeled. Branch conditions are not modeled: an execution is any walk of the CFG (all paths are feasible). There is no memory, aliasing, call or exception edge.
- Values are compared on entry to the last block of a walk (`atTop`) and, in the SSA-construction and out-of-SSA theorems, also at the end of the last block (`run`). φ-functions execute as one parallel copy on entry to a block, reading the store left by the predecessor; a repeated φ destination takes its first entry.
- Every variable has an implicit initial definition at the entry (`Src.defPts` contains the entry), unlike compilers that give uninitialized variables an undefined value along definition-free paths.
- `SsaProg` is syntax: single assignment, distinct φ destinations, strictness, and the absence of φs at the entry are not built into the type.
- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled by the placement results.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only: no Mathlib and no `Std` import. The Lake project is `lean/` (package `toy-ssa`, library `ToySsa`, modules `Cfg`, `Decide`, `Examples`, `Lang`, `Placement`, `OutOfSsa`, `Construct`).

**Subjects and their relationship.** `REPORT.json` lists the Lean toolchain release, which is the system that checked every proof, and the primary papers whose results are restated (Cytron et al. 1991; Weiss 1992; Briggs et al. 1998; Bilardi and Pingali 2003; Rideau, Serpette, and Leroy 2008; Boissinot et al. 2009). The papers are sources for the known results that cards marked T0, T1 or T2 restate in this vocabulary; nothing in the package mechanizes the papers' own definitions verbatim, and differences are recorded per card (for example Cytron et al. assume every node lies on a path from the entry, which corresponds to the hypothesis `AllReachable` here).

**Exact observation versus broader applicability.** What is established is exactly the set of Lean statements quoted under Findings, checked by the Lean kernel under the toolchain above. Each statement quantifies over all finite CFGs `Cfg n` (every `n`) or all programs of the stated shape, except the counterexample cards and the cards about one fixed program (`swap-temp-sequence-correct`, `lost-copy-split-fixes`), which say so in their claims.

**Modeling bridges to real compilers** (`Basis: derived (modeling bridge)`; not checked by Lean). These connect the toy model to source code inspected on 2026-11-21 (model–system relation: none proved); they neither establish nor refute properties of those compilers.

- (a) LLVM (`llvm/llvm-project` at commit `4e7821e89a0cb307ea61620b5c17e9ff7028cb8a`, file `llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp`): mem2reg computes φ blocks with `ForwardIDFCalculator`, given the defining blocks and the live-in blocks (`IDF.setLiveInBlocks`, `IDF.setDefiningBlocks`, `IDF.calculate`, lines 901 and 978-988), that is, a liveness-pruned iterated dominance frontier, and initializes renaming with an undefined value for each promoted slot (`UndefValue::get`, line 1009). This package models the unpruned placement `DF⁺(defs ∪ {entry})` with an initial definition at the entry and has no allocas, loads or stores, so it bears on mem2reg through the shared φ-placement and dominator-tree-renaming structure and no further.
- (b) Cranelift (`bytecodealliance/wasmtime` at commit `64d5afa6960f5a20536f9404b64f2d26b2611990`, file `cranelift/frontend/src/ssa.rs`, lines 1-8) states that its SSA builder follows Braun et al. (CC 2013), an on-the-fly construction with block parameters rather than dominance frontiers. The out-of-SSA results bear on it insofar as block parameters are resolved by per-edge parallel moves.
- (c) rustc's MIR (`rust-lang/rust`) is not an SSA form with φ-functions; rustc reaches SSA through its LLVM and Cranelift backends, so any bridge to rustc is indirect through (a) and (b).

## Findings

Every finding below has `Basis: execution (Lean kernel check)`: the quoted Lean statement was elaborated and its proof checked by the Lean kernel (see Evidence for axioms and statement hashes). Statement blocks are verbatim quotes of the Lean source with the proof elided, each headed by its `file:line` range relative to the package directory. Blocks labelled "unfolded" are Lean terms that elaborate in the theorem's context and are definitionally equal to the quoted statement.

### Definitions

Core graph notions (verbatim; `variable {n : Nat}` is in scope):

```lean
-- lean/ToySsa/Cfg.lean:13-15
structure Cfg (n : Nat) where
  edge : Fin n → Fin n → Bool
  entry : Fin n
-- lean/ToySsa/Cfg.lean:26-29
inductive Walk (G : Cfg n) : Fin n → Fin n → List (Fin n) → Prop
  | single (a : Fin n) : Walk G a a [a]
  | cons {a b c : Fin n} {p : List (Fin n)} :
      G.edge a b = true → Walk G b c p → Walk G a c (a :: p)
-- lean/ToySsa/Cfg.lean:32
def Reachable (G : Cfg n) (b : Fin n) : Prop := ∃ p, Walk G G.entry b p
-- lean/ToySsa/Cfg.lean:35
def AllReachable (G : Cfg n) : Prop := ∀ b, Reachable G b
-- lean/ToySsa/Cfg.lean:38
def EntryNoPreds (G : Cfg n) : Prop := ∀ a, G.edge a G.entry = false
-- lean/ToySsa/Cfg.lean:42
def EntryNoReachablePreds (G : Cfg n) : Prop := ∀ a, Reachable G a → G.edge a G.entry = false
-- lean/ToySsa/Cfg.lean:49
def Dom (G : Cfg n) (a b : Fin n) : Prop := ∀ p, Walk G G.entry b p → a ∈ p
-- lean/ToySsa/Cfg.lean:52
def SDom (G : Cfg n) (a b : Fin n) : Prop := Dom G a b ∧ a ≠ b
-- lean/ToySsa/Cfg.lean:56-57
def DF (G : Cfg n) (a y : Fin n) : Prop :=
  (∃ p, G.edge p y = true ∧ Dom G a p) ∧ ¬ SDom G a y
-- lean/ToySsa/Cfg.lean:61-63
inductive IDF (G : Cfg n) (S : Fin n → Prop) : Fin n → Prop
  | base {x y : Fin n} : S x → DF G x y → IDF G S y
  | step {x y : Fin n} : IDF G S x → DF G x y → IDF G S y
-- lean/ToySsa/Cfg.lean:68-71
def Converge (G : Cfg n) (x y z : Fin n) (p q : List (Fin n)) : Prop :=
  x ≠ y ∧ Walk G x z p ∧ Walk G y z q ∧ 2 ≤ p.length ∧ 2 ≤ q.length ∧
    ∀ (i : Fin p.length) (j : Fin q.length), p[i] = q[j] →
      i.val + 1 = p.length ∨ j.val + 1 = q.length
-- lean/ToySsa/Cfg.lean:75-76
def InJoin (G : Cfg n) (S : Fin n → Prop) (z : Fin n) : Prop :=
  ∃ x y p q, S x ∧ S y ∧ Converge G x y z p q
```

`IDF G S` is the least set `T` with `DF(S ∪ T) ⊆ T`. `Converge` is Cytron et al.'s convergence of two nonnull walks (conditions (1)-(3)); the "or" lets one walk be a cycle through `z`. `InJoin G S` is the join set `J(S)`.

Reaching definitions and the renaming source (verbatim):

```lean
-- lean/ToySsa/Cfg.lean:80-82
inductive Clear (G : Cfg n) (Defs : Fin n → Prop) : Fin n → Fin n → Prop
  | here (b : Fin n) : Clear G Defs b b
  | step {v w b : Fin n} : ¬ Defs v → G.edge v w = true → Clear G Defs w b → Clear G Defs v b
-- lean/ToySsa/Cfg.lean:87-88
def ReachesTop (G : Cfg n) (Defs : Fin n → Prop) (u b : Fin n) : Prop :=
  Defs u ∧ ∃ v, G.edge u v = true ∧ Clear G Defs v b
-- lean/ToySsa/Cfg.lean:94-96
def SingleReachingDef (G : Cfg n) (D P : Fin n → Prop) : Prop :=
  ∀ b, ¬ P b → b ≠ G.entry → ∀ u v,
    ReachesTop G (fun w => D w ∨ P w) u b → ReachesTop G (fun w => D w ∨ P w) v b → u = v
-- lean/ToySsa/Placement.lean:533-535
def SingleReachingDefAll (G : Cfg n) (D P : Fin n → Prop) : Prop :=
  ∀ b, ¬ P b → ∀ u v,
    ReachesTop G (fun w => D w ∨ P w) u b → ReachesTop G (fun w => D w ∨ P w) v b → u = v
-- lean/ToySsa/Cfg.lean:102-103
def NearestSDomDef (G : Cfg n) (Defs : Fin n → Prop) (b d : Fin n) : Prop :=
  Defs d ∧ SDom G d b ∧ ∀ d', Defs d' → SDom G d' b → Dom G d' d
-- lean/ToySsa/Construct.lean:14
def Acyclic (G : Cfg n) : Prop := ∀ a p, Walk G a a p → p.length = 1
```

`SingleReachingDef G D P` says that at the top of every non-entry block without a φ at most one definition point of `D ∪ P` reaches; it holds vacuously at blocks reached by no definition. `SingleReachingDefAll` drops the entry exemption.

Language, SSA form and the naive out-of-SSA translation (verbatim):

```lean
-- lean/ToySsa/Lang.lean:32-35
def parCopy {V : Type} [DecidableEq V] (ms : List (V × V)) (σ : V → Nat) : V → Nat :=
  fun y => match ms.find? (fun m => decide (m.1 = y)) with
    | some m => σ m.2
    | none => σ y
-- lean/ToySsa/Lang.lean:48-49
def execBody {V : Type} [DecidableEq V] (is : List (Instr V)) (σ : V → Nat) : V → Nat :=
  is.foldl (fun σ i => i.exec σ) σ
-- lean/ToySsa/Lang.lean:72-75
structure SsaProg (V : Type) (n : Nat) where
  cfg : Cfg n
  phis : Fin n → List (V × (Fin n → V))
  body : Fin n → List (Instr V)
-- lean/ToySsa/Lang.lean:78-79
def SsaProg.phiMoves {V : Type} (P : SsaProg V n) (p b : Fin n) : List (V × V) :=
  (P.phis b).map (fun φ => (φ.1, φ.2 p))
-- lean/ToySsa/Lang.lean:82-84
def SsaProg.enter {V : Type} [DecidableEq V] (P : SsaProg V n) (p b : Fin n) (σ : V → Nat) :
    V → Nat :=
  parCopy (P.phiMoves p b) σ
-- lean/ToySsa/Lang.lean:100-104
def SsaProg.atTop {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (path : List (Fin n)) : V → Nat :=
  match path.reverse with
  | b :: p :: _ => P.enter p b (P.run σ path.dropLast)
  | _ => σ
-- lean/ToySsa/Lang.lean:116-118
def copyInstrs {V : Type} : CopyMode → List (V × V) → List (Instr V)
  | .parallel, ms => [.pcopy ms]
  | .sequential, ms => ms.map (fun m => .assign m.1 (.var m.2))
-- lean/ToySsa/Lang.lean:121
def succs (G : Cfg n) (p : Fin n) : List (Fin n) := (List.finRange n).filter (fun b => G.edge p b)
-- lean/ToySsa/Lang.lean:126-128
def naiveOutOfSsa {V : Type} (mode : CopyMode) (P : SsaProg V n) : Prog V n where
  cfg := P.cfg
  body p := P.body p ++ (succs P.cfg p).flatMap (fun b => copyInstrs mode (P.phiMoves p b))
-- lean/ToySsa/Lang.lean:133-134
def NoCriticalEdges (G : Cfg n) : Prop :=
  ∀ a b, G.edge a b = true → (∀ c, G.edge a c = true → c = b) ∨ (∀ c, G.edge c b = true → c = a)
-- lean/ToySsa/Lang.lean:137-138
def PhisOnlyAtJoins {V : Type} (P : SsaProg V n) : Prop :=
  ∀ b, 0 < (P.phis b).length → ∃ a c, a ≠ c ∧ P.cfg.edge a b = true ∧ P.cfg.edge c b = true
-- lean/ToySsa/Lang.lean:141-142
def PhiPredsSingleSucc {V : Type} (P : SsaProg V n) : Prop :=
  ∀ p b, 0 < (P.phis b).length → P.cfg.edge p b = true → ∀ c, P.cfg.edge p c = true → c = b
-- lean/ToySsa/Lang.lean:247-249
def SeqSafe {V : Type} : List (V × V) → Prop
  | [] => True
  | m :: rest => m.1 ∉ rest.map Prod.fst ∧ m.1 ∉ rest.map Prod.snd ∧ SeqSafe rest
-- lean/ToySsa/Lang.lean:226-227
def SsaProg.defsAt {V : Type} (P : SsaProg V n) (b : Fin n) : List V :=
  (P.phis b).map Prod.fst ++ (P.body b).flatMap Instr.dests
-- lean/ToySsa/Lang.lean:232-233
def SsaProg.SingleAssignment {V : Type} (P : SsaProg V n) : Prop :=
  (∀ b, (P.defsAt b).Nodup) ∧ ∀ b b' v, v ∈ P.defsAt b → v ∈ P.defsAt b' → b = b'
```

Graph constructor, expressions, instructions, programs, runs, copy emission, and the renaming helpers (verbatim):

```lean
-- lean/ToySsa/Cfg.lean:18-20
def Cfg.ofEdges (n : Nat) (es : List (Nat × Nat)) (entry : Fin n) : Cfg n where
  edge a b := es.contains (a.val, b.val)
  entry := entry
-- lean/ToySsa/Lang.lean:13-17
inductive Exp (V : Type) where
  | lit (k : Nat)
  | var (x : V)
  | add (a b : Exp V)
  deriving Repr
-- lean/ToySsa/Lang.lean:20-23
def Exp.eval {V : Type} (σ : V → Nat) : Exp V → Nat
  | .lit k => k
  | .var x => σ x
  | .add a b => a.eval σ + b.eval σ
-- lean/ToySsa/Lang.lean:26-27
def upd {V : Type} [DecidableEq V] (σ : V → Nat) (x : V) (v : Nat) : V → Nat :=
  fun y => if y = x then v else σ y
-- lean/ToySsa/Lang.lean:38-40
inductive Instr (V : Type) where
  | assign (x : V) (e : Exp V)
  | pcopy (moves : List (V × V))
-- lean/ToySsa/Lang.lean:43-45
def Instr.exec {V : Type} [DecidableEq V] : Instr V → (V → Nat) → (V → Nat)
  | .assign x e, σ => upd σ x (e.eval σ)
  | .pcopy ms, σ => parCopy ms σ
-- lean/ToySsa/Lang.lean:53-55
structure Prog (V : Type) (n : Nat) where
  cfg : Cfg n
  body : Fin n → List (Instr V)
-- lean/ToySsa/Lang.lean:58-60
def Prog.run {V : Type} [DecidableEq V] (P : Prog V n) : (V → Nat) → List (Fin n) → (V → Nat)
  | σ, [] => σ
  | σ, b :: bs => P.run (execBody (P.body b) σ) bs
-- lean/ToySsa/Lang.lean:63-65
def Prog.atTop {V : Type} [DecidableEq V] (P : Prog V n) (σ : V → Nat) (path : List (Fin n)) :
    V → Nat :=
  P.run σ path.dropLast
-- lean/ToySsa/Lang.lean:87-90
def SsaProg.runFrom {V : Type} [DecidableEq V] (P : SsaProg V n) :
    Fin n → (V → Nat) → List (Fin n) → (V → Nat)
  | _, σ, [] => σ
  | cur, σ, b :: bs => P.runFrom b (execBody (P.body b) (P.enter cur b σ)) bs
-- lean/ToySsa/Lang.lean:94-97
def SsaProg.run {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat) :
    List (Fin n) → (V → Nat)
  | [] => σ
  | b :: bs => P.runFrom b (execBody (P.body b) σ) bs
-- lean/ToySsa/Lang.lean:109-113
inductive CopyMode where
  /-- one parallel copy instruction -/
  | parallel
  /-- one assignment per φ, in φ order -/
  | sequential
-- lean/ToySsa/Lang.lean:148-150
structure Src (n : Nat) where
  cfg : Cfg n
  body : Fin n → List (Nat × Exp Nat)
-- lean/ToySsa/Lang.lean:153-155
def Src.toProg (S : Src n) : Prog Nat n where
  cfg := S.cfg
  body b := (S.body b).map (fun xe => .assign xe.1 xe.2)
-- lean/ToySsa/Lang.lean:163
abbrev SName (n : Nat) := Nat × Fin n × Nat
-- lean/ToySsa/Lang.lean:166-168
def lastDefAux (x : Nat) : Nat → List (Nat × Exp Nat) → Option Nat → Option Nat
  | _, [], acc => acc
  | i, xe :: rest, acc => lastDefAux x (i + 1) rest (if xe.1 = x then some i else acc)
-- lean/ToySsa/Lang.lean:171
def lastDef (x : Nat) (body : List (Nat × Exp Nat)) : Option Nat := lastDefAux x 0 body none
-- lean/ToySsa/Lang.lean:194-197
def renameExp {W : Type} (env : Nat → W) : Exp Nat → Exp W
  | .lit k => .lit k
  | .var x => .var (env x)
  | .add a b => .add (renameExp env a) (renameExp env b)
-- lean/ToySsa/Lang.lean:201-205
def renameBody (b : Fin n) : (Nat → SName n) → Nat → List (Nat × Exp Nat) → List (Instr (SName n))
  | _, _, [] => []
  | env, i, xe :: rest =>
      .assign (xe.1, b, i + 1) (renameExp env xe.2) ::
        renameBody b (fun y => if y = xe.1 then (xe.1, b, i + 1) else env y) (i + 1) rest
-- lean/ToySsa/Lang.lean:220-222
def Instr.dests {V : Type} : Instr V → List V
  | .assign x _ => [x]
  | .pcopy ms => ms.map Prod.fst
-- lean/ToySsa/Lang.lean:239-240
def outCopies {V : Type} (mode : CopyMode) (P : SsaProg V n) (p : Fin n) : List (Instr V) :=
  (succs P.cfg p).flatMap (fun b => copyInstrs mode (P.phiMoves p b))
```
SSA construction (verbatim):

```lean
-- lean/ToySsa/Lang.lean:158-159
def Src.defPts (S : Src n) (x : Nat) (b : Fin n) : Prop :=
  b = S.cfg.entry ∨ x ∈ (S.body b).map Prod.fst
-- lean/ToySsa/Lang.lean:174-177
def outName (S : Src n) (x : Nat) (d : Fin n) : SName n :=
  match lastDef x (S.body d) with
  | some i => (x, d, i + 1)
  | none => (x, d, 0)
-- lean/ToySsa/Lang.lean:182-184
def topName (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (x : Nat)
    (b : Fin n) : SName n :=
  if b = S.cfg.entry ∨ phi x b = true then (x, b, 0) else outName S x (idom x b)
-- lean/ToySsa/Lang.lean:187-191
def liveOutName (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (x : Nat)
    (p : Fin n) : SName n :=
  match lastDef x (S.body p) with
  | some i => (x, p, i + 1)
  | none => topName S phi idom x p
-- lean/ToySsa/Lang.lean:210-215
def ssaConstruct (S : Src n) (vars : List Nat) (phi : Nat → Fin n → Bool)
    (idom : Nat → Fin n → Fin n) : SsaProg (SName n) n where
  cfg := S.cfg
  phis b := if b = S.cfg.entry then [] else
    (vars.filter (fun x => phi x b)).map (fun x => ((x, b, 0), fun p => liveOutName S phi idom x p))
  body b := renameBody b (fun x => topName S phi idom x b) 0 (S.body b)
```

`Prog.run` and `SsaProg.run` execute the bodies along a list of blocks (the SSA program first executes the φs of each later block for the edge just taken); `Prog.atTop` is the store on entry to the last block, and `SsaProg.atTop` the store on entry to the last block after its φs. `renameBody` renames one block body, giving instruction `i` of block `b` the fresh name `(x, b, i + 1)`.

Concrete CFGs used by the cards (verbatim):

```lean
-- lean/ToySsa/Examples.lean:9
def diamond : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (0, 2), (1, 3), (2, 3)] 0
-- lean/ToySsa/Examples.lean:12
def chain3 : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 2)] 0
-- lean/ToySsa/Examples.lean:15
def loop4 : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 2), (2, 1), (1, 3)] 0
-- lean/ToySsa/Examples.lean:18
def ladder5 : Cfg 5 := Cfg.ofEdges 5 [(0, 1), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)] 0
-- lean/ToySsa/Examples.lean:21
def selfLoop2 : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 1)] 0
-- lean/ToySsa/Examples.lean:46
def isolated2 : Cfg 2 := Cfg.ofEdges 2 [] 0
-- lean/ToySsa/Placement.lean:412
def unreachJoin4 : Cfg 4 := Cfg.ofEdges 4 [(1, 3), (2, 3)] 0
-- lean/ToySsa/Placement.lean:438
def entryLoop1 : Cfg 1 := Cfg.ofEdges 1 [(0, 0)] 0
-- lean/ToySsa/Placement.lean:470
def unreachLoop2 : Cfg 2 := Cfg.ofEdges 2 [(1, 1)] 0
-- lean/ToySsa/Placement.lean:943
def entryCycle2 : Cfg 2 := Cfg.ofEdges 2 [(0, 0), (0, 1), (1, 0)] 0
-- lean/ToySsa/OutOfSsa.lean:243
def swapCfg : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 2), (2, 1), (1, 3)] 0
-- lean/ToySsa/OutOfSsa.lean:441
def lostCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 1), (1, 2)] 0
-- lean/ToySsa/OutOfSsa.lean:487
def lostSplitCfg : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 3), (3, 1), (1, 2)] 0
-- lean/ToySsa/OutOfSsa.lean:658
def lostNoExitCfg : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 1)] 0
```

Concrete programs of the out-of-SSA cards (prose summary; the verbatim Lean definitions follow it):

```text
swapSsaAB  : variables a1 = 0, b1 = 1, a2 = 2, b2 = 3 on swapCfg (latch block 2 splits the back edge);
             block 0: a1 := 1; b1 := 2; header block 1: a2 = phi(a1 from 0, b2 from 2),
             b2 = phi(b1 from 0, a2 from 2), in this order.  swapSsaBA: the same phis in the other order.
swapTempProg: block 0: a1 := 1; b1 := 2; a2 := a1; b2 := b1;  block 2: t := a2; a2 := b2; b2 := t (t = 4).
lostSsa    : variables x1 = 0, x2 = 1, x3 = 2 on lostCfg; block 0: x1 := 1; block 1: x2 = phi(x1 from 0,
             x3 from 1), then x3 := x2 + 1; the exit block 2 reads x2.
lostSource : the source program on lostCfg, with its own numbering x = 0, y = 1 (unlike lostSsa);
             block 0: x := 1; block 1: y := x; x := x + 1; the exit block 2 reads y.
lostSplitSsa: lostSsa on lostSplitCfg, where the new block 3 splits the critical edge 1 -> 1.
lostNoExitSsa: lostSsa on lostNoExitCfg (no exit block; the return of x2 is not an edge).
chainPhiAB / chainPhiBA: header phis a2 = phi(a1, c1), b2 = phi(b1, a2) on swapCfg, in order [a2, b2]
             resp. [b2, a2]; variables a1 = 0, b1 = 1, c1 = 2, a2 = 3, b2 = 4, and block 0 also sets c1 := 5.
dupPhiSsa: two phis with the same destination on a 3-node chain.
swapWalk = [0, 1, 2, 1]; lostWalk = [0, 1, 1, 2]; lostLoopWalk k = [0, 1] ++ k copies of 1 ++ [2]
(k + 1 runs of block 1); lostSplitWalk k = [0, 1] ++ k copies of [3, 1] ++ [2].
```

```lean
-- lean/ToySsa/OutOfSsa.lean:248-252
def swapSsaAB : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(2, fun p => if p = 0 then 0 else 3), (3, fun p => if p = 0 then 1 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2)] else []
-- lean/ToySsa/OutOfSsa.lean:255-259
def swapSsaBA : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(3, fun p => if p = 0 then 1 else 2), (2, fun p => if p = 0 then 0 else 3)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2)] else []
-- lean/ToySsa/OutOfSsa.lean:263-268
def swapTempProg : Prog Nat 4 where
  cfg := swapCfg
  body b :=
    if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.var 0), .assign 3 (.var 1)]
    else if b = 2 then [.assign 4 (.var 2), .assign 2 (.var 3), .assign 3 (.var 4)]
    else []
-- lean/ToySsa/OutOfSsa.lean:271
def swapWalk : List (Fin 4) := [0, 1, 2, 1]
-- lean/ToySsa/OutOfSsa.lean:367
def dupCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 2)] 0
-- lean/ToySsa/OutOfSsa.lean:372-375
def dupPhiSsa : SsaProg Nat 3 where
  cfg := dupCfg
  phis b := if b = 1 then [(2, fun _ => 0), (2, fun _ => 1)] else []
  body b := if b = 0 then [.assign 0 (.lit 10), .assign 1 (.lit 20)] else []
-- lean/ToySsa/OutOfSsa.lean:396-400
def chainPhiAB : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(3, fun p => if p = 0 then 0 else 2), (4, fun p => if p = 0 then 1 else 3)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.lit 5)] else []
-- lean/ToySsa/OutOfSsa.lean:403-407
def chainPhiBA : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(4, fun p => if p = 0 then 1 else 3), (3, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.lit 5)] else []
-- lean/ToySsa/OutOfSsa.lean:445-449
def lostSsa : SsaProg Nat 3 where
  cfg := lostCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 2 (.add (.var 1) (.lit 1))] else []
-- lean/ToySsa/OutOfSsa.lean:453-456
def lostSource : Prog Nat 3 where
  cfg := lostCfg
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 1 (.var 0), .assign 0 (.add (.var 0) (.lit 1))] else []
-- lean/ToySsa/OutOfSsa.lean:459
def lostWalk : List (Fin 3) := [0, 1, 1, 2]
-- lean/ToySsa/OutOfSsa.lean:490-494
def lostSplitSsa : SsaProg Nat 4 where
  cfg := lostSplitCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 2 (.add (.var 1) (.lit 1))] else []
-- lean/ToySsa/OutOfSsa.lean:497
def lostLoopWalk (k : Nat) : List (Fin 3) := [0, 1] ++ List.replicate k 1 ++ [2]
-- lean/ToySsa/OutOfSsa.lean:500
def lostSplitWalk (k : Nat) : List (Fin 4) := [0, 1] ++ (List.replicate k [3, 1]).flatten ++ [2]
-- lean/ToySsa/OutOfSsa.lean:660-663
def lostNoExitSsa : SsaProg Nat 2 where
  cfg := lostNoExitCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)] else [.assign 2 (.add (.var 1) (.lit 1))]
-- lean/ToySsa/OutOfSsa.lean:692
def branchPhiCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (0, 2)] 0
-- lean/ToySsa/OutOfSsa.lean:694-697
def branchPhiSsa : SsaProg Nat 3 where
  cfg := branchPhiCfg
  phis b := if b = 1 then [(1, fun _ => 0)] else []
  body b := if b = 0 then [.assign 0 (.lit 5)] else []
```

Intended positive and negative examples of the core definitions are proved in `lean/ToySsa/Examples.lean` (the graph notions), `lean/ToySsa/Placement.lean` (`SingleReachingDefAll`), `lean/ToySsa/Construct.lean` (`Acyclic`, `EntryNoReachablePreds`, `SsaProg.SingleAssignment`) and `lean/ToySsa/OutOfSsa.lean` (the out-of-SSA predicates). Where an example is one conjunct of a larger theorem, the conjunct is named. Every theorem in the table is quoted under Auxiliary declarations cited by name.

| Definition | Positive example | Negative example |
| :--- | :--- | :--- |
| `Walk` | `walk_example` | `not_walk_example` |
| `AllReachable` | `allReachable_diamond` | `not_allReachable_isolated2` |
| `EntryNoPreds` | `entryNoPreds_diamond` | `not_entryNoPreds_backToEntry2` |
| `Dom` | `dom_example`, `dom_chain_example` | `not_dom_example` |
| `SDom` | `sdom_example` | `not_sdom_self_example` |
| `DF` | `df_example`, `df_loop_example` | `not_df_example`, `not_df_ladder_example` |
| `IDF` | `idf_iterates_example` | `not_idf_example` |
| `InJoin / Converge` | `inJoin_example`, `inJoin_cycle_example` | `not_converge_example`, `not_inJoin_example` |
| `ReachesTop` | `reachesTop_example` | `not_reachesTop_example` |
| `SingleReachingDef` | `srd_example` | `not_srd_example` |
| `NearestSDomDef` | `nearestSDomDef_example` | `not_nearestSDomDef_example` |
| `SingleReachingDefAll` (in `Placement.lean`) | `srdAll_hyps_nonvacuous` | `srd_entry_exemption_example` (last conjunct) |
| `Acyclic` (in `Construct.lean`) | `acyclic_diamond` | `not_acyclic_loop4` |
| `EntryNoReachablePreds` (in `Construct.lean`) | `entryNoReachablePreds_diamond` | `ssaConstruct_needs_entryNoReachablePreds` (first conjunct) |
| `SsaProg.SingleAssignment` (in `Construct.lean`) | `ssaConstruct_singleAssignment_nonvacuous` (second conjunct) | `ssaConstruct_singleAssignment_needs_nodup` (third conjunct) |
| `NoCriticalEdges` (in `OutOfSsa.lean`) | `noCriticalEdges_swapCfg`, `noCriticalEdges_lostSplitCfg` | `not_noCriticalEdges_lostCfg` |
| `PhisOnlyAtJoins` (in `OutOfSsa.lean`) | `phisOnlyAtJoins_swapSsaAB` | `naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins` (second conjunct) |
| `PhiPredsSingleSucc` (in `OutOfSsa.lean`) | `phiPredsSingleSucc_swapSsaAB` | `not_phiPredsSingleSucc_lostSsa` |
| `SeqSafe` (in `OutOfSsa.lean`) | `execBody_sequential_hyps_nonvacuous` | `execBody_sequential_needs_seqSafe` (first conjunct) |

### Results

Each card gives tier, kind and depth, the plain claim, the verbatim Lean statement, a hypothesis ledger (`tight` means: there is a counterexample, satisfying all the other hypotheses, in which the conclusion fails; the witness class is recorded), the non-vacuity witness, prior art, and the design question. Non-claims for every card are under Boundaries.

### 1. `join-subset-iterated-df-of-all-reachable`

**Tier** T0 · **Kind** theorem · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry, for every set S of nodes, every join node of S (a node at which two nonnull walks starting at two distinct nodes of S converge in Cytron et al.'s sense) lies in the iterated dominance frontier DF+(S).

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:868-869
theorem join_subset_iteratedDF_of_allReachable (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) : ∀ z, InJoin G S z → IDF G S z := …
```

**Definitions used:** `AllReachable`, `InJoin`, `Converge`, `IDF`, `DF`, `Dom`, `SDom` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | Dominance is vacuous at unreachable nodes, which removes them from dominance frontiers. | tight | `join_subset_iteratedDF_needs_allReachable`; witness class: a 4-node CFG whose join node and both start nodes are unreachable |

**Non-vacuity witness.** Diamond 0->1->3, 0->2->3 with S = {0, 1}: all nodes reachable and 3 is a join node of S. Lean: `join_iteratedDF_full_nonvacuous`.

**Tier justification.** Cytron et al. Lemma 6, restated over semantic dominance and index-based convergence.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 2 defines convergence of nonnull paths by (1) X0 != Y0, (2) XJ = Z = YK, (3) Xj = Yk implies j = J or k = K, and assumes every node is on a path from Entry; Lemma 6: for any set S of CFG nodes, J(S) is contained in DF+(S); Lemma 7: if Entry is in S then DF(S) is contained in J(S); Theorem 2: J+(S) = DF+(S), which 'depends on the fact that Entry is in S'.
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `join-subset-iterated-df-of-all-reachable`.

### 2. `iterated-df-subset-join-of-entry-mem`

**Tier** T0 · **Kind** theorem · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry and no edge enters the entry, for every set S of nodes that contains the entry, every node of the iterated dominance frontier DF+(S) is a join node of S.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:370-372
theorem iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) (hnp : EntryNoPreds G) (hS : S G.entry) :
    ∀ z, IDF G S z → InJoin G S z := …
```

Unfolded (`InJoin` expanded to `Converge`), in the context of `G S hreach hnp hS`:

```lean
∀ z, IDF G S z → ∃ x y p q, S x ∧ S y ∧ Converge G x y z p q
```

**Definitions used:** `AllReachable`, `EntryNoPreds`, `IDF`, `DF`, `InJoin`, `Converge` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | Vacuous dominance at unreachable nodes puts single-predecessor nodes into DF. | tight | `iteratedDF_subset_join_needs_allReachable`; witness class: a 2-node CFG with an unreachable self-loop |
| `hnp : EntryNoPreds G` | With an edge into the entry, the entry is in its own dominance frontier but is not a join node. | tight | `iteratedDF_subset_join_needs_entryNoPreds`; witness class: the 1-node CFG with a self-loop on the entry |
| `hS : S G.entry` | A single definition inside a loop has the loop header in DF+ but no second definition to join with. | tight | `iteratedDF_subset_join_needs_entry_mem`; witness class: the 2-node CFG 0 -> 1 with a self-loop on 1 |

**Non-vacuity witness.** Diamond with S = {0, 1}: 3 is in DF+(S). Lean: `join_iteratedDF_full_nonvacuous`.

**Proof structure.** For `y ∈ DF(x)`, `df_preWalks_of_allReachable_of_entryNoPreds` builds two converging walks, one from `x` and one from the entry: the walk from `x` is the suffix, after the last visit to `x`, of a walk from the entry to a predecessor of `y` dominated by `x` (every node on it is dominated by `x`); the walk from the entry avoids `x` (when `x` does not dominate `y`) or is a walk to the first visit of `x = y`, and therefore avoids every node dominated by `x`. `EntryNoPreds` gives `x ≠ entry`. Induction on `DF⁺` then uses join closure (`inJoinPre_of_insert_join`) at each step.

**Tier justification.** Cytron et al. Lemma 7 iterated as in their Theorem 2, with the no-edge-into-entry condition made explicit.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 2 defines convergence of nonnull paths by (1) X0 != Y0, (2) XJ = Z = YK, (3) Xj = Yk implies j = J or k = K, and assumes every node is on a path from Entry; Lemma 6: for any set S of CFG nodes, J(S) is contained in DF+(S); Lemma 7: if Entry is in S then DF(S) is contained in J(S); Theorem 2: J+(S) = DF+(S), which 'depends on the fact that Entry is in S'.
- Bilardi, Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573. Definition 1.1 defines J(S) only for sets S containing START (paths u ->+ v and w ->+ v from distinct u, w in S intersecting only at v) and notes J(S u J(S)) = J(S), crediting Weiss (1992), so that 'the phi-assignments in the nodes J(S) are sufficient'; Theorem 2.2 (for {START} within S) expresses J(S) through the merge relation.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `iterated-df-subset-join-of-entry-mem`.

### 3. `join-eq-iterated-df-of-entry-mem`

**Tier** T0 · **Kind** characterization · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry and no edge enters the entry, for every set S of nodes that contains the entry, the join set J(S) equals the iterated dominance frontier DF+(S).

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:883-885
theorem join_eq_iteratedDF_of_allReachable_of_entryNoPreds_of_entry_mem (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) (hnp : EntryNoPreds G) (hS : S G.entry) :
    ∀ z, InJoin G S z ↔ IDF G S z := …
```

**Definitions used:** `AllReachable`, `EntryNoPreds`, `InJoin`, `IDF` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | As for both inclusions. | tight | `iteratedDF_subset_join_needs_allReachable`; witness class: a 2-node CFG with an unreachable self-loop (S contains the entry, no edge enters the entry) |
| `hnp : EntryNoPreds G` | As for DF+(S) within J(S). | tight | `iteratedDF_subset_join_needs_entryNoPreds`; witness class: the 1-node CFG with a self-loop on the entry |
| `hS : S G.entry` | As for DF+(S) within J(S). | tight | `iteratedDF_subset_join_needs_entry_mem`; witness class: the 2-node CFG 0 -> 1 with a self-loop on 1 |

**Non-vacuity witness.** Diamond with S = {0, 1}: J(S) = DF+(S) = {3}. Lean: `join_iteratedDF_full_nonvacuous`.

**Tier justification.** Cytron et al. Theorem 2 (J+(S) = DF+(S) when Entry is in S) combined with J(S u J(S)) = J(S); derived here from the two inclusions.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 2 defines convergence of nonnull paths by (1) X0 != Y0, (2) XJ = Z = YK, (3) Xj = Yk implies j = J or k = K, and assumes every node is on a path from Entry; Lemma 6: for any set S of CFG nodes, J(S) is contained in DF+(S); Lemma 7: if Entry is in S then DF(S) is contained in J(S); Theorem 2: J+(S) = DF+(S), which 'depends on the fact that Entry is in S'.
- Bilardi, Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573. Definition 1.1 defines J(S) only for sets S containing START (paths u ->+ v and w ->+ v from distinct u, w in S intersecting only at v) and notes J(S u J(S)) = J(S), crediting Weiss (1992), so that 'the phi-assignments in the nodes J(S) are sufficient'; Theorem 2.2 (for {START} within S) expresses J(S) through the merge relation.
- Rastello, Bouchez Tichadou (eds.). SSA-based Compiler Design. Springer, 2022. DOI 10.1007/978-3-030-80515-9. Textbook treatment of phi placement, renaming, and SSA destruction.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Basis: derived (modeling bridge).** LLVM's mem2reg places φs at a liveness-pruned iterated dominance frontier of the defining blocks (Applicability, bridge (a)); this theorem characterizes the unpruned placement with the entry counted as a definition point, so it describes a superset of mem2reg's φ blocks under the CFG conditions stated. It neither establishes nor refutes the correctness of mem2reg.

**Non-claims:** see Boundaries, card `join-eq-iterated-df-of-entry-mem`.

### 4. `join-union-join-subset-join`

**Tier** T2 · **Kind** theorem · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** In every finite CFG and for every set S of nodes, J(S u J(S)) is contained in J(S): a node at which walks from two distinct nodes of S or of J(S) converge is already a join node of S.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:387-388
theorem join_union_join_subset_join (G : Cfg n) (S : Fin n → Prop) :
    ∀ z, InJoin G (fun x => S x ∨ InJoin G S x) z → InJoin G S z := …
```

Unfolded (`InJoin` expanded to `Converge` on both sides), in the context of `G S`:

```lean
∀ z, (∃ x y p q, (S x ∨ InJoin G S x) ∧ (S y ∨ InJoin G S y) ∧ Converge G x y z p q) →
  ∃ x y p q, S x ∧ S y ∧ Converge G x y z p q
```

**Definitions used:** `InJoin`, `Converge`, `Walk` (see Definitions).

**Hypothesis ledger.** No hypotheses beyond the universally quantified CFG `G` and set `S`.

**Non-vacuity witness.** ladder5 with S = {0, 2}: 3 is in J(S) but not in S, and 4 is in J(S u J(S)) via the start nodes 0 (in S) and 3 (in J(S)). Lean: `join_union_join_genuine_nonvacuous`.

**Proof structure.** Convergence is first restated with walks presented by their nodes before the final one: `inJoin_iff_preWalks` proves `InJoin G S z ↔ InJoinPre G S z`, where `InJoinPre` asks for two such node lists from distinct start nodes of `S` that are disjoint. The core step `inJoinPre_of_join_point` shows: if `w ∈ J(S)` (disjoint lists `A`, `B` from `x ≠ y ∈ S`) and disjoint lists `C` from `a ∈ S` and `R` from `w` lead to `z`, then `z ∈ J(S)`. It is proved by strong induction on the length of `R`: if `R` meets `A ∪ B`, its first meeting point is again in `J(S)` and the remaining suffix is shorter. Otherwise, if `C` avoids `A ∪ B`, `z` is reached from `a` (along `C`) and from `x` (along `A`, then `R`); if the last node of `C` in `A ∪ B` is a node `t` of `A`, `z` is reached from `x` (along `A` up to `t`, then along `C`) and from `y` (along `B`, then `R`), and symmetrically when `t` lies in `B`. Two applications handle the case where both start nodes lie in `J(S)`.

**Tier justification.** Bilardi and Pingali define J(S) only for sets S containing START and state J(S u J(S)) = J(S) there (crediting Weiss 1992); stated here for every finite CFG and every S, with no reachability, entry, or START-membership hypothesis.

**Prior art.**

- Bilardi, Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573. Definition 1.1 defines J(S) only for sets S containing START (paths u ->+ v and w ->+ v from distinct u, w in S intersecting only at v) and notes J(S u J(S)) = J(S), crediting Weiss (1992), so that 'the phi-assignments in the nodes J(S) are sufficient'; Theorem 2.2 (for {START} within S) expresses J(S) through the merge relation.
- Weiss. "The transitive closure of control dependence: the iterated join." ACM LOPLAS 1(2):178-190, 1992. DOI 10.1145/151333.151337. Credited by Bilardi and Pingali (2003) with J(S u J(S)) = J(S); no statement about the hypotheses under which Weiss proves it is made here.
- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `join-union-join-subset-join`.

### 5. `single-reaching-def-of-join-closed`

**Tier** T1 · **Kind** theorem · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** In every finite CFG, for definition blocks D and a phi placement P with J(D u P) contained in P (join closure), at the top of every block without a phi, the entry included, at most one definition point of D u P reaches (singleReachingDefAll_of_joinClosed); in particular this holds at every non-entry block without a phi (singleReachingDef_of_joinClosed).

**Lean statements** (verbatim source, proofs elided; this card bundles 2 theorems: `singleReachingDef_of_joinClosed`, `singleReachingDefAll_of_joinClosed`):

```lean
-- lean/ToySsa/Placement.lean:722-723
theorem singleReachingDef_of_joinClosed (G : Cfg n) (D P : Fin n → Prop)
    (hclosed : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z) : SingleReachingDef G D P := …
-- lean/ToySsa/Placement.lean:670-671
theorem singleReachingDefAll_of_joinClosed (G : Cfg n) (D P : Fin n → Prop)
    (hclosed : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z) : SingleReachingDefAll G D P := …
```

**Definitions used:** `InJoin`, `SingleReachingDef`, `SingleReachingDefAll`, `ReachesTop`, `Clear` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hclosed : forall z, InJoin G (fun w => D w \/ P w) z -> P z (premise of both bundled theorems)` | Without join closure two definitions converge at a block without a phi. | tight | `singleReachingDef_needs_joinClosed`, `singleReachingDefAll_needs_joinClosed`; witness class: the diamond with D = {0, 1} and P empty (both conclusions fail) |

**Non-vacuity witness.** Diamond with D = {0, 1}, P = {3}: J(D u P) = {3}. Lean: `joinClosed_diamond_example`.

**Tier justification.** The rationale behind Cytron et al.'s iterated join and Bilardi-Pingali's sufficiency of J(S) (placements closed under joins) made precise for per-block reaching definitions.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.
- Bilardi, Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573. Definition 1.1 defines J(S) only for sets S containing START (paths u ->+ v and w ->+ v from distinct u, w in S intersecting only at v) and notes J(S u J(S)) = J(S), crediting Weiss (1992), so that 'the phi-assignments in the nodes J(S) are sufficient'; Theorem 2.2 (for {START} within S) expresses J(S) through the merge relation.
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `single-reaching-def-of-join-closed`.

### 6. `join-closed-of-single-reaching-def`

**Tier** T1 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG with no edge into the entry, if at the top of every non-entry block without a phi at most one definition point of D u P reaches, then J(D u P) is contained in P (joinClosed_of_entryNoPreds_of_singleReachingDef). In every finite CFG, if at the top of every block without a phi, the entry included, at most one definition point of D u P reaches (SingleReachingDefAll), then J(D u P) is contained in P (joinClosed_of_singleReachingDefAll).

**Lean statements** (verbatim source, proofs elided; this card bundles 2 theorems: `joinClosed_of_entryNoPreds_of_singleReachingDef`, `joinClosed_of_singleReachingDefAll`):

```lean
-- lean/ToySsa/Placement.lean:728-730
theorem joinClosed_of_entryNoPreds_of_singleReachingDef (G : Cfg n) (D P : Fin n → Prop)
    (hnp : EntryNoPreds G) (h : SingleReachingDef G D P) :
    ∀ z, InJoin G (fun w => D w ∨ P w) z → P z := …
-- lean/ToySsa/Placement.lean:564-565
theorem joinClosed_of_singleReachingDefAll (G : Cfg n) (D P : Fin n → Prop)
    (h : SingleReachingDefAll G D P) : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z := …
```

**Definitions used:** `EntryNoPreds`, `SingleReachingDef`, `SingleReachingDefAll`, `InJoin` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hnp : EntryNoPreds G (for SingleReachingDef; dropped in joinClosed_of_singleReachingDefAll)` | SingleReachingDef exempts the entry; with an edge into the entry, the entry can be a join node of D u P that carries no phi. | tight | `srd_join_needs_entryNoPreds`; witness class: a 2-node CFG with a self-loop on the entry and an edge back into it |
| `h : SingleReachingDef G D P (in joinClosed_of_singleReachingDefAll: h : SingleReachingDefAll G D P)` | The premise of the implication. | tight | `joinClosed_needs_singleReachingDef`, `joinClosed_needs_singleReachingDefAll`; witness class: the diamond with D = {0, 1} and P empty (for both bundled theorems) |

**Non-vacuity witness.** Diamond with D = {0, 1}, P = {3}: EntryNoPreds and SingleReachingDef hold, and so does SingleReachingDefAll. Lean: `srd_hyps_nonvacuous`, `srdAll_hyps_nonvacuous`.

**Tier justification.** Converse of the previous result: phis are needed wherever definitions converge (folklore; here under EntryNoPreds, or without it for SingleReachingDefAll), made precise.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `join-closed-of-single-reaching-def`.

### 7. `single-reaching-def-at-join`

**Tier** T2 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In every finite CFG and for every set D of definition blocks, placing phis at J(D) leaves at most one definition point of D u J(D) reaching the top of every non-entry block without a phi.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:735-736
theorem singleReachingDef_at_join (G : Cfg n) (D : Fin n → Prop) :
    SingleReachingDef G D (InJoin G D) := …
```

Unfolded (`SingleReachingDef` expanded), in the context of `G D`:

```lean
∀ b, ¬ InJoin G D b → b ≠ G.entry → ∀ u v,
  ReachesTop G (fun w => D w ∨ InJoin G D w) u b →
  ReachesTop G (fun w => D w ∨ InJoin G D w) v b → u = v
```

**Definitions used:** `SingleReachingDef`, `InJoin` (see Definitions).

**Hypothesis ledger.** No hypotheses beyond the universally quantified CFG `G` and definition-block set `D`.

**Non-vacuity witness.** Diamond with D = {0, 1}: J(D) = {3} is nonempty. Lean: `join_placement_nonempty_example`.

**Tier justification.** Bilardi-Pingali's 'the phi-assignments in the nodes J(S) are sufficient', stated for sets containing START; here for every finite CFG and every D (derived from join closure).

**Prior art.**

- Bilardi, Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573. Definition 1.1 defines J(S) only for sets S containing START (paths u ->+ v and w ->+ v from distinct u, w in S intersecting only at v) and notes J(S u J(S)) = J(S), crediting Weiss (1992), so that 'the phi-assignments in the nodes J(S) are sufficient'; Theorem 2.2 (for {START} within S) expresses J(S) through the merge relation.
- Weiss. "The transitive closure of control dependence: the iterated join." ACM LOPLAS 1(2):178-190, 1992. DOI 10.1145/151333.151337. Credited by Bilardi and Pingali (2003) with J(S u J(S)) = J(S); no statement about the hypotheses under which Weiss proves it is made here.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `single-reaching-def-at-join`.

### 8. `single-reaching-def-at-iterated-df-of-all-reachable`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry, for every set D of definition blocks, placing phis at DF+(D) leaves at most one definition point of D u DF+(D) reaching the top of every non-entry block without a phi.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:892-893
theorem singleReachingDef_at_iteratedDF_of_allReachable (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) : SingleReachingDef G D (IDF G D) := …
```

**Definitions used:** `AllReachable`, `SingleReachingDef`, `IDF` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | DF+ misses joins of unreachable nodes. | tight | `srd_iteratedDF_needs_allReachable`; witness class: a 4-node CFG with an unreachable join |

**Non-vacuity witness.** Diamond (all nodes reachable). Lean: `allReachable_nonvacuous`.

**Tier justification.** Cytron et al.: phi placement at DF+ is correct; derived here from J within DF+ and join closure.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 2 defines convergence of nonnull paths by (1) X0 != Y0, (2) XJ = Z = YK, (3) Xj = Yk implies j = J or k = K, and assumes every node is on a path from Entry; Lemma 6: for any set S of CFG nodes, J(S) is contained in DF+(S); Lemma 7: if Entry is in S then DF(S) is contained in J(S); Theorem 2: J+(S) = DF+(S), which 'depends on the fact that Entry is in S'.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `single-reaching-def-at-iterated-df-of-all-reachable`.

### 9. `exists-reaches-top-of-entry-mem`

**Tier** T1 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In every finite CFG, if the entry is a definition point, then for every placement P some definition point of D u P reaches the top of every reachable non-entry block.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:751-753
theorem exists_reachesTop_of_entry_mem (G : Cfg n) (D P : Fin n → Prop) (hD : D G.entry)
    {b : Fin n} (hb : Reachable G b) (hbe : b ≠ G.entry) :
    ∃ u, ReachesTop G (fun w => D w ∨ P w) u b := …
```

**Definitions used:** `Reachable`, `ReachesTop` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hD : D G.entry` | Without the entry's initial definition nothing need reach. | tight | `exists_reachesTop_needs_entry_mem`; witness class: the 3-node chain with D = P = empty |
| `hb : Reachable G b` | An unreachable block is reached by nothing. | tight | `exists_reachesTop_needs_reachable`; witness class: the 2-node CFG with no edges |
| `hbe : b != G.entry` | With no edge into the entry, nothing reaches the entry's top. | tight | `exists_reachesTop_needs_ne_entry`; witness class: the diamond |

**Non-vacuity witness.** Diamond with D = {0, 1}, b = 3. Lean: `exists_reachesTop_hyps_nonvacuous`.

**Tier justification.** Folklore (the entry carries every variable's initial value) made precise.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `exists-reaches-top-of-entry-mem`.

### 10. `exists-unique-reaches-top-at-iterated-df`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry, for definition blocks D containing the entry, at the top of every non-entry block outside DF+(D) exactly one definition point of D u DF+(D) reaches.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:900-903
theorem existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) (hD : D G.entry) {b : Fin n} (hb : ¬ IDF G D b)
    (hbe : b ≠ G.entry) : ∃ u, ReachesTop G (fun w => D w ∨ IDF G D w) u b ∧
      ∀ v, ReachesTop G (fun w => D w ∨ IDF G D w) v b → v = u := …
```

**Definitions used:** `AllReachable`, `IDF`, `ReachesTop` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | As for the at-most-one part. | tight | `existsUnique_needs_allReachable`; witness class: a 4-node CFG with an unreachable join |
| `hD : D G.entry` | As for existence. | tight | `existsUnique_needs_entry_mem`; witness class: the 3-node chain with D empty |
| `hb : not IDF G D b` | At a phi block two definitions reach its top. | tight | `existsUnique_needs_not_idf`; witness class: the diamond with D = {0, 1}, b = 3 |
| `hbe : b != G.entry` | Nothing reaches the entry's top. | tight | `existsUnique_needs_ne_entry`; witness class: the diamond, b = 0 |

**Non-vacuity witness.** Diamond with D = {0, 1}, b = 1. Lean: `existsUnique_hyps_nonvacuous`.

**Tier justification.** Cytron et al.'s correctness of DF+ placement in its exactly-one form; derived from the two previous results.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `exists-unique-reaches-top-at-iterated-df`.

### 11. `reaches-top-iff-nearest-sdom-def-at-iterated-df`

**Tier** T0 · **Kind** characterization · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG in which every node is reachable from the entry, for every set D of definition blocks, every block b outside DF+(D), and every block u, u reaches the top of b as a definition point of D u DF+(D) if and only if u is the nearest definition point of D u DF+(D) strictly dominating b (both sides require u to lie in D u DF+(D)).

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:766-769
theorem reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) {b : Fin n} (hb : ¬ IDF G D b) (u : Fin n) :
    ReachesTop G (fun w => D w ∨ IDF G D w) u b ↔
      NearestSDomDef G (fun w => D w ∨ IDF G D w) b u := …
```

**Definitions used:** `AllReachable`, `IDF`, `ReachesTop`, `NearestSDomDef` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hreach : AllReachable G` | At an unreachable block dominance is vacuous while nothing reaches. | tight | `reachesTop_iff_needs_allReachable`; witness class: the 2-node CFG with no edges |
| `hb : not IDF G D b` | At a phi block a non-dominating definition reaches. | tight | `reachesTop_at_phi_block_example`; witness class: the diamond with D = {0, 1}, b = 3 |

**Non-vacuity witness.** Diamond with D = {0, 1}, b = 1. Lean: `reachesTop_iff_hyps_nonvacuous`.

**Tier justification.** The correctness argument of dominator-tree renaming in Cytron et al. Section 5 (a use is renamed to the nearest dominating definition), restated over reaching definitions.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 5.2: Lemma 8 (each new variable is the target of exactly one assignment), Lemma 9 (for an edge X -> Y such that Y has no phi for V, TopAfter(V, X) = TopAfter(V, idom(Y))), Lemma 10 (along every control path the renamed variables agree with the original ones).
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `reaches-top-iff-nearest-sdom-def-at-iterated-df`.

### 12. `join-subset-of-single-reaching-def`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** In a finite CFG with no edge into the entry, every phi placement P under which at most one definition point of D u P reaches the top of every non-entry block without a phi contains J(D).

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Placement.lean:911-912
theorem join_subset_of_entryNoPreds_of_singleReachingDef (G : Cfg n) (D P : Fin n → Prop)
    (hnp : EntryNoPreds G) (h : SingleReachingDef G D P) : ∀ z, InJoin G D z → P z := …
```

**Definitions used:** `EntryNoPreds`, `SingleReachingDef`, `InJoin` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hnp : EntryNoPreds G` | The entry can be a join node but is exempt from SingleReachingDef. | tight | `srd_join_needs_entryNoPreds`; witness class: a 2-node CFG with a self-loop on the entry and an edge back into it |
| `h : SingleReachingDef G D P` | The premise of the implication. | tight | `join_subset_needs_singleReachingDef`; witness class: the diamond with D = {0, 1} and P empty |

**Further examples:** `strict_subset_of_join_two_defs_diamond` and `strict_subset_of_join_two_defs_loop` are two instances of a placement P contained in J(D) that misses a join node of D and violates SingleReachingDef: on the diamond with D = {0, 1} (respectively loop4 with D = {0, 2}), the empty placement is contained in J(D), the join node 3 (respectively 1) of D lies outside it, and SingleReachingDef fails (statements under Auxiliary declarations cited by name).

**Non-vacuity witness.** Diamond with D = {0, 1}, P = {3}. Lean: `srd_hyps_nonvacuous`.

**Tier justification.** Minimality of Cytron et al.'s placement (a phi is necessary at every convergence point of two definitions); mechanized for an SSA graph locale in Formal_SSA (lemma convergence_prop').

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.

**Design question.** Where must an SSA builder place phi-functions so that every use has exactly one reaching definition, and is the iterated dominance frontier exactly that set (and under which CFG conditions)?

**Non-claims:** see Boundaries, card `join-subset-of-single-reaching-def`.

### 13. `ssa-construct-preserves-values`

**Tier** T0 · **Kind** theorem · **Depth** substantive · **Basis:** execution (Lean kernel check)

**Plain claim.** For a source program in which no block reachable from the entry has an edge into the entry, whose assigned variables all lie in vars, with a phi placement equal to DF+ of each variable's definition points (entry included) and a renaming source that picks, at every reachable non-entry block without a phi for x, the nearest strictly dominating definition point of x (phis included), and an SSA initial store that holds each variable's initial value in its entry name: on every walk from the entry with last block b, (1) on entry to b every variable's source value equals the value of the SSA name the construction reads for an upward-exposed use at b, and (2) after b's body every variable's source value equals the value of its live-out SSA name at b. The acyclic corollary replaces the entry hypothesis by acyclicity.

**Lean statements** (verbatim source, proofs elided; this card bundles 2 theorems: `ssaConstruct_preserves_values_of_entryNoReachablePreds`, `ssaConstruct_preserves_values_of_acyclic`):

```lean
-- lean/ToySsa/Construct.lean:231-244
theorem ssaConstruct_preserves_values_of_entryNoReachablePreds (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (hnp : EntryNoReachablePreds S.cfg)
    (hvars : ∀ b x e, (x, e) ∈ S.body b → x ∈ vars)
    (hphi_cover : ∀ x b, IDF S.cfg (S.defPts x) b → phi x b = true)
    (hphi_within : ∀ x b, phi x b = true → IDF S.cfg (S.defPts x) b)
    (hidom : ∀ x b, Reachable S.cfg b → b ≠ S.cfg.entry → phi x b = false →
      NearestSDomDef S.cfg (fun d => S.defPts x d ∨ phi x d = true) b (idom x b))
    (σ : Nat → Nat) (σ' : SName n → Nat) (hinit : ∀ x, σ' (x, S.cfg.entry, 0) = σ x)
    {b : Fin n} {path : List (Fin n)} (hw : Walk S.cfg S.cfg.entry b path) (x : Nat) :
    S.toProg.atTop σ path x =
        (ssaConstruct S vars phi idom).atTop σ' path (topName S phi idom x b) ∧
      S.toProg.run σ path x =
        (ssaConstruct S vars phi idom).run σ' path (liveOutName S phi idom x b) := …
-- lean/ToySsa/Construct.lean:367-380
theorem ssaConstruct_preserves_values_of_acyclic (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (hacyc : Acyclic S.cfg)
    (hvars : ∀ b x e, (x, e) ∈ S.body b → x ∈ vars)
    (hphi_cover : ∀ x b, IDF S.cfg (S.defPts x) b → phi x b = true)
    (hphi_within : ∀ x b, phi x b = true → IDF S.cfg (S.defPts x) b)
    (hidom : ∀ x b, Reachable S.cfg b → b ≠ S.cfg.entry → phi x b = false →
      NearestSDomDef S.cfg (fun d => S.defPts x d ∨ phi x d = true) b (idom x b))
    (σ : Nat → Nat) (σ' : SName n → Nat) (hinit : ∀ x, σ' (x, S.cfg.entry, 0) = σ x)
    {b : Fin n} {path : List (Fin n)} (hw : Walk S.cfg S.cfg.entry b path) (x : Nat) :
    S.toProg.atTop σ path x =
        (ssaConstruct S vars phi idom).atTop σ' path (topName S phi idom x b) ∧
      S.toProg.run σ path x =
        (ssaConstruct S vars phi idom).run σ' path (liveOutName S phi idom x b) := …
```

**Definitions used:** `EntryNoReachablePreds`, `Acyclic`, `IDF`, `Src.defPts`, `NearestSDomDef`, `ssaConstruct`, `topName`, `liveOutName`, `Walk` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hnp : EntryNoReachablePreds S.cfg (replaced by hacyc : Acyclic S.cfg in ssaConstruct_preserves_values_of_acyclic)` | The construction never puts phis at the entry; a reachable edge back into the entry needs one. | tight | `ssaConstruct_needs_entryNoReachablePreds`; witness class: the 1-node CFG with a self-loop on the entry |
| `hacyc : Acyclic S.cfg (premise of ssaConstruct_preserves_values_of_acyclic, in place of hnp)` | Acyclicity implies EntryNoReachablePreds (Toy.Ssa.entryNoReachablePreds_of_acyclic); the entry self-loop program, which is not acyclic, satisfies every other hypothesis of the corollary and its conclusion fails. | tight | `ssaConstruct_acyclic_corollary_needs_acyclic`; witness class: the 1-node CFG with a self-loop on the entry |
| `hvars : forall b x e, (x, e) in S.body b -> x in vars` | Phis are emitted only for variables in vars. | tight | `ssaConstruct_needs_hvars`; witness class: the diamond program with vars = [] |
| `hphi_cover : forall x b, IDF S.cfg (S.defPts x) b -> phi x b = true` | A missing phi at a join leaves a stale value. | tight | `ssaConstruct_needs_phi_cover`; witness class: the diamond program with no phis |
| `hphi_within : forall x b, phi x b = true -> IDF S.cfg (S.defPts x) b` | topName reads a phi name for every phi x b, but phis are emitted only for x in vars; a spurious phi for a variable outside vars is read uninitialized. | tight | `ssaConstruct_needs_phi_within`; witness class: the diamond program with a spurious phi for a variable outside vars |
| `hidom : forall x b, Reachable S.cfg b -> b != S.cfg.entry -> phi x b = false -> NearestSDomDef S.cfg (fun d => S.defPts x d \/ phi x d = true) b (idom x b)` | Renaming must read the nearest dominating definition. | tight | `ssaConstruct_needs_nearestSDomDef`; witness class: the 3-node chain program renamed to the entry value |
| `hinit : forall x, sigma' (x, S.cfg.entry, 0) = sigma x` | The SSA entry names hold the initial values. | tight | `ssaConstruct_needs_hinit`; witness class: the diamond program with entry names initialized to 5 |
| `hw : Walk S.cfg S.cfg.entry b path` | Executions start at the entry. | tight | `ssaConstruct_needs_walk_from_entry`; witness class: the diamond program on the null walk at 3 |

**Non-vacuity witness.** Diamond program (x := x + 1 in block 1, phi at 3); a while loop with an unreachable block and renaming through the loop-header phi; an acyclic CFG whose entry has an unreachable predecessor (EntryNoPreds fails). Lean: `ssaConstruct_hyps_nonvacuous`, `ssaConstruct_cyclic_unreach_nonvacuous`, `ssaConstruct_entryPred_nonvacuous`.

**Tier justification.** Semantic correctness of SSA construction is known and mechanized in other formalisms for other construction algorithms (Formal_SSA for Braun et al.'s algorithm; Vellvm for a phi-everywhere-then-prune pass) and argued on paper by Cytron et al. (Section 5.2; the edge step of the proof here is their Lemma 9); restated here for DF+ placement plus declarative dominator-tree renaming.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 5.2: Lemma 8 (each new variable is the target of exactly one assignment), Lemma 9 (for an edge X -> Y such that Y has no phi for V, TopAfter(V, X) = TopAfter(V, idom(Y))), Lemma 10 (along every control path the renamed variables agree with the original ones).
- Ullrich, Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 2016 (Isabelle/HOL session Formal_SSA). Mechanizes Braun et al.'s construction (semantic equivalence; minimal SSA for reducible CFGs). Its theory Minimality defines Cytron's index-based path convergence (pathsConverge), proves it equivalent to disjointness of the paths without their last nodes (lemma pathsConverge'), defines necessaryPhi, and proves that a phi is present at a convergence point of two definitions reaching a use (lemmas convergence_prop, convergence_prop'). It does not formalize dominance frontiers or DF+.
- Buchwald, Lohner, Ullrich. "Verified Construction of Static Single Assignment Form." CC 2016, pp. 67-76. DOI 10.1145/2892208.2892211. Paper accompanying the Formal_SSA development.
- Braun, Buchwald, Hack, Leissa, Mallon, Zwinkau. "Simple and Efficient Construction of Static Single Assignment Form." CC 2013, LNCS 7791:102-122. DOI 10.1007/978-3-642-37051-9_6. On-the-fly construction without dominance frontiers.
- Zhao, Nagarakatte, Martin, Zdancewic. "Formal verification of SSA-based optimizations for LLVM." PLDI 2013, pp. 175-186. DOI 10.1145/2491956.2462164. The verified pass vmem2reg inserts phi-nodes for a promotable allocation at the beginning of every block and then removes redundant ones by verified micro-transformations (source for this description: J. Zhao, "Formalizing an SSA-based Compiler for Verified Advanced Program Transformations", PhD dissertation, University of Pennsylvania, 2013, Chapter 8). It does not mechanize phi placement at DF+ or J(S) = DF+(S).
- Barthe, Demange, Pichardie. "Formal verification of an SSA-based middle-end for CompCert." ACM TOPLAS 36(1), Article 4, 2014. DOI 10.1145/2579080. SSA generation by an untrusted builder checked by a verified validator; Section 8 verifies conversion out of SSA on normalized CFGs (critical edges removed, phis at join points), for phi-blocks whose sequential and parallel readings agree.

**Design question.** Does phi placement at the iterated dominance frontier plus dominator-tree renaming produce an SSA program that computes the same values as the source, and which hypotheses on the CFG, the placement, and the renaming does that need?

**Basis: derived (modeling bridge).** The construction mirrors the classic Cytron et al. pipeline (DF⁺ placement plus dominator-tree renaming) that LLVM's mem2reg also follows in pruned form (bridge (a)); Cranelift uses a different algorithm (bridge (b)). The theorem neither establishes nor refutes the correctness of either implementation.

**Non-claims:** see Boundaries, card `ssa-construct-preserves-values`.

### 14. `ssa-construct-single-assignment`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** For every source program, placement, and renaming source, if the list vars has no duplicates then the constructed program is in static single-assignment form (every SSA name has at most one static definition, a phi destination or an instruction destination), and no phi or instruction defines an entry name (x, entry, 0).

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/Construct.lean:436-439
theorem ssaConstruct_singleAssignment_of_nodup (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (hnd : vars.Nodup) :
    (ssaConstruct S vars phi idom).SingleAssignment ∧
      ∀ b x, ((x, S.cfg.entry, 0) : SName n) ∉ (ssaConstruct S vars phi idom).defsAt b := …
```

**Definitions used:** `ssaConstruct`, `SsaProg.SingleAssignment`, `SsaProg.defsAt` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hnd : vars.Nodup` | A duplicated variable gets two phis with the same destination. | tight | `ssaConstruct_singleAssignment_needs_nodup`; witness class: the diamond program with vars = [0, 0] |

**Non-vacuity witness.** Diamond program with vars = [0]. Lean: `ssaConstruct_singleAssignment_nonvacuous`.

**Tier justification.** Cytron et al. Lemma 8 (each new variable is the target of exactly one assignment), restated for this construction.

**Prior art.**

- Cytron, Ferrante, Rosen, Wegman, Zadeck. "Efficiently computing static single assignment form and the control dependence graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320. Section 5.2: Lemma 8 (each new variable is the target of exactly one assignment), Lemma 9 (for an edge X -> Y such that Y has no phi for V, TopAfter(V, X) = TopAfter(V, idom(Y))), Lemma 10 (along every control path the renamed variables agree with the original ones).

**Design question.** Does phi placement at the iterated dominance frontier plus dominator-tree renaming produce an SSA program that computes the same values as the source, and which hypotheses on the CFG, the placement, and the renaming does that need?

**Non-claims:** see Boundaries, card `ssa-construct-single-assignment`.

### 15. `naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ`

**Tier** T2 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** For every SSA program in which every predecessor of a block carrying phis has that block as its only successor, the naive translation with parallel copies satisfies, along every walk with last block b: (a) on entry to b (after b's phis in the SSA program) the two stores are equal on all variables, and (b) if no successor of b carries phis, the stores are also equal after b's body.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:104-109
theorem naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc {V : Type} [DecidableEq V]
    (P : SsaProg V n) (h : PhiPredsSingleSucc P) {a b : Fin n} {path : List (Fin n)}
    (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .parallel P).run σ path = P.run σ path) := …
```

**Definitions used:** `PhiPredsSingleSucc`, `naiveOutOfSsa`, `SsaProg.atTop`, `Walk` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `h : PhiPredsSingleSucc P` | Copies for a phi block also run on the other branches of a branching predecessor. | tight | `naiveOutOfSsa_needs_phiPredsSingleSucc`; witness class: the lost-copy loop (critical back edge) |
| `mode = .parallel` | Sequential copies break when a phi reads another phi's destination. | tight | `naiveOutOfSsa_needs_parallel`; witness class: the swap loop |
| `hw : Walk P.cfg a b path` | On a non-walk, copies for a real successor are visible elsewhere. | tight | `naiveOutOfSsa_needs_walk`; witness class: the swap CFG on the non-walk [0, 3] |
| `hexit : forall c, P.cfg.edge b c = true -> P.phis c = [] (premise of conclusion (b) only)` | At the end of a block with a phi-carrying successor the naive translation has already run that successor's copies. | tight | `naiveOutOfSsa_run_needs_exit`; witness class: the 2-node lost-copy loop without an exit block |

**Non-vacuity witness.** The swap loop (back edge split by a latch) on a walk ending at its exit block. Lean: `naiveOutOfSsa_hyps_nonvacuous`.

**Tier justification.** Known informally (Briggs et al.); mechanized for normalized CFGs (no critical edges, phis at join points) in CompCertSSA (Barthe et al.; Demange and Fernandez de Retana). Stated here with parallel copies on unnormalized CFGs under the weaker condition PhiPredsSingleSucc (critical edges into phi-free blocks allowed).

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Barthe, Demange, Pichardie. "Formal verification of an SSA-based middle-end for CompCert." ACM TOPLAS 36(1), Article 4, 2014. DOI 10.1145/2579080. SSA generation by an untrusted builder checked by a verified validator; Section 8 verifies conversion out of SSA on normalized CFGs (critical edges removed, phis at join points), for phi-blocks whose sequential and parallel readings agree.
- Demange, Fernandez de Retana. "Mechanizing conventional SSA for a verified destruction with coalescing." CC 2016, pp. 77-87. DOI 10.1145/2892208.2892222. Mechanized SSA destruction in CompCertSSA via conventional SSA and parallel copies.
- Sreedhar, Ju, Gillies, Santhanam. "Translating out of static single assignment form." SAS 1999, LNCS 1694:194-210. DOI 10.1007/3-540-48294-6_13. Conventional SSA (CSSA): phi-related variables with non-interfering live ranges, eliminated without edge splitting.
- Rastello, Bouchez Tichadou (eds.). SSA-based Compiler Design. Springer, 2022. DOI 10.1007/978-3-030-80515-9. Textbook treatment of phi placement, renaming, and SSA destruction.

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Basis: derived (modeling bridge).** Compilers that lower φs or block parameters to per-edge parallel moves, after splitting critical edges into φ blocks, match the shape of this theorem; the toy model omits terminators and parallel edges (Applicability), so this neither establishes nor refutes the correctness of any such lowering.

**Non-claims:** see Boundaries, card `naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ`.

### 16. `naive-out-of-ssa-parallel-eq-of-no-critical-edges`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** For every SSA program whose CFG has no critical edges and whose phis occur only at blocks with two distinct predecessors, the naive translation with parallel copies satisfies conclusions (a) and (b) of naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ along every walk.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:134-139
theorem naiveOutOfSsa_parallel_eq_of_noCriticalEdges_of_phisOnlyAtJoins {V : Type} [DecidableEq V]
    (P : SsaProg V n) (hce : NoCriticalEdges P.cfg) (hj : PhisOnlyAtJoins P)
    {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .parallel P).run σ path = P.run σ path) := …
```

**Definitions used:** `NoCriticalEdges`, `PhisOnlyAtJoins`, `naiveOutOfSsa` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hce : NoCriticalEdges P.cfg` | Lost copy. | tight | `naiveOutOfSsa_noCriticalEdges_needs_noCriticalEdges`; witness class: the lost-copy loop |
| `hj : PhisOnlyAtJoins P` | A phi at a single-predecessor block below a branch runs its copy on the other branch. | tight | `naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins`; witness class: a 3-node branch with a phi at a single-predecessor block |
| `mode = .parallel` | Swap. | tight | `naiveOutOfSsa_noCriticalEdges_needs_parallel`; witness class: the swap loop |
| `hw : Walk P.cfg a b path` | As above. | tight | `naiveOutOfSsa_needs_walk`; witness class: the swap CFG on the non-walk [0, 3] |
| `hexit : forall c, P.cfg.edge b c = true -> P.phis c = [] (premise of conclusion (b) only)` | At the end of a block with a phi-carrying successor the naive translation has already run that successor's copies. | tight | `naiveOutOfSsa_run_needs_exit`; witness class: the 2-node lost-copy loop without an exit block |

**Non-vacuity witness.** The swap loop on a walk ending at its exit block. Lean: `naiveOutOfSsa_hyps_nonvacuous`.

**Tier justification.** The standard recipe (split critical edges, phis at join points, parallel copies): textbook, and mechanized for normalized CFGs in CompCertSSA; derived here from the previous result.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Barthe, Demange, Pichardie. "Formal verification of an SSA-based middle-end for CompCert." ACM TOPLAS 36(1), Article 4, 2014. DOI 10.1145/2579080. SSA generation by an untrusted builder checked by a verified validator; Section 8 verifies conversion out of SSA on normalized CFGs (critical edges removed, phis at join points), for phi-blocks whose sequential and parallel readings agree.
- Demange, Fernandez de Retana. "Mechanizing conventional SSA for a verified destruction with coalescing." CC 2016, pp. 77-87. DOI 10.1145/2892208.2892222. Mechanized SSA destruction in CompCertSSA via conventional SSA and parallel copies.
- Rastello, Bouchez Tichadou (eds.). SSA-based Compiler Design. Springer, 2022. DOI 10.1007/978-3-030-80515-9. Textbook treatment of phi placement, renaming, and SSA destruction.

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `naive-out-of-ssa-parallel-eq-of-no-critical-edges`.

### 17. `naive-out-of-ssa-sequential-eq-of-seq-safe`

**Tier** T1 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** For every SSA program in which every predecessor of a block carrying phis has that block as its only successor and in which, for every pair of blocks (p, b) (including non-edges, since SsaProg.phis supplies total operand functions), no phi destination of b is the destination or the p-operand of a later phi of b (SeqSafe (P.phiMoves p b)), the naive translation with sequential copies in phi order satisfies conclusions (a) and (b) of the parallel theorem along every walk. At the level of one move list: SeqSafe moves executed one at a time have the effect of the parallel copy.

**Lean statements** (verbatim source, proofs elided; this card bundles 2 theorems: `naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe`, `execBody_sequential_eq_parCopy`):

```lean
-- lean/ToySsa/OutOfSsa.lean:210-215
theorem naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe {V : Type} [DecidableEq V]
    (P : SsaProg V n) (h : PhiPredsSingleSucc P) (hs : ∀ p b, SeqSafe (P.phiMoves p b))
    {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .sequential P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .sequential P).run σ path = P.run σ path) := …
-- lean/ToySsa/OutOfSsa.lean:154-156
theorem execBody_sequential_eq_parCopy {V : Type} [DecidableEq V] :
    ∀ (ms : List (V × V)), SeqSafe ms → ∀ σ : V → Nat,
      execBody (copyInstrs .sequential ms) σ = parCopy ms σ
```

**Definitions used:** `PhiPredsSingleSucc`, `SeqSafe`, `copyInstrs`, `parCopy`, `naiveOutOfSsa` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `h : PhiPredsSingleSucc P (premise of naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe)` | As for parallel copies. | tight | `naiveOutOfSsa_sequential_needs_phiPredsSingleSucc`; witness class: the lost-copy loop (one phi, so SeqSafe holds) |
| `hs : forall p b, SeqSafe (P.phiMoves p b) (in execBody_sequential_eq_parCopy: SeqSafe ms for the single move list ms)` | A destination read or rewritten by a later copy is clobbered. The hypothesis ranges over every pair of blocks (p, b), including pairs that are not CFG edges; a version restricted to CFG edges is not proved here. | tight | `naiveOutOfSsa_sequential_needs_seqSafe`, `execBody_sequential_needs_seqSafe`; witness class: the swap CFG with header phis a2 = phi(a1, c1), b2 = phi(b1, a2) in this order; for execBody_sequential_eq_parCopy, the 2-move swap list [(0, 1), (1, 0)] from the identity store |
| `hw : Walk P.cfg a b path (premise of naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe)` | As for parallel copies. | tight | `naiveOutOfSsa_sequential_needs_walk`; witness class: the swap CFG on the non-walk [0, 3] |
| `hexit : forall c, P.cfg.edge b c = true -> P.phis c = [] (premise of conclusion (b) of naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe)` | As for parallel copies. | tight | `naiveOutOfSsa_sequential_run_needs_exit`; witness class: the 2-node lost-copy loop without an exit block |

**Non-vacuity witness.** The swap CFG with header phis in order [b2, a2] on a walk through the back edge to the exit. For execBody_sequential_eq_parCopy: the move list [(2, 1), (1, 0)], in which the second move overwrites the source of the first, is SeqSafe. Lean: `naiveOutOfSsa_sequential_hyps_nonvacuous`, `execBody_sequential_hyps_nonvacuous`.

**Tier justification.** The ordering condition for sequential copies (Briggs et al. Figure 13; parallel-move sequentialization) made precise for the naive translation.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Rideau, Serpette, Leroy. "Tilting at windmills with Coq: formal verification of a compilation algorithm for parallel moves." J. Automated Reasoning 40(4):307-326, 2008. DOI 10.1007/s10817-007-9096-8. Verified sequentialization of parallel moves using a temporary.
- Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125. DOI 10.1109/CGO.2009.19 (research report version HAL inria-00349925). Section III-C, Algorithm 1 sequentializes a parallel copy using one extra fresh variable n shared by all cycles, emitting at most one additional copy per circuit with no outgoing tree edge and none for a circuit that has one (example: a->b, b->c, c->a, c->d becomes d = c, c = a, a = b, b = d).

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `naive-out-of-ssa-sequential-eq-of-seq-safe`.

### 18. `naive-out-of-ssa-block-end-needs-exit-edge`

**Tier** T0 · **Kind** counterexample · **Depth** definitional · **Basis:** execution (Lean kernel check)

**Plain claim.** On the lost-copy loop 0 -> 1, 1 -> 1 without an exit block (the return of x2 at the end of block 1 not modeled as an edge), every predecessor of the phi block has a single successor, no edge is critical, and the block-entry stores agree on the walk [0, 1, 1], but at the end of block 1 the naive translation with parallel copies has x2 = 3 while the SSA program has x2 = 2.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:670-677
theorem naiveOutOfSsa_run_needs_exit :
    PhiPredsSingleSucc lostNoExitSsa ∧ NoCriticalEdges lostNoExitCfg ∧
    PhisOnlyAtJoins lostNoExitSsa ∧ Walk lostNoExitCfg 0 1 [0, 1, 1] ∧
    ¬ (∀ c, lostNoExitCfg.edge 1 c = true → lostNoExitSsa.phis c = []) ∧
    (naiveOutOfSsa .parallel lostNoExitSsa).atTop (fun _ => 0) [0, 1, 1] =
      lostNoExitSsa.atTop (fun _ => 0) [0, 1, 1] ∧
    (naiveOutOfSsa .parallel lostNoExitSsa).run (fun _ => 0) [0, 1, 1] 1 = 3 ∧
    lostNoExitSsa.run (fun _ => 0) [0, 1, 1] 1 = 2 := …
```

**Definitions used:** `lostNoExitCfg`, `PhiPredsSingleSucc`, `NoCriticalEdges`, `naiveOutOfSsa` (see Definitions).

**Hypothesis ledger.** None (parameterless concrete counterexample instance).

**Non-vacuity witness.** Concrete instance (the statement is the instance).

**Tier justification.** Briggs et al.'s lost-copy loop with the return left implicit; a concrete kernel-checked instance.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `naive-out-of-ssa-block-end-needs-exit-edge`.

### 19. `swap-sequential-either-order-wrong`

**Tier** T0 · **Kind** counterexample · **Depth** definitional · **Basis:** execution (Lean kernel check)

**Plain claim.** On the swap loop (a1 := 1, b1 := 2; header phis a2 = phi(a1, b2), b2 = phi(b1, a2); back edge split by a latch block), after one back-edge traversal the SSA program has (a2, b2) = (2, 1), while the naive translation with sequential copies gives (2, 2) in phi order [a2, b2] and (1, 1) in phi order [b2, a2].

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:278-284
theorem swap_sequential_either_order_wrong :
    (swapSsaAB.atTop (fun _ => 0) swapWalk 2, swapSsaAB.atTop (fun _ => 0) swapWalk 3) = (2, 1) ∧
    (swapSsaBA.atTop (fun _ => 0) swapWalk 2, swapSsaBA.atTop (fun _ => 0) swapWalk 3) = (2, 1) ∧
    ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk 2,
      (naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk 3) = (2, 2) ∧
    ((naiveOutOfSsa .sequential swapSsaBA).atTop (fun _ => 0) swapWalk 2,
      (naiveOutOfSsa .sequential swapSsaBA).atTop (fun _ => 0) swapWalk 3) = (1, 1) := …
```

**Definitions used:** `swapCfg`, `naiveOutOfSsa`, `SsaProg.atTop` (see Definitions).

**Hypothesis ledger.** None (parameterless concrete counterexample instance).

**Non-vacuity witness.** Concrete instance.

**Positive control** (a nearby setting where the failure does not occur): `swap_parallel_correct` (on every walk of swapCfg, the naive translation of swapSsaAB with parallel copies agrees with swapSsaAB on entry to the last block, on every variable and for every initial store) and `swap_temp_sequence_correct` (card 20).

**Tier justification.** Briggs et al.'s swap problem as a concrete kernel-checked instance.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Barthe, Demange, Pichardie. "Formal verification of an SSA-based middle-end for CompCert." ACM TOPLAS 36(1), Article 4, 2014. DOI 10.1145/2579080. SSA generation by an untrusted builder checked by a verified validator; Section 8 verifies conversion out of SSA on normalized CFGs (critical edges removed, phis at join points), for phi-blocks whose sequential and parallel readings agree.
- Rideau, Serpette, Leroy. "Tilting at windmills with Coq: formal verification of a compilation algorithm for parallel moves." J. Automated Reasoning 40(4):307-326, 2008. DOI 10.1007/s10817-007-9096-8. Verified sequentialization of parallel moves using a temporary.
- Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125. DOI 10.1109/CGO.2009.19 (research report version HAL inria-00349925). Section III-C, Algorithm 1 sequentializes a parallel copy using one extra fresh variable n shared by all cycles, emitting at most one additional copy per circuit with no outgoing tree edge and none for a circuit that has one (example: a->b, b->c, c->a, c->d becomes d = c, c = a, a = b, b = d).

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `swap-sequential-either-order-wrong`.

### 20. `swap-temp-sequence-correct`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** On every walk of the swap CFG, the out-of-SSA program swapTempProg (block 0: a1 := 1; b1 := 2; a2 := a1; b2 := b1; latch block 2: t := a2; a2 := b2; b2 := t) agrees with the swap SSA program on entry to the last block on every variable other than the temporary t.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:351-353
theorem swap_temp_sequence_correct {a b : Fin 4} {path : List (Fin 4)}
    (hw : Walk swapCfg a b path) (σ : Nat → Nat) (x : Nat) (hx : x ≠ 4) :
    swapTempProg.atTop σ path x = swapSsaAB.atTop σ path x := …
```

**Definitions used:** `swapCfg`, `Walk`, `Prog.atTop`, `SsaProg.atTop` (see Definitions).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample and witness class |
| :--- | :--- | :--- | :--- |
| `hw : Walk swapCfg a b path` | On a non-walk the entry copies are visible at the exit. | tight | `swap_temp_needs_walk`; witness class: the swap CFG on the non-walk [0, 3] |
| `hx : x != 4` | The temporary itself differs. | tight | `swap_temp_needs_ne_temp`; witness class: the swap loop after one trip, x = 4 |

**Non-vacuity witness.** One loop trip [0, 1, 2, 1], observed variable a2 = 2. Lean: `swap_temp_hyps_nonvacuous`.

**Tier justification.** Breaking a copy cycle with one temporary (Briggs et al.; Rideau et al.; Boissinot et al.'s Algorithm 1) on the swap loop.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Rideau, Serpette, Leroy. "Tilting at windmills with Coq: formal verification of a compilation algorithm for parallel moves." J. Automated Reasoning 40(4):307-326, 2008. DOI 10.1007/s10817-007-9096-8. Verified sequentialization of parallel moves using a temporary.
- Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125. DOI 10.1109/CGO.2009.19 (research report version HAL inria-00349925). Section III-C, Algorithm 1 sequentializes a parallel copy using one extra fresh variable n shared by all cycles, emitting at most one additional copy per circuit with no outgoing tree edge and none for a circuit that has one (example: a->b, b->c, c->a, c->d becomes d = c, c = a, a = b, b = d).

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `swap-temp-sequence-correct`.

### 21. `lost-copy-naive-miscompiles`

**Tier** T0 · **Kind** counterexample · **Depth** definitional · **Basis:** execution (Lean kernel check)

**Plain claim.** On Briggs et al.'s lost-copy loop (CFG 0 -> 1, 1 -> 1, 1 -> 2; x1 := 1; x2 = phi(x1, x3); x3 := x2 + 1; the exit reads x2), on the walk [0, 1, 1, 2] the source returns 2 and the SSA program has x2 = 2 at the exit, but the naive translation has x2 = 3 with parallel copies and with sequential copies.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:466-470
theorem lostCopy_naive_miscompiles :
    lostSource.atTop (fun _ => 0) lostWalk 1 = 2 ∧
    lostSsa.atTop (fun _ => 0) lostWalk 1 = 2 ∧
    (naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk 1 = 3 ∧
    (naiveOutOfSsa .sequential lostSsa).atTop (fun _ => 0) lostWalk 1 = 3 := …
```

**Definitions used:** `lostCfg`, `naiveOutOfSsa`, `Prog.atTop`, `SsaProg.atTop` (see Definitions).

**Hypothesis ledger.** None (parameterless concrete counterexample instance).

**Non-vacuity witness.** Concrete instance.

**Positive control** (a nearby setting where the failure does not occur): `lostCopy_split_fixes`.

**Tier justification.** Briggs et al. Figure 10 as a concrete kernel-checked instance.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).
- Sreedhar, Ju, Gillies, Santhanam. "Translating out of static single assignment form." SAS 1999, LNCS 1694:194-210. DOI 10.1007/3-540-48294-6_13. Conventional SSA (CSSA): phi-related variables with non-interfering live ranges, eliminated without edge splitting.
- Demange, Fernandez de Retana. "Mechanizing conventional SSA for a verified destruction with coalescing." CC 2016, pp. 77-87. DOI 10.1145/2892208.2892222. Mechanized SSA destruction in CompCertSSA via conventional SSA and parallel copies.

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Basis: derived (modeling bridge).** The program is Briggs et al.'s lost-copy example; any compiler whose out-of-SSA pass appends φ copies to a predecessor with a critical edge after copy folding faces this pattern. The theorem is about the toy program (model–system relation: none proved) and neither establishes nor refutes the behaviour of a particular compiler.

**Non-claims:** see Boundaries, card `lost-copy-naive-miscompiles`.

### 22. `lost-copy-split-fixes`

**Tier** T0 · **Kind** theorem · **Depth** shallow · **Basis:** execution (Lean kernel check)

**Plain claim.** For every number k of back-edge traversals (the loop body runs k + 1 >= 1 times) and every initial store, the naive parallel-copy translation of the lost-copy program on the CFG with the critical edge 1 -> 1 split by a new block 3 reaches the exit with the same store as the SSA program on the original CFG.

**Lean statement** (verbatim source, proof elided):

```lean
-- lean/ToySsa/OutOfSsa.lean:583-585
theorem lostCopy_split_fixes (k : Nat) (σ : Nat → Nat) :
    (naiveOutOfSsa .parallel lostSplitSsa).atTop σ (lostSplitWalk k) =
      lostSsa.atTop σ (lostLoopWalk k) := …
```

**Definitions used:** `lostCfg`, `lostSplitCfg`, `naiveOutOfSsa` (see Definitions).

**Hypothesis ledger.** No hypotheses beyond the universally quantified back-edge traversal count `k : Nat` and initial store `σ : Nat → Nat` (on the fixed concrete programs `lostSsa` and `lostSplitSsa`).

**Non-vacuity witness.** Both compared lists are walks for every k (lostLoopWalk_walk, lostSplitWalk_walk). Lean: `lostSplitWalk_walk`, `lostLoopWalk_walk`.

**Tier justification.** Briggs et al.'s fix (split the critical edge) for their Figure 10.

**Prior art.**

- Briggs, Cooper, Harvey, Simpson. "Practical improvements to the construction and destruction of static single assignment form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8. Critical edge: from a block with several successors to a block with several predecessors; the lost-copy problem 'can only occur when copies are folded and one or more critical back-edges are present' (Figure 10, fixed by splitting the critical edge or, in their Figure 11, by saving live phi destinations in temporaries); the swap problem (Figure 12) and the ordering of copies when a phi reads another phi's destination (Figure 13).

**Design question.** When is replacing phi-functions by copies at the end of predecessor blocks a correct out-of-SSA translation, and which conditions (parallel copy semantics, edge splitting, exit modeling) are exactly needed?

**Non-claims:** see Boundaries, card `lost-copy-split-fixes`.

### Auxiliary declarations cited by name

The declarations below are named in the cards, ledgers, tables or non-claims (non-vacuity witnesses, tightness counterexamples, examples, positive controls, concrete programs and CFGs, and the auxiliary lemmas of the join-closure proofs), or occur in a quoted statement, without being quoted elsewhere in this report. Each is quoted verbatim from the source with its `file:line` range: theorems with the proof elided, definitions in full. All of them are listed in `results.json` (`lean_names`), so their statement hashes are recorded in `audit/statements.json` (see Evidence).

Examples of the graph notions (from `lean/ToySsa/Examples.lean`):

```lean
-- lean/ToySsa/Examples.lean:25
theorem walk_example : Walk diamond 0 3 [0, 1, 3] := …
-- lean/ToySsa/Examples.lean:27
theorem not_walk_example : ¬ Walk diamond 0 3 [0, 3] := …
-- lean/ToySsa/Examples.lean:36
theorem allReachable_diamond : AllReachable diamond := …
-- lean/ToySsa/Examples.lean:48
theorem not_allReachable_isolated2 : ¬ AllReachable isolated2 := …
-- lean/ToySsa/Examples.lean:54
theorem entryNoPreds_diamond : EntryNoPreds diamond := …
-- lean/ToySsa/Examples.lean:57
def backToEntry2 : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 0)] 0
-- lean/ToySsa/Examples.lean:59
theorem not_entryNoPreds_backToEntry2 : ¬ EntryNoPreds backToEntry2 := …
-- lean/ToySsa/Examples.lean:64
theorem dom_example : Dom diamond 0 3 := …
-- lean/ToySsa/Examples.lean:65
theorem dom_chain_example : Dom chain3 1 2 := …
-- lean/ToySsa/Examples.lean:66
theorem not_dom_example : ¬ Dom diamond 1 3 := …
-- lean/ToySsa/Examples.lean:67
theorem sdom_example : SDom diamond 0 3 := …
-- lean/ToySsa/Examples.lean:68
theorem not_sdom_self_example : ¬ SDom diamond 3 3 := …
-- lean/ToySsa/Examples.lean:72
theorem df_example : DF diamond 1 3 := …
-- lean/ToySsa/Examples.lean:73
theorem not_df_example : ¬ DF diamond 0 3 := …
-- lean/ToySsa/Examples.lean:75
theorem df_loop_example : DF loop4 2 1 := …
-- lean/ToySsa/Examples.lean:77
theorem not_df_ladder_example : ¬ DF ladder5 2 4 := …
-- lean/ToySsa/Examples.lean:82
theorem idf_iterates_example : IDF ladder5 (fun x => x = 2) 4 := …
-- lean/ToySsa/Examples.lean:86
theorem not_idf_example (y : Fin 4) : ¬ IDF diamond (fun x => x = diamond.entry) y := …
-- lean/ToySsa/Examples.lean:91
theorem inJoin_example : InJoin diamond (fun x => x = 1 ∨ x = 2) 3 := …
-- lean/ToySsa/Examples.lean:97
theorem inJoin_cycle_example : InJoin selfLoop2 (fun x => x = 0 ∨ x = 1) 1 := …
-- lean/ToySsa/Examples.lean:103
theorem not_converge_example : ¬ Converge diamond 0 1 3 [0, 1, 3] [1, 3] := …
-- lean/ToySsa/Examples.lean:109
theorem not_inJoin_example : ¬ InJoin chain3 (fun x => x = 0 ∨ x = 1) 2 := …
-- lean/ToySsa/Examples.lean:116
theorem reachesTop_example : ReachesTop diamond (fun w => w = 0 ∨ w = 1) 0 3 := …
-- lean/ToySsa/Examples.lean:119-120
theorem not_reachesTop_example :
    ¬ ReachesTop diamond (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) 0 3 := …
-- lean/ToySsa/Examples.lean:124-126
theorem srd_example :
    SingleReachingDef diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) := …
-- lean/ToySsa/Examples.lean:129-130
theorem not_srd_example :
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := …
-- lean/ToySsa/Examples.lean:139
theorem nearestSDomDef_example : NearestSDomDef chain3 (fun w => w = 0 ∨ w = 1) 2 1 := …
-- lean/ToySsa/Examples.lean:147
theorem not_nearestSDomDef_example : ¬ NearestSDomDef chain3 (fun w => w = 0 ∨ w = 1) 2 0 := …
```

Placement and reaching definitions (from `lean/ToySsa/Placement.lean`):

```lean
-- lean/ToySsa/Placement.lean:37-38
def PreWalk (G : Cfg n) (x z : Fin n) (A : List (Fin n)) : Prop :=
  ∃ u, Walk G x u A ∧ G.edge u z = true
-- lean/ToySsa/Placement.lean:41-42
def InJoinPre (G : Cfg n) (S : Fin n → Prop) (z : Fin n) : Prop :=
  ∃ x y A B, S x ∧ S y ∧ x ≠ y ∧ PreWalk G x z A ∧ PreWalk G y z B ∧ ∀ v, v ∈ A → v ∉ B
-- lean/ToySsa/Placement.lean:55-56
theorem inJoin_iff_preWalks (G : Cfg n) (S : Fin n → Prop) (z : Fin n) :
    InJoin G S z ↔ InJoinPre G S z := …
-- lean/ToySsa/Placement.lean:199-203
theorem inJoinPre_of_join_point (G : Cfg n) (S : Fin n → Prop) :
    ∀ (N : Nat) (w z a x y : Fin n) (A B C R : List (Fin n)), R.length ≤ N →
      S x → S y → x ≠ y → PreWalk G x w A → PreWalk G y w B → (∀ v, v ∈ A → v ∉ B) →
      S a → PreWalk G a z C → PreWalk G w z R → (∀ v, v ∈ C → v ∉ R) →
      InJoinPre G S z := …
-- lean/ToySsa/Placement.lean:289-290
theorem inJoinPre_of_insert_join {G : Cfg n} {S : Fin n → Prop} {w z : Fin n}
    (hw : InJoinPre G S w) (hz : InJoinPre G (fun t => S t ∨ t = w) z) : InJoinPre G S z := …
-- lean/ToySsa/Placement.lean:314-316
theorem df_preWalks_of_allReachable_of_entryNoPreds {G : Cfg n} (hreach : AllReachable G)
    (hnp : EntryNoPreds G) {x y : Fin n} (hdf : DF G x y) :
    x ≠ G.entry ∧ ∃ A B, PreWalk G x y A ∧ PreWalk G G.entry y B ∧ ∀ v, v ∈ A → v ∉ B := …
-- lean/ToySsa/Placement.lean:416-419
theorem join_subset_iteratedDF_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    InJoin unreachJoin4 (fun x => x = 1 ∨ x = 2) 3 ∧
    ¬ IDF unreachJoin4 (fun x => x = 1 ∨ x = 2) 3 := …
-- lean/ToySsa/Placement.lean:442-445
theorem iteratedDF_subset_join_needs_entryNoPreds :
    AllReachable entryLoop1 ∧ ¬ EntryNoPreds entryLoop1 ∧
    (fun x => x = (0 : Fin 1)) entryLoop1.entry ∧
    IDF entryLoop1 (fun x => x = 0) 0 ∧ ¬ InJoin entryLoop1 (fun x => x = 0) 0 := …
-- lean/ToySsa/Placement.lean:456-458
theorem iteratedDF_subset_join_needs_entry_mem :
    AllReachable selfLoop2 ∧ EntryNoPreds selfLoop2 ∧ ¬ (fun x => x = (1 : Fin 2)) selfLoop2.entry ∧
    IDF selfLoop2 (fun x => x = 1) 1 ∧ ¬ InJoin selfLoop2 (fun x => x = 1) 1 := …
-- lean/ToySsa/Placement.lean:474-478
theorem iteratedDF_subset_join_needs_allReachable :
    ¬ AllReachable unreachLoop2 ∧
    EntryNoPreds unreachLoop2 ∧ (fun x => x = (0 : Fin 2) ∨ x = 1) unreachLoop2.entry ∧
    IDF unreachLoop2 (fun x => x = 0 ∨ x = 1) 1 ∧
    ¬ InJoin unreachLoop2 (fun x => x = 0 ∨ x = 1) 1 := …
-- lean/ToySsa/Placement.lean:920-921
theorem joinClosed_diamond_example :
    ∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ w = 3) z → z = 3 := …
-- lean/ToySsa/Placement.lean:929-932
theorem srd_hyps_nonvacuous :
    EntryNoPreds diamond ∧
    SingleReachingDef diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) := …
-- lean/ToySsa/Placement.lean:937-939
theorem srdAll_hyps_nonvacuous :
    SingleReachingDefAll diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) := …
-- lean/ToySsa/Placement.lean:948-955
theorem srd_join_needs_entryNoPreds :
    ¬ EntryNoPreds entryCycle2 ∧
    SingleReachingDef entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => (fun _ => false : Fin 2 → Bool) w = true) ∧
    InJoin entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true ∨
      (fun _ => false : Fin 2 → Bool) w = true) 0 ∧
    InJoin entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true) 0 ∧
    ¬ (fun _ => false : Fin 2 → Bool) 0 = true := …
-- lean/ToySsa/Placement.lean:966-971
theorem extra_phi_srd_without_joinClosed_when_entryPred :
    ¬ EntryNoPreds entryCycle2 ∧
    (∀ z, ¬ InJoin entryCycle2 (fun w => w = 0) z) ∧
    SingleReachingDef entryCycle2 (fun w => w = 0) (fun w => w = 1) ∧
    InJoin entryCycle2 (fun w => w = 0 ∨ w = 1) 0 ∧
    ¬ (fun w : Fin 2 => w = 1) 0 := …
-- lean/ToySsa/Placement.lean:985
theorem join_placement_nonempty_example : InJoin diamond (fun w => w = 0 ∨ w = 1) 3 := …
-- lean/ToySsa/Placement.lean:992-996
theorem srd_iteratedDF_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    ¬ SingleReachingDef unreachJoin4
      (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true)
      (IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true)) := …
-- lean/ToySsa/Placement.lean:1011
theorem allReachable_nonvacuous : AllReachable diamond := …
-- lean/ToySsa/Placement.lean:1015-1018
theorem exists_reachesTop_needs_entry_mem :
    ¬ (fun _ => False : Fin 3 → Prop) chain3.entry ∧ Reachable chain3 1 ∧ (1 : Fin 3) ≠ chain3.entry ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨
      (fun _ => False : Fin 3 → Prop) w) u 1 := …
-- lean/ToySsa/Placement.lean:1024-1027
theorem exists_reachesTop_needs_reachable :
    (fun w => w = (0 : Fin 2)) isolated2.entry ∧ ¬ Reachable isolated2 1 ∧
    (1 : Fin 2) ≠ isolated2.entry ∧
    ¬ ∃ u, ReachesTop isolated2 (fun w => w = 0 ∨ (fun _ => False : Fin 2 → Prop) w) u 1 := …
-- lean/ToySsa/Placement.lean:1037-1040
theorem exists_reachesTop_needs_ne_entry :
    (fun w : Fin 4 => w = 0) diamond.entry ∧ Reachable diamond 0 ∧
    ¬ ((0 : Fin 4) ≠ diamond.entry) ∧
    ¬ ∃ u, ReachesTop diamond (fun w => w = 0 ∨ (fun _ => False : Fin 4 → Prop) w) u 0 := …
-- lean/ToySsa/Placement.lean:1048-1053
theorem reachesTop_at_phi_block_example :
    AllReachable diamond ∧ IDF diamond (fun w => w = 0 ∨ w = 1) 3 ∧
    ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 1 3 ∧
    ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 0 3 ∧
    ¬ NearestSDomDef diamond
      (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 3 1 := …
-- lean/ToySsa/Placement.lean:1073-1076
theorem reachesTop_iff_needs_allReachable :
    ¬ AllReachable isolated2 ∧ ¬ IDF isolated2 (fun w => w = 0) 1 ∧
    NearestSDomDef isolated2 (fun w => w = 0 ∨ IDF isolated2 (fun w => w = 0) w) 1 0 ∧
    ¬ ReachesTop isolated2 (fun w => w = 0 ∨ IDF isolated2 (fun w => w = 0) w) 0 1 := …
-- lean/ToySsa/Placement.lean:1096-1099
theorem strict_subset_of_join_two_defs_diamond :
    (∀ z, (fun _ => False : Fin 4 → Prop) z → InJoin diamond (fun w => w = 0 ∨ w = 1) z) ∧
    InJoin diamond (fun w => w = 0 ∨ w = 1) 3 ∧ ¬ (fun _ => False : Fin 4 → Prop) 3 ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := …
-- lean/ToySsa/Placement.lean:1104-1107
theorem strict_subset_of_join_two_defs_loop :
    (∀ z, (fun _ => False : Fin 4 → Prop) z → InJoin loop4 (fun w => w = 0 ∨ w = 2) z) ∧
    InJoin loop4 (fun w => w = 0 ∨ w = 2) 1 ∧ ¬ (fun _ => False : Fin 4 → Prop) 1 ∧
    ¬ SingleReachingDef loop4 (fun w => w = 0 ∨ w = 2) (fun _ => False) := …
-- lean/ToySsa/Placement.lean:1128-1132
theorem existsUnique_needs_entry_mem :
    AllReachable chain3 ∧ ¬ (fun _ => False : Fin 3 → Prop) chain3.entry ∧
    ¬ IDF chain3 (fun _ => False) 1 ∧ (1 : Fin 3) ≠ chain3.entry ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨
      IDF chain3 (fun _ => False) w) u 1 := …
-- lean/ToySsa/Placement.lean:1146-1158
theorem existsUnique_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) unreachJoin4.entry ∧
    ¬ IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) 3 ∧
    (3 : Fin 4) ≠ unreachJoin4.entry ∧
    ¬ ∃ u, ReachesTop unreachJoin4
        (fun w => (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w ∨
          IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w)
        u 3 ∧
      ∀ v, ReachesTop unreachJoin4
        (fun w => (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w ∨
          IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w)
        v 3 → v = u := …
-- lean/ToySsa/Placement.lean:1174-1180
theorem existsUnique_needs_not_idf :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧
    IDF diamond (fun w => w = 0 ∨ w = 1) 3 ∧ (3 : Fin 4) ≠ diamond.entry ∧
    ¬ ∃ u, ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w)
        u 3 ∧
      ∀ v, ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w)
        v 3 → v = u := …
-- lean/ToySsa/Placement.lean:1188-1192
theorem existsUnique_needs_ne_entry :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4)) diamond.entry ∧
    ¬ IDF diamond (fun w => w = 0) 0 ∧ ¬ ((0 : Fin 4) ≠ diamond.entry) ∧
    ¬ ∃ u, ReachesTop diamond (fun w => w = 0 ∨ IDF diamond (fun w => w = 0) w) u 0 ∧
      ∀ v, ReachesTop diamond (fun w => w = 0 ∨ IDF diamond (fun w => w = 0) w) v 0 → v = u := …
-- lean/ToySsa/Placement.lean:1220-1222
theorem exists_reachesTop_hyps_nonvacuous :
    (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧ Reachable diamond 3 ∧
    (3 : Fin 4) ≠ diamond.entry := …
-- lean/ToySsa/Placement.lean:1226-1228
theorem existsUnique_hyps_nonvacuous :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧
    ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 1 ∧ (1 : Fin 4) ≠ diamond.entry := …
-- lean/ToySsa/Placement.lean:1233-1234
theorem reachesTop_iff_hyps_nonvacuous :
    AllReachable diamond ∧ ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 1 := …
-- lean/ToySsa/Placement.lean:1241-1244
theorem singleReachingDef_needs_joinClosed :
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := …
-- lean/ToySsa/Placement.lean:1251-1254
theorem singleReachingDefAll_needs_joinClosed :
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) ∧
    ¬ SingleReachingDefAll diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := …
-- lean/ToySsa/Placement.lean:1261-1264
theorem joinClosed_needs_singleReachingDefAll :
    ¬ SingleReachingDefAll diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) := …
-- lean/ToySsa/Placement.lean:1268-1272
theorem joinClosed_needs_singleReachingDef :
    EntryNoPreds diamond ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) := …
-- lean/ToySsa/Placement.lean:1276-1279
theorem join_subset_needs_singleReachingDef :
    EntryNoPreds diamond ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => w = 0 ∨ w = 1) z → (fun _ => False : Fin 4 → Prop) z) := …
-- lean/ToySsa/Placement.lean:1284-1288
theorem srd_entry_exemption_example :
    ReachesTop entryCycle2 (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 2 → Prop) w) 0 0 ∧
    ReachesTop entryCycle2 (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 2 → Prop) w) 1 0 ∧
    SingleReachingDef entryCycle2 (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ SingleReachingDefAll entryCycle2 (fun w => w = 0 ∨ w = 1) (fun _ => False) := …
-- lean/ToySsa/Placement.lean:1307-1309
theorem srd_at_most_one_example :
    SingleReachingDef chain3 (fun _ => False) (fun _ => False) ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨ False) u 1 := …
-- lean/ToySsa/Placement.lean:1318-1320
theorem srd_not_monotone_diamond :
    (∀ z, InJoin diamond (fun w => w = 0) z → (fun w : Fin 4 => w = 1) z) ∧
    ¬ SingleReachingDef diamond (fun w => w = 0) (fun w => w = 1) := …
-- lean/ToySsa/Placement.lean:1330-1332
theorem join_union_join_genuine_nonvacuous :
    InJoin ladder5 (fun x => x = 0 ∨ x = 2) 3 ∧ ¬ (fun x : Fin 5 => x = 0 ∨ x = 2) 3 ∧
    InJoin ladder5 (fun x => (x = 0 ∨ x = 2) ∨ InJoin ladder5 (fun x => x = 0 ∨ x = 2) x) 4 := …
-- lean/ToySsa/Placement.lean:1341-1343
theorem join_iteratedDF_full_nonvacuous :
    AllReachable diamond ∧ EntryNoPreds diamond ∧ (fun x : Fin 4 => x = 0 ∨ x = 1) diamond.entry ∧
    InJoin diamond (fun x => x = 0 ∨ x = 1) 3 ∧ IDF diamond (fun x => x = 0 ∨ x = 1) 3 := …
```

SSA construction (from `lean/ToySsa/Construct.lean`):

```lean
-- lean/ToySsa/Construct.lean:28
theorem acyclic_diamond : Acyclic diamond := …
-- lean/ToySsa/Construct.lean:31
theorem not_acyclic_loop4 : ¬ Acyclic loop4 := …
-- lean/ToySsa/Construct.lean:38
theorem entryNoReachablePreds_of_acyclic {G : Cfg n} (h : Acyclic G) : EntryNoReachablePreds G := …
-- lean/ToySsa/Construct.lean:469-471
def diamondSrc : Src 4 where
  cfg := diamond
  body b := if b = 1 then [(0, .add (.var 0) (.lit 1))] else []
-- lean/ToySsa/Construct.lean:474
def diamondPhi (x : Nat) (b : Fin 4) : Bool := decide (x = 0) && decide (b = 3)
-- lean/ToySsa/Construct.lean:477
def diamondIdom (_ : Nat) (_ : Fin 4) : Fin 4 := 0
-- lean/ToySsa/Construct.lean:553
theorem entryNoReachablePreds_diamond : EntryNoReachablePreds diamond := …
-- lean/ToySsa/Construct.lean:558-568
theorem ssaConstruct_hyps_nonvacuous :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] := …
-- lean/ToySsa/Construct.lean:587
def acyclicEntryPredCfg : Cfg 3 := Cfg.ofEdges 3 [(1, 0), (0, 2)] 0
-- lean/ToySsa/Construct.lean:590-592
def acyclicEntryPredSrc : Src 3 where
  cfg := acyclicEntryPredCfg
  body b := if b = 0 then [(0, .add (.var 0) (.lit 1))] else []
-- lean/ToySsa/Construct.lean:596
def epPhi (_ : Nat) (b : Fin 3) : Bool := decide (b = 0)
-- lean/ToySsa/Construct.lean:598
def epIdom (_ : Nat) (_ : Fin 3) : Fin 3 := 0
-- lean/ToySsa/Construct.lean:655-673
theorem ssaConstruct_entryPred_nonvacuous :
    ¬ EntryNoPreds acyclicEntryPredSrc.cfg ∧
    EntryNoReachablePreds acyclicEntryPredSrc.cfg ∧
    (∀ b x e, (x, e) ∈ acyclicEntryPredSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF acyclicEntryPredSrc.cfg (acyclicEntryPredSrc.defPts x) b → epPhi x b = true) ∧
    (∀ x b, epPhi x b = true → IDF acyclicEntryPredSrc.cfg (acyclicEntryPredSrc.defPts x) b) ∧
    (∀ x b, Reachable acyclicEntryPredSrc.cfg b → b ≠ acyclicEntryPredSrc.cfg.entry →
      epPhi x b = false →
      NearestSDomDef acyclicEntryPredSrc.cfg
        (fun d => acyclicEntryPredSrc.defPts x d ∨ epPhi x d = true) b (epIdom x b)) ∧
    (∀ x, (fun nm : SName 3 => (fun _ => 0 : Nat → Nat) nm.1)
      (x, acyclicEntryPredSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk acyclicEntryPredSrc.cfg acyclicEntryPredSrc.cfg.entry 2 [0, 2] ∧
    acyclicEntryPredSrc.toProg.atTop (fun _ => 0) [0, 2] 0 =
      (ssaConstruct acyclicEntryPredSrc [0] epPhi epIdom).atTop
        (fun nm => (fun _ => 0) nm.1) [0, 2] (topName acyclicEntryPredSrc epPhi epIdom 0 2) ∧
    acyclicEntryPredSrc.toProg.run (fun _ => 0) [0, 2] 0 =
      (ssaConstruct acyclicEntryPredSrc [0] epPhi epIdom).run
        (fun nm => (fun _ => 0) nm.1) [0, 2] (liveOutName acyclicEntryPredSrc epPhi epIdom 0 2) := …
-- lean/ToySsa/Construct.lean:684
def loopUnreach5 : Cfg 5 := Cfg.ofEdges 5 [(0, 1), (1, 2), (2, 1), (1, 3)] 0
-- lean/ToySsa/Construct.lean:687-689
def loopUnreachSrc : Src 5 where
  cfg := loopUnreach5
  body b := if b = 2 then [(0, .add (.var 0) (.lit 1))] else []
-- lean/ToySsa/Construct.lean:691
def luPhi (x : Nat) (b : Fin 5) : Bool := decide (x = 0) && decide (b = 1)
-- lean/ToySsa/Construct.lean:693
def luIdom (x : Nat) (b : Fin 5) : Fin 5 := if x = 0 ∧ (b = 2 ∨ b = 3) then 1 else 0
-- lean/ToySsa/Construct.lean:785-802
theorem ssaConstruct_cyclic_unreach_nonvacuous :
    ¬ Acyclic loopUnreach5 ∧ ¬ AllReachable loopUnreach5 ∧
    EntryNoReachablePreds loopUnreachSrc.cfg ∧
    (∀ b x e, (x, e) ∈ loopUnreachSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF loopUnreachSrc.cfg (loopUnreachSrc.defPts x) b → luPhi x b = true) ∧
    (∀ x b, luPhi x b = true → IDF loopUnreachSrc.cfg (loopUnreachSrc.defPts x) b) ∧
    (∀ x b, Reachable loopUnreachSrc.cfg b → b ≠ loopUnreachSrc.cfg.entry → luPhi x b = false →
      NearestSDomDef loopUnreachSrc.cfg (fun d => loopUnreachSrc.defPts x d ∨ luPhi x d = true) b
        (luIdom x b)) ∧
    (∀ x, (fun nm : SName 5 => (fun _ => 0 : Nat → Nat) nm.1)
      (x, loopUnreachSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk loopUnreachSrc.cfg loopUnreachSrc.cfg.entry 3 [0, 1, 2, 1, 2, 1, 3] ∧
    loopUnreachSrc.toProg.atTop (fun _ => 0) [0, 1, 2, 1, 2, 1, 3] 0 = 2 ∧
    (ssaConstruct loopUnreachSrc [0] luPhi luIdom).atTop (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2, 1, 3] (topName loopUnreachSrc luPhi luIdom 0 3) = 2 ∧
    loopUnreachSrc.toProg.run (fun _ => 0) [0, 1, 2, 1, 2] 0 = 2 ∧
    (ssaConstruct loopUnreachSrc [0] luPhi luIdom).run (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2] (liveOutName loopUnreachSrc luPhi luIdom 0 2) = 2 := …
-- lean/ToySsa/Construct.lean:822-824
theorem ssaConstruct_singleAssignment_needs_nodup :
    [0].Nodup ∧ ¬ [0, 0].Nodup ∧
    ¬ (ssaConstruct diamondSrc [0, 0] diamondPhi diamondIdom).SingleAssignment := …
-- lean/ToySsa/Construct.lean:833-835
def entryLoopSrc : Src 1 where
  cfg := entryLoop1
  body _ := [(0, .add (.var 0) (.lit 1))]
-- lean/ToySsa/Construct.lean:840-862
theorem ssaConstruct_needs_entryNoReachablePreds :
    ¬ EntryNoReachablePreds entryLoopSrc.cfg ∧
    (∀ b x e, (x, e) ∈ entryLoopSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => true : Nat → Fin 1 → Bool) x b = true →
      IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b) ∧
    (∀ x b, Reachable entryLoopSrc.cfg b → b ≠ entryLoopSrc.cfg.entry →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = false →
      NearestSDomDef entryLoopSrc.cfg
        (fun d => entryLoopSrc.defPts x d ∨ (fun _ _ => true : Nat → Fin 1 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 1 → Fin 1) x b)) ∧
    (∀ x, (fun nm : SName 1 => (fun _ => 0 : Nat → Nat) nm.1) (x, entryLoopSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk entryLoopSrc.cfg entryLoopSrc.cfg.entry 0 [0, 0] ∧
    ¬ (entryLoopSrc.toProg.atTop (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (topName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0) ∧
      entryLoopSrc.toProg.run (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (liveOutName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0)) := …
-- lean/ToySsa/Construct.lean:881-903
theorem ssaConstruct_acyclic_corollary_needs_acyclic :
    ¬ Acyclic entryLoopSrc.cfg ∧
    (∀ b x e, (x, e) ∈ entryLoopSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => true : Nat → Fin 1 → Bool) x b = true →
      IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b) ∧
    (∀ x b, Reachable entryLoopSrc.cfg b → b ≠ entryLoopSrc.cfg.entry →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = false →
      NearestSDomDef entryLoopSrc.cfg
        (fun d => entryLoopSrc.defPts x d ∨ (fun _ _ => true : Nat → Fin 1 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 1 → Fin 1) x b)) ∧
    (∀ x, (fun nm : SName 1 => (fun _ => 0 : Nat → Nat) nm.1) (x, entryLoopSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk entryLoopSrc.cfg entryLoopSrc.cfg.entry 0 [0, 0] ∧
    ¬ (entryLoopSrc.toProg.atTop (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (topName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0) ∧
      entryLoopSrc.toProg.run (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (liveOutName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0)) := …
-- lean/ToySsa/Construct.lean:911-933
theorem ssaConstruct_needs_phi_cover :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    ¬ (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b →
      (fun _ _ => false : Nat → Fin 4 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => false : Nat → Fin 4 → Bool) x b = true →
      IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry →
      (fun _ _ => false : Nat → Fin 4 → Bool) x b = false →
      NearestSDomDef diamondSrc.cfg
        (fun d => diamondSrc.defPts x d ∨ (fun _ _ => false : Nat → Fin 4 → Bool) x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [0] (fun _ _ => false) diamondIdom).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 1, 3]
          (topName diamondSrc (fun _ _ => false) diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [0] (fun _ _ => false) diamondIdom).run
          (fun nm => (fun _ => 0) nm.1) [0, 1, 3]
          (liveOutName diamondSrc (fun _ _ => false) diamondIdom 0 3)) := …
-- lean/ToySsa/Construct.lean:963-964
def diamondPhiSpurious (x : Nat) (b : Fin 4) : Bool :=
  diamondPhi x b || (decide (x = 1) && decide (b ≠ 0))
-- lean/ToySsa/Construct.lean:988-1007
theorem ssaConstruct_needs_phi_within :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhiSpurious x b = true) ∧
    ¬ (∀ x b, diamondPhiSpurious x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry →
      diamondPhiSpurious x b = false →
      NearestSDomDef diamondSrc.cfg
        (fun d => diamondSrc.defPts x d ∨ diamondPhiSpurious x d = true) b (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => if nm.2.1 = 0 then 0 else 7) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 1 =
        (ssaConstruct diamondSrc [0] diamondPhiSpurious diamondIdom).atTop
          (fun nm => if nm.2.1 = 0 then 0 else 7) [0, 1, 3]
          (topName diamondSrc diamondPhiSpurious diamondIdom 1 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 1 =
        (ssaConstruct diamondSrc [0] diamondPhiSpurious diamondIdom).run
          (fun nm => if nm.2.1 = 0 then 0 else 7) [0, 1, 3]
          (liveOutName diamondSrc diamondPhiSpurious diamondIdom 1 3)) := …
-- lean/ToySsa/Construct.lean:1018-1020
def chainSrc : Src 3 where
  cfg := chain3
  body b := if b = 1 then [(0, .add (.var 0) (.lit 1))] else []
-- lean/ToySsa/Construct.lean:1024-1046
theorem ssaConstruct_needs_nearestSDomDef :
    EntryNoReachablePreds chainSrc.cfg ∧
    (∀ b x e, (x, e) ∈ chainSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF chainSrc.cfg (chainSrc.defPts x) b →
      (fun _ _ => false : Nat → Fin 3 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => false : Nat → Fin 3 → Bool) x b = true →
      IDF chainSrc.cfg (chainSrc.defPts x) b) ∧
    ¬ (∀ x b, Reachable chainSrc.cfg b → b ≠ chainSrc.cfg.entry →
      (fun _ _ => false : Nat → Fin 3 → Bool) x b = false →
      NearestSDomDef chainSrc.cfg
        (fun d => chainSrc.defPts x d ∨ (fun _ _ => false : Nat → Fin 3 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 3 → Fin 3) x b)) ∧
    (∀ x, (fun nm : SName 3 => (fun _ => 0 : Nat → Nat) nm.1) (x, chainSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk chainSrc.cfg chainSrc.cfg.entry 2 [0, 1, 2] ∧
    ¬ (chainSrc.toProg.atTop (fun _ => 0) [0, 1, 2] 0 =
        (ssaConstruct chainSrc [0] (fun _ _ => false) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 1, 2]
          (topName chainSrc (fun _ _ => false) (fun _ _ => 0) 0 2) ∧
      chainSrc.toProg.run (fun _ => 0) [0, 1, 2] 0 =
        (ssaConstruct chainSrc [0] (fun _ _ => false) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 1, 2]
          (liveOutName chainSrc (fun _ _ => false) (fun _ _ => 0) 0 2)) := …
-- lean/ToySsa/Construct.lean:1076-1091
theorem ssaConstruct_needs_hinit :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    ¬ (∀ x, (fun _ => 5 : SName 4 → Nat) (x, diamondSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 0 [0] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).atTop (fun _ => 5) [0]
          (topName diamondSrc diamondPhi diamondIdom 0 0) ∧
      diamondSrc.toProg.run (fun _ => 0) [0] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).run (fun _ => 5) [0]
          (liveOutName diamondSrc diamondPhi diamondIdom 0 0)) := …
-- lean/ToySsa/Construct.lean:1098-1116
theorem ssaConstruct_needs_walk_from_entry :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99)
      (x, diamondSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    ¬ Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [3] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).atTop
          (fun nm => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99) [3]
          (topName diamondSrc diamondPhi diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [3] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).run
          (fun nm => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99) [3]
          (liveOutName diamondSrc diamondPhi diamondIdom 0 3)) := …
-- lean/ToySsa/Construct.lean:1123-1139
theorem ssaConstruct_needs_hvars :
    EntryNoReachablePreds diamondSrc.cfg ∧
    ¬ (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ ([] : List Nat)) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [] diamondPhi diamondIdom).atTop (fun nm => (fun _ => 0) nm.1)
          [0, 1, 3] (topName diamondSrc diamondPhi diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [] diamondPhi diamondIdom).run (fun nm => (fun _ => 0) nm.1)
          [0, 1, 3] (liveOutName diamondSrc diamondPhi diamondIdom 0 3)) := …
-- lean/ToySsa/Construct.lean:1170-1171
theorem ssaConstruct_singleAssignment_nonvacuous :
    [0].Nodup ∧ (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).SingleAssignment := …
```

Out-of-SSA translation (from `lean/ToySsa/OutOfSsa.lean`):

```lean
-- lean/ToySsa/OutOfSsa.lean:82-85
theorem naiveOutOfSsa_parallel_run_eq_outCopies {V : Type} [DecidableEq V] (P : SsaProg V n)
    (h : PhiPredsSingleSucc P) {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path)
    (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).run σ path = execBody (outCopies .parallel P b) (P.run σ path) := …
-- lean/ToySsa/OutOfSsa.lean:226-229
theorem execBody_sequential_needs_seqSafe :
    ¬ SeqSafe ([(0, 1), (1, 0)] : List (Nat × Nat)) ∧
    ¬ (∀ σ : Nat → Nat, execBody (copyInstrs .sequential ([(0, 1), (1, 0)] : List (Nat × Nat))) σ =
        parCopy [(0, 1), (1, 0)] σ) := …
-- lean/ToySsa/OutOfSsa.lean:237
theorem execBody_sequential_hyps_nonvacuous : SeqSafe ([(2, 1), (1, 0)] : List (Nat × Nat)) := …
-- lean/ToySsa/OutOfSsa.lean:287
theorem phiPredsSingleSucc_swapSsaAB : PhiPredsSingleSucc swapSsaAB := …
-- lean/ToySsa/OutOfSsa.lean:290
theorem noCriticalEdges_swapCfg : NoCriticalEdges swapCfg := …
-- lean/ToySsa/OutOfSsa.lean:293
theorem phisOnlyAtJoins_swapSsaAB : PhisOnlyAtJoins swapSsaAB := …
-- lean/ToySsa/OutOfSsa.lean:302-304
theorem swap_parallel_correct {a b : Fin 4} {path : List (Fin 4)} (hw : Walk swapCfg a b path)
    (σ : Nat → Nat) :
    (naiveOutOfSsa .parallel swapSsaAB).atTop σ path = swapSsaAB.atTop σ path := …
-- lean/ToySsa/OutOfSsa.lean:381-386
theorem dupPhi_sequential_wrong :
    PhiPredsSingleSucc dupPhiSsa ∧ NoCriticalEdges dupCfg ∧
    (∀ (p : Fin 3), ∀ φ ∈ dupPhiSsa.phis 1, φ.2 p ≠ 2) ∧
    ¬ SeqSafe (dupPhiSsa.phiMoves 0 1) ∧ Walk dupCfg 0 1 [0, 1] ∧
    (naiveOutOfSsa .sequential dupPhiSsa).atTop (fun _ => 0) [0, 1] 2 = 20 ∧
    dupPhiSsa.atTop (fun _ => 0) [0, 1] 2 = 10 := …
-- lean/ToySsa/OutOfSsa.lean:413-418
theorem chainPhi_order_matters :
    PhiPredsSingleSucc chainPhiAB ∧ ¬ SeqSafe (chainPhiAB.phiMoves 2 1) ∧
    (chainPhiAB.atTop (fun _ => 0) swapWalk 3, chainPhiAB.atTop (fun _ => 0) swapWalk 4) = (5, 1) ∧
    ((naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk 3,
      (naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk 4) = (5, 5) ∧
    (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) := …
-- lean/ToySsa/OutOfSsa.lean:430-432
theorem windmill_sequential_no_temp (σ : Nat → Nat) :
    execBody [.assign 2 (.var 0), .assign 0 (.var 1), .assign 1 (.var 2)] σ =
      parCopy [(0, 1), (1, 0), (2, 0)] σ := …
-- lean/ToySsa/OutOfSsa.lean:473
theorem not_noCriticalEdges_lostCfg : ¬ NoCriticalEdges lostCfg := …
-- lean/ToySsa/OutOfSsa.lean:482
theorem not_phiPredsSingleSucc_lostSsa : ¬ PhiPredsSingleSucc lostSsa := …
-- lean/ToySsa/OutOfSsa.lean:547
theorem lostLoopWalk_walk (k : Nat) : Walk lostCfg 0 2 (lostLoopWalk k) := …
-- lean/ToySsa/OutOfSsa.lean:561
theorem lostSplitWalk_walk (k : Nat) : Walk lostSplitCfg 0 2 (lostSplitWalk k) := …
-- lean/ToySsa/OutOfSsa.lean:600
theorem noCriticalEdges_lostSplitCfg : NoCriticalEdges lostSplitCfg := …
-- lean/ToySsa/OutOfSsa.lean:610-616
theorem naiveOutOfSsa_needs_phiPredsSingleSucc :
    ¬ PhiPredsSingleSucc lostSsa ∧ Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .parallel lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:623-629
theorem naiveOutOfSsa_needs_parallel :
    PhiPredsSingleSucc swapSsaAB ∧ Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk =
          swapSsaAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .sequential swapSsaAB).run (fun _ => 0) swapWalk =
            swapSsaAB.run (fun _ => 0) swapWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:636-643
theorem naiveOutOfSsa_needs_walk :
    PhiPredsSingleSucc swapSsaAB ∧ NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧
    ¬ ((naiveOutOfSsa .parallel swapSsaAB).atTop (fun _ => 0) [0, 3] =
          swapSsaAB.atTop (fun _ => 0) [0, 3] ∧
        ((∀ c, swapCfg.edge 3 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .parallel swapSsaAB).run (fun _ => 0) [0, 3] =
            swapSsaAB.run (fun _ => 0) [0, 3])) := …
-- lean/ToySsa/OutOfSsa.lean:701-708
theorem naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins :
    NoCriticalEdges branchPhiCfg ∧ ¬ PhisOnlyAtJoins branchPhiSsa ∧
    Walk branchPhiCfg 0 2 [0, 2] ∧
    ¬ ((naiveOutOfSsa .parallel branchPhiSsa).atTop (fun _ => 0) [0, 2] =
          branchPhiSsa.atTop (fun _ => 0) [0, 2] ∧
        ((∀ c, branchPhiCfg.edge 2 c = true → branchPhiSsa.phis c = []) →
          (naiveOutOfSsa .parallel branchPhiSsa).run (fun _ => 0) [0, 2] =
            branchPhiSsa.run (fun _ => 0) [0, 2])) := …
-- lean/ToySsa/OutOfSsa.lean:717-723
theorem naiveOutOfSsa_noCriticalEdges_needs_noCriticalEdges :
    ¬ NoCriticalEdges lostCfg ∧ PhisOnlyAtJoins lostSsa ∧ Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .parallel lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:728-734
theorem naiveOutOfSsa_noCriticalEdges_needs_parallel :
    NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧ Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk =
          swapSsaAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .sequential swapSsaAB).run (fun _ => 0) swapWalk =
            swapSsaAB.run (fun _ => 0) swapWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:740-742
theorem naiveOutOfSsa_hyps_nonvacuous :
    PhiPredsSingleSucc swapSsaAB ∧ NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧
    Walk swapCfg 0 3 [0, 1, 2, 1, 3] ∧ (∀ c, swapCfg.edge 3 c = true → swapSsaAB.phis c = []) := …
-- lean/ToySsa/OutOfSsa.lean:748-750
theorem naiveOutOfSsa_sequential_hyps_nonvacuous :
    PhiPredsSingleSucc chainPhiBA ∧ (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) ∧
    Walk swapCfg 0 3 [0, 1, 2, 1, 3] ∧ (∀ c, swapCfg.edge 3 c = true → chainPhiBA.phis c = []) := …
-- lean/ToySsa/OutOfSsa.lean:755
theorem swap_temp_hyps_nonvacuous : Walk swapCfg 0 1 swapWalk ∧ (2 : Nat) ≠ 4 := …
-- lean/ToySsa/OutOfSsa.lean:760-762
theorem swap_temp_needs_ne_temp :
    Walk swapCfg 0 1 swapWalk ∧ ¬ ((4 : Nat) ≠ 4) ∧
    swapTempProg.atTop (fun _ => 0) swapWalk 4 ≠ swapSsaAB.atTop (fun _ => 0) swapWalk 4 := …
-- lean/ToySsa/OutOfSsa.lean:767-769
theorem swap_temp_needs_walk :
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧ (2 : Nat) ≠ 4 ∧
    swapTempProg.atTop (fun _ => 0) [0, 3] 2 ≠ swapSsaAB.atTop (fun _ => 0) [0, 3] 2 := …
-- lean/ToySsa/OutOfSsa.lean:774-781
theorem naiveOutOfSsa_sequential_needs_phiPredsSingleSucc :
    ¬ PhiPredsSingleSucc lostSsa ∧ (∀ p b, SeqSafe (lostSsa.phiMoves p b)) ∧
    Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .sequential lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .sequential lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:787-794
theorem naiveOutOfSsa_sequential_needs_seqSafe :
    PhiPredsSingleSucc chainPhiAB ∧ ¬ (∀ p b, SeqSafe (chainPhiAB.phiMoves p b)) ∧
    Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk =
          chainPhiAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → chainPhiAB.phis c = []) →
          (naiveOutOfSsa .sequential chainPhiAB).run (fun _ => 0) swapWalk =
            chainPhiAB.run (fun _ => 0) swapWalk)) := …
-- lean/ToySsa/OutOfSsa.lean:802-809
theorem naiveOutOfSsa_sequential_needs_walk :
    PhiPredsSingleSucc chainPhiBA ∧ (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) ∧
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧
    ¬ ((naiveOutOfSsa .sequential chainPhiBA).atTop (fun _ => 0) [0, 3] =
          chainPhiBA.atTop (fun _ => 0) [0, 3] ∧
        ((∀ c, swapCfg.edge 3 c = true → chainPhiBA.phis c = []) →
          (naiveOutOfSsa .sequential chainPhiBA).run (fun _ => 0) [0, 3] =
            chainPhiBA.run (fun _ => 0) [0, 3])) := …
-- lean/ToySsa/OutOfSsa.lean:817-822
theorem naiveOutOfSsa_sequential_run_needs_exit :
    PhiPredsSingleSucc lostNoExitSsa ∧ (∀ p b, SeqSafe (lostNoExitSsa.phiMoves p b)) ∧
    Walk lostNoExitCfg 0 1 [0, 1, 1] ∧
    ¬ (∀ c, lostNoExitCfg.edge 1 c = true → lostNoExitSsa.phis c = []) ∧
    (naiveOutOfSsa .sequential lostNoExitSsa).run (fun _ => 0) [0, 1, 1] 1 = 3 ∧
    lostNoExitSsa.run (fun _ => 0) [0, 1, 1] 1 = 2 := …
```

## Boundaries

### Non-claims

These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about any production compiler. Per card, what the result does not show:

**1. `join-subset-iterated-df-of-all-reachable`**

- Does not say DF+(S) is contained in J(S); the package proves that inclusion under the additional hypotheses that S contains the entry and no edge enters the entry (iterated-df-subset-join-of-entry-mem), each tight there.
- Says nothing about CFGs with unreachable nodes, where the inclusion fails (Toy.Ssa.join_subset_iteratedDF_needs_allReachable).
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.
- Dominance is the semantic all-walks notion; no dominator-tree algorithm is modeled or verified.

**2. `iterated-df-subset-join-of-entry-mem`**

- Does not apply when S omits the entry (Toy.Ssa.iteratedDF_subset_join_needs_entry_mem).
- Does not cover CFGs with an edge into the entry or with unreachable nodes.
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.
- Dominance is the semantic all-walks notion; no dominator-tree algorithm is modeled or verified.

**3. `join-eq-iterated-df-of-entry-mem`**

- States equality of node sets; it says nothing about the cost of computing either set.
- Not claimed when S omits the entry: for such S the package proves J(S) within DF+(S) given reachability (join-subset-iterated-df-of-all-reachable), and DF+(S) within J(S) fails on the 2-node CFG 0 -> 1 with a self-loop on 1 (Toy.Ssa.iteratedDF_subset_join_needs_entry_mem).
- Characterizes unpruned placement; liveness-pruned SSA (as computed by an iterated dominance frontier restricted to live-in blocks) places phis on a subset of DF+(S), omitting blocks where the variable is dead, and is not covered.
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.

**4. `join-union-join-subset-join`**

- Does not say J(S) is computed by any particular algorithm.
- Convergence is Cytron et al.'s index-based condition; its equivalence with disjointness of the two walks without their last nodes is proved here as the auxiliary lemma Toy.Ssa.inJoin_iff_preWalks (used in the proof, not a separate card; the Isabelle Formal_SSA development proves the same equivalence as lemma pathsConverge'). Bilardi and Pingali's 'intersecting only at v' (paths) is not formalized.
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.

**5. `single-reaching-def-of-join-closed`**

- 'Single reaching definition' means at most one: SingleReachingDef holds vacuously at blocks reached by no definition (Toy.Ssa.srd_at_most_one_example); existence is proved when the entry is a definition point (exists-reaches-top-of-entry-mem) and fails without it on the 3-node chain with D = P = empty (Toy.Ssa.exists_reachesTop_needs_entry_mem).
- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled.
- Does not say a join-closed placement is minimal; extra join-closed phis are allowed.
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.

**6. `join-closed-of-single-reaching-def`**

- 'Single reaching definition' means at most one: SingleReachingDef holds vacuously at blocks reached by no definition (Toy.Ssa.srd_at_most_one_example); existence is proved when the entry is a definition point (exists-reaches-top-of-entry-mem) and fails without it on the 3-node chain with D = P = empty (Toy.Ssa.exists_reachesTop_needs_entry_mem).
- SingleReachingDef exempts the entry block: when edges enter the entry, two definitions can reach its top while SingleReachingDef holds (Toy.Ssa.srd_entry_exemption_example); the exemption-free SingleReachingDefAll fails there.
- SingleReachingDef G D P is not monotone in P: on the diamond with D = {0}, J(D) is empty and contained in P = {1}, yet the extra phi at 1 makes two definitions reach 3 (Toy.Ssa.srd_not_monotone_diamond); extra phis preserve SingleReachingDef whenever the placement stays join-closed (J(D u P) within P; single-reaching-def-of-join-closed), and under EntryNoPreds (or for SingleReachingDefAll) only then (join-closed-of-single-reaching-def); without EntryNoPreds an extra phi can satisfy SingleReachingDef while the placement is not join-closed (Toy.Ssa.extra_phi_srd_without_joinClosed_when_entryPred).
- The CFG is a simple directed graph (edge : Fin n -> Fin n -> Bool): parallel edges between the same two blocks (such as switch arms with one target) are collapsed.

**7. `single-reaching-def-at-join`**

- Does not say J(D) is computable by dominance frontiers in every CFG: the package proves J(D) = DF+(D) under reachability, the entry in D, and no edge into the entry (join-eq-iterated-df-of-entry-mem), each hypothesis tight there.
- 'Single reaching definition' means at most one: SingleReachingDef holds vacuously at blocks reached by no definition (Toy.Ssa.srd_at_most_one_example); existence is proved when the entry is a definition point (exists-reaches-top-of-entry-mem) and fails without it on the 3-node chain with D = P = empty (Toy.Ssa.exists_reachesTop_needs_entry_mem).
- SingleReachingDef G D P is not monotone in P: on the diamond with D = {0}, J(D) is empty and contained in P = {1}, yet the extra phi at 1 makes two definitions reach 3 (Toy.Ssa.srd_not_monotone_diamond); extra phis preserve SingleReachingDef whenever the placement stays join-closed (J(D u P) within P; single-reaching-def-of-join-closed), and under EntryNoPreds (or for SingleReachingDefAll) only then (join-closed-of-single-reaching-def); without EntryNoPreds an extra phi can satisfy SingleReachingDef while the placement is not join-closed (Toy.Ssa.extra_phi_srd_without_joinClosed_when_entryPred).
- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled.

**8. `single-reaching-def-at-iterated-df-of-all-reachable`**

- Does not claim DF+(D) is the smallest correct placement (minimality is join-subset-of-single-reaching-def).
- The theorem needs no entry hypothesis because SingleReachingDef exempts the entry block; SSA construction (ssa-construct-preserves-values) assumes that no reachable block has an edge into the entry, a hypothesis that is tight there (Toy.Ssa.ssaConstruct_needs_entryNoReachablePreds); adding a fresh pre-entry block is the usual way to meet it (not proved here).
- SingleReachingDef exempts the entry block: when edges enter the entry, two definitions can reach its top while SingleReachingDef holds (Toy.Ssa.srd_entry_exemption_example); the exemption-free SingleReachingDefAll fails there.
- Characterizes unpruned placement; liveness-pruned SSA (as computed by an iterated dominance frontier restricted to live-in blocks) places phis on a subset of DF+(S), omitting blocks where the variable is dead, and is not covered.
- 'Single reaching definition' means at most one: SingleReachingDef holds vacuously at blocks reached by no definition (Toy.Ssa.srd_at_most_one_example); existence is proved when the entry is a definition point (exists-reaches-top-of-entry-mem) and fails without it on the 3-node chain with D = P = empty (Toy.Ssa.exists_reachesTop_needs_entry_mem).

**9. `exists-reaches-top-of-entry-mem`**

- Models variables with an implicit initial definition at the entry; a compiler that gives uninitialized variables an undefined value along definition-free paths (instead of an initial definition at the entry) corresponds (as a modeling remark) to D without the entry, where existence of a reaching definition can fail (Toy.Ssa.exists_reachesTop_needs_entry_mem).
- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled.

**10. `exists-unique-reaches-top-at-iterated-df`**

- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled.
- Characterizes unpruned placement; liveness-pruned SSA (as computed by an iterated dominance frontier restricted to live-in blocks) places phis on a subset of DF+(S), omitting blocks where the variable is dead, and is not covered.
- Uniqueness is among block-level definition points; intra-block definitions are handled by renaming (ssa-construct-preserves-values).

**11. `reaches-top-iff-nearest-sdom-def-at-iterated-df`**

- The entry need not be in D and b may be the entry: both sides are then empty when nothing strictly dominates b.
- Says nothing about the stack-based renaming algorithm; the renaming source is declarative.
- Reaching definitions are per block (the value leaving a definition block); the order of instructions inside a block and the liveness of upward-exposed uses are not modeled.

**12. `join-subset-of-single-reaching-def`**

- Under EntryNoPreds, J(D) within P is necessary for SingleReachingDef (this result) but not sufficient: P must also be join-closed for the new phi definitions (Toy.Ssa.srd_not_monotone_diamond).
- 'Single reaching definition' means at most one: SingleReachingDef holds vacuously at blocks reached by no definition (Toy.Ssa.srd_at_most_one_example); existence is proved when the entry is a definition point (exists-reaches-top-of-entry-mem) and fails without it on the 3-node chain with D = P = empty (Toy.Ssa.exists_reachesTop_needs_entry_mem).
- SingleReachingDef exempts the entry block: when edges enter the entry, two definitions can reach its top while SingleReachingDef holds (Toy.Ssa.srd_entry_exemption_example); the exemption-free SingleReachingDefAll fails there.
- Characterizes unpruned placement; liveness-pruned SSA (as computed by an iterated dominance frontier restricted to live-in blocks) places phis on a subset of DF+(S), omitting blocks where the variable is dead, and is not covered.

**13. `ssa-construct-preserves-values`**

- Static single assignment of the output is a separate result (ssa-construct-single-assignment); strictness (every use dominated by its definition) is not stated or proved here.
- The hypothesis hnp allows edges into the entry from unreachable blocks and from no reachable block; in an acyclic CFG every edge into the entry comes from an unreachable block (Toy.Ssa.entryNoReachablePreds_of_acyclic), which is why the acyclic corollary needs no entry hypothesis.
- The tightness witness for hphi_within uses a variable outside vars (Toy.Ssa.ssaConstruct_needs_phi_within); whether extra phis for variables in vars (for example maximal placement at every non-entry block) also preserve values is not established here (not proved here).
- Liveness-pruned placements, which drop phis inside DF+ for dead variables, violate hphi_cover and are not covered; neither are copy folding or later SSA optimizations.
- Branch conditions are not modeled: every walk is an execution; a procedure exit is observed through conclusion (2) at the last block of a walk; there is no separate exit semantics.
- Existence, for an arbitrary program, of a renaming source satisfying hidom is not proved here (not proved here); the non-vacuity witnesses exhibit one on concrete programs, including one with an unreachable block.
- Not a model of LLVM mem2reg, Cranelift, or rustc; any such connection is a separate derived (modeling bridge) claim.

**14. `ssa-construct-single-assignment`**

- States syntactic single assignment; strictness (each use dominated by its definition) is not stated.
- Holds for every placement and renaming source, so it says nothing about value preservation (ssa-construct-preserves-values).

**15. `naive-out-of-ssa-parallel-eq-of-phi-preds-single-succ`**

- Returns, halts, and exceptional exits must be modeled as edges to an explicit exit block: conclusion (b) is stated for the end of a block none of whose successors carries phis, and without an exit edge the naive translation's store at the end of a phi-predecessor differs (Toy.Ssa.naiveOutOfSsa_run_needs_exit; the exact relation, Toy.Ssa.naiveOutOfSsa_parallel_run_eq_outCopies, states that under PhiPredsSingleSucc, along every walk with last block b, the parallel naive translation's store at the end of b equals the SSA program's store there followed by outCopies .parallel P b, the copies appended to b).
- Relaxing full-store equality to live variables would excuse phis at single-predecessor blocks whose destinations are dead on the other branch (not proved here), but not critical edges: lostSsa is already strict SSA with x2 live at the exit and still miscompiles (Toy.Ssa.lostCopy_naive_miscompiles); approaches that avoid edge splitting, such as conventional SSA (non-interfering phi-related live ranges) or saving live phi destinations in temporaries, are not formalized here (not proved here).
- Assumes a simple CFG and omits branch instructions: parallel edges from p to b with different phi operands, and terminators at the end of p that read variables overwritten by the appended copies, are not modeled.
- The naive translation appends the copies for all successors of p one after another; under PhiPredsSingleSucc all but at most one of them are empty.
- A machine without a parallel-copy instruction executes a parallel copy as a sequence of moves (treated by naive-out-of-ssa-sequential-eq-of-seq-safe and swap-temp-sequence-correct); register allocation and coalescing are not covered.

**16. `naive-out-of-ssa-parallel-eq-of-no-critical-edges`**

- Without PhisOnlyAtJoins the statement as commonly phrased is false in this full-store sense (Toy.Ssa.naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins).
- Does not say critical edges can always be split in a real compiler; indirect branches and values defined by branch instructions are known obstacles in practice (not proved here).
- Returns, halts, and exceptional exits must be modeled as edges to an explicit exit block: conclusion (b) is stated for the end of a block none of whose successors carries phis, and without an exit edge the naive translation's store at the end of a phi-predecessor differs (Toy.Ssa.naiveOutOfSsa_run_needs_exit; the exact relation, Toy.Ssa.naiveOutOfSsa_parallel_run_eq_outCopies, states that under PhiPredsSingleSucc, along every walk with last block b, the parallel naive translation's store at the end of b equals the SSA program's store there followed by outCopies .parallel P b, the copies appended to b).
- Relaxing full-store equality to live variables would excuse phis at single-predecessor blocks whose destinations are dead on the other branch (not proved here), but not critical edges: lostSsa is already strict SSA with x2 live at the exit and still miscompiles (Toy.Ssa.lostCopy_naive_miscompiles); approaches that avoid edge splitting, such as conventional SSA (non-interfering phi-related live ranges) or saving live phi destinations in temporaries, are not formalized here (not proved here).
- Assumes a simple CFG and omits branch instructions: parallel edges from p to b with different phi operands, and terminators at the end of p that read variables overwritten by the appended copies, are not modeled.

**17. `naive-out-of-ssa-sequential-eq-of-seq-safe`**

- The hypothesis hs is not guarded by P.cfg.edge p b = true: it requires SeqSafe (P.phiMoves p b) for every pair of blocks (p, b), including pairs that are not CFG edges, for which SsaProg.phis still supplies operands (SsaProg.phis b : List (V × (Fin n → V)) gives each phi a total operand function). Whether the conclusion still holds when hs is restricted to CFG edges (P.cfg.edge p b = true) is not established here (not proved here).
- SeqSafe is a sufficient condition; whether a weaker condition suffices (for example, when the values of the reordered copies happen to coincide) is not examined (not proved here).
- Distinct phi destinations are part of SeqSafe and cannot be dropped: two phis for the same destination give the first operand under parallel copies but the last under sequential copies (Toy.Ssa.dupPhi_sequential_wrong).
- A phi order can be SeqSafe even when another order of the same phis is not (Toy.Ssa.chainPhi_order_matters); cyclic copies such as the swap admit no SeqSafe order, because the first move of any order writes a source of a later move (not proved here as a general theorem; the swap list [(0, 1), (1, 0)] is shown not SeqSafe in Toy.Ssa.execBody_sequential_needs_seqSafe).
- Returns, halts, and exceptional exits must be modeled as edges to an explicit exit block: conclusion (b) is stated for the end of a block none of whose successors carries phis, and without an exit edge the naive translation's store at the end of a phi-predecessor differs (Toy.Ssa.naiveOutOfSsa_run_needs_exit for parallel copies and Toy.Ssa.naiveOutOfSsa_sequential_run_needs_exit for sequential copies; the exact relation, Toy.Ssa.naiveOutOfSsa_parallel_run_eq_outCopies, states that under PhiPredsSingleSucc, along every walk with last block b, the parallel naive translation's store at the end of b equals the SSA program's store there followed by outCopies .parallel P b, the copies appended to b).

**18. `naive-out-of-ssa-block-end-needs-exit-edge`**

- Does not say the naive translation is wrong once the return is modeled as an edge to an exit block: then the loop block has two successors, the back edge is critical, and the result is the ordinary lost-copy problem (lost-copy-naive-miscompiles), fixed by edge splitting (lost-copy-split-fixes).
- One concrete program and walk.

**19. `swap-sequential-either-order-wrong`**

- Sequential copies in phi order do realize the parallel copy of one move list when no destination in the list is the destination or the source of a later move (SeqSafe, Toy.Ssa.execBody_sequential_eq_parCopy); combined with PhiPredsSingleSucc, SeqSafe of the phi moves for every pair of blocks (p, b), including pairs that are not CFG edges, makes the sequential naive translation exact (naive-out-of-ssa-sequential-eq-of-seq-safe). Without distinct destinations this fails (Toy.Ssa.dupPhi_sequential_wrong), and without PhiPredsSingleSucc it fails even with a single phi, whose moves are SeqSafe for every pair of blocks (Toy.Ssa.naiveOutOfSsa_sequential_needs_phiPredsSingleSucc).
- Does not imply that every cyclic copy needs a temporary: on one instance where a cycle vertex also feeds a destination outside the cycle, (a2, b2, c2) := (b2, a2, a2), three plain assignments suffice (Toy.Ssa.windmill_sequential_no_temp); hardware exchange instructions are not modeled.
- With a1 = b1 both orders would give the right values, so the failure depends on the input values (not proved here).

**20. `swap-temp-sequence-correct`**

- One fixed program; general parallel-copy sequentialization is not restated here.
- Correctness relies on the temporary t never being read by the SSA program; a temporary live across the edge would be clobbered (not proved here).
- On one instance, a copy cycle with an outgoing tree copy, (a2, b2, c2) := (b2, a2, a2), is realized by three plain assignments without a temporary (Toy.Ssa.windmill_sequential_no_temp).

**21. `lost-copy-naive-miscompiles`**

- The miscompilation is exhibited on one program with a critical back edge and a folded copy, and splitting that edge removes it (lost-copy-split-fixes); it is not a claim that every critical edge causes one, and which features of the program are necessary for it is not examined (not proved here).
- lostSsa is already strict SSA and x2 is live at the exit, so liveness alone does not excuse the critical edge; splitting it is one fix (lost-copy-split-fixes); conventional SSA and saving the live phi destination in a temporary are fixes described in the literature (Sreedhar et al.; Briggs et al., Figure 11) and are not formalized here (not proved here).

**22. `lost-copy-split-fixes`**

- One concrete CFG; a general edge-splitting transformation over arbitrary Cfg n is not formalized.
- The compared walks have the shape entry, k + 1 loop-body runs, exit; walks bypassing the loop do not exist in this CFG, and partial walks ending inside the loop are not stated.
- Other fixes described in the literature, conventional SSA and saving the live phi destination in a temporary, are not formalized here (not proved here).

### Escape hatches

The counterexample cards exhibit failures of the naive out-of-SSA translation. Each failure disappears when the setting changes as follows, and each of these settings is backed by a proved theorem:

- Lost copy (`lost-copy-naive-miscompiles`): splitting the critical back edge (`lostCopy_split_fixes`); in general, `PhiPredsSingleSucc` with parallel copies (`naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc`).
- Swap (`swap-sequential-either-order-wrong`): parallel copies (`swap_parallel_correct`), or one temporary (`swap_temp_sequence_correct`); in general, under `PhiPredsSingleSucc`, sequential copies are exact when the phi moves for every pair of blocks `(p, b)`, including pairs that are not CFG edges, are `SeqSafe` (`naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe`).
- Block end without an exit edge (`naive-out-of-ssa-block-end-needs-exit-edge`): conclusion (b) of the out-of-SSA theorems holds at blocks none of whose successors carries φs, for example an explicit exit block with no successors.

### Tightness `unknown`

None. Every hypothesis of every card is `tight`, with a proved counterexample named in its ledger.

### Dropped or disproved statements

None. Every result listed in this report is proved, including the hypothesis-free join closure `join_union_join_subset_join` and `iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem` (and therefore `join_eq_iteratedDF_of_allReachable_of_entryNoPreds_of_entry_mem` and `singleReachingDef_at_join`, which are derived from them). No statement was found false.

### Not examined

- Existence, for an arbitrary program, of a renaming source satisfying `hidom` (the non-vacuity witnesses exhibit one on concrete programs).
- Whether extra φs for variables in `vars` (beyond `DF⁺`) preserve values.
- Strictness of the constructed SSA program (uses dominated by definitions).
- Liveness-based correctness criteria, conventional SSA, liveness-pruned placement, and out-of-SSA algorithms that avoid edge splitting; remarks about them in the cards are marked "(not proved here)".
- The cost of any algorithm: nothing here bounds the work to compute `J(S)`, `DF⁺(S)`, or the translations.

## Evidence

**Kernel check.** On 2026-11-21, `lake build` of `lean/` succeeded under Lean 4.34.1 (`lean --version`: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`), with no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the sources. The axioms of every declaration of the library were computed with Lean's `collectAxioms` and recorded in `audit/axioms.json`; every declaration depends on at most `propext`, `Classical.choice`, `Quot.sound`.

**Toolchain identity.** `leanprover/lean4` tag `v4.34.1` points to commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API `repos/leanprover/lean4/git/ref/tags/v4.34.1`, read on 2026-11-21).

**Statement hashes.** For every Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of the statement (Lean `repr` of its type) and of its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded). For a definition listed by name, the statement hash covers its type; its value is covered by the closure hash of every listed theorem whose statement uses it. The table lists each name, its axioms, and both hashes.

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Acyclic` | none | `c7cd987fa6104ebe3d30fd84d88d746129a2712d80bdb182c255c8dfcb5a6a0e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `AllReachable` | none | `c7cd987fa6104ebe3d30fd84d88d746129a2712d80bdb182c255c8dfcb5a6a0e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Cfg` | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Cfg.ofEdges` | none | `4ba1d572db72e6d659c609a498e5152477f070c1c0889e9c4d7818d556107f74` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Clear` | none | `1ba21bd36bb7d95e18175ebdab345b5b2217f0667fd174a4550654adf689aa2f` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Converge` | Quot.sound, propext | `c96febd927b36686fe28f05eb059c3330465e4e81f922caa44f3d793d0a0ad64` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `CopyMode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DF` | none | `283f98902cf7f09a6dc77c57390a073ce19d322f55a2e79af6db31cd4de34b08` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Dom` | none | `091eb58943bfe89c08db7dcd008b2ab14529f87e9d82f5fe8ec45ada877d468b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `EntryNoPreds` | none | `c7cd987fa6104ebe3d30fd84d88d746129a2712d80bdb182c255c8dfcb5a6a0e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `EntryNoReachablePreds` | none | `c7cd987fa6104ebe3d30fd84d88d746129a2712d80bdb182c255c8dfcb5a6a0e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Exp` | none | `97f4baba4179aa3cf4eda9fad3557c253328e098be2ba18700f2bac9a9a1b985` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Exp.eval` | none | `6bd3b77a0d1c75364ffefed44b53744fbf1bdb9c73cb9321a3dd526ad05a8954` | `e0ee024cb554ce734e5572009dd6556044d93dcc024949f86f06283c11e90230` |
| `IDF` | none | `ce6be638905d0181cba610ad985c7a5aee3b34fb5c0ecd6f80ed7c460b1c3349` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `InJoin` | Quot.sound, propext | `5c791ebdd76239a4b608341820c466e3e303e11b0e17835c5dde8d455ddf7d02` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `InJoinPre` | none | `5c791ebdd76239a4b608341820c466e3e303e11b0e17835c5dde8d455ddf7d02` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Instr` | none | `97f4baba4179aa3cf4eda9fad3557c253328e098be2ba18700f2bac9a9a1b985` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Instr.dests` | none | `e1fcb4737bfb9483da46946e9bd6665f4454d3ae7abbdb54fc7ae0fd922ffc4d` | `2c7cd65928b2825f8f482b8ee4b731f3addbbedd15b9ebcad188f3364b0b7e09` |
| `Instr.exec` | none | `08480f4e044cf8297a74ecc95e0136164368216b66f43e53f9c2988a79dfad0a` | `2c7cd65928b2825f8f482b8ee4b731f3addbbedd15b9ebcad188f3364b0b7e09` |
| `NearestSDomDef` | none | `a3193b670ed7fe6fb50d764b85c07c41701f1e337a46d9fc60e45a177388d08c` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `NoCriticalEdges` | none | `c7cd987fa6104ebe3d30fd84d88d746129a2712d80bdb182c255c8dfcb5a6a0e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `PhiPredsSingleSucc` | none | `ea9f4e9333b304e86d1b0859563001b201df675ac3d7b741e69fac6989a89e94` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `PhisOnlyAtJoins` | none | `ea9f4e9333b304e86d1b0859563001b201df675ac3d7b741e69fac6989a89e94` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `PreWalk` | none | `571e4805be7b4437ce564b7eec765e630a8ef23cfb1221176d0bd9a17b7b3e6f` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Prog` | none | `fe3037e6e18dff0ae53bca7f34015236316274070cc26e82b25602462db29777` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Prog.atTop` | none | `e64d5b7c1633e023acc95fea16bee96c2827008da6671f9beddc0d62dc3ebc03` | `864fc965df5d443c5592ecff150f8f310a093268f18eac86a8f29b658bdc42e8` |
| `Prog.run` | none | `ca37368ff8a8e56dd45e0b65f3394b7c292a2995013ecca9ba0e2230bbd7bb5f` | `864fc965df5d443c5592ecff150f8f310a093268f18eac86a8f29b658bdc42e8` |
| `Reachable` | none | `4317a9fff5a7f42ef493c1298689dd02b031339a459e33bc90247e08a7ff2e39` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `ReachesTop` | none | `ae156e7bb96e0c056819f4084dac5dd90771f9f0a1d9a52e5a21db7f1fa5549a` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `SDom` | none | `091eb58943bfe89c08db7dcd008b2ab14529f87e9d82f5fe8ec45ada877d468b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `SName` | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SeqSafe` | none | `23df472a296b98ecb284e68b9da2d80f30eb1dc8e7f09d52d4328c95f9c58fb2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SingleReachingDef` | none | `7fcf19e039d50f8c783012754e99f89ca22a616208bb8ceca006fce646c6e436` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `SingleReachingDefAll` | none | `7fcf19e039d50f8c783012754e99f89ca22a616208bb8ceca006fce646c6e436` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `Src` | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Src.defPts` | none | `1878a1ed15786926c5c23df2b02518827ea76e0aa90a19ec80592720e3240188` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `Src.toProg` | none | `2ff58f0fb68d50bd87f795520607afc019888f835c031cad761f9f9f5d423dd2` | `c3f15ec3b4efa27586fa928e0274af81eda22472ba83cfc9b267cfec6254921a` |
| `SsaProg` | none | `fe3037e6e18dff0ae53bca7f34015236316274070cc26e82b25602462db29777` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SsaProg.SingleAssignment` | none | `ea9f4e9333b304e86d1b0859563001b201df675ac3d7b741e69fac6989a89e94` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.atTop` | propext | `288f29739a1659611afd2f473927381b5c3798d55eaedcd89fb6888800090929` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.defsAt` | none | `c0a58e5382539946623fbcbaa451970c8c05f1f021481f549bc126d8b62f29ff` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.enter` | none | `d09c676ad7466b05749f0df99047d0202698fa8236b490848b8fa298b5cb2b32` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.phiMoves` | none | `c17207bbcdb5706adbc6ddca12530124bb910dac672d109730b363347daf7f1b` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.run` | none | `5ed75b135f3c5eead23ed429ed99eec01e11e0817aeb462a1ca61cec8ed22fdd` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `SsaProg.runFrom` | none | `d32c6c4216671fafd52583f808d8d1f12f000131bf3d41aa1ed3a58b80ee1597` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `Walk` | none | `95b98cadade8b5b8501054fab450c579acee1adeb930a86c90b72c2ef0576b5e` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `acyclicEntryPredCfg` | propext | `865a8530ac6c30a9967c42c83012dea2447be8d00bc8a68bc037bc28e18b875b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `acyclicEntryPredSrc` | propext | `4ec4cb082f4d2b8ddef9e8edb7ee6ac963863c2ecf3947b5b86732ce73d52060` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `acyclic_diamond` | Quot.sound, propext | `5845f3f8b14bcd666e62dc755ed9e33b436566cc3838db2b11d1be967ffe6e6b` | `dc0341fdcef5951d70642c82a79e761c4ef74d99553df136a020ff9c02c417ad` |
| `allReachable_diamond` | propext | `5aea77a8ca38247eefe0e69ce08a942f7207f423e1570f3d6c01bbee41777f0a` | `36c5ccafc296aee8b64b234dcc577b40712f8051256e5ad0174e7afe4e2d77f7` |
| `allReachable_nonvacuous` | propext | `5aea77a8ca38247eefe0e69ce08a942f7207f423e1570f3d6c01bbee41777f0a` | `36c5ccafc296aee8b64b234dcc577b40712f8051256e5ad0174e7afe4e2d77f7` |
| `backToEntry2` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `branchPhiCfg` | propext | `865a8530ac6c30a9967c42c83012dea2447be8d00bc8a68bc037bc28e18b875b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `branchPhiSsa` | propext | `c4bd619f5c4e6e848a75a3db70f6197e957686cae37ac92064e87511a14664aa` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `chain3` | propext | `865a8530ac6c30a9967c42c83012dea2447be8d00bc8a68bc037bc28e18b875b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `chainPhiAB` | propext | `d1f251ce376a7120c53a86b4f2ecfb84142ca6e364853b00e53082d01517054d` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `chainPhiBA` | propext | `d1f251ce376a7120c53a86b4f2ecfb84142ca6e364853b00e53082d01517054d` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `chainPhi_order_matters` | propext | `707ab35a4a1e5e762a916f882109e6cc39fbbcf425af738d15b65fe64e043542` | `c327a53c49c63616dc76772771c5e07d8f852aab8d046e702c2b158a157cf295` |
| `chainSrc` | propext | `4ec4cb082f4d2b8ddef9e8edb7ee6ac963863c2ecf3947b5b86732ce73d52060` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `copyInstrs` | none | `f5be766e12c0252880c64f4e3ccd3c8c1d029280329c242c096f9d9398d298b0` | `b701dfad7fbe86ee12605e35551d13852005a1a7e76f522bbb574ea7cb2b11e5` |
| `df_example` | Quot.sound, propext | `57997c6afcb897c6232b700fba77cadf481a6381d39c2d03b548c93b96998a08` | `45d4ec0423ceeabd79615587117c72a4884b60d1c1f6e5f835fc065b82bce431` |
| `df_loop_example` | Quot.sound, propext | `58caaf5bdabf83d33891ee1c89553e508d669dea1b4e4618ed1bdbacedccc1f8` | `4919ca5112390f0ea040a476bf00de14082bb514ec7f1986dba9ae2025893dc7` |
| `df_preWalks_of_allReachable_of_entryNoPreds` | Classical.choice, Quot.sound, propext | `f67a7d6380e51913edb482db570136eabeccb5558f6ecbaaabd80689d8d1cb0f` | `3a61de9a2d66d4e02f1e379ff4fbb83811fd2007acec5f476a7ca85d55747aeb` |
| `diamond` | propext | `ba928c7f1845a80f04b6e926bb1ea117f67b11ac542fdae976d23a6b1813cd65` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `diamondIdom` | propext | `87ab45c02f74295a4f871c92f7e0db111e12036d5e4994b9f6a79c9815ea490f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `diamondPhi` | propext | `2d7e0e633ce645fd7f67d49860bdefe8869514de1624c3d8f7f034990e45d5b9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `diamondPhiSpurious` | propext | `2d7e0e633ce645fd7f67d49860bdefe8869514de1624c3d8f7f034990e45d5b9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `diamondSrc` | propext | `496d4289978e38c349856d729c2f68796b0c454992b8c739c5afc073ce6bdbfa` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `dom_chain_example` | Quot.sound, propext | `2f4feda90d6b87ad51f578a2f0a545172a96d29ac0096ace84f1c40ce8b8c252` | `a88640fa0c77b1678a55925e75babdafdb6f00975f4ac97f78bcd127ae9d438f` |
| `dom_example` | Quot.sound, propext | `304ba632629039c3993dec5bc66a5e61602015b1ce421470ea8560acbe257fce` | `31a095ce24a7593a7b8667c312c6dcdb430f140161bb7b2df5d6fe72cda88cd1` |
| `dupCfg` | propext | `865a8530ac6c30a9967c42c83012dea2447be8d00bc8a68bc037bc28e18b875b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `dupPhiSsa` | propext | `c4bd619f5c4e6e848a75a3db70f6197e957686cae37ac92064e87511a14664aa` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `dupPhi_sequential_wrong` | propext | `4e24ae7dc793e32f105b916f4001758ef0f926c432bbcc727b142ee2fad4b310` | `25cdadc87c1d5b22a607f61167aa98b1214e621b80ed65a1121b08caf902d53f` |
| `entryCycle2` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `entryLoop1` | propext | `0539cdfaec0afed3c8ae8424537f2349b59d7e5e25d82e00d2121fb9f0cacab3` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `entryLoopSrc` | propext | `45cda09ca9411c3a3e86e49226fc40bdd793b54cc8d98b342dd083d7b91427f9` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `entryNoPreds_diamond` | propext | `f6a8d2765bad9209c6ff67a77e940c4a712375356b13127c4049a54f28798a0c` | `79223a1b243d7e40f76aa9516ddff58375e37e9232317a5a89a08a3ee8de3244` |
| `entryNoReachablePreds_diamond` | propext | `f3ada0c9918b3cbd61985c106db2a3e44cf6b3c9eb89c0fd4b1cf882d60a7247` | `e898e65ff643db578fa92519f678b16393e8199aa0682ceb8df97e712a14ad33` |
| `entryNoReachablePreds_of_acyclic` | Quot.sound, propext | `bb83ea3332753112690a045024e4f6aba08bd1426461fef89515ac618cd72830` | `3e9f02f2f45373bfca5b56799b82eb4b8dab3b5c461f48a1bde3107f34cc8b2a` |
| `epIdom` | propext | `21a82f8354548cee24653683a69b7c7068ebdf4365cbf13fd74658059e90b726` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `epPhi` | propext | `9c73172ed41b1c8f9e984df664e0259284345fe61aaeea3484bf336a5e5b7904` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `execBody` | none | `c1b649845bdaceaa824be23bd07a453b1c9262f6ba51c84642a99e0b80e417c2` | `2c7cd65928b2825f8f482b8ee4b731f3addbbedd15b9ebcad188f3364b0b7e09` |
| `execBody_sequential_eq_parCopy` | Quot.sound, propext | `f875992329e7f36c0e6b1d68eae9679ce50970b91675245b7523d8d0718dae28` | `379e1350a4d4b49e1add518c0c881c8c58fa6431425b1def6e9883917f56e081` |
| `execBody_sequential_hyps_nonvacuous` | propext | `7663650443cc0f3347f0ba8411ae3ff76ec24ad7c1facc11ec0e634fb01c7401` | `11323bdd75d79ea912e77e9398caa85e41507494ce00902d6d007a6b1eb780e1` |
| `execBody_sequential_needs_seqSafe` | propext | `f483e4efbea48de3d4b62981316e720057531a132ed05a6f666f016e795aa846` | `379e1350a4d4b49e1add518c0c881c8c58fa6431425b1def6e9883917f56e081` |
| `existsUnique_hyps_nonvacuous` | Quot.sound, propext | `3dc8d6fb4d5ad755fbfa9e90da356681c5a264b218b09e65862d3963b5e10b1d` | `29b7a996a2c7a6a39c4ede6a2949274b9e02aa48a824778574eb66a75a314cbc` |
| `existsUnique_needs_allReachable` | Quot.sound, propext | `b97639f25aef76ded6e9140edb2b9dbdead76e3a5162216ef87b0e17010eff93` | `7861b7079cd7978f5d2a277a2752559eb2d8dfbb82f774101fd77f1a540821ca` |
| `existsUnique_needs_entry_mem` | propext | `1783fd31198e85a8a47b3f9757c415aa616ea4754222abec411cba348e78b83e` | `705a916ab248fe26a009f4a62095ad704a5ae65adc6f34e51e2fe5e93a9dbfb0` |
| `existsUnique_needs_ne_entry` | Quot.sound, propext | `99bc4965d4cdf99375a1a4fabb003160e2a26b6cc32640fcb053df3d9c949e78` | `b37aa091f8a6258b81106355f84e98e2fc0ef01197c851fc3aedd79f940a2ccb` |
| `existsUnique_needs_not_idf` | Quot.sound, propext | `54b5cb1b23ce6c1dcc63e98d1469ad9a7f24e473e57979d091459c7c7bbb2bc9` | `b37aa091f8a6258b81106355f84e98e2fc0ef01197c851fc3aedd79f940a2ccb` |
| `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry` | Classical.choice, Quot.sound, propext | `a0e50a179f46ce4a6a5489a0bce1c5d93526af1b0b0409a0f645338c9f1a5ce5` | `cf9460aad19186c10f339576b1092150517cfbe9970cfd5b7f6f23b3ba2bf1e9` |
| `exists_reachesTop_hyps_nonvacuous` | propext | `9c959af124dab7da7f90839a2df6e74a80ed24dbbed8e1d0cf16cee90f6a9bac` | `3e06eebc8aac570f11a0bd5148a16ca93bba4bad7a09b2473b50e4ef8c04805f` |
| `exists_reachesTop_needs_entry_mem` | propext | `e8c4883ce1a0103cd06c6756184a88da982bd7a349cae53f00bd383d34b9d01a` | `2927f6b52b845ac98cc5397cec633c136167bb3a43162f8ec21e76ea217204ec` |
| `exists_reachesTop_needs_ne_entry` | propext | `a8a46d9934875349a1cd780ece954ee87e186e8f19429eaf1c23e11f6b0c9193` | `e3f65414e4c415ddcf3533bc19c6cdd574377ae95ad0f4c96a9cdfccc71f813a` |
| `exists_reachesTop_needs_reachable` | propext | `067129063d350189a60e8c60c496e3d5c1d6d9e7a19c7eb8972d95ff46abceb5` | `5dc78badde9fbd04cf2269e0cf9a63eeb25313569ddb4da1ded42e4e3ef42028` |
| `exists_reachesTop_of_entry_mem` | Classical.choice, Quot.sound, propext | `c1bd6653080b8ca4d1135e96f2a3398d1b82e13c40963f889312759ef9f5fa7e` | `76fc8f4c4c38b3ecb2d73b1009f6e89c58bb90296b2726851132ad7f48f8c9ba` |
| `extra_phi_srd_without_joinClosed_when_entryPred` | Quot.sound, propext | `11abc96bb7e611c6d613c5cdf2a4b7e291ca8d8a3a190e8a2c9e96e98e6ac9ef` | `ccb7d9aa416cccc5e28534db21c8125081af7d8c1ec313a304dc6acfb15b7e74` |
| `idf_iterates_example` | Quot.sound, propext | `8262068e3e704ba58b6777290f00f0086dc6015b255a7e0db7b8a2f3da53cb88` | `648296c2f0b7f9a7a11000d0d7091cc67b2e51b978f66d5135f1972c86418ca4` |
| `inJoinPre_of_insert_join` | Classical.choice, Quot.sound, propext | `63dd0216957781e72d47ec20a35c88f86bd75001f52844c3853554e8801402b0` | `9f307c083f0ef8d6f94f5d983a02f41e1f0ebe42e95ea5b924140507beb986ec` |
| `inJoinPre_of_join_point` | Classical.choice, Quot.sound, propext | `2ed98145c4cbff287dbe8ad463c245222c8a8a1b9dc48276c88af4857f5dde0b` | `9f307c083f0ef8d6f94f5d983a02f41e1f0ebe42e95ea5b924140507beb986ec` |
| `inJoin_cycle_example` | Quot.sound, propext | `ff54312e28d544f582cd9ccff3cee66dc6853f485aff4ad11205a98097a4aa7e` | `c3038f925ca1b71c6b8cce033ae670e3552a1f4180444fcc70c760af9b61183e` |
| `inJoin_example` | Quot.sound, propext | `50161f0b0ef4d191b296fc391c0c249b2b8c2d6d1d3d65a9b4526dad9453adab` | `54e39c2cd67038cd24dcf295cd2f54b3e6e2877609956f3f27aa539aa9848cc7` |
| `inJoin_iff_preWalks` | Quot.sound, propext | `70cb3fa07df705f2115cd1f467fcdcfbc41c068a26563a410ca32b329a52ee28` | `364f4e169076ed42292d755a7537cf05e728a414b8c360894a8c856f7a0360ce` |
| `isolated2` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `iteratedDF_subset_join_needs_allReachable` | Quot.sound, propext | `1a13cc41b91a6dd4d5c9a3e1c01392e1b102d6aa637da1f5411ad5421b11bda0` | `1c83d8053952494c0133b9bcfdd14848e4255c33fce021d8f6944015b383f7d2` |
| `iteratedDF_subset_join_needs_entryNoPreds` | Quot.sound, propext | `5eb4ac68959738dfaff6be78a2b5d7722f2b535cc6130277a7c4f6e0036974a2` | `33ed21ac8e047ea92b47d19f30318362231bc6e584fda928c55b002b82f6ddea` |
| `iteratedDF_subset_join_needs_entry_mem` | Quot.sound, propext | `78c51597dc7a904429951eb1f4d33971a854ea2a98e292613d77ab8126e63052` | `a800034afb78b091f4c7df907e21f5ea72085151cfc70a74678503a7addf6a3f` |
| `iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem` | Classical.choice, Quot.sound, propext | `f49d62bfb0643ff4d4da9b3527034909abed5e8c59202b4b023f786d8ac92408` | `f57c17f4ac87049aaff752117f2ba49a76ca9af0337df4039b2816d9b4b05452` |
| `joinClosed_diamond_example` | Quot.sound, propext | `6a319316c42da7ae9c67c24a0f34a102ccafcc2e5bf5aebb77f16472784f524d` | `54e39c2cd67038cd24dcf295cd2f54b3e6e2877609956f3f27aa539aa9848cc7` |
| `joinClosed_needs_singleReachingDef` | Quot.sound, propext | `18f54b87b7a586793ae9ef9e3f23d963c15c210321fcebb0e82c6da3c0a0643f` | `cee197c797f36cff96c865bbe1904aef9786986347fb8e439a5c8e577c305e45` |
| `joinClosed_needs_singleReachingDefAll` | Quot.sound, propext | `b6edd319eb74a33d1028871590ac2c4f664133a812979f868c192c93f177a904` | `3385da14844632e17d02db0bf53422b970d783adbe33fa3eab75df195c50823f` |
| `joinClosed_of_entryNoPreds_of_singleReachingDef` | Classical.choice, Quot.sound, propext | `5c60a205bd2eb2202d65a7f17bed73fe7f205ab7e76254b30827441b0b7e9068` | `cb3281cac9928f77e9f586a2bd1c82b3112c01756cd8fd1f6cbb5e82d7e52039` |
| `joinClosed_of_singleReachingDefAll` | Classical.choice, Quot.sound, propext | `7ec2c04e3d5d7833469689db658d398816354dac02e371d5483e8390434b810f` | `e34a12aeb3d436cb02b5adf4ea0fb7320596b6a42d729744d2064338ef18ec7c` |
| `join_eq_iteratedDF_of_allReachable_of_entryNoPreds_of_entry_mem` | Classical.choice, Quot.sound, propext | `3c3ecd013be5f9860577ece697547002cf4eb9eda79a2ba08f2bc6f77f865a25` | `f57c17f4ac87049aaff752117f2ba49a76ca9af0337df4039b2816d9b4b05452` |
| `join_iteratedDF_full_nonvacuous` | Quot.sound, propext | `903f784b59e1325cd6cff1d7d5062d954621c27b528c6d3b93491a472d298dde` | `03a303c1bbf65ad804108ad26ea2dc1d82742aa9e3c752a3cddc9c3011b2b9cd` |
| `join_placement_nonempty_example` | Quot.sound, propext | `78f90c7fe36c4ae630b4fbef0ac27910fba49e40eefd267c08c7f5af563db7ad` | `54e39c2cd67038cd24dcf295cd2f54b3e6e2877609956f3f27aa539aa9848cc7` |
| `join_subset_iteratedDF_needs_allReachable` | Quot.sound, propext | `189367c742aa4f25d85956272432f642be2439ef4b2abaad6c7b40b02f20c496` | `69bd5e272c0b9e9216769f633f9365c1c42a0fca0d9654f0b78337b765e49c46` |
| `join_subset_iteratedDF_of_allReachable` | Classical.choice, Quot.sound, propext | `12c628180ff55eb6d97728c5a03ff9c69caccfaacf7527f430fe164a9ebc4871` | `cd6f6aad22ca3e5f195a0ac31c03f3a409b141ddea6d4d197fb6395102265ec4` |
| `join_subset_needs_singleReachingDef` | Quot.sound, propext | `0e37d59884f113d6faea0c56c2f580164d31811cd8b4116e4f8ad1dfdbb9827e` | `cee197c797f36cff96c865bbe1904aef9786986347fb8e439a5c8e577c305e45` |
| `join_subset_of_entryNoPreds_of_singleReachingDef` | Classical.choice, Quot.sound, propext | `f5081925c7b21101b5d2bb564845c845fa128a4922fa6f8b8a57791e2578c604` | `cb3281cac9928f77e9f586a2bd1c82b3112c01756cd8fd1f6cbb5e82d7e52039` |
| `join_union_join_genuine_nonvacuous` | Quot.sound, propext | `b58ec83052ff306020f616dc8ba5d13901629e9f49fd9c44442e38fc967fce05` | `a64217cd5e3b588237dcb4e224ba736717e940610881afe91342a68f9c223f9b` |
| `join_union_join_subset_join` | Classical.choice, Quot.sound, propext | `751251e5c827b3c6414b3fa988a18c26bae73bb9541afed90044f9b4ce83038c` | `cb294a8ff3e858753e68d7033bcf900205d99854b4bf83b148753ea974a2f61c` |
| `ladder5` | propext | `fe5f683953839315161fd70be1e0f8957de182bd043506ff85dde9d755370289` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `lastDef` | none | `2fb8521433d10769c60234c729fcc425a23d9738e238d4accbed47049d0e77ce` | `e0ee024cb554ce734e5572009dd6556044d93dcc024949f86f06283c11e90230` |
| `lastDefAux` | none | `72d82318b7076dac2b84a78fea61e82fe6e9d23ca48558572eafbe6a34e85a82` | `e0ee024cb554ce734e5572009dd6556044d93dcc024949f86f06283c11e90230` |
| `liveOutName` | none | `31359f347b5eff9ac914b419474e6b9e62cee3ef3e95afda1171dfb971a95692` | `9788628305cb968817751f90343a16aef694b96dc27c612c03fe728d966f05f0` |
| `loop4` | propext | `ba928c7f1845a80f04b6e926bb1ea117f67b11ac542fdae976d23a6b1813cd65` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `loopUnreach5` | propext | `fe5f683953839315161fd70be1e0f8957de182bd043506ff85dde9d755370289` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `loopUnreachSrc` | propext | `6131d2ecc8415f2c33eb0b9c041196545343a305eab262596ede0a2cb0c80c9a` | `45cac984a445467f02e3d5730f7e30239bfe4c2a32115ed9b28ed72e21196ceb` |
| `lostCfg` | propext | `865a8530ac6c30a9967c42c83012dea2447be8d00bc8a68bc037bc28e18b875b` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `lostCopy_naive_miscompiles` | propext | `0582967f4bbe3bd4a59ac3000a3c450943c7900e1bcbf4608968b54b09949811` | `186077cd7361ffc6b55a8df2d476d37f6e9036ea731ba7647aa3f0a586bf98ee` |
| `lostCopy_split_fixes` | Classical.choice, Quot.sound, propext | `896435693eaa173472b0df7cf817d3d69e412fca04a6e6683eef371487d0cf55` | `2a1c164f4df9ec246272eae3a5414b294f0d993268882fae9ac454665d8b0328` |
| `lostLoopWalk` | propext | `9d68cd8e395faffbd342a92f95901844d0859e75bdd8fae6b9148f7c06e12eda` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `lostLoopWalk_walk` | propext | `883195a4f1d87902b83d7691324b76570d322c04c07713bf2e65478ed3a4be86` | `7f9a431f3e7a25c9bd661d10d8313610398ee8b80e4be5fafa9250e7acf4c85b` |
| `lostNoExitCfg` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `lostNoExitSsa` | propext | `81e1d4565e026e010c07dfe68f68b107e5bdfe09cae51c56bef8037594869169` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `lostSource` | propext | `3e84f2e0eb1fb5626025eabfaec030e5125268cbcd6f1324096e1d78826c6158` | `864fc965df5d443c5592ecff150f8f310a093268f18eac86a8f29b658bdc42e8` |
| `lostSplitCfg` | propext | `ba928c7f1845a80f04b6e926bb1ea117f67b11ac542fdae976d23a6b1813cd65` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `lostSplitSsa` | propext | `d1f251ce376a7120c53a86b4f2ecfb84142ca6e364853b00e53082d01517054d` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `lostSplitWalk` | propext | `dcb289270e0586c623254e514d858a3952524cb28ba913c0342bf80e25ec0353` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `lostSplitWalk_walk` | propext | `cce1ebb47ccb874910f60dd54e5087733d5a53d2f1e2eeab24ff2d507dfc619a` | `0f32f0385da1ee50b49f5ed5db2704a4746b9fe63f896168c123d2df3e30bf1e` |
| `lostSsa` | propext | `c4bd619f5c4e6e848a75a3db70f6197e957686cae37ac92064e87511a14664aa` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `lostWalk` | propext | `5a26f748610a28ee0498fc77635298e0d1114d2cba3ae04f24a01f677ca0c707` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `luIdom` | propext | `9c94e1cc9fa6c2ee7ad50a04bf9a65199de14d4f90d09213852dc172621b2c70` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `luPhi` | propext | `b1b2fa8c37ac3541ec2f9af7f6fb509a0cb914f6845bb1a14e395e145755f565` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `naiveOutOfSsa` | none | `eb4c3f1b1c630723df4111ccb86ee22c4f8c4025802ac828855dcc66c1c17e82` | `b4a985d4e7ba2b18603006a7725c52df0f085f81c70c6739f5db21213d9cbf75` |
| `naiveOutOfSsa_hyps_nonvacuous` | propext | `e4d826ff17f77e89361cc02a194a850467ac5e1a8c5d2dbbf25c781377d49eee` | `7f162a14401a5f38f1109b57c82c528d0f4186eeeaa08725c293af4b1a5b00f1` |
| `naiveOutOfSsa_needs_parallel` | propext | `b5fb67aaa56767a2abed6968a463dc5e678bb805934a05ce227f2c10d0cb1592` | `fc7f65c0f0ba625be8b7e4486e134dbe82620b7a9ff1f3adc8374262d2e3ee2c` |
| `naiveOutOfSsa_needs_phiPredsSingleSucc` | propext | `441d52b9b08a0dd4fe312f7caa395b583108a9136bf5ed26ac7bb7215aa5a6f7` | `7e870caada515bc275ef54a7603aabfcab7ce21ef2f632e079bbab6e6cab7705` |
| `naiveOutOfSsa_needs_walk` | propext | `80470288c89ce6857516bf49ac428ea540bad445d79d5add17e3bd699d8930bc` | `c46eb345713f893837cd0ae59b287f9ec8f67d536fbc6f8df2e33f5ae13a8188` |
| `naiveOutOfSsa_noCriticalEdges_needs_noCriticalEdges` | propext | `fdc5139df8decdbecd52a88ad89fabe1a432b897225d9781f45f3560da98fd93` | `a979113c03a128b3e7a3eded0163c84d4d715546865d29b59e2a8a2ea11fe42b` |
| `naiveOutOfSsa_noCriticalEdges_needs_parallel` | propext | `defb1a0019820b5dc5e3cb0aeb9b152d5661408e59bfe3718e160a5176976954` | `6cb917d076b5d668f0ea364b27a349b276e02c848e08028f7c8cf2f5df507b15` |
| `naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins` | propext | `f4a12dc8a4797357a107358e8585f8571cab0e98d206f8f7e556cc8b8f5244c6` | `d54bf86205c5522a1cb5cfa1530ff4d02b230db74ec2723c401ec5c32df9b5a2` |
| `naiveOutOfSsa_parallel_eq_of_noCriticalEdges_of_phisOnlyAtJoins` | Classical.choice, Quot.sound, propext | `8b45cb808a55f8329e0a51d04ab3d0358b8421d2abf4b08c559723ab81f43ab6` | `eaee38785b829cb995728c4384900e623b8426b3e3f481bcf811a4decfe9ce94` |
| `naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc` | Classical.choice, Quot.sound, propext | `20fdd7d09cd002a02f15eb26caac7d5edebf2eb036e9472e2fb992486a683ebd` | `3ebcf549c13e51641a2469cf1f089d94118d03b54ab36fb17a58585100b9275f` |
| `naiveOutOfSsa_parallel_run_eq_outCopies` | Classical.choice, Quot.sound, propext | `04f3fc17652f7a408bf6fd59ecd015f113082e63a0f42d551d64b8bebdde5073` | `5436833131802305d7fffe1665698b713bd8d94dd0e5c2a05ce11eaf483e7511` |
| `naiveOutOfSsa_run_needs_exit` | Classical.choice, Quot.sound, propext | `337ce3104f187a930b33f784e8e944ce372afef0f6332f3b930975d6cb7bfd4e` | `5b39054b01d451166fc619263b2fa45d252eef39be58970a1780d8bfe32991a0` |
| `naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe` | Classical.choice, Quot.sound, propext | `9941c8a7239f49e549b8994b9c11e2153e4c2727331ed70ebd6a6a198dda71cf` | `3c1329745f354e5f7a132f4abd2759b1ee9d9dbcab45c22cc66175827db93ad8` |
| `naiveOutOfSsa_sequential_hyps_nonvacuous` | propext | `a5ce47a4c492210738e30f0d1751a4dd86b9e5f501b49203bad919057e22112c` | `2b8cc2591612be6d45e6467b3aaf6b63d7f3a4c913d1be4c0a90eb499f2dfa5d` |
| `naiveOutOfSsa_sequential_needs_phiPredsSingleSucc` | propext | `3cfd6092a7de0f78ae0dcf5166dc9e36c33854c8a8cc8e5c49ba2981098d0858` | `71f9470b56ffea82abf71d9d60d3790d7ef0db2a70d5d08cae9c83eec831d17f` |
| `naiveOutOfSsa_sequential_needs_seqSafe` | propext | `fc60e2a872a71af118a1a06fe80a7e75b16b81ca424ab7cb12af9715f9d6d886` | `b72311cc67885ddff57caa90dc20ce5869d23da29346436f2d4527664b5f0a18` |
| `naiveOutOfSsa_sequential_needs_walk` | propext | `4d7d75293f4b9f16bc7e90d2fe00e2581e12cc0a3b001bd4cc591cf806b59e84` | `bdd45e0a8bdf21ddfd6f0e4d9f95d3dd74ed31eae879a342d508e5a3073d4a0e` |
| `naiveOutOfSsa_sequential_run_needs_exit` | Classical.choice, Quot.sound, propext | `28dfe399006fe0360c679123c46b0600531fd8e84b130331a119368cb96bfaeb` | `e447b35740e944feb701b65bf66208cbe0b018c30e188228996010903a3e7694` |
| `nearestSDomDef_example` | Quot.sound, propext | `73cfaeb97dec0269c3b21e20090ed26e1e93eea120b4aba7ebfdf471de9b9e43` | `dfb5168a0827e7b285a3ceb6fc20abfdd3b554588d1ea873d7fb83ed99f50ef8` |
| `noCriticalEdges_lostSplitCfg` | propext | `0245d83d10ec7e4c3784bd4e0b1befddf64e5b1992e603b4734271aa2db9653d` | `00ebee5e0fd657a305e1c02d85206e34b7f48873913bdfa96f1c81f45d42dd0c` |
| `noCriticalEdges_swapCfg` | propext | `1ac9de284557c17e97e7980ff29c65c87e737d92799abaefed48d7542a769286` | `42cb3feab15e4c19b605174bd1e1724cd69974a644690459f6c09e9a4942471e` |
| `not_acyclic_loop4` | propext | `d44382e62472db851ef10c99b78242ec05283850faedc308844e963d44b83797` | `997df80239dba06d97fc7562b82bc40398644dce5ce9ca74b9dbb03953d9f549` |
| `not_allReachable_isolated2` | propext | `9f6f5bf17c6938c5f1e9da8984dd301ff6057f83c53e9f0303643409b2e4b493` | `085c15d684bf107ae965151aade6fef1c0d4d6e53bff85246f9961bac393201f` |
| `not_converge_example` | Quot.sound, propext | `1ccf458971905252d8b2e2898a4ff8b401bfbb778ee62796769ad7173c5df993` | `7205164e8d93caf57c37117d965ed4a73b9b2276f4751204939c28e4a35331f9` |
| `not_df_example` | Quot.sound, propext | `01be4ad798fc57c7f642f49ac16f9f4e090ccdd96ed54f7aa3df4ae2ca12e5cf` | `45d4ec0423ceeabd79615587117c72a4884b60d1c1f6e5f835fc065b82bce431` |
| `not_df_ladder_example` | Quot.sound, propext | `6b9af240d6a5c282ee971808d8cf59fa0c023df30bd6ff5c3fb5626386f7fd63` | `f00ad19d5f4a0b15a139d353251a586ce895922cd7223a21209a2c7017a1262f` |
| `not_dom_example` | Quot.sound, propext | `8d3d2fa5498bb5c6b8f08e9a3bccfd82d35bda997881d4444541d34e259fb540` | `31a095ce24a7593a7b8667c312c6dcdb430f140161bb7b2df5d6fe72cda88cd1` |
| `not_entryNoPreds_backToEntry2` | propext | `39ba765062957c9ee1d70825aac9d6c447e4ff9b069e96d08666450bec1eeb03` | `37da89f6d4d3201e36879cf94e47e194e312406005dd8b6e70e5a9bc0a2c42e1` |
| `not_idf_example` | propext | `4b1210a75291a04d133988a80ae27a30a7f11f1534718d864f6e69b70e091c2b` | `0253de5e6407f6e449aee5f146b65eba3002d0cf829f89a542d22dc7858fae83` |
| `not_inJoin_example` | Quot.sound, propext | `d4ef1043e781c7937124974fd539a4f967c9741c234557cfbf3de98acb12f513` | `649c5985cd5efea11ad77dbbe1af487514495ba0c4ec42df43d1f37c8bdd917c` |
| `not_nearestSDomDef_example` | Quot.sound, propext | `4c1ca9635ca45d50290971a4daa8119f7fcff4292506ed2c2e11e35c1e0fb59b` | `dfb5168a0827e7b285a3ceb6fc20abfdd3b554588d1ea873d7fb83ed99f50ef8` |
| `not_noCriticalEdges_lostCfg` | propext | `2769457bdbaa3f19752249c3e6fdbfc51dbd2cd99bbb4a4cc07cf7ebca5b576f` | `28f22749874e270a44ac4d49ed77e383f209b78e4044809782a5f6f651f4a2ea` |
| `not_phiPredsSingleSucc_lostSsa` | propext | `6a6670e1c48561c9c383c67c56952bf827637d3493e3f110a995b32c4ce1293a` | `b08076908ce8c72a6b007c4e39e64480f7cfa47d5fcefe76582f7831eec11a9a` |
| `not_reachesTop_example` | Quot.sound, propext | `de6a250e6131281eb06c798bed5ac616cceec936615ceb9d0ec36181a1b6b10e` | `5ceb7229158c7cea5a58e77c04e597060e604d434cdd2b2d81278975b4f4fe7f` |
| `not_sdom_self_example` | propext | `b503984e11ca87efdd8f2fd9eb1817be6cdf65b10cf835ded099da02f5903de1` | `0fcb68186fde2dfab8c47b3483c605f47f1a067ddf7e0ac69c72b292ec1b8713` |
| `not_srd_example` | propext | `4dc191c89609d52993156387c55a11cfcdb9faf66a00dada18f8ad97c9e15922` | `860009f34d0d06547c6516f0e8f16622728f069ceb3e247ab7f2550c3655dcf2` |
| `not_walk_example` | propext | `b1591dd393a1e6a3542dd437a82d419bd796a6e4d754cd9565e8934507c9c612` | `483cabc648cc8f7f109597951edf2bbae418a2c62e05c2d2f76e3af106e2fe33` |
| `outCopies` | none | `2cb322fd38a7e7a48807940c67be0d1c62ed502947f8288631102e23c006a5ec` | `968e41b7ab48a7ae0281bd8f3821cf88b5b333492f12e5895e157afeb10fa5d4` |
| `outName` | none | `2ccaa429b78940b3c31a5304d6daf90487cba1514ddc849f9ff75cba8a218e1e` | `9788628305cb968817751f90343a16aef694b96dc27c612c03fe728d966f05f0` |
| `parCopy` | none | `a89957fb2cf91905e112766df29a487fd75c26d98e2d70e9aa5d8bed5ff137c1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `phiPredsSingleSucc_swapSsaAB` | propext | `da325e8ff6cd530ad90caf4931f9f31aadd537e627ccaf53c300fba0cc0e48b6` | `91045b4f542e13c9eb6e553d5344d605a0e0d59e96a2687c7ba38a2427249f40` |
| `phisOnlyAtJoins_swapSsaAB` | propext | `b7b89711ab0975f9cbf05cef03ddede86138a65571b500c393987abe78de5b75` | `c087d76938c89e0f1acebf3aacbd2ebe0f06bed8cead79004b2929b0017a859d` |
| `reachesTop_at_phi_block_example` | Quot.sound, propext | `9bd36783d88a3da8fc1d614ca5c04f3c84c10b41c61b5fb70abc85a2e83a06d6` | `c484e961c1de87d9aeb62baa80be0d17e1dde3807be1f2f452eb9f1be6998b13` |
| `reachesTop_example` | propext | `b06d296941caf41eb6df55c87db86e567364cc02d87134cde9d02c0030ae4225` | `5ceb7229158c7cea5a58e77c04e597060e604d434cdd2b2d81278975b4f4fe7f` |
| `reachesTop_iff_hyps_nonvacuous` | Quot.sound, propext | `ca414bf340191edcab1e5315ef34fb51591b96e7dd54e42df827aed159858acc` | `29b7a996a2c7a6a39c4ede6a2949274b9e02aa48a824778574eb66a75a314cbc` |
| `reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf` | Classical.choice, Quot.sound, propext | `98fc3bfe176f0fe66d70ea58120b05d811e63de6d975e8fabde7f6d2432bd3f4` | `47783ffb29dcf174a56ae1930d476b08a723f2afd7664bf2ede78e3e2b9cb265` |
| `reachesTop_iff_needs_allReachable` | Quot.sound, propext | `7c90ec087a279d62d5f1acecf257ee2621be3a583d1e3007ece2b8b883cfe54f` | `0305e3cbab5a552c4e48a9abc9ab1d1ac1ed284b39102f82416135a494e9434f` |
| `renameBody` | none | `c3f04183e04f3cd30e675a0c4abb09a38badec205724358f5d48cc4a9032103a` | `4ff0191f88cf82067b765ddc202649717cb6d9a8009621e93ef5f98e2f4c94fb` |
| `renameExp` | none | `22c818650e9edb40a73cce0147f1b9e62a8751a90f7ba4c7052a808ad3bb72ea` | `e0ee024cb554ce734e5572009dd6556044d93dcc024949f86f06283c11e90230` |
| `sdom_example` | Quot.sound, propext | `fdcce8a4f02654789bca9694b4b99ee20f3abf66a449456f7f8b3c4eb77e0feb` | `0fcb68186fde2dfab8c47b3483c605f47f1a067ddf7e0ac69c72b292ec1b8713` |
| `selfLoop2` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `singleReachingDefAll_needs_joinClosed` | Quot.sound, propext | `9db77e0f064f073d7626b2ddccd4ae34ac26d82b5acd5461d9931df1375eaf71` | `3385da14844632e17d02db0bf53422b970d783adbe33fa3eab75df195c50823f` |
| `singleReachingDefAll_of_joinClosed` | Classical.choice, Quot.sound, propext | `6156787777ac71f8cc268e03e9cd855f15ca908a80844be2eb234510bcb2dcaf` | `e34a12aeb3d436cb02b5adf4ea0fb7320596b6a42d729744d2064338ef18ec7c` |
| `singleReachingDef_at_iteratedDF_of_allReachable` | Classical.choice, Quot.sound, propext | `bb3ad913d71ba82b76094e438ead3534e97f0f2de75c041fe1311b729ec6973b` | `3c7a7ba08dd733e8f4b2e4df6ee4f176e25565f44949ce9cb2bbf6016620786d` |
| `singleReachingDef_at_join` | Classical.choice, Quot.sound, propext | `4d44eb7fd7fc555afc4bd8ba8a10b9ed47858c8963a87eb28db3aff05947255d` | `900442b4d467eb0c9b75ccdd3ba600ed0d5ed1910f1f1e3e387a2e93734dd9d0` |
| `singleReachingDef_needs_joinClosed` | Quot.sound, propext | `491d112d6bbfae346734fbc3016961e053f2ec01b71e95f0a9b42fbedad19537` | `6bb2428bbc644ce4e7f4d7cc6f0f54a15e5fd09908d8e97ac20bba9520e02468` |
| `singleReachingDef_of_joinClosed` | Classical.choice, Quot.sound, propext | `c993777d94b8b1df626f099a6f1d9161a91d4543a307fcc9ba6109293df51dfd` | `900442b4d467eb0c9b75ccdd3ba600ed0d5ed1910f1f1e3e387a2e93734dd9d0` |
| `srdAll_hyps_nonvacuous` | Quot.sound, propext | `91c6b7f1f255072e6ef361db3498db60ca33c440833e6b435accb5dc6d954540` | `5d6a7c295011ad8f717d54386a77f4aaaece5ee04815f71d6cf6f83b9f1ebff3` |
| `srd_at_most_one_example` | propext | `6bad175ece5b934be88304f4849a9a5a7b40a513b268d160e9a7245e724dc31e` | `7eca62e516730c47c7a91e44709ba43c749da19978aaa4c4cd7be5fb48604fb3` |
| `srd_entry_exemption_example` | Quot.sound, propext | `4b9be48f21611aadc5d81d5b04ed2f9423f2bb6584dc5d0328dc42b4d43b79b2` | `adb2f9db14f0efd7645e30fb1c27b5aca18270fae4b55e8140f1f22b9a744e08` |
| `srd_example` | Quot.sound, propext | `0e01f71c49d65dfe63a3db77f732bc0374539961b2582e1ba50b31355a082975` | `860009f34d0d06547c6516f0e8f16622728f069ceb3e247ab7f2550c3655dcf2` |
| `srd_hyps_nonvacuous` | Quot.sound, propext | `af9211eefc57623d232338a9411161cf96e830ff4c4e13ad1d189c101128a5d2` | `326b3767714e2a18be6b4deae9e9ec51805797a5e30149d1a65c7292ab8188fa` |
| `srd_iteratedDF_needs_allReachable` | Quot.sound, propext | `62ff3bd85d25597dc6dd510a728d0e358737a3a750be8dbef41bc126a85c0028` | `5fda40f57b71705ff06fc46445d4bf4404a5ef7b74957d54597dce882aa0f244` |
| `srd_join_needs_entryNoPreds` | Quot.sound, propext | `c002b5704f9c2077e95d05baf97297bbfd5e875d1d75efd3e089dc3f7c593433` | `ccb7d9aa416cccc5e28534db21c8125081af7d8c1ec313a304dc6acfb15b7e74` |
| `srd_not_monotone_diamond` | Quot.sound, propext | `a2ac00d3381230f7c6e6499a582696952162dc58b4caa647f085b55aa3ed5e30` | `6bb2428bbc644ce4e7f4d7cc6f0f54a15e5fd09908d8e97ac20bba9520e02468` |
| `ssaConstruct` | none | `9c932199a70ae2b2de876a45ab39c51aa166b7707b249b2c035c89f81d99333b` | `744b43f61a45d9b6b424ee42b90542d6ef9b708788dabffbcc87e272bc97faec` |
| `ssaConstruct_acyclic_corollary_needs_acyclic` | Quot.sound, propext | `7c03769b181a052e0aeda3f729814c4cd53cc9b04332514f6049f7c5dc81d33f` | `3503b2830543f0945b78f8c6ca2e8b2894f215ccfc36da0d8603fd93b1a0ddcf` |
| `ssaConstruct_cyclic_unreach_nonvacuous` | Quot.sound, propext | `9c7a91af455192766540f1f431227bd827185971048f1a60ee99ac4f5b486e23` | `efb447ca82703b69b7f15064baa1d05da02d2c66fe64715106c6f7c904df0b3d` |
| `ssaConstruct_entryPred_nonvacuous` | Quot.sound, propext | `ba2626ba46863050a913a6a875cae8507581950669fec46d467b004165d7a56b` | `e45f8fa9f8254d9c46e8f1b8ab5f2a39d1cce3fb61cf9c70e77366b6dfe03c7a` |
| `ssaConstruct_hyps_nonvacuous` | Quot.sound, propext | `9ea23342b284a8addac90c5faacaca7fea1460d142228428e52c9eeddb9a75ac` | `a60e89fe48531dfe334bcf21a3925cb28f69056ba66f28673f465e3058e49b96` |
| `ssaConstruct_needs_entryNoReachablePreds` | Quot.sound, propext | `4768a403d59443362408371471a5795016c7133670a08dea66152666f15d612a` | `122c4c5eaa64dde3454b21dd9ce57ed11a919ec4ec90b91df70e0d4804c2996b` |
| `ssaConstruct_needs_hinit` | Quot.sound, propext | `df4825ce7d4f2bf43ad00fe8e94e80c8b0b70a7bd70efc7f79abf7cfbfdea841` | `19df44ff8ef0b2a0bf8dfff0a6e36362a0be9a2f1daf2bc017a100699c496226` |
| `ssaConstruct_needs_hvars` | Quot.sound, propext | `f5d5913b5e6446f46a2a1b413517ae6806f59dcd8556ca3e19705e7b776e18b4` | `19df44ff8ef0b2a0bf8dfff0a6e36362a0be9a2f1daf2bc017a100699c496226` |
| `ssaConstruct_needs_nearestSDomDef` | Quot.sound, propext | `8e49b8bca349fb591286d1195c9b88c5cfc09831947b4cd1341dbac928d8a513` | `54dea67d2f2c87a98e7de781a830ea996144aac3ddb05486fdb6d1bd2bd1e6bc` |
| `ssaConstruct_needs_phi_cover` | Quot.sound, propext | `3b7315a04cd27da253459dc1b60b17e8e36f52091c8656734f26a2660c3c542d` | `d8fbc0ae9e5f51607b1446fd71765f52116ce6053a3b3e27dd5fad13952a03f9` |
| `ssaConstruct_needs_phi_within` | Quot.sound, propext | `a4ea960d69c21ba41756635d4eedda0ccc42238ca0321c169ed769c036d12f4e` | `7b4327cf8273b492fe6e3e8fbf308b9bc69f1f62d62972ca95af276fc7068202` |
| `ssaConstruct_needs_walk_from_entry` | Quot.sound, propext | `aeef799952ca86b1eb2fa41c0faf3dd5d0db494bb7d71e41798c123d3b168ef3` | `19df44ff8ef0b2a0bf8dfff0a6e36362a0be9a2f1daf2bc017a100699c496226` |
| `ssaConstruct_preserves_values_of_acyclic` | Classical.choice, Quot.sound, propext | `fd810f2f2b9a57825398a8be1f5267d0b2a8a19dbc2f8c0d1b5be2b17e280766` | `841b8f46b633b5ba3c4648a72b0d651929bdc5bc4a75af0ef4e2843939e90f28` |
| `ssaConstruct_preserves_values_of_entryNoReachablePreds` | Classical.choice, Quot.sound, propext | `ee555b9994bed993f69ced86cc0dac9e5bec0861f93ecf49b426dc741d551ce4` | `f0ac0905a2018284d92b8259332bf7cdc17451a238d95171d0b6c8c45a53d9f8` |
| `ssaConstruct_singleAssignment_needs_nodup` | propext | `94eef51b1765887c9637f2c4e4ce721fc35a919b64619d010ded2ece88466022` | `c1d184afba035b29cb9e2f68d1abfdd01e6f14f4db9cb5cc3509388e4f95b2e7` |
| `ssaConstruct_singleAssignment_nonvacuous` | Quot.sound, propext | `717e939596c3857ec180851bb1b0b768fbe473a614705fbcbf395afe0237b534` | `c1d184afba035b29cb9e2f68d1abfdd01e6f14f4db9cb5cc3509388e4f95b2e7` |
| `ssaConstruct_singleAssignment_of_nodup` | Quot.sound, propext | `da53cda33ab642a3f403eee188915c44ff33ddde6876e74486de62056b6f5c8a` | `eb0c8c3b2ba578dd8d41be0541c95e6846c3189ae9d31ae1087532f55883070c` |
| `strict_subset_of_join_two_defs_diamond` | Quot.sound, propext | `26609c5993a499d6800286b4481c0c811b642c79f6c6ecd36c66fa19d7bef819` | `6bb2428bbc644ce4e7f4d7cc6f0f54a15e5fd09908d8e97ac20bba9520e02468` |
| `strict_subset_of_join_two_defs_loop` | Quot.sound, propext | `6d1dd99af463950e126165b332c55713787b04df4d71155ad946729d7d1d32b6` | `6fd32a9dbc14647c3c1f08e2082f192fd89d6cfb5486df3ff9c612943d5b384a` |
| `succs` | none | `d2cee663d90a5598b9c1f0b29b3c988906ebdf675ac7a84c782cf995a9429a9f` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `swapCfg` | propext | `ba928c7f1845a80f04b6e926bb1ea117f67b11ac542fdae976d23a6b1813cd65` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `swapSsaAB` | propext | `d1f251ce376a7120c53a86b4f2ecfb84142ca6e364853b00e53082d01517054d` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `swapSsaBA` | propext | `d1f251ce376a7120c53a86b4f2ecfb84142ca6e364853b00e53082d01517054d` | `074f79ff579ec7c92c01d8c0dbd9d243c2cf9c5d1e4f1b203e8a84183b843b7c` |
| `swapTempProg` | propext | `311128e24d600b3b94934d6293a819e203ddd2b968085ddc5a97142de82f810b` | `864fc965df5d443c5592ecff150f8f310a093268f18eac86a8f29b658bdc42e8` |
| `swapWalk` | propext | `0ea31a9c55c41d2e21f19caf0bc289994b2a494afbfcc17bba93e781c02af0c9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `swap_parallel_correct` | Classical.choice, Quot.sound, propext | `0598742bdfcd89ee86a74f3d373553207800488b56b80cc386a8783182cb9ab0` | `ca876c802e51d4676da52af776c8e7a786ade6abb6edc553b051643f2b4574f5` |
| `swap_sequential_either_order_wrong` | propext | `66018f2e841b541516440745a321a9ce1678f6f9927bb8e6b6267e6b5b337db2` | `5070551fc75595d41bf7afb74179729e3981ef35a5036fee2e50ac874a99aedc` |
| `swap_temp_hyps_nonvacuous` | propext | `9cfc0ce6c9c7fffda9be11808e547e7aafe3d80a70a20058bf9eb46b6bf5b618` | `37fdae9059827a1c30d8967d4f96603961207148ebd26302b686091d8931b22c` |
| `swap_temp_needs_ne_temp` | propext | `447aaddda7e778cc3b199010641d4c094e3c595a85677c30faabf046fe1d86ad` | `2e9903c9b70ecc7fcdff3cacbefff31d80796fd86610b06be8e49beca49748fe` |
| `swap_temp_needs_walk` | propext | `dd50fa73021a8e4ece7f06afc8182e36263b88b0d22520adedc828ccac821a02` | `0331058c6e8d9a6cf76215f3945a592c45222d6a72900759bda768678857893b` |
| `swap_temp_sequence_correct` | Classical.choice, Quot.sound, propext | `af5e39a9a2ac0faa372339ee46f95a19c5ae0b0d6354f5595b1c682eb07f5099` | `0331058c6e8d9a6cf76215f3945a592c45222d6a72900759bda768678857893b` |
| `topName` | none | `0a1b545bed5394b6b34fc1604e1262caf2645afb3519c5beecff029b98bdf851` | `9788628305cb968817751f90343a16aef694b96dc27c612c03fe728d966f05f0` |
| `unreachJoin4` | propext | `ba928c7f1845a80f04b6e926bb1ea117f67b11ac542fdae976d23a6b1813cd65` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `unreachLoop2` | propext | `ac70f90f93584e6562ad0016bb582e6bfd671cf9d176b91ae67ebaf664326339` | `856fa0ea0c463fc6498b7cbd14b04892b9f3d72728d00720b770d915b350ca30` |
| `upd` | none | `460fed40c8f4744a3cea4c72482e211d92056da191889fca472cc2253f2ce08b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `walk_example` | propext | `9119e292182faf319606ae8e78d5ac9690767ebca5daf987456d2281d948e9c9` | `483cabc648cc8f7f109597951edf2bbae418a2c62e05c2d2f76e3af106e2fe33` |
| `windmill_sequential_no_temp` | Quot.sound, propext | `071c274387ee63bb83717d24ef5494a6ce7a335c1f9d98fdcc0d6839e33bf6d5` | `5629fdae5dab193539661ced8c0ad8d0580461e77ea0e2d81635131adb6dfd28` |

**Auxiliary declarations.** Every package-local declaration that this report names outside the card statements (witnesses, counterexamples, examples, concrete programs, and the auxiliary lemmas of the join-closure proofs such as `inJoin_iff_preWalks`) is quoted verbatim under Auxiliary declarations cited by name or under Definitions, and is listed in `results.json`, so its statement hash appears in the table above. The axioms of every declaration of the library, including those not named here, are recorded in `audit/axioms.json`.

**Primary sources** (bibliographic records checked against DBLP on 2026-11-21):

- Ron Cytron, Jeanne Ferrante, Barry K. Rosen, Mark N. Wegman, F. Kenneth Zadeck. "Efficiently Computing Static Single Assignment Form and the Control Dependence Graph." ACM TOPLAS 13(4):451-490, 1991. DOI 10.1145/115372.115320.
- Michael Weiss. "The Transitive Closure of Control Dependence: The Iterated Join." ACM LOPLAS 1(2):178-190, 1992. DOI 10.1145/151333.151337.
- Preston Briggs, Keith D. Cooper, Timothy J. Harvey, L. Taylor Simpson. "Practical Improvements to the Construction and Destruction of Static Single Assignment Form." Software: Practice and Experience 28(8):859-881, 1998. DOI 10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8.
- Vugranam C. Sreedhar, Roy Dz-Ching Ju, David M. Gillies, Vatsa Santhanam. "Translating Out of Static Single Assignment Form." SAS 1999, LNCS 1694:194-210. DOI 10.1007/3-540-48294-6_13.
- Gianfranco Bilardi, Keshav Pingali. "Algorithms for computing the static single assignment form." J. ACM 50(3):375-425, 2003. DOI 10.1145/765568.765573.
- Laurence Rideau, Bernard P. Serpette, Xavier Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." J. Automated Reasoning 40(4):307-326, 2008. DOI 10.1007/s10817-007-9096-8.
- Benoit Boissinot, Alain Darte, Fabrice Rastello, Benoît Dupont de Dinechin, Christophe Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125. DOI 10.1109/CGO.2009.19.
- Matthias Braun, Sebastian Buchwald, Sebastian Hack, Roland Leißa, Christoph Mallon, Andreas Zwinkau. "Simple and Efficient Construction of Static Single Assignment Form." CC 2013, LNCS 7791:102-122. DOI 10.1007/978-3-642-37051-9_6.
- Jianzhou Zhao, Santosh Nagarakatte, Milo M. K. Martin, Steve Zdancewic. "Formal verification of SSA-based optimizations for LLVM." PLDI 2013, pp. 175-186. DOI 10.1145/2491956.2462164.
- Gilles Barthe, Delphine Demange, David Pichardie. "Formal Verification of an SSA-Based Middle-End for CompCert." ACM TOPLAS 36(1), Article 4, 2014. DOI 10.1145/2579080.
- Sebastian Ullrich, Denis Lohner. "Verified Construction of Static Single Assignment Form." Archive of Formal Proofs, February 5, 2016, https://www.isa-afp.org/entries/Formal_SSA.html (theory `Minimality`, lemma `pathsConverge'`, checked at `isabelle-prover/mirror-afp-devel` commit `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, `thys/Formal_SSA/Minimality.thy`).
- Sebastian Buchwald, Denis Lohner, Sebastian Ullrich. "Verified construction of static single assignment form." CC 2016, pp. 67-76. DOI 10.1145/2892208.2892211.
- Delphine Demange, Yon Fernández de Retana. "Mechanizing conventional SSA for a verified destruction with coalescing." CC 2016, pp. 77-87. DOI 10.1145/2892208.2892222.
- Fabrice Rastello, Florent Bouchez Tichadou (eds.). SSA-based Compiler Design. Springer, 2022. DOI 10.1007/978-3-030-80515-9.

**Modeling-bridge sources** (read on 2026-11-21): `llvm/llvm-project` commit `4e7821e89a0cb307ea61620b5c17e9ff7028cb8a`, `llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp` lines 901, 978-988 and 1009; `bytecodealliance/wasmtime` commit `64d5afa6960f5a20536f9404b64f2d26b2611990`, `cranelift/frontend/src/ssa.rs` lines 1-8.

**Support material.** `lean/` (the Lake project), `results.json` (machine-readable cards), `audit/axioms.json` and `audit/statements.json` (recorded axioms and hashes), and `support/revalidate.py` (the revalidation program described below).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified) and checks: (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit`, `native_decide` or an `axiom` declaration; (3) every declaration of the library depends on at most `propext`, `Classical.choice`, `Quot.sound` (Lean's `collectAxioms`); (4) for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (Lean `repr` of its type) and of its definition closure (the `repr` of the types and values of every package-local constant reachable from the statement, theorem bodies excluded, sorted and newline-joined) equals the recorded value. It prints `REVALIDATED` and exits with status 0 exactly when all four checks pass.

A manual equivalent of the build and of the axiom audit for the main results:

```sh
cd lean
lake build
cat > /tmp/ToySsaAxioms.lean <<'EOF'
import ToySsa
#print axioms Toy.Ssa.join_subset_iteratedDF_of_allReachable
#print axioms Toy.Ssa.iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem
#print axioms Toy.Ssa.join_eq_iteratedDF_of_allReachable_of_entryNoPreds_of_entry_mem
#print axioms Toy.Ssa.join_union_join_subset_join
#print axioms Toy.Ssa.singleReachingDef_of_joinClosed
#print axioms Toy.Ssa.singleReachingDefAll_of_joinClosed
#print axioms Toy.Ssa.joinClosed_of_entryNoPreds_of_singleReachingDef
#print axioms Toy.Ssa.joinClosed_of_singleReachingDefAll
#print axioms Toy.Ssa.singleReachingDef_at_join
#print axioms Toy.Ssa.singleReachingDef_at_iteratedDF_of_allReachable
#print axioms Toy.Ssa.exists_reachesTop_of_entry_mem
#print axioms Toy.Ssa.existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry
#print axioms Toy.Ssa.reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf
#print axioms Toy.Ssa.join_subset_of_entryNoPreds_of_singleReachingDef
#print axioms Toy.Ssa.ssaConstruct_preserves_values_of_entryNoReachablePreds
#print axioms Toy.Ssa.ssaConstruct_preserves_values_of_acyclic
#print axioms Toy.Ssa.ssaConstruct_singleAssignment_of_nodup
#print axioms Toy.Ssa.naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc
#print axioms Toy.Ssa.naiveOutOfSsa_parallel_eq_of_noCriticalEdges_of_phisOnlyAtJoins
#print axioms Toy.Ssa.naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe
#print axioms Toy.Ssa.execBody_sequential_eq_parCopy
#print axioms Toy.Ssa.naiveOutOfSsa_run_needs_exit
#print axioms Toy.Ssa.swap_sequential_either_order_wrong
#print axioms Toy.Ssa.swap_temp_sequence_correct
#print axioms Toy.Ssa.lostCopy_naive_miscompiles
#print axioms Toy.Ssa.lostCopy_split_fixes
EOF
lake env lean /tmp/ToySsaAxioms.lean
```

Each `#print axioms` line must report a subset of `[propext, Classical.choice, Quot.sound]`. A passing run establishes that the quoted statements are proved under Lean 4.34.1; it says nothing about real compilers. To revalidate after a change of toolchain, rerun the same commands with the new toolchain in `lean/lean-toolchain`; a changed statement or closure hash means the statement or a definition it depends on changed and the affected cards must be re-read.
