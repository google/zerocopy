# MFP versus MOP in monotone dataflow frameworks: distributivity, side conditions, and a non-distributive analysis (Lean 4 toy model)

## Summary

This package is a self-contained, kernel-checked Lean 4 development (core Lean only, no Mathlib) of a toy forward dataflow model: a finite control-flow graph (CFG) with one transfer function per node, facts in a join-semilattice with bottom, the MOP value at a node specified as a least upper bound of the values of all syntactic paths from the entry, the MFP value specified as the least solution of the dataflow inequations, and a fuel-bounded worklist solver. Every result is a statement about this model; none is a statement about a particular compiler.

- **`mop-le-solution-soundness`.** On a finite CFG whose transfer functions are all monotone, and for any transitive relation `L.le` (reflexivity and antisymmetry are not assumed), the value of every path from the entry to a node `v` is below `x v` for every solution `x` of the dataflow inequations, and if `m` is a least upper bound of all path values at `v` (the MOP value) then `m ≤ x v`.
- **`mfp-eq-mop-exactness`.** In a join-semilattice with bottom satisfying the ascending chain condition, if every transfer function distributes over binary joins and every node unreachable from the entry has a strict transfer function (`f u ⊥ = ⊥`), then the dataflow inequations have a least solution and every least solution equals the MOP value at every node; the unreachable-node condition may be replaced by "every node is reachable" or by "every transfer function is strict"; and, separately, under the ascending chain condition the inequations have a least solution whenever every transfer function is monotone.
- **`diamond-exactness-characterization`.** In a join-semilattice with bottom, for five-node diamonds whose entry transfer is `id`, whose initial value lies in `I` and whose two branch transfers and join transfer lie in `F`: if every member of `F` distributes over every realizable pair `(g a, h a)` with `g, h ∈ F` and `a ∈ I`, then on every such diamond every least solution equals MOP at every node (without a monotonicity hypothesis); if every member of `F` is monotone and every such diamond is exact, `F` distributes over every realizable pair; and if `F` contains every constant function, `I` is non-empty, and either every member of `F` is monotone or `L` satisfies the ascending chain condition, then exactness on all such diamonds is equivalent to full distributivity of every member of `F`.
- **`constant-propagation-not-exact`.** In the unsmashed pointwise flat constant-propagation lattice over `x, y, z`, for the program whose two branches are `y := 1; z := 2` and `y := 2; z := 1` followed by `x := y + z`: for every entry state `a` the diamond has a least solution, and every least solution `x` has `x 4 = (x = ⊤, y = ⊤, z = ⊤)` after the assignment, while the MOP value there is `(x = 3, y = ⊤, z = ⊤)`; the transfer of `x := y + z` is monotone (`assignXYZ_monotone`) but not distributive (`assignXYZ_not_distributive`).
- **`gen-kill-distributive-and-exact`.** On bit vectors over `Fin k` ordered by inclusion with union as join, every gen/kill transfer `f a = (a \ kill) ∪ gen` distributes over union and is strict exactly when `gen = ∅`; for a CFG all of whose transfers are gen/kill and in which every node unreachable from the entry has an empty gen set, a least solution exists and every least solution equals MOP at every node; in the dual must orientation (reverse inclusion, intersection, full set as bottom) gen/kill transfers distribute over intersection and are strict exactly when `kill ⊆ gen`.
- **`kildall-computes-mfp`.** For a join-semilattice with bottom `L` with a decidable order test, whenever the fuel-bounded worklist solver `kildall L G fuel` (all nodes initially on the worklist, one unit of fuel per pop) returns `some x`, `x` is a solution of the inequations (for any transfer functions) and, if the transfers are monotone, the least solution; on a lattice of height at most `h` it returns some value whenever `fuel ≥ n * (h + 1) + 1`, with or without monotonicity, and this fuel bound is attained for every `n ≥ 1` and `h ≥ 0` (`kildall_fuel_bound_attained`: on a CFG of `n` nodes, each with a self-loop, with monotone transfers over a chain of height `h`, fuel `n * (h + 1)` returns `none`).
- **`kildall-computes-mop`.** For distributive transfer functions on a join-semilattice with bottom of height at most `h` with a decidable order test, if every node unreachable from the entry has a strict transfer function, then with `fuel ≥ n * (h + 1) + 1` the worklist solver `kildall` returns some `x`, `x` is the least solution of the inequations, and `x v` is the MOP value at every node `v`.
- **`reachable-node-not-exact-unreachable-gen`.** With gen/kill (distributive) transfers on 1-bit vectors, there is a three-node CFG (entry `0 → 2`, and an unreachable node `1` with no incoming edge, gen set `{0}`, and an edge `1 → 2`) in which node `2` is reachable from the entry, yet the least solution at node `2` is `{0}` while MOP there is `∅` (`ugCFG_isMOPAt_two_empty`).
- **`exactness-needs-acc`.** On the chain `0 < 1 < 2 < ⋯ < ω < ω+1`, which violates the ascending chain condition and on which every monotone map is distributive (`omegaLat_monotone_distributive`), the CFG `0 → 1` with a loop `1 → 1` whose transfer is the successor map has all nodes reachable, distributive transfers, and least solution `ω+1` at node `1`, while MOP there is `ω`.

What these results do *not* show is recorded under **Boundaries**, non-claims first; each card's hypothesis ledger under **Findings** names, for every hypothesis marked tight, a kernel-checked counterexample and the class of instances it lies in.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** The definitions (quoted in full under Findings) are meant to capture the textbook monotone-framework presentation of a *forward may-analysis* in join orientation (`le a b` means `a` is at least as precise as `b`; `⊥` means "no information yet"). Meet-semilattice presentations, such as Kildall's and Kam and Ullman's, are the order dual. The model consists of:

- `Lat α`: a carrier with `le`, `join`, `bot` and no bundled laws; each law (`LeRefl`, `LeTrans`, `LeAntisymm`, `JoinLeIff`, `BotLe`) is a separate named proposition and `Lat.IsJSL` bundles all of them. The ascending chain condition `AscendingChainCondition` is well-foundedness of the reversed strict order; `HeightLe h` bounds the length of strictly ascending chains.
- `CFG n α`: nodes `Fin n`, an edge list, one entry node, an initial value at the entry, and one transfer function `f u` per node, applied along every out-edge of `u`.
- `Walk G v`: a path from the entry to `v`; its value is the composition of the transfer functions of the nodes it leaves, applied to the initial value. MOP at `v` (`IsMOPAt L G v m`) is the universal property "`m` is a least upper bound of all path values at `v`"; there is no bounded-length approximation.
- MFP is the least solution of the inequations `init ≤ x entry` and `f u (x u) ≤ x w` for every edge `u → w` (`IsLeastSolution`), i.e. the least pre-fixpoint; with monotone transfers it also satisfies the equations with equality (`isEquationSolution_of_isLeastSolution_of_monotone`).
- `kildall`: a specification-level worklist solver over lists and functions, starting with `init` at the entry and `⊥` elsewhere and with every node on the worklist; it consumes one unit of fuel per worklist pop and returns `none` when fuel runs out.

**Known gaps between the model and real analyses** (each also appears as a non-claim under Boundaries):

- `x v` and the MOP value at `v` are facts at the *entry* of `v` (before `f v`); `f v` of a node without out-edges is never applied. The fact after a sink's transfer needs an explicit exit node.
- One node-indexed transfer is applied on every out-edge; branch-sensitive (edge-specific) transfers need edge splitting. There is a single entry node (so `n ≥ 1`); several entries need a synthetic entry node. Duplicate edges are allowed and change no specification.
- MOP ranges over all syntactic walks, including branch combinations that no execution takes; no concrete program semantics is modeled, so "soundness" and "exactness" relate abstract inequation solutions to compositions of the given transfer functions only.
- No widening or narrowing; termination of the solver is proved only under a uniform height bound.
- Only forward analyses on the given edge list are formalized; backward analyses (on the reversed CFG) and interprocedural analyses are not.
- The constant-propagation lattice `cpLat` is the unsmashed product `Flat³` (a bottom per variable, strict abstract addition), not the textbook lattice with a single added bottom for unreachable code; there is no conditional-branch pruning.
- The solver seeds the worklist with all nodes; seeding only the entry (as in some compiler solvers) is not formalized.

**Scope of the theorems.** Every universally quantified result applies to every `n`, every carrier `α`, every `L : Lat α` satisfying the stated laws and every `G : CFG n α`. The degenerate cases `n = 0` and `α = Empty` are vacuous: no `CFG 0 α` and no `CFG n Empty` exists (`cfg_zero_empty`, `cfg_empty_carrier_empty`).

**Toolchain.** Lean 4 `v4.34.1` (repository `leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib and no other Lake dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyDataflow`, and no `[[require]]`).

**How the subjects relate.** The Lean toolchain is the checker for every `execution (Lean kernel check)` claim. The cited papers (Kildall 1973; Kam and Ullman 1977; Nielson, Nielson and Hankin 1999; Davey and Priestley 2002; Cousot and Cousot 1979) are prior art for the restated known results; none of their theorems is formalized here, and each card says which statement of the source it relies on. The compiler sources (CompCert `backend/Kildall.v`, rustc's `rustc_mir_dataflow` framework, LLVM's SCCP solver, each at a pinned commit) are compared with the model only in separate `derived (modeling bridge)` paragraphs under Findings; no kernel-checked claim is made about any of them.

## Findings

### Reading the statements

- **Quoting convention.** Every theorem statement below is the verbatim output of Lean's signature pretty-printer (`Lean.PrettyPrinter.ppSignature`, width 100, with `open Toy.Dataflow`) as printed by `lean/RevalidationAudit.lean`, with two edits: the keyword `theorem` is prepended (the pretty-printer prints only the name and the signature), and the declaration name is shown without its `Toy.Dataflow.` prefix. Definitions are quoted verbatim from the Lean sources, with their doc comments. The section variables `{n : Nat} {α : Type}` are implicit arguments of the definitions that mention `n` or `α`.
- Lean's pretty-printer displays the `let` binders of a statement as `have` (for example in `strict_and_genKill_exactness_needs_least` and `diamond_entry_id_matters`); the printed statement is still the complete statement. It also hides instance arguments, so `kildall_decidableRel_irrelevant` displays both sides as `kildall L G fuel` although the left side uses the instance `d1` and the right side `d2`.
- `Fin n` numerals denote nodes; `x : Fin n → α` assigns a fact to the entry of every node. In `diamond a g h f` the nodes are `0` (entry, transfer `id`), `1` and `2` (branches, transfers `g` and `h`), `3` (join, transfer `f`) and `4` (exit); `x 4` is the fact after the join node's transfer.
- Every theorem statement in this section has `Basis: execution (Lean kernel check)`; its axioms and hashes are listed under Evidence. Claims about real systems are confined to the separately labeled `Basis: derived (modeling bridge)` paragraphs.

### Core definitions (quoted from the sources)

#### Lattices (`ToyDataflow/Lattice.lean`)

`Toy.Dataflow.Lat` (ToyDataflow/Lattice.lean):

```lean
/-- The operations of a join-semilattice with bottom: an order relation `le`,
a binary `join` (intended least upper bound), and a bottom element `bot`.
No laws are bundled; see `Lat.IsJSL`. -/
structure Lat (α : Type) where
  le : α → α → Prop
  join : α → α → α
  bot : α
```

`Toy.Dataflow.Lat.LeRefl` (ToyDataflow/Lattice.lean):

```lean
/-- Reflexivity of `le`. -/
def LeRefl : Prop := ∀ a, L.le a a
```

`Toy.Dataflow.Lat.LeTrans` (ToyDataflow/Lattice.lean):

```lean
/-- Transitivity of `le`. -/
def LeTrans : Prop := ∀ a b c, L.le a b → L.le b c → L.le a c
```

`Toy.Dataflow.Lat.LeAntisymm` (ToyDataflow/Lattice.lean):

```lean
/-- Antisymmetry of `le`. -/
def LeAntisymm : Prop := ∀ a b, L.le a b → L.le b a → a = b
```

`Toy.Dataflow.Lat.JoinLeIff` (ToyDataflow/Lattice.lean):

```lean
/-- `join a b` is a least upper bound of `a` and `b`:
`join a b ≤ c` exactly when both `a ≤ c` and `b ≤ c`. -/
def JoinLeIff : Prop := ∀ a b c, L.le (L.join a b) c ↔ (L.le a c ∧ L.le b c)
```

`Toy.Dataflow.Lat.BotLe` (ToyDataflow/Lattice.lean):

```lean
/-- `bot` is below every element. -/
def BotLe : Prop := ∀ a, L.le L.bot a
```

`Toy.Dataflow.Lat.IsJSL` (ToyDataflow/Lattice.lean):

```lean
/-- All join-semilattice-with-bottom laws: `le` is a partial order, `join` is the
binary least upper bound, and `bot` is the least element. Each field is a
separate named law.

The field `trans` is redundant given `refl`, `antisymm` and `join_le_iff`
(`Lat.leTrans_of_leRefl_leAntisymm_joinLeIff`). It is kept as its own field so
that results needing only transitivity (such as the soundness theorems in
`MopMfp.lean`) can assume `LeTrans` alone. -/
structure IsJSL : Prop where
  refl : L.LeRefl
  trans : L.LeTrans
  antisymm : L.LeAntisymm
  join_le_iff : L.JoinLeIff
  bot_le : L.BotLe
```

`Toy.Dataflow.Lat.lt` (ToyDataflow/Lattice.lean):

```lean
/-- Strict order: `le a b` and `a ≠ b`. -/
def lt (a b : α) : Prop := L.le a b ∧ a ≠ b
```

`Toy.Dataflow.Lat.AscendingChainCondition` (ToyDataflow/Lattice.lean):

```lean
/-- Ascending chain condition: there is no infinite strictly ascending chain
`a₀ < a₁ < a₂ < ⋯`. Stated as well-foundedness of the reversed strict order. -/
def AscendingChainCondition : Prop := WellFounded (fun a b : α => L.lt b a)
```

`Toy.Dataflow.Lat.HeightLe` (ToyDataflow/Lattice.lean):

```lean
/-- Height bound `h`: every strictly ascending chain `c 0 < c 1 < ⋯ < c k` has at
most `h` steps (`k ≤ h`). -/
def HeightLe (h : Nat) : Prop :=
  ∀ (k : Nat) (c : Nat → α), (∀ i, i < k → L.lt (c i) (c (i + 1))) → k ≤ h
```

`Toy.Dataflow.Lat.IsUB` (ToyDataflow/Lattice.lean):

```lean
/-- `a` is an upper bound of the set `S` (a predicate). -/
def IsUB (S : α → Prop) (a : α) : Prop := ∀ b, S b → L.le b a
```

`Toy.Dataflow.Lat.IsLUB` (ToyDataflow/Lattice.lean):

```lean
/-- `a` is a least upper bound of the set `S`: an upper bound below every upper
bound. This is how infinite joins (over unboundedly many paths) are specified. -/
def IsLUB (S : α → Prop) (a : α) : Prop := L.IsUB S a ∧ ∀ u, L.IsUB S u → L.le a u
```

`Toy.Dataflow.Lat.joinList` (ToyDataflow/Lattice.lean):

```lean
/-- Join of a finite list (`bot` for the empty list). -/
def joinList : List α → α
  | [] => L.bot
  | a :: l => L.join a (joinList l)
```

`Toy.Dataflow.Monotone` (ToyDataflow/Lattice.lean):

```lean
/-- `f` is monotone: it preserves `le`. Monotone transfer functions are the
setting of monotone dataflow frameworks. -/
def Monotone (L : Lat α) (f : α → α) : Prop := ∀ a b, L.le a b → L.le (f a) (f b)
```

`Toy.Dataflow.Distributive` (ToyDataflow/Lattice.lean):

```lean
/-- `f` distributes over binary joins: `f (a ⊔ b) = f a ⊔ f b`. This is the
"distributive framework" condition (Kildall's "homomorphic" condition, dualized). -/
def Distributive (L : Lat α) (f : α → α) : Prop := ∀ a b, f (L.join a b) = L.join (f a) (f b)
```

`Toy.Dataflow.Strict` (ToyDataflow/Lattice.lean):

```lean
/-- `f` is strict: it maps `bot` to `bot`. -/
def Strict (L : Lat α) (f : α → α) : Prop := f L.bot = L.bot
```

`Toy.Dataflow.pwLat` (ToyDataflow/Lattice.lean):

```lean
/-- The pointwise order, join and bottom on `Fin n → α`. -/
def pwLat (n : Nat) {α : Type} (L : Lat α) : Lat (Fin n → α) where
  le x y := ∀ v, L.le (x v) (y v)
  join x y v := L.join (x v) (y v)
  bot _ := L.bot
```

#### CFGs, paths, MOP and MFP (`ToyDataflow/CFG.lean`)

`Toy.Dataflow.CFG` (ToyDataflow/CFG.lean):

```lean
/-- A finite control-flow graph with a node-indexed transfer function. The value
`init` holds at the entry; `f u` is applied along every out-edge of `u`. -/
structure CFG (n : Nat) (α : Type) where
  edges : List (Fin n × Fin n)
  entry : Fin n
  init : α
  f : Fin n → α → α
```

`Toy.Dataflow.Walk` (ToyDataflow/CFG.lean):

```lean
/-- A path from the entry of `G` to `v`, built by appending edges. -/
inductive Walk (G : CFG n α) : Fin n → Type
  | nil : Walk G G.entry
  | snoc {u w : Fin n} : Walk G u → (u, w) ∈ G.edges → Walk G w
```

`Toy.Dataflow.Walk.val` (ToyDataflow/CFG.lean):

```lean
/-- The value of a path: the transfer functions of the nodes it leaves, composed
in order and applied to `G.init`. -/
def val : {v : Fin n} → Walk G v → α
  | _, .nil => G.init
  | _, @Walk.snoc _ _ _ u _ p _ => G.f u p.val
```

`Toy.Dataflow.Walk.pre` (ToyDataflow/CFG.lean):

```lean
/-- The nodes a path leaves, in order (all its nodes except the last). -/
def pre : {v : Fin n} → Walk G v → List (Fin n)
  | _, .nil => []
  | _, @Walk.snoc _ _ _ u _ p _ => p.pre ++ [u]
```

`Toy.Dataflow.pathVals` (ToyDataflow/CFG.lean):

```lean
/-- The set of values of all paths from the entry to `v`. -/
def pathVals (G : CFG n α) (v : Fin n) : α → Prop := fun b => ∃ p : Walk G v, p.val = b
```

`Toy.Dataflow.IsMOPAt` (ToyDataflow/CFG.lean):

```lean
/-- MOP (join over all paths) at `v`: `m` is a least upper bound of the values of
all paths from the entry to `v`. -/
def IsMOPAt (L : Lat α) (G : CFG n α) (v : Fin n) (m : α) : Prop :=
  L.IsLUB (pathVals G v) m
```

`Toy.Dataflow.Reachable` (ToyDataflow/CFG.lean):

```lean
/-- `v` is reachable from the entry. -/
def Reachable (G : CFG n α) (v : Fin n) : Prop := Nonempty (Walk G v)
```

`Toy.Dataflow.AllReachable` (ToyDataflow/CFG.lean):

```lean
/-- Every node is reachable from the entry. -/
def AllReachable (G : CFG n α) : Prop := ∀ v, Reachable G v
```

`Toy.Dataflow.IsSolution` (ToyDataflow/CFG.lean):

```lean
/-- `x` solves the dataflow inequations: `init ≤ x entry`, and
`f u (x u) ≤ x w` for every edge `u → w`. -/
def IsSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  L.le G.init (x G.entry) ∧ ∀ u w, (u, w) ∈ G.edges → L.le (G.f u (x u)) (x w)
```

`Toy.Dataflow.IsLeastSolution` (ToyDataflow/CFG.lean):

```lean
/-- MFP: `x` is a solution that is pointwise below every solution. -/
def IsLeastSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  IsSolution L G x ∧ ∀ y, IsSolution L G y → ∀ v, L.le (x v) (y v)
```

`Toy.Dataflow.UnreachableStrict` (ToyDataflow/CFG.lean):

```lean
/-- Every node that is unreachable from the entry has a strict transfer function
(`f u bot = bot`). Holds vacuously when all nodes are reachable, and holds when
all transfer functions are strict. -/
def UnreachableStrict (L : Lat α) (G : CFG n α) : Prop :=
  ∀ u, ¬ Reachable G u → G.f u L.bot = L.bot
```

`Toy.Dataflow.eqRHS` (ToyDataflow/CFG.lean):

```lean
/-- Right-hand side of the dataflow equation at `w`: `init` (if `w` is the entry)
joined with `f u (x u)` for every edge `u → w` (listed with multiplicity). -/
def eqRHS (L : Lat α) (G : CFG n α) (x : Fin n → α) (w : Fin n) : α :=
  L.join (if w = G.entry then G.init else L.bot)
    (L.joinList ((G.edges.filter (fun e => decide (e.2 = w))).map (fun e => G.f e.1 (x e.1))))
```

`Toy.Dataflow.IsEquationSolution` (ToyDataflow/CFG.lean):

```lean
/-- `x` satisfies the dataflow equations with equality (a fixed point of `eqRHS`). -/
def IsEquationSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  ∀ w, x w = eqRHS L G x w
```

#### Diamonds (`ToyDataflow/Diamond.lean`)

`Toy.Dataflow.diamond` (ToyDataflow/Diamond.lean):

```lean
/-- The diamond CFG with initial value `a`, branch transfers `g`, `h`, and
join-node transfer `f`. -/
def diamond (a : α) (g h f : α → α) : CFG 5 α where
  edges := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
  entry := 0
  init := a
  f := fun v => if v = 1 then g else if v = 2 then h else if v = 3 then f else id
```

`Toy.Dataflow.DiamondExact` (ToyDataflow/Diamond.lean):

```lean
/-- MFP = MOP holds at every node of every diamond whose initial value lies in `I`
and whose three transfers `g`, `h`, `f` are drawn from the family `F`. -/
def DiamondExact (L : Lat α) (I : α → Prop) (F : (α → α) → Prop) : Prop :=
  ∀ a g h f, I a → F g → F h → F f →
    ∀ x, IsLeastSolution L (diamond a g h f) x → ∀ v, IsMOPAt L (diamond a g h f) v (x v)
```

`Toy.Dataflow.DistributiveOnRealizable` (ToyDataflow/Diamond.lean):

```lean
/-- Every `f ∈ F` distributes over every *realizable* pair: a pair `(g a, h a)` of
branch outputs with `g, h ∈ F` and `a ∈ I`. Weaker than distributivity over all
pairs. -/
def DistributiveOnRealizable (L : Lat α) (I : α → Prop) (F : (α → α) → Prop) : Prop :=
  ∀ a g h f, I a → F g → F h → F f → f (L.join (g a) (h a)) = L.join (f (g a)) (f (h a))
```

#### Gen/kill (`ToyDataflow/GenKill.lean`)

`Toy.Dataflow.bvLat` (ToyDataflow/GenKill.lean):

```lean
/-- The bit-vector (powerset) lattice over `Fin k`: inclusion, union, empty set. -/
def bvLat (k : Nat) : Lat (Fin k → Bool) where
  le a b := ∀ i, a i = true → b i = true
  join a b := fun i => a i || b i
  bot := fun _ => false
```

`Toy.Dataflow.bvMustLat` (ToyDataflow/GenKill.lean):

```lean
/-- Bit vectors ordered by reverse inclusion, with intersection as join and the full
set as bottom: the orientation of must analyses such as available expressions. -/
def bvMustLat (k : Nat) : Lat (Fin k → Bool) where
  le a b := ∀ i, b i = true → a i = true
  join a b := fun i => a i && b i
  bot := fun _ => true
```

`Toy.Dataflow.genKill` (ToyDataflow/GenKill.lean):

```lean
/-- A gen/kill transfer function: `f a = (a \ kill) ∪ gen`. -/
def genKill {k : Nat} (gen kill : Fin k → Bool) (a : Fin k → Bool) : Fin k → Bool :=
  fun i => (a i && !kill i) || gen i
```

#### Constant propagation (`ToyDataflow/ConstProp.lean`, `ToyDataflow/DiamondExamples.lean`)

`Toy.Dataflow.Flat` (ToyDataflow/ConstProp.lean):

```lean
/-- The flat constant lattice over `Int`. -/
inductive Flat where
  | bot
  | const (c : Int)
  | top
  deriving DecidableEq, Repr
```

`Toy.Dataflow.Flat.le` (ToyDataflow/ConstProp.lean):

```lean
/-- `a ⊑ b`: `a` is `⊥`, or `b` is `⊤`, or they are equal. -/
def le (a b : Flat) : Prop := a = bot ∨ b = top ∨ a = b
```

`Toy.Dataflow.Flat.join` (ToyDataflow/ConstProp.lean):

```lean
/-- Join: two different constants join to `⊤`. -/
def join : Flat → Flat → Flat
  | bot, b => b
  | const c, bot => const c
  | const c, const d => if c = d then const c else top
  | const _, top => top
  | top, _ => top
```

`Toy.Dataflow.Flat.add` (ToyDataflow/ConstProp.lean):

```lean
/-- Abstract addition, strict in `⊥`. -/
def add : Flat → Flat → Flat
  | bot, _ => bot
  | const _, bot => bot
  | const c, const d => const (c + d)
  | const _, top => top
  | top, bot => bot
  | top, _ => top
```

`Toy.Dataflow.St` (ToyDataflow/ConstProp.lean):

```lean
/-- Abstract states for three variables `x, y, z` (pointwise lift of `Flat`). -/
structure St where
  x : Flat
  y : Flat
  z : Flat
  deriving DecidableEq, Repr
```

`Toy.Dataflow.cpLat` (ToyDataflow/ConstProp.lean):

```lean
/-- The pointwise constant-propagation lattice on `{x, y, z}`. -/
def cpLat : Lat St where
  le s t := Flat.le s.x t.x ∧ Flat.le s.y t.y ∧ Flat.le s.z t.z
  join s t := ⟨Flat.join s.x t.x, Flat.join s.y t.y, Flat.join s.z t.z⟩
  bot := ⟨.bot, .bot, .bot⟩
```

`Toy.Dataflow.assignYZ` (ToyDataflow/ConstProp.lean):

```lean
/-- Transfer of `y := c; z := d`. -/
def assignYZ (c d : Int) (s : St) : St := { s with y := .const c, z := .const d }
```

`Toy.Dataflow.assignXYZ` (ToyDataflow/ConstProp.lean):

```lean
/-- Transfer of `x := y + z`. -/
def assignXYZ (s : St) : St := { s with x := Flat.add s.y s.z }
```

`Toy.Dataflow.cpDiamond` (ToyDataflow/ConstProp.lean):

```lean
/-- The constant-propagation diamond: branches `y := 1; z := 2` and
`y := 2; z := 1`, then `x := y + z`, with arbitrary entry state `a`. -/
def cpDiamond (a : St) : CFG 5 St := diamond a (assignYZ 1 2) (assignYZ 2 1) assignXYZ
```

`Toy.Dataflow.copyXY` (ToyDataflow/ConstProp.lean):

```lean
/-- Transfer of the copy `x := y`. -/
def copyXY (s : St) : St := { s with x := s.y }
```

`Toy.Dataflow.setY` (ToyDataflow/DiamondExamples.lean):

```lean
/-- Transfer of `y := c`. -/
def setY (c : Int) (s : St) : St := { s with y := .const c }
```

`Toy.Dataflow.setZ` (ToyDataflow/DiamondExamples.lean):

```lean
/-- Transfer of `z := c`. -/
def setZ (c : Int) (s : St) : St := { s with z := .const c }
```

#### Worklist solver (`ToyDataflow/Kildall.lean`)

`Toy.Dataflow.succs` (ToyDataflow/Kildall.lean):

```lean
/-- Successors of `u` in the edge list (with multiplicity). -/
def succs (G : CFG n α) (u : Fin n) : List (Fin n) :=
  (G.edges.filter (fun e => decide (e.1 = u))).map Prod.snd
```

`Toy.Dataflow.upd` (ToyDataflow/Kildall.lean):

```lean
/-- Pointwise update. -/
def upd (x : Fin n → α) (w : Fin n) (b : α) : Fin n → α := fun v => if v = w then b else x v
```

`Toy.Dataflow.propagate` (ToyDataflow/Kildall.lean):

```lean
/-- Propagate `out` into each listed successor, pushing every successor whose
value is updated. -/
def propagate (L : Lat α) [DecidableRel L.le] (out : α) :
    List (Fin n) → (Fin n → α) → List (Fin n) → (Fin n → α) × List (Fin n)
  | [], x, wl => (x, wl)
  | w :: ws, x, wl =>
    if L.le out (x w) then propagate L out ws x wl
    else propagate L out ws (upd x w (L.join (x w) out)) (w :: wl)
```

`Toy.Dataflow.kildallInit` (ToyDataflow/Kildall.lean):

```lean
/-- Initial assignment: `init` at the entry, `bot` elsewhere. -/
def kildallInit (L : Lat α) (G : CFG n α) : Fin n → α :=
  fun v => if v = G.entry then G.init else L.bot
```

`Toy.Dataflow.kildallLoop` (ToyDataflow/Kildall.lean):

```lean
/-- The worklist loop; one unit of fuel per step (including the final step that
observes an empty worklist). -/
def kildallLoop (L : Lat α) [DecidableRel L.le] (G : CFG n α) :
    Nat → (Fin n → α) → List (Fin n) → Option (Fin n → α)
  | 0, _, _ => none
  | _ + 1, x, [] => some x
  | fuel + 1, x, u :: wl =>
    let r := propagate L (G.f u (x u)) (succs G u) x wl
    kildallLoop L G fuel r.1 r.2
```

`Toy.Dataflow.kildall` (ToyDataflow/Kildall.lean):

```lean
/-- The solver: all nodes initially on the worklist. -/
def kildall (L : Lat α) [DecidableRel L.le] (G : CFG n α) (fuel : Nat) : Option (Fin n → α) :=
  kildallLoop L G fuel (kildallInit L G) (List.finRange n)
```

### Definition adequacy (positive and negative examples)

The lattice laws are tested by structures that violate exactly one law or a recorded set of laws (`*_law_profile`), and the lattice instances used by the witnesses are shown to satisfy the laws, the ascending chain condition and height bounds where claimed. These theorems are not referenced by a card, so no statement hash is recorded for them; they are covered by the package-wide axiom audit.

```lean
theorem IsLeastSolution.unique {n : Nat} {α : Type} {L : Lat α} (hL : L.IsJSL) {G : CFG n α}
  {x y : Fin n → α} (hx : IsLeastSolution L G x) (hy : IsLeastSolution L G y) : x = y
```

```lean
theorem IsMOPAt.unique {n : Nat} {α : Type} {L : Lat α} (hL : L.IsJSL) {G : CFG n α}
  {v : Fin n} {a b : α} (ha : IsMOPAt L G v a) (hb : IsMOPAt L G v b) : a = b
```

```lean
theorem Lat.leTrans_of_leRefl_leAntisymm_joinLeIff {α : Type} {L : Lat α} (hrefl : L.LeRefl)
  (hanti : L.LeAntisymm) (hjoin : L.JoinLeIff) : L.LeTrans
```

```lean
theorem Walk.val_eq_foldl {n : Nat} {α : Type} {G : CFG n α} {v : Fin n} (p : Walk G v) :
  p.val = List.foldl (fun a u => G.f u a) G.init p.pre
```

```lean
theorem boolLat_heightLe_one : boolLat.HeightLe 1
```

```lean
theorem boolLat_isJSL : boolLat.IsJSL
```

```lean
theorem boolLat_not_heightLe_zero : ¬boolLat.HeightLe 0
```

```lean
theorem bvLat_heightLe (k : Nat) : (bvLat k).HeightLe k
```

```lean
theorem bvLat_isJSL (k : Nat) : (bvLat k).IsJSL
```

```lean
theorem bvMustLat_isJSL (k : Nat) : (bvMustLat k).IsJSL
```

```lean
theorem cpLat_heightLe : cpLat.HeightLe 6
```

```lean
theorem cpLat_isJSL : cpLat.IsJSL
```

```lean
theorem fin4PreLat_law_profile :
  fin4PreLat.LeRefl ∧
    ¬fin4PreLat.LeTrans ∧ ¬fin4PreLat.LeAntisymm ∧ fin4PreLat.JoinLeIff ∧ fin4PreLat.BotLe
```

```lean
theorem finChainLat_heightLe (h : Nat) : (finChainLat h).HeightLe h
```

```lean
theorem finChainLat_isJSL (h : Nat) : (finChainLat h).IsJSL
```

```lean
theorem isMOPAt_bot_of_not_reachable {n : Nat} {α : Type} {L : Lat α} (hL : L.IsJSL)
  {G : CFG n α} {v : Fin n} (hv : ¬Reachable G v) : IsMOPAt L G v L.bot
```

```lean
theorem isSolution_iff_eqRHS_le {n : Nat} {α : Type} {L : Lat α} (hL : L.IsJSL) (G : CFG n α)
  (x : Fin n → α) : IsSolution L G x ↔ (pwLat n L).le (eqRHS L G x) x
```

```lean
theorem natMaxLat_isJSL : natMaxLat.IsJSL
```

```lean
theorem natMaxLat_not_acc : ¬natMaxLat.AscendingChainCondition
```

```lean
theorem natMaxLat_not_heightLe (h : Nat) : ¬natMaxLat.HeightLe h
```

```lean
theorem no_lat_violates_only_leTrans {α : Type} :
  ¬∃ L, L.LeRefl ∧ ¬L.LeTrans ∧ L.LeAntisymm ∧ L.JoinLeIff ∧ L.BotLe
```

```lean
theorem notAntisymmLat_law_profile :
  notAntisymmLat.LeRefl ∧
    notAntisymmLat.LeTrans ∧
      ¬notAntisymmLat.LeAntisymm ∧ notAntisymmLat.JoinLeIff ∧ notAntisymmLat.BotLe
```

```lean
theorem notBotLat_law_profile :
  notBotLat.LeRefl ∧
    notBotLat.LeTrans ∧ notBotLat.LeAntisymm ∧ notBotLat.JoinLeIff ∧ ¬notBotLat.BotLe
```

```lean
theorem notJoinLat_law_profile :
  notJoinLat.LeRefl ∧
    notJoinLat.LeTrans ∧ notJoinLat.LeAntisymm ∧ ¬notJoinLat.JoinLeIff ∧ notJoinLat.BotLe
```

```lean
theorem notReflLat_law_profile :
  ¬notReflLat.LeRefl ∧
    notReflLat.LeTrans ∧ notReflLat.LeAntisymm ∧ notReflLat.JoinLeIff ∧ notReflLat.BotLe
```

```lean
theorem notTransLat_law_profile :
  notTransLat.LeRefl ∧
    ¬notTransLat.LeTrans ∧ notTransLat.LeAntisymm ∧ ¬notTransLat.JoinLeIff ∧ ¬notTransLat.BotLe
```

```lean
theorem omegaLat_isJSL : omegaLat.IsJSL
```

```lean
theorem omegaLat_not_acc : ¬omegaLat.AscendingChainCondition
```

```lean
theorem unboundedChainsLat_acc : unboundedChainsLat.AscendingChainCondition
```

```lean
theorem unboundedChainsLat_isJSL : unboundedChainsLat.IsJSL
```

```lean
theorem unboundedChainsLat_not_heightLe (h : Nat) : ¬unboundedChainsLat.HeightLe h
```

```lean
theorem withBotIntLat_isJSL : withBotIntLat.IsJSL
```

```lean
theorem withBotIntLat_not_acc : ¬withBotIntLat.AscendingChainCondition
```

### Results

#### `mop-le-solution-soundness`: Soundness: MOP ⊑ every solution (monotone transfers, transitive order)

- **Kind:** theorem. **Tier:** T0. Textbook soundness of the MFP solution for monotone frameworks (Nielson-Nielson-Hankin, Section 2.4; slide 79 of the authors' Chapter 2 transparencies), restated in this vocabulary and strengthened from 'the least solution' to 'every solution' and from a partial order to any transitive relation.
- **Depth:** shallow. Induction on the path, then the universal property of the least upper bound.
- **Plain claim.** On a finite CFG whose transfer functions are all monotone, and for any transitive binary relation L.le (reflexivity and antisymmetry are not assumed), the value of every path from the entry to a node v is L.le-below x v for every solution x of the dataflow inequations (init ≤ x entry and f u (x u) ≤ x w for each edge u → w); hence if m is a least upper bound of all path values at v (the MOP value), then m ≤ x v, in particular for the least solution (MFP). This relates solutions of the abstract inequations to the join over syntactic CFG paths; no concrete program semantics is involved.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem walk_val_le_of_isSolution_of_monotone {n : Nat} {α : Type} (L : Lat α) (G : CFG n α)
  (htrans : L.LeTrans) (hmono : ∀ (u : Fin n), Monotone L (G.f u)) {x : Fin n → α}
  (hx : IsSolution L G x) {v : Fin n} (p : Walk G v) : L.le p.val (x v)
```

```lean
theorem mop_le_of_isSolution_of_monotone {n : Nat} {α : Type} (L : Lat α) (G : CFG n α)
  (htrans : L.LeTrans) (hmono : ∀ (u : Fin n), Monotone L (G.f u)) {x : Fin n → α}
  (hx : IsSolution L G x) {v : Fin n} {m : α} (hm : IsMOPAt L G v m) : L.le m (x v)
```

**Hypothesis ledger.**

- `htrans : L.LeTrans` — Chains the per-edge inequations along a path. The only law assumed of L.le (reflexivity and antisymmetry are not used).
  - Hypothesis of: `walk_val_le_of_isSolution_of_monotone`, `mop_le_of_isSolution_of_monotone`.
  - Tightness: **tight** — counterexample(s) for `walk_val_le_of_isSolution_of_monotone`: `soundness_needs_leTrans`; for `mop_le_of_isSolution_of_monotone`: `soundness_needs_leTrans`.
  - Witness class: soundness_needs_leTrans: the 3-node path CFG notTransCFG (0 → 1 → 2, identity transfers) over the 3-element carrier Fin 3 with the non-transitive relation notTransLat; the identity assignment is a solution, the MOP value at node 2 is 0, 0 is not below x 2 = 2, and some walk value is not below x 2.
- `hmono : ∀ u, Monotone L (G.f u)` — Pushes the inductive bound p.val ≤ x u through f u.
  - Hypothesis of: `walk_val_le_of_isSolution_of_monotone`, `mop_le_of_isSolution_of_monotone`.
  - Tightness: **tight** — counterexample(s) for `walk_val_le_of_isSolution_of_monotone`: `soundness_needs_monotone`; for `mop_le_of_isSolution_of_monotone`: `soundness_needs_monotone`.
  - Witness class: soundness_needs_monotone: the 2-node CFG notCFG (self-loop at the entry and an edge 0 → 1, every transfer is negation) over boolLat; even the least solution notSol fails the bound at node 1 (MOP value true), and some walk value is not below notSol 1.
- `hx : IsSolution L G x` — The bound is only claimed for solutions of the inequations.
  - Hypothesis of: `walk_val_le_of_isSolution_of_monotone`, `mop_le_of_isSolution_of_monotone`.
  - Tightness: **tight** — counterexample(s) for `walk_val_le_of_isSolution_of_monotone`: `soundness_needs_solution`; for `mop_le_of_isSolution_of_monotone`: `soundness_needs_solution`.
  - Witness class: soundness_needs_solution: the 2-node gen/kill loop loopGK over 2-bit vectors bvLat 2 with the assignment x = ∅ everywhere, which is not a solution; the MOP value at node 1 and some walk value are not below x 1.
- `hm : IsMOPAt L G v m` — Identifies m as the least upper bound of the path values at v; only its leastness is used.
  - Hypothesis of: `mop_le_of_isSolution_of_monotone`.
  - Tightness: **tight** — counterexample(s) for `mop_le_of_isSolution_of_monotone`: `soundness_needs_isMOPAt`.
  - Witness class: soundness_needs_isMOPAt: loopGK over bvLat 2 with the least solution loopGKSol and the value m = full set at node 0, which is not the MOP value there and is not below loopGKSol 0.

**Non-vacuity witness.** The gen/kill loop 0 → 1, 1 → 1 on 2-bit vectors (node 0 gens bit 0; node 1 gens bit 1 and kills bit 0) with its least solution (∅ at node 0, {0,1} at node 1) and MOP {0,1} at node 1. Lean: `soundness_nonvacuous`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `exactness_needs_distributive`, `exists_isMOPAt_of_acc`, `isEquationSolution_of_isLeastSolution_of_monotone`, `notCFG_isLeastSolution_not_isEquationSolution`.

**Prior art.**

- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.
- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162). Works over a finite meet-semilattice with transfer functions having the 'homomorphism property' f(N, x ^ y) = f(N, x) ^ f(N, y) (distributivity, in the dual orientation); Algorithm A is a worklist algorithm; Theorem 1 states that it terminates; Theorem 2 relates the final pool at each node N to the values propagated along all paths from entry nodes to N. Exact bounds and formulas of the paper are not quoted here.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `mop-le-solution-soundness`.

#### `mfp-eq-mop-exactness`: Exactness: MFP = MOP under distributivity, ACC and strictness at unreachable nodes

- **Kind:** theorem. **Tier:** T1. The distributive case MFP = MOP is classical (Kildall; Kam-Ullman; Nielson-Nielson-Hankin, Section 2.4), but no mechanized MFP = MOP statement was found. The statement here makes the side conditions explicit: the ascending chain condition, and strictness only at unreachable nodes, which covers both the 'all nodes reachable' form (Nielson-Nielson-Hankin) and the 'all transfers strict' form.
- **Depth:** substantive. Needs the ascending-chain argument that every set has a least upper bound attained by a finite join (maximal-element extraction from well-foundedness), distributivity over finite joins, construction of the MOP assignment as a solution, soundness for the reverse inequality, and, for existence, well-foundedness of the pointwise order on assignments.
- **Plain claim.** In a join-semilattice with bottom satisfying the ascending chain condition (ACC), if every transfer function distributes over binary joins and every node unreachable from the entry has a strict transfer function (f u ⊥ = ⊥), then the dataflow inequations have a least solution, and for every least solution x and every node v, x v is a least upper bound of the values of all paths from the entry to v (MFP = MOP). Two corollaries replace the unreachable-node condition by 'every node is reachable' or by 'every transfer function is strict'. Separately, under ACC the inequations have a least solution whenever every transfer function is monotone.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict {n : Nat} {α : Type}
  (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
  (hdist : ∀ (u : Fin n), Distributive L (G.f u)) (hstrict : UnreachableStrict L G) {x : Fin n → α}
  (hx : IsLeastSolution L G x) (v : Fin n) : IsMOPAt L G v (x v)
```

```lean
theorem isMOPAt_of_isLeastSolution_of_distributive_of_allReachable {n : Nat} {α : Type}
  (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
  (hdist : ∀ (u : Fin n), Distributive L (G.f u)) (hreach : AllReachable G) {x : Fin n → α}
  (hx : IsLeastSolution L G x) (v : Fin n) : IsMOPAt L G v (x v)
```

```lean
theorem isMOPAt_of_isLeastSolution_of_distributive_of_strict {n : Nat} {α : Type} (L : Lat α)
  (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
  (hdist : ∀ (u : Fin n), Distributive L (G.f u)) (hstrict : ∀ (u : Fin n), Strict L (G.f u))
  {x : Fin n → α} (hx : IsLeastSolution L G x) (v : Fin n) : IsMOPAt L G v (x v)
```

```lean
theorem exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict {n : Nat}
  {α : Type} (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
  (hdist : ∀ (u : Fin n), Distributive L (G.f u)) (hstrict : UnreachableStrict L G) :
  ∃ x, IsLeastSolution L G x ∧ ∀ (v : Fin n), IsMOPAt L G v (x v)
```

```lean
theorem exists_isLeastSolution_of_monotone_of_acc {n : Nat} {α : Type} (L : Lat α)
  (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
  (hmono : ∀ (u : Fin n), Monotone L (G.f u)) : ∃ x, IsLeastSolution L G x
```

**Hypothesis ledger.**

- `hL : L.IsJSL` — Partial order, binary least upper bounds, bottom: used to form finite joins and compare them. The intended setting; not weakened further here.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`, `isMOPAt_of_isLeastSolution_of_distributive_of_strict`, `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`, `exists_isLeastSolution_of_monotone_of_acc`.
  - Tightness: **harmless** — the intended setting (all join-semilattice-with-bottom laws); no weakening is studied and no counterexample is claimed.
- `hacc : L.AscendingChainCondition` — Makes the (possibly infinite) set of path values at each node have a least upper bound that is a finite join of path values, to which binary distributivity applies; gives existence of the least solution.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`, `isMOPAt_of_isLeastSolution_of_distributive_of_strict`, `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`, `exists_isLeastSolution_of_monotone_of_acc`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`: `exactness_needs_acc`; for `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`: `exactness_needs_acc`; for `isMOPAt_of_isLeastSolution_of_distributive_of_strict`: `strict_exactness_needs_acc`; for `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`: `exactness_needs_acc`, `exists_exactness_counterexamples`, `exists_exactness_combined_counterexamples`; for `exists_isLeastSolution_of_monotone_of_acc`: `exists_isLeastSolution_counterexamples`.
  - Witness class: exactness_needs_acc (unreachable-strict and all-reachable forms): the 2-node CFG omegaCFG (0 → 1, loop 1 → 1 with the successor transfer) over the chain omegaLat = 0 < 1 < 2 < ⋯ < ω < ω+1, all nodes reachable; strict_exactness_needs_acc (all-strict form): the analogous strict loop omegaStrictCFG over omegaLat; exists_exactness_combined_counterexamples, first conjunct (existence form): omegaCFG over omegaLat; exists_isLeastSolution_counterexamples, first conjunct (exists_isLeastSolution_of_monotone_of_acc): the 1-node successor self-loop succCFG over natMaxLat (natural numbers under max), which has no least solution. exactness_needs_acc and strict_exactness_needs_acc fix one least solution and refute the conclusion at node 1; exists_exactness_counterexamples supplies only the failing existential conclusion and is used together with exactness_needs_acc.
- `hdist : ∀ u, Distributive L (G.f u)` — Lets each transfer function commute with the finite join of path values at its source; implies monotonicity (monotone_of_distributive).
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`, `isMOPAt_of_isLeastSolution_of_distributive_of_strict`, `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`: `exactness_needs_distributive`; for `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`: `exactness_needs_distributive`; for `isMOPAt_of_isLeastSolution_of_distributive_of_strict`: `strict_exactness_needs_distributive`; for `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`: `exactness_needs_distributive`, `exists_exactness_counterexamples`, `exists_exactness_combined_counterexamples`.
  - Witness class: exactness_needs_distributive (unreachable-strict and all-reachable forms): the 5-node constant-propagation diamond cpDiamond ⟨⊤, ⊤, ⊤⟩ over cpLat, all nodes reachable, monotone but not distributive transfers; strict_exactness_needs_distributive (all-strict form): the 5-node diamond strictBBDiamond over bvLat 2 with strict, monotone, non-distributive transfers; exists_exactness_combined_counterexamples, second conjunct (existence form): cpDiamond ⟨⊤, ⊤, ⊤⟩ over cpLat. exists_exactness_counterexamples supplies only the failing existential conclusion and is used together with exactness_needs_distributive.
- `hstrict : UnreachableStrict L G` — At an unreachable node the MOP value is ⊥; a non-strict transfer there injects f u ⊥ into its successors, which no path from the entry accounts for.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`: `exactness_needs_unreachableStrict`; for `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict`: `exactness_needs_unreachableStrict`, `exists_exactness_counterexamples`, `exists_exactness_combined_counterexamples`.
  - Witness class: exactness_needs_unreachableStrict: the acyclic 3-node gen/kill CFG ugCFG over 1-bit vectors bvLat 1 (edges 0 → 2 and 1 → 2; node 1 has no incoming edge and gen set {0}); node 2 is reachable and the least solution ugSol is not MOP at node 2; exists_exactness_combined_counterexamples, third conjunct (existence form): ugCFG over bvLat 1. exists_exactness_counterexamples supplies only the failing existential conclusion and is used together with exactness_needs_unreachableStrict.
- `hreach : AllReachable G` — Every node is reachable, so UnreachableStrict holds vacuously.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`: `exactness_needs_unreachableStrict`, `exactness_corollaries_need_allReachable_or_strict`, `exactness_corollaries_combined_counterexample`.
  - Witness class: exactness_corollaries_combined_counterexample: ugCFG over bvLat 1; hL, hacc and hdist hold, not every node is reachable, the least solution ugSol is not MOP at node 2. The same facts are split over exactness_needs_unreachableStrict (hL, hacc, hdist) and exactness_corollaries_need_allReachable_or_strict (the rest).
- `hstrict : ∀ u, Strict L (G.f u)` — Every transfer is strict, so UnreachableStrict holds.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_strict`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_strict`: `exactness_needs_unreachableStrict`, `exactness_corollaries_need_allReachable_or_strict`, `exactness_corollaries_combined_counterexample`.
  - Witness class: exactness_corollaries_combined_counterexample: ugCFG over bvLat 1; hL, hacc and hdist hold, not every transfer is strict, the least solution ugSol is not MOP at node 2. The same facts are split over exactness_needs_unreachableStrict (hL, hacc, hdist) and exactness_corollaries_need_allReachable_or_strict (the rest).
- `hx : IsLeastSolution L G x` — The claim is about least solutions; larger solutions over-approximate MOP.
  - Hypothesis of: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`, `isMOPAt_of_isLeastSolution_of_distributive_of_strict`.
  - Tightness: **tight** — counterexample(s) for `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`: `exactness_needs_least`; for `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`: `exactness_needs_least`; for `isMOPAt_of_isLeastSolution_of_distributive_of_strict`: `strict_and_genKill_exactness_needs_least`.
  - Witness class: exactness_needs_least (unreachable-strict and all-reachable forms): loopGK over bvLat 2 with the solution x = full set everywhere, which is not least and not MOP at node 0; strict_and_genKill_exactness_needs_least (all-strict form): the 1-node gen/kill self-loop with gen = kill = ∅ over bvLat 1 (every transfer strict, all nodes reachable) with the solution x = full set, which is not least and not MOP at node 0.
- `hmono : ∀ u, Monotone L (G.f u)` — Existence of the least solution without distributivity.
  - Hypothesis of: `exists_isLeastSolution_of_monotone_of_acc`.
  - Tightness: **tight** — counterexample(s) for `exists_isLeastSolution_of_monotone_of_acc`: `exists_isLeastSolution_counterexamples`.
  - Witness class: exists_isLeastSolution_counterexamples, second conjunct: the 5-node diamond over boolLat with initial value false, branch transfers id and negation and join transfer negation (diamond false id not not); boolLat satisfies the lattice laws and the ascending chain condition, the transfers are not all monotone, and no least solution exists.

**Non-vacuity witness.** The gen/kill loop 0 → 1, 1 → 1 on 2-bit vectors (all nodes reachable); a strict gen/kill loop (all transfers strict); a CFG with an unreachable strict node and a reachable non-strict node (covered by neither corollary); and a lattice with ACC but no finite height. The existence form also holds, with all its hypotheses, on the one-node self-loop stepMidCFG m over unboundedChainsLat (ascending chain condition, no finite height) for every m (cyclic_exactness_on_unboundedChainsLat). Lean: `exactness_nonvacuous`, `strict_exactness_nonvacuous`, `unreachableStrict_strictly_between_nonvacuous`, `exactness_holds_on_unboundedChainsLat`, `cyclic_exactness_on_unboundedChainsLat`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `acc_strictly_weaker_than_heightLe`, `cfg_empty_carrier_empty`, `cfg_zero_empty`, `kildall_acc_has_no_uniform_fuel`, `kildall_isSome_of_heightLe`, `monotone_of_distributive`, `stepMid_distributive`.

**Prior art.**

- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162). Works over a finite meet-semilattice with transfer functions having the 'homomorphism property' f(N, x ^ y) = f(N, x) ^ f(N, y) (distributivity, in the dual orientation); Algorithm A is a worklist algorithm; Theorem 1 states that it terminates; Theorem 2 relates the final pool at each node N to the values propagated along all paths from entry nodes to N. Exact bounds and formulas of the paper are not quoted here.
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.
- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- T. J. Marlowe and B. G. Ryder, "Properties of data flow frameworks: a unified model", Acta Informatica 28(2):121-163, 1990, doi:10.1007/BF01237234. A unified classification of data flow framework properties (distributivity, monotonicity and related conditions).
- CompCert, file backend/Kildall.v, repository AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (last change to the file: 4710ec093ddea8e6eb86ad519df61c59b654e861). Module Dataflow_Solver: fixpoint seeds the worklist with the entry point only and proves fixpoint_solution (every edge inequation holds) under the hypothesis 'forall n, L.eq (transf n L.bot) L.bot'; fixpoint_allnodes starts with every node at L.bot and every node on the worklist and proves fixpoint_allnodes_solution without that hypothesis; fixpoint_nodeset_solution proves that a solver seeded with a given set of nodes satisfies the inequations at every program point reachable from those nodes; fixpoint_entry and fixpoint_invariant are also proved. No least-solution or MOP statement is proved, monotonicity of transfer functions is never assumed, and iteration is bounded by fuel (PrimIter), returning None when fuel is exhausted.
- Y. Bertot, B. Grégoire, X. Leroy, "A structured approach to proving compiler optimizations based on dataflow analysis", Types for Proofs and Programs (TYPES 2004), LNCS 3839, pp. 66-81, Springer, 2006, doi:10.1007/11617990_5. Coq proofs of dataflow-based optimizations in the line of work leading to CompCert's dataflow solver.
- A search of the Archive of Formal Proofs (static-analysis and Kildall entries), Coq/Rocq developments (rocq-archive/kildall, CompCert), Lean mathlib (Order.FixedPoints) and Agda sources, and web searches pairing 'meet over all paths'/MOP/MFP with Coq, Isabelle, Agda and Lean, found mechanized least-fixpoint (MFP) solvers but no mechanized MFP = MOP statement; this is not proof of absence.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `mfp-eq-mop-exactness`.

#### `diamond-exactness-characterization`: Exactness on five-node diamonds characterized by distributivity on realizable pairs

- **Kind:** characterization. **Tier:** T1. That monotone non-distributive frameworks have instances with MOP ≠ MFP is due to Kam and Ullman (abstract). The exact diamond characterization here (the quantifier over realizable pairs, the role of monotonicity, the constant-closed corollaries) is not claimed to appear there; no mechanization was found.
- **Depth:** shallow. Explicit enumeration of the path values of the five-node diamond and of its least solution; MFP and MOP can only differ at the exit node. The ascending-chain form adds a maximal-element argument (monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty).
- **Plain claim.** In a join-semilattice with bottom L (L.IsJSL), consider the five-node diamond CFG: an entry node with initial value a ∈ I and transfer id, two single-node branches with transfers g, h ∈ F, a join node with transfer f ∈ F, and an exit node. (i) If every f ∈ F distributes over every realizable pair (g a, h a) with g, h ∈ F and a ∈ I, then on every such diamond every least solution equals MOP at every node (without a monotonicity hypothesis). (ii) Conversely, if every member of F is monotone and every such diamond is exact, then F distributes over every realizable pair. (iii) If F contains every constant function, I is non-empty, and either every member of F is monotone or L satisfies the ascending chain condition, then exactness on all such diamonds is equivalent to full distributivity of every member of F (in the ascending-chain case, exactness on all such diamonds forces every member of F to be monotone: monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty). The entry transfer is fixed to id whatever F is.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem diamondExact_iff_distributiveOnRealizable_of_monotone {α : Type} {L : Lat α}
  (hL : L.IsJSL) (I : α → Prop) (F : (α → α) → Prop) (hmono : ∀ (φ : α → α), F φ → Monotone L φ) :
  DiamondExact L I F ↔ DistributiveOnRealizable L I F
```

```lean
theorem diamondExact_of_distributiveOnRealizable {α : Type} {L : Lat α} (hL : L.IsJSL)
  {I : α → Prop} {F : (α → α) → Prop} (hd : DistributiveOnRealizable L I F) : DiamondExact L I F
```

```lean
theorem distributiveOnRealizable_of_diamondExact_of_monotone {α : Type} {L : Lat α}
  (hL : L.IsJSL) {I : α → Prop} {F : (α → α) → Prop} (hmono : ∀ (φ : α → α), F φ → Monotone L φ)
  (he : DiamondExact L I F) : DistributiveOnRealizable L I F
```

```lean
theorem diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty {α : Type}
  {L : Lat α} (hL : L.IsJSL) (I : α → Prop) (F : (α → α) → Prop)
  (hmono : ∀ (φ : α → α), F φ → Monotone L φ) (hconst : ∀ (b : α), F fun x => b) (hI : ∃ a, I a) :
  DiamondExact L I F ↔ ∀ (f : α → α), F f → Distributive L f
```

```lean
theorem diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty {α : Type} {L : Lat α}
  (hL : L.IsJSL) (hacc : L.AscendingChainCondition) (I : α → Prop) (F : (α → α) → Prop)
  (hconst : ∀ (b : α), F fun x => b) (hI : ∃ a, I a) :
  DiamondExact L I F ↔ ∀ (f : α → α), F f → Distributive L f
```

**Hypothesis ledger.**

- `hL : L.IsJSL` — Lattice laws for least upper bounds and uniqueness of least solutions and of MOP values. The intended setting; not weakened further here.
  - Hypothesis of: `diamondExact_iff_distributiveOnRealizable_of_monotone`, `diamondExact_of_distributiveOnRealizable`, `distributiveOnRealizable_of_diamondExact_of_monotone`, `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`, `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`.
  - Tightness: **harmless** — the intended setting (all join-semilattice-with-bottom laws); no weakening is studied and no counterexample is claimed.
- `hmono : ∀ φ, F φ → Monotone L φ` — Guarantees that each diamond built from F has a least solution, so that exactness can be tested at each realizable pair.
  - Hypothesis of: `diamondExact_iff_distributiveOnRealizable_of_monotone`, `distributiveOnRealizable_of_diamondExact_of_monotone`, `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`.
  - Tightness: **tight** — counterexample(s) for `diamondExact_iff_distributiveOnRealizable_of_monotone`: `diamondExact_needs_monotone`; for `distributiveOnRealizable_of_diamondExact_of_monotone`: `diamondExact_needs_monotone`; for `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`: `diamondExact_const_mem_needs_monotone`.
  - Witness class: diamondExact_needs_monotone (the two realizable-pair theorems that assume hmono): 5-node diamonds over boolLat with the family idNotFamily = {id, negation} and initial values {false}; DiamondExact holds and DistributiveOnRealizable fails. diamondExact_const_mem_needs_monotone (monotone constant-closed corollary): 5-node diamonds over withBotIntLat (integers with an added bottom; no ascending chain condition) with the family wbNegFamily (all constants and negation) and all initial values; hconst and hI hold, DiamondExact holds, and not every member is distributive.
- `hacc : L.AscendingChainCondition` — Lets exactness on all diamonds force monotonicity of a constant-closed family (a non-monotone member has a maximal witness u < v with f u ≰ f v).
  - Hypothesis of: `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`.
  - Tightness: **tight** — counterexample(s) for `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`: `diamondExact_const_mem_needs_monotone`.
  - Witness class: diamondExact_const_mem_needs_monotone: withBotIntLat with wbNegFamily and all initial values; the lattice laws, hconst and hI hold, the ascending chain condition fails, DiamondExact holds, and not every member is distributive.
- `hconst : ∀ b, F (fun _ => b)` — Makes every pair realizable, turning the realizable-pair condition into full distributivity.
  - Hypothesis of: `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`, `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`.
  - Tightness: **tight** — counterexample(s) for `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`: `diamondExact_singleton_of_not_distributive`; for `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`: `diamondExact_singleton_of_not_distributive`.
  - Witness class: diamondExact_singleton_of_not_distributive: 5-node diamonds over cpLat with the one-element family {assignXYZ} (x := y + z) and all initial values; hL, hacc, hmono and hI hold, the family contains no constant function, DiamondExact holds, and assignXYZ is not distributive.
- `hI : ∃ a, I a` — With no initial values every diamond condition is vacuous.
  - Hypothesis of: `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`, `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`.
  - Tightness: **tight** — counterexample(s) for `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`: `diamondExact_const_needs_nonempty_init`; for `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`: `diamondExact_const_needs_nonempty_init`.
  - Witness class: diamondExact_const_needs_nonempty_init: cpLat with the family of all constants together with assignXYZ and the empty set of initial values; hL, hacc, hmono and hconst hold, DiamondExact holds vacuously, and not every member is distributive.
- `hd : DistributiveOnRealizable L I F` — The sufficient condition of direction (i).
  - Hypothesis of: `diamondExact_of_distributiveOnRealizable`.
  - Tightness: **tight** — counterexample(s) for `diamondExact_of_distributiveOnRealizable`: `diamondExact_iff_nonvacuous`, `diamondExact_needs_distributiveOnRealizable`.
  - Witness class: diamondExact_needs_distributiveOnRealizable: cpLat with the family cpFamily = {y := 1; z := 2, y := 2; z := 1, x := y + z} and all initial values; hL holds, DistributiveOnRealizable fails, DiamondExact fails. diamondExact_iff_nonvacuous proves hL and the failure of DiamondExact on the same instance (the failure of DistributiveOnRealizable then follows from diamondExact_of_distributiveOnRealizable).
- `he : DiamondExact L I F` — The premise of direction (ii).
  - Hypothesis of: `distributiveOnRealizable_of_diamondExact_of_monotone`.
  - Tightness: **tight** — counterexample(s) for `distributiveOnRealizable_of_diamondExact_of_monotone`: `diamondExact_const_mem_nonvacuous`.
  - Witness class: diamondExact_const_mem_nonvacuous, second conjunct: cpLat with the family of all constants together with cpFamily and all initial values; hL and hmono hold, DiamondExact fails, DistributiveOnRealizable fails.

**Non-vacuity witness.** Gen/kill functions on 1-bit vectors with all initial values (monotone, constant-closed family; both sides true), and the constant-propagation family {y:=1;z:=2, y:=2;z:=1, x:=y+z}, also with all constants added (monotone family; both sides false). Lean: `diamondExact_iff_nonvacuous`, `diamondExact_const_mem_nonvacuous`.

**Positive control** (a nearby setting where the negative conclusion does not occur): `diamondExact_singleton_of_not_distributive`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `diamondExact_not_exact_on_two_step_branches`, `diamond_entry_id_matters`, `isEquationSolution_of_isLeastSolution_of_monotone`, `monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty`, `notCFG_isLeastSolution_not_isEquationSolution`.

**Prior art.**

- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.
- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `diamond-exactness-characterization`.

#### `constant-propagation-not-exact`: Constant propagation: MFP ≠ MOP on a diamond (monotone, not distributive)

- **Kind:** counterexample. **Tier:** T0. The standard example that constant propagation is a monotone but non-distributive framework (Nielson-Nielson-Hankin, Section 2.3.3), restated and checked in this vocabulary.
- **Depth:** shallow. Direct computation using the diamond lemmas.
- **Plain claim.** In the unsmashed pointwise flat constant-propagation lattice over variables x, y, z, for the program whose two branches are 'y := 1; z := 2' and 'y := 2; z := 1' followed by 'x := y + z': for every entry state a, the diamond has a least solution, and every least solution x has x 4 = (x = ⊤, y = ⊤, z = ⊤) after the assignment, while the MOP value there is (x = 3, y = ⊤, z = ⊤), so MFP ≠ MOP; the transfer of 'x := y + z' is monotone (assignXYZ_monotone) but not distributive (assignXYZ_not_distributive).

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem cpDiamond_mfp_x_top_ne_mop_x_const3 (a : St) {x : Fin 5 → St}
  (hx : IsLeastSolution cpLat (cpDiamond a) x) :
  x 4 = { x := Flat.top, y := Flat.top, z := Flat.top } ∧
    IsMOPAt cpLat (cpDiamond a) 4 { x := Flat.const 3, y := Flat.top, z := Flat.top } ∧
      ¬IsMOPAt cpLat (cpDiamond a) 4 (x 4)
```

```lean
theorem cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3 (a : St) :
  ∃ x,
    IsLeastSolution cpLat (cpDiamond a) x ∧
      x 4 = { x := Flat.top, y := Flat.top, z := Flat.top } ∧
        IsMOPAt cpLat (cpDiamond a) 4 { x := Flat.const 3, y := Flat.top, z := Flat.top } ∧
          ¬IsMOPAt cpLat (cpDiamond a) 4 (x 4)
```

```lean
theorem assignXYZ_not_distributive : ¬Distributive cpLat assignXYZ
```

The clause "the transfer of 'x := y + z' is monotone" of the plain claim is proved by the supporting theorem `assignXYZ_monotone` (statement under *Statements of counterexamples, witnesses, positive controls and supporting theorems*).

**Hypothesis ledger.**

- `hx : IsLeastSolution cpLat (cpDiamond a) x` — The statement describes least solutions; the existential form cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3 shows one exists.
  - Hypothesis of: `cpDiamond_mfp_x_top_ne_mop_x_const3`.
  - Tightness: **tight** — counterexample(s) for `cpDiamond_mfp_x_top_ne_mop_x_const3`: `cpDiamond_mfp_needs_least`.
  - Witness class: cpDiamond_mfp_needs_least: for every entry state a, on cpDiamond a the assignment constantly equal to ⟨x = 3, y = ⊤, z = ⊤⟩ is not a least solution, and the conclusion fails for it.

**Non-vacuity witness.** A least solution exists for every entry state (cpDiamond_isLeastSolution), so the statement is not vacuous. Lean: `cpDiamond_isLeastSolution`, `cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3`.

**Positive control** (a nearby setting where the negative conclusion does not occur): `cpDiamond_sameBranches_exact`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `assignXYZ_monotone`, `assignYZ_distributive`, `assignYZ_not_strict`, `copyXY_distributive`.

**Prior art.**

- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, Section 2.3.3. In the authors' Chapter 2 transparencies (May 2005) the constant-propagation lattice is ((Var → Z^⊤)_⊥, ⊑): a single added bottom element ⊥ for the whole state, with per-variable values in Z ∪ {⊤} and no per-variable bottom (slides 67-68); the extremal (entry) value is λx.⊤ (slide 70); the transfer function of an assignment maps ⊥ to ⊥ (slide 71); constant propagation is shown not distributive using y := x * x (slide 72); and slide 81 states the lemma 'The MOP solution for Constant Propagation is undecidable', proved by encoding the Modified Post Correspondence Problem.
- J. H. Reif and H. R. Lewis, "Symbolic evaluation and the global value graph", POPL 1977, pp. 104-118, doi:10.1145/512950.512961. The abstract states that, with expressions interpreted over integer arithmetic, many natural global flow problems are unsolvable.
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `constant-propagation-not-exact`.

#### `gen-kill-distributive-and-exact`: Gen/kill (bit-vector) transfers are distributive; exactness for gen/kill CFGs

- **Kind:** theorem. **Tier:** T0. Classical: bit-vector (gen/kill) frameworks are distributive (Nielson-Nielson-Hankin, Chapter 2), hence MFP = MOP under the exactness side conditions.
- **Depth:** shallow. Distributivity and strictness are bitwise case analyses (definitional); the exactness statements instantiate mfp-eq-mop-exactness with the height bound k of the bit-vector lattice (proved via a popcount rank).
- **Plain claim.** On the powerset lattice of Fin k (bit vectors, inclusion, union), every gen/kill transfer f a = (a \ kill) ∪ gen distributes over union and is strict exactly when gen = ∅; consequently, for a CFG all of whose transfers are gen/kill and in which every node unreachable from the entry has an empty gen set, a least solution exists and every least solution equals MOP at every node. In the dual must orientation (reverse inclusion, intersection, full set as bottom) gen/kill transfers distribute over intersection and are strict exactly when kill ⊆ gen.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem genKill_distributive {k : Nat} (gen kill : Fin k → Bool) :
  Distributive (bvLat k) (genKill gen kill)
```

```lean
theorem genKill_strict_iff {k : Nat} (gen kill : Fin k → Bool) :
  Strict (bvLat k) (genKill gen kill) ↔ gen = fun x => false
```

```lean
theorem genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty {n k : Nat}
  (G : CFG n (Fin k → Bool)) (gen kill : Fin n → Fin k → Bool)
  (hG : ∀ (u : Fin n), G.f u = genKill (gen u) (kill u))
  (hgen : ∀ (u : Fin n), ¬Reachable G u → gen u = fun x => false) {x : Fin n → Fin k → Bool}
  (hx : IsLeastSolution (bvLat k) G x) (v : Fin n) : IsMOPAt (bvLat k) G v (x v)
```

```lean
theorem genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty {n k : Nat}
  (G : CFG n (Fin k → Bool)) (gen kill : Fin n → Fin k → Bool)
  (hG : ∀ (u : Fin n), G.f u = genKill (gen u) (kill u))
  (hgen : ∀ (u : Fin n), ¬Reachable G u → gen u = fun x => false) :
  ∃ x, IsLeastSolution (bvLat k) G x ∧ ∀ (v : Fin n), IsMOPAt (bvLat k) G v (x v)
```

```lean
theorem genKill_distributive_must {k : Nat} (gen kill : Fin k → Bool) :
  Distributive (bvMustLat k) (genKill gen kill)
```

```lean
theorem genKill_strict_must_iff {k : Nat} (gen kill : Fin k → Bool) :
  Strict (bvMustLat k) (genKill gen kill) ↔ ∀ (i : Fin k), kill i = true → gen i = true
```

**Hypothesis ledger.**

- `hG : ∀ u, G.f u = genKill (gen u) (kill u)` — Supplies distributivity of every transfer.
  - Hypothesis of: `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`, `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty`.
  - Tightness: **tight** — counterexample(s) for `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`: `genKill_exactness_needs_genKill_form`; for `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty`: `genKill_exactness_needs_genKill_form`, `exists_exactness_counterexamples`, `genKill_exists_exactness_combined_counterexamples`.
  - Witness class: genKill_exactness_needs_genKill_form: the 5-node diamond bbDiamond over bvLat 2 (all nodes reachable, so hgen holds for every gen; monotone transfers; the join-node transfer bothBits is not a gen/kill transfer; the least solution bbSol is not MOP at node 4); genKill_exists_exactness_combined_counterexamples, first conjunct (existence form): bbDiamond over bvLat 2 for every choice of gen and kill. exists_exactness_counterexamples supplies only the failing existential conclusion and is used together with genKill_exactness_needs_genKill_form.
- `hgen : ∀ u, ¬ Reachable G u → gen u = fun _ => false` — Strictness at unreachable nodes (gen = ∅ iff strict, in the may orientation).
  - Hypothesis of: `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`, `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty`.
  - Tightness: **tight** — counterexample(s) for `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`: `genKill_exactness_needs_unreachable_gen_empty`; for `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty`: `genKill_exactness_needs_unreachable_gen_empty`, `exists_exactness_counterexamples`, `genKill_exists_exactness_combined_counterexamples`.
  - Witness class: genKill_exactness_needs_unreachable_gen_empty: ugCFG over bvLat 1 with gen/kill sets ugGen/ugKill (hG holds; the unreachable node 1 has gen set {0}; the least solution ugSol is not MOP at node 2); genKill_exists_exactness_combined_counterexamples, second conjunct (existence form): ugCFG over bvLat 1. exists_exactness_counterexamples supplies only the failing existential conclusion and is used together with genKill_exactness_needs_unreachable_gen_empty.
- `hx : IsLeastSolution (bvLat k) G x` — The claim is about least solutions.
  - Hypothesis of: `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`.
  - Tightness: **tight** — counterexample(s) for `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`: `strict_and_genKill_exactness_needs_least`.
  - Witness class: strict_and_genKill_exactness_needs_least: the 1-node gen/kill self-loop with gen = kill = ∅ over bvLat 1 (hG and hgen hold) with the solution x = full set, which is not least and not MOP at node 0.

**Non-vacuity witness.** The gen/kill loop 0 → 1, 1 → 1 on 2-bit vectors (all nodes reachable) with its least solution. For the must orientation, gen = kill = {0} on 2-bit vectors gives a distributive, strict transfer with a non-empty kill set (genKill_must_strict_nonempty_kill_nonvacuous). Lean: `genKill_exactness_nonvacuous`, `genKill_must_strict_nonempty_kill_nonvacuous`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `copyBit0_distributive`, `copyBit0_not_genKill`, `genKill_killOnly_strict_may_not_must`.

**Prior art.**

- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162). Works over a finite meet-semilattice with transfer functions having the 'homomorphism property' f(N, x ^ y) = f(N, x) ^ f(N, y) (distributivity, in the dual orientation); Algorithm A is a worklist algorithm; Theorem 1 states that it terminates; Theorem 2 relates the final pool at each node N to the values propagated along all paths from entry nodes to N. Exact bounds and formulas of the paper are not quoted here.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `gen-kill-distributive-and-exact`.

#### `kildall-computes-mfp`: The worklist solver: solutions, least solutions under monotonicity, termination with fuel n * (h + 1) + 1 on height-h lattices

- **Kind:** theorem. **Tier:** T0. Kildall's Theorem 1 (termination) and the least-fixed-point property of the worklist result are classical, and least-ness of a Kildall-style iteration is mechanized in Isabelle (JinjaThreads, kildall_properties) and Coq (rocq-archive/kildall, monotone_step_imp_kildall_dfa). Restated with an explicit fuel bound n * (h + 1) + 1 and with the solution property separated from monotonicity.
- **Depth:** substantive. Partial correctness needs a three-part worklist invariant preserved by edge propagation (two parts suffice for the solution property); termination needs a rank function built from the height bound (longest strict chain ending at each element) and a potential argument (worklist length plus remaining rank headroom).
- **Plain claim.** For a join-semilattice with bottom L (L.IsJSL) with a decidable order test, the fuel-bounded worklist solver kildall L G fuel (start with init at the entry and ⊥ elsewhere, all nodes on the worklist; popping u joins f u (x u) into each successor whose value it does not already lie below and pushes that successor; one unit of fuel per pop) satisfies: whenever it returns some x, x is a solution of the inequations (for any transfer functions) and, if the transfers are monotone, the least solution; on a lattice of height at most h it returns some value whenever fuel ≥ n * (h + 1) + 1, with or without monotonicity; together, with monotone transfers and that fuel, it returns some x and x is the least solution (MFP). The fuel bound is attained for every n ≥ 1 and h ≥ 0 (kildall_fuel_bound_attained: on a CFG of n nodes, each with a self-loop, with monotone transfers over a chain of height h, fuel n * (h + 1) returns none).

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem kildall_isLeastSolution_of_monotone_of_eq_some {n : Nat} {α : Type} {L : Lat α}
  [DecidableRel L.le] (hL : L.IsJSL) (G : CFG n α) (hmono : ∀ (u : Fin n), Monotone L (G.f u))
  {fuel : Nat} {x : Fin n → α} (h : kildall L G fuel = some x) : IsLeastSolution L G x
```

```lean
theorem kildall_isSolution_of_eq_some {n : Nat} {α : Type} {L : Lat α} [DecidableRel L.le]
  (hL : L.IsJSL) (G : CFG n α) {fuel : Nat} {x : Fin n → α} (h : kildall L G fuel = some x) :
  IsSolution L G x
```

```lean
theorem kildall_isSome_of_heightLe {n : Nat} {α : Type} {L : Lat α} [DecidableRel L.le]
  (hL : L.IsJSL) (G : CFG n α) {h : Nat} (hh : L.HeightLe h) {fuel : Nat}
  (hfuel : n * (h + 1) + 1 ≤ fuel) : (kildall L G fuel).isSome = true
```

```lean
theorem kildall_eq_some_isLeastSolution_of_monotone_of_heightLe {n : Nat} {α : Type}
  {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL) (G : CFG n α)
  (hmono : ∀ (u : Fin n), Monotone L (G.f u)) {h : Nat} (hh : L.HeightLe h) {fuel : Nat}
  (hfuel : n * (h + 1) + 1 ≤ fuel) : ∃ x, kildall L G fuel = some x ∧ IsLeastSolution L G x
```

The last sentence of the plain claim (the fuel bound is attained) is proved by `kildall_fuel_bound_attained`, the counterexample recorded for `hfuel` in the hypothesis ledger below (statement under *Statements of counterexamples, witnesses, positive controls and supporting theorems*).

**Hypothesis ledger.**

- `[DecidableRel L.le]` — Data needed to run the solver (the order test in propagate), not a property of L: every relation has a classical instance (Classical.decRel), so it excludes no lattice.
  - Hypothesis of: `kildall_isLeastSolution_of_monotone_of_eq_some`, `kildall_isSolution_of_eq_some`, `kildall_isSome_of_heightLe`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`.
  - Tightness: **harmless** — computational data only: a classical instance exists for every relation (`Classical.decRel`), and the solver's result does not depend on which instance is supplied (`kildall_decidableRel_irrelevant`).
- `hL : L.IsJSL` — Joins are upper bounds (invariant x ≤ every solution, strict increase on update). The intended setting; not weakened further here.
  - Hypothesis of: `kildall_isLeastSolution_of_monotone_of_eq_some`, `kildall_isSolution_of_eq_some`, `kildall_isSome_of_heightLe`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`.
  - Tightness: **harmless** — the intended setting (all join-semilattice-with-bottom laws); no weakening is studied and no counterexample is claimed.
- `hmono : ∀ u, Monotone L (G.f u)` — Keeps the iterate below every solution.
  - Hypothesis of: `kildall_isLeastSolution_of_monotone_of_eq_some`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_isLeastSolution_of_monotone_of_eq_some`: `kildall_needs_monotone`; for `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`: `kildall_needs_monotone`.
  - Witness class: kildall_needs_monotone: the 2-node CFG notCFG over boolLat (height 1) with fuel 10 ≥ 2 * (1 + 1) + 1; the solver returns x with (x 0, x 1) = (true, true), a solution that is not least, and no output of the solver at that fuel is a least solution.
- `h : kildall L G fuel = some x` — The statement is about the solver's output.
  - Hypothesis of: `kildall_isLeastSolution_of_monotone_of_eq_some`, `kildall_isSolution_of_eq_some`.
  - Tightness: **tight** — counterexample(s) for `kildall_isLeastSolution_of_monotone_of_eq_some`: `kildall_needs_eq_some`; for `kildall_isSolution_of_eq_some`: `kildall_needs_eq_some`.
  - Witness class: kildall_needs_eq_some: loopGK over bvLat 2 (monotone transfers) at fuel 7; the full-set assignment is not the solver's output and is not least; the empty assignment is not the solver's output and is not a solution.
- `hh : L.HeightLe h` — Bounds the number of strict increases per node by h.
  - Hypothesis of: `kildall_isSome_of_heightLe`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_isSome_of_heightLe`: `kildall_needs_heightLe`; for `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`: `kildall_needs_heightLe`.
  - Witness class: kildall_needs_heightLe: the 1-node successor self-loop succCFG over natMaxLat (monotone and distributive transfer, all nodes reachable, no ascending chain condition, no height bound); the solver returns none for every fuel.
- `hfuel : n * (h + 1) + 1 ≤ fuel` — At most n initial pops plus n * h pushes, plus one final step.
  - Hypothesis of: `kildall_isSome_of_heightLe`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_isSome_of_heightLe`: `kildall_fuel_bound_attained`; for `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`: `kildall_fuel_bound_attained`.
  - Witness class: kildall_fuel_bound_attained: for every m and h, the CFG selfLoopsCFG m h of n = m + 1 nodes, each with a self-loop, over the chain finChainLat h of height h, with monotone transfers; fuel n * (h + 1) returns none and fuel n * (h + 1) + 1 returns some value.

**Non-vacuity witness.** The gen/kill loop on 2-bit vectors with fuel 7 = 2 * (2 + 1) + 1; the solver returns ∅ at node 0 and {0,1} at node 1 (checked by evaluation). Lean: `kildall_nonvacuous`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `acc_strictly_weaker_than_heightLe`, `exactness_holds_on_unboundedChainsLat`, `exactness_needs_unreachableStrict`, `exists_isLeastSolution_of_monotone_of_acc`, `isEquationSolution_of_isLeastSolution_of_monotone`, `kildall_acc_has_no_uniform_fuel`, `kildall_decidableRel_irrelevant`, `notCFG_isLeastSolution_not_isEquationSolution`.

**Prior art.**

- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162). Works over a finite meet-semilattice with transfer functions having the 'homomorphism property' f(N, x ^ y) = f(N, x) ^ f(N, y) (distributivity, in the dual orientation); Algorithm A is a worklist algorithm; Theorem 1 states that it terminates; Theorem 2 relates the final pool at each node N to the values propagated along all paths from entry nodes to N. Exact bounds and formulas of the paper are not quoted here.
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.
- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- A. Lochbihler, "Jinja with Threads", Archive of Formal Proofs, December 2007, https://www.isa-afp.org/entries/JinjaThreads.html. Theory JinjaThreads/DFA/Kildall.thy (authors T. Nipkow, G. Klein, A. Lochbihler) proves lemma kildall_properties: assuming a semilattice, the ascending chain condition (acc), type preservation, monotone and bounded step functions, the result of kildall is stable, above the start state, and below every stable state above the start state (the least stable state above the start); lemma iter_properties is the corresponding worklist-iteration statement. There is no notion of paths or MOP.
- G. Klein and T. Nipkow, "Verified bytecode verifiers", Theoretical Computer Science 298(3):583-626, 2003. Isabelle/HOL verification of a Kildall-style dataflow bytecode verifier.
- S. Coupet-Grimal and W. Delobel, "A Uniform and Certified Approach for Two Static Analyses", Types for Proofs and Programs (TYPES 2004), LNCS 3839, pp. 115-137, Springer, 2006; Coq development https://github.com/rocq-archive/kildall (commit 87422e1815e22a3f4821b29a1fd7a7f385667b91). File kildall/kildall_dfa.v proves monotone_step_imp_kildall_dfa: for a monotone step function, Kildall's algorithm is a data flow analyser in the sense of kildall/dfa.v (Is_data_flow_analyser: the result is stable, above the start vector, and below every stable vector above the start vector), over a well-founded semilattice. There is no notion of paths or MOP.
- D. Cachera, T. Jensen, D. Pichardie, V. Rusu, "Extracting a data flow analyser in constructive logic", Theoretical Computer Science 342(1):56-78, 2005 (preliminary version at ESOP 2004). A Coq lattice library and a least-fixpoint data flow analyser extracted from a constructive proof.
- CompCert, file backend/Kildall.v, repository AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (last change to the file: 4710ec093ddea8e6eb86ad519df61c59b654e861). Module Dataflow_Solver: fixpoint seeds the worklist with the entry point only and proves fixpoint_solution (every edge inequation holds) under the hypothesis 'forall n, L.eq (transf n L.bot) L.bot'; fixpoint_allnodes starts with every node at L.bot and every node on the worklist and proves fixpoint_allnodes_solution without that hypothesis; fixpoint_nodeset_solution proves that a solver seeded with a given set of nodes satisfies the inequations at every program point reachable from those nodes; fixpoint_entry and fixpoint_invariant are also proved. No least-solution or MOP statement is proved, monotonicity of transfer functions is never assumed, and iteration is bounded by fuel (PrimIter), returning None when fuel is exhausted.
- Y. Bertot, B. Grégoire, X. Leroy, "A structured approach to proving compiler optimizations based on dataflow analysis", Types for Proofs and Programs (TYPES 2004), LNCS 3839, pp. 66-81, Springer, 2006, doi:10.1007/11617990_5. Coq proofs of dataflow-based optimizations in the line of work leading to CompCert's dataflow solver.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `kildall-computes-mfp`.

#### `kildall-computes-mop`: End to end: the worklist solver computes MOP for distributive frameworks

- **Kind:** theorem. **Tier:** T1. The composition 'Kildall's algorithm computes MOP for distributive frameworks' is classical (Kildall, Theorem 2; Kam-Ullman), but no mechanized solver-computes-MOP statement was found. The statement makes the side conditions explicit (finite height, strictness at unreachable nodes).
- **Depth:** shallow. Composition of kildall_eq_some_isLeastSolution_of_monotone_of_heightLe and isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict via monotone_of_distributive and Lat.acc_of_heightLe.
- **Plain claim.** For distributive transfer functions on a join-semilattice with bottom of height at most h with a decidable order test, if every node unreachable from the entry has a strict transfer function, then with fuel ≥ n * (h + 1) + 1 the worklist solver kildall returns some x, x is the least solution of the inequations, and x v is the MOP value (the least upper bound of all path values) at every node v.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe {n : Nat}
  {α : Type} {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL) (G : CFG n α)
  (hdist : ∀ (u : Fin n), Distributive L (G.f u)) (hstrict : UnreachableStrict L G) {h : Nat}
  (hh : L.HeightLe h) {fuel : Nat} (hfuel : n * (h + 1) + 1 ≤ fuel) :
  ∃ x, kildall L G fuel = some x ∧ IsLeastSolution L G x ∧ ∀ (v : Fin n), IsMOPAt L G v (x v)
```

**Hypothesis ledger.**

- `[DecidableRel L.le]` — Data needed to run the solver, not a property of L (every relation has a classical instance).
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **harmless** — computational data only: a classical instance exists for every relation (`Classical.decRel`), and the solver's result does not depend on which instance is supplied (`kildall_decidableRel_irrelevant`).
- `hL : L.IsJSL` — Lattice laws. The intended setting; not weakened further here.
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **harmless** — the intended setting (all join-semilattice-with-bottom laws); no weakening is studied and no counterexample is claimed.
- `hdist : ∀ u, Distributive L (G.f u)` — Exactness of the least solution; implies (monotone_of_distributive) the monotonicity used for least-ness.
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`: `kildall_isMOPAt_counterexamples`.
  - Witness class: kildall_isMOPAt_counterexamples, first conjunct: cpDiamond ⟨⊤, ⊤, ⊤⟩ over cpLat (height 6, fuel 36 ≥ 5 * (6 + 1) + 1, all nodes reachable); the transfers are not all distributive, and no output of the solver at fuel 36 is a least solution equal to MOP at every node.
- `hstrict : UnreachableStrict L G` — Exactness at nodes fed by unreachable nodes.
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`: `kildall_isMOPAt_counterexamples`.
  - Witness class: kildall_isMOPAt_counterexamples, second conjunct: ugCFG over bvLat 1 (height 1, fuel 7 ≥ 3 * (1 + 1) + 1, distributive transfers); UnreachableStrict fails, and the conclusion fails.
- `hh : L.HeightLe h` — Termination (and, via Lat.acc_of_heightLe, the ascending chain condition for exactness).
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`: `kildall_isMOPAt_counterexamples`.
  - Witness class: kildall_isMOPAt_counterexamples, third conjunct: succCFG over natMaxLat (distributive transfer, all nodes reachable, no height bound); the conclusion fails for every fuel.
- `hfuel : n * (h + 1) + 1 ≤ fuel` — Enough fuel to terminate.
  - Hypothesis of: `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
  - Tightness: **tight** — counterexample(s) for `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`: `kildall_isMOPAt_counterexamples`.
  - Witness class: kildall_isMOPAt_counterexamples, fourth conjunct: for every h, selfLoopsCFG 0 h (one node with a self-loop) over finChainLat h (height h, distributive transfer, all nodes reachable); at fuel 1 * (h + 1), which is below 1 * (h + 1) + 1, the conclusion fails.

**Non-vacuity witness.** The gen/kill loop on 2-bit vectors with fuel 7: the solver's result is the least solution and the MOP value at both nodes. Lean: `kildall_isMOPAt_nonvacuous`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `Lat.acc_of_heightLe`, `exactness_needs_unreachableStrict`, `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `kildall_acc_has_no_uniform_fuel`, `kildall_decidableRel_irrelevant`, `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe`, `kildall_isSolution_of_eq_some`, `monotone_of_distributive`.

**Prior art.**

- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162). Works over a finite meet-semilattice with transfer functions having the 'homomorphism property' f(N, x ^ y) = f(N, x) ^ f(N, y) (distributivity, in the dual orientation); Algorithm A is a worklist algorithm; Theorem 1 states that it terminates; Theorem 2 relates the final pool at each node N to the values propagated along all paths from entry nodes to N. Exact bounds and formulas of the paper are not quoted here.
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305-317, 1977, doi:10.1007/BF00290339. The abstract states that the maximal fixed point solution exists for every instance of every monotone framework and is obtained by Kildall's algorithm; that whenever a framework is monotone but not distributive there are instances in which the meet-over-all-paths solution differs from the maximal fixed point; and that no algorithm computes the meet-over-all-paths solution for monotone frameworks in general. These statements concern monotone frameworks in general (meet-semilattice orientation); this card cites only the abstract, and attributes to the paper no statement about any particular framework such as constant propagation.
- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- A search of the Archive of Formal Proofs (static-analysis and Kildall entries), Coq/Rocq developments (rocq-archive/kildall, CompCert), Lean mathlib (Order.FixedPoints) and Agda sources, and web searches pairing 'meet over all paths'/MOP/MFP with Coq, Isabelle, Agda and Lean, found mechanized least-fixpoint (MFP) solvers but no mechanized MFP = MOP statement; this is not proof of absence.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `kildall-computes-mop`.

#### `reachable-node-not-exact-unreachable-gen`: Counterexample: MFP ≠ MOP at a reachable node fed by a non-strict unreachable node

- **Kind:** counterexample. **Tier:** T1. Prior statements exclude the situation by assuming that every node has a path from the entry (Nielson-Nielson-Hankin) or that all transfers are strict (CompCert's fixpoint_solution); the explicit three-node acyclic counterexample, in which the affected node is itself reachable, is what is made precise and checked here.
- **Depth:** shallow. Finite computation of the least solution and of the path values.
- **Plain claim.** With gen/kill (distributive) transfers on 1-bit vectors, there is a three-node CFG (entry 0 → 2, and an unreachable node 1 with no incoming edge, gen = {0}, and an edge 1 → 2) in which node 2 is reachable from the entry, yet the least solution at node 2 is {0} while MOP there is ∅ (ugCFG_isMOPAt_two_empty).

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem exactness_needs_unreachableStrict :
  (bvLat 1).IsJSL ∧
    (bvLat 1).AscendingChainCondition ∧
      (∀ (u : Fin 3), Distributive (bvLat 1) (ugCFG.f u)) ∧
        (∀ (u : Fin 3), ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
          ¬Reachable ugCFG 1 ∧
            ¬UnreachableStrict (bvLat 1) ugCFG ∧
              IsLeastSolution (bvLat 1) ugCFG ugSol ∧
                Reachable ugCFG 2 ∧ ¬IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2)
```

The clause "MOP there is ∅" of the plain claim is proved by the supporting theorem `ugCFG_isMOPAt_two_empty` (statement under *Statements of counterexamples, witnesses, positive controls and supporting theorems*); `exactness_needs_unreachableStrict` above proves that the least solution's value `ugSol 2 = {0}` at node `2` is not MOP there.

**Hypothesis ledger.**

- The result is a closed statement about one concrete instance; it has no hypotheses. Non-vacuity: the instance itself, every listed property of which is proved.

**Non-vacuity witness.** The instance itself (all listed properties are proved). Lean: `exactness_needs_unreachableStrict`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, `kildall_isSolution_of_eq_some`, `ugCFG_isMOPAt_two_empty`.

**Prior art.**

- F. Nielson, H. R. Nielson, C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0. Chapter 2: Section 2.3 'Monotone Frameworks' (2.3.3 'A Non-distributive Example'), Section 2.4 'Equation Solving' (2.4.1 'The MFP Solution', 2.4.2 'The MOP Solution'); worklist algorithms in Section 6.1. The authors' Chapter 2 transparencies (May 2005), slide 79, state a lemma for the MFP and MOP solutions of an instance of a monotone framework: 'MFP◦ ⊒ MOP◦ and MFP• ⊒ MOP•', and 'If the framework is distributive and if path◦(ℓ) ≠ ∅ for all ℓ in E and F then: MFP◦ = MOP◦ and MFP• = MOP•' (join orientation; MFP◦/MFP• and MOP◦/MOP• are the pre- and post-transfer solutions).
- CompCert, file backend/Kildall.v, repository AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (last change to the file: 4710ec093ddea8e6eb86ad519df61c59b654e861). Module Dataflow_Solver: fixpoint seeds the worklist with the entry point only and proves fixpoint_solution (every edge inequation holds) under the hypothesis 'forall n, L.eq (transf n L.bot) L.bot'; fixpoint_allnodes starts with every node at L.bot and every node on the worklist and proves fixpoint_allnodes_solution without that hypothesis; fixpoint_nodeset_solution proves that a solver seeded with a given set of nodes satisfies the inequations at every program point reachable from those nodes; fixpoint_entry and fixpoint_invariant are also proved. No least-solution or MOP statement is proved, monotonicity of transfer functions is never assumed, and iteration is bounded by fuel (PrimIter), returning None when fuel is exhausted.
- Y. Bertot, B. Grégoire, X. Leroy, "A structured approach to proving compiler optimizations based on dataflow analysis", Types for Proofs and Programs (TYPES 2004), LNCS 3839, pp. 66-81, Springer, 2006, doi:10.1007/11617990_5. Coq proofs of dataflow-based optimizations in the line of work leading to CompCert's dataflow solver.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `reachable-node-not-exact-unreachable-gen`.

#### `exactness-needs-acc`: Counterexample: MFP ≠ MOP on a chain without the ascending chain condition

- **Kind:** counterexample. **Tier:** T0. An instance of the classical fact that the join of the iterates f^k(⊥) is the least fixed point for continuous maps but not, in general, for maps that are merely monotone (Davey-Priestley, Chapter 8; transfinite iteration in Cousot-Cousot 1979): on the loop, MOP is the join of the iterates and MFP is the least fixed point.
- **Depth:** shallow. Path values are exactly the finite elements; the least solution is forced by the loop inequation.
- **Plain claim.** On the chain 0 < 1 < 2 < ⋯ < ω < ω+1, which violates the ascending chain condition and on which every monotone map is distributive (omegaLat_monotone_distributive), the CFG 0 → 1 with a loop 1 → 1 whose transfer is the successor map (k ↦ k+1, ω ↦ ω+1) has all nodes reachable, distributive transfers, and least solution ω+1 at node 1, while MOP there (the least upper bound of the path values 0, 1, 2, …) is ω.

**Lean statements.** Basis: execution (Lean kernel check).

```lean
theorem exactness_needs_acc :
  omegaLat.IsJSL ∧
    ¬omegaLat.AscendingChainCondition ∧
      (∀ (u : Fin 2), Distributive omegaLat (omegaCFG.f u)) ∧
        AllReachable omegaCFG ∧
          UnreachableStrict omegaLat omegaCFG ∧
            IsLeastSolution omegaLat omegaCFG omegaSol ∧
              IsMOPAt omegaLat omegaCFG 1 OmegaTwo.omega ∧ ¬IsMOPAt omegaLat omegaCFG 1 (omegaSol 1)
```

The clause "every monotone map on it is distributive" of the plain claim is proved by the supporting theorem `omegaLat_monotone_distributive` (statement under *Statements of counterexamples, witnesses, positive controls and supporting theorems*).

**Hypothesis ledger.**

- The result is a closed statement about one concrete instance; it has no hypotheses. Non-vacuity: the instance itself, every listed property of which is proved.

**Non-vacuity witness.** The instance itself. Lean: `exactness_needs_acc`.

**Positive control** (a nearby setting where the negative conclusion does not occur): `cyclic_exactness_on_unboundedChainsLat`, `exactness_holds_on_unboundedChainsLat`.

**Supporting theorems cited in this card** (statements below; hashes under Evidence): `acc_strictly_weaker_than_heightLe`, `distributive_of_monotone_of_total`, `kildall_acc_has_no_uniform_fuel`, `kildall_isSome_of_heightLe`, `kildall_needs_heightLe`, `omegaLat_monotone_distributive`, `omegaLat_total`.

**Prior art.**

- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002, Chapter 8 'CPOs and fixpoint theorems' (Section 8.3 'Fixpoint theorems'): the least fixed point is the join of the iterates f^k(⊥) for continuous maps; monotonicity alone does not guarantee this.
- P. Cousot and R. Cousot, "Constructive versions of Tarski's fixed point theorems", Pacific Journal of Mathematics 82(1):43-57, 1979. Least fixed points of monotone (not necessarily continuous) maps are reached by transfinite iteration sequences, which can extend beyond ω.

**Design question.** When does the fixed point a worklist dataflow solver computes (MFP) equal the join-over-all-paths specification (MOP), when is it only a sound over-approximation, which property of the transfer functions decides it, and which side conditions (finite height, strictness at unreachable nodes, monotonicity, worklist seeding) do textbook statements assume?

**Non-claims:** see Boundaries, `exactness-needs-acc`.

### Statements of counterexamples, witnesses, positive controls and supporting theorems

Every Lean name referenced by a card other than its main statements, in alphabetical order. Each is a fully proved theorem (Basis: execution (Lean kernel check)). Counterexamples are stated in the form "the other hypotheses hold and the conclusion fails" (in some theorems the failing conclusion is supplied by a companion theorem; the witness class of each ledger entry says which).

`Lat.acc_of_heightLe` — cited in `kildall-computes-mop`.

```lean
theorem Lat.acc_of_heightLe {α : Type} {L : Lat α} {h : Nat} (hh : L.HeightLe h) :
  L.AscendingChainCondition
```

`acc_strictly_weaker_than_heightLe` — cited in `mfp-eq-mop-exactness`; cited in `kildall-computes-mfp`; cited in `exactness-needs-acc`.

```lean
theorem acc_strictly_weaker_than_heightLe :
  unboundedChainsLat.IsJSL ∧
    unboundedChainsLat.AscendingChainCondition ∧ ∀ (h : Nat), ¬unboundedChainsLat.HeightLe h
```

`assignXYZ_monotone` — cited in `constant-propagation-not-exact`.

```lean
theorem assignXYZ_monotone : Monotone cpLat assignXYZ
```

`assignYZ_distributive` — cited in `constant-propagation-not-exact`.

```lean
theorem assignYZ_distributive (c d : Int) : Distributive cpLat (assignYZ c d)
```

`assignYZ_not_strict` — cited in `constant-propagation-not-exact`.

```lean
theorem assignYZ_not_strict (c d : Int) : ¬Strict cpLat (assignYZ c d)
```

`cfg_empty_carrier_empty` — cited in `mfp-eq-mop-exactness`.

```lean
theorem cfg_empty_carrier_empty {n : Nat} (G : CFG n Empty) : False
```

`cfg_zero_empty` — cited in `mfp-eq-mop-exactness`.

```lean
theorem cfg_zero_empty {α : Type} (G : CFG 0 α) : False
```

`copyBit0_distributive` — cited in `gen-kill-distributive-and-exact`.

```lean
theorem copyBit0_distributive : Distributive (bvLat 2) copyBit0
```

`copyBit0_not_genKill` — cited in `gen-kill-distributive-and-exact`.

```lean
theorem copyBit0_not_genKill :
  ¬∃ gen kill, ∀ (a : Fin 2 → Bool), copyBit0 a = genKill gen kill a
```

`copyXY_distributive` — cited in `constant-propagation-not-exact`.

```lean
theorem copyXY_distributive : Distributive cpLat copyXY
```

`cpDiamond_isLeastSolution` — non-vacuity witness of `constant-propagation-not-exact`.

```lean
theorem cpDiamond_isLeastSolution (a : St) :
  IsLeastSolution cpLat (cpDiamond a) (diamondSol cpLat a (assignYZ 1 2) (assignYZ 2 1) assignXYZ)
```

`cpDiamond_mfp_needs_least` — counterexample for `hx` in `constant-propagation-not-exact`.

```lean
theorem cpDiamond_mfp_needs_least (a : St) :
  (¬IsLeastSolution cpLat (cpDiamond a) fun x =>
        { x := Flat.const 3, y := Flat.top, z := Flat.top }) ∧
    ¬((fun x => { x := Flat.const 3, y := Flat.top, z := Flat.top }) 4 =
          { x := Flat.top, y := Flat.top, z := Flat.top } ∧
        IsMOPAt cpLat (cpDiamond a) 4 { x := Flat.const 3, y := Flat.top, z := Flat.top } ∧
          ¬IsMOPAt cpLat (cpDiamond a) 4
              ((fun x => { x := Flat.const 3, y := Flat.top, z := Flat.top }) 4))
```

`cpDiamond_sameBranches_exact` — positive control of `constant-propagation-not-exact`.

```lean
theorem cpDiamond_sameBranches_exact (a : St) {x : Fin 5 → St}
  (hx : IsLeastSolution cpLat (diamond a (assignYZ 1 2) (assignYZ 1 2) assignXYZ) x) :
  (∀ (v : Fin 5), IsMOPAt cpLat (diamond a (assignYZ 1 2) (assignYZ 1 2) assignXYZ) v (x v)) ∧
    (x 4).x = Flat.const 3
```

`cyclic_exactness_on_unboundedChainsLat` — non-vacuity witness of `mfp-eq-mop-exactness`; positive control of `exactness-needs-acc`.

```lean
theorem cyclic_exactness_on_unboundedChainsLat (m : Nat) :
  unboundedChainsLat.IsJSL ∧
    unboundedChainsLat.AscendingChainCondition ∧
      (∀ (h : Nat), ¬unboundedChainsLat.HeightLe h) ∧
        (∀ (u : Fin 1), Distributive unboundedChainsLat ((stepMidCFG m).f u)) ∧
          UnreachableStrict unboundedChainsLat (stepMidCFG m) ∧
            ∃ x,
              IsLeastSolution unboundedChainsLat (stepMidCFG m) x ∧
                ∀ (v : Fin 1), IsMOPAt unboundedChainsLat (stepMidCFG m) v (x v)
```

`diamondExact_const_mem_needs_monotone` — counterexample for `hmono` in `diamond-exactness-characterization`; counterexample for `hacc` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_const_mem_needs_monotone :
  withBotIntLat.IsJSL ∧
    ¬withBotIntLat.AscendingChainCondition ∧
      (¬∀ (φ : WithBotInt → WithBotInt), wbNegFamily φ → Monotone withBotIntLat φ) ∧
        (∀ (b : WithBotInt), wbNegFamily fun x => b) ∧
          (∃ a, (fun x => True) a) ∧
            DiamondExact withBotIntLat (fun x => True) wbNegFamily ∧
              ¬∀ (f : WithBotInt → WithBotInt), wbNegFamily f → Distributive withBotIntLat f
```

`diamondExact_const_mem_nonvacuous` — non-vacuity witness of `diamond-exactness-characterization`; counterexample for `he` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_const_mem_nonvacuous :
  ((bvLat 1).IsJSL ∧
      (bvLat 1).AscendingChainCondition ∧
        (∀ (φ : (Fin 1 → Bool) → Fin 1 → Bool),
            (∃ gen kill, φ = genKill gen kill) → Monotone (bvLat 1) φ) ∧
          (∀ (b : Fin 1 → Bool), ∃ gen kill, (fun x => b) = genKill gen kill) ∧
            (∃ a, (fun x => True) a) ∧
              (DiamondExact (bvLat 1) (fun x => True) fun φ => ∃ gen kill, φ = genKill gen kill) ∧
                (DistributiveOnRealizable (bvLat 1) (fun x => True) fun φ =>
                    ∃ gen kill, φ = genKill gen kill) ∧
                  ∀ (f : (Fin 1 → Bool) → Fin 1 → Bool),
                    (∃ gen kill, f = genKill gen kill) → Distributive (bvLat 1) f) ∧
    cpLat.IsJSL ∧
      cpLat.AscendingChainCondition ∧
        (∀ (φ : St → St), (∃ b, φ = fun x => b) ∨ cpFamily φ → Monotone cpLat φ) ∧
          (∀ (b : St), (∃ b', (fun x => b) = fun x => b') ∨ cpFamily fun x => b) ∧
            (∃ a, (fun x => True) a) ∧
              (¬DiamondExact cpLat (fun x => True) fun φ => (∃ b, φ = fun x => b) ∨ cpFamily φ) ∧
                (¬DistributiveOnRealizable cpLat (fun x => True) fun φ =>
                      (∃ b, φ = fun x => b) ∨ cpFamily φ) ∧
                  ¬∀ (f : St → St), (∃ b, f = fun x => b) ∨ cpFamily f → Distributive cpLat f
```

`diamondExact_const_needs_nonempty_init` — counterexample for `hI` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_const_needs_nonempty_init :
  cpLat.IsJSL ∧
    cpLat.AscendingChainCondition ∧
      (¬∃ a, (fun x => False) a) ∧
        (∀ (φ : St → St), (∃ b, φ = fun x => b) ∨ φ = assignXYZ → Monotone cpLat φ) ∧
          (∀ (b : St), (∃ b', (fun x => b) = fun x => b') ∨ (fun x => b) = assignXYZ) ∧
            (DiamondExact cpLat (fun x => False) fun φ => (∃ b, φ = fun x => b) ∨ φ = assignXYZ) ∧
              ¬∀ (f : St → St), (∃ b, f = fun x => b) ∨ f = assignXYZ → Distributive cpLat f
```

`diamondExact_iff_nonvacuous` — non-vacuity witness of `diamond-exactness-characterization`; counterexample for `hd` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_iff_nonvacuous :
  ((bvLat 1).IsJSL ∧
      (∀ (φ : (Fin 1 → Bool) → Fin 1 → Bool),
          (∃ gen kill, φ = genKill gen kill) → Monotone (bvLat 1) φ) ∧
        DiamondExact (bvLat 1) (fun x => True) fun φ => ∃ gen kill, φ = genKill gen kill) ∧
    cpLat.IsJSL ∧
      (∀ (φ : St → St), cpFamily φ → Monotone cpLat φ) ∧
        ¬DiamondExact cpLat (fun x => True) cpFamily
```

`diamondExact_needs_distributiveOnRealizable` — counterexample for `hd` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_needs_distributiveOnRealizable :
  cpLat.IsJSL ∧
    ¬DistributiveOnRealizable cpLat (fun x => True) cpFamily ∧
      ¬DiamondExact cpLat (fun x => True) cpFamily
```

`diamondExact_needs_monotone` — counterexample for `hmono` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_needs_monotone :
  boolLat.IsJSL ∧
    (¬∀ (φ : Bool → Bool), idNotFamily φ → Monotone boolLat φ) ∧
      DiamondExact boolLat (fun x => x = false) idNotFamily ∧
        ¬DistributiveOnRealizable boolLat (fun x => x = false) idNotFamily
```

`diamondExact_not_exact_on_two_step_branches` — cited in `diamond-exactness-characterization`.

```lean
theorem diamondExact_not_exact_on_two_step_branches :
  cpLat.IsJSL ∧
    cpLat.AscendingChainCondition ∧
      (∀ (φ : St → St), twoStepFamily φ → Monotone cpLat φ) ∧
        DiamondExact cpLat (fun x => x = { x := Flat.top, y := Flat.top, z := Flat.top })
            twoStepFamily ∧
          (∀ (v : Fin 7),
              v ≠ 0 →
                v ≠ 6 →
                  twoStepFamily
                    ((diamond2 { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2)
                          (setY 2) (setZ 1) assignXYZ).f
                      v)) ∧
            IsLeastSolution cpLat
                (diamond2 { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2) (setY 2)
                  (setZ 1) assignXYZ)
                (diamond2Sol cpLat { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2)
                  (setY 2) (setZ 1) assignXYZ) ∧
              diamond2Sol cpLat { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2)
                    (setY 2) (setZ 1) assignXYZ 6 =
                  { x := Flat.top, y := Flat.top, z := Flat.top } ∧
                IsMOPAt cpLat
                    (diamond2 { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2)
                      (setY 2) (setZ 1) assignXYZ)
                    6 { x := Flat.const 3, y := Flat.top, z := Flat.top } ∧
                  ¬IsMOPAt cpLat
                      (diamond2 { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1) (setZ 2)
                        (setY 2) (setZ 1) assignXYZ)
                      6
                      (diamond2Sol cpLat { x := Flat.top, y := Flat.top, z := Flat.top } (setY 1)
                        (setZ 2) (setY 2) (setZ 1) assignXYZ 6)
```

`diamondExact_singleton_of_not_distributive` — positive control of `diamond-exactness-characterization`; counterexample for `hconst` in `diamond-exactness-characterization`.

```lean
theorem diamondExact_singleton_of_not_distributive :
  cpLat.IsJSL ∧
    cpLat.AscendingChainCondition ∧
      (∀ (φ : St → St), φ = assignXYZ → Monotone cpLat φ) ∧
        (∃ a, (fun x => True) a) ∧
          (¬∀ (b : St), (fun x => b) = assignXYZ) ∧
            (DiamondExact cpLat (fun x => True) fun φ => φ = assignXYZ) ∧
              ¬Distributive cpLat assignXYZ
```

`diamond_entry_id_matters` — cited in `diamond-exactness-characterization`.

```lean
theorem diamond_entry_id_matters :
  have I := fun a => a = fun i => decide (i = 2);
  (∀ (φ : (Fin 3 → Bool) → Fin 3 → Bool), bv3Family φ → Monotone (bvLat 3) φ) ∧
    ¬DiamondExact (bvLat 3) I bv3Family ∧
      ∀ (k : (Fin 3 → Bool) → Fin 3 → Bool) (a : Fin 3 → Bool)
        (g h f : (Fin 3 → Bool) → Fin 3 → Bool),
        bv3Family k →
          I a →
            bv3Family g →
              bv3Family h →
                bv3Family f →
                  ∀ (x : Fin 5 → Fin 3 → Bool),
                    IsLeastSolution (bvLat 3) (diamondWithEntry k a g h f) x →
                      ∀ (v : Fin 5), IsMOPAt (bvLat 3) (diamondWithEntry k a g h f) v (x v)
```

`distributive_of_monotone_of_total` — cited in `exactness-needs-acc`.

```lean
theorem distributive_of_monotone_of_total {α : Type} {L : Lat α} (hL : L.IsJSL)
  (htot : ∀ (a b : α), L.le a b ∨ L.le b a) {f : α → α} (hf : Monotone L f) : Distributive L f
```

`exactness_corollaries_combined_counterexample` — counterexample for `hreach` in `mfp-eq-mop-exactness`; counterexample for `hstrict` in `mfp-eq-mop-exactness`.

```lean
theorem exactness_corollaries_combined_counterexample :
  (bvLat 1).IsJSL ∧
    (bvLat 1).AscendingChainCondition ∧
      (∀ (u : Fin 3), Distributive (bvLat 1) (ugCFG.f u)) ∧
        ¬AllReachable ugCFG ∧
          (¬∀ (u : Fin 3), Strict (bvLat 1) (ugCFG.f u)) ∧
            IsLeastSolution (bvLat 1) ugCFG ugSol ∧ ¬IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2)
```

`exactness_corollaries_need_allReachable_or_strict` — counterexample for `hreach` in `mfp-eq-mop-exactness`; counterexample for `hstrict` in `mfp-eq-mop-exactness`.

```lean
theorem exactness_corollaries_need_allReachable_or_strict :
  ¬AllReachable ugCFG ∧
    (¬∀ (u : Fin 3), Strict (bvLat 1) (ugCFG.f u)) ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧ ¬IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2)
```

`exactness_holds_on_unboundedChainsLat` — non-vacuity witness of `mfp-eq-mop-exactness`; cited in `kildall-computes-mfp`; positive control of `exactness-needs-acc`.

```lean
theorem exactness_holds_on_unboundedChainsLat :
  ∃ G x,
    (∀ (u : Fin 2), Distributive unboundedChainsLat (G.f u)) ∧
      UnreachableStrict unboundedChainsLat G ∧
        IsLeastSolution unboundedChainsLat G x ∧ ∀ (v : Fin 2), IsMOPAt unboundedChainsLat G v (x v)
```

`exactness_needs_distributive` — cited in `mop-le-solution-soundness`; counterexample for `hdist` in `mfp-eq-mop-exactness`.

```lean
theorem exactness_needs_distributive :
  cpLat.IsJSL ∧
    cpLat.AscendingChainCondition ∧
      AllReachable (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) ∧
        UnreachableStrict cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) ∧
          (∀ (u : Fin 5),
              Monotone cpLat ((cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }).f u)) ∧
            (¬∀ (u : Fin 5),
                  Distributive cpLat
                    ((cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }).f u)) ∧
              IsLeastSolution cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top })
                  (diamondSol cpLat { x := Flat.top, y := Flat.top, z := Flat.top } (assignYZ 1 2)
                    (assignYZ 2 1) assignXYZ) ∧
                ¬IsMOPAt cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) 4
                    (diamondSol cpLat { x := Flat.top, y := Flat.top, z := Flat.top } (assignYZ 1 2)
                      (assignYZ 2 1) assignXYZ 4)
```

`exactness_needs_least` — counterexample for `hx` in `mfp-eq-mop-exactness`.

```lean
theorem exactness_needs_least :
  (bvLat 2).IsJSL ∧
    (bvLat 2).AscendingChainCondition ∧
      (∀ (u : Fin 2), Distributive (bvLat 2) (loopGK.f u)) ∧
        UnreachableStrict (bvLat 2) loopGK ∧
          AllReachable loopGK ∧
            (IsSolution (bvLat 2) loopGK fun x x_1 => true) ∧
              (¬IsLeastSolution (bvLat 2) loopGK fun x x_1 => true) ∧
                ¬IsMOPAt (bvLat 2) loopGK 0 fun x => true
```

`exactness_nonvacuous` — non-vacuity witness of `mfp-eq-mop-exactness`.

```lean
theorem exactness_nonvacuous :
  (bvLat 2).IsJSL ∧
    (bvLat 2).AscendingChainCondition ∧
      (∀ (u : Fin 2), Distributive (bvLat 2) (loopGK.f u)) ∧
        UnreachableStrict (bvLat 2) loopGK ∧
          AllReachable loopGK ∧ IsLeastSolution (bvLat 2) loopGK loopGKSol
```

`exists_exactness_combined_counterexamples` — counterexample for `hacc` in `mfp-eq-mop-exactness`; counterexample for `hdist` in `mfp-eq-mop-exactness`; counterexample for `hstrict` in `mfp-eq-mop-exactness`.

```lean
theorem exists_exactness_combined_counterexamples :
  (omegaLat.IsJSL ∧
      ¬omegaLat.AscendingChainCondition ∧
        (∀ (u : Fin 2), Distributive omegaLat (omegaCFG.f u)) ∧
          UnreachableStrict omegaLat omegaCFG ∧
            ¬∃ x,
                IsLeastSolution omegaLat omegaCFG x ∧
                  ∀ (v : Fin 2), IsMOPAt omegaLat omegaCFG v (x v)) ∧
    (cpLat.IsJSL ∧
        cpLat.AscendingChainCondition ∧
          (¬∀ (u : Fin 5),
                Distributive cpLat
                  ((cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }).f u)) ∧
            UnreachableStrict cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) ∧
              ¬∃ x,
                  IsLeastSolution cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top })
                      x ∧
                    ∀ (v : Fin 5),
                      IsMOPAt cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) v
                        (x v)) ∧
      (bvLat 1).IsJSL ∧
        (bvLat 1).AscendingChainCondition ∧
          (∀ (u : Fin 3), Distributive (bvLat 1) (ugCFG.f u)) ∧
            ¬UnreachableStrict (bvLat 1) ugCFG ∧
              ¬∃ x,
                  IsLeastSolution (bvLat 1) ugCFG x ∧ ∀ (v : Fin 3), IsMOPAt (bvLat 1) ugCFG v (x v)
```

`exists_exactness_counterexamples` — counterexample for `hacc` in `mfp-eq-mop-exactness`; counterexample for `hdist` in `mfp-eq-mop-exactness`; counterexample for `hstrict` in `mfp-eq-mop-exactness`; counterexample for `hG` in `gen-kill-distributive-and-exact`; counterexample for `hgen` in `gen-kill-distributive-and-exact`.

```lean
theorem exists_exactness_counterexamples :
  (¬∃ x, IsLeastSolution omegaLat omegaCFG x ∧ ∀ (v : Fin 2), IsMOPAt omegaLat omegaCFG v (x v)) ∧
    (¬∃ x,
          IsLeastSolution cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) x ∧
            ∀ (v : Fin 5),
              IsMOPAt cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) v (x v)) ∧
      (¬∃ x, IsLeastSolution (bvLat 1) ugCFG x ∧ ∀ (v : Fin 3), IsMOPAt (bvLat 1) ugCFG v (x v)) ∧
        ¬∃ x,
            IsLeastSolution (bvLat 2) bbDiamond x ∧
              ∀ (v : Fin 5), IsMOPAt (bvLat 2) bbDiamond v (x v)
```

`exists_isLeastSolution_counterexamples` — counterexample for `hacc` in `mfp-eq-mop-exactness`; counterexample for `hmono` in `mfp-eq-mop-exactness`.

```lean
theorem exists_isLeastSolution_counterexamples :
  (natMaxLat.IsJSL ∧
      ¬natMaxLat.AscendingChainCondition ∧
        (∀ (u : Fin 1), Monotone natMaxLat (succCFG.f u)) ∧
          ¬∃ x, IsLeastSolution natMaxLat succCFG x) ∧
    boolLat.IsJSL ∧
      boolLat.AscendingChainCondition ∧
        (¬∀ (u : Fin 5), Monotone boolLat ((diamond false id (fun b => !b) fun b => !b).f u)) ∧
          ¬∃ x, IsLeastSolution boolLat (diamond false id (fun b => !b) fun b => !b) x
```

`exists_isMOPAt_of_acc` — cited in `mop-le-solution-soundness`.

```lean
theorem exists_isMOPAt_of_acc {n : Nat} {α : Type} (L : Lat α) (G : CFG n α) (hL : L.IsJSL)
  (hacc : L.AscendingChainCondition) (v : Fin n) : ∃ m, IsMOPAt L G v m
```

`genKill_exactness_needs_genKill_form` — counterexample for `hG` in `gen-kill-distributive-and-exact`.

```lean
theorem genKill_exactness_needs_genKill_form :
  (bvLat 2).IsJSL ∧
    AllReachable bbDiamond ∧
      (∀ (u : Fin 5), Monotone (bvLat 2) (bbDiamond.f u)) ∧
        (¬∃ gen kill, ∀ (a : Fin 2 → Bool), bbDiamond.f 3 a = genKill gen kill a) ∧
          IsLeastSolution (bvLat 2) bbDiamond bbSol ∧ ¬IsMOPAt (bvLat 2) bbDiamond 4 (bbSol 4)
```

`genKill_exactness_needs_unreachable_gen_empty` — counterexample for `hgen` in `gen-kill-distributive-and-exact`.

```lean
theorem genKill_exactness_needs_unreachable_gen_empty :
  (∀ (u : Fin 3), ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
    (¬∀ (u : Fin 3), ¬Reachable ugCFG u → ugGen u = fun x => false) ∧
      IsLeastSolution (bvLat 1) ugCFG ugSol ∧ ¬IsMOPAt (bvLat 1) ugCFG 2 (ugSol 2)
```

`genKill_exactness_nonvacuous` — non-vacuity witness of `gen-kill-distributive-and-exact`.

```lean
theorem genKill_exactness_nonvacuous :
  (∀ (u : Fin 2), loopGK.f u = genKill (lgGen u) (lgKill u)) ∧
    (∀ (u : Fin 2), ¬Reachable loopGK u → lgGen u = fun x => false) ∧
      IsLeastSolution (bvLat 2) loopGK loopGKSol
```

`genKill_exists_exactness_combined_counterexamples` — counterexample for `hG` in `gen-kill-distributive-and-exact`; counterexample for `hgen` in `gen-kill-distributive-and-exact`.

```lean
theorem genKill_exists_exactness_combined_counterexamples :
  ((∀ (gen kill : Fin 5 → Fin 2 → Bool),
        (¬∀ (u : Fin 5), bbDiamond.f u = genKill (gen u) (kill u)) ∧
          ∀ (u : Fin 5), ¬Reachable bbDiamond u → gen u = fun x => false) ∧
      ¬∃ x,
          IsLeastSolution (bvLat 2) bbDiamond x ∧
            ∀ (v : Fin 5), IsMOPAt (bvLat 2) bbDiamond v (x v)) ∧
    (∀ (u : Fin 3), ugCFG.f u = genKill (ugGen u) (ugKill u)) ∧
      (¬∀ (u : Fin 3), ¬Reachable ugCFG u → ugGen u = fun x => false) ∧
        ¬∃ x, IsLeastSolution (bvLat 1) ugCFG x ∧ ∀ (v : Fin 3), IsMOPAt (bvLat 1) ugCFG v (x v)
```

`genKill_killOnly_strict_may_not_must` — cited in `gen-kill-distributive-and-exact`.

```lean
theorem genKill_killOnly_strict_may_not_must :
  Strict (bvLat 1) (genKill (fun x => false) fun x => true) ∧
    ¬Strict (bvMustLat 1) (genKill (fun x => false) fun x => true)
```

`genKill_must_strict_nonempty_kill_nonvacuous` — non-vacuity witness of `gen-kill-distributive-and-exact`.

```lean
theorem genKill_must_strict_nonempty_kill_nonvacuous :
  have gen := fun i => decide (i = 0);
  have kill := fun i => decide (i = 0);
  (∃ i, kill i = true) ∧
    Distributive (bvMustLat 2) (genKill gen kill) ∧ Strict (bvMustLat 2) (genKill gen kill)
```

`isEquationSolution_of_isLeastSolution_of_monotone` — cited in `mop-le-solution-soundness`; cited in `diamond-exactness-characterization`; cited in `kildall-computes-mfp`.

```lean
theorem isEquationSolution_of_isLeastSolution_of_monotone {n : Nat} {α : Type} {L : Lat α}
  (hL : L.IsJSL) (G : CFG n α) (hmono : ∀ (u : Fin n), Monotone L (G.f u)) {x : Fin n → α}
  (hx : IsLeastSolution L G x) : IsEquationSolution L G x
```

`kildall_acc_has_no_uniform_fuel` — cited in `mfp-eq-mop-exactness`; cited in `kildall-computes-mfp`; cited in `kildall-computes-mop`; cited in `exactness-needs-acc`.

```lean
theorem kildall_acc_has_no_uniform_fuel :
  unboundedChainsLat.IsJSL ∧
    unboundedChainsLat.AscendingChainCondition ∧
      ∀ (fuel : Nat),
        ∃ G,
          (∀ (u : Fin 1), Monotone unboundedChainsLat (G.f u)) ∧
            kildall unboundedChainsLat G fuel = none
```

`kildall_decidableRel_irrelevant` — cited in `kildall-computes-mfp`; cited in `kildall-computes-mop`.

```lean
theorem kildall_decidableRel_irrelevant {n : Nat} {α : Type} {L : Lat α}
  (d1 d2 : DecidableRel L.le) (G : CFG n α) (fuel : Nat) : kildall L G fuel = kildall L G fuel
```

`kildall_fuel_bound_attained` — counterexample for `hfuel` in `kildall-computes-mfp`.

```lean
theorem kildall_fuel_bound_attained (m h : Nat) :
  (finChainLat h).IsJSL ∧
    (∀ (u : Fin (m + 1)), Monotone (finChainLat h) ((selfLoopsCFG m h).f u)) ∧
      (finChainLat h).HeightLe h ∧
        ¬(m + 1) * (h + 1) + 1 ≤ (m + 1) * (h + 1) ∧
          kildall (finChainLat h) (selfLoopsCFG m h) ((m + 1) * (h + 1)) = none ∧
            (kildall (finChainLat h) (selfLoopsCFG m h) ((m + 1) * (h + 1) + 1)).isSome = true
```

`kildall_isMOPAt_counterexamples` — counterexample for `hdist` in `kildall-computes-mop`; counterexample for `hstrict` in `kildall-computes-mop`; counterexample for `hh` in `kildall-computes-mop`; counterexample for `hfuel` in `kildall-computes-mop`.

```lean
theorem kildall_isMOPAt_counterexamples :
  (cpLat.IsJSL ∧
      cpLat.HeightLe 6 ∧
        5 * (6 + 1) + 1 ≤ 36 ∧
          AllReachable (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) ∧
            UnreachableStrict cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) ∧
              (¬∀ (u : Fin 5),
                    Distributive cpLat
                      ((cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }).f u)) ∧
                ¬∃ x,
                    kildall cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) 36 =
                        some x ∧
                      IsLeastSolution cpLat
                          (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top }) x ∧
                        ∀ (v : Fin 5),
                          IsMOPAt cpLat (cpDiamond { x := Flat.top, y := Flat.top, z := Flat.top })
                            v (x v)) ∧
    ((bvLat 1).IsJSL ∧
        (bvLat 1).HeightLe 1 ∧
          3 * (1 + 1) + 1 ≤ 7 ∧
            (∀ (u : Fin 3), Distributive (bvLat 1) (ugCFG.f u)) ∧
              ¬UnreachableStrict (bvLat 1) ugCFG ∧
                ¬∃ x,
                    kildall (bvLat 1) ugCFG 7 = some x ∧
                      IsLeastSolution (bvLat 1) ugCFG x ∧
                        ∀ (v : Fin 3), IsMOPAt (bvLat 1) ugCFG v (x v)) ∧
      (natMaxLat.IsJSL ∧
          (∀ (u : Fin 1), Distributive natMaxLat (succCFG.f u)) ∧
            AllReachable succCFG ∧
              UnreachableStrict natMaxLat succCFG ∧
                (∀ (h : Nat), ¬natMaxLat.HeightLe h) ∧
                  ∀ (fuel : Nat),
                    ¬∃ x,
                        kildall natMaxLat succCFG fuel = some x ∧
                          IsLeastSolution natMaxLat succCFG x ∧
                            ∀ (v : Fin 1), IsMOPAt natMaxLat succCFG v (x v)) ∧
        ∀ (h : Nat),
          (finChainLat h).IsJSL ∧
            (∀ (u : Fin (0 + 1)), Distributive (finChainLat h) ((selfLoopsCFG 0 h).f u)) ∧
              AllReachable (selfLoopsCFG 0 h) ∧
                UnreachableStrict (finChainLat h) (selfLoopsCFG 0 h) ∧
                  (finChainLat h).HeightLe h ∧
                    ¬1 * (h + 1) + 1 ≤ 1 * (h + 1) ∧
                      ¬∃ x,
                          kildall (finChainLat h) (selfLoopsCFG 0 h) (1 * (h + 1)) = some x ∧
                            IsLeastSolution (finChainLat h) (selfLoopsCFG 0 h) x ∧
                              ∀ (v : Fin (0 + 1)),
                                IsMOPAt (finChainLat h) (selfLoopsCFG 0 h) v (x v)
```

`kildall_isMOPAt_nonvacuous` — non-vacuity witness of `kildall-computes-mop`.

```lean
theorem kildall_isMOPAt_nonvacuous :
  (bvLat 2).IsJSL ∧
    (∀ (u : Fin 2), Distributive (bvLat 2) (loopGK.f u)) ∧
      UnreachableStrict (bvLat 2) loopGK ∧
        (bvLat 2).HeightLe 2 ∧
          2 * (2 + 1) + 1 ≤ 7 ∧
            ∃ x,
              kildall (bvLat 2) loopGK 7 = some x ∧
                IsLeastSolution (bvLat 2) loopGK x ∧ ∀ (v : Fin 2), IsMOPAt (bvLat 2) loopGK v (x v)
```

`kildall_needs_eq_some` — counterexample for `h` in `kildall-computes-mfp`.

```lean
theorem kildall_needs_eq_some :
  (bvLat 2).IsJSL ∧
    (∀ (u : Fin 2), Monotone (bvLat 2) (loopGK.f u)) ∧
      (kildall (bvLat 2) loopGK 7 ≠ some fun x x_1 => true) ∧
        (¬IsLeastSolution (bvLat 2) loopGK fun x x_1 => true) ∧
          (kildall (bvLat 2) loopGK 7 ≠ some fun x x_1 => false) ∧
            ¬IsSolution (bvLat 2) loopGK fun x x_1 => false
```

`kildall_needs_heightLe` — counterexample for `hh` in `kildall-computes-mfp`; cited in `exactness-needs-acc`.

```lean
theorem kildall_needs_heightLe :
  natMaxLat.IsJSL ∧
    (∀ (u : Fin 1), Monotone natMaxLat (succCFG.f u)) ∧
      (∀ (u : Fin 1), Distributive natMaxLat (succCFG.f u)) ∧
        AllReachable succCFG ∧
          ¬natMaxLat.AscendingChainCondition ∧
            (∀ (h : Nat), ¬natMaxLat.HeightLe h) ∧
              ∀ (fuel : Nat), kildall natMaxLat succCFG fuel = none
```

`kildall_needs_monotone` — counterexample for `hmono` in `kildall-computes-mfp`.

```lean
theorem kildall_needs_monotone :
  boolLat.IsJSL ∧
    (¬∀ (u : Fin 2), Monotone boolLat (notCFG.f u)) ∧
      boolLat.HeightLe 1 ∧
        2 * (1 + 1) + 1 ≤ 10 ∧
          (∃ x,
              kildall boolLat notCFG 10 = some x ∧
                (x 0, x 1) = (true, true) ∧
                  IsSolution boolLat notCFG x ∧ ¬IsLeastSolution boolLat notCFG x) ∧
            ¬∃ x, kildall boolLat notCFG 10 = some x ∧ IsLeastSolution boolLat notCFG x
```

`kildall_nonvacuous` — non-vacuity witness of `kildall-computes-mfp`.

```lean
theorem kildall_nonvacuous :
  (bvLat 2).IsJSL ∧
    (∀ (u : Fin 2), Monotone (bvLat 2) (loopGK.f u)) ∧
      (bvLat 2).HeightLe 2 ∧
        2 * (2 + 1) + 1 ≤ 7 ∧
          Option.map (fun x => (x 0 0, x 0 1, x 1 0, x 1 1)) (kildall (bvLat 2) loopGK 7) =
            some (false, false, true, true)
```

`monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty` — cited in `diamond-exactness-characterization`.

```lean
theorem monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty {α : Type} {L : Lat α}
  (hL : L.IsJSL) (hacc : L.AscendingChainCondition) {I : α → Prop} {F : (α → α) → Prop}
  (hconst : ∀ (b : α), F fun x => b) (hI : ∃ a, I a) (he : DiamondExact L I F) (f : α → α) :
  F f → Monotone L f
```

`monotone_of_distributive` — cited in `mfp-eq-mop-exactness`; cited in `kildall-computes-mop`.

```lean
theorem monotone_of_distributive {α : Type} {L : Lat α} (hL : L.IsJSL) {f : α → α}
  (hf : Distributive L f) : Monotone L f
```

`notCFG_isLeastSolution_not_isEquationSolution` — cited in `mop-le-solution-soundness`; cited in `diamond-exactness-characterization`; cited in `kildall-computes-mfp`.

```lean
theorem notCFG_isLeastSolution_not_isEquationSolution :
  IsLeastSolution boolLat notCFG notSol ∧ ∀ (x : Fin 2 → Bool), ¬IsEquationSolution boolLat notCFG x
```

`omegaLat_monotone_distributive` — cited in `exactness-needs-acc`.

```lean
theorem omegaLat_monotone_distributive (f : OmegaTwo → OmegaTwo) (hf : Monotone omegaLat f) :
  Distributive omegaLat f
```

`omegaLat_total` — cited in `exactness-needs-acc`.

```lean
theorem omegaLat_total (a b : OmegaTwo) : omegaLat.le a b ∨ omegaLat.le b a
```

`soundness_needs_isMOPAt` — counterexample for `hm` in `mop-le-solution-soundness`.

```lean
theorem soundness_needs_isMOPAt :
  (bvLat 2).LeTrans ∧
    (∀ (u : Fin 2), Monotone (bvLat 2) (loopGK.f u)) ∧
      IsSolution (bvLat 2) loopGK loopGKSol ∧
        (¬IsMOPAt (bvLat 2) loopGK 0 fun x => true) ∧ ¬(bvLat 2).le (fun x => true) (loopGKSol 0)
```

`soundness_needs_leTrans` — counterexample for `htrans` in `mop-le-solution-soundness`.

```lean
theorem soundness_needs_leTrans :
  ¬notTransLat.LeTrans ∧
    (∀ (u : Fin 3), Monotone notTransLat (notTransCFG.f u)) ∧
      (IsSolution notTransLat notTransCFG fun v => v) ∧
        IsMOPAt notTransLat notTransCFG 2 0 ∧ ¬notTransLat.le 0 2 ∧ ∃ p, ¬notTransLat.le p.val 2
```

`soundness_needs_monotone` — counterexample for `hmono` in `mop-le-solution-soundness`.

```lean
theorem soundness_needs_monotone :
  boolLat.LeTrans ∧
    (¬∀ (u : Fin 2), Monotone boolLat (notCFG.f u)) ∧
      IsLeastSolution boolLat notCFG notSol ∧
        IsMOPAt boolLat notCFG 1 true ∧
          ¬boolLat.le true (notSol 1) ∧ ∃ p, ¬boolLat.le p.val (notSol 1)
```

`soundness_needs_solution` — counterexample for `hx` in `mop-le-solution-soundness`.

```lean
theorem soundness_needs_solution :
  (bvLat 2).LeTrans ∧
    (∀ (u : Fin 2), Monotone (bvLat 2) (loopGK.f u)) ∧
      (¬IsSolution (bvLat 2) loopGK fun x x_1 => false) ∧
        IsMOPAt (bvLat 2) loopGK 1 (loopGKSol 1) ∧
          (¬(bvLat 2).le (loopGKSol 1) fun x => false) ∧ ∃ p, ¬(bvLat 2).le p.val fun x => false
```

`soundness_nonvacuous` — non-vacuity witness of `mop-le-solution-soundness`.

```lean
theorem soundness_nonvacuous :
  (bvLat 2).LeTrans ∧
    (∀ (u : Fin 2), Monotone (bvLat 2) (loopGK.f u)) ∧
      IsSolution (bvLat 2) loopGK loopGKSol ∧ IsMOPAt (bvLat 2) loopGK 1 (loopGKSol 1)
```

`stepMid_distributive` — cited in `mfp-eq-mop-exactness`.

```lean
theorem stepMid_distributive (m : Nat) : Distributive unboundedChainsLat (stepMid m)
```

`strict_and_genKill_exactness_needs_least` — counterexample for `hx` in `mfp-eq-mop-exactness`; counterexample for `hx` in `gen-kill-distributive-and-exact`.

```lean
theorem strict_and_genKill_exactness_needs_least :
  have G :=
    { edges := [(0, 0)], entry := 0, init := fun x => false,
      f := fun x => genKill (fun x => false) fun x => false };
  have x := fun x x_1 => true;
  (bvLat 1).IsJSL ∧
    (bvLat 1).AscendingChainCondition ∧
      (∀ (u : Fin 1), Distributive (bvLat 1) (G.f u)) ∧
        (∀ (u : Fin 1), Strict (bvLat 1) (G.f u)) ∧
          AllReachable G ∧
            (∀ (u : Fin 1), G.f u = genKill (fun x => false) fun x => false) ∧
              (∀ (u : Fin 1), ¬Reachable G u → (fun x => false) = fun x => false) ∧
                IsSolution (bvLat 1) G x ∧
                  ¬IsLeastSolution (bvLat 1) G x ∧ ¬IsMOPAt (bvLat 1) G 0 (x 0)
```

`strict_exactness_needs_acc` — counterexample for `hacc` in `mfp-eq-mop-exactness`.

```lean
theorem strict_exactness_needs_acc :
  omegaLat.IsJSL ∧
    ¬omegaLat.AscendingChainCondition ∧
      (∀ (u : Fin 2), Distributive omegaLat (omegaStrictCFG.f u)) ∧
        (∀ (u : Fin 2), Strict omegaLat (omegaStrictCFG.f u)) ∧
          AllReachable omegaStrictCFG ∧
            IsLeastSolution omegaLat omegaStrictCFG omegaStrictSol ∧
              IsMOPAt omegaLat omegaStrictCFG 1 OmegaTwo.omega ∧
                ¬IsMOPAt omegaLat omegaStrictCFG 1 (omegaStrictSol 1)
```

`strict_exactness_needs_distributive` — counterexample for `hdist` in `mfp-eq-mop-exactness`.

```lean
theorem strict_exactness_needs_distributive :
  (bvLat 2).IsJSL ∧
    (bvLat 2).AscendingChainCondition ∧
      AllReachable strictBBDiamond ∧
        (∀ (u : Fin 5), Strict (bvLat 2) (strictBBDiamond.f u)) ∧
          (∀ (u : Fin 5), Monotone (bvLat 2) (strictBBDiamond.f u)) ∧
            (¬∀ (u : Fin 5), Distributive (bvLat 2) (strictBBDiamond.f u)) ∧
              IsLeastSolution (bvLat 2) strictBBDiamond strictBBSol ∧
                ¬IsMOPAt (bvLat 2) strictBBDiamond 4 (strictBBSol 4)
```

`strict_exactness_nonvacuous` — non-vacuity witness of `mfp-eq-mop-exactness`.

```lean
theorem strict_exactness_nonvacuous :
  (bvLat 2).IsJSL ∧
    (bvLat 2).AscendingChainCondition ∧
      (∀ (u : Fin 2), Distributive (bvLat 2) (strictLoopGK.f u)) ∧
        (∀ (u : Fin 2), Strict (bvLat 2) (strictLoopGK.f u)) ∧
          AllReachable strictLoopGK ∧ IsLeastSolution (bvLat 2) strictLoopGK strictLoopGKSol
```

`ugCFG_isMOPAt_two_empty` — cited in `reachable-node-not-exact-unreachable-gen`.

```lean
theorem ugCFG_isMOPAt_two_empty : IsMOPAt (bvLat 1) ugCFG 2 fun x => false
```

`unreachableStrict_strictly_between_nonvacuous` — non-vacuity witness of `mfp-eq-mop-exactness`.

```lean
theorem unreachableStrict_strictly_between_nonvacuous :
  (bvLat 1).IsJSL ∧
    (bvLat 1).AscendingChainCondition ∧
      (∀ (u : Fin 3), Distributive (bvLat 1) (midStrictCFG.f u)) ∧
        UnreachableStrict (bvLat 1) midStrictCFG ∧
          ¬AllReachable midStrictCFG ∧
            (¬∀ (u : Fin 3), Strict (bvLat 1) (midStrictCFG.f u)) ∧
              IsLeastSolution (bvLat 1) midStrictCFG midStrictSol
```

### Instances used by witnesses and counterexamples (quoted from the sources)

`Toy.Dataflow.boolLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- The two-point lattice `false < true` (one bit of a may-analysis). -/
def boolLat : Lat Bool where
  le a b := a = true → b = true
  join a b := a || b
  bot := false
```

`Toy.Dataflow.natMaxLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- The natural numbers under `max`: a join-semilattice with bottom but with
infinite ascending chains. -/
def natMaxLat : Lat Nat where
  le a b := a ≤ b
  join a b := max a b
  bot := 0
```

`Toy.Dataflow.finChainLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Finite chain `0 < 1 < ... < h` of height `h`. -/
def finChainLat (h : Nat) : Lat (Fin (h + 1)) where
  le a b := a.val ≤ b.val
  join a b := if a.val ≤ b.val then b else a
  bot := ⟨0, Nat.zero_lt_succ h⟩
```

`Toy.Dataflow.OmegaTwo` (ToyDataflow/Examples.lean):

```lean
/-- The chain `0 < 1 < 2 < ⋯ < ω < ω+1`. -/
inductive OmegaTwo where
  | fin (k : Nat)
  | omega
  | omega1
  deriving DecidableEq
```

`Toy.Dataflow.OmegaTwo.le` (ToyDataflow/Examples.lean):

```lean
def le : OmegaTwo → OmegaTwo → Prop
  | fin a, fin b => a ≤ b
  | fin _, _ => True
  | omega, fin _ => False
  | omega, _ => True
  | omega1, omega1 => True
  | omega1, _ => False
```

`Toy.Dataflow.OmegaTwo.join` (ToyDataflow/Examples.lean):

```lean
def join : OmegaTwo → OmegaTwo → OmegaTwo
  | fin a, fin b => fin (max a b)
  | fin _, b => b
  | omega, fin _ => omega
  | omega, b => b
  | omega1, _ => omega1
```

`Toy.Dataflow.OmegaTwo.succ` (ToyDataflow/Examples.lean):

```lean
/-- Successor on the chain: `k ↦ k + 1`, `ω ↦ ω + 1`, `ω + 1 ↦ ω + 1`. -/
def succ : OmegaTwo → OmegaTwo
  | fin k => fin (k + 1)
  | omega => omega1
  | omega1 => omega1
```

`Toy.Dataflow.OmegaTwo.succStrict` (ToyDataflow/ExactnessExamples.lean):

```lean
def OmegaTwo.succStrict : OmegaTwo → OmegaTwo
  | .fin 0 => .fin 0
  | .fin (k + 1) => .fin (k + 2)
  | .omega => .omega1
  | .omega1 => .omega1
```

`Toy.Dataflow.omegaLat` (ToyDataflow/Examples.lean):

```lean
def omegaLat : Lat OmegaTwo := ⟨OmegaTwo.le, OmegaTwo.join, .fin 0⟩
```

`Toy.Dataflow.UnboundedChains` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Disjoint union of the finite chains `mid m 0 < mid m 1 < ... < mid m m`, one for
each `m`, with a common `bot` and `top`. It satisfies the ascending chain condition
but has no finite height bound (`unboundedChainsLat_acc`, `unboundedChainsLat_not_heightLe`). -/
inductive UnboundedChains where
  | bot
  | mid (m k : Nat)
  | top
  deriving DecidableEq
```

`Toy.Dataflow.UnboundedChains.le` (ToyDataflow/LatticeExamples.lean):

```lean
def le : UnboundedChains → UnboundedChains → Prop
  | bot, _ => True
  | _, top => True
  | mid m₁ k₁, mid m₂ k₂ => (m₁ = m₂ ∧ k₁ = k₂) ∨ (m₁ = m₂ ∧ k₁ ≤ k₂ ∧ k₂ ≤ m₁)
  | _, _ => False
```

`Toy.Dataflow.UnboundedChains.join` (ToyDataflow/LatticeExamples.lean):

```lean
def join : UnboundedChains → UnboundedChains → UnboundedChains
  | bot, b => b
  | a, bot => a
  | top, _ => top
  | _, top => top
  | mid m₁ k₁, mid m₂ k₂ =>
    if m₁ = m₂ then
      if k₁ = k₂ then mid m₁ k₁
      else if max k₁ k₂ ≤ m₁ then mid m₁ (max k₁ k₂)
      else top
    else top
```

`Toy.Dataflow.unboundedChainsLat` (ToyDataflow/LatticeExamples.lean):

```lean
def unboundedChainsLat : Lat UnboundedChains :=
  ⟨UnboundedChains.le, UnboundedChains.join, .bot⟩
```

`Toy.Dataflow.WithBotInt` (ToyDataflow/LatticeExamples.lean):

```lean
/-- `Int` with an explicit bottom element `⊥`. -/
inductive WithBotInt where
  | bot
  | val (z : Int)
  deriving DecidableEq
```

`Toy.Dataflow.WithBotInt.le` (ToyDataflow/LatticeExamples.lean):

```lean
def le : WithBotInt → WithBotInt → Prop
  | bot, _ => True
  | val _, bot => False
  | val a, val b => a ≤ b
```

`Toy.Dataflow.WithBotInt.join` (ToyDataflow/LatticeExamples.lean):

```lean
def join : WithBotInt → WithBotInt → WithBotInt
  | bot, b => b
  | a, bot => a
  | val a, val b => val (max a b)
```

`Toy.Dataflow.withBotIntLat` (ToyDataflow/LatticeExamples.lean):

```lean
def withBotIntLat : Lat WithBotInt := ⟨WithBotInt.le, WithBotInt.join, .bot⟩
```

`Toy.Dataflow.wbNeg` (ToyDataflow/DiamondExamples.lean):

```lean
/-- Negation on `Int ∪ {⊥}` (strict). -/
def wbNeg : WithBotInt → WithBotInt
  | .bot => .bot
  | .val z => .val (-z)
```

`Toy.Dataflow.notReflLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Violates reflexivity only: `le a b := (a = false)`, so `true ≤ true` fails. -/
def notReflLat : Lat Bool := { boolLat with le := fun a _ => a = false }
```

`Toy.Dataflow.notTransLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Violates transitivity: `0 ≤ 1` and `1 ≤ 2` but not `0 ≤ 2`. It also violates
`JoinLeIff` and `BotLe` (`notTransLat_law_profile`); violating `LeTrans` alone is
impossible (`no_lat_violates_only_leTrans`). -/
def notTransLat : Lat (Fin 3) where
  le a b := a.val ≤ b.val ∧ b.val ≤ a.val + 1
  join a b := if a.val ≤ b.val then b else a
  bot := 0
```

`Toy.Dataflow.fin4PreLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- A preorder-like structure on `Fin 4` satisfying `LeRefl`, `JoinLeIff` and `BotLe`
but neither `LeAntisymm` nor `LeTrans`: antisymmetry is needed to derive
transitivity. -/
def fin4PreLat : Lat (Fin 4) where
  le a b := match a, b with
    | 0, _ => True
    | 1, 1 | 1, 2 | 1, 3 => True
    | 2, 0 | 2, 2 | 2, 3 => True
    | 3, 2 | 3, 3 => True
    | _, _ => False
  join a b := match a, b with
    | 0, b => b
    | a, 0 => a
    | 1, 1 => 1
    | 2, 2 => 2
    | _, _ => 3
  bot := 0
```

`Toy.Dataflow.notAntisymmLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Violates antisymmetry (`le` is total). -/
def notAntisymmLat : Lat Bool := { boolLat with le := fun _ _ => True }
```

`Toy.Dataflow.notJoinLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Violates the join law: `join` is the left projection. -/
def notJoinLat : Lat Bool := { boolLat with join := fun a _ => a }
```

`Toy.Dataflow.notBotLat` (ToyDataflow/LatticeExamples.lean):

```lean
/-- Violates the bottom law: `bot := true`. -/
def notBotLat : Lat Bool := { boolLat with bot := true }
```

`Toy.Dataflow.notTransCFG` (ToyDataflow/Examples.lean):

```lean
/-- Path `0 → 1 → 2` with identity transfers on the non-transitive `notTransLat`. -/
def notTransCFG : CFG 3 (Fin 3) := ⟨[(0, 1), (1, 2)], 0, 0, fun _ => id⟩
```

`Toy.Dataflow.notCFG` (ToyDataflow/Examples.lean):

```lean
/-- Entry `0` with a self-loop and an edge to `1`; every transfer is negation. -/
def notCFG : CFG 2 Bool where
  edges := [(0, 0), (0, 1)]
  entry := 0
  init := false
  f := fun _ b => !b
```

`Toy.Dataflow.notSol` (ToyDataflow/Examples.lean):

```lean
def notSol : Fin 2 → Bool := fun v => decide (v = 0)
```

`Toy.Dataflow.succCFG` (ToyDataflow/Examples.lean):

```lean
/-- `0 → 0` with transfer `n ↦ n + 1` on the natural numbers under `max`. -/
def succCFG : CFG 1 Nat := ⟨[(0, 0)], 0, 0, fun _ n => n + 1⟩
```

`Toy.Dataflow.loopGK` (ToyDataflow/Examples.lean):

```lean
/-- `0 → 1`, `1 → 1` (a loop), gen/kill transfers over `bvLat 2`. -/
def loopGK : CFG 2 (Fin 2 → Bool) where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (lgGen u) (lgKill u)
```

`Toy.Dataflow.lgGen` (ToyDataflow/Examples.lean):

```lean
/-- Node 0 generates bit 0; node 1 generates bit 1 and kills bit 0. -/
def lgGen : Fin 2 → Fin 2 → Bool := fun u i => decide (i = u)
```

`Toy.Dataflow.lgKill` (ToyDataflow/Examples.lean):

```lean
def lgKill : Fin 2 → Fin 2 → Bool := fun u i => decide (u = 1 ∧ i = 0)
```

`Toy.Dataflow.loopGKSol` (ToyDataflow/Examples.lean):

```lean
/-- Its least solution: `∅` at node 0, `{0, 1}` at node 1. -/
def loopGKSol : Fin 2 → Fin 2 → Bool := fun v _ => decide (v = 1)
```

`Toy.Dataflow.strictLoopGK` (ToyDataflow/ExactnessExamples.lean):

```lean
/-- A gen/kill loop all of whose transfers are strict (empty gen sets). -/
def strictLoopGK : CFG 2 (Fin 2 → Bool) where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := fun _ => true
  f := fun u => genKill (fun _ => false) (fun i => decide (u = 1 ∧ i = 0))
```

`Toy.Dataflow.strictLoopGKSol` (ToyDataflow/ExactnessExamples.lean):

```lean
def strictLoopGKSol : Fin 2 → Fin 2 → Bool := fun _ _ => true
```

`Toy.Dataflow.ugCFG` (ToyDataflow/Examples.lean):

```lean
/-- Entry `0 → 2`; node `1` has no incoming edge (unreachable), generates the bit,
and has an edge `1 → 2`. -/
def ugCFG : CFG 3 (Fin 1 → Bool) where
  edges := [(0, 2), (1, 2)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (ugGen u) (ugKill u)
```

`Toy.Dataflow.ugGen` (ToyDataflow/Examples.lean):

```lean
def ugGen : Fin 3 → Fin 1 → Bool := fun u _ => decide (u = 1)
```

`Toy.Dataflow.ugKill` (ToyDataflow/Examples.lean):

```lean
def ugKill : Fin 3 → Fin 1 → Bool := fun _ _ => false
```

`Toy.Dataflow.ugSol` (ToyDataflow/Examples.lean):

```lean
def ugSol : Fin 3 → Fin 1 → Bool := fun v _ => decide (v = 2)
```

`Toy.Dataflow.midStrictCFG` (ToyDataflow/ExactnessExamples.lean):

```lean
/-- A CFG where `UnreachableStrict` holds but neither `AllReachable` nor
`∀ u, Strict`: node 2 is unreachable (with empty gen), while node 0 is non-strict
(gen `{0}`). -/
def midStrictCFG : CFG 3 (Fin 1 → Bool) where
  edges := [(0, 1)]
  entry := 0
  init := fun _ => false
  f := fun u => genKill (fun _ => decide (u = 0)) (fun _ => false)
```

`Toy.Dataflow.midStrictSol` (ToyDataflow/ExactnessExamples.lean):

```lean
def midStrictSol : Fin 3 → Fin 1 → Bool := fun v _ => decide (v = 1)
```

`Toy.Dataflow.omegaCFG` (ToyDataflow/Examples.lean):

```lean
/-- Entry `0 → 1`, loop `1 → 1` with transfer `succ`. -/
def omegaCFG : CFG 2 OmegaTwo where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := .fin 0
  f := fun u => if u = 1 then OmegaTwo.succ else id
```

`Toy.Dataflow.omegaSol` (ToyDataflow/Examples.lean):

```lean
/-- Least solution: `0` at node 0, `ω + 1` at node 1. -/
def omegaSol : Fin 2 → OmegaTwo := fun v => if v = 1 then .omega1 else .fin 0
```

`Toy.Dataflow.omegaStrictCFG` (ToyDataflow/ExactnessExamples.lean):

```lean
def omegaStrictCFG : CFG 2 OmegaTwo where
  edges := [(0, 1), (1, 1)]
  entry := 0
  init := .fin 1
  f := fun u => if u = 1 then OmegaTwo.succStrict else id
```

`Toy.Dataflow.omegaStrictSol` (ToyDataflow/ExactnessExamples.lean):

```lean
def omegaStrictSol : Fin 2 → OmegaTwo := fun v => if v = 1 then .omega1 else .fin 1
```

`Toy.Dataflow.bothBits` (ToyDataflow/GenKill.lean):

```lean
/-- "Both bits set", broadcast to both bits: monotone but not distributive. -/
def bothBits (a : Fin 2 → Bool) : Fin 2 → Bool := fun _ => a 0 && a 1
```

`Toy.Dataflow.bbDiamond` (ToyDataflow/Examples.lean):

```lean
/-- Branches set bit 0 and bit 1 respectively (as gen/kill functions that kill
everything); the join node computes `bothBits`, which is not gen/kill. -/
def bbDiamond : CFG 5 (Fin 2 → Bool) :=
  diamond (fun _ => false) (genKill (fun i => decide (i = 0)) (fun _ => true))
    (genKill (fun i => decide (i = 1)) (fun _ => true)) bothBits
```

`Toy.Dataflow.bbSol` (ToyDataflow/Examples.lean):

```lean
def bbSol : Fin 5 → Fin 2 → Bool :=
  diamondSol (bvLat 2) (fun _ => false) (genKill (fun i => decide (i = 0)) (fun _ => true))
    (genKill (fun i => decide (i = 1)) (fun _ => true)) bothBits
```

`Toy.Dataflow.strictBBDiamond` (ToyDataflow/ExactnessExamples.lean):

```lean
def strictBBDiamond : CFG 5 (Fin 2 → Bool) :=
  diamond (fun _ => true)
    (genKill (fun _ => false) (fun i => decide (i = 1)))
    (genKill (fun _ => false) (fun i => decide (i = 0)))
    bothBits
```

`Toy.Dataflow.strictBBSol` (ToyDataflow/ExactnessExamples.lean):

```lean
def strictBBSol : Fin 5 → Fin 2 → Bool :=
  diamondSol (bvLat 2) (fun _ => true)
    (genKill (fun _ => false) (fun i => decide (i = 1)))
    (genKill (fun _ => false) (fun i => decide (i = 0)))
    bothBits
```

`Toy.Dataflow.diamondSol` (ToyDataflow/Diamond.lean):

```lean
/-- The explicit least solution of the diamond (for monotone transfers). -/
def diamondSol (L : Lat α) (a : α) (g h f : α → α) : Fin 5 → α :=
  fun v => if v = 3 then L.join (g a) (h a) else if v = 4 then f (L.join (g a) (h a)) else a
```

`Toy.Dataflow.idNotFamily` (ToyDataflow/Examples.lean):

```lean
/-- The family `{id, not}` on `boolLat`. -/
def idNotFamily : (Bool → Bool) → Prop := fun φ => φ = id ∨ φ = (fun b => !b)
```

`Toy.Dataflow.wbNegFamily` (ToyDataflow/DiamondExamples.lean):

```lean
/-- All constants plus negation. -/
def wbNegFamily : (WithBotInt → WithBotInt) → Prop :=
  fun φ => (∃ b, φ = fun _ => b) ∨ φ = wbNeg
```

`Toy.Dataflow.cpFamily` (ToyDataflow/Examples.lean):

```lean
/-- The constant-propagation family of the diamond program. -/
def cpFamily : (St → St) → Prop :=
  fun φ => φ = assignYZ 1 2 ∨ φ = assignYZ 2 1 ∨ φ = assignXYZ
```

`Toy.Dataflow.twoStepFamily` (ToyDataflow/DiamondExamples.lean):

```lean
/-- Single-variable assignments `y := 1`, `z := 2`, `y := 2`, `z := 1`, `x := y + z`. -/
def twoStepFamily : (St → St) → Prop :=
  fun φ => φ = setY 1 ∨ φ = setZ 2 ∨ φ = setY 2 ∨ φ = setZ 1 ∨ φ = assignXYZ
```

`Toy.Dataflow.diamond2` (ToyDataflow/DiamondExamples.lean):

```lean
/-- A two-path acyclic CFG with two transfers on each branch:
`0 → 1 → 2 → 5`, `0 → 3 → 4 → 5`, `5 → 6`, with transfers `g1, g2` on the first
branch, `h1, h2` on the second, `f` at the join node 5, and `id` at nodes 0 and 6. -/
def diamond2 {α : Type} (a : α) (g1 g2 h1 h2 f : α → α) : CFG 7 α where
  edges := [(0, 1), (1, 2), (2, 5), (0, 3), (3, 4), (4, 5), (5, 6)]
  entry := 0
  init := a
  f := fun v => if v = 1 then g1 else if v = 2 then g2 else if v = 3 then h1 else
    if v = 4 then h2 else if v = 5 then f else id
```

`Toy.Dataflow.diamond2Sol` (ToyDataflow/DiamondExamples.lean):

```lean
/-- The explicit least solution of `diamond2` (for monotone transfers). -/
def diamond2Sol {α : Type} (L : Lat α) (a : α) (g1 g2 h1 h2 f : α → α) : Fin 7 → α :=
  fun v => if v = 2 then g1 a else if v = 4 then h1 a else
    if v = 5 then L.join (g2 (g1 a)) (h2 (h1 a)) else
    if v = 6 then f (L.join (g2 (g1 a)) (h2 (h1 a))) else a
```

`Toy.Dataflow.diamondWithEntry` (ToyDataflow/DiamondExamples.lean):

```lean
/-- The diamond with an arbitrary entry transfer `k` instead of `id`. -/
def diamondWithEntry {α : Type} (k : α → α) (a : α) (g h f : α → α) : CFG 5 α where
  edges := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
  entry := 0
  init := a
  f := fun v => if v = 0 then k else if v = 1 then g else if v = 2 then h else if v = 3 then f else id
```

`Toy.Dataflow.bv3G` (ToyDataflow/DiamondExamples.lean):

```lean
/-- Members of the family used in `diamond_entry_id_matters`. -/
def bv3G (s : Fin 3 → Bool) : Fin 3 → Bool := fun i => decide (i = 0) && s 2
```

`Toy.Dataflow.bv3H` (ToyDataflow/DiamondExamples.lean):

```lean
def bv3H (s : Fin 3 → Bool) : Fin 3 → Bool := fun i => decide (i = 1) && s 2
```

`Toy.Dataflow.bv3F` (ToyDataflow/DiamondExamples.lean):

```lean
def bv3F (s : Fin 3 → Bool) : Fin 3 → Bool := fun _ => s 0 && s 1
```

`Toy.Dataflow.bv3Family` (ToyDataflow/DiamondExamples.lean):

```lean
def bv3Family : ((Fin 3 → Bool) → Fin 3 → Bool) → Prop :=
  fun φ => φ = bv3G ∨ φ = bv3H ∨ φ = bv3F
```

`Toy.Dataflow.satSucc` (ToyDataflow/KildallExamples.lean):

```lean
/-- Saturating successor on the chain `0 < 1 < ⋯ < h`. -/
def satSucc (h : Nat) (a : Fin (h + 1)) : Fin (h + 1) :=
  if ha : a.val < h then ⟨a.val + 1, by omega⟩ else a
```

`Toy.Dataflow.selfLoopsCFG` (ToyDataflow/KildallExamples.lean):

```lean
/-- `m + 1` nodes, each with a self-loop, transfer `satSucc h`. -/
def selfLoopsCFG (m h : Nat) : CFG (m + 1) (Fin (h + 1)) where
  edges := (List.finRange (m + 1)).map (fun u => (u, u))
  entry := 0
  init := ⟨0, Nat.zero_lt_succ h⟩
  f := fun _ => satSucc h
```

`Toy.Dataflow.stepMid` (ToyDataflow/KildallExamples.lean):

```lean
/-- Climb the chain `mid m 0 < ⋯ < mid m m` one step at a time. -/
def stepMid (m : Nat) : UnboundedChains → UnboundedChains
  | .bot => .bot
  | .mid m' k =>
    if m' = m then
      if k < m then .mid m (k + 1)
      else if k = m then .mid m m
      else .top
    else .top
  | .top => .top
```

`Toy.Dataflow.stepMidCFG` (ToyDataflow/KildallExamples.lean):

```lean
def stepMidCFG (m : Nat) : CFG 1 UnboundedChains :=
  ⟨[(0, 0)], 0, .mid m 0, fun _ => stepMid m⟩
```

`Toy.Dataflow.copyBit0` (ToyDataflow/GenKill.lean):

```lean
/-- Copy bit 0 into both bits: distributive, but not of gen/kill form. -/
def copyBit0 (a : Fin 2 → Bool) : Fin 2 → Bool := fun _ => a 0
```

### Modeling bridges to real analyses

None of the following is kernel-checked. Each paragraph compares the model with one compiler source at a pinned commit; the quoted facts about the source were read directly from the file at that commit, and the comparison itself is reasoning.

**CompCert `backend/Kildall.v`** (repository `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`; last change to the file at commit `4710ec093ddea8e6eb86ad519df61c59b654e861`). Basis: derived (modeling bridge).

- Source facts: in module `Dataflow_Solver`, `Definition fixpoint` (line 300) starts from the entry point only (its start state, lines 296–298, maps the entry to the entry value and puts only the entry on the worklist), and `Theorem fixpoint_solution` (line 661) proves that every edge inequation holds under the hypothesis `forall n, L.eq (transf n L.bot) L.bot` (line 666); `Definition fixpoint_allnodes` (line 324) starts with every program point at `L.bot` and every node on the worklist (lines 319–322; the comment at lines 303–309 describes this variant as intended for backward analyses viewed as forward analyses on the reversed CFG), and `Theorem fixpoint_allnodes_solution` (line 697) proves the inequations without the strictness hypothesis; `Theorem fixpoint_nodeset_solution` (line 717) proves the inequations at program points reachable from a given seed set; iteration is fuel-bounded through `PrimIter.iterate` (line 287).
- Reasoning: `kildall` resembles the all-nodes variant in putting every node on the initial worklist (it additionally starts the entry at `init`), and `kildall_isSolution_of_eq_some` (solution property without strictness or monotonicity) is the analogue of `fixpoint_allnodes_solution`. CompCert's strictness hypothesis for entry-only seeding plays the role that `UnreachableStrict` plays here for exactness: `exactness_needs_unreachableStrict` shows that with all-nodes seeding a non-strict unreachable node can make the least solution differ from MOP at a reachable node. CompCert proves no least-solution or MOP statement, so `mfp-eq-mop-exactness` and `kildall-computes-mop` are not restatements of it.
- Not established: that CompCert's solver output coincides with `kildall`'s, or that CompCert's semilattice interface (with `L.eq` as equality) satisfies `Lat.IsJSL` for any particular abstract domain.

**rustc dataflow framework** (repository `rust-lang/rust`, commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`). Basis: derived (modeling bridge).

- Source facts: `compiler/rustc_mir_dataflow/src/framework/lattice.rs` lines 51–57 define `pub trait JoinSemiLattice: Eq { fn join(&mut self, other: &Self) -> bool; }`, and lines 74–78 implement it for `DenseBitSet` as set union (the powerset ordered by inclusion). In `compiler/rustc_mir_dataflow/src/framework/mod.rs`, `iterate_to_fixpoint` (line 288) starts every block's entry state at `bottom_value` and sets the start block with `initialize_start_block` (lines 298–300), processes blocks in reverse postorder with every reachable block initially dirty (comment at lines 307–323; `DenseBitSet::new_filled(rpo.len())` at line 346), and joins the propagated state into a successor's entry state, re-dirtying the successor when the join changes it (lines 370–373); the comment at lines 361–363 states that in a forward analysis any successor of a reachable block is reachable. In `compiler/rustc_mir_dataflow/src/framework/direction.rs`, the forward `apply_effects_in_block` applies `apply_call_return_effect` on call-return edges and `apply_switch_int_edge_effect` per `SwitchInt` target (lines 190–203).
- Reasoning: for a forward analysis without edge effects, block entry states updated by join-on-propagate correspond to the model's node-entry facts and edge inequations, and bit-set analyses whose block transfers are gen/kill fall under `gen-kill-distributive-and-exact`. Because only blocks reachable from the start block are processed, unreachable blocks contribute nothing, which is the entry-only seeding that this package does not formalize; call-return and `SwitchInt` edge effects are edge-specific transfers, which the model represents only through edge splitting; and termination rests on the domain, not on a fuel bound.
- Not established: distributivity, the ascending chain condition or exactness of any particular rustc analysis.

**LLVM sparse conditional constant propagation** (repository `llvm/llvm-project`, commit `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`). Basis: derived (modeling bridge).

- Source facts: `llvm/include/llvm/Analysis/ValueLattice.h` line 27 declares `class ValueLatticeElement`, whose states are `unknown`, `undef`, `constant`, `notconstant`, `constantrange`, `constantrange_including_undef` and `overdefined` (lines 34–76), merged by `mergeIn` (line 407). `llvm/lib/Transforms/Utils/SCCPSolver.cpp` tracks executable blocks (`BBExecutable`, line 572) and feasible edges (`KnownFeasibleEdges`, line 629; `markEdgeExecutable`, line 820; `isEdgeFeasible`, line 983).
- Reasoning: the solver keeps one lattice value per SSA value rather than a state per CFG node, and propagates only along edges it has marked feasible, so it does not compute the model's least solution over all syntactic paths. `constant-propagation-not-exact` is a statement about the model's unsmashed `cpLat` with whole-state joins, not about SCCP's output.
- Not established: whether SCCP loses precision on the SSA form of the diamond program of `constant-propagation-not-exact`.

## Boundaries

### Non-claims (per result)

**`mop-le-solution-soundness`**

- It does not say MFP equals MOP; equality can fail for monotone but non-distributive transfers (exactness_needs_distributive) and without the further side conditions of mfp-eq-mop-exactness.
- It does not assert that an MOP value exists: it is conditional on a least upper bound m of the path values (which exists under the ascending chain condition, exists_isMOPAt_of_acc).
- It does not assert that a solution or a least solution exists, nor that any algorithm computes one (see mfp-eq-mop-exactness for existence under the ascending chain condition and kildall-computes-mfp for an algorithm).
- Without monotonicity the bound fails even for the least solution (soundness_needs_monotone); without transitivity it fails even for a solution of a two-edge path (soundness_needs_leTrans).
- It does not establish semantic soundness with respect to any concrete operational semantics: `MOP ≤ x` only relates solutions of the abstract inequations to syntactic compositions of the given transfer functions `G.f`, without proving that `G.f` soundly abstracts concrete program execution.
- `MOP` ranges over all syntactically valid CFG walks `Walk G v`, including dynamically infeasible branch combinations; `MFP = MOP` therefore does not mean exactness with respect to feasible runtime executions (a join over only the feasible paths).
- `IsLeastSolution` specifies the least solution of the dataflow inequations (the least pre-fixpoint), which satisfies the dataflow equations with equality when transfer functions are monotone, but need not be a fixed point of the equations when monotonicity fails (for instance, `notCFG` has unique least inequation solution `(true, false)` while `x 0 = false ⊔ !x 0` has no fixed point). Lean: `isEquationSolution_of_isLeastSolution_of_monotone`, `notCFG_isLeastSolution_not_isEquationSolution`.
- `x v` and `IsMOPAt L G v` represent pre-transfer facts at node entry (`MFP◦` and `MOP◦`), because `G.f u` is applied only along outgoing edges `(u, w) ∈ G.edges`; at any sink or return node `v` with zero outgoing edges, `G.f v` is completely unconstrained and ignored unless a synthetic exit edge `(v, exit)` is added.
- It concerns a toy forward analysis on an explicit edge list with transfer functions applied on leaving a node; applying it to a real compiler analysis is a separate modeling argument.

**`mfp-eq-mop-exactness`**

- Reachability of v alone is not enough: exactness_needs_unreachableStrict has a reachable node where MFP ≠ MOP because an unreachable predecessor with a non-empty gen set feeds it (no cycle is involved).
- The unreachable-node condition is proved sufficient; it is not shown to be necessary. An unreachable non-strict node with no successors, or whose contribution is already present, plausibly does no harm (not proved here). No exact characterization of the unreachable-node condition is claimed.
- Not established here: a local form of the unreachable-node condition. The package does not prove that strictness is needed only at unreachable nodes from which `v` can be reached; `UnreachableStrict` constrains every unreachable node.
- Distributivity and the ascending chain condition are not replaceable by monotonicity alone or by 'every monotone map on a chain is distributive': exactness_needs_distributive has monotone, non-distributive transfers where MFP ≠ MOP, and exactness_needs_acc is a chain lattice without the ascending chain condition where MFP ≠ MOP.
- `AscendingChainCondition` (sufficient for `mfp-eq-mop-exactness`) is strictly weaker than uniform finite height `HeightLe h` (assumed by the uniform fuel bound in `kildall_isSome_of_heightLe`; under the ascending chain condition alone no uniform fuel bound exists, `kildall_acc_has_no_uniform_fuel`); neither theorem models widening (`∇`) or narrowing (`Δ`) operators used on infinite-height domains. Lean: `acc_strictly_weaker_than_heightLe`, `exactness_holds_on_unboundedChainsLat`, `kildall_acc_has_no_uniform_fuel`.
- It says nothing about how MFP is computed; termination and the fuel bound are in kildall-computes-mfp, and the end-to-end statement is kildall-computes-mop.
- The undecidability of MOP for general monotone frameworks (Kam-Ullman) and for constant propagation (Nielson-Nielson-Hankin) is not formalized here.
- It does not establish semantic soundness with respect to any concrete operational semantics: `MOP ≤ x` only relates solutions of the abstract inequations to syntactic compositions of the given transfer functions `G.f`, without proving that `G.f` soundly abstracts concrete program execution.
- `MOP` ranges over all syntactically valid CFG walks `Walk G v`, including dynamically infeasible branch combinations; `MFP = MOP` therefore does not mean exactness with respect to feasible runtime executions (a join over only the feasible paths).
- `x v` and `IsMOPAt L G v` represent pre-transfer facts at node entry (`MFP◦` and `MOP◦`), because `G.f u` is applied only along outgoing edges `(u, w) ∈ G.edges`; at any sink or return node `v` with zero outgoing edges, `G.f v` is completely unconstrained and ignored unless a synthetic exit edge `(v, exit)` is added.
- `CFG` applies a single node-indexed transfer `G.f u` along every outgoing edge of `u` and assumes a single entry node `G.entry` (`n ≥ 1`); branch-sensitive edge transfers `(u, w) ↦ f_{u,w}` and multi-entry graphs require edge-splitting or a synthetic super-entry node.

**`diamond-exactness-characterization`**

- Exactness on diamonds is not exactness on all CFGs: the characterization is for the specific five-node diamond shape. A family exact on all diamonds is not shown to be exact on CFGs with loops or with more than two merging paths.
- `DiamondExact L I F` does not imply `MFP = MOP` even on two-path acyclic CFGs (DAGs) with two sequential transfers per branch: for single-variable assignments `F = {y := 1, z := 2, y := 2, z := 1, x := y + z}` from `I = {⟨⊤, ⊤, ⊤⟩}`, every one-step diamond is exact, yet the seven-node two-path DAG executing `y := 1; z := 2` vs `y := 2; z := 1` before `x := y + z` has `MFP ≠ MOP` (`diamondExact_not_exact_on_two_step_branches`; this `F` is not closed under composition). No sufficient condition for exactness on larger CFGs (such as closure of `F` under composition and joins) is claimed.
- The entry transfer of the diamond is always id, even when id ∉ F; DiamondExact is not the same as exactness on diamonds all of whose transfers come from F (diamond_entry_id_matters gives a monotone family on 3-bit vectors for which the two notions differ).
- 'Distributive over all pairs' is sufficient but not necessary for diamond exactness: the one-element family {x := y + z} is exact on every diamond built from it although its member is not distributive (diamondExact_singleton_of_not_distributive).
- Without monotone members, diamond exactness can hold vacuously because the offending diamonds have no least solution (diamondExact_needs_monotone for direction (ii); diamondExact_const_mem_needs_monotone for the constant-closed corollary on a lattice without the ascending chain condition).
- `IsLeastSolution` specifies the least solution of the dataflow inequations (the least pre-fixpoint), which satisfies the dataflow equations with equality when transfer functions are monotone, but need not be a fixed point of the equations when monotonicity fails (for instance, `notCFG` has unique least inequation solution `(true, false)` while `x 0 = false ⊔ !x 0` has no fixed point). Lean: `isEquationSolution_of_isLeastSolution_of_monotone`, `notCFG_isLeastSolution_not_isEquationSolution`.

**`constant-propagation-not-exact`**

- It does not show that constant propagation is imprecise on every program; with identical branches the same analysis is exact (cpDiamond_sameBranches_exact).
- It does not show undecidability of MOP for constant propagation. That result is stated and proved in Nielson-Nielson-Hankin (Section 2.4.2; slide 81 of the authors' Chapter 2 transparencies) by encoding the Modified Post Correspondence Problem, and Reif and Lewis (POPL 1977) show that many natural global flow problems over integer arithmetic are unsolvable. Kam and Ullman (1977) state undecidability of MOP for monotone frameworks in general. None of these results is formalized here.
- `cpLat` is the unsmashed product `Flat³`, with a bottom in each variable; it is not the lattice `(Var → Z^⊤)_⊥` of Nielson-Nielson-Hankin, which adds a single bottom for unreachable code and makes assignment transfers strict. In `cpLat` constant assignments are not strict (`assignYZ_not_strict`), and because `⊥` is the identity of `Flat.join` (`Flat.join (.const c) .bot = .const c`), a variable whose entry value is unknown should be `.top` at the entry (as in the textbook entry value `λx.⊤`), not `.bot`. The theorems here hold for every entry state.
- Escape hatches that defeat this precision loss include: (a) relational abstract domains (such as affine equalities `y + z = 3`, octagons, or polyhedra) that preserve linear relationships across joins; (b) disjunctive (powerset) completion of `St`; and (c) restricting constant propagation to constant and copy assignments (`x := c` and `x := y`) without binary arithmetic transfers, which are distributive (`assignYZ_distributive`, `copyXY_distributive`). None of (a)-(c) is formalized here.
- The flat lattice uses strict abstract addition (⊥ + _ = ⊥) and no conditional-branch pruning; it does not model sparse conditional constant propagation or any specific compiler pass.
- All nodes of the diamond are reachable, so the example does not exercise the unreachable-node side condition of mfp-eq-mop-exactness.
- `MOP` ranges over all syntactically valid CFG walks `Walk G v`, including dynamically infeasible branch combinations; `MFP = MOP` therefore does not mean exactness with respect to feasible runtime executions (a join over only the feasible paths).
- `x v` and `IsMOPAt L G v` represent pre-transfer facts at node entry (`MFP◦` and `MOP◦`), because `G.f u` is applied only along outgoing edges `(u, w) ∈ G.edges`; at any sink or return node `v` with zero outgoing edges, `G.f v` is completely unconstrained and ignored unless a synthetic exit edge `(v, exit)` is added.

**`gen-kill-distributive-and-exact`**

- Gen/kill form is sufficient, not necessary, for distributivity: copyBit0 is distributive (copyBit0_distributive) but not gen/kill (copyBit0_not_genKill).
- The `gen = ∅` unreachable-node condition is specific to the union (`may`-analysis, `⊆`, bottom `∅`) orientation of `bvLat k`. For dual `must` bit-vector analyses ordered by `⊇` with intersection `∩` as join and the full set as bottom (such as available expressions), strictness at unreachable nodes flips to `kill \ gen = ∅` (empty net kill set), not `gen = ∅`. Lean: `bvMustLat`, `genKill_distributive_must`, `genKill_strict_must_iff`, `genKill_killOnly_strict_may_not_must`.
- It covers forward analyses on the given edge list; backward analyses (e.g. liveness) correspond to running it on the reversed CFG, which is not formalized here.
- Reachability of a node alone does not give exactness there when an unreachable node with non-empty gen feeds it (genKill_exactness_needs_unreachable_gen_empty).
- `MOP` ranges over all syntactically valid CFG walks `Walk G v`, including dynamically infeasible branch combinations; `MFP = MOP` therefore does not mean exactness with respect to feasible runtime executions (a join over only the feasible paths).
- `x v` and `IsMOPAt L G v` represent pre-transfer facts at node entry (`MFP◦` and `MOP◦`), because `G.f u` is applied only along outgoing edges `(u, w) ∈ G.edges`; at any sink or return node `v` with zero outgoing edges, `G.f v` is completely unconstrained and ignored unless a synthetic exit edge `(v, exit)` is added.

**`kildall-computes-mfp`**

- The fuel bound n * (h + 1) + 1 is attained for every n ≥ 1 and h ≥ 0 (kildall_fuel_bound_attained: n self-loops on a chain of height h), but it is a bound on worklist pops for this node-indexed solver, not an asymptotic complexity bound for efficient implementations.
- One unit of `fuel` in `kildall` pays for popping one node `u` and running `propagate` across all entries of `succs G u`; thus `fuel ≥ n * (h + 1) + 1` bounds outer worklist pops rather than individual edge propagations (`O(|G.edges|)` join and order checks per pop, including duplicate edges).
- The ascending chain condition alone gives no uniform fuel bound (kildall_acc_has_no_uniform_fuel), although it suffices for the existence of the least solution (exists_isLeastSolution_of_monotone_of_acc).
- All-nodes worklist seeding vs entry-only seeding trades global inequation satisfaction against unreachable-code isolation: seeding all nodes (`kildall`) guarantees a global `IsSolution` without strictness (even without monotonicity, `kildall_isSolution_of_eq_some`) but allows non-strict unreachable nodes to over-approximate reachable nodes (`exactness_needs_unreachableStrict`), whereas seeding only the entry avoids unreachable-node propagation and solves the reachable-subgraph inequations (as in CompCert's `fixpoint_nodeset_solution`) at the cost of violating inequations on edges out of unreachable nodes when transfers are non-strict (not proved here). Entry-only seeding is not formalized here.
- Without monotone transfers the solver can return a solution that is not least (kildall_needs_monotone); termination and the solution property do not need monotonicity.
- It says nothing about MOP; see kildall-computes-mop for the end-to-end statement under distributivity and the exactness side conditions.
- `IsLeastSolution` specifies the least solution of the dataflow inequations (the least pre-fixpoint), which satisfies the dataflow equations with equality when transfer functions are monotone, but need not be a fixed point of the equations when monotonicity fails (for instance, `notCFG` has unique least inequation solution `(true, false)` while `x 0 = false ⊔ !x 0` has no fixed point). Lean: `isEquationSolution_of_isLeastSolution_of_monotone`, `notCFG_isLeastSolution_not_isEquationSolution`.
- `AscendingChainCondition` (sufficient for `mfp-eq-mop-exactness`) is strictly weaker than uniform finite height `HeightLe h` (assumed by the uniform fuel bound in `kildall_isSome_of_heightLe`; under the ascending chain condition alone no uniform fuel bound exists, `kildall_acc_has_no_uniform_fuel`); neither theorem models widening (`∇`) or narrowing (`Δ`) operators used on infinite-height domains. Lean: `acc_strictly_weaker_than_heightLe`, `exactness_holds_on_unboundedChainsLat`, `kildall_acc_has_no_uniform_fuel`.
- It is a specification-level algorithm over lists and functions, not a verified efficient implementation.

**`kildall-computes-mop`**

- Finite height is assumed for termination; under the ascending chain condition alone MFP = MOP still holds (mfp-eq-mop-exactness) but no uniform fuel bound exists (kildall_acc_has_no_uniform_fuel).
- All-nodes worklist seeding vs entry-only seeding trades global inequation satisfaction against unreachable-code isolation: seeding all nodes (`kildall`) guarantees a global `IsSolution` without strictness (even without monotonicity, `kildall_isSolution_of_eq_some`) but allows non-strict unreachable nodes to over-approximate reachable nodes (`exactness_needs_unreachableStrict`), whereas seeding only the entry avoids unreachable-node propagation and solves the reachable-subgraph inequations (as in CompCert's `fixpoint_nodeset_solution`) at the cost of violating inequations on edges out of unreachable nodes when transfers are non-strict (not proved here). Entry-only seeding is not formalized here.
- One unit of `fuel` in `kildall` pays for popping one node `u` and running `propagate` across all entries of `succs G u`; thus `fuel ≥ n * (h + 1) + 1` bounds outer worklist pops rather than individual edge propagations (`O(|G.edges|)` join and order checks per pop, including duplicate edges).
- It does not establish semantic soundness with respect to any concrete operational semantics: `MOP ≤ x` only relates solutions of the abstract inequations to syntactic compositions of the given transfer functions `G.f`, without proving that `G.f` soundly abstracts concrete program execution.
- `MOP` ranges over all syntactically valid CFG walks `Walk G v`, including dynamically infeasible branch combinations; `MFP = MOP` therefore does not mean exactness with respect to feasible runtime executions (a join over only the feasible paths).
- `x v` and `IsMOPAt L G v` represent pre-transfer facts at node entry (`MFP◦` and `MOP◦`), because `G.f u` is applied only along outgoing edges `(u, w) ∈ G.edges`; at any sink or return node `v` with zero outgoing edges, `G.f v` is completely unconstrained and ignored unless a synthetic exit edge `(v, exit)` is added.
- `CFG` applies a single node-indexed transfer `G.f u` along every outgoing edge of `u` and assumes a single entry node `G.entry` (`n ≥ 1`); branch-sensitive edge transfers `(u, w) ↦ f_{u,w}` and multi-entry graphs require edge-splitting or a synthetic super-entry node.

**`reachable-node-not-exact-unreachable-gen`**

- It does not show that unreachable nodes always break exactness: when every unreachable node has a strict transfer, the least solution equals MOP (isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict); in this instance the MOP value at node 2 is ∅ (ugCFG_isMOPAt_two_empty). That a non-strict unreachable node without edges into the rest of the graph is also harmless is plausible but not proved here.
- Not established here: a local form of the unreachable-node condition. The package does not prove that strictness is needed only at unreachable nodes from which `v` can be reached; `UnreachableStrict` constrains every unreachable node.
- It does not involve a cycle; an unreachable cycle is not needed for the failure.
- It does not concern the computed fixpoint of a solver seeded only from the entry, which would not propagate from node 1 (not proved here; entry-only seeding is not formalized).
- All-nodes worklist seeding vs entry-only seeding trades global inequation satisfaction against unreachable-code isolation: seeding all nodes (`kildall`) guarantees a global `IsSolution` without strictness (even without monotonicity, `kildall_isSolution_of_eq_some`) but allows non-strict unreachable nodes to over-approximate reachable nodes (`exactness_needs_unreachableStrict`), whereas seeding only the entry avoids unreachable-node propagation and solves the reachable-subgraph inequations (as in CompCert's `fixpoint_nodeset_solution`) at the cost of violating inequations on edges out of unreachable nodes when transfers are non-strict (not proved here). Entry-only seeding is not formalized here.

**`exactness-needs-acc`**

- It does not show that infinite-height lattices always break exactness; ACC suffices, and lattices with ACC can have unbounded height (acc_strictly_weaker_than_heightLe, exactness_holds_on_unboundedChainsLat). A transfer that is continuous at the limit (here, mapping ω to ω) would not produce this gap (not proved here).
- A variant with all transfers strict is strict_exactness_needs_acc.
- It does not concern termination of a solver (non-termination on this lattice is not proved here; kildall_needs_heightLe proves that the solver returns none for every fuel on the successor self-loop succCFG over natMaxLat).
- `AscendingChainCondition` (sufficient for `mfp-eq-mop-exactness`) is strictly weaker than uniform finite height `HeightLe h` (assumed by the uniform fuel bound in `kildall_isSome_of_heightLe`; under the ascending chain condition alone no uniform fuel bound exists, `kildall_acc_has_no_uniform_fuel`); neither theorem models widening (`∇`) or narrowing (`Δ`) operators used on infinite-height domains. Lean: `acc_strictly_weaker_than_heightLe`, `exactness_holds_on_unboundedChainsLat`, `kildall_acc_has_no_uniform_fuel`.

### Escape hatches

- **`constant-propagation-not-exact`.** The precision loss disappears if every transfer is distributive and the side conditions of `mfp-eq-mop-exactness` hold (proved: `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`); the constant and copy assignment transfers are distributive (proved: `assignYZ_distributive`, `copyXY_distributive`); with identical branches the same analysis is exact (proved: `cpDiamond_sameBranches_exact`). Relational domains and disjunctive completion are further escape hatches (not formalized here).
- **`reachable-node-not-exact-unreachable-gen`.** The failure disappears when every unreachable node has a strict transfer (proved sufficient: `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`; for gen/kill transfers, empty gen sets at unreachable nodes: `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty`) or when every node is reachable (proved: `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable`). Seeding the solver only at the entry is a further escape hatch for the computed result (not formalized here).
- **`exactness-needs-acc`.** The gap disappears under the ascending chain condition (proved sufficient together with distributivity and strictness at unreachable nodes: `mfp-eq-mop-exactness`), which holds on lattices of unbounded height (proved: `acc_strictly_weaker_than_heightLe`). A transfer continuous at the limit is a further escape hatch (not proved here).
- For the positive theorems, the ledgers under Findings name, for each tight hypothesis, an instance where dropping that hypothesis alone defeats the conclusion.

### Tightness status

- Every hypothesis of every card is either `tight` (with a kernel-checked counterexample and a stated witness class) or `harmless`; no hypothesis has tightness `unknown`.
- `harmless` hypotheses: `hL : L.IsJSL` (the intended join-semilattice-with-bottom setting; no weakening is studied, and `harmless` does not mean that the laws can be dropped) and `[DecidableRel L.le]` (computational data; `kildall_decidableRel_irrelevant`).
- "Tight" always means: in the stated witness class there is an instance satisfying all other hypotheses of that theorem in which the conclusion fails. It does not mean that the hypothesis is necessary in every class of instances.

### Not examined or unknown

- **unknown:** a local form of the unreachable-node condition (strictness only at unreachable nodes from which `v` can be reached); considered, plausible, not proved.
- **unknown:** whether diamond exactness of a family closed under composition and joins implies exactness on larger CFGs; `diamondExact_not_exact_on_two_step_branches` shows that diamond exactness alone does not.
- **not examined:** entry-only worklist seeding; backward analyses on reversed CFGs; interprocedural analyses and valid paths; widening and narrowing; exactness with respect to feasible executions; undecidability of MOP (Kam and Ullman 1977; Nielson, Nielson and Hankin, Section 2.4.2); efficient solver implementations; any concrete compiler pass.

### Disproved or withdrawn statements

None. Every stated result is proved; no stated result was found false, and none was removed.

## Evidence

### Kernel-check record

- Toolchain: Lean 4 `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, resolved through the GitHub API on 2026-11-21). Core Lean only; no Mathlib; no Lake dependencies.
- On 2026-11-21, `lake build` of a fresh copy of `lean/` (Lake artifact cache disabled) succeeded; `Lean.collectAxioms` over all 764 non-internal declarations of the `ToyDataflow` library found no axiom outside `propext`, `Classical.choice`, `Quot.sound` (per-declaration record: `audit/axioms.json`); the Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe` declarations.
- Statement hash: SHA-256 of Lean's `repr` of the declaration's type. Closure hash: SHA-256 of the sorted lines `name : repr(type)` (followed by ` := repr(value)` unless the constant is a theorem) for every constant of the `ToyDataflow` library reachable from the statement, joined by newlines; theorem bodies are excluded, so proofs can change without changing either hash, but any change to a statement or to a definition it depends on changes them. Recorded in `audit/statements.json`.

| Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `assignXYZ_not_distributive` | main: constant-propagation-not-exact | propext | `cd15712e780e555096f22a283a70df1d77b77c6a745f8027eeae9c82913d6f55` | `a9ea9292d07ce00bd2fe219a74a7e2f792bde7f273eab8290d4d3838c2dd9b47` (24) |
| `cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3` | main: constant-propagation-not-exact | Quot.sound, propext | `77c83c0a7215e8ce770e52aa46948a1b943df66ec98e7766af20fb37f72cd906` | `8bf248fad33fd4e4a3cd32cf777b172e71b4c46bf9d3feeed6b290b2178e443d` (50) |
| `cpDiamond_mfp_x_top_ne_mop_x_const3` | main: constant-propagation-not-exact | Quot.sound, propext | `99209095dda24720a079fef1d9cf51f0f74539c2ab51ebe5bb98488b9ec223ef` | `8bf248fad33fd4e4a3cd32cf777b172e71b4c46bf9d3feeed6b290b2178e443d` (50) |
| `diamondExact_iff_distributiveOnRealizable_of_monotone` | main: diamond-exactness-characterization | Quot.sound, propext | `eecba70c180b95b5e4b641acfc6e1eb4d646218b1b284e60a0143cc9bd976819` | `7e50572f8f64b82fd4bf5cbb0ba601993c72b39dc65493b12e4e759557d784c2` (40) |
| `diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty` | main: diamond-exactness-characterization | Classical.choice, Quot.sound, propext | `5f1e7b0bfe90ebfcd768be99bdf408598ace5bc47783766c411bec13c8c88f81` | `3a0f3b49fe0116c9741ae12c64f81dc88ca7b076c8f65081478f294a3f6d56b5` (41) |
| `diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty` | main: diamond-exactness-characterization | Quot.sound, propext | `f4605bbccb895a62c23d3f56c716d464a94232996f41f6ece593ba5b88dbebac` | `74aa6579670d1286b2153c4f37bc5759d0cc16dd3613a090c344db762c915b9a` (40) |
| `diamondExact_of_distributiveOnRealizable` | main: diamond-exactness-characterization | Quot.sound, propext | `ba1ba5bf09db65fc5d806da5706aa0f3c8daf1f36aba302c4cfc9404ea6e332c` | `1c25fa166c4a63145b37bc6f3edf8e6be523500359efa904d19239b4424d3b5c` (39) |
| `distributiveOnRealizable_of_diamondExact_of_monotone` | main: diamond-exactness-characterization | Quot.sound, propext | `303940d3cf5c2090c9a0b0631d35d6177c12bde9fac6b2984d98d3e489260ef7` | `7e50572f8f64b82fd4bf5cbb0ba601993c72b39dc65493b12e4e759557d784c2` (40) |
| `exactness_needs_acc` | main: exactness-needs-acc | Classical.choice, Quot.sound, propext | `3e278176811c3a2137c44e64eb2bd952d21eb76a90016d1a53a129246352c5ce` | `e1a359bb8dbce205ddf20c8464a10c2458ff145fff6f219b6e1754b3cfa63845` (60) |
| `exactness_needs_unreachableStrict` | main: reachable-node-not-exact-unreachable-gen | Classical.choice, Quot.sound, propext | `b599264c42f70ab1e276524abbf124cf9bdde2dacecb26dc95d44cc1bdaaa87d` | `29ffb80d2c6a7ce54a84f7987667d13a8e0905eedd953d9ba752e42701a55ab8` (47) |
| `exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict` | main: mfp-eq-mop-exactness | Classical.choice, Quot.sound, propext | `4b3f958881ef1c331ba111ace1657fd2a219fa720a774c3d40002fa584df181f` | `0a75a7ccfc25334ebec11f37857fd168d5313a0023cd55683db44c54c77152c2` (40) |
| `exists_isLeastSolution_of_monotone_of_acc` | main: mfp-eq-mop-exactness | Classical.choice, Quot.sound, propext | `5f9ac64b724c184e44f4d5483b86aacf242d1cac1ec5f2122987a76afd3fa871` | `35d8459efa17512f5156c25b0cd3009ef6b65425c73a793beb0c6d4495e46c14` (23) |
| `genKill_distributive` | main: gen-kill-distributive-and-exact | Quot.sound | `2bbfff89a1c62a1d7507ca32a8f453c55587e5894b7ed5c89a2e97b2004f65c3` | `d4c8591b252490e3f36c54581ac63ea9e3f81eae52cbaa247354402ecc4fa158` (6) |
| `genKill_distributive_must` | main: gen-kill-distributive-and-exact | Quot.sound | `b5eaf6ed2f53479bfa6fadb1fed7b32108741f40a27830d93d1ebb2333fb2bb6` | `afbd2679394331194bb3105b4926a7ecd7f2dc0f5a17267dce3d0f9e5afba196` (6) |
| `genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty` | main: gen-kill-distributive-and-exact | Classical.choice, Quot.sound, propext | `c2c2f44c7564b5962eecd11a7616b052b29ae125082521a4f25de361962be67e` | `7ad14318386eb936f7412c4719cca48204da88126729206c67dce1cabb2c5bda` (29) |
| `genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty` | main: gen-kill-distributive-and-exact | Classical.choice, Quot.sound, propext | `5406457875e9ba0cf08327f1fe474cb68f197d72abb0635dea137c6dc57f5726` | `7ad14318386eb936f7412c4719cca48204da88126729206c67dce1cabb2c5bda` (29) |
| `genKill_strict_iff` | main: gen-kill-distributive-and-exact | (none) | `7ede1eb6e9f3b33111ac0c162226c9373c7139920bbfdb48a9d573a0abff54a8` | `06c6b2813d09bca6fd7fec344df87b0b2ad4b54d46ff258d53bb7c3aa58e1eca` (6) |
| `genKill_strict_must_iff` | main: gen-kill-distributive-and-exact | Quot.sound, propext | `1d24dace13056061d7429e9227264edc250d2ab6ba188ce59c1d85698c2772e1` | `61a719f4b5a07abdd19c4a52c2bed323918121c3800e66532ff31d31d737fef0` (6) |
| `isMOPAt_of_isLeastSolution_of_distributive_of_allReachable` | main: mfp-eq-mop-exactness | Classical.choice, Quot.sound, propext | `34bf47237c79b5d0ad61cd269adced53d07ffb3302cfebac875ebc9ed73b1ac3` | `8f5adc376abada1ca5b35467d8bf138ae6875b84291de786ed871d764b98dcf3` (40) |
| `isMOPAt_of_isLeastSolution_of_distributive_of_strict` | main: mfp-eq-mop-exactness | Classical.choice, Quot.sound, propext | `5411f772696fa73f429c57ae9150dba79634c9f9610ffb4c162938277d631c20` | `6d772f203e0c5dd2f4118cc54a7f7940d45bce8d7ee97679dd0b0b4a718c32eb` (39) |
| `isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict` | main: mfp-eq-mop-exactness | Classical.choice, Quot.sound, propext | `76d95eb94cd3fa252e1c1137dc878d2caf128f81afe423ab8e09deb3b2eb7279` | `0a75a7ccfc25334ebec11f37857fd168d5313a0023cd55683db44c54c77152c2` (40) |
| `kildall_eq_some_isLeastSolution_of_monotone_of_heightLe` | main: kildall-computes-mfp | Classical.choice, Quot.sound, propext | `9bc50c9f030729decc99973944f53e31d736068e07e9aa56592c8c1709a8d412` | `04c3d1d0bc9818614aa0686963d0ef240b6eca49b4fe40e52f60ea9e637e795f` (33) |
| `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe` | main: kildall-computes-mop | Classical.choice, Quot.sound, propext | `89b8e87149c3a5c67dda88118b1eb153ac1da52cc28d9c6e2bb6d5b7290259cc` | `5698c609d662d1a4658d9377a9e27c09d467e519aa666d686dc9b5ee0ed95e29` (50) |
| `kildall_isLeastSolution_of_monotone_of_eq_some` | main: kildall-computes-mfp | Classical.choice, Quot.sound, propext | `ea4fd91671db938f86e6b82f37a51a33c1249c88a483652aef90c8b88b70fc88` | `1bb72af78cf79a92c536ef757654048bb08c43d432f70e6adca3128f78d18c2c` (31) |
| `kildall_isSolution_of_eq_some` | main: kildall-computes-mfp | Classical.choice, Quot.sound, propext | `7e3d29140ddc5946c0dc6b3130489fc77b44c73148e913981325f2710cd90104` | `1ecba79abdeacf7d52e66a3d0e5409a125651f6fcf3fc862c5f817224955b9d9` (29) |
| `kildall_isSome_of_heightLe` | main: kildall-computes-mfp | Classical.choice, Quot.sound, propext | `4d3246f3e6455aa00d3fe62d1036b6897356aed6732dace589829014a8db854f` | `9b4884055def7ab554efdea090341ad6388e773af016a261495515e189904197` (30) |
| `mop_le_of_isSolution_of_monotone` | main: mop-le-solution-soundness | (none) | `77aaae32e6d0ad8de7bc74804d3db9279fa398a6ffe4d41c268b65dfb4546dfd` | `3fe6352cf884b3193028cb6eac3f38cdf6bdba24a3fb48235cdd38648945376f` (27) |
| `walk_val_le_of_isSolution_of_monotone` | main: mop-le-solution-soundness | (none) | `bf7ad11adf3606bb3dc05b123d3db64024eb46f2733f818dad5df6a046fa6033` | `a7a7b066a095a59ee3620a430e2d26e9d4cf7781cec24ab1e0355767e4bf5677` (23) |
| `Lat.acc_of_heightLe` | supporting | Classical.choice, Quot.sound, propext | `101c0b26a0906ca9961750b4d72cd00f306ad432d7ba4e36df4de894743c6f73` | `6893b53c969e347ee559f5ada89a856c9f8dd5e0e03e7ffdbf7d6a68d668704b` (6) |
| `acc_strictly_weaker_than_heightLe` | supporting | Classical.choice, Quot.sound, propext | `40e919095c66d65a50870b0ba8777e480d9e76248cb3da72fa52ff89a3ec7b8a` | `738cdf5b1edae727298301ea8266e2dfafda6b725f375ee74e5f01d981ece2c4` (31) |
| `assignXYZ_monotone` | supporting | propext | `1dfbcf810355925a47543392477634d867e86a33f63c3826a7e8177968c8dd70` | `d8d0492c7e62ddcf78c633d9295a22a98ec650765c8391390c1b1f0f605df7b6` (24) |
| `assignYZ_distributive` | supporting | propext | `b5c6dfef0016a313df443f9a0b410d1a84ef960a25e82afa03503be89ac1004f` | `fc3b2533cd64af5cfc41f82b71485da19d73f00244ca6e8750bcea93215c1252` (20) |
| `assignYZ_not_strict` | supporting | propext | `357b2e4119c2d58fa31687149ba74b5b78dfd34650ba212d009994db63065f04` | `691b3803ee2a3498dbf022fd393b0588674806b5885b992c6382564d7762830a` (20) |
| `cfg_empty_carrier_empty` | supporting | (none) | `62abd3b21b2eb40e4dcdd4aca72fbdbed1fe740b7975656f41076d664bafb741` | `69fbf1525732dfedfeae060302176db89ddb100c5438495fb1fefc5a1215e449` (2) |
| `cfg_zero_empty` | supporting | (none) | `8ce9f22e46fe5725606d0e5de758221d6d13c3c1bd1fb2f74cac0bf4b3408095` | `69fbf1525732dfedfeae060302176db89ddb100c5438495fb1fefc5a1215e449` (2) |
| `copyBit0_distributive` | supporting | propext | `b043133f79528b4346f12237734cb856e848a6f24a6c8da63401195618883656` | `b53907215b65c05d7a94867315f16f723da2f35046a3cd80242ebcac1ff2ed96` (7) |
| `copyBit0_not_genKill` | supporting | propext | `b8406b8a956896154d4fa961c114deb47c18859e634334ae358472726648185f` | `1cdf0b848c10160255cde494083d4a8798dc7d510655c76ebd946bdab7ce2a7f` (3) |
| `copyXY_distributive` | supporting | propext | `996c44443645df6c1920d276a0115c875aa9dfcbbfc52759b6fcbe4b4e473542` | `9113bc22df44fd98422f392d519cb67d9b5ec1f7f27e7804c26f78b714d7699b` (20) |
| `cpDiamond_isLeastSolution` | supporting | Quot.sound, propext | `171581a9f4429710b57c5a8d3e8b94a8f0a28f1fedb06dcc8a3c5f5fda7f9dab` | `58788ca5c30bde5678455e176af1bf5ae4675bec2f32179d511adaaaae339ffd` (37) |
| `cpDiamond_mfp_needs_least` | supporting | Quot.sound, propext | `d91416bda0b965dd22c7de983d91b3328e515ddd9b83f3d526a0ef0549a25281` | `8bf248fad33fd4e4a3cd32cf777b172e71b4c46bf9d3feeed6b290b2178e443d` (50) |
| `cpDiamond_sameBranches_exact` | supporting | Quot.sound, propext | `377a72b34c44dfc16fbeff88755f66055ae33e092e413a0fe1f28a6855847514` | `28f691309d7190411ea4e174833d2b1fd5f06a10ef359599f924d215af414505` (49) |
| `cyclic_exactness_on_unboundedChainsLat` | supporting | Classical.choice, Quot.sound, propext | `4c226c4db5023109a9819c5128e33e4cfcfc589bdb496087740d90412e7d7e41` | `fab3256be9b5589c2cff8f3b8b43674f1ddcbbf5c169c10b8a71679c87e21df8` (61) |
| `diamondExact_const_mem_needs_monotone` | supporting | Classical.choice, Quot.sound, propext | `936113403ce7bebefea0a70d20272ad36c5be7c1be94ac96911d956c914f4357` | `a90e19cde1ad3d2a6bf535f74227b4d8de0462c6d0dab2d3dc91356ee5dccb26` (55) |
| `diamondExact_const_mem_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `4c10127e743dadcbe8a22f161cdefe74a9c68ef73dcc43b6a3945ed372bd404a` | `51332d7e44c82ea93fca29551bfcbb026fccd511a46896a5b5cb86d9288df1a2` (67) |
| `diamondExact_const_needs_nonempty_init` | supporting | Classical.choice, Quot.sound, propext | `09485d6cfb01598678b7ffb775c4a429d378430bf493637a820b0daa2665714d` | `5a3d58cf23be85bc07a27fab07d739a250a6d8cbc210f3e17df328bf8cc34b0f` (62) |
| `diamondExact_iff_nonvacuous` | supporting | Quot.sound, propext | `1555ea365fcc6441f60ae87cb92fd7a5588df5f112901708899d1d0f8f4530f3` | `5f81cee132f0b9ceeb843fe50a9e4704a0d402f90b784b036a4042a2d3bc1a10` (63) |
| `diamondExact_needs_distributiveOnRealizable` | supporting | Quot.sound, propext | `07f23e771ca88ad3d42724f8659b024c462fd82dea0456d3cfd2b96305ef914e` | `c61fbceb27ba66f8ac7c1820b7384668c8a3a542a25cb8734242d960a0895d4f` (61) |
| `diamondExact_needs_monotone` | supporting | Quot.sound, propext | `461bad8356aad240a300f7e37bc4338c686a3451cf0fea44d8f9d579d3e3a9cd` | `a2cefeb3f82db40793abb768c58851e5e1e939c9e32215e88e555deaf75a719e` (42) |
| `diamondExact_not_exact_on_two_step_branches` | supporting | Classical.choice, Quot.sound, propext | `89fbf053c6bf23b4f6490eeba8dbc3ef66b2863aec05355fe63b66fb65ee06b7` | `d1d87ec363622e09ca3ac381acf642e3bfa01bed7ec5ee0208e49d289cd34679` (67) |
| `diamondExact_singleton_of_not_distributive` | supporting | Classical.choice, Quot.sound, propext | `bca5dfd59deda938ba484819e263da5c864c4b11430e3e8895b4020a25473533` | `5a3d58cf23be85bc07a27fab07d739a250a6d8cbc210f3e17df328bf8cc34b0f` (62) |
| `diamond_entry_id_matters` | supporting | Classical.choice, Quot.sound, propext | `4aebf16513ba9c55d63a7499a9b8dd4b3a8cef4b488b03f41ece191f8dbe4bd9` | `4abf2dd5f89797f2706d634e88cebf6d6d4d726b971676d6cf62af430f9ab781` (38) |
| `distributive_of_monotone_of_total` | supporting | (none) | `d31980b50ce00fe5dd02a96e7ce1b628b7ff797523de05fe89b1b11cf671909e` | `ab7a998bedc612f0fbfcd00ea2334bc667f405787e9da605f00615e2aed311f3` (14) |
| `exactness_corollaries_combined_counterexample` | supporting | Classical.choice, Quot.sound, propext | `bf922dc87b66e299ec29686b14d9672c003996882e656c6c54adee66838df459` | `b0c10d29fe51411a14ca93ca11b085411dccfcdeb6b67b8d9a6be403a0220598` (48) |
| `exactness_corollaries_need_allReachable_or_strict` | supporting | Classical.choice, Quot.sound, propext | `f6713425fe0ee29648064b1672cda1593660140cd7684d14685a7fd5a8438e4d` | `c8e247cfbb59f46723f0d1fad5fb668e1c76973df18090ebfe9ce09c31a10824` (37) |
| `exactness_holds_on_unboundedChainsLat` | supporting | Classical.choice, Quot.sound, propext | `a044f419eef61751a864adf1f660a5e9344a1dc92bcb4fb7c41ba1a75b72a211` | `814680f29e14b681e2f4fbb27b8414d7262673be3f07fa4ded5fc6f50387c7b2` (47) |
| `exactness_needs_distributive` | supporting | Classical.choice, Quot.sound, propext | `9374b856766782d7c1318033c9bb0715fdd97cb099eacd0f742c07e85ba48999` | `fc7e489d3258399be30b8f798d91d19e22ffb0d40ad317b179db786285d9cfec` (67) |
| `exactness_needs_least` | supporting | Classical.choice, Quot.sound, propext | `48c43300b18d0871e61635b832126023baf378fc76bc92bf87c54d15b854ec4a` | `117eb3facdab3da2ad7ef30661ae648f6bd42da895cab583ebf9678fcdae3fbd` (47) |
| `exactness_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `77b8e0bbc9382cce298c8ad03b27dc14aa854a80a5ed6510cb75ba96d49c2efd` | `c6ce2a1985ac249a76daf2f9e123e19a7417a26ec68bc1e2e3a7b2d45b23b39c` (36) |
| `exists_exactness_combined_counterexamples` | supporting | Classical.choice, Quot.sound, propext | `7052a632b35e9b995ab5d5d86307e7938cd647198aed9f2cf56d5594907ec401` | `6269b6cf2c8f75354e14a6fbb3d51f87eccc62f1a64656a5da7873355c14f3f4` (88) |
| `exists_exactness_counterexamples` | supporting | Classical.choice, Quot.sound, propext | `5de5a1eca93b155c5d1bfd01a2dec51fa5d13fe6a1b9d7ecfa0fb26e1151cc0e` | `53418b1fca5dc417bff1d329b8593815c1e9121994402d230b18e3cc72147488` (77) |
| `exists_isLeastSolution_counterexamples` | supporting | Classical.choice, Quot.sound, propext | `0890e0d7c8c2f50198d7e97fe33301bb5c373d2070c516b0b85ef30a38dbeb6d` | `7d675a5d12439bff07d99b9f18be9b55f772796be4d436fbb604a5dd766a853e` (29) |
| `exists_isMOPAt_of_acc` | supporting | Classical.choice, Quot.sound, propext | `f6ec422bcd1f7f588aaa1ee42b2dc4ad5dfcb18cce4b2062cb58d1fcc1d2d0c4` | `4ea980e58663e4ac9898d1f2f9a0d0332ab181d7e30031fd37b4429673f8ee8d` (35) |
| `genKill_exactness_needs_genKill_form` | supporting | Quot.sound, propext | `a92abee12f2ee064f71e385abed6a6c3bbc92245fd2a3e97bfbd148efc26937d` | `e379b551c019f9f779a69303acac5fb90cefff158524dc7b53e05e568ef3189e` (48) |
| `genKill_exactness_needs_unreachable_gen_empty` | supporting | Classical.choice, Quot.sound, propext | `a620028a9ff93a4bba36c4d9332c74cb16094e0152685ff440a4e6021d7ee1ed` | `5c2bc08ce12acf87030973f3759940d3c622d77d71ed2344966cd3d8eb4efd25` (34) |
| `genKill_exactness_nonvacuous` | supporting | propext | `b9a558e49f82a4a006972a64814a9c4a8cee1373df4b4364c186683b2c482b72` | `281961e2b6c30608884d3b596d8f9e16496e5e15b3b186ce4ccf48f76fef03d0` (22) |
| `genKill_exists_exactness_combined_counterexamples` | supporting | Classical.choice, Quot.sound, propext | `9ac68d305df694dd3128e3797eecfd2cf2af457e57ecdc22407b15099a3a8cf1` | `036ad1697c22299b076edc20cdf8b4936c2ec6ae2d4a8c0dac18216546cb62f0` (39) |
| `genKill_killOnly_strict_may_not_must` | supporting | Quot.sound, propext | `2b02adb0abda6b007e9071d9fbe8978e4e2531fc96ce15d3b1bf0390275e30b2` | `14dec96e788582d782c159bdbfbef36309ff93bdcdf549a1f3df42668e64f7b4` (7) |
| `genKill_must_strict_nonempty_kill_nonvacuous` | supporting | Quot.sound, propext | `274d8c998a7cc8a67ee3ce302d19239ce56bc26255af26b19b3b7ec155a063b9` | `ea2f80b01465325726cf729b155f05fad97a4e41d0d1ff441e38b888eef8b5d7` (8) |
| `isEquationSolution_of_isLeastSolution_of_monotone` | supporting | Quot.sound, propext | `1ad9f75ebb721e48162a3b999f59158a2fb3d19915c7e25bb7a99910b09d08e1` | `29d8e2619b7b874124aea834ea294f236ed00647747f6af0e2c3d6c4abd4fc93` (26) |
| `kildall_acc_has_no_uniform_fuel` | supporting | Classical.choice, Quot.sound, propext | `920acced5d9f22533c5db95cb07d9fcbaa51de7962ae6a9ee686b832ce290d0c` | `9255dd2b6dc3519bd099b04b3c66fe73376657ae753c791f32fcb10c9ec0c230` (50) |
| `kildall_decidableRel_irrelevant` | supporting | Quot.sound | `a62fc33a4363ed30bd49cacb9e3c7453b4f781622efe40c760b5bd80090c8d70` | `67015ca26737015cc9c492093ab3d5e4f6bef42b15af6e0e9a9c083696194a5c` (21) |
| `kildall_fuel_bound_attained` | supporting | Classical.choice, Quot.sound, propext | `c179e5c20b378fe00ed8c31ede1ad7d6cb74a45cdaf185f6e2e55ed7bb18e8c3` | `136f8a766a5d512778d1b8368fb280a82e1138ddffd0b6d60758e5fddb1b6eb7` (37) |
| `kildall_isMOPAt_counterexamples` | supporting | Classical.choice, Quot.sound, propext | `0d3ec83735ef84410e9127ef53fee22acfb08f13e00a6c01987b9f31a2892a1e` | `bedfa07cb4b17aa3375154ad041870bf66d894a7fae7dcd53bb6820234b03a75` (108) |
| `kildall_isMOPAt_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `b692f7636bd0cf68679189d1556be62f5245d62c386a7b8e779d4dbc72ab19a7` | `3811228202e4d0cd8afe69f866b6f9905a7fc49f34b8ea7748d888eeae6930bf` (58) |
| `kildall_needs_eq_some` | supporting | Classical.choice, Quot.sound, propext | `91f79e4fb24377bf7aad079bea8e1fbb5c3a3571f1b9e248235ffe7952654d64` | `f61dba05fcb937ed79bae169af681c11b6ac772d92f4fa924091bbf4a080e8cd` (39) |
| `kildall_needs_heightLe` | supporting | Quot.sound, propext | `0ec14b210b912ff6f153789dc070eab837cda34e88eb7340201e05fffef9d17d` | `c01de3b235a4e025087239baac087daa4a943a21fed8e9fac40483286d7fb1b2` (42) |
| `kildall_needs_monotone` | supporting | Classical.choice, Quot.sound, propext | `fa80baf7e0dc3ad537231168f5cd43e957ef8647acad42facdc97938cd200a09` | `2869c31c300800533e0751d985688a770f2e5a7dd30965a83b642fe1e28543e5` (38) |
| `kildall_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `124b977ff17e80d8281edca6a455475a98e655669c8663a0e7b9ce902ba2485a` | `34f06e1d85c11db640cf5c6973ed5e87d129ae82c34f28433294edc3a0f96940` (39) |
| `monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty` | supporting | Classical.choice, Quot.sound, propext | `b02a35fdd1997cd49527926f468aded5b921ee6c433560521e6179dcc10a4aa5` | `83b782ef12bf70486f00d5a1cb0a641406c9f64f1a4b788f94764a44104ee4a4` (41) |
| `monotone_of_distributive` | supporting | (none) | `017e864d1a10e435eaba4e0c6127ec249a87d79676657e7f434e26107c3973c4` | `ab7a998bedc612f0fbfcd00ea2334bc667f405787e9da605f00615e2aed311f3` (14) |
| `notCFG_isLeastSolution_not_isEquationSolution` | supporting | propext | `b9e07acc5da06c969f5da020fff8a82db78b68d8c8d4f7e68c783dba7a7e153a` | `d987bc11f1c3754be0952db9ed10100c0e87800a093e39f1e7273e66aa692c66` (22) |
| `omegaLat_monotone_distributive` | supporting | Quot.sound, propext | `a9932432d5dc6fec7adb7ae9bc4ed52bfb6bda4ba4b970e0bbb680bb71089994` | `ec58ef01c11a77a3dbde55aad8db50525f1d3485c79b8bfe720dfb960ef7c928` (20) |
| `omegaLat_total` | supporting | Quot.sound, propext | `f1f540e77d8227a253f90f6e3bfc886fb4ed3301850d7db84a7f63f5fd0cedeb` | `0459fc7821fd76612a22d56124a0adf47bef9fb98e1dd5c977d3edd528746e26` (17) |
| `soundness_needs_isMOPAt` | supporting | Classical.choice, Quot.sound, propext | `4922ec2b971e7a68911c69138f2a8ce8bea9232e683829b43146dc830059c68a` | `d8a79e07f8a75707ecd8749d11fa44d9d3882e3ef3911809b8a80a35669e93ac` (34) |
| `soundness_needs_leTrans` | supporting | Quot.sound, propext | `679ba3823f44f3242bea97363173f0110c3e9e1456b00abfcd99d25244912363` | `fdd54f5fc299c59ef8b58a45aea5fafa2107bde3d10c44a9af1aa443004f1b68` (31) |
| `soundness_needs_monotone` | supporting | propext | `e5aa82fe018ca4f62d14917470d029742a0e950948269e5f401b0d974f2bb5ce` | `933d0dbaf6ef88946b5ae5ce50f39787cc84d96d2a03bd4bceeb3250a408bd7c` (32) |
| `soundness_needs_solution` | supporting | Classical.choice, Quot.sound, propext | `ad57fb4ed32fc67afa0b327daab761e94a9231d083abcce06a724776a964e94b` | `d8a79e07f8a75707ecd8749d11fa44d9d3882e3ef3911809b8a80a35669e93ac` (34) |
| `soundness_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `37829b314cd7e370e10a6a529955439e00ba80e77b0e1b107db74003c99d2322` | `d8a79e07f8a75707ecd8749d11fa44d9d3882e3ef3911809b8a80a35669e93ac` (34) |
| `stepMid_distributive` | supporting | Classical.choice, Quot.sound, propext | `53ddf43691b9a2c275e103336203f2cbd751f89e4560b372dcd1b2afde2a8637` | `1d5f9a532d722bfc91e8e8575be87b57f03433f2ed866892bf6b516f9578c2b4` (22) |
| `strict_and_genKill_exactness_needs_least` | supporting | Classical.choice, Quot.sound, propext | `9942e47f1257d8df21e35b87db2fd10469e7af4e1c6b9d5f58f40565f5f6fc8d` | `c1dffe61d4177d583222d30cddf917dfe28b6df76a2f824d7b2a301490465ea2` (43) |
| `strict_exactness_needs_acc` | supporting | Classical.choice, Quot.sound, propext | `95a4ed477c9404f96abfe9549317b4bd069b06ef362980b56c3272f05ebb6804` | `7c3f5a879da3a34a2becff8f554dd36b08411e03d70161d25d59621a85a01cac` (60) |
| `strict_exactness_needs_distributive` | supporting | Classical.choice, Quot.sound, propext | `fd228f5f1a51107938c159293f08e96bcb202deeead925615cc6b242b73353e5` | `9c52c198eaee7fe14aa9ee3cecca5f410d86e8c09ad4c39b3ec22e0b4fc9acf3` (52) |
| `strict_exactness_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `5d0b3f3417588107bab75f4239910e4cd4ac70985bd15d75697bac3c9265d765` | `50dc449161b7d9734e8c9cb44308114af04488c07cb531d1cccad4ee655ab192` (34) |
| `ugCFG_isMOPAt_two_empty` | supporting | Quot.sound, propext | `62916cc927c674c0b2909393a18a136a5520ea8d17dff1d1bede4b4b7386d1d1` | `f7b84c9d77ae2379d56fddc2f25b1ddb76987c7dcb9e86775e3b32eae1306a46` (30) |
| `unreachableStrict_strictly_between_nonvacuous` | supporting | Classical.choice, Quot.sound, propext | `95d0df567581f2578cf508f56ab018ca5a7bfcd7ed4edfeb088f567663cea2f9` | `11463b2eb023759699e6d5de8f2bfe6142fd9747d51e195f12c4617d02f4bdb3` (35) |

### Primary sources

Bibliographic records were checked against Crossref DOI metadata on 2026-11-21; the repository commits and file paths were resolved through the GitHub API and read at the stated commits on 2026-11-21.

- G. A. Kildall, "A unified approach to global program optimization", Conference Record of the ACM Symposium on Principles of Programming Languages (POPL 1973), pp. 194–206, doi:10.1145/512927.512945 (public-domain archival copy: handle 10945/42162).
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", Acta Informatica 7(3):305–317, 1977, doi:10.1007/BF00290339.
- F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer, 1999 (corrected 2nd printing 2005), doi:10.1007/978-3-662-03811-6, ISBN 978-3-540-65410-0; Chapter 2 and the authors' Chapter 2 transparencies (May 2005), slides 67–72, 79 and 81 as cited in the cards.
- J. H. Reif and H. R. Lewis, "Symbolic evaluation and the global value graph", POPL 1977, pp. 104–118, doi:10.1145/512950.512961.
- T. J. Marlowe and B. G. Ryder, "Properties of data flow frameworks: a unified model", Acta Informatica 28(2):121–163, 1990, doi:10.1007/BF01237234.
- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002, doi:10.1017/CBO9780511809088, Chapter 8.
- P. Cousot and R. Cousot, "Constructive versions of Tarski's fixed point theorems", Pacific Journal of Mathematics 82(1):43–57, 1979, doi:10.2140/pjm.1979.82.43.
- Y. Bertot, B. Grégoire and X. Leroy, "A structured approach to proving compiler optimizations based on dataflow analysis", TYPES 2004, LNCS 3839, pp. 66–81, Springer, 2006, doi:10.1007/11617990_5.
- S. Coupet-Grimal and W. Delobel, "A Uniform and Certified Approach for Two Static Analyses", TYPES 2004, LNCS 3839, pp. 115–137, Springer, 2006, doi:10.1007/11617990_8; Coq development `rocq-archive/kildall` at commit `87422e1815e22a3f4821b29a1fd7a7f385667b91` (`kildall/kildall_dfa.v` line 125: `Theorem monotone_step_imp_kildall_dfa`; `kildall/dfa.v` line 39: `Definition Is_data_flow_analyser`).
- D. Cachera, T. Jensen, D. Pichardie and V. Rusu, "Extracting a data flow analyser in constructive logic", Theoretical Computer Science 342(1):56–78, 2005, doi:10.1016/j.tcs.2005.06.004.
- G. Klein and T. Nipkow, "Verified bytecode verifiers", Theoretical Computer Science 298(3):583–626, 2003, doi:10.1016/S0304-3975(02)00869-1.
- A. Lochbihler, "Jinja with Threads", Archive of Formal Proofs, December 2007, https://www.isa-afp.org/entries/JinjaThreads.html (theory `JinjaThreads/DFA/Kildall.thy`, lemmas `kildall_properties` and `iter_properties`, as cited in `kildall-computes-mfp`).

### Compiler sources read for the modeling bridges

- `AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`, `backend/Kildall.v`: lines 287, 296–335, 661–666, 697, 717.
- `rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`: `compiler/rustc_mir_dataflow/src/framework/lattice.rs` lines 51–57 and 74–78; `compiler/rustc_mir_dataflow/src/framework/mod.rs` lines 288–380; `compiler/rustc_mir_dataflow/src/framework/direction.rs` lines 153–205.
- `llvm/llvm-project` at `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`: `llvm/include/llvm/Analysis/ValueLattice.h` lines 27–76 and 407; `llvm/lib/Transforms/Utils/SCCPSolver.cpp` lines 572, 629, 820, 983.

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3`. Nothing else is needed; the commands below do not modify the package.

**Primary check**, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, runs `lake build`, rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration, checks with `Lean.collectAxioms` that every declaration of the library depends only on `propext`, `Classical.choice` and `Quot.sound`, and recomputes, for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, the statement hash and the closure hash defined under Evidence, comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 exactly when all checks pass.

**Equivalent manual check** with the package-included audit program `lean/RevalidationAudit.lean` (outside the library target; it prints the axioms, the pretty-printed signature and the statement and closure text of every card-referenced name and of the definition-adequacy theorems):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/revalidation_audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
rec = json.load(open("audit/statements.json"))["statements"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
ok, seen = True, set()
for line in open("/tmp/revalidation_audit.txt", encoding="utf-8"):
    if line.startswith("MISSING "):
        ok = False; print(line.strip())
    elif line.startswith("AXIOMS "):
        name, axs = re.match(r"AXIOMS (\S+) \[(.*)\]", line).groups()
        bad = {a.strip() for a in axs.split(",") if a.strip()} - allowed
        if bad:
            ok = False; print("axioms", name, sorted(bad))
    elif line.startswith("STATEMENT_JSON "):
        s = json.loads(line[len("STATEMENT_JSON "):])
        if s["name"] not in rec:
            continue
        got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
               "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
               "closure_size": len(s["closure"])}
        seen.add(s["name"])
        if got != rec[s["name"]]:
            ok = False; print("hash mismatch", s["name"])
print("recorded names checked:", len(seen), "of", len(rec))
print("OK" if ok and seen == set(rec) else "FAILED")
EOF
```

This manual check covers the axioms of the printed names only; the package-wide axiom audit over every declaration is part of `support/revalidate.py`.

**What a passing run establishes.** That the theorems still type-check in the Lean kernel under the pinned toolchain with only the three standard axioms, and that no recorded statement or definition it depends on has changed. It does not re-check the prior-art citations or the modeling bridges; to revalidate a bridge, re-read the cited lines of the compiler source at the stated commit (or at a newer commit, with the expectation that line numbers and code move). Under a different Lean version, `repr` output can change even when the mathematics does not, so a hash mismatch after a toolchain change calls for re-reading the affected statements rather than implying a semantic change.
