# Lean 4 Separation Logics, `iris-lean`, and `ChoiceKind` Adequacy

## Summary

`leanprover-community/iris-lean` (at tag `v4.34.1`, commit
`04b7689c294bb1dd6401e2dd53b337871934ea47`, and `main` commit
`fb21a8af4727bd42190072a5ed2836cbe9fb844e`) is the only general-purpose,
higher-order impredicative separation logic in Lean 4 with a complete algebraic
hierarchy (ordered family of equivalences `OFE`/`COFE`, cameras `CMRA`,
resource algebras `UPred M`, recursive domain equation solution `IProp GF`,
basic updates `BUpd`, step-indexed fancy updates `FUpd`, invariants `Inv`,
ghost maps `GhostMapG`, and ghost variables `GhostVarG`) and a tactic-level
Interactive Proof Mode (`iintro`, `iframe`, `isplitl`, `isplitr`, `iapply`,
`ihave`, `imod`). However, `iris-lean` is purely an algebraic and logical
framework: it ships no generic operational language interface (`Language`
structure), no generic weakest-precondition definition (`wp`), and no generic
operational adequacy theorem connecting `IProp GF` to small-step machine
executions.

This report establishes five results across the Lean 4 separation-logic and
program-logic ecosystem and Anneal's trusted small-step operational kernel
(`Trusted/StepResult.lean`, `Trusted/Refinement.lean`, `Trusted/Memory.lean`,
and `Trusted/MirSemantics.lean`):

1. **Architecture of `iris-lean` (`04b7689` / `fb21a8a`):** `iris-lean` builds
   its assertion logic in three layers: the syntactic/axiomatic `BIBase`/`BI`
   hierarchy (`Iris/BI/`), the uniform step-indexed predicate camera
   `UPred (M : UCMRA)` (`Iris/Instances/UPred/Instance.lean`), and the bundled
   recursive domain solution `IProp (GF : BundledGFunctors)`
   (`UPred (IResUR GF)` in `Iris/Algebra/IProp.lean`). Fancy updates
   `|={E1,E2}=> P` are defined in
   `Iris/Instances/Lib/FUpd.lean` via explicit world satisfaction
   (`WorldSatisfaction`), invariant pools (`InvPool`), mask tokens
   (`MaskToken`), and later credits (`LaterCredits`), and closed into pure
   Lean `Prop` via `Iris.step_fupdN_soundness_close` and `UPred.pure_soundness`
   with zero `sorry` and only Lean's standard axioms
   `[propext, Classical.choice, Quot.sound]`.
2. **Ecosystem Comparison Across Seven Lean 4 Frameworks:** A source-level
   comparison of `verse-lab/velvet` (`836ed5a`), `verse-lab/loom` (`78928ab`),
   `verse-lab/veil` (`eb458cb`), `verse-lab/splean` (`e24286f`),
   `verse-lab/Lentil` (`b3ca5e2`), `goens/lean-hoare` (`aa2d88a`),
   `leanprover/cslib` (`82db31e`), and `alexkeizer/QpfTypes` (`5b5dd4f`) shows
   that none of the non-Iris frameworks can serve as Anneal's primary Rust/MIR
   separation logic without either trusting an external SMT solver (`veil`),
   restricting to deterministic heap-allocated imperative references (`splean`),
   requiring complete lattice step-indexing incompatible with `IProp`'s step-
   indexed `OFE` (`loom`/`velvet`), or hitting syntactic macro limitations on
   indexed interaction trees (`QpfTypes`).
3. **Two-Tier Step-Indexed Weakest Preconditions and Adequacy to Anneal's
   `SpecOn`:** Because Anneal's trusted boundary (`Trusted.BehaviorOf` and
   `Language.SpecOn`) is parameterized over fuel-bounded finite prefixes
   `q : ExecQuery State` (`ReachesPrefix M p q.init q.steps q.init tr out`)
   and pure `Prop` refinement (`L.Sem p ≤ L.SpecOn pre post`), neither `BI` nor
   `IProp GF` belongs inside `trusted/lean/`. Instead, `theory/` can provide two
   complementary, sound weakest-precondition layers that discharge into
   `Trusted.BehaviorOf M p ≤ M.toLanguage.SpecOn pre post`:
   - A lightweight, zero-dependency, fuel-indexed `Prop` separation logic
     (`wpAt` over `ResourceAlgebra`, verified in
     `support/anneal_step_wp_and_choicekind_probe.lean` with only `[propext]`),
   - A full `iris-lean` `IProp AnnealGF` + `FUpd` weakest precondition
     (`wpIProp` using `|={⊤}[∅]▷=>`, `GhostMapG` spatial points-to
     `loc ↦ₘ[γh]{dq} v` tied to `Trusted.MemState` coherence views via
     `OwnLocInMem`, and `GhostVarG` state ownership, verified in
     `support/R2IrisLeanProbe.lean` on `idCopyBody` and `writeRead42Body` with
     only `[propext, Classical.choice, Quot.sound]`).
4. **Empirical `iris-lean` IPM Framing Scaling Laws ($N = 5, 10, 20, 40$):**
   Controlled benchmarks in `support/R2IrisLeanProbe.lean` across $N \in \{5,
   10, 20, 40\}$ spatial points-to hypotheses establish that `iframe`
   elaboration cost scales linearly at $\approx 50,665$ heartbeats per spatial
   hypothesis regardless of ordering, whereas kernel proof-term DAG size
   (`Expr.numObjs`) is **quadratic** ($\text{numObjs}(N) = 5N^2 + 33N + 314$,
   reaching $9,214$ nodes at $N = 40$) when `iframe` removes hypotheses left-to-
   right from a right-associated `Hyps.mkSep` spine, and **strictly linear**
   ($\text{numObjs}(N) = 79N + 165$, or $3,325$ nodes at $N = 40$—a $2.77\times$
   reduction) when hypotheses are framed right-to-left. By contrast, functional
   local lookup on `MirState.locals` (`rfl` over `Trusted.updateLocal`) takes
   $1,826$ heartbeats per local and produces a constant **24-node, depth-7**
   proof term at every $N$, confirming that stack-only MIR locals must remain
   in functional `MirState.locals` maps while `IProp AnnealGF` spatial
   points-to assertions are reserved for dereferenced pointers, mutable/shared
   references, and atomics.
5. **Audit and Two-Stage Resolution of `ChoiceKind.angelic` in
   `Trusted/StepResult.lean`:** In Anneal's current `Trusted/StepResult.lean`,
   `ReachesPrefix.choice` and `ReachesPrefix.emptyChoice` accept
   `(kind : ChoiceKind)` as an unconstrained free variable and never inspect
   whether `kind = .demonic` or `kind = .angelic`. Combined with the universal
   quantification over all reachable prefixes in `BehaviorOf.defined`, any
   `.choice .angelic` transition that includes even one failing branch causes
   the entire program execution to be undefined (`defined = False`, i.e.,
   `Partial.ub`), even when a safe terminating angelic witness exists
   (`optionB_angelic_trap_is_ub`). We mechanize a two-stage resolution:
   - **Stage 1 (Option A — Immediate Cleanup):** Delete `ChoiceKind` from
     `Trusted/StepResult.lean` so `.choice (branches : State → Prop)` is
     unambiguously demonic (`reachesPrefixA_iff_reachesPrefix`).
   - **Stage 2 (Option C — Two-Player Game / Skolemized Strategy Semantics):**
     When angelic nondeterminism is needed for relational/refinement or FFI
     witness specifications, define dual game semantics (`GameHolds` /
     `GameBehaviorOf` and the Skolemized `ReachesWithStrategy` /
     `StrategyBehaviorOf`), which quantify existentially over an angelic
     strategy $\sigma : \text{Nat} \to \text{State} \to \text{State}$ outside
     universal demonic path reachability and compose directly with
     `Iris.step_fupdN_soundness_close`.

## Applicability

The findings in this report apply to the concrete repository revisions and
preserved Lean 4 artifacts listed in `REPORT.json` and
`support/source-manifest.json`:

- **`leanprover-community/iris-lean`:** Examined at tag `v4.34.1` (commit
  `04b7689c294bb1dd6401e2dd53b337871934ea47`, tree
  `1282d7d5b1405ae3db38efe58c04c2261dc31f1f`, toolchain
  `leanprover/lean4:v4.34.1`) for direct execution compatibility with Anneal's
  `trusted/lean` toolchain, and at `main` HEAD (commit
  `fb21a8af4727bd42190072a5ed2836cbe9fb844e`, tree
  `4912bf34c2e7f40635ecad94671ebc0af64f3c55`, toolchain
  `leanprover/lean4:v4.35.0`) for recent upstream additions (`IrisStepIndex`).
- **Lean 4 Program-Logic and Behavioral Libraries:** Examined by direct source
  inspection at pinned commits:
  - `verse-lab/velvet` at `836ed5a163b36c09081ed1d8aeecd3cec040f87e`
    (`leanprover/lean4:v4.35.0`),
  - `verse-lab/loom` at `78928abc9054b31d0bea85985496490baae95244`
    (`leanprover/lean4:v4.24.0`, cross-referenced with `7f53c15`),
  - `verse-lab/veil` at `eb458cb602d3cf9a19d8f5d8af21edcf27775c8e`
    (`leanprover/lean4:v4.32.0`, cross-referenced with `712a8a5`),
  - `verse-lab/splean` at `e24286f51bd9ee207197d47ec587d592cdfb0ddc`
    (`leanprover/lean4:v4.11.0`),
  - `verse-lab/Lentil` at `b3ca5e224fed1e09fb22daa45a0b61ec5685df76`
    (`leanprover/lean4:v4.34.1`),
  - `goens/lean-hoare` at `aa2d88ae418d58ee22460a9097a2fad62c47eb38`
    (`leanprover/lean4:v4.22.0-rc2`, cross-referenced with `92e033c`),
  - `leanprover/cslib` at `82db31eec215b6843be6df283304cc02e736ddef`
    (`leanprover/lean4:v4.36.0-rc2`, and `v4.34.1` tag
    `7c8f6c0f67015df29b152fdcffaf7850db2e9185`),
  - `alexkeizer/QpfTypes` at `5b5dd4f83121662838b99d129b92f632f263c508`
    (`leanprover/lean4:v4.25.0`).
- **Anneal Trusted Operational Core (`joshlf/anneal`):** Examined at commit
  `6e9bf8b54344c8283946387b7db8bf6879c4caf1` (weak-memory MIR semantics in
  `trusted/lean/Trusted/` across `StepResult.lean`, `Refinement.lean`,
  `Memory.lean`, `MirAst.lean`, and `MirSemantics.lean`)
  and commit `8e7ab324dc86e2086f301cdfc61a35c768896229` (`trusted-core` branch
  with `Trusted/Attributes.lean` and `CrateTheorem`), both targeting
  `leanprover/lean4:v4.34.1`.
- **Preserved Mechanized Probes:**
  - `support/anneal_step_wp_and_choicekind_probe.lean` (SHA-256
    `38a5f90f0d5269ce763079d496c7034e9deef31da62a39950393d57f193accf7`, 1,674
    lines) is a standalone, zero-dependency Lean `v4.34.1` file that compiles
    directly via `lean -j1 -M1024`.
  - `support/R2IrisLeanProbe.lean` (SHA-256
    `67772f157e86f81b996cfc4b990721d328d3096ee309740ee8f000ed33653d4b`, 1,340
    lines) compiles via `lake env lean -j1 -M2048` against `iris-lean` at tag
    `v4.34.1` (`04b7689c294bb1dd6401e2dd53b337871934ea47`) and Anneal's
    `Trusted` library at commit `6e9bf8b54344c8283946387b7db8bf6879c4caf1`.

Execution timings (`time` in milliseconds) in Section 4 were measured on Linux
x86_64 (`joshlf-cloudtop`) under `leanprover/lean4:v4.34.1` with
`precompileLibrary = true` enabled for `Iris`; deterministic Lean heartbeat
counts (`IO.getNumHeartbeats`) and kernel expression DAG metrics
(`Expr.numObjs`, `Expr.approxDepth`) are machine-independent for a fixed Lean
toolchain and `iris-lean` commit.

## Findings

### 1. Architecture of `leanprover-community/iris-lean` (`04b7689` / `fb21a8a`)

`Basis: source + execution`

`iris-lean` is partitioned into two Lake workspaces in the repository root:
`IrisMath/` (containing ordinal arithmetic for transfinite step-indexing) and
`Iris/` (containing the separation-logic algebra, bunched-implication classes,
`UPred`/`IProp` models, ghost state libraries, and the Interactive Proof Mode).

#### 1.1 Bunched Implications (`BIBase`, `BI`, `Sbi`) and Multi-BI Notation

In `Iris/Iris/BI/BIBase.lean` and `Iris/Iris/BI/BI.lean`, the assertion logic
is parameterized over a carrier `PROP : Type u` equipped with `BIBase PROP` and
`BI PROP`:

- **Primitive connectives (`BIBase PROP`):** entailment `P ⊢ Q` (`Entails`),
  `emp`, pure embedding `⌜φ⌝` (`Pure`), conjunction `P ∧ Q`, disjunction
  `P ∨ Q`, implication `P → Q`, universal/existential quantifiers `∀ x, P x`
  and `∃ x, P x`, separating conjunction `P ∗ Q` (`Sep`), magic wand
  `P -∗ Q` (`Wand`), persistence modality `<pers> P` (`Persistently`), and
  later modality `▷ P` (`Later`).
- **Step-indexed BI (`Sbi PROP` in `Iris/Iris/BI/Sbi.lean`):** extends `BI PROP`
  with an internal step-indexed equality `x ≡{n}≡ y` (`InternalEq`) and Lӧb
  induction (`loeb`).
- **Multi-BI macro (`iprop(...)` and `bi%` in `Iris/Iris/BI/Notation.lean`):**
  To prevent notation collisions between standard Lean `Prop` connectives
  (`∧`, `∨`, `→`, `∀`, `∃`) and BI connectives, `iris-lean` scopes BI syntax
  inside `iprop(...)` or `bi%`. In `main` (`fb21a8a`), `local bi PROP` pins a
  default `BI` carrier within a section so nested `iprop(...)` blocks elaborate
  without repeated type annotations.

#### 1.2 Step-Indices (`SIdx I`), `OFE`/`COFE`, and Cameras (`CMRA` / `UCMRA`)

`iris-lean` abstracts step-indexing over a general `StepIndex I` typeclass
(`Iris/Iris/Algebra/OFE.lean`), instantiated both for standard natural numbers
`Nat` (finer-grained finite fuel) and for transfinite ordinals `Ordinal`
(`IrisMath/IrisMath/Ordinal.lean`). At `main` commit `fb21a8a`,
`Iris/IrisStepIndex/Elab.lean` and `Iris/IrisStepIndex/Registry.lean` add custom
elaborators for step-index polymorphism.

On top of `SIdx I`, `Iris/Iris/Algebra/` builds the camera hierarchy:

| Module | Core Declarations | Role in Separation Logic |
| :--- | :--- | :--- |
| `Iris/Iris/Algebra/OFE.lean` | `OFE α`, `COFE α`, `NonExpansive`, `Contractive`, `DiscreteO α`, `LeibnizO α`, ` OFunctor F`, `fixpoint` | Step-indexed metric space (`x ≡{n}≡ y`) and Banach/America-Rutten guarded recursive domain solver |
| `Iris/Iris/Algebra/CMRA.lean` | `CMRA α`, `UCMRA α`, `✓{n} x` (`ValidN`), `x • y` (`op`), `pcore`, `Included` | Partial commutative monoids with step-indexed validity and persistent cores |
| `Iris/Iris/Algebra/LocalUpdates.lean` & `Updates.lean` | `LocalUpdate (x, y) (x', y')`, `UpdateP x P` (`x ~~>: P`) | Frame-preserving algebraic updates backing ghost state mutation |
| `Iris/Iris/Algebra/Excl.lean` & `Agree.lean` | `Excl α`, `Agree α` | Exclusive ownership (`Excl.excl a`) and duplicable agreement (`toAgree a`) |
| `Iris/Iris/Algebra/DFrac.lean` | `DFrac` (`.own q`, `.discarded`, `.both q`) | Discardable fractions supporting exclusive (`1`), fractional (`q`), and permanently read-only (`discarded`) permissions |
| `Iris/Iris/Algebra/View.lean` & `HeapView.lean` | `View rel B`, `Auth α := View AuthRel α`, `HeapView K V M` | Authoritative (`● a`) and fragment (`◯ b`) views and partial-map heap cameras (`γ ↪●MAP m`, `γ ↪◯MAP[k]{dq} v`) |

#### 1.3 `UPred M`, `IProp GF`, and `BundledGFunctors`

`Iris/Iris/Instances/UPred/Instance.lean` defines the uniform step-indexed
resource predicate type `UPred (M : UCMRA)` as a predicate `M → SIdx → Prop`
monotone with respect to resource inclusion (`Included`) and downward-closed in
the step index (`SIdx`).

To support higher-order impredicative ghost state (such as impredicative
invariants storing arbitrary assertions), `Iris/Iris/Algebra/IProp.lean` solves
the recursive domain equation
$$\text{IProp}(\Sigma) \cong \text{UPred}\!\left(\prod_{i : \mathbb{N}} \text{DiscreteMap}(\text{GName}, \Sigma_i(\text{IProp}(\Sigma), \text{IProp}(\Sigma)))\right)$$
where `BundledGFunctors := Nat → GFunctor` (written `GF`) maps each integer slot
to a locally contractive bifunctor `RFunctorContractive F`. A concrete
instantiation provides a `BundledGFunctors` function assigning slots to specific
ghost state functors and discharging slot membership via `ElemG GF F` (a wrapper
around `∃ i : Nat, GF i = ⟨F, inst⟩`).

#### 1.4 Updates (`BUpd`, `FUpd`), Invariants (`Inv`), and Soundness

- **Basic updates (`|==> P` in `Iris/Iris/BI/Updates.lean` and
  `Iris/Iris/Instances/UPred/Instance.lean`):** `BUpd P` models frame-preserving
  ghost state allocation and mutation (`ghost_var_alloc`, `ghost_var_update`,
  `ghost_map_alloc_empty`, `ghost_map_insert`, `ghost_map_update`).
- **Fancy updates (`|={E1,E2}=> P` and `|={E1}[E2]▷=> P` in
  `Iris/Iris/Instances/Lib/FUpd.lean`):** Unlike basic updates, fancy updates
  carry co-finite invariant masks `E1, E2 : CoPset` and later credits.
  `Iris/Instances/Lib/FUpd.lean` defines:
  - `WorldSatisfaction (γ_inv γ_enb γ_dis : GName) (E : CoPset) : IProp GF`,
    holding the authoritative invariant map `InvPool` (slots of impredicative
    predicates guarded by `▷`), the enabled mask token `MaskToken`, and
    disabled-invariant tracking,
  - `uFUpd hlc γ_inv γ_enb γ_dis γ_cred E1 E2 P`, which threads
    `WorldSatisfaction` and `LaterCredits` across mask changes,
  - `Inv N P` (`inv N P`), which allocates a persistent impredicative invariant
    in namespace `N` that can be opened across an atomic step when `↑N ⊆ E1`.
- **Soundness / Adequacy Entry Points (`Iris/Iris/Instances/Lib/FUpd.lean` and
  `Iris/Iris/Instances/UPred/Instance.lean`):**
  - `Iris.step_fupdN_soundness_close`: given
    `∀ [InvGS_gen hlc GF], ⊢@{IProp GF} £ m -∗ |={⊤}[∅]▷=>^[n] ⌜φ⌝`,
    allocates fresh ghost names for the invariant pool, mask tokens, and `m`
    later credits, peels `n` nested step-indexed fancy updates
    `|={⊤}[∅]▷=>^[n]`, and extracts `⊢@{IProp GF} ⌜φ⌝`.
  - `UPred.pure_soundness : (⊢@{UPred M} ⌜φ⌝) → φ` evaluates a pure `UPred`
    entailment at the unit camera element `CMRA.unit` and step index `0` to
    obtain a pure Lean `Prop` proof of `φ`.
- **Interactive Proof Mode (`Iris/Iris/ProofMode/`):** In `Iris/lakefile.toml`,
  `precompileLibrary = true` compiles the ProofMode metaprograms (`iintro`,
  `icases`, `isplitl`, `isplitr`, `iframe`, `iapply`, `ihave`, `iexact`,
  `imod`, `imodintro`, `ipureintro`, `iexists`) into native shared objects,
  avoiding interpreter overhead during tactic execution.

---

### 2. Comparative Analysis of Lean 4 Program-Logic and Behavioral Frameworks

`Basis: source + execution + derived`

To determine whether any existing Lean 4 program-logic or behavioral framework
can verify Anneal's `MirMachine` or replace `iris-lean`, we inspected eight
upstream repositories across their source trees.

| Repository | Pinned Commit (`lean-toolchain`) | Semantic Paradigm | Separation Logic (`∗`, `-∗`) | Nondeterminism Model | TCB / Axiom Footprint | Suitability for Anneal `MirMachine` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `leanprover-community/iris-lean` | `04b7689c294bb1dd6401e2dd53b337871934ea47` (`v4.34.1`) & `fb21a8af4727bd42190072a5ed2836cbe9fb844e` (`v4.35.0`) | Higher-order step-indexed separation logic (`UPred`, `IProp`, `CMRA`, `FUpd`, `Inv`) | Full BI (`∗`, `-∗`, `<pers>`, `▷`, `\|==>`, `\|={E1,E2}=>`) + IPM tactics | Algebraic / agnostic (user defines `wp` over operational step relation) | Zero `sorry`; standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) | **Directly suitable** for `theory/` via custom `wpIProp` + `wpIProp_adequacy` (Section 3.2) |
| `verse-lab/loom` | `78928abc9054b31d0bea85985496490baae95244` (`v4.24.0`; ref `7f53c15`) | Monad-algebra WP (`MAlgOrdered`, `MAlgDet`) over `CCompleteLattice` (`PROP`) | None (pure complete-lattice assertions over monadic state) | Simultaneous demonic (`pickCont` / `iInf`) and angelic (`angelicCont` / `iSup`) in `NonDetT` | Uses `Classical.choice`; relies on `QpfTypes` & `Mathlib` | **Incompatible with `IProp`:** `WP/Gen.lean` requires `[CCompleteLattice l]` (`iSup`/`iInf` laws), which `UPred`/`IProp` does not satisfy |
| `verse-lab/velvet` | `836ed5a163b36c09081ed1d8aeecd3cec040f87e` (`v4.35.0`) | Imperative DSL (`method`) compiled to `Loom`'s `NonDetT`/`DivM` with `mvcgen` + ` grind`/`omega` | Affine array slice permissions via `SepConj` in pure `Prop` (`AssertionTypes.lean`), not BI | Inherits `Loom` `NonDetT` (`wp_demonic`, `wp_angelic`, `totalCorrectness`, `partialCorrectness`) | Depends on `loom`, `Mathlib`, `auto` | Shallow DSL over `DivM`; does not model an AST-defined small-step machine or weak-memory heap |
| `verse-lab/veil` | `eb458cb602d3cf9a19d8f5d8af21edcf27775c8e` (`v4.32.0`; ref `712a8a5`) | Relational two-state transition systems (`ActionSpec.lean`, `wp_action`, `wlp_action`) | None (first-order relational predicates over global state) | Relational two-state predicates translated to SMT-LIB | Discharges proof obligations via `lean-auto` + external SMT solvers (`cvc5`/`z3`) | Violates Anneal's self-contained Lean kernel proof requirement unless SMT proofs are reconstructed |
| `verse-lab/splean` | `e24286f51bd9ee207197d47ec587d592cdfb0ddc` (`v4.11.0`) | CFML-style shallowly embedded separation logic over `Finmap Ptr Val` (`HProp := Heap → Prop`) | First-order `HProp` (`hstar`, `hwand`, `hpure`, `hexists`, `xsimp` tactic) | Deterministic big-step evaluation (`eval_ns` in `WP1.lean`) | Depends on `Mathlib` (`Finmap`); pinned to `v4.11.0` | Lacks step-indexing, ghost state, cameras, invariants, and weak-memory timestamp views |
| `verse-lab/Lentil` | `b3ca5e224fed1e09fb22daa45a0b61ec5685df76` (`v4.34.1`) | Small-step and big-step operational equivalence for an educational `WHILE` language (`Lentil.lean`) | None (no Hoare logic, WP, or separation logic) | Deterministic `Stmt` transitions | Zero dependencies (`v4.34.1`) | Educational semantics demo only (374 lines in `Lentil.lean`); no program logic |
| `goens/lean-hoare` | `aa2d88ae418d58ee22460a9097a2fad62c47eb38` (`v4.22.0-rc2`; ref `92e033c`) | Educational Hoare triples `Triple P c Q` over an imperative `Com` AST (`Hoare/Logic.lean`) | None (`Assn := State → Prop`) | Deterministic `Com.Step` / `Com.eval` (`Hoare/Basic.lean`) | **Unsound rules + `sorry`:** `TripleHolds.skip` and `.assign` leave `c : Com` unconstrained; `Sqrt.lean` has `sorry` | Unusable: no soundness proof connecting `TripleHolds` to `Com.Step` or `Com.eval` |
| `leanprover/cslib` | `82db31eec215b6843be6df283304cc02e736ddef` (`v4.36.0-rc2`; `v4.34.1` tag `7c8f6c0`) | Labeled transition systems (`LTS`), weak/branching bisimulation, Hennessy-Milner logic (`HML`) | None (behavioral equivalence and modal logic over `LTS`) | Relation-based labeled transitions `Tr : State → Label → State → Prop` | Depends on `Mathlib` | Orthogonal: provides `LTS` bisimulation and `HML`, not separation logic or `SmallStepMachine` WP |
| `alexkeizer/QpfTypes` | `5b5dd4f83121662838b99d129b92f632f263c508` (`v4.25.0`) | Multivariate Quotient Polynomial Functors (`data` / `codata` macros for inductive/coinductive types) | N/A (datatype construction library used by `Loom`) | Coinductive trees over non-indexed polynomial functors | Depends on `Mathlib` | **Cannot elaborate indexed `ITree.vis`:** `elabQpfCompositionBody` rejects dependent constructor arguments |

#### 2.1 Detailed Findings on Individual Non-Iris Frameworks

- **`verse-lab/loom` (`78928ab`) and `verse-lab/velvet` (`836ed5a`):**
  In `Loom/MonadAlgebras/NonDetT/Extract.lean` (lines 17–86), `Loom` defines a
  nondeterministic interaction-tree transformer `NonDetT m α` with explicit
  constructors for demonic choice (`pickCont : (τ → NonDetT m α) → NonDetT m α`)
  and angelic choice (`angelicCont : (τ → NonDetT m α) → NonDetT m α`),
  interpreted via a `MAlgOrdered` homomorphic lift mapping `pickCont` to the
  complete-lattice infimum `⨅ x, f x` and `angelicCont` to the supremum
  `⨆ x, f x`. In `Loom/MonadAlgebras/WP/Gen.lean`, `WPGen` requires the
  assertion carrier `l` to implement `[CCompleteLattice l]`. Because `UPred M`
  and `IProp GF` are step-indexed `OFE`s rather than complete Boolean lattices
  with law-abiding classical `iSup`/`iInf` distribution, `Loom`'s `WPGen` cannot
  be instantiated over `IProp GF`.
- **`verse-lab/splean` (`e24286f`) and the `LayerCake` Naming Clarification:**
  No standalone Lean 4 program-logic repository named `LayerCake` exists on
  GitHub or Lean Reservoir (in `Mathlib4`,
  `Mathlib/MeasureTheory/Integral/Layercake.lean` formalizes the
  measure-theoretic layer-cake representation theorem). Within the `verse-lab`
  ecosystem, the companion separation-logic project to `velvet`, `loom`, `veil`,
  and `Lentil` is `verse-lab/splean`
  (`e24286f51bd9ee207197d47ec587d592cdfb0ddc`),
  which ports Arthur Charguéraud's CFML separation logic (`HProp := Heap → Prop`
  over `Finmap Ptr Val`, with an `xsimp` framing tactic in
  `SPLean/Theories/XSimp.lean` and big-step evaluation `eval_ns` in
  `SPLean/Theories/WP1.lean`). Because `splean` models assertions as flat
  predicates over a single `Finmap Ptr Val` heap without step-indexing, cameras,
  ghost state, or weak-memory views, it cannot model Anneal's timestamped
  `Trusted.MemState` or recursive invariants.
- **`goens/lean-hoare` (`aa2d88a`):**
  Direct inspection of `Hoare/Logic.lean` (lines 7–29) reveals that the
  inductive derivation relation `TripleHolds : Triple → Prop` is both
  disconnected from the operational semantics in `Hoare/Basic.lean` (there is no
  soundness theorem relating `TripleHolds` to `Com.Step` or `Com.eval`) and
  **syntactically unsound**: the `skip` constructor
  `| skip : TripleHolds {P := P, c := c, Q := P}` and the `assign` constructor
  `| assign : TripleHolds {P := fun s => P (s[x ↦ a.eval s]), c := c, Q := P}`
  universally quantify over an arbitrary command `c : Com` instead of fixing
  `c = Com.skip` and `c = Com.assign x a`. Furthermore,
  `Hoare/Examples/Sqrt.lean` (line 87) leaves its loop-invariant verification
  obligation as `sorry`.
- **`alexkeizer/QpfTypes` (`5b5dd4f`) Limitation on Indexed `ITree.vis`:**
  In `Qpf/Macro/Data.lean` (lines 75–160), `elabQpfCompositionBody` compiles
  recursive constructor payloads into compositions of multivariate polynomial
  functors `MvPFunctor`. In `Test/ITree.lean` (lines 17–24), the author
  documents that standard indexed interaction trees
  `vis : {ans : Type} → E ans → (ans → ITree E R) → ITree E R` **cannot** be
  defined via `codata` because the continuation type `ans → ITree E R` depends
  on the value of the preceding constructor argument `ans` (and/or an indexed
  effect family `E : Type → Type`), which `elabQpfCompositionBody` rejects as a
  non-functorial dependent arrow. `Test/ITree.lean` works around this only by
  collapsing `vis` to a fixed, unindexed parameter type `E → (A → ITree E A R)`.
  Consequently, `QpfTypes` cannot directly represent dependently typed
  effect signatures without encoding them into a fixed sum type.

---

### 3. Two-Tier Step-Indexed WPs and Adequacy to Anneal's `SpecOn`

`Basis: source + execution + derived`

Anneal's trusted core (`Trusted/Refinement.lean` and `Trusted/StepResult.lean`)
defines program verification as refinement in the `Partial` Smyth powerdomain
over finite fuel-indexed execution queries `q : ExecQuery State`:
```lean
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined := M.initState p q.init → ∀ tr out,
      ReachesPrefix M p q.init q.steps q.init tr out → out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧ ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }
```
A specification `L.SpecOn pre post` holds
(`BehaviorOf M p ≤ M.toLanguage.SpecOn pre post`)
if and only if, for every query `q : ExecQuery State` satisfying `pre q` and
every valid initial state `M.initState p q.init`, **every** reachable prefix
`ReachesPrefix M p q.init q.steps q.init tr out` is safe (`out.isSafe`, meaning
`out ≠ .failed err` and `out ≠ .stuck`) and satisfies `post q ⟨tr, out⟩`.

Because `BehaviorOf` and `SpecOn` are stated purely in Lean `Prop` over
finite fuel `q.steps : Nat`:

1. **`trusted/` remains completely independent of `iris-lean`:** Neither `BI`,
   `CMRA`, `UPred`, nor `IProp` needs to enter `trusted/lean/`.
2. **`theory/` can use two complementary WP adequacy bridges** that discharge
   directly into `Trusted.BehaviorOf M p ≤ M.toLanguage.SpecOn pre post`.

#### 3.1 Tier 1: Zero-Dependency Fuel-Indexed `wpAt` in `Prop`

For sequential, loop-invariant, and lightweight ownership proofs that do not
require impredicative invariants or higher-order ghost state,
`support/anneal_step_wp_and_choicekind_probe.lean` defines a standalone,
zero-dependency separation logic `Assertion α := Nat → α → Prop` over an
abstract `ResourceAlgebra α` (`ValidAt`, `op`, `core`, `IncludedAt`, and
frame-preserving update `FrameUpdate` `|==> P`) and a fuel-indexed weakest
precondition `wpAt`:
```lean
def wpAt (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → Assertion α)
    (p : Prog) :
    Nat → State → List Obs →
      (List Obs → PrefixOutcome Val → Assertion α) → Assertion α
  | 0, s, hist, Φ =>
      Assertion.wand (stateInterp s hist)
        (Assertion.bupd (Assertion.sep (stateInterp s hist) (Φ hist .running)))
  | k + 1, s, hist, Φ =>
      Assertion.and (Assertion.pure (∃ r0, M.step p s r0))
        (Assertion.forall_ fun r =>
          Assertion.wand (Assertion.pure (M.step p s r))
            (match r with
             | .step obs s' =>
                 Assertion.wand (stateInterp s hist)
                   (Assertion.bupd (Assertion.later
                     (Assertion.sep (stateInterp s' (hist ++ [obs]))
                       (wpAt M stateInterp p k s' (hist ++ [obs]) Φ))))
             | .choice _ branches =>
                 Assertion.and (Assertion.pure (∃ s0, branches s0))
                   (Assertion.forall_ fun s' =>
                     Assertion.wand (Assertion.pure (branches s'))
                       (Assertion.wand (stateInterp s hist)
                         (Assertion.bupd (Assertion.later
                           (Assertion.sep (stateInterp s' hist)
                             (wpAt M stateInterp p k s' hist Φ))))))
             | .terminated term =>
                 Assertion.wand (stateInterp s hist)
                   (Assertion.bupd
                     (Assertion.sep (stateInterp s hist)
                       (Φ hist (.terminated term))))
             | .failed _ =>
                 Assertion.pure False))
```
Key design invariants of `wpAt` proved in
`support/anneal_step_wp_and_choicekind_probe.lean`:

- **Total step obligation (`∃ r0, M.step p s r0` and `∃ s0, branches s0`):**
  Unlike partial-correctness Iris `wp` in Rocq (which treats stuck non-values as
  vacuously safe or handles progress separately), Anneal's `ReachesPrefix` has
  explicit `.noStep` and `.emptyChoice` constructors that produce `.stuck`
  (`isSafe = False`). Conjoining `⌜∃ r0, M.step p s r0⌝` and
  `⌜∃ s0, branches s0⌝` in `wpAt` rules out `.noStep` and `.emptyChoice` during
  adequacy induction.
- **Zero-fuel base case (`k = 0`):** Because `ReachesPrefix.zero` produces
  `.running` when `q.steps = 0`, `wpAt` at `k = 0` requires
  `stateInterp s hist -∗ |==> (stateInterp s hist ∗ Φ hist .running)`.
- **Frame rule (`wpAt_frame`), consequence (`wpAt_mono`), and adequacy
  (`wp_adequacy_specOn`):** Proved with zero `sorry` and depending only on
  `[propext]`, and exercised on both an unbounded fuel-indexed loop with a loop
  invariant (`counterLoop_wellFormed`) and a two-cell spatial framing update
  (`twoCell_spec`).

#### 3.2 Tier 2: Full `iris-lean` `IProp AnnealGF` + `FUpd` Adequacy

For unsafe Rust and concurrent/weak-memory verification requiring impredicative
invariants (`Inv N P`), fractional/discardable permissions (`DFrac`), or
authoritative ghost maps (`GhostMapG`), `support/R2IrisLeanProbe.lean`
instantiates `iris-lean` (`04b7689`) directly over Anneal's `Trusted.MirMachine`
and `Trusted.MemState`:

1. **`AnnealGF : BundledGFunctors`:**
   - Slots `0..3`: `InvGpreS AnnealGF` (`InvMapF`, `CoPsetDisjL`,
     `DisjointLeibnizSet PosSet`, and `Auth.AuthURF (constOF Credit)`),
     enabling full `FUpd` (`|={E1,E2}=>` and `|={⊤}[∅]▷=>`) and `Inv N P`.
   - Slot `4`: `GhostMapG AnnealGF Nat Trusted.MirVal HeapMapF` over
     `HeapMapF V := Std.ExtTreeMap Nat V compare`, providing spatial points-to
     assertions `loc ↦ₘ[γh]{dq} v` (`γh ↪◯MAP[loc]{dq} v`) and authoritative
     heap ownership `γh ↪●MAP m`.
   - Slot `5`: `GhostVarG AnnealGF Trusted.MirState` (`γs ↪VAR s`), tracking
     control-flow (`block`, `stmtIdx`) and functional locals.
2. **Bridging Spatial Points-To `loc ↦ₘ[γh]{dq} v` to Weak-Memory Views
   (`OwnLocInMem`):**
   In `Trusted/Memory.lean`, non-atomic reads (`MemState.readNA`) and writes
   (`MemState.writeNA`) fail with `.ub` (data race) unless the active thread's
   coherence view `curView loc` dominates `naWriteTs loc` (for reads and writes)
   and `naReadTs loc` (for writes). `support/R2IrisLeanProbe.lean` defines:
   ```lean
   def OwnLocInMem (mem : Trusted.MemState) (loc : Nat) (v : Trusted.MirVal) : Prop :=
     mem.naVal loc = some v ∧
     mem.naWriteTs loc ≤ mem.curView loc ∧
     mem.naReadTs loc ≤ mem.curView loc
   ```
   and ties the authoritative ghost map `γh ↪●MAP m` to `OwnLocInMem s.mem` in
   `mirHeapInterp`. By `mirPointsTo_lookup` (`ghost_map_lookup`), holding
   `loc ↦ₘ[γh]{dq} v` immediately entails `⌜OwnLocInMem s.mem loc v⌝`, which by
   `writeNA_of_ownLocInMem` and `readNA_of_ownLocInMem` guarantees that
   `writeNA` and `readNA` succeed without `.ub` and preserve `OwnLocInMem` after
   `View.bump`!
3. **Fancy-Update Adequacy Bridge (`wpIProp_adequacy`):**
   `wpIProp` uses `|={⊤}[∅]▷=>` (`step_fupd`) at every `.step` and `.choice`
   transition and `|={⊤}=>` at `k = 0` and `.terminated term`. Because a
   machine can terminate at step $m < q.\text{steps}$, `wpIProp_reachesPrefix`
   pads early termination with $q.\text{steps} - m$ vacuous step-indexed fancy
   updates via `fupd_to_step_fupdN`, yielding uniformly
   `|={⊤}[∅]▷=>^[q.steps] |={⊤}=> ⌜out.isSafe ∧ post q ⟨tr, out⟩⌝`.
   `wpIProp_adequacy` then converts this to `|={⊤}[∅]▷=>^[q.steps + 1] ⌜...⌝`
   via `step_fupdN_fupd_to_succ` and discharges it into `Prop` using
   `Iris.step_fupdN_soundness_close (q.steps + 1) 0` followed by
   `UPred.pure_soundness`.
4. **End-to-End Verified MIR Canaries (`idCopyBody` and `writeRead42Body`):**
   - `idCopyBody_verified_via_iris_lean` proves
     `Trusted.MirSem idCopyBody ≤ Trusted.EnsuresEqArg 1` using `GhostVarG`
     allocation (`ghost_var_alloc`), mutation (`ghost_var_update`), and mask
     closing (`fupd_mask_subseteq`).
   - `writeRead42Body_verified_via_iris_lean` proves
     `Trusted.MirSem writeRead42Body ≤ EnsuresWriteRead42` for
     `pub fn write_read_42(x: &mut usize) -> usize { *x = 42; *x }` using
     spatial points-to allocation (`ghost_map_alloc_empty`, `ghost_map_insert`),
     spatial write update (`ghost_map_update`), and spatial read lookup
     (`ghost_map_lookup`).
   - `#print axioms` on `wpIProp_adequacy`, `idCopyBody_verified_via_iris_lean`,
     and `writeRead42Body_verified_via_iris_lean` confirms that all three
     depend solely on `[propext, Classical.choice, Quot.sound]`.

---

### 4. Empirical `iris-lean` IPM Framing Scaling Laws ($N = 5, 10, 20, 40$)

`Basis: source + execution + derived`

In `support/R2IrisLeanProbe.lean` (Part 2), the custom command elaborator
`measure_decl` instruments Lean 4 (`v4.34.1`) across four benchmark families for
$N \in \{5, 10, 20, 40\}$ spatial points-to hypotheses `(i ↦ₘ[γ] v)` in
`IProp AnnealGF`, recording wall-clock elaboration time (`IO.monoNanosNow`),
deterministic heartbeats (`IO.getNumHeartbeats`), kernel proof-term DAG node
count (`Expr.numObjs`), and expression tree depth (`Expr.approxDepth`).

#### 4.1 Complete Benchmark Table ($N = 5, 10, 20, 40$)

| Benchmark Family | Declaration | $N$ | Wall Time (ms) | Heartbeats ($\text{HB}$) | $\Delta\text{HB} / \Delta N$ | Proof DAG Nodes (`numObjs`) | $\Delta\text{numObjs} / \Delta N$ | Proof Depth (`approxDepth`) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Family 1:** In-order `iintro` + `iframe` | `bench_iframe_inorder_5` | 5 | 32.58 | 260,040 | — | 604 | — | 64 |
| | `bench_iframe_inorder_10` | 10 | 47.45 | 513,156 | 50,623.2 | 1,234 | 126.0 | 114 |
| | `bench_iframe_inorder_20` | 20 | 94.58 | 1,019,686 | 50,653.0 | 3,094 | 186.0 | 214 |
| | `bench_iframe_inorder_40` | 40 | 181.42 | 2,033,344 | 50,682.9 | 9,214 | 306.0 | 255 (capped) |
| **Family 2:** Reverse-order `iintro` + `iframe` | `bench_iframe_rev_5` | 5 | 25.67 | 260,001 | — | 560 | — | 64 |
| | `bench_iframe_rev_10` | 10 | 47.22 | 513,220 | 50,643.8 | 955 | 79.0 | 114 |
| | `bench_iframe_rev_20` | 20 | 92.45 | 1,019,689 | 50,646.9 | 1,745 | 79.0 | 214 |
| | `bench_iframe_rev_40` | 40 | 185.26 | 2,033,283 | 50,679.7 | 3,325 | 79.0 | 255 (capped) |
| **Family 3:** `iintro` + `isplitr` + `iframe` + `iapply` | `bench_step_split_apply_5` | 5 | 30.55 | 317,804 | — | 722 | — | 64 |
| | `bench_step_split_apply_10` | 10 | 52.86 | 571,007 | 50,640.6 | 1,317 | 119.0 | 114 |
| | `bench_step_split_apply_20` | 20 | 97.23 | 1,077,659 | 50,665.2 | 3,107 | 179.0 | 214 |
| | `bench_step_split_apply_40` | 40 | 189.54 | 2,091,263 | 50,680.2 | 9,087 | 299.0 | 255 (capped) |
| **Family 4:** Functional `MirState.locals` (`rfl`) | `bench_func_locals_5` | 5 | 2.43 | 18,609 | — | 24 | — | 7 |
| | `bench_func_locals_10` | 10 | 3.24 | 27,773 | 1,832.8 | 24 | 0.0 | 7 |
| | `bench_func_locals_20` | 20 | 4.68 | 46,056 | 1,828.3 | 24 | 0.0 | 7 |
| | `bench_func_locals_40` | 40 | 7.43 | 82,516 | 1,823.0 | 24 | 0.0 | 7 |

*(Note: `Expr.approxDepth` in Lean 4's C++ kernel stores expression depth in a
`uint8_t` field capped at `255`; for $N \in \{5, 10, 20\}$, the exact depth is
$\text{depth}(N) = 10N + 14$, which extrapolates to $414$ at $N = 40$.)*

#### 4.2 Root-Cause Analysis of Quadratic vs. Linear Proof-Term DAGs

Inspection of `Iris/Iris/ProofMode/Expr.lean` (`Hyps`),
`Iris/Iris/ProofMode/Tactics/Frame.lean`, and
`Iris/Iris/ProofMode/Tactics/Split.lean` explains every empirical scaling law in
the table above:

1. **Why `iframe` Heartbeats Scale Linearly ($\approx 50,665\,\text{HB}/N$) in
   Both Orderings:**
   When `iintro ⟨H1, ..., HN⟩` introduces $N$ right-associated spatial
   hypotheses, it performs $N - 1$ calls to `icases` ($\approx 25\text{k}$
   heartbeats per hypothesis), building a right-leaning binary `Hyps.sep` spine
   of depth $N$. When `iframe` runs (`Frame.lean`), it decomposes the target
   conjunction `Q1 ∗ (Q2 ∗ ... ∗ QN)` left-to-right and synthesizes a
   `Frame (IProp AnnealGF) false P Q R` typeclass instance for each atomic
   target `Qi`, searching the `Hyps` tree via `Hyps.findWithInfo`
   ($\approx 25\text{k}$ heartbeats per hypothesis). Because `precompileLibrary
   = true` compiles the `Hyps` traversal into native code, the tree search
   itself costs negligible heartbeats compared to Lean's `synthInstance` and
   `isDefEq` checks, yielding a nearly constant marginal cost of
   $\approx 50,665$ heartbeats per spatial hypothesis:
   $$\text{HB}_{\text{iframe}}(N) \approx 50,665\,N + 6,700.$$
2. **Why In-Order `iframe` (`Family 1` & `Family 3`) Produces Quadratic
   ($O(N^2)$) Kernel Proof Terms While Reverse-Order `iframe` (`Family 2`)
   Produces Linear ($O(N)$) Kernel Proof Terms:**
   After `iintro ⟨H1, H2, ..., HN⟩` elaborates via
   `Iris/ProofMode/Patterns/CasesPattern.lean`, the IPM context `Hyps` is a
   binary `Hyps.sep` spine in which $H_1$ sits at the deepest leaf while $H_N$
   sits near the root:
   - In **Family 1 (In-Order)**, `iframe` frames target $Q_1$ (matching $H_1$ at
     depth $N$), then $Q_2$ (matching $H_2$ at depth $N - 1$), ..., up to $Q_N$
     (matching $H_N$). Because `Hyps` is an applicative `Expr`-backed tree,
     each call to `Hyps.remove` for $H_i$ traverses to depth $N - i + 1$ and
     invokes the smart constructor `Hyps.mkSep` at every ancestor on the path
     back to the root, allocating $N - i$ fresh `Expr` applications containing
     the newly mutated subtrees. Summing $\sum_{i=1}^N (N - i) = N(N-1)/2$
     yields the exact quadratic closed form:
     $$\text{numObjs}_{\text{inorder}}(N) = 5N^2 + 33N + 314 \quad (\text{exact for } N = 5, 10, 20, 40).$$
   - Conversely, in **Family 2 (Reverse-Order)**, the target is ordered
     $(N \mapsto_m v) ∗ ((N-1) \mapsto_m v) ∗ \dots ∗ (1 \mapsto_m v)$, so
     `iframe` removes $H_N$ first (at the shallow end of the `Hyps` spine),
     collapsing the top `Hyps.sep` node in $O(1)$ nodes without rebuilding any
     ancestors! Every subsequent removal $H_{N-1}, \dots, H_1$ also peels the
     current top of the spine in $O(1)$ nodes, yielding the exact linear closed
     form:
     $$\text{numObjs}_{\text{rev}}(N) = 79N + 165 \quad (\text{exact for } N = 5, 10, 20, 40).$$
     At $N = 40$, reverse-order framing reduces kernel proof-term DAG size from
     $9,214$ nodes to $3,325$ nodes ($2.77\times$ smaller) and at $N = 100$
     extrapolates to $8,065$ nodes vs. $53,614$ nodes ($6.65\times$ smaller).
3. **Why `isplitr` / `isplitl` (`Family 3`) Adds Only $O(1)$ Overhead:**
   In `Iris/Iris/ProofMode/Tactics/Split.lean`, `Hyps.split` partitions the
   `Hyps` tree in a single bottom-up pass using a boolean membership predicate,
   emitting one `split_Step` theorem application per binary `Hyps.sep` node
   without repeated root-to-leaf removals. Thus `Family 3` adds a fixed constant
   overhead of $\approx 57,800\text{--}57,970$ heartbeats over `Family 1`.
4. **Why Functional `MirState.locals` (`Family 4`) Is $27.7\times$ Cheaper in
   Heartbeats and $384\times$ Smaller in Proof-Term Nodes at $N = 40$:**
   Evaluating `populateLocals v N 1 = some v` by `rfl` performs kernel WHNF
   reduction of `Trusted.updateLocal` without constructing any BI or `Hyps`
   proof terms, producing a constant **24-node, depth-7** `Eq.refl` proof term
   at all $N$. Therefore, Anneal's MIR verification architecture should never
   place non-address-taken SSA/stack locals into `GhostMapG`; stack-only MIR
   locals should remain in the functional `MirState.locals` map
   (`LocalIdx → Option MirVal`), while `mirPointsTo` (`loc ↦ₘ[γh]{dq} v`) is
   used exclusively for memory allocations (`MemState`) accessed via references,
   raw pointers, or atomics.

---

### 5. Audit and Resolution of `ChoiceKind.angelic` in `Trusted/StepResult.lean`

`Basis: source + execution + derived`

#### 5.1 Audit of `ChoiceKind.angelic` (Option B Semantic Trap)

In Anneal's `trusted/lean/Trusted/StepResult.lean` (commit
`6e9bf8b54344c8283946387b7db8bf6879c4caf1`, lines 18–26 and 95–133; and commit
`8e7ab324dc86e2086f301cdfc61a35c768896229`), `ChoiceKind` and `StepResult` are
defined as:
```lean
inductive ChoiceKind where
  | demonic
  | angelic
  deriving DecidableEq, Repr

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
```
However, in `ReachesPrefix` (`Trusted/StepResult.lean`, lines 95–133), the two
choice constructors are:
```lean
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
```
And `BehaviorOf` (`Trusted/StepResult.lean`, lines 155–165) defines:
```lean
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined := M.initState p q.init → ∀ tr out,
      ReachesPrefix M p q.init q.steps q.init tr out → out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧ ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }
```
Three mechanized facts in `support/anneal_step_wp_and_choicekind_probe.lean`
and `support/R2IrisLeanProbe.lean` expose the exact semantic defect in this
encoding (Option B):

1. **`ChoiceKind` is a phantom parameter in `ReachesPrefix`
   (`angelic_choice_phantom_in_reachesPrefix`):** Neither `ReachesPrefix.choice`
   nor `ReachesPrefix.emptyChoice` discriminates on `kind`. Every enabled branch
   `branches s'` of a `.choice .angelic branches` transition generates a valid
   `ReachesPrefix` derivation tree, identically to `.choice .demonic branches`.
2. **Universal path quantification in `BehaviorOf.defined` turns
   `.choice .angelic` into demonic intersection
   (`optionB_angelic_trap_is_ub`):**
   Consider the 3-state machine `angelicTrapMachine`:
   - State `0` (initial state) steps via
     `.choice .angelic (fun s' => s' = 1 ∨ s' = 2)`,
   - State `1` (the good angelic witness) terminates normally via
     `.terminated (.normal ())`,
   - State `2` (an untaken angelic branch) fails via `.failed .ub`.
   Under standard angelic nondeterminism, state `0` is **safe** because the
   angelic player can choose witness `s' = 1`. Under `Trusted.BehaviorOf`,
   however, `optionB_angelic_trap_is_ub` proves
   `¬ (Trusted.BehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined`
   (`defined = False`, i.e., `Partial.ub`), because `ReachesPrefix.choice`
   explores branch `s' = 2` and `BehaviorOf.defined` universally quantifies over
   **all** `ReachesPrefix` derivations!
3. **`Trusted/MirSemantics.lean` never constructs `.choice .angelic`:** Across
   all of `trusted/lean/`, `evalMirStep` is a deterministic function
   `MirBody → MirState → StepResult MirState Unit MirVal` that emits only
   `.step`, `.terminated`, and `.failed`. Neither `.choice .demonic` nor
   `.choice .angelic` is emitted by current MIR evaluation.

#### 5.2 Why Pathwise `ReachesPrefix` Cannot Express Angelic Choice

Why can't `ReachesPrefix` simply be patched in-place while keeping
`BehaviorOf.defined := ∀ tr out, ReachesPrefix ... → out.isSafe`?

- A single derivation of `ReachesPrefix M p init k s tr out` represents a
  **single execution path** producing a single trace `tr : List Obs` and single
  terminal outcome `out : PrefixOutcome Val`.
- Under universal quantification `∀ tr out, ReachesPrefix ... → P tr out`:
  $$\left(\forall \text{tr}, \text{out},\; (\exists s',\, \text{branches}(s') \wedge \text{ReachesPrefix}(s', \text{tr}, \text{out})) \to P(\text{tr}, \text{out})\right) \iff \left(\forall s',\, \text{branches}(s') \to \forall \text{tr}, \text{out},\; \text{ReachesPrefix}(s', \text{tr}, \text{out}) \to P(\text{tr}, \text{out})\right).$$
  By currying, an existential quantifier inside the premise of
  `BehaviorOf.defined` automatically becomes a **universal** quantifier over
  `s'`!
- Genuine dual (demonic + angelic) nondeterminism is a **two-player game**
  (alternating $\forall_{\text{demonic}} \exists_{\text{angelic}}$ at each step,
  or existentially quantifying over an angelic strategy tree $\exists \sigma,
  \forall \text{path} \in \sigma$) and cannot be represented as universal
  quantification over unstratified single-path reachability.

#### 5.3 Two-Stage Resolution Mechanized in the Preserved Probes

| Option | Trusted-Core Delta | Treatment of Demonic Choice | Treatment of Angelic Choice | Compatibility with `Iris.step_fupdN_soundness_close` | Recommended Role |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Option A** (`StepResultA`, `ReachesPrefixA`) | Delete `ChoiceKind` (4 lines in `Trusted/StepResult.lean`); `.choice (branches : State → Prop)` | Universal over all `branches s'`, inhabited (`¬ ∃ s', branches s'` is `.stuck`) | Removed from `StepResult`; relational/existential witnesses live in `SpecOn` `post` | **Direct 1-to-1 compatibility** (`wpIProp_adequacy`) | **Stage 1 (Immediate):** Eliminate the Option B semantic trap in `Trusted/StepResult.lean` |
| **Option B** (Status quo `Trusted/StepResult.lean`) | 0 lines (keeps dead `ChoiceKind.angelic`) | Universal over `branches s'` | **Broken (`optionB_angelic_trap_is_ub`):** treated identically to `.demonic` | Compatible only because `.angelic` is treated as `.demonic` | **Reject / Replace** |
| **Option C** (`GameHolds` / `GameBehaviorOf` and Skolemized `ReachesWithStrategy` / `StrategyBehaviorOf`) | Replace or augment `BehaviorOf` with `GameBehaviorOf` or `StrategyBehaviorOf` (~35 lines) | Universal over all `branches s'` (`(∃ s0, branches s0) ∧ ∀ s', ...`) | Existential witness `∃ s', branches s' ∧ ...` (or Skolem strategy `strat : Nat → State → State`) | **Direct compatibility via Skolemized `ReachesWithStrategy`** (`∃ strat` outside `step_fupdN_soundness_close`) | **Stage 2 (When needed):** If FFI/abstract-module specs require in-step angelic witness selection |

Both stages are mechanized with zero `sorry` in both preserved probes:

1. **Stage 1 (`Option A` — `reachesPrefixA_iff_reachesPrefix`):**
   Removing `ChoiceKind` from `StepResult` (`StepResultA.choice`)
   and `ReachesPrefix` (`ReachesPrefixA`) is proved strictly equivalent to
   `Trusted.ReachesPrefix` over `SmallStepMachineA.toTrusted` (which maps
   `.choice` to `.choice .demonic` and maps `.choice .angelic` to `False`),
   using **zero axioms** (`reachesPrefixA_iff_reachesPrefix` depends on no
   axioms).
2. **Stage 2 (`Option C` — Inductive Game Semantics `GameHolds` / `wpDualAt` and
   Skolemized Strategy Semantics `ReachesWithStrategy`):**
   - **Inductive Game Form (`GameHolds`, `GameBehaviorOf`, `wpDualAt`):**
     `GameHolds M p post fuel s hist` recurses on `fuel : Nat`, interpreting
     `.choice .demonic branches` as
     `(∃ s0, branches s0) ∧ ∀ s', branches s' → GameHolds ...`
     and `.choice .angelic branches` as `∃ s', branches s' ∧ GameHolds ...`.
     In `support/anneal_step_wp_and_choicekind_probe.lean`, `wpDualAt` models
     existential angelic choice inside the separation-logic WP, and
     `wpDualAt_sound_for_gameHolds` + `wpDual_adequacy_specOn` prove its
     adequacy for `GameBehaviorOf`. On `angelicTrapMachine`,
     `optionC_angelic_trap_holds` and `optionC_angelic_trap_is_defined` prove
     that `GameBehaviorOf angelicTrapMachine () ⟨0, 2⟩` is **defined** (`True`)
     and terminates normally at `()`, contrasting directly with
     `optionB_angelic_trap_is_ub`.
   - **Skolemized Strategy-Tree Form (`AngelicStrategy`, `ReachesWithStrategy`,
     `StrategyBehaviorOf`) for `iris-lean` `FUpd` Adequacy:**
     Because `Iris.step_fupdN_soundness_close` closes a single linear chain of
     fancy updates `|={⊤}[∅]▷=>^[n] ⌜φ⌝` into `Prop` at the end of a path, one
     cannot push a `Prop`-level existential quantifier across an unclosed
     `IProp GF` fancy update mid-execution without choosing the witness first.
     Skolemizing the angelic player's choices into a strategy function
     `strat : AngelicStrategy State := Nat → State → State` resolves this
     cleanly: `ReachesWithStrategy M strat p init n s tr out` steps
     deterministically to `strat n s` at `.choice .angelic branches` (or to
     `.stuck` if `¬ branches (strat n s)`), while still branching universally
     over all `s'` at `.choice .demonic branches`. The prover supplies
     `∃ strat : AngelicStrategy State` at the outer `Prop` level (or extracts it
     from `wpDualIProp` when ghost state is purely functional), and for that
     fixed `strat`, `ReachesWithStrategy` is a purely demonic reachability
     relation that closes via `Iris.step_fupdN_soundness_close` identically to
     `wpIProp_adequacy`. `optionC_strategy_angelic_trap_is_defined` verifies
     this on `angelicTrapMachine` using the constant strategy
     `strat := fun _ _ => 1`.

## Boundaries

To prevent future agents from over-extrapolating these findings, the following
boundaries are established by the evidence:

1. **Toolchain Pinning Between `iris-lean` Revisions (`known not to apply`
   without matching toolchain):**
   `iris-lean` tag `v4.34.1` (`04b7689c294bb1dd6401e2dd53b337871934ea47`)
   compiles cleanly under Anneal's current `leanprover/lean4:v4.34.1` toolchain,
   whereas `iris-lean` `main` HEAD (`fb21a8af4727bd42190072a5ed2836cbe9fb844e`)
   targets `leanprover/lean4:v4.35.0` and uses `v4.35.0` elaborator APIs in
   `Iris/IrisStepIndex/Elab.lean`. Do not point a `v4.34.1` Lake manifest at
   `iris-lean` `main` without pinning commit
   `04b7689c294bb1dd6401e2dd53b337871934ea47`.
2. **Non-Existence of a Standalone `LayerCake` Lean 4 Program-Logic Repository
   (`known not to apply`):**
   There is no Lean 4 program-logic repository named `LayerCake` on GitHub or
   Lean Reservoir; the CFML-style separation logic in the `verse-lab` suite is
   `verse-lab/splean` (`e24286f51bd9ee207197d47ec587d592cdfb0ddc`), and
   `Layercake.lean` in `Mathlib4` is a measure-theory theorem file.
3. **Unsoundness of `goens/lean-hoare` (`known not to apply`):**
   `goens/lean-hoare` (`aa2d88ae418d58ee22460a9097a2fad62c47eb38`) must not be
   cited or reused as a sound Hoare logic: its `TripleHolds.skip` and
   `TripleHolds.assign` rules in `Hoare/Logic.lean` leave the command `c : Com`
   unconstrained, and no soundness theorem connects `TripleHolds` to
   `Com.Step` or `Com.eval`.
4. **Incompatibility of `Loom`'s `WPGen` with `iris-lean`'s `IProp GF`
   (`unsupported`):**
   `verse-lab/loom`'s generic weakest-precondition generator (`WP/Gen.lean`)
   requires `[CCompleteLattice l]` on the assertion carrier `l`, which is
   unsupported by step-indexed `OFE`/`UPred`/`IProp` carriers.
5. **Single-Thread Weak-Memory Scope of `OwnLocInMem` in `R2IrisLeanProbe.lean`
   (`not examined` for multi-thread concurrent release/acquire invariants):**
   In `support/R2IrisLeanProbe.lean`, `OwnLocInMem` and `mirPointsTo` verify
   non-atomic memory reads and writes (`readNA`, `writeNA`) against the active
   thread's coherence view `curView` in `Trusted.MemState`. While `AnnealGF`
   includes `InvGpreS` (`Inv N P` and `FUpd`), multi-thread release/acquire
   message-passing protocols over `MemState.readAtomic` and
   `MemState.writeAtomic` were not mechanized in the Round 2 canary probe.

## Evidence

### 1. Primary Upstream Sources Inspected

All repositories, full 40-character commit hashes, tree hashes, and per-file
SHA-256 and Git blob SHA-1 digests are recorded in
`support/source-manifest.json`. Key source locations backing the findings:

- **`leanprover-community/iris-lean` (`04b7689c294bb1dd6401e2dd53b337871934ea47`
  and `fb21a8af4727bd42190072a5ed2836cbe9fb844e`):**
  - `Iris/lakefile.toml` (lines 1–53): `precompileLibrary = true` on `Iris`.
  - `Iris/Iris/BI/BIBase.lean` (lines 1–137), `Iris/Iris/BI/BI.lean` (lines
    1–401), `Iris/Iris/BI/Sbi.lean` (lines 1–85), `Iris/Iris/BI/Updates.lean`
    (lines 1–393), `Iris/Iris/BI/Notation.lean` (lines 1–171).
  - `Iris/Iris/Algebra/OFE.lean` (lines 1–866), `Iris/Iris/Algebra/CMRA.lean`
    (lines 1–948), `Iris/Iris/Algebra/IProp.lean` (lines 1–205),
    `Iris/Iris/Algebra/HeapView.lean` (lines 1–414).
  - `Iris/Iris/Instances/UPred/Instance.lean` (lines 1–1034, including
    `UPred.pure_soundness` and `UPred.bupd_soundness`).
  - `Iris/Iris/Instances/IProp/Instance.lean` (lines 1–194).
  - `Iris/Iris/Instances/Lib/FUpd.lean` (lines 1–509, including
    `WorldSatisfaction`, `InvPool`, `uFUpd`, `inv`, and
    `Iris.step_fupdN_soundness_close` at lines 473–509).
  - `Iris/Iris/Instances/Lib/GhostMap.lean` (lines 1–246) and
    `Iris/Iris/Instances/Lib/GhostVar.lean` (lines 1–106).
  - `Iris/Iris/ProofMode/Expr.lean` (lines 1–233, `Hyps` representation and
    `Hyps.mkSep`), `Iris/Iris/ProofMode/Tactics/Frame.lean` (lines 1–116), and
    `Iris/Iris/ProofMode/Tactics/Split.lean` (lines 1–115).
- **`verse-lab/velvet` (`836ed5a163b36c09081ed1d8aeecd3cec040f87e`) and
  `verse-lab/loom` (`78928abc9054b31d0bea85985496490baae95244`):**
  - `Loom/MonadAlgebras/NonDetT/Extract.lean` (lines 17–86): `NonDetT`,
    `pickCont`, `angelicCont`, and `MAlgOrdered` `iInf`/`iSup` interpretation.
  - `Loom/MonadAlgebras/WP/Gen.lean` (lines 1–120): `CCompleteLattice`
    requirement on `WPGen`.
  - `Velvet/Core/NonDet/WP.lean` and `Velvet/Core/VCGen/Driver.lean`.
- **`verse-lab/veil` (`eb458cb602d3cf9a19d8f5d8af21edcf27775c8e`):**
  - `Veil/DSL/Specification/ActionSpec.lean` (lines 1–145): relational
    `wp_action` / `wlp_action` and SMT obligation generation.
- **`verse-lab/splean` (`e24286f51bd9ee207197d47ec587d592cdfb0ddc`):**
  - `SPLean/Common/State.lean` (`Heap := Finmap Ptr Val`),
    `SPLean/Theories/HProp.lean` (`HProp := Heap → Prop`),
    `SPLean/Theories/XSimp.lean`, and `SPLean/Theories/WP1.lean`.
- **`verse-lab/Lentil` (`b3ca5e224fed1e09fb22daa45a0b61ec5685df76`):**
  - `Lentil.lean` (lines 1–374): small-step and big-step `WHILE` equivalence.
- **`goens/lean-hoare` (`aa2d88ae418d58ee22460a9097a2fad62c47eb38`):**
  - `Hoare/Logic.lean` (lines 7–29: unconstrained `c : Com` in `skip` and
    `assign`) and `Hoare/Examples/Sqrt.lean` (line 87: `sorry`).
- **`leanprover/cslib` (`82db31eec215b6843be6df283304cc02e736ddef`):**
  - `Cslib/Foundations/Semantics/LTS/{Basic,Bisimulation}.lean`,
    `Cslib/Foundations/Semantics/Flts/Basic.lean`, and
    `Cslib/Logics/HML/LogicalEquivalence.lean`.
- **`alexkeizer/QpfTypes` (`5b5dd4f83121662838b99d129b92f632f263c508`):**
  - `Qpf/Macro/Data.lean` (lines 75–160: `elabQpfCompositionBody`) and
    `Test/ITree.lean` (lines 17–24: unindexed `ITree.vis` workaround).
- **`joshlf/anneal` (`6e9bf8b54344c8283946387b7db8bf6879c4caf1` and
  `8e7ab324dc86e2086f301cdfc61a35c768896229`):**
  - `trusted/lean/Trusted/StepResult.lean` (lines 18–26, 95–165: `ChoiceKind`,
    `StepResult`, `ReachesPrefix`, `BehaviorOf`).
  - `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Language`, `SpecOn`,
    `WellFormedOn`, `WellFormed`).
  - `trusted/lean/Trusted/Memory.lean` (`View`, `MemState`, `readNA`,
    `writeNA`).
  - `trusted/lean/Trusted/MirSemantics.lean` (`MirState`, `evalMirStep`,
    `MirMachine`, `MirSem`, `EnsuresEqArg`).

### 2. Preserved Mechanized Artifacts in `support/`

#### 2.1 `support/anneal_step_wp_and_choicekind_probe.lean`

- **SHA-256:**
  `38a5f90f0d5269ce763079d496c7034e9deef31da62a39950393d57f193accf7`
- **Lines:** 1,674
- **Toolchain:** `leanprover/lean4:v4.34.1` (standalone, zero external
  dependencies, zero `sorry`, zero warnings)
- **Key mechanized declarations and theorems:**

| Declaration / Theorem | Lines | Description & Kernel Axiom Footprint |
| :--- | :--- | :--- |
| `Partial`, `Language`, `ChoiceKind`, `StepResult`, `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`, `RustcCompiler`, `VerificationResult` | 36–294 | Exact standalone replica of Anneal's Layer 0/1A/1B/3 trusted definitions |
| `ResourceAlgebra`, `Assertion`, `bupd`, `later`, `bupd_sound` | 300–524 | Step-indexed resource algebra and assertion logic (`∗`, `-∗`, `▷`, `\|==>`) in `Prop` |
| `wpAt`, `wpAt_mono`, `wpAt_frame` | 530–656 | Fuel-indexed weakest precondition over `SmallStepMachine`, consequence rule, and spatial frame rule |
| `wp_adequacy_reachesPrefix`, `wp_adequacy_specOn`, `wp_adequacy_wellFormedOn`, `wp_adequacy_wellFormed`, `wp_adequacy_compiler_verified` | 662–839 | All-prefix adequacy theorems bridging `wpAt` to `ReachesPrefix`, `SpecOn`, `WellFormed`, and `Compiler.Verified` (`[propext]`) |
| `angelic_choice_phantom_in_reachesPrefix`, `angelicTrapMachine`, `optionB_angelic_trap_is_ub` | 853–929 | Proof that `ChoiceKind.angelic` is a phantom parameter in `ReachesPrefix` and causes `angelicTrapMachine` to be `Partial.ub` (`[]` — zero axioms) |
| `StepResultA`, `SmallStepMachineA`, `ReachesPrefixA`, `reachesPrefixA_iff_reachesPrefix` | 933–1042 | Option A (demonic-only `StepResultA`) and exact equivalence to `ReachesPrefix` (`[]` — zero axioms) |
| `wpDualAt`, `SafePrefixWithPost`, `wpDualAt_sound_for_safePrefixWithPost` | 1048–1225 | Option C dual WP with existential `.angelic` choice and soundness for inductive `SafePrefixWithPost` (`[]` — zero axioms) |
| `GameHolds`, `GameBehaviorOf`, `wpDualAt_sound_for_gameHolds`, `wpDual_adequacy_specOn`, `optionC_angelic_trap_holds`, `optionC_angelic_trap_is_defined` | 1227–1311 | Option C fuel-indexed two-player game semantics, adequacy for `SpecOn`, and proof that `angelicTrapMachine` is defined and terminates normally |
| `AngelicStrategy`, `ReachesWithStrategy`, `StrategyBehaviorOf`, `optionC_strategy_angelic_trap_is_defined` | 1313–1400 | Option C Skolemized strategy-tree reachability and proof that `angelicTrapMachine` is defined via `strat := fun _ _ => 1` (`[propext]`) |
| `counterLoopProg`, `counterLoop_wellFormed` | 1406–1536 | Verification of an unbounded fuel-indexed counter loop via loop invariant `counterLoopInv` and `wp_adequacy_wellFormed` (`[propext]`) |
| `TwoCellRA`, `twoCellProg`, `twoCell_spec` | 1542–1654 | Spatial framing verification over a 2-cell exclusive resource algebra via `wpAt_frame` and `wp_adequacy_specOn` (`[propext]`) |

#### 2.2 `support/R2IrisLeanProbe.lean`

- **SHA-256:**
  `67772f157e86f81b996cfc4b990721d328d3096ee309740ee8f000ed33653d4b`
- **Lines:** 1,340
- **Toolchain:** `leanprover/lean4:v4.34.1` against `iris-lean@04b7689` and
  `joshlf/anneal@6e9bf8b` (zero `sorry`, zero warnings)
- **Key mechanized declarations and theorems:**

| Declaration / Theorem | Lines | Description & Kernel Axiom Footprint |
| :--- | :--- | :--- |
| `AnnealGF`, `instInvGpreS_AnnealGF`, `instGhostMapG_AnnealGF`, `instGhostVarG_AnnealGF` | 30–66 | Concrete 6-slot `BundledGFunctors` providing `InvGpreS` (`FUpd`/`Inv`), `GhostMapG` (`Nat ↦ MirVal`), and `GhostVarG` (`MirState`) |
| `OwnLocInMem`, `mirPointsTo`, `mirHeapInterp`, `mirPointsTo_lookup`, `mirPointsTo_exclusive`, `mirPointsTo_update` | 68–133 | Spatial points-to `loc ↦ₘ[γh]{dq} v` in `IProp AnnealGF` tied to `Trusted.MemState` coherence views (`curView`, `naWriteTs`, `naReadTs`) |
| `wpIProp`, `fupd_to_step_fupd`, `fupd_to_step_fupdN`, `fupd_step_fupdN_fupd`, `step_fupdN_fupd_to_succ`, `wpIProp_reachesPrefix` | 140–298 | Step-indexed `wpIProp` in `IProp GF` using `\|={⊤}[∅]▷=>` and preservation along `Trusted.ReachesPrefix` |
| `wpIProp_adequacy` | 302–340 | Adequacy theorem closing `IProp GF` + `FUpd` into `Trusted.BehaviorOf M p ≤ M.toLanguage.SpecOn pre post` via `Iris.step_fupdN_soundness_close` and `UPred.pure_soundness` (`[propext, Classical.choice, Quot.sound]`) |
| `wpIProp_mir_zero`, `wpIProp_mir_step`, `wpIProp_mir_terminated` | 348–406 | Deterministic `MirMachine` WP lifting lemmas in `IProp GF` |
| `idCopyBody`, `idCopyBody_verified_via_iris_lean`, `idCopyBody_wellFormed_via_iris_lean` | 408–495 | End-to-end verification of `pub fn id(x: usize) -> usize { x }` via `iris-lean` (`[propext, Classical.choice, Quot.sound]`) |
| `writeRead42Body`, `writeNA_of_ownLocInMem`, `readNA_of_ownLocInMem`, `writeRead42Body_verified_via_iris_lean`, `writeRead42Body_wellFormed_via_iris_lean` | 497–750 | End-to-end verification of `pub fn write_read_42(x: &mut usize) -> usize { *x = 42; *x }` using spatial points-to `loc ↦ₘ[γh] v` (`[propext, Classical.choice, Quot.sound]`) |
| `measure_decl`, `bench_iframe_inorder_{5,10,20,40}`, `bench_iframe_rev_{5,10,20,40}`, `bench_step_split_apply_{5,10,20,40}`, `bench_func_locals_{5,10,20,40}` | 756–1010 | 16-point IPM framing scaling benchmark suite ($N = 5, 10, 20, 40$) |
| `angelicTrapMachine`, `optionB_angelic_trap_is_ub`, `reachesPrefixA_iff_reachesPrefix`, `GameHolds`, `GameBehaviorOf`, `optionC_angelic_trap_holds`, `optionC_angelic_trap_is_defined`, `ReachesWithStrategy`, `StrategyBehaviorOf`, `optionC_strategy_angelic_trap_is_defined` | 1012–1340 | Mechanized `ChoiceKind.angelic` audit and Options A, B, and C over `Trusted.SmallStepMachine` |

## Revalidation

To revalidate the findings in this report cheaply without repeating the broad
multi-repository crawl:

1. **Re-verify the standalone `wpAt` + `ChoiceKind` probe (requires only Lean
   `v4.34.1`, ~3 seconds):**
   ```console
   ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 \
     reports/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy-2026/support/anneal_step_wp_and_choicekind_probe.lean
   ```
   Confirm exit code `0`, zero warnings, and that `#print axioms` reports only
   `[propext]` (and `Quot.sound` on `wpDualAt_sound_for_gameHolds` /
   `wpDual_adequacy_specOn`, or no axioms on the `ChoiceKind` equivalences).
2. **Re-verify the `iris-lean` `IProp` + `FUpd` + IPM scaling probe (~8 seconds
   once `iris-lean@04b7689` is built):**
   In a Lake workspace pinning `leanprover-community/iris-lean` at rev
   `04b7689c294bb1dd6401e2dd53b337871934ea47` (`subdir = "Iris"`) and Anneal's
   `Trusted` module at `6e9bf8b54344c8283946387b7db8bf6879c4caf1`, run:
   ```console
   ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake env lean -j1 -M2048 \
     reports/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy-2026/support/R2IrisLeanProbe.lean
   ```
   Confirm exit code `0`, `#print axioms` output
   `[propext, Classical.choice, Quot.sound]` on `wpIProp_adequacy`,
   `idCopyBody_verified_via_iris_lean`, and
   `writeRead42Body_verified_via_iris_lean`, and compare the `BENCHMARK | ...`
   log lines against the `heartbeats` and `numObjs` columns in Section 4.1.
3. **Check whether `iris-lean` IPM `Hyps.remove` still exhibits quadratic
   in-order proof-term growth on a newer `iris-lean` commit:**
   Diff `Iris/Iris/ProofMode/Expr.lean` (`Hyps`),
   `Iris/Iris/ProofMode/Tactics/Frame.lean`, and
   `Iris/Iris/ProofMode/Patterns/CasesPattern.lean` against commit
   `04b7689c294bb1dd6401e2dd53b337871934ea47`, or re-run `measure_decl` on
   `bench_iframe_inorder_{5,10,20,40}` and `bench_iframe_rev_{5,10,20,40}` to
   check whether `numObjs` still follows $5N^2 + 33N + 314$ vs. $79N + 165$.
4. **Check `Trusted/StepResult.lean` for `ChoiceKind` resolution:**
   Inspect `trusted/lean/Trusted/StepResult.lean` in `joshlf/anneal` to verify
   whether `ChoiceKind` has been removed (Option A) or whether `BehaviorOf` has
   been updated to `GameBehaviorOf` / `StrategyBehaviorOf` (Option C).
