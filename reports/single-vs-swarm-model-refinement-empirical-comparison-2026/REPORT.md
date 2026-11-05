# Single-Agent vs. Swarm Conceptual Model Refinement: Controlled Empirical Comparison on Anneal's MIR Verification Pipeline

## Summary

Single-agent conceptual model refinement (`model-refinement`) and multi-agent
adversarial model refinement (`swarm-model-refinement`) were evaluated head to
head on the same formal-methods refactoring target: simplifying and generalizing
Anneal's three-stage Rust Mid-level Intermediate Representation (MIR) extraction
and Lean 4 verification pipeline (`joshlf/anneal` implementation baseline
`572f1e80580daa4b052ce5646bb675484d9bb957` and architecture specification
`d79b0c070cf4115b523fe6ee62c1e72504de2254`).

The controlled experiment reveals a sharp structural dichotomy between
**macro-architectural simplification** and **micro-semantic soundness**:

1. **Macro-architectural convergence (`5 / 5` in both workflows):** Both the
   2-pass single-agent workflow (`M1`/`M2`/`M3` to `M3'`) and the 3-pass,
   12-agent swarm workflow (`Candidate 001` to `Candidate 003`) independently
   discovered the same five high-level architectural simplifications:
   eliminating `CaptureProfile` and multi-version capture subcrates (`M-1`),
   replacing five dead `TargetSem`/`BehaviorCodec` definitions with
   `Obligation.assumed` (`M-2`), breaking the `Terminator`/`MirBody` mutual
   induction via flat `BodyId` tables (`M-3`), replacing the 9-entry `beqCrate`
   lookup table with verified Stage 3 MIR lowering (`M-4`), and keeping
   first-order specification ASTs in `Mir.lean` with a static 8-line
   `Proof.lean` and demand-driven `.unsupported` capture (`M-5`).
2. **Micro-semantic and audit-boundary divergence (`0 / 12` in single-agent vs.
   `12 / 12` in swarm):** Across 12 concrete soundness, completeness, and
   `.olean` audit-boundary defects (`D-01` through `D-12`), single-agent
   `model-refinement` resolved `0 / 12`. Its final design `M3'` left 10 active
   defects in the proposed Trusted Computing Base (TCB) and avoided the
   remaining 2 second-order defects only because it omitted partial-move
   deinitialization and multi-step `Place` projections altogether. By contrast,
   `swarm-model-refinement` discovered and resolved all `12 / 12` defects by
   Pass 3 (`Candidate 003`).
3. **Second-order regression trap across iterative repairs:** Repairing complex
   semantic boundaries introduced new regressions before converging. In the
   swarm run, Pass-1 synthesis (`Candidate 001`) introduced 7 new boundary
   regressions (`9` active defects), and Pass-2 repair (`Candidate 002`) fixed 5
   defects but introduced 3 second-order regressions—most notably stepping
   compiler-inserted `Terminator.assert` failure to `.terminated .unwind`
   (`D-08`), which masked release-mode arithmetic wrapping undefined behavior
   (`UB`), and writing `ConstsTotal` with a vacuous implication antecedent
   (`D-05`). Reaching a zero-defect fixed point required three full
   synthesis-and-falsification rounds (`k = 3`) gated by a sealed holdout
   stitcher and newly spawned, unanchored fresh critics.

## Applicability

These findings apply to formal verification pipelines, compiler intermediate
representations, and high-assurance software architectures modeled in
interactive theorem provers:

- **Target repository (`joshlf/anneal`):**
  - Implementation baseline commit `572f1e80580daa4b052ce5646bb675484d9bb957`
    (`7,030` lines across `trusted/lean/Trusted/*.lean`,
    `trusted/rustc-capture/src/*.rs`, `trusted/audit/TrustedBoundary.lean`, and
    `trusted/cargo-anneal/src/lib.rs`, plus `4,837` lines across
    `theory/Anneal/*.lean`).
  - Design and skill baseline commit `d79b0c070cf4115b523fe6ee62c1e72504de2254`
    (`docs/architecture.md` at `366` lines, `skills/model-refinement/SKILL.md`
    at `307` lines, and `skills/swarm-model-refinement/SKILL.md` at `336`
    lines).
- **Pinned compiler and kernel toolchains:**
  - `rustc` `nightly-2026-03-15` at `rust-lang/rust` commit
    `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, specifically its
    `Runtime(PostCleanup)` MIR pass pipeline (`SimplifyConstCondition`,
    `RemoveDeadBlocks`), `Body::required_consts`, `Body::mentioned_items`,
    `TerminatorKind::Assert`, and `rustc_abi::Layout` size invariants.
  - Lean `v4.28.0` kernel environment and `.olean` syntax/import audit enforced
    by `trusted/audit/TrustedBoundary.lean` and `trusted/foundation-lock.json`.
- **Workflow selection criteria:** Use single-agent `model-refinement` when a
  task requires conceptual compression of a closed module or documentation with
  low semantic coupling. Use `swarm-model-refinement` whenever a design modifies
  an executable operational semantics, a compiler-to-prover translation
  boundary, a kernel syntax/import whitelist, or a backward simulation theorem
  whose invariants couple multiple subsystems.

## Findings

### Finding 1: Controlled Baseline and Convergence on Macro-Architectural Simplifications (`M-1` through `M-5`)

Basis: documentation, source, execution, derived

Both `model-refinement` and `swarm-model-refinement` were given the same target
codebase (`joshlf/anneal` at `572f1e80580daa4b052ce5646bb675484d9bb957`) and
architecture specification (`docs/architecture.md` at
`d79b0c070cf4115b523fe6ee62c1e72504de2254`). At the baseline commit, the
repository exhibited five macro-architectural tensions between its documented
three-stage design and its `simplify-trusted` implementation:

1. `docs/architecture.md` (`lines 38-47`, `69-72`, `206-298`) specified
   versioned capture subcrates (`rustc-capture-v1_85/`, `rustc-capture-v1_86/`)
   and a 3-tuple `CaptureProfile = (schema_version, rustc_version, SemProfile)`
   to parameterize Stage 2 semantics across compiler releases, whereas
   `toolchain-manifest.json` pinned a single `rustc` commit.
2. `trusted/lean/Trusted/MirSemantics.lean` (`lines 1045-1108`, `1131-1140`)
   defined five unprovable target-compilation constructs (`TargetArtifact`,
   `rustc`, `opaque TargetSem`, `TargetLang`, and `rustcCodec`) solely to state
   an `Obligation.compiles` wrapper that `defaultTrustPolicy` always waived.
3. `trusted/lean/Trusted/MirAst.lean` (`lines 193-260`) embedded recursive
   `MirBody` structures inside `Terminator.call`, `Rvalue.constBlock`, and
   `TCBItem`, forcing a `mutual inductive Terminator ... structure MirBody`
   block that prevented structural equality and required a 200-line fuel-bounded
   `beqMirBodyFuel 8` comparator in `theory/Anneal/MirLemmas.lean`
   (`lines 1-260`).
4. `theory/Anneal/MirLemmas.lean` (`lines 3752-3795`) defined `proveCrateOpt`
   as a rigid 9-entry whole-crate `beqCrate` lookup table (`idCopyEnsuresCrate`,
   `idCopyWfCrate`, `idMoveEnsuresCrate`, `idMoveWfCrate`,
   `allocPassthroughCrate`, `allocPassthroughWfCrate`,
   `pmeConcreteTransmuteCrate`, `inlineConstPmeCrate`, and
   `nonzeroLibraryCrate`), rejecting any crate outside those nine hard-coded AST
   shapes.
5. `docs/architecture.md` (`lines 88-114`, `300-355`) described Stage 1 as
   generating per-crate Lean specification theorems inside `Proof.lean`, whereas
   `trusted/cargo-anneal/src/lib.rs` (`lines 52-63`) and
   `trusted/rustc-capture/src/spec.rs` (`lines 1-156`) emitted a static 8-line
   `Proof.lean` (`Anneal.proveCrate Mir.crate rfl`) backed by first-order spec
   ASTs in `Mir.lean`.

Under the single-agent `model-refinement` workflow (`1` agent, `2` passes), Pass
1 explored three candidate architectures (`M1` heavy Stage 2 interpreter, `M2`
two-stage direct verification without Stage 3, and `M3` flat indexed Stage 2
plus Stage 3 MIR-to-MIR cleanup) and selected `M3`; Pass 2 performed a
self-critique pass yielding `M3'`. Under the `swarm-model-refinement` workflow
(`12` agents across `3` passes), a Coordinator/Synthesizer orchestrated three
divergent Architects ($\alpha$ Radical Minimizer, $\beta$ Structural
Generalizer, and $\gamma$ Pragmatic Incumbent Defender), four Challenger roles,
one sealed Holdout Stitcher, and three newly spawned unanchored Fresh Critics
(`001`–`003`).

| ID | Macro-Architectural Simplification | Baseline Location (`572f1e80` / `d79b0c07`) | Single-Agent `M3'` (Pass 2) | Swarm `Candidate 003` (Pass 3) |
| :--- | :--- | :--- | :--- | :--- |
| `M-1` | Eliminate `CaptureProfile` and multi-version `rustc-capture-v1_X` subcrates in favor of one pinned toolchain and `LayoutEnv` | `docs/architecture.md:38-47, 206-298` | Converged (`TargetLayout` record, single `rustc-capture` binary) | Converged (`LayoutEnv = { ptrBits, maxTypeSize }`, single `rustc-capture` binary) |
| `M-2` | Remove dead `TargetArtifact`, `rustc`, `opaque TargetSem`, `TargetLang`, and `rustcCodec` scaffolding via `Obligation.assumed` | `Trusted/MirSemantics.lean:1045-1108`; `Trusted/Refinement.lean:231-288` | Converged (`Obligation.assumed (id : TCBItem)`) | Converged (`Obligation.assumed (item : TCBItem)`) |
| `M-3` | Break `Terminator`/`MirBody` mutual induction and remove `MirBody` from `TCBItem` via flat `BodyId` tables (`Crate.bodies`) | `Trusted/MirAst.lean:193-260`; `theory/Anneal/MirLemmas.lean:1-260` | Converged (`BodyId` index table, `TCBItem.rustcLowering String BodyId`) | Converged (`BodyId` index table `Crate.bodies : List BodyDecl`, `TCBItem.rustcLowering FnId BodyId`) |
| `M-4` | Replace 9-entry `proveCrateOpt` `beqCrate` lookup table with compositional per-function verification and Stage 3 `lowerBody` | `theory/Anneal/MirLemmas.lean:3752-3795`; `docs/architecture.md:158-204` | Converged (`lowerBody : MirBody -> MirBody` + `lowerBody_simulates`) | Converged (in-place `lowerBody` + block-entry `lowerBody_simulates`) |
| `M-5` | First-order specification ASTs in `Mir.lean`, static 8-line `Proof.lean`, and syntax-total `.unsupported` fail-closed capture | `trusted/rustc-capture/src/spec.rs:1-156`; `trusted/cargo-anneal/src/lib.rs:52-63` | Converged (first-order `SpecExpr`, static `Proof.lean`, `.unsupported` nodes) | Converged (first-order `SpecExpr`/`InvariantSpec`/`RequiresSpec`/`PostSpec`, static `Proof.lean`, `.unsupported` nodes) |

Both workflows achieved `5 / 5` (`100%`) agreement on the macro-architectural
decomposition. When conceptual redundancy is visible in type signatures and
module boundaries—such as five definitions feeding an `opaque` function mapped
to `False`, or a 9-entry `if/else` chain in `proveCrateOpt`—a single agent
applying the core `model-refinement` operations (eliminate, inline, unify,
re-index) identifies the same macro-level design as a multi-agent swarm.

### Finding 2: Head-to-Head Asymmetry on Micro-Semantic, Soundness, Completeness, and Audit-Boundary Defects (`D-01` through `D-12`)

Basis: source, execution, derived

Whereas both workflows converged on macro-architecture, they diverged
completely on semantic soundness, compiler fidelity, and TCB auditability.
Across 12 concrete defects (`D-01` through `D-12`) spanning partial moves,
polymorphic Compile-Time Function Evaluation (CTFE), Post-Monomorphization
Errors (PMEs), ADT representation invariants, compiler overflow assertions,
multi-configuration MIR determinism, `TrustedBoundary.lean` `.olean` rules,
nested frame lifetimes, and Stage 3 simulation proofs, single-agent
`model-refinement` resolved `0 / 12` (`10` active defects in `M3'`, plus `2`
untriggered second-order defects whose prerequisite `Place` machinery `M3'`
omitted). `swarm-model-refinement` identified and resolved all `12 / 12`
defects by Pass 3 (`Candidate 003`).

| ID | Defect Summary | Category | Origin | Baseline Location (`572f1e80`) | Single-Agent `M3'` Status | Swarm Pass Caught / Resolved | Discovering Swarm Mechanisms |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `D-01` | `extract.rs` lowers `Operand::Move(_1.0)` to non-destructive `Rvalue.field0`; `M3'` omits partial-move deinitialization | Soundness | Baseline codebase | `extract.rs:458-485`; `MirSemantics.lean:589-597` | **Missed** (`Rvalue.field` never deinitializes moved sub-place) | Caught Pass 0 / Resolved Pass 2–3 | Architect $\beta$, `D5`, `H1` (`S4`), Challenger 1 (`F1.1`), `fresh-critic-001` (`C3`) |
| `D-02` | Pass-1 partial-move over-correction / unchecked whole-aggregate read (`Copy(_1)`, `Move(_1)`, `&_1`) after moving `_1.0` | Soundness | Swarm Pass-1 regression | `MirSemantics.lean:491-507` | **Unaddressed prerequisite** (no `Place` or `.uninit` sub-tree model) | Caught Pass 1 / Resolved Pass 2 | Challenger 1 (`F1.1`), Stitcher `H1` (`S4`), `fresh-critic-001` (`C3`) |
| `D-03` | Intermediate `.deref` hop `(*r).1` on partially-moved struct and `Rvalue.ref` borrow bypassing `isFullyInitFuel` | Soundness | Swarm Pass-2 regression | `MirSemantics.lean:598-635` | **Unaddressed prerequisite** (no `.deref` projection chain) | Caught Pass 2 / Resolved Pass 3 | Challenger 1 (`P2.2`), `fresh-critic-002` (`FC2-3`), `H1`/`H5` |
| `D-04` | Polymorphic dead-branch PME (`if false { Fail::<T>::C }`) erased from `required_consts`; requires `Body::mentioned_items` + two-stage `ConstsTotal` / `MonoAdmitted` | Soundness | Baseline + Single/Swarm Pass 1 | `extract.rs:140-210`; `MirSemantics.lean:946-960` | **Introduced / Missed** (omitted `mentioned_items`; collapsed to single-stage `ConstsEvaluated`) | Caught Pass 0 & 1 / Resolved Pass 2–3 | Architect $\beta$, Architect $\gamma$, `D8`, `H3`/`H5` (`S2`), Challenger 1 (`F1.3`), `fresh-critic-001` (`C2`) |
| `D-05` | Vacuous `ConstsTotal` implication (`mapOpt evalTyByteSize = some argSizes -> ...`) on `.unsupported` types and `instantiateBody c cid []` empty-arg bug | Soundness | Swarm Pass-2 regression | `MirSemantics.lean:946-960` | **Missed** (no generic `typeArgs` substitution or layout totality in `ConstsEvaluated`) | Caught Pass 2 / Resolved Pass 3 | Challenger 1 (`P2.1`), `fresh-critic-002` (`FC2-1`), `H3`/`R3` |
| `D-06` | Unconstrained `tySizes > isize::MAX` violating Rust `Layout` invariant and unbounded `MirVal.usize > usize::MAX` bypassing bounds | Soundness | Baseline codebase | `MirSemantics.lean:367-371, 946-967` | **Missed** (unconstrained `tySizes : Nat -> Nat` and unbounded `.usize`) | Caught Pass 0 & 1 / Resolved Pass 2 | Architect $\alpha$, Architect $\beta$, `D8`, `H9`, `R1`, Challenger 1 (`F1.3`), `fresh-critic-001` (`C8`) |
| `D-07` | `AdmissibleAdtInv` `defaultAdtInv` failure on nested structs (`Outer { pub inner: NonZero }`) and Pass-1 `FieldAccess` omission | Soundness | Baseline + Swarm Pass 1 | `MirSemantics.lean:1000-1007` | **Missed** (kept `defaultAdtInv` field check on nested ADTs) | Caught Pass 0 & 1 / Resolved Pass 2 | Architect $\beta$, `D7`, `H4` (`S1b`), Challenger 2 (`F2.2`), `fresh-critic-001` (`C1`) |
| `D-08` | Compiler-inserted `TerminatorKind::Assert` stepping to `.terminated .unwind` instead of `.failed`, masking release-mode wrapping UB in `bad_overflow` | Soundness | Swarm Pass-2 regression | `extract.rs:580-630`; `MirSemantics.lean:772-775` | **Missed** (did not model `Terminator.assert` vs. `Callee.panic`) | Caught Pass 2 / Resolved Pass 3 | Challenger 1 (`P2.3`), `fresh-critic-002` (`FC2-5`), `H3`/`R2` |
| `D-09` | `-C overflow-checks` variance across `CONFIGS` rejecting every `+`/`-`/`*` and `#[cfg(debug_assertions)]` shifting raw `LocalDefId` indices | Completeness / Determinism | Baseline + Single/Swarm Pass 1 | `main.rs:325-328`; `items.rs:1-120` | **Introduced / Missed** (kept `CONFIGS` variance and raw `LocalDefId` index as `BodyId`) | Caught Pass 1 & 2 / Resolved Pass 3 | Architect $\gamma$, Challenger 2 (`F2.4`), `fresh-critic-001` (`C7`), `fresh-critic-002` (`FC2-5`) |
| `D-10` | `TrustedBoundary.lean` rejects `deriving DecidableEq, Repr`, `Init.Data.String.Basic`, unary `-`, exponentiation `^`, and `∉` in `SourceRole.trusted` | Audit Boundary | Single `M3'` + Swarm Pass 1 & 3 | `TrustedBoundary.lean:206-290, 510-590` | **Introduced** (relied on `deriving BEq/DecidableEq` and forbidden syntax) | Caught Pass 1 & 3 / Resolved Pass 2–3 | Architect $\gamma$, Challenger 2 (`F2.1`), Challenger 4 (`C10`), Stitcher `H6` (`S6`), `fresh-critic-001` (`C8`, `C10`), `fresh-critic-003` |
| `D-11` | Frame-relative `returnRefsOk` and `resolveLocal` bounds rejecting valid nested helpers (`fn id_ref(r: &usize) -> &usize { r }`) when `s.frameId > 0` | Completeness | Swarm Pass-1 & Pass-2 regressions | `MirSemantics.lean:320-348, 742-764` | **Missed** (did not specify multi-frame `returnRefsOk` across nested calls) | Caught Pass 1 & 2 / Resolved Pass 3 | Challenger 1 (`F1.2`, `P2.2`), Stitcher `H2` (`S3`), `fresh-critic-001` (`C5`), `fresh-critic-002` (`FC2-2`) |
| `D-12` | Root `Terminator.return_` PC-canonicalization in `MirReturn.state` and `storageLive`/`storageDead` preservation required by `lowerBody_simulates` | Soundness | Single `M3'` + Swarm Pass 1 & 2 | `MirSemantics.lean:740-745, 1011-1016` | **Introduced** (`lowerBody` stripped `nop`/`StorageLive` without canonicalizing `MirReturn.state`) | Caught Pass 1 & 2 / Resolved Pass 2–3 | Architect $\beta$, Challenger 2 (`F2.3`), Challenger 3 (`F3.1`), Stitcher `H8` (`S5`), `fresh-critic-001` (`C9`), `fresh-critic-002` (`FC2-4`) |

#### Group A: Partial Moves, Sub-Place Deinitialization, and Projection Chains (`D-01`, `D-02`, `D-03`)

- **Defect `D-01` (Baseline `extract.rs` partial-move soundness bug and `M3'`
  omission):** In `trusted/rustc-capture/src/extract.rs` (`lines 458-485`), both
  `mir::Operand::Copy(p)` and `mir::Operand::Move(p)` on field `0` of a local
  struct are lowered to the identical `ir::Rvalue::Field0(local_index(l))`
  constructor. In `trusted/lean/Trusted/MirSemantics.lean` (`lines 589-597`),
  evaluating `.assign dst (.field0 src)` reads `s.locals src.index` without
  modifying `src`:
  ```rust
  struct Pair(NonCopy, NonCopy);
  let _a = move (_1.0);
  let _b = move (_1.0); // Illegal second move of _1.0!
  ```
  Because `_1` remains `some (.adt id inner)`, a second `Move(_1.0)` or a
  whole-struct `Move(_1)` succeeds instead of stepping to `.failed`.
  Single-agent `M3'` replaced `.field0` with
  `Rvalue.field (src : LocalId) (fieldIdx : Nat)` without introducing `Place`
  projections or leaf-level `.uninit`, leaving `Operand::Move(_1.0)`
  non-destructive.
- **Defect `D-02` (Swarm Pass-1 partial-move over-correction vs. whole-aggregate
  reads):** If `Operand::Move(_1.0)` overwrote root local `_1` with `.uninit`
  (or `none`), any subsequent read of the unmoved sibling field `_1.1` (`D5` /
  `H1`) would falsely fail. To preserve sibling field reads, Swarm `Candidate
  001` introduced `Place = { local : LocalId, proj : List ProjElem }`,
  `MirVal.uninit`, and path-sensitive `updateProj`, setting `_1` to
  `.adt id [.uninit, v1]`. However, `Candidate 001`'s `evalProjFuel` only
  checked for `.uninit` at the top constructor (`| _ + 1, .uninit, _ => none`).
  When evaluating whole-struct `Operand.copy ⟨1, []⟩`, `Operand.move ⟨1, []⟩`,
  `Stmt.placeMention ⟨1, []⟩`, or `Rvalue.ref ⟨1, []⟩`, the empty projection arm
  `| _ + 1, v, [] => some v` returned `some (.adt id [.uninit, v1])`! Challenger
  1 (`F1.1`), the Holdout Stitcher (`H1` / `S4`), and `fresh-critic-001` (`C3`)
  independently caught this hole. Pass 2 (`Candidate 002`) fixed direct reads by
  defining a total, fuel-bounded `MirVal.isFullyInitFuel (depthFuel c) v` check
  that recursively rejects `.uninit` anywhere inside `.adt` or `.tuple` trees at
  the terminal `[]` arm of `evalProjFuel`, and by requiring
  `evalPlace c s place = some _` in `Rvalue.ref` and `Stmt.placeMention`.
- **Defect `D-03` (Intermediate `.deref` hop on partially-moved struct):** In
  Pass 2 (`Candidate 002`), the `.deref :: rest` arm of `evalProjFuel` resolved
  a reference `.ref targetFrameId gen root targetProj` by concatenating
  `targetProj ++ rest` and recursing:
  ```lean
  -- Candidate 002 bug: skips isFullyInitFuel on the dereferenced aggregate *r
  evalProjFuel c s fuel rootVal (targetProj ++ rest)
  ```
  `fresh-critic-002` (`FC2-3`) and Challenger 1 (`P2.2`) demonstrated that if
  `r = &_1` (`targetProj = []`), `_1.0` is subsequently moved (`_1 = .adt id
  [.uninit, v1]`), and the program evaluates `(*r).1` (`rest = [.field 1]`),
  concatenating `[] ++ [.field 1]` checks `isFullyInitFuel` only on the leaf
  `v1` rather than on the dereferenced intermediate aggregate `*r` (`_1`). Pass
  3 (`Candidate 003`) resolved `D-03` by first evaluating
  `evalProjFuel c s fuel rootVal targetProj` to `some targetVal` (which enforces
  `isFullyInitFuel` on `targetVal` at the end of `targetProj`) before projecting
  `rest` from `targetVal`.

#### Group B: Polymorphic CTFE, Post-Monomorphization Errors, and Layout Bounds (`D-04`, `D-05`, `D-06`)

- **Defect `D-04` (Polymorphic dead-branch PME hole and two-stage `ConstsTotal`
  vs. `MonoAdmitted`):** In `rustc`
  (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), dead-branch constant references
  such as:
  ```rust
  pub fn dead_branch_pme<T>() {
      if false {
          let _ = Fail::<T>::C;
      }
  }
  ```
  have their dead basic blocks removed by `SimplifyConstCondition` and
  `RemoveDeadBlocks` before `Runtime(PostCleanup)`, which also drains
  `Body::required_consts`. However, `rustc`'s monomorphization collector still
  evaluates items recorded in `Body::mentioned_items` and rejects failing
  generic instantiations at compile time. Baseline `extract.rs` (`lines
  140-210`) only inspected `required_consts`, missing dead-branch PMEs.
  Single-agent `M3'` not only missed `Body::mentioned_items`, but also collapsed
  `MirSemantics.lean`'s two-stage `ConstsTotal` and `MonoAdmitted` predicates
  (`lines 946-960`) into a single-stage `ConstsEvaluated` predicate. Swarm
  `Candidate 001` added `MentionedItem` capture (from Architect $\beta$), but
  likewise collapsed `ConstsTotal` and `MonoAdmitted` into a single
  `∀ tySizes, ExecNormal` check. Challenger 1 (`F1.3`), Stitcher (`H3`/`H5`,
  `S2`), and `fresh-critic-001` (`C2`) proved that a single universal
  `ExecNormal` predicate makes every conditional PME guard
  (`const { assert!(core::mem::size_of::<T>() == 8); }`) unverifiable: for
  `tySizes 0 = 4`, the constant panics (`Terminator.panic` / `Callee.panic`
  $\to$ `.terminated .unwind`), which falsifies `ExecNormal` and empties
  `initMirState` for all `tySizes`! Pass 2 and Pass 3 restored the two-stage
  split over transitive `ReachableMentioned`:
  1. `ConstsTotal c body`: for *all* `ValidTySizes c tySizes`, every transitive
     mentioned constant either succeeds (`ConstSucceeds`) or panics cleanly
     (`ConstUnwinds`), never stepping to `.failed` or diverging; and
  2. `MonoAdmitted c s.tySizes body`: at the *active* monomorphization
     `s.tySizes`, every transitive mentioned constant succeeds (`ConstSucceeds`)
     and every `MentionedItem.tyLayout` evaluates to `some sz`.
- **Defect `D-05` (Vacuous `ConstsTotal` implication and `instantiateBody`
  empty-arg bug in Pass 2):** When repairing `ConstsTotal` in Pass 2
  (`Candidate 002`), the synthesizer wrote:
  ```lean
  -- Candidate 002 bug: implication antecedent + empty typeArgs []
  ∀ argSizes, mapOpt (evalTyByteSize c tySizes) typeArgs = some argSizes →
    ∃ constBody, instantiateBody c cid [] = some constBody ∧
      (ConstSucceeds c tySizes argSizes constBody ∨
       ConstUnwinds c tySizes argSizes constBody)
  ```
  Challenger 1 (`P2.1`) and `fresh-critic-002` (`FC2-1`) caught two critical
  flaws in this formula: first, placing `mapOpt (evalTyByteSize c tySizes)
  typeArgs = some argSizes` on the left-hand side of `→` made `ConstsTotal`
  vacuously `True` whenever `typeArgs` contained `.unsupported` or an
  overflowing array `[T; N]` (`evalTyByteSize = none`); second, passing `[]` to
  `instantiateBody c cid []` caused every generic constant
  (`b.typeParamCount > 0`) to fail `typeArgs.length == b.typeParamCount`
  (`none`), making `ConstsTotal` `False` for all generic constants! Pass 3
  (`Candidate 003`) replaced the implication with a positive existential
  conjunction (`∃ argSizes constBody, mapOpt (evalTyByteSize c tySizes)
  typeArgs = some argSizes ∧ instantiateBody c cid typeArgs = some constBody ∧
  ...`) and required `∃ sz, evalTyByteSize c tySizes ty = some sz` for
  `.tyLayout ty`.
- **Defect `D-06` (Unconstrained `tySizes > isize::MAX` and unbounded
  `MirVal.usize > usize::MAX`):** Baseline `Trusted/MirSemantics.lean` left
  `tySizes : Nat → Nat` unconstrained above `isize::MAX` (`line 947`) and
  defined `validStep | .usize, .usize _ => True` (`line 370`), admitting
  mathematical naturals $v \ge 2^{64}$ as valid `usize` inputs and type sizes
  exceeding `rustc_abi::Layout`'s `isize::MAX` ceiling. Single-agent `M3'`
  inherited both omissions. Swarm Architects $\alpha$ and $\beta$, along with
  `D8`, `H9`, and `R1`, introduced `LayoutEnv = { ptrBits : Nat, maxTypeSize :
  Nat }`, bounded `MirVal.usize val` by `val ≤ c.layout.usizeMax` in
  `validStep`, and constrained `ConstsTotal` and `initMirState` by
  `ValidTySizes c tySizes` (`∀ idx, tySizes idx ≤ c.layout.maxTypeSize`).

#### Group C: Representation Invariants, Overflow Assertions, and Multi-Config Determinism (`D-07`, `D-08`, `D-09`)

- **Defect `D-07` (`AdmissibleAdtInv` `defaultAdtInv` failure on nested structs
  and Pass-1 `FieldAccess` omission):** Baseline `Trusted/MirSemantics.lean`
  (`lines 1000-1007`) defined `AdmissibleAdtInv` by checking whether every
  struct with `allFieldsPubSafe = true` satisfies `adtInv decl.id inner`
  whenever its payload satisfies `inner.valid adts defaultAdtInv s 0 payload`.
  Evaluating the field under `defaultAdtInv` strips representation invariants
  from all nested ADTs! Consider Holdout `H4`:
  ```rust
  pub struct NonZero(usize); // private field 0, invariant: self.0 != 0
  pub struct PublicWrapper { pub inner: NonZero } // all fields pub!
  ```
  Safe code can construct `PublicWrapper { inner }` directly, so
  `allFieldsPubSafe = true`, but safe code can only supply a `NonZero` value
  that already satisfies `NonZero`'s private invariant (`inner.0 != 0`). Under
  `defaultAdtInv`, `inner = NonZero(0)` is treated as valid, making any
  invariant on `PublicWrapper` that depends on `inner.0 != 0` unprovable.
  Single-agent `M3'` kept the baseline `defaultAdtInv` formulation. Swarm
  `Candidate 001` initially erred in the opposite direction by dropping
  `FieldAccess` and `InvariantSpec` from `AdtDecl` (`C1`, `F2.2`, `S1b`). Pass 2
  and Pass 3 restored `FieldAccess` and `InvariantSpec` and stratified
  `AdmissibleAdtInv` so each field of a public-fields struct is checked under
  the full crate `validFuel c adtInv s 0 0 (depthFuel c)`.
- **Defect `D-08` (Compiler-inserted `TerminatorKind::Assert` stepping to
  `.unwind` instead of `.failed`):** In Pass 2 (`Candidate 002`), while trying
  to make `const { assert!(size_of::<T>() == 8); }` unwind under `H3`, the
  synthesizer changed `Terminator.assert` failure from `.failed` to
  `.terminated .unwind`. Challenger 1 (`P2.3`) and `fresh-critic-002` (`FC2-5`)
  proved that this introduced a severe soundness hole for runtime functions:
  ```rust
  pub unsafe fn bad_overflow(x: usize) -> usize {
      let y = x + 1;
      if y == 0 {
          unsafe { core::hint::unreachable_unchecked() }
      } else {
          y
      }
  }
  ```
  Under `-C overflow-checks=on`, `x + 1` lowers to `Rvalue.checkedBinOp .add`
  followed by `TerminatorKind::Assert { cond, expected: true, .. }`. Because
  `isSafe` permits `.terminated .unwind` (`TerminationKind.unwind` is a clean
  panic, not UB), stepping `Terminator.assert` failure to `.terminated .unwind`
  allows `bad_overflow` to verify as safe (unwinding on `x = usize::MAX`),
  whereas in `--release` builds (`-C overflow-checks=off`) `usize::MAX + 1`
  wraps to `0` and executes `unreachable_unchecked()` UB! Furthermore, in
  `rustc`, user `assert!(...)` inside `const { ... }` lowers to `SwitchInt` +
  `core::panicking::panic` (`Callee.panic`), not `TerminatorKind::Assert`. Pass
  3 (`Candidate 003`) resolved `D-08` by stepping `Terminator.assert` failure
  strictly to `.failed` and `Callee.panic` to `.terminated .unwind`.
- **Defect `D-09` (`-C overflow-checks` variance across `CONFIGS` and
  `#[cfg(debug_assertions)]` shifting `LocalDefId`):** Baseline
  `trusted/rustc-capture/src/main.rs` (`lines 325-328`) ran `rustc` twice—under
  `("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"])` and
  `("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"])`—and
  required byte-identical `Mir.lean` output. `fresh-critic-002` (`FC2-5`) noted
  that any crate containing `+`, `-`, or `*` emits `AddWithOverflow` returning
  `(T, bool)` plus `TerminatorKind::Assert` when overflow checks are on vs.
  plain `Add` when off, causing every arithmetic crate to fail capture with
  `ConfigMismatch`! In addition, Challenger 2 (`F2.4`) and `fresh-critic-001`
  (`C7`) showed that keying `BodyId` by raw `LocalDefId.local_def_index` (as
  both single-agent `M3'` and Swarm `Candidate 001` did) shifts `BodyId`
  numbers whenever `#[cfg(debug_assertions)]` defines an uncalled helper item.
  Pass 3 (`Candidate 003`) pinned `-C overflow-checks=on -Z mir-preserve-ub` in
  both `CONFIGS` passes (varying only `-C debug-assertions=on` vs. `off`), added
  `MirTy.tuple` and `MirVal.tuple` for `CheckedBinOp`, and interned dense
  0-based `BodyId`/`AdtId`/`SpanId` in deterministic pre-order reachability
  traversal from `Crate.fns`.

#### Group D: TCB Audit Whitelist, Nested Call Reference Lifetimes, and Stage 3 Simulation (`D-10`, `D-11`, `D-12`)

- **Defect `D-10` (`TrustedBoundary.lean` syntax and `.olean` import
  rejections):** `trusted/audit/TrustedBoundary.lean` (`lines 206-290`,
  `510-590`) enforces two mechanical checks on `SourceRole.trusted`:
  1. Only modules listed in `trusted/foundation-lock.json` (`Init.Core`,
     `Init.Data.List.Basic`, `Init.Data.Option.Basic`, etc.—excluding
     `Init.Data.String.Basic`) may appear in the transitive `.olean` import
     graph.
  2. Every file in `trusted/lean/` is parsed and checked against closed syntax
     allowlists: `allowedCommandSyntaxKinds` (which excludes `derivingClass` at
     `line 218`) and `allowedNotationSyntaxKinds` (`lines 274-280`, which
     excludes unary negation `` `«term-_» ``, exponentiation `` `«term_^_» ``,
     and not-in notation `` `«term_∉_» ``).
  Single-agent `M3'` assumed `BEq` and `DecidableEq` could be derived on
  `MirBody` once the mutual inductive cycle was broken. Swarm `Candidate 001`
  avoided `deriving`, but imported `Init.Data.String.Basic` and wrote
  `-(Int.ofNat n)` and `2 ^ (c.layout.ptrBits - 1) - 1`; those were caught in
  Pass 1 by Challenger 2 (`F2.1`), Stitcher (`H6` / `S6`), and
  `fresh-critic-001` (`C8`, `C10`). Even in Pass 3, an initial draft of
  `NoDupIds` used `x ∉ xs`, which `fresh-critic-003` (Section 1.2 item 1) caught
  against `TrustedBoundary.lean:274-280` (`allowedNotationSyntaxKinds` admits
  `` `«term_∈_» `` at `line 279` but excludes `` `«term_∉_» ``) and replaced
  with `(x ∈ xs → False)`.
- **Defect `D-11` (Frame-relative `returnRefsOk` and `resolveLocal` bounds):**
  When a function returns a value containing a reference `.ref targetFrameId gen
  root targetProj`, `evalMirTerminator` checks `retVal.returnRefsOk`. In Pass 1
  (`Candidate 001`), `resolveRefLocal` checked `root.index <
  activeBody.localCount`, which rejected all caller-owned synthetic referents
  allocated at `root.index ≥ rootBody.localCount` (`F1.2`, `C5`). In Pass 2
  (`Candidate 002`), `returnRefsOk` removed that bound in `resolveLocal` but
  hardcoded `targetFrameId = 0 ∧ b.localCount ≤ root.index` for all returns.
  Challenger 1 (`P2.2`), Stitcher (`H2` / `S3`), and `fresh-critic-002`
  (`FC2-2`) showed that when a nested callee (`s.frameId = 1`) executes:
  ```rust
  fn id_ref<'a>(r: &'a usize) -> &'a usize { r }
  pub fn caller(x: usize) -> usize { let p = id_ref(&x); *p }
  ```
  the caller's local `x` lives at `targetFrameId = 0, root.index = 1`. Inside
  `id_ref` (`b.localCount = 2`), `b.localCount ≤ root.index` (`2 ≤ 1`) evaluates
  to `false`, causing a valid helper return to step to `.failed`! Pass 3
  (`Candidate 003`) made `MirVal.returnRefsOk` a computable `Bool` that branches
  on `s.frameId == 0`:
  - At root return (`s.frameId == 0`): requires `targetFrameId == 0 && decide
    (localCount ≤ root.index)`.
  - At nested callee return (`s.frameId > 0`): requires `decide (targetFrameId <
    s.frameId)` (preventing dangling references to the dying callee frame
    `s.frameId` while allowing references into any caller frame `0 .. s.frameId
    - 1`).
- **Defect `D-12` (Root `Terminator.return_` PC-canonicalization in
  `MirReturn.state` and in-place `lowerBody`):** At root return (`s.stack =
  []`), baseline `Trusted/MirSemantics.lean` (`line 744`) returned
  `.terminated (.normal ⟨retVal, s⟩)`, embedding the full `MirState` `s` inside
  `MirReturn.state` so `EnsuresRetLibInv` (`lines 1011-1015`) can evaluate
  `r.value.valid adts adtInv r.state body.localCount body.retTy`. Both
  single-agent `M3'` and Swarm `Candidate 001` proposed a Stage 3 `lowerBody`
  pass that strips `Stmt.nop` (and in `M3'` / `Candidate 001`,
  `Stmt.storageLive` / `Stmt.storageDead`) and coalesces `.goto` chains, paired
  with a backward simulation theorem `lowerBody_simulates`. Challenger 2
  (`F2.3`), Challenger 3 (`F3.1`), Stitcher (`H8` / `S5`), and
  `fresh-critic-001` (`C9`) proved that `lowerBody_simulates` was mathematically
  false in both `M3'` and `Candidate 001`: removing `Stmt.nop` changes the
  terminal `s.stmtIdx` at `Terminator.return_`, coalescing blocks changes
  `s.block`, and removing `storageLive`/`storageDead` changes `s.localGens`, so
  the terminal `MirReturn` records `⟨retVal, s_lowered⟩ ≠ ⟨retVal, s_raw⟩`!
  Furthermore, in Pass 2 (`Candidate 002`), `fresh-critic-002` (`FC2-4`) noted
  that stating `lowerBody_simulates` for arbitrary mid-block states `s` fails if
  `s.stmtIdx` points past the shortened statement list of `lowerBody b`. Pass 3
  (`Candidate 003`) resolved `D-12` completely by:
  1. Canonicalizing the root return state in `evalMirTerminator` via
     `{ s with block := 0, stmtIdx := 0, curBody := none }`;
  2. Keeping `Stmt.storageLive` and `Stmt.storageDead` in `lowerBody` (stripping
     only `Stmt.nop` and `Stmt.placeMention (LocalId, [])`) and updating blocks
     in place so `b.blocks.length` and `s.localGens` are preserved; and
  3. Gating `lowerBody_simulates` with the block-entry precondition
     `hEntry : s.stmtIdx = 0 ∧ s.curBody = none`.

### Finding 3: Mechanism-by-Mechanism Attribution in `swarm-model-refinement`

Basis: documentation, execution, derived

The 12-defect gap between single-agent `model-refinement` and
`swarm-model-refinement` is explained by four distinct mechanisms in the swarm
protocol (`skills/swarm-model-refinement/SKILL.md` at
`d79b0c070cf4115b523fe6ee62c1e72504de2254`). Each mechanism caught defects that
the other mechanisms missed:

```
+-----------------------------------------------------------------------------+
|                    SWARM-MODEL-REFINEMENT TOPOLOGY                          |
+-----------------------------------------------------------------------------+
|                                                                             |
|  Pass 0: Divergent Exploration & Holdout Audit                              |
|  +-------------------+  +-------------------+  +-------------------+        |
|  | Architect Alpha   |  | Architect Beta    |  | Architect Gamma   |        |
|  | (Minimizer:       |  | (Generalizer:     |  | (Incumbent Def.:  |        |
|  |  M-1, M-2, M-3,   |  |  D-01, D-04,      |  |  D-04, D-09,      |        |
|  |  D-06)            |  |  D-07, D-12)      |  |  D-10)            |        |
|  +---------+---------+  +---------+---------+  +---------+---------+        |
|            \                      |                      /                  |
|             v                     v                     v                   |
|        +-----------------------------------------------------+              |
|        | Coordinator / Synthesizer (Candidate 001 -> 002 -> 003)            |
|        +-----------------------------------------------------+              |
|                  |                 ^                 |                      |
|                  v                 |                 v                      |
|  +-----------------------+  +------+------+  +---------------------------+  |
|  | 4 Challenger Roles    |  | Sealed      |  | Unanchored Fresh Critics  |  |
|  | C1: UB/Semantics      |  | Holdout     |  | FC-001 (Pass 1: C1..C10)  |  |
|  | C2: Extractor/Audit   |  | Stitcher    |  | FC-002 (Pass 2: FC2-1..5) |  |
|  | C3: Stage 3 Proofs    |  | D1..D10     |  | FC-003 (Pass 3: ∉ audit)  |  |
|  | C4: Parsimony         |  | H1..H10, R4 |  | (Zero prior history)      |  |
|  +-----------------------+  +-------------+  +---------------------------+  |
+-----------------------------------------------------------------------------+
```

#### 1. Divergent Architects ($\alpha$ Minimization, $\beta$ Generalization, $\gamma$ Incumbent Defense)

Forcing three architects to optimize orthogonal objective functions before any
synthesis prevented premature convergence on a single local optimum:

- **Architect $\alpha$ (Radical Minimizer):** Drove TCB concept elimination
  (`M-1` `CaptureProfile` removal, `M-2` `Obligation.assumed`, `M-3` flat
  `BodyId` tables, and `D-06` `ValidTySizes` upper bound). However, taken alone,
  Architect $\alpha$'s proposal was unsound: it dropped `MentionedItem`
  dead-branch PME tracking (`D-04`), dropped `FieldAccess` and stratified
  `AdmissibleAdtInv` (`D-07`), and eliminated Stage 3 lowering (`M-4`).
- **Architect $\beta$ (Structural Generalizer):** Replaced ad-hoc single-field
  operators (`Rvalue.field0`, `Rvalue.copyDeref`) with general `Place`
  projections and `MirVal.uninit` (`D-01`), discovered that
  `SimplifyConstCondition` and `RemoveDeadBlocks` erase dead-branch PMEs from
  `required_consts` so `Body::mentioned_items` must be captured (`D-04`),
  formulated stratified `AdmissibleAdtInv` for nested ADTs (`D-07`), and
  designed Stage 3 `lowerBody` (`M-4`, `D-12`). Taken alone, however, Architect
  $\beta$ missed recursive `isFullyInitFuel` on whole-aggregate reads (`D-02`)
  and root return PC canonicalization (`D-12`).
- **Architect $\gamma$ (Pragmatic Incumbent Defender):** Audited the existing
  repository's enforcement boundaries (`TrustedBoundary.lean` and
  `foundation-lock.json` in `D-10`), defended the two-stage `ConstsTotal` vs.
  `MonoAdmitted` distinction (`D-04`), and highlighted multi-configuration
  `CONFIGS` hazards (`D-09`).

#### 2. Sealed Holdout Stitcher ($D_1\text{--}D_{10}$, $H_1\text{--}H_{10}$, and Reserve $R_1\text{--}R_4$)

In `swarm-model-refinement`, the Holdout Stitcher is isolated from the
Coordinator, Architects, and Challengers; it never reveals holdout definitions
to the synthesis loop and reports only minimal behavioral failure descriptions
when a candidate fails a holdout.

During Pass 0, the Stitcher audited its initial 10 holdout candidates against
the repository (`572f1e80580daa4b052ce5646bb675484d9bb957` and
`d79b0c070cf4115b523fe6ee62c1e72504de2254`) and discovered that **6 of the 10
initial shapes were already visible in repository source files**:
`id_copy`/`id_move` (`D1`), `alloc_passthrough` (`D2`), `pme_concrete_transmute`
(`D3`), `inline_const_pme` (`D4`), and the 3-function `NonZero` crate (`D7`)
appeared verbatim in `theory/Anneal/MirLemmas.lean` (`lines 3752-3790`), while
`CaptureProfile` removal (`D9`) and static `Proof.lean` (`D10`) appeared in
`docs/architecture.md`. Because any agent reading the codebase had already
observed those six shapes, keeping them as "holdouts" would have produced false
confirmation. The Stitcher reclassified those 6 shapes to the public Discovery
Set ($D_1\text{--}D_{10}$) and constructed 10 genuinely unseen blind holdouts
($H_1\text{--}H_{10}$) plus 4 reserve holdouts ($R_1\text{--}R_4$):

| Holdout ID | Stitcher Cluster | Scenario Description | Pass 1 (`Cand. 001`) | Pass 2 (`Cand. 002`) | Pass 3 (`Cand. 003`) | Primary Defects Gated |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `H1` | `S4` | Multi-field partial move (`Move(_1.0)`), valid sibling read (`_1.1`), and illegal whole-aggregate read/borrow (`Move(_1)`, `&_1`) | **FAIL** | **PASS** | **PASS** | `D-01`, `D-02`, `D-03` |
| `H2` | `S3` | Nested callee returning reference to caller frame (`fn id_ref(r: &usize) -> &usize { r }`) across activation boundary | **FAIL** | **FAIL** | **PASS** | `D-11` |
| `H3` | `S2` | Generic constant block with conditional panic (`const { assert!(size_of::<T>() == 8) }`) | **FAIL** | **FAIL** | **PASS** | `D-04`, `D-05`, `D-08` |
| `H4` | `S1b` | Public struct wrapping private-invariant ADT (`PublicWrapper { pub inner: NonZero }`) under `AdmissibleAdtInv` | **FAIL** | **PASS** | **PASS** | `D-07` |
| `H5` | `S2` | Dead-branch polymorphic const reference (`if false { let _ = Fail::<T>::C; }`) via `Body::mentioned_items` | **PARTIAL** | **PASS** | **PASS** | `D-04`, `D-05` |
| `H6` | `S6` | `TrustedBoundary.lean` syntax whitelist (`deriving`, unary `-`, `^`, `∉`) and `foundation-lock.json` import audit | **FAIL** | **PASS** | **PASS** | `D-10` |
| `H7` | `S3` | Reference generation invalidation via re-entry (`StorageDead` + `StorageLive` of same local index) | **PASS** | **PASS** | **PASS** | `D-12` (`storageLive` retention) |
| `H8` | `S5` | Stage 3 `lowerBody` backward simulation and terminal `MirReturn.state` PC canonicalization | **FAIL** | **PASS** | **PASS** | `D-12` |
| `H9` | — | `tySizes` upper bound (`isize::MAX`) and checked arithmetic overflow interaction | **PARTIAL** | **PASS** | **PASS** | `D-06`, `D-08`, `D-09` |
| `H10` | — | Unsupported construct inside uncalled private helper vs. called helper (reachable capture from `Crate.fns`) | **PASS** | **PASS** | **PASS** | `D-09` |
| `R1`–`R4` | Reserve | `[T; N]` `evalTyByteSize` overflow (`R1`), recursion fuel exhaustion (`R2`), transitive generic const items (`R3`), nested ref in returned tuple/struct (`R4`) | Sealed | `R2`, `R3` activated | **4 / 4 PASS** | `D-05`, `D-06`, `D-08`, `D-11` |

When `Candidate 002` failed `H2` and `H3` in Pass 2, the Stitcher activated
Reserve holdouts `R2` and `R3` to replace the exposed failure modes and verify
that Pass 3's repair generalized to transitive generic constant items (`R3`) and
recursion fuel exhaustion (`R2`) rather than overfitting to the Pass-2 feedback.

#### 3. Unanchored Fresh Critics (`fresh-critic-001` through `003`)

Even adversarial Challengers accumulate **conversational anchoring** after
reviewing multiple revisions of the same design: once a Challenger signs off on
a subsystem's general shape in Pass 1, it focuses on verifying whether its prior
objections were addressed. `swarm-model-refinement` counteracts this by spawning
a brand-new critic agent on each pass (`fresh-critic-001`, `fresh-critic-002`,
`fresh-critic-003`) that receives *only* the problem contract and the current
candidate design, with zero access to prior proposals, challenger transcripts,
or repair notes:

- **`fresh-critic-001` (Pass 1):** Produced 10 findings (`C1`–`C10`),
  independently corroborating the partial-move whole-struct bypass (`C3` /
  `D-02`), the `ConstsEvaluated` PME collapse (`C2` / `D-04`), the
  `#[cfg(debug_assertions)]` `LocalDefId` shift (`C7` / `D-09`), and
  `TrustedBoundary.lean` violations (`C8`, `C10` / `D-10`).
- **`fresh-critic-002` (Pass 2):** Produced 5 high-severity findings
  (`FC2-1`–`FC2-5`), including **two defects that no anchored Challenger or
  Architect had previously isolated**:
  1. `FC2-3` (`D-03`): The intermediate `.deref` hop bypass in `evalProjFuel`,
     where evaluating `(*r).1` concatenated `targetProj ++ rest` and skipped
     `isFullyInitFuel` on the dereferenced struct `*r`.
  2. `FC2-5` (`D-09`): The cross-config `-C overflow-checks` divergence in
     `CONFIGS`, where `debug` (`-Coverflow-checks=on`) and `release`
     (`-Coverflow-checks=off`) produce non-identical PostCleanup MIR on every
     `+`, `-`, or `*` expression.
- **`fresh-critic-003` (Pass 3):** Confirmed zero blocking semantic defects in
  `Candidate 003`, while catching one last `TrustedBoundary.lean` syntax
  violation in `NoDupIds` (Section 1.2 item 1, `D-10`): writing `x ∉ xs`
  expands to `` `«term_∉_» ``, which is excluded from
  `TrustedBoundary.lean`'s `allowedNotationSyntaxKinds` (`lines 274-280`).
  Replacing `x ∉ xs` with `(x ∈ xs → False)` eliminated the last audit-boundary
  defect.

### Finding 4: The Second-Order Regression Trap and Minimum Falsification Depth ($k \ge 3$ Passes)

Basis: execution, derived

Tracking the active defect set across Pass 0, Pass 1 (`Candidate 001`), Pass 2
(`Candidate 002`), and Pass 3 (`Candidate 003`) exposes why neither a
2-pass single-agent loop nor a 1-pass swarm critique is sufficient for
soundness-critical model refinement:

| Refinement Stage | Active Defects (of `D-01`..`D-12`) | Newly Introduced Regressions in This Pass | Holdouts Passed (`H1`..`H10`) | Key Regression Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| **Single-Agent `M3'`** (Pass 2 final) | **10** (`D-01`, `D-04`..`D-12`; `D-02`/`D-03` untriggered only because `Place` was omitted) | 4 design/audit regressions (`D-04` single-stage `ConstsEvaluated`, `D-09` raw `LocalDefId`, `D-10` `deriving`, `D-12` unsound `lowerBody`) | Not applicable (no holdout set) | Self-critique confirmed macro-parsimony without testing boundary counterexamples |
| **Swarm Pass 1** (`Candidate 001`) | **9** (`D-02`, `D-03`, `D-04`, `D-06`, `D-07`, `D-09`, `D-10`, `D-11`, `D-12`) | **7** newly introduced synthesis regressions (`D-02`, `D-03`, `D-04`, `D-07`, `D-10`, `D-11`, `D-12`) | `2 / 10` (`2` partial, `6` fail) | Merging $\alpha$'s aggressive deletions with $\beta$'s new `Place` and `lowerBody` mechanisms created boundary mismatches |
| **Swarm Pass 2** (`Candidate 002`) | **6** (`D-03`, `D-05`, `D-08`, `D-09`, `D-11`, `D-12` mid-block) | **3** newly introduced second-order repair regressions (`D-05`, `D-08`, `D-11`) | `8 / 10` (`0` partial, `2` fail) | Local patches to Pass-1 critiques broke adjacent invariants (`Terminator.assert` $\to$ `.unwind`, `ConstsTotal` implication, `targetFrameId = 0`) |
| **Swarm Pass 3** (`Candidate 003`) | **0** (all `12 / 12` defects resolved) | **0** | `10 / 10` (+ `4 / 4` Reserve) | Exact separation of `Terminator.assert` vs. `Callee.panic`, existential `ConstsTotal`, frame-relative `returnRefsOk`, step-by-step `.deref` |

This progression demonstrates the **Second-Order Regression Trap**:

1. **First-order synthesis regressions (Pass 1):** When a synthesizer combines
   macro-simplifications (such as removing `MirBody` nesting and adding Stage 3
   `lowerBody`) with micro-generalizations (such as `Place` projections and
   `MirVal.uninit`), the seams between new definitions almost always contain
   boundary defects (`7` new regressions in `Candidate 001`). In a single-agent
   workflow, Pass 2 is the *only* review pass after synthesis, and is performed
   by the same agent that authored the synthesis.
2. **Second-order repair regressions (Pass 2):** When Pass 2 repairs the
   first-order defects flagged in Pass 1, the repairs themselves perturb
   adjacent invariants (`3` new regressions in `Candidate 002`). For example,
   fixing `H3` (`const { assert!(...) }` unwinding) by changing
   `Terminator.assert` failure to `.terminated .unwind` (`D-08`) broke runtime
   overflow soundness (`bad_overflow`), and fixing `ConstsTotal` by adding
   `evalTyByteSize` on the left of `→` (`D-05`) made `ConstsTotal` vacuous on
   `.unsupported` types.
3. **Convergence at $k = 3$:** Because Pass 2 introduced second-order
   regressions while fixing Pass-1 defects, a second adversarial falsification
   round (Pass 2 critique by Challengers + Stitcher + `fresh-critic-002`) and a
   third synthesis and verification pass (Pass 3 `Candidate 003` +
   `fresh-critic-003`) were strictly necessary to reach a zero-defect fixed
   point.

## Boundaries

1. **Single-domain empirical scope (`n = 1` controlled complex system):** Both
   workflows were evaluated on one high-complexity formal-methods architecture
   (`joshlf/anneal` MIR capture and Lean 4 operational semantics). While the
   12 defects span diverse failure classes (Rust compiler passes, operational
   semantics, propositional quantifiers, kernel syntax whitelists, and backward
   simulation theorems), quantitative defect ratios will vary in domains without
   strict formal soundness invariants.
2. **Specification-level vs. kernel-compiled mechanized proofs:** The
   single-agent (`M3'`) and swarm (`Candidate 003`) outputs are complete
   architectural and Lean 4 / Rust specification designs audited line by line
   against `TrustedBoundary.lean` and the 24 discovery/holdout scenarios
   ($D_1\text{--}D_{10}$, $H_1\text{--}H_{10}$, $R_1\text{--}R_4$), rather than
   a full end-to-end replacement of `theory/Anneal/MirLemmas.lean` compiled in
   `lake build`. Mechanizing the inductive `lowerBody_simulates` proof inside
   Lean 4 provides an additional layer of machine-checked assurance beyond
   specification review.
3. **Coordination cost vs. task criticality:** `swarm-model-refinement` invoked
   12 distinct agent roles across 3 passes, whereas `model-refinement` ran in a
   single conversation across 2 passes. For macro-level refactoring or
   low-coupling conceptual cleanup where micro-semantic boundary bugs cannot
   compromise soundness, single-agent `model-refinement` captures the same
   macro-architectural simplifications (`5 / 5`) at a fraction of the compute
   and coordination cost.

## Evidence

- **Immutable repository revisions (`joshlf/anneal`):**
  - Implementation baseline commit `572f1e80580daa4b052ce5646bb675484d9bb957`
    (`2026-11-05T02:35:58Z`):
    - `trusted/lean/Trusted/MirAst.lean` (`282` lines, SHA-256
      `a8f289cd80b354757491d5f3b45f3cf60789031b3cfd9897641a73331d9e8ffc`):
      `Terminator`/`MirBody` mutual inductive (`lines 193-235`), `TCBItem`
      embedding `MirBody` (`lines 258-260`).
    - `trusted/lean/Trusted/MirSemantics.lean` (`1,150` lines, SHA-256
      `f679659d884ab1bff5067c77cd4c8a92c0829b8a08cbc81737259adca50980c3`):
      `validStep` unbounded `.usize` (`line 370`), `evalOperand` (`lines
      491-510`), `.assign dst (.field0 src)` (`lines 589-597`), root
      `Terminator.return_` returning raw `⟨retVal, s⟩` (`lines 740-745`),
      `ConstsTotal` and `MonoAdmitted` (`lines 946-960`), `AdmissibleAdtInv`
      using `defaultAdtInv` (`lines 1000-1007`), `EnsuresRetLibInv` (`lines
      1011-1015`), and dead target-compilation scaffolding
      (`TargetArtifact`/`rustc`/`TargetSem`/`TargetLang`/`rustcCodec`, `lines
      1056-1099`).
    - `trusted/lean/Trusted/Refinement.lean` (`288` lines, SHA-256
      `5e4d7b356178a78c8ce927fae3ae6b31dcdf14f735a189f7ec3b7dc4574f0ae3`) and
      `trusted/lean/Trusted/StepResult.lean` (`164` lines, SHA-256
      `d6a6d5d1865b7718921bf92ecdff92fa22c4e312ddd06037f78dc5c4f147d8e4`).
    - `trusted/rustc-capture/src/extract.rs` (`709` lines, SHA-256
      `355aad45538815385820aa4cd730ef52c42c1f5e3cfd0eefcaafa205fab340dd`):
      `Operand::Copy(_1.0)` and `Operand::Move(_1.0)` both lowered to
      `ir::Rvalue::Field0` (`lines 458-485`).
    - `trusted/rustc-capture/src/main.rs` (`570` lines, SHA-256
      `1191d8ee12afd73aa50b114ff3c6a98ccf7b443435a6151797ef37dc1f849995`):
      `CONFIGS` differing in `-Coverflow-checks=on` vs. `off` (`lines 325-328`).
    - `trusted/audit/TrustedBoundary.lean` (`823` lines, SHA-256
      `7534e9c4571d5769af1f2028adb6688071fdad81ddb7cc084372f587a11cc96a`):
      `allowedCommandSyntaxKinds` excluding `derivingClass` (`lines 218-238`)
      and `allowedNotationSyntaxKinds` excluding unary `-`, `^`, and `∉`
      (`lines 274-280`).
    - `theory/Anneal/MirLemmas.lean` (`3,829` lines, SHA-256
      `473ade75e099abb69e5badb6ba9082521f4d25abb3d9c300c1dc7e031b49438b`):
      `beqMirBodyFuel 8` (`lines 1-260`) and 9-entry `proveCrateOpt` lookup
      table (`lines 3752-3795`).
  - Design and skill baseline commit `d79b0c070cf4115b523fe6ee62c1e72504de2254`
    (`2026-11-05T10:23:12-05:00`):
    - `skills/model-refinement/SKILL.md` (`307` lines, SHA-256
      `a219d993410dcd67b0783f05681e686bc1fb2e2fe4378acc32daf751e5a190e9`).
    - `skills/swarm-model-refinement/SKILL.md` (`336` lines, SHA-256
      `157092de1eabf6686a47b97c7a62e50649cfc5ec508555bc3e66e1da9f4691aa`).
    - `docs/architecture.md` (`366` lines, SHA-256
      `191f598ffc8b306a25c27d00af1302309a45a764508376546e93e7f4e59005b8`).
- **Package support artifacts (`support/`):**
  - `support/refinement_defects_and_metrics.json`: Complete structured dataset
    recording file SHA-256 digests and line counts across both revisions, the
    5 macro-architectural simplifications (`M-1`–`M-5`), all 12 defects
    (`D-01`–`D-12`) with pass-by-pass lifecycle states, mechanism attribution
    tables, and the Pass 0 $\to$ Pass 3 regression transition matrix.
  - `support/verify_refinement_comparison.py`: Standalone reproducible audit
    script verifying `REPORT.json`, `REPORT.md`, and
    `support/refinement_defects_and_metrics.json` (plus live git blob and line
    assertions against `joshlf/anneal` when `--anneal-repo` is available).

## Revalidation

Run the self-contained verification script from the report package directory
(or from the root of the `reference` branch):

```bash
python3 support/verify_refinement_comparison.py
```

When a checkout of `joshlf/anneal` containing commits
`572f1e80580daa4b052ce5646bb675484d9bb957` and
`d79b0c070cf4115b523fe6ee62c1e72504de2254` is present, pass `--anneal-repo` to
cross-verify all 19 git blobs, SHA-256 digests, line counts, and baseline code
patterns directly against the repository:

```bash
python3 support/verify_refinement_comparison.py --anneal-repo /path/to/anneal
```

Revalidate this report when:

1. `skills/model-refinement/SKILL.md` or
   `skills/swarm-model-refinement/SKILL.md` changes its pass structure, holdout
   isolation rules, or fresh-critic spawning protocol; or
2. Anneal's `trusted/` MIR AST, operational semantics, or `TrustedBoundary.lean`
   audit rules are updated to implement the Stage 3 `lowerBody` pipeline.
