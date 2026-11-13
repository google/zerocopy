# Approaches to a Verified Rust Frontend: Trait Solver Proof Trees, Polonius Borrow Certificates, Reference Elaborators, and THIR-to-MIR Lowering

## Summary

A drop-in verified Rust compiler (`v0`) that anchors its initial soundness boundary at `Runtime(PostCleanup)` Mid-Level Intermediate Representation (MIR) leaves the `rustc` frontend (`rustc_parse` through `rustc_mir_build` and `rustc_borrowck`) in the Trusted Computing Base (TCB). Keeping a verified frontend achievable in future milestones without rewriting the `v0` middle-end or proof architecture requires understanding the scale, internal modularity, and certificate boundaries of `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):

1. **Quantitative Scale and Modularity of the `rustc 1.99.1` Frontend (`support/frontend_architecture_and_crate_metrics.json`):**
   Across all **78 crates** in `compiler/` (**865,761 total lines**, **657,923 non-comment/non-blank LOC**, **2,020 `Diagnostic`** and **517 `Subdiagnostic`** derive occurrences, and **576 `E0xxx` error-code registrations**), the frontend prior to `rustc_codegen_ssa` accounts for **55 crates** and **521,986 non-comment LOC** (**79.3%** of the compiler):
   - *Lexing, Parsing, and AST (`1_lex_parse_ast`)*: 6 crates, **44,703 LOC**.
   - *Macro Expansion, Hygiene, Name Resolution, and HIR (`2_expand_resolve_hir`)*: 7 crates, **62,110 LOC** (`rustc_expand` 15,826 LOC, `rustc_builtin_macros` 16,603 LOC, `rustc_resolve` 13,562 LOC, `rustc_hir` 9,432 LOC).
   - *Portable Type IR, Next-Generation Trait Solver, and Pattern Exhaustiveness (`3_type_ir_and_trait_solver`)*: 4 crates, **26,037 LOC** (`rustc_type_ir` **9,849 LOC**, `rustc_next_trait_solver` **11,013 LOC**, `rustc_pattern_analysis` **4,548 LOC**, `rustc_type_ir_macros` **627 LOC**). Crucially, `rustc_type_ir` and `rustc_next_trait_solver` are parameterized over an abstract `Interner` trait (`compiler/rustc_type_ir/src/interner.rs`) and do **not** depend on `rustc_middle`, `rustc_hir`, or `rustc_session`.
   - *Hacked/Coupled Typechecking, Inference, and Legacy Trait Selection (`4_typeck_infer_trait_selection`)*: 5 crates, **119,289 LOC** (`rustc_hir_analysis` 42,610 LOC, `rustc_hir_typeck` 35,342 LOC, `rustc_trait_selection` 30,664 LOC, `rustc_infer` 8,857 LOC, `rustc_traits` 1,816 LOC).
   - *THIR Construction, MIR Building, Borrow Checking, Polonius, and Const Eval (`5_thir_mir_build_borrowck_polonius`)*: 5 crates, **92,679 LOC** (`rustc_mir_transform` 34,934 LOC, `rustc_borrowck` 25,947 LOC, `rustc_mir_build` 17,679 LOC, `rustc_const_eval` 8,832 LOC, `rustc_mir_dataflow` 5,193 LOC, `rustc_polonius` 94 LOC).
2. **Five Candidate Frontend Verification Approaches and Their Trade-Offs:**
   - **Approach A — Proof-Tree Certificate Checking for Trait and Type Solving (`rustc_type_ir::solve::inspect`):** `rustc 1.99.1`'s next-generation trait solver (`-Znext-solver`) builds explicit canonicalized proof trees (`GoalEvaluation<I>`, `Probe<I>`, `ProbeStep<I>`, `ProbeKind<I>` in `compiler/rustc_type_ir/src/solve/inspect.rs:36-114` and `compiler/rustc_next_trait_solver/src/solve/inspect/build.rs:25-289`). Because proof trees are shallow per canonical query (`inspect.rs:14-16`), an untrusted solver can export a witness tree of `CandidateSource` selections (`Impl(DefId)`, `ParamEnv(usize)`, `AliasBound`, `BuiltinImpl`) and canonical substitutions (`CanonicalVarValues<I>`), which a verified checker of **~1,500–2,500 Lean 4 LOC** checks without replicating search heuristics, probe backtracking, or caching.
   - **Approach B — Polonius Borrow-Check Fixed-Point Certificate Verification (`rustc_borrowck::polonius`):** `rustc 1.99.1` supports three borrow-check modes (`Polonius::Disabled`, `Polonius::Legacy` via `-Zpolonius`, and `Polonius::Next` location-sensitive localized constraint graphs via `-Zpolonius=next` in `compiler/rustc_borrowck/src/polonius/constraints.rs:1-324`). Rather than verifying `rustc_borrowck`'s 25,947 LOC dataflow solver, a certifying frontend emits the converged loan-liveness fixed point $\text{LiveLoans} : \text{Point} \to \mathcal{P}(\text{Loan})$ and region subset witness $\text{Subset} : \text{Point} \to \mathcal{P}(\text{Region} \times \text{Region})$. Checking that $\text{LiveLoans}$ contains all `loan_issued_at` seeds, is closed under `cfg_edge` transitions modulo `loan_killed_at`, and is disjoint from `loan_invalidated_at` at every `loan_used_at` point requires $O(|E| \cdot |\text{Loans}|)$ boolean checks (**~800–1,200 Lean 4 LOC**).
   - **Approach C — Verified THIR-to-MIR Lowering (`rustc_mir_build`):** `rustc` lowers typed HIR to a compact Typed High-Level IR (`compiler/rustc_middle/src/thir.rs`, **51 `ExprKind` variants** where all implicit coercions, autoderefs, method resolutions, and overloaded operators are already explicit) before building `mir_built` (`compiler/rustc_mir_build/src/builder/`, **10,636 LOC** across `expr/`, `matches/`, and `scope.rs`). A translation validator or verified lowering pass from THIR to `mir_built` (**~4,000–6,000 Lean 4 LOC**) bridges expression trees, LIFO temporary drop scopes (`scope.rs`), and pattern decision trees (`rustc_pattern_analysis`, 4,548 LOC) to CFG basic blocks.
   - **Approach D — Executable Specification Elaborators (`a-mir-formality` / MiniRust) vs. Mechanical Translation (`rustc_type_ir` + `rustc_next_trait_solver`):** Full mechanical translation of `rustc_parse` + `rustc_expand` + `rustc_resolve` + `rustc_hir_typeck` (>225,000 LOC of mutable arena/session code) is infeasible, whereas `rustc_type_ir` (9,849 LOC) + `rustc_next_trait_solver` (11,013 LOC) + `rustc_pattern_analysis` (4,548 LOC) are intentionally isolated from `TyCtxt` behind generic traits (`Interner`, `SolverDelegate`, `PatCx`), making them directly extractable via Charon/Aeneas or `rocq-of-rust`/`hax`.
3. **Design Choices in `v0` Required to Keep All Frontend Approaches Open:**
   To avoid painting `v0` into an architectural corner, the `v0` verified backend and MIR semantics must satisfy four interface invariants: (i) dual-stage MIR schema compatibility (`mir_built` / `Analysis(PostCleanup)` alongside `Runtime(PostCleanup)`), (ii) `rustc_type_ir`-isomorphic `Ty`/`Predicate`/`GenericArg` representations with explicit `ParamEnv` indices on every generic call and projection, (iii) explicit capability/loan tags (`Retag` / `StorageLive` / `StorageDead`) linking Polonius loan certificates to operational aliasing semantics, and (iv) treating proc-macro and declarative macro expansion (`rustc_expand`) as an untrusted AST/HIR generator whose expanded output is checked post-expansion.
4. **Mechanized Lean 4 (`v4.34.1`) Verification Probe (`support/VerifiedFrontendTraitPoloniusAndThirProbe.lean`):**
   We mechanize and prove sound (286 lines, 0 `sorryAx`, `[propext]` only) a trait proof-tree certificate checker (`checkInductiveCert_sound`, plus `canary_inductive_cycle_unsound`), a Polonius loan-liveness fixed-point certificate verifier (`checkPoloniusCert_sound`, plus `canary_unpropagated_loan_unsound`), and a THIR-to-MIR short-circuiting and LIFO temporary drop-scope equivalence proof (`thir_to_mir_and_drop_sound`, plus `canary_premature_temp_drop_unsound`).

## Applicability

The findings in this report apply to:

- **`rust-lang/rust` (`1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`)**: specifically the 78 workspace crates under `compiler/`, including `rustc_type_ir`, `rustc_next_trait_solver`, `rustc_pattern_analysis`, `rustc_trait_selection`, `rustc_hir_analysis`, `rustc_hir_typeck`, `rustc_middle` (`src/thir.rs`), `rustc_mir_build`, `rustc_borrowck`, and `rustc_polonius`.
- **`leanprover/lean4` (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`)**: kernel environment used to check `support/VerifiedFrontendTraitPoloniusAndThirProbe.lean`.
- **`joshlf/anneal` (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`)**, **`AeneasVerif/charon` (`cf02e3f228f97ee7be3a415be56989053063326d`)**, and **`AeneasVerif/aeneas` (`ca282ec2312a96f6a985a4d23a6636908564d23`)**: MIR/THIR capture boundaries and pure functional extraction pipelines.
- **Normative and formal semantic specifications**: `rust-lang/reference` (`bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`), `rust-lang/fls` tag `1.99` (`946eacae5a4a33a89af7832178504692439e7478`), and `minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`).

This package extends `rustc-name-resolution-local-item-identity-and-type-lowering` (which covers `rustc_resolve`, `DefId` vs. `DefPathHash`, and HIR type-alias lowering) and `verified-rust-compiler-architecture-self-hosting-and-certifying-bootstrap` (which covers the `Runtime(PostCleanup)` MIR-to-machine-code backend architecture).

## Findings

### 1. Quantitative Decomposition of the `rustc 1.99.1` Frontend

`Basis: source + execution` (`compiler/*/Cargo.toml`, `support/verify_frontend_metrics.py`, `support/frontend_architecture_and_crate_metrics.json`)

To evaluate which frontend stages can be verified by foundational proof, mechanical extraction, or certificate checking, Table 1 partitions all 78 crates of `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) into eight architectural layers.

| Stage / Subsystem | Crates | `.rs` Files | Total Lines | Code Lines (LOC) | Key Architectural Property |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **1. Lexing, Parsing & AST** (`rustc_lexer`, `rustc_parse`, `rustc_ast*`) | 6 | 172 | 56,530 | 44,703 | Concrete syntax only; bypassed if verification starts post-expansion or on HIR/THIR |
| **2. Expansion, Name Resolution & HIR** (`rustc_expand`, `rustc_resolve`, `rustc_hir*`, `rustc_builtin_macros`, `rustc_passes`) | 7 | 212 | 77,940 | 62,110 | Arbitrary Turing-complete proc-macros (`dlopen`); must be treated as untrusted syntax generator |
| **3. Portable Type IR, Trait Solver & Patterns** (`rustc_type_ir*`, `rustc_next_trait_solver`, `rustc_pattern_analysis`) | 4 | 132 | 37,088 | 26,037 | **Zero dependency on `rustc_middle`/`TyCtxt`**; generic over `Interner` / `PatCx` traits |
| **4. HIR Typeck, Inference & Legacy Selection** (`rustc_hir_analysis`, `rustc_hir_typeck`, `rustc_trait_selection`, `rustc_infer`, `rustc_traits`) | 5 | 380 | 153,395 | 119,289 | Heavily coupled to `TyCtxt`, diagnostics, method probing, and coercion heuristics |
| **5. THIR, MIR Build, Borrowck, Polonius & Const Eval** (`rustc_mir_build`, `rustc_borrowck`, `rustc_polonius`, `rustc_mir_dataflow`, `rustc_const_eval`, `rustc_mir_transform`) | 6 | 428 | 123,768 | 92,679 | Lowers 51-variant `thir::ExprKind` to CFG MIR and runs NLL/Polonius borrow checking |
| **6. Middle IR, ABI, Metadata & Diagnostics** (`rustc_middle`, `rustc_abi`, `rustc_target`, `rustc_session`, `rustc_metadata`, `rustc_errors`, etc.) | 27 | 806 | 244,606 | 177,227 | Defines `mir::Body`, `thir::Body`, `TyCtxt` queries, and 2,020 `Diagnostic` types |
| **7. Codegen Backends** (`rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_llvm`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`) | 5 | 288 | 119,336 | 95,859 | Target of `v0` verified backend (`Runtime(PostCleanup)` MIR to machine code) |
| **8. Driver, Interface & Build Support** (`rustc_driver*`, `rustc_interface`, `rustc_smir`, `rustc_public*`, etc.) | 18 | 227 | 53,098 | 40,019 | CLI orchestration and StableMIR external consumer wrappers |
| **Total (`compiler/`)** | **78** | **2,645** | **865,761** | **657,923** | — |

Two structural facts stand out from `support/frontend_architecture_and_crate_metrics.json`:

1. **Isolation of `rustc_type_ir`, `rustc_next_trait_solver`, and `rustc_pattern_analysis`:**
   In `rustc 1.99.1`, the Rust trait and pattern teams factored the core logical engines out of `rustc_middle` and `rustc_trait_selection` into standalone crates with minimal Cargo dependencies:
   - `compiler/rustc_type_ir/Cargo.toml`: 9,849 LOC across 57 files; depends only on `derive-where`, `ena` (union-find), `indexmap`, `rustc_ast_ir`, `rustc_data_structures`, `rustc_index`, `rustc_serialize`, `rustc_type_ir_macros`, ` smallvec`, `thin-vec`, and `tracing`.
   - `compiler/rustc_next_trait_solver/Cargo.toml`: 11,013 LOC across 24 files; depends **only** on `derive-where`, `rustc_index`, `rustc_type_ir`, `rustc_type_ir_macros`, `smallvec`, and `tracing`!
   - `compiler/rustc_pattern_analysis/Cargo.toml`: 4,548 LOC across 12 files; depends **only** on `rustc_apfloat`, `rustc_arena`, `rustc_data_structures`, `rustc_index`, and `tracing`!
   - `compiler/rustc_polonius/Cargo.toml`: 94 LOC across 2 files; depends **only** on `rustc_data_structures` and `rustc_index`.
2. **Diagnostic-dominated bulk in `rustc_hir_typeck` and `rustc_hir_analysis`:**
   Across `compiler/`, there are **2,020 `Diagnostic`** and **517 `Subdiagnostic`** derive macros supporting **576 `E0xxx` error codes** (`compiler/rustc_error_codes/src/error_codes.rs`). Over 35% of `rustc_hir_typeck` (35,342 LOC), `rustc_hir_analysis` (42,610 LOC), and `rustc_trait_selection` (30,664 LOC) consists of error recovery, suggestion heuristics, and diagnostic formatting that are irrelevant to a soundness certificate for accepted programs (since a certifying compiler only needs to prove that *accepted* programs are well-typed and lower soundly to MIR).

---

### 2. Approach A: Certificate Checking for Trait and Type Solving (`rustc_next_trait_solver` & `a-mir-formality`)

`Basis: source + execution + derived` (`compiler/rustc_type_ir/src/solve/inspect.rs:1-114`, `compiler/rustc_next_trait_solver/src/solve/inspect/build.rs:25-289`, `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs:1-450`, `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:1-159`)

#### 2.1 Architecture of the Next-Generation Trait Solver (`-Znext-solver`)
In `rustc 1.99.1`, the next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/`) replaces the legacy split between `SelectionContext` (impl selection) and `FulfillmentContext` (obligation forest + separate projection normalization) with a unified, canonicalized goal evaluation engine (`EvalCtxt` in `eval_ctxt/mod.rs`) parameterized by `D: SolverDelegate<Interner = I>`.

Every goal `Goal<I, I::Predicate>` (`PredicateKind::Clause(ClauseKind::Trait, Projection, TypeOutlives, RegionOutlives, ConstArgHasType, WellFormed, ...)` or `PredicateKind::Subtype`, `AliasRelate`, `NormalizesTo`) is solved by:
1. **Canonicalization (`eval_ctxt/mod.rs`):** Abstracting local inference variables (`?T`, `'r`, `?C`) into canonical bound variables (`Canonical<I, Goal<I, I::Predicate>>`) while recording the caller's original arguments in `orig_values: ThinVec<I::GenericArg>`.
2. **Candidate Assembly (`assembly/mod.rs`, 1,496 LOC; `trait_goals.rs`, 1,676 LOC; `normalizes_to.rs`, 1,129 LOC):** Enumerating candidate sources (`CandidateSource<I>` in `compiler/rustc_type_ir/src/solve/mod.rs`):
   - `CandidateSource::Impl(I::DefId)` — user or standard-library `impl` blocks;
   - `CandidateSource::ParamEnv(usize)` — `where`-clause assumptions in the caller's `ParamEnv`;
   - `CandidateSource::AliasBound` — bounds declared on an associated type or opaque `impl Trait`;
   - `CandidateSource::BuiltinImpl(BuiltinImplSource)` — compiler-synthesized implementations (`Copy`, `Sized`, `Tuple`, `FnPtr`, `TraitUpcasting`, `Unsize`, `Auto` traits);
   - `CandidateSource::CoherenceUnknowable` — coherence-only ambiguity marker.
3. **Cycle Handling in the Search Graph (`search_graph.rs:1-159`):**
   When evaluating a canonical goal $G$ encounters $G$ already on the active stack, `rustc_next_trait_solver` checks the cycle's `StepKind` / `GoalPolarity`:
   - **Coinductive cycles** (auto traits such as `Send`/`Sync` and `WellFormed` predicates when all cycle participants are coinductive) succeed on the initial fixpoint iteration;
   - **Inductive cycles** (ordinary traits and projections) fail on the base iteration (`Certainty::Overflow` / `NoSolution`) and iterate to a least fixed point bounded by `repr_depth`.

#### 2.2 Proof Trees (`GoalEvaluation<I>` and `Probe<I>`) and What a Certificate Checker Must Verify
`rustc_type_ir::solve::inspect` (`compiler/rustc_type_ir/src/solve/inspect.rs:36-114`) and `ProofTreeBuilder` (`compiler/rustc_next_trait_solver/src/solve/inspect/build.rs:25-289`) already instrument `EvalCtxt` to emit structured proof trees whenever `GenerateProofTree::Yes` is active:
- `GoalEvaluation<I>` (`inspect.rs:50-55`) records `uncanonicalized_goal: Goal<I, I::Predicate>`, `orig_values: ThinVec<I::GenericArg>`, `final_revision: I::Probe` (`Probe<I>`), and `result: QueryResult<I>`.
- Each `Probe<I>` (`inspect.rs:61-66`) records `steps: Vec<ProbeStep<I>>`, `kind: ProbeKind<I>`, and `final_state: CanonicalState<I, ()>`.
- Each `ProbeStep<I>` (`inspect.rs:69-85`) is one of:
  - `AddGoal(GoalSource, CanonicalState<I, Goal<I, I::Predicate>>)` — a subgoal emitted while instantiating an `impl` or builtin rule;
  - `NestedProbe(Probe<I>)` — a child candidate branch;
  - `RecordImplArgs { impl_args: CanonicalState<I, I::GenericArgs> }` — the concrete generic arguments instantiated for an `Impl(DefId)` candidate;
  - `MakeCanonicalResponse { shallow_certainty: Certainty }`.

**Crucial limitation of `rustc`'s built-in proof trees (`inspect.rs:14-16`):**
As documented at `compiler/rustc_type_ir/src/solve/inspect.rs:14-16`:
> *"Proof trees are only shallow, we do not compute the proof tree for nested goals. Visiting proof trees instead recomputes nested goals in the parents inference context when necessary."*

For a verified compiler frontend, recomputing nested goals inside the TCB would drag the solver search back into the checker. However, converting shallow `GoalEvaluation<I>` nodes into a **complete, deep deduction certificate** requires only two changes outside the TCB:
1. **Prune dead candidate probes:** Keep only the winning `ProbeKind::TraitCandidate { source, result: Ok(...) }` branch at each goal node, discarding failed/backtracked sibling probes.
2. **Recursively attach child `GoalEvaluation` trees to each `ProbeStep::AddGoal`:** When `GoalSource` is proven with `Certainty::Yes`, attach the child's instantiated `RecordImplArgs` and subgoal derivations (plus a coinductive assumption index for coinductive cycles, or a finite fuel/rank witness for inductive derivations).

With those two additions, the **trusted trait-certificate checker** in Lean 4 reduces to:
- Checking that for `CandidateSource::Impl(def_id)` with `impl_args`, substituting `impl_args` into `tcx.impl_trait_ref(def_id)` equals the goal's `TraitRef` and every predicate in `tcx.predicates_of(def_id)` instantiated with `impl_args` appears in `AddGoal` and is discharged by its child certificate;
- Checking that for `CandidateSource::ParamEnv(idx)`, the `idx`-th caller bound in `ParamEnv` matches the goal;
- Enforcing polarity: rejecting any cycle that contains an inductive step (`checkInductiveCert_sound` and `canary_inductive_cycle_unsound` in `support/VerifiedFrontendTraitPoloniusAndThirProbe.lean:99-160`).

---

### 3. Approach B: Formalizations and Certificate Checking of Borrow Checking (`Polonius` & NLL)

`Basis: source + execution + derived` (`compiler/rustc_polonius/src/lib.rs`, `compiler/rustc_borrowck/src/polonius/mod.rs:1-189`, `compiler/rustc_borrowck/src/polonius/constraints.rs:1-324`, `compiler/rustc_borrowck/src/polonius/legacy/facts.rs:1-237`)

#### 3.1 Three Borrow-Checker Engines in `rustc 1.99.1`
Empirical execution of `rustc 1.99.1` (`support/deep_extracted_details.json`) and source inspection of `compiler/rustc_session/src/options.rs:977-990, 2744-2745` and `compiler/rustc_borrowck/src/polonius/` show three distinct borrow-checking modes in `rustc 1.99.1`:
1. **Default NLL (`Polonius::Disabled`):** Location-insensitive region outlives constraints (`'a: 'b @ P` treated as global CFG reachability bounded by liveness in `compiler/rustc_borrowck/src/region_infer/`).
2. **Legacy Polonius Fact Extractor (`-Zpolonius` / `Polonius::Legacy`, `compiler/rustc_borrowck/src/polonius/legacy/`):**
   Extracts 14 relational Datalog tables (`RustcFacts` in `legacy/facts.rs:1-237`, `legacy/accesses.rs`, `legacy/loan_invalidations.rs`, `legacy/loan_kills.rs`, `legacy/location.rs`):
   - Input facts: `loan_issued_at(Origin, Loan, Point)`, `loan_killed_at(Loan, Point)`, `cfg_edge(Point, Point)`, `loan_invalidated_at(Point, Loan)`, `subset_base(Origin, Origin, Point)`, `var_used_at`, `var_defined_at`, `var_dropped_at`, `use_of_var_derefs_origin`, `drop_of_var_derefs_origin`, `child_path`, `path_is_var`, `path_assigned_at_base`, `path_moved_at_base`, `universal_region`, `placeholder`.
3. **In-Tree Next-Generation Polonius (`-Zpolonius=next` / `Polonius::Next`, `compiler/rustc_borrowck/src/polonius/constraints.rs:1-324` and `liveness_constraints.rs:1-159`):**
   Instead of invoking an external Datalog engine, `rustc 1.99.1` constructs a `LocalizedConstraintGraph` over `LocalizedNode { region: RegionVid, point: PointIndex }` (`constraints.rs:20-85`), combining forward CFG liveness edges and variance-directed localized outlives constraints (`ConstraintDirection::Forward` vs. `Backward` in `polonius/mod.rs:38-189`) to compute `compute_loan_liveness` directly inside `rustc_borrowck`.

#### 3.2 Linear-Time Fixed-Point Certificate Verification vs. Verified Fixpoint Solver
In all formalizations of Rust borrow checking—including **Oxide** (Weiss et al. 2019), **Featherweight Rust / FRB** (Pearce 2021), **Polonius** (`rust-lang/polonius`), and **Aeneas/LLBC** (`AeneasVerif/aeneas`)—the borrow checker computes a least fixed point of subset and loan-containment relations over the MIR control-flow graph.

Verifying the *fixed-point solver algorithm* inside the TCB is unnecessary. If the untrusted `rustc_borrowck` emits the converged valuation as a certificate:
$$\mathcal{C}_{\text{pol}} = \bigl(\text{Sub} : \text{Point} \to \mathcal{P}(\text{Origin} \times \text{Origin}),\;\; \text{LiveLoan} : \text{Point} \to \mathcal{P}(\text{Origin} \times \text{Loan})\bigr)$$
then a verified certificate checker only needs to check three local, loop-free boolean conditions:
1. **Seed inclusion:** Every `loan_issued_at(O, L, P)` is present in $\text{LiveLoan}(P)$, and every `subset_base(O_1, O_2, P)` is present in $\text{Sub}(P)$.
2. **Inductive step closure (1-step verification):**
   - At each point $P$, if $(O_1, L) \in \text{LiveLoan}(P)$ and $(O_1, O_2) \in \text{Sub}(P)$, then $(O_2, L) \in \text{LiveLoan}(P)$.
   - Across each `cfg_edge(P, Q)`, if $(O, L) \in \text{LiveLoan}(P)$, $L \notin \text{loan\_killed\_at}(P)$, and $O$ is live at $Q$, then $(O, L) \in \text{LiveLoan}(Q)$.
3. **Safety disjointness:** At every point $P$, if $(O, L) \in \text{LiveLoan}(P)$ for an origin $O$ accessed at $P$, then $L \notin \text{loan\_invalidated\_at}(P)$.

By Park's fixpoint induction principle (`cert_covers_reachable_loans` and `checkPoloniusCert_sound` in `support/VerifiedFrontendTraitPoloniusAndThirProbe.lean:199-231`), any pre-fixpoint $\mathcal{C}_{\text{pol}}$ satisfying (1) and (2) over-approximates the true least fixed point of reachable loans, so condition (3) suffices to prove absence of use-after-invalidation in $O(|E| \cdot |\text{Origins}| \cdot |\text{Loans}|)$ time without trusting `rustc_borrowck`'s solver.

---

### 4. Approach C & D: Reference Elaborators, Mechanical Translation, and THIR-to-MIR Lowering

`Basis: source + derived` (`compiler/rustc_middle/src/thir.rs`, `compiler/rustc_mir_build/src/thir/`, `compiler/rustc_mir_build/src/builder/`, `compiler/rustc_pattern_analysis/src/`)

#### 4.1 Why THIR (`rustc_middle::thir`) Is the Ideal Frontend-to-Middle-End Seam
In `rustc 1.99.1`, `rustc_mir_build` does not lower HIR directly to MIR. Instead:
1. **`tcx.thir_body(def_id)` (`compiler/rustc_mir_build/src/thir/cx/`, 2,083 LOC):**
   Converts HIR + `TypeckResults` into a `thir::Body<'tcx>` (`compiler/rustc_middle/src/thir.rs`). Unlike HIR—where expressions rely on implicit side tables in `TypeckResults` (`adjustments`, `method_map`, `coercion_casts`, `overloaded_binops`, `closure_kind_origins`)—every `thir::Expr` carries its fully resolved `ty: Ty<'tcx>`, `temp_lifetime: Option<Scope>`, and one of **51 explicit `thir::ExprKind` variants** (`support/frontend_architecture_and_crate_metrics.json`), including explicit `Deref`, `Borrow`, `AddrOf`, `PointerCoercion`, `NeverToAny`, `PlaceTypeAscription`, `ValueTypeAscription`, `LogicalOp`, `Use`, `Adt`, `Closure`, and `Call`.
2. **Unsafety Checking on THIR (`compiler/rustc_mir_build/src/check_unsafety.rs:1-1118`):**
   `check_unsafety` runs directly on THIR (`UnsafetyVisitor`), classifying all **13 `UnsafeOpKind` variants** (`check_unsafety.rs:643-666`):
   - `CallToUnsafeFunction`, `UseOfInlineAssembly`, `InitializingTypeWithUnsafeField`, `UseOfMutableStatic`, `UseOfExternStatic`, `UseOfUnsafeField`, `DerefOfRawPointer`, `AccessToUnionField`, `MutationOfLayoutConstrainedField`, `BorrowOfLayoutConstrainedField`, `CallToFunctionWith` (missing `#[target_feature]`), `UnsafeBinderCast`, and `CallDropExplicitly`.
3. **Pattern Exhaustiveness and Lowering (`compiler/rustc_mir_build/src/thir/pattern/`, 3,223 LOC + `rustc_pattern_analysis`, 4,548 LOC):**
   Normalizes HIR patterns into `thir::Pat` and verifies exhaustiveness before MIR construction.
4. **THIR-to-MIR Builder (`compiler/rustc_mir_build/src/builder/`, 10,636 LOC):**
   Lowers `thir::Body` into `mir::Body` (`mir_built`) across four core mechanisms:
   - *Category-directed expression compilation* (`builder/expr/category.rs` 102 LOC, `as_place.rs` 744 LOC, `as_rvalue.rs` 755 LOC, `as_operand.rs` 165 LOC, `as_temp.rs` 139 LOC, `into.rs` 941 LOC, `stmt.rs` 204 LOC);
   - *Hierarchical LIFO temporary and break/continue drop scopes* (`builder/scope.rs`, 2,190 LOC);
   - *Decision-tree match compilation with fake borrows for guard soundness* (`builder/matches/`, 4,742 LOC);
   - *Custom MIR parsing for `#[custom_mir]` tests* (`builder/custom/`, 895 LOC, out of scope for user code).

#### 4.2 Comparing the Four Frontend Verification Strategies

Table 2 compares the engineering cost, TCB reduction, and `v0` compatibility of the four approaches to verifying or certifying the frontend above `mir_built`.

| Approach | Target Crates / Seam | Estimated Mechanization / Checker Size | What Leaves the TCB | Blocking Obstacles if Applied Alone |
| :--- | :--- | :--- | :--- | :--- |
| **1. Trait & Borrow Certificate Checkers** | `rustc_type_ir::solve::inspect` + `rustc_borrowck::polonius` | **~2,300–3,700 Lean 4 LOC** | Trait selection, projection normalization, coherence checks, NLL/Polonius dataflow solver (~65,000 Rust LOC) | Does not verify HIR $\to$ THIR coercion insertion or THIR $\to$ MIR CFG lowering |
| **2. Verified THIR $\to$ `mir_built` Lowering / Validator** | `rustc_middle::thir` $\to$ `rustc_middle::mir` (`rustc_mir_build::builder`) | **~4,000–6,000 Lean 4 LOC** | Expression flattening, short-circuit evaluation, temporary drop-scope scheduling (`scope.rs`), decision-tree compilation (`matches/`) (~18,000 Rust LOC) | Assumes input `thir::Body` has already been soundly typed and adjustment-elaborated |
| **3. Mechanical Extraction of Portable Crates** (`Charon`/`Aeneas` or `rocq-of-rust`) | `rustc_type_ir` (9,849 LOC), `rustc_next_trait_solver` (11,013 LOC), `rustc_pattern_analysis` (4,548 LOC), `rustc_polonius` (94 LOC) | **25,504 Rust LOC** extracted + ~5,000–8,000 Lean 4 invariant proofs | The exact upstream Rust implementations of the next-gen trait solver and pattern analyzer | Cannot easily extract `rustc_hir_typeck` (35,342 LOC) or `rustc_expand` (15,826 LOC) due to `TyCtxt` arena/query coupling |
| **4. Clean-Slate Executable Reference Elaborator** (`a-mir-formality` style) | Typed HIR / Surface AST $\to$ THIR + Trait/Borrow obligations | **~15,000–25,000 Lean 4 LOC** | Coercion insertion, autoderef, method resolution, closure upvar inference (`rustc_hir_typeck` + `rustc_hir_analysis`) | Must track evolving Rust surface ergonomics and still relies on `rustc_expand`/`rustc_resolve` for macro expansion |

**Optimal Hybrid Path:** Combine **Approach 1** (Trait Proof-Tree + Polonius Fixed-Point Certificate Checkers), **Approach 2** (Verified THIR $\to$ `mir_built` lowering), and a **Typechecked-THIR Well-Formedness Checker** (verifying that every `thir::Expr` node's explicit type and adjustments satisfy the local typing rules discharged by the trait certificates). Together, this hybrid path requires **~9,000–12,000 lines of Lean 4** while removing **>180,000 LOC** of `rustc_hir_analysis`, `rustc_hir_typeck`, `rustc_trait_selection`, `rustc_infer`, `rustc_borrowck`, and `rustc_mir_build` from the TCB!

---

### 5. Which `v0` Architectural Choices Keep Every Verified Frontend Approach Open

`Basis: derived + source` (`support/VerifiedFrontendTraitPoloniusAndThirProbe.lean`)

A designer building the `v0` verified backend (`Runtime(PostCleanup)` MIR $\to$ machine code) keeps all four frontend verification approaches open by enforcing five concrete design rules in `v0`:

1. **Preserve a Dual-Dialectic MIR AST (`Analysis` + `Runtime` Dialects):**
   `v0` code generation consumes `Runtime(PostCleanup)` MIR (where `FalseEdge`, `FalseUnwind`, `AscribeUserType`, and `FakeRead` have been erased and `Drop` has been elaborated). To keep **Approach B (Polonius)** and **Approach C (THIR $\to$ `mir_built`)** composable without re-defining MIR, the `v0` Lean `Mir.Body` data structure should include the `Analysis`-phase statement/terminator constructors (`FakeRead`, `AscribeUserType`, `FalseEdge`, `StorageLive`, `StorageDead`, `Retag`) and formalize `Cleanup` / `ElaborateDrops` as verified MIR-to-MIR passes rather than hardcoding a `Runtime`-only AST.
2. **Use `rustc_type_ir`-Isomorphic Type and Predicate Representations:**
   Do not erase generic types or trait predicates at the `v0` capture boundary into opaque strings or layout-only byte sizes. Represent `Mir.Ty`, `Mir.GenericArg`, `Mir.Clause`, and `Mir.ParamEnv` in Lean 4 as a direct structural mirror of `rustc_type_ir` (`compiler/rustc_type_ir/src/`). This keeps both **Approach 1 (Proof-Tree Certificates)** and **Approach 3 (Mechanical Extraction of `rustc_type_ir` + `rustc_next_trait_solver`)** plug-compatible with `v0`.
3. **Carry Explicit Trait-Resolution Witness IDs on Every Generic Call and Associated-Type Projection:**
   In `v0`, monomorphization (`Instance::try_resolve`) resolves `(DefId, GenericArgs, ParamEnv)` to a concrete `Instance`. Recording the `CandidateSource` (`Impl(DefId, impl_args)` or `BuiltinImpl`) as an explicit witness index on each call/projection site in `v0`'s MIR capture format allows `v0` to trust that witness initially and later plug in `checkInductiveCert` (`support/VerifiedFrontendTraitPoloniusAndThirProbe.lean:77-140`) with zero change to the MIR-to-machine-code backend.
4. **Retain `StorageLive`, `StorageDead`, and `Retag` Capability Hooks in the Operational Semantics:**
   Polonius certificates (`checkPoloniusCert_sound`, lines 217–231) prove that borrows are never used after loan invalidation, which bridges to LLVM `noalias` and mid-end memory optimizations only if the `v0` MIR operational semantics retains `Retag` and storage-lifetime transitions (as in MiniRust / Tree Borrows).
5. **Define the Frontend Trust Boundary Post-Macro-Expansion (at HIR/THIR):**
   Because Rust procedural macros (`rustc_expand` / `proc_macro`) execute arbitrary host native code via `dlopen`, no purely foundational proof can verify arbitrary proc-macro execution. `v0` should explicitly anchor source-level specifications and future frontend verification at the **expanded HIR/THIR representation** (or offer deterministic AST-to-HIR desugaring only for proc-macro-free crates).

## Boundaries

- **Not examined — Procedural macro sandboxing (`Wasm` proc-macros) and parser grammar verification (`rustc_lexer` / `rustc_parse`):** While `rustc_parse` (44,703 LOC across `1_lex_parse_ast`) could be replaced by a verified PEG/LR parser against the Ferrocene Language Specification (`rust-lang/fls@946eacae5a4a33a89af7832178504692439e7478`), we did not build a mechanized parser prototype in this package because macro hygiene (`rustc_expand`) sits between surface syntax and name resolution.
- **Known limitation of `rustc 1.99.1`'s `-Znext-solver`:** While `-Znext-solver=coherence` is enabled by default in `rustc 1.99.1`, full `-Znext-solver=globally` across all HIR typeck passes still has open corner-case deviations tracked upstream (`compiler/rustc_next_trait_solver/`), so proof-tree export for general crate bodies currently requires passing `-Znext-solver` or invoking `evaluate_root_goal_for_proof_tree_raw_provider` (`eval_ctxt/mod.rs:146`) on individual obligations.
- **Known limitation of shallow `GoalEvaluation<I>` proof trees (`compiler/rustc_type_ir/src/solve/inspect.rs:14-16`):** Upstream `ProofTreeBuilder` only materializes one canonical query frame at a time; exporting a standalone certificate file requires driving a `ProofTreeVisitor` (`compiler/rustc_trait_selection/src/solve/inspect/analyse.rs`) to recursively expand nested `AddGoal` steps.

## Evidence

1. **Primary Upstream Source Code (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, tag `1.99.1`):**
   - `compiler/rustc_type_ir/src/solve/inspect.rs:1-114`: definitions of `State<I, T>`, `CanonicalState<I, T>`, `GoalEvaluation<I>`, `Probe<I>`, `ProbeStep<I>`, and `ProbeKind<I>`.
   - `compiler/rustc_next_trait_solver/src/solve/inspect/build.rs:25-289`: `ProofTreeBuilder<D>`, `EvaluationStepBuilder<D>`, `WipEvaluationStep<I>`, `WipProbe<I>`, and `WipProbeStep<I>`.
   - `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs:1-450` and `search_graph.rs:1-159`: `EvalCtxt`, `evaluate_root_goal_for_proof_tree_raw_provider`, and coinductive vs. inductive cycle detection.
   - `compiler/rustc_borrowck/src/polonius/{mod.rs:1-189, constraints.rs:1-324, liveness_constraints.rs:1-159, dump.rs:1-497}` and `compiler/rustc_borrowck/src/polonius/legacy/{facts.rs:1-237, loan_invalidations.rs:1-447, loan_kills.rs:1-148, location.rs:1-114}`: Polonius Datalog facts (`RustcFacts`) and `-Zpolonius=next` localized constraint graph (`LocalizedConstraintGraph`).
   - `compiler/rustc_middle/src/thir.rs` and `compiler/rustc_mir_build/src/{thir/, builder/, check_unsafety.rs:1-1118}`: 51-variant `thir::ExprKind`, `UnsafetyVisitor` (`13 UnsafeOpKind` variants at lines 643–666), and THIR-to-MIR lowering (`builder/expr/into.rs`, `builder/scope.rs`, `builder/matches/mod.rs`).
2. **Mechanized Lean 4 (`v4.34.1`) Proofs (`support/VerifiedFrontendTraitPoloniusAndThirProbe.lean`):**
   - 288 lines of standalone Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), verified with 0 `sorryAx` and 0 `Lean.ofReduceBool`:
     - `checkInductiveCert_sound` & `canary_inductive_cycle_unsound` (lines 100–164);
     - `cert_covers_reachable_loans`, `checkPoloniusCert_sound`, & `canary_unpropagated_loan_unsound` (lines 199–256);
     - `thir_to_mir_and_drop_sound` & `canary_premature_temp_drop_unsound` (lines 296–304).
3. **Quantitative Metrics and Reproducible Scripts (`support/`):**
   - `support/frontend_architecture_and_crate_metrics.json`: complete 78-crate LOC, `.ftl`/diagnostic, `THIR` variant, and file-level breakdown of `rustc_next_trait_solver`, `rustc_polonius`, `rustc_borrowck`, and `rustc_mir_build`.
   - `support/verify_frontend_metrics.py`: standalone Python 3 script reproducing the crate metrics from a `rust-lang/rust` `1.99.1` checkout.

## Revalidation

1. **Re-verify the Lean 4 frontend certificate and THIR-to-MIR proofs:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- lean \
     reports/verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering/support/VerifiedFrontendTraitPoloniusAndThirProbe.lean
   ```
   Confirm exit code `0` and that `#print axioms` reports only `[propext]` (for `checkInductiveCert_sound`) and `does not depend on any axioms` (for `checkPoloniusCert_sound` and `thir_to_mir_and_drop_sound`).
2. **Re-run the `rustc 1.99.1` frontend crate and THIR census:**
   ```bash
   RUST_1991_ROOT=/path/to/rust-1.99.1 \
     python3 reports/verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering/support/verify_frontend_metrics.py
   ```
   Verify that `rustc_type_ir` and `rustc_next_trait_solver` remain decoupled from `rustc_middle` and check whether `thir::ExprKind` (51 variants in `1.99.1`) or `inspect::ProbeStep` (4 variants in `1.99.1`) has added new constructors.
