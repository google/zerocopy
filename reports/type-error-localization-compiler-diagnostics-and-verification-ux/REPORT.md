# Type-Error Localization, Compiler Diagnostics, and Verification Failure UX

## Summary

Non-local and unactionable diagnostics in compilers and deductive verifiers stem from four structural causes rather than formatting shortcomings:

1. **Constraint non-uniqueness and greedy traversal bias in unification-based inference.** An ill-typed Hindley-Milner program produces an unsatisfiable constraint set admitting multiple Minimal Correction Subsets (MCSes). Bottom-up `Algorithm W` commits substitutions eagerly in left-to-right order and fails late at downstream innocent sites. Top-down `Algorithm M` (Lee & Yi 1998) fails strictly earlier; Minimal Unsatisfiable Subsets (MUSes) yield order-invariant error slices (Haack & Wells 2003); Weighted MaxSMT (`MinErrLoc`; Pavlinovic, King & Wies 2014, 2015) and Bayesian constraint-graph path ranking (`SHErrLoc`; Zhang & Myers 2014, 2015) pinpoint minimum-weight/maximum-likelihood root causes; counter-factual typing (Chen & Erwig 2014) computes ranked type-level fixes via variational types; and dynamic witnesses (`NanoMaLy`; Seidel, Jhala & Weimer 2016) synthesize concrete crashing inputs and navigable reduction graphs.
2. **Structural provenance anchoring via bidirectional typing, context threading, and interactive proof trees.** Bidirectional typing (Dunfield & Krishnaswami 2021) separates checking ($\Gamma \vdash e \Leftarrow A$) from synthesis ($\Gamma \vdash e \Rightarrow A$), anchoring mismatches at `Sub` boundaries. Production compilers operationalize this via context-threaded constraints and poison recovery (`Elm`'s `Expected`/`Context`/`Category` + `Applicative Diff` + `UF.union ... errorDescriptor`; `Roc`'s `FnCallArgsConflictContext` and `CopiedRequirement`) and obligation provenance (`rustc`'s `ObligationCause`, `ErrorSortKey`, implication suppression, and `#[diagnostic::on_unimplemented]`). Because trait resolution is Horn-clause proof search, flattening failed AND-OR trees into linear text discards branch context; exposing the proof tree interactively (`Argus`; Gray, Crichton & Krishnamurthi 2025) delivered $2.2\times$ higher fault localization and $3.3\times$ faster debugging ($n = 25$).
3. **Permission-provenance models for ownership and borrowing.** Region-outlives constraints have no surface syntax. `Aquascope` (Crichton, Gray & Krishnamurthi 2023) translates Polonius facts into per-place `Read`/`Write`/`Own` (`drop`) permissions refined by `Loan`/`Move` refiners plus SCC-condensed region-flow faults (`LocalOutlivesUniversal`, `MissingUniversalConstraint`, `LocalInvalidatedAtExit`).
4. **Conflict between elaboration-dependent syntax and resilient parsing, plus spurious SMT counterexamples.** Resilient IDE parsers (`rust-analyzer`, `Scala 3`'s typed-AST `Quotes`) rely on static grammars. Mid-file parser mutation (`Lean 4`'s sequential `parseCmd` over post-elaboration `cmdState.env`) forces 2-command invalidation rewind and creates a `<|>` vs. `recover'` conflict; `Agda` partially decouples this via two-stage `RawApp` + scope-deferred mixfix parsing. In SMT verification, backward WP VCs yield opaque `unknown`/timeouts under E-matching trigger instability (Leino & Pit-Claudel 2016) and potentially invalid raw models (`DafnyModel.cs:190` prints an explicit validity disclaimer, while `ProofDependencyWarnings` detects vacuous proofs). `Why3`'s giant-step assertion checking (Becker, Belo Lourenço & Marché 2021; `src/mlw/check_ce.ml`) pairs Concrete and Giant-Step RAC to separate real bugs (`NC`), weak invariants/contracts (`SW`), incomplete checks (`NC_SW`), and spurious solver models (`BAD_CE`).

A standalone Python 3.10+ probe ([`support/verify_error_localization_mus.py`](support/verify_error_localization_mus.py)) deterministically reproduces both `Algorithm W`/`M` vs. exact `MUS`/`MCS`/`SHErrLoc` blame across 6 benchmarks and Why3's 5-outcome Giant-Step RAC classification matrix.

## Applicability

This report synthesizes language-general diagnostic principles across 15 peer-reviewed papers and 11 pinned upstream repositories inspected on `2026-11-19`:

- **Type-error localization:** Lee & Yi (1998), Haack & Wells (2003), Zhang & Myers (2014, 2015), Pavlinovic, King & Wies (2014, 2015), Chen & Erwig (2014), Seidel, Jhala & Weimer (2016) + `ucsd-progsys/nanomaly@0de06f2c3a41`, Dunfield & Krishnaswami (2021), and Zhao et al. (2024).
- **Production compiler/IDE diagnostics:** `elm/compiler@1c278bf5ecf4`, `roc-lang/roc@63434e9847e7` (Zig compiler under `src/check/`), `rust-lang/rust@b0b600668bb9`, `cognitive-engineering-lab/argus@8d41733c313e` (Gray et al. 2025), and `cognitive-engineering-lab/aquascope@f2d0a06034b8` (Crichton et al. 2023).
- **Extensible parsing & verification UX:** `leanprover/lean4@8009d0a64d28` (Ullrich & de Moura 2020), `agda/agda@9691cf2331ed`, `scala/scala3@90f3daf0a479`, `dafny-lang/dafny@8c137ba351c6` (Leino & Pit-Claudel 2016), and `AdaCore/why3@02050ad2905b` (Becker et al. 2021).

**Cross-referenced adjacent corpus packages (non-duplication boundary):**

- Rust-specific MIR span mapping, `StmtOrd` sidebands, and `cargo-anneal` / `rustc` formatting: `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux`.
- Cross-tool UTF-8/UTF-16 column normalization and Charon/Aeneas span projection: `cross-tool-source-spans-utf8-columns-and-diagnostic-normalization`.
- Compiler-backed IDE snapshots, Salsa/red-green CSTs, and batch-live equivalence: `language-server-snapshots-views-and-compiler-backed-ide-architectures`.
- Lean 4 `InfoTree` internals and hygiene: `lean-elaboration-hygiene-positions-and-infotree`.
- VC-generation encodings across Dafny, Boogie, Viper, F*, and Why3: `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`.

Exact source claims apply strictly to the pinned revisions in `REPORT.json`; general architectural invariants (`derived`) extend to any HM, trait-solving, region-based, macro-extensible, or SMT-backed frontend sharing those mechanisms.

## Findings

### 1. Why Unification-Based Inference Mislocalizes Blame (`Algorithm W` vs. `M`, MUS, `MinErrLoc`, `SHErrLoc`, Counterfactual Typing, Dynamic Witnesses)

Basis: documentation + source + execution + derived

#### 1.1 Constraint-Set Non-Uniqueness and Traversal-Order Bias

In Damas-Milner type inference, typing an expression $e$ generates equality constraints $C = \{\tau_i \doteq \sigma_i\}_{i=1}^n$ tagged with source sites $\ell_i$. When $e$ is ill-typed, $C$ is unsatisfiable—a global subset property, not a property of one node:

- **Minimal Unsatisfiable Subset (MUS):** $U \subseteq C$ is unsatisfiable, and every $U' \subsetneq U$ is satisfiable. Every site in $U$ is jointly necessary for that contradiction.
- **Minimal Correction Subset (MCS):** $M \subseteq C$ is minimal such that $C \setminus M$ is satisfiable. By Reiter's hitting-set duality, $M$ is an MCS iff $M$ is a minimal hitting set of all MUSes $\mathcal{U}(C)$.

Because $\mathcal{U}(C)$ usually has multiple minimal hitting sets, **no purely deductive rule selects a unique buggy node**. Standard `Algorithm W` resolves ambiguity arbitrarily via traversal order:

1. **Left-to-right commitment bias:** Destructive Robinson unification commits shared type variables on the first visited expression, treating an early defect as ground truth and crashing on a later innocent use.
2. **Bottom-up late failure:** `Algorithm W` ($\mathcal{W}(\Gamma, e) \to (S, \tau)$) checks subexpressions without an expected type and fails only at an enclosing application or annotation. Lee & Yi (TOPLAS 1998, DOI `10.1145/291891.291892`) formalized top-down **`Algorithm M`** ($\mathcal{M}(\Gamma, e, \rho) \to S$), proved soundness and completeness, and proved **`Algorithm M` always fails earlier than `Algorithm W`**. Yet `Algorithm M` still commits substitutions left-to-right across peer subexpressions.
3. **Polymorphic propagation:** Polymorphic combinators (`same : ∀a. a -> a -> a`, `id`, list constructors) transport a defective type across multiple hops before colliding at a distant consumer.

#### 1.2 Algorithmic Localization Paradigms

- **Type Error Slicing** (Wand POPL 1986, DOI `10.1145/512644.512648`; Haack & Wells ESOP 2003, DOI `10.1007/3-540-36575-3_20`): Computes an **MUS** and highlights the minimal syntactic slice of all contributing sites (scaled to SML in `Skalpel`). Sound and order-invariant, but unranked and potentially wide.
- **Weighted MaxSMT (`MinErrLoc`)** (Pavlinovic, King & Wies OOPSLA 2014, DOI `10.1145/2660193.2660230`; ICFP 2015, DOI `10.1145/2784731.2784765`): Splits $C$ into **hard** typing axioms and **soft** weighted expression constraints $w(c_i)$ reflecting compiler heuristics (e.g., higher weight on explicit annotations). The complement of a Weighted MaxSMT optimum is a **minimum-weight MCS**; blocking clauses enumerate runner-up MCSes interactively.
- **Bayesian Holistic Constraint Graphs (`SHErrLoc`)** (Zhang & Myers POPL 2014, DOI `10.1145/2535838.2535870`; Zhang, Myers, Vytiniotis & Peyton Jones PLDI 2015, DOI `10.1145/2737924.2738009` for GHC type classes/GADTs/type families): Represents analyses (OCaml, Jif, GHC) as directed constraint graphs and uses CFG-reachability over **both unsatisfiable and satisfiable paths**. Under an Occam prior ("code is mostly right"), an explanation hypothesis $h$ must hit every unsatisfiable path while incurring likelihood penalties whenever $h$ blames edges corroborated by many satisfiable paths. Candidate missing edges also diagnose *omitted assumptions* (missing typeclass bounds or security annotations).
- **Counter-Factual Typing** (Chen & Erwig POPL 2014, DOI `10.1145/2535838.2535863`): Embeds **variational choice types** into inference so AST leaves carry open counter-factual type alternatives; bidirectional flow computes ranked type-level repairs ("if $e$ had type $\tau'$, the program checks") without syntactic search. Evaluated on 121 ill-typed benchmarks from 22 prior papers.
- **Dynamic Witnesses & Reduction Graphs (`NanoMaLy`)** (Seidel, Jhala & Weimer ICFP 2016, DOI `10.1145/2951913.2951915`; `ucsd-progsys/nanomaly@0de06f2c3a41`): Symbolically executes ill-typed code with lazily narrowed input holes (`src/NanoML/Step.hs`, `Eval.hs`) to synthesize concrete crashing inputs, builds a reduction graph (`Step.hs:149` `buildGraph`), and supports path-preserving interactive stepping/zooming (`Explore.hs:25-153` `explore`, `collapse`, `collapseBadEdges`). Synthesized witnesses for **88%** of >4,500 student OCaml programs and small comprehensible graphs for **81%** of witnesses.
- **Total Hole Localization (`Hazel`)** (Omar et al. POPL 2019, DOI `10.1145/3290327`; Zhao et al. POPL 2024, DOI `10.1145/3632910`): Gives every edit state total static/dynamic semantics via typed empty and non-empty error holes (`?`), trapping mismatches inside hole membranes so downstream typing and live evaluation continue.

| Paradigm | Formal Target | Order-Invariant? | Symmetric Ties | Output Artifact | Adoption |
|---|---|---|---|---|---|
| **Algorithm W** | First failing Robinson unification | No (L→R, bottom-up) | Blames later site | Single span | Mainstream baseline |
| **Algorithm M** | First failing top-down unification | No (L→R, top-down) | Blames later peer | Earlier inner span | Hybrid passes (SML/NJ, OCaml) |
| **Error Slicing** | Minimal Unsatisfiable Subset (MUS) | Yes | Shows all sites | Minimal program slice | Research (`Skalpel`) |
| **MinErrLoc** | Minimum-weight MCS ($C \setminus \text{MaxSMT}$) | Yes | Enumerates via blocking clauses | Ranked blame sites | Research (OCaml) |
| **SHErrLoc** | Max-posterior hitting set (sat + unsat paths) | Yes | Reports tied top hypotheses | Ranked sites + missing assumptions | Research (OCaml, Jif, GHC, SCIF) |
| **Counter-Factual** | Variational choice-type repairs | Yes | Ranks alternative repairs | Concrete type-change suggestions | Research (Haskell/ML) |
| **NanoMaLy** | Crashing input + collapsed reduction graph | Semantic | Concrete runtime clash | Interactive execution trace | Research/education |
| **Hazel** | Bidirectional hole-wrapped derivation | Anchored | Localized at hole membrane | Live partial execution + holes | Research live IDE |

#### 1.3 Executable Probe Results (`support/verify_error_localization_mus.py`, Part 1)

Running `python3 -B support/verify_error_localization_mus.py` ($p_{\text{err}} = 0.05$, annotation weight $1.5$, default weight $1.0$) verifies six Mini-ML benchmarks:

| Benchmark | Expression | `W` Blame | `M` Blame | `#MUS` | Top `MCS`/`SHErrLoc` (`size`, `mus_hits`, `logP`) | Runner-Up (`size`, `logP`) | Diagnostic Finding |
|---|---|---|---|---|---|---|---|
| `B1_tuple_bug_first` | `fun x -> (not x, add1 x, add1 x, add1 x)` | `site:add1_x_1` *(wrong)* | `x1` *(wrong)* | 3 | `['site:not_x']` (`1`, `3`, `-2.6996`) | 3 `add1` sites (`3`, `-15.7885`) | L→R bias misblames innocent `add1 x`; MUS/MCS isolates `not x` (3/3 MUSes). |
| `B2_tuple_bug_last` | `fun x -> (add1 x, add1 x, add1 x, not x)` | `site:not_x` | `x0` | 3 | `['site:not_x']` (`1`, `3`, `-2.6996`) | 3 `add1` sites (`3`, `-15.7885`) | Reordering flips `W`; MUS/MCS is strictly order-invariant. |
| `B3_poly_chain_propagated_bug` | `fun x y -> let zero = false in let p1 = same zero x in let p2 = same x y in (p1, p2, add1 y, add1 x, add1 zero)` | `site:add1_y_innocent` *(2 hops away)* | — | 3 | `['site:zero_false']` (`1`, `3`, `-2.8022`) | `['site:add1_zero_innocent', 'site:same_zero_x']` (`2`, `-5.7466`) | Polymorphic `same` carries `Bool` 2 hops; `W` blames innocent `add1 y`, while MUS/MCS uniquely pinpoints `zero = false`. |
| `B4_defective_helper_3_callers` | `let f = fun x -> add1 x in (f true, f false, f true)` | `site:call1` *(wrong caller)* | — | 3 | `['site:def_body_add1']` (`1`, `3`, `-2.8535`) | 3 callers (`3`, `-8.7424`) | `W` blames innocent caller; global MCS blames single buggy body `add1 x`. |
| `B5_annotated_lambda_W_vs_M` | `((fun x -> add1 x) : Bool -> Int)` | `site:outer_annotation` *(late)* | `site:leaf_x` *(early)* | 1 | `['site:body_add1_x']` (`1`, `1`, `-2.8970`) | `['site:outer_annotation']` (`1`, `-3.1470`) | Confirms Lee & Yi (1998): `M` fails early at leaf `x`; `W` fails late at outer annotation. |
| `B6_symmetric_if_branches` | `if true then 1 else "oops"` | `site:if_expr` | `site:else_str` | 1 | `['site:else_str']` (`1`, `1`, `-2.9996`) | `['site:then_int']` (`1`, `-2.9996`) | Exact posterior tie (`-2.9996 == -2.9996`): confirms irreducible symmetry. |

*(Derived note: Because exact MUS/MCS enumeration is worst-case exponential and interacts awkwardly with incremental IDE typing and coercions, mainstream compilers rely on bidirectional structural anchoring and context threading in the hot path, leaving global solvers or proof-tree debuggers as opt-in passes.)*

---

### 2. Bidirectional Typing, Context-Threaded Diagnostics (`Elm`, `Roc`, `Rust`), and Interactive Proof Trees (`Argus`)

Basis: documentation + source + derived

#### 2.1 Bidirectional Typing as Structural Provenance (Dunfield & Krishnaswami 2021)

Per Dunfield & Krishnaswami (ACM Computing Surveys 54(5), Art. 98, 2021, DOI `10.1145/3450952`, `arXiv:1908.05839`), bidirectional typing follows Pfenning's recipe: **introduction forms check** against an expected type ($\Gamma \vdash e \Leftarrow A$), **elimination forms synthesize** a type upward ($\Gamma \vdash e \Rightarrow A$), and two explicit switching rules bridge modes:

$$\frac{\Gamma \vdash e \Leftarrow A}{\Gamma \vdash (e : A) \Rightarrow A}\;(\text{Anno}) \qquad\qquad \frac{\Gamma \vdash e \Rightarrow A \quad A \le B}{\Gamma \vdash e \Leftarrow B}\;(\text{Sub})$$

Every mismatch lands structurally at a **`Sub` transition** (or an incompatible introduction constructor), where the checker holds exact provenance for the node $e$, synthesized type $A$, and context-propagated expected type $B$. Annotations (`Anno`) act as firewalls preventing inner defects from leaking outward, at the cost of requiring annotations on redexes and unannotated top-level forms in synthesis positions.

#### 2.2 `Elm` and `Roc`: Context-Threaded Constraints, Type Diffs, and Poison Recovery

1. **`Elm` (`elm/compiler@1c278bf5ecf4136f122ce1cba436783c7f561dac`):**
   - **Expectation threading (`Type/Constrain/Expression.hs:42-221`, `Reporting/Error/Type.hs:44-138`):** `constrain :: RTV -> Can.Expr -> Expected Type -> IO Constraint` threads `Expected Type` (`NoExpectation | FromContext A.Region Context tipe | FromAnnotation N.Name Int SubContext tipe`) through every expression, pairing 13 syntactic `Context` constructors (`ListEntry`, `OpLeft`, `OpRight`, `IfCondition`, `IfBranch`, `CaseBranch`, `CallArity`, `CallArg`, `RecordAccess`, `RecordUpdateKeys`, `RecordUpdateValue`, `Negate`, `Destructure`) with `Category` (what expression produced `actualType`) and `MaybeName` (`FuncName`, `CtorName`, `OpName`, `NoName`).
   - **Structural type diffing (`Type/Error.hs:157-300`):** `toDiff` builds an `Applicative` `Diff D.Doc = Diff D.Doc D.Doc Status` highlighting only diverging sub-nodes (`D.dullyellow`) while collecting domain `Problem` hints (`IntFloat`, `StringFromInt`, `AnythingFromMaybe`, `ArityMismatch`, `BadRigidVar`, `FieldTypo`, `FieldsMissing`).
   - **Cascade-preventing union-find poison (`Type/Unify.hs:30-49`, `Type/Solve.hs:86-160`):** On mismatch, `unify` snapshots `(t1, t2)` and executes `UF.union v1 v2 errorDescriptor` (`Descriptor Error noRank noMark Nothing`), suppressing downstream secondary mismatches.
2. **`Roc` (`roc-lang/roc@63434e9847e74db8ffed7e9244bcb8317771c350`):**
   - `src/check/problem/context.zig:1-250` explicitly builds on Elm's `Type/Error.hs` and adds contexts targeting structural and polymorphic multi-site gaps:
     - **`FnCallArgsConflictContext` (`context.zig:59-61, 173-196`):** Records both `first_region` (receiver or earlier arg), `second_region`, and the callee's `fn_type` snapshot when two operands individually fit a polymorphic signature but conflict via a shared type variable.
     - **`CopiedRequirement` / `SharedMethodUses` (`context.zig:20-42`):** Preserves both caller `use_region` and callee `requirement_region` (plus paired method call regions) when inferred method obligations propagate across definitions.
     - **`TagNotInAnnotationContext` (`context.zig:88-92`), `MatchAltBinderContext` (`context.zig:226-243`), and `TryReturnContext` (`context.zig:111-116`):** Anchors row/tag-union polarity, multi-pattern binders, and `?` early-return errors.

#### 2.3 `rustc` Trait Provenance, Pruning, and Interactive Proof Trees (`Argus`)

Trait/typeclass resolution is proof search in a Horn-clause logic program; failure is a branching AND-OR tree of failed subgoals often 4–8 `impl`s deep (`Diesel`, `Axum`, `Bevy`).

1. **`rustc` (`rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545`):**
   - **Compact provenance chains (`compiler/rustc_middle/src/traits/mod.rs:44-260`):** `ObligationCause<'tcx>` stores `ObligationCauseCodeHandle` (`Option<Arc<ObligationCauseCode>>`), encoding ~60% `Misc` obligations as `None` (line 152) and omitting `code` from `Hash` (lines 63-68). Recursive subgoals link via `derived_cause` (`DerivedCause` chains: `ImplDerived`, `BuiltinDerived`, `WellFormedDerived`).
   - **Priority sorting, implication suppression, and ambiguity merging (`compiler/rustc_trait_selection/src/error_reporting/traits/mod.rs:141-340`):** `report_fulfillment_errors` orders obligations by `ErrorSortKey` (`FormatLiteral` first; `Sized`/`MetaSized`/`PointeeSized`/`Coerce`/`WellFormed` last), normalizes `ExpnKind::Desugaring` spans to `call_site`, suppresses errors implied by another error or a definite trait failure covering a projection (`error_implies`, `covered_by_trait_error`, lines 226-269), and merges ambiguity errors sharing a sub-unification root inference variable (`ambiguity_infer_var`, lines 281-340) into one diagnostic.
   - **Root-vs-leaf selection and library diagnostics (`fulfillment_errors.rs:164-213`, `on_unimplemented.rs:34-260`):** `report_selection_error` promotes the root trait when `self_ty` matches up to `peel_refs()` and the root trait is non-internal (`CoerceUnsized`/`Unsize` excluded). `#[diagnostic::on_unimplemented]` lets trait authors match `FilterOptions { self_types, from_desugaring, cause, crate_local, direct, generic_args }`.
2. **`Argus` (`cognitive-engineering-lab/argus@8d41733c313e97f87c6bf390ec59f2701e4e41d9`; Gray, Crichton & Krishnamurthi PLDI 2025, DOI `10.1145/3729302`):**
   - Linear CLI messages still collapse branching AND-OR trees and hide rejected near-miss `impl`s. `Argus` serializes `rustc_next_trait_solver` proof trees (`crates/argus/src/proof_tree/mod.rs:39-177`, `topology.rs:31-140`) into bit-packed `ProofNode(u32)` graphs (`Goal`/`Candidate`/`Result`), `GraphTopology`, `ProofCycle`, and `GoalData { necessity, num_vars, is_main_tv }`, offering bottom-up and top-down interactive views with complexity-sorted obligations (`aadebug::AnalysisResults`). In a 25-developer user study (`arXiv:2504.18704`), Argus localized **$2.2\times$ more faults** and completed tasks **$3.3\times$ faster** than standard `rustc` messages.

*(Cross-reference: Rust MIR span projection and `cargo-anneal` diagnostic contracts live in `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux` and `cross-tool-source-spans-utf8-columns-and-diagnostic-normalization`.)*

---

### 3. Borrow-Checker Mental Models and Permission Provenance (`Aquascope`)

Basis: documentation + source + derived

Rust's borrow checker solves whole-function region-outlives constraints (`'a: 'b`) and loan-liveness equations over MIR places—constraints with no surface syntax. Using their *Ownership Inventory*, Crichton, Gray & Krishnamurthi (*A Grounded Conceptual Model for Ownership Types in Rust*, PACMPL 7(OOPSLA2), Art. 265, 2023, DOI `10.1145/3622841`) showed that programmers routinely conflate static borrow-checker over-approximations with dynamic undefined behavior.

Direct inspection of `cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6` documents how `Aquascope` translates Polonius facts into an operational capability view:

1. **Per-Place Permission Lattice (`crates/aquascope/src/analysis/permissions/mod.rs:98-189`):**
   - Every MIR `Place` holds `Permissions { read: bool, write: bool, drop: bool }` (`drop` is rendered pedagogically as **Own (`O`)** alongside `R` and `W`, lines 100-108).
   - `PermissionsData` (lines 118-145) preserves first-order provenance: static type capabilities (`type_droppable`, `type_writeable`, `type_copyable`), liveness/initialization (`is_live`, `path_uninitialized`, `path_moved: Option<MoveKey>`), and active Polonius loan refiners (`loan_refined: LoanRefined<LoanKey>`, `loan_drop_refined: Option<LoanKey>`).
   - Exact derivation (`permissions_ignore_liveness`, lines 173-180; dead places collapse to $\emptyset$):
     ```rust
     let mem_uninit = self.path_moved.is_some() || self.path_uninitialized;
     let read  = !mem_uninit && !self.loan_refined.is_read_refined();
     let write = self.type_writeable && read && !self.loan_refined.is_write_refined();
     let drop  = self.type_droppable && read && self.loan_drop_refined.is_none();
     ```
     Linking permission deltas to `Refiner::{Loan(LoanKey), Move(MoveKey)}` and `RefinementRegion` turns abstract borrow conflicts into concrete missing-capability explanations.
2. **SCC Region-Flow Fault Classification (`crates/aquascope/src/analysis/permissions/flow.rs:1-291`):**
   - Under `ENABLE_FLOW_PERMISSIONS`, `RegionFlows` (lines 170-188) condenses Polonius `subset_base` edges into `Sccs<Origin, SccIdx>`, stores user-declared bounds in `specified_flows` (`known_placeholder_subset`), and tracks abstract ($\varrho$) vs. local ($S$) taint.
   - `flow_kind(from, to)` (lines 217-291) classifies lifetime errors into **`LocalOutlivesUniversal`** (local stack borrow escaping to a universal lifetime parameter), **`MissingUniversalConstraint`** (abstract $\varrho_1 \to \varrho_2$ lacking `'from: 'to`), and **`LocalInvalidatedAtExit`** (local dangling across a scope exit). `flow.rs:56-66` explicitly excludes `impl Trait` hidden-type member constraints and pure concrete-value lifetime conflicts.

---

### 4. Resilient Live Parsing Under Elaboration-Dependent Syntax (`Lean 4`, `Agda`, `Scala 3`, `rust-analyzer`)

Basis: documentation + source + derived

IDE-grade resilient parsers (`rust-analyzer`, cross-referenced in `language-server-snapshots-views-and-compiler-backed-ide-architectures`; Kladov's *Resilient LL Parsing Tutorial*) preserve lossless CSTs with local `ERROR` nodes, token-consumption progress invariants, and delimiter recovery sets—all predicated on a **static grammar**. User-extensible mixfix notations and macros that mutate parser tables mid-file break that premise directly.

#### 4.1 `Lean 4`: Elaboration-Coupled Parsing, Two-Command Rewind, and `recover'` vs. `<|>`

Direct inspection of `leanprover/lean4@8009d0a64d2860606c6a5ac5ff6702622b24921e` (implementing Ullrich & de Moura, *Beyond Notations*, IJCAR 2020 / LMCS 2022, `arXiv:2001.10490`) reveals four concrete structural costs:

1. **Sequential parse–elaborate coupling (`src/Lean/Language/Lean.lean:558-754`):** `parseCmd` passes `pmctx := { env := cmdState.env, ... }` to `Parser.parseCommand` (lines 595-601) and waits for `doElab` to complete before parsing the next command (`-- for now, wait on "command finished" snapshot before parsing next command`, lines 658, 682, 753) because command $k$ may register `syntax`, `notation`, `infix`, or `macro_rules` extensions in `cmdState.env`.
2. **Two-command backward invalidation (`# Note [Incremental Parsing]`, `Language/Lean.lean:21-79, 442-447, 587-591`):** Backtracking across `atomic` rules allows an edit after command $k$ to alter command $k$'s parse (e.g., deleting the space in `def a := b private def c` turns `private def` into an argument `privatedef`). Worse, inserting `s` into `Sort` in:
   ```lean
   structure Signature where
     /-- a docstring -/
     Sort : Type
   ```
   re-attaches a previously split docstring command back onto `structure`, breaking Lean 3's 1-command rewind and forcing Lean 4 to rewind **two commands** because no parser high-water mark is tracked.
3. **Recovery vs. extensible choice conflict (`src/Lean/Parser/Basic.lean:325-361, 452-453, 1426`):** `recoverFn` catches errors, logs `recoveredErrors`, and inserts `Syntax.missing`, but `recover'`'s docstring (lines 347-360) explicitly warns against using it in user-extensible `<|>` categories because eager recovery prevents backtracking to user-registered notations.
4. **Intra-command promise snapshots and sound cancellation (`Language/Lean.lean:81-230`):** Lean 4 threads `IO.Promise`-backed `SnapshotBundle` trees (`withNarrowedArgTacticReuse`, `withoutTacticIncrementality` for multi-pass tactics like `induction`), disables macro incrementality when traces or wide default `ref` spans appear, and uses per-subtree `IO.CancelToken`s (`SnapshotTask.cancelRec`) because eager whole-file cancellation is unsound under parallel async kernel tasks.

#### 4.2 Architectural Spectrum Across Extensible and Resilient Frontends

| Architecture | Inspected Source | Grammar Resolution Timing | Statement-Grammar Mutation? | Live Error Recovery | Principal UX Trade-Off |
|---|---|---|---|---|---|
| **Static Resilient LL CST** (`rust-analyzer`) | Cross-ref `language-server-snapshots-*` | Phase 1 (static) | No (proc macros take balanced `TokenTree`s) | High (local delimiter recovery) | Proc macros fail wholesale on incomplete arguments |
| **Typed-AST Quotes** (`Scala 3`) | `scala/scala3@90f3daf0`: `library/src/scala/quoted/Quotes.scala:24-100` | Phase 1 (fixed `${...}` / `'{...}` syntax); macros operate on typed `Expr[T]`/`Type[T]` | No | High (static grammar unaffected by macros) | Less custom surface syntax; macro exceptions arise post-typing |
| **Two-Stage Mixfix** (`Agda`) | `agda/agda@9691cf23`: `src/full/Agda/Syntax/Concrete/Operators.hs:6-200, 573-807` | Stage 1: flat `RawApp`/`RawAppP`; Stage 2: scope-checked `buildParsersFromOperatorScope` with `Trie` filtering | Expressions/patterns only | Medium (Stage 1 survives broken mixfix) | Late Stage-2 `NoParseForApplication` / `AmbiguousParseForLHS` errors (`OperatorInformation`) |
| **Elaboration-Coupled** (`Lean 4`) | `leanprover/lean4@8009d0a6`: `Language/Lean.lean`, `Parser/Basic.lean` | Interleaved command-by-command (`cmdState.env`) | Yes (`syntax`, `declare_syntax_cat`, `macro_rules`) | Low-to-Medium (2-cmd rewind; `recover'` avoids extensible `<|>`) | Slow/failing command $k$ blocks parsing command $k+1$ |
| **Projectional Holes** (`Hazel`) | Omar et al. 2019; Zhao et al. 2024 | Structural editing preserves AST with holes | No | Total (no unparseable states) | Text-editing ergonomics vs. free-form editors |

---

### 5. Verification Failure UX: Backward VCG Opacity, SMT `unknown`/Triggers, and Giant-Step Counterexample Validation (`Dafny`, `Why3`)

Basis: documentation + source + execution + derived

#### 5.1 Backward VCG, E-Matching Trigger Pathologies, and the Triage Crisis

In SMT-backed deductive verifiers (`Dafny`, `Why3`, `Viper`, `F*`, `Verus`), weakest-precondition VC generation lowers a procedure into a first-order query with heap and quantifier axioms. Because first-order SMT with quantifiers and nonlinear arithmetic is undecidable, an `unknown`, `timeout`, or raw satisfying model leaves the user unable to distinguish (1) a **real code bug**, (2) a **too-weak loop invariant or callee contract**, or (3) **prover incompleteness**.

Under E-matching quantifier instantiation (Leino & Pit-Claudel, CAV 2016, DOI `10.1007/978-3-319-41528-4_20`), **cyclic triggers** cause non-terminating matching loops (`timeout` / "butterfly effect"), while **missing instantiations** leave true quantified axioms or uninterpreted helper functions unconstrained, letting the SMT solver fabricate **spurious counterexamples** (e.g., `sq(3) = -7`). Dafny counters matching loops in the frontend via `Source/DafnyCore/Triggers/TriggersCollector.cs:44-180` (filtering trigger killers and translating nonlinear ops under `/noNLarith`) and `QuantifierSplitter.cs`.

#### 5.2 `Dafny`: Unvalidated Model Extraction Disclaimers and Proof-Dependency Diagnostics

Direct inspection of `dafny-lang/dafny@8c137ba351c60a521cfb122011770fdbea9a0453` documents two complementary mechanisms:

1. **Raw Model Extraction (`Source/DafnyCore/CounterExampleGeneration/DafnyModel.cs:46-202`, `PartialState.cs:13-238`):** `DafnyModel` decodes Boogie `Model.CapturedState` tables across 30+ internal SMT functions (`MapType0Select`, `Seq#Length`, `$Is`, `U_2_int`, `$LS`/`$LZ`, lines 53-90), assigns unused concrete primitives (`AssignConcretePrimitiveValues`, lines 104-172), and builds balanced `AssumeStmt`s guarded by `counterexampleLoopGuard`s (`PartialState.cs:89-155`). Because raw solver models are not dynamically validated, **`DafnyModel.ToString()` (`DafnyModel.cs:190`) explicitly warns:**
   > `WARNING: the following counterexample may be inconsistent or invalid. See dafny.org/dafny/DafnyRef/DafnyRef#sec-counterexamples`
2. **Unsat-Core Proof-Dependency Warnings (`Source/DafnyCore/ProofDependencyWarnings.cs:17-216`):** On passing VCs, Dafny diffs SMT `CoveredElements` against `potentialDependencies` to warn on vacuous proofs (`"proved using contradictory assumptions"`, lines 104-124), `"unnecessary requires clause"` (lines 126-132), unused visible functions (`SuggestFunctionHiding`, lines 151-156), and single-use lemmas (`SuggestByProofRefactoring`, lines 158-216)—reducing irrelevant SMT context that drives trigger instability.

#### 5.3 `Why3`: Giant-Step Assertion Checking and 5-Verdict Classification

Becker, Belo Lourenço & Marché (*Explaining Counterexamples with Giant-Step Assertion Checking*, F-IDE 2021, EPTCS 338, pp. 82–88, DOI `10.4204/EPTCS.338.10`, `arXiv:2108.02967`), inspected directly in `AdaCore/why3@02050ad2905bc0f54e7efdf7ad809cfee7a67fef` (`src/mlw/check_ce.ml:28-300`, `src/mlw/rac.ml:31-282`), validate every candidate SMT counterexample by running **Run-Time Assertion Checking (RAC)** twice using the SMT model as an oracle (with range/record checks in `import_model_value`, `check_ce.ml:209-300`):

- **Normal (Concrete) RAC:** Runs actual code semantics from oracle inputs.
- **Giant-Step (Abstract) RAC:** Skips loops and function calls by checking entry invariants/preconditions, fetching post-loop variables or return values from the SMT oracle, and **assuming** the loop invariant (+ negated guard) or callee postcondition—halting in **`Res_stuck`** if the oracle violates an assumed contract, range, or axiom.

Exact classification logic in `Check_ce.classify` (`src/mlw/check_ce.ml:28, 100-188`; note line 148 `FIXME` relaxes `Sattr.mem ctx.attr vc_term_attrs || true` so location matching dominates):

| Normal RAC | Giant-Step RAC | `Why3` Verdict | Meaning & User Action |
|---|---|---|---|
| `Res_fail` at $\ell_{\text{VC}}$ | *(any)* | **`NC`** | Confirmed program bug reaching target VC. |
| `Res_fail` at $\ell \neq \ell_{\text{VC}}$ or `Res_stuck` | *(any)* | **`BAD_CE`** | Invalid oracle inputs or mismatched failure point; suppress. |
| `Res_normal` | `Res_fail` | **`SW`** | Code conforms concretely, but contracts are too weak (`report_verdict:53-57` lists exact skipped loops/callees). |
| `Res_normal` | `Res_stuck` | **`BAD_CE`** | Spurious SMT oracle violated assumed contract/axiom (e.g., untriggered quantifier); suppress. |
| `Res_normal` | `Res_normal` | **`BAD_CE`** | `"no failure"` in either semantics (e.g., trivial timeout model); suppress. |
| `Res_incomplete` | `Res_fail` | **`NC_SW`** | Concrete RAC hit computability/step limit while giant-step failed (bug or weak sub-contract). |
| `Res_incomplete` | `Res_stuck` | **`BAD_CE`** | Giant-step proved oracle violates an assumed contract. |
| `Res_normal`/`Res_incomplete` | `Res_incomplete` (or `Res_normal` when concrete incomplete) | **`INCOMPLETE`** | Validation inconclusive (e.g., non-executable ghost/quantified spec). |

#### 5.4 Executable Probe Results (`support/verify_error_localization_mus.py`, Part 2)

| Scenario | Setup & SMT Oracle | Normal RAC | Giant-Step RAC | Verdict | Action |
|---|---|---|---|---|---|
| `CE1_real_program_bug_NC` | `abs_buggy(x) = x`, `ensures ret >= 0`; `{x: -5}` | `FAIL` (`vc:abs_post`) | `FAIL` | **`NC`** | Fix code bug. |
| `CE2_weak_loop_invariant_SW` | `count_to_n(n)` (`s += 1`), weak inv `0 <= i <= n`; `{n: 2, loop_exit: {i: 2, s: 99}}` | `NORMAL` (`s = 2`) | `FAIL` (`99 != 2`) | **`SW`** | Strengthen loop invariant (`s == i`). |
| `CE3_spurious_uninterpreted_axiom_BAD_CE` | `caller_sq(x)` calls `sq` (`ensures ret == x*x && ret >= 0`); untriggered axiom gives `{x: 3, sq: -7}` | `NORMAL` (`9 >= 0`) | `STUCK` (violates `sq` post) | **`BAD_CE`** | Suppress spurious model; inspect triggers. |
| `CE4_timeout_trivial_model_BAD_CE` | Same `caller_sq(x)`; timeout default `{x: 0, sq: 0}` | `NORMAL` | `NORMAL` | **`BAD_CE`** | Suppress non-failing model (`no failure`). |
| `CE5_large_loop_concrete_incomplete_NC_SW` | `count_to_n(10^7)` exceeds 10,000-step fuel; `{loop_exit: {i: 10^7, s: 42}}` | `INCOMPLETE` | `FAIL` | **`NC_SW`** | Inspect loop invariant or reduce bound. |

---

### 6. Architectural Co-Design Synthesis

Basis: derived (synthesized from Sections 1–5)

| Failure Class | Root Defect | Co-Design Mitigation | Remaining Irreducible Cost |
|---|---|---|---|
| **Non-local HM errors** | Eager unification without provenance | Bidirectional checking + Elm/Roc `Expected`/`Context` + `Error` union-find poison; on-demand MUS/MCS or Bayesian ranking | Symmetric conflicts have no unique blame; exact MaxSMT is exponential in worst case |
| **Deep trait failures** | Flattening AND-OR search trees into text | `ObligationCause` chains + implication pruning + `#[diagnostic::on_unimplemented]` + interactive proof trees (`Argus`) | DSL libraries still require domain-aware hooks and solver instrumentation |
| **Opaque borrow errors** | Exposing raw solver region IDs (`'1: '2`) | Per-place `R`/`W`/`O` permission deltas + `Loan`/`Move` refiners + SCC taint flow (`Aquascope`) | Higher-ranked lifetimes (`for<'a>`) and `impl Trait` member constraints remain hard |
| **Broken live parsing** | Coupling parser tables to sequential elaboration | Static grammar + typed-AST macros (`Scala 3`) or two-stage mixfix (`Agda`); if full extension required (`Lean 4`), promise snapshots + 2-cmd rewind | Turing-complete parser extensions prohibit independent whole-file parsing |
| **Opaque SMT / spurious CEs** | Returning unvalidated solver models | Frontend trigger selection + quantifier splitting + unsat-core vacuity warnings (`Dafny`) + Normal vs. Giant-Step RAC validation (`Why3`) | Non-executable ghost/quantified specs hit `INCOMPLETE`; E-matching failure stays semi-decidable |

## Boundaries

- **known not to apply:**
  - *Unique single-site blame in HM inference:* As shown in `B6_symmetric_if_branches`, neither `MinErrLoc` nor `SHErrLoc` can break structural/statistical symmetry without external priors (annotations or edit history).
  - *`Aquascope` region-flow analysis (`flow.rs:56-66`):* Explicitly excludes `impl Trait` hidden-type member constraints and pure concrete-value lifetime conflicts.
  - *Single-command incremental parse rewind (`Lean 4` `Language/Lean.lean:58-79`):* Broken by nested-docstring backtracking; two-command rewind is required.
  - *Raw `Dafny` SMT model soundness (`DafnyModel.cs:190`):* Extracted models are explicitly unvalidated and may violate uninstantiated axioms.
- **unsupported:**
  - *`Lean 4` `recover'` inside user-extensible `<|>` syntax categories (`Parser/Basic.lean:347-360`):* Discouraged/unsupported because eager recovery suppresses backtracking to user notations.
  - *`Why3` Giant-Step RAC on non-executable ghost/unbounded-quantifier specs (`check_ce.ml`):* Yields `INCOMPLETE` rather than `NC`/`SW`/`BAD_CE`.
- **not examined:**
  - Neural/ML type-error blame classifiers (e.g., `Nate`, OOPSLA 2017) and LLM diagnostic rewriters.
  - C++20 Concepts / Clang template backtrace pruning, GHC `GHC.TypeLits.TypeError`, `Verus` `--expand-errors` / Axiom Profiler, and `Rocq`/`Isabelle/PIDE` document models at pinned source commits.
- **unknown:**
  - *General `isDefEq`-failure explainers in dependent-type elaborators:* No examined system (`Lean 4`, `Agda`) provides a principled minimal provenance explainer when higher-order unification or reduction diverges between identically printed terms.
  - *Sub-50 ms LSP feasibility of incremental MaxSMT/Bayesian localization:* Whether bounded `SHErrLoc`/`MinErrLoc` scales to interactive keystroke budgets on trait-heavy production codebases remains unresolved.

## Evidence

All inspections and executions were performed on `2026-11-19`.

### Pinned Source Repositories

1. `cognitive-engineering-lab/aquascope` @ `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`: `crates/aquascope/src/analysis/permissions/mod.rs:29-30, 98-189`; `flow.rs:1-66, 136-291`.
2. `cognitive-engineering-lab/argus` @ `8d41733c313e97f87c6bf390ec59f2701e4e41d9`: `crates/argus/src/proof_tree/mod.rs:39-177`; `topology.rs:31-140`.
3. `elm/compiler` @ `1c278bf5ecf4136f122ce1cba436783c7f561dac`: `compiler/src/Type/Constrain/Expression.hs:42-221`; `Reporting/Error/Type.hs:44-250`; `Type/Error.hs:37-58, 157-300`; `Type/Unify.hs:25-49`; `Type/Solve.hs:77-162`.
4. `roc-lang/roc` @ `63434e9847e74db8ffed7e9244bcb8317771c350`: `src/check/problem/context.zig:1-250`.
5. `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`: `compiler/rustc_middle/src/traits/mod.rs:44-260`; `compiler/rustc_trait_selection/src/error_reporting/traits/mod.rs:141-340`; `fulfillment_errors.rs:93-320`; `on_unimplemented.rs:34-260`.
6. `leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`: `src/Lean/Language/Lean.lean:21-230, 438-487, 558-754`; `src/Lean/Parser/Basic.lean:318-374, 452-453, 1426`.
7. `agda/agda` @ `9691cf2331ed3d5f9aba04380cc1cc8f415d192e`: `src/full/Agda/Syntax/Concrete/Operators.hs:6-13, 86-200, 573-590, 700-706, 807`.
8. `scala/scala3` @ `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`: `library/src/scala/quoted/Quotes.scala:24-100`.
9. `dafny-lang/dafny` @ `8c137ba351c60a521cfb122011770fdbea9a0453`: `Source/DafnyCore/CounterExampleGeneration/DafnyModel.cs:46-202`; `PartialState.cs:13-238`; `Triggers/TriggersCollector.cs:12-180`; `ProofDependencyWarnings.cs:17-216`.
10. `AdaCore/why3` @ `02050ad2905bc0f54e7efdf7ad809cfee7a67fef`: `src/mlw/check_ce.ml:28-300`; `src/mlw/rac.ml:31-55, 275-282`.
11. `ucsd-progsys/nanomaly` @ `0de06f2c3a41063b1bf87d5f6dd11ad830be0512`: `src/NanoML/Step.hs:88-154`; `src/NanoML/Explore.hs:25-153`.

### Peer-Reviewed Literature & Preserved Probe

- Lee & Yi (TOPLAS 1998, `10.1145/291891.291892`); Wand (POPL 1986, `10.1145/512644.512648`); Haack & Wells (ESOP 2003, `10.1007/3-540-36575-3_20`); Zhang & Myers (POPL 2014, `10.1145/2535838.2535870`); Zhang, Myers, Vytiniotis & Peyton Jones (PLDI 2015, `10.1145/2737924.2738009`); Pavlinovic, King & Wies (OOPSLA 2014, `10.1145/2660193.2660230`; ICFP 2015, `10.1145/2784731.2784765`); Chen & Erwig (POPL 2014, `10.1145/2535838.2535863`); Seidel, Jhala & Weimer (ICFP 2016, `10.1145/2951913.2951915`); Omar et al. (POPL 2019, `10.1145/3290327`); Zhao et al. (POPL 2024, `10.1145/3632910`); Dunfield & Krishnaswami (CSUR 2021, `10.1145/3450952`, `arXiv:1908.05839`); Crichton, Gray & Krishnamurthi (OOPSLA 2023, `10.1145/3622841`); Gray, Crichton & Krishnamurthi (PLDI 2025, `10.1145/3729302`, `arXiv:2504.18704`); Ullrich & de Moura (IJCAR 2020 / LMCS 2022, `arXiv:2001.10490`); Leino & Pit-Claudel (CAV 2016, `10.1007/978-3-319-41528-4_20`); Becker, Belo Lourenço & Marché (F-IDE 2021, EPTCS 338:82–88, `10.4204/EPTCS.338.10`, `arXiv:2108.02967`).
- [`support/verify_error_localization_mus.py`](support/verify_error_localization_mus.py): Executed via `python3 -B support/verify_error_localization_mus.py` (exit `0`), confirming all `B1`–`B6` and `CE1`–`CE5` assertions.

## Revalidation

1. **Re-run the preserved probe:**
   ```console
   python3 -B reports/type-error-localization-compiler-diagnostics-and-verification-ux/support/verify_error_localization_mus.py
   ```
   A zero exit confirms all `Algorithm W`/`M` vs. `MUS`/`MCS`/`SHErrLoc` and Why3-equivalent Giant-Step RAC invariants.
2. **Targeted upstream diffs:**
   - `leanprover/lean4` (`src/Lean/Language/Lean.lean`, `src/Lean/Parser/Basic.lean` vs. `8009d0a64d28`): check for parser high-water-mark tracking or decoupling of syntax parsing from command elaboration.
   - `rust-lang/rust` (`compiler/rustc_trait_selection/src/error_reporting/traits/` vs. `b0b600668bb9`): check whether interactive next-solver proof-tree inspection enters `rustc`.
   - `dafny-lang/dafny` (`DafnyModel.cs:190`, `ProofDependencyWarnings.cs` vs. `8c137ba351c6`): check whether execution/giant-step counterexample validation removes the invalidity disclaimer.
   - `AdaCore/why3` (`src/mlw/check_ce.ml` vs. `02050ad2905b`): check whether `is_vc_term` tightens attribute matching or expands `type verdict`.
   - `cognitive-engineering-lab/aquascope` (`permissions/{mod.rs,flow.rs}` vs. `f2d0a06034b8`) and `roc-lang/roc` (`src/check/problem/context.zig` vs. `63434e9847e7`): check `ENABLE_FLOW_PERMISSIONS` defaults and hidden-type region support.
3. **Literature checks:** Monitor post-2025 POPL/PLDI/OOPSLA/CAV/ITP venues for sub-50 ms incremental MaxSMT/Bayesian localization in production IDEs and general `isDefEq`-failure explainers.
