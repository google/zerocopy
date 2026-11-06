# Rust Lifetime and Borrow Verification, Prophecies vs. Backward Functions, Charon/Aeneas Region Lowering, and Trace-Preserving Loop Reasoning in Lean 4

## Summary

Rust verifiers that eliminate or abstract mutable memory borrows must address two distinct obligations: how to represent a live mutable borrow (`&'a mut T`) and return its final mutated value to the suspended owner when lifetime `'a` expires, and what establishes that the source program satisfies the aliasing and lifetime assumptions of that representation:

1. **Four Architectural Families for Mutable-Borrow and Lifetime Reasoning:**
   Across published Rust verification systems (`support/rust-lifetime-resource-reasoning-approaches/approach-map.json`), borrow termination is modeled by:
   - **Semantic lifetime resources in separation logic (`RustBelt`, `RefinedRust`, `lambda-rust`):** Lifetimes (`&'κ uniq T`) are first-class step-indexed Iris resources that split ownership across time and support unsafe library verification via the semantic fundamental theorem.
   - **Current/future prophecy pairs (`RustHorn`, `RustHornBelt`, `Thrust`, `Creusot`):** A mutable reference `&mut T` is represented as a pair `(current_value, future_prophecy_value)` (`*x` and `^x`), resolving the prophecy to the final current value when the borrow expires (with `RustHornBelt` supplying parametric prophecies in Iris to bridge unsafe implementations to first-order functional client specifications).
   - **Loan graphs and functional backward functions (`Aeneas`, `Cryspen hax`):** Borrow termination is compiled into pure forward functions paired with backward functions that consume updated borrowed values and return reconstructed lender states.
   - **Type-derived Viper permissions and expiry pledges (`Prusti`):** Ownership and framing permissions are synthesized from `rustc` typing, with `before_expiry` and `after_expiry` pledges expressing deferred postconditions for returned mutable references.
2. **Region Representation Shifts Across `rustc`, `Charon`, and `Aeneas`:**
   At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, non-lexical lifetime (NLL) borrow checking (`compiler/rustc_borrowck/src/lib.rs`, `nll.rs`, `renumber.rs`) clones promoted MIR into a private working copy (`body_owned = input_body.clone()`), replaces all regions with fresh `RegionVid` inference variables, and solves constraints in `RegionInferenceContext`, while post-borrowck MIR (`mir_drops_elaborated_and_const_checked`) steals the original promoted MIR and strips borrow-check statements (`CleanupPostBorrowck`). `AeneasVerif/charon` (`0.1.210` at `a535e914f74db4fd9e6be7048f4233270d8945c0`) hooks `after_expansion` before MIR analysis and reads `mir_promoted`: it preserves signature-level `Region::Var`, `Region::Static`, outlives clauses, and ADT `LifetimeMutability`, while converting erased body regions (`ReErased`) into fresh synthetic existential `Region::Body` IDs (`translate_erased_region`). `Aeneas` (`ac9f1bc5262a5e4ff1e24ca78617121382202727` and `70683bd4ab876179a23e5f994d02947b3e5c4f0d`) then erases local/place body regions (`PrePasses.erase_body_regions`), groups mutually outliving signature regions into strongly connected `RegionGroupId` hierarchies (`RegionsHierarchy.ml`) that drive symbolic borrow abstractions and backward function synthesis (`Interp.ml`), and finally erases lifetime parameters and `&`/`&mut` type constructors in `SymbolicToPureTypes.ml` (`choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` becomes `def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`).
3. **Paired `Charon`/`Aeneas` Version Coupling and Translation Specimen Boundaries:**
   Executing the 8-case Rust-to-LLBC-to-Lean specimen suite (`support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/`) across `Aeneas` June 1 (`f95a80abaf554d4612cb60ef9ec8e849139bec44` + `Charon` `0.1.208`) and `Aeneas` June 3 (`ac9f1bc5262a5e4ff1e24ca78617121382202727` + `Charon` `0.1.210` at `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`) shows that cross-paired binaries fail LLBC schema version validation (`aeneas-revision-matrix.json`), whereas matching pairs emit byte-identical `Baseline.lean` output (1,120 bytes, SHA-256 `3d854188c5820b9d08f9d767a7af2efb520140017243afa9cdcc3eb0b1cd503f`) despite distinct serialized LLBC hashes. Safe arithmetic, branching, `&mut` updates, closures, traits, loops, type-alias namespaces, and duplicate names translate to Lean 4 (`v4.30.0-rc2`), whereas `raw_pointer` and `function_pointer` specimens extract to LLBC in `Charon` and fail closed with source-located unsupported diagnostics in `Aeneas`.
4. **Aeneas/Hax `Result` CCPO vs. RefinedRust/Lithium Goal-Directed Stepping and Telescopic `ArgSpec` Contracts:**
   In `Aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) and `cryspen/hax` (`1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`, which unifies onto `public import Aeneas`), `Result α` (`.ok`, `.fail`, `.div`) carries a `CCPO` over `FlatOrder .div` for `partial_fixpoint` loops, paired with `@[step]`/`step*` e-graph automation (`StepGrindState`), `predn` curried postconditions, and `ITreeWP` (`DWP`/`DWLP`). In `RefinedRust` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) and `RefinedC` (`d057583986651a28047164581f05fbee3a83ed9d`), `radium` emits a uniform 7-line Rocq proof script (`rep <-! liRStep; liShow`) backed by Lithium's syntax-directed interpreter, `SHELVED_SIDECOND`, `CACHED`/`JCACHED` join-block caching, and `RUST_PROGRAM_POINT` diagnostics. In `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean`, we mechanize a single generic `FnSig`/`FuncSpec` contract and an inductive `ArgSpec` telescope (`nil`, `val`, `boolVal`, `mutRef`, `mutRefFrom`) that replaces 15 shape-specific `Ensures*` predicates with one 35-line soundness theorem (`funcSpec_verified`) and a uniform one-line tactic (`by anneal_vcgen`) with `ShelvedVC` source-span and branch-trace diagnostics.
5. **Trace-Preserving Functional Translation (`TrackedFuncLang`), Fuel-Free Loop Invariants, and Constant-Time 2-Safety:**
   In `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeTrackedFuncLangAndLoops.lean`, upgrading symbolic evaluation to `evalSymWithTracked` and `TrackedFuncLang` preserves `[StepObs.step]` observations in 1-to-1 lockstep across all 5 MIR terminators (`evalSymWithTracked_sound : ForwardSim MirLang TrackedFuncLang`), proves fuel-free loop termination and exact trace length $n + 2$ via well-founded ranking measures (`tracked_loop_spec_decr_nat` and `sumToN_satisfies_fuelFree_specOn`), collapses $k$ sequential CFG diamonds from $2^{k+1} - 2$ states to $2k$ obligations (`diamond_join_cutpoint` + `JCACHED` in `twoDiamondBody_verified_linear`), and proves relational constant-time 2-safety (`trackedFuncLang_implies_constantTime2Safety` and `ctPublicModeXor_is_constant_time`).

## Applicability

This report covers the publications, compiler/extractor revisions, verifier repositories, and Lean 4 toolchains recorded in `REPORT.json`:

- **Foundational Publications on Rust Borrow and Lifetime Reasoning:**
  - `RustBelt` (POPL 2018, DOI `10.1145/3158154`), `Prusti` (OOPSLA 2019, DOI `10.1145/3360573`), `RustHorn` (ESOP 2020, DOI `10.1007/978-3-030-44914-8_18`), `Aeneas` (ICFP 2022, DOI `10.1145/3547647`), `RustHornBelt` (PLDI 2022, DOI `10.1145/3519939.3523704`), `RefinedRust` (PLDI 2024, DOI `10.1145/3656422`), and `Thrust` (PLDI 2025, DOI `10.1145/3729333`).
- **`rustc`, `Charon`, and `Aeneas` Multi-Version Coverage:**
  - **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `nightly`) and `google/zerocopy` (`41f5b37afe7060fd9fe08c00b200672cd76d77b9`):** Examined for HIR/MIR region lowering, private NLL MIR cloning, and `CleanupPostBorrowck`.
  - **`AeneasVerif/charon` Revisions:**
    - `0.1.208` (`6101d742777bf9f9b48979ac1ad4d2c07dfe10db`, pinned by Aeneas June 1 `f95a80abaf554d4612cb60ef9ec8e849139bec44`);
    - `0.1.210` (`a535e914f74db4fd9e6be7048f4233270d8945c0` and `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, pinned by Aeneas June 3 `ac9f1bc5262a5e4ff1e24ca78617121382202727`).
  - **`AeneasVerif/aeneas` Revisions:**
    - Release `f95a80abaf554d4612cb60ef9ec8e849139bec44` (2026-06-01);
    - Release `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`, 2026-06-03);
    - Upstream Lean 4 backend revision `70683bd4ab876179a23e5f994d02947b3e5c4f0d` (2026-10-30), paired with `cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`.
  - **Version-Invariant vs. Version-Specific Behavior Across `Charon` and `Aeneas`:**
    - *Invariant across all examined `Charon` and `Aeneas` revisions:* Extraction of `mir_promoted` prior to `rustc_borrowck`, synthesis of fresh `Region::Body` IDs for `ReErased` inside bodies, early erasure of local/place body regions in `PrePasses.erase_body_regions`, SCC grouping of signature regions in `RegionsHierarchy.ml`, and complete erasure of region parameters and `&`/`&mut` constructors in `Pure.ty` (`SymbolicToPureTypes.ml`).
    - *Version-specific:* Serialized LLBC schema version numbers change between `Charon` `0.1.208` (`f95a80ab`) and `0.1.210` (`ac9f1bc5`), causing cross-paired `Aeneas` invocations to fail immediately. In `Aeneas` Lean backend development between `ac9f1bc5` (June 2026) and `70683bd4` (October 2026), the forward proof tactic evolved from `@[progress]`/`progress` to `@[step]`/`step`/`step*` backed by a persistent incremental `StepGrindState` e-graph, and `ITreeWP` (`DWP`/`DWLP`/`AWP`/`AWLP` in `Taxonomy.lean`) plus `Std.Do.WP Result .pure` were added.
- **Comparative Verifier Repositories and Lean 4 Toolchains:**
  - `lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, `iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, `creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`, `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, `model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`, `GillianPlatform/Gillian@83d739e83034d71162fb66b569041cf301123df7`, `iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`, and `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`.
  - **Lean 4 (`leanprover/lean4`):** `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, used for checking `Aeneas` `ac9f1bc5` specimen outputs) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, used to kernel-check `ProbeGeneralSpecAndLithium.lean` and `ProbeTrackedFuncLangAndLoops.lean`).

## Findings

### 1. Comparative Taxonomy of Lifetime, Prophecy, and Resource Reasoning Approaches

**Basis:** `source` (publications and repository implementations) + `derived` synthesis (`support/rust-lifetime-resource-reasoning-approaches/approach-map.json`).

Every verifier that supports mutable borrows (`&'a mut T`) must model both phases of the temporal split: what capability or value is available while the borrow is live, and how the updated value or resource returns to the suspended owner when `'a` expires:

| System / Publication | 1. Live Borrow Representation | 2. Lender State Recovery at Expiry | 3. Memory-Erasure Premise | 4. Unsafe Code & Frontend Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **RustBelt** (`10.1145/3158154`) & **`lambda-rust`** (`186900b2`) | Iris lifetime token `[\kappa]_q` and full borrow `&^{\kappa} P` over semantic heap predicates. | Closing lifetime $\kappa$ restores the full resource $P$ (updated by borrower). | Retains explicit heap/locations in Iris separation logic. | Directly verifies unsafe library implementations in Coq/Iris; safe clients compose via the fundamental theorem. |
| **RefinedRust** (`10.1145/3656422`, `8a07f4f2`) | Iris lifetime logic enriched with borrow names and value-level refinement types (`&uniq`). | Borrow-name resolution restores strengthened refinement predicate to owner when lifetime expires. | Explicit Caesium `(block_id, offset)` byte heap beneath automated Lithium typing rules. | Verifies both safe and unsafe Rust in Rocq; `radium` frontend supplies lifetime hints that Rocq typing rules check. |
| **RustHorn** (`10.1007/978-3-030-44914-8_18`) | Pair `(v_cur, v_final)` of current value and deadline prophecy variable in CHCs. | Releasing `&mut T` constrains prophecy `v_final = v_cur`, updating the lender's logical state. | Assumes source program is well-borrowed safe Rust (erases heap to first-order CHCs). | Cannot verify raw-pointer unsafe implementations directly without a semantic bridge. |
| **RustHornBelt** (`10.1145/3519939.3523704`) | Parametric prophecies inside Iris separation logic coupled with RustBelt lifetime tokens. | Resolves parametric prophecy assignment when borrow ends. | Safe clients see pure first-order functional specs; unsafe boundary proved in Iris. | Provides the foundational Iris soundness bridge for prophecy-based functional specifications of unsafe APIs. |
| **Thrust** (`10.1145/3729333`) & **Creusot** (`c4e9770a`) | Prophetic refinement type / Pearlite borrow `Bor { cur: *x, final: ^x, id }`. | Nested reborrow `r2 = &mut *r1` equates `r1.cur = r2.final` upon `r2` expiration. | Soundness is conditional on well-borrowedness (e.g. Stacked Borrows / `rustc` borrowck). | Unsafe primitives (`PermCell`, `PtrOwn`) require trusted axiomatic contracts. |
| **Aeneas** (`10.1145/3547647`, `70683bd4`) & **Hax** (`1ec88cdb`) | Symbolic loans (`aloans`) and borrow projectors (`aproj`) grouped by `RegionGroupId`. | Generated pure **backward function** consumes updated borrowed values and returns reconstructed owner values. | Eliminates heap addresses by relying on LLBC ownership/borrowing discipline. | Interior mutability and raw-pointer unsafe blocks require explicit external models or spatial extensions. |
| **Prusti** (`10.1145/3360573`) | Viper fractional/exclusive permissions synthesized from `rustc` type/borrow analysis. | Permissions return at borrow end; `before_expiry` / `after_expiry` **pledges** specify returned `&mut` references. | Relies on `rustc` type/borrow checker to justify framing permissions. | Unsafe blocks and interior mutability fall outside automatic type-derived framing. |

---

### 2. Lifetime and Region Dataflow Through `rustc`, `Charon`, and `Aeneas`

**Basis:** `source` + `derived` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`).

1. **`rustc` NLL Operates on a Cloned Private MIR Body (`compiler/rustc_borrowck/src/lib.rs`, `nll.rs`, `renumber.rs`):**
   When `mir_borrowck` runs on a function, it clones the input promoted MIR (`let mut body_owned = input_body.clone(); let mut promoted = input_promoted.to_owned();`), constructs `UniversalRegions` for signature lifetimes, and invokes `renumber::renumber_mir` to overwrite every region inside `body_owned` with a fresh existential NLL `RegionVid` variable. `nll::compute_regions` then solves outlives and liveness constraints inside `RegionInferenceContext`. Crucially, when `mir_drops_elaborated_and_const_checked` (`compiler/rustc_mir_transform/src/lib.rs`) later constructs runtime MIR, it forces `mir_borrowck` to run and then steals `tcx.mir_promoted(def)`—the original un-renumbered promoted body—and runs `CleanupPostBorrowck` (`cleanup_post_borrowck.rs`), discarding `body_owned` and `RegionInferenceContext`.
2. **`Charon` Extracts `mir_promoted` Before Borrow Checking and Invents Synthetic `Region::Body` IDs:**
   `Charon` (`charon/src/bin/charon-driver/driver.rs`, `translate/get_mir.rs`, `options.rs`) hooks `after_expansion` prior to MIR analysis and queries `Promoted` MIR. In `charon/src/ast/types.rs` and `translate/translate_types.rs`:
   - `ReStatic` maps to `Region::Static`, early/bound signature lifetimes map to `Region::Var`, and ADT lifetime parameters receive a `LifetimeMutability` classification (`translate_generics.rs` and `charon/tests/ui/lifetime-mutability.{rs,out}`).
   - Inside function bodies, `rustc`'s promoted MIR exposes `ReErased` on local types; `translate_erased_region` checks whether `lifetime_freshener` is active and allocates a fresh `Region::Body` identifier for every occurrence (`charon/tests/ui/region-inference-vars.{rs,out}`). These `Region::Body` IDs are synthetic existential handles created by `Charon`, **not** `rustc`'s solved NLL `RegionVid` sets.
3. **`Aeneas` Consumes Signature Region Hierarchies Before Erasing Pure Lifetimes:**
   - **Early Body-Region Erasure (`src/PrePasses.ml`):** `erase_body_regions` erases `RBody`, `RVar`, and `RStatic` from statement types and local declarations while preserving region arguments inside function-call operands.
   - **Signature Region SCC Grouping (`src/llbc/RegionsHierarchy.ml` and `src/interp/Interp.ml`):** `compute_regions_hierarchy_for_sig` computes strongly connected components of signature lifetimes under outlives predicates, assigning each SCC a `RegionGroupId` and parent edges. Symbolic execution creates one borrow abstraction per `RegionGroupId` and synthesizes one backward function per mutable region group.
   - **Pure Type Erasure vs. Surviving Backward Structure (`src/symbolic/SymbolicToPureTypes.ml` and `src/pure/Pure.ml`):** `SymbolicToPureTypes` drops region binders, omits regions from `Pure.generic_params` and `Pure.generic_args`, and translates `TRef (_, referent, _)` to the pure referent type `T` (while keeping `llbc_generics` and `mutRegions` attributes in `ExtractTypes.ml`). In `tests/lean/Paper.lean`, `pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` translates to `def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`: the lifetime `'a` disappears from the Lean type signature, while its borrow-return obligation survives as the backward closure `T → (T × T)`.

---

### 3. Executed Rust-to-LLBC-to-Lean Specimens and `Aeneas` Revision Compatibility

**Basis:** `execution` + `derived` (`support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/RESULTS.md`, `coverage.json`, `canonical-order-check.json`, `aeneas-revision-matrix.json`, and `aeneas-revision-comparison.json`).

1. **Eight-Case Translation Specimen Matrix (`support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/cases/`):**
   Running `Charon` `0.1.210` (`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`), `Aeneas` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), and Lean `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) across eight fixture classes establishes:
   - **Supported through Lean 4 (`baseline`, `closure`, `trait`, `loop`, `alias`, `names`):** Branching lowers to `if`/`else` in `Result`, `&mut` updates lower to pure state-returning functions (`Baseline-0.lean`..`Baseline-2.lean`), closures and traits lower to explicit dictionary/struct records (`Closure-0.lean`, `Trait-0.lean`), loops lower to `loop` fixed points (`Loop-0.lean`), type aliases alter emitted Lean namespaces unless overridden (`Alias-0.lean` vs. `support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/alias-namespace/Alias-0.lean`), and duplicate item names receive deterministic disambiguation (`Names-0.lean`..`Names-2.lean`).
   - **Rejected by `Aeneas` with Source-Located Diagnostics (`raw_pointer`, `function_pointer`):** `Charon` emits valid LLBC (`support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/cases/raw_pointer/raw_pointer-0.llbc` and `cases/function_pointer/function_pointer-0.llbc`), and `Aeneas` rejects raw pointer dereferences and indirect function-pointer calls with explicit source-span errors (`src/Translate.ml`, `src/Errors.ml`).
2. **Paired `Charon`/`Aeneas` Revision Compatibility (`aeneas-revision-matrix.json`):**
   Testing the $2 \times 2$ matrix of `Aeneas` June 1 (`f95a80abaf554d4612cb60ef9ec8e849139bec44`) and June 3 (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) against `Charon` `0.1.208` and `0.1.210` confirms:
   - Both cross-paired cells (`june1-cross-pair` in `support/rust-llbc-lean-golden-and-aeneas-revision-probes/aeneas-revision/june1-cross-pair/stderr.txt`) fail immediately with an explicit LLBC version mismatch error.
   - Both matching cells (`june1-matching-pair` and `june3-matching-pair`) succeed and emit byte-identical `Baseline.lean` files (1,120 bytes, SHA-256 `3d854188c5820b9d08f9d767a7af2efb520140017243afa9cdcc3eb0b1cd503f`) even though the intermediate `.llbc` files have distinct SHA-256 digests (`455145d...` vs. `3e081d...`).

---

### 4. `Aeneas`/`Hax` and `RefinedRust`/`Lithium` Proof Engines vs. Telescopic `ArgSpec` in Lean 4

**Basis:** `source` + `execution` + `derived` (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, `cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`, `lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, `iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, `joshlf/anneal@c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, and `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean`).

#### 4.1 `Aeneas` (`70683bd4`) and `Cryspen hax` (`1ec88cdb`) Lean 4 Architecture

In `backends/lean/Aeneas/Std/Primitives.lean` (lines 50–222) and `Std/WP.lean` (lines 9–529), `Aeneas` defines `Result α` (`.ok`, `.fail`, `.div`) with `CCPO (Result α)` over `FlatOrder Result.div` and `MonoBind Result`, lowering Rust loops to `partial_fixpoint` definitions over `ControlFlow α β`. Its verification layer combines:
- Curried n-ary postconditions `predn (ty : List (Type u))` (`Std/WP.lean:61-65, 127-155`) that eliminate nested tuple projections (`x.1`, `x.2.1`) when destructuring multi-borrow backward returns;
- Coinductive Interaction Tree modalities (`DWP`, `DWLP`, `AWP`, `AWLP` in `Data/Coinductive/ITreeWP/Taxonomy.lean:1-39`) and a `Std.Do.WP Result .pure` instance (`Std/WP.lean:447-480`) compatible with Lean 4.34+ `mvcgen`;
- The `@[step]` / `step*` forward symbolic execution engine (`Tactic/Step/Init.lean`, `Step.lean:355-755`, `StepStar.lean:415-895`), which indexes specifications in a `DiscrTree`, maintains a single persistent `StepGrindState` (`Sym.State` + `Grind.Goal`) across sequential binds to avoid $O(N^2)$ context re-internalization, prunes infeasible branches via `esplitAtSpec`, and isolates large power-of-two bounds (`U64.max`, `U128.max`, `I128.max`) behind `irreducible_def` for `scalar_tac` and `bv_tac` (`Std/Scalar/Core.lean:66-300`);
- Unification of `cryspen/hax` (`hax-lib/proof-libs/lean/CoreModels/RustPrimitives/Types.lean:1-13` and `Arithmetic.lean:1-59`) directly onto `public import Aeneas`.

#### 4.2 `RefinedRust` / `Lithium` Goal-Directed Engine and `ProbeGeneralSpecAndLithium.lean`

In `RefinedRust` (`rr_frontend/radium/src/code.rs:1381-1426` and `theories/refinedrust/lithium/interpreter.v:354-976`), `radium` emits a fixed 7-line Rocq proof script (`rep <-! liRStep; liShow; ...; Unshelve. all: sidecond_solver`) for every function. Lithium steps deterministically without backtracking over a restricted separation-logic grammar (`FindInContext`, `Subsume`, `case_if`, `li_trace`), shelves pure obligations via `SHELVED_SIDECOND`, caches proved pure obligations (`CACHED`) and join-block preconditions (`JCACHED` in `rust_typing/automation/proof_state.v:63-164`), and attributes failed goals to Rust source locations and branch traces via `RUST_PROGRAM_POINT` and `CASE_DISTINCTION_INFO`.

In `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean` (784 lines, SHA-256 `65f8af557997769bd43b4ce6eac36b79e1555bd222b75f31a4b439f08016895a`, zero `sorry`, verified under Lean `v4.34.1`), we mechanize this architecture for Anneal's MIR semantics:
1. **Generic `FnSig` and `FuncSpec` (lines 204–223) + Telescopic `ArgSpec` (lines 502–561):** Replaces 15 shape-specific `Ensures*` predicates (`Ensures`, `Ensures2`, `EnsuresMut1`, `EnsuresMaxAssign`, `EnsuresClampAssign`, `EnsuresChooseMut`, etc.) and 15 `translate_*_spec` unpacking theorems with a single `FnSig` (`pre : MirState → Prop`, `post : MirState → MirState → Prop`), an inductive `ArgSpec : Nat → Type` (`nil`, `val`, `boolVal`, `mutRef`, `mutRefFrom`), and one 35-line generic soundness theorem `funcSpec_verified` (lines 601–650):
   ```lean
   theorem funcSpec_verified (body : Body) (fuel : Nat) (spec : ArgSpec n)
       (heval : ∀ args, spec.symPre args →
         ∃ ret outArgs, evalSymWith fuel body args = some (ret, outArgs) ∧
           spec.symPost args ret outArgs) :
       FuncSpec body (spec.toFnSig n)
   ```
2. **Source-Attributed Shelving (`ShelvedVC`, lines 244–253) and Uniform `anneal_vcgen` (lines 674–782):** `vcgenSym` wraps assertions and postconditions in `ShelvedVC (span : SourceSpan) (branchTrace : List String) (label : String) (P : Prop) : Prop := P`, preserving the exact Rust file, line, column, snippet, and branch path whenever a side condition remains open, while discharging `maxAssign_verified`, `clampAssign_verified`, and lifetime-linked `chooseMut_verified` (`RetPlaceGives`) via the identical one-line proof `by anneal_vcgen`.

---

### 5. Trace-Preserving Functional Translation (`TrackedFuncLang`), Compositional Loops, and Constant-Time 2-Safety

**Basis:** `source` + `execution` + `derived` (`support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeTrackedFuncLangAndLoops.lean`, 2,199 lines, SHA-256 `98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66`, zero `sorry`, verified under Lean `v4.34.1`).

1. **Lockstep Trace Preservation (`evalSymWithTracked` and `TrackedFuncLang`, lines 714–1215):**
   Whereas baseline `FuncLang` collapses intermediate basic-block transitions into stutter steps emitting `[] : List StepObs`—erasing step counts and timing traces—`evalSymWithTracked` accumulates `[StepObs.step]` at every basic-block dispatch (`return_`, `goto`, `switchInt`, `assert`, `call`), and `TrackedFuncLang` emits one `StepObs` per step from the accumulated trace. `evalSymWithTracked_sound` (lines 1029–1170, using only `[propext, Quot.sound]`) proves lockstep `Refinement.ForwardSim MirLang TrackedFuncLang (π_tracked callEnv)`, yielding exact step counts (`trackedFuncLang_exact_trace_length_at_steps`, lines 1179–1197) and end-to-end `Language.SpecOn MirLang` adequacy (`trackedFuncLang_adequacy_specOn`, lines 1201–1215).
2. **Fuel-Free Compositional Loop Invariants (`tracked_loop_spec_decr_nat`, lines 1255–1694):**
   Proved by strong induction (`Nat.strong_induction_on`) on a natural-number ranking measure `measure : SymEnv → Nat`, `tracked_loop_spec_decr_nat` existentially quantifies the symbolic evaluation fuel `∃ fuel` inside its conclusion (`fuel := stepFuel * (measure initEnv + 1)`). Applied to the cyclic 4-block MIR program `sumToNBody` (`while i < n { acc += i; i += 1 }`), `sumToN_verified_via_ranking_measure` and `sumToN_satisfies_fuelFree_specOn` (lines 1574–1694) prove a 100% fuel-free `Language.SpecOn MirLang` contract establishing $2 \cdot \mathit{ret} = n(n - 1)$ and exact trace length $\text{trace.length} = n + 2$ for all $n \le 1000$.
3. **Diamond CFG Join Cutpoints and `JCACHED` Subsumption (`diamond_join_cutpoint`, lines 1712–1940):**
   Factoring multi-predecessor join blocks through an intermediate invariant `joinInv : SymEnv → List StepObs → Prop` (`diamond_join_cutpoint`) and caching proved pure obligations via `JCACHED (P : Prop) : Prop := P` (`cache_sidecond` / `solve_with_jcache`) reduces $k$ sequential `if`/`else` diamonds from $2^{k+1} - 2$ symbolic states to $2k$ branch obligations (`twoDiamondBody_verified_linear`, verifying a 7-block, 2-diamond MIR function in $2k = 4$ linear steps).
4. **Relational Constant-Time 2-Safety (`BranchAligned` and `trackedFuncLang_implies_constantTime2Safety`, lines 1955–2194):**
   When two symbolic argument vectors `args1` and `args2` satisfy `BranchAligned callEnv fuel body args1 args2` (taking identical control-flow edges at every terminator while differing on secret scalar values), `evalSymTracked_trace_eq_of_branchAligned` proves their emitted `List StepObs` traces are identical ($\tau_1 = \tau_2$), and `trackedFuncLang_implies_constantTime2Safety` lifts this equality through `evalSymWithTracked_sound` to establish `ConstantTime2Safety` on concrete `MirLang` executions (demonstrated on `ctPublicModeXorBody` in `ctPublicModeXor_is_constant_time` across arbitrary secret keys `secret1, secret2 : UInt32`).

## Boundaries

- **Not Examined:**
  - Fresh execution of `RustBelt`, `Prusti`, `RustHorn`, `RustHornBelt`, or `Thrust` toolchains (their comparative findings derive from primary publications and repository source inspections).
  - Irreducible multi-entry control-flow graphs with unstructured cycles outside standard single-header `loop`/`while` reducible loops (`tracked_loop_spec_decr_nat` inducts over a single `headerIdx : BasicBlockIdx`).
  - Microarchitectural intra-block side channels such as secret-dependent cache-line indexing (`arr[secret]`) or variable-latency division (`TrackedFuncLang` preserves `[StepObs.step]` basic-block-granular control-flow and loop-iteration traces; instruction-operand leakage requires enriching `StepObs` with address/operand tags).
- **Unknown:**
  - Whether `Charon`'s synthetic `Region::Body` placeholders and `Aeneas`'s `RegionsHierarchy` SCC grouping are semantically equivalent to `rustc`'s NLL `RegionInferenceContext` across all higher-ranked/late-bound lifetime edge cases (`SymbolicToPureTypes.translate_region_binder` explicitly notes De Bruijn binder level limitations when dropping region binders).
- **Known Not to Apply:**
  - `Charon`'s numeric `Region::Body` IDs do **not** represent `rustc`'s solved NLL `RegionVid` inference variables or CFG point sets.
  - Pure lifetime erasure in `Aeneas`'s `Pure.ty` does **not** mean lifetimes were ignored during translation (`RegionsHierarchy` consumes signature lifetimes first to synthesize backward functions).
  - Functional borrow-elimination approaches (`RustHorn`, `Thrust`, and pure `Aeneas`) are conditional on well-borrowed safe Rust and do **not** by themselves validate raw-pointer aliasing or interior mutability (`UnsafeCell`).
- **Unsupported:**
  - Cross-pairing `Aeneas` `f95a80ab` (June 1) with `Charon` `0.1.210` (`0c91ca1a`) or `Aeneas` `ac9f1bc5` (June 3) with `Charon` `0.1.208` (`6101d742`) is unsupported and rejected by `Aeneas`'s LLBC schema version check.
  - Raw-pointer dereference (`raw_pointer.rs`) and indirect function-pointer invocation (`function_pointer.rs`) are unsupported by `Aeneas` `ac9f1bc5` during LLBC-to-Lean translation.

## Evidence

| Artifact / Source Path | SHA-256 / Commit / DOI Identity | Evidence Role |
| :--- | :--- | :--- |
| `support/rust-lifetime-resource-reasoning-approaches/approach-map.json` | DOIs `10.1145/3158154`, `10.1145/3360573`, `10.1007/978-3-030-44914-8_18`, `10.1145/3547647`, `10.1145/3519939.3523704`, `10.1145/3656422`, `10.1145/3729333` | **source** & **derived**: Structured 4-axis comparison of lifetime, prophecy, backward-function, and permission-synthesis verifiers. |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` | `rustc_borrowck/src/{lib,nll,renumber}.rs`, `charon/src/bin/charon-driver/translate/translate_types.rs`, `aeneas/src/{PrePasses.ml,llbc/RegionsHierarchy.ml,symbolic/SymbolicToPureTypes.ml}` | **source** & **derived**: End-to-end region transformation from `rustc` HIR/MIR and NLL to `Charon` `Region::Body` and `Aeneas` backward functions. |
| `support/rust-llbc-lean-golden-and-aeneas-revision-probes/translation-specimens/RESULTS.md`, `coverage.json`, `canonical-order-check.json`, `aeneas-revision-matrix.json`, `aeneas-revision-comparison.json` | `Baseline.lean` (June 1 & June 3): `3d854188c5820b9d08f9d767a7af2efb520140017243afa9cdcc3eb0b1cd503f`; `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) | **execution**: 8-case Rust-to-LLBC-to-Lean specimen outputs and $2 \times 2$ `Charon`/`Aeneas` pair compatibility matrix. |
| `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean` | `65f8af557997769bd43b4ce6eac36b79e1555bd222b75f31a4b439f08016895a` (784 lines, 0 `sorry`, Lean `v4.34.1`) | **execution** & **derived**: Mechanized `FnSig`/`FuncSpec`, telescopic `ArgSpec`, `funcSpec_verified`, `ShelvedVC`, and `anneal_vcgen`. |
| `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeTrackedFuncLangAndLoops.lean` | `98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66` (2,199 lines, 0 `sorry`, Lean `v4.34.1`) | **execution** & **derived**: Mechanized `TrackedFuncLang`, `evalSymWithTracked_sound`, `tracked_loop_spec_decr_nat`, `diamond_join_cutpoint`, and `trackedFuncLang_implies_constantTime2Safety`. |
| `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/source-manifest.json` | `AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, `cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`, `lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, `iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d` | **source**: File-level SHA-256 and Git blob manifest for all inspected `Aeneas`, `hax`, `RefinedRust`, `RefinedC`, and `Anneal` files. |

## Revalidation

Run the following deterministic checks from the package directory (`reports/rust-verification-lifetimes-prophecies-and-functional-translation/`):

1. **Verify SHA-256 Digests and Kernel-Check Both Standalone Lean 4.34.1 Mechanization Probes:**
   ```bash
   sha256sum \
     support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean \
     support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeTrackedFuncLangAndLoops.lean

   anneal-lean-run --mode file --concurrency 1 -- \
     elan run leanprover/lean4:v4.34.1 lean -j1 -M1024 \
     support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeGeneralSpecAndLithium.lean

   anneal-lean-run --mode file --concurrency 1 -- \
     elan run leanprover/lean4:v4.34.1 lean -j1 -M1024 \
     support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/ProbeTrackedFuncLangAndLoops.lean
   ```
2. **Verify `Baseline.lean` Byte Identity Across Matching `Aeneas` June 1 and June 3 Pairs and Specimen Coverage:**
   ```bash
   python3 - <<'PY'
   import hashlib, json
   p1 = "support/rust-llbc-lean-golden-and-aeneas-revision-probes/aeneas-revision/june1-matching-pair/lean/Baseline.lean"
   p3 = "support/rust-llbc-lean-golden-and-aeneas-revision-probes/aeneas-revision/june3-matching-pair/lean/Baseline.lean"
   h1 = hashlib.sha256(open(p1, "rb").read()).hexdigest()
   h3 = hashlib.sha256(open(p3, "rb").read()).hexdigest()
   assert h1 == h3 == "3d854188c5820b9d08f9d767a7af2efb520140017243afa9cdcc3eb0b1cd503f", (h1, h3)
   with open("support/rust-llbc-lean-golden-and-aeneas-revision-probes/aeneas-revision-matrix.json") as f:
       mat = json.load(f)
   print("Verified Baseline.lean SHA-256 identity and revision matrix:", len(mat))
   PY
   ```
3. **Revalidate Region Lowering and Tactic Infrastructure on Upstream Updates:**
   - When updating `rust-lang/rust`, `AeneasVerif/charon`, or `AeneasVerif/aeneas`, inspect `rustc_borrowck/src/nll.rs` (`replace_regions_in_mir`), `charon/src/bin/charon-driver/translate/translate_types.rs` (`translate_erased_region`), `aeneas/src/PrePasses.ml` (`erase_body_regions`), `aeneas/src/llbc/RegionsHierarchy.ml`, and `aeneas/src/symbolic/SymbolicToPureTypes.ml` to verify whether `Charon` still synthesizes `Region::Body` placeholders from `mir_promoted` and whether `Pure.ty` remains region-free.
   - Check `backends/lean/Aeneas/Std/Primitives.lean`, `Std/WP.lean`, and `Tactic/Step/StepStar.lean` against `support/rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026/source-manifest.json`.
