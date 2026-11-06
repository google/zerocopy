# Aeneas architecture, translation pipeline, pure extraction, and Lean item emission

## Summary

Aeneas is a staged compiler and symbolic execution engine written in OCaml that translates Charon's serialized Low-Level Borrow Calculus (`LLBC`) into a functional target program for Lean, F\*, Coq, or HOL4. Rather than acting as a direct syntax-directed printer from LLBC to Lean, the normal translation path traverses a multi-stage pipeline with two distinct semantic interpretation boundaries:

```text
Charon (--preset=aeneas) -> serialized .llbc crate
  -> Aeneas LLBC PrePasses.apply_passes (crate-wide and per-function normalization)
  -> Interp.compute_contexts (whole-crate use graph, SCC splitting, type/function analysis)
  -> Symbolic execution (Interp.evaluate_function_symbolic with synthesize = true)
  -> Symbolic-to-pure translation (SymbolicToPure / SymbolicToPureTypes)
  -> Ordered pure-IR micro-passes and loop decomposition (PureMicroPasses)
  -> Backend name registration, SCC ordering, and file extraction (Extract / ExtractBase / ExtractTypes)
```

Across the examined Aeneas revisions (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` at release `nightly-2026.06.03` and `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`), seven architectural and representational properties govern integration, verification, and interactive tooling:

1. **Multi-stage pipeline and mode sharing**: Both normal translation mode (`-backend`) and standalone borrow-check mode (`-borrow-check`) load a single `.llbc` file, enforce that Charon produced it with `--preset=aeneas`, and run `PrePasses.apply_passes`. Borrow-check mode invokes `evaluate_function_symbolic` with `synthesize = false` and emits no target program; translation mode runs with `synthesize = true`, converts the synthesized symbolic AST into a typed pure functional intermediate representation (`Pure.texpr`), runs an ordered sequence of effect-sensitive pure micro-passes and loop lowerings, and extracts target files.
2. **Recoverable per-declaration failure vs. whole-crate exit status**: By default (`Config.fail_hard = false`), pre-pass failures replace an individual function body with `ErrorBody`, symbolic/pure translation catches `CFailure` around individual declarations (omitting failed declarations or bodies), and extraction can emit `sorry` (for Lean) on expression-level errors. However, `Errors.push_error` records every recoverable error into the process-global `Errors.error_list`, and `Main.ml` exits with status `1` after extraction whenever that list is non-empty. Consequently, the existence of generated `.lean` files never suffices to establish complete or error-free translation.
3. **Phase ordering, pure micro-passes, and extracted theorem identity**: The pure intermediate representation retains effect wrappers (`Result`, `ControlFlow`), ordinary vs. monadic `Let` bindings, backward continuations, loop nodes (`Pure.Loop`), and explicit error nodes (`EError`). `PureMicroPasses.passes` applies an ordered sequence of rewrites (metadata removal, assignment inlining, beta reduction, Box elimination, trait simplification, loop output/input preparation, `loops_to_recursive`, index recovery, and monadic let normalization), followed by post-list loop decomposition (`decompose_loops`, `loops_to_fixed_points_visitor` producing `Qualif LoopOp` / `loop`, and optional fuel introduction). Default runs keep `Config.sanity_checks = false` and `Config.type_check_pure_code = false`. At `21345f80fa212c596f6437378d7d57984fa2ea77`, the Lean primitive library defines `@[irreducible] def Result α := ITree RustEffect α` and defines `loop` over `ControlFlow` using `partial_fixpoint`.
4. **Functionalization of values, borrows, and traits in Lean**: In the pure forward type (`translate_fwd_ty`), `Box<T>`, `&T`, and `&mut T` all erase to the translated referent type `T` (while raw pointers become a distinct pure builtin type whose dereference remains unsupported in `interp/InterpPaths.ml`). Shared borrows freeze deeper mutable update paths; mutable borrows add region-group-indexed (`back_sg`) and abstraction-level-indexed backward functions that propagate updated values back to original owners (for example, `choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` becomes `Bool → T → T → Result (T × (T → (T × T)))`). Fallible functions wrap the combined forward/backward output in `Result` when `fun_effect_info.can_fail` holds. Rust traits become explicit Lean dictionary `structure` declarations rather than implicit typeclasses.
5. **Lean item naming and namespace synthesis**: Generated Lean names derive from structured Charon item identities rather than raw source text replacement. By default, generated Lean files open a single outer `namespace <crate.name>` (overridable via `-namespace`), while output filenames use a CamelCase basename (`Types.lean`, `Funs.lean` under `-split-files`). Local items strip the leading crate component and join module segments with `.` (`crate::m::f` becomes `m.f` inside `namespace crate`), whereas external items keep their crate prefix (`core.option.Option`). Trait implementations synthesize names of the form `<SelfType>.Insts.<TraitName><ConcreteArgs>` (unless renamed), default trait methods append `.default`, extracted loops append `_loop` / `_loop<index>` and `.body`, and inherent methods that collide with short record-field projectors conditionally insert `.impl.` (or uniformly under `-impl-namespace`).
6. **Synthetic correspondence comments vs. loss of original Rust prose**: Aeneas emits `/-- ... -/` doc comments on generated Lean declarations (`extract_comment_with_span` / `extract_fun_comment`), but these are synthetic metadata blocks assembled from the Rust item path, formatted source span (`Source: '...'`), optional external name pattern, and visibility (`Visibility: public`). User-authored Rust doc comments (`/// ...`) and statement-adjacent body comments (`// ...`) are omitted from ordinary generated Lean output even though upstream Charon (`recover_body_comments.rs`) recovers body comments into LLBC statement `comments_before` lists and retains optional `item_meta.source_text`.
7. **Library vs. process boundary and incremental translation feasibility**: Aeneas's `src/dune` publishes both the `aeneas` CLI executable (`Main`) and an installable OCaml library (`aeneas`) exposing `LlbcOfJson`, `PrePasses`, `Translate.translate_crate_to_pure` (returning in-memory `trans_ctx * translated_crate`), `Extract`, and a lazy persistent `Domainslib.Task` worker pool (`Parallel.ml`). However, configuration (`Config.ml`) and error accumulation (`Errors.error_list`, `Errors.unique_errors` in `Errors.ml`, with no reset helper) live in process-global mutable `ref`s, and every call to `translate_crate_to_pure` rebuilds a fresh whole-crate `trans_ctx` (`compute_contexts`) and retranslates all selected declaration classes. Thus a persistent in-process host can reuse the OCaml process and worker pool only if it fences and resets global state per request, and must treat the normalized whole LLBC crate as the semantic invalidation unit until an explicit dependency-tracking adapter is added.

---

## Applicability

This report synthesizes findings across the five subjects recorded in `REPORT.json`:

- **Aeneas release `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`), the primary Aeneas revision selected by Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` in `anneal/flake.nix`).
- **Paired Charon `0.1.210`** (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, using Rust toolchain `nightly`), pinned by `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`charon-pin` blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`) as the `.llbc` producer and comment/metadata source.
- **Aeneas later pipeline revision** (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`), examined for detailed phase-graph ordering, `PrePasses.apply_passes` evolution, the full `PureMicroPasses.passes` inventory, loop fixed-point lowering, disabled-by-default pure typechecking (`PureTypeCheck`), and the `ITree RustEffect` formulation of Lean `Result` in `backends/lean/Aeneas/Std/Primitives.lean`. At `21345f80fa212c596f6437378d7d57984fa2ea77`, `charon-pin` names Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`.

### Shared vs. Revision-Specific Behavior

- **Shared across `ac9f1bc5262a5e4ff1e24ca78617121382202727` and `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - The overall call graph (`Main.ml` -> `PrePasses.apply_passes` -> `BorrowCheck.borrow_check_crate` or `Translate.translate_crate` -> `translate_crate_to_pure` -> `Interp.compute_contexts` -> declaration/signature translation -> `translate_function_to_symbolics` -> `SymbolicToPure.translate_fun_decl` -> `PureMicroPasses.apply_passes_to_pure_fun_translations` -> `extract_translated_crate`).
  - Enforcement of Charon's `--preset=aeneas` flag on the decoded `.llbc` crate (`Main.ml`).
  - Recoverable per-declaration failure (`CFailure` caught per pre-pass and per declaration, `ErrorBody` substitution, `sorry` emission at extraction) paired with process-global `Errors.error_list` accumulation and exit code `1` on any recorded error.
  - Three distinct body paths in `translate_function_to_symbolics`: structured bodies (`evaluate_function_symbolic` with `synthesize = true`), `TargetDispatchBody` (`SymbolicAst.TargetDispatch` with dummy symbolic inputs), and opaque/missing bodies (`body = None`).
  - Parallel transparent-function translation (sorted by decreasing LLBC function size via `parallel_filter_map`) and parallel pure micro-passes using domain-local fresh-variable generators.
  - Pure forward/backward type decomposition, reference/Box erasure, region-group-indexed backward functions, conditional `Result` wrapping via `effect_info.can_fail`, and explicit trait dictionaries.
- **Specific to `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)**:
  - Paired with Charon `a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`).
  - In `PrePasses.apply_passes`, the crate-wide initial step is `update_array_default`, followed by 10 per-function passes (`fix_closure_lifetimes`, `erase_body_regions`, `remove_unreachable`, `update_loops`, `remove_useless_joins`, `remove_shallow_borrows_storage_live_dead`, `decompose_str_borrows`, `simplify_panics`, `decompose_global_accesses`, `refresh_statement_ids`) and crate-wide post-passes (including `replace_statics`).
  - Exact Dune build boundary (`src/dune`, `src/aeneas.opam`), Lean item-naming fixtures (`Names.lean`, `RenameAttribute.lean`, `Traits.lean`, `NoNestedBorrows.lean`, `NestedBorrows.lean`, `Arrays.lean`), and Charon `0.1.210` comment-recovery inspection (`recover_body_comments.rs`) are pinned to this revision.
- **Specific to `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - Paired in its `charon-pin` with Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`.
  - `PrePasses.apply_passes` adds crate-wide `anon_consts_to_calls` after `update_array_default` and includes `fix_closure_signature_regions` and `fix_anon_const_initializers` in the per-function sequence (`src/PrePasses.ml` L2322–2392).
  - The complete ordered `PureMicroPasses.passes` inventory (`support/aeneas-pipeline-pure-extraction-21345f80/pass-inventory.json`), `PureTypeCheck.check_texpr` partiality analysis, the `ITree RustEffect` definition of `Result` and `partial_fixpoint` definition of `loop` in `backends/lean/Aeneas/Std/Primitives.lean` (L51–91, L447–457), and the source-reconstructed `list_nth_mut` trace (`support/aeneas-pipeline-pure-extraction-21345f80/representative-trace.md`) are recorded at this revision.

### Configuration and Mode Scope

- **CLI modes**: Translation mode (`-backend lean|fstar|coq|hol4`) executes the full pipeline and writes target files; borrow-check mode (`-borrow-check`) reuses `PrePasses.apply_passes`, `compute_contexts`, and `evaluate_function_symbolic` (`synthesize = false`) without pure synthesis or extraction.
- **Default configuration flags**: `Config.parallel = true` (changed by `-sequential`), `Config.fail_hard = false` (changed by `-abort-on-error`), `Config.warnings_as_errors = false` (changed by `-warnings-as-errors`), `Config.drop_as_no_op = true` (changed by `-eval-drops`), `Config.sanity_checks = false`, `Config.type_check_pure_code = false`, and `Config.method_names_in_impl_namespace = false` (changed by `-impl-namespace`).

---

## Findings

### 1. Top-Level Pipeline Architecture, Mode Dispatch, and Error Recovery

#### 1.1 Serialized LLBC Input Boundary and Preset Enforcement

`src/Main.ml` (`ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`; `21345f80fa212c596f6437378d7d57984fa2ea77` L583–617, L755–812) parses command-line options, accepts positional filenames only when the list contains **exactly one file** (`"For now, we only process one file at a time"`), decodes the crate with `LlbcOfJson.crate_of_json_file`, clears Charon's `short_names` field (`"to make printing more deterministic"`), and verifies that the serialized crate's options record Charon's `Aeneas` preset (`charon cargo --preset=aeneas`).

The architectural boundary is strict: Charon owns `rustc` integration and extraction into LLBC; the Aeneas executable starts from a serialized `.llbc` JSON file and never re-runs `rustc` or recovers source information absent from the serialized LLBC crate.

Basis: **source** + upstream **documentation**.

#### 1.2 Phase Graph and Two Distinct Interpretation Boundaries

In `src/Main.ml` and `src/Translate.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L22–51, L315–450, L2198–2209; `ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), the end-to-end call graph is:

```text
Main: decode crate -> check extraction preset -> PrePasses.apply_passes
  -> optional concrete unit-function testing
  -> BorrowCheck.borrow_check_crate OR Translate.translate_crate
Translate.translate_crate
  -> translate_crate_to_pure
     -> Interp.compute_contexts
     -> translate type/global declarations and function/method signatures
     -> translate_function_to_pure
        -> translate_function_to_symbolics
           -> Interp.evaluate_function_symbolic (structured body, synthesize = true)
           OR SymbolicAst.TargetDispatch (target-dispatch body)
        -> SymbolicToPure.translate_fun_decl
     -> translate trait declarations/implementations
     -> PureMicroPasses.apply_passes_to_pure_fun_translations
  -> extract_translated_crate -> register names/models -> extract files
Main: report accumulated errors -> nonzero exit (status 1) if Errors.error_list is nonempty
```

This phase graph crosses two distinct semantic interpretation boundaries:

1. **LLBC to Symbolic AST (`translate_function_to_symbolics`)**: For a function with a structured body, Aeneas invokes `evaluate_function_symbolic` with `synthesize = true`, producing symbolic input values plus a synthesized `SymbolicAst.expr`. For a `TargetDispatchBody`, Aeneas bypasses symbolic execution and constructs symbolic input placeholders and a `SymbolicAst.TargetDispatch` node directly. Other opaque or non-translatable body forms yield no symbolic body (`None`) and become opaque declarations downstream.
2. **Symbolic AST to Pure IR (`SymbolicToPure.translate_fun_decl`)**: `translate_function_to_pure_aux` converts the symbolic result into Aeneas's typed, effect-bearing pure representation (`Pure.fun_decl`), decomposing forward values and backward continuations.

In standalone borrow-check mode (`src/BorrowCheck.ml`, blob `eaa294db179d74efd99f01ed2e69a5e54c6b6a30`), `BorrowCheck.borrow_check_crate` computes the translation context and visits structured function bodies by calling `evaluate_function_symbolic` with `synthesize = false`. It returns no `translated_crate` and writes no target files. Thus "Aeneas accepted the crate under `-borrow-check`" does not imply that pure synthesis, micro-passes, loop decomposition, or backend extraction succeed.

Basis: **source**.

#### 1.3 Separate Declaration Staging and Completeness Boundaries

`Translate.translate_crate_to_pure` (`src/Translate.ml` L315–450) does not process the crate as an undifferentiated AST pass. After computing `trans_ctx = Interp.compute_contexts crate` (which relies on `src/TranslateCore.ml`, blob `55e2abe89a5a519013347635bfb96669e2d73d38`, for name matching and builtin/model lookup), it sequentially stages:

1. type declarations (`translate_type_decl`);
2. global declarations (separately from their initializer function bodies);
3. pure function signatures for all selected functions (`SymbolicToPureTypes.translate_fun_sig_from_decl_to_decomposed`);
4. builtin-function signatures;
5. function bodies (including global initializer bodies), partitioning opaque and transparent functions and sorting transparent functions by decreasing LLBC size for parallel execution via `parallel_filter_map`;
6. trait declarations; and
7. trait implementations.

Computing crate-wide function signatures before translating bodies allows body translation to resolve calls against known translated signatures. Because each declaration class is staged and wrapped in independent error recovery, a function's signature can succeed while its body fails, or a global, trait declaration, or trait implementation can fail independently.

Basis: **source** + **derived** completeness implication.

#### 1.4 Recoverable Per-Declaration Failures vs. Whole-Run Error Accounting

Three mechanisms in `src/Errors.ml` (blob `c135674b8601786616c6c20ad81ec388bb8cbfea`), `src/PrePasses.ml`, `src/Translate.ml` (L280–304), `src/extract/Extract.ml` (L703–741), and `src/extract/ExtractErrors.ml` (L13–50) govern error recovery:

1. **Recoverable exceptions**: Because `Config.fail_hard` defaults to `false` (unless `-abort-on-error` is passed), recoverable errors call `Errors.push_error`—appending to the global `Errors.error_list`—and raise `CFailure`.
2. **Stage-local catch boundaries**:
   - In `PrePasses.apply_passes`, if a per-function pre-pass raises `CFailure`, Aeneas logs that the function body is ignored, substitutes `ErrorBody`, and continues preprocessing the crate.
   - In `Translate.translate_function_to_pure` and the loops over globals, traits, and trait impls, catching `CFailure` drops the failed declaration (`None`) or leaves `body = None` in `SymbolicToPure.translate_fun_decl`.
   - In `Extract.extract_texpr_errors`, residual expression errors (`Pure.EError`) print `sorry` for Lean (and admission/error forms for other backends) while recording an extraction error and continuing file generation.
3. **Final CLI exit status**: After translation and file extraction finish, `Main.ml` checks `Errors.error_list` and exits with status `1` if any error was recorded during the run.

Consequently, Aeneas intentionally emits partial target files on failed runs to aid debugging. Any downstream consumer or verification harness must check both the Aeneas process exit status (`0` vs. nonzero) and explicit declaration coverage accounting rather than treating emitted `.lean` files as proof of complete translation.

Basis: **source** + **derived** integration requirement.

---

### 2. LLBC Normalization (`PrePasses`) and Pure IR Micro-Passes (`PureMicroPasses`)

#### 2.1 Fixed LLBC Preprocessing Sequence (`PrePasses.apply_passes`)

Before either borrow-checking or pure translation, `Main.ml` invokes `PrePasses.apply_passes` (`src/PrePasses.ml`, `ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`; `21345f80fa212c596f6437378d7d57984fa2ea77` L2322–2392):

1. **Initial crate-wide passes**:
   - `update_array_default` (normalizes `rustc`'s array `Default` implementations across the crate);
   - `anon_consts_to_calls` (present in `21345f80fa212c596f6437378d7d57984fa2ea77`).
2. **Per-function pass sequence** (folded in order with per-function `CFailure` -> `ErrorBody` recovery):
   - repair closure lifetimes (`fix_closure_lifetimes`) and, in `21345f80fa212c596f6437378d7d57984fa2ea77`, `fix_closure_signature_regions` and `fix_anon_const_initializers`;
   - erase body regions not needed at function-call boundaries (`erase_body_regions`);
   - replace `core::intrinsics::unreachable` calls with `Abort UndefinedBehavior` (`remove_unreachable`);
   - normalize loops (`update_loops`);
   - remove useless joins (`remove_useless_joins`);
   - remove shallow borrows and `StorageLive`/`StorageDead` statements (`remove_shallow_borrows_storage_live_dead`);
   - decompose string borrows (`decompose_str_borrows` in `ac9f1bc5262a5e4ff1e24ca78617121382202727`);
   - simplify panic forms (`simplify_panics`);
   - decompose global accesses (`decompose_global_accesses`); and
   - refresh statement IDs (`refresh_statement_ids`).
3. **Final crate-wide passes**:
   - `strip_unnecessary_target_suffixes`;
   - `filter_marker_traits`;
   - `filter_type_aliases`;
   - `replace_statics` (in `ac9f1bc5262a5e4ff1e24ca78617121382202727`);
   - `remove_vtables`;
   - `rename_type_vars`; and
   - `simplify_trait_calls`.

These pre-passes perform semantic and representational rewrites (such as region erasure and converting `unreachable` to `Abort UndefinedBehavior`), not merely formatting. Moreover, there is no single total admission predicate up front: while `Main.ml` checks the `Aeneas` preset and `Translate.translate_function_to_pure_aux` (`src/Translate.ml` L121–132) rejects bound/free implied lifetime constraints before body translation, other unsupported constructs fail only during symbolic execution, pure synthesis, micro-passes, or extraction.

Basis: **source** + **derived** classification of pass obligations.

#### 2.2 Pure Intermediate Representation (`Pure.texpr`) and Symbolic-to-Pure Lowering

In `src/pure/Pure.ml` (`ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `acde8579d6861a08efae086c72f3156283110342`; `21345f80fa212c596f6437378d7d57984fa2ea77` L1349–1447), a pure expression `Pure.texpr` is a record `{ e : expr; ty : ty }`. The expression grammar includes free and bound variables, constants, function/operator application (`App`), lambdas (`Lambda`), qualified definitions and operators (`Qualif`), `Let (monadic : bool, lv, re, next_e)` where `monadic` distinguishes monadic bind from pure let-binding, `Switch`, `Loop`, structure updates, `Meta`, and `EError`. Loop records store ordered input values, backward continuations, input/output types, body binders, and the `to_rec` boolean flag.

In `src/symbolic/SymbolicToPure.ml` (`ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `95ba91f539e48009efa420dfa956c4c55581cb3a`; `21345f80fa212c596f6437378d7d57984fa2ea77` L11–125), `translate_fun_decl_body` and `translate_fun_decl` construct a return continuation that wraps outputs in the `Result` effect constructor when `effect_info.can_fail` is true, supply a panic constructor of matching output type, translate the symbolic AST body, and close the input binders. At this stage, `Pure.Loop` nodes remain embedded inside the expression tree.

Basis: **source** + **derived** semantic obligation (any formal denotation of `Pure.texpr` must account for ordinary vs. monadic `Let`, failure/panic, divergence, backward continuations, and `Loop` before rewrite soundness can be proved).

#### 2.3 Ordered Pure Micro-Pass Pipeline and Backend-Sensitive Configuration

After initial pure translation, `PureMicroPasses.apply_passes_to_pure_fun_translations` (`src/pure/PureMicroPasses.ml`, `ac9f1bc5262a5e4ff1e24ca78617121382202727` blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`; `21345f80fa212c596f6437378d7d57984fa2ea77` L13–235, L240–270, L369–374) folds the ordered `PureMicroPasses.passes` list over each translated function in parallel using task-local fresh-variable generators. The full pass sequence and its configuration gates are preserved in `support/aeneas-pipeline-pure-extraction-21345f80/pass-inventory.json`.

| Stage | Named transformations (`PureMicroPasses.passes`) | Preservation concern and ordering dependency |
| --- | --- | --- |
| Metadata and basic normalization | Pretty names; remove metadata; inline anonymous constants; optional target-feature assertions; unit variables; optional assertions (`intro_massert`); structure decomposition/update introduction; lambda/let simplification | Pretty-name recovery must run before metadata removal; later passes assume `Meta` nodes are gone. Feature assertions add explicit failure conditions to the model. |
| Expression cleanup | Assignment inlining; beta reduction; `Box` elimination; trait-call simplification; duplicate-call simplification; optional application/tuple merge (`merge_let_app_decompose_tuple`); useless-expression filtering; branching lets; let-then-return simplification | Inlining, dead-code removal, and duplicate-call elimination must respect monadic failure, sequencing, and divergence. |
| Loop relation preparation | Output tuple decomposition; output-continuation simplification; beta/inlining rounds; input/output filtering without constant-input filtering; reorder outputs; `loops_to_recursive`; reorder inputs | Loop-output tuple decomposition must precede relation analysis (later passes crash without it); output-continuation simplification precedes filtering to preserve loop-input ordering; constant inputs are kept until after auxiliary loop definitions are extracted. |
| Backend-oriented cleanup | Let-to-match; flatten/update/aggregate simplification; additional lambda/let/inlining/filtering rounds; panic-then-wrapping arithmetic simplification | Refutable pattern matching, checked arithmetic failure, and evaluation order must remain aligned. |
| Index recovery and final generic lowering | Recover builtin indexing; filter/eta/inlining cleanup; array/slice-update simplification; let-then-return; optional monadic-let decomposition (`decompose_monadic_let_bindings`), nested-pattern decomposition (`decompose_nested_let_patterns`), monadic unfolding, pure-call lifting (`lift_pure_function_calls`); machine-word matches | Recovered array/slice indexing and update primitives must match the target standard-library models, bounds checks, backward behavior, and scalar widths. |

Crucially, the pure IR pipeline is **not** completely backend-independent: `Main.ml` mutates `Config` flags after backend selection (`src/Config.ml` blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`). Selecting Lean enables `merge_let_app_decompose_tuple` and `lift_pure_function_calls`; selecting Coq enables `decompose_monadic_let_bindings` and `decompose_nested_let_patterns`; selecting F\* disables `intro_massert`.

Basis: **source** + upstream **documentation**.

#### 2.4 Post-List Loop Decomposition, Fixed-Point Operators, and Fuel

Following the main `passes` list, `apply_passes_to_pure_fun_translations` (`src/pure/PureMicroPasses.ml` L376–503) and `src/pure/PureMicroPassesLoops.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L2436–2585, L3269–3315) run a dedicated post-list loop pipeline:

1. **Recursive loop recognition (`loops_to_recursive`)**: During the main pass list, `loop_satisfies_recursive_criteria_aux` checks whether a loop has identity input continuations, compatible calls to input continuations in outputs and reentry, and a detected structural-decrease relation. Unless disabled by `-no-recursive-loops`, qualifying loops set `to_rec = true` for direct recursive extraction.
2. **Loop decomposition (`decompose_loops`)**: Extracts auxiliary loop definitions (`loops`), filters constant loop inputs on the parent function and auxiliary loops, and extracts loop-body continuations into auxiliary `.body` functions (`bodies`), producing a bundle `{ f; loops; bodies }` where a single Rust function yields multiple top-level pure declarations.
3. **Fixed-point operator introduction (`loops_to_fixed_points_visitor`)**: Replaces residual non-recursive `Pure.Loop` nodes by packaging loop inputs and outputs into types, rewriting `continue`/`break` branches into `ControlFlow`, constructing a body lambda, and applying `Qualif LoopOp` to that body and initial inputs. `Extract.extract_App` (`src/extract/Extract.ml` L803–817) prints `LoopOp` as `loop`. If any `Pure.Loop` node survives into extraction without being lowered, extraction raises an internal error.
4. **Post-loop cleanup, fuel, and annotations**: Simplifies let-then-return, reintroduces assertions, optionally adds fuel parameters last (because earlier passes manipulate unfuelled parameter lists), adds final type annotations, and computes reducibility metadata.

Basis: **source**.

#### 2.5 Disabled-by-Default Sanity Checks and Partial Pure Typechecking

In `src/Config.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L409–417), both `Config.sanity_checks` and `Config.type_check_pure_code` default to `false` (the latter carries an upstream `TODO` to fix bugs and reactivate checks).

- `Translate.check_fun_decl_vars_are_well_bound` (`src/Translate.ml` L53–98), which verifies free-variable closure and opens binders to catch invalid bound occurrences, runs only when `Config.sanity_checks` is enabled.
- `SymbolicToPureTypes.type_check_texpr` (`src/symbolic/SymbolicToPureTypes.ml` L1273–1303) checks `!Config.type_check_pure_code` before invoking `PureTypeCheck.check_texpr`. Even when enabled, `PureTypeCheck.check_texpr` (`src/pure/PureTypeCheck.ml` L165–268) is partial: qualified function/global/trait-constant/loop-operator/scalar-projection cases and loop-input checking contain `TODO` branches.
- CLI option guards in `Main.ml` (L460–485, L604–617) reject incompatible fuel/decreases flags and reject Lean `-decreases-clauses` combined with mutually recursive function groups.

Basis: **source**.

#### 2.6 Target Extraction, `ITree RustEffect` Lean Semantics, and Representative Trace

During `extract_translated_crate` (`src/Translate.ml` L1362–1413, L1461–1510), `ExtractBuiltin.ml` (`21345f80fa212c596f6437378d7d57984fa2ea77` L883–953), `ExtractBase.ml` (L755–790, L1133–1201, L1418–1457), and `Extract.ml` (L2082–2135):

- Builtin maps associate Rust item patterns with target extraction names, types, and `can_fail` effect metadata (rejecting duplicate patterns and memoizing the map for effect analysis).
- For Lean, emitted files `import Aeneas`, `open Aeneas Aeneas.Std Result ControlFlow Error`, configure `set_option maxHeartbeats` / `maxRecDepth`, and optionally open a `noncomputable section`.
- Builtin `TResult` prints as `Result` (`ok` / `fail`), `TLoopResult` prints as `ControlFlow`, recursive definitions print `def ...` followed by `partial_fixpoint`, and opaque/builtin declarations can print `axiom`.
- At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, `backends/lean/Aeneas/Std/Primitives.lean` (L51–91, L447–457) defines `@[irreducible] def Result α := ITree RustEffect α` (where `RustEffect` models failure with an empty output type, `ok` is pure return, `fail` emits the failure effect, and `div` is interaction-tree divergence) and defines `loop` over `ControlFlow` via `partial_fixpoint`.
- A concrete source-reconstructed trace of `list_nth_mut` connecting preprocessing, symbolic ownership, loop decomposition, pure micro-passes, and retained Lean output is preserved in `support/aeneas-pipeline-pure-extraction-21345f80/representative-trace.md` and `support/aeneas-pipeline-pure-extraction-21345f80/specimen-trace.json`, with supporting blob/pass inventories in `support/aeneas-pipeline-pure-extraction-21345f80/source-reading.json` and `support/aeneas-pipeline-pure-extraction-21345f80/supplement-source-reading.json`.

Basis: **source** + **derived** theorem-identity requirement (establishing that a kernel-checked Lean theorem characterizes a Rust artifact requires retaining the source, `.llbc`, Aeneas/Charon revisions, flags, `Std.Primitives` model revision, and inspecting the elaborated constant's dependencies for `sorry` or `axiom` declarations).

---

### 3. Rust-to-Lean Value, Function, Reference, and Trait Translation

#### 3.1 Logical Type Translation, Box/Reference Erasure, and Raw Pointers

In `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), and `src/extract/ExtractTypes.ml` (blob `371717638f4298cc9c488b31a597608f9bf5089c`) at `ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- **References and `Box<T>`**: `translate_fwd_ty` maps `Box<T>` directly to the translated `T` and maps `TRef` (`&T` and `&mut T`) recursively to its referent type `T`. `Pure.ty` has no ordinary reference constructor. In `tests/lean/NoNestedBorrows.lean` (blob `e2a706b744e2e9a105e305cf8a2b353354209dae`), the recursive `Box<List<T>>` field in Rust `List<T>` becomes a direct `List T` inductive constructor argument.
- **Scalars, tuples, arrays, slices, and ADTs**: Rust integer primitives map to bounded scalar types printed as `Std.U32`, `Std.U64`, `Std.Usize`, `Std.Isize`, etc.; tuples map to Lean products (`×`); arrays retain element type and length; slices retain element type; structs and enums (`translate_type_decl_kind`) become logical Lean `structure` or `inductive` declarations (with empty structs simplified to `Unit`), abstracting away ABI layout, padding, discriminant encoding, pointer identity, and drop glue.
- **Raw pointers (`*const T`, `*mut T`)**: Unlike ordinary references, raw pointers are preserved in `Pure.ty` as a distinct raw-pointer builtin carrying mutability and translated pointee type. However, type representability does not imply operational support: the checked-in known-failure fixture `tests/src/raw_pointers.rs` (blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`) paired with `tests/src/raw_pointers.lean.out` (blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`) records that dereferencing raw pointers fails in `interp/InterpPaths.ml`.

Basis: **source** + preserved generated and known-failure **execution** artifacts.

#### 3.2 Shared vs. Mutable References and Region-Group Backward Functions

In `src/symbolic/SymbolicToPureTypes.ml` and `src/symbolic/SymbolicToPureExpressions.ml` (blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`):

- **Shared references (`&T`)**: Forward translation maps `&T` to `T`, and the backward-type traversal stops whenever it encounters a shared reference because shared borrows freeze all paths beneath them. For example, `is_cons(&List<T>)` in `NoNestedBorrows.lean` takes `List T` and produces no backward function.
- **Mutable references (`&mut T`) and `back_sg`**: Forward translation maps `&mut T` to `T`, while `translate_fun_sig_from_decl_to_decomposed` computes a decomposed signature whose `back_sg` map is keyed by **region-group IDs** (`RegionGroupId`), not syntax nodes. Mutable borrows in forward inputs contribute outputs that a region group's backward function returns to original owners; mutable borrows in the Rust return type contribute inputs that the caller later supplies to the backward function. Empty backward functions are filtered out, and `compute_output_ty_from_decomposed` combines the forward output value with surviving backward functions before wrapping the result in `Result` (when `fun_effect_info.can_fail` holds).
- **Preserved witness (`choose`)**: In `tests/src/no_nested_borrows.rs` (blob `707f7d6e1201d1220380dd565a4178806cf3a9ec`) and `tests/lean/NoNestedBorrows.lean` (blob `e2a706b744e2e9a105e305cf8a2b353354209dae`), Rust:
  ```rust
  fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T
  ```
  is extracted to Lean as:
  ```lean
  def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))
  ```
  where the first tuple component is the chosen value (`x` or `y`) and the second component `T → (T × T)` is the merged backward closure that maps the caller's updated `T` back to reconstructed `(x', y')`.
- **Nested mutable borrows and ADT boundary**: `compute_back_ty_num_levels` and `translate_back_ty_aux` support multi-level borrow abstractions in function signatures (witnessed by `inner_mut` and `IterMut.next` in `tests/src/nested-borrows.rs` blob `61d62cf0e0723a4019e024882e35fb8b212a67eb` and `tests/lean/NestedBorrows.lean` blob `61b3b2b31e50555182867a5b73fa510d05106e22`), but the type analysis explicitly rejects user-defined ADTs containing nested mutable borrows.

Basis: **source** + preserved generated **execution** artifacts.

#### 3.3 Explicit Trait Dictionaries in Generated Lean

In `tests/src/traits.rs` (blob `a20f6ee91960cbacf99e8899a32e789f7b855671`) and `tests/lean/Traits.lean` (blob `d234936b72231024fbccf0030a08023836e5eb6e`), Rust trait declarations are extracted as explicit Lean `structure` types whose fields hold method implementations and associated items (with associated types represented as extra type parameters or structure fields depending on Charon normalization). Generic functions take explicit dictionary parameters such as `(BoolTraitInst : BoolTrait T)`, and trait implementations become `@[reducible]` structure values rather than Lean `class` / `instance` declarations.

Basis: **source** + preserved generated **execution** artifact.

---

### 4. Rust Item Names, Namespaces, and Collision Policy in Generated Lean

#### 4.1 Outer Crate Namespace vs. CamelCase Module Filenames

At `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`src/Translate.ml` blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`, `src/Config.ml` blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`, `src/Main.ml` blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`), Aeneas separates the semantic Lean namespace from output file naming:

- **Outer Lean `namespace`**: By default, `Translate.ml` sets the Lean namespace to the raw Rust `crate.name` unless overridden by `-namespace <name>`. `extract_file` wraps ordinary generated files in `namespace <namespace> ... end <namespace>` (while external-model or template files can configure `in_namespace` / `open_namespace` differently).
- **Output file/module names**: `Translate.ml` derives a CamelCase `crate_name` from the `.llbc` filename (and combines it with `-subdir` and `-split-files` suffixes such as `Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, `FunsExternal.lean`). In `tests/src/names.rs` (blob `7d6ed18643b37393a76881e5719c420a7451b265`) and `tests/lean/Names.lean` (blob `ff03c177c059ef63cb890038957b1b1626e89c6a`), crate `names` is written to `Names.lean` but opens `namespace names`.

Basis: **source** + checked-in generated fixture.

#### 4.2 Local vs. External Item Paths, Types, Fields, Variants, and Helpers

In `src/extract/ExtractName.ml` (blob `294499309f9492bf74f9a5fc95261556fcdb76a6`), `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`), and `src/extract/ExtractBuiltinCore.ml` (blob `60961bddc9aa65a40b58caf5d1c3c777f7990ab9`):

| Rust / Charon Item Class | Aeneas Lean Naming Rule (`ExtractBase.ml` / `ExtractBuiltinCore.ml`) | Concrete Fixture Witness |
| --- | --- | --- |
| Local item (`crate::m::item`) | `ctx_prepare_name` strips the leading `PeIdent` matching `ctx.crate.name`; `name_to_simple_name` simplifies components; `flatten_name` joins with `.` inside `namespace <crate>` | `mod ExpandSimpliy` items become `ExpandSimpliy.Wrapper` and `ExpandSimpliy.check_expand_simplify_symb1` inside `namespace no_nested_borrows` (`NoNestedBorrows.lean`) |
| External item (`ext_crate::m::item`) | Leading crate component is retained | `core.option.Option.Insts.TraitsBoolTrait` (`Traits.lean`) |
| Types and structure constructors | `ctx_compute_type_name_no_suffix` uses the dot-joined path with no `_t` suffix; constructor is `<type-name>.mk` | `Pair`, `Pair.mk`, `List` (`NoNestedBorrows.lean`) |
| Record fields and enum variants | Lean sets `record_fields_short_names := true` (short field names; `_<index>` for unnamed fields on non-tuples) and unprefixed enum variant names | `Wrapper.x`, `Foo.x`, `Foo.y` (`Traits.lean`); `VariantsTest.Variant1` (`RenameAttribute.lean`) |
| Loop helpers and bodies | `ctx_compute_fun_name` appends `_loop` (single loop) or `_loop<index>` (multiple loops), plus `.body` for extracted Lean loop-body declarations | `No_borrows_sum`, `No_borrows_sum_loop`, `No_borrows_sum_loop.body` (`RenameAttribute.lean`) |
| Provided/default trait methods | Appends `.default` to the trait method path | `BoolTrait.ret_true.default` (`Traits.lean`); `BoolTrait.retTest.default` (`RenameAttribute.lean`) |
| Non-blanket trait implementations | `ctx_compute_trait_impl_name_raw` synthesizes `<SelfType>.Insts.<SeparatorFreeTraitName><ConcreteGenericArgs>` (type variables omitted; blanket impls add `Blanket`) | `Bool.Insts.TraitsBoolTrait`, `U64.Insts.TraitsToTypeBool`, `Wrapper.Insts.TraitsToU64` (`Traits.lean`); renamed impl becomes `BoolImpl` with `BoolImpl.getTest` (`RenameAttribute.lean`) |
| Inherent method colliding with field projector | Checks generated method names against recorded ADT projector names; inserts `.impl.` on collision by default, or for all methods when `-impl-namespace` sets `method_names_in_impl_namespace = true` | `Struct.impl.len` when method `len` collides with field `len` (`ExtractBase.ml`) |

#### 4.3 Rename Attributes, Collision Maps, and Identifier Quoting

- **Rename propagation**: `#[aeneas::rename("...")]` / `#[charon::rename("...")]` (`tests/src/rename_attribute.rs` blob `0c9dd7f32725c1051437f5873856dea53db61308` and `tests/lean/RenameAttribute.lean` blob `76b08a33172229d237825cc6171832d319f76d5f`) replaces the target item's own spelling. For trait-implementation methods without an explicit method-level rename on the `impl`, Aeneas looks up the trait declaration's method rename (`BoolImpl.getTest`). However, renames act locally on the item rather than rewriting all enclosing path prefixes (a trait renamed `BoolTest` with default method renamed `retTest` still emits `BoolTrait.retTest.default`).
- **Asymmetric collision handling and escaping**: Top-level declaration collisions are tracked via strict/unsafe global name maps in `ExtractBase.ml` and reported as errors recommending a rename attribute, whereas local variables, generic parameters, and trait-clause variables append numeric suffixes via `basename_to_unique`. In `ctx_add` (`ExtractBase.ml`) and `escape_name` (`21345f80fa212c596f6437378d7d57984fa2ea77` L755–790), dot-separated components containing `-` are wrapped in Lean French quotes `«...»`, and `Names.lean` demonstrates `«name»` for a reserved field identifier.

Basis: **source** + checked-in generated fixtures.

---

### 5. Synthetic Declaration Comments vs. Omission of Original Rust Prose

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, Aeneas's Lean comment printer (`extract_comment_with_span` in `src/extract/ExtractTypes.ml` blob `371717638f4298cc9c488b31a597608f9bf5089c` L1197–1257, L1497–1509; `extract_fun_comment` in `src/extract/Extract.ml` blob `52754e4fdb25b50fce63abe2d2184751d69632e8` L2047–2065; span formatting in `src/Errors.ml` blob `c135674b8601786616c6c20ad81ec388bb8cbfea` L13–36) emits `/-- ... -/` doc comments before generated declarations. However, those comments are **synthetic correspondence headers** assembled solely from:

1. the bracketed Rust item path (plus generated loop/body tags in `extract_fun_comment`);
2. `Source: '<file>', lines <start>-<end>` formatted from `item_meta.span`;
3. an optional external name pattern; and
4. optional `Visibility: public`.

Original user-authored Rust comments are dropped in both declaration and body positions, as demonstrated by the exact-revision golden pair `tests/src/arrays.rs` (blob `478af7171452826436f56f12c88493debac8e0d0`, L132–136 and L255–268) and `tests/lean/Arrays.lean` (blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`, L221–231 and L417–427):

- **Declaration doc comments (`/// ...`)**: In `tests/src/arrays.rs` L132–136, `pub fn array_update2` is preceded by `/// This test is to exercise the pure micro passes`. In `tests/lean/Arrays.lean` L221–231, `def array_update2` carries only `/-- [arrays::array_update2]: Source: 'tests/src/arrays.rs', lines 133:0-136:1 Visibility: public -/`; the Rust doc sentence is absent.
- **Statement-adjacent body comments (`// ...`)**: In `tests/src/arrays.rs` L255–268, `non_copyable_array` contains body comments `// x is moved (not deep copied!)`, `// TODO: ...`, and `// this fails, naturally:`. In `tests/lean/Arrays.lean` L417–427, `def non_copyable_array : Result Unit` contains only the translated call `take_array_t (Array.make 2#usize [ AB.A, AB.B ])`.
- **Upstream Charon preserves comments that Aeneas omits**: At the paired Charon revision `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/transform/add_missing_info/recover_body_comments.rs` (blob `d1defb3d5b552c4f1309f9b7990b0ce1cca492c0`, L1–19, L39–79) explicitly recovers original body comments and attaches them to LLBC statements in `comments_before : string list` (`charon-ml/src/generated/Generated_LlbcAst.ml` blob `2a9a9aa71ae863fb3178eaee9f790de16a9f28ea` L9–19), and `item_meta` retains optional `source_text` (`charon-ml/src/generated/Generated_Types.ml` blob `69aad6059931c8b365f7d1abb800e5716aec8ad5` L963–987). Aeneas's Lean printer simply does not serialize `comments_before` or `source_text`.

Basis: **source** + checked-in generated **execution** artifacts.

---

### 6. OCaml Library Boundary, Process State, and Incremental Translation Feasibility

#### 6.1 Public OCaml Library (`aeneas`) vs. Thin CLI Executable (`Main`)

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`support/aeneas-library-process-architecture/source-map.json`), `src/dune` (blob `4152c9de6d84484bf501da543553f3e6af324f9a`), `src/dune-project` (blob `4656b7396dc213ebfef5c351986e9d89645078cd`), and `src/aeneas.opam` (blob `70ea2f7050a98a598b85f982d1e65259c6a66b0a`) define two distinct public targets built by Dune `@install`:

1. A public `(library (name aeneas) (public_name aeneas) ...)` containing `Config`, `Errors`, `LlbcOfJson`, `Parallel`, `PrePasses`, `Translate`, the symbolic interpreter (`Interp`, `InterpReduceCollapse`), `SymbolicToPure*`, `Pure*`, and `Extract*`.
2. A thin `(executable (name main) (public_name aeneas) (libraries aeneas) (modules Main))` that parses CLI flags, mutates `Config`, loads one `.llbc` file, runs `Aeneas.PrePasses.apply_passes`, dispatches to `BorrowCheck.borrow_check_crate` or `Translate.translate_crate`, checks `Errors.error_list`, and exits.

Furthermore, `Translate.translate_crate_to_pure` returns `trans_ctx * translated_crate` in memory before `extract_translated_crate` writes files (`Translate.translate_crate` is just their composition). An OCaml host can link the `aeneas` library directly and retain the in-memory `trans_ctx` and `translated_crate`, and `src/Parallel.ml` (blob `08f055cf2e87e0164bb3d02dc9f8dde2fc84034c`) maintains a lazy persistent `Domainslib.Task` worker pool created once and reused across parallel operations until `at_exit`.

#### 6.2 Process-Global Mutable State and Absence of a Server Protocol

Despite the clean library split, Aeneas is not a ready-made multi-request server:

- **Mutable global configuration (`src/Config.ml`)**: `opt_backend : backend option ref = ref None` and dozens of backend/translation flags live in module-level mutable `ref`s mutated by `Main.ml` according to the selected backend.
- **Unreset global error accumulators (`src/Errors.ml`)**: `let error_list = ref []` and `let unique_errors = ref FileLineMap.empty` are appended to by `push_error`, and the pinned `Errors.ml` defines **no reset helper**. Because there is no `.mli` hiding these `ref`s, an in-process host can clear them manually, but doing so is an adapter responsibility; overlapping concurrent requests in one process would race on `Config` and `Errors`.
- **No daemon/session/cancellation API**: The pinned source tree contains no RPC/LSP server, request ID, workspace session, cancellation token, or edit-patching API.

#### 6.3 Whole-Crate Invalidation Boundaries vs. Per-Function Decomposition

As detailed in `support/aeneas-incremental-translation-feasibility/incremental-feasibility-matrix.json` and `support/aeneas-incremental-translation-feasibility/source-map.json`, reusing an in-memory process is distinct from semantic incremental translation across edited LLBC snapshots:

| Pipeline Stage | Decomposition Unit in `ac9f1bc5262a5e4ff1e24ca78617121382202727` | Whole-Crate Coupling / Invalidation Barrier |
| --- | --- | --- |
| `PrePasses.apply_passes` (`src/PrePasses.ml`) | 10 per-function passes run per body | Bookended by crate-wide `update_array_default` (which selects a representative across declaration membership) and crate-wide post-passes (`filter_marker_traits`, `filter_type_aliases`, `replace_statics`, `remove_vtables`, `simplify_trait_calls`). Cache keys below pre-passes must key on the **normalized** LLBC crate. |
| `Interp.compute_contexts` (`src/interp/Interp.ml` blob `7b06ee4d1bdd302d9cbd85fc2e822c1f5324c1e5`) | Whole crate (`let trans_ctx = compute_contexts crate`) | Recomputes `Deps.compute_graph_of_uses crate`, declaration-group splitting, mixed recursive group detection, `analyze_type_declarations`, and `FunsAnalysis.analyze_module` from scratch on every call. |
| `translate_crate_to_pure` (`src/Translate.ml`) | Transparent and opaque functions translated per `fun_decl` in parallel via `parallel_filter_map` with local symbolic/variable generators | Computes all selected type definitions, globals, and the full function-signature map first; each `translate_function_to_pure` call reads the shared `trans_ctx`, translated types/globals, and peer function signatures. |
| `PureMicroPasses` (`src/pure/PureMicroPasses.ml`) | Per-function pass pipeline and loop decomposition run in parallel with domain-local variable generators | Each task context receives maps of all translated functions, types, and trait impls; final type annotation and reducibility passes run across collected translations. |
| `extract_translated_crate` (`src/Translate.ml`, `ExtractBase.ml`) | Per-declaration printing | Registers globally unique names across declaration classes (where registration order and inherent-method vs. field-projector collisions matter) and computes SCC recursion groups before emission. |

Note also that the comment `"incremental update of the context information"` inside `src/interp/InterpReduceCollapse.ml` (blob `379bcd2d4904abf5e76a2f28877b2e28877b2e293cf5f4e3`) refers only to maintaining borrow/loan lookup maps while merging abstractions within a single symbolic execution, not cross-request crate caching. Consequently, the safe interactive baseline at this revision is **process and worker-pool reuse with whole-crate semantic recomputation** keyed on the normalized LLBC snapshot and `Config` vector.

Basis: **source** + **derived** architectural and invalidation boundaries.

---

## Boundaries

- **Not examined**: Fresh execution of Charon, Aeneas, OCaml/Dune, or Lean was not performed for the architecture, naming, comment-preservation, or incremental-feasibility slices; those findings derive from pinned source and checked-in upstream fixtures (`NoNestedBorrows.lean`, `NestedBorrows.lean`, `Traits.lean`, `Names.lean`, `RenameAttribute.lean`, `Arrays.lean`, `raw_pointers.lean.out`). Exhaustive verification of every micro-pass body in `PureMicroPasses.ml`, every builtin mapping in `ExtractBuiltinCore.ml`, and non-Lean backends (F\*, Coq, HOL4) beyond shared pipeline switches was not performed.
- **Unknown**: Byte-for-byte output determinism between parallel (`Config.parallel = true`) and sequential (`-sequential`) runs across host OSes; complete formal denotational semantics and rewrite soundness proofs for the current `Pure.texpr` IR across all effectful micro-passes; and the exact minimal dependency closure required for sound function-level incremental invalidation without whole-crate `compute_contexts` recomputation.
- **Known not to apply**:
  - The presence of generated `.lean` files or a well-typed `Pure.texpr` record does **not** imply error-free translation or checked pure typing (`Errors.error_list` determines CLI exit status, and `Config.type_check_pure_code` defaults to `false`).
  - Acceptance under `-borrow-check` does **not** imply that pure translation, loop decomposition, or Lean extraction will succeed.
  - Ordinary Rust doc comments (`///`) and body comments (`//`) do **not** survive into ordinary generated Lean files, despite Charon's `recover_body_comments.rs` populating `comments_before` in LLBC.
  - The internal incremental borrow/loan map maintenance in `InterpReduceCollapse.ml` and the persistent `Domainslib` pool in `Parallel.ml` do **not** provide cross-snapshot semantic incremental translation.
- **Unsupported**:
  - Multi-file CLI invocation (`Main.ml` enforces a single `.llbc` input file per run) and `.llbc` inputs not produced with Charon `--preset=aeneas`.
  - Dereferencing raw pointers in symbolic execution (`interp/InterpPaths.ml`, recorded in `tests/src/raw_pointers.lean.out`), even though raw-pointer types are representable in `Pure.ty`.
  - User-defined ADTs containing nested mutable borrows in backward-type analysis (`SymbolicToPureTypes.ml`), and higher-ranked bound/free implied lifetime constraints rejected in `Translate.translate_function_to_pure_aux`.
  - Combining Lean `-decreases-clauses` with mutually recursive function groups (`Main.ml` L604–617), and any residual `Pure.Loop` node reaching `Extract.ml` unlowered.

---

## Evidence

### 1. Primary Upstream Source — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)

- **Build and package surface**:
  - `src/dune` (blob `4152c9de6d84484bf501da543553f3e6af324f9a`), `src/dune-project` (blob `4656b7396dc213ebfef5c351986e9d89645078cd`), `src/aeneas.opam` (blob `70ea2f7050a98a598b85f982d1e65259c6a66b0a`), `charon-pin` (blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`).
- **Pipeline, CLI, configuration, and parallel/error state**:
  - `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`), `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`), `src/Errors.ml` (blob `c135674b8601786616c6c20ad81ec388bb8cbfea`, L13–36), `src/Parallel.ml` (blob `08f055cf2e87e0164bb3d02dc9f8dde2fc84034c`), `src/LlbcOfJson.ml` (`src/llbc/LlbcOfJson.ml`, blob `4007be2f7e77c20babd765802e6742307d6128a3`), `src/PrePasses.ml` (blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`), `src/BorrowCheck.ml` (blob `eaa294db179d74efd99f01ed2e69a5e54c6b6a30`), `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), `src/TranslateCore.ml` (blob `55e2abe89a5a519013347635bfb96669e2d73d38`).
- **Interpreter, symbolic-to-pure, pure IR, and extraction**:
  - `src/interp/Interp.ml` (blob `7b06ee4d1bdd302d9cbd85fc2e822c1f5324c1e5`), `src/interp/InterpReduceCollapse.ml` (blob `379bcd2d4904abf5e76a2f28877b2e293cf5f4e3`), `src/symbolic/SymbolicToPure.ml` (blob `95ba91f539e48009efa420dfa956c4c55581cb3a`), `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/symbolic/SymbolicToPureExpressions.ml` (blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`), `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), `src/pure/PureMicroPasses.ml` (blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`), `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`, L2047–2065), `src/extract/ExtractTypes.ml` (blob `371717638f4298cc9c488b31a597608f9bf5089c`, L1197–1257, L1497–1509), `src/extract/ExtractName.ml` (blob `294499309f9492bf74f9a5fc95261556fcdb76a6`), `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`), `src/extract/ExtractBuiltinCore.ml` (blob `60961bddc9aa65a40b58caf5d1c3c777f7990ab9`).
- **Documentation and checked-in test fixtures at `ac9f1bc5262a5e4ff1e24ca78617121382202727`**:
  - `README.md` (blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`), `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`).
  - `tests/src/no_nested_borrows.rs` (blob `707f7d6e1201d1220380dd565a4178806cf3a9ec`) & `tests/lean/NoNestedBorrows.lean` (blob `e2a706b744e2e9a105e305cf8a2b353354209dae`).
  - `tests/src/nested-borrows.rs` (blob `61d62cf0e0723a4019e024882e35fb8b212a67eb`) & `tests/lean/NestedBorrows.lean` (blob `61b3b2b31e50555182867a5b73fa510d05106e22`).
  - `tests/src/traits.rs` (blob `a20f6ee91960cbacf99e8899a32e789f7b855671`) & `tests/lean/Traits.lean` (blob `d234936b72231024fbccf0030a08023836e5eb6e`).
  - `tests/src/raw_pointers.rs` (blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`) & `tests/src/raw_pointers.lean.out` (blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`).
  - `tests/src/names.rs` (blob `7d6ed18643b37393a76881e5719c420a7451b265`) & `tests/lean/Names.lean` (blob `ff03c177c059ef63cb890038957b1b1626e89c6a`).
  - `tests/src/rename_attribute.rs` (blob `0c9dd7f32725c1051437f5873856dea53db61308`) & `tests/lean/RenameAttribute.lean` (blob `76b08a33172229d237825cc6171832d319f76d5f`).
  - `tests/src/arrays.rs` (blob `478af7171452826436f56f12c88493debac8e0d0`, L132–136, L255–268) & `tests/lean/Arrays.lean` (blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`, L221–231, L417–427).

### 2. Primary Upstream Source — `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`

- `charon-pin` (pins Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`).
- `src/Main.ml` (L460–485, L552–559, L583–617, L755–812), `src/Translate.ml` (L22–51, L53–98, L121–132, L280–304, L315–450, L1362–1413, L1461–1510, L2198–2209), `src/PrePasses.ml` (L2322–2392), `src/Config.ml` (L409–417).
- `src/pure/Pure.ml` (L1349–1447), `src/pure/PureMicroPasses.ml` (L13–235, L240–270, L369–374, L376–503), `src/pure/PureMicroPassesLoops.ml` (L2436–2585, L3269–3315), `src/pure/PureTypeCheck.ml` (L165–268).
- `src/symbolic/SymbolicToPure.ml` (L11–125), `src/symbolic/SymbolicToPureTypes.ml` (L1273–1303).
- `src/extract/Extract.ml` (L703–741, L803–817, L2082–2135), `src/extract/ExtractBase.ml` (L755–790, L1133–1201, L1418–1457), `src/extract/ExtractBuiltin.ml` (L883–953), `src/extract/ExtractErrors.ml` (L13–50).
- `backends/lean/Aeneas/Std/Primitives.lean` (L51–91 for `Result α := ITree RustEffect α`, L447–457 for `loop` via `partial_fixpoint`).

### 3. Paired Charon Source — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`)

- `charon/src/transform/add_missing_info/recover_body_comments.rs` (blob `d1defb3d5b552c4f1309f9b7990b0ce1cca492c0`, L1–19, L39–79).
- `charon-ml/src/generated/Generated_LlbcAst.ml` (blob `2a9a9aa71ae863fb3178eaee9f790de16a9f28ea`, L9–19).
- `charon-ml/src/generated/Generated_Types.ml` (blob `69aad6059931c8b365f7d1abb800e5716aec8ad5`, L963–987).

### 4. Preserved Package Support Artifacts

- `support/aeneas-pipeline-pure-extraction-21345f80/pass-inventory.json`: complete ordered inventory of `PureMicroPasses.passes` and post-list stages with configuration gates at `21345f80fa212c596f6437378d7d57984fa2ea77`.
- `support/aeneas-pipeline-pure-extraction-21345f80/representative-trace.md` and `support/aeneas-pipeline-pure-extraction-21345f80/specimen-trace.json`: end-to-end source-reconstructed trace of `list_nth_mut` across preprocessing, symbolic ownership, loop decomposition, pure micro-passes, and Lean extraction.
- `support/aeneas-pipeline-pure-extraction-21345f80/source-reading.json` and `support/aeneas-pipeline-pure-extraction-21345f80/supplement-source-reading.json`: blob identities and line ranges for the `21345f80fa212c596f6437378d7d57984fa2ea77` phase-graph audit.
- `support/aeneas-library-process-architecture/source-map.json`: build and mutable-state source map at `ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- `support/aeneas-incremental-translation-feasibility/incremental-feasibility-matrix.json` and `support/aeneas-incremental-translation-feasibility/source-map.json`: stage-by-stage incremental reuse and invalidation matrix at `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

---

## Revalidation

To revalidate these findings against a newer Aeneas or Charon revision without repeating broad exploratory research:

1. **Source-directed pipeline and state diff**:
   - Diff `src/dune` and `src/Main.ml` to check whether the public `aeneas` OCaml library, the single-input `.llbc` constraint, the `--preset=aeneas` check, backend-specific `Config` mutations, and the final `Errors.error_list` exit-code-1 check still hold, or whether a server/session API was added.
   - Diff `PrePasses.apply_passes` (`src/PrePasses.ml`), `Interp.compute_contexts` (`src/interp/Interp.ml`), `Translate.translate_crate_to_pure` (`src/Translate.ml`), and `PureMicroPasses.passes` (`src/pure/PureMicroPasses.ml`) against `support/aeneas-pipeline-pure-extraction-21345f80/pass-inventory.json`.
   - Diff `SymbolicToPureTypes.ml` (`translate_fwd_ty`, `back_sg`, nested borrow levels), `ExtractName.ml`, `ExtractBase.ml` (`ctx_prepare_name`, `ctx_compute_trait_impl_name_raw`, projector collision logic), `ExtractTypes.ml` (`extract_comment_with_span`), and `backends/lean/Aeneas/Std/Primitives.lean` (`Result` and `loop`).
2. **Discriminating execution probes**:
   - **Recovery vs. exit status and mode separation**: Run `aeneas` on a 2-function `.llbc` crate where one function translates cleanly (`choose`) and one triggers a recoverable `CFailure` (such as raw-pointer dereference), both in `-backend lean` (parallel and `-sequential`) and `-borrow-check`. Verify that `-backend lean` writes partial output (`sorry` or omitted declaration) while exiting with status `1`.
   - **Value/borrow, naming, and comment sentinels**: Translate a compact fixture crate containing:
     ```rust
     /// SENTINEL_DOC
     pub fn f(x: u32) -> u32 {
         // SENTINEL_BODY
         x
     }
     ```
     alongside `choose`, a struct with colliding field/method name `len` (tested with and without `-impl-namespace` and `-namespace Probe`), a trait with a default method and concrete `impl`, a single-loop function, and `#[aeneas::rename]`. Verify the emitted Lean signatures, `.Insts.` / `_loop.body` / `.default` names, and absence of `SENTINEL_DOC` and `SENTINEL_BODY`.
   - **In-process state and incremental oracle check**: In a tiny OCaml test harness linked against the `aeneas` Dune library, run two sequential `translate_crate_to_pure` calls with different `Config` flags and after a recoverable error to verify whether `Config` and `Errors.error_list` leak across calls unless reset, and compare any proposed declaration-level cache reuse against a clean whole-crate translation across body, signature, type, trait, global, and rename edits.
