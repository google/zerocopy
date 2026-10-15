# Aeneas phase order, pure transformations, and extracted-definition identity

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Aeneas at `21345f80fa212c596f6437378d7d57984fa2ea77` translates a decoded Charon crate through LLBC preprocessing, declaration analysis, symbolic ownership execution, symbolic-to-pure synthesis, ordered pure micro-passes, loop decomposition, and backend extraction. The later phases are substantive: they filter values and continuations, restructure loops, recover indexing primitives, choose external models, and print definitions with backend-specific recursion and binding behavior. Inspecting only the symbolic interpreter leaves these links unaccounted for.

Generated output is deliberately available even after some failures. Per-declaration recovery can omit a declaration, discard a body, or print a hole; the CLI checks its accumulated error list after extraction and exits unsuccessfully when errors remain. A file's existence, a well-typed local pure expression, and successful target elaboration are different outcomes. None alone identifies a theorem with the intended Rust artifact and all its model assumptions.

## Applicability

This source-only report addresses A05 (architecture), A18 (pure IR transformations), and A30 (generated definitions and theorem identity). It examines selected paths from [AeneasVerif/aeneas at the immutable pin](https://github.com/AeneasVerif/aeneas/tree/21345f80fa212c596f6437378d7d57984fa2ea77), acquired through read-only GitHub tools on 2026-10-15. Its [`charon-pin`][source-1] names Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`. This report does not claim that a newer Charon producing the same version string has been validated with it.

The report follows the normal translation path and selected failure/configuration branches. It is a module/call-path investigation, not an exhaustive audit of every rewrite body, builtin model, target elaborator, or language backend. No input program was translated, built, or proof-checked. The checked current Lean `Result` definition is reported below; full Lean WP semantics and mechanized LLBC claims require separate evidence.

## Findings

### 1. The phase graph includes two different interpretation boundaries

Basis: source. The main call graph is:

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
           -> Interp.evaluate_function_symbolic (structured body)
           OR SymbolicAst.TargetDispatch (target-dispatch body)
        -> SymbolicToPure.translate_fun_decl
     -> translate trait declarations/implementations
     -> PureMicroPasses.apply_passes_to_pure_fun_translations
  -> extract_translated_crate -> register names/models -> extract files
Main: report accumulated errors -> nonzero exit if any
```

The first boundary interprets LLBC into symbolic ownership operations and symbolic syntax; the second interprets that symbolic syntax into a typed, effect-bearing pure program. Target-dispatch bodies bypass ordinary symbolic execution and directly produce a symbolic dispatch node with dummy symbolic inputs. Bodies not handled by these transparent paths can yield no symbolic body. [`Main.ml`, load and dispatch; L583–617][source-2], [prepasses through final error status; L755–812][source-2], [`Translate.ml`, symbolic entry; L22–51][source-3], [crate translation and extraction; L2198–2209][source-3].

`translate_crate_to_pure` computes contexts first, translates type declarations and global signatures, builds function/method signature maps, then processes bodies. It partitions opaque and transparent functions and orders transparent work by size for parallel scheduling. That size ordering is a scheduling heuristic, not an independently proved semantic decomposition. Source includes per-task fresh-variable generators and precomputes builtin maps before parallel work to avoid races on memoized values. [`translate_crate_to_pure`; L315–450][source-3], [`Main.ml`, cache preparation; L552–559][source-2], [`PureMicroPasses`, task-local generator; L369–374][source-4].

### 2. LLBC preprocessing changes the admitted program representation

Basis: source. [`PrePasses.apply_passes`; L2322–2392][source-5] gives the exact order:

1. Crate-wide `update_array_default`, then `anon_consts_to_calls`.
2. Per-function `fix_closure_lifetimes`, `fix_closure_signature_regions`, `fix_anon_const_initializers`, `erase_body_regions`, `remove_unreachable`, `update_loops`, `remove_useless_joins`, `remove_shallow_borrows_storage_live_dead`, `simplify_panics`, `decompose_global_accesses`, `refresh_statement_ids`.
3. Crate-wide `strip_unnecessary_target_suffixes`, `filter_marker_traits`, `filter_type_aliases`, `remove_vtables`, `rename_type_vars`, `simplify_trait_calls`.

This inventory separates semantic normalization (closure lifetime/signature repair, anonymous-constant calls, loop/global/panic transformation) from representation maintenance (region erasure and statement-ID refresh) and naming/filtering. That classification is **derived** from the named transformations and inspected driver; it is not a theorem that the naming/filtering steps are always semantically irrelevant. In particular, erasing a field or filtering a declaration is justified only relative to the intended downstream semantics and retained context. The driver folds these passes in order; a failed per-function pass records an error and substitutes `ErrorBody`, allowing the remaining crate to proceed.

There is no single total “supported fragment” predicate demonstrated by this path. Some checks are early, such as the required Charon `Aeneas` preset and the rejection of bound/free implied lifetime constraints before body translation. Other cases fail only during interpretation, synthesis, a micro-pass, or printing. The preset is a configuration admission check; it does not prove every surviving body belongs to a mathematically characterized subset. [`Translate.translate_function_to_pure_aux`; L121–132][source-3].

### 3. Pure syntax retains effects, binders, loops, and explicit error nodes

Basis: source. `Pure.texpr` is a record `{ e; ty }`; the OCaml type does not make the annotation a proof of typing. Expressions include free/bound variables, constants, application, lambda, qualified definitions/operators, `Let`, switch, loop, structure update, metadata, and `EError`. A boolean on `Let` distinguishes monadic sequencing from ordinary binding. Loop records carry ordered values and backward continuations, input/output types, body binders, and the `to_rec` flag. [`Pure.ml`, expression and loop grammar; L1349–1447][source-6].

Symbolic-to-pure function synthesis supplies a return constructor that wraps outputs in the result effect when `effect_info.can_fail`; it supplies a panic constructor of the matching output type; then translates the symbolic body and closes the input binders. Initially loop nodes remain inside the body. Translation of the body can catch `CFailure` and leave `body = None`. These details distinguish a typed record from checked typing, and a missing body from an implementation proved correct. [`SymbolicToPure.translate_fun_decl_body`, `translate_fun_decl`; L11–125][source-7].

Derived semantic obligation: the pure IR needs an interpretation for ordinary versus monadic `Let`, panic/failure, divergence, backward continuations, and the loop operator before rewrite correctness can be stated. A homomorphic “lambda calculus plus tuples” account is insufficient if it forgets when a failing or diverging computation is evaluated. This investigation identifies the syntax and lowering sites, but does not provide a complete formal denotation for the current IR.

### 4. The micro-pass list is ordered and includes effect-sensitive rewrites

Basis: source + documentation. [`PureMicroPasses.passes`; L13–235][source-4] is folded once in list order; individual entries can be configuration-gated. The companion `pass-inventory.json` preserves every label, including repeated passes and flags. The useful dependency groups, in their actual relative order, are:

| Stage | Named transformations | Preservation concern |
| --- | --- | --- |
| Metadata and basic normalization | Pretty names; remove metadata; inline anonymous constants; optional target-feature assertions; unit variables; optional assertions; structure decomposition/update introduction; lambda/let simplification | Metadata may be discarded only after its consumers have run. Feature assertions add an explicit condition to the model. |
| Expression cleanup | Assignment inlining; beta reduction; box elimination; trait simplification; duplicate-call simplification; optional application/tuple merge; useless-expression filtering; branching lets; let-then-return simplification | Inlining, call removal, and duplication must respect failure, sequencing, and divergence. Names alone do not prove the relevant side conditions. |
| Loop relation preparation | Output tuple decomposition; output-continuation simplification; beta/inlining rounds; input/output filtering without constant-input filtering; reorder outputs; `loops_to_recursive`; reorder inputs | Stable correspondence between values, continuation positions, and loop edges must survive every permutation and deletion. |
| Backend-oriented cleanup | Let-to-match; flatten/update/aggregate simplification; further lambda/let/inlining/filtering rounds; panic-then-wrapping arithmetic simplification | Refutable patterns, checked arithmetic failure, and evaluation order must remain aligned. |
| Index recovery and final generic lowering | Recover builtin indexing; filter/eta/inlining cleanup; array/slice-update simplification; let-then-return; optional monadic-let decomposition, nested-pattern decomposition, monadic unfolding, pure-call lifting; machine-word matches | Recovered primitives must agree with the selected models, including bounds failure, update/backward behavior, and target width. |

The source gives concrete ordering reasons. Pretty naming precedes metadata removal, and later passes assume metadata is gone. Loop-output decomposition precedes relation analysis because later passes can crash without it. Output-continuation simplification precedes filtering to avoid losing useful loop-input ordering. Constant inputs are deliberately retained until after auxiliary loop definitions are introduced. Repeated beta, lambda, inlining, and filtering passes exploit opportunities created by prior rewrites; they are not an arbitrary fixpoint saturation engine. [`passes`, dependencies around loop preparation; L95–155][source-4], [`apply_passes_to_def`; L240–270][source-4].

A pass inventory is not a proof inventory. Derived obligations include beta/eta laws under the chosen effect discipline; freshness/capture avoidance; effect-aware dead-code and duplicate-call elimination; equivalence of indexing/update primitives; and a simulation for every loop-interface change. No independently verified rewrite certificate was identified in this bounded reading. The numerous sanity checks and typed helper constructors are executable safeguards, not replacements for those arguments.

### 5. Loop lowering has a post-list pipeline of its own

Basis: source. After the ordinary pass list, the driver applies `decompose_loops`; filters constant loop inputs on the function and auxiliary loops; extracts loop-body continuations into auxiliary body functions; replaces residual loop nodes with fixed-point-operator applications on functions, loops, and bodies; simplifies let-then-return; reintroduces assertions; and optionally adds fuel last. It assembles `{ f; loops; bodies }`, so the output definition associated with one source function can include several generated auxiliaries. [`apply_passes_to_pure_fun_translations`, post-list stages; L376–503][source-4].

`loops_to_fixed_points_visitor` packages loop inputs and outputs into types, rewrites continue/break handling, creates a body lambda, and applies `Qualif LoopOp` to that body and its initial inputs. Extraction prints this qualifier as `loop`. [`PureMicroPassesLoops`; L3269–3315][source-8], [`Extract.extract_App`; L803–817][source-9].

The earlier `loops_to_recursive` transformation is guarded by an analysis of loop input/output relations: identity input continuations, compatible calls to input continuations in outputs/reentry, and a detected structural-decrease relation; `no_recursive_loops` can disable it. The list entry itself has no outer flag gate, so the internal criteria matter. Its recognition of a structural measure guides a transformation; it is not a report of a target proof being elaborated. [`loop_satisfies_recursive_criteria_aux`; L2436–2585][source-8]. Fuel is introduced last because earlier passes manipulate unfuelled parameter lists. Changing that order requires reviewing every affected call signature.

### 6. Checks and diagnostics have different force

Basis: source. `Config.sanity_checks` defaults false. `check_fun_decl_vars_are_well_bound` is gated by it and checks free-variable closure, then opens all binders to detect invalid bound occurrences. `Config.type_check_pure_code` also defaults false, with an upstream TODO to fix bugs and reactivate checks. `SymbolicToPureTypes.type_check_texpr` tests this flag before calling `PureTypeCheck.check_texpr`; several typed constructors have the same gate. Calling a helper named `type_check_texpr` in source therefore does not mean a default run performs that check. [`Translate` well-binding check; L53–98][source-3], [`Config`; L409–417][source-10], [`type_check_texpr`; L1273–1303][source-11].

Even enabled, `PureTypeCheck` is partial: qualified function/global/trait-constant/loop-operator/scalar-projection cases contain TODO branches; loop checking traverses the body with a TODO for inputs. Its implemented application, binding, pattern, constructor, and structure-field checks are valuable, but they do not form a complete verified typechecker for the current IR. [`PureTypeCheck.check_texpr`; L165–268][source-12].

Timing/size diagnostics, pretty-name generation, output formatting, and progress reports should not be conflated with checks. `diagnose_detailed` requires `diagnose_micro_passes`; those flags collect timings, not proof certificates. CLI rejects incompatible fuel/decreases settings, limits certain options to Lean, and rejects Lean decreases-clause use with recursive groups in the inspected condition. Such configuration rejection is evidence of a guard, not a theorem that all other combinations work. [`Main.ml`, option checks; L460–485][source-2], [recursive/decreases guard; L604–617][source-2].

### 7. Model selection and printing determine the actual target program

Basis: source. Builtin maps associate Rust name patterns with extraction names, types, and `can_fail` metadata; default trait methods produce additional names. Duplicate builtin patterns are rejected while building the name-matcher map. These maps are memoized and shared with effect analysis. Consequently a call's emitted constant and whether a call is treated as effectful depend on model selection, not only the Rust signature or symbolic node. [`ExtractBuiltin`, map/effect construction; L883–953][source-13].

Extraction initializes names, registers local declarations and generated auxiliaries, handles declaration groups, and opens bound variables to fresh free names before printing. Name maps distinguish function IDs plus loop IDs from display strings. Lean escaping handles hyphens and certain keyword positions using quoted identifiers; namespace/import choices and collision resolution also matter to the final constant. This is source-level naming machinery, not a proof that Lean resolves every printed occurrence as intended. [`extract_translated_crate`; L1461–1510][source-3], [`escape_name`; L755–790][source-14], [`extract_fun_decl_gen`; L2082–2135][source-9].

For Lean, emitted files import `Aeneas`, open `Aeneas Aeneas.Std Result ControlFlow Error`, set heartbeat/recursion-depth options, and may declare a noncomputable section. Builtin `TResult` prints as `Result`; success/failure print as `ok`/`fail`; `TLoopResult` prints as `ControlFlow`. Recursive declarations print `def` followed by `partial_fixpoint`; opaque/builtin declaration kinds can print `axiom`. Optional termination clauses name generated measure/proof helpers. [`Lean file headers`; L1362–1413][source-3], [`builtin names`; L1133–1201][source-14], [`declaration qualifiers`; L1418–1457][source-14].

The current Lean library defines `@[irreducible] def Result α := ITree RustEffect α`; `RustEffect` has a failure input with empty output, `ok` is return, `fail` emits that effect, and `div` is tree divergence. The checked `loop` definition recursively binds a `ControlFlow` body and uses `partial_fixpoint`. This refutes treating the current backend model as merely an old three-constructor inductive result datatype. It does not establish the entire ITree library or WP metatheory. [`Std/Primitives.lean`, current result; L51–91][source-15], [current loop; L447–457][source-15].

### 8. Recovery and target elaboration do not certify completeness

Basis: source + derived. `translate_function_to_pure` catches `CFailure` and returns no translation; symbolic-to-pure body recovery can return no body; prepass recovery creates `ErrorBody`. `Extract.extract_texpr_errors` prints `sorry` for Lean and admission/error forms for other targets; extraction error helpers can save an error and continue printing. `Main` evaluates `Errors.error_list` after translation/extraction. Therefore output may intentionally be partial even when files were written. [`function recovery`; L280–304][source-3], [`error printing`; L703–741][source-9], [`ExtractErrors`; L13–50][source-16].

Derived identity requirement: retain the source/build artifact, exact `.llbc`, Aeneas/Charon pins, flags, selected target, model-library revision, generated files and auxiliaries, and target imports/options; then inspect the elaborated constant and theorem statement, their dependencies, and any admitted or opaque assumptions. Printed text is input to name resolution, notation, coercions, instance search, and elaboration. A kernel-checked theorem is about the elaborated expression under its assumptions; the inspected printer does not independently certify that this expression denotes the intended extracted source definition. Deeply embedded syntax plus a denotation could make that relation explicit, but no such end-to-end certificate was established for this pipeline by this source reading.

### 9. A concrete function connects the phase graph to retained output

The [source-reconstructed list_nth_mut trace](representative-trace.md) follows a particular current Rust function and its retained Lean endpoint through the controlling preprocessing, ownership, loop, pure and extraction paths. It explains the selected value and backward list reconstruction, with [specimen-trace.json](specimen-trace.json) preserving the endpoint identities. Intermediate LLBC and runtime state snapshots were not acquired; this is not a newly executed pipeline trace.

## Boundaries

- **Not examined:** every micro-pass implementation body, every builtin model, all target elaborators, generated `.olean` files, external model proofs, and all configurations. The full ordered inventory is stronger than a list of topics but weaker than per-pass verification.
- **Unknown:** complete current pure-IR semantics; effect-sensitive correctness of all rewrites; pass-order independence beyond the documented dependencies; end-to-end source/target refinement; and elaborated theorem identity for any concrete input. No experiment or proof run occurred.
- **Unsupported in identified guards:** some higher-ranked bound/free lifetime constraints; selected incompatible CLI combinations; the inspected Lean decreases/mutual-recursion combination. Residual `Pure.Loop` at extraction is an error because micro-passes should have eliminated it.
- **Known not to imply:** Aeneas output existence does not imply error-free translation; pure type annotations do not imply checked typing; target elaboration does not remove axioms or `sorry`; a theorem about a generated function does not itself prove extraction fidelity or the validity of external models.

## Evidence

Immutable links identify the Aeneas pin and narrow symbols/regions. `source-reading.json` records acquired blob identities and scope; `pass-inventory.json` preserves exact driver order and gate information for cheaper future review. Source comments serve as documentation, and semantic obligations/classification are labeled derived. There is no execution or normative theorem evidence.

## Revalidation

Diff `Main` load/dispatch/error handling, `PrePasses.apply_passes`, `Translate.translate_crate_to_pure`, the `PureMicroPasses.passes` list and post-list pipeline, and `ExtractBase`/`Extract` names and qualifiers. Inspect each changed transformation together with its preconditions and consumers; list equality alone does not validate a modified pass body. Recheck model effect metadata, `TResult`/`LoopOp` mappings, and the actual imported `Std.Primitives` definitions before reusing any backend claim.

For a concrete future artifact, the cheapest discriminating validation is a small function exercising one failing primitive, one mutable-reference backward continuation, one loop, and one opaque/modelled call, with the generated auxiliary definitions and target elaboration results preserved. Check final CLI status and errors, emitted holes/axioms, exact model imports, elaborated names and theorem dependencies. Such runs were not performed in this source-only investigation. A passing example checks those paths; a proof of a current rewrite or end-to-end pipeline requires substantially stronger evidence.

[source-1]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin
[source-2]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml
[source-3]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml
[source-4]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/pure/PureMicroPasses.ml
[source-5]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/PrePasses.ml
[source-6]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/pure/Pure.ml
[source-7]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPure.ml
[source-8]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/pure/PureMicroPassesLoops.ml
[source-9]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/Extract.ml
[source-10]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml
[source-11]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureTypes.ml
[source-12]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/pure/PureTypeCheck.ml
[source-13]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/ExtractBuiltin.ml
[source-14]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/ExtractBase.ml
[source-15]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Primitives.lean
[source-16]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/ExtractErrors.ml
