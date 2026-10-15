# Charon extraction and normalization at 9e95cf3

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Charon extracts a compiler-selected program, then performs configurable type and body transformations. Requested MIR level is not a uniform guarantee about all bodies: local early bodies can have been stolen, foreign function bodies normally use optimized MIR, and constants may use CTFE MIR. The Aeneas preset keeps the default request of promoted MIR; precise drops raise it to at least elaborated MIR. Effective source-build identity and actual per-body MIR provenance therefore belong at the extraction boundary.

The production pipeline has 53 non-print schedule occurrences, including repeated storage, CFG and local cleanup passes. Most are not whole-crate sweeps: ULLBC and LLBC phases fuse passes per body, and owned passes preprocess bodies they carry. The inventory below and the accompanying JSON distinguish scheduling, predicates, data-dependent matches and semantic obligations. Neither the two type checks nor a successful extraction proves preservation of Rust behavior.

The strongest immediately useful semantic warning is that normalization intentionally abstracts. Dynamic-check folding can discard a concrete cleanup destination; indexing-to-calls introduces references; allocator hiding removes a type parameter. These transformations need assumptions about the consumer's semantics and permitted inputs. RawMir is still translated and normalized by several always-scheduled passes; it is not untouched rustc MIR.

## Applicability

Directly examined: AeneasVerif/charon at `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`, package 0.1.291, whose root `rust-toolchain` requests nightly-2026-09-17 with rustc-dev, llvm-tools, rust-src and miri. This identifies source configuration, not installed compiler binaries or compiler source revisions. No upstream program was built or run.

For a limited revision comparison, `options.rs`, `transform/mod.rs` and `docs/minirust.md` were also fetched at Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`, the dependency identified for Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`. Those three files have identical acquired contents at the two Charon pins. This does not establish compatibility of the complete repositories, identity of all translator code, or successful execution of that Aeneas/Charon combination.

This report answers A06 and A07 of the investigation agenda. “Aeneas preset” means Charon's `Preset::Aeneas` at the examined Charon revision; it does not assert that any particular invocation of Aeneas selected every default recorded here.

## Findings

### A06: the driver establishes a compiler boundary with qualifications

Basis: **source**.

In [`driver.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/driver.rs), `run_rustc_driver` distinguishes Cargo primary packages from dependencies with `CHARON_USING_CARGO` and `CARGO_PRIMARY_PACKAGE`. Translation additionally requires a `--target` argument: host build-script and proc-macro crates run through normal compiler callbacks. Charon's [wrapper](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon/main.rs), `translate_with_cargo`, arranges an explicit target, supplies `CHARON_ARGS`, and uses wrappers to prevent ordinary Cargo cache reuse for selected extraction. These are operational selections, not a proof of a complete Cargo dependency closure.

`setup_compiler` and `set_mir_options` set always-encode-MIR, optimization level zero and preserve-UB, and disable the MIR CheckAlignment and CheckNull passes. These settings apply even in the “normal compiler” callbacks for dependencies. “Normal” therefore does not mean default compiler MIR settings. The settings help retain MIR and avoid specific inserted checks; they do not undo earlier lowering or prove every source UB survives.

Selected translation occurs in `after_expansion`. The driver first runs attribute, well-formedness, coherence and typechecking queries chosen to avoid stealing MIR. It continues compiler analysis; `after_analysis` additionally requests instance MIR and mono-item collection when ordinary artifacts are not emitted, to expose late errors. `--skip-borrowck` can override `mir_borrowck` with an empty success result. Thus the extraction callback precedes completion of all ordinary MIR checks, and an intermediate extracted body is not evidence that borrow checking succeeded. A consumer must check final success and partial-error state and record whether borrow checking was bypassed.

Sysroot selection can use explicit/default/custom-built Miri sysroots. The Miri sysroot disables codegen. Availability of foreign MIR depends on the exact sysroot and compiled dependencies. The selected compiler performs expansion, typing, const-related queries, borrow analysis unless skipped, MIR lowering and shims; Charon does not independently certify those stages. The present source audit did not inspect the pinned rustc implementation of every invoked query.

### Actual MIR selection is item-specific

Basis: **source** in [`get_mir.rs`, `get_mir_for_def_id_and_level`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/translate/get_mir.rs) and [`TranslateOptions::new`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/options.rs).

| Item/query case | Body supplied |
| --- | --- |
| Local, Built requested and body available | clone of `tcx.mir_built` |
| Local, Promoted requested and body available | main body of `tcx.mir_promoted` |
| Local, Elaborated requested and body available | `mir_drops_elaborated_and_const_checked` |
| Local early body stolen, or Optimized requested | continue into the general availability path |
| MIR available, item neither a global const nor static | `optimized_mir` |
| Nontrivial global const, local static, or const function falling through the preceding branch | `mir_for_ctfe` |
| Promoted definition | `rustc_const_uneval::promoted_body` |
| Allocation definition or no available body | no MIR body |

The branch order matters: a const function with ordinary MIR available can take optimized MIR before the CTFE alternative. It would be inaccurate to say all const functions always use CTFE. The general query path also explains foreign bodies; early MIR is local-only. Always-encode-MIR helps dependencies built through this wrapper, while the source explicitly limits ordinary prebuilt stdlib MIR availability.

`get_mir_inner` additionally invokes hax substitution under full monomorphization, using the item's actual generic arguments and typing environment. `get_mir` catches panics and turns them into translation errors. This is error recovery, not an alternate verified extraction semantics. [`translate_bodies.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/translate/translate_bodies.rs) determines conditional versus precise drops from actual body phase, not merely the requested level.

### Artifact identity is useful but incomplete

Basis: **source** plus **derived** consequences.

[`CrateData`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/export.rs) stores Charon version, translated crate and `has_errors`. [`TranslatedCrate`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/krate.rs) stores CLI options, target information, runtime UB/overflow/contract-check flags, source-file records, declarations and item names. [`File` and spans](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/meta/spans.rs) record crate name, local/virtual/not-real file name and optional contents, with macro/inlining provenance spans. Missing file contents are permitted. The stored CLI options are more informative than a preset name alone, but are not a complete transcript of every effective compiler input.

These inspected structures do not constitute an authenticated build manifest. They do not, by themselves, bind executable/compiler/sysroot hashes, all dependency artifacts, Cargo lock resolution, edition/cfg/features, build-script outputs, environment, proc-macro inputs, or the final effective rustc argument vector to a particular output. Some of those may appear in user-supplied arguments or file contents, but absence of dedicated binding remains consequential. Nor is requested MIR level an explicit record of the actual query branch used for each body.

A reliable source-build-to-output claim therefore needs a separately preserved manifest and output digest, final success/error status, selected target and entry set, dependency and sysroot identities, effective options and compiler arguments, generated inputs and source contents. A boundary at post-MIR ULLBC can identify the program handed to normalization; it cannot independently establish that rustc faithfully extracted the intended Rust build.

### A07: full schedule and preservation obligations

Basis: **source** for schedule/gates; **derived** for obligations.

[`run_transformation_passes`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/mod.rs) schedules the following exact order, omitting diagnostic prints. Rows 1–8 are the item prefix, 9–36 the fused ULLBC phase, 37–39 run only when `!options.ullbc`, and 40–53 the common final phase. The accompanying [pass inventory](pass-inventory.json) gives immutable source links, Git blob identities, exact `should_run` excerpts and internal option references for each occurrence. A blank predicate excerpt means there is no override in that module; the pass traits default to true. Internal early returns and pattern failures may still make a scheduled pass inert. Row 4 is PostTranslation; row 52 is PostTransformation.

| # | Scheduled pass | Preservation obligation, not an established theorem |
| --- | --- | --- |
| 1 | `add_missing_info::link_specs` | Contract links preserve item/associated-item identity; no executable change. |
| 2 | `simplify_output::duplicate_defaulted_methods` | Copied default bodies substitute the same trait/impl arguments and dispatch. |
| 3 | `add_missing_info::compute_short_names` | Names remain unambiguous display aliases; IDs and execution unchanged. |
| 4 | `typecheck_and_unify::Check` | Type consistency and best-effort region unification; this check is not semantic preservation. |
| 5 | `finish_translation::filter_invisible_trait_impls` | Remove only implementations already classified invisible; preserve relevant dispatch. |
| 6 | `simplify_output::lift_associated_item_clauses` | Reindex proof arguments and bound regions consistently when moving clauses. |
| 7 | `add_missing_info::add_missing_alias_clauses` | Added trait premises match unresolved associated-type requirements without changing instantiations. |
| 8 | `add_missing_info::add_implied_outlives` | Make only signature-implied outlives predicates explicit with correct binders. |
| 9 | `add_missing_info::detect_drop_flags` | Detected Boolean tracks precisely initializedness on the relevant paths. |
| 10 | `resugar::resugar_drops` | Recover conditional drops without losing partial-move/cleanup effects or misidentifying flags. |
| 11 | `finish_translation::insert_ptr_metadata` | Inserted metadata expressions match original pointer metadata without new accesses. |
| 12 | `finish_translation::insert_assign_return_unit` | Unit return initialization changes no observable evaluation or validity behavior. |
| 13 | `finish_translation::insert_storage_statements` | Explicit allocation/deallocation reproduces implicit local lifetime; globals excluded from dead insertion. |
| 14 | `normalize::desugar_drops` | Precise drop glue call with fresh mutable reference preserves validity, moved-out state, cleanup and evaluation order. |
| 15 | `normalize::skip_trait_refs_when_known` | Direct callee has identical implementation selection and generic substitution. |
| 16 | `normalize::transform_dyn_trait_calls` | Vtable load/call preserves metadata, method ABI, argument ordering and unwind edge. |
| 17 | `simplify_output::anon_const_to_call` | Initializer invocation preserves constant identity, sharing, evaluation and effects. |
| 18 | `simplify_output::inline_selected_functions` | Inlining preserves argument moves, local scope, returns, unwind paths and constant semantics. |
| 19 | `resugar::reconstruct_panic_calls` | Recognized panic callee has the same failure and unwind behavior. |
| 20 | `simplify_output::filter_trivial_drops` | NoopDestruct classification justifies removing all effects and unwind behavior. |
| 21 | `resugar::move_asserts_to_statements` | Implicit failure semantics must justify discarding the concrete cleanup-edge identity. |
| 22 | `control_flow::merge_goto_chains` | Redirected/concatenated paths preserve statements and all edge destinations, including cyclic paths. |
| 23 | `resugar::reconstruct_fallible_operations` | Matched checks correspond exactly to implicit panic checks, arithmetic mode and operand evaluation. |
| 24 | `resugar::reconstruct_vec_boxes` | Box/Vec construction rewrite preserves initialization, allocation failure, moves and cleanup. |
| 25 | `resugar::reconstruct_box_derefs` | Hidden-pointer projection denotes the same Box pointee and validity requirements. |
| 26 | `resugar::reconstruct_intrinsics` | Recognized offset_of constant equals compiler layout-derived offset. |
| 27 | `resugar::reconstruct_asserts` | Branch-to-assert resugaring preserves condition, expected value and error/unwind effects. |
| 28 | `resugar::reconstruct_static_accesses` | All rewritten temporary dereferences denote the same static; no other temporary uses are lost. |
| 29 | `simplify_output::simplify_constants` | Fresh temporaries/promoted globals preserve sharing, relocation, metadata and evaluation order. |
| 30 | `simplify_output::index_intermediate_assigns` | RHS is evaluated before LHS reference construction with identical moves and failure behavior. |
| 31 | `simplify_output::remove_unit_locals` | Erased direct unit uses/stores do not erase side effects or validity errors. |
| 32 | `control_flow::duplicate_return` | Clones keep branch/cleanup destinations and cycles; dynamic execution still visits only one clone. |
| 33 | `resugar::reconstruct_matches` | Discriminant cases and fallthrough remain equivalent including invalid discriminants. |
| 34 | `simplify_output::remove_unused_locals` | Only unobserved local storage is removed; all remaining IDs/types/references remap consistently. |
| 35 | `control_flow::merge_goto_chains` | Redirected/concatenated paths preserve statements and all edge destinations, including cyclic paths. |
| 36 | `simplify_output::update_block_indices` | Reachability and bijective renaming preserve all reachable edges; unreachable blocks may disappear. |
| 37 | `control_flow::ullbc_to_llbc` | Structured positions simulate CFG positions including divergence and unwinding. |
| 38 | `control_flow::prettify_cfg` | Structural simplification preserves nested block, loop and jump targets. |
| 39 | `simplify_output::builtins_to_function_calls` | Library models agree on validity, panic, retagging, allocation, aliases and evaluation order. |
| 40 | `finish_translation::insert_storage_statements` | Explicit allocation/deallocation reproduces implicit local lifetime; globals excluded from dead insertion. |
| 41 | `normalize::normalize_trait_refs` | Normalized proof references select equivalent implementations. |
| 42 | `normalize::expand_associated_types` | Lifted generics/associated types and substitutions agree for every caller. |
| 43 | `simplify_output::remove_unused_clauses` | Removed evidence is unused, including indirect proof dependencies. |
| 44 | `simplify_output::remove_adt_clauses` | Removed ADT evidence does not lose associated-type information or relevant trait obligations. |
| 45 | `simplify_output::remove_unused_locals` | Only unobserved local storage is removed; all remaining IDs/types/references remap consistently. |
| 46 | `simplify_output::remove_nops` | Only inert statements are removed; comments retained when present. |
| 47 | `add_missing_info::recover_body_comments` | Only source presentation changes. |
| 48 | `simplify_output::hide_allocator_param` | Consumer restriction/model must justify losing allocator parameter identity. |
| 49 | `normalize::partial_monomorphization` | Specialized copies and shape arguments denote the original instantiation with matching binders. |
| 50 | `add_missing_info::compute_layout_guarantees` | Derived layout facts are valid for represented target/repr and do not overclaim actual layout. |
| 51 | `add_missing_info::reorder_decls` | Dependency SCC/order changes do not alter item identity or runtime order. |
| 52 | `typecheck_and_unify::Check` | Type consistency and best-effort region unification; this check is not semantic preservation. |
| 53 | `simplify_output::unbind_item_vars` | Free-variable renaming preserves the correct binding level under nested binders. |

`TransformCtx::run_pass` checks predicates, processes an owned ULLBC pass's carried bodies through its preceding passes, runs the enabled body sequence per item, and then calls enabled finalizers. This detail matters to any attempted replay: a simple sequence of 53 independent whole-program rewrites is not the implemented execution scheme.

The Aeneas preset enables box treatment, operations/indexing to calls, fallible-operation/panic/assert/match reconstruction, associated-type lifting for all items, hidden marker traits/allocators, unused Self/ADT clause removal, top-level free variables, explicit local deallocation and nongenerated tuple structs. It does not itself force full monomorphization, precise drops, inline-anonymous-const handling or drop resugaring. The separate MiniRust option overlay has a different semantic profile, described in the companion report.

For a default-options invocation with only this preset added, rows 2, 9, 10, 14 and 17 are disabled by their explicit gates; row 49 returns immediately without a monomorphize-mut choice. Rows 18 and 24 depend on discovered inline candidates and Box library functions, respectively. The other scheduled rows are enabled in this profile, although many are inert where their input patterns do not occur. Extra user flags can change that profile. The JSON retains the predicate and internal-guard lines needed to recompute it rather than treating this profile as universal.

The type checker skips items already marked erroneous and accepts certain type mismatches in copies of default trait methods, whose potentially contradictory associated-type premises were checked in the original methods. Its source distinguishes best-effort body-region unification after translation from the post-transformation consistency check. These qualifications further limit what passing the two checks establishes.

### Checks, references and erasure require distinct justifications

Basis: **source** plus **derived** obligations.

[`reconstruct_fallible_operations`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/resugar/reconstruct_fallible_operations.rs) recognizes precise instruction shapes and restores implicit panic behavior, including overflow modes. It uses local-use checks and pattern guards; this is substantive implementation, not an arbitrary removal of every assertion. Its source explanation relies on arithmetic/array operations on the verification side having the corresponding failure semantics.

[`move_asserts_to_statements`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/resugar/move_asserts_to_statements.rs) changes a built-in-check assert terminator into a statement and a normal goto. It maps the old unwind target to an `AbortKind` if the target is a recognized abort block, otherwise to generic panic. The original cleanup-block identity is no longer in that statement. Reconstruction later gives such a statement an unwind-resume block. Consequently the existence of unwind fields in current LLBC does not alone imply all dynamic-check cleanup paths survived every selected normalization. Full unwind preservation is an additional condition to establish for this mode.

[`index_intermediate_assigns`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/simplify_output/index_intermediate_assigns.rs) splits assignments whose RHS and LHS both contain index projections. Its documented motivation is to finish the RHS before introducing the mutable LHS reference. [`IndexVisitor::transform_place`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/simplify_output/builtins_to_function_calls.rs) introduces a fresh shared or mutable borrow of the array/slice base and calls the selected library indexing method. This avoids a specific alias-ordering problem but is not a general proof that introducing references preserves all pointer, initializedness, validity and retagging behavior. The same issue arises for precise-drop desugaring's fresh mutable reference. One must justify reference validity and alias permissions over its whole referent at the insertion point, matching original access/borrow requirements and failure behavior. A fresh local name does not supply that justification.

Box dereference reconstruction tracks recognized hidden-pointer assignments and rejects ambiguous/non-dereference uses. Vec construction reconstruction recognizes the `Box<MaybeUninit<[T; N]>>` lowering and replaces unsafe construction with Box::write/new patterns under its guards; it is disabled under full hax monomorphization. These transformations abstract allocation and initialization patterns; they do not prove arbitrary unsafe blocks safe.

Unit-local removal deliberately limits substituted reads to direct unit locals and leaves other rvalues that may have side effects. Unused-local removal does not count storage markers as uses. These restrictions narrow what is erased, but whole-program preservation still requires a validity/storage argument. `hide_allocator_param` removes the last allocator type argument for identified Box, Vec, Rc and Arc types and can insert an error type for references to the removed binder. This is a consumer abstraction with a restriction/model obligation, not a theorem about arbitrary allocator behavior.

### Small witnesses and the pre-normalization seam

Basis: **derived** design analysis grounded in the inspected interfaces.

Renumbering, goto merging, return/cleanup cloning, binder renaming and clause substitutions admit finite local witnesses: old/new ID maps, copied-block maps, edge maps, binder substitutions and proof-reference maps. A checker could validate those maps against both programs without rerunning heuristics. Check folding needs an exact matched sequence plus use/def and failure correspondence; reference-introducing rewrites additionally need semantic validity and alias assumptions. A syntactic match alone cannot discharge these.

`print_original_ullbc` is invoked before row 1; this is a useful inspection seam after MIR translation but before the listed normalization. It is a diagnostic pretty-print, not a supplied proof certificate or a complete compiler-origin record. A preserved structured artifact at that seam would retain concrete CFG and cleanup information that later passes abstract, but already excludes MIR-only statements removed by translation and any earlier compiler transformations. The RawMir preset sets opaque-body extraction, raw constants and ULLBC only; many listed passes still execute. It must not be equated with a no-transform extraction.

## Boundaries

- **Not examined:** actual rustc binaries, full rustc query implementation, Cargo resolver/build-script closure, reproducible build binding or runtime behavior of these pins.
- **Unknown:** full semantic preservation of each pass, in particular UB reflection under fresh references and failure/cleanup correspondence under every normalization combination. No theorem or independent certificate was found in the inspected transformation code.
- **Known not to apply:** one uniform early-MIR phase for local and dependency bodies; the claim that RawMir bypasses the schedule; the claim that type consistency establishes Rust semantic preservation.
- Source error recovery and `has_errors` permit partial artifacts. An artifact's existence does not establish complete translation.
- Existing corpus reports about Charon 0.1.210 and earlier nightly toolchains were consulted for candidate seams, then current determining source was read. Their old claim that LLBC drops/calls discard all unwind targets does not describe the present AST. Their older drop-interface name `drop_in_place` must not replace the present `drop_glue` name.

## Evidence

All technical acquisition occurred on 2026-10-15 through immutable GitHub source reads. [source-index.json](source-index.json) records paths, exact blob identities and URLs for the principal files and transformation modules read. Pass-specific links/gates and derived obligations are in [pass-inventory.json](pass-inventory.json). Neither file records execution.

Key controlling symbols are `driver::{setup_compiler,set_mir_options,run_rustc_driver,precheck_rustc_errors}`, `get_mir_for_def_id_and_level`, `CliOpts::apply_preset`, `TranslateOptions::new`, `run_transformation_passes`, `TransformCtx::run_pass`, `CrateData`, `TranslatedCrate`, `IndexVisitor::transform_place`, and the pass implementations linked above. The bounded dependency comparison covered only three named files. Source index entries whose contents were inspected only for introductory rationale, guards or scheduling are evidence for those limited properties, not full algorithm verification.

## Revalidation

For another revision, first diff driver settings, the complete MIR-query branch order and `TranslateOptions::new`; changes there can alter applicability before normalization runs. Diff `apply_preset`, the schedule, each predicate and its internal guards, including carried-body preprocessing/finalization. Compare the three dependency files again before extending their equality claim.

Then check the narrow semantic seams: dynamic-check statements' retained failure destinations; indexing reference insertion and RHS/LHS order; storage insertion on return and unwind; unit-local erasure; allocator-parameter removal; Box/Vec lowering recognizers. Inspect artifact structures for newly added build/provenance records. Source comparisons discriminate implementation changes; they do not prove preservation. A later reproduction would need complete toolchain/configuration, input and output bytes.
