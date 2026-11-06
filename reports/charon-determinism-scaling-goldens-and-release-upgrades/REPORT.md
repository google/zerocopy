# Charon Determinism, Extraction Normalization, Scaling Probes, Output Goldens, and Release Upgrade Gates

## Summary

This report synthesizes seven primary source-level and empirical investigations covering Charon's extraction boundary and 53-pass transformation schedule, repeat-run LLBC determinism on both minimal probes and the full `zerocopy` library, whole-crate and many-root scaling benchmarks, schema-aware LLBC/Lean golden harnesses, the twelve-gate release upgrade checklist for Anneal, and the bounded 45-cohort source reconciliation between Charon `0.1.210` (`nightly` / `nightly`) and standalone Charon `nightly-2026.09.30` (`0.1.274`, selecting Rust `nightly`):

1. **Extraction Boundary, Per-Body MIR Provenance, and the 53-Pass Normalization Schedule (`9e95cf31` / `1aebab5f`)**: Charon extracts a compiler-selected program in `after_expansion` and `after_analysis` (`charon/src/bin/charon-driver/driver.rs`) with `always-encode-mir`, optimization level zero, `preserve-ub`, and disabled `CheckAlignment`/`CheckNull` MIR passes (`setup_compiler`, `set_mir_options`). Requested MIR level is not a uniform guarantee across all bodies (`get_mir_for_def_id_and_level` in `translate/get_mir.rs`): local early bodies (`mir_built`, `mir_promoted`, `mir_drops_elaborated_and_const_checked`) can have been stolen, falling back to `optimized_mir` or `mir_for_ctfe`, and foreign bodies use `optimized_mir`. The production transformation schedule (`run_transformation_passes` in `charon/src/transform/mod.rs`) comprises 53 non-print pass occurrences (rows 1–8 item prefix, rows 9–36 fused per-body ULLBC phase, rows 37–39 ULLBC-to-LLBC structuring when `!options.ullbc`, and rows 40–53 common final phase). Normalization intentionally abstracts: `move_asserts_to_statements` discards concrete cleanup-block identities in favor of `AbortKind`, `index_intermediate_assigns` and `IndexVisitor::transform_place` introduce fresh shared/mutable references for indexing, and `hide_allocator_param` erases the trailing allocator type parameter on `Box`, `Vec`, `Rc`, and `Arc`. Even `Preset::RawMir` runs all always-scheduled passes rather than returning untouched `rustc` MIR.
2. **Repeat-Run LLBC Determinism on Small Probes and the Full `zerocopy` Library (`0.1.210`)**:
   - On a dependency-free three-function fixture (`checked_add`, `choose`, `bump` in `support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.rs`), repeated Charon `0.1.210` runs at a fixed `--dest-file` produced distinct raw JSON SHA-256 digests (`3b29f4aeaa6abce2bc8fe2e6c7c3ccde063a7555eaf4d7e4488ed1c12d655511` vs. `b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098`) solely due to key ordering in `translated.item_names` (`Fun: 1` and `Fun: 2`), while `charon pretty-print` outputs (1,542 bytes, SHA-256 `0d671705f8d15327fca8355c3e1dfb8cccf7d9f100e21996356e042e46250d27`) and Aeneas-generated `Probe.lean` outputs (1,219 bytes, SHA-256 `767acaeb0288a57cfdabdb1c276cbf0f7d9a85a0558f367601f5082c60349bca`) were byte-identical.
   - Across three serial offline runs on the real `zerocopy --lib` crate (`google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, subtree `574add5aabfa15dd2d16a4646f01f6f944d124d8`), Charon `0.1.210` emitted equal-length 173,520,683-byte LLBC files with distinct raw SHA-256 hashes (`426fa64ab7ee1be150c9d1d063f7a34decfdcf892ecde9b29f5f022d43c83f50`, `60d183425f61fdc64ad082168684ea1c04d58416413255a11b3d988786a1502e`, `aec93122b46a466c4ff560e369d597dd261cd76b442283d4b3e1426c9a5c35a1`). The only differences were the run-specific `options.dest_file` path and the permutation of the 17,903-entry `translated.short_names` array (1,540,054 bytes at offset 4,417,993, first diverging at 0-based index 17,471). Sorting canonical `short_names` entries yielded identical SHA-256 `959066b8e35940df5b72296f77c44a8d3ba4b8fe297b7f2d433e3369f1c947a8` across all runs, and omitting `short_names` while normalizing `/run1/`..`/run3/` to `/runX/` in `dest_file` yielded byte-for-byte identical remaining LLBC (SHA-256 `18be28d9c96069266916733aa4336e9473c9c2f727c9670cc4acbfceb8b76d18`). Furthermore, Aeneas's CLI importer (`src/Main.ml:556-564`) immediately replaces `short_names` with `[]` before translation (`{ m with short_names = [] }`). However, all three `zerocopy` runs exited 0 while serializing `"has_errors": true` and 13 `Deref::Target` extraction warnings, proving that zero exit status alone cannot validate an LLBC artifact for downstream consumption.
3. **Extraction Scaling and Cross-Revision Normalization (`0.1.208` vs. `0.1.210`)**:
   - Sixteen bounded single-worker runs on the 3-function `probe.rs` fixture (`whole`, `one` root, `three` roots, and `whole_no_serialize`) completed in ~0.08–0.09s warm wall time (~100–101.6 MiB child peak RSS).
   - On generated dependency-free crates of 10, 100, and 1,000 independent functions (`support/charon-performance-and-revision-probes/generated-crates/`), whole-crate extraction medians were 0.051s (33,433 bytes), 0.062s (303,310 bytes), and 0.145s (3,044,692 bytes), and explicit `--start-from` root sweeps of 1, 10, 100, and 1,000 roots on the 1,000-function crate completed in 0.390s (cold), 0.075s, 0.082s, and 0.18s with 2, 11, 101, and 1,001 ordered declarations.
   - Comparing Charon `0.1.208` (`6101d742777bf9f9b48979ac1ad4d2c07dfe10db`, release `2026.06.02`) and Charon `0.1.210` (`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, release `2026.06.03`) under identical `rustc` (`nightly`) and `--preset aeneas` on the 3-function fixture produced identical normalized JSON projections (SHA-256 `c6df813c98fbc86c32a89e8895add960d2def6d14bb9d63a3ba96001483b4914`) after replacing `translated.options.dest_file` with `<OUTPUT>` and sorting `item_names`, `short_names`, and `assoc_item_names`.
4. **Twelve-Gate Release Upgrade Checklist and 45-Cohort Source Review (`0.1.210` to `nightly-2026.09.30` / `0.1.274`)**:
   - Upgrading Charon requires validating a 12-gate chain (`support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json`) because package version strings (`0.1.210`) and release dates (`nightly-2026.06.03`) are not unique commit identities: Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` pins `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`rust-toolchain` `nightly`), whereas standalone Charon `nightly-2026.06.03` resolves to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (`rust-toolchain` `nightly`), even though both declare `0.1.210`.
   - Reconciling all 45 frozen `0.1.210` corpus reports against standalone Charon `nightly-2026.09.30` (`2804f2dbc349a4c80201f7c528adf70f8d1ee5fa`, version `0.1.274`, selecting `nightly` with `llvm-tools` instead of `llvm-tools-preview` and adding `aarch64-unknown-linux-gnu`) establishes configuration metadata deltas only; all 45 report claims remain `unresolved_at_target` until claim-specific source paths and runtime fixtures are executed.

---

## Applicability

The findings in this report apply to the following repository revisions, release tags, and binary artifacts recorded in `REPORT.json`:

| Component / Cohort | Repository / Artifact | Revision / Tag / Hash | Toolchain / Version Notes |
| --- | --- | --- | --- |
| **Aeneas-pinned Charon 0.1.210 source** | `AeneasVerif/charon` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | Version `0.1.210`; `charon/rust-toolchain` selects `nightly` (`rustc-dev`, `llvm-tools-preview`, `rust-src`, `miri`). Locked by `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`charon-pin` and `flake.lock`). |
| **Standalone Charon 0.1.210 source & binary (`nightly-2026.06.03`)** | `AeneasVerif/charon` | `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (tag `nightly-2026.06.03`) | Version `0.1.210`; `charon/rust-toolchain` selects `nightly`. Local `charon` binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; `charon-driver` binary SHA-256 `09a530746044c0ef169f7d0cfa099700c06934163a70b138cafc6d125d08037e`; driver launcher script SHA-256 `234ec4cd40eeb42fa1f749f653614cfc251a79bb1f53a903160b921b6cf90b90`. |
| **Standalone Charon 0.1.208 source & binary (`2026.06.02`)** | `AeneasVerif/charon` | `6101d742777bf9f9b48979ac1ad4d2c07dfe10db` | Official macOS `arm64` release binary SHA-256 `094ba2dc1d23f82be5ad2bb378e94ce8c66ca9d13c551edfeb8597b392558272`. |
| **Standalone Charon `nightly-2026.09.30` source** | `AeneasVerif/charon` | `2804f2dbc349a4c80201f7c528adf70f8d1ee5fa` (lightweight tag `nightly-2026.09.30`) | Version `0.1.274`; `charon/rust-toolchain` selects `nightly` (`rustc-dev`, `llvm-tools`, `rust-src`, `miri`, adding `aarch64-unknown-linux-gnu`). Aeneas-paired commit `e435e5f` is a parent, not the tag target. |
| **Charon normalization audit source (`0.1.291`) & dependency comparison** | `AeneasVerif/charon` | `9e95cf318e3a2964fcf5e03104cde5b718f98ea5` and `1aebab5f03a58067e5dc0ede2fec584117f54964` | `9e95cf31` declares version `0.1.291` and requests `nightly`. `1aebab5f` (dependency of Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`) has byte-identical `options.rs`, `transform/mod.rs`, and `docs/minirust.md`. |
| **Aeneas baseline source & binary** | `AeneasVerif/aeneas` | `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`) | Binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03` (`aeneas -version` reports `unknown`). `src/Main.ml` blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`. |
| **Pinned Rust & Cargo toolchain** | `rust-lang/rust` / `rust-lang/cargo` | `rustc` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, `2026-05-30`, LLVM `22.1.6`); `cargo` `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (`2026-05-26`) | Host `aarch64-apple-darwin` (macOS Darwin 25.6.0, 8 GiB RAM). `rustc` binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`; `cargo` binary SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`. |
| **Anneal & `zerocopy` workspace authorities** | `google/zerocopy` | `41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` | `41f5b37a` instantiates the upgrade checklist (`anneal/flake.nix` blob `433fcf5c…`). `bd0956be` supplies the `zerocopy/` subtree (`574add5aabfa15dd2d16a4646f01f6f944d124d8`) and Anneal design docs. Reference corpus commits `e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10`, `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` (581 reports), and `2e9db344b6c0e6391ff78655a18b81ecb7e293e1` (587 reports). |

**Shared vs. Revision-Specific Behavior**:
- **Shared across `0.1.208`, `0.1.210` (`a535e914` and `0c91ca1a`), `0.1.274` (`2804f2db`), and `0.1.291` (`9e95cf31`)**: The `CrateData` top-level JSON envelope (`charon_version`, `translated`, `has_errors`), exact `CARGO_PKG_VERSION` equality check on deserialization, queue-and-processed-set reachability traversal (`translate_crate.rs`), `RUSTC_WRAPPER`-based Cargo integration, and the separation between `charon_lib` and the `rustc-private`-linked `charon-driver`.
- **Revision-Specific**:
  - Both `a535e914` and `0c91ca1a` declare `charon` version `0.1.210`, but `a535e914/charon/rust-toolchain` selects `nightly` whereas `0c91ca1a/charon/rust-toolchain` selects `nightly`.
  - Standalone `2804f2db` (`nightly-2026.09.30`) bumps package version to `0.1.274`, selects `nightly`, renames toolchain component `llvm-tools-preview` to `llvm-tools`, and adds `aarch64-unknown-linux-gnu`.
  - At `9e95cf31` (`0.1.291`), LLBC call and drop terminators retain unwind targets in the AST (`drop_glue` replaces older `drop_in_place` terminology), though `move_asserts_to_statements` still folds built-in dynamic checks into statements whose original cleanup-block identity is replaced by `AbortKind` and later given a generic unwind-resume block during LLBC reconstruction.

---

## Findings

### 1. Extraction Boundary, Per-Body MIR Provenance, and Artifact Identity (`9e95cf31` / `1aebab5f`)

#### 1.1 Compiler Driver Boundary and Query Ordering

Basis: **source** ([`driver.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/driver.rs), [`charon/main.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon/main.rs)).

In `driver.rs`, `run_rustc_driver` distinguishes Cargo primary packages from dependencies via `CHARON_USING_CARGO` and `CARGO_PRIMARY_PACKAGE`. Translation additionally requires an explicit `--target` argument so that host build-script and proc-macro crates execute through normal compiler callbacks. In `charon/src/bin/charon/main.rs`, `translate_with_cargo` arranges an explicit target, supplies `CHARON_ARGS`, and uses wrappers to prevent ordinary Cargo cache reuse for selected extraction. These are operational selections rather than a proof of complete Cargo dependency closure.

`setup_compiler` and `set_mir_options` configure `always-encode-mir`, optimization level zero, and `preserve-ub`, and disable the MIR `CheckAlignment` and `CheckNull` passes. These settings apply even inside the "normal compiler" callbacks used for dependencies, meaning dependency compilation under `charon cargo` does not run with default `rustc` MIR flags. While these settings retain MIR and suppress specific inserted checks, they do not undo earlier lowering or guarantee that all source-level undefined behavior survives into MIR.

Selected translation runs in `after_expansion`:
1. The driver first invokes attribute, well-formedness, coherence, and typechecking queries chosen to avoid stealing early MIR.
2. It then continues compiler analysis; `after_analysis` additionally requests instance MIR and mono-item collection when ordinary artifacts are not emitted, in order to surface late compiler errors.
3. `--skip-borrowck` can override `mir_borrowck` with an empty success result. Because the extraction callback precedes completion of all ordinary MIR checks, an extracted body is not by itself evidence that borrow checking succeeded. Consumers must check final success, `has_errors`, and whether borrow checking was bypassed.
4. Sysroot selection supports explicit, default, or custom-built Miri sysroots (which disable codegen). Foreign MIR availability depends on the exact sysroot and compiled dependencies.

#### 1.2 Item-Specific MIR Query Selection

Basis: **source** ([`get_mir.rs`, `get_mir_for_def_id_and_level`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/translate/get_mir.rs), [`TranslateOptions::new`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/options.rs), [`translate_bodies.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/bin/charon-driver/translate/translate_bodies.rs)).

Requested MIR level (`Built`, `Promoted`, `Elaborated`, `Optimized`) is not a uniform invariant across all extracted bodies. `Preset::Aeneas` keeps the default request of `Promoted` MIR, whereas enabling precise drops raises the requested level to at least `Elaborated` MIR. `get_mir_for_def_id_and_level` selects each item's body according to the following exact branch order:

| Item / Query Case | Body Supplied |
| --- | --- |
| Local item, `Built` requested, and early body available | Clone of `tcx.mir_built` |
| Local item, `Promoted` requested, and early body available | Main body of `tcx.mir_promoted` |
| Local item, `Elaborated` requested, and early body available | `mir_drops_elaborated_and_const_checked` |
| Local early body already stolen, or `Optimized` requested | Falls through into the general availability path below |
| MIR available, and item is neither a global `const` nor `static` | `optimized_mir` |
| Nontrivial global `const`, local `static`, or `const fn` falling through the preceding branch | `mir_for_ctfe` |
| Promoted constant definition | `rustc_const_uneval::promoted_body` |
| Allocation definition or no available body | No MIR body (`Opaque`) |

Because a `const fn` with ordinary MIR available matches the `optimized_mir` branch before `mir_for_ctfe`, not all `const fn` items use CTFE MIR. Early MIR (`Built`, `Promoted`, `Elaborated`) is local-only; foreign bodies always take the general query path (`optimized_mir` or `mir_for_ctfe`). Under full monomorphization, `get_mir_inner` invokes `hax` substitution with the item's concrete generic arguments and typing environment. `get_mir` wraps body retrieval in panic recovery that converts compiler panics into registered translation errors (`has_errors: true`), and `translate_bodies.rs` determines conditional versus precise drops from the actual body phase returned rather than merely the requested CLI level.

#### 1.3 Incompleteness of Embedded Artifact Provenance

Basis: **source** ([`export.rs`, `CrateData`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/export.rs), [`ast/krate.rs`, `TranslatedCrate`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/krate.rs), [`ast/meta/spans.rs`, `File`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/meta/spans.rs)) plus **derived** consequences.

`CrateData` serializes `charon_version`, `translated` (`TranslatedCrate`), and `has_errors`. `TranslatedCrate` records CLI options, target layout information, runtime UB/overflow/contract-check flags, source-file records (with local/virtual/not-real filenames, optional source text, and macro/inlining provenance spans), declarations, and item names. However, `CrateData` is not an authenticated build manifest: it does not bind compiler/driver/sysroot executable hashes, dependency `.rlib`/`.rmeta` digests, `Cargo.lock` resolution, active `cfg`/feature flags, build-script outputs, environment variables, proc-macro inputs, the effective `rustc` argument vector, or which branch of `get_mir_for_def_id_and_level` produced each body.

---

### 2. Full 53-Pass Transformation Schedule and Semantic Preservation Obligations (`9e95cf31`)

#### 2.1 Execution Model and Pass Schedule

Basis: **source** ([`transform/mod.rs`, `run_transformation_passes`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/mod.rs) and `support/charon-extraction-normalization-9e95cf3/pass-inventory.json`) for scheduling and predicates; **derived** for semantic obligations.

`TransformCtx::run_pass` is not a naive sequence of 53 independent whole-crate AST sweeps:
- Rows `1..=8` execute as crate-level prefix passes (`Row 4` is the `PostTranslation` typecheck).
- Rows `9..=36` form the fused per-body ULLBC phase; when an owned ULLBC pass carries newly synthesized bodies, `TransformCtx::run_pass` preprocesses those carried bodies through the preceding passes, runs the enabled body sequence per item, and then invokes enabled finalizers.
- Rows `37..=39` execute only when `!options.ullbc` (`ullbc_to_llbc`, `prettify_cfg`, `builtins_to_function_calls`).
- Rows `40..=53` form the common final phase (`Row 52` is the `PostTransformation` typecheck).

| # | Scheduled Pass | Preservation Obligation (Required Consumer Assumption, Not an Established Theorem) |
| --- | --- | --- |
| 1 | `add_missing_info::link_specs` | Contract links preserve item/associated-item identity; no executable change. |
| 2 | `simplify_output::duplicate_defaulted_methods` | Copied default bodies substitute the same trait/impl arguments and dispatch (`disabled` by default under `Preset::Aeneas` alone). |
| 3 | `add_missing_info::compute_short_names` | Names remain unambiguous display aliases; IDs and execution unchanged. |
| 4 | `typecheck_and_unify::Check` (`PostTranslation`) | Type consistency and best-effort region unification; skips items already marked erroneous and permits certain default-method associated-type mismatches. |
| 5 | `finish_translation::filter_invisible_trait_impls` | Remove only implementations already classified invisible; preserve relevant dispatch. |
| 6 | `simplify_output::lift_associated_item_clauses` | Reindex proof arguments and bound regions consistently when moving clauses. |
| 7 | `add_missing_info::add_missing_alias_clauses` | Added trait premises match unresolved associated-type requirements without changing instantiations. |
| 8 | `add_missing_info::add_implied_outlives` | Make only signature-implied outlives predicates explicit with correct binders. |
| 9 | `add_missing_info::detect_drop_flags` | Detected Boolean tracks precisely initializedness on the relevant paths (`disabled` by default under `Preset::Aeneas` alone). |
| 10 | `resugar::resugar_drops` | Recover conditional drops without losing partial-move/cleanup effects or misidentifying flags (`disabled` by default under `Preset::Aeneas` alone). |
| 11 | `finish_translation::insert_ptr_metadata` | Inserted metadata expressions match original pointer metadata without new memory accesses. |
| 12 | `finish_translation::insert_assign_return_unit` | Unit return initialization changes no observable evaluation or validity behavior. |
| 13 | `finish_translation::insert_storage_statements` | Explicit allocation/deallocation reproduces implicit local lifetime; globals excluded from dead insertion. |
| 14 | `normalize::desugar_drops` | Precise `drop_glue` call with fresh mutable reference preserves validity, moved-out state, cleanup, and evaluation order (`disabled` by default under `Preset::Aeneas` alone). |
| 15 | `normalize::skip_trait_refs_when_known` | Direct callee has identical implementation selection and generic substitution. |
| 16 | `normalize::transform_dyn_trait_calls` | Vtable load/call preserves metadata, method ABI, argument ordering, and unwind edge. |
| 17 | `simplify_output::anon_const_to_call` | Initializer invocation preserves constant identity, sharing, evaluation, and effects (`disabled` by default under `Preset::Aeneas` alone). |
| 18 | `simplify_output::inline_selected_functions` | Inlining preserves argument moves, local scope, returns, unwind paths, and constant semantics (depends on discovered inline candidates). |
| 19 | `resugar::reconstruct_panic_calls` | Recognized panic callee has the same failure and unwind behavior. |
| 20 | `simplify_output::filter_trivial_drops` | `NoopDestruct` classification justifies removing all effects and unwind behavior. |
| 21 | `resugar::move_asserts_to_statements` | Implicit failure semantics must justify discarding the concrete cleanup-edge identity in favor of `AbortKind`. |
| 22 | `control_flow::merge_goto_chains` | Redirected/concatenated paths preserve statements and all edge destinations, including cyclic paths. |
| 23 | `resugar::reconstruct_fallible_operations` | Matched checks correspond exactly to implicit panic checks, arithmetic overflow mode, and operand evaluation. |
| 24 | `resugar::reconstruct_vec_boxes` | `Box`/`Vec` construction rewrite (`Box<MaybeUninit<[T; N]>>` to `Box::write`/`Box::new`) preserves initialization, allocation failure, moves, and cleanup (disabled under full `hax` monomorphization). |
| 25 | `resugar::reconstruct_box_derefs` | Hidden-pointer projection denotes the same `Box` pointee and validity requirements. |
| 26 | `resugar::reconstruct_intrinsics` | Recognized `offset_of` constant equals compiler layout-derived offset. |
| 27 | `resugar::reconstruct_asserts` | Branch-to-assert resugaring preserves condition, expected value, and error/unwind effects. |
| 28 | `resugar::reconstruct_static_accesses` | All rewritten temporary dereferences denote the same `static`; no other temporary uses are lost. |
| 29 | `simplify_output::simplify_constants` | Fresh temporaries/promoted globals preserve sharing, relocation, metadata, and evaluation order. |
| 30 | `simplify_output::index_intermediate_assigns` | RHS is evaluated before LHS reference construction with identical moves and failure behavior. |
| 31 | `simplify_output::remove_unit_locals` | Erased direct unit uses/stores do not erase side effects or validity errors. |
| 32 | `control_flow::duplicate_return` | Clones keep branch/cleanup destinations and cycles; dynamic execution still visits only one clone. |
| 33 | `resugar::reconstruct_matches` | Discriminant cases and fallthrough remain equivalent including invalid discriminants. |
| 34 | `simplify_output::remove_unused_locals` | Only unobserved local storage is removed; all remaining IDs/types/references remap consistently. |
| 35 | `control_flow::merge_goto_chains` | Redirected/concatenated paths preserve statements and all edge destinations, including cyclic paths. |
| 36 | `simplify_output::update_block_indices` | Reachability and bijective renaming preserve all reachable edges; unreachable blocks may disappear. |
| 37 | `control_flow::ullbc_to_llbc` | Structured positions simulate CFG positions including divergence and unwinding (`!options.ullbc` only). |
| 38 | `control_flow::prettify_cfg` | Structural simplification preserves nested block, loop, and jump targets (`!options.ullbc` only). |
| 39 | `simplify_output::builtins_to_function_calls` | Library models agree on validity, panic, retagging, allocation, aliases, and evaluation order (`!options.ullbc` only). |
| 40 | `finish_translation::insert_storage_statements` | Explicit allocation/deallocation reproduces implicit local lifetime; globals excluded from dead insertion. |
| 41 | `normalize::normalize_trait_refs` | Normalized proof references select equivalent implementations. |
| 42 | `normalize::expand_associated_types` | Lifted generics/associated types and substitutions agree for every caller. |
| 43 | `simplify_output::remove_unused_clauses` | Removed evidence is unused, including indirect proof dependencies. |
| 44 | `simplify_output::remove_adt_clauses` | Removed ADT evidence does not lose associated-type information or relevant trait obligations. |
| 45 | `simplify_output::remove_unused_locals` | Only unobserved local storage is removed; all remaining IDs/types/references remap consistently. |
| 46 | `simplify_output::remove_nops` | Only inert statements are removed; comments retained when present. |
| 47 | `add_missing_info::recover_body_comments` | Only source presentation changes. |
| 48 | `simplify_output::hide_allocator_param` | Consumer restriction/model must justify losing trailing allocator type parameter on `Box`, `Vec`, `Rc`, and `Arc`. |
| 49 | `normalize::partial_monomorphization` | Specialized copies and shape arguments denote the original instantiation with matching binders (returns immediately unless a monomorphize-mut option is selected). |
| 50 | `add_missing_info::compute_layout_guarantees` | Derived layout facts are valid for represented target/`repr` and do not overclaim actual layout. |
| 51 | `add_missing_info::reorder_decls` | Dependency SCC/order changes do not alter item identity or runtime order. |
| 52 | `typecheck_and_unify::Check` (`PostTransformation`) | Post-transformation type consistency check; not a proof of semantic preservation. |
| 53 | `simplify_output::unbind_item_vars` | Free-variable renaming preserves the correct binding level under nested binders. |

#### 2.2 Critical Semantic Abstractions in `Preset::Aeneas`

Basis: **source** ([`reconstruct_fallible_operations.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/resugar/reconstruct_fallible_operations.rs), [`move_asserts_to_statements.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/resugar/move_asserts_to_statements.rs), [`index_intermediate_assigns.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/simplify_output/index_intermediate_assigns.rs), [`builtins_to_function_calls.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/simplify_output/builtins_to_function_calls.rs)) plus **derived** obligations.

- **Dynamic-Check Folding Discards Concrete Cleanup Block Targets**: `move_asserts_to_statements` converts a built-in check `Assert` terminator into a statement plus a normal `Goto`, mapping the old unwind target to an `AbortKind` (`Abort` if the target is a recognized abort block, otherwise generic panic). The concrete cleanup-block identity is lost from that statement and later reconstructed as a generic unwind-resume block. Thus, the presence of unwind fields in current LLBC does not mean all dynamic-check cleanup paths survived normalization intact.
- **Reference Insertion During Indexing and Drop Desugaring**: `index_intermediate_assigns` splits assignments whose RHS and LHS both contain index projections so the RHS finishes evaluating before the mutable LHS borrow is created. `IndexVisitor::transform_place` (`builtins_to_function_calls.rs`) then introduces a fresh shared or mutable reference to the array/slice base and calls the library indexing method (`Index::index` or `IndexMut::index_mut`). As Charon's own CLI help notes, creating references where raw MIR performed in-place projection requires justifying full-referent validity and Stacked/Tree Borrows aliasing permissions at the insertion point.
- **Pre-Normalization Inspection Seam vs. `Preset::RawMir`**: `print_original_ullbc` runs before pass 1 (`link_specs`), offering a post-translation, pre-normalization inspection seam (though it is a diagnostic print rather than a structured certificate and already excludes MIR-only statements stripped during initial translation). By contrast, `Preset::RawMir` sets opaque-body extraction, raw constants, and `--ullbc`, but still executes all unconditionally scheduled passes in `run_transformation_passes`.

---

### 3. Repeat-Run LLBC Determinism on Small Probes and the `zerocopy` Library (`0.1.210`)

#### 3.1 Three-Function Probe (`probe.rs`): Raw JSON Map Permutation vs. Byte-Identical Pretty LLBC and Lean

Basis: **execution** (`support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/`).

Using Charon `0.1.210` (`51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`), `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, and Aeneas `nightly-2026.06.03` (`f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`) on `aarch64-apple-darwin`, the 264-byte dependency-free library fixture (`support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.rs` containing `checked_add`, `choose`, and `bump`) was extracted via `charon rustc --preset aeneas`, pretty-printed via `charon pretty-print`, and translated via `aeneas -backend lean`:

| Artifact / Comparison | Baseline Run Digest / Size | Repeat Run Digest / Size | Observed Determinism |
| --- | --- | --- | --- |
| Raw LLBC JSON (`probe-baseline.llbc` vs. `probe-repeat.llbc`, fixed `--dest-file`) | `3b29f4aeaa6abce2bc8fe2e6c7c3ccde063a7555eaf4d7e4488ed1c12d655511` | `b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098` | Differed **only** in the relative order of two `translated.item_names` entries (`Fun: 1` and `Fun: 2`). Sorting keyed name-map arrays made the JSON values equal. |
| Pretty-printed LLBC (`pretty-baseline.txt` vs. `pretty-repeat.txt`) | `0d671705f8d15327fca8355c3e1dfb8cccf7d9f100e21996356e042e46250d27` (1,542 bytes) | `0d671705f8d15327fca8355c3e1dfb8cccf7d9f100e21996356e042e46250d27` (1,542 bytes) | **Byte-identical**. |
| Generated Lean (`lean-baseline.lean` / `lean/Probe.lean`) | `767acaeb0288a57cfdabdb1c276cbf0f7d9a85a0558f367601f5082c60349bca` (1,219 bytes) | `767acaeb0288a57cfdabdb1c276cbf0f7d9a85a0558f367601f5082c60349bca` (1,219 bytes) | **Byte-identical** (`bump (value : Std.U32) : Result Std.U32`, `choose` lowered to Lean `if`, `checked_add` calling opaque `core::num::{u32}::checked_add`). |

#### 3.2 Full `zerocopy --lib` Repeat-Run Extraction: 173.5 MB LLBC Field-Aware Equivalence and Error-Bearing Exit Zero

Basis: **execution** and field-aware comparison (`support/charon-zerocopy-library-repeat-order/observations.json`, `support/charon-zerocopy-library-repeat-order/comparison.json`, `support/charon-zerocopy-library-repeat-order/first-order-differences.json`, `support/charon-zerocopy-library-repeat-order/replay-comparison.json`) plus **source** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `src/Main.ml:556-564`).

Three serial, offline Charon `0.1.210` runs (`--preset aeneas` with Cargo `--package zerocopy --lib --offline --locked`, isolated target directories, `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`) were executed on `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (`zerocopy/` subtree `574add5aabfa15dd2d16a4646f01f6f944d124d8`):

| Run | LLBC Size (bytes) | Raw SHA-256 | Canonical Sorted `short_names` SHA-256 | Remaining Bytes SHA-256 (`dest_file` normalized, `short_names` omitted) | Peak Process-Group RSS | Min System Free RAM |
| --- | ---: | --- | --- | --- | ---: | ---: |
| 1 | 173,520,683 | `426fa64ab7ee1be150c9d1d063f7a34decfdcf892ecde9b29f5f022d43c83f50` | `959066b8e35940df5b72296f77c44a8d3ba4b8fe297b7f2d433e3369f1c947a8` | `18be28d9c96069266916733aa4336e9473c9c2f727c9670cc4acbfceb8b76d18` | 985,408 KiB | 40% |
| 2 | 173,520,683 | `60d183425f61fdc64ad082168684ea1c04d58416413255a11b3d988786a1502e` | `959066b8e35940df5b72296f77c44a8d3ba4b8fe297b7f2d433e3369f1c947a8` | `18be28d9c96069266916733aa4336e9473c9c2f727c9670cc4acbfceb8b76d18` | 964,688 KiB | 42% |
| 3 | 173,520,683 | `aec93122b46a466c4ff560e369d597dd261cd76b442283d4b3e1426c9a5c35a1` | `959066b8e35940df5b72296f77c44a8d3ba4b8fe297b7f2d433e3369f1c947a8` | `18be28d9c96069266916733aa4336e9473c9c2f727c9670cc4acbfceb8b76d18` | 976,816 KiB | 45% |

1. **Exact Location of Nondeterminism**: Aside from the `/run1/`, `/run2/`, `/run3/` directory component in `options.dest_file`, the sole difference across all 173,520,683 bytes is the entry order of `translated.short_names` (beginning at byte offset `4,417,993`, length `1,540,054` bytes, containing `17,903` unique keys, first diverging at 0-based entry index `17,471`). All declarations, bodies, expressions, types, source spans, and `has_errors` bytes outside `short_names` and `dest_file` match byte-for-byte (`18be28d9…`). A guarded 3-run replay (`support/charon-zerocopy-library-repeat-order/replay.py`, producing 173,520,692-byte files due to a 9-byte longer scratch path) reproduced the identical `17,903`-entry multiset (`959066b8…`) and within-replay byte equality (`support/charon-zerocopy-library-repeat-order/replay-comparison.json`).
2. **Aeneas CLI Importer Discards `short_names`**: In `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`, lines 556–564) imports the JSON crate via `crate_of_json_file` and immediately resets `{ m with short_names = [] }` prior to logging, pre-passes, and `Translate.translate_crate` (lines 735–739) with the comment that doing so makes printing more deterministic. Thus `short_names` permutations cannot affect downstream translation through that Aeneas CLI importer.
3. **Fail-Closed Hazard (`has_errors: true` with Exit Code `0`)**: Every `zerocopy --lib` run exited with status `0` after printing `The extraction generated 13 warnings` (`Could not compute the value of ... Target ... needed to update item reference ... Deref`, preserved in `support/charon-zerocopy-library-repeat-order/run1-stderr.txt`, `support/charon-zerocopy-library-repeat-order/run2-stderr.txt`, and `support/charon-zerocopy-library-repeat-order/run3-stderr.txt`) and wrote `"has_errors": true` at the end of the LLBC file. Because `charon-driver` (`charon/src/bin/charon-driver/main.rs`) serializes `CrateData` before checking `error_on_warnings`, Anneal orchestration must inspect `has_errors` (and pass `--error-on-warnings` where supported) rather than trusting process exit code `0` or output file existence.

---

### 4. Extraction Performance, Scaling Probes, and Cross-Revision Golden Normalization (`0.1.208` vs. `0.1.210`)

#### 4.1 Baseline Mode Comparison on `probe.rs` (16 Runs)

Basis: **execution** (`support/charon-extraction-scaling/charon-scaling/measure.py`, `support/charon-extraction-scaling/charon-scaling/runs.jsonl`, and `support/charon-extraction-scaling/SUPPORT.md`).

Sixteen interleaved single-process invocations of `charon rustc --preset aeneas` on the 3-function `probe.rs` fixture (`CHARON_TOOLCHAIN_IS_IN_PATH=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 CARGO_INCREMENTAL=0`) measured four modes (`support/charon-extraction-scaling/charon-scaling/whole.json`, `support/charon-extraction-scaling/charon-scaling/one.json`, `support/charon-extraction-scaling/charon-scaling/three.json`, `support/charon-extraction-scaling/charon-scaling/whole_no_serialize.json` and `.llbc`/`.stderr`/`.stdout` counterparts):

| Mode | Additional Charon Flags | Emitted `ordered_decls` | LLBC Bytes | Wall Time Across 4 Runs (s) | Child Peak RSS Range (MiB) |
| --- | --- | ---: | ---: | --- | ---: |
| Whole crate (`whole`) | none | 6 | 19,822 | 0.269 (cold), 0.150, 0.086, 0.090 | 101.2–101.5 |
| One root (`one`) | `--start-from crate::choose` | 1 | 5,739 | 0.089, 0.088, 0.088, 0.081 | 99.8–99.8 |
| Three roots (`three`) | `--start-from` for `choose`, `bump`, `checked_add` | 6 | 19,874 | 0.090, 0.082, 0.090, 0.090 | 101.3–101.5 |
| Whole, no file (`whole_no_serialize`) | `--no-serialize` | not emitted | 0 | 0.083, 0.090, 0.090, 0.084 | 101.3–101.6 |

#### 4.2 Generated Whole-Crate (10 / 100 / 1,000 Functions) and Many-Root Sweep (1 / 10 / 100 / 1,000 Roots)

Basis: **execution** (`support/charon-performance-and-revision-probes/generated-crate-summary.json`, `support/charon-performance-and-revision-probes/prior-generated-sweep.md`, `support/charon-performance-and-revision-probes/root-matrix-summary.json`, `support/charon-performance-and-revision-probes/root-matrix.json`, and `support/charon-performance-and-revision-probes/many-roots/root_matrix.py`).

1. **Whole-Crate Scaling on Generated Independent Functions**: Running Charon `0.1.210` on generated dependency-free Rust crates with 10, 100, and 1,000 independent small functions (`support/charon-performance-and-revision-probes/generated-crates/functions_10.rs`, `support/charon-performance-and-revision-probes/generated-crates/functions_100.rs`, `support/charon-performance-and-revision-probes/generated-crates/functions_1000.rs` -> `support/charon-performance-and-revision-probes/generated-crates/whole-10.llbc`, `support/charon-performance-and-revision-probes/generated-crates/whole-100.llbc`, `support/charon-performance-and-revision-probes/generated-crates/whole-1000.llbc`) succeeded with `has_errors: false`:
   - **10 functions**: 3-run median `0.051s`, `33,433` LLBC bytes.
   - **100 functions**: 3-run median `0.062s`, `303,310` LLBC bytes.
   - **1,000 functions** (51,915-byte source, SHA-256 `a7242d3ed0681bcaae7121eb11665febcbdfd0b7ae2be325c4d7c7b2d86f64b1`): 3-run median `0.145s`, `3,044,692` LLBC bytes.
2. **Many-Root Selection Matrix on the 1,000-Function Crate**: Invoking Charon `0.1.210` on `functions_1000.rs` with `1`, `10`, `100`, and `1,000` explicit `--start-from` flags (`support/charon-performance-and-revision-probes/many-roots/roots-1.llbc`, `support/charon-performance-and-revision-probes/many-roots/roots-10.llbc`, `support/charon-performance-and-revision-probes/many-roots/roots-100.llbc`, `support/charon-performance-and-revision-probes/many-roots/roots-1000.llbc`) exited `0` with `has_errors: false`:

| Explicit `--start-from` Roots | Emitted Local Functions | Emitted `ordered_decls` | LLBC Output Size (bytes) | Captured Wall Time (s) |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 2 | 59,592 | 0.390 (cold first run) |
| 10 | 10 | 11 | 86,112 | 0.075 |
| 100 | 100 | 101 | 353,715 | 0.082 |
| 1,000 | 1,000 | 1,001 | ~3,060,000 | 0.180 |

3. **Source-Level Scaling Factors and Multi-Target Caveats**:
   - In `charon/src/bin/charon-driver/translate/translate_crate.rs` (`enqueue_module_item`, `translate`, and the work-queue/processed-set loop), `--start-from crate` traverses all local items, while `--start-from-pub` and `--start-from-attribute` iterate crate HIR definitions to find roots (growing setup cost with total crate HIR size even when few roots match).
   - Foreign items default to `Foreign` (signatures and all-public struct fields/enum variants translated, bodies omitted) unless `--include` or `--extract-opaque-bodies` expands reachability.
   - Charon's multi-target `--targets` flag spawns one thread per target and merges crates afterward (documented in CLI help as extremely slow), whereas a single `charon cargo` invocation with multiple primary Cargo units shares one output destination policy and can overwrite a single `--dest-file` unless targets are invoked and routed individually (as in Anneal's `src/resolve.rs` and `src/scanner.rs`).

#### 4.3 Cross-Revision Normalization (`0.1.208` vs. `0.1.210`) and Schema-Aware Golden Design

Basis: **execution** and **derived** normalization (`support/charon-performance-and-revision-probes/normalize.py`, `support/charon-performance-and-revision-probes/revision-comparison-raw.json`, `support/charon-performance-and-revision-probes/revision-diff/compare.py`, `support/charon-performance-and-revision-probes/revision-diff/comparison.json`, `support/charon-performance-and-revision-probes/revision-diff/normalized-1.json`, `support/charon-performance-and-revision-probes/revision-diff/normalized-2.json`).

- Running the 3-function fixture under Charon `0.1.208` (`6101d742777bf9f9b48979ac1ad4d2c07dfe10db`, binary `094ba2dc…`) and Charon `0.1.210` (`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, binary `51bb6d23…`) with identical `rustc` (`nightly`) and `--preset aeneas` yielded identical normalized JSON projections: both normalized to SHA-256 `c6df813c98fbc86c32a89e8895add960d2def6d14bb9d63a3ba96001483b4914`.
- The normalization (`normalize.py` / `revision-diff/compare.py`) is strictly bounded: it replaces `translated.options.dest_file` with `"<OUTPUT>"` and sorts the associative key/value arrays `item_names`, `short_names`, and `assoc_item_names` by key. It never reorders statement sequences, declaration lists (`ordered_decls`), branch arms, or array elements, and never erases source spans, target metadata, or `has_errors`.
- A production golden and revision-diff harness for Anneal should key fixtures by fixture name + target/configuration (not path-derived checkout slugs), commit the Rust source, pretty LLBC, canonical structured LLBC projection, and generated Lean, test `2x2` producer/consumer compatibility matrices (old/new Charon x old/new Aeneas) when LLBC versions permit, and separately verify Lean typechecking (`lake env lean`) rather than treating string stability as soundness.

---

### 5. Twelve-Gate Charon Release Upgrade Checklist and 45-Cohort Source Review (`0.1.210` to `nightly-2026.09.30`)

#### 5.1 Twelve-Gate Release Upgrade Checklist for Anneal

Basis: **source** (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`) plus **derived** acceptance gates (`support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json`, `support/charon-release-upgrade-checklist-0-1-210/source-map.json`).

At the Anneal baseline (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` blob `433fcf5c…`), Anneal selects Aeneas `nightly-2026.06.03` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), whose `charon-pin` (`06dbe0db…`) and `flake.lock` (`d6862b6e…`) lock `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, `rust-toolchain` `4e348eda…` selecting `nightly`), and whose `flake.nix` (`05e71549…`) copies `charon`, `charon-driver`, and `rust-toolchain` from `charon-portable` into the Aeneas release tree. Any candidate upgrade must satisfy twelve gates (`support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json`):

| Gate | Requirement | Source vs. Empirical Boundary |
| --- | --- | --- |
| **1. Producer Identity Chain** | Resolve `Anneal rev -> Aeneas rev -> charon-pin + flake.lock -> Charon commit -> CARGO_PKG_VERSION -> rust-toolchain`. Stop if `charon-pin` and lock disagree or if same-version (`0.1.210`) / same-date (`nightly-2026.06.03`) labels are conflated. | Source + artifact hash manifest |
| **2. Coupled `rustc-private` Unit** | Re-resolve `charon/rust-toolchain` (`Cargo.toml` blob `8c993620…`), compare components with Anneal's packaged Rust sysroot, and verify runtime loading under `CHARON_TOOLCHAIN_IS_IN_PATH` (`rustc -vV`). | Source + packaged execution |
| **3. Effective Configuration & Preset Snapshot** | Diff `CliOpts`, `Preset::Aeneas` (`options.rs` blob `f08f8bae…`), `run_transformation_passes`, `should_run` predicates, and invocation mode (`charon cargo` vs. `charon rustc`). | Source diff |
| **4. LLBC Wire vs. `charon_lib` API Surface** | Diff `CrateData` (`export.rs` blob `d5428958…`), `charon_lib::VERSION` (`lib.rs` blob `a5530a17…`), AST schema, and generated OCaml readers. Treat `charon_lib` Rust API compilation separately from LLBC file consumption. | Source diff + consumer decode |
| **5. Transformation Pipeline Semantics** | Diff pass ordering and guards (`transform/mod.rs` blob `8d9ec016…`); regenerate compact LLBC fixtures covering changed passes and review structural diffs against semantic obligations. | Source diff + fixture execution |
| **6. Fail-Closed Error & Warning Boundary** | Verify error registration, placeholder nodes, `has_errors`, and serialization order (`charon-driver/main.rs` blob `ab74f3f3…` serializes before `error_on_warnings`). Test 5 discriminator cases: success, warning/partial result, unsupported construct, compiler failure, and panic/ICE. | Source + 5-case execution matrix |
| **7. Translation Coverage & Source Spans** | Recheck `--start-from`, `--include`/`--opaque`/`--exclude`, foreign MIR availability, and semantic `ItemId` vs. `Span`/`File` mapping structures. | Source + fixture verification |
| **8. Multi-Target & Multi-Primary-Unit Routing** | Distinguish `--targets` thread fan-out/merge from `charon cargo` multi-primary-unit destination collisions. Enforce per-target output routing or single-primary-unit invariants. | Source + Cargo unit graph check |
| **9. Paired Aeneas Consumer Validation** | Decode representative LLBC with the exact Aeneas revision (`src/Main.ml` blob `b3f373f8…`) selected by the dependency graph rather than assuming same-version compatibility. | Execution |
| **10. Same-Revision Determinism vs. Upgrade Drift** | Separately test repeat-run determinism at the candidate revision and cross-revision structural diffs between baseline and candidate. | Execution |
| **11. Packaged Multi-Host Runtime Viability** | Exercise relocated `charon` and `charon-driver` binaries against the managed Rust sysroot on every claimed host (`x86_64`/`aarch64` Linux and macOS), not just `--version`. | Packaged execution |
| **12. Integrated End-to-End Acceptance Corpus** | Run scalar/ADT control flow, shared/mutable borrows, supported raw-pointer/unsafe operations, loops/recursion, traits/associated types, foreign calls, and an expected-failure discriminator through packaged `rustc -> Charon -> Aeneas`. | Integrated execution |

#### 5.2 Bounded Source Review of 45 Frozen `0.1.210` Reports Against `nightly-2026.09.30` (`2804f2db` / `0.1.274`)

Basis: **source** (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, `AeneasVerif/charon@2804f2dbc349a4c80201f7c528adf70f8d1ee5fa`) and **derived** reconciliation (`support/charon-0-1-210-to-source-review/matrix.json`, `support/charon-0-1-210-to-source-review/frozen-cohort.csv`, `support/charon-0-1-210-to-source-review/version-inventory-ebcdcad-581.csv`, `support/charon-0-1-210-to-source-review/baseline-report-paths.txt`, `support/charon-0-1-210-to-source-review/check_matrix.py`).

1. **Cohort Reconciliation (45 Reports)**: From the 581-row inventory at reference commit `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` (and 587-package corpus at `2e9db344b6c0e6391ff78655a18b81ecb7e293e1`), `matrix.json` reconciles all **45** frozen Charon `0.1.210` report packages:
   - `17` classified as `Charon 0.1.210 + Rust nightly` and `28` classified as `Charon 0.1.210 + Rust/Cargo nightly`.
   - Direct subject metadata names `a535e914f74db4fd9e6be7048f4233270d8945c0` in 17 reports and `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` in 3 entries (1 report naming both, for 19 direct Charon repo subjects total), 2 reports directly naming `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, and 1 directly naming `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`. Six post-baseline packages added between `ebcdcadb` and `2e9db344` are tracked separately in `matrix.json` without altering the 45-row cohort.
2. **Target Release Configuration Delta (`2804f2dbc349a4c80201f7c528adf70f8d1ee5fa`)**:
   - Read-only `git ls-remote https://github.com/AeneasVerif/charon.git refs/tags/nightly-2026.09.30 'refs/tags/nightly-2026.09.30^{}'` returned lightweight tag commit `2804f2dbc349a4c80201f7c528adf70f8d1ee5fa` directly (with Aeneas-paired commit `e435e5f` as a parent, not the tag target).
   - `charon/Cargo.toml` at `2804f2db` declares version `0.1.274` (up from `0.1.210` at both `a535e914` and `0c91ca1a`).
   - `charon/rust-toolchain` at `2804f2db` selects `nightly` (versus `nightly` at `a535e914` and `nightly` at `0c91ca1a`), lists components `rustc-dev`, `llvm-tools`, `rust-src`, and `miri` (replacing `llvm-tools-preview` with `llvm-tools`), and adds target `aarch64-unknown-linux-gnu`.
3. **Unresolved Claim Status Across All 45 Rows**: Because a package version bump (`0.1.210 -> 0.1.274`), toolchain channel change (`nightly / 06-01 -> nightly`), and release notes (mentioning multiple concurrent Charon versions and remembering starting items) do not trace the determining implementation paths of individual report claims, every row in `matrix.json` records `source_claim_result="unresolved_at_target"`, `current_runtime_result="unexecuted_in_this_review"`, `compatibility_result="unresolved"`, and `anneal_product_result="unassessed"`, with `rustc_source_commit` and `cargo_source_commit` left `null` until the September 17 toolchain components are resolved and executed.

---

## Boundaries

- **Not examined**:
  - Runtime execution of Charon `0.1.274` (`2804f2db`) or Charon `0.1.291` (`9e95cf31`), or resolution of the exact `rust-lang/rust` and `rust-lang/cargo` source commits underlying `nightly`.
  - Downstream Aeneas or Lean execution on the 173.5 MB error-bearing `zerocopy --lib` LLBC artifact (omitted due to `"has_errors": true` and 8 GiB host memory limits) or Lean typechecking (`lake env lean`) of the generated `Probe.lean` golden in `charon-llbc-output-goldens-and-revision-diffs`.
  - Large multi-package Cargo workspace scaling, deep dependency-chasing graphs, build-script/proc-macro compilation overhead, or process-tree aggregate RSS in the scaling probes (which measured single-file dependency-free fixtures of 3, 10, 100, and 1,000 independent functions via `charon rustc` and reported single-child `ru_maxrss`).
- **Unknown**:
  - Formal semantic preservation of Charon's 53 transformation passes—specifically UB reflection when `IndexVisitor::transform_place` or `desugar_drops` introduces fresh references, and cleanup-path equivalence when `move_asserts_to_statements` folds dynamic checks into statements with `AbortKind`.
  - Whether any of the 45 frozen `0.1.210` cohort claims change behavior at `2804f2db` (`0.1.274`).
- **Known not to apply**:
  - Treating `Preset::RawMir` as an unnormalized passthrough of `rustc` MIR, or treating a requested MIR level (`Promoted`, `Elaborated`) as a uniform guarantee across local stolen bodies, `const fn` bodies, and foreign bodies.
  - Treating Charon process exit status `0` or `.llbc` file creation as proof of error-free extraction (`zerocopy --lib` exits `0` with `"has_errors": true` and 13 warnings).
  - Treating Charon package version strings (`0.1.210`) or release date tags (`nightly-2026.06.03`) as unique commit identities (`a535e914` vs. `0c91ca1a`), or treating raw LLBC SHA-256 inequality as semantic drift without normalizing `options.dest_file` and associative name maps (`item_names`, `short_names`, `assoc_item_names`).
- **Language-support and failure inventory**: The documented language-support and failure behavior (and language-support and unsoundness report boundaries) in the upgrade checklist reflects known/tested constructs rather than a guarantee that every unlisted Rust feature is supported.

---

## Evidence

All staged support artifacts in this package are verified on disk and indexed below by constituent investigation:

1. **45-Cohort Source Review (`charon-0-1-210-to-source-review`)**:
   - [support/charon-0-1-210-to-source-review/matrix.json](support/charon-0-1-210-to-source-review/matrix.json) — full 45-row reconciliation matrix with report/metadata SHA-256 digests, first-section excerpts and line locators, subject graphs, and four-part outcome fields.
   - [support/charon-0-1-210-to-source-review/frozen-cohort.csv](support/charon-0-1-210-to-source-review/frozen-cohort.csv), [support/charon-0-1-210-to-source-review/version-inventory-ebcdcad-581.csv](support/charon-0-1-210-to-source-review/version-inventory-ebcdcad-581.csv), and [support/charon-0-1-210-to-source-review/baseline-report-paths.txt](support/charon-0-1-210-to-source-review/baseline-report-paths.txt) — cohort selectors and 581-row baseline inventory.
   - [support/charon-0-1-210-to-source-review/check_matrix.py](support/charon-0-1-210-to-source-review/check_matrix.py) — offline validator for commit IDs, cohort membership, hashes, excerpts, and result fields.
2. **Extraction Boundary and 53-Pass Normalization Audit (`charon-extraction-normalization-9e95cf3`)**:
   - [support/charon-extraction-normalization-9e95cf3/pass-inventory.json](support/charon-extraction-normalization-9e95cf3/pass-inventory.json) — all 53 scheduled pass occurrences with immutable GitHub blob links, `should_run` predicates, internal guards, and derived preservation obligations.
   - [support/charon-extraction-normalization-9e95cf3/source-index.json](support/charon-extraction-normalization-9e95cf3/source-index.json), [support/charon-extraction-normalization-9e95cf3/additional-source-index.json](support/charon-extraction-normalization-9e95cf3/additional-source-index.json), and [support/charon-extraction-normalization-9e95cf3/coverage.json](support/charon-extraction-normalization-9e95cf3/coverage.json) — exact blob SHA-1 identities and URLs for `driver.rs`, `get_mir.rs`, `options.rs`, `transform/mod.rs`, `export.rs`, `ast/krate.rs`, and transformation modules at `9e95cf318e3a2964fcf5e03104cde5b718f98ea5` and `1aebab5f03a58067e5dc0ede2fec584117f54964`.
3. **16-Run Mode Baseline and Scaling Protocol (`charon-extraction-scaling`)**:
   - [support/charon-extraction-scaling/SUPPORT.md](support/charon-extraction-scaling/SUPPORT.md), [support/charon-extraction-scaling/charon-scaling/measure.py](support/charon-extraction-scaling/charon-scaling/measure.py), and [support/charon-extraction-scaling/charon-scaling/runs.jsonl](support/charon-extraction-scaling/charon-scaling/runs.jsonl) — measurement harness and 16 per-run timing/RSS records.
   - Emitted mode artifacts: [support/charon-extraction-scaling/charon-scaling/whole.json](support/charon-extraction-scaling/charon-scaling/whole.json), [support/charon-extraction-scaling/charon-scaling/whole.llbc](support/charon-extraction-scaling/charon-scaling/whole.llbc), [support/charon-extraction-scaling/charon-scaling/whole.stderr](support/charon-extraction-scaling/charon-scaling/whole.stderr), [support/charon-extraction-scaling/charon-scaling/whole.stdout](support/charon-extraction-scaling/charon-scaling/whole.stdout), [support/charon-extraction-scaling/charon-scaling/one.json](support/charon-extraction-scaling/charon-scaling/one.json), [support/charon-extraction-scaling/charon-scaling/one.llbc](support/charon-extraction-scaling/charon-scaling/one.llbc), [support/charon-extraction-scaling/charon-scaling/one.stderr](support/charon-extraction-scaling/charon-scaling/one.stderr), [support/charon-extraction-scaling/charon-scaling/one.stdout](support/charon-extraction-scaling/charon-scaling/one.stdout), [support/charon-extraction-scaling/charon-scaling/three.json](support/charon-extraction-scaling/charon-scaling/three.json), [support/charon-extraction-scaling/charon-scaling/three.llbc](support/charon-extraction-scaling/charon-scaling/three.llbc), [support/charon-extraction-scaling/charon-scaling/three.stderr](support/charon-extraction-scaling/charon-scaling/three.stderr), [support/charon-extraction-scaling/charon-scaling/three.stdout](support/charon-extraction-scaling/charon-scaling/three.stdout), [support/charon-extraction-scaling/charon-scaling/whole_no_serialize.json](support/charon-extraction-scaling/charon-scaling/whole_no_serialize.json), [support/charon-extraction-scaling/charon-scaling/whole_no_serialize.stderr](support/charon-extraction-scaling/charon-scaling/whole_no_serialize.stderr), and [support/charon-extraction-scaling/charon-scaling/whole_no_serialize.stdout](support/charon-extraction-scaling/charon-scaling/whole_no_serialize.stdout).
4. **Translation Goldens and Repeat-Run Probe (`charon-llbc-output-goldens-and-revision-diffs`)**:
   - [support/charon-llbc-output-goldens-and-revision-diffs/SUPPORT.md](support/charon-llbc-output-goldens-and-revision-diffs/SUPPORT.md) and fixture source [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.rs](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.rs).
   - Raw LLBC, pretty LLBC, and generated Lean outputs: [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.llbc](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe.llbc), [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe-baseline.llbc](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe-baseline.llbc), [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe-repeat.llbc](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/probe-repeat.llbc), [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/pretty-baseline.txt](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/pretty-baseline.txt), [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/pretty-repeat.txt](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/pretty-repeat.txt), [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/lean-baseline.lean](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/lean-baseline.lean), and [support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/lean/Probe.lean](support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/lean/Probe.lean).
5. **Generated Crate Scaling, Many-Root Sweep, and `0.1.208`/`0.1.210` Diffs (`charon-performance-and-revision-probes`)**:
   - Generated crate fixtures and whole-crate outputs: [support/charon-performance-and-revision-probes/generated-crate-summary.json](support/charon-performance-and-revision-probes/generated-crate-summary.json), [support/charon-performance-and-revision-probes/prior-generated-sweep.md](support/charon-performance-and-revision-probes/prior-generated-sweep.md), [support/charon-performance-and-revision-probes/generated-crates/functions_10.rs](support/charon-performance-and-revision-probes/generated-crates/functions_10.rs), [support/charon-performance-and-revision-probes/generated-crates/functions_100.rs](support/charon-performance-and-revision-probes/generated-crates/functions_100.rs), [support/charon-performance-and-revision-probes/generated-crates/functions_1000.rs](support/charon-performance-and-revision-probes/generated-crates/functions_1000.rs), [support/charon-performance-and-revision-probes/generated-crates/whole-10.llbc](support/charon-performance-and-revision-probes/generated-crates/whole-10.llbc), [support/charon-performance-and-revision-probes/generated-crates/whole-100.llbc](support/charon-performance-and-revision-probes/generated-crates/whole-100.llbc), and [support/charon-performance-and-revision-probes/generated-crates/whole-1000.llbc](support/charon-performance-and-revision-probes/generated-crates/whole-1000.llbc).
   - Many-root sweep artifacts: [support/charon-performance-and-revision-probes/root-matrix-summary.json](support/charon-performance-and-revision-probes/root-matrix-summary.json), [support/charon-performance-and-revision-probes/root-matrix.json](support/charon-performance-and-revision-probes/root-matrix.json), [support/charon-performance-and-revision-probes/many-roots/root_matrix.py](support/charon-performance-and-revision-probes/many-roots/root_matrix.py), [support/charon-performance-and-revision-probes/many-roots/roots-1.llbc](support/charon-performance-and-revision-probes/many-roots/roots-1.llbc), [support/charon-performance-and-revision-probes/many-roots/roots-10.llbc](support/charon-performance-and-revision-probes/many-roots/roots-10.llbc), [support/charon-performance-and-revision-probes/many-roots/roots-100.llbc](support/charon-performance-and-revision-probes/many-roots/roots-100.llbc), and [support/charon-performance-and-revision-probes/many-roots/roots-1000.llbc](support/charon-performance-and-revision-probes/many-roots/roots-1000.llbc).
   - Revision normalization artifacts: [support/charon-performance-and-revision-probes/normalize.py](support/charon-performance-and-revision-probes/normalize.py), [support/charon-performance-and-revision-probes/revision-comparison-raw.json](support/charon-performance-and-revision-probes/revision-comparison-raw.json), [support/charon-performance-and-revision-probes/revision-diff/compare.py](support/charon-performance-and-revision-probes/revision-diff/compare.py), [support/charon-performance-and-revision-probes/revision-diff/comparison.json](support/charon-performance-and-revision-probes/revision-diff/comparison.json), [support/charon-performance-and-revision-probes/revision-diff/normalized-1.json](support/charon-performance-and-revision-probes/revision-diff/normalized-1.json), and [support/charon-performance-and-revision-probes/revision-diff/normalized-2.json](support/charon-performance-and-revision-probes/revision-diff/normalized-2.json).
6. **Twelve-Gate Release Upgrade Checklist (`charon-release-upgrade-checklist-0-1-210`)**:
   - [support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json](support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json) and [support/charon-release-upgrade-checklist-0-1-210/source-map.json](support/charon-release-upgrade-checklist-0-1-210/source-map.json).
7. **`zerocopy --lib` Repeat-Run Determinism (`charon-zerocopy-library-repeat-order`)**:
   - [support/charon-zerocopy-library-repeat-order/observations.json](support/charon-zerocopy-library-repeat-order/observations.json), [support/charon-zerocopy-library-repeat-order/comparison.json](support/charon-zerocopy-library-repeat-order/comparison.json), [support/charon-zerocopy-library-repeat-order/first-order-differences.json](support/charon-zerocopy-library-repeat-order/first-order-differences.json), and [support/charon-zerocopy-library-repeat-order/replay-comparison.json](support/charon-zerocopy-library-repeat-order/replay-comparison.json).
   - Verification and replay scripts: [support/charon-zerocopy-library-repeat-order/check.py](support/charon-zerocopy-library-repeat-order/check.py), [support/charon-zerocopy-library-repeat-order/compare.py](support/charon-zerocopy-library-repeat-order/compare.py), and [support/charon-zerocopy-library-repeat-order/replay.py](support/charon-zerocopy-library-repeat-order/replay.py).
   - Redacted stderr logs: [support/charon-zerocopy-library-repeat-order/run1-stderr.txt](support/charon-zerocopy-library-repeat-order/run1-stderr.txt), [support/charon-zerocopy-library-repeat-order/run2-stderr.txt](support/charon-zerocopy-library-repeat-order/run2-stderr.txt), and [support/charon-zerocopy-library-repeat-order/run3-stderr.txt](support/charon-zerocopy-library-repeat-order/run3-stderr.txt).

---

## Revalidation

To revalidate the findings and support artifacts in this package across toolchain upgrades or environment changes:

1. **Validate the 45-Cohort Reconciliation Matrix**:
   - Run `python3 support/charon-0-1-210-to-source-review/check_matrix.py` against a reference checkout containing commits `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` and `2e9db344b6c0e6391ff78655a18b81ecb7e293e1`. Before changing any row's `source_claim_result` from `unresolved_at_target`, inspect the claim-determining source path at the target Charon revision, resolve the exact `rustc` and `cargo` revisions for `nightly`, and execute a bounded reproducer.
2. **Audit Extraction and Normalization Passes on a New Charon Pin**:
   - Diff `driver::{setup_compiler, set_mir_options, run_rustc_driver}`, `get_mir_for_def_id_and_level`, `CliOpts::apply_preset`, `TranslateOptions::new`, and `run_transformation_passes` (`charon/src/transform/mod.rs`) against `support/charon-extraction-normalization-9e95cf3/pass-inventory.json`. Check dynamic-check `AbortKind` folding (`move_asserts_to_statements`), index reference insertion (`index_intermediate_assigns`, `IndexVisitor::transform_place`), storage statement insertion, unit-local erasure, and `hide_allocator_param`.
3. **Re-run Small-Fixture Scaling, Many-Root Sweeps, and Golden Normalization**:
   - Verify pinned binary SHA-256 digests (`charon`, `charon-driver`, `rustc`, `aeneas`), then run `support/charon-extraction-scaling/charon-scaling/measure.py` and `support/charon-performance-and-revision-probes/many-roots/root_matrix.py` with `CHARON_TOOLCHAIN_IS_IN_PATH=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 CARGO_INCREMENTAL=0`.
   - Compare raw JSON, `support/charon-performance-and-revision-probes/normalize.py` (`dest_file` + sorted `item_names`, `short_names`, `assoc_item_names`), `charon pretty-print`, and `aeneas -backend lean` outputs against `support/charon-llbc-output-goldens-and-revision-diffs/translation-goldens/`.
4. **Re-verify `zerocopy --lib` Repeat-Run Determinism**:
   - Run `python3 support/charon-zerocopy-library-repeat-order/check.py` to validate retained observations and stderr hashes, or run `python3 support/charon-zerocopy-library-repeat-order/replay.py` with an offline checkout of `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` under its 180s, 3.5 GiB process RSS, 15% free RAM, and 15 GiB disk guards.
5. **Execute the Twelve-Gate Release Upgrade Checklist**:
   - Record candidate evidence against each gate in `support/charon-release-upgrade-checklist-0-1-210/upgrade-checklist.json`, ensuring that `has_errors: true` outputs are rejected fail-closed and that every empirical gate is satisfied by packaged execution rather than source inspection alone.
