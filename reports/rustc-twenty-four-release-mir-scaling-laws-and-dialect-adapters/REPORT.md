# Twenty-Four-Release `rustc` MIR Scaling Laws and Zero-`build.rs` Dialect Adapters (`1.78.0`–`1.102.0-nightly`)

## Summary

Programmatic Git source extraction across **24 pinned `rust-lang/rust` revisions** (`23` consecutive stable minor releases `1.78.0` through `1.100.0` plus `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, spanning `926.17` days / **`2.5357` years** across `23` adjacent transitions from `2024-04-29` to `2026-11-11`, plus an intra-cycle `1.102.0-nightly` checkpoint at `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` on `2026-11-19`), primary-source inspection of `rust-lang/rust` and `dtolnay/rustversion` (`1.0.23`), and **live `rustc` and `#![feature(rustc_private)]` compilation experiments across 18 toolchains** (including **10 `rustc-dev` compilers** spanning `1.91.0-nightly` through `1.102.0-nightly`, **7 standalone `--sysroot` eras** spanning `1.94.1` through `1.102.0-nightly`, and a custom `1.100.0-dev` `stage1` build) establish three engineering laws for multi-compiler `MirPhase::Runtime(RuntimePhase::PostCleanup)` MIR capture and verification:

1. **Four-Tier Longitudinal Scaling Stratification (`1.78.0` $\to$ `1.102.0-nightly`, `23` Transitions, `9.07` Releases/Year):**
   - **Tier A (Narrow `rustc_private` Capture-Driver API):** **`19` breaking transitions** across six driver/type/layout/const/crate sub-surfaces (**`0.826` breaks/release**, **`7.49` breaks/year**), of which **`14`** (**`0.609`/release**, **`5.52`/year**) affect a minimal scalar/ADT MIR-capture driver. Two core sub-surfaces—`tcx.mir_drops_elaborated_and_const_checked(local_def_id)` / `tcx.dcx().has_errors()` and `tcx.crates(())` / `tcx.used_crate_source(cnum)`—suffered **`0` breaking API changes across `2.54` years**.
   - **Tier B (`rustc_middle::mir` AST Syntax Schema):** **`44` raw declaration-level mutations** across `18` core MIR AST structs and enums (**`1.913` deltas/release**, **`17.35` deltas/year**). Excluding `8` non-operational metadata/coverage mutations and pre-runtime constructs provably unreachable in `Runtime(PostCleanup)` (`StatementKind::BackwardIncompatibleDropHint` and `ProjectionElem::PhantomDeref`) leaves **`36` `Runtime(PostCleanup)`-reachable schema deltas** (**`1.565`/release**, **`14.20`/year**): `34` operational construct/payload changes (`1.478`/release) and `2` pure pattern-destructuring field changes (`-Drop.async_fut` in `1.98.0`, `+Goto.loop_hint_attrs` in `1.102.0-nightly`).
   - **Tier C (Genuine Runtime Operational Semantics):** Out of **`591` non-merge commits** touching `compiler/rustc_const_eval/src/interpret/*.rs`, `library/core/src/convert/mod.rs`, and `library/alloc/src/boxed.rs` over `2.54` years, **`575` (`97.29%`) are internal compiler refactors** with zero operational semantic impact, leaving **`16` genuine runtime semantic transitions** (**`0.696`/release**, **`6.31`/year**) that alter undefined-behavior boundaries, evaluation order, provenance retagging, padding initialization, or primitive type identity.
   - **Tier D (Lowering-Only, Monomorphization, and Stdlib Representation Shifts):** Syntax-only splits (`CheckedBinaryOp` $\to$ `*WithOverflow`, `NullOp::OffsetOf` $\to$ constant sums, `Goto { loop_hint_attrs }` when empty, `CleanupPostBorrowck` erasing edition-specific drop hints) and opaque stdlib wrapper refactors (`AtomicU*` $\to$ `Atomic<T>`, `Unique<T>` $\to$ `BoxRaw<T>`) normalize losslessly into a monotonic superset trunk IR, whereas Tier-C operational transitions must bind to explicit semantic dialect/capability flags rather than being silently erased by a syntax adapter.

2. **Disqualification of `#![feature(cfg_version)]`, `#![feature(cfg_accessible)]`, and `#[rustversion]` for Zero-`build.rs` TCB Drivers:**
   - **`#![feature(cfg_version)]` (`#[cfg(version("..."))]`):** Evaluates `RustcVersion::current_overridable() >= min_version` after stripping `-nightly`, `-beta`, and `-dev` suffixes. Live tests prove three disqualifying failures: (a) unprivileged ambient `RUSTC_OVERRIDE_VERSION_STRING` spoofs predicate evaluation at compile time (`"1.78.0-custom"` flips `version("1.100")` to `false` on `rustc 1.100.0`; `"1.999.0"` flips `version("1.102")` to `true`), while custom `1.100.0-dev` claims full `1.100.0` completion; (b) default `>=` crashes mid-cycle on `1.97.0-nightly (bf4fbfb7a 2026-04-11)` with `error[E0023]` when gating 2-field `Rvalue::Use(op, _retag)`; and (c) `-Z assume-incomplete-release` (`>`) counter-crashes on `1.102.0-nightly (3ef0c22cd 2026-11-11)` with `error[E0425]: cannot find function run_compiler`.
   - **`#![feature(cfg_accessible)]` (`#[cfg_accessible(path)]`):** Implemented as an outer `MultiItemModifier` attribute macro rather than a `cfg(...)` predicate. While top-level module/type/function paths (`rustc_abi::TyAndLayout`, `rustc_driver::compiler_entrypoint`) resolve cleanly, enum variants create an **asymmetric cross-version compile-time trap**: when a variant exists (`CastKind::BoxDerefTransmute` on `1.99.1+`, `StatementKind::Retag` on `1.94.1`), compilation succeeds (`Ok(true)`), but on compilers where the variant is absent (`BoxDerefTransmute` on `<= 1.98.0-nightly`, `Retag` on `>= 1.98.0-nightly`), `Resolver::path_accessible` hits `PathResult::NonModule(..)` with an unresolved trailing segment and aborts compilation with `CfgAccessibleUnsure` (`error: not sure whether the path is accessible or not`) even inside glob-shadowed fallback modules. It likewise hard-errors on struct fields, enum struct-variant fields (`TerminatorKind::Goto::loop_hint_attrs`), inherent methods, `cfg(not(cfg_accessible(...)))` negation (`E0537`/`E0539`), and `match` arms.
   - **`#[rustversion]` (`dtolnay/rustversion` `1.0.23`):** Requires both executing a `build.rs` script (`Command::new(rustc).arg("--version")`, inheriting `RUSTC_OVERRIDE_VERSION_STRING` spoofing) and compiling/loading a host `proc-macro` library (`proc-macro = true`), discards nightly commit hashes in favor of coarse `YYYY-MM-DD` dates (`Channel::Dev` evaluates `>` every future nightly date; custom channel suffixes abort `build.rs` with `exit 1`), and orders `Stable`/`Beta` strictly below all `Bound::Nightly(date)` bounds while ignoring channel tags on `Bound::Stable(release)` (`1.97.0-nightly` `2026-04-11` satisfies `since(1.97)`).

3. **`164`-LOC (`13.67` LOC/Release) Zero-`build.rs` `--cfg` Dialect Adapter Across `10 / 10` `rustc-dev` Toolchains (`1.91.0-nightly`–`1.102.0-nightly`) and `7 / 7` `--sysroot` Eras (`1.94.1`–`1.102.0-nightly`):**
   - Isolating Tier-A and Tier-B compiler drift behind a leaf `src/dialect.rs` module (`164` non-comment, non-blank LOC = **`13.67` LOC per minor release** across 12 minor cycles, projecting to `~314` LOC across 24 releases) gated by explicit launcher-passed `--cfg` flags (`--check-cfg` + `#![deny(unexpected_cfgs)]` + crate-root `compile_error!` mutual-exclusivity check, zero `build.rs`, zero external crates) compiles with `-D warnings` (`rc = 0`) and captures live `Runtime(PostCleanup)` MIR (`rc = 0`) across **`10 / 10` `rustc-dev` toolchains** under hostile `RUSTC_OVERRIDE_VERSION_STRING="1.78.0-hostile"` plus **`2 / 2` offline Cargo builds**. A companion single-file capability-flag driver (`--cfg=dialect_has_stmt_retag` / `dialect_use_has_with_retag`, `--cfg=dialect_run_compiler_fn` / `dialect_entrypoint_fn`) compiles in **`315.3–389.3 ms`** warm (`971.7 ms` cold tarball sysroot) into **`35.6–48.4 KiB`** binaries across **`7 / 7` `rustc-dev` sysroots** (`1.94.1`–`1.102.0-nightly`), leaving `>90%` of capture-emitter logic completely free of `#[cfg]` conditionals.

## Applicability

This report extends the corpus's nine-month (`1.93.1`–`1.102.0-nightly`) crate-level body-drift study (`reports/rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility/`) without repeating its `ryu`/`itoa`/`memchr` body-diff tables. Where that study measured how often downstream crate MIR bodies change across seven releases, this report establishes (1) the **24-revision (`2.54`-year) compiler-side scaling law** across driver APIs, MIR AST declarations, and `rustc_const_eval::interpret` operational semantics, and (2) the **compile-time multi-version adapter mechanism** required for a single `#![feature(rustc_private)]` capture crate to span multiple `rustc` releases without `build.rs` or external proc-macros.

Findings apply to the concrete upstream revisions recorded in `REPORT.json` and observed on `2026-11-22` on `x86_64-unknown-linux-gnu`:

- **Longitudinal `rust-lang/rust` scaling census (`24` primary revisions + `1` intra-nightly checkpoint, `[published source]`):**
  - Consecutive official stable minor releases `1.78.0` (`9b00956e56009bab2aa15d7bff10916599e3d6d6`, `2024-04-29`) through `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, `2026-11-09`), plus `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`), forming `23` adjacent transitions across `926.17` days (`2.5357` years).
  - Intra-cycle nightly checkpoint `1.102.0-nightly` (`6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, `2026-11-19`) testing same-version-string API drift within an active nightly cycle.
- **Live compiler execution matrices (`18` distinct toolchains on `x86_64-unknown-linux-gnu`, `[real measurement]`):**
  - **`10` `rustup` toolchains with `rustc-dev` (`12` minor cycles `1.91`–`1.102`):** `1.91.0-nightly` (`05f5a58e84a9c3a68586d70bf3d7442c571e379e`), `1.93.0-nightly` (`94b49fd998d6723e0a9240a7cff5f9df37b84dd8`), `1.95.0-nightly` (`efc9e1b50cbf2cede7ebe25f0a1fc64fd8b3e942`), `1.97.0-nightly` (`bf4fbfb7a18d74e7cd8eef93af7329c58fbb5344`), `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`), `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `1.102.0-nightly` (`8eb778d04094d3af4b26580cab327e0413eb1e02`).
  - **`2` additional standalone `rustc-dev` sysroots in the 7-era `--sysroot` capability-driver matrix:** `1.94.1` (`e408947bfd200af42db322daf0fadfe7e26d3bd1`, source-tarball build) and `1.100.0-nightly` (`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, `2026-09-16`), alongside `1.95.0-nightly` (`efc9e1b50...`), `1.97.0-nightly` (`bf4fbfb7a...`), `1.98.0-nightly` (`f8a08b688...`), `1.100.0` (`0ef1bc386...`), and `1.102.0-nightly` (`3ef0c22cd...`).
  - **`6` additional toolchains in the `cfg(version)` truth table:** `1.78.0` (`9b00956e5...`), `1.80.1` (`3f5fd8dd41153bc5fdca9427e9e05be2c767ba23`), `1.84.0` (`9fc6b4312...`), `1.93.1` (`01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`), `1.96.0` (`ac68faa20...`), `1.95.0-nightly` (`c78a29473a68f07012904af11c92ecffa68fcc75`, `2026-02-22`), `1.102.0-nightly` (`6905905bb...`, `2026-11-19`), plus a local `stage1` build reporting `rustc 1.100.0-dev` (characterizing `-dev` channel parsing in `RustcVersion::parse_str`).
- **External proc-macro version gate (`[published source]`):** `dtolnay/rustversion` `1.0.23` (`3a7c76605450b9a7299c6502a421909de9126a59`).
- **MIR phase scope:** Tier-B reachability and Tier-C operational semantics apply specifically to `MirPhase::Runtime(RuntimePhase::PostCleanup)` retrieved via `tcx.mir_drops_elaborated_and_const_checked(local_def_id)` after borrow-checking, drop elaboration, and post-borrowck cleanup, and prior to `Runtime(Optimized)` MIR optimization and inlining passes.

## Findings

### 1. Four-Tier Longitudinal Scaling Census Across 24 `rustc` Revisions (`1.78.0`–`1.102.0-nightly`)

`Basis: source + execution + derived (support/probe_mir_scaling_and_cfg_matrix.py, support/probe_mir_scaling_and_cfg_matrix.json against https://github.com/rust-lang/rust.git)`

#### 1.1 Summary Four-Tier Scaling Matrix and 24-Revision Anchor Table

Across `926.17` days (`2.5357` years; `23` adjacent transitions at **`9.07` transitions/year**), compiler churn stratifies into four distinct architectural layers with markedly different mutation rates and handling mechanisms:

| Tier | Compiler / Semantic Surface | 24-Revision Count (`1.78.0` $\to$ `1.102.0-nightly`) | Per-Release Rate (`/ 23` transitions) | Annualized Rate (`/ 2.5357` yr) | Required Architectural Handling Layer |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **Baseline Cadence** | Pinned stable minor releases (`1.78.0`..`1.100.0`) + `1.102.0-nightly` | **`24` revisions** (`23` transitions) | `1.000` / release | **`9.07` / yr** | Declarative launcher manifest mapping `(commit_sha, archive_sha256)` to `--cfg` dialect & semantic profile |
| **Tier A: Narrow Driver API** | 6-part `rustc_private` MIR-capture surface `(a)`–`(f)` | **`19` breaks** (`14` minimal scalar/ADT driver; `0` on MIR query & crate source) | **`0.826`** (`0.609` minimal) | **`7.49` / yr** (`5.52` minimal) | Leaf `dialect.rs` helper functions (`~13.7` LOC/release; `0` `#[cfg]` in main emitter) |
| **Tier B: `mir` AST Syntax** | 18 core AST structs/enums in `compiler/rustc_middle/src/mir/{syntax,mod}.rs` | **`44` raw deltas** (`36` `PostCleanup`-reachable; `34` operational + `2` field-only) | **`1.913` raw** (`1.565` reachable; `1.478` op) | **`17.35` / yr** (`14.20` reachable) | Direct 1-pass spoke lowering in `dialect.rs` to monotonic superset trunk IR + fail-closed `.unsupported` |
| **Tier C: Runtime Operational Semantics** | `rustc_const_eval/src/interpret/*.rs` + `core`/`alloc` lang primitives (`591` commits audited) | **`16` genuine transitions** (`575 / 591 = 97.29%` internal refactors) | **`0.696` / release** | **`6.31` / yr** | Explicit `MirSemantics` / `SemProfile` capability flags (or fail-closed rejection on affected constructs) |
| **Tier D: Lowering & Stdlib Repr** | Desugaring-only splits, `CleanupPostBorrowck` erasure, & stdlib private wrapper refactors | Absorbed without new operational rules | — | — | Trunk canonicalization + opaque normative contracts / `TyAndLayout`-based lowering |

Every tag SHA in the 24-revision anchor sequence (plus intra-cycle checkpoint `24b`) was resolved via `git rev-parse <tag>^{commit}` in `rust-lang/rust`:

| # | Release / Checkpoint | Channel | Full 40-Character `rust-lang/rust` Commit SHA | Commit Timestamp (UTC) |
| ---: | :--- | :--- | :--- | :--- |
| 1 | `1.78.0` | stable | `9b00956e56009bab2aa15d7bff10916599e3d6d6` | `2024-04-29T14:01:42Z` |
| 2 | `1.79.0` | stable | `129f3b9964af4d4a709d1383930ade12dfe7c081` | `2024-06-10T08:33:35Z` |
| 3 | `1.80.0` | stable | `051478957371ee0084a7c0913941d2a8c4757bb9` | `2024-07-21T15:48:16Z` |
| 4 | `1.81.0` | stable | `eeb90cda1969383f56a2637cbd3037bdf598841c` | `2024-09-04T15:07:06Z` |
| 5 | `1.82.0` | stable | `f6e511eec7342f59a25f7c0534f1dbea00d01b14` | `2024-10-15T17:22:50Z` |
| 6 | `1.83.0` | stable | `90b35a6239c3d8bdabc530a6a0816f7ff89a0aaf` | `2024-11-26T10:12:09Z` |
| 7 | `1.84.0` | stable | `9fc6b43126469e3858e2fe86cafb4f0fd5068869` | `2025-01-07T01:26:09Z` |
| 8 | `1.85.0` | stable | `4d91de4e48198da2e33413efdcd9cd2cc0c46688` | `2025-02-17T18:17:27Z` |
| 9 | `1.86.0` | stable | `05f9846f893b09a1be1fc8560e33fc3c815cfecb` | `2025-03-31T21:37:24Z` |
| 10 | `1.87.0` | stable | `17067e9ac6d7ecb70e50f92c1944e545188d2359` | `2025-05-09T20:37:37Z` |
| 11 | `1.88.0` | stable | `6b00bc3880198600130e1cf62b8f8a93494488cc` | `2025-06-23T19:24:54Z` |
| 12 | `1.89.0` | stable | `29483883eed69d5fb4db01964cdf2af4d86e9cb2` | `2025-08-04T12:20:29Z` |
| 13 | `1.90.0` | stable | `1159e78c4747b02ef996e55082b704c09b970588` | `2025-09-14T15:05:11Z` |
| 14 | `1.91.0` | stable | `f8297e351a40c1439a467bbbb6879088047f50b3` | `2025-10-28T16:34:16Z` |
| 15 | `1.92.0` | stable | `ded5c06cf21d2b93bffd5d884aa6e96934ee4234` | `2025-12-08T12:52:32Z` |
| 16 | `1.93.0` | stable | `254b59607d4417e9dffbc307138ae5c86280fe4c` | `2026-01-19T16:34:28Z` |
| 17 | `1.94.0` | stable | `4a4ef493e3a1488c6e321570238084b38948f6db` | `2026-03-02T23:18:25Z` |
| 18 | `1.95.0` | stable | `59807616e1fa2540724bfbac14d7976d7e4a3860` | `2026-04-14T19:55:32Z` |
| 19 | `1.96.0` | stable | `ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96` | `2026-05-25T23:21:07Z` |
| 20 | `1.97.0` | stable | `2d8144b7880597b6e6d3dfd63a9a9efae3f533d3` | `2026-07-07T01:27:02Z` |
| 21 | `1.98.0` | stable | `88d9e12ae178fab0fb5cc050a94da85685d449ea` | `2026-08-18T19:58:58Z` |
| 22 | `1.99.0` | stable | `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` | `2026-09-28T18:24:15Z` |
| 23 | `1.100.0` | stable | `0ef1bc386059596dada8fb65b50425aab2ea637a` | `2026-11-09T22:11:55Z` |
| 24 | `1.102.0-nightly` (`2026-11-11`) | nightly | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `2026-11-11T17:59:24Z` |
| 24b | `1.102.0-nightly` (`2026-11-19`) | nightly | `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` | `2026-11-19T17:33:07Z` |

#### 1.2 Tier A: Narrow `rustc_private` Capture-Driver API Breakage Census (`19` Full / `14` Minimal Transitions)

`Basis: source + derived (compiler/rustc_driver_impl, compiler/rustc_interface, compiler/rustc_middle/src/{ty,mir/interpret}, compiler/rustc_abi across all 24 revisions)`

Auditing the narrow six-part `rustc_private` surface required by an in-process `Runtime(PostCleanup)` MIR capture driver reveals that API churn is heavily concentrated in type/layout wrappers while core query entrypoints are completely invariant:

- **Zero-breakage sub-surfaces (`0` breaking changes across `24` revisions / `2.54` years):**
  - **(b) Post-cleanup MIR & error queries:** `tcx.mir_drops_elaborated_and_const_checked(local_def_id)` (`LocalDefId -> &'tcx Steal<mir::Body<'tcx>>`) and `tcx.dcx().has_errors()` (`&self -> Option<ErrorGuaranteed>`) preserved identical call syntax and return types across all 24 revisions (including the internal query-macro table split out of `rustc_middle/src/query/mod.rs` in `1.95.0`).
  - **(f) External crate enumeration & `.rmeta` path lookup:** `tcx.crates(())` and `tcx.used_crate_source(cnum)` remained `100%` source-compatible across all 24 revisions (`used_crate_source` replaced type alias `Lrc<CrateSource>` with `Arc<CrateSource>` in `1.86.0`, which already resolved to `Arc` under parallel `rustc`).
- **Concentrated breakage sub-surfaces (`19` transition events total; `14` affecting minimal scalar/ADT capture drivers that match unsupported `TyKind` variants via `_`):**
  - **(a) `rustc_driver` / `rustc_interface` (`5` transitions):** `RunCompiler<'a, 'b>` $\to$ `RunCompiler<'a>` (`1.83.0`); `Callbacks::after_analysis` & `after_expansion` changing third parameter `&'tcx Queries<'tcx>` $\to$ `TyCtxt<'tcx>` (`1.85.0`); `RunCompiler` struct deleted in favor of `rustc_driver::run_compiler(&[String], &mut (dyn Callbacks + Send))` (`1.86.0`); `catch_with_exit_code` return type `i32` $\to$ `std::process::ExitCode` (`1.94.0`); `rustc_driver::run_compiler` renamed to `rustc_driver::compiler_entrypoint` (`1.102.0-nightly`). (`interface::Compiler` mutated only `pub(crate)` fields `current_gcx` and `jobserver_proxy`.)
  - **(c) `TyKind` and `ParamEnv` $\to$ `TypingEnv` (`10` transitions + `1` intra-nightly):** `ParamEnv::reveal_all().and(ty)` (`ParamEnvAnd`) was replaced by `TypingEnv::fully_monomorphized().as_query_input(ty)` (`PseudoCanonicalInput`) in `1.84.0`; `TyKind` mutated in `1.79.0` (`RawPtr(Ty, Mutability)`, `+Pat`), `1.80.0` (`FnPtr`, `Alias`), `1.82.0` (`FnPtr` 2-arg split), `1.85.0` (`+UnsafeBinder`), `1.91.0` (`FnDef`/`Closure` associated ID aliases, transparent when `I = TyCtxt<'tcx>`), `1.92.0` (`Dynamic` `-DynKind`, `Bound`), `1.96.0` (`Alias` 1-arg), `1.98.0` (`Alias(IsRigid, ..)`), `1.99.0` (`FnDef(FunctionId, Binder<I, GenericArgs>)`), and intra-nightly `1.102.0-nightly` (`+View` at `94add9677e2de57a2e414350bedcd13f07426a5e`).
  - **(d) `rustc_target::abi` $\to$ `rustc_abi` & layout representations (`9` transitions):** Full crate extraction to `extern crate rustc_abi` + `Abi` $\to$ `BackendRepr` (`Aggregate` $\to$ `Memory`, `LayoutS` $\to$ `LayoutData`) (`1.84.0`); `+Variants::Empty` (`1.85.0`); `-BackendRepr::Uninhabited` $\to$ `LayoutData.uninhabited: bool` + `SimdVector` (`1.87.0`); `AbiAndPrefAlign` $\to$ `AbiAlign` + `Variants::Multiple.tag_field: FieldIdx` (`1.89.0`); `FieldsShape::Arbitrary.memory_index` $\to$ inverse `in_memory_order` (`1.94.0`); `SimdScalableVector` (`1.96.0`); `Variants::Multiple.variants` element `LayoutData` $\to$ `VariantLayout<FieldIdx>` (`1.97.0`); `BackendRepr::ScalarPair { a, b, b_offset }` (`1.99.0`); `LayoutData.align: AbiAlign` $\to$ `Align` (`1.102.0-nightly`).
  - **(e) `mir::interpret` constants & allocations (`5` transitions):** `GlobalAlloc::Function(Instance)` $\to$ `Function { instance, unique }` (`1.81.0`) $\to$ `Function { instance }` (`1.82.0`); `GlobalAlloc::VTable` existential predicate list (`1.83.0`); `ConstValue::Slice { data }` $\to$ `Slice { alloc_id, meta }` + `+GlobalAlloc::TypeId { ty }` (`1.90.0`); `Scalar::Ptr(Pointer, u8)` $\to$ `Scalar::Ptr(Pointer, NonZero<u8>)` (`1.100.0`). (`AllocId(pub NonZero<u64>)` remained invariant.)

| ID (`tier2_breaks`) | Transition | Sub-Surface | Breaking Signature / Type / Crate Change | Verified Causal `rust-lang/rust` Commit SHA(s) | Minimal Driver? |
| :--- | :--- | :--- | :--- | :--- | :---: |
| `T2-01` | `1.78.0 -> 1.79.0` | `(c) TyKind` | `TyKind::RawPtr(TypeAndMut)` $\to$ `RawPtr(Ty, Mutability)`; `+TyKind::Pat` | `7be0dbe77292de955da02fe1de1626bdd2e4cc0a`, `84acfe86dec370028987c205e7ba32cc5796d9b0` | Yes |
| `T2-02` | `1.79.0 -> 1.80.0` | `(c) TyKind` | `TyKind::FnPtr(Binder<I, FnSig<I>>)`, `Alias(AliasTyKind, AliasTy<I>)` | `3bcdf3058ef3eaef5042661cf8301acfbcddce65` | No (`_` wildcard) |
| `T2-03` | `1.80.0 -> 1.81.0` | `(e) GlobalAlloc` | `GlobalAlloc::Function(Instance)` $\to$ `Function { instance, unique }` | `41b98da42d0500e38b9dd85c82110ba177ac4de1` | Yes |
| `T2-04` | `1.81.0 -> 1.82.0` | `(c)/(e) TyKind, GlobalAlloc` | `TyKind::FnPtr` 2-arg `(Binder<FnSigTys>, FnHeader)`; `-Function.unique` | `c4717cc9d15d30e08f03f51845c950175979bcc4`, `5cab8ae4a4a033acb25d629871deb24db19b638b` | Yes |
| `T2-05` | `1.82.0 -> 1.83.0` | `(a)/(e) RunCompiler, GlobalAlloc` | `RunCompiler<'a, 'b>` $\to$ `RunCompiler<'a>`; `GlobalAlloc::VTable` predicate list | `072bf482c98d0f33d8456c6000babf315b63e104`, `018ba0528fa5d22712397e520351295f8582a525` | No (elided lifetime) |
| `T2-06` | `1.83.0 -> 1.84.0` | `(c)/(d) TypingEnv, rustc_abi` | `rustc_target::abi` $\to$ `rustc_abi` (`Abi` $\to$ `BackendRepr`); `ParamEnvAnd` $\to$ `TypingEnv` | `10721909f29024ba56a9ce667da8652a99a04784`, `236fe33345072e6363560fd2b535a10947af86f7`, `7086dd83cca1cf694c7bd171efbf262fa8ffb4aa`, `9cba14b95bb07a5b31ed1aac2bf4eadd248232da` | Yes |
| `T2-07` | `1.84.0 -> 1.85.0` | `(a)/(c)/(d) Callbacks, Variants` | `Callbacks::after_analysis(&'tcx Queries)` $\to$ `TyCtxt<'tcx>`; `+Variants::Empty`; `+TyKind::UnsafeBinder` | `3b02a3309e12906a455eb128a0aa74c6a6afc932`, `b795264daa2d411fa232a3de51cc4b0ef8c86a33`, `e023590de407f417e0f3da675a372eca7acf60c6`, `9a1c5eb5b385adb3cd04af0049cbf5c225cefdc3` | Yes |
| `T2-08` | `1.85.0 -> 1.86.0` | `(a) rustc_driver` | `RunCompiler` struct deleted $\to$ `rustc_driver::run_compiler(&[String], &mut (dyn Callbacks + Send))` | `a77776cc1d7c599f4ff9355ffe01bad2e2b5bbad` | Yes |
| `T2-09` | `1.86.0 -> 1.87.0` | `(d) BackendRepr, LayoutData` | `-BackendRepr::Uninhabited` $\to$ `LayoutData.uninhabited: bool`; `Vector` $\to$ `SimdVector` | `7ba3d7b54e7688f6f1a0fd22fe274ee7b06fea3e`, `aac65f562b3e9351d4a4336c270ce13c130de467` | Yes |
| `T2-10` | `1.88.0 -> 1.89.0` | `(d) LayoutData, Variants` | `LayoutData.align: AbiAndPrefAlign` $\to$ `AbiAlign`; `Variants::Multiple.tag_field: usize` $\to$ `FieldIdx` | `2e1965831526407bada7abec631d7b7e9f6cbc7d`, `ee9901e65c78f70b93dab5bd1e04bd77273b7c40` | Yes |
| `T2-11` | `1.89.0 -> 1.90.0` | `(e) ConstValue, GlobalAlloc` | `ConstValue::Slice { data }` $\to$ `Slice { alloc_id }`; `+GlobalAlloc::TypeId { ty }` | `9ff071219bca913e45235568defadd5ab840c50a`, `486ffda9dcd0d4ef0a09d81e6ce5f241e77526a1` | Yes |
| `T2-12` | `1.91.0 -> 1.92.0` | `(c) TyKind` | `TyKind::Dynamic` `-DynKind`; `Bound(BoundVarIndexKind, ..)` | `26f3337d4eda0ba22b615744fda0185d0ee344b1` | No (`_` wildcard) |
| `T2-13` | `1.93.0 -> 1.94.0` | `(a)/(d) Driver, FieldsShape` | `catch_with_exit_code` `i32` $\to$ `ExitCode`; `FieldsShape::Arbitrary.memory_index` $\to$ `in_memory_order` | `6d36c8a5fc4dd9ad3a4cf95ca31ecdc7f06bafc1`, `b31ee3af9c67c777143c0b6707a4439c78391b69` | Yes |
| `T2-14` | `1.95.0 -> 1.96.0` | `(c)/(d) TyKind, BackendRepr` | `TyKind::Alias(AliasTy<I>)` 1-arg; `SimdScalableVector` | `cf96c5fa87f6805a382d4c6a9082c9777a404b5f`, `db5e2dc248fe5bb26f70d7baec46a3bca9fa3e1d` | No (`_` wildcard) |
| `T2-15` | `1.96.0 -> 1.97.0` | `(d) Variants::Multiple` | `Variants::Multiple.variants` element `LayoutData` $\to$ `VariantLayout<FieldIdx>` | `1162bdc1f3fe4a85f6b1d217578f40669c43aeb5`, `0569574938af400dfbfd88fea5a402a52f4cb4cf` | Yes |
| `T2-16` | `1.97.0 -> 1.98.0` | `(c) TyKind` | `TyKind::Alias(IsRigid, AliasTy<I>)` | `3dbe96a5a1b3e0e9cf8b9f0db1e7e4a5af58bf08` | No (`_` wildcard) |
| `T2-17` | `1.98.0 -> 1.99.0` | `(c)/(d) TyKind::FnDef, BackendRepr` | `TyKind::FnDef(FunctionId, Binder<I, GenericArgs>)`; `BackendRepr::ScalarPair { a, b, b_offset }` | `8fb83aba335e79dfb6843ec40c21b37f5f85a772`, `2efdc665a7809236738262ea13e5e3f1db204fd4` | Yes |
| `T2-18` | `1.99.0 -> 1.100.0` | `(e) Scalar::Ptr` | `Scalar::Ptr(Pointer<Prov>, u8)` $\to$ `Scalar::Ptr(Pointer<Prov>, NonZero<u8>)` | `d802d17e292ff782d346e0353af3a37dcb5ca12f` | Yes |
| `T2-19` | `1.100.0 -> 1.102.0-nightly` | `(a)/(d) Driver, LayoutData` | `rustc_driver::run_compiler` $\to$ `compiler_entrypoint`; `LayoutData.align: AbiAlign` $\to$ `Align` | `c39fbc44eb0f296a7ad161eee642e8bcd2a82235`, `81330f91e512e79001654f32843633dc21c42117` | Yes |

Between `1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) and intra-cycle `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` (`2026-11-19`), commit `94add9677e2de57a2e414350bedcd13f07426a5e` added `TyKind::View(I::AdtDef, I::GenericArgs, I::Ty)` and commit `c7577d3452810c553e2377d9c9b9eb2a9ce9148d` moved delayed-error checking into `compiler_entrypoint` while preserving the identical `"1.102.0-nightly"` version string.

#### 1.3 Tier B: Exhaustive `rustc_middle::mir` AST Schema Mutation Census (`44` Raw / `36` `PostCleanup`-Reachable)

`Basis: source + execution (programmatic brace-block extraction over compiler/rustc_middle/src/mir/{syntax,mod}.rs across all 24 revisions, cross-checked against cleanup_post_borrowck.rs, validate.rs, and interpret/projection.rs)`

Programmatic AST diffing across all `18` core MIR declarations in `compiler/rustc_middle/src/mir/syntax.rs` and `compiler/rustc_middle/src/mir/mod.rs`—`Body`, `BasicBlockData`, `LocalDecl`, `StatementKind`, `Rvalue`, `Operand`, `ProjectionElem` (aliased as `pub type PlaceElem<'tcx> = ProjectionElem<Local, Ty<'tcx>>`), `TerminatorKind`, `CastKind`, `BinOp`, `UnOp`, `NullOp`, `UnwindAction`, `AssertKind` (aliased as `pub type AssertMessage<'tcx> = AssertKind<Operand<'tcx>>`), `NonDivergingIntrinsic`, `RetagKind`, `WithRetag`, and `RuntimeChecks`—yields **`44` declaration-level schema mutations** across `18 / 23` transitions:

- **Zero-mutation declarations (`0` changes in `2.54` years):** `LocalDecl<'tcx>`, `UnwindAction` (`4` variants), and `NonDivergingIntrinsic` (`Assume`, `CopyNonOverlapping`).
- **Zero-mutation transitions (`5 / 23`):** `1.84.0 -> 1.85.0`, `1.86.0 -> 1.87.0`, `1.88.0 -> 1.89.0`, `1.90.0 -> 1.91.0`, and `1.95.0 -> 1.96.0` (`1.85.0 -> 1.86.0` only reformatted `Coverage(CoverageKind)` trailing commas).
- **`8` mutations excluded from `Runtime(PostCleanup)` operational reachability:**
  - `5` metadata/debug/coverage struct-field mutations on `Body` and `BasicBlockData` plus `1` `StatementKind::Coverage` wrapper change.
  - `StatementKind::BackwardIncompatibleDropHint` (`297b618944d4619a1990b1992d9142c6cf893dc6`, `1.84.0`), which `CleanupPostBorrowck` unconditionally rewrites to `StatementKind::Nop` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:36` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
  - `ProjectionElem::PhantomDeref` (`5686e563774cd9e8bfba79d3ab1167fe198e9e78`, `1.100.0`), a pre-borrowck reborrow placeholder that triggers an immediate internal compiler error if encountered after borrowck (`compiler/rustc_const_eval/src/interpret/projection.rs:414-415`: `span_bug!(self.cur_span(), "PhantomDeref encountered after borrowck")`).
- **Additional `MirPhase::Runtime(_)` validator exclusions (`compiler/rustc_mir_transform/src/validate.rs` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):** `Yield` (`:471`), `FalseEdge` (`:480`), `FalseUnwind` (`:490`), `CoroutineDrop` (`:509`), `ProjectionElem::OpaqueCast` (`:882`), `Rvalue::CopyForDeref` (`:1029`), `BorrowKind::Fake` (`:1158`), `PointerCoercion::{MutToConstPointer, ArrayToPointer}` (`:1326, :1342`, banned in `4630d1b23b996793e9188490cc99b1576176233f`), `AscribeUserType` (`:1510`), and `FakeRead` (`:1518`).

| Transition | Declaration (`PlaceElem` / `AssertMessage`) | Exact Schema Mutation (`-` Removed / `+` Added) | `PostCleanup` Reachable? | Causal `rust-lang/rust` Commit SHA(s) |
| :--- | :--- | :--- | :---: | :--- |
| `1.78.0 -> 1.79.0` | `Body` | `+mentioned_items: Vec<Spanned<MentionedItem<'tcx>>>` | No (meta) | `339f4be04627f192ba29c33ab2251a582241a112` |
| | `StatementKind` | `Coverage(Box<Coverage>)` $\to$ `Coverage(CoverageKind)` | No (coverage) | `ab92699f4a4bce54675012112693e9919ab19f54` |
| | `CastKind` | `PointerExposeAddress` / `PointerFromExposedAddress` $\to$ `PointerExposeProvenance` / `PointerWithExposedProvenance` | **Yes** (op) | `989660c3e6efc1c5eb2e822f68863df7d06cbcb4`, `038e7c6c38b9e1713fb258c783441bb0102b8492` |
| | `BinOp` | `+Cmp` (`22` $\to$ `23`) | **Yes** (op) | `3da115a93b782796e3d267266b4241e5258f1fef` |
| | `NullOp` | `UbCheck(UbKind)` $\to$ `UbChecks` | **Yes** (op) | `61775304200826b412f18fc87218161fb8a0dc5c` |
| `1.79.0 -> 1.80.0` | `Rvalue` | `-CheckedBinaryOp(BinOp, Box<(Operand, Operand)>)` (`15` $\to$ `14`) | **Yes** (op) | `95c0e5c6a86ca467b0fb7043bd56dee82418ac5f` |
| | `BinOp` | `+AddWithOverflow`, `+SubWithOverflow`, `+MulWithOverflow` (`23` $\to$ `26`) | **Yes** (op) | `95c0e5c6a86ca467b0fb7043bd56dee82418ac5f` |
| | `UnOp` | `+PtrMetadata` (`2` $\to$ `3`) | **Yes** (op) | `459ce3f6bb5d8827835ed9b9f916eb189420b38a` |
| `1.80.0 -> 1.81.0` | `Body` | `coverage_branch_info` $\to$ `coverage_info_hi` | No (meta) | `f095de4bf105e92b035a7cd64c34bcce56b7cb78` |
| | `TerminatorKind` | `Call.args` & `InlineAsm.{operands,targets}` `Vec` $\to$ `Box<[_]>`; `+TailCall` (`14` $\to$ `15`) | **Yes** (op) | `b28efb11af6c3aea1117df81df9fc6ddf5b88077`, `484152d562f6babaacb3fae08cc5f70ee550e9ee` |
| `1.81.0 -> 1.82.0` | `Body` | `required_consts` & `mentioned_items` wrapped in `Option<Vec<..>>` | No (meta) | `6d312d7bd17598153c018e4879ccaa657eb48853` |
| | `Rvalue` | `AddressOf(Mutability, Place)` $\to$ `RawPtr(Mutability, Place)` | **Yes** (op) | `35709be02d43b40e7f720408f8a88bf6e9d5501d` |
| `1.82.0 -> 1.83.0` | `TerminatorKind` | `InlineAsm` gained `asm_macro: InlineAsmMacro` | **Yes** (op) | `5fc60d1e52ea12f53d2c8d22fee94592860739ad` |
| | `CastKind` | `-DynStar`; `PointerCoercion(PointerCoercion)` $\to$ `PointerCoercion(PointerCoercion, CoercionSource)` (`11` $\to$ `10`) | **Yes** (op) | `46ecb23198fa83136a266cb5a18675d2d342ab18`, `bd31e3ed70b75e5936880b18f6b5d1c8f5ee344f` |
| `1.83.0 -> 1.84.0` | `StatementKind` | `+BackwardIncompatibleDropHint { place, reason }` (`13` $\to$ `14`) | No (`CleanupPostBorrowck`) | `297b618944d4619a1990b1992d9142c6cf893dc6` |
| `1.85.0 -> 1.86.0` | `Rvalue` | `RawPtr(Mutability, ..)` $\to$ `RawPtr(RawPtrKind, ..)`; `+WrapUnsafeBinder(Operand, Ty)` (`14` $\to$ `15`) | **Yes** (op) | `eeecb56b7301c1bf1cf221c65e857b756b9ab42b`, `fc1a9186dcdad111fd99ddd38bd961a8a205c380` |
| | `ProjectionElem` (`PlaceElem`) | `+UnwrapUnsafeBinder(T)` (`8` $\to$ `9`) | **Yes** (op) | `fc1a9186dcdad111fd99ddd38bd961a8a205c380` |
| | `NullOp` | `+ContractChecks` (`4` $\to$ `5`) | **Yes** (op) | `bcb8565f301b579dee60fffe87d5a329cc69fefa` |
| | `AssertKind` (`AssertMessage`) | `+NullPointerDereference` (`8` $\to$ `9`) | **Yes** (op) | `b151b513ba2b65c7506ec1a80f2712bbd09154d1` |
| `1.87.0 -> 1.88.0` | `TerminatorKind` | `Drop` gained `drop: Option<BasicBlock>, async_fut: Option<Local>` | **Yes** (op) | `c366756a8537ef998d32c1ef57098d5aae7ca92f` |
| | `AssertKind` (`AssertMessage`) | `+ResumedAfterDrop(CoroutineKind)` (`9` $\to$ `10`) | **Yes** (op) | `c366756a8537ef998d32c1ef57098d5aae7ca92f` |
| `1.89.0 -> 1.90.0` | `AssertKind` (`AssertMessage`) | `+InvalidEnumConstruction(O)` (`10` $\to$ `11`); `Statement`/`BasicBlockData` marked `#[non_exhaustive]` | **Yes** (op) | `1087042e22ae3d14ff856f621a84eaa3e15cc537`, `90e0835004b2ec6dc596bbecf65eb49f49c01e7f` |
| `1.91.0 -> 1.92.0` | `BasicBlockData` | `+after_last_stmt_debuginfos: StmtDebugInfos<'tcx>` | No (debuginfo) | `8da04285cf6fe61587e16155a8b224dba64bf0be` |
| | `StatementKind` | `-Deinit(Box<Place<'tcx>>)` (`14` $\to$ `13`) | **Yes** (op) | `b7c2b3dc80e03dbbde6ff869c1f975c036703590` |
| | `Rvalue` | `-Len(Place<'tcx>)` (`15` $\to$ `14`) | **Yes** (op) | `53b91ea87fe4b430c33bd22dfdaaa6289bf9466a` |
| | `ProjectionElem` (`PlaceElem`) | `-Subtype(T)` (`9` $\to$ `8`) | **Yes** (op) | `aa5a21450a070fdea66a07d3cab3b69e6735c328` |
| | `CastKind` | `+Subtype` (`10` $\to$ `11`) | **Yes** (op) | `aa5a21450a070fdea66a07d3cab3b69e6735c328` |
| `1.92.0 -> 1.93.0` | `Rvalue` | `NullaryOp(NullOp<'tcx>, Ty<'tcx>)` $\to$ `NullaryOp(NullOp)` | **Yes** (op) | `72444372ae6900792ae53bec89c2ab442d589a71`, `2e5d395f2bfdedfda6bddc4797fbd4c04711efde` |
| | `NullOp` | `-SizeOf`, `-AlignOf`, `-OffsetOf`, `-UbChecks`, `-ContractChecks` $\to$ `RuntimeChecks(RuntimeChecks)` | **Yes** (op) | `72444372ae6900792ae53bec89c2ab442d589a71`, `2e5d395f2bfdedfda6bddc4797fbd4c04711efde` |
| | `RuntimeChecks` | Added enum `{ UbChecks, ContractChecks, OverflowChecks }` | **Yes** (op) | `cc8b95cc5490552e7080ec4e98c19249b47dac3a`, `2e5d395f2bfdedfda6bddc4797fbd4c04711efde` |
| `1.93.0 -> 1.94.0` | `Rvalue` | `-NullaryOp(NullOp)` (`14` $\to$ `13`) | **Yes** (op) | `1a227bd47ff200975f4afb287ec725861ab8b87a`, `6319bee585561a078de4a0f8d07d567ce69cf12c` |
| | `Operand` | `+RuntimeChecks(RuntimeChecks)` (`3` $\to$ `4`) | **Yes** (op) | `6319bee585561a078de4a0f8d07d567ce69cf12c` |
| | `NullOp` | Removed enum `NullOp` | **Yes** (op) | `6319bee585561a078de4a0f8d07d567ce69cf12c` |
| `1.94.0 -> 1.95.0` | `Rvalue` | `-ShallowInitBox(Operand<'tcx>, Ty<'tcx>)` (`13` $\to$ `12`) | **Yes** (op) | `6d4b1b38e76c0858c8e98f89afa37535261749ca` |
| `1.96.0 -> 1.97.0` | `StatementKind` | `-Retag(RetagKind, Box<Place<'tcx>>)` (`13` $\to$ `12`) | **Yes** (op) | `e402c1edf047a23b0cfef40c6097d1caa294050b` |
| | `Rvalue` | `Use(Operand)` $\to$ `Use(Operand, WithRetag)`; `+Reborrow(Ty, Mutability, Place)` | **Yes** (op) | `e402c1edf047a23b0cfef40c6097d1caa294050b`, `2d88ee87ddaa584a19e438528f60f825f735076a` |
| | `RetagKind` | Removed enum `RetagKind` | **Yes** (op) | `e402c1edf047a23b0cfef40c6097d1caa294050b` |
| | `WithRetag` | Added enum `WithRetag { Yes, No }` | **Yes** (op) | `e402c1edf047a23b0cfef40c6097d1caa294050b` |
| `1.97.0 -> 1.98.0` | `TerminatorKind` | `Drop` removed `async_fut: Option<Local>` (expanded during drop elaboration) | **Yes** (field-only) | `a27155e69172af4cddde6b5c5c6cc9d627d6fcc3`, `30782fc2a228a65773ec6c9665c8de63072ac0d9` |
| `1.98.0 -> 1.99.0` | `CastKind` | `+BoxDerefTransmute` (`11` $\to$ `12`) | **Yes** (op) | `fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f` |
| | `AssertKind` (`AssertMessage`) | `+NullReferenceConstructed` (`11` $\to$ `12`) | **Yes** (op) | `1a982425b6699f2b26552c6b44cc979a3d84543b` |
| `1.99.0 -> 1.100.0` | `Body` | `coverage_info_hi` / `function_coverage_info` $\to$ `coverage_{early,mir}_info` | No (meta) | `0bce0415d5545614f99c0c27244f5f46aa1269a7` |
| | `ProjectionElem` (`PlaceElem`) | `+PhantomDeref` (`8` $\to$ `9`) | No (post-borrowck ICE) | `5686e563774cd9e8bfba79d3ab1167fe198e9e78` |
| `1.100.0 -> 1.102.0-nightly` | `TerminatorKind` | `Goto { target }` $\to$ `Goto { target, loop_hint_attrs: ThinVec<UnrollAttr> }` | **Yes** (field-only) | `ec45ecffeee8ba13e42a7f45b6cdad3155ebd146` |

#### 1.4 Tier C: Genuine Runtime Operational Semantics Deltas (`16` Transitions Out of `591` Commits)

`Basis: source + derived (audit of 591 non-merge commits across compiler/rustc_const_eval/src/interpret/{step,operand,place,operator,cast,terminator,memory,validity,intrinsics}.rs, library/core/src/convert/mod.rs, and library/alloc/src/boxed.rs)`

Inspecting all `591` non-merge commits touching `rustc_const_eval::interpret` and core/alloc primitive wrappers across `1.78.0` $\to$ `1.102.0-nightly` shows that **`575` (`97.29%`)** are internal compiler engineering refactors (diagnostic formatting, tracing spans, `InterpResult` wrappers, lifetime elision) with zero operational runtime MIR effect. Exactly **`16` transitions (`0.696`/release)** alter runtime MIR operational meaning:

| ID (`tier4_semantic_deltas`) | Transition | Semantic Category | Operational Runtime MIR Meaning Change | Verified Causal `rust-lang/rust` Commit SHA(s) |
| :--- | :--- | :--- | :--- | :--- |
| `T4-01` | `1.78.0 -> 1.79.0` | Operators & Provenance | Added 3-way integer `BinOp::Cmp` (`Ordering` `-1`/`0`/`+1`), provenance-exposing cast semantics (`PointerExposeProvenance` / `PointerWithExposedProvenance`), and unified `UbChecks` | `3da115a93b782796e3d267266b4241e5258f1fef`, `989660c3e6efc1c5eb2e822f68863df7d06cbcb4`, `61775304200826b412f18fc87218161fb8a0dc5c` |
| `T4-02` | `1.79.0 -> 1.80.0` | Pointer Offset & `Drop` | Folded `CheckedBinaryOp` into `BinOp::*WithOverflow`; added `UnOp::PtrMetadata`; permitted `0`-byte `offset`/`offset_from` on arbitrary null/dangling pointers; `TerminatorKind::Drop` unconditionally evaluates `place` even when the type lacks drop glue | `95c0e5c6a86ca467b0fb7043bd56dee82418ac5f`, `459ce3f6bb5d8827835ed9b9f916eb189420b38a`, `5c33a5690de89587b645fb0e7b657fe545e4d0e8`, `86a933a5743afe4117fdde5bdf04ba1baa634715` |
| `T4-03` | `1.80.0 -> 1.81.0` | **`StorageLive` UB Removal** & Shifts | **`StorageLive(local)` on an already-live local changed from immediate UB to storage refresh** (deallocating old storage and allocating fresh `Uninit` storage); negative signed shift counts defined via `rem_euclid`; `offset_from` permitted on equal-address pointers across distinct allocations; `TerminatorKind::TailCall` frame replacement | `9b05e154f39f1a413ebc09c8f1dd751f991b3bba`, `669a40006bf3494b0d320fb77bf39cc19a6c5bc4`, `f6c377c350d7946881449daac2039a09b1734b46`, `484152d562f6babaacb3fae08cc5f70ee550e9ee` |
| `T4-04` | `1.81.0 -> 1.82.0` | `raw_eq` Provenance & `UbChecks` | `raw_eq` on bytes carrying pointer provenance relaxed from runtime UB to defined (still rejected in CTFE), while enforcing alignment checks; `UbChecks` evaluated per defining crate rather than root crate | `f97aba2271baf1876940b42cc68f1b60ac97bf98`, `e17be955bbd5c0fa6e95805a2cb96946262cd75b`, `7ea2981605ef13f713f42e877c4c31b059cb1ebe` |
| `T4-05` | `1.82.0 -> 1.83.0` | Typed Copy Provenance Stripping | Typed MIR copies strip pointer provenance (`reset_provenance`) on non-pointer scalar subfields and reset padding during validation; `Box<ZST>` validity updated for zero-sized allocation rules | `cbdcbf0d6a586792c5e0a0b8965a3179bac56120`, `8cd982caa1221c54dbdb036083d659c619024d45`, `05ffd446a9b2d2c67c450bea4180eb4790939e07` |
| `T4-06` | `1.84.0 -> 1.85.0` | Non-Overlapping Swap UB | `typed_swap_nonoverlapping` enforces aliasing/overlap UB checks even on scalar immediate locals (closing an unsound non-memory scalar fast path) | `335f7f59c1a4ffa0483f936a905b25f2f58c0263` |
| `T4-07` | `1.85.0 -> 1.86.0` | Float NaN & Unsafe Binders | Operational `f32`/`f64` `minnum`/`maxnum` NaN sign/payload made non-deterministic; `WrapUnsafeBinder`/`UnwrapUnsafeBinder` operational rules added; slice indexing lowered via `PtrMetadata` | `d98270b07a04178b019d8317d146eb3dd1afface`, `fc1a9186dcdad111fd99ddd38bd961a8a205c380`, `057313b7a607513d6c1aa82e454e2370025f3b9a` |
| `T4-08` | `1.90.0 -> 1.91.0` | Call `Move` Aliasing UB | Passing identical/overlapping locals as multiple in-place `Operand::Move` call arguments or aliasing a `Move` argument with `destination` made UB (`interpret/step.rs:465-486`); function allocations stripped of spurious alignment | `ece1397e3ff40e7f8a411981844a8214659da970`, `7dfbc0ac1435b76bce4b6baf1ce1b3f7080538e1`, `78bdd86c676a4e08849677c351591db3564d87e8`, `f554c79ef819cbc0f9983d0d5306cd7a9bfea6d8` |
| `T4-09` | `1.91.0 -> 1.92.0` | `-Deinit`, `-Len`, & Aggregates | Eliminated `StatementKind::Deinit` and `Rvalue::Len` from runtime MIR; fixed overlapping aggregate field initialization; moved `Subtype` from `ProjectionElem` to `CastKind` | `b7c2b3dc80e03dbbde6ff869c1f975c036703590`, `53b91ea87fe4b430c33bd22dfdaaa6289bf9466a`, `8ecda4b7f866d77d4a87c5b5bc601d4078841093`, `aa5a21450a070fdea66a07d3cab3b69e6735c328` |
| `T4-10` | `1.92.0 -> 1.93.0` | `OffsetOf` & `ScalarPair` Padding | Replaced `NullOp::OffsetOf` with explicit compile-time constant sums; writing a `ScalarPair` resets uninitialized padding across the entire destination byte range | `72444372ae6900792ae53bec89c2ab442d589a71`, `324e47ba2b3d2f211e4125d0b6c8fe3ceee35e91` |
| `T4-11` | `1.93.0 -> 1.94.0` | `Operand::RuntimeChecks` | Eliminated `Rvalue::NullaryOp`; moved crate-session `UbChecks`/`ContractChecks`/`OverflowChecks` evaluation to `Operand::RuntimeChecks` (`step.rs:419`) | `1a227bd47ff200975f4afb287ec725861ab8b87a`, `6319bee585561a078de4a0f8d07d567ce69cf12c` |
| `T4-12` | `1.94.0 -> 1.95.0` | `Box` Init & Padding Copies | Removed `Rvalue::ShallowInitBox` in favor of `write_via_move` / `write_box_via_move` intrinsics; forced byte-preserving mem-to-mem copies whenever type layout contains padding | `6d4b1b38e76c0858c8e98f89afa37535261749ca`, `93d45480aa6db1009ebf67b845d8e9b995f46f56`, `635bacf46627409cb4569b93d38bdf23282966f3` |
| `T4-13` | `1.96.0 -> 1.97.0` | **Implicit Copy Retagging (`WithRetag`)** | Deleted `StatementKind::Retag`; `StatementKind::Assign` with `Rvalue::Use(op, WithRetag::Yes)` implicitly retags references/boxes under Stacked/Tree Borrows unless suppressed via `WithRetag::No` | `e402c1edf047a23b0cfef40c6097d1caa294050b`, `c6befd82cea3ce6322ec7384c10cdfe9dd2fd957` |
| `T4-14` | `1.98.0 -> 1.99.0` | **`Call` Eval Order Flip & `BoxDerefTransmute`** | **`TerminatorKind::Call` operational order flipped to evaluate `destination` place BEFORE `func` and `args`** (`step.rs:601-605`); `CastKind::BoxDerefTransmute` makes invalid-`Box<T>` deref casts immediate UB; cast inputs and dereferenced pointers validated | `752a91064f4297df39b7215bd9ba30bdd8145661`, `fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f`, `b3724b650ef1fc5fcdf348e4077e68715596f888`, `14d28b13c77ecc83458f26cfff5cd4b56b852d29` |
| `T4-15` | `1.99.0 -> 1.100.0` | **`!` Stabilization & `Infallible = !`** | Stabilized `!` (`!`-fallback across all editions) and aliased `core::convert::Infallible = !`, flipping observable runtime `TypeId::of::<Infallible>() == TypeId::of::<!>()` from `false` (`<= 1.99.1`) to `true` (`1.100.0+`) | `cfc82ebbfc6098a18fa09457e6f966cc237577bb`, `e7769602aca3770e8d8ea55716becb22e839a579`, `dd132214ed3e2415da4292fec21f564f4496baa5` |
| `T4-16` | `1.100.0 -> 1.102.0-nightly` | Union Padding, `copy_nonoverlapping`, & `BoxRaw` | Newly constructed unions reset padding bytes to `Uninit`; `copy_nonoverlapping` checks overlap even when `src` is fully `Uninit`; `write_bytes` checks alignment; `InlineAsm` evaluates destination places before inputs; `Box<T>.0` changed from `Unique<T>` to `BoxRaw<T>` | `e7007d3aaaa6a6ca1bcd95f1f10c9411693a3628`, `50871c88373cb15c35226246bcbee10ce5712691`, `50031dfd7825adc0da3918230a141971ac578bf7`, `834e5b6caa3a365dc242d61425308c25b3af9b5e`, `5d260fd3da7b0165d6365adab12746bfc389d913` |

#### 1.5 Tier D: Why Trunk Canonicalization Absorbs Lowering-Only Shifts While Semantic Shifts Map to Explicit Dialect Flags

`Basis: source + derived`

Comparing Tiers A–C against downstream crate lowering establishes a strict soundness boundary between **trunk canonicalization** and **semantic dialect parameterization**:

1. **Syntax-only and lowering-only splits absorbed by a monotonic superset trunk IR:**
   - *AST surface reorganizations with identical runtime meaning:* `Rvalue::CheckedBinaryOp(op, a, b)` (`1.79.0`) and `Rvalue::BinaryOp(op_with_overflow, a, b)` (`1.80.0+`) denote identical checked arithmetic tuples; `Rvalue::AddressOf` (`1.81.0`) and `Rvalue::RawPtr` (`1.82.0+`) denote identical raw-pointer formation; `Scalar::Ptr(_, sz: u8)` (`<= 1.99.1`) and `Scalar::Ptr(_, nz_sz: NonZero<u8>)` (`1.100.0+`) carry the exact same byte width; `LayoutData.align.abi` (`<= 1.100.0`) and `LayoutData.align` (`1.102.0-nightly`) yield identical ABI alignment; and `TerminatorKind::Goto { target, loop_hint_attrs }` carries zero operational effect in `interpret/step.rs:563`.
   - *Pre-runtime pass normalization:* Because `CleanupPostBorrowck` rewrites `StatementKind::BackwardIncompatibleDropHint` to `StatementKind::Nop` before `Runtime(PostCleanup)` (`cleanup_post_borrowck.rs:36`), edition-2024 temporary-drop migration hints vanish prior to capture, keeping `Runtime(PostCleanup)` MIR edition-independent.
   - *Stdlib private wrapper and derive refactors:* Changes such as `AtomicU*` becoming type aliases of `core::sync::atomic::Atomic<T>` (`fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`), `Box<T>.0` switching from `Unique<T>` to `BoxRaw<T>` (`5d260fd3da7b0165d6365adab12746bfc389d913`), or `#[derive(Debug)]` concatenating field-name literals (`4719edece749ef683e8971e6e08fd643744a82d0`) alter `DefId`s and private struct shells without changing the normative specifications of uninlined `core`/`alloc` operations when lowered via `TyAndLayout` and opaque lang/intrinsic contracts.
2. **Operational semantic transitions requiring explicit dialect flags:**
   - Conversely, a syntax adapter must **never** silently collapse `Rvalue::Use(op)` (`<= 1.96.0`, where retags lived only in explicit `StatementKind::Retag` statements when `-Z mir-emit-retag` was enabled) and `Rvalue::Use(op, WithRetag::Yes | No)` (`1.97.0+`, where reference/box copies retag implicitly unless `WithRetag::No`) into an unparameterized trunk `Use(op)` once reference provenance is modeled. Likewise, `StorageLive` on a live local (`T4-03`: UB $\to$ storage refresh), `Move` call-argument aliasing (`T4-08`: defined $\to$ UB), `TerminatorKind::Call` destination-before-arguments evaluation order (`T4-14`), and `Infallible = !` (`T4-15`) change the set of safe executions and must bind to explicit `MirSemantics` capability flags (or fail closed to `.unsupported` on affected constructs).

---

### 2. Evaluation and Disqualification of In-Source Compiler-Detection Mechanisms

#### 2.1 `#![feature(cfg_version)]` (`#[cfg(version("..."))]`): Spoofing, Suffix Erasure, and Mid-Cycle Nightly Crashes

`Basis: source + execution (compiler/rustc_attr_parsing/src/attributes/{util.rs:16-27, cfg.rs:125-147, 270-285}, compiler/rustc_ast/src/attr/version.rs:8-48 at 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1; support/probe_mir_scaling_and_cfg_matrix.json)`

1. **Primary-source mechanism:**
   In `compiler/rustc_ast/src/attr/version.rs:8-48`, `#[cfg(version("..."))]` compares the parsed literal (`<major>.<minor>[.<patch>]`; any `-nightly` or `-dev` suffix inside the attribute literal is rejected by `parse_version` in `util.rs:16-27`, evaluating to `false` with `unknown_version_literal`) against `RustcVersion::current_overridable()`:
   ```rust
   pub fn current_overridable() -> Self {
       *CURRENT_OVERRIDABLE.get_or_init(|| {
           if let Ok(override_var) = std::env::var("RUSTC_OVERRIDE_VERSION_STRING")
               && let Some(override_) = Self::parse_str(&override_var)
           {
               override_
           } else {
               Self::CURRENT
           }
       })
   }
   fn parse_str(value: &str) -> Option<Self> {
       let mut components = value.split('-').next().unwrap().splitn(3, '.');
       ...
   }
   ```
   In `compiler/rustc_attr_parsing/src/attributes/cfg.rs:270-285`, `rustc` evaluates `RustcVersion::current_overridable() > *min_version` when `-Z assume-incomplete-release` is passed, and `>= *min_version` otherwise. Because both `CURRENT` (`current_rustc_version!()`) and `parse_str` split on `'-'` and discard all pre-release suffixes, `"1.100.0-nightly"`, `"1.100.0-dev"`, `"1.100.0-beta.1"`, and `"1.100.0"` collapse to the identical `RustcVersion { major: 1, minor: 100, patch: 0 }`.

2. **Live 14-toolchain + 4-override truth table (`[real measurement]`):**

| Toolchain / Environment Condition | `rustc -V` Headline | `1.78` | `1.84` | `1.95` | `1.97` | `1.99.1` | `1.100` | `1.100.0` | `1.102` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `1.78.0` (`9b00956e5...`) | `rustc 1.78.0 (9b00956e5 2024-04-29)` | `true` | `false` | `false` | `false` | `false` | `false` | `false` | `false` |
| `1.80.1` (`3f5fd8dd4...`) | `rustc 1.80.1 (3f5fd8dd4 2024-08-06)` | `true` | `false` | `false` | `false` | `false` | `false` | `false` | `false` |
| `1.84.0` (`9fc6b4312...`) | `rustc 1.84.0 (9fc6b4312 2025-01-07)` | `true` | `true` | `false` | `false` | `false` | `false` | `false` | `false` |
| `1.93.1` (`01f6ddf75...`) | `rustc 1.93.1 (01f6ddf75 2026-02-11)` | `true` | `true` | `false` | `false` | `false` | `false` | `false` | `false` |
| `1.96.0` (`ac68faa20...`) | `rustc 1.96.0 (ac68faa20 2026-05-25)` | `true` | `true` | `true` | `false` | `false` | `false` | `false` | `false` |
| `1.99.1` (`58cf8f9c3...`) | `rustc 1.99.1 (58cf8f9c3 2026-10-13)` | `true` | `true` | `true` | `true` | `true` | `false` | `false` | `false` |
| `1.100.0` / `stable` (`0ef1bc386...`) | `rustc 1.100.0 (0ef1bc386 2026-11-09)` | `true` | `true` | `true` | `true` | `true` | `true` | `true` | `false` |
| **`stage1` (custom `-dev` build)** | **`rustc 1.100.0-dev`** | `true` | `true` | `true` | `true` | `true` | **`true`** | **`true`** | `false` |
| `nightly-2026-02-07` (`efc9e1b50...`, pre-`-ShallowInitBox`) | `rustc 1.95.0-nightly (efc9e1b50 2026-02-06)` | `true` | `true` | **`true`** | `false` | `false` | `false` | `false` | `false` |
| `nightly-2026-02-23` (`c78a29473...`, post-`-ShallowInitBox`) | `rustc 1.95.0-nightly (c78a29473 2026-02-22)` | `true` | `true` | **`true`** | `false` | `false` | `false` | `false` | `false` |
| **`nightly-2026-04-12` (`bf4fbfb7a...`, pre-`WithRetag`)** | `rustc 1.97.0-nightly (bf4fbfb7a 2026-04-11)` | `true` | `true` | `true` | **`true`** | `false` | `false` | `false` | `false` |
| `nightly` / `nightly-2026-11-20` (`3ef0c22cd...` / `6905905bb...`) | `rustc 1.102.0-nightly` | `true` | `true` | `true` | `true` | `true` | `true` | `true` | **`true`** |
| **`1.100.0` + `RUSTC_OVERRIDE_VERSION_STRING="1.78.0-custom"`** | `rustc 1.78.0-custom` | `true` | **`false`** | **`false`** | **`false`** | **`false`** | **`false`** | **`false`** | `false` |
| **`1.100.0` + `RUSTC_OVERRIDE_VERSION_STRING="1.999.0"`** | `rustc 1.999.0` | `true` | `true` | `true` | `true` | `true` | `true` | `true` | **`true`** |
| **`1.100.0` + `RUSTC_OVERRIDE_VERSION_STRING="0.0.0"`** | `rustc 0.0.0` | **`false`** | **`false`** | **`false`** | **`false`** | **`false`** | **`false`** | **`false`** | `false` |
| **`1.100.0` + `RUSTC_OVERRIDE_VERSION_STRING="non-semver-custom"`** | `rustc non-semver-custom` (fallback to `CURRENT`) | `true` | `true` | `true` | `true` | `true` | `true` | `true` | `false` |

3. **Bidirectional mid-cycle nightly impossibility proof (`[real measurement]`):**
   - *Default `>=` crashes on pre-break nightlies (`E0023`):* `Rvalue::Use(Operand, WithRetag)` landed in the `1.97` cycle on `2026-05-02` (`e402c1edf047a23b0cfef40c6097d1caa294050b`). Gating `#[cfg(version("1.97"))] Rvalue::Use(op, _retag)` compiles (`rc = 0`) on `1.95.0-nightly` (`efc9e1b50...`) and `1.98.0-nightly` (`f8a08b688...`), but **aborts (`rc = 1`)** on `1.97.0-nightly (bf4fbfb7a 2026-04-11)` with `error[E0023]: this pattern has 2 fields, but the corresponding tuple variant has 1 field`.
   - *`-Z assume-incomplete-release` (`>`) counter-crashes on post-break nightlies (`E0425`):* Gating `#[cfg(version("1.102"))] rustc_driver::compiler_entrypoint(args, cb)` (`c39fbc44eb0f296a7ad161eee642e8bcd2a82235`, `2026-10-02`) compiles (`rc = 0`) under default flags on `1.102.0-nightly (3ef0c22cd 2026-11-11)`, but passing `-Z assume-incomplete-release` flips `version("1.102")` to `false` and **aborts (`rc = 1`)** with `error[E0425]: cannot find function run_compiler in crate rustc_driver`. No global `cfg(version)` mode can separate pre-break and post-break commits sharing a minor version number.

#### 2.2 `#![feature(cfg_accessible)]` (`#[cfg_accessible(path)]`): Asymmetric Enum-Variant Trap and Resolver Failures

`Basis: source + execution (compiler/rustc_builtin_macros/src/cfg_accessible.rs:36-69, compiler/rustc_resolve/src/macros.rs:524-530, 1272-1311 at 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1; support/probe_mir_scaling_and_cfg_matrix.json)`

1. **Primary-source mechanism and asymmetric cross-version trap:**
   `#[cfg_accessible(path)]` is registered as an active `MultiItemModifier` macro—not a `cfg(...)` predicate—delegating to `Resolver::path_accessible` (`compiler/rustc_resolve/src/macros.rs:1272-1311`):
   ```rust
   match self.cm().maybe_resolve_path(path, Some(*ns), &parent_scope, None) {
       PathResult::Module(ModuleOrUniformRoot::Module(_)) => return Ok(true),
       PathResult::NonModule(partial_res) if partial_res.unresolved_segments() == 0 => {
           return Ok(true);
       }
       PathResult::NonModule(..) |
       PathResult::Failed { is_error_from_last_segment: false, .. } => {
           self.dcx().emit_err(diagnostics::CfgAccessibleUnsure { span });
           return Ok(false);
       }
       PathResult::Indeterminate => indeterminate = true,
       PathResult::Failed { .. } => {}
       PathResult::Module(_) => panic!("unexpected path resolution"),
   }
   ```
   Lines `1286–1294` create an **asymmetric cross-version trap** whenever an author gates an added or removed enum variant:
   - On a compiler where the variant **exists** (`CastKind::BoxDerefTransmute` on `1.99.1+`, `ProjectionElem::PhantomDeref` on `1.100.0+`, `StatementKind::Retag` on `1.94.1`, or in-crate `LocalEnum::Present`), `maybe_resolve_path` resolves all segments (`unresolved_segments() == 0`) and returns `Ok(true)` (`rc = 0`), falsely appearing to support enum-variant probing.
   - On any compiler where that variant is **absent** (`BoxDerefTransmute` on `1.94.1` or `1.98.0-nightly`, `PhantomDeref` on `1.98.0-nightly` or `1.99.1`, or removed `StatementKind::Retag` on `1.98.0-nightly`, `1.100.0`, and `1.102.0-nightly`), `maybe_resolve_path` resolves the parent enum as `DefKind::Enum` (`PathResult::NonModule`) with `unresolved_segments() == 1` (because early expansion cannot rule out a later inherent `impl Enum { const Variant: ... }` block) and **aborts compilation with a hard error** (`CfgAccessibleUnsure`: `error: not sure whether the path is accessible or not`)—even when wrapped in the glob-shadowing fallback pattern (`mod fallback { pub const PRESENT: bool = false; } mod probe { pub use super::fallback::*; #[cfg_accessible(...)] pub const PRESENT: bool = true; }`).

2. **Live empirical `cfg_accessible` matrix across `5` `rustc-dev` compilers (`[real measurement]`):**

| Probe Case | `1.94.1` (`e408947bf`) | `1.98.0-nightly` (`f8a08b688`) | `1.99.1` (`58cf8f9c3`) | `1.100.0` (`0ef1bc386`) | `1.102.0-nightly` (`3ef0c22cd`) | Observed `rustc` Outcome & Diagnostic |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `#[cfg_accessible(rustc_abi::TyAndLayout)]` / `rustc_abi::Size` (module type) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | `rc=0` | Succeeds (`Ok(true)`) across all tested compilers |
| `#[cfg_accessible(rustc_driver::compiler_entrypoint)]` (top-level fn + glob fallback) | `rc=0` (`false`) | `rc=0` (`false`) | `rc=0` (stripped) | `rc=0` (`false`) | `rc=0` (`true`) | Cleanly strips item (`Ok(false)`) on `<= 1.100.0` and keeps on `1.102.0-nightly` |
| `#[cfg_accessible(StatementKind::Retag)]` (variant removed in `1.97`) | `rc=0` (`true`) | **`rc=1` FAIL** | — | **`rc=1` FAIL** | **`rc=1` FAIL** | **Asymmetric trap:** `error: not sure whether the path is accessible or not` on `>= 1.98.0-nightly` |
| `#[cfg_accessible(CastKind::BoxDerefTransmute)]` (variant added in `1.99`) | **`rc=1` FAIL** | **`rc=1` FAIL** | `rc=0` | `rc=0` (`true`) | `rc=0` (`true`) | **Asymmetric trap:** `error: not sure whether the path is accessible or not` on `1.94.1` & `1.98.0-nightly` |
| `#[cfg_accessible(ProjectionElem::PhantomDeref)]` (variant added in `1.100`) | — | **`rc=1` FAIL** | **`rc=1` FAIL** | `rc=0` | `rc=0` | **Asymmetric trap:** `error: not sure whether the path is accessible or not` on `1.98.0-nightly` & `1.99.1` |
| `#[cfg_accessible(LocalEnum::Present)]` (present same-crate variant) | — | `rc=0` | `rc=0` | `rc=0` | `rc=0` | `unresolved_segments() == 0` succeeds only while variant exists |
| `#[cfg_accessible(rustc_middle::nonexistent_submodule::Item)]` (missing parent module) | — | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | `is_error_from_last_segment: false` $\to$ `CfgAccessibleUnsure` |
| `#[cfg_accessible(MyStruct::field)]` (struct field) | — | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | `CfgAccessibleUnsure` across all compilers |
| `#[cfg_accessible(TerminatorKind::Goto::loop_hint_attrs)]` (enum variant field) | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | `CfgAccessibleUnsure` even on `1.102.0-nightly` where field exists |
| `#[cfg_accessible(TyCtxt::mir_drops_elaborated_and_const_checked)]` (inherent method) | — | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | `CfgAccessibleUnsure` across all compilers |
| `#[cfg(not(cfg_accessible(...)))]` (negation / `else` branch) | **`rc=1` (`E0537`)** | **`rc=1` (`E0537`)** | **`rc=1` (`E0539`)** | **`rc=1` (`E0539`)** | **`rc=1` (`E0539`)** | `invalid predicate cfg_accessible` (`<= 1.98`) / `malformed cfg attribute input` (`>= 1.99.1`) |
| `#[cfg_accessible(...)]` on `match` arm | — | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | **`rc=1` FAIL** | `error: expected non-macro attribute, found attribute macro cfg_accessible` |

#### 2.3 `#[rustversion]` (`dtolnay/rustversion` `1.0.23`) and Four-Mechanism Comparison

`Basis: source + derived (dtolnay/rustversion@3a7c76605450b9a7299c6502a421909de9126a59: Cargo.toml:5, 14-15, build/build.rs:21-46, 80-86, 100-103, build/rustc.rs:47-90, src/bound.rs:33-62, src/expr.rs:24-50)`

Primary-source inspection of `dtolnay/rustversion` `1.0.23` (`3a7c76605450b9a7299c6502a421909de9126a59`) establishes four structural reasons why `#[rustversion]` is inferior to launcher-probed `--cfg` dialect/capability flags for a TCB MIR-capture driver:

1. **Dual `build.rs` + host `proc-macro` build-graph requirement (`Cargo.toml:5, 14-15`, `build/build.rs:21-46, 100-103`):** `rustversion` executes a `build.rs` script that spawns `$RUSTC --version` (`Command::new`) to write `$OUT_DIR/version.expr`, and then compiles and dlopens a host `proc-macro` shared library (`proc-macro = true`). It cannot be used in a zero-`build.rs`, zero-external-dependency direct-`rustc` TCB build, and `$RUSTC --version` inherits ambient `RUSTC_OVERRIDE_VERSION_STRING` spoofing.
2. **Commit-hash erasure and `Channel::Dev` / custom-channel hazards (`build/rustc.rs:60-83`):** `parse_words` discards the `(commit_hash` token completely (`Some(hash) if hash.starts_with('(')`), retaining only `(minor, patch, Channel::Nightly(Date { year, month, day }))`. Multiple nightly or monorepo commits on the same UTC date are indistinguishable; `-dev` builds (`1.100.0-dev`) and date-less nightlies map to `Channel::Dev`, which `src/bound.rs:54` orders strictly **greater** than every `Bound::Nightly(date)` (`Dev => Some(Ordering::Greater)`, falsely claiming future nightly APIs exist on older `-dev` builds); and custom channel suffixes (`1.100.0-custom`) return `None` at `build/rustc.rs:82`, aborting `build.rs` with `process::exit(1)` (`build/build.rs:85`).
3. **Cross-channel ordering trap (`src/bound.rs:48-62`):** `Bound::Nightly(date)` evaluates every `Stable` and `Beta` compiler as `Ordering::Less` (`false` even on `rustc 1.100.0` six months after `2026-05-02`), while `Bound::Stable(release)` compares `(self.minor, self.patch)` **ignoring `self.channel`** (`1.97.0-nightly` `2026-04-11` satisfies `since(1.97)`). Correctly gating a mid-cycle `rustc_private` break across nightlies and stable releases requires compound `#[rustversion::any(all(not(nightly), since(1.97)), since(2026-05-03))]` predicates at every call site (and `not(nightly)` is `false` on `Channel::Dev` per `src/expr.rs:30-31`).

| Criterion | `#![feature(cfg_version)]` | `#![feature(cfg_accessible)]` | `#[rustversion]` (`1.0.23`) | Launcher `--cfg` Dialect / Capability Flags |
| :--- | :--- | :--- | :--- | :--- |
| **Requires `build.rs` or host `proc-macro`?** | No | No | **Yes (`build.rs` + `proc-macro`)** | **No** (stable `--cfg` + `--check-cfg` since `1.80.0`) |
| **Extra unstable `#![feature(...)]`?** | Yes (`cfg_version`) | Yes (`cfg_accessible`) | No (unless on expressions/arms) | **None** (`#[cfg]`, `compile_error!`, `--check-cfg`) |
| **Enum variant & struct-field deltas?** | Stable boundaries only | **NO — `CfgAccessibleUnsure` hard error** | Verbose dual-bound `attr(..., cfg)` | **Yes (`100%`)** |
| **`not(...)` / exhaustive `else` / `match` arms?** | Yes | **NO** (`E0537`/`E0539` & macro-attr error) | Via `#[rustversion::attr(..., cfg)]` | **Yes (`100%`)** |
| **Mid-cycle nightly & same-day SHA precision?** | **BROKEN** (`E0023` / `E0425`) | **BROKEN** on variants/fields | Coarse `YYYY-MM-DD` (drops SHA) | **Exact (`100%`)** — keyed by exact `commit-hash` |
| **`RUSTC_OVERRIDE_VERSION_STRING` & `-dev` safety?** | **VULNERABLE** (spoofed + `-dev` stripped) | Immune to version string | **VULNERABLE** (`$RUSTC --version` + `Dev > Date`) | **100% Immune** — explicit CLI `--cfg` only |

---

### 3. Concrete `164`-LOC Zero-`build.rs` `--cfg` Dialect Adapter and Live Multi-Toolchain Matrices

`Basis: execution + source (support/probe_mir_scaling_and_cfg_matrix.py, support/probe_mir_scaling_and_cfg_matrix.json)`

#### 3.1 Narrow `dialect.rs` Boundary (`164` Non-Comment LOC = `13.67` LOC/Release)

Because a verified launcher already authenticates the compiler's `rustc -vV` `commit-hash` (or bundled archive `SHA-256`) before invoking compilation, passing `--cfg anneal_mir_dialect="<dialect>"` paired with `[lints.rust] unexpected_cfgs = { level = "deny", check-cfg = ['cfg(anneal_mir_dialect, values(...))'] }` and a crate-root `compile_error!` guard isolates `100%` of 12 minor cycles (`1.91.0-nightly`–`1.102.0-nightly`) of Tier-A and Tier-B drift inside a single leaf module `src/dialect.rs` (**`164` non-comment, non-blank LOC**, `177` total lines = **`13.67` LOC per minor release**, projecting linearly to **`~314` LOC** across all 24 revisions) while keeping `src/main.rs` (`139` non-comment LOC; `>90%` of a full capture emitter) completely `#[cfg]`-free:

```rust
// Crate-root fail-closed guard (`src/main.rs`, zero `#[cfg]` inside `CaptureCallbacks`):
#![feature(rustc_private)]
#![deny(unexpected_cfgs)]

#[cfg(not(any(
    anneal_mir_dialect = "mir_1_91_93",
    anneal_mir_dialect = "mir_1_94_96",
    anneal_mir_dialect = "mir_1_97_98",
    anneal_mir_dialect = "mir_1_99",
    anneal_mir_dialect = "mir_1_100",
    anneal_mir_dialect = "mir_1_102_nightly",
)))]
compile_error!("exactly one known `--cfg anneal_mir_dialect=\"...\"` must be passed");
```

The leaf `dialect.rs` module exposes nine normalized trunk-projection helpers covering every breaking API and AST delta across `1.91`–`1.102`:

1. `run_driver_and_exit(f: impl FnOnce()) -> std::process::ExitCode` — bridges `catch_with_exit_code` returning `i32` (`mir_1_91_93`) vs. `ExitCode` (`1.94.0+`).
2. `invoke_driver(args: &[String], callbacks: &mut (dyn Callbacks + Send))` — bridges `rustc_driver::run_compiler` (`<= 1.100.0`) vs. `rustc_driver::compiler_entrypoint` (`mir_1_102_nightly`; extendable to `RunCompiler::new(args, callbacks).run()` for `<= 1.85.0`).
3. `layout_abi_align_bytes<'tcx>(layout: &TyAndLayout<'tcx, Ty<'tcx>>) -> u64` — bridges `layout.align.abi.bytes()` (`<= 1.100.0`) vs. `layout.align.bytes()` (`mir_1_102_nightly`).
4. `scalar_ptr_size_bytes(scalar: Scalar) -> Option<u8>` — bridges `Scalar::Ptr(_, sz: u8)` (`<= 1.99.1`) vs. `Scalar::Ptr(_, nz_sz: NonZero<u8>)` (`1.100.0+`).
5. `extract_rvalue_use(rv: &Rvalue<'tcx>) -> Option<(&Operand<'tcx>, RetagMode)>` — maps `Rvalue::Use(op)` (`<= 1.96`, `RetagMode::LegacySeparateStmt`) and `Rvalue::Use(op, WithRetag::Yes | No)` (`1.97+`, `ImplicitYes` / `ExplicitNo`) without losing provenance-retag semantics.
6. `is_legacy_retag_stmt(kind: &StatementKind<'_>) -> bool` — matches `StatementKind::Retag(_, _)` on `<= 1.96` and returns `false` on `1.97+`.
7. `is_box_deref_transmute(ck: &CastKind) -> bool` — matches `CastKind::BoxDerefTransmute` on `1.99+` and returns `false` on `<= 1.98`.
8. `is_phantom_deref<V, T>(elem: &ProjectionElem<V, T>) -> bool` — matches `ProjectionElem::PhantomDeref` on `1.100+` (for explicit fail-closed assertions) and returns `false` on `<= 1.99`.
9. `classify_goto(term: &TerminatorKind<'_>) -> Option<GotoSummary>` — destructures `Goto { target }` (`<= 1.100.0`) vs. `Goto { target, loop_hint_attrs }` (`1.102.0-nightly`).

Negative fail-closed guard runs on `rustc 1.100.0` confirm that both omitting `--cfg anneal_mir_dialect` and passing typoed `--cfg anneal_mir_dialect="mir_1_100_typo"` exit with **`rc = 1`** (`error: exactly one known --cfg anneal_mir_dialect="..." must be passed` plus `unexpected_cfgs`). When linking directly against `<sysroot>/bin/rustc` on nightlies whose `libLLVM-*.so` resides solely in `<sysroot>/lib`, passing both `-L <sysroot>/lib` and `-Clink-arg=-Wl,-rpath,<sysroot>/lib` is required.

#### 3.2 Live 10-Toolchain `rustc-dev` Compilation & Execution Matrix (`1.91.0-nightly`–`1.102.0-nightly`)

Every toolchain below compiled the identical two-file crate (`src/main.rs` + `src/dialect.rs`) with `-D warnings --check-cfg='cfg(anneal_mir_dialect, values(...))'` **while hostile `RUSTC_OVERRIDE_VERSION_STRING="1.78.0-hostile"` was set in the environment**, and executed the resulting binary against `deref_box_and_loop(b: Box<u64>, w: &Wrapper<'_>, n: u64) -> u64`:

| Toolchain | `rustc -V` (`40`-char `commit-hash` prefix) | `--cfg anneal_mir_dialect` | Compile `rc` | Exec `rc` | Live Captured `Runtime(PostCleanup)` MIR Metrics (`deref_box_and_loop`) |
| :--- | :--- | :--- | :---: | :---: | :--- |
| `nightly-2025-08-20` | `1.91.0-nightly` (`05f5a58e84a9...`) | `mir_1_91_93` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=13, uses_implicit_yes=0, uses_explicit_no=0, box_deref_casts=0, gotos_plain=2, size=8, align=8` |
| `nightly-2025-11-23` | `1.93.0-nightly` (`94b49fd998d6...`) | `mir_1_91_93` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=14, uses_implicit_yes=0, uses_explicit_no=0, box_deref_casts=0, gotos_plain=2, size=8, align=8` |
| `nightly-2026-02-07` | `1.95.0-nightly` (`efc9e1b50cbf...`) | `mir_1_94_96` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=14, uses_implicit_yes=0, uses_explicit_no=0, box_deref_casts=0, gotos_plain=2, size=8, align=8` |
| **`nightly-2026-04-12` (mid-cycle `1.97`)** | `1.97.0-nightly` (`bf4fbfb7a18d...`) | **`mir_1_94_96`** | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=14` (**succeeds where `cfg(version("1.97"))` crashed with `E0023`**) |
| `nightly-2026-05-31` | `1.98.0-nightly` (`f8a08b688cbe...`) | `mir_1_97_98` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=0, gotos_plain=2, size=8, align=8` |
| `nightly-2026-06-01` | `1.98.0-nightly` (`14210df0e27c...`) | `mir_1_97_98` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=0, gotos_plain=2, size=8, align=8` |
| `1.99.1` (stable) | `1.99.1` (`58cf8f9c35b3...`) | `mir_1_99` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=1, gotos_plain=2, size=8, align=8` |
| **`stable` (`1.100.0`)** | `1.100.0` (`0ef1bc386059...`) | **`mir_1_100`** | **`0`** (+ `cargo build --offline` `0`) | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=1, gotos_plain=2, size=8, align=8` |
| **`nightly` (`1.102.0-nightly`)** | `1.102.0-nightly` (`3ef0c22cdb86...`) | **`mir_1_102_nightly`** | **`0`** (+ `cargo build --offline` `0`) | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=1, gotos_plain=2, size=8, align=8` |
| `nightly-2026-11-13` | `1.102.0-nightly` (`8eb778d04094...`) | `mir_1_102_nightly` | **`0`** | **`0`** | `bodies=1, bbs=10, uses_legacy=0, uses_implicit_yes=13, uses_explicit_no=1, box_deref_casts=1, gotos_plain=2, size=8, align=8` |

#### 3.3 Companion 7-Era Standalone `--sysroot` Capability-Flag Driver Matrix (`1.94.1`–`1.102.0-nightly`)

Instead of named era bundles (`mir_1_97_98`), a launcher can equivalently pass orthogonal feature-capability `--cfg` flags (`--cfg=dialect_has_stmt_retag` vs. `--cfg=dialect_use_has_with_retag`; `--cfg=dialect_run_compiler_fn` vs. `--cfg=dialect_entrypoint_fn`, while using `TerminatorKind::Goto { target: _, .. }` across `<= 1.100.0` and `1.102.0-nightly`). Compiling `MULTI_ERA_CAPABILITY_DRIVER_RS` (`rustc --edition=2021 -O --sysroot <sr>`) and executing it with `-Zmir-preserve-ub -Copt-level=2` across seven `rustc-dev` sysroots confirms sub-second compile latency and `<50 KiB` driver binaries:

| Sysroot Era | `rustc -V` (`commit-hash` prefix) | Capability `--cfg` Flags | Compile `rc` (`ms`) | Driver Size | Run `rc` | Captured `borrow_roundtrip` / `clamp_u32` Summary |
| :--- | :--- | :--- | :---: | ---: | :---: | :--- |
| `1.94.1` (source tarball) | `1.94.1` (`e408947bfd20...`) | `dialect_has_stmt_retag`, `dialect_run_compiler_fn` | **`0`** (`971.7 ms`) | `48,392 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=0`; `clamp_u32`: `bbs=7, assigns=9, retags=0` |
| `1.95.0-nightly-2026-02-07` | `1.95.0-nightly` (`efc9e1b50cbf...`) | `dialect_has_stmt_retag`, `dialect_run_compiler_fn` | **`0`** (`364.9 ms`) | `38,560 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=0`; `clamp_u32`: `bbs=7, assigns=9, retags=0` |
| `1.97.0-nightly-2026-04-12` | `1.97.0-nightly` (`bf4fbfb7a18d...`) | `dialect_has_stmt_retag`, `dialect_run_compiler_fn` | **`0`** (`381.7 ms`) | `38,784 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=0`; `clamp_u32`: `bbs=7, assigns=9, retags=0` |
| `1.98.0-nightly-2026-05-31` | `1.98.0-nightly` (`f8a08b688cbe...`) | `dialect_use_has_with_retag`, `dialect_run_compiler_fn` | **`0`** (`389.3 ms`) | `36,656 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=3`; `clamp_u32`: `bbs=7, assigns=9, retags=7` |
| `1.100.0-nightly-2026-09-17` | `1.100.0-nightly` (`923c95cdf5ba...`) | `dialect_use_has_with_retag`, `dialect_run_compiler_fn` | **`0`** (`321.9 ms`) | `35,744 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=3`; `clamp_u32`: `bbs=7, assigns=9, retags=7` |
| `1.100.0-stable` | `1.100.0` (`0ef1bc386059...`) | `dialect_use_has_with_retag`, `dialect_run_compiler_fn` | **`0`** (`315.3 ms`) | `35,616 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=3`; `clamp_u32`: `bbs=7, assigns=9, retags=7` |
| `1.102.0-nightly-2026-11-11` | `1.102.0-nightly` (`3ef0c22cdb86...`) | `dialect_use_has_with_retag`, `dialect_entrypoint_fn` | **`0`** (`343.9 ms`) | `35,976 B` | **`0`** | `used_crates=19`; `borrow_roundtrip`: `bbs=2, assigns=3, retags=3`; `clamp_u32`: `bbs=7, assigns=9, retags=7` |

Notice the operational jump between `1.97.0-nightly-2026-04-12` (`retags=0`, because pre-`e402c1ed` `StatementKind::Retag` was omitted unless `-Z mir-emit-retag` was passed) and `1.98.0-nightly-2026-05-31` (`retags=3` and `7`, because `Rvalue::Use(_, WithRetag::Yes)` became unconditionally present on standard `Use` assignments even under `-Zmir-preserve-ub` without `-Z mir-emit-retag`), empirically illustrating why Tier-C semantic shifts must be surfaced rather than erased.

## Boundaries

1. **Pre-`1.78.0` History and Pre-`1.91.0-nightly` Live `rustc-dev` Compilation (`not examined`):** Static source extraction covers `1.78.0` (`2024-04-29`) through `1.102.0-nightly` (`2026-11-19`); live `#![feature(rustc_private)]` compilation covers `1.91.0-nightly` through `1.102.0-nightly` (`12` minor cycles) because pre-`1.91` `rustc-dev` sysroots were not installed in the test environment. Extending `dialect.rs` back to `1.78.0` requires adding `RunCompiler` (`<= 1.85.0`), `&'tcx Queries` (`<= 1.84.0`), and `rustc_target::abi` (`<= 1.83.0`) shims (`not examined` via live `rustc-dev` execution).
2. **`Runtime(Optimized)` MIR, Borrow-Checker Internals, and HIR/THIR Lowering (`known not to apply`):** Tier-A (`0.826` breaks/release) and Tier-B (`1.565` reachable deltas/release) scaling rates are **`known not to apply`** to tools hooking `rustc_borrowck`, HIR/THIR type-checking internals, or post-optimization `optimized_mir`, which touch broader internal surfaces and pre-borrowck constructs (`BackwardIncompatibleDropHint`, `PhantomDeref`, `FakeRead`, `AscribeUserType`) excluded from `Runtime(PostCleanup)`.
3. **`#![feature(cfg_accessible)]` on Enum Variants, Fields, Inherent Methods, Negation, and `match` Arms (`unsupported` / `known not to apply`):** In `rustc` through `1.102.0-nightly`, `cfg_accessible` is **`unsupported`** as a general `cfg(...)` predicate (`E0537`/`E0539` inside `cfg(not(...))`, macro-attribute error on `match` arms) and is **`known not to apply`** to cross-version enum-variant or struct-field gating (`CfgAccessibleUnsure` compile error whenever the variant or field is absent).
4. **Silent Cross-Version Semantic Equivalence Under Syntactic Trunk Normalization (`known not to apply`):** Compiling `dialect.rs` across `1.91`–`1.102` establishes syntactic adapter compactness (`13.67` LOC/release), NOT operational semantic equivalence across releases. Unconditional cross-compiler proof transfer without checking Tier-C semantic capability flags (`WithRetag`, `Call` destination-before-args order, `StorageLive` refresh, `Move` call-arg aliasing UB, `Infallible = !`) is **`known not to apply`**.
5. **Post-`1.102.0-nightly` (`6905905bb...`) Churn Rates and Future RFC 2523 Resolver Changes (`unknown`):** Whether future `rust-lang/rust` cycles maintain `~0.83` narrow driver breaks/release and `~0.70` semantic deltas/release—or whether `rustc_resolve` eventually resolves `CfgAccessibleUnsure` for external enum variants—is **`unknown`** without re-running the revalidation probes below.
6. **Non-`x86_64-unknown-linux-gnu` Hosts and Custom-Patched Monorepo `librustc_driver` Symbol Mangling (`not examined`):** Live compilation timings (`315–972 ms`) and binary sizes (`35.6–48.4 KiB`) were measured on `x86_64-unknown-linux-gnu`; Windows/macOS dylib linking flags and binary-level `StableCrateId` symbol-hash incompatibilities across custom-patched monorepo compilers are **`not examined`** in this package.

## Evidence

- **Preserved standalone probe and raw dataset (`execution` + `source`, acquired `2026-11-22` on `x86_64-unknown-linux-gnu`):**
  - `support/probe_mir_scaling_and_cfg_matrix.py` — stdlib-only Python 3.10+ script implementing Part 1 (`run_part1_git_census`: blobless `rust-lang/rust` clone, 24-tag + intra-nightly SHA resolution, 18-declaration `mir/{syntax,mod}.rs` AST parser and `Runtime(PostCleanup)` classifier, and verification of all causal Tier-A/Tier-C commits), Part 2 (`run_part2_live_matrix`: 14-toolchain + 4-override `cfg_version` truth table, mid-cycle `E0023` & `-Z assume-incomplete-release` `E0425` reproducers, 11-case × 4-compiler `cfg_accessible` matrix, 10-compiler `164`-LOC `dialect.rs` + `main.rs` prototype under `RUSTC_OVERRIDE_VERSION_STRING="1.78.0-hostile"`, `cargo build --offline` runs, and negative `compile_error!` / `--check-cfg` guards), and Part 3 (`run_part3_capability_sysroot_probe`: 7-era `--sysroot` `TrunkCapture` capability-flag driver + glob-shadowed `cfg_accessible` probes).
  - `support/probe_mir_scaling_and_cfg_matrix.json` — complete machine-readable output containing `part1_four_tier_scaling_census` (`revisions`, `intra_nightly_revision`, `rates`, `tier2_breaks`, `tier3_transitions`, `tier4_semantic_deltas`, `verified_commits`), `part2_multi_version_rustc_private_matrix`, and `part3_seven_era_capability_driver_and_glob_shadowing`.
- **Primary upstream source locations (`source`):**
  - `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`:
    - `compiler/rustc_middle/src/mir/syntax.rs` and `compiler/rustc_middle/src/mir/mod.rs` (18 core MIR AST declarations, `PlaceElem` and `AssertMessage` type aliases).
    - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:36` (`BackwardIncompatibleDropHint` $\to$ `StatementKind::Nop`).
    - `compiler/rustc_mir_transform/src/validate.rs:471, 480, 490, 509, 882, 1029, 1158, 1326, 1342, 1510, 1518` (`MirPhase::Runtime` bans).
    - `compiler/rustc_const_eval/src/interpret/projection.rs:414-415` (`PhantomDeref` post-borrowck `span_bug!`) and `compiler/rustc_const_eval/src/interpret/step.rs:419, 465-486, 563, 601-605, 654-657` (`RuntimeChecks`, `Move` call-arg aliasing UB, `Goto` unroll-hint no-op, `Call` destination-first evaluation order, runtime `Drop` invariants).
    - `compiler/rustc_ast/src/attr/version.rs:8-48` and `compiler/rustc_attr_parsing/src/attributes/{util.rs:16-27, cfg.rs:125-147, 270-285}` (`cfg_version`, `RUSTC_OVERRIDE_VERSION_STRING`, `-Z assume-incomplete-release`).
    - `compiler/rustc_builtin_macros/src/cfg_accessible.rs:36-69` and `compiler/rustc_resolve/src/macros.rs:524-530, 1272-1311` (`cfg_accessible` and `CfgAccessibleUnsure`).
  - `rust-lang/rust@6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`: intra-cycle `1.102.0-nightly` (`94add9677e2de57a2e414350bedcd13f07426a5e` `+TyKind::View`; `c7577d3452810c553e2377d9c9b9eb2a9ce9148d` `compiler_entrypoint` delayed-error check).
  - `dtolnay/rustversion@3a7c76605450b9a7299c6502a421909de9126a59` (`v1.0.23`): `Cargo.toml:5, 14-15`, `build/build.rs:21-46, 80-86, 100-103`, `build/rustc.rs:47-90`, `src/bound.rs:33-62`, and `src/expr.rs:24-50`.

## Revalidation

1. **Extend or re-verify the 4-tier Git scaling census on a newer `rust-lang/rust` release or nightly (`~40s` with network access, `0` local state left behind):**
   ```sh
   python3 -B reports/rustc-twenty-four-release-mir-scaling-laws-and-dialect-adapters/support/probe_mir_scaling_and_cfg_matrix.py \
     --census-only --out /tmp/mir_scaling_recheck.json
   ```
   To inspect a new release `1.X.0` or candidate commit `<NEW_SHA>` cheaply without a full run, diff only the narrow capture & operational semantics files in a blobless `rust-lang/rust` clone:
   ```sh
   git diff 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1..<NEW_SHA> -- \
     compiler/rustc_driver_impl/src/lib.rs \
     compiler/rustc_interface/src/interface.rs \
     compiler/rustc_middle/src/mir/syntax.rs \
     compiler/rustc_middle/src/mir/mod.rs \
     compiler/rustc_abi/src/layout.rs \
     compiler/rustc_const_eval/src/interpret/
   ```
2. **Validate the zero-`build.rs` `--cfg` dialect adapter and `cfg_version` / `cfg_accessible` discriminators on installed `rustc-dev` toolchains (`~10s`):**
   ```sh
   python3 -B reports/rustc-twenty-four-release-mir-scaling-laws-and-dialect-adapters/support/probe_mir_scaling_and_cfg_matrix.py \
     --matrix-only --out /tmp/mir_cfg_matrix_recheck.json
   ```
   Pass repeatable `--extra-sysroot <label>=<path>` flags to test arbitrary standalone or tarball `rustc` + `rustc-dev` sysroots. A passing run (`compile_rc == 0` and `exec_rc == 0`) confirms source-level `rustc_private` compatibility for the selected `--cfg` dialect; any Tier-C semantic additions uncovered by the `interpret/` diff above must still be audited manually against the consumer's formal operational semantics.
