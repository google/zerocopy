# `rustc` Frontend, Typeck, Borrowck, Procedural-Macro Bridge, `.rmeta`, and `rustdoc` JSON Completeness Contract

## Summary

An in-process Mid-Level Intermediate Representation (MIR) codegen backend
inherits `rustc`'s parser, macro expander, name resolver, type checker, trait
solver, borrow checker, crate metadata encoder, and `rustdoc` driver without
reimplementing them. By contrast, a **standalone Rust compiler**—one that parses
`.rs` source files directly rather than linking `rustc_driver`—must satisfy the
complete frontend, cross-crate metadata, procedural-macro hosting, and
documentation-JSON contracts expected by Cargo, the Rust standard library
(`core`, `alloc`, `std`), and crates.io packages.

Machine extraction of `rust-lang/rust` at `1.102.0-nightly`
(`412be32a6a189d9a28922beee178bc0abee9d492`, preserved in
`support/extract_frontend_contracts.py` and
`support/frontend_features_attrs_langitems.json`), paired with isolated
execution probes on `rustc`/`rustdoc` `1.102.0-nightly`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), establishes six governing
completeness contracts:

1. **Surface editions and feature-gate registry (`589` tracked language
   features, `5` editions, `172` compiler edition checks):** `rustc_span`
   defines four stable editions (`2015`, `2018`, `2021`, `2024`, with `2015` as
   the CLI default when `--edition` is omitted and `2024` as
   `LATEST_STABLE_EDITION`) plus unstable `future`. Because every `Span` carries
   its `SyntaxContext` hygiene edition, a single crate compilation routinely
   mixes editions across macro expansions. At `412be32a6a189d9a28922beee178bc0abee9d492`,
   `rustc_feature` tracks **`214` accepted** (`ACCEPTED_LANG_FEATURES`),
   **`266` active** (`192` normal `unstable`, `41` `incomplete`, and `33`
   `internal` compiler/stdlib gates), and **`109` removed** language features.
2. **Typed attribute lowering, built-in macros/derives, and `233` lang items:**
   Upstream replaced scattered `ast::Attribute` inspection with a three-crate
   pipeline: `rustc_feature::BUILTIN_ATTRIBUTES` (`199` built-in attribute
   symbols and `18` `GATED_CFGS`), `rustc_attr_parsing::ATTRIBUTE_PARSERS`
   (`193` state-machine parsers accepting `202` attribute paths, plus
   pre-lowering `cfg` and `cfg_attr`), and `rustc_attr_ir::AttributeKind` (`196`
   typed semantic variants backed by `6` `#![deny(unstable_features)]` shared
   types in `rustc_structures`). Exactly **`8` attribute paths are
   `AttributeSafety::Unsafe`** (`export_name`, `link_section`, and `no_mangle`
   since Edition 2024; `naked`, `force_target_feature`, `ffi_const`, `ffi_pure`,
   and `rustc_allow_lifetime_dependent_specialization` unconditionally), and
   **`29` paths are `CrateLevel`-only**. `rustc_builtin_macros` registers **`65`
   built-in expanders** (`30` `AstBang`, `18` `AstAttr`, `14` `AstDerive`, and
   `3` proc-macro/contract built-ins), augmented by `rustc_expand_queries`'s new
   `derive_macro_expansion` query cache. `rustc_attr_ir::lang_items` declares
   **`233` `LangItem` variants** (`196` defined in `core`, `3` in `alloc`, `2`
   in `std`, `7` duplicated in `rtstartup`, `2` weak linker symbols, and `32`
   compiler-internal/test-only items); even `#![no_core]` requires `sized`,
   `meta_sized`, `pointee_sized`, and `copy` as soon as any `struct` or `fn` is
   declared.
3. **Built-in lints (`261` compiler + `31` tool lints across `rustc::*` and
   `rustdoc::*`), lint groups, and `518` `E0xxx` error codes:** `declare_lint!`
   defines `261` compiler lints (`63` `Allow`, `144` `Warn`, `54` `Deny`, `0`
   default-`Forbid`), alongside `17` `rustc::*` internal compiler lints and `14`
   `rustdoc::*` documentation lints (`292` in-tree lints total); `71` compiler
   lints carry `FutureIncompatibleInfo` (`42` `FutureReleaseError`, `16`
   `EditionError`, `11` `EditionSemanticsChange`, `2` custom). `LintStore`
   exposes `10` static/explicit lint groups (`unused`, `nonstandard_style`,
   `rust_2018_idioms`, `rustc::internal`, `rustdoc::all`, etc.), `6` dynamic
   groups (`warnings`, `future_incompatible`, and four edition compatibility
   groups), `18` renamed lints, and `68` removed lints. `rustc_error_codes`
   registers `518` `E0001`–`E0806` codes (`387` actively emitted, `131` retired
   historical codes retained for `rustc --explain`).
4. **Dual trait-solver and three-mode borrow-checker boundary:** Across `9`
   type-system and borrow-checking crates (`194,421` SLOC), `rustc` runs the
   canonicalized next-generation trait solver (`rustc_next_trait_solver`, `9,568`
   SLOC, generic over `rustc_type_ir::Interner`) **on stable Rust for coherence
   checking** (`NextSolverConfig::Coherence`) while still defaulting to the
   legacy `SelectionContext`/`FulfillmentContext` engine (`41,023` SLOC) outside
   coherence unless `-Znext-solver=globally` is set. Pattern checking
   (`rustc_pattern_analysis`, `3,102` SLOC) normalizes patterns into `21`
   `Constructor` variants for Maranget matrix usefulness checking. Borrow
   checking (`rustc_borrowck`, `27,851` SLOC) operates over `mir_promoted` with
   three `Polonius` modes (`Off` = NLL location-insensitive SCC region solving,
   `Legacy` = Datalog `polonius-engine` over `AllFacts<RustcFacts>`, and `Next`
   = `-Zpolonius=next` variance-directed `LocalizedConstraintGraph` + bitset
   `LiveLoans`) and resolves return-position `impl Trait` / TAIT hidden types
   via SCC member constraints (`region_infer::opaque_types`).
5. **ABI-isolated `proc_macro::bridge` wire protocol (`31` RPC tags):** Host
   procedural macro `.so`/`.dylib`/`.dll` plugins export a single symbol
   `__rustc_proc_macro_decls_<StableCrateId>__: &[ProcMacro]` (`CustomDerive`,
   `Attr`, `Bang`), where every macro entry point has C-ABI type
   `extern "C" fn(BridgeConfig<'_>) -> Buffer` and catches panics inside the
   dylib via `catch_unwind`. Cross-boundary values are serialized in
   little-endian byte frames (`rpc.rs`) with `NonZero<u32>` handles (`OwnedStore`
   for `TokenStream`, `InternedStore` for `Span` and `Symbol`) and `31` `u8`
   `ApiTags` (`0..=30`) callbacks into `rustc_expand::proc_macro_server`. Even
   `Buffer` heap growth and drop cross via `extern "C"` function pointers
   embedded in `Buffer`, allowing a standalone compiler written in any language
   to host `rustc`-compiled proc-macro dylibs—or delegate to an external
   `proc-macro-srv` worker—without matching Rust's unstable internal struct ABI.
6. **`.rmeta` v12 binary schema (`48` `CrateRoot` fields, `82` `LazyTables`),
   XXH3-128 `Svh`, and `rustdoc` JSON `FORMAT_VERSION = 61`:** Between `1.99.1`
   and `1.102.0-nightly`, `rustc_metadata` bumped `METADATA_VERSION` from `10`
   to **`12`**, expanding the fixed header to `40` bytes (`METADATA_HEADER` at
   `0..8`, `CrateRoot` offset at `8..16`, `CrateRootUnhashed` offset at
   `16..24`, 128-bit `Svh` `Fingerprint` at `24..40`, and `rustc_version` at
   byte `40`) and switching default `Svh` computation (`-Zmetadata-crate-hash=yes`)
   to an **XXH3-128** digest over the encoded `CrateRoot` bytes seeded with
   `dep_tracking_hash` + `compute_hir_hash`, while isolating `-Cextra-filename`
   inside `CrateRootUnhashed` so filename suffixes no longer perturb `Svh`. A
   standalone compiler that compiles its own sysroot and dependency graph from
   source **does not** need bit-for-bit `.rmeta` compatibility with upstream
   `rustc`, whereas external documentation tools (`cargo-semver-checks`,
   `cargo-public-api`) couple directly to `rustdoc-json-types`
   (`FORMAT_VERSION = 61`, `8`-field `Crate` root, `21`-variant `ItemEnum`).

## Applicability

This report governs any standalone Rust compiler, verified frontend, custom
driver, or documentation/metadata tool targeting the `rustc` frontend and
crate-interface contracts:

- **Primary source baseline:** `rust-lang/rust` commit
  `412be32a6a189d9a28922beee178bc0abee9d492` (`1.102.0-nightly`, `2026-11-18`),
  together with its pinned normative submodules `rust-lang/reference`
  (`bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`) and `rust-lang/edition-guide`
  (`ab8544aeed7b792984366aa122ac19bd47ad9a2f`).
- **Execution toolchains compared:** `rustc` and `rustdoc` `1.102.0-nightly`
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, LLVM `23.1.5`) and
  `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `2026-10-13`,
  LLVM `23.1.1`) on `x86_64-unknown-linux-gnu`.
- **Relationship to sibling corpus packages:** This package extends
  `rustc-external-cli-json-and-backend-interface-contract` (which specifies CLI
  flags, JSON stderr diagnostics, `CodegenBackend`, and `.rmeta` v10 magic
  bytes at `1.99.1`) and `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts`
  (which specifies Miri, `rust-analyzer`, `proc-macro-srv` JSON/postcard framing,
  and `rustdoc --test-builder`). Where those two packages treat the frontend as
  an inherited black box, this report specifies the internal frontend, metadata,
  proc-macro wire, and `rustdoc` JSON contracts that a standalone compiler must
  implement.

## Findings

### 1. Surface Language, Editions (`2015`–`Future`), and Feature-Gate Inventories

Basis: normative + source + execution

#### 1.1 Edition model and per-`Span` hygiene mixing

`compiler/rustc_span/src/edition.rs:34-133` defines five ordered variants of
`Edition`: `Edition2015` (`"2015"`, `DEFAULT_EDITION` when `--edition` is
omitted on the CLI), `Edition2018` (`"2018"`), `Edition2021` (`"2021"`),
`Edition2024` (`"2024"`, `LATEST_STABLE_EDITION`), and `EditionFuture`
(`"future"`, accepted only on nightly or under `-Zunstable-options`).

Crucially for a standalone compiler, **edition is not a mere global session
boolean**: while `Session::edition()` records the root crate's `--edition` flag,
macro hygiene attaches an `ExpnData` record (carrying the defining crate's
`Edition`) to every `SyntaxContext` (`compiler/rustc_span/src/hygiene.rs`). Of
the **`172` non-comment edition checks** across `compiler/` at
`412be32a6a189d9a28922beee178bc0abee9d492` (`rustc_span`: `59`, `rustc_parse`:
`28`, `rustc_resolve`: `25`, `rustc_hir_typeck`: `14`, `rustc_lint`: `12`,
`rustc_lint_defs`: `9`, `rustc_session`: `8`, `rustc_hir_analysis`: `5`,
`rustc_mir_build`: `5`, and `7` across remaining crates), lexical, syntactic,
and drop-scope decisions query `span.edition()` so that a `macro_rules!` macro
defined in an Edition 2021 dependency preserves Edition 2021 token, capture, and
temporary-drop semantics when expanded inside an Edition 2024 crate.

Table 1 summarizes the semantic and syntactic deltas across all five editions
(`compiler/rustc_span/src/symbol.rs:32-148`, `rustc_parse`, `rustc_resolve`,
`rustc_hir_analysis`, `rustc_hir_typeck`, and `rustc_mir_build`).

| Subsystem | Edition 2015 | Edition 2018 | Edition 2021 | Edition 2024 (`LATEST_STABLE_EDITION`) | `EditionFuture` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Strict & reserved keywords** (`symbol.rs:45-116`) | `35` base strict + `12` reserved (`abstract`, `become`, `box`, `do`, `final`, `macro`, `override`, `priv`, `typeof`, `unsized`, `virtual`, `yield`) | Adds strict `async`, `await`, `dyn`; reserves `try`; enables `r#ident` raw identifiers | Reserves `ident#...`, `ident"..."`, `ident'...'` lexer prefixes (`RFC 3101`) | Reserves **`gen`** (`symbol.rs:113`); enables `c"..."` / `cr"..."` C-string literals (accepted since `1.77`, lexer token rule simplified with guarded strings) | Staging ground for post-2024 keyword/syntax gates (`edition_future_compatibility`) |
| **Module & path resolution** (`rustc_resolve`) | Crate-root-relative `use`, mandatory `extern crate`, anonymous trait-method params allowed (`fn f(u8)`) | Uniform paths, `--extern` prelude without `extern crate`, `dyn Trait` lints on bare trait objects, anonymous trait params hard error | Prelude adds `TryInto`, `TryFrom`, `FromIterator` (`RUST_2021_PRELUDE_COLLISIONS`) | Prelude adds `Future`, `IntoFuture` (`RUST_2024_PRELUDE_COLLISIONS`, `prelude_edition_lints.rs:173-205`) | Inherits 2024 |
| **`macro_rules!` fragment specifiers** (`rustc_parse`) | `expr` matches full 2015 expressions | Same as 2015 | `pat` matches top-level `\|` or-patterns (`pat_param` preserves pre-2021 single pattern) | **`expr` also matches `const { ... }` and `_` expressions**; `expr_2021` preserves pre-2024 behavior (`macro_expr_fragment_specifier_2024_migration.rs`) | Inherits 2024 |
| **Closures, patterns & arrays** (`rustc_hir_typeck`) | Whole-variable closure capture; `[T; N].into_iter()` resolves via ` &[T; N]` autoref | Same as 2015 | **Disjoint field capture** (`RFC 2229`, `upvar.rs:2540,2754`) + by-value `[T; N]::into_iter` workaround (`probe.rs:2099`) | **Match ergonomics reservations (`pat.rs:344,1186`)**: `mut` / `ref` / `ref mut` cannot be written under inherited reference binding modes (`RUST_2024_INCOMPATIBLE_PAT`); `Box<[T]>::into_iter` by-value resolution (`probe.rs:2109`) | Inherits 2024 |
| **RPIT lifetime capture & `!` fallback** (`rustc_hir_analysis`) | Free-fn `-> impl Trait` captures only lifetimes mentioned in bounds | Same as 2015 | Same as 2015 | **All in-scope type & lifetime parameters captured by default** in `-> impl Trait` unless overridden with explicit **`use<...>`** precise capturing (`resolve_bound_vars.rs:322-331`); unconstrained `!` inference vars fall back to **`!`** instead of `()` | Inherits 2024 |
| **Temporary drop order** (`region.rs`, `scope.rs`) | Block tail expression temporaries outlive local variables of the block; `if let` temporaries live across `else` | Same as 2015 | Same as 2015 | **`tail_expr_drop_order`** (`region.rs:148`, `scope.rs:437,1179,1927`): tail-expression temporaries drop *before* block locals (`terminating = true`). **`if_let_rescope`** (`region.rs:355-374`): `if let` scrutinee temporaries drop before entering `else` (`ScopeData::IfThenRescope`) | Inherits 2024 |
| **Safety syntax** (`rustc_parse`, `safety.rs`) | `extern "C" { ... }` and `#[no_mangle]` safe to write | Same as 2015 | Same as 2015 | **`unsafe extern` blocks mandatory** (`MISSING_UNSAFE_ON_EXTERN` -> hard error in 2024); **`#[unsafe(export_name = ...)]`**, **`#[unsafe(link_section = ...)]`**, **`#[unsafe(no_mangle)]`** mandatory (`safety.rs:51-54`); `unsafe_op_in_unsafe_fn` `Warn`-by-default; `static mut` references `Deny`-by-default (`STATIC_MUT_REFS`) | Inherits 2024 |

#### 1.2 Feature-gate inventory at `412be32a6a189d9a28922beee178bc0abee9d492`

`compiler/rustc_feature/src/{lib.rs,accepted.rs,unstable.rs,removed.rs}` governs
all `#![feature(...)]` gates. Channel enforcement in `UnstableFeatures::from_environment_value`
(`compiler/rustc_feature/src/lib.rs:84-112`) resolves four states:
`Disallow` (stable/beta builds with `CFG_DISABLE_UNSTABLE_FEATURES != "0"`, or
`RUSTC_BOOTSTRAP=-1`), `Allow` (nightly builds), `Cheat` (`RUSTC_BOOTSTRAP=1` or
`RUSTC_BOOTSTRAP=<crate_a>,<crate_b>` matching `--crate-name`), and
`AllowSelectedUnstableCompilerFlagsOnly` (`RUSTC_BOOTSTRAP=-allow-unstable-compiler-flags=...`
for `compiletest` on stable channels). Any `#![feature(name)]` not found in the
three language feature tables below is recorded in
`Features::enabled_lib_features` (`unstable.rs:51`) and validated later against
`#[unstable(feature = "...", ...)]` library stability markers.

| Registry Table | Source File | Count | Breakdown & Completeness Rules |
| :--- | :--- | ---: | :--- |
| **`ACCEPTED_LANG_FEATURES`** | `compiler/rustc_feature/src/accepted.rs:23-498` | **`214`** | Stabilized features (`#![feature(...)]` emits `STABLE_FEATURES` warning rather than `E0635`). Recent stabilizations include `c_variadic` & `c_variadic_naked_functions` (`1.99.0`), `abi_custom` & `const_destruct` (`1.100.0`), and `indirection_in_diagnostic_on_unimplemented` (`1.101.0`). |
| **`UNSTABLE_LANG_FEATURES` (`unstable`)** | `compiler/rustc_feature/src/unstable.rs:212-912` | **`192`** | Standard active nightly language features (`FeatureStatus::Default`), gated by `E0658` when `Disallow` is active. |
| **`UNSTABLE_LANG_FEATURES` (`incomplete`)** | `compiler/rustc_feature/src/unstable.rs:155-168` | **`41`** | Active features emitting `INCOMPLETE_FEATURES` (`Warn` by default) when enabled: includes `adt_const_params`, `async_drop`, `contracts`, `deref_patterns`, `ergonomic_clones`, `explicit_tail_calls`, `field_projections`, `generic_const_exprs`, `generic_const_items`, `lazy_type_alias`, `mut_ref`, `pin_ergonomics`, `return_type_notation`, `specialization`, `unsized_const_params`, and `unsized_locals`. |
| **`UNSTABLE_LANG_FEATURES` (`internal`)** | `compiler/rustc_feature/src/unstable.rs:172-188` | **`33`** | Compiler/stdlib implementation gates emitting `INTERNAL_FEATURES` (`Warn` by default): includes `allow_internal_unsafe`, `allow_internal_unstable`, `allocator_internals`, `compiler_builtins`, `core_intrinsics`, `custom_mir`, `eii_internals`, `fundamental`, `intrinsics`, `lang_items`, `link_cfg`, `link_llvm_intrinsics`, `min_specialization`, `more_maybe_bounds`, `negative_bounds`, `needs_panic_runtime`, `no_core`, `panic_runtime`, `pattern_complexity_limit`, `prelude_import`, `proc_macro_internals`, `proc_macro_quote`, `profiler_runtime`, `rustc_attrs`, `rustdoc_internals`, and `staged_api`. |
| **`REMOVED_LANG_FEATURES`** | `compiler/rustc_feature/src/removed.rs:44-327` | **`109`** | Tombstoned features (`83` with explicit human-readable `reason`, `75` citing removal PR numbers); enabling any emits hard error `E0557` (`feature has been removed`). |

---

### 2. Built-in Attributes, Built-in Macros/Derives, and `#[lang = "..."]` Items

Basis: source + execution

#### 2.1 Three-crate typed attribute architecture (`rustc_feature` -> `rustc_attr_parsing` -> `rustc_attr_ir`)

Prior to Rust `1.100`–`1.102`, built-in attributes were described in a static
`BuiltinAttribute` table in `rustc_feature` while ad-hoc `MetaItem` token
parsing was scattered across the compiler. At
`412be32a6a189d9a28922beee178bc0abee9d492`, attribute handling is centralized
across four crates (`compiler/rustc_attr_parsing/src/lib.rs:3-88`):

1. **`compiler/rustc_feature/src/builtin_attrs.rs:15-298`:** Exports `18`
   feature-gated `cfg(...)` keys in `GATED_CFGS` (`overflow_checks`,
   `ub_checks`, `contract_checks`, `target_thread_local`,
   `target_has_atomic_load_store`, `sanitize`, `version`, `relocation_model`,
   `sanitizer_cfi_generalize_pointers`, `sanitizer_cfi_normalize_integers`,
   `fmt_debug`, `target_has_reliable_f16`, `target_has_reliable_f16_math`,
   `target_has_reliable_f16b`, `target_has_reliable_f128`,
   `target_has_reliable_f128_math`, `target_has_threads`, and
   `target_object_format`), `AttributeStability` (`Stable` vs `Unstable {
   gate_name, notes }`), and `BUILTIN_ATTRIBUTES` (`199` single-segment built-in
   attribute symbols).
2. **`compiler/rustc_structures/src/lib.rs:1-20`:** Enforces
   `#![deny(unstable_features)]` so `rust-analyzer` can share `6` core attribute
   payload types (`CollapseMacroDebuginfo`, `CrateType`, `Limit`, `LintName`,
   `NativeLibKind`, and `SanitizerSet`) on stable Rust.
3. **`compiler/rustc_attr_parsing/src/context.rs:163-365` and
   `interface.rs:626-637`:** Registers **`193` stateful `AttributeParser`
   implementations** (`21` multi-path or custom state machines, `15`
   `Combine<T>` multi-attribute coalescers such as `#[repr(C)]` +
   `#[repr(packed)]`, `57` `Single<T>` one-shot parsers, and `100`
   `Single<WithoutArgs<T>>` word-only parsers) covering **`202` distinct
   attribute paths** (including segmented paths `diagnostic::on_unimplemented`,
   `diagnostic::on_move`, `diagnostic::on_const`, `diagnostic::on_type_error`,
   `diagnostic::on_unknown`, `diagnostic::on_unmatched_args`,
   `diagnostic::do_not_recommend`, `diagnostic::opaque`, `lint::as_ptr`,
   `lint::never_returns_null_ptr`, and
   `lint::should_not_be_called_on_const_items`), plus `2` `SPECIAL_ATTRIBUTES`
   (`cfg` and `cfg_attr`, stripped/expanded before HIR lowering).
4. **`compiler/rustc_attr_ir/src/{attr.rs,data_structures.rs}`:** Lowers every
   surviving HIR attribute into a 3-variant `Attribute` enum (`attr.rs:100-124`):
   `Attribute::Parsed(AttributeKind)` (**`196` strongly typed semantic
   variants**), `Attribute::Tool { item, opts }` (registered Clippy/rustfmt/custom
   tool attributes), or `Attribute::DeriveHelper(Box<AttrItem>)` (inert helper
   attributes retained for `rustdoc` JSON).

Grouping all `202` parsed attribute paths in `support/frontend_features_attrs_langitems.json`
across the three enforcement axes yields:

- **`AttributeSafety` (`safety.rs:12-127`):** **`194` `Normal`** (writing
  `#[unsafe(...)]` is a hard error `InvalidAttrUnsafe`) vs. **`8` `Unsafe`**
  (Table 2; omitting `unsafe(...)` emits hard error `UnsafeAttrOutsideUnsafe`
  when `path_span.edition() >= unsafe_since`, or future-incompatible lint
  `UNSAFE_ATTR_OUTSIDE_UNSAFE` on older editions, and always triggers the
  `UNSAFE_CODE` lint). In addition, active macro attribute `#[unsafe(eii)]` is
  handled in `rustc_builtin_macros` (`eii::unsafe_eii`).
- **Scope / `AllowedTargets` (`target_checking.rs:23-95`):** **`29`
  `CrateLevel`-only** attributes (`compiler_builtins`, `crate_name`,
  `crate_type`, `default_lib_allocator`, `feature`, `move_size_limit`,
  `needs_allocator`, `needs_panic_runtime`, `no_builtins`, `no_core`, `no_main`,
  `no_std`, `panic_runtime`, `pattern_complexity_limit`, `profiler_runtime`,
  `recursion_limit`, `reexport_test_harness_main`, `register_attribute_tool`,
  `register_lint_tool`, `register_tool`, `rustc_coherence_is_core`,
  `rustc_dump_hidden_type_of_opaques`, `rustc_dump_variances_of_opaques`,
  `rustc_no_implicit_bounds`, `rustc_preserve_ub_checks`, `test_runner`,
  `type_length_limit`, `unstable_removed`, `windows_subsystem`) vs. **`173`
  `Normal`** item/statement/expression/parameter attributes.
- **Feature gating (`AttributeStability`):** **`53` `Ungated`** (`Stable`),
  **`6` `Mixed(Stable+Gated)`** (stable outer attribute with unstable sub-forms,
  such as `#[doc(...)]`, `#[link(...)]`, `#[repr(...)]`, and `#[inline]` vs
  `#[rustc_force_inline]`), **`1` `CompilerBuiltins`** (`#![compiler_builtins]`,
  gated on `#![feature(compiler_builtins)]`), **`92` `Gated(rustc_attrs)`**
  (`#[rustc_*]` internal attributes), and **`50` `Gated`** behind dedicated
  feature gates (`naked_functions_target_feature`, `linkage`, `thread_local`,
  `coverage_attribute`, `sanitize`, `patchable_function_entry`, `pin_ergonomics`,
  etc.).

| `Unsafe` Attribute Path | `unsafe_since` | Stability Gate | Source Location | Required Safety Invariant |
| :--- | :--- | :--- | :--- | :--- |
| `export_name` | `Some(Edition2024)` | `Stable` | `codegen_attrs.rs:117` | Linker symbol-collision freedom and ABI signature match |
| `link_section` | `Some(Edition2024)` | `Stable` | `codegen_attrs.rs:229` | Target section permissions, alignment, and linker script invariants |
| `no_mangle` | `Some(Edition2024)` | `Stable` | `codegen_attrs.rs:632` | Global unmangled symbol uniqueness and C/platform ABI validity |
| `naked` | `None` (all editions) | `Stable` (`1.88.0`) | `codegen_attrs.rs:421` | Body must be a single `naked_asm!` adhering to calling convention |
| `force_target_feature` | `None` (all editions) | `effective_target_features` | `link_attrs.rs:520` | Caller/CPU guaranteed to support enabled ISA extensions |
| `ffi_const` | `None` (all editions) | `ffi_const` | `link_attrs.rs:588` | Foreign function reads no mutable memory (`LLVM memory(none)`) |
| `ffi_pure` | `None` (all editions) | `ffi_pure` | `link_attrs.rs:601` | Foreign function has no side effects (`LLVM memory(read)`) |
| `rustc_allow_lifetime_dependent_specialization` | `None` (all editions) | `rustc_attrs` | `traits.rs:104` | Impl specialization soundness despite lifetime-erased codegen |

#### 2.2 Built-in macros, built-in derives, and `derive_macro_expansion` query caching

`compiler/rustc_builtin_macros/src/lib.rs:62-155` (`register_builtin_macros`)
registers **`65` compiler-built-in syntax extensions** (invoked when a standard
library stub carries `#[rustc_builtin_macro]`):

- **`30` `AstBang` function-like macros (`lib.rs:74-107`):** `asm`, `assert`,
  `cfg`, `cfg_select`, `column`, `compile_error`, `concat`, `concat_bytes`,
  `const_format_args`, `core_panic`, `env`, `file`, `format_args`,
  `format_args_nl`, `gca`, `global_asm`, `include`, `include_bytes`,
  `include_str`, `iter`, `line`, `log_syntax`, `module_path`, `naked_asm`,
  `option_env`, `std_panic`, `stringify`, `test_binder_constraints`,
  `trace_macros`, and `unreachable`.
- **`18` `AstAttr` active attribute macros (`lib.rs:109-130`):**
  `alloc_error_handler`, `autodiff_forward`, `autodiff_reverse`, `bench`,
  `cfg_accessible`, `cfg_eval`, `define_opaque`, `derive` (`is_const: false`),
  `derive_const` (`is_const: true`), `eii`, `eii_declaration`,
  `eii_shared_macro`, `global_allocator`, `offload_kernel`,
  `rustdoc_skip_body`, `test`, `test_case`, and `unsafe_eii`.
- **`14` `AstDerive` built-in trait derives (`lib.rs:132-147`):** `Clone`,
  `CoercePointee`, `CoerceShared`, `ConstParamTy`, `Copy`, `Debug`, `Default`,
  `Eq`, `From`, `Hash`, `Ord`, `PartialEq`, `PartialOrd`, and `Reborrow`.
- **`3` proc-macro and contract built-ins (`lib.rs:149-154`):** `quote!`
  (`BangProcMacro` backed by `rustc_proc_macro::quote`),
  `#[contracts_requires]`, and `#[contracts_ensures]`.

At `412be32a6a189d9a28922beee178bc0abee9d492`, upstream also added
`compiler/rustc_expand_queries/src/{lib.rs,derive.rs}` (`82` lines), wiring
`rustc_expand::proc_macro::EXPAND_DERIVE_MACRO_CACHED` to the `TyCtxt` query
`derive_macro_expansion((LocalExpnId, &'tcx TokenStream)) -> Result<&'tcx TokenStream, ()>`.
Before invoking the proc-macro client via `scoped_tls` (`DERIVE_EXPAND_CTX`),
`derive_macro_expansion` forces `tcx.crate_hash(macro_def_id.krate)`
(`derive.rs:76`) so incremental compilation caches `#[derive(...)]` token-stream
outputs on disk and invalidates them whenever the defining proc-macro crate's
`Svh` changes.

#### 2.3 Complete `LangItem` inventory (`233` items) and `#![no_core]` floor

`compiler/rustc_attr_ir/src/lang_items.rs:151-542` (`language_item_table!`)
declares **`233` `LangItem` variants** (with `LanguageItems` enforcing a strict
1:1 bijection between `DefId` and `LangItem`, `lang_items.rs:48-55`). Across
`Target` and `GenericRequirement` constraints:

- **By required HIR `Target`:** `85` `Trait`s (operators, `Sized`/`MetaSized`/`PointeeSized`,
  `Copy`, `Clone`, `Sync`, `Freeze`, `Unpin`, `Drop`, `AsyncDrop`, `Fn`/`FnMut`/`FnOnce`,
  `AsyncFn*`, `Future`, `Iterator`, `Coroutine`, `Tuple`, `Unsize`,
  `CoerceUnsized`, `DispatchFromDyn`, `TransmuteTrait`, `Destruct`, `Receiver`,
  `LegacyReceiver`), `48` `Fn`s (panic formatting hooks, `exchange_malloc`,
  `box_free`, `drop_in_place`, `offset_of`, const-eval panic hooks, `start`),
  `41` `Struct`s (`PhantomData`, `ManuallyDrop`, `UnsafeCell`, `Pin`, `Range*`,
  `Arguments`, `Context`, `Poll`, `String`, `OwnedBox`, `GlobalAlloc` layout
  types, `CStr`), `15` trait methods (`next`, `into_iter`, `poll`, `resume`,
  `branch`, `from_residual`, `from_output`, `call*`), `14` trait `AssocTy`s
  (`Output`, `Item`, `IntoIter`, `Target`, `Metadata`, `Residual`), `8` enum
  `Variant`s (`Some`, `None`, `Ok`, `Err`, `Ready`, `Pending`, `Continue`,
  `Break`), `6` `Enum`s (`Option`, `Poll`, `ControlFlow`, `Ordering`,
  `CoroutineState`), `7` `AssocConst`s (`AlignOf`, `SizeOf`, float radixes), `4`
  inherent methods (`slice_len_fn`, etc.), `1` `Union`, `1` `ForeignTy`, and `1`
  `ForeignFn`.
- **By generic parameter arity (`GenericRequirement`):** `126` `None`
  (unconstrained), `53` `Exact(1)`, `44` `Exact(0)`, `4` `Exact(2)` (`Coroutine`,
  `Index`, `IndexMut`, `TransmuteTrait` variants), `4` `Minimum(1)` (`Unsize`,
  `CoerceUnsized`, `DispatchFromDyn`, `CoercePointeeValidated`), `1` `Exact(3)`
  (`TransmuteTrait`), and `1` `Exact(5)` (`asm` / contract/field lang item).
- **Crate tier distribution across `library/` and `#![no_core]` execution
  probes (`support/frontend_features_attrs_langitems.json`):**
  1. **`#![no_core]` absolute floor (`0` vs. `4`–`6` lang items):** Probing
     `rustc +nightly --edition=2024 --crate-type=rlib` confirms that a
     completely empty `#![no_core]` crate compiles (`rc = 0`) with **zero** lang
     items. Declaring even `pub struct Unit;` or `pub fn id(x: S) -> S`
     immediately fails with `error: requires 'copy' lang_item` unless the crate
     defines the **`4`-trait sizing and copy floor**: `pointee_sized`,
     `meta_sized`, `sized`, and `copy` (`rc = 0` on
     `copy_and_sized_hierarchy_without_freeze`). Adding shared-reference
     dereferencing (`*r` on `&i32`) and interior-mutability analysis requires
     `freeze` (with `#![feature(auto_traits)]`) and `legacy_receiver` (`rc = 0`
     on `copy_freeze_and_reference_floor`). Notice that `library/rtstartup`
     (`rbegin.rs`/`rend.rs`) defines exactly `7` `#![no_core]` lang items:
     `pointee_sized`, `meta_sized`, `sized`, `copy`, `sync`, `freeze`, and
     `drop_glue`.
  2. **`library/core` (`196` distinct `LangItem`s across `198` `#[lang = ...]`
     attributes):** Supplies all operator traits, `Option`/`Result`/`Poll`/`ControlFlow`,
     iterators, futures, coroutines, `Pin`, `UnsafeCell`, `ManuallyDrop`,
     `PhantomData`, formatting, and panic entry wrappers (`panic`,
     `panic_bounds_check`, `panic_nounwind`, `panic_misaligned_pointer_dereference`,
     `panic_null_pointer_dereference`).
  3. **`library/alloc` (`3` distinct `LangItem`s across `4` attributes):**
     `owned_box` (`alloc::boxed::Box`), `global_alloc_ty` (` Layout` / allocator
     hook), and `String` (`alloc::string::String`).
  4. **`library/std` & `library/compiler-builtins` (`2` `LangItem`s + `2` weak
     linker symbols):** `start` (`std::rt::lang_start`) and `eh_personality`
     (defined in `std::sys::personality` or `compiler-builtins`).
     `compiler/rustc_attr_ir/src/weak_lang_items.rs:26-29` marks exactly **`2`
     weak lang items**: `PanicImpl` (lowered to external symbol
     `rust_begin_unwind`, satisfied by `#[panic_handler]`) and `EhPersonality`
     (lowered to `rust_eh_personality`), which are only enforced when linking a
     final binary, `dylib`, `cdylib`, or `staticlib` that requires unwinding or
     panicking.
  5. **`32` `LangItem`s absent from `library/`:** Target-specific or unstable
     synthetic types (`ppcf128`, `x87_f80`, `x87_f80_raw`, `fn_static`),
     compiler-internal CTFE panic diagnostic items (`panic_const_add_overflow`
     through `panic_const_gen_fn_none_drop`), legacy `begin_panic` /
     `termination` (`termination` is in `std::process::Termination` under a
     macro/cfg or test), and `default_trait1..4` (used only in UI tests).

---

### 3. Built-in Compiler Lints, Lint Groups, and `E0xxx` Error Codes

Basis: source + execution

#### 3.1 Built-in lint declarations, levels, and pass architecture

Scanning all `declare_lint!`, `declare_tool_lint!`, and `declare_rustdoc_lint!`
invocations across `compiler/` and `src/librustdoc/` at
`412be32a6a189d9a28922beee178bc0abee9d492` extracts **`261` built-in compiler
lints** (`155` in `compiler/rustc_lint_defs/src/builtin.rs` and `106` in
`compiler/rustc_lint/src/**`) plus **`31` scoped tool lints** (`17` `rustc::*`
compiler-hygiene lints in `compiler/rustc_lint/src/` and `14` `rustdoc::*`
documentation lints in `src/librustdoc/lint.rs`):

- **Default severity levels (`261` compiler + `31` tool lints):** **`63`
  `Allow`**, **`144` `Warn`**, **`54` `Deny`**, and **`0` `Forbid`** (`Forbid`
  is never used as a built-in default so downstream crates can `#[allow(...)]`
  or `--cap-lints` every built-in lint; `rustc -W help` on `+nightly` reports
  `258` non-internal user-visible lints: `63` `allow`, `142` `warn`, `53`
  `deny`, matching the source table after excluding `3` test/internal-only
  lints; `1.99.1` reported `249`). Among the `17` `rustc::*` internal tool
  lints, `15` default to `Allow`, `1` to `Warn` (`rustc::disallowed_pass_by_ref`),
  and `1` to `Deny` (`rustc::bad_opt_access`); among the `14` `rustdoc::*` tool
  lints, `10` default to `Warn` (including `broken_intra_doc_links`,
  `private_intra_doc_links`, `invalid_codeblock_attributes`,
  `invalid_html_tags`, `bare_urls`, `invalid_rust_codeblocks`,
  `redundant_explicit_links`, `broken_footnote`, `unused_footnote_definition`,
  and `invalid_markdown_table`) and `4` default to `Allow`
  (`missing_crate_level_docs`, `private_doc_tests`, `unescaped_backticks`, and
  unstable `missing_doc_code_examples`).
- **Four-phase lint execution pipeline (`compiler/rustc_lint/src/lib.rs:167-230`):**
  1. `BuiltinCombinedPreExpansionLintPass` (`1` AST pass before macro expansion:
     `KeywordIdents`).
  2. `BuiltinCombinedEarlyLintPass` (`15` post-expansion AST passes:
     `UnusedParens`, `UnusedBraces`, `UnsafeCode`, `NonAsciiIdents`, `Expr2024`,
     `Precedence`, `RedundantSemicolons`, etc.).
  3. `BuiltinCombinedLateLintModPass` + crate-wide late HIR/TyCtxt passes
     (type-directed lints, `dead_code`, `unused_must_use`, `improper_ctypes`,
     `static_mut_refs`, `impl_trait_overcaptures`, etc.).
  4. `hardwired::lint_vec()` (`builtin.rs:15-165`): lints buffered or emitted
     inline during parsing, attribute checking (`rustc_attr_parsing`), name
     resolution, MIR construction (`tail_expr_drop_order`), const-eval, or
     borrow checking, resolved against scoped `#[allow]`/`#[warn]`/`#[expect]`/`#[deny]`/`#[forbid]`
     via `HirId` level tables (`rustc_lint/src/levels.rs`) and RFC 2383
     `#[expect(...)]` fulfillment (`rustc_lint/src/expect.rs`).
- **Future-incompatibility metadata (`71` lints):** `42` `FutureReleaseError`
  (grouped dynamically into `future_incompatible`, causing Cargo to cache and
  display a future-breakage report even for dependencies built with
  `--cap-lints=allow`!), `16` `EditionError`, `11` `EditionSemanticsChange`, and
  `2` custom reasons.

#### 3.2 Lint groups, aliases, and `518` `E0xxx` error codes

`LintStore` (`compiler/rustc_lint/src/{lib.rs:342-782,context.rs:212-305}`)
registers:

- **`10` explicit groups:** `nonstandard_style` (`3` lints, aliased to
  `bad_style`), `unused` (`25` lints), `let_underscore` (`2`),
  `rust_2018_idioms` (`4`), `keyword_idents` (`2`), `refining_impl_trait` (`2`),
  `deprecated_safe` (`1`), `unknown_or_malformed_diagnostic_attributes` (`4`),
  `rustc::internal` (`15` compiler-tree lints), and `rustdoc::all`.
- **`6` dynamic groups:** `warnings` (all lints currently at `Warn`),
  `future_incompatible` (all non-edition FCW lints), and
  `rust_2015_compatibility` / `rust_2018_compatibility` /
  `rust_2021_compatibility` / `rust_2024_compatibility` /
  `edition_future_compatibility` (populated automatically from
  `FutureIncompatibilityReason::edition()`).
- **Backwards-compatibility tombstones:** `18` `register_renamed` pairs, `8`
  `register_ignored` legacy bare `rustdoc` lint names, and `68`
  `register_removed` lint names (emitting `RENAMED_AND_REMOVED_LINTS` rather
  than `UNKNOWN_LINTS`).

`compiler/rustc_error_codes/src/lib.rs:27-691` registers **`518` four-digit
`E0xxx` codes** (`E0001` through `E0806`), each backed by a Markdown explanation
in `compiler/rustc_error_codes/src/error_codes/E*.md` for `rustc --explain E0xxx`.
Of those `518` codes, **`387` are actively emitted** at
`412be32a6a189d9a28922beee178bc0abee9d492` and **`131` are retired** (marked
*"Note: this error code is no longer emitted by the compiler"*). A standalone
compiler targeting Cargo and IDE parity must preserve `E0xxx` codes on JSON
diagnostics (`code.code`) where tests, `compiletest`, or IDE quick-fixes match
specific error numbers (most notably `E0308` mismatched types, `E0277` trait
bound unsatisfied, `E0382`/`E0499`/`E0502`/`E0505`/`E0507`/`E0597` borrow/move
errors, `E0425`/`E0432`/`E0433` unresolved names, `E0133` unsafe obligations,
`E0554`/`E0658` unstable feature gates, and `E0460`/`E0463` crate metadata
errors).

---

### 4. Type System, Trait Solver (`NextSolver` vs. Legacy), Pattern Analysis, and Borrow Checker (`NLL` vs. `Polonius`)

Basis: source + derived

Table 3 summarizes the nine crates implementing type checking, trait solving,
exhaustiveness checking, THIR/MIR lowering, and borrow checking at
`412be32a6a189d9a28922beee178bc0abee9d492` (`194,421` SLOC total).

| Crate | `.rs` Files | Raw Lines | SLOC | Architectural Role & Coupling |
| :--- | ---: | ---: | ---: | :--- |
| `rustc_type_ir` | 52 | 20,562 | 14,255 | `TyCtxt`-independent generic `Interner` representation of types, clauses, canonical vars, and proof trees |
| `rustc_next_trait_solver` | 25 | 12,856 | 9,568 | Canonicalized coinductive/inductive goal solver (`EvalCtxt`, `SearchGraph`), generic over `SolverDelegate` |
| `rustc_infer` | 39 | 13,543 | 9,385 | `InferCtxt` unification tables (`ena`), generalization, region obligations, and opaque-type provisional storage |
| `rustc_trait_selection` | 72 | 51,827 | 41,023 | Legacy `SelectionContext`/`FulfillmentContext` + `FulfillmentEngine` dispatcher (`Old` vs `Next`) + coherence |
| `rustc_hir_analysis` | 53 | 41,020 | 32,071 | Item signature collection (`type_of`, `generics_of`, `predicates_of`), variance, WF checking, coherence orphan/overlap |
| `rustc_hir_typeck` | 40 | 50,633 | 39,630 | Body expression/pattern checking (`FnCtxt`), method lookup, coercions, autoderef, closure `upvar` capture, `TypeckResults` |
| `rustc_pattern_analysis` | 10 | 5,212 | 3,102 | `TyCtxt`-independent pattern exhaustiveness & usefulness engine (`PatCx`, `21` `Constructor` kinds) |
| `rustc_mir_build` | 39 | 23,282 | 17,536 | HIR -> `thir::Body` lowering and THIR -> `mir_built` CFG construction (LIFO drop scopes, match decision trees) |
| `rustc_borrowck` | 62 | 36,847 | 27,851 | MIR typeck, NLL region SCC inference, two-phase borrows, `Polonius` (`Legacy` & `Next`), opaque-type member constraints |

#### 4.1 Boundary between `rustc_hir_typeck`, legacy `rustc_trait_selection`, and `rustc_next_trait_solver`

1. **Item collection vs. body checking:** `rustc_hir_analysis` answers signature
   queries (`type_of`, `fn_sig`, `generics_of`, `explicit_predicates_of`,
   `variances_of`, `check_well_formed`) without inspecting function bodies,
   except for return-position opaque types (`impl Trait`), whose concrete hidden
   types are constrained during body `typeck` and finalized during
   `mir_borrowck`. `rustc_hir_typeck` (`FnCtxt` in
   `compiler/rustc_hir_typeck/src/fn_ctxt/mod.rs:47`) checks each body owner and
   produces `TypeckResults<'tcx>`, recording resolved method targets, implicit
   `Adjustment` chains (`Deref`, `Borrow`, `PointerCoercion`, `NeverToAny`),
   upvar capture modes (`CaptureInfo`), and user type annotations for THIR
   lowering.
2. **Where the next-generation trait solver is already normative on stable Rust:**
   `compiler/rustc_session/src/config.rs:1071-1086` defines
   `NextSolverConfig::{Coherence, Globally}` and defaults to **`Coherence`**
   whenever `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY` is unset. In
   `compiler/rustc_trait_selection/src/traits/engine.rs:34-54`,
   `FulfillmentEngine::new(infcx)` selects `FulfillmentEngine::Next` whenever
   `infcx.next_trait_solver()` is true—which is **unconditionally enabled during
   trait coherence overlap checking (`rustc_hir_analysis::coherence`) on stable
   Rust** as well as globally under `-Znext-solver=globally`.
   - **Key semantic difference a standalone compiler must replicate:** During
     coherence (`InCrate::Remote` negative reasoning), `rustc_next_trait_solver`
     evaluates canonicalized goals (`Goal<I, I::Predicate>`) over `5`
     `CandidateSource`s (`Impl`, `BuiltinImpl`, `ParamEnv`, `AliasBound`,
     `CoherenceUnknowable`), unifies lazy alias/projection normalization
     (`NormalizesTo`) directly inside goal solving rather than as a separate
     pre-pass, and handles active search-graph cycles (`search_graph.rs`)
     coinductively for auto traits/`WellFormed` and inductively (least fixed
     point) for ordinary traits. Replicating only the legacy `SelectionContext`
     accepts unsound coherence overlaps and rejects valid bidirectional
     associated-type equalities that stable `rustc` now decides via
     `NextSolverConfig::Coherence`.

#### 4.2 Pattern exhaustiveness (`rustc_pattern_analysis`)

`compiler/rustc_pattern_analysis/src/{constructor.rs,usefulness.rs}` isolates
exhaustiveness and arm-reachability checking behind the `PatCx` trait (used both
on THIR during `mir_build` and standalone). Every `DeconstructedPat<Cx>` is
classified into one of **`21` `Constructor<Cx>` variants** (`Struct`, `Variant`,
`Ref`, `Slice`, `UnionField`, `Bool`, `IntRange`, `F16Range`, `F32Range`,
`F64Range`, `F128Range`, `Str`, `DerefPattern`, `Opaque`, `Or`, `Wildcard`,
`Never`, `NonExhaustive`, `Hidden`, `Missing`, and `PrivateUninhabited`).
`compute_exhaustiveness_and_usefulness` (`usefulness.rs:1698`) specializes the
`Matrix` column-by-column after splitting wildcard constructor sets
(`ConstructorSet::split`), accounting for `#[non_exhaustive]` foreign ADTs,
visibly uninhabited `!`/empty-enum fields (gated by reference indirection and
privacy), and `#![pattern_complexity_limit]`.

#### 4.3 Borrow checking: NLL, two-phase borrows, `Polonius` (`Off`/`Legacy`/`Next`), and opaque types

`rustc_borrowck` (`root_cx.rs:269` `do_mir_borrowck`, `nll.rs:114`
`compute_regions`) checks `mir_promoted` in five stages:

1. **Region renumbering & universal regions (`nll.rs:56-76`):**
   `replace_regions_in_mir` replaces every erased HIR region in the MIR body and
   its `Promoted` constants with fresh existential `RegionVid` variables and
   populates `UniversalRegions` (`'static`, input/output free lifetimes, and
   `ParamEnv` outlives relations).
2. **MIR type check & liveness (`type_check/mod.rs`):** Re-checks every MIR
   statement and terminator to generate outlives constraints
   `('r_sub: 'r_sup) @ Location` (`OutlivesConstraint`), `TypeTest` bounds, and
   reverse-CFG variable/region liveness (`LivenessValues`).
3. **Two-phase borrows (`BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }`):**
   Generated for autoref method receivers (`vec.push(vec.len())`). A two-phase
   loan has a *reservation* point and a *activation* point: between reservation
   and activation, shared reads of the borrowed place are permitted, whereas
   conflicting mutations invalidate the loan (`borrow_set.rs`
   `TwoPhaseActivation`).
4. **Region & loan propagation across `Polonius::{Off, Legacy, Next}`
   (`config.rs:3838-3858`, `polonius/mod.rs:64-120`):**
   - **`Polonius::Off` (default NLL):** Condenses the location-insensitive
     `OutlivesConstraint` graph into strongly connected components (`SCC`s in
     `region_infer/reverse_sccs.rs`) so each `RegionVid` holds a set of CFG
     `Location`s + universal regions, then propagates active `BorrowIndex` loans
     forward along CFG edges (`Borrows` dataflow) until the borrowed region goes
     dead or the borrowed `Place` is overwritten (`loan_killed_at`). Because NLL
     region values are *location-insensitive*, returning a reference in one
     match arm artificially extends that loan across sibling arms (the classic
     NLL Problem Case #3 false positive).
   - **`Polonius::Legacy` (`-Zpolonius` / `-Zpolonius=legacy`):** Emits
     `14` relational tables (`PoloniusFacts = AllFacts<RustcFacts>` in
     `polonius/legacy/facts.rs:73`: `loan_issued_at`, `universal_region`,
     `cfg_edge`, `loan_killed_at`, `subset_base`, `loan_invalidated_at`,
     `var_used_at`, `var_defined_at`, `var_dropped_at`, `use_of_var_derefs_origin`,
     `drop_of_var_derefs_origin`, `child_path`, `path_is_var`, `path_assigned_at_base`,
     `path_moved_at_base`, `path_accessed_at_base`, `known_placeholder_subset`,
     `placeholder`) to the external Datalog `polonius_engine`.
   - **`Polonius::Next` (`-Zpolonius=next`, controlled at build time by
     `CFG_DEFAULT_POLONIUS_NEXT`):** Keeps the entire NLL pipeline in-tree and
     augments it with a flow-sensitive `LocalizedConstraintGraph`
     (`polonius/constraints.rs`) whose nodes are `(RegionVid, PointIndex)` pairs
     and whose inter-point edges follow type variance (`ConstraintDirection::Forward`
     for covariant regions, `Backward` for contravariant, bidirectional for
     invariant, enabling loans to flow "back in time" across invariant mutable
     references in loops) packed into a flat bitset matrix `LiveLoans`
     (`num_points * num_borrows`, `polonius/mod.rs:65-85`).
5. **Opaque-type hidden-type region resolution
   (`region_infer/opaque_types/mod.rs:66-127`, `member_constraints.rs`):**
   Defining uses of RPIT/TAIT opaque types inside a body constrain existential
   NLL region variables via **`MemberConstraint`s** ($\text{R}_{\text{member}}$
   must equal one of the captured choice regions $\{ 'a_1, \dots, 'a_k,
   \text{'static} \}$). `nll_var_to_universal_region` maps each member SCC
   representative to a unique non-external universal region in `OpaqueTypeKey`,
   rejecting non-defining uses or ambiguous equal lifetimes (`DeferredOpaqueTypeError`).

---

### 5. Procedural Macro Bridge Wire Protocol (`proc_macro::bridge`)

Basis: source

#### 5.1 Dynamic library symbol contract and `BridgeConfig<'a>` C-ABI isolation

Unlike `rustc_driver` plugins, compiled procedural macro crates (`--crate-type
proc-macro`) are **ABI-isolated** from internal `rustc_*` data structures
(`library/proc_macro/src/bridge/{mod.rs,buffer.rs,client.rs,rpc.rs,handle.rs}`
[`1,571` SLOC across `12` files] and
`compiler/rustc_expand/src/proc_macro_server.rs` [`714` SLOC]).

1. **Exported dylib symbol (`compiler/rustc_builtin_macros/src/proc_macro_harness.rs`,
   `compiler/rustc_metadata/src/host_dylib.rs`):** Every `proc-macro` shared
   library embeds a `.rustc` metadata section (carrying `ProcMacroData` in
   `CrateRoot`) and exports a single data symbol:
   `__rustc_proc_macro_decls_<StableCrateId_16hex>__: &[bridge::client::ProcMacro]`.
   `ProcMacro` has three variants (`CustomDerive { trait_name, attributes, client }`,
   `Attr { name, client }`, `Bang { name, client }`), where every `Client` holds:
   - `get_symbol_table`: `extern "C" fn() -> ...` / version check against
     `RUSTC_VERSION_STRING` (note: `rustc` checks `MetadataBlob::check_version`
     on the `.rustc` section before `dlsym`!), and
   - `run: extern "C" fn(BridgeConfig<'_>) -> Buffer`.
2. **`#[repr(C)]` `BridgeConfig<'a>` (`mod.rs:120-129`) and `Buffer`
   (`buffer.rs:7-14`):**
   ```rust
   #[repr(C)]
   pub struct Buffer {
       data: *mut u8,
       len: usize,
       capacity: usize,
       reserve: extern "C" fn(Buffer, usize) -> Buffer,
       drop: extern "C" fn(Buffer),
   }

   #[repr(C)]
   pub struct BridgeConfig<'a> {
       input: Buffer,
       dispatch: closure::Closure<'a>, // #[repr(C)] { env: *mut (), call: extern "C" fn(*mut (), Buffer) -> Buffer }
       force_show_panics: bool,
   }
   ```
   Because `Buffer` carries its own `extern "C"` `reserve` and `drop` vtable
   pointers, the host compiler and the proc-macro dylib can use completely
   independent global allocators (`jemalloc` vs `mimalloc` vs system `malloc`)
   without UB! Furthermore, `run_client` (`client.rs:245-295`) wraps user macro
   execution in `std::panic::catch_unwind`, encoding any panic as
   `Result::<TokenStream, PanicMessage>::Err` inside the returned `Buffer` so
   stack unwinding never crosses the FFI boundary.

#### 5.2 Wire framing (`Encode`/`Decode`), `HandleStore`, and all `31` `ApiTags` RPCs

All values in `BridgeConfig::input`, `Closure` requests, and return `Buffer`s
use deterministic unaligned byte packing (`library/proc_macro/src/bridge/rpc.rs:15-259`):

- **Primitives & containers:** `()` -> `0` bytes; `u8` -> `1` byte; `bool` -> `u8`
  (`0` or `1`); `u32` and `NonZero<u32>` -> `4`-byte little-endian; `usize` ->
  **always `8`-byte little-endian** (`MAX_USIZE_SIZE = 8` zero-padded on 32-bit
  hosts, `rpc.rs:119-155`); `&str` / `String` / `&[T]` / `Vec<T>` -> `usize`
  length followed by elements; `enum`s (`Option`, `Result`, `ApiTags`,
  `Delimiter`, `Level`, `LitKind`, `TokenTree`, `Spacing`, `IdentKind`) -> `1`-byte
  `u8` variant tag (`0..N-1` in declaration order) followed by variant fields.
- **Opaque handle arenas (`handle.rs:15-95`):** Server-side compiler objects
  cross the bridge as `NonZero<u32>` handles (`1`-indexed monotonic counters
  stored in `HandleStore<S>`):
  - `TokenStream`: `OwnedStore` (supports `alloc` and explicit `ts_drop` slot
    reclamation; cloned explicitly via `ts_clone`).
  - `Span` and `Symbol`: `InternedStore` (deduplicated via `FxHashMap` for the
    duration of a single macro invocation; freed in bulk when `run_server`
    returns).
- **Initial `BridgeConfig::input` frame:** Encodes `(ExpnGlobals<Span>, input_handles)`
  where `ExpnGlobals` supplies `(def_site: Span, call_site: Span, mixed_site: Span)`
  upfront so `Span::call_site()` / `Span::mixed_site()` need zero round-trip RPCs!
- **Complete `31`-method `ApiTags` RPC table (`mod.rs:33-82,134-152`):** Every
  client->server callback writes `ApiTags` (`u8` `0..=30`) followed by encoded
  arguments into `Buffer`, calls `BridgeConfig::dispatch`, and decodes the
  response `Buffer`:

| `u8` Tag | RPC Method | Wire Arguments | Wire Return Type | Server Semantics (`proc_macro_server.rs`) |
| ---: | :--- | :--- | :--- | :--- |
| `0` | `track_env_var` | `var: &str, value: Option<&str>` | `()` | Records `env_depinfo` for Cargo `.d` & incremental rebuilds (`proc_macro::tracked::env_var`) |
| `1` | `track_path` | `path: &str` | `()` | Records file dependency in `file_depinfo` |
| `2` | `literal_from_str` | `s: &str` | `Result<Literal<Span, Symbol>, String>` | Lexes single literal (`11`-variant `LitKind`: `Byte`, `Char`, `Integer`, `Float`, `Str`, `StrRaw(u8)`, `ByteStr`, `ByteStrRaw(u8)`, `CStr`, `CStrRaw(u8)`, `ErrWithGuar`) |
| `3` | `emit_diagnostic` | `Diagnostic<Span>` | `()` | Emits `proc_macro::Diagnostic` (`Level::{Error,Warning,Note,Help}` + child notes + multi-spans) |
| `4`–`13` | `ts_drop`, `ts_clone`, `ts_is_empty`, `ts_expand_expr`, `ts_from_str`, `ts_to_string`, `ts_from_token_tree`, `ts_concat_trees`, `ts_concat_streams`, `ts_into_trees` | `TokenStream` (`NonZero<u32>`), `&str`, or `Vec<TokenTree>` | `()`, `bool`, `String`, `TokenStream`, `Result<TokenStream, ...>`, or `Vec<TokenTree>` | Token-stream lifecycle, lexer parsing (`ts_from_str`), eager literal/macro expression expansion (`ts_expand_expr`), and structural unpacking into `Group`/`Ident`/`Punct`/`Literal` |
| `14`–`29` | `span_debug`, `span_parent`, `span_source`, `span_byte_range`, `span_start`, `span_end`, `span_line`, `span_column`, `span_file`, `span_local_file`, `span_join`, `span_subspan`, `span_resolved_at`, `span_source_text`, `span_save_span`, `span_recover_proc_macro_span` | `Span` (`NonZero<u32>`), `Bound<usize>`, or `usize` | `String`, `Option<String>`, `usize`, `Range<usize>`, `Span`, or `Option<Span>` | SourceMap location queries, hygiene transplanting (`span_resolved_at`), and cross-crate `quote!` span persistence (`span_save_span` -> `ProcMacroData::proc_macro_quoted_spans`) |
| `30` | `symbol_normalize_and_validate_ident` | `string: &str` | `Result<Symbol, ()>` | NFC Unicode normalization (`UNICODE_VERSION`) and XID identifier validation |

**Standalone-compiler hosting consequence:** A standalone compiler has two sound
options for procedural macros:
1. **Direct in-process C-ABI hosting:** Compile `proc-macro` crates into native
   host shared libraries exporting `__rustc_proc_macro_decls_<StableCrateId>__`
   (linking the compiler's own sysroot `libproc_macro.rlib`) and implement the
   `31`-tag `BridgeConfig` server loop in ~700 lines of host code. Even if the
   standalone compiler is written in C++, OCaml, or Lean, `BridgeConfig` and
   `Buffer` are pure `#[repr(C)]` + `extern "C"`.
2. **Out-of-process `proc-macro-srv` delegation:** Spawn an isolated worker
   process (identical in architecture to `rust-analyzer-proc-macro-srv`
   `CURRENT_API_VERSION = 6`, documented in
   `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts`) so crashes,
   `-Cpanic=abort` aborts, or memory corruption inside untrusted proc-macros
   cannot corrupt the compiler process. Note that a `proc-macro` `.so` compiled
   by toolchain $A$ can only be loaded by a `proc_macro` server whose
   `bridge::rpc` tag layout matches $A$'s `libproc_macro`.

---

### 6. `.rmeta` Binary Schema (`METADATA_VERSION = 12`), `StableCrateId`, `Svh`, and `rustdoc` JSON (`FORMAT_VERSION = 61`)

Basis: source + execution + derived

#### 6.1 `.rmeta` v10 -> v12 binary header evolution and `LazyValue`/`LazyArray`/`LazyTable` encoding

Between Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and
`1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and
`412be32a6a189d9a28922beee178bc0abee9d492`), `compiler/rustc_metadata/src/rmeta/{mod.rs:73-92,encoder.rs:2720-2855}`
bumped `METADATA_VERSION` from `10` to **`12`**. Table 4 compares the exact header
layout verified empirically on a `specimen` crate (`support/frontend_features_attrs_langitems.json`).

| Byte Offset | `1.99.1` (`METADATA_VERSION = 10`) | `1.102.0-nightly` (`METADATA_VERSION = 12`) | Purpose & Decoder Gate |
| :--- | :--- | :--- | :--- |
| `0..8` | `72 75 73 74 00 00 00 0a` (`b"rust\0\0\0\x0a"`) | `72 75 73 74 00 00 00 0c` (`b"rust\0\0\0\x0c"`) | `METADATA_HEADER` magic + `u8` format version |
| `8..16` | `u64` LE `CrateRoot` offset (`2591` in `2980`-B probe) | `u64` LE `CrateRoot` offset (`2246` in `2982`-B probe) | Post-order pointer to hashed `CrateRoot` |
| `16..24` | *(Start of LEB128 `rustc_version` string)* | `u64` LE `CrateRootUnhashed` offset (`2599`; `0` on stubs) | Post-order pointer to unhashed filename trailer |
| `24..40` | *(Inside `rustc_version` / payload)* | `128`-bit LE `Fingerprint` (`Svh`, e.g. `fb12d432...21604739`) | Fast O(1) `get_crate_hash()` without decoding `CrateRoot` |
| `40..` (`16..` in v10) | `"rustc 1.99.1 (58cf8f9c3 2026-10-13)"` | `"rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)"` | Checked *before* `CrateRoot` decode to emit clean version-mismatch error |

All interior `.rmeta` structures are serialized in post-order using three lazy
pointer primitives (`rmeta/mod.rs:110-213`, `rmeta/table.rs:8-611`):
- **`LazyValue<T>`:** Relative byte distance (`NonZero<usize>`) from the
  containing node's start (for the first `Lazy` field) or forward distance from
  the preceding `Lazy` target (for subsequent fields).
- **`LazyArray<T>`:** `(position, num_elems)` enabling zero-cost slice skipping
  (`num_elems == 0` encodes zero position bytes).
- **`LazyTable<IdxEncode, IdxDecode, T>`:** O(1) random-access table indexed by
  `DefIndex` (after deterministic `LocalDefsRemapping` sorting non-deterministic
  local definitions by `(parent_depth, def_path_hash.local_hash())`,
  `rmeta/mod.rs:455-498`). `width_and_sparse` packs a low-bit sparse flag (`64`-entry
  blocks with `12`-byte sparse bitmask+offset headers when sparse saves space,
  `table.rs:8-9`) and runtime-selected element byte width `1..=8` (stripping
  leading zero bytes). Spans use `1`-byte `SpanTag` headers (`[len:5 | root_ctxt:1 |
  kind:2]` for `Local`/`Foreign`/`Partial`/`Indirect`, `rmeta/mod.rs:751-828`).

#### 6.2 Complete `CrateRoot` (`48` fields) and `LazyTables` (`82` per-`DefIndex` tables) inventory

`CrateRoot` (`rmeta/mod.rs:276-335`) contains **`48` fields**, flanked by
`CrateRootUnhashed` (`extra_filename` + `dep_extra_filenames`, `mod.rs:340-347`):

- **Identity, ABI & runtime flags (`18` scalar/header fields):** `header`
  (`CrateHeader { triple, name, is_proc_macro_crate, is_stub }`),
  `stable_crate_id`, `required_panic_strategy`, `panic_in_drop_strategy`,
  `edition`, `has_global_allocator`, `has_alloc_error_handler`,
  `has_panic_handler`, `has_default_lib_allocator`, `compiler_builtins`,
  `needs_allocator`, `needs_panic_runtime`, `no_builtins`, `panic_runtime`,
  `profiler_runtime`, `symbol_mangling_version`, `specialization_enabled_in`,
  and `proc_macro_data: Option<ProcMacroData>`.
- **Crate-wide index arrays & hygiene tables (`29` `LazyArray`/`LazyValue`/`LazyTable`
  fields):** `crate_deps` (`CrateDep { name, hash: Svh, host_hash, kind, is_private }`),
  `dylib_dependency_formats`, `lib_features`, `stability_implications`,
  `lang_items`, `lang_items_missing`, `stripped_cfg_items`, `diagnostic_items`,
  `canonical_symbols`, `fake_doc_items`, `externally_implementable_items`,
  `native_libraries`, `foreign_modules`, `traits`, `impls` (with `SimplifiedType`
  fast-reject keys), `incoherent_impls`, `interpret_alloc_index`,
  `debugger_visualizers`, `exportable_items`, `stable_order_of_exportable_impls`,
  `exported_non_generic_symbols`, `exported_generic_symbols`, `syntax_contexts`,
  `expn_data`, `expn_hashes`, `def_path_hash_map` (sorted O(log N) binary-search
  table mapping `DefPathHash::local_hash` -> `DefIndex`), `source_map`,
  `target_modifiers` (ABI-unsoundness flag guards like `-Zsanitizer` /
  `-Cpanic`), and `denied_partial_mitigations`.
- **`tables: LazyTables` (`82` per-`DefIndex` random-access tables in
  `define_tables!`, `rmeta/mod.rs:623-727`):**
  - **`21` `defaulted` tables:** `intrinsic`, `is_macro_rules`,
    `type_alias_is_checked`, `attr_flags` (`IS_DOC_HIDDEN`), `def_path_hashes`
    (dense `u64` local half for every `DefIndex`), `explicit_item_bounds`,
    `explicit_item_self_bounds`, `inferred_outlives_of`,
    `explicit_super_clauses_of`, `explicit_implied_clauses_of`,
    `explicit_implied_const_bounds`, `inherent_impls`, `opt_item_name`,
    `module_children_reexports`, `ambig_module_children`, `cross_crate_inlinable`,
    `asyncness`, `constness`, `safety`, `defaultness`, and
    `impl_is_fully_generic_for_reflection`.
  - **`61` `optional` tables (`Option<T>`):** Module/HIR skeleton (`def_kind`,
    `def_keys`, `visibility`, `def_span`, `def_ident_span`, `attributes`,
    `module_children_non_reexports`, `associated_item_or_field_def_ids`,
    `assoc_container`, `variant_data`, `default_fields`, `repr_options`,
    `params_in_repr`, `macro_definition`, `expn_that_defined`), type/trait
    signatures (`generics_of`, `explicit_clauses_of`, `type_of`, `variances_of`,
    `fn_sig`, `fn_arg_idents`, `impl_trait_header`, `impl_parent`, `trait_def`,
    `const_param_default`, `object_lifetime_default`, `coerce_unsized_info`,
    `const_conditions`, `opaque_ty_origin`, `opt_rpitit_info`,
    `collect_return_position_impl_trait_in_trait_tys`, `assumed_wf_types_for_rpitit`,
    `associated_types_for_impl_traits_in_trait_or_impl`,
    `args_known_to_outlive_alias_params`, `anon_const_kind`, `const_of_item`,
    `mut_restriction`), MIR/CTFE/codegen (`optimized_mir` [encoded for generic,
    `#[inline]`, or `-Zalways-encode-mir` items], `mir_for_ctfe` [`const fn` and
    constants], `promoted_mir`, `mir_const_qualif`, `mir_coroutine_witnesses`,
    `closure_saved_names_of_captured_variables`, `coroutine_kind`,
    `coroutine_for_closure`, `coroutine_by_move_body_def_id`, `trivial_const`,
    `rendered_const`, `rendered_precise_capturing_args`,
    `thir_abstract_const`, `eval_static_initializer`, `adt_destructor`,
    `adt_async_destructor`, `codegen_fn_attrs`, `deduced_param_attrs`), and
    stability/rustdoc (`lookup_stability`, `lookup_const_stability`,
    `lookup_default_body_stability`, `lookup_deprecation_entry`,
    `doc_link_resolutions`, `doc_link_traits_in_scope`).

#### 6.3 `StableCrateId` vs. `Svh` (`StrictVersionHash`) and when `.rmeta` compatibility is (or is not) required

1. **`StableCrateId` (`64`-bit `Hash64`, `compiler/rustc_span/src/def_id.rs:154-202`):**
   Hashed via `StableHasher` (`SipHash-1-3`) over **four** inputs in exact order:
   `crate_name.as_str()`, `b"metadata"` followed by sorted/deduplicated
   `-Cmetadata` strings with `usize` length prefixes, `b"exe"` or `b"lib"`, and
   `RUSTC_FORCE_RUSTC_VERSION` (else `cfg_version`). `StableCrateId` namespaces
   v0/legacy mangled symbols, `DefPathHash` upper 64-bit halves, and
   `__rustc_proc_macro_decls_<StableCrateId>__`.
2. **`Svh` (`128`-bit `Fingerprint`, `rmeta/encoder.rs:835-846,2725-2753`):**
   At `412be32a6a189d9a28922beee178bc0abee9d492` (`-Zmetadata-crate-hash=yes`,
   default `true`), `Svh` is an **`XxHash3_128`** digest seeded with a
   `StableHasher` `supplement: Fingerprint` (`tcx.sess.opts.dep_tracking_hash(true)`
   + `compute_hir_hash(tcx)` covering `global_asm!` and non-exported HIR bodies)
   and fed every byte flushed to `.rmeta` up to `CrateRoot`. `CrateRootUnhashed`
   (`extra_filename` and `dep_extra_filenames`) is written *after* finalizing
   `XxHash3_128`. Our live `+nightly` probe confirms that changing
   `-Cextra-filename=-ef1` to `-Cextra-filename=-ef2_longer_suffix` grows `.rmeta`
   from `2,982` to `2,996` bytes (`+14` bytes) while keeping the `128`-bit `Svh`
   at bytes `24..40` bit-for-bit identical
   (`fb12d432588a3d526996e4ff21604739`). Downstream crates embed each upstream
   dependency's `Svh` in `CrateDep::hash` and reject mismatched diamonds with
   `E0460` (`found possibly newer version of crate`).
3. **When cross-compiler `.rmeta` binary compatibility is vs. is NOT required:**
   - **NOT required (standard Cargo & `rustup` operation):** Even upstream
     `rustc` refuses `.rmeta` files from any other `rustc` commit
     (`MetadataBlob::check_version` compares `rustc_version` before reading
     `CrateRoot`). Because Cargo always invokes a single `RUSTC` toolchain to
     compile the entire dependency DAG against that toolchain's own sysroot
     (`libcore`, `liballoc`, `libstd`), **a standalone compiler may define its
     own `.rmeta` wire format** as long as: (a) `--emit=metadata` writes
     `<prefix><crate><extra>.rmeta`, (b) `.rlib` archives include `lib.rmeta`,
     (c) `dylib`/`proc-macro` shared libraries embed `.rustc`, and (d) the
     compiler's own crate loader round-trips all semantic tables above (including
     cross-crate generic/inlineable MIR, `macro_rules!`, lang/diagnostic items,
     traits, coherence `SimplifiedType` impls, stability, and `Svh` diamond
     checks).
   - **REQUIRED only for mixed-compiler builds:** Mixing prebuilt upstream
     `rustc` `.rlib`s without recompiling from source—or running upstream
     `rustc_driver` tools (`clippy`, `miri`) directly against artifacts emitted
     by the standalone compiler—would require exact `METADATA_VERSION = 12` +
     identical `rustc_version` string spoofing, which is neither expected nor
     safe across independent compilers.

#### 6.4 `rustdoc` JSON schema contract (`src/rustdoc-json-types`)

Unlike `.rmeta`, **`rustdoc --output-format=json` is an externally consumed
machine interface** parsed via `serde` (and optionally zero-copy `rkyv` `0.8` at
`412be32a6a189d9a28922beee178bc0abee9d492`, `src/rustdoc-json-types/lib.rs:126-147`)
by ecosystem tools (`cargo-semver-checks`, `cargo-public-api`, docs.rs):

- **Schema version:** `FORMAT_VERSION: u32 = 61` (`lib.rs:118`, verified
  identically in both `412be32a6a189d9a28922beee178bc0abee9d492` source and our
  live `rustdoc +nightly -Zunstable-options --output-format=json` probe on
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Root `Crate` object (`lib.rs:128-147`, `57` public structs/enums total):**
  Contains exactly **`8` top-level keys**:
  1. `root: Id` (`u32` opaque key of the crate root `Module` in `index`),
  2. `crate_version: Option<String>` (`--crate-version`),
  3. `includes_private: bool` (`--document-private-items`),
  4. `index: HashMap<Id, Item>` (all documented local items plus referenced
     external traits/blanket impls; `54` items on our `13`-line specimen due to
     synthesized `Borrow`/`From`/`Into`/`TryFrom`/`TryInto`/`Any` blanket impls!),
  5. `paths: HashMap<Id, ItemSummary>` (`crate_id`, `path: Vec<String>`,
     `kind: ItemKind` for intra-doc link resolution; `913` entries including
     `core`/`std` items on our specimen),
  6. `external_crates: HashMap<u32, ExternalCrate>` (`name`, `html_root_url`,
     `attrs`),
  7. `target: Target` (`triple: String` + `target_features: Vec<TargetFeature>`
     with `name`, `implies_features`, `unstable_feature_gate`, and
     `globally_enabled`; `78` x86_64 user-selectable target features emitted in
     our live probe), and
  8. `format_version: u32` (`61`).
- **`Item` and `21`-variant `ItemEnum`:** Each `Item` carries `id`, `crate_id`,
  `name`, `span`, `visibility`, `docs`, `links` (resolved intra-doc markdown
  links -> `Id`), `attrs` (structured `Attribute` enum), `deprecation`, and
  `inner: ItemEnum` (`Module`, `ExternCrate`, `Use`, `Union`, `Struct`,
  `StructField`, `Enum`, `Variant`, `Function`, `Trait`, `TraitAlias`, `Impl`,
  `TypeAlias`, `Constant`, `Static`, `ExternType`, `Macro`, `ProcMacro`,
  `Primitive`, `AssocConst`, `AssocType`).

## Boundaries

- **Clippy lint inventory (`src/tools/clippy`) — not examined:** Section 3
  extracts all `261` `rustc` compiler lints, `17` `rustc::*` internal tool
  lints, and `14` `rustdoc::*` tool lints; Clippy's >750 `clippy::*` lints run
  inside the separate `clippy-driver` `rustc_private` binary and are **not
  examined** here.
- **Unstabilized `EditionFuture` rules — unknown:** `Edition::EditionFuture`
  currently inherits Edition 2024 rules and reserves `edition_future_compatibility`;
  which unstable features will join a future Rust 2027 edition is **unknown**
  upstream.
- **Cross-toolchain binary `.rmeta` mixing — unsupported:** Upstream `rustc`
  explicitly rejects `.rmeta` and `proc-macro` dylib artifacts built by a
  different compiler commit (`MetadataBlob::check_version`, `METADATA_VERSION`).
- **Pre-`1.85` `rustdoc` JSON consumers — known not to apply:** `rustdoc` JSON
  remains gated behind `-Zunstable-options` and increments `FORMAT_VERSION`
  (`61` at `1.102.0-nightly`) on breaking schema changes without backwards
  compatibility across versions.

## Evidence

- **Primary source (`rust-lang/rust` @ `412be32a6a189d9a28922beee178bc0abee9d492`):**
  - Editions & keywords: `compiler/rustc_span/src/edition.rs:34-133`,
    `compiler/rustc_span/src/symbol.rs:32-215`,
    `compiler/rustc_hir_analysis/src/check/region.rs:145-163,353-380`,
    `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:322-331`,
    `compiler/rustc_hir_typeck/src/pat.rs:335-365`,
    `compiler/rustc_mir_build/src/builder/scope.rs:437,1179,1927`.
  - Feature gates: `compiler/rustc_feature/src/{lib.rs:26-159,accepted.rs:23-498,unstable.rs:19-912,removed.rs:9-327}`.
  - Attributes, macros & lang items:
    `compiler/rustc_feature/src/builtin_attrs.rs:15-298`,
    `compiler/rustc_structures/src/lib.rs:1-20`,
    `compiler/rustc_attr_parsing/src/{lib.rs:1-125,attributes/mod.rs:143-318,context.rs:118-365,interface.rs:625-675,safety.rs:12-127,target_checking.rs:23-140}`,
    `compiler/rustc_attr_ir/src/{attr.rs:15-166,data_structures.rs:828-1610,lang_items.rs:18-542,weak_lang_items.rs:7-29}`,
    `compiler/rustc_builtin_macros/src/lib.rs:62-155`,
    `compiler/rustc_expand_queries/src/{lib.rs:1-13,derive.rs:1-82}`.
  - Lints & error codes: `compiler/rustc_lint_defs/src/{lib.rs:450-750,builtin.rs:1-6053}`,
    `compiler/rustc_lint/src/{lib.rs:156-801,context.rs:190-335}`,
    `src/librustdoc/lint.rs:1-260`,
    `compiler/rustc_error_codes/src/lib.rs:25-691`.
  - Typeck, trait solver, patterns & borrowck:
    `compiler/rustc_session/src/config.rs:1071-1086,3838-3865`,
    `compiler/rustc_hir_typeck/src/fn_ctxt/mod.rs:47`,
    `compiler/rustc_trait_selection/src/traits/engine.rs:34-75`,
    `compiler/rustc_type_ir/src/solve/{mod.rs,inspect.rs}`,
    `compiler/rustc_pattern_analysis/src/{constructor.rs:75-180,usefulness.rs:1698-1855}`,
    `compiler/rustc_borrowck/src/{nll.rs:38-185,polonius/mod.rs:64-120,polonius/legacy/facts.rs:1-90,region_infer/opaque_types/mod.rs:44-128}`.
  - `proc_macro::bridge`: `library/proc_macro/src/bridge/{mod.rs:33-358,buffer.rs:7-60,rpc.rs:7-259,handle.rs:15-95,client.rs:215-299,server.rs:120-290}`,
    `compiler/rustc_expand/src/proc_macro_server.rs:1-740`.
  - `.rmeta`, `StableCrateId`, `Svh`, & `rustdoc` JSON:
    `compiler/rustc_metadata/src/rmeta/{mod.rs:66-838,table.rs:8-611,encoder.rs:815-880,2612-2855}`,
    `compiler/rustc_span/src/def_id.rs:154-213`,
    `src/rustdoc-json-types/lib.rs:95-220`.
- **Normative specifications:** `rust-lang/reference`
  (`bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`) and `rust-lang/edition-guide`
  (`ab8544aeed7b792984366aa122ac19bd47ad9a2f`).
- **Execution probes (`x86_64-unknown-linux-gnu`, `2026-11-21`):** Executed inside
  `tempfile.TemporaryDirectory()` by `support/extract_frontend_contracts.py`
  against `rustc`/`rustdoc` `1.102.0-nightly`
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `rustc` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`), with complete outputs archived in
  `support/frontend_features_attrs_langitems.json`.

## Revalidation

Run the self-contained read-only Git and `TemporaryDirectory` probe script
against any `rust-lang/rust` commit `<REV>`:

```console
python3 -B support/extract_frontend_contracts.py \
  --rust-repo /path/to/rust \
  --rev 412be32a6a189d9a28922beee178bc0abee9d492 \
  --out /tmp/revalidated_frontend_contracts.json
```

Diff `/tmp/revalidated_frontend_contracts.json` against
`support/frontend_features_attrs_langitems.json` to detect: (1) newly stabilized,
added, or removed `#![feature(...)]` gates, (2) changes to `ATTRIBUTE_PARSERS`,
`AttributeSafety::Unsafe`, `register_builtin_macros`, or `LangItem` counts,
(3) lint or `E0xxx` additions, (4) `NextSolverConfig::default()` or
`Polonius::DEFAULT` flips (`CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`,
`CFG_DEFAULT_POLONIUS_NEXT`), (5) `proc_macro::bridge::with_api!` RPC tag
changes, and (6) `.rmeta` `METADATA_VERSION` or `rustdoc-json-types`
`FORMAT_VERSION` bumps.
