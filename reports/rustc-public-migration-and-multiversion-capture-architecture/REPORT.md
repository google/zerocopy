# rustc_public Feasibility, Capture Coverage, and Multi-Version Architecture for Anneal

Created: 2026-11-23
Updated: 2026-11-23

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Migrating Anneal's MIR capture driver (`anneal/trusted/rustc-capture`) directly onto `rustc_public` today is **blocked for standalone soundness parity**, and `rustc_public` does **not** eliminate multi-version compiler maintenance across Rust releases. At the same time, factoring `rustc-capture` into a compiler-agnostic core plus thin per-toolchain adapters already isolates **`~65%`** of production capture code from `rustc_*` internals, and selectively adopting `rustc_public` on **`1.100.0+`** for **ADT layouts, repr options, enums/niches, and constant allocations** (while preserving `rustc_private` for `Runtime(PostCleanup)` capture, input confinement, and fail-closed guards) yields concrete multi-version leverage.

Measured directly on `google/zerocopy@3741897d51a2d91354d4427b4a4a155346d16ccf` and compiled probes across **10 installed Rust toolchains (`1.91.0-nightly` through `1.102.0-nightly`, including `1.99.1` and stable `1.100.0`)**:

1. **Production `rustc-capture` surface exceeds the old `driver.rs` scaffold by `>8x`:** `anneal/trusted/rustc-capture/src/*.rs` comprises **`8,003` LOC** (`5,678` non-`mod tests` LOC, `2,325` `mod tests` LOC, plus `3,285` LOC in `tests/`, total **`11,288` LOC**), importing **9 `rustc_*` crates** (`rustc_abi`, `rustc_ast`, `rustc_data_structures`, `rustc_driver`, `rustc_hir`, `rustc_interface`, `rustc_middle`, `rustc_session`, `rustc_span`), **26 distinct `TyCtxt` members**, pre-expansion AST checks, a custom `FileLoader`, a whole-crate `DefKind` census, exhaustive `CodegenFnAttrs` destructuring, and a `mir_drops_elaborated_and_const_checked` query hook (`Runtime(PostCleanup)`).
2. **`rustc_public` itself broke across 5 distinct epochs in 15 months and still cannot build on `stable` without `RUSTC_BOOTSTRAP=1`:**
   - Compiling a representative `rustc_public` probe across 10 toolchains observed five breaking API epochs: `1.91`–`1.97` (`Rvalue::Use(Operand)` 1-tuple), `1.98` (`Rvalue::Use(Operand, WithRetag)`, `.span` on `Statement`/`Terminator`, `LayoutShape.abi`), `1.99.1` (`Statement`/`Terminator.source_info`, `Crate::adts`, `TyKind::Alias`, `VariantDef::idx`), `1.100.0` (`LayoutShape.abi -> value_repr`), and `1.102` (`rustc_driver::run_compiler -> compiler_entrypoint`).
   - Both `1.99.1` and stable `1.100.0` fail to compile `rustc_public` consumers with `error[E0554]: #![feature] may not be used on the stable release channel` unless `RUSTC_BOOTSTRAP=1` is set (`rustc_public` remains unpublished on crates.io and tied to `rustc-dev`).
3. **Real-target validation on unmodified `google/zerocopy` (`0.8.64`, `no_std`) exposed a fatal `1.98.0-nightly` panic and severe `Optimized` vs `PostCleanup` divergence:**
   - On Anneal's current pin (`1.98.0-nightly f8a08b688`), iterating `zerocopy`'s local items via `rustc_public` **panicked `rustc`** inside `rustc_public/src/unstable/convert/stable/ty.rs:479:17` (`not yet implemented`) on `ty::Alias` when inspecting `Ptr::assume_alignment`.
   - On `1.102.0-nightly` (`8eb778d04`, where `TyKind::Alias` is implemented), `zerocopy/src/lib.rs` completed cleanly across `8,558` local items (`4,464` functions, `81` ADTs -> `64` concrete layouts `Ok`, `17` generic `Err`, `45` `TyKind::Alias` locals). However, `rustc_public`'s default `CrateItem::body()` (`Runtime(Optimized)`) lost **`316 / 963` (`32.8%`) of `PlaceMention` UB checks**, collapsed **`40,758` `PostCleanup` statements across `4,430` Fn bodies to `15,711` statements across `4,730` bodies (`-61.5%`)**, and silently dropped all **`153` `block.is_cleanup`** flags.
4. **Hard soundness & security blockers forbid naive `rustc_public` replacement:** Pure `rustc_public` lacks `Runtime(PostCleanup)` / `override_queries`, `CallSource::Use` gating, `block.is_cleanup`, `UnwindTerminateReason`, `required_consts`, `tainted_by_errors`, `injection_phase`, `CodegenFnAttrs` (`tool_attrs()` skips parsed attributes like `#[inline(always)]` and `#[cold]`), `FileLoader`, pre-expansion `#![crate_type]` / `#![feature(...)]` AST validation, external-crate path/sysroot provenance, visibility queries, `InlineAsm` structured operands (only `Debug` strings), and propagates post-mono CTFE errors only after `BodyBuilder` silently swallows `ErrorHandled::Reported`.
5. **Recommended Multi-Version Architecture (`google/zerocopy#4014` / `#4017`):** Split `anneal/trusted/rustc-capture` into a compiler-agnostic **`anneal-capture-core`** crate (`~3,698` non-`mod tests` LOC, `0` `rustc_*` crates) plus version-isolated **`anneal-capture-shim-<epoch>`** adapters (`~1,980` non-`mod tests` LOC today, shrinking to `~1,100–1,350` LOC on `1.100+` by delegating `LayoutShape`, `ReprOptions`, `TagEncoding`, `GlobalAlloc`, and `StaticDef` queries to `rustc_public` inside a thin `rustc_private` `PostCleanup` driver), communicating over a versioned `ProducerProvenance` + monotonic `SemProfile` IR trunk.

## Applicability

- **Extends prior corpus reports (distinct scope, zero duplication):**
  - `rustc-public-stable-mir-vs-middle-mir-capture-seam-completeness` audited an earlier 2-file `driver.rs` prototype and `rustc_public` internal sources (`f8a08b688cbe` / `49d734536222` / `342d74463af7`). This report audits the live `8,003`-LOC `src/*.rs` `rustc-capture` implementation at `google/zerocopy@3741897d51a2d91354d4427b4a4a155346d16ccf`, runs compiled probes across **10** toolchains (`1.91.0-nightly`–`1.102.0-nightly`), tests unmodified `zerocopy/src/lib.rs`, quantifies the TCB LOC delta, and specifies the multi-version shim boundary and upstream `rustc_public` PR list.
  - `rustc-multi-release-mir-abi-drift-and-version-isolated-adapter` measured cross-release churn in `rustc_middle`, `rustc_abi`, and `rustc_codegen_ssa`. Here we measure cross-release churn inside `rustc_public` itself across `1.91`–`1.102` and map how `rustc-capture`'s session, census, and UB-preservation invariants intersect that boundary.
  - `multi-version-ir-migration-topologies-and-capability-schemas`, `rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility`, `multi-version-compiler-internal-plugin-and-driver-architectures`, and `anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement` establish the `T4` per-spoke lowering topology, 3-axis `SemProfile` header contract, and forward-compatible `TargetLayout`/`AdtRepr`/`Crate.tcb` Lean semantics on which Section 5 builds.
- **Applies to:** `google/zerocopy@3741897d51a2d91354d4427b4a4a155346d16ccf` (`anneal/trusted/rustc-capture`, `anneal/trusted/cargo-anneal`, `anneal/trusted/audit`, and `zerocopy/`), on Linux `x86_64` across Rust `1.91.0-nightly`–`1.102.0-nightly`.

## Findings

### 1. Empirical `rustc_private` Inventory of `anneal/trusted/rustc-capture`

**Basis: source + measurement (`support/inventory_rustc_private.py`, `support/results.json`)**

Scanning `anneal/trusted/rustc-capture` at `3741897d51a2d91354d4427b4a4a155346d16ccf` establishes an exact production vs. test footprint (`8,003` `src/*.rs` LOC = `5,678` non-`mod tests` LOC + `2,325` `mod tests` LOC; plus `3,285` LOC in `tests/` = `11,288` total Rust LOC):

| File | Total LOC | Non-`mod tests` LOC | `mod tests` LOC | Direct `rustc_*` Crates / Primary Coupling |
| :--- | ---: | ---: | ---: | :--- |
| `src/main.rs` | 267 | 267 | 0 | 9 `extern crate rustc_*` declarations; `#![feature(normalize_lexically, rustc_private)]`; CLI & panic boundary |
| `src/driver.rs` | 177 | 177 | 0 | `rustc_driver`, `rustc_interface`, `rustc_middle`, `rustc_session` (`EarlyDiagCtxt`, `install_ice_hook`, `run_compiler`) |
| `src/capture.rs` | 1,253 | 1,061 | 192 | `override_queries` (`PostCleanup` hook), `FileLoader`, `rustc_ast` crate-root gate, `DefKind` census, sysroot-only crate & depinfo checks |
| `src/extract.rs` | 1,314 | 924 | 390 | `rustc_middle::{mir,ty}`, `rustc_abi`, `rustc_hir::{attrs,LangItem}`, `CodegenFnAttrs`, MIR/Ty/enum extraction + soundness guards |
| `src/identity.rs` | 2,397 | 1,629 | 768 | Pure ELF/`/proc/self/maps`/TOCTOU checks except 3 calls (`rustc_version_str`, `host_tuple`, `run_compiler as *const ()`) |
| `src/ir.rs` | 1,606 | 1,067 | 539 | **0 `rustc_*` symbols** (pure Rust IR + fail-closed invariants) |
| `src/lean.rs` | 801 | 434 | 367 | **0 `rustc_*` symbols** (pure Lean renderer; includes 1 4-line `#[cfg(test)]` helper) |
| `src/publication.rs` | 188 | 119 | 69 | **0 `rustc_*` symbols** (atomic directory staging/publication) |
| **Total `src/*.rs`** | **8,003** | **5,678** | **2,325** | **`~3,698` compiler-agnostic vs `~1,980` compiler-coupled non-`mod tests` LOC** |

Note: `identity.rs` includes a 9-line `#[cfg(test)]` helper outside `mod tests`, and `lean.rs` includes a 4-line `#[cfg(test)]` helper outside `mod tests`, giving `5,665` active non-test LOC (`5,678` non-`mod tests`).

Across those files, production code directly depends on **9 `rustc_*` crates**:
- `rustc_abi`: `Endian`, `ExternAbi`, `Integer`, `Primitive`, `TagEncoding`, `Variants`
- `rustc_ast`: `Attribute`, `Crate`, `MetaItem`, `MetaItemInner`
- `rustc_data_structures`: `steal::Steal`
- `rustc_driver`: `Callbacks`, `Compilation`, `catch_fatal_errors`, `catch_with_exit_code`, `install_ice_hook`, `run_compiler`
- `rustc_hir`: `Attribute::Parsed`, `attrs::{AttributeKind::CrateType, InlineAttr, OptimizeAttr}`, `def::DefKind` (32+ variants explicitly classified), `LangItem::OrderingEnum`
- `rustc_interface`: `interface`, `util::rustc_version_str`
- `rustc_middle`: `codegen_fn_attrs::{CodegenFnAttrs, CodegenFnAttrFlags, SanitizerFnAttrs}`, `mir` (`Body`, `MirPhase`, `RuntimePhase`, `StatementKind`, `TerminatorKind`, `CallSource`, `Rvalue`, `WithRetag`, `Operand`, `Place`, `Const::Val`, `ConstValue::ZeroSized`, `BinOp`, `UnOp`, `CastKind`), `ty` (`TyCtxt`, `TypingEnv`, `print::{with_no_trimmed_paths, with_no_visible_paths}`), `util::Providers`
- `rustc_session`: `EarlyDiagCtxt`, `Session`, `config::{CrateType, ErrorOutputType, Options, host_tuple}`
- `rustc_span`: `FileName`, `def_id::{DefId, LOCAL_CRATE, LocalDefId}`, `source_map::{FileLoader, RealFileLoader}`, `sym::{cfg_attr, crate_type, feature, rustc_private}`

It invokes **26 distinct `TyCtxt` methods/fields**: `codegen_fn_attrs`, `crate_dep_kind`, `crate_extern_paths`, `crate_name`, `crate_types`, `crates`, `data_layout`, `dcx`, `def_kind`, `def_path_str`, `effective_visibilities`, `features`, `fn_sig`, `generics_of`, `hir_krate_attrs`, `intrinsic`, `is_lang_item`, `iter_local_def_id`, `lang_items`, `mir_drops_elaborated_and_const_checked`, `native_libraries`, `proc_macro_decls_static`, `sess`, `type_of`, `used_crate_source`, `visibility`.

---

### 2. Cross-Version `rustc_public` Stability Matrix (`10` Toolchains, `1.91`–`1.102`)

**Basis: execution (`support/probe_matrix.py`, `support/results.json`)**

We compiled and executed two probes against every installed `rustup` toolchain shipping `librustc_public*.rlib`: (a) `compat` using only macro/match forms shared loosely (`Rvalue::Use(_, _)` without field names like `.span` or `.abi`), and (b) `pin_surface` pinning the `1.98.0-nightly` `rustc_public` + driver signatures (`Statement.span`, `Terminator.span`, `LayoutShape.abi`, `WithRetag::Yes`, `rustc_driver::run_compiler`). On stable channels (`1.99.1`, `1.100.0`), both variants were compiled both bare and with `RUSTC_BOOTSTRAP=1`.

| Toolchain (`rust-lang/rust` commit) | `compat` (bare) | `compat` (`RUSTC_BOOTSTRAP=1`) | `pin_surface` (bare / bootstrap) | Observed Breaking Boundary |
| :--- | :--- | :--- | :--- | :--- |
| `1.91.0-nightly` (`05f5a58e8`, 2025-08-19) | **FAIL** (`E0023`) | n/a | **FAIL** (`E0432`, `E0023`) | `Rvalue::Use(Operand)` is 1-tuple; no `WithRetag` |
| `1.93.0-nightly` (`94b49fd99`, 2025-11-22) | **FAIL** (`E0023`) | n/a | **FAIL** (`E0432`, `E0023`) | `Rvalue::Use(Operand)` is 1-tuple; no `WithRetag` |
| `1.95.0-nightly` (`efc9e1b50`, 2026-02-06) | **FAIL** (`E0023`) | n/a | **FAIL** (`E0432`, `E0023`) | `Rvalue::Use(Operand)` is 1-tuple; no `WithRetag` |
| `1.97.0-nightly` (`bf4fbfb7a`, 2026-04-11) | **FAIL** (`E0023`) | n/a | **FAIL** (`E0432`, `E0023`) | `Rvalue::Use(Operand)` is 1-tuple; no `WithRetag` |
| `1.98.0-nightly` (`f8a08b688`, 2026-05-30, pin) | **PASS** (run=0) | n/a | **PASS** (run=0) | Baseline: `WithRetag` added, `.span`, `LayoutShape.abi`, `run_compiler`, `ty::Alias => todo!()` |
| `1.98.0-nightly` (`14210df0e`, 2026-05-31) | **PASS** (run=0) | n/a | **PASS** (run=0) | Matches `f8a08b688` |
| `1.99.1` (`58cf8f9c3`, 2026-10-13) | **FAIL** (`E0554`) | **PASS** (run=0) | **FAIL** (`E0554` / `E0609`) | Requires `RUSTC_BOOTSTRAP=1`; `Statement`/`Terminator.span` -> `source_info`; `Crate::adts` & `TyKind::Alias` added; still `.abi` |
| `1.100.0` (`0ef1bc386`, 2026-11-09, stable) | **FAIL** (`E0554`) | **PASS** (run=0) | **FAIL** (`E0554` / `E0609`) | Requires `RUSTC_BOOTSTRAP=1`; `LayoutShape.abi` -> `value_repr` (`ValueAbi` -> `ValueRepr`); still `rustc_driver::run_compiler` |
| `1.102.0-nightly` (`3ef0c22cd`, 2026-11-11) | **PASS** (run=0) | n/a | **FAIL** (`E0425`, `E0609`) | `rustc_driver::run_compiler` removed -> `rustc_driver::compiler_entrypoint` (and `.source_info`/`.value_repr`) |
| `1.102.0-nightly` (`8eb778d04`, 2026-11-12) | **PASS** (run=0) | n/a | **FAIL** (`E0425`, `E0609`) | Matches `3ef0c22cd` |

Two structural conclusions follow directly from this measurement:
1. **`rustc_public` experiences frequent breaking churn:** Even ignoring `rustc_driver`, `rustc_public`'s own MIR/ABI types broke `compat`/`pin_surface` across **4 distinct `rustc_public` epochs** inside 15 months (`1.91..1.97` -> `1.98` -> `1.99.1` -> `1.100.0`), plus the `rustc_driver::run_compiler` -> `compiler_entrypoint` break in `1.102`. Note why `compat` compiled on `1.98`–`1.102` (with bootstrap on `1.99.1`/`1.100.0`): `rustc_public::run!` expands inside the compiler's own macro to `run_compiler` vs `compiler_entrypoint`, hiding driver churn **only** for callers that do not use custom `Callbacks` (`override_queries`, `file_loader`, `after_crate_root_parsing`) or inspect driver symbols (`identity.rs`).
2. **No `stable`-channel build independence yet:** `rustc_public` ships inside `rustc-dev` (`version = "0.1.0-preview"`), not on crates.io. Both `1.99.1` and `1.100.0` fail `E0554` (`#![feature(rustc_private)]`) unless `RUSTC_BOOTSTRAP=1` is set — meaning even a pure `rustc_public` binary cannot build cleanly with stock stable Rust or eliminate sysroot-coupled `rustc-dev` linking (`-L native=<sysroot>/lib` + rpath to `libLLVM-*.so` / `librustc_driver-*.so`).

---

### 3. Surface-by-Surface Capability Probe & Real `zerocopy` Crate Measurements

**Basis: source + execution (`support/probe_target.rs`, `support/probe_driver_1_98.rs`, `support/probe_driver_1_102.rs`, `support/results.json`)**

#### A. Purpose-Built Edge-Case Probe (`probe_target.rs`)

Running both `rustc_public::run!` (`Runtime(Optimized)`) and hybrid `override_queries + rustc_internal::stable` (`Runtime(PostCleanup)`) on `probe_target.rs` (under `-Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no -Zmir-preserve-ub`) directly measured the following behaviors:

- **`Runtime(PostCleanup)` vs `Runtime(Optimized)` and `-Zmir-preserve-ub`:**
  - `const_eval_fn` drops from **`3` blocks / `39` statements** in `PostCleanup` to **`1` block / `14` statements** in `item.body()` (`Runtime(Optimized)`).
  - `touch_all_adts` drops from **`12` blocks / `116` statements** (`PostCleanup`) to **`12` blocks / `21` statements** (`Optimized`).
  - Passing `-Zmir-preserve-ub` preserves `StatementKind::PlaceMention` (`place_mention_test`: `1` in both `PostCleanup` and `rustc_internal::stable(&body)`; `niche_match`: `1` in both) — whereas omitting `-Zmir-preserve-ub` erases both to **`0`** before `PostCleanup`.
- **Lost Metadata During `Stable::stable` Conversion (`compiler/rustc_public/src/unstable/convert/stable/mir.rs`):**
  - `cleanup_unwind_test`: `PostCleanup` contains **`cleanup_bbs=2` (`block.is_cleanup == true`)**; `rustc_public::mir::BasicBlock` omits `is_cleanup` entirely (`0` signal exposed). `UnwindTerminateReason` is collapsed into unit `TerminatorKind::Abort`.
  - `ergonomic_use_fn` (`#![feature(ergonomic_clones)]`, `x.use`): `PostCleanup` emits `TerminatorKind::Call { call_source: CallSource::Use, .. }`; `rustc_public::mir::TerminatorKind::Call` discards `call_source: _` so `rustc-capture` cannot fail closed on `.use` calls through `rustc_public` alone.
  - `mir::Body` fields `phase`, `injection_phase`, `tainted_by_errors`, `coroutine`, and `required_consts` are all dropped (`spread_arg()` and `locals()` are preserved).
- **Crate-Root, Attribute, and Visibility Blindness:**
  - `attr_fn` carries `#[inline(always)] #[cold]`, yet `item.all_tool_attrs()` returned **`0` attributes** (`compiler_interface.rs` filters `Attribute::Unparsed`, skipping parsed built-in attrs / `CodegenFnAttrs`).
  - `global_asm!(".text")` in `probe_target.rs` is absent from `all_local_items()` (`36` items) and from all `local_crate()` collections.
  - `#![feature(ergonomic_clones)]`, `#![crate_type = "lib"]`, `FileLoader` read provenance, external-crate paths (`19` external crates returned only `{id, name, is_local}`), `native_libraries`, `env_depinfo`/`file_depinfo`, and item `Visibility` are unavailable.
- **`IndexedVal` Trait Privacy Trap (`1.98.0-nightly`):**
  - `rustc_public::lib.rs:23` imports `rustc_public_bridge::IndexedVal` as `pub(crate)`. Pure `rustc_public` callers on `1.98` cannot call `VariantIdx::to_val(...)` or `.to_index()` without `extern crate rustc_public_bridge`, and `CrateNum` does not implement `IndexedVal` at all (`rustc_internal::crate_num(&local)` is required to inspect crate ID numerically). (In `1.100`/`1.102`, `VariantDef::idx(&self)` was added, mitigating enum-variant indexing, though `IndexedVal` remains non-public.)
- **Layouts, Reprs, Niches, Statics, and Const Allocations (Strong Coverage):**
  - `AdtDef::repr()` and `Ty::layout()?.shape()` faithfully recovered all struct/union/enum layouts in `probe_target.rs` (`ReprCStruct` size `12` align `4` offsets `[0, 4, 8]` bytes; `PackedStruct` size `10` align `2` `pack=Some(2)`; `AlignedStruct` size `16` align `16`; `TransparentWrapper` `is_transparent: true`; `ReprRustStruct` reordered offsets `[10, 0, 8]` bytes; `ExplicitDiscrEnum` `repr(u16)` `discrs=[(0, 10), (1, 42)]` `valid_range: 10..=42`; `Option<NonZeroU8>` `TagEncoding::Niche { untagged_variant: 1, niche_variants: 0..=0, niche_start: 0 }`; `RawUnion` `FieldsShape::Union(2)`). Generic unresolved local `T` cleanly returned `Err` instead of panicking.
  - `CrateItem::body()` left `SLICE_CONST` and `union_uninit_const::U_VAL` as `ConstantKind::Unevaluated`, whereas `Instance::try_from(*item).unwrap().body()` (`BodyBuilder`) evaluated `U_VAL` to `Allocation { bytes: [Some(7), None, None, None], align: 4 }` (accurately flagging uninitialized union bytes as `None`) and resolved `S_REF` provenance to `GlobalAlloc::Static(StaticDef)`.
- **Swallowed Post-Mono CTFE Failure (`BodyBuilder`) & Unstructured `InlineAsm`:**
  - Resolving `generic_ctfe_bomb::<u8>` via `Instance::resolve` + `.body()` triggered CTFE inside `after_analysis`, emitted `error[E0080]` to stderr, **swallowed `ErrorHandled::Reported` inside `rustc_public_bridge/src/builder.rs:63`**, returned `body_some = true` with an `Unevaluated` const operand, and then aborted `rustc` with **exit code `101`**.
  - `inline_asm_fn` surfaced `TerminatorKind::InlineAsm`, but `template`, `options`, `line_spans`, and non-place operand data are opaque `Debug`-formatted `String`s (`template="[String(\"mov \"), ...]"`, `options="NOMEM | PRESERVES_FLAGS | NOSTACK"`), and jump `targets` collapse to `destination: targets.first()`.

#### B. Real-Customer Probe: Unmodified `google/zerocopy` (`0.8.64`, `no_std`)

Compiling unmodified `zerocopy/src/lib.rs` (`--edition 2021 --crate-type lib --cfg no_zerocopy_allocator_api_1_100_0`) against `probe_driver_1_98` and `probe_driver_1_102` uncovered two concrete facts that synthetic tests missed:

1. **Fatal `1.98.0-nightly` `ty::Alias` panic:** Iterating `zerocopy`'s local items on Anneal's current compiler pin (`f8a08b688`) **panicked `rustc` (`exit 101`)** at `rustc_public/src/unstable/convert/stable/ty.rs:479:17` (`not yet implemented`) when lowering `zerocopy::pointer::ptr::_transitions::<impl Ptr<'a, T, I>>::assume_alignment`. In `1.98`, `ty::Alias(_alias_ty) => todo!()` inside `Stable::stable for ty::Ty` crashes on any generic body whose locals contain un-normalized associated types (`alias_tys_seen = 45` across `zerocopy`).
2. **Whole-crate `zerocopy` capture metrics on `1.102.0-nightly` (`8eb778d04`, where `TyKind::Alias` is implemented):**

| Metric (`zerocopy 0.8.64`, `no_std`) | Hybrid `PostCleanup` (`rustc_internal::stable`) | `rustc_public` `item.body()` (`Runtime(Optimized)`) | Delta / Operational Impact |
| :--- | ---: | ---: | :--- |
| Bodies inspected | `4,430` (`Fn`/`AssocFn`, `is_mir_available`) | `4,730` `Ok` / `3,828` `None` (`all_local_items = 8,558`) | Bodyless trait methods require `is_mir_available` guard when iterating `DefKind::AssocFn` directly (avoiding `rustc_hir_typeck` ICE observed on `TryTransmuteRefDst::try_transmute_ref`) |
| Basic blocks (`-Zmir-preserve-ub`) | `12,639` | `13,069` | Optimized includes `300` extra `Const`/`Ctor` items while rewriting CFG |
| Statements (`-Zmir-preserve-ub`) | **`40,758`** | **`15,711`** | **`-61.5%`** statements (`25,047+` stripped across MIR opts even at `-Copt-level=0`) |
| `PlaceMention` UB checks (`-Zmir-preserve-ub`) | **`963`** | **`647`** | **`-32.8%` (`316` UB checks silently lost!)** |
| `PlaceMention` without `-Zmir-preserve-ub` | `0` | `0` | Confirms `-Zmir-preserve-ub` is mandatory |
| `is_cleanup == true` blocks | **`153`** | **`0` exposed (`false`)** | All `153` cleanup blocks flattened to non-cleanup blocks in `rustc_public` |
| `TyKind::Alias` locals | `45` (handled) | `45` (handled) | Crashed `1.98.0-nightly` (`ty.rs:479`); requires `1.100+` |
| `Crate::adts()` (`81` ADTs) | `—` | `64` layout `Ok` / `17` generic `Err` | Monomorphic layouts + reprs + niches succeed; generic `Unalign<T>` etc. require monomorphized `Ty::layout()` |

---

### 4. Quantified Coverage Matrix and Exact TCB LOC Delta

**Basis: source + measurement (`support/results.json`)**

#### A. Coverage Classification Across `rustc-capture` & Multi-Version Layout Needs

| Surface / Responsibility | Current `rustc-capture` Location | `rustc_public` Coverage (`1.98` / `1.100+`) | Status Classification |
| :--- | :--- | :--- | :--- |
| MIR `Statement` / `Rvalue` / `Terminator` ops (`Assign`, `PlaceMention`, `WithRetag`, `SwitchInt`, `BinOp`, `UnOp`, `Cast`, `Discriminant`) | `extract.rs:32–521` | Present on `1.98+` (`rustc_internal::stable(&raw)` works on `PostCleanup` body once `1.100+` fixes `ty::Alias`) | **Covered if bridged (`PostCleanup` hook needed)** |
| `Runtime(PostCleanup)` phase hook (`override_queries` on `mir_drops_elaborated_and_const_checked`) & `body.{phase,injection_phase}` | `capture.rs:52–76`, `extract.rs:766–815` | Absent (`CrateItem::body()` / `Instance::body()` hardcodes `Optimized`; loses `32.8%` `PlaceMention` on `zerocopy`) | **Hard blocker (`rustc_private`)** |
| Body soundness gates (`block.is_cleanup`, `UnwindTerminateReason`, `CallSource::Use`, `required_consts`, `tainted_by_errors`, `coroutine`) | `extract.rs:443–465, 794–860` | Absent (`is_cleanup`, `CallSource`, `UnwindTerminateReason`, `required_consts`, `tainted_by_errors` dropped; only `spread_arg` exposed) | **Hard blocker (`rustc_private`)** |
| `CodegenFnAttrs` exhaustive gate (`flags`, `inline`, `optimize`, `sanitizers`, `export_name`, etc.) | `extract.rs:585–741` (`157` LOC) | Absent (`all_tool_attrs()` skips parsed attributes; `tool_attrs = 0` on `#[inline(always)] #[cold]`) | **Hard blocker (`rustc_private`)** |
| Driver session setup, `EarlyDiagCtxt`, ICE hook, error/ICE exit codes, `host_tuple`, `rustc_version_str`, `/proc/self/maps` DSO check | `driver.rs` (`177` LOC), `identity.rs` (`6` of `1,629` LOC) | `run!` hides `Callbacks::config`, `after_crate_root_parsing`, error-vs-ICE distinction, version string, DSO symbol | **Hard blocker (`rustc_private`, `1.102` renamed `run_compiler` -> `compiler_entrypoint`)** |
| Closed-world `FileLoader` + source hashes + `file_depinfo`/`env_depinfo` + `native_libraries` | `capture.rs:93–232, 820–885` | Absent (`run!` accepts only `args: &[String]`) | **Hard blocker (`rustc_private`)** |
| Pre-expansion crate-root `#![crate_type]` / `#![feature(...)]` gate + `tcx.features().ergonomic_clones()` | `capture.rs:363–436`, `extract.rs` | Absent (`Crate` has no attrs, `crate_type`, or feature flags) | **Hard blocker (`rustc_private`)** |
| Whole-crate fail-closed `DefKind` census + `Visibility` / `effective_visibilities` + sysroot-only external crate provenance + local `LangItem` ban | `capture.rs:233–397, 486–685` | Partial (`fn_defs`/`statics`/`adts`/`trait_*` miss `GlobalAsm`, non-MIR `Const`, `TypeAlias`, `CrateDepKind`, `crate_extern_paths`, visibility) | **Hard blocker (`rustc_private`)** |
| `known_core_fn` & `OrderingEnum` lang-item detection | `extract.rs:558–575` | Thin string-path check possible (`is_box` exists, general `LangItem` absent) | **Thin bridge / `rustc_private`** |
| **Monomorphized `Instance` resolution (`Instance::resolve`), generics, `FnABI`** | Future / multi-crate expansion | Native (`Instance::resolve`, `Instance::fn_abi`, `requires_monomorphization`); note `.body()` is `Optimized` | **Covered natively (except phase & CTFE swallow)** |
| **`LayoutShape`, `FieldsShape`, `VariantsShape`, `TagEncoding::Niche`, `ReprOptions`, `MachineInfo`, `AdtDef::discriminant_for_variant`** | `extract.rs:57–201` + planned `#4017` general ADTs / padding | Native on `1.100+` (`1.98` lacks `Crate::adts()`, `VariantDef::idx()`, public `IndexedVal`, and crashes on `ty::Alias`) | **Covered natively on `1.100+`** |
| **`MirConst`, `Allocation` (`bytes: Vec<Option<u8>>`), `ProvenanceMap`, `GlobalAlloc`, `StaticDef::eval_initializer`** | Planned `#4017` const/static/union support | Native on `1.98+` via `Instance` / `StaticDef` (`Item::body()` leaves `SLICE_CONST`/locals `Unevaluated`; `BodyBuilder` swallows CTFE errors) | **Covered natively w/ CTFE check guard** |
| **`TerminatorKind::InlineAsm`** | Future ISA / `asm!` work | Stringified `Debug` (`template`, `options`, `line_spans`, `raw_rpr: String`); multi-target jump labels lost | **Hard blocker for machine semantics (`rustc_private`)** |

#### B. Exact Production TCB LOC Delta (`src/*.rs` Non-`mod tests` LOC = `5,678`)

| Architecture Option | Compiler-Agnostic Core (`0` `rustc_*` deps) | Compiler-Coupled `rustc_*` Code | Net Production LOC vs Today (`5,678`) | Feasibility Assessment |
| :--- | ---: | ---: | ---: | :--- |
| **Status Quo (`rustc-capture` @ `3741897d`)** | `~3,698` (inside same crate, so whole `5,678`-LOC binary links `rustc-dev`) | `~1,980` (`driver` 177 + `capture` ~861 + `extract` 924 + `main`/`identity` ~18) | Baseline (`5,678`) | Works only on single pinned `1.98.0-nightly` (`f8a08b688`) |
| **Option A: Naive Pure `rustc_public` Rewrite** | `~3,700` | `~900–1,050` (hypothetical) | **Infeasible** (breaks soundness) | **Blocked:** Drops `PostCleanup` (`-32.8%` `PlaceMention` on `zerocopy`), `is_cleanup`, `CallSource::Use`, `CodegenFnAttrs`, `FileLoader`, AST/feature/sysroot gates; crashes on `1.98` `zerocopy`; needs `RUSTC_BOOTSTRAP=1` on `stable` |
| **Option B: In-Crate Hybrid (`rustc_internal` + `rustc_public` MIR/Layout)** | `~3,698` | **`~1,970` (`-10` to `+40` LOC today)** | **`~5,668–5,718` (`~0%` delta)** | **No net win today:** Must retain `override_queries`, all session/census guards, and pre-conversion `PostCleanup` body checks (`is_cleanup`, `CallSource`, `required_consts`, etc.) while paying `rustc_public` version breaks AND `1.98` `ty::Alias` crash |
| **Option C (Recommended): Split `anneal-capture-core` + Thin Per-Toolchain Adapter (`1.100+` hybrid for ADT/Layout/Const)** | **`~3,700` (1 shared crate, `0` `rustc_*` deps)** | **`~1,980` (`rustc_private` only) or `~1,450–1,650` (`1.100+` w/ `rustc_public` `LayoutShape`/`ReprOptions`/`Allocation`)** | **`-330` to `-530` LOC per shim (`-17%`–`-27%` shim TCB) as `#4017` adds general structs/unions/niches/consts; `65%` core decoupled immediately** | **Best architecture:** Isolates `rustc` churn inside `~1.5–1.9 KLOC` per toolchain family; stops re-implementing `rustc_abi::LayoutData` / `rustc_const_eval` internals for `#4017` while preserving 100% of `PostCleanup`, `FileLoader`, AST, and soundness guards |

---

### 5. Multi-Version `rustc` Capture-Shim Architecture (`google/zerocopy#4017`)

**Basis: source + corpus synthesis**

Combining the empirically measured `rustc_public` breakage epochs (`1.91..1.97`, `1.98`, `1.99.1`, `1.100.0`, `1.102`), `rustc-multi-release-mir-abi-drift-and-version-isolated-adapter`'s finding that `rustc_middle`'s `Runtime(PostCleanup)` MIR variants are remarkably stable once wrapped per epoch, and `anneal/trusted/cargo-anneal` / `anneal/trusted/audit` boundary requirements yields a concrete multi-version capture-shim design:

#### 1. Two-Tier Crate & Workspace Separation

Factor `anneal/trusted/rustc-capture/` into:
- **`trusted/capture-core`** (pure stable Rust, **0 `rustc_*` dependencies**):
  - `ir.rs` (`1,067` prod LOC): fail-closed MIR/Layout/Repr/Const IR + type/CFG/retag/place-mention invariants.
  - `lean.rs` (`434` LOC) & `publication.rs` (`119` LOC): chunked balanced Lean emitter + atomic private staging.
  - `identity_host.rs` (`~1,623` LOC): ambient `LD_*` hygiene, ELF64 `PT_INTERP`/`RUNPATH` parsing, `/proc/self/maps` closed-world DSO residency verification, `<sysroot>/bin/rustc` TOCTOU hashing — parameterized over a tiny 3-method trait (`version_str()`, `host_tuple()`, `driver_entry_addr()`).
  - `policy.rs` (`~450` LOC): CLI/scope parsing, disallowed compiler flag filtering, `RecordingLoader` allowlist/symlink-confinement policy (`ReadEvent` ledger & manifest digesting), and compiler-agnostic `Crate` normalization.
- **`trusted/capture-shims/<epoch_id>`** (thin toolchain-coupled binary/crate per supported compiler family, e.g. `v1_98`, `v1_100`, `v1_102`, **`~1,450–1,980` prod LOC each**):
  - Links `capture-core` + `rustc_private` for its pinned toolchain ABI epoch (`1.98`, `1.100` stable w/ `RUSTC_BOOTSTRAP=1`, etc.).
  - Implements `driver.rs` (`Callbacks`, `override_queries` on `mir_drops_elaborated_and_const_checked`, `FileLoader` delegation to `capture_core::policy`), pre-expansion AST `#![crate_type]` / `#![feature]` gate, `DefKind` census, `CodegenFnAttrs` gate, and MIR lowering.
  - On `1.100+` adapters, calls `rustc_internal::run(tcx, || ...)` **strictly as an internal helper for ADT layouts (`LayoutShape`, `ReprOptions`, `TagEncoding`, `discriminant_for_variant`) and constant allocations (`GlobalAlloc`, `Allocation`, `StaticDef`)**, avoiding duplicating fragile `rustc_abi::LayoutData` and `rustc_const_eval` internals across compiler releases while keeping all `PostCleanup` MIR extraction and soundness guards on `&mir::Body<'tcx>`.

#### 2. Versioned Schema, `ProducerProvenance`, and Monotonic `SemProfile`

Consistent with the `T4` per-spoke lowering topology established in `multi-version-ir-migration-topologies-and-capability-schemas`, adapters never pass raw `rustc_middle` or raw `rustc_public` data directly to Lean:
- Every captured IR & Lean `Trusted.MirAst.Program` carries a 3-axis header:
  1. `schema_version`: capture IR wire format version.
  2. `producer_provenance`: `{ capture_shim_id, capture_shim_sha256, rustc_version, rustc_commit_sha, rustc_driver_sha256, target_layout: TargetLayout, mir_preserve_ub }`.
  3. `sem_profile`: monotonic capability set (`mir_ops`, `ub_checks`, `adt_repr`, `adt_layout`, `const_alloc`) negotiated against `Trusted.MirSemantics.Crate.tcb` (`sem_profile` features required by the target spec/proof).
- Because `#[repr(Rust)]` field ordering, enum tag niche selection, and `TargetLayout` can vary across `rustc` releases (`google/zerocopy#4017`), layout-dependent ADTs are lowered into explicit concrete per-compilation records (`AdtRepr` + `TargetLayout` offsets, sizes, alignments, valid scalar ranges, and padding byte masks) emitted into the captured Lean subject rather than hardcoding compiler heuristics inside Lean.

#### 3. Build, Packaging, and Forward-Compatible TCB Accounting

- **Declarative capability manifest instead of `build.rs` in the TCB:** Each shim ships an immutable `toolchain-capture-lock.json` (`compiler_version`, `compiler_commit`, `driver_dso_sha256`, `shim_sha256`, supported `rustc_args` / `-Zmir-preserve-ub` capability flags). `cargo-anneal` selects the matching shim binary by inspecting the target toolchain's `--version --verbose` commit/version against the manifest — avoiding any `build.rs` or proc-macro inside the capture TCB.
- **Additive per-epoch lock entries in `anneal-audit`:** Separating `capture-core`'s SHA-256 / TCB root from per-shim entries in `trusted/root-manifest.sha256` ensures onboarding a new compiler release (`1.100` or `1.102`) adds one small audited `~1.5 KLOC` shim without modifying `capture-core`, `TrustedBoundary.lean`, or `MirSemantics`.

---

### 6. Concrete Upstream `rust-lang/rust` `rustc_public` Feature Requests

**Basis: source + execution**

To make a future **pure `rustc_public`** capture backend viable without sacrificing Anneal's TCB or soundness guarantees, six targeted upstream additions/fixes to `rust-lang/rust` `compiler/rustc_public` are needed:

1. **Pre-Optimization MIR Phase Access & Unflattened Body Metadata:**
   - Expose `CrateItem::body_at_phase(MirPhase)` / `Instance::body_at_phase(MirPhase)` supporting `Runtime(PostCleanup)` (preventing the `-32.8%` `PlaceMention` loss and `-61.5%` statement rewriting measured on `zerocopy`), or allow registering a query hook prior to `optimized_mir`.
   - Preserve `BasicBlock::is_cleanup: bool`, `TerminatorKind::Abort(Option<UnwindTerminateReason>)`, `TerminatorKind::Call { call_source, .. }` (`CallSource::Use` visibility), `Body::required_consts`, `Body::tainted_by_errors`, and `Body::injection_phase`.
2. **Stabilize Ergonomics, `IndexedVal`, and Structured `InlineAsm`:**
   - Re-export `IndexedVal` (`to_val` / `to_index`) in `rustc_public` instead of keeping it `pub(crate)`, and preserve `VariantDef::idx` and `Crate::adts` across stable point releases.
   - Replace `Debug`-stringified `TerminatorKind::InlineAsm` (`template`, `options`, `line_spans`, `InlineAsmOperand::raw_rpr`) with structured AST/operand enums and complete jump-target slices (`targets: Vec<BasicBlockIdx>`).
3. **Fail-Closed CTFE Error Propagation in `BodyBuilder`:**
   - Change `rustc_public_bridge::builder::BodyBuilder::visit_const_operand` so `ErrorHandled::Reported` is returned as a structured `Err` (or explicit `ConstantKind::EvalError`) instead of silently returning `Some(Body)` with an unevaluated constant.
4. **Crate-Root, Attribute, Provenance, and Exhaustive Item Queries:**
   - Expose `Crate::crate_types()`, active `#![feature(...)]` gates (`Features`), parsed `CodegenFnAttrs` / function attributes (`#[inline]`, `#[cold]`, `#[track_caller]`, `#[no_mangle]`, `#[export_name]`, sanitizers), item `Visibility`, `Crate::native_libraries()`, `Crate::global_asm_items()`, `Crate::const_defs()`, and `ExternalCrateSource { dep_kind, extern_paths, is_sysroot }`.
5. **Driver Input Confinement & Pre-Expansion Hooks (`FileLoader`):**
   - Provide a `DriverConfig` / `SessionCallbacks` API supporting custom `FileLoader` injection (to record/confine source reads and compute input digests) and pre-expansion crate-root AST attribute inspection without raw `rustc_driver` / `rustc_ast` imports.
6. **Stable `crates.io` Packaging Decoupled from `#![feature(rustc_private)]`:**
   - Remove the `#![feature(rustc_private)]` + `rustc_driver` macro-expansion dependency (`rustc_public::run!`) via a versioned IPC or driver-shim ABI so downstream verification tools can build with stock stable `rustc` without `RUSTC_BOOTSTRAP=1` and decouple compile-time toolchain updates.

## Boundaries

- All compiled execution measurements ran on Linux `x86_64` (`Little` endian, `64`-bit pointers) against 10 locally installed toolchains (`1.91.0-nightly`–`1.102.0-nightly`, including `1.99.1` and `1.100.0`). Other hosts/targets (`aarch64`, `wasm32`, Windows MSVC) were not probed.
- The `zerocopy` crate (`0.8.64`) was probed in its default `no_std` library configuration (`--cfg no_zerocopy_allocator_api_1_100_0`); `alloc`/`std`/`derive` features and external multi-crate Cargo dependency graphs were not compiled through `rustc_public` here.
- Multi-version shim LOC projections (`~1,450–1,650` LOC on `1.100+` hybrid adapters) are derived directly from exact `rustc-capture/src/*.rs` function-level line spans (`support/results.json`) rather than from writing a full replacement shim.

## Evidence

- `support/inventory_rustc_private.py` + `support/results.json` (`rustc_private_inventory`): Exact LOC breakdown (`8,003` `src/*.rs` = `5,678` non-`mod tests` + `2,325` `mod tests`; `3,285` `tests/`), 9 `rustc_*` crates, all imports, paths, and 26 `TyCtxt` members on `google/zerocopy@3741897d51a2d91354d4427b4a4a155346d16ccf`.
- `support/probe_matrix.py` + `support/results.json` (`cross_version_matrix`): Real compile+run outcomes across 10 toolchains (`05f5a58e8` `1.91.0-nightly`, `94b49fd99` `1.93.0-nightly`, `efc9e1b50` `1.95.0-nightly`, `bf4fbfb7a` `1.97.0-nightly`, `f8a08b688` / `14210df0e` `1.98.0-nightly`, `58cf8f9c3` `1.99.1`, `0ef1bc386` `1.100.0`, `3ef0c22cd` / `8eb778d04` `1.102.0-nightly`).
- `support/probe_target.rs` + `support/probe_driver_1_98.rs` + `support/results.json` (`probe_target_measurements`): Empirical comparison of `rustc_public::run!`, hybrid `override_queries` + `rustc_internal::stable`, `-Zmir-preserve-ub` on/off, `CallSource::Use`, `is_cleanup`, `InlineAsm`, `Option<NonZeroU8>` `TagEncoding::Niche`, `RawUnion` `None`-byte consts, `attr_fn` `tool_attrs = 0`, and `generic_ctfe_bomb::<u8>` exit `101` after `ErrorHandled::Reported` swallow.
- `support/probe_driver_1_102.rs` + `support/results.json` (`real_zerocopy_measurements`): Unmodified `zerocopy/src/lib.rs` (`0.8.64`) panic at `ty.rs:479:17` on `1.98.0-nightly` (`f8a08b688`) and full-crate measurement (`8,558` items, `4,430` `PostCleanup` Fn bodies vs `4,730` `Optimized` bodies, `-316` / `-32.8%` `PlaceMention` loss, `153` hidden `is_cleanup` blocks, `45` `TyKind::Alias` locals) on `1.102.0-nightly` (`8eb778d04`).

## Revalidation

- **Triggers requiring revalidation:** (1) `rustc_public` landing on crates.io without `#![feature(rustc_private)]` / `RUSTC_BOOTSTRAP=1`; (2) upstream `rust-lang/rust` PRs exposing `Runtime(PostCleanup)` bodies, `CallSource`, `is_cleanup`, `CodegenFnAttrs`, `FileLoader`, or structured `InlineAsm` in `rustc_public`; (3) pinning `anneal/trusted/rustc-capture` to `1.100.0+` or implementing `anneal-capture-core` / multi-version shims in `google/zerocopy`.
- **Re-run commands:**
  - `python3 support/inventory_rustc_private.py --capture-root <zerocopy>/anneal/trusted/rustc-capture`
  - `python3 support/probe_matrix.py`
  - Compile `support/probe_driver_1_98.rs` / `support/probe_driver_1_102.rs` against installed toolchains and execute against `support/probe_target.rs` and `zerocopy/src/lib.rs`.
