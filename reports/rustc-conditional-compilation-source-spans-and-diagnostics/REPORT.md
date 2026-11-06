# `rustc` Conditional Compilation (`#[cfg]`, `#[cfg_attr]`, `cfg!`), Module File Resolution, Source Span Provenance, and Diagnostic Width Controls

## Summary

This report synthesizes six investigations into how `rustc` and Charon handle pre-HIR conditional compilation, out-of-line module file resolution and path identity, source span hygiene and macro expansion provenance, and diagnostic width/formatting controls across `rustc` `1.98.0-nightly` (`2026-05-31`), `1.98.1` stable, and `1.101.0-nightly` (`2026-09-30`):

1. **Early AST Stripping of `#[cfg]` and `#[cfg_attr]` vs. Expression-Level `cfg!(...)` (`nightly` and `nightly`):**
   - In `rustc` (`compiler/rustc_expand/src/config.rs`, `StripUnconfigured`, and `compiler/rustc_interface/src/passes.rs`, `configure_and_expand`), false `#[cfg(...)]` AST nodes are stripped and true `#[cfg_attr(pred, attr...)]` attributes are expanded during AST configuration and macro expansion—**before** name resolution finishes and before `lower_to_hir` or `mir_built` runs. Excluded items never receive a `DefId`, HIR node, or MIR body.
   - Because `#[cfg_attr(pred, path = "...")]` is expanded during `configure_and_expand`, the active configuration determines which external file is parsed for an out-of-line `mod m;`.
   - By contrast, the built-in `cfg!(...)` macro (`compiler/rustc_builtin_macros/src/cfg.rs`) expands to a boolean literal (`true` or `false`) in expression position; both branch arms of `if cfg!(feature = "a") { ... } else { ... }` are parsed, name-resolved, type-checked, and lowered into HIR and unoptimized MIR (`SwitchInt` on `const true`/`const false`).
   - Across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `2026-09-30`), 16 serial runs across 4 `--cfg` combinations (`none`, `feature="a"`, `custom_from_build`, `both`) on the 3-file fixture in [`support/rust-cfg-hir-mir-r522-may-september/fixture/`](support/rust-cfg-hir-mir-r522-may-september/fixture/) confirmed that excluded `#[cfg]` items and unselected `cfg_attr(path = ...)` files never enter HIR or MIR, while emitted `-Zmir-opt-level=0` `.mir` files are **byte-identical** across both nightlies.
2. **Module File Resolution, `DirOwnership`, `#[path]`, and Non-Canonicalized `StableSourceFileId`:**
   - In `compiler/rustc_expand/src/module.rs` (`default_submod_path`, `mod_file_path_from_attr`), `rustc` resolves an out-of-line `mod m;` relative to the enclosing module's directory and `DirOwnership` (`Mod::ModRs` vs. `Mod::FileOwner`): a root or `mod.rs` owner searches `m.rs` and `m/mod.rs` (emitting `E0761` if both exist), whereas a non-`mod.rs` file `foo.rs` searches `foo/m.rs` and `foo/m/mod.rs`.
   - An explicit `#[path = "..."]` attribute overrides the file lookup and sets the loaded module's `DirOwnership` to `ModRs`-style (so its own children resolve relative to the directory containing the `#[path]` target file), and `rustc` requires `#[path = "..."]` to be a literal string after `cfg_attr` expansion (rejecting unexpanded macro calls in `#[path = mac!()]`).
   - Crucially, `SourceMap::load_file` (`compiler/rustc_span/src/source_map.rs`) does **not** call `std::fs::canonicalize`, and `StableSourceFileId` (`rustc_span/src/lib.rs`) hashes the `FileName` (`RealFileName` local/remapped path string and `StableCrateId`), **not** the file's content hash or filesystem inode. Consequently, loading the same physical file through two different relative paths or symlinks produces two distinct `SourceFile` records unless they form a direct parent-child module cycle (`check_mod_file_cycle`).
3. **Source Span Hygiene (`SyntaxContext` / `ExpnData`) vs. Charon's Flattened `Span` Model:**
   - In `rustc_span` (`SpanData { lo: BytePos, hi: BytePos, ctxt: SyntaxContext, parent: Option<LocalDefId> }`), every span carries a `SyntaxContext` indexing a chain of `ExpnData` records (`ExpnKind::{Macro, AstPass, Desugaring}`, `call_site: Span`, `def_site: Span`, `transparency: Transparency::{Transparent, SemiTransparent, Opaque}`), and `proc_macro::Span` independently exposes `resolved_at` (`ctxt`) and `located_at` (`lo`/`hi`).
   - By contrast, Charon `0.1.210` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/bin/charon-driver/translate/translate_meta.rs`) translates `rustc_span::Span` into `charon_lib::meta::Span { data: RawSpan, generated_from_span: Option<RawSpan> }`:
     - Charon converts `lo` and `hi` via `SourceMap::lookup_char_pos` into `(FileId, Loc { line: usize, col: usize })` (`1`-based line, `0`-based character column `col_display`), **discarding `SyntaxContext` and `ExpnData` (`call_site`/`def_site`)**.
     - Charon rejects virtual `FileName` variants (`QuoteExpansion`, `Anon`, `MacroExpansion`, `ProcMacroSourceCode`, `CliCrateAttr`, `Custom`, `DocTest`) with `unimplemented!()`, supporting only `FileName::Real` (`LocalPath` / `Remapped`).
     - Charon populates `generated_from_span` **only** from MIR `SourceScopeData::inlined_parent_scope` (MIR inlining), never from macro expansion (`Span::parent_callsite()`).
4. **`--diagnostic-width=<N>` and Output-Format Controls Across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`:**
   - In `rustc` (`compiler/rustc_session/src/options.rs` and `compiler/rustc_errors/src/emitter.rs` / `json.rs`), `--diagnostic-width=<N>` is marked `UNTRACKED` for incremental-compilation dep-tracking, overrides terminal width detection in `Session::diagnostic_width()`, and is passed into both human `AnnotateSnippetEmitter` and JSON `JsonEmitter` (which renders the human snippet into the JSON `rendered` field).
   - Crucially, `Session::diagnostic_width()` is also queried **before** rendering during structured diagnostic construction: `TyCtxt::short_string` (`compiler/rustc_middle/src/ty/print/pretty.rs`, controlled alongside `-Z write-long-types-to-disk=yes`) uses `diagnostic_width()` to decide when to abbreviate long types to `<...>` / `<_>` and write `<crate>.long-type-<hash>.txt` files, and trait-error reporting (`compiler/rustc_trait_selection/src/error_reporting/traits/fulfillment_errors.rs`) uses `diagnostic_width()` to decide whether the list of implemented traits fits in the primary span label or is moved into a separate `help` child diagnostic!
   - Executing 15 serial runs across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`), stable `rustc 1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`), and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `2026-09-30`) at `--diagnostic-width=40` vs. `--diagnostic-width=100` in `human`, `json`, and `json` + `--json=diagnostic-short` modes ([`support/rustc-diagnostic-width-to/results.json`](support/rustc-diagnostic-width-to/results.json)) proved:
     - Within every compiler version, changing `--diagnostic-width=100` to `--diagnostic-width=40` mutates not only `rendered`, but also the top-level structured JSON `message` (`Wrap<Option<Result<Vec<(u32, u64)>, &str>>>` shortened at width `40`), primary `spans[0].label` (`the trait ... is not implemented for ...` shortened to `unsatisfied trait bound`), and `children` (`help` text).
     - Across compiler versions, `1.98.0-nightly` and `1.98.1` produce **identical** diagnostic outputs (`Wrap<...>`), whereas `1.101.0-nightly` changed the type-abbreviation placeholder from `Wrap<...>` to `Wrap<_>` and added a note path (`note: required by a bound in 'need'`) at width `40`.

---

## Applicability

This report applies to the following pinned compilers, language references, and tools recorded in `REPORT.json`:

| Component / Subject | Version / Toolchain Date | Commit / Revision | Scope & Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (`nightly` source pin)** | `nightly` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Source audit of `StripUnconfigured`, `cfg!`, `rustc_expand::module`, `SourceMap`, `SpanData`, and `SyntaxContext`. |
| **`rust-lang/rust` (`nightly` binary)** | `1.98.0-nightly` (`2026-05-30`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | Source audit of `--diagnostic-width` and empirical execution of `#[cfg]`/`cfg_attr`/`cfg!` and diagnostic-width matrices (`aarch64-apple-darwin`, `SHA-256: 2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`). |
| **`rust-lang/rust` (`1.98.1` stable binary)** | `1.98.1` | `48a229ceaefd4985c50990b14116b6d856af0985` | Stable comparison target in the 15-run `--diagnostic-width` execution matrix (`aarch64-apple-darwin`). |
| **`rust-lang/rust` (`nightly` binary)** | `1.101.0-nightly` (`2026-09-29`) | `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` | Newer nightly comparison target in both the 16-run `#[cfg]` HIR/MIR matrix and the 15-run `--diagnostic-width` matrix (`aarch64-apple-darwin`, `SHA-256: 29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d`). |
| **`rust-lang/cargo`** | `nightly` | `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` | Cargo `--cfg feature="..."`, `--cfg test`, and build-script `cargo::rustc-cfg=` forwarding. |
| **`rust-lang/reference`** | Normative Reference | `ad35aca481751a06afeb23820a672b0f3b11a476` | Normative rules for `#[cfg]`, `#[cfg_attr]`, `cfg!`, `mod`, and `#[path]`. |
| **`AeneasVerif/charon`** | `0.1.210` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | Charon `translate_meta.rs` span conversion and `FileName` handling. |
| **`google/zerocopy`** | `tools/ui-runner` | `41f5b37afe7060fd9fe08c00b200672cd76d77b9` | UI diagnostic test runner consuming `rustc` human/JSON diagnostics. |

---

## Findings

### 1. Pre-HIR Conditional Compilation (`#[cfg]`, `#[cfg_attr]`) vs. Expression-Level `cfg!(...)` (`1.98.0-nightly` and `1.101.0-nightly`)

`Basis: normative, source, execution`

In `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/conditional-compilation.md`), `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`:

1. **Compiler Phase Ordering (`StripUnconfigured` vs. `cfg!`):**
   - `rustc_interface::passes::configure_and_expand` runs `StripUnconfigured` (`compiler/rustc_expand/src/config.rs`) integrated with the macro expander (`MacroExpander`).
   - Whenever `cfg_true` evaluates a `#[cfg(pred)]` attribute to `false`, the annotated item, field, variant, match arm, or statement is deleted from the AST before name resolution finishes and before `lower_to_hir` runs.
   - Whenever `#[cfg_attr(pred, attr1, attr2)]` evaluates `pred` to `true`, `rustc` splices `attr1, attr2` in place of the `cfg_attr` attribute. When one of those attributes is `path = "selected_a.rs"` on an out-of-line `mod selected;`, the module loader (`rustc_expand/src/module.rs`) reads only the selected file; unselected files are never opened or parsed.
   - By contrast, `cfg!(pred)` (`compiler/rustc_builtin_macros/src/cfg.rs`) is an ordinary built-in macro that expands in expression position to an AST boolean literal (`true` or `false`). In `if cfg!(feature = "a") { 70 } else { 80 }`, **both** branches remain in the AST, undergo full name resolution and type checking, and are lowered into HIR and unoptimized MIR (`SwitchInt(const true)` / `SwitchInt(const false)`).
   - Cargo (`src/cargo/core/compiler/mod.rs`) passes `--cfg feature="<name>"` for each enabled feature of a compilation unit, `--cfg test` for test/benchmark units, and custom `--cfg <key>` flags emitted by build scripts via `cargo::rustc-cfg=<key>`.
2. **Multi-Version Execution Verification (`1.98.0-nightly` vs. `1.101.0-nightly`):**
   - In [`support/rust-cfg-hir-mir-r522-may-september/`](support/rust-cfg-hir-mir-r522-may-september/), the 3-file fixture ([`main.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/main.rs), [`selected_a.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/selected_a.rs), [`selected_b.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/selected_b.rs)) was compiled across 4 `--cfg` combinations (`neither`, `feature="a"`, `custom_from_build`, `both`) under both `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`) with `-Zunpretty=hir-tree` and `--emit=mir -Zmir-opt-level=0`:

| `--cfg` Configuration | Present HIR/MIR Feature Item | Present HIR/MIR Custom Item | Selected Module File & Function | Macro-Emitted Item | `cfg_control` in `-Zmir-opt-level=0` MIR | `1.98.0-nightly` vs. `1.101.0-nightly` Comparison |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`neither`** (no `--cfg`) | `feature_off_only` | `no_custom_cfg_only` | `selected_b.rs` (`selected_b_only`) | `macro_off_only` | `switchInt(const false)` with both `70_u32` and `80_u32` arms | HIR owner sets identical; `.mir` files **byte-identical**. |
| **`--cfg 'feature="a"'`** | `feature_a_only` | `no_custom_cfg_only` | `selected_a.rs` (`selected_a_only`) | `macro_a_only` | `switchInt(const true)` with both `70_u32` and `80_u32` arms | HIR owner sets identical; `.mir` files **byte-identical**. |
| **`--cfg custom_from_build`** | `feature_off_only` | `custom_cfg_only` | `selected_b.rs` (`selected_b_only`) | `macro_off_only` | `switchInt(const false)` with both `70_u32` and `80_u32` arms | HIR owner sets identical; `.mir` files **byte-identical**. |
| **`both`** | `feature_a_only` | `custom_cfg_only` | `selected_a.rs` (`selected_a_only`) | `macro_a_only` | `switchInt(const true)` with both `70_u32` and `80_u32` arms | HIR owner sets identical; `.mir` files **byte-identical**. |

---

### 2. Module File Resolution, `DirOwnership`, `#[path]`, and `StableSourceFileId` Identity

`Basis: normative, source`

At `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/items/modules.md`) and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`compiler/rustc_expand/src/module.rs`, `compiler/rustc_parse/src/parser/item.rs`, and `compiler/rustc_span/src/source_map.rs`):

1. **Logical Module Identity (`DefId`) vs. Source File Identity (`SourceFile` / `StableSourceFileId`):**
   - Logical modules are identified by their `DefPath` in the module hierarchy (`crate::m::sub`), whereas source files are stored in `SourceMap` as `SourceFile` records keyed by `StableSourceFileId`.
2. **`DirOwnership` (`ModRs` vs. `FileOwner`) and Ambiguity Rejection (`E0761`):**
   - For an unannotated out-of-line `mod m;`:
     - If the enclosing module is a crate root, `mod.rs`, or an inline `mod parent { ... }` (or has an explicit `#[path]` attribute), its `DirOwnership` is `Mod::ModRs`, and `default_submod_path` searches `<dir>/m.rs` and `<dir>/m/mod.rs`. If **both** exist on disk, `rustc` rejects the build with `E0761` (`file for module 'm' found at both "m.rs" and "m/mod.rs"`).
     - If the enclosing module was loaded from `<dir>/foo.rs` without `#[path]`, its `DirOwnership` is `Mod::FileOwner("foo")`, and `default_submod_path` searches `<dir>/foo/m.rs` and `<dir>/foo/m/mod.rs`.
3. **Explicit `#[path = "..."]` Semantics:**
   - `mod_file_path_from_attr` extracts the last `#[path = "..."]` attribute on a module (and compounds `#[path = "dir"]` on inline `mod inline { #[path = "file.rs"] mod child; }` into `dir/file.rs`).
   - Any file loaded via an explicit `#[path = "..."]` is assigned `DirOwnership::ModRs` (`mod.rs`-style), so its own unannotated child modules resolve directly inside the directory containing the `#[path]` target file rather than a `<stem>/` subdirectory.
   - Furthermore, `rustc` requires the `#[path = ...]` value to be a string literal at attribute inspection time; macro invocations inside `#[path = concat!(...)]` are not expanded by `mod_file_path_from_attr` and trigger an error.
4. **Absence of `fs::canonicalize` and Symlink/Relative-Path Aliasing in `SourceMap`:**
   - `SourceMap::load_file` normalizes `./` components via `normalize_path`, maps prefixes via `FilePathMapping` (`--remap-path-prefix`), and constructs `FileName::Real(RealFileName)` (preserving `local_path` alongside `remapped_path`).
   - `SourceMap::load_file` does **not** call `std::fs::canonicalize`, and `StableSourceFileId` hashes `(FileName, StableCrateId)` rather than file content SHA-256 or inode number. If two modules reference the same underlying file via two distinct relative paths or symlinks (or via `include!`), `SourceMap` creates two separate `SourceFile` entries with disjoint byte-position ranges (`lo..hi`).

---

### 3. Source Span Provenance (`SyntaxContext` / `ExpnData`) vs. Charon's Flattened Span Model

`Basis: source`

Comparing `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`compiler/rustc_span/src/lib.rs`, `hygiene.rs`) with `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`charon/src/bin/charon-driver/translate/translate_meta.rs` and `charon-lib/src/meta.rs`) reveals four provenance boundaries:

| Provenance Dimension | `rustc` (`rustc_span` & `proc_macro::Span`) | Charon `0.1.210` (`translate_meta.rs` & `charon_lib::meta::Span`) | Implication for Downstream Verifiers |
| :--- | :--- | :--- | :--- |
| **Byte Offset vs. Line/Column Coordinates** | `SpanData` stores global `BytePos` (`lo`, `hi`) across the session `SourceMap`'s contiguous virtual byte space. | Calls `SourceMap::lookup_char_pos(lo)` and `lookup_char_pos(hi)` to emit `RawSpan { file_id, beg: Loc, end: Loc }` with `1`-based `line` and `0`-based `col` (`CharPos` / `col_display`). | Charon `.llbc` spans do not preserve raw UTF-8 byte offsets; mapping back to source bytes requires line/char indexing. |
| **Macro Hygiene & Expansion Chain (`SyntaxContext` / `ExpnData`)** | `SpanData.ctxt` (`SyntaxContext`) indexes a full `ExpnData` tree (`call_site`, `def_site`, `ExpnKind`, `Transparency`), allowing `span.source_callsite()` to walk from a macro body token out to the top-level invocation site, and `proc_macro::Span::located_at` / `resolved_at` to mix location and hygiene independently. | `translate_raw_span` converts `span.lo()` and `span.hi()` **directly without calling `source_callsite()` and without exporting `SyntaxContext` or `ExpnData`**. | For tokens originating inside a declarative or procedural macro definition (whose `lo`/`hi` was not overridden with `located_at(call_site)`), Charon's `RawSpan` points to the macro definition file/line rather than the macro invocation site. |
| **`generated_from_span` Field** | `rustc` tracks both macro expansion (`Span::parent_callsite`) and MIR inlining (`SourceScopeData::inlined_parent_scope`). | `translate_span_from_source_info` populates `Span.generated_from_span` **solely** by walking `SourceScopeData::inlined_parent_scope` in the MIR scope tree. | Since Charon runs at `-Z mir-opt-level=0` (where the MIR `Inline` pass does not run except for `#[rustc_force_inline]`), `generated_from_span` is almost always `None` and never records macro expansion ancestry. |
| **Virtual `FileName` Variants** | `FileName` includes `Real`, `QuoteExpansion`, `Anon`, `MacroExpansion`, `ProcMacroSourceCode`, `CliCrateAttr`, `Custom`, `DocTest`, `CfgSpec`. | `translate_filename` handles only `FileName::Real(RealFileName)` and panics with `unimplemented!()` on all other `FileName` variants. | Synthetic spans from quote expansions or custom harnesses cannot be translated by Charon `0.1.210`. |

---

### 4. `--diagnostic-width=<N>` and Output-Format Controls Across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`

`Basis: source, execution`

Auditing `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`compiler/rustc_session/src/options.rs`, `compiler/rustc_session/src/config.rs`, `compiler/rustc_errors/src/emitter.rs`, `compiler/rustc_errors/src/json.rs`, `compiler/rustc_middle/src/ty/print/pretty.rs`, and `compiler/rustc_trait_selection/src/error_reporting/traits/fulfillment_errors.rs`) alongside `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`tools/ui-runner`, mapped in [`support/rustc-diagnostic-width-format/source-map.json`](support/rustc-diagnostic-width-format/source-map.json) and [`support/rustc-diagnostic-width-format/diagnostic-controls.json`](support/rustc-diagnostic-width-format/diagnostic-controls.json)) and executing the 15-run multi-version matrix in [`support/rustc-diagnostic-width-to/results.json`](support/rustc-diagnostic-width-to/results.json) establishes four findings:

1. **Precedence of `--diagnostic-width=<N>` Over Terminal Width Discovery:**
   - `Session::diagnostic_width()` (`compiler/rustc_session/src/session.rs`) returns `self.opts.diagnostic_width`, which is wired to both the human `AnnotateSnippetEmitter` (`terminal_width`) and the internal `HumanEmitter` used by `JsonEmitter` to format the `rendered` string inside `--error-format=json` objects.
   - Only when `--diagnostic-width` is omitted (`None`) does `AnnotateSnippetEmitter` fall back to querying `stderr` terminal dimensions (`DEFAULT_COLUMN_WIDTH = 140`).
   - `--diagnostic-width` is marked `UNTRACKED` in `options.rs`, so changing it does not invalidate incremental-compilation query hashes.
2. **Interaction Between `--error-format` and `--json=...` Sub-Options:**
   - `--error-format=human | short | json` selects the top-level emitter (`config.rs`); passing `--json=diagnostic-short` or `--json=diagnostic-rendered-ansi` requires `--error-format=json` (otherwise `rustc` exits with an option validation error) and modifies only the `rendered` field inside each emitted JSON line.
3. **Structured Diagnostic Mutation Under Narrow `--diagnostic-width` (`TyCtxt::short_string` and Trait Fulfillment Errors):**
   - `Session::diagnostic_width()` is not merely a visual line-wrapping parameter:
     - `TyCtxt::short_string` (`pretty.rs`) uses `diagnostic_width()` to threshold type-string length; when a printed type exceeds the width budget, `short_string` replaces inner generic arguments with `<...>` (in `1.98.0-nightly` and `1.98.1`) or `<_>` (in `1.101.0-nightly`) and records a sidecar `.long-type-<hash>.txt` path (written when `-Z write-long-types-to-disk=yes`).
     - `fulfillment_errors.rs` uses `diagnostic_width()` to decide whether the list of candidate trait implementations fits inside the primary span label or is emitted as a separate `help` child diagnostic.
4. **15-Run Multi-Version Execution Matrix (`1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`):**
   - Compiling the trait-bound failure probe (`struct Wrap<T>(T); trait Marker {} fn need<T: Marker>(_: T) {}` called with `Wrap<Option<Result<Vec<(u32, u64)>, &'static str>>>`) at `--diagnostic-width=100` vs. `--diagnostic-width=40` across all three compilers ([`support/rustc-diagnostic-width-to/results.json`](support/rustc-diagnostic-width-to/results.json)):

| Compiler Version | Width `100` JSON `message` & `spans[0].label` | Width `40` JSON `message` & `spans[0].label` | Multi-Version Continuity / Drift |
| :--- | :--- | :--- | :--- |
| **`1.98.0-nightly` (`2026-05-31`, `f8a08b688`)** | Full type `Wrap<Option<Result<Vec<(u32, u64)>, &str>>>` in `message`; full `the trait 'Marker' is not implemented for ...` in `spans[0].label` | Shortened `Wrap<...>` in `message` + `the full type name has been written to ...` note; shortened `"unsatisfied trait bound"` in `spans[0].label` | Baseline (`nightly`). |
| **`1.98.1` stable (`48a229cea`)** | Full type `Wrap<Option<Result<Vec<(u32, u64)>, &str>>>` in `message` and `spans[0].label` | Shortened `Wrap<...>` in `message`; shortened `"unsatisfied trait bound"` in `spans[0].label` | **100% identical** to `1.98.0-nightly` across all 5 width/format modes (`human`, `json`, `json-short` at widths `40` and `100`). |
| **`1.101.0-nightly` (`2026-09-30`, `5c543b0b8`)** | Full type in `message` and `spans[0].label` (matches `1.98.x` at width `100`) | Shortened **`Wrap<_>`** (instead of `Wrap<...>`) in `message` and `help` child; adds source path to `note: required by a bound in 'need'` in `diagnostic-short` at width `40` | Width `100` matches `1.98.x`; width `40` exhibits placeholder drift (`<...>` $\to$ `<_>`). |

---

## Boundaries

1. **Unconfigured Code Is Invisible to HIR/MIR Tools:** Any verification pipeline operating on HIR, THIR, MIR, or Charon `.llbc` verifies only the single active `--cfg` configuration of that `rustc` invocation; code behind inactive `#[cfg(...)]` predicates or unselected `#[cfg_attr(..., path = "...")]` files is stripped before HIR construction.
2. **Structured JSON Diagnostics Are Not Width-Invariant:** Test harnesses (such as `zerocopy`'s `tools/ui-runner`) that parse `--error-format=json` must still pin `--diagnostic-width=<N>` if they assert on `message`, `spans[].label`, or `children[].message`, because `TyCtxt::short_string` and trait-error formatting mutate those structured JSON fields as a function of `Session::diagnostic_width()`.

---

## Evidence

All supporting Rust fixtures, raw HIR/MIR/diagnostic outputs, and offline verification scripts are preserved under `support/`:

- **Multi-Version (`2026-05-31` vs. `2026-09-30`) `#[cfg]` / `#[cfg_attr]` / `cfg!` HIR & MIR Matrix (`support/rust-cfg-hir-mir-r522-may-september/`):**
  - Fixtures and scripts: [`support/rust-cfg-hir-mir-r522-may-september/fixture/main.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/main.rs), [`support/rust-cfg-hir-mir-r522-may-september/fixture/selected_a.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/selected_a.rs), [`support/rust-cfg-hir-mir-r522-may-september/fixture/selected_b.rs`](support/rust-cfg-hir-mir-r522-may-september/fixture/selected_b.rs), [`support/rust-cfg-hir-mir-r522-may-september/check.py`](support/rust-cfg-hir-mir-r522-may-september/check.py), [`support/rust-cfg-hir-mir-r522-may-september/probe.py`](support/rust-cfg-hir-mir-r522-may-september/probe.py), [`support/rust-cfg-hir-mir-r522-may-september/analyze.py`](support/rust-cfg-hir-mir-r522-may-september/analyze.py).
  - Recorded results and raw outputs: [`support/rust-cfg-hir-mir-r522-may-september/results.json`](support/rust-cfg-hir-mir-r522-may-september/results.json), [`support/rust-cfg-hir-mir-r522-may-september/analysis.json`](support/rust-cfg-hir-mir-r522-may-september/analysis.json), [`support/rust-cfg-hir-mir-r522-may-september/raw/old/both.mir`](support/rust-cfg-hir-mir-r522-may-september/raw/old/both.mir), [`support/rust-cfg-hir-mir-r522-may-september/raw/new/both.mir`](support/rust-cfg-hir-mir-r522-may-september/raw/new/both.mir).
- **Diagnostic Width Source Map & Multi-Version (`1.98.0-nightly`, `1.98.1`, `1.101.0-nightly`) Execution Matrix:**
  - Source map and controls (`support/rustc-diagnostic-width-format/`): [`support/rustc-diagnostic-width-format/source-map.json`](support/rustc-diagnostic-width-format/source-map.json), [`support/rustc-diagnostic-width-format/diagnostic-controls.json`](support/rustc-diagnostic-width-format/diagnostic-controls.json).
  - Multi-version execution results and raw stderr streams (`support/rustc-diagnostic-width-to/`): [`support/rustc-diagnostic-width-to/results.json`](support/rustc-diagnostic-width-to/results.json), [`support/rustc-diagnostic-width-to/raw/nightly-human-w40.stderr`](support/rustc-diagnostic-width-to/raw/nightly-human-w40.stderr), [`support/rustc-diagnostic-width-to/raw/nightly-human-w100.stderr`](support/rustc-diagnostic-width-to/raw/nightly-human-w100.stderr), [`support/rustc-diagnostic-width-to/raw/nightly-json-w40.stderr`](support/rustc-diagnostic-width-to/raw/nightly-json-w40.stderr), [`support/rustc-diagnostic-width-to/raw/nightly-json-w100.stderr`](support/rustc-diagnostic-width-to/raw/nightly-json-w100.stderr).

---

## Revalidation

Run the following self-contained commands from this package directory to verify the 16-run `#[cfg]` HIR/MIR matrix and the 15-run `--diagnostic-width` multi-version artifacts:

```bash
# 1. Verify the 16-run multi-version (2026-05-31 vs. 2026-09-30) #[cfg] / #[cfg_attr] / cfg! HIR and MIR artifacts offline
python3 -B support/rust-cfg-hir-mir-r522-may-september/check.py

# 2. Reproduce the 4-configuration MIR emission on support/rust-cfg-hir-mir-r522-may-september/fixture/main.rs
mkdir -p build/cfg-probe
rustc +nightly --edition 2021 --crate-type lib \
  --cfg 'feature="a"' --cfg custom_from_build \
  -Zmir-opt-level=0 --emit=mir \
  -o build/cfg-probe/both.mir \
  support/rust-cfg-hir-mir-r522-may-september/fixture/main.rs

# 3. Verify the 15-run multi-version (2026-05-31, 1.98.1, 2026-09-30) --diagnostic-width results.json
python3 - << 'EOF'
import json, pathlib
res = json.loads(pathlib.Path("support/rustc-diagnostic-width-to/results.json").read_text())
runs = res["runs"] if isinstance(res, dict) and "runs" in res else res
assert len(runs) == 15, f"Expected 15 runs, got {len(runs)}"
print("Verified 15 diagnostic-width execution records.")
EOF
```
