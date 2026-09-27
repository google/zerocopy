# Diagnostic path normalization and relocation across the Anneal toolchain

## Summary

At the revisions selected by Anneal, diagnostic paths are not one shared cross-tool identifier. Rustc, Charon, Aeneas, Lean batch mode, and Lean LSP each choose paths for different purposes, and relocation can change some of them without changing the source program.

Rustc has explicit path-remapping semantics. `--remap-path-prefix` creates a `RealFileName` that retains a local filesystem path when available and a maybe-remapped path. A scope controls which representation is displayed: rustc diagnostics use the `DIAGNOSTICS` scope. The default remap scope is all scopes, so an active prefix mapping normally affects diagnostics unless the caller narrows it.

Charon does **not** simply serialize rustc's diagnostic path. At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `translate_filename` first asks a real rustc filename for `local_path()`. When that path exists, Charon intentionally takes the local path, even if rustc has a remapped diagnostic representation, then performs its own normalization: path separators are normalized, Rust sysroot paths become `/rustc/...` or `/toolchain/...`, and Cargo-home paths become `/cargo/...`. When no local path is available, Charon instead asks rustc for the `MACRO`-scope path and strips a leading `/rustc/<40-hex-hash>/` component when present.

Aeneas source diagnostics print the Charon file name directly. Consequently, an Aeneas location can be stable across machines for normalized sysroot/Cargo paths while a local-crate location remains tied to the local source path. It can also differ from the path rustc printed for the same source if rustc path remapping was active.

Lean has a separate model. Batch messages retain the frontend's `fileName` string. Direct `lean` passes the CLI filename through to the frontend, so moving a generated Lean file or invoking it through a different path can change the batch diagnostic file name. Lake's build action is an important exception: when it parses Lean JSON diagnostics from a build subprocess, it rewrites the message file name to Lake's relative Lean-file path before logging it. Lean LSP diagnostics are instead attached to the document URI supplied by the client; the server derives its frontend file name from that URI and publishes diagnostics back on the same URI.

The practical rule is therefore to treat diagnostic paths as **producer-local display locators**, not as stable source identities. A cross-layer source map should preserve the raw producer path/URI and bind it to a separately defined source identity. Relocation normalization should be explicit and origin-aware; blanket path-string equality, basename equality, or ad hoc prefix stripping can conflate distinct files or split one file into multiple identities.

Basis: **source** at the exact Rust, Charon, Aeneas, and Lean revisions above. No fresh tool execution was performed.

## Applicability

This report covers path identity and normalization in the versions used by current Anneal's Rust-to-Charon-to-Aeneas-to-Lean pipeline:

- rustc from Charon's `nightly-2026-05-31` toolchain;
- Charon `0.1.210`, commit `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Aeneas `nightly-2026.06.03`, commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

The report concerns file-name/path fields that can appear in diagnostics or source-correspondence metadata. It does not claim that every tool invocation passes through every path described here. In particular:

- rustc remapping behavior depends on the actual `--remap-path-prefix` and `--remap-path-scope` arguments;
- Charon treats locally available and imported/remapped source files differently;
- direct Lean CLI execution and Lake's build action have different file-name handling;
- Lean LSP uses document URIs supplied by the client rather than a batch CLI filename.

"Relocation" here means changing the filesystem root, checkout location, toolchain installation root, Cargo home, generated workspace root, or URI used to address otherwise corresponding source. The report distinguishes path-display stability from source-content or semantic stability.

The immediately adjacent report `cross-tool-utf8-span-columns-2026-09-27`, if present in the corpus revision being used, owns coordinate units. This report assumes coordinates can be associated with a file and asks how the file itself is named.

## Findings

### Rustc distinguishes local paths from remapped paths and applies remapping by scope

`rustc_span::RealFileName` stores:

- an optional `local` representation;
- a `maybe_remapped` representation; and
- the set of `RemapPathScopeComponents` to which the remapping applies.

The source explicitly warns that `local_path()` is for reading from the local host and should not be embedded in build artifacts. `RealFileName::path(scope)` returns the local path when that scope is not remapped and the local representation exists; otherwise it returns the maybe-remapped path.

The relevant scopes include `MACRO`, `DIAGNOSTICS`, `DEBUGINFO`, `COVERAGE`, and `DOCUMENTATION`. Rustc's option parser accepts corresponding names for `--remap-path-scope`; absent an explicit scope argument, it uses all scopes.

Therefore a prefix mapping does not have one universal visible result. The same `RealFileName` can produce a local path for one use and a remapped path for another if the configured scopes differ.

Basis: **source** in pinned `compiler/rustc_span/src/lib.rs` and `compiler/rustc_session/src/config.rs`.

### Rustc JSON diagnostics use the diagnostic-scope filename

`rustc_errors::json::DiagnosticSpan::from_span_full` sets `file_name` with:

`sm.filename_for_diagnostics(&start.file.name)`

and `SourceMap::filename_for_diagnostics` formats the filename with `RemapPathScopeComponents::DIAGNOSTICS`.

The JSON representation also separately records byte offsets and line/column positions. The path string is therefore a diagnostic presentation of the underlying source-file identity, not the only source locator available in rustc's internal model.

A run performed under a different remap prefix can intentionally print the same remapped diagnostic path from a different checkout. Conversely, a run without matching remap options can expose the changed local root even if the source bytes are identical.

Basis: **source** in pinned `compiler/rustc_errors/src/json.rs` and `compiler/rustc_span/src/source_map.rs`.

### Rustc keeps local paths specifically so tools can still read remapped source

`FilePathMapping::to_real_filename` populates the local component even when a path has just been remapped. Its comment explains that this is deliberate: code that needs to load the file from disk still needs the real path.

For source imported from another crate, local information can be unavailable. `SourceMap` then has a heuristic reverse-mapping path for trying to find remapped dependency source locally. The source notes that this reconstruction is heuristic and content hashes are used by the caller to check the loaded source.

This difference matters downstream because Charon branches on `RealFileName::local_path()`. A local current-crate filename and an imported filename that denote analogous source can therefore enter different normalization paths.

Basis: **source** in pinned `compiler/rustc_span/src/source_map.rs`.

### Charon intentionally prefers the local rustc path when it exists

Pinned Charon's `translate_filename` receives a rustc `FileName`. For a real filename, its first branch is `name.local_path()`.

When that returns a path, Charon does not ask rustc for the `DIAGNOSTICS` representation. It starts from the local filesystem path and then applies Charon's own canonicalizations.

This is a material interoperability boundary. Suppose rustc was invoked with a remap from `/checkout-A` to `/src` and diagnostic remapping enabled. Rustc can print `/src/foo.rs`, while Charon running in the same process can receive the same `RealFileName`, recover `/checkout-A/foo.rs` through `local_path()`, and then serialize that local path if none of Charon's own special prefixes applies.

A consumer must not use path-string equality to infer that a rustc diagnostic and a Charon/Aeneas diagnostic refer to different source merely because one path is remapped and the other is local.

Basis: **source** in pinned Charon `charon/src/bin/charon-driver/translate/translate_meta.rs`, interpreted together with pinned rustc `RealFileName::local_path`.

### Charon performs three important relocation normalizations on local paths

After taking a local path, pinned Charon applies its own normalization.

First, it rebuilds the path by splitting path components on `\`. The source explains that this handles cross-compilation to Windows, where separators can otherwise differ.

Second, paths beneath Charon's configured sysroot are rewritten:

- a path under `lib/rustlib/src/rust` becomes `/rustc/<remainder>`;
- another path under the sysroot becomes `/toolchain/<remainder>`.

Third, a path beneath `$CARGO_HOME`, or `$HOME/.cargo` when `CARGO_HOME` is absent, becomes `/cargo/<remainder>`.

These rewrites intentionally remove installation-specific prefixes. They make many standard-library and Cargo-home dependency locations stable across different host roots.

They do not canonicalize arbitrary current-workspace paths. A local crate at `/workspace-A/project/src/lib.rs` can remain `/workspace-A/project/src/lib.rs`; after relocation to `/workspace-B/project`, the serialized Charon file name can change.

Basis: **source** in pinned Charon `translate_meta.rs`.

### When Charon cannot recover a local path, it uses rustc's macro-scope representation

If `RealFileName::local_path()` returns `None`, Charon asks for:

`name.path(RemapPathScopeComponents::MACRO)`

rather than `DIAGNOSTICS`.

For a virtual path beginning with `/rustc/<40-hex-hash>/...`, Charon removes the hash component and keeps `/rustc/...`.

The distinction between `MACRO` and `DIAGNOSTICS` is observable when a rustc invocation configures different remap scopes. Charon's external/imported-path representation is therefore not defined as "whatever rustc would show in a diagnostic."

The hash stripping is also intentionally lossy. It improves stability across compiler revisions/installations but means the Charon string is a normalized navigation path, not a globally unique file identifier.

Basis: **source** in pinned Charon `translate_meta.rs` and pinned rustc remapping definitions.

### Charon source metadata preserves the normalized Charon filename, not a rustc path object

Charon's translated `File` stores a `FileName` variant and, when available, the source contents. `SpanData` refers to the registered file by `FileId`.

Once translation has crossed this boundary, downstream LLBC consumers see Charon's `Local`, `Virtual`, or `NotReal` file-name representation. They do not receive rustc's `RealFileName` with both local/remapped variants and its scope set.

This means a later Aeneas or Anneal component cannot reconstruct rustc's original remapping policy solely from ordinary Charon file metadata. If that policy matters, it must be preserved independently at acquisition time.

Basis: **source** in pinned Charon `charon/src/ast/meta.rs` and `translate_meta.rs`; the reconstruction limitation is **derived** from the discarded rustc path state.

### Aeneas prints the Charon file name directly in source diagnostics

Pinned Aeneas `src/Errors.ml` formats a `Meta.span_data` by matching the file name and taking the contained string for `Virtual`, `Local`, or `NotReal`. It then appends the beginning/end locations.

There is no additional Aeneas path remapping in this formatter. The source path shown by these errors is therefore the Charon-normalized path carried through the serialized metadata.

The same path semantics can also appear in Aeneas-generated source-correspondence comments because those comments use Aeneas' span formatter. The separate Aeneas comments report owns the broader generated-comment behavior; the relevant fact here is that this path layer is inherited, not recomputed from the current Aeneas working directory.

Basis: **source** in pinned Aeneas `src/Errors.ml` and pinned Charon metadata.

### Lean batch messages preserve the frontend's file-name string

Lean's `BaseMessage` stores a `fileName : String`, and the JSON batch path serializes the message after converting its structured data to a `SerialMessage`.

In direct `lean` CLI execution, `Lean/Shell.lean` obtains the input filename from the command-line argument, reads that file, and passes the same `fileName` to `Elab.runFrontend`. Frontend messages then carry that input-context file name.

Thus two semantically identical generated files invoked as:

- `/tmp/run-A/Generated.lean`
- `/tmp/run-B/Generated.lean`

can produce batch JSON messages with different `fileName` values merely because the invocation path changed. Lean batch diagnostics do not perform a general workspace-root canonicalization on that field.

Basis: **source** in pinned Lean `src/Lean/Shell.lean`, `src/Lean/Message.lean`, and frontend/parser message construction.

### Lake build diagnostics deliberately rewrite Lean's batch file name

Lake's build action runs Lean with JSON diagnostics, parses each output line as a `SerialMessage`, and then replaces:

`msg.fileName`

with `mkRelPathString relLeanFile` before logging the message.

This is a separate normalization layer supplied by Lake, not by the Lean frontend. A diagnostic observed through `lake build` can therefore have a stable package-relative file name even though invoking `lean` directly on the same file would preserve the direct CLI path.

Automation must identify the execution surface before comparing diagnostic filenames. "Lean JSON diagnostic" alone is not sufficient to determine the path policy.

Basis: **source** in pinned Lean/Lake `src/lake/Lake/Build/Actions.lean`.

### Lean LSP diagnostics are anchored to the document URI

The Lean server's document metadata contains the LSP `DocumentUri`. `DocumentMeta.mkInputContext` converts a file URI to a filesystem path when possible and uses that string as the frontend file name.

When the server publishes diagnostics, `mkPublishDiagnosticsNotification` sets the notification URI to the document metadata's original `m.uri`. LSP consumers therefore identify the diagnostic document by URI, not by the batch `fileName` string.

The server also resolves module files to real paths before constructing file URIs in `documentUriFromModule?`, explicitly resolving symlinks.

Relocating an interactive workspace can thus change file URIs even when module names and source contents are the same. Symlink spelling can also collapse to the resolved path in server-created module URIs. A cross-run equality test should compare a normalized source identity, not the literal URI string, unless URI equality is itself the property under test.

Basis: **source** in pinned Lean `src/Lean/Server/Utils.lean` and `src/Lean/Data/Lsp/Diagnostics.lean`.

### The same source can legitimately have several path spellings in one end-to-end run

Combining the source-defined policies gives a concrete path-family model:

| Layer | Path representation |
| --- | --- |
| rustc JSON diagnostic | rustc filename under `DIAGNOSTICS` remap scope |
| Charon current/local source | local filesystem path, then Charon normalization |
| Charon imported/remapped source without local path | rustc `MACRO`-scope path, then Charon virtual normalization |
| Aeneas source diagnostic | Charon stored path |
| direct Lean batch JSON | frontend input filename, ordinarily the direct CLI argument |
| Lake-mediated Lean build log | Lake-relative Lean-file path |
| Lean LSP notification | document URI |

These strings should be expected to disagree without implying a source mismatch.

Basis: **derived** from the pinned source paths above.

### A robust source identity needs more than a normalized display string

For Anneal-style cross-layer diagnostics, a path should be modeled as evidence about where a producer found or displayed a source file, not as the identity itself.

A robust mapping record should preserve at least:

1. the raw producer path or URI;
2. the producer and path policy that generated it;
3. a source-space classification such as workspace source, Cargo dependency, Rust sysroot/toolchain source, generated Aeneas Lean, or generated Anneal Lean;
4. a stable identity appropriate to that class, such as workspace-relative path under a known checkout identity, repository/revision/path for immutable dependency source, or generated-artifact identity;
5. source bytes or a content digest when exact diagnostic projection depends on the precise file contents.

Relativization should occur only against a known authoritative root for that source class. Stripping arbitrary common prefixes or reducing to basenames is unsafe: two dependencies can both contain `src/lib.rs`, and `/rustc/...` or `/cargo/...` prefixes intentionally describe different source spaces.

This is a **derived** interoperability recommendation. The inspected tools do not define one common source-identity schema.

### Relocation tests should compare semantics and path policy separately

A useful relocation fixture should copy or reconstruct the same source under two different roots and record each tool's raw path output.

For Rust/Charon/Aeneas, run with and without an explicit rustc remap prefix and preserve:

- rustc JSON `file_name`;
- Charon serialized file table;
- Aeneas rendered source location;
- exact source contents.

Include at least:

- one local crate file;
- one Cargo-home dependency file;
- one Rust sysroot source file; and
- one imported/remapped dependency whose rustc `RealFileName` lacks a usable local path if the fixture can reproduce that state.

For Lean, compare:

- direct `lean --json` on differently rooted generated files;
- the same module through Lake's build action; and
- LSP diagnostics for document URIs under two workspace roots.

The test should assert two different properties separately:

- **semantic/source correspondence:** each diagnostic still resolves to the same intended source identity and range;
- **display-path policy:** the raw path/URI changes or remains stable exactly where the relevant producer policy predicts.

Path-string equality by itself should not be an acceptance criterion.

This test design is **derived** from the source behavior and was not executed in this investigation.

## Boundaries

**No fresh execution.** The report is source-grounded. The relocation matrix in Revalidation remains to be run against the exact selected toolchain.

**No complete rustc path-remapping treatise.** The report covers the `RealFileName`, remap scopes, and diagnostic display behavior needed to interpret Charon and rustc diagnostics. Debug info, coverage, rustdoc, doctests, proc-macro source virtual names, and every metadata transport are not exhaustively surveyed.

**No guarantee that Charon normalization is collision-free.** Replacing install prefixes with `/rustc`, `/toolchain`, or `/cargo`, and stripping a rustc virtual hash, improves reproducibility but is not a proof of global uniqueness.

**No claim that every dependency loses its local path.** Whether `RealFileName::local_path()` is available depends on how the file entered the current compiler session. The source establishes the branch behavior, not a universal population count.

**No claim that direct Lean batch paths are absolute.** Lean preserves the frontend input filename string. Whether that string is absolute or relative depends on how the caller invoked the executable.

**Lake's rewrite is not a general Lean guarantee.** It applies to the inspected Lake build action. Direct `lake env lean ...` executes Lean in the Lake environment but does not, merely by being launched via `lake env`, imply the `Build/Actions.lean` JSON-message rewrite.

**No URI canonicalization guarantee for arbitrary clients.** Lean's LSP publication uses the document URI supplied/retained by the server. Server-created module URIs resolve filesystem symlinks, but this does not make every client-provided URI globally canonical.

**No content-equivalence claim.** Two relocated paths can name different bytes. A source-identity layer must still bind to the expected source revision/content.

**Coordinate units are separate.** Path normalization cannot repair a column-unit mismatch. The cross-tool UTF-8 coordinate report owns those semantics.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Rust compiler

Subject: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, selected by Charon's `nightly-2026-05-31`.

- `compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`
  - `RemapPathScopeComponents`;
  - `RealFileName::{path, embeddable_name, local_path}`;
  - `FileName::display`.
- `compiler/rustc_span/src/source_map.rs`, blob `47c933e245d4942a81f48dc8bcd6b15ba9c39ea7`
  - `SourceMap::filename_for_diagnostics`;
  - `FilePathMapping::to_real_filename`;
  - imported-source local-path/reverse-remapping path.
- `compiler/rustc_session/src/config.rs`, blob `e82f67eac5e9f7d0b089727e6317d77242ba3b1c`
  - `parse_remap_path_scope`; default all-scopes behavior.
- `compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`
  - JSON diagnostic `file_name` uses `filename_for_diagnostics`.

### Charon

Subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`).

- root `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`
  - selects `nightly-2026-05-31`.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`
  - `translate_filename`;
  - local-path preference;
  - Windows separator normalization;
  - `/rustc`, `/toolchain`, `/cargo` canonicalization;
  - `MACRO`-scope fallback and rustc-hash stripping.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`
  - serialized Charon `FileName`, `File`, `SpanData`, and source contents.

### Aeneas

Subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`
  - `span_data_to_string` prints the Charon file-name string directly.

### Lean and Lake

Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`
  - `BaseMessage.fileName` and JSON serialization path.
- `src/Lean/Shell.lean`, blob `2ff5c4b0c82f876ddd4384c9c20dcaefb1b90e`
  - direct CLI input filename is passed to `Elab.runFrontend`.
- `src/lake/Lake/Build/Actions.lean`, blob `5b3ab3cc3e9f45b8c695e31680342acc795004c7`
  - parses Lean JSON `SerialMessage` and rewrites its `fileName` to `mkRelPathString relLeanFile`.
- `src/Lean/Server/Utils.lean`, blob `46a0826d3941b9f749ee4770273eac97d0501103`
  - `DocumentMeta.mkInputContext`;
  - `mkPublishDiagnosticsNotification`;
  - `documentUriFromModule?` resolves symlinks before producing a file URI.
- `src/Lean/Data/Lsp/Diagnostics.lean`, blob `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34`
  - LSP diagnostics publication schema keyed by `DocumentUri`.

Evidence roles are **source** and **derived**. There is no fresh **execution** evidence.

## Revalidation

For a new rustc/Charon/Aeneas combination:

1. inspect rustc `RealFileName`, remap scopes, `SourceMap::filename_for_diagnostics`, and JSON diagnostic construction;
2. inspect Charon `translate_filename` before assuming it follows rustc's diagnostic display policy;
3. search Charon for all construction/rewriting of `meta::FileName`;
4. inspect Aeneas' span formatter and generated-comment/source-map paths for additional rewriting.

For a new Lean/Lake combination:

1. inspect `BaseMessage.fileName`;
2. trace the direct CLI filename into `Elab.runFrontend`;
3. inspect Lake's JSON-message interception/rewrite path;
4. inspect LSP document metadata and publish-diagnostics URI construction.

Then run a minimal relocation matrix. Use two checkout roots whose prefixes and path lengths differ so accidental substring assumptions are visible. Preserve exact command lines, working directories, remap flags, environment variables, raw JSON/LLBC/Lean diagnostics, generated source, and content hashes.

The cheapest discriminating Rust/Charon probe is one local source file compiled twice under different roots with:

- no rustc remap;
- a common `--remap-path-prefix=<root>=/src`;
- a remap restricted away from `diagnostics` but including `macro`;
- a remap including `diagnostics` but excluding `macro`, if the selected compiler accepts that combination.

Compare rustc JSON `file_name` with Charon's serialized file name. This directly tests the source-derived claim that rustc and Charon can choose different representations of one `RealFileName`.

Add one Cargo-home file and one sysroot file to confirm Charon's `/cargo` and `/rustc`/`/toolchain` normalization.

For Lean, invoke one erroring file under two roots directly with `lean --json`, then build the corresponding module through Lake and query it through LSP. Preserve the direct batch file name, Lake-logged file name, and LSP document URI. The expected result is not universal string equality; it is conformance to the distinct source-defined policies above.
