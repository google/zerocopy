# External-crate source recovery for diagnostics

## Summary

The selected Rust compiler contains a real external-source recovery mechanism, but the selected Charon translation does not carry that mechanism across the LLBC boundary.

At the rustc revision corresponding to Charon's `nightly-2026-05-31` toolchain, an imported `SourceFile` retains its file identity, line table, multibyte-character metadata, crate number, and source hash even though its ordinary `src` field is `None`. When rustc needs source text for an imported file, `SourceMap::ensure_source_file_source_present` first tries the file's local path. If no local path exists, it can heuristically reverse a configured remap prefix. The candidate bytes are accepted only if their pre-normalization hash matches the source hash recorded in crate metadata. Rustc's diagnostic emitter uses this recovery path before deciding that source code cannot be shown.

Charon 0.1.210 loses the integrity-bound recovery capability at translation time. `register_file` copies only `source_file.src` into LLBC `File.contents`. For imported rustc source files, that field is `None`; source recovered lazily into rustc's `external_src` is not consulted. Charon does preserve a normalized file name, the source crate name, line/column locations, and the optional `contents` field, but it does not serialize rustc's source hash or stable source-file identifier. An LLBC consumer can therefore know *where rustc said the span was* without necessarily possessing either the corresponding source bytes or a cryptographic value that can validate independently recovered bytes.

Aeneas preserves that limitation. Its source diagnostics print Charon's file-name string and line/column locations directly. They do not recover source bytes.

Historical Anneal V1 was intentionally narrower still: its `DiagnosticMapper` only rendered source excerpts for paths lexically within the user's workspace root. Dependency and system paths fell back to an external diagnostic containing the path and line rather than a source excerpt. That behavior is historical evidence, not current Anneal architecture authority.

For Anneal, external-crate diagnostics should therefore distinguish **location metadata** from **verified source recovery**. At the pinned toolchain, rustc has enough metadata to recover and verify imported source while the compiler session is alive; ordinary Charon/Aeneas artifacts do not preserve the source hash needed to reproduce that guarantee downstream. If a later Anneal stage needs exact dependency-source excerpts, it needs either source bytes captured at translation time or an explicit content identity carried across the translation boundary. Path rewriting alone is not enough.

Basis: exact pinned rustc, Charon, Aeneas, and historical Anneal source. No fresh compiler/translator execution was performed.

## Applicability

This report covers the external-source behavior relevant to the current Anneal-selected translation stack:

- rustc source revision `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, corresponding to Charon's `nightly-2026-05-31` toolchain;
- Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`);
- Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`);
- current Anneal authority `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- historical Anneal V1 at that same repository revision, used only as implementation evidence.

"External crate" here means source imported from another crate into the current rustc `SourceMap`, including dependency and standard-library source represented through crate metadata. It does not mean merely "a file outside the current working directory." Rustc's decisive internal distinction is whether the `SourceFile` is imported: imported files have `src = None` and carry an `ExternalSource` slot that can be populated lazily.

"Source recovery" means obtaining source text corresponding to a diagnostic/span and having evidence that the text is the source rustc used. A path that can be opened is weaker evidence. A line/column pair without bytes is location metadata, not source recovery.

The report does not prescribe how current Anneal must package dependency sources. Current Anneal design authority requires Rust-oriented diagnostics but has not fixed this particular source-identity mechanism.

## Findings

### Rustc keeps enough metadata for imported spans even when source text is absent

`SourceMap::new_imported_source_file` constructs a `SourceFile` for source metadata imported from another crate.

The imported file deliberately has:

- `src: None`;
- the original `src_hash`;
- an optional checksum hash;
- normalized and unnormalized source lengths;
- line-start metadata;
- multibyte-character metadata;
- normalization metadata;
- a stable source-file identifier;
- the originating crate number; and
- `external_src = Foreign { AbsentOk, metadata_index }`.

The source comment says the source code of an imported file is not initially available, but enough data is retained to generate accurate locations for code inlined from another crate.

This is the first important boundary: rustc does not need the source bytes in memory to carry meaningful imported spans. It preserves a compact location model and a content hash separately.

Basis: **source** in pinned `compiler/rustc_span/src/source_map.rs` and `compiler/rustc_span/src/lib.rs`.

### Rustc can lazily recover imported source and verifies it by content hash

`SourceMap::ensure_source_file_source_present` attempts to populate an imported file's external source.

For a real filename it chooses a candidate path as follows:

1. if `RealFileName::local_path()` exists, use that local path;
2. otherwise obtain the diagnostic-scope path and ask `FilePathMapping::reverse_map_prefix_heuristically` for a candidate local path;
3. if there is no unique usable reverse mapping, use the maybe-remapped path itself.

The reverse mapping is explicitly documented as heuristic and potentially wrong. Rustc does not trust it on its own.

`SourceFile::add_external_src` supplies the integrity check. It reads candidate source text, recomputes the recorded `src_hash` on the pre-normalized bytes, accepts the source only when the hashes match, then normalizes it. A missing file or hash mismatch transitions the external-source state to `AbsentErr`.

This is a stronger contract than "find a file with this path." Path reconstruction discovers a candidate; the recorded source hash establishes whether the bytes match the source represented by imported metadata.

Basis: **source** in pinned `compiler/rustc_span/src/source_map.rs` and `compiler/rustc_span/src/lib.rs`.

### Rustc diagnostics use that recovery path before hiding source excerpts

The rustc diagnostic emitter's `should_show_source_code` first calls `ensure_source_file_source_present`. If recovery fails, the emitter declines to show the source. If recovery succeeds, it applies any configured ignored-directory policy.

Thus rustc itself already treats dependency-source presentation as a recover-and-verify operation. The location can remain reportable when source recovery fails, but source excerpts are gated on actual source availability.

This distinction is directly useful to Anneal: absence of an excerpt does not mean the imported span has no file or location metadata.

Basis: **source** in pinned `compiler/rustc_errors/src/emitter.rs`.

### Charon normalizes imported filenames but does not preserve rustc's source-recovery proof

Pinned Charon obtains the rustc `SourceFile` while registering a translated file. It stores:

- a translated `FileName`;
- the source crate name; and
- `contents: source_file.src.as_deref().cloned()`.

That last expression is decisive for imported source. Rustc defines `SourceFile::is_imported()` as `src.is_none()`. Even if rustc has lazily loaded verified bytes into `external_src`, the imported file's `src` field remains `None`.

Charon does not call `ensure_source_file_source_present` here and does not inspect `external_src`. Therefore an imported file is serialized with `contents = None` through this path.

The LLBC `File` type has no source-hash field and no rustc stable-source-file identifier. Those facts are present in rustc's `SourceFile` but are not part of Charon's serialized `File`.

The resulting boundary is exact:

- rustc can possess a hash-verified external source;
- Charon can preserve the imported span's normalized filename, crate name, and line/column coordinates;
- ordinary Charon serialization does not preserve the hash or recovered external bytes needed for the same verification downstream.

Basis: **source** in pinned Charon `translate_meta.rs` and `charon/src/ast/meta.rs`, interpreted with pinned rustc `SourceFile`.

### Charon's filename normalization helps navigation but is not an integrity identity

Charon gives filenames useful cross-machine normalization.

For local paths it normalizes separators and rewrites:

- standard-library paths under the sysroot to `/rustc/...`;
- other sysroot paths to `/toolchain/...`; and
- Cargo-home paths to `/cargo/...`.

If a local path is unavailable, Charon uses rustc's `MACRO`-scope path and strips a leading `/rustc/<40-hex-hash>/` component when present.

These transformations intentionally discard machine-specific prefixes. That is useful for reproducibility and human navigation, but it weakens the path as a unique source identity. `/cargo/...` does not itself record the original Cargo home; `/rustc/...` does not carry the stripped compiler hash; and an arbitrary virtual/remapped path may not identify recoverable bytes on another host.

A consumer can use such paths as lookup hints only after supplying an environment-specific mapping. Without a preserved content hash, opening a matching path does not reproduce rustc's verified-recovery guarantee.

Basis: **source** in pinned Charon `translate_meta.rs`; the integrity conclusion is **derived** from the information removed or not serialized.

### Aeneas preserves location strings, not dependency source text

Pinned Aeneas formats a `Meta.span_data` by taking the Charon file name (`Virtual`, `Local`, or `NotReal`) and appending the begin/end locations.

There is no external-source loading step in this error formatter. The diagnostic can therefore tell a user or higher-level tool that an error relates to, for example, a normalized `/cargo/...` or `/rustc/...` location while providing no source bytes.

This is not an Aeneas defect by itself. The Charon artifact it consumes does not carry the rustc content hash, and imported Charon `File.contents` is normally absent. Aeneas cannot recreate the compiler-session guarantee from information that has already been discarded.

Basis: **source** in pinned Aeneas `src/Errors.ml` plus the Charon artifact boundary above.

### Historical Anneal V1 deliberately rejected dependency paths for source rendering

V1's `DiagnosticMapper` was rooted at a `user_root`. Its `map_path` normalized a candidate path and returned it only if it stayed beneath either the user root or its canonicalized form. Its own comment says this is intended to avoid reporting source excerpts for dependencies or system files.

`render_miette` attempted to load and render source only for those accepted paths. If no diagnostic span mapped to a readable workspace file, it fell back to a textual external diagnostic containing the upstream file name and line. `render_raw` used the same workspace-only path gate.

Therefore V1 did **not** solve external-crate source recovery. Even when a dependency file happened to exist locally, the mapper intentionally declined to load it unless the path fell inside the user's workspace boundary.

That behavior is historical implementation evidence. Current Anneal's redesign is free to choose a different policy.

Basis: historical **source** in `anneal/v1/src/diagnostics.rs`.

### Recovery must bind bytes to identity before using exact ranges

A span with line/column information is only meaningful against the correct file bytes.

Rustc makes this explicit: imported metadata includes line and multibyte-character tables from the original compilation, and recovered source is accepted only after the source hash matches. This prevents a remapped dependency path from silently pointing at a different crate checkout and then being rendered with stale coordinates.

The analogous downstream rule is derived: if Anneal independently resolves `/cargo/...`, `/rustc/...`, or another external path, it should not treat the first readable file as authoritative when exact source highlighting matters. It needs content identity strong enough to establish that the recovered bytes correspond to the span metadata.

At the pinned Charon boundary, that identity is not present in ordinary `File`. A later consumer cannot recover it from path, crate name, and locations alone.

Basis: rustc **source** plus **derived** cross-boundary consequence.

### There are three materially different recovery cases

The pinned behavior yields three useful cases.

**Current-crate/local source.** Rustc has `src`, Charon can serialize `File.contents`, and a consumer can render from preserved bytes or an applicable local path.

**Imported source that rustc can recover.** Rustc has `src = None` but can load `external_src`, verify it with `src_hash`, and render it. Charon still serializes `contents = None` and does not preserve the hash.

**Imported source that rustc cannot recover.** The compiler retains filename/location metadata and the recorded hash but no source excerpt. Charon preserves a normalized filename and location, again without the hash.

These cases should not be collapsed into one `has_span` bit. The second case is especially easy to miss: source can be available to rustc's diagnostics yet absent from downstream LLBC.

Basis: pinned **source**; classification is **derived**.

### A downstream recovery protocol needs more than normalized paths

If Anneal wants exact external-crate source excerpts after Charon/Aeneas have finished, the inspected pipeline supports two principled strategies:

- capture verified source bytes while the rustc session still has both imported metadata and the hash-verifying loader; or
- carry enough source identity downstream to recover bytes later and verify them, at minimum a content hash plus the producer's file/crate identity and the coordinate convention used by the span.

This is a requirement statement, not a mandate for one storage format. The source could live in the generated corpus, a source cache, a toolchain archive, Cargo registry state, or another content-addressed store. What matters is that the displayed bytes are tied to the span's source identity rather than inferred solely from a rewritten path.

A weaker fallback remains valid: when verified source is unavailable, preserve and display the producer-local path/crate/location and state that the source excerpt could not be recovered. That is preferable to presenting an unverified local file under exact highlighting.

Basis: **derived** from the pinned rustc/Charon information boundary and current Anneal's Rust-oriented diagnostic requirement.

## Boundaries

**No fresh execution.** The report reconstructs exact control flow and serialized data from source. It does not empirically enumerate which dependency files are recoverable in a particular Cargo/rustup installation.

**The rustc reverse map is intentionally heuristic.** Its safety comes from the subsequent source-hash check. A downstream implementation that copies only the path heuristic without the hash check would have weaker semantics.

**Charon may preserve contents for non-imported files outside the user's conceptual package.** The important condition is rustc `SourceFile.src`, not a human category such as "dependency." This report does not claim every file from another logical component has `contents = None`.

**Imported source availability is environment-dependent.** Rust source components, Cargo registry/cache contents, remap prefixes, vendored source, and filesystem layout affect whether rustc can open candidate paths.

**Filename normalization is covered only as needed for recovery.** Full cross-tool relocation semantics are a separate inventory subject.

**No content hash is claimed in ordinary Charon `File`.** A different Charon artifact or future revision may add one and must be revalidated.

**No current Anneal architecture decision.** V1's workspace-only mapper is historical. Current `anneal/DESIGN.md` does not require retaining that restriction.

**No remote source download protocol.** The report does not recommend fetching crates from a registry or repository based on a display path. Such recovery would need its own package/source identity and integrity policy.

**No claim that source display is necessary for correctness.** Location-only diagnostics remain legitimate when verified bytes are unavailable. The subject here is source recovery quality, not verification soundness itself.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Rust compiler

Subject: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, used here as the source revision for Charon's `nightly-2026-05-31` toolchain.

- `compiler/rustc_span/src/source_map.rs`, blob `47c933e245d4942a81f48dc8bcd6b15ba9c39ea7`
  - imported `SourceFile` construction;
  - `ensure_source_file_source_present`;
  - heuristic reverse prefix mapping;
  - diagnostic-scope filename behavior.
- `compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`
  - `SourceFile` fields;
  - `ExternalSource` state;
  - source hashes;
  - `add_external_src` hash verification;
  - imported-source definition.
- `compiler/rustc_errors/src/emitter.rs`, blob `fa3ff21b2726ff400e378d8ef6f888156829d980`
  - diagnostic source-display gate through `ensure_source_file_source_present`.
- commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, dated 2026-05-30.

### Charon

Subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`).

- `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`
  - selects `nightly-2026-05-31`.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`
  - file registration;
  - `contents` copied from `source_file.src`;
  - filename normalization and virtual-path handling.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`
  - serialized `FileName`, `File`, `SpanData`, and `Span`;
  - absence of a source-hash field in `File`.

### Aeneas

Subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`
  - direct formatting of Charon filename and begin/end line/column locations.

### Anneal

Current authority: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`
  - Rust-oriented user surface and trust/correctness goals.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`
  - current design boundary; diagnostics should connect verification obligations to Rust without fixing this recovery mechanism.
- historical `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`
  - workspace-only `map_path`;
  - filesystem source cache;
  - source rendering and external-diagnostic fallback.

Evidence roles are exact **source**, current **design authority**, historical **implementation source**, and explicitly marked **derived** consequences. There is no fresh execution evidence.

## Revalidation

After a toolchain change, revalidate the information boundary rather than only the displayed path syntax.

1. In rustc, inspect imported `SourceFile` construction. Confirm which source identity, hash, coordinate, and crate fields survive crate metadata.
2. Recheck `ensure_source_file_source_present` and `add_external_src`. Verify whether candidate-path recovery is still hash-checked and whether the hash is computed before or after normalization.
3. Recheck rustc's diagnostic emitter to see whether source snippets still use the same external-source loader.
4. In Charon, inspect `register_file` and the serialized `File` type. Determine whether imported `external_src`, `src_hash`, stable file identity, or equivalent information is now preserved.
5. Recheck Charon's filename normalization separately. Do not infer source-byte identity from a stable-looking `/cargo`, `/rustc`, or `/toolchain` path.
6. In Aeneas, determine whether diagnostics or generated correspondence now carry richer source identity than the Charon filename/location pair.
7. In current Anneal, inspect the actual diagnostic renderer rather than historical V1. Determine whether dependency/system source is intentionally recoverable, intentionally location-only, or loaded from a verified source store.
8. If exact source excerpts matter, run a bounded specimen matrix with:
   - a path dependency;
   - a Cargo-registry dependency;
   - a standard-library/inlined span;
   - a remapped dependency source;
   - the correct source removed;
   - a wrong file deliberately placed at the expected path.
   Preserve the upstream diagnostic, Charon file record, source hashes if available, rendered excerpt, and whether the wrong-file case is rejected.

The decisive regression property is not merely "a source excerpt appeared." It is that any excerpt used for exact external-crate highlighting is demonstrably the source corresponding to the recorded span.
