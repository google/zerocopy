# Rust module, file, and source identity at nightly-2026-05-31

## Summary

At the Rust compiler revision used by Anneal's pinned Charon toolchain, a Rust module's logical identity and the source file that supplied its text are distinct facts. An inline `mod m { ... }` has a logical module but no separate module file. An out-of-line `mod m;` loads exactly one source file selected by Rust's module-path rules or by a literal `#[path = "..."]` override. The resulting file is registered in rustc's `SourceMap` under a `FileName`; spans refer into that source-file identity, while Rust item identity is assigned separately.

The default module search chooses between `m.rs` and `m/mod.rs`, and reports an error if both exist. Nested lookup depends on whether the containing module came from a mod-rs-style file, a non-mod-rs file, an inline module, or an explicit `#[path]` file. `#[path]` files are treated as mod-rs-style owners for the purpose of finding their children. A `cfg_attr` can synthesize `path`, so configuration can select a different physical source file for the same logical module name.

rustc does not canonicalize module paths through the filesystem before the inspected source-map identity path. The module loader joins and tests path values, the default real-file loader opens the supplied path, and `SourceMap::load_file` constructs a `RealFileName` from that path and the compiler's path-remapping configuration. `StableSourceFileId` is then a hash of the resulting `FileName`, not a filesystem inode or content hash. Consequently, two lexical paths that reach the same underlying file through symlinks are not intentionally coalesced by this identity mechanism. That conclusion is from source inspection; no fresh symlink experiment was run.

Path remapping is also part of source identity. `RealFileName` keeps a local path when available and a maybe-remapped representation for selected scopes. Its hash deliberately uses the remapped representation when a filename was fully remapped so remapped sysroot paths can remain stable across local installations. Consumers must therefore distinguish local filesystem path, remapped diagnostic/embedded path, logical module path, and stable source-file ID.

No fresh rustc, Cargo, Charon, symlink, or generated-source experiment was performed. The report establishes the exact pinned module-resolution and source-map implementation plus the normative module rules. It does not claim filesystem aliases are interchangeable across platforms or filesystems.

## Applicability

Rust compiler subject:

- repository: `rust-lang/rust`
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`

Rust Reference subject:

- repository: `rust-lang/reference`
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`
- relationship: the `src/doc/reference` submodule recorded by the compiler revision above.

This report covers inline and out-of-line modules; default `foo.rs` / `foo/mod.rs` search; `#[path]` and cfg-dependent path selection; nested module lookup; source-file registration and stable source-file identity; path remapping; the implementation-visible consequence of symlink aliases; and the boundary between generated syntax and real source files.

The report does not attempt to define a cross-version stable rustc source-file-ID API. These structures are compiler internals at the pinned revision.

## Findings

### Logical module identity does not imply one source-file shape

The Rust Reference defines modules as namespace-forming items. A module can be inline, with its body between braces, or out-of-line, with a declaration such as `mod util;` whose contents are loaded from another file.

An inline module therefore has a Rust module path without introducing a separate module source file. Its items retain spans into the file containing the inline module, modulo macro expansion.

An out-of-line module adds a source-file-selection step before the module body is available to later compiler phases.

Basis: **normative**.

### Default out-of-line lookup selects one of two conventional paths

For `mod m;` without `#[path]`, the Reference permits the module contents in either `m.rs` or `m/mod.rs`.

The pinned rustc implementation constructs both candidate paths and asks the source map's file loader whether each exists. Exactly one existing candidate succeeds. Neither candidate produces a file-not-found error; both candidates existing produce a multiple-candidates error.

This means default module resolution is not "first file wins." The filesystem state is part of the compilation input, and an ambiguous pair is rejected.

Basis: **normative** + **source**.

### Nested lookup depends on the containing module's file form

The Reference's path examples and rustc's `DirOwnership` state encode the historical distinction between mod-rs-style and non-mod-rs module files.

If a module body came from a non-mod-rs file such as `foo.rs`, a child `mod bar;` is searched under `foo/bar.rs` or `foo/bar/mod.rs`. A module body from `foo/mod.rs` searches children in the same `foo/` directory.

Inline modules extend the directory calculation with their logical components according to the Reference's documented rules.

The source pathname for a child module is therefore a function of both the child declaration and how its ancestors were sourced.

Basis: **normative** + **source**.

### A literal `#[path]` overrides the default search

The `path` attribute lets a module declaration name another source file. In the pinned rustc source, `mod_file_path_from_attr` finds the first `path` attribute, requires a string literal, and joins it with the current module directory.

Macro expressions such as `#[path = concat!(...)]` are explicitly rejected by this implementation. The source comment explains that supporting such a value would require deferring module loading until the attribute macro expression was expanded.

For child-module lookup, rustc treats a file loaded through `#[path]` as though it were a mod-rs-style file: its children are siblings relative to that path's directory rather than descendants implied by a non-mod-rs filename.

Basis: **source** + **normative**.

### `cfg_attr(path = ...)` can select different files for the same module name

The Reference explicitly demonstrates `cfg_attr` choosing `linux.rs` or `windows.rs` as the backing file for one logical module declaration.

The pinned expansion machinery processes configuration attributes before it asks the module loader for the file path. The module loader then consumes the processed attributes when resolving the file.

Thus `crate::os` can denote code loaded from different files in different configurations while retaining the same logical module path.

Basis: **normative** + **source**.

### rustc parses the selected path as the external module body

`parse_external_mod` computes the module file path, rejects a path that would create a circular inclusion through the current module-file stack, then creates a parser from that path and parses the file as a module.

Any inner attributes parsed from the external file are appended to the module's attributes. The expansion path notes that if loading the file introduces inner attributes, rustc reconfigures and recollects the module so those attributes affect subsequent resolution and expansion.

The selected source file is therefore an active compiler input, not merely diagnostic metadata attached after parsing.

Basis: **source**.

### The module cycle check is path-based at this stage

The external-module loader's cycle check compares the selected `PathBuf` against the module's current file-path stack.

The inspected path does not pass through filesystem canonicalization before this comparison. A filesystem alias such as a symlink can therefore differ from an earlier path value even if both ultimately reach the same underlying file. Other parsing or recursion limits can still stop such input; this report makes no broader claim from that fact.

The durable point is narrower: the module loader is reasoning over path values, not filesystem object identity.

Basis: **source**.

### SourceMap records a real source file from the path it is asked to load

The default `SourceMap::load_file` path reads the file through the configured `FileLoader`, constructs a `FileName::Real` with `FilePathMapping::to_real_filename`, and registers the text as a `SourceFile`.

The default real-file loader's `file_exists` is ordinary `Path::exists`, and its text read uses `File::open(path)`. The inspected code does not call `fs::canonicalize` on the source path before source-map registration.

This preserves the compiler-supplied path relationship rather than deliberately replacing it with the filesystem's canonical target path.

Basis: **source**.

### RealFileName keeps local and remapped path views

`FilePathMapping::to_real_filename` constructs a `RealFileName` with a local path plus local working directory, a maybe-remapped path plus remapped working directory, and the scopes in which remapping applies.

Relative local paths also receive an embeddable form joined to the working directory. Prefix remapping is applied according to rustc's `--remap-path-prefix` configuration and scope.

Consumers can request the path appropriate for a particular remapping scope or request a local filesystem path when that information exists.

A diagnostic path and a local read path can therefore intentionally differ without referring to different parsed source text.

Basis: **source**.

### StableSourceFileId is filename-derived, not content- or inode-derived

At the pinned revision, `StableSourceFileId::from_filename_in_current_crate` hashes the `FileName` together with the current-crate marker. The `SourceFile` separately computes a source-content hash, but that hash is not the input to the stable source-file ID.

`RealFileName`'s hash deliberately includes the local representation unless the filename was fully remapped, plus the maybe-remapped representation and remapping scopes. The source comment says fully remapped paths should remain stable even if corresponding local sysroot paths change.

Source-file identity is therefore path-identity-oriented. Equal content does not by itself merge source files, and a path-remapping policy can intentionally alter which pathname components participate in stable identity.

Basis: **source**.

### Symlink aliases are not deliberately coalesced by source-file identity

Combining the module loader and source-map paths yields a concrete implementation fact at this revision: module resolution constructs and joins `PathBuf` values; the real loader opens those paths without canonicalizing them; `to_real_filename` preserves the supplied local path and applies prefix mapping, not symlink resolution; and `StableSourceFileId` hashes the resulting `FileName`.

Therefore distinct lexical module paths that the filesystem resolves to one target are not intentionally normalized to a single canonical filesystem path before stable source-file identity is formed.

This does not promise that every pair yields distinct 128-bit IDs: hashes can theoretically collide, and platform path semantics can equate some spellings. It establishes the identity rule implemented by this path.

Basis: **derived** from **source**. No fresh symlink execution.

### FileName includes virtual sources as well as real files

The rustc `FileName` enum distinguishes `Real` source files from virtual compiler inputs such as macro expansion, proc-macro source code, command-line cfg specifications, anonymous input, inline assembly, and custom parser sources.

A span naming `<macro expansion>` or another virtual source therefore does not necessarily correspond to a readable filesystem path.

This matters when a downstream tool tries to map compiler spans back to user files. "Has a source-file identity" and "has a local file path" are separate properties.

Basis: **source**.

### Generated source enters module/file identity only through how rustc consumes it

A build script can write arbitrary Rust files, but merely writing a file does not add a Rust module. The crate must consume it through a Rust mechanism such as `include!`, an explicit/generated module path, or another macro expansion route.

When rustc actually loads generated text as a real file, SourceMap can preserve a real filename for it. When generated Rust arrives as proc-macro output, the relevant syntax instead carries macro spans and may be associated with virtual macro-source identities.

The existing generated-Rust-visibility report preserves the build-script/proc-macro boundary in more detail. The module/file conclusion here is that generation mechanism affects source identity independently of logical item identity.

Basis: **source** + **derived**.

### Source-file identity is not Rust item identity

A source file can define many items and modules; an inline module shares a file with its parent; a macro can generate multiple items; and one logical module can be backed by different files across configurations.

Conversely, rustc item/definition identity and downstream Charon item identity are semantic compiler identities, not filesystem paths.

A robust source correspondence record therefore needs both semantic item identity and source span/file identity with its configuration/path provenance. Using only a filename as the identity of a Rust declaration is insufficient.

Basis: **derived** from **source** and the corpus's Charon item-identity report.

## Boundaries

- No fresh rustc, Cargo, Charon, filesystem, symlink, `--remap-path-prefix`, proc-macro, or generated-file execution was performed.
- The symlink conclusion is an implementation-source conclusion for this pin: the inspected path does not canonicalize module/source paths before `RealFileName` and `StableSourceFileId` construction. Filesystem-specific alias behavior was not experimentally tested.
- This report does not claim stable source-file IDs are collision-free identifiers. They are 128-bit hashes.
- It does not promise the rustc-internal `StableSourceFileId` representation as a stable external API.
- It does not claim `RealFileName::path` always returns a local path; remapping scope determines which representation is appropriate.
- It does not inventory every way macros can synthesize module declarations or source spans.
- It does not fully describe `include!`, proc-macro span hygiene, or generated-file provenance; those are preserved in existing generated-source and source-correspondence reports.
- It does not cover Cargo package-root selection or unit identity except where needed to explain generated/configured source.
- It does not choose an Anneal source-identity or diagnostics architecture.

## Evidence

**Normative — Rust Reference.** Repository `rust-lang/reference`, revision `ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/items/modules.md`, blob `3cc015025bab29ec026d2a56538d97051eb6a660`: inline/out-of-line modules, default module filenames, nested lookup, and `path`.
- `src/conditional-compilation.md`, blob `c0351610d6d0c495233eb382e97cdb6c5ff3864d`: `cfg_attr` and its conditional `path` example.

**Source — rustc.** Repository `rust-lang/rust`, revision `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_expand/src/module.rs`, blob `f64ff982e5238ed567446081830769d47b1898b9`: `parse_external_mod`, `mod_file_path`, `mod_file_path_from_attr`, `default_submod_path`, and module path-stack cycle checking.
- `compiler/rustc_expand/src/expand.rs`, blob `741c34e0304af71c8fbbad394d18809f9126b0df`: module attribute processing and external-module loading during expansion.
- `compiler/rustc_span/src/source_map.rs`, blob `47c933e245d4942a81f48dc8bcd6b15ba9c39ea7`: `SourceMap::load_file`, default `RealFileLoader`, `FilePathMapping`, and local/remapped filename construction.
- `compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`: `RealFileName`, `FileName`, `StableSourceFileId`, `SourceFile::new`, and filename-based stable-ID hashing.

**Related corpus evidence.**

- `generated-rust-visibility-nightly-2026-05-31`: build-script files and proc-macro generated syntax.
- `rust-conditional-compilation-nightly-2026-05-31`: cfg-driven item and module-file selection. This report is prepared in the same linear candidate chain and must be published first.
- `charon-item-identity-spans-comments-nightly-2026-06-03`: downstream semantic item identity and source spans.
- `end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2`: cross-layer diagnostic/source correspondence.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Rust pin, resolve the exact compiler and Rust Reference revisions; re-read the module filename and `path` rules; inspect external-module default candidates, `#[path]`, child-directory ownership, and cycle detection; inspect `SourceMap::load_file`, `FilePathMapping::to_real_filename`, `RealFileName` hashing, and `StableSourceFileId`; search specifically for filesystem canonicalization; recheck remapping scopes; and diff virtual `FileName` variants.

On an execution-capable surface, create one crate containing a default `mod a;`, mod-rs and non-mod-rs nested modules, a literal `#[path]` module, a cfg-selected `#[path]` pair, two symlink paths to one source file, a build-generated real Rust file, one proc macro that emits an item, and a `--remap-path-prefix` control.

Preserve rustc dep-info/source-map observations if available, diagnostics, HIR item spans, MIR spans, Charon source spans, exact argv, filesystem layout including symlink targets, and hashes.

The decisive symlink observation is whether the two lexical aliases receive distinct `FileName` / stable source-file identities and downstream span filenames under the exact platform and remapping configuration. The decisive remap observation is which local/remapped path appears in diagnostics and downstream serialization.

These experiments establish concrete behavior for the tested platform and revision. They do not turn filesystem paths into a stable semantic identity for Rust items.
