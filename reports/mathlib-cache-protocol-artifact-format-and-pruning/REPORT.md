# Mathlib `lake exe cache` Protocol, `.ltar` Artifact Format, Dependency-Closure Pruning, and Upgrade Contract

## Summary

Across Mathlib `v4.30.0-rc2` (`leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, paired with Lean `v4.30.0-rc2` `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` via Aeneas `nightly-2026.06.03` `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`) and Mathlib `v4.34.1` (`leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`, paired with Lean `v4.34.1` `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib provides a repository-specific per-module `.ltar` cache (`lake exe cache`) that is distinct from Lake's generic local artifact cache:

1. **Dual hash identities (`.ltar` filename hash vs. archive header Lake `depHash`):**
   - Each covered module maps to one `<16-hex-digits>.ltar` file formatted by `UInt64.asLTar` (`Cache/Lean.lean`, byte-identical across `v4.30.0-rc2` and `v4.34.1`). That filename hash is computed by `Cache/Hashing.lean` from `rootHashGeneration` (`4` in `v4.30.0-rc2`; bumped to `5` at line 150 of `Cache/IO.lean` in `v4.34.1`), Mathlib's `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`, plus each module's relative `.lean` path, source text, and transitive import hashes.
   - Separately, `IO.readLtarHash` reads the first 12 bytes of `<hash>.ltar`—a 4-byte `LTAR`, `LTR2`, or `LTR3` magic string followed by an 8-byte little-endian integer representing the Lake `depHash` from the module's `.trace` file (which `packCache` passes as the mandatory first argument to `leantar`). `IO.needsDecompression` skips unpacking if and only if that 8-byte header `depHash` matches the installed `.lake/build/lib/lean/<Module>.trace` `depHash`.
2. **Per-module `.ltar` payload and `v4.34.1` additions (`Cache/IO.lean` `mkBuildPaths`):**
   - **7 required outputs** (packing is skipped if any is missing): `.lake/build/lib/lean/<Module>.trace` (must be first), `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, `.lake/build/ir/<Module>.c`, and `.c.hash`.
   - **Optional outputs** (packed when present): `.olean.server`, `.olean.server.hash`, `.olean.private`, `.olean.private.hash`, `.ir`, `.ir.hash`, and `.extra` in `v4.30.0-rc2`, plus **`.ir.sig` and `.ir.sig.hash`** added in `v4.34.1` (`Cache/IO.lean`, line 344).
3. **Transport vs. unpack CLI split (`get`, `get!`, `get-`) and `v4.34.1` protocol changes:**
   - Both tags preserve `get` (download missing linked `.ltar` files and decompress), `get!` (force download and decompress), and `get-` (download missing linked `.ltar` files with `decompress := false`). Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`) relies on `get-` inside its network-enabled Nix fixed-output derivation and defers `leantar` unpacking to a later offline derivation.
   - In `v4.34.1`, `Cache/Main.lean` and `Cache/Requests.lean` add `--scope`, `--unsafe`, container selection, a trust-ordered read URL chain (`Requests.lean`, line 298), and a per-process suffix on temporary `<hash>.ltar.part` download filenames (`Cache/IO.lean`, line 69) before atomic rename.
   - Separately, while `lean-4.30.0-rc2-linux_aarch64.tar.zst` bundled an incompatible `leantar` binary, `lean-4.34.1-linux_aarch64.tar.zst` (SHA-256 `fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37`) bundles a valid native AArch64 ELF `bin/leantar`.
4. **Anneal dependency-closure pruning and 11-gate upgrade checklist:**
   - `anneal/prune-lake-cache.py` retains the transitive Mathlib module closure seeded from all non-Mathlib `.lean` imports (`IMPORT_RE`) and non-Mathlib `.trace` JSON strings (`MATHLIB_TRACE_RE`), deletes unreachable Mathlib `.lean` files and matching `.lake/build/{lib/lean,ir}/<Module>.*` products, deletes duplicate root-project Mathlib build products (`prune_root_mathlib_cache`), and preserves all non-Mathlib packages in full. Lean's authoritative header import syntax (`src/Lean/Parser/Module/Syntax.lean`, lines 17–29) is byte-identical between `v4.30.0-rc2` and `v4.34.1`.
   - Upgrading Mathlib in Anneal requires satisfying the 11-gate revalidation checklist preserved in `support/mathlib-release-cache-upgrade-checklist/upgrade-checklist.json`.

## Applicability

This report covers the six subjects declared in `REPORT.json`:

1. **Mathlib `v4.30.0-rc2`:** `leanprover-community/mathlib4` revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (`input-revision: v4.30.0-rc2`).
2. **Mathlib `v4.34.1`:** `leanprover-community/mathlib4` revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (`tag: v4.34.1`).
3. **Lean 4 `v4.30.0-rc2` (`Lean.Parser.Module`):** `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
4. **Lean 4 `v4.34.1`:** `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`tag: v4.34.1`).
5. **Aeneas `nightly-2026.06.03`:** `AeneasVerif/aeneas` revision `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`backends/lean/{lakefile.lean,lake-manifest.json,lean-toolchain}`).
6. **Anneal Mathlib cache consumption and pruning pipeline:** `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, `anneal/prune-lake-cache.py`, `anneal/tests/test_prune_lake_cache.py`).

## Findings

### 1. Mathlib `.ltar` Artifact Format, Dual Hash Identities, and Path Redirection (`v4.30.0-rc2` vs. `v4.34.1`)

#### Per-Module Archive Naming vs. Header Lake `depHash`
In both `5450b53e5ddc` (`v4.30.0-rc2`) and `d13f23b723b8` (`v4.34.1`), `Cache/Lean.lean` (blob `0934e22f2dc396411106b008016fba4569cf741d` at both tags, lines 27–29) defines `UInt64.asLTar`, formatting each module's 64-bit Mathlib cache hash as `<16-hex-digits>.ltar`.

- **Custom module filename hash (`Cache/Hashing.lean`):** `Hashing.getRootHash` hashes `rootHashGeneration` (`Cache/IO.lean`: `4` at line 110 in `v4.30.0-rc2`; bumped to `5` at line 150 in `v4.34.1`) together with the contents of Mathlib's `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`. (Although a source comment above `getRootHash` mentions `Lean.githash`, the executable code hashes `rootHashGeneration` and the three project files.) `Hashing.getHash` mixes that root hash with each module's relative `.lean` path, source text, and covered transitive import hashes. Because `rootHashGeneration` changed from `4` to `5` in `v4.34.1`, `v4.30.0-rc2` and `v4.34.1` `.ltar` filenames are disjoint by construction.
- **12-byte LTAR header `depHash` (`Cache/IO.lean`):** `IO.readLtarHash` (lines 361–424 in `v4.30.0-rc2`; near line 426 in `v4.34.1`) reads 12 bytes from `<mathlibHash>.ltar`: a 4-byte magic (`LTAR`, `LTR2`, or `LTR3`) followed by an 8-byte little-endian integer containing the module's Lake `depHash`. `IO.needsDecompression` compares that 8-byte header value against `depHash` in the installed `.lake/build/lib/lean/<Module>.trace` file (`readTraceHash`) and skips decompression only when they are equal.
- **Provenance comment:** `Cache/Main.lean` passes `git rev-parse HEAD` to `packCache`, which invokes `leantar` with `-c git=mathlib4@<commit>` (inspectable via `lookup` / `leantar -k`).

#### Required and Optional Per-Module Build Products (`mkBuildPaths`)

| Build Path Category | `v4.30.0-rc2` (`5450b53e5ddc`, `Cache/IO.lean` lines 268–307) | `v4.34.1` (`d13f23b723b8`, `Cache/IO.lean` lines 316–351) | Packing Rule (`packCache`) |
| --- | --- | --- | --- |
| **Required (7 files)** | 1. `.lake/build/lib/lean/<Module>.trace` (**must be first**)<br>2. `.lake/build/lib/lean/<Module>.olean`<br>3. `.lake/build/lib/lean/<Module>.olean.hash`<br>4. `.lake/build/lib/lean/<Module>.ilean`<br>5. `.lake/build/lib/lean/<Module>.ilean.hash`<br>6. `.lake/build/ir/<Module>.c`<br>7. `.lake/build/ir/<Module>.c.hash` | Identical 7 required files (with `.trace` still required first). | `allExist` checks all required files; if any is absent, `packCache` skips the module. |
| **Optional (7 in `v4.30.0-rc2`; 9 in `v4.34.1`)** | 1. `.olean.server` & 2. `.olean.server.hash`<br>3. `.olean.private` & 4. `.olean.private.hash`<br>5. `.ir` & 6. `.ir.hash` (under `lib/lean/`)<br>7. `.extra` (under `lib/lean/`) | Retains all 7 optional files from `v4.30.0-rc2` and adds:<br>8. **`.ir.sig`** (line 344)<br>9. **`.ir.sig.hash`** (line 344) | Filtered by file existence; present optional files are packed, absent ones are omitted. |

#### Package Directory Paths and Downstream `base` Redirection
`mkBuildPaths` constructs paths under each owning package's `.lake/build` directory (assuming default `srcDir` layout). Because dependency package paths (`e.g. .lake/packages/...`) are embedded inside `.ltar` member entries, `unpackCache` (`Cache/IO.lean`, lines 419–457 in `v4.30.0-rc2`) passes `leantar` a JSON object with `"base"` redirected to the actual Mathlib dependency directory when Mathlib is consumed as a dependency rather than as the root workspace. Other cached dependency packages are unpacked without that Mathlib-specific `"base"` override. Furthermore, `Cache/IO.lean` warns that modifying generated `.ltar` contents does not automatically alter the filename hash, so any archive-layout change must be paired with a `rootHashGeneration` bump.

Basis: **source** + **documentation** (`support/mathlib-cache-artifact-format/source-map.json`, `support/mathlib-430rc2-to-4341-cache-source-review/official-source-observation.json`, and preserved snapshots under `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/mathlib/`).

### 2. `lake exe cache` Retrieval Protocol (`get`, `get!`, `get-`) Across `v4.30.0-rc2` and `v4.34.1`

In both `v4.30.0-rc2` and `v4.34.1` (`Cache/Main.lean` and `Cache/Requests.lean`, mapped in `support/mathlib-lake-exe-cache-protocol/protocol-map.json`), `lake exe cache` separates object transport from build-tree extraction:

- `get`: checks downstream `lean-toolchain` and shared `lake-manifest.json` compatibility against Mathlib (`Requests.getFiles`), downloads missing `<hash>.ltar` files into `MATHLIB_CACHE_DIR` (defaulting to `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib`), and calls `unpackCache` (`leantar`).
- `get!`: forces both download and decompression even when local archives or matching traces exist.
- `get-`: runs the compatibility checks and downloads missing `<hash>.ltar` files into `MATHLIB_CACHE_DIR` with `decompress := false` (`Cache/Main.lean`, line 289 in `v4.34.1`), terminating without invoking `unpackCache` or mutating `.lake/build`.

In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, lines 325–350), Anneal's fixed-output derivation runs `lake exe cache get-` while network access is enabled, copies the downloaded `.ltar` cache and dependency checkouts into the Nix store, and runs `leantar` decompression in a subsequent offline derivation.

| Protocol Dimension | `v4.30.0-rc2` (`5450b53e5ddc`) | `v4.34.1` (`d13f23b723b8`) |
| --- | --- | --- |
| `rootHashGeneration` (`Cache/IO.lean`) | `4` (line 110) | `5` (line 150) |
| CLI flags & container selection (`Cache/Main.lean`) | Repository/URL selection via Azure/Cloudflare defaults or `MATHLIB_CACHE_GET_URL`. | Adds `--scope`, `--unsafe`, and cache-container selection while preserving `get`, `get!`, and `get-` (line 289). |
| Read endpoint resolution (`Cache/Requests.lean`) | Single selected read endpoint (`mkFileURL` under `<endpoint>/f/<filename>`). | Defines a trust-ordered read URL chain (line 298) and retains downstream toolchain/manifest checks (lines 965–1046). |
| Temporary download `.part` files (`Cache/IO.lean` & `Requests.lean`) | Writes `<cache>/<hash>.ltar.part` and renames to `<hash>.ltar` (concurrent processes sharing `MATHLIB_CACHE_DIR` could collide on `.part`). | Adds a per-process suffix to temporary `<hash>.ltar.part` filenames (`Cache/IO.lean`, line 69) before atomic rename. |
| Bundled Linux AArch64 `bin/leantar` | `lean-4.30.0-rc2-linux_aarch64.tar.zst` bundled an x86-64 / incompatible `leantar` binary (requiring Anneal host workaround). | `lean-4.34.1-linux_aarch64.tar.zst` (SHA-256 `fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37`) bundles a valid native AArch64 ELF `bin/leantar`. |

Basis: **source** (`support/mathlib-lake-exe-cache-protocol/protocol-map.json`, `support/mathlib-430rc2-to-4341-cache-source-review/official-source-observation.json`, and `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/mathlib/new/`).

### 3. Dependency-Closure Pruning (`anneal/prune-lake-cache.py`) and Lean Import Grammar

In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` invokes `anneal/prune-lake-cache.py` (blob `b0eb8eaa5ecefad9766a155994968712826ed996`; unit-tested in `anneal/tests/test_prune_lake_cache.py`, blob `596603415cf21be8b1e7b585e67bd37631b9a522`; algorithm formalized in `support/mathlib-dependency-closure-pruning/closure-algorithm.json`) after offline `lake --old build` and package-config priming complete:

1. **Seed collection and graph reachability (`collect_mathlib_closure`):**
   - Scans all `.lean` files under `project_root` and `packages_root` outside `mathlib` using `IMPORT_RE` to extract direct `Mathlib.*` imports into the seed set.
   - Scans all non-Mathlib `.trace` JSON files using `MATHLIB_TRACE_RE` (matching `Mathlib.<ASCII-ident>` tokens anywhere in serialized JSON captions, logs, or inputs) as a conservative over-approximating seed supplement.
   - Scans `mathlib` `.lean` files to map each Mathlib module to its direct `Mathlib.*` imports and performs a depth-first worklist traversal from the seeds.
2. **Module and artifact deletion (`prune_package`, `remove_build_artifacts`, `prune_root_mathlib_cache`):**
   - Non-Mathlib packages (`pkg_dir.name != "mathlib"`, such as Aeneas, Batteries, Aesop, Qq) keep 100% of their `.lean` modules and build products.
   - For `mathlib`, unreachable `.lean` source files are deleted, and `remove_build_artifacts` deletes matching `<Module>.*` files under `.lake/build/lib/lean` and `.lake/build/ir`.
   - `prune_root_mathlib_cache` deletes `project_root/.lake/build/lib/lean/Mathlib` and root-level `Mathlib.*` build products so only the vendored `mathlib/.lake/build` copy remains.
3. **Comparison with Lean's authoritative header import syntax (`v4.30.0-rc2` and `v4.34.1`):**
   - In `leanprover/lean4` at both `3dc1a088b6d2` (`v4.30.0-rc2`) and `5045d0056413` (`v4.34.1`), `src/Lean/Parser/Module/Syntax.lean` (blob `1fd6c0af6d7e204bbfd1c0e97fa80c818bf6f97c`, byte-identical across both tags, lines 17–29) defines `header` as optional `module`, optional `prelude`, and repeated `import` directives (`optional "public"`, `optional "meta"`, `"import"`, `optional "all"`, and `ident`). `src/Lean/Parser/Module.lean` (lines 84–112 in both tags; `v4.34.1` adds `withPosition` only at line 127 outside header import extraction) elaborates header imports before commands.
   - Because `IMPORT_RE` is a line-oriented regex rather than `Lean.Parser.Module`, unusual multi-line comments between `import` tokens or non-ASCII module identifiers in `.trace` files sit outside the regex grammar and must be covered by post-prune consumer validation.

Basis: **source** (`anneal/prune-lake-cache.py`, `anneal/tests/test_prune_lake_cache.py`, `support/mathlib-dependency-closure-pruning/closure-algorithm.json`, and `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/lean/`).

### 4. Eleven-Gate Mathlib Release and Cache Upgrade Checklist

Upgrading Anneal's Mathlib pin (for example, from `v4.30.0-rc2` `5450b53e5ddc` to `v4.34.1` `d13f23b723b8` once paired with a compatible Aeneas release) requires revalidating the 11 gates defined in `support/mathlib-release-cache-upgrade-checklist/upgrade-checklist.json`:

| Gate | Upgrade Requirement | `v4.30.0-rc2` → `v4.34.1` Source Status |
| --- | --- | --- |
| **1. Dependency closure identity** | Record `Anneal → Aeneas → Lean toolchain → lake-manifest.json → Mathlib commit → transitive package commits`. | Mathlib `v4.34.1` (`d13f23b723b8`) updates `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`; requires matching Aeneas manifest update. |
| **2. Toolchain alignment** | Verify Mathlib `lean-toolchain`, Aeneas `lean-toolchain`, and Anneal packaged Lean commit match. | Mathlib `d13f23b723b8` `lean-toolchain` selects `leanprover/lean4:v4.34.1` (`5045d0056413`). |
| **3. `lake exe cache` CLI boundary** | Verify `get-` remains transport-only (`decompress := false`) without mutating `.lake/build`. | Preserved at `Cache/Main.lean` line 289 in `v4.34.1`; adds `--scope`, `--unsafe`, trust-ordered URLs, and per-process `.part` suffixes. |
| **4. Cache-key contract** | Diff `Cache/Hashing.lean` and `rootHashGeneration`; keep filename hash distinct from header `depHash`. | `rootHashGeneration` bumped from `4` to `5` (`Cache/IO.lean`, line 150); header 12-byte `depHash` check unchanged. |
| **5. Payload & `leantar` format** | Diff `mkBuildPaths` and `packCache`; verify `leantar` binary compatibility. | `mkBuildPaths` adds optional `.ir.sig` and `.ir.sig.hash` (line 344); `v4.34.1` fixes native Linux AArch64 `bin/leantar`. |
| **6. Native & platform artifacts** | Validate per-host `.olean`, `.ilean`, `.c`, and native libraries across supported architectures. | Requires per-host execution on Linux/macOS x86_64 and AArch64. |
| **7. Nix fixed-output hashes** | Regenerate and diff `mathlib-cache-download` fixed-output derivation hashes per host. | Required on upgrade because `rootHashGeneration = 5` and source commits change all `.ltar` objects. |
| **8. Relocation, read-only & offline** | Verify unpacked dependency tree works read-only and offline after relocation. | Benefits from Lake `v4.30.0`+ `.lake/config/<pkgIdx>` workspace hoisting (see `lake-configuration-elaboration-and-workspace-ownership`). |
| **9. Dependency-closure pruning** | Re-run `prune-lake-cache.py` and verify retained closure against Lean's header parser. | `Lean/Parser/Module/Syntax.lean` unchanged in `v4.34.1`; update `remove_build_artifacts` if new output directories appear. |
| **10. Clean vs. cache-seeded equivalence** | Compare clean vs. cache-seeded `.olean`, `.ilean`, `.c`, `.ir.sig`, `setup-file`, and theorem checking. | Must be executed on representative Aeneas/Anneal modules at the target tuple. |
| **11. End-to-end lifecycle gate** | Execute full `get-` → unpack → rewrite → prune → relocate → read-only/offline consumer verification. | Final integration gate before updating Anneal's production pins. |

Basis: **source** + **derived** (`support/mathlib-release-cache-upgrade-checklist/upgrade-checklist.json`, `support/mathlib-release-cache-upgrade-checklist/source-map.json`, `support/mathlib-430rc2-to-4341-cache-source-review/matrix.json`).

## Boundaries

- **No fresh `lake exe cache` network download or `v4.34.1` Mathlib build execution (`not examined`):** The `v4.30.0-rc2` and `v4.34.1` Mathlib findings in this package are established from exact upstream source snapshots and offline verification scripts (`support/mathlib-430rc2-to-4341-cache-source-review/official-source-observation.json`). Live network downloads from Mathlib's Azure/Cloudflare endpoints and full Mathlib archive extraction at `v4.34.1` were **not examined**.
- **Binary `leantar` payload framing beyond byte 12 (`not examined` here):** Mathlib's `Cache/IO.lean` directly reads only the first 12 bytes (`LTAR`/`LTR2`/`LTR3` magic + 8-byte little-endian `depHash`). Internal `leantar` frame compression and path record encoding are covered in the dedicated `lean-olean-ilean-and-leantar-determinism` package.
- **Regex import scanner vs. full Lean parser (`known not to apply` to arbitrary comment-interleaved headers):** `anneal/prune-lake-cache.py` uses line-oriented `IMPORT_RE` and ASCII `MATHLIB_TRACE_RE` rather than invoking `Lean.Parser.Module`; valid Lean headers with block comments splitting `import` and `Mathlib.*` are not parsed by `IMPORT_RE`.
- **Cross-platform `.ltar` interchangeability (`unsupported` without per-platform verification):** Mathlib's per-module filename hash does not mix `System.Platform.target`, while Lake traces and native build products can be platform-dependent; `.ltar` archives must be validated per host platform.

## Evidence

### Pinned Upstream Revisions and Source Blobs
- **Mathlib `v4.30.0-rc2` (`leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`):**
  - `Cache/Lean.lean` (blob `0934e22f2dc396411106b008016fba4569cf741d`, lines 27–29)
  - `Cache/IO.lean` (blob `872ffe7ce8c608f6769e3e3cc5bb5dac8f9b001a`, lines 110–113, 268–484)
  - `Cache/Hashing.lean` (blob `418e884d1262cd8655ceddccf0e3c5894f742e46`, lines 88–165)
  - `Cache/Requests.lean` (blob `2f59d1ec95d8f04574c74b869afd4473acf60406`, lines 253–341, 501–704)
  - `Cache/Main.lean` (blob `12f69c07522f61db89318bc8331b5eb395b45377`, lines 119–125)
  - `Cache/README.md` (blob `2c25714653f41c9c378849abb8d59f92145fd9b3`)
  - `lakefile.lean` (blob `2615d72c0aa5e414234eac5f7ade10f4f3890916`), `lake-manifest.json` (blob `86b358344ea45a46d99dc19ac861011583e6d6e5`), `lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`)
- **Mathlib `v4.34.1` (`leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`):**
  - Preserved in `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/mathlib/new/` (`Cache/Lean.lean`, `Cache/IO.lean`, `Cache/Hashing.lean`, `Cache/Requests.lean`, `Cache/Main.lean`, `Cache/README.md`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`), with exact blob SHA-1s, SHA-256 digests, and line locators recorded in `support/mathlib-430rc2-to-4341-cache-source-review/official-source-observation.json`.
- **Lean 4 `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `src/Lean/Parser/Module/Syntax.lean` (blob `1fd6c0af6d7e204bbfd1c0e97fa80c818bf6f97c` at both tags, lines 17–29) and `src/Lean/Parser/Module.lean` (blob `024a5c10df494caccca4bb908e7bcc32df2530ca` at `v4.30.0-rc2`, lines 84–112), preserved under `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/lean/{old,new}/`.
- **Aeneas (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`):**
  - `backends/lean/lakefile.lean` (blob `c32062866e2f88d2eb768b904745e7104edddb0d`), `backends/lean/lake-manifest.json` (blob `1a5af703163d8b39f4311aafe22ae171788179ee`), `backends/lean/lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`).
- **Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`):**
  - `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, lines 325–350), `anneal/prune-lake-cache.py` (blob `b0eb8eaa5ecefad9766a155994968712826ed996`), `anneal/tests/test_prune_lake_cache.py` (blob `596603415cf21be8b1e7b585e67bd37631b9a522`).

### Preserved Package Support Material
- `support/mathlib-cache-artifact-format/source-map.json`
- `support/mathlib-lake-exe-cache-protocol/protocol-map.json`
- `support/mathlib-dependency-closure-pruning/closure-algorithm.json`
- `support/mathlib-release-cache-upgrade-checklist/source-map.json` and `support/mathlib-release-cache-upgrade-checklist/upgrade-checklist.json`
- `support/mathlib-430rc2-to-4341-cache-source-review/official-source-observation.json`, `support/mathlib-430rc2-to-4341-cache-source-review/matrix.json`, `support/mathlib-430rc2-to-4341-cache-source-review/frozen-cohort.csv`, `support/mathlib-430rc2-to-4341-cache-source-review/baseline-report-paths.txt`, `support/mathlib-430rc2-to-4341-cache-source-review/lean-tag-refs.txt`, `support/mathlib-430rc2-to-4341-cache-source-review/mathlib-tag-refs.txt`, `support/mathlib-430rc2-to-4341-cache-source-review/version-inventory-ebcdcad-581.csv`, `support/mathlib-430rc2-to-4341-cache-source-review/check_matrix.py`, and old/new source snapshots under `support/mathlib-430rc2-to-4341-cache-source-review/snapshots/`

## Revalidation

1. **Offline snapshot and source-diff verification:**
   - Diff the preserved `v4.30.0-rc2` (`old`) and `v4.34.1` (`new`) Mathlib cache and Lean parser snapshots directly:
     ```bash
     diff -u support/mathlib-430rc2-to-4341-cache-source-review/snapshots/mathlib/old/Cache/IO.lean \
             support/mathlib-430rc2-to-4341-cache-source-review/snapshots/mathlib/new/Cache/IO.lean
     diff -u support/mathlib-430rc2-to-4341-cache-source-review/snapshots/lean/old/src/Lean/Parser/Module/Syntax.lean \
             support/mathlib-430rc2-to-4341-cache-source-review/snapshots/lean/new/src/Lean/Parser/Module/Syntax.lean
     ```
2. **Targeted source revalidation on a newer Mathlib/Lean pair:**
   - Check `Cache/Lean.lean` (`UInt64.asLTar`), `Cache/Hashing.lean` (`getRootHash`, `getHash`), `Cache/IO.lean` (`rootHashGeneration`, `mkBuildPaths`, `packCache`, `readLtarHash`, `needsDecompression`, `unpackCache`), `Cache/Main.lean` (`get-` dispatch), and `Cache/Requests.lean` (URL resolution and compatibility checks).
3. **Minimal execution and pruning probe:**
   - Run `lake exe cache get-` on a single covered Mathlib module into an isolated `MATHLIB_CACHE_DIR`, inspect the first 12 bytes of the downloaded `<hash>.ltar` file to verify the `LTAR`/`LTR2`/`LTR3` magic and 8-byte little-endian `depHash`, unpack with `leantar`, and verify that the unpacked `.trace` `depHash` matches the header value.
   - Run `anneal/tests/test_prune_lake_cache.py` and compare `collect_mathlib_closure` against Lean's header parser on the target dependency tree before and after pruning.
