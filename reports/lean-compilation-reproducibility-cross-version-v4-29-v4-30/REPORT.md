# Lean compilation determinism and version diff

## Summary

Two small-project builds per Lean version produced byte-identical repeated clean artifacts and repeated fetched-cache artifacts. The cache-fetched path omitted project-local `.olean` files, so batch imports failed until local artifacts were materialized. The LSP comparison found a version-specific advertised RPC capability.

## Applicability

Two official local macOS arm64 Lean/Lake toolchains, 4.29.0 and 4.30.0-rc2, one two-module synthetic project, no Mathlib or external dependencies. Related corpus reports: [lean-compilation-determinism-v4-30-0-rc2](../lean-compilation-determinism-v4-30-0-rc2/REPORT.md), [adjacent-version-non-generalization-examples-2026-09-27](../adjacent-version-non-generalization-examples-2026-09-27/REPORT.md).

## Findings


**Scope.** This is a Nix-independent, two-version experiment with one small synthetic Lean/Lake project. It follows [Anneal's principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md) and [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md): repeatable Lean artifacts and a clean editor query are interface evidence, not proof of Rust/model correspondence, obligation coverage, UB freedom, or Anneal verification success. The historical `v1/` prototype is not design authority. No product or test source was changed.

### Bounds, identities, and retained evidence

The work stayed in [scratch](support/lean-compilation-diff), plus this report. Before the first run, disk had 83,472,437,248 free bytes and `memory_pressure -Q` reported 8 GiB physical memory and 45% system-wide free. Before the 4.29 run, memory free was 46%. The final scratch file payload, including both runs, was under 1 MiB, against a 1 GiB cap. One server ran at a time; every child was bounded to 30 seconds, and all completed within the bound. No Mathlib tree, Nix command, or credentials were used. `LAKE_JOBS=1` was set, but Lake's “4 jobs” output counts tasks and does not demonstrate a global one-worker limit.

The official [Lean 4.29.0 release](https://github.com/leanprover/lean4/releases/tag/v4.29.0) supplied `lean-4.29.0-darwin_aarch64.tar.zst`. GitHub release metadata recorded [here](support/lean-compilation-diff/upstream-asset.json) gives 526,040,358 archive bytes and SHA-256 `74309b8f2312f0e8608e0281fd47b08d213bcd53f3c2099fcd10ce3a1a46f0c8`, under the revised 600 MB archive limit. The local `elan toolchain install leanprover/lean4:v4.29.0` finished in 20.252 seconds; the expanded toolchain was 2,673,149,688 file bytes, under 3 GiB ([install record](support/lean-compilation-diff/install-429.json)). The downloaded archive was not retained. Installation and both version runs used only `$ELAN_HOME` for Lean tooling.

| Version | Lean commit | Lake version | `lean` SHA-256 | `lake` SHA-256 |
| --- | --- | --- | --- | --- |
| 4.30.0-rc2 | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `5.0.0-src+3dc1a08` | `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` | `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` |
| 4.29.0 | `98dc76e3c0a9b856c9b98726b713fb04fab16740` | `5.0.0-src+98dc76e` | `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37` | `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b` |

The exact executable paths, arguments, cwd, exit codes, elapsed times, stdout, and stderr are retained in [4.30 runs](support/lean-compilation-diff/runs.json) and [4.29 runs](support/lean-compilation-diff/v429/runs.json). Their SHA-256 values are `95e5543bef3e19ca402bcd7b8f6d3d26b97d226bd762be25a4bb59be08a27770` and `2c5f68330872472796e8ac6b525c5b47f92c69b9d1ee0133efcf9688295b56d4`. The executed [probe](support/lean-compilation-diff/probe.py) and [normalizer](support/lean-compilation-diff/compare.py) have SHA-256 `f1110297b7e3c1abcc8c6d84a54b893ecfe8363a15b525559ce8f434099c7370` and `4c816ce1c83fa425559b1c0846d471cb64184bcc8c3fd43b0b70e42276890936`.

### Fixture and command matrix

Each version ran the same source and config bytes except `lean-toolchain`. The project contains `Probe/Base.lean`, `Probe.lean`, and a separate `Goal.lean` query file. `Probe.lean` evaluates `inc 4` to `5` and prints that `Probe.inc_four` depends on no axioms. `Goal.lean` has an unfinished `exact ?_` tactic; an in-memory LSP edit changes it to `simpa using h`. A relative `lake-manifest.json` (`packagesDir: ".lake/packages"`, `lakeDir: ".lake"`, no external packages) was written before the first Lake invocation on each version. The [input hash record](support/lean-compilation-diff/inputs.json) matches both final trees for all six files. Shared hashes: `lakefile.lean` `ba744b92c5524c6c8096aaa38f57da7c1944d7162546945300206027ba7a3674`; manifest `e00985d61f56efe3f912003a1628166119c495ce8c94ede0f09b56436e896072`; `Probe/Base.lean` `353b9ceb04f5f739703468c468023da3d3c201a9d3a5398dae5bfa0119b57088`; `Probe.lean` `1c6efbb5aafdec02b3f8c876307a6ac18fa59c18875960411ae2d22d932564ba`; `Goal.lean` `ca72613130b63f3ceedde54104312a54adc4949b1295b2ae0ee6f2f545799ced`. The toolchain file hashes are `ce4c4e3d87434b48a0cf0d392e0a320a0787b4674a2d7b61` for 4.30 and `651c8accb402b0c071cd336e9d3dc0a55516b1bfb434ddc4801f14936785b1d2` for 4.29.

For each version, the harness removed only that fixture's `.lake` tree before each build. It ran two clean builds with `LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR='' lake --keep-toolchain --no-cache --old build Probe`, then a cache seed and two fresh-tree cache reuse builds with `LAKE_ARTIFACT_CACHE=true LAKE_CACHE_DIR=<version-scratch>/cache lake --keep-toolchain --old build Probe`. Each build was followed by `lake --keep-toolchain setup-file Probe.lean` and `lake --keep-toolchain env lean --json Probe.lean` with the matching cache environment. Additional cells used `--no-build build Probe`, `setup-file Goal.lean`, batch Lean JSON for both goal variants, and `lake --keep-toolchain serve` for LSP. The direct binary paths, environment and complete command records are in the run JSON files. The manifest has no network dependencies; this is not an offline network-denial test.

### Observed compilation and cache behavior

Within **each** version, clean build 1 and clean build 2 produced the same 16 artifact paths with identical bytes: two `.olean`, two `.ilean`, two `.trace`, two generated `.c`, their `.hash` files, and two setup JSON files. There were no local `.o` or other native object outputs in this `--old build Probe` cell. Both clean batches exited 0, evaluated to `5`, and reported no axioms for `Probe.inc_four`. The cache seed built the same modules; 15 of 16 local artifact hashes matched clean, while `ir/Probe.setup.json` changed with the selected import artifact location. The two cache reuse runs matched each other byte for byte across their six local artifacts. The [4.30 artifact manifest](support/lean-compilation-diff/builds.json) and [4.29 artifact manifest](support/lean-compilation-diff/v429/builds.json) retain every path, byte count, and SHA-256.

| Clean artifact | 4.30.0-rc2 SHA-256 | 4.29.0 SHA-256 |
| --- | --- | --- |
| `Probe.olean` | `0f375fc7aa020047550dc27c031f3ddf0b6640215c981205cc75115f26d17431` | `fdd42592a11e7c790d04c7ee0ea27e1b755a856c12593d3c63147e620ce7a0f8` |
| `Probe.ilean` | `35041f9c03bbbf9318aebc5469258dc0868231ca32d240077f101131d0aad421` | same |
| `Probe.trace` | `66b169e2b314f8846ec14437c13fa8d74ab3eeceeb8554272408ee89e1f59eb3` | `3520bb8d71b423ed968428ee7c1132ffa83b046aacbc47e47bc047016765f7f7` |
| `Probe.c` | `e04ea7174f4bdf205f6ade89b074e3a1e908bd792191d1cbf102c4e8d410e4db` | `1baff1af41be5a3676dc979be9f24dd4fd0ffa100f6068f227e0f11a52e00d50` |

The `.hash` bytes and remaining exact artifact hashes are in the manifests. Across versions, only five of the 16 clean artifact hashes matched: both `.ilean`, both `.ilean.hash`, and `Probe/Base.setup.json`. Version-specific `.olean`, `.trace`, `.c`, and associated `.hash` bytes differed; binary identity must therefore include the toolchain. This is a two-module reproducibility observation, not a claim of Lean's global deterministic compilation.

In both versions, cache reuse printed `Fetched Probe.Base` and `Fetched Probe` and exited 0, but left no project-local `.olean`, `.c`, or related hash files. Its six local files were `.ilean`, `.ilean.hash`, and short fetch traces. `setup-file` succeeded and identified the cached `.olean` paths, and `lake serve` used those paths to elaborate and answer goal queries. By contrast, `lake env lean --json Probe.lean` and `Goal.lean` failed to import their modules from the absent project-local `.olean` paths. `--no-build build Probe` still exited 0 and said targets were up to date. A subsequent build with artifact caching disabled materialized the 16 local files, exactly matching that version's clean artifact snapshot; batch `Probe.lean` then exited 0 and the two goal variants respectively produced the expected errors and no errors. Thus a successful Lake fetch or `--no-build` check alone is insufficient evidence that every downstream Lean invocation can import the module. This is an observed interface difference in this fixture; it does not establish a general Lake defect.

### Server transcript and normalized version diff

Raw [4.30 LSP](support/lean-compilation-diff/lsp-raw.json) and [4.29 LSP](support/lean-compilation-diff/v429/lsp-raw.json) transcripts retain every framed request/response/notification, including elapsed time and process exit. Their SHA-256 values are `0255f835279b7731d2d77a838486aecf1a972a2792d51c9ac852b481458756d3` and `aeaccf222851d9ce5ea6263949e2bbf5140a4051454cc99016c681d99a11fc82`. Both servers exited 0. The sequence was `initialize` → `initialized` → `didOpen` version 1 → `waitForDiagnostics` → two `$/lean/plainGoal` queries → unsaved `didChange` version 2 → wait → two queries, followed by an outside-tactic query, an unsupported method, shutdown, and exit. Earlier cache-mode and materialized-mode transcripts are retained beside the primary transcripts.

Both versions agreed semantically. Version 1 reported placeholder and unsolved-goal errors, with `n : Nat`, `h : n = 0`, and `⊢ n + 0 = 0`; both pre- and post-tactic goal queries returned that goal. Version 2's final diagnostics were empty, its pre-tactic goal was unchanged, and its post-tactic result was `goals: []`, `rendered: "no goals"`. An outside-tactic query returned JSON `null` in both. The deliberately unsupported `$/lean/nonexistentProbe` returned JSON-RPC `-32601` in both. The saved batch goal variants, after materialization, agreed on error versus success. These checks compare final diagnostics for the awaited version, not transient notification count or event timing.

The [normalizer](support/lean-compilation-diff/compare.py) retains raw files and writes [normalized 4.30](support/lean-compilation-diff/normalized.json), [normalized 4.29](support/lean-compilation-diff/v429/normalized.json), and [cross-version diff](support/lean-compilation-diff/cross-version-diff.json). It strips fixture/cache path prefixes and build timing, converts CLI diagnostics to severity/position/message tuples, keeps the last versioned LSP diagnostics, and tags missing, null, and JSON-RPC error responses separately. Its behavioral projection compares source/config identity, Lake exit and built/fetched mode, artifact *presence*, setup import storage and availability, CLI messages, LSP goals/diagnostics, and protocol capability. The full projection also preserves every artifact hash, version identity, setup path, and raw-record hash. The fixture bytes matched; there were 86 full differences, mostly version-specific binary artifacts and identities, and **one behavioral difference**: `initialize.capabilities.experimental.rpcProvider.rpcWireFormat` was `"v1"` in 4.30.0-rc2 and absent in 4.29.0. Both advertised server version `0.3.0`. Treat absence as an unadvertised capability, not as proof that an RPC wire request would fail; no widget RPC call was tested.

### Limits and setup/prompt recommendation

This fixture has two modules, one import edge, and one elementary tactic. It does not cover parallel compilation races, native object/link outputs, package graphs, Mathlib, arbitrary macros, remote cache transport, protocol changes beyond the queried methods, or Lean kernel soundness. Byte equality within one version does not prove semantic equality by itself; the batch evaluation, axiom print, diagnostics, setup-file imports, and LSP goals supply separate semantic checks. Conversely, no-goals at one cursor position is not a complete proof result for Anneal. The query and build evidence remains subordinate to Anneal's Rust-semantics, coverage, and TCB requirements.

**Setup/prompt recommendation.** Pin and record the Lean/Lake binary hashes, toolchain file, source/config hashes, package cwd, manifest, cache mode, setup-file import artifact paths and hashes, and raw versioned LSP transcript for each result. Preseed the relative manifest before any Lake command. Ask probes to check both clean and fetched builds with the exact downstream consumer (`setup-file`, server, and batch CLI if used), treating missing project-local artifacts, import errors, unsupported protocol responses, timeouts, and stale-version diagnostics as incomplete rather than successful verification. Normalize event timing and absolute paths for comparison, but retain raw records and version-specific artifact hashes for audit.

## Boundaries

This is a small fixture, not general Lean compilation determinism. Native object/link outputs, parallel compilation, Mathlib, remote cache transport, arbitrary packages, and other protocol methods remain untested.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/lean-compilation-diff/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Use the retained project, scripts, runs, artifact manifests, and raw LSP transcripts. Verify input and executable hashes; repeat clean and cache-fetched builds; compare semantic checks and artifact presence separately; normalize timing/paths while preserving raw protocol records.
