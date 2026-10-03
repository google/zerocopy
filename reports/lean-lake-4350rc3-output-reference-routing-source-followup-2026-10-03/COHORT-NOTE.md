# Lean, Lake, Mathlib, and editor-source version follow-up (3 October 2026)

## Method

This is a read-only version and mapped-source audit against the persisted 651-row v90 matrix at `ba4556c30835b56d108b0a6854a760bccf8438c5`. `upstream_refs.json` preserves the stdout and command for official GitHub `git ls-remote` HEAD/tag queries. `mapped_source_results.json` records official raw-source URLs and SHA-256 comparisons for 52 mapped paths, selected from the published current-source claim maps and the narrow Lean/Lake source review. Commands used: `git ls-remote https://github.com/<owner>/<repo>.git HEAD [release refs]`; `curl --fail --silent --show-error --location https://raw.githubusercontent.com/<owner>/<repo>/<full-commit>/<mapped-path>`; `python3 check_mapped_sources.py`; and `python3 -B check.py --reference-root /path/to/zerocopy-checkout`. The network helper fetches source text only. It does not install or execute any toolchain.

The current branch tips are revision observations, not release version claims. Equal mapped bytes do not prove equivalent runtime behavior, and changed bytes do not prove a behavioral regression. The published old-pin reports and v90 status labels remain as they were.

## Release identities

| Cohort | Latest stable release observed | Optional prerelease observed | Current official HEAD |
| --- | --- | --- | --- |
| Lean/Lake | [`v4.34.1`](https://github.com/leanprover/lean4/releases/tag/v4.34.1), 24 Sep 2026, `5045d0056413266e57c625dcd7c365b10e377c52` | [`v4.35.0-rc3`](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc3), 24 Sep 2026, `470d5ce1400764999581fd26d5d72b00d990b0f4` | `193c3589a4fc16c4059261ab38cfa365eb24f323` |
| Mathlib4 | [`v4.34.1`](https://github.com/leanprover-community/mathlib4/releases/tag/v4.34.1), 24 Sep 2026, `d13f23b723b8a846827a245b89c10fc7d3f11612` | [`v4.35.0-rc3`](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0-rc3), 25 Sep 2026, `c55e6e786f49471c72fbddbec5415808896aec1e` | `302343bb9a029d4edab4f736703f0736896c1b64` |
| TypeScript native | [`v7.0.2`](https://github.com/microsoft/TypeScript/releases/tag/v7.0.2), 20 Aug 2026, mirrored tag `1e4744d68260a7cb91b62b12edc3f6a2187faaf1`; [original tag](https://github.com/microsoft/typescript-go/releases/tag/typescript%2Fv7.0.2) `2bd066d87f5bafd315be9f40889d0a60b9e58e0b` | None identified in the checked release page | `microsoft/TypeScript` `f9f8d01292562242b6e7c7142e46ed7e470926f9`; archived original `microsoft/typescript-go` `89d5d5b2849a0db0957065889ca58536fa6d2e4a` |

The Lean/Mathlib stable tags and rc3 tags were already named in v90's newer target fields. No newer stable Lean or Mathlib release was found on the checked first-party release pages. Lake follows the Lean repository version; it has no separate checked release identity here. Mathlib's current `lean-toolchain` is exactly `leanprover/lean4:v4.35.0-rc3`, matching the tagged Mathlib rc3 text and differing from the 4.34.1 tag's `leanprover/lean4:v4.34.1`.

## Mapped source comparisons

| Published claim cohort | Official HEAD checked | Mapped paths | Outcome versus published selected source |
| --- | --- | ---: | --- |
| clangd, LLVM | `1f1a5b38374af3fc5afb52d91c91c0203b5edcdf` | 5 | All byte-identical |
| gopls, golang/tools | `3f3efb7c3b31192232c67403b23a00bfcdbc3eec` | 7 | All byte-identical |
| rust-analyzer | `3332931d313fad08166571c05d7237d3a4d77ac2` | 1 | Byte-identical |
| Roslyn | `8d2c75f24c88ea99a01a8579ecb67e303d566670` | 13 | All byte-identical |
| rocq-lsp | `6ff2d0723547eb84352892cd546f87824d9a9f18` | 4 | All byte-identical |
| Haskell Language Server | `1cd039d9e3916264724071068f8eb38c5ee7fa85` | 4 | All byte-identical |
| Kotlin | `9b80c8ff99f3a63fcf578010bb2712697f4886aa` | 6 | All byte-identical |
| sourcekit-lsp | `46d33b124af55647b8329b694373c8479ccb0a85` | 3 | All byte-identical |
| Swift | `c5fe44b279ba711339330853a14be3b6516511e8` | 2 | Both byte-identical |
| Lean/Lake selected claim paths | `193c3589a4fc16c4059261ab38cfa365eb24f323` | 6 | Three equal, three changed; see [supplement](REPORT.md) |
| Mathlib toolchain selector | `302343bb9a029d4edab4f736703f0736896c1b64` | 1 | Changed to rc3 version |

The 52 selected path comparisons total **48 equal and four changed**. The changed Lean files are `Cache.lean` (deprecation spelling only), `Build/Common.lean` (rc3 output-reference condition change plus a later HEAD-only hash helper), and `RequestHandling.lean` (LSP helper refactor, with the selected wait-for-diagnostics predicate unchanged). Exact old/tag/HEAD source snapshots and hashes for these are retained under `raw/leanprover/lean4/`; `REPORT.md` states the claim consequence. The published maps themselves remain the source of path selection. The other 45 paths' official raw URL and observed SHA-256 are recorded in JSON but their full bytes are not retained locally; an offline checker can verify retained evidence and structural counts, while repeating those 45 remote comparisons requires network access.

The official `HEAD` checks also returned unchanged pinned tips for `haskell/hie-bios` `32dd07707423ffabb34e44af68fcbd027b60ded2`, archived `rust-lang/rls` `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`, and `microsoft/TypeScript-wiki` `966988bcca7c835fd22ab066bb6a9ff4d5ba511d`; those three had no newer mapped path to fetch. `rocq-archive/coq-serapi` was not freshly queried in this follow-up, so its status remains the prior published observation, not a fresh check. Separate release catalogs for clangd, Roslyn, gopls, HLS, Kotlin, Swift, Rocq and rust-analyzer were not inventoried; this cohort note reports exact current branch revisions and mapped path content only.

## TypeScript native-source boundary

The v90 R576 review already leaves the 7.0.2 host/world mapping unresolved. The three native entry points it inspected at original `microsoft/typescript-go@2bd066d87f5bafd315be9f40889d0a60b9e58e0b`—`internal/project/project.go`, `internal/lsp/server.go`, and `cmd/tsgo/lsp.go`—all have changed bytes at that repository's later archived HEAD `89d5d5b2849a0db0957065889ca58536fa6d2e4a`. Both versions are retained under `raw/microsoft/typescript-go/`. The same relative raw paths returned HTTP 404 at both the mirror's `v7.0.2` tag and the checked `microsoft/TypeScript` main tip; no mirror path equivalence was inferred. A full post-7.0.2 native architecture or integration-surface review remains unavailable here. The observed source drift therefore does not upgrade R576's unresolved source, runtime, or product labels.

## Limits

No Lean/Lake, Mathlib, TypeScript or editor engine was executed. No toolchain or server was installed or downloaded. The retained admission estimate was approximately 24.3% reclaimable RAM, below the 30% gate; only text source/ref queries were performed. The source comparisons do not cover whole repositories, transitive dependencies, every version named in the 651-row matrix, or all report clauses. They establish only the selected path byte relation and the scoped source changes stated above.
