# R444/R448 Lean batch diagnostics, 4.30.0-rc2 to 4.34.1

## Result and limits

The [R444 normalization-oracle report](../lean-batch-diagnostic-normalization-oracle-v4-30-0-rc2/REPORT.md) (report SHA-256 `ebc75fa732c3c385f3167791ae66986550093423701c98020d8d96b7c3842b22`) and [R448 formatting-controls report](../lean-diagnostic-format-controls-v4-30-0-rc2/REPORT.md) (SHA-256 `ab733a11cf1bec0d6973d34d3960a6575cf7b13e13877024260706fc2c8661b1`) were pinned to Lean 4.30.0-rc2. This supplement reruns their narrow batch claims under that exact binary and Lean 4.34.1. The **31 corresponding batch stdout transcripts per version are byte-identical across versions** for these fixtures, though the emitted R444 `.olean` files have different hashes across versions. These observations establish no general diagnostic or artifact compatibility guarantee.

The two parts below have separate fixtures and assertions. All runs were local, serial, offline batch `lean` children. No Lake, Lean server, Anneal workflow, or user proof was exercised.

## R444: retained normalization fixture

The five [`Probe.lean` inputs and `Query.lean`](support/r444/) are byte-identical copies of R444's retained fixture. Seven compiler cells (a–e, a repeated to the same output path, and a compiled to another output path) plus four successful consumer imports ran under each version. [Raw JSON and `.olean` outputs](raw/r444/) and [results.json](results.json) preserve commands, hashes, and exit codes.

| Within each Lean version | Observed result |
| --- | --- |
| a/b: same source, different input directory | Raw JSON differs in `fileName`; replacing only that path gives equal JSON. `.olean` hashes differ; fixed consumer queries agree. |
| a repeated / output path changed | Both `.olean` hashes equal a's original hash. |
| a/c: `Nat.zero` versus `Nat.succ` information | Normalized full diagnostics differ, but actionable error/warning sets and fixed consumer outputs agree. |
| d: false theorem | Exit 1 and no `.olean`. |
| a/e: true theorem type changed | Normalized diagnostics agree, while `.olean` hashes and consumer-reported theorem types differ (`1 + 1 = 2` versus `2 + 2 = 4`). |

All these relations persisted at 4.34.1. Each of the 11 R444 stdout transcripts is also byte-identical old/new. The artifact hashes differ between compiler versions for a, b, c, and e, even where same-version reruns are reproducible. Thus diagnostic normalization alone remains too weak an equivalence oracle; the consumer query detects the a/e semantic change on this specimen.

## R448: option matrix

The dedicated [Format.lean fixture](support/r448/Format.lean) adapts the unchanged pinned `ppOneline.lean` and `ppUnicode.lean` test expressions, adds a nested `let`, and deliberately ends with an unknown name. Its expected exit status is 1 in every cell; the final error gives a positioned diagnostic. Twenty text/JSON option cells ran under each version. The default and explicit `printMessageEndPos=false` runs agree. The [raw outputs](raw/r448/) and checker preserve each cell separately.

| Control, on this fixture | Observed under both versions |
| --- | --- |
| `format.width=10` versus `120`, `pp.oneline=false` | JSON unchanged. |
| Same widths, `pp.oneline=true` | JSON changes; width 10 truncates the list and lambda with `[...]`. |
| `format.indent=2` versus `8` | Nested `let` lines use 2 versus 8 spaces. |
| `pp.unicode=false` versus `true` | `→`, `∧` become `->`, `/\\` in ASCII mode. |
| `pp.unicode.fun=false` versus `true` | With Unicode enabled, lambda `=>` becomes `↦`; with Unicode disabled, the toggle is invisible. |
| `pp.mvars.anonymous=false` versus `true` | The generated `?m.1` is rendered `?_` when false, and with its numeric name when true. |
| `pp.fvars.anonymous=false` versus `true` | No change; this fixture does not expose a loose generated free variable. |
| `printMessageEndPos=false` versus `true` | Text error location changes from `10:7` to `10:7-10:35`; JSON is byte-identical and retains structured positions. |

The [exact source map](support/source-map.json) binds Lean commits `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and `5045d0056413266e57c625dcd7c365b10e377c52` to the Message, Formatter, Language, Shell, Format, and pinned-test blobs; the [source diff](support/source-diff.patch) is retained. Although these source files have other changes, the selected batch boundaries still call `MessageData.toString` through ordinary `Format` string conversion, use `OneLine.pretty` with `format.width` when `pp.oneline` is set, read `format.indent` during syntax formatting, and select `msg.toString includeEndPos` for text versus `msg.toJson` for JSON. The two pinned pretty-printer test files are byte-identical across commits. This source reading explains the measured result at these exact revisions; the runtime matrix is the evidence for actual output equality.

## Execution and replay

Old binary: Lean 4.30.0-rc2, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. New binary: Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`. Full `lean --version` strings and argv are in [results.json](results.json).

The [runner](support/probe.py) checked reclaimable memory above 20%, disk above 1 GiB, and package bytes below 100 MB before each of 62 recorded children. Minimum admission was 22.0371% memory and 2,276,118,528 disk bytes; maximum owned package bytes at admission was 260,572, maximum sampled child RSS 402,256 KiB, and maximum child duration 1.61 s. It killed a **preliminary, excluded** R448 attempt with `import Lean` when sampled RSS reached 1,051,648 KiB, above the 1 GiB cap. Removing that unnecessary import made the core fixture safe; the excluded attempt has no retained stdout and is not counted among the 62 results.

Run `python3 -B support/check.py` from this package to recheck fixture and source hashes, every recorded command/output/artifact, admission arithmetic, both claim matrices, and cross-version stdout equality without launching Lean. `python3 -B support/probe.py` reruns the batch cells only with the named local toolchains and fresh per-child resource admission. The offline checker works after relocating this package; active reproduction requires those installed binaries.
