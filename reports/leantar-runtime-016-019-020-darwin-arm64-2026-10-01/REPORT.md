# R491: native `leantar` 0.1.16, 0.1.19, and 0.1.20 fixture comparison

## Result

The already-installed Darwin arm64 helpers identify as **0.1.16** (Anneal's separately fetched unpacker), **0.1.19** (bundled with Lean 4.30.0-rc2), and **0.1.20** (bundled with Lean 4.34.1). With one ten-byte numeric trace and one 30-byte artifact, each helper produced the same 101-byte `LTAR` archive, SHA-256 `be5e94042c7f4c245ffeb92c4266c6e15f136539dbd5d3451906e4dd03f94f16`. All **nine** producer/consumer combinations exited zero and reproduced both fixture files exactly. This is a direct small-fixture compatibility observation, not a proof of general archive compatibility.

The newer helper also accepts `-s` and produced a 143-byte **`LTR4`** stripped-hash archive, SHA-256 `f95e6fe5f7a351259f87af14838bebecc33fbd2789bbbb94d4e42971f1f1cd52`. The 0.1.16 and 0.1.19 helpers each rejected those bytes with `bad .ltar file` and exit 1, leaving no output files. The 0.1.20 helper extracted the artifact with exit 0 when given the hash `75bcd15` through its JSON input; it reconstructed the trace as `{"depHash":"00000000075bcd15","schemaVersion":"2025-09-10"}`. Thus the newer bundled helper retains ordinary `LTAR` behavior on this fixture but has a **new, opt-in archive variant** that the older helpers do not read.

## Exact identities and method

| Helper | Provenance | Local binary SHA-256 |
| --- | --- | --- |
| `leantar 0.1.16` | Anneal's direct helper, matching the operational subject of [the pinned format report](../leantar-archive-format-v0-1-16-v0-1-19/REPORT.md) | `74b681d647b5f288b7e3ba89b562808de656abcde72771e97170bc377137e20a` |
| `leantar 0.1.19` | Lean 4.30.0-rc2 toolchain's `bin/leantar` | `9bddd23bcddf44b27cf3a79e38dde45c53278721980695abdc76587fc3c89d41` |
| `leantar 0.1.20` | Lean 4.34.1 toolchain's `bin/leantar` | `97ddd119805f7d020bb823f818140b078eb37057b1b53174899c0d9aff0ea6c7` |

The original `reference` package `reports/leantar-archive-format-v0-1-16-v0-1-19` compared source-level format and extraction behavior of 0.1.16/0.1.19 and explained Anneal's split between its fetched unpacker and the Lean-sysroot helper. The later `reports/anneal-3731-version-source-audit-83-2026-10-01` marks R491's helper runtime recheck unexecuted. This report adds a direct comparison of those two local binaries with the 4.34.1-bundled binary. It does not revise the pinned source report's path-handling, corrupted-input, atomicity, or cache-producer claims. The separate [Linux AArch64 packaging recheck](../lean-430rc2-to-4341-linux-aarch64-leantar-static-recheck/REPORT.md) concerns ELF architecture, while all three binaries executed here are native Darwin arm64.

The [probe](support/probe.py) hashes each binary before execution, checks a small resource floor before each invocation, runs one process at a time with an eight-second timeout and `--jobs 1` for unpacking, and records each command, return code, stderr/stdout, and resource sample in [results.json](results.json). Its fixture is [build.trace](fixture/build.trace) (`123456789`, no newline) and [artifact.txt](fixture/artifact.txt). The retained [work tree](work/) contains the three ordinary archives, nine extracted pairs, the stripped archive, and its successful extraction. The [offline checker](support/check.py) verifies the retained evidence without executing a helper.

Across 19 guarded calls (three version queries and 16 archive operations), the minimum sampled reclaimable fraction was **25.37%** and the minimum free disk was **15,403,745,280 bytes**. The helper-specific admission floor was >20% reclaimable RAM and >10 GiB disk. This is a tiny helper probe; it did not launch Lean, Lake, an LSP server, or Anneal. The separate guarded Lean-server experiment remained unexecuted after its >30% RAM admission failed.

## Limits and reproduction

Only the numeric-trace `LTAR` path and the 0.1.20 `-s` `LTR4` path were run. No Mathlib object, V2/V3 trace, `.olean` codec, damaged archive, preexisting destination, overlapping process, or Anneal end-to-end workflow was tested. The `LTR4` result does not imply Anneal currently uses `-s`, and the nine successful cells do not establish equal extraction failure semantics.

Run `python3 -B support/check.py` to check retained evidence offline. To repeat the active probe, run `python3 -B support/probe.py --bin-016 /path/to/0.1.16/leantar --bin-019 /path/to/Lean-4.30.0-rc2/bin/leantar --bin-020 /path/to/Lean-4.34.1/bin/leantar` in a fresh copy of this package. The script rejects binaries with SHA-256 identities different from those above and replaces its own small `work/` output tree; it does not install anything or contact the network.
