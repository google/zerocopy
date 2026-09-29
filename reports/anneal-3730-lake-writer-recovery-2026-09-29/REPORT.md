# Lake artifact-cache writer interruption and recovery at v4.30.0-rc2

## Summary

In a tiny Lean/Lake fixture with `LAKE_ARTIFACT_CACHE=true`, killing the only writer during `Dep.lean` elaboration left **no cache files** and a partially prepared writable package directory. `lake --no-build setup-file` then exited 3 as out of date; an ordinary build repaired the package and populated the cache, after which setup succeeded. In a separate two-consumer run, both writers reached the controlled pause; one was killed, the other completed and published three cache artifacts plus one output mapping. The killed consumer subsequently fetched `Dep` from that cache and completed setup. A copied cache with a deliberately truncated output mapping caused no-build setup to fail explicitly; ordinary build repaired the mapping, and setup plus a direct Lean proof loader passed.

These are bounded execution slices for [#3731](https://github.com/google/zerocopy/issues/3731) I092/I098/I102/I108/I109/I151 and #3730 F06/F07/F11/F12/J13/J15. The kill occurs **before artifact publication**. This report does not claim crash atomicity of the cache mapping write or safety for two writers in one package directory.

## Applicability and controls

The executed toolchain was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `v4.30.0-rc2`, on macOS 26.6.2 arm64 with 8 GiB physical RAM. Binary SHA-256: Lake `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; Lean `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The fixture has one local producer module `Dep` defining `depValue := 7` and a consumer source proving `depValue + 1 = 8` by `decide`. Each consumer has a complete relative path manifest before Lake starts. There are no registry dependencies, Mathlib, plugins, native libraries, generated Rust models, or Anneal code in this run.

Every Lake process used an isolated `HOME`, `LEAN_NUM_THREADS=1`, `LAKE_ARTIFACT_CACHE=true`, and an explicit owned `LAKE_CACHE_DIR`. The solo and paired jobs used distinct producer/consumer package directories; only the paired jobs shared the **cache directory**. A `run_cmd` in `Dep.lean` writes its process-specific marker and sleeps 1.5 seconds before the module result is emitted. The harness kills the writer process group once the required marker exists. In the paired case it waits for both markers, kills A, and lets B finish. At most two consumers ran concurrently. A 5,500,000 KiB sampled summed-RSS guard and short marker/completion timeouts would kill the groups and fail the experiment if exceeded. Observed sampled maxima were 1,799,328 KiB across two processes for solo and 3,512,256 KiB across four processes for the pair. These sums can double-count shared pages and are not unique physical memory or true peak RSS.

The corrupted mapping was produced by local deliberate truncation **after** the successful paired publication, in a copy of that cache. It is a failure-injection control, not a claim that the preceding process kill caused corruption. Scratch execution trees are under the conversation-owned Meta/Data directory; `support/artifacts/` retains selected killed-package and cache trees for inspection.

## Observations

### Sole writer killed before cache publication

The solo preflight `--no-build build Dep` exited 3, establishing an unbuilt starting point while loading package configuration. A subsequent `build Dep` entered the `run_cmd` pause and was killed with `SIGKILL` (`-9`). The cache inventory immediately after the kill was empty. The producer directory had six files: source/control, compiled configuration and its trace, and `Dep.setup.json`; it had no `Dep.olean`, `.ilean`, generated C, or module trace. `--no-build setup-file Generated.lean` exited 3 with “target is out-of-date and needs to be rebuilt.”

An ordinary `build Dep` retry exited 0, then no-build `setup-file` exited 0 and named the cache-resident `Dep.olean`. The repaired cache had three content-addressed artifacts—`.olean`, `.ilean`, and generated `.c`—plus `outputs/probe_dep/566c416840dafb01.json`. The producer directory grew to 13 files. This schedule demonstrates explicit failure and recovery after an early killed writer, not interruption during cache-object or mapping publication.

### Two writers, one shared cache, separate writable package directories

Both consumers first ran no-build preflights, each exiting 3. Their independent writers then reached the pause; A was killed (`-9`) and B exited 0 after building `Dep`. At that point the shared cache contained exactly four files: `.c`, `.ilean`, `.olean`, and one output mapping. A's producer package still had six files and no module result, while B's producer package had 13 files. The successful cache object `7b7a31f2adb2306a.olean` had SHA-256 `4d2519d8006d6b63510989fa471021ac046867c69ec94aa8e11212bc8468da85`; the mapping had SHA-256 `4374ce75e3040a0287f0da02104f90620d0b53e417a218b68ab5e7c4cd21f4e7`.

A subsequent `--no-build build Dep` in the killed consumer exited 0 and logged `Fetched Dep`. No-build `setup-file Generated.lean` exited 0 and returned the cache-resident OLean path. After fetch, A's producer directory had nine files, still without a conventional local `Dep.olean`; its setup used the cache path. A's package state therefore changed independently of the four-file cache inventory. A direct Lean loader using that cache object under an isolated `Dep.olean` name accepted the theorem and evaluated `8` (exit 0).

The paired result is one surviving-writer schedule. It does not establish that two complete concurrent writers would serialize output mappings, that a cache map is crash-atomic, or that one shared **package build directory** is safe. The earlier writer-scale report found a schedule-dependent compiled-configuration error in a shared writable package; this run avoids that collision by using separate package trees.

### Deliberately truncated mapping rejects, then rebuilds

The script copied the intact four-file shared cache and replaced its output mapping bytes with `{"data":`. A fresh source/control-only consumer's `--no-build setup-file` exited 3, warning of invalid JSON and saying `Dep` needed rebuilding. Ordinary `build Dep` exited 0 despite warning about the prior invalid mapping, rewrote it to the same SHA-256 as the intact mapping, and left the three content-addressed artifact hashes unchanged. No-build setup then exited 0. A direct Lean loader of the repaired `.olean` accepted the equality theorem and evaluated `8`.

This validates one explicit parser-failure/fallback/retry path. It does not cover an interrupted mapping write itself, a valid-but-wrong mapping/object, remote download, extraction, cache eviction, or filesystem durability. Prior reports separately show that a present wrong-generation local OLean can pass Lake no-build setup; this malformed-JSON rejection must not be generalized into a byte-integrity guarantee.

## Exact residuals

| Item | New evidence | Still unresolved |
| --- | --- | --- |
| I092 | No-build setup rejects missing output after killed writer and accepts repaired output; explicit cache path returned. | Exact `lake serve`/server no-build path, malformed manifests, missing configs, all artifact families, read-only package semantics. |
| I098 | `.olean`, `.ilean`, generated `.c`, output mapping, and package-local trace/setup state inventoried separately; direct Lean loader checked OLean. | Mixed/truncated cross-generation `.ilean`, native/plugin artifacts, server/private OLeans, diagnostic quality for every missing family. |
| I102 | One solo and one two-writer early kill; shared cache survivor/fetch; truncated mapping rejection and repair. | Kill between artifact and mapping publication, simultaneous map writers, interrupted restore/download/extract, wrong-identity objects, durable atomicity. |
| I108 | Bounded waits and no deadlock in this two-writer cache schedule. | Lock-order graph across preparation, publication, server restart, garbage collection, and induced waits after lock acquisition. |
| I109 | Memory guard, timeouts, killed-process classification, explicit post-kill no-build failure and retry. | Actual memory/disk/descriptor/process-slot exhaustion, cleanup of arbitrary descendants and partial generations, last-good Anneal publication. |
| I151 | Shared cache with separate writable package dirs; killed A did not prevent B and later fetch. | Same writable package/build tree, conflicting definitions, kill at output/trace publication, and a general contract for shared package writers. |

No Anneal claim, Rust-to-Lean correspondence, proof-obligation coverage, live Lean server, or MCP operation follows from this fixture. Lake and direct Lean success establish only the stated synthetic module theorem under this selected toolchain. The paired run is capped at two consumers; no high-load extrapolation is made.

## Evidence and replay

- `support/probe.py` SHA-256 `6304d7953ed43bc75dd621f85f882d51824d26341f7a63c2091cb8daf90badf2` creates the fixture, controls `LAKE_ARTIFACT_CACHE`, monitors process-tree RSS, kills at source markers, retains inventories, injects mapping truncation, checks statuses, and writes the evidence.
- `support/results.json` SHA-256 `5accf91a0611bff361ceb03bd4e2de2f43ebb17ce34ef17768ebb5239b3dc215` records 16 labelled invocations, commands, exits, messages, timings, cache and package SHA-256 inventories, marker/peak observations, and the corruption/repair identities. Local roots are replaced with `$WORK` and `$TOOLCHAIN` in command text.
- `support/artifacts/solo-killed-package/`, `pair-killed-package/`, `shared-cache/`, `solo-repaired-cache/`, `truncated-output-map.json`, and `repaired-cache/` preserve representative bytes for comparing package-local state with artifact-cache state. The complete disposable execution tree remains in the recorded Meta/Data work directory.

Replay from this package with `python3 support/probe.py --work /new/absent/owned/directory` while the pinned binaries remain at the paths declared in the script. The work path must not exist. Confirm the exit/classification assertions, the post-kill empty cache, the survivor's four-file cache, fetched setup path, direct Lean value, truncated-map warning, and repaired mapping/artifact hashes. Marker scheduling, wall times, process IDs, and sampled RSS can vary; a failed guard is a failed run, not evidence of successful recovery.
