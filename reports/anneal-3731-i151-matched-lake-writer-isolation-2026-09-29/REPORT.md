# Matched shared and isolated Lake writer interruption at 4.30.0-rc2

## Summary

Four two-writer cells compared one shared writable Lake package/build tree with two isolated package/build trees under the same source values and reverse killed-writer schedules. When the newer writer was killed, the older writer exited successfully in both topologies and produced the same old-definition OLean bytes. Its isolated tree remained up to date for its own unchanged source; its shared tree, whose source had changed from 7 to 9, failed an immediate `lake --no-build build Dep` freshness check (exit 3). The successful writer exit therefore did not certify the current source of the shared tree. A fresh Lean process read 7 from each old artifact. When the older writer was killed, both newer writers produced byte-identical 9 artifacts and passed no-build.

This fills a bounded matched isolated-versus-shared comparison for #3731 I151 and #3730 F12. The sampled RSS values served as an admission and gate-period safety guard; this fixture does not measure the Rust-side sharing or disk bill requested by other issue rows.

## Applicability

The exact subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Lake binary SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, Lean binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, on macOS arm64/APFS with 8 GiB RAM. The fixture is a local one-module Lake package, no remote dependency, one `LEAN_NUM_THREADS=1` compiler child per writer, `LAKE_NO_NET=1`, `LAKE_NO_CACHE=1`, and `LAKE_ARTIFACT_CACHE=false`. Each cell was run serially with at most two writer process groups concurrently. Both topologies used the same module text and controlled gate code; the distinction was whether A and B wrote one physical package/build tree or separate trees.

Before each cell, the script checked over 10 GiB free disk and at least 35% system-wide memory free. The four actual preflights reported 42% free memory. While waiting for both writers to reach their gates, a sampled summed process-tree RSS guard would stop the cell above 4,000,000 KiB; maxima recorded in that interval ranged from 3,614,416 to 3,642,960 KiB. Sampling stopped after both gate markers, so these are not whole-cell peaks. The sum may count shared pages twice and can miss peaks between polls; it is not physical-memory use. All commands had bounded waits. The artifact-cache publication path was disabled and is outside this comparison.

## Findings

Each root was primed with a successful `lake build Dep`, then only its `.lake/build` directory was removed; this kept compiled package configuration state while forcing a module build. A's compiler read `depValue := 7` and blocked in `run_cmd` after writing `A.entered`. For the shared cells, the script changed that same `Dep.lean` to 9 before launching B. For isolated cells, B already had an independent 9 source. B wrote `B.entered` before either process group was killed. The script killed one writer group, released the other, and recorded its exit, artifact, trace, no-build result, and two fresh direct Lean proof controls.

| Topology; killed writer | Survivor exit and OLean definition | Immediate no-build | Fresh proof controls |
| --- | --- | --- | --- |
| Shared; A (old 7) | B exits 0; 9 | 0, up to date | 9 succeeds; 7 fails |
| Isolated; A (old 7) | B exits 0; 9 | 0, up to date | 9 succeeds; 7 fails |
| Shared; B (new 9) | A exits 0; 7 | 3, out of date | 7 succeeds; 9 fails |
| Isolated; B (new 9) | A exits 0; 7 | 0, up to date | 7 succeeds; 9 fails |

The A-killed pair had identical OLean SHA-256 `d934a89791cbb4236eca9f88c4e3f5d7136c47c8f3aecc965f476df32f69b15c`. The B-killed pair had identical OLean SHA-256 `17bae46ced2944349a85c534f3e6240dc96b89da2569fe358620932df0c8f89c`, distinct from the 9 artifact. In the shared B-killed cell, `--no-build` wrote `Dep.trace.nobuild`; the retained `Dep.trace` hash did not change. The isolated B-killed cell and both A-killed cells had no such no-build trace. Trace bytes themselves differ across topology because Lake logs physical command paths, so their raw hashes are not an equivalence oracle. **Basis: execution**, `support/results.json` and retained `support/artifacts/` OLean and trace specimens.

The matched control isolates a narrow source-ownership distinction: an old build is valid in its own unchanged root but stale at a reused mutable pathname. The no-build failure shows Lake detected this selected stale state after the successful old writer; no silent acceptance was observed. It does not prove that separate roots are generally safe under every dependency graph or interruption phase. **Basis: execution + derived**.

## Boundaries

- This is one retained completed run per cell. It establishes the witnessed outcomes, not failure frequencies or schedule independence.
- Both writers stopped inside source-level `run_cmd` before artifact output. The kill did not occur during an OLean, trace, hash-sidecar, or configuration write syscall. Partial-file integrity and recovery at those points remain unresolved for I151/F12.
- Each cell used one package/module on APFS with no native plugin, Mathlib, Aeneas-generated model, actual Anneal scheduler, or prepared archive. No general shared-writer ownership protocol follows. The actual Anneal V2 ownership policy remains a product/integration prerequisite.
- Artifact cache was explicitly off. This result must not be combined with same-key artifact-cache publication experiments as if they were the same writable surface.
- RSS was sampled only before the gate release. The fixture gives no whole-cell memory peak, disk amplification, cumulative writes, unique physical memory, 4/8/16-worker economics, or cancellation cost. Whole build trees were not retained or measured; the small saved OLean and trace specimens do not substitute for an actual prepared workspace.

## Evidence

- `support/probe.py` constructs all four fresh local cells; it records priming, gate order, process-group kill/release, exact exits and streams, source/artifact/trace hashes, no-build behavior, fresh Lean proof controls, and preflight/gate-period RSS samples. It writes the selected work directory, result JSON, and `support/artifacts/` beside the script. The work directory is disposable and is not needed to check the retained result.
- `support/results.json` is the exact retained command/event record for the trace-capture run. `support/artifacts/` preserves four survivor OLeans and four build traces. The trace logs include absolute local build paths; they are evidence of this exact run, not portable byte goldens.
- `support/check.py` checks the four cell names, gate/kill ordering, resource guards, exit/proof/no-build matrix, and SHA-256 of every retained artifact and trace against the result record. The checker does not prove unsampled absence of a write or other schedules.
- Related prior execution: [two conflicting writers in a shared tree](../anneal-3730-lake-shared-tree-conflicting-writers-2026-09-29/REPORT.md) and [writer-scale/frozen-producer controls](../anneal-3730-lake-writer-scale-v4-30-0-rc2/REPORT.md). This report adds the matched separate-root controls for both reverse kills.

## Revalidation

Run `python3 support/check.py` to check retained evidence. To reacquire the experiment with the identified local binaries and sufficient host resources, copy the package to an owned disposable directory and run `python3 support/probe.py` there; a replay replaces the copy's saved artifacts and result. Compare the matrix of exits, two fresh Lean controls, and paired OLean byte hashes. A repeat may encounter a compiled-configuration race before the gates; the script fails that cell rather than treating it as an equivalent completed comparison. To address the remaining I151 interruption question, instrument a controlled artifact or trace publication point in an owned disposable tree, observe both writer generations there, then test immediate fresh reads and retries before drawing a stronger sharing rule.
