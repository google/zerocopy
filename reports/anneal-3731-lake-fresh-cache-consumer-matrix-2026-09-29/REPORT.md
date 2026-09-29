# Fresh Lake consumer with a seeded artifact cache and selected missing state

## Summary

A new two-package consumer fetched both modules from a seeded Lake artifact cache under `--no-build`, then matched an independently clean build on the tested OLean/ILEAN/C bytes, batch theorem/axiom output, and live first goal. Removing the dependency source from a prepared producer split the outcomes: no-build Lake rejected the missing `Dep.lean`, a direct `lake env lean --json` batch still accepted the retained OLean and printed the theorem's axiom result, and a fresh `lake serve` returned no first goal with missing-source diagnostics. Batch import success alone did not establish a usable prepared interactive consumer.

Removing the producer's saved traces allowed a cache fetch to reconstruct them. Removing hash sidecars allowed local replay and rewrote the sidecars. Removing its IR setup JSON did not force its recreation in this selected no-build path. Removing compiled package configuration let Lake recreate that state in the producer. These are different persistence and write requirements; a seeded cache is not a complete read-only archive.

## Applicability

The executed subject was local Lean/Lake `v4.30.0-rc2` at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, on macOS arm64/APFS with 8 GiB RAM. The fixture has a `probe_dep` package defining `depValue : Nat := 7` and a `probe_consumer` package importing `Dep`, proving `depValue + 1 = 8` with `decide`, tracing the first tactic goal, printing axioms, and evaluating 8. It has a complete relative path manifest, a local installed toolchain, no remote dependencies, and no Anneal, Aeneas, Mathlib, native plugin, or generated Rust model.

The script ran one fixture cell at a time after observing 47,671,160,832 free disk bytes and 21.97% free memory by its `vm_stat` estimate. Each Lake call used an empty test `HOME` and XDG cache, explicit owned `LAKE_CACHE_DIR`, `LAKE_NO_NET=1`, `LEAN_NUM_THREADS=1`, a 35-second command timeout, and `/usr/bin/sandbox-exec` with `(deny network*)`. No download or dependency installation was attempted. The producer build used `LAKE_ARTIFACT_CACHE=true`; the independent clean build used `false`; fresh consumers left it unset, selecting Lake's default readable/non-writable policy. The server used `--no-cache`; no-build was applied to the Lake build check, not to the later direct batch command or server launcher.

This is component evidence for #3731 I089/I092/I099 and the corresponding #3730 F02/F04/F07/F08/F13/F19/F20/I02/I04 crosswalk destinations. It does not close the actual-archive requirements in those rows. The [real archive availability report](../anneal-3730-real-archive-manifest-gate-2026-09-29/REPORT.md) found no built Anneal omnibus archive in its bounded local inventory. The [clean/cache source contract](../lake-clean-cache-seeded-equivalence-v4-30-0-rc2/REPORT.md) and [artifact-cache noncoverage report](../lake-artifact-cache-noncoverage-v4-30-0-rc2/REPORT.md) identify why this selected execution matters and why it cannot establish whole-archive equivalence.

## Findings

### Clean and freshly fetched controls agreed on the selected artifact and proof observations

The clean `lake -v build Generated` reported `Built Dep` and `Built Generated`. A separate cache-writing seed build also built both. Their producer `Dep.olean`, `.ilean`, and generated `.c` SHA-256 values matched exactly: respectively `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`, `ee34578f6077d4f2019dca615b30d0de14340a9d0d36cdb2870f3285adeb00e5`, and `36383e740367044dc594c872922b0c37356a7c73a35f72ff5cdc252e829e052e`. The clean batch command exited 0, evaluated 8, and printed that `generatedEq` depends on no axioms. Its fresh live `$/lean/plainGoal` returned `⊢ depValue + 1 = 8`.

The `fresh_full` consumer started in a new root and private producer copy with that producer's entire `.lake/build` removed, while the eight-file seeded artifact cache remained. `lake -v --no-build build Generated` exited 0 and reported `Fetched Dep` and `Fetched Generated`; it materialized seven producer build files and changed no pre-existing producer file bytes. Subsequent direct batch checking again evaluated 8 and printed the same axiom result. A new Lake-launched server returned the same first goal. The shared cache inventory did not change. **Basis: execution**, `support/results.json` clean/seed/fresh_full records and SHA-256 inventories. This paired result covers only the named artifacts and selected theorem/goal.

### Source absence was rejected by Lake preparation despite a successful direct batch import

`no_source` retained the prepared producer's OLean and other build state but removed `Dep.lean` before a new consumer was created. The no-build Lake action exited 1 with “no such file or directory” at `producer/Dep.lean`, a bad `Dep` import, and build failure. The direct `lake --no-cache env lean --json Generated.lean` command still exited 0 using the retained OLean, evaluated 8, and printed that `generatedEq` depends on no axioms. A fresh `lake --no-cache serve` process answered `textDocument/waitForDiagnostics`, but its `$/lean/plainGoal` result was `null`; its diagnostics named the missing source and failed setup. A successful wait response or batch theorem check was therefore not a successful first-goal result in this cell. The producer's remaining file-byte inventory did not change. **Basis: execution**.

This result is specific to direct Lean import from the prepared artifact versus Lake's source-dependent preparation for that document. It does not imply that the missing source is safe to omit from an Anneal archive merely because one batch command accepted its compiled artifact.

### Trace, hash, setup, and compiled-config ablations took different paths

| Producer removal before a new consumer | No-build Lake action | Batch / first goal | Producer net-byte result |
| --- | --- | --- | --- |
| `Dep.lean` | Exit 1; missing source/bad import | Batch exit 0; goal `null` | No remaining file changed |
| Both saved `.trace` files, including config trace | Exit 0; `Fetched Dep`, `Fetched Generated` | Batch exit 0; same goal | Two traces recreated |
| Three `.hash` sidecars | Exit 0; `Replayed Dep`, `Fetched Generated` | Batch exit 0; same goal | Three sidecars recreated |
| `Dep.setup.json` | Exit 0; `Replayed Dep`, `Fetched Generated` | Batch exit 0; same goal | Setup file remained absent |
| Compiled producer `.lake/config` | Exit 0; `Replayed Dep`, `Fetched Generated` | Batch exit 0; same goal | Config OLean and trace recreated |

Every cell used its own new consumer root and copied producer tree, with consumer `.lake` removed before its first call. The seeded cache's file/hash inventory was unchanged in every cell. The recreated producer files show that a successful no-build read can still write local metadata or configuration. The `no_setup` result shows only that this selected path did not require that one IR setup file; it does not establish that all setup/control files are dispensable. **Basis: execution**.

## Boundaries

- **Actual Anneal archive and first-goal write tracing remain unexamined.** This one-module fixture cannot close I089/F02/F04/F08/F13/F20/I04, or establish a production read-only dependency contract. The copied producers were writable to classify net changes; permission denial and syscall-level write tracing were not repeated here.
- **No complete clean-versus-prepared equivalence is claimed.** Only one theorem, one dependency, three producer artifact classes, batch output, and the selected live first goal were compared. There was no generated model, full import graph, plugin, native output, navigation comparison, or Rust-to-Lean correspondence. I099/F19/I02 remain partial.
- **No whole-process write/read trace is claimed.** File inventories are SHA-256 snapshots of the producer and seeded cache before/after each cell. They detect net file creation and byte changes there, not transient writes, reads, writes outside those roots, or process launches. The network profile denied network capability but no independent attempted-connect control was run in this probe.
- **The seed producer was not resnapshotted after the cells.** The `Replayed Dep` command traces name `$WORK/seed/producer` paths even for private consumer cells. Each cell's copied producer and the shared cache were inventoried, but these snapshots cannot rule out accesses or changes to the original seed producer during replay.
- **Resource gates were preflight-only.** The script required at least 20% estimated free memory and 10 GiB free disk before its sequential run and gave each Lake command a 35-second timeout. It did not recheck the resource gates between cells or impose a single total-run timeout.
- **Operation ordering matters.** The no-build action ran before direct batch and live server for each cell. Those later commands can use existing OLeans or perform their own preparation. The direct batch's success in `no_source` did not repair Lake's failed preparation.
- **Artifact-cache state and mutable-tree writer state are separate.** This experiment used one cache producer and sequential fresh consumers with a non-writable cache policy. It did not race writers or test the shared writable package/build-tree interruption behavior of [I151](../anneal-3731-i151-matched-lake-writer-isolation-2026-09-29/REPORT.md).

## Evidence

- `support/probe.py`, SHA-256 `0b5dc8abace2ac483cf64f7cf783ce3bc878eabcf7b142c8d2c8b4e6b9e5d491`, creates the fixture, clean and seed states, six private fresh-consumer cells, preflight, bounded offline Lake calls, batch controls, LSP first-goal requests, and before/after SHA-256 inventories. It requires an absent scratch work path.
- `support/results.json`, SHA-256 `2b566c7e04e1cf94a270e64b35a3ddc17f3b49ca1c768a87beaf63d97dfda23e`, records the exact command labels, exits, streams, goal responses, relevant server notifications, preflight, tool hashes, selected removals, and inventories. Local work and toolchain paths are normalized to `$WORK` and `$TOOLCHAIN`.
- Local binary SHA-256 values in that run were Lake `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and Lean `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Tool versions printed `Lake version 5.0.0-src+3dc1a08 (Lean version 4.30.0-rc2)` and Lean commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- `support/check.py` checks the retained cell ordering, no-build commands and outcomes, selected artifact hashes, batch values and axiom result, live goals and missing-source diagnostics, and net producer/cache inventories. It requires only Python and does not replay Lake. It printed `Lake fresh-cache matrix assertions passed` on 2026-09-29.

## Revalidation

Run `python3 support/check.py` to verify the retained results without Lake. With the identified already installed local toolchain, run `python3 support/probe.py --work /new/absent/private/path --output /new/results.json` from a copy of this package. Compare action classes, no-build exits, batch value and axiom result, non-null goal text, the missing-source diagnostics, and producer/cache inventory deltas. For I089 and I099 at their requested scope, obtain the actual content-identified Anneal prepared archive and matching generated consumer, then repeat these operations with frozen dependencies, first-goal write tracing, and representative generated proofs. Do not infer those outcomes from this tiny fixture.
