# APFS sharing of a prepared Lean artifact: aliases, copies, and live readers

## Summary

On this Darwin 25.6.0 APFS host, a symlink and a hardlink to a writable producer `.olean` let a consumer overwrite the producer's bytes. A successful `/bin/cp -c` clone and an ordinary full copy gave separate files: the same consumer overwrite corrupted its own `.olean` but left the producer hash unchanged. Direct use of a producer file with mode `0444` allowed the initial read and rejected the tested in-place write. These are observations about one small artifact and one write path, not a general filesystem security or cache design guarantee.

## Applicability

The executable subject is Lean/Lake v4.30.0-rc2 at `leanprover/lean4` commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, on Darwin 25.6.0 arm64 with the fixture under `/System/Volumes/Data` (`diskutil` reported APFS). `lake build Dep --keep-toolchain --no-cache` produced a 4,608-byte `.olean` from `def depValue : Nat := 7`; a separately built `9` artifact supplied the replacement. Each mode had its own disposable producer file. A Lean consumer imported through `LEAN_PATH` and checked `depValue = 7` before mutation.

This tests one Lake-produced `.olean` shared into a direct Lean consumer, rather than a complete Lake package tree or an Anneal server. The report informs I119, the path-alias portion of I123, and the local APFS rename/unlink portion of I124 only partially.

## Findings

**Basis: execution.** In each mode, the first consumer read exited 0 and printed `7`. The controlled write opened the consumer-visible file as `r+b`, replaced byte zero, flushed, and called `fsync`. A fresh Lean read then exited 1 for each intentionally corrupted consumer artifact. `raw.json` preserves before/after hashes, inode/link counts, file inventories, commands, exit codes, and output.

| Consumer access | Before inventory: producer / alias | Write result | Producer after write | Meaning in this fixture |
| --- | --- | --- | --- | --- |
| Direct producer file, `0444` | 1 file, 4,608 logical bytes, 8,192 `st_blocks` bytes / no alias entry | `PermissionError`, errno 13 | SHA-256 unchanged; fresh Lean read `7` | File mode rejected this user's tested in-place write. |
| Symlink to writable producer | 1 file, 4,608 / 1 symlink (0 allocated bytes reported) | Succeeded | SHA-256 changed; fresh read fails | Path alias follows the producer file; it did not isolate bytes. |
| Hardlink to writable producer | 1 file, 4,608 / 1 file, 4,608; same inode, link count 2 | Succeeded | SHA-256 changed; fresh read fails | Both names reached one inode; it did not isolate bytes. |
| `/bin/cp -c` APFS clone | 1 file, 4,608 / 1 file, 4,608; distinct inodes | Succeeded | SHA-256 unchanged; alias read fails | This successful clone invocation isolated producer bytes under the tested overwrite. |
| Ordinary full copy | 1 file, 4,608 / 1 file, 4,608; distinct inodes | Succeeded | SHA-256 unchanged; alias read fails | Independent copy isolated producer bytes under the tested overwrite. |

The producer's starting `.olean` SHA-256 was `5a4030a600a43d13aa4b111bb81daae47c22636143a273da5e07dedc5916032f`. Symlink and hardlink writes changed it to `19d2d9c889780b68e6cd2ac447e073a8d02794418c6cefbc3d00d3e9c592b15a`; clone and full-copy writes changed only their alias to that latter hash. The `9` replacement artifact SHA-256 was `daa1410620b8f13f0bd2d958a30ed8cf0d9de8b5407abbef6a23774d8fba394d`.

**Basis: execution.** The file inventory reports logical bytes and `st_blocks * 512` per pathname. For hardlink, clone, and full copy, it reports 8,192 allocated bytes for each pathname. Those per-path `st_blocks` values cannot measure unique physical extents or APFS clone savings. The symlink entry reported 0 allocated bytes; directory metadata and APFS accounting were not measured. A clone's distinct inode plus successful `cp -c` and mutation isolation supports copy-on-write behavior here, but does not quantify saved physical storage.

**Basis: execution.** A live Lean process imported `Dep` from the `7` artifact, signaled readiness, and slept while the path was replaced with the `9` artifact via `os.replace`. It printed resident value `7`; a fresh process printed `9`. In the next run, a live process imported `9`, the path was unlinked, and the resident process still printed `9`; a fresh process failed with `unknown module prefix 'Dep'`. A separate explicit open-file-descriptor control read the old `7` bytes after path replacement with `9`, and read the `9` bytes after unlink; the path then did not exist. This distinguishes a resident import/open descriptor from fresh path resolution. It does not establish that Lean kept a file descriptor open after import.

## Boundaries

- I119 remains open for a complete prepared build tree, multiple artifact families, real consumer write patterns, physical APFS extent accounting, and throughput under load. Direct `0444` protects only this in-place write by this user; a writable parent directory, owner permission changes, or privileged writes can replace it.
- I123 remains open for case-folding, Unicode normalization, relative paths, multiple roots, module/document routing, and cache keys. This report exercised absolute symlink and hardlink aliases of one `.olean` only.
- I124 remains open for Windows, Linux, network filesystems, mapped artifact use, antivirus/indexer interference, locking, crash durability, and publication/cleanup races involving a full worker. The controlled rename/unlink result applies only to this APFS fixture. It does not prove atomicity to all concurrent readers or durable publication after a crash.
- No inference is made about security isolation against an adversarial process. The script uses the same user and writable disposable directories.

## Evidence

- Preserved executable harness: [`probe.py`](probe.py), SHA-256 `0a6de307f62e5334171360eaac343afcdae6ad58761ed02a9419f7fc9739d40b`.
- Sanitized command/output/inventory transcript: [`raw.json`](raw.json), SHA-256 `f487d10afd24d1f41e19c4637778ef95134ca75153925b8e905de52e897fa795`. `$WORK`, `$LEAN_BIN`, `$LEAN_HOME`, and `$HOME` replace local absolute paths in the transcript. The script itself specifies the pinned local toolchain path for replay; substitute an equivalent pinned installation if necessary.
- Pinned local `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`. Source SHA-256: `Dep.lean` with value 7 `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2`; value 9 `f24ea593a7ec12a08b2ab0c096b8babdbf9baeaef4c4a46286e12bf19959c0d0`; shared `lakefile.lean` `5d373bb5c2c0a8b1dec5d4e4c6eb731bc39ff9b58b44b0022f44c5ff6f8b3d36`.
- The harness was replayed once from this report package on 2026-09-29; the disposable generated `work/` tree was then removed. All five initial reads and expected mutations, plus resident/fresh reader and explicit descriptor controls, completed as recorded. The fixture sources are generated by the preserved harness.

## Revalidation

Run `python3 probe.py` on a disposable APFS directory with Lean/Lake v4.30.0-rc2 installed at the pinned path, or update `TOOLCHAIN` to an explicitly recorded replacement. The script recreates `work/`, writes sanitized `raw.json`, and prints a short result. Compare producer/alias hashes, inode/link counts, and resident/fresh reads; inspect `diskutil` and `df` results before applying this report to another volume. Remove the generated `work/` only after preserving any data needed for the new comparison.
