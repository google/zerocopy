# Per-worker copied-byte inventory for a tiny Lean proof project

## Summary

A direct Lean 4.30.0-rc2 experiment built one 5-file dependency universe and one or two private proof workers on the local APFS Data volume. Each worker built and then batch-checked a generated `Proof.lean` against `Dep.olean` in a fresh process. The proof was accepted in every configuration, and all worker `Proof.olean` files had the same SHA-256. With ordinary byte copies, each worker added **5 dependency files, 6,189 payload bytes, and 24,576 bytes of `st_blocks` charge**. With a directory symlink to the shared universe, each worker added **zero dependency file payload bytes** and still built 7 private source/config/product files (5,810 payload bytes; 28,672 bytes of `st_blocks` charge). For two workers, the total regular-file payload bill was 30,187 bytes with copies and 17,809 bytes with symlinks: a 12,378-byte difference, precisely two copies of this tiny dependency set.

This is an executable accounting fixture for #3731 J02 and I113–I114, not an Anneal worker or Mathlib measurement. It identifies what was copied, what was linked, and what remained private; it does not establish APFS physical extent sharing or a production worker's memory/disk budget.

## Method and scope

The pinned binary was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `v4.30.0-rc2`, Lean SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Execution occurred on macOS arm64 in a private Meta/Data scratch directory, located by `df` on `/dev/disk3s1`; `diskutil info` reported APFS. Before the experiment, `df -h` showed about 51 GiB available. No backup volume or system tree was used as a test directory. Cases ran serially, with at most one Lean process at a time. No installation or cache download occurred.

The shared universe contained `Dep.lean` (`def depValue : Nat := 7`), compiled `Dep.olean`, `Dep.ilean`, `Dep.c`, and `lean-toolchain`. Each worker had a `Proof.lean` theorem of `depValue = 7`, a `lakefile.toml`, `lean-toolchain`, a tiny synthetic `anneal-manifest.json`, and private `Proof.olean`, `Proof.ilean`, `Proof.c` outputs. The proof was built with direct `lean --json -o -i -c`; a separate direct `lean --json Proof.lean` process checked the source again. The `lakefile.toml` is inventoried as configuration, but Lake was not invoked. The generator and manifest are synthetic stand-ins, not Anneal output.

Six cases used the same dependency and proof bytes: `cold-1` and `cold-2` wrote each dependency file by a read/write byte-copy loop into each worker; `warm-1` and `warm-2` linked each worker's `deps` directory to one shared universe; `hardlink-1` made hard links to the five shared files; `clone-1` used macOS `/bin/cp -c` for five APFS clone copies. Every case retained a producer-side shared universe, including the cold cases, so totals represent **producer plus worker** state. The cold-worker duplication is therefore visible rather than hidden by removing the producer. All paths were enumerated with `lstat` without following directory symlinks. The inventory records role, type, logical size, `st_blocks × 512`, device/inode, link count, SHA-256 for regular files, and symlink target. Every entry was assigned a role.

## Observed inventory

| Case | Workers | Regular files | Distinct inodes, all entries | Regular payload bytes | Regular `st_blocks` charge | Distinct-inode charge | Worker copied-dependency bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| cold-1 | 1 | 17 | 22 | 18,188 | 77,824 | 77,824 | 6,189 |
| cold-2 | 2 | 29 | 37 | 30,187 | 131,072 | 131,072 | 12,378 |
| warm-1, directory symlink | 1 | 12 | 17 | 11,999 | 53,248 | 53,248 | 0 |
| warm-2, directory symlinks | 2 | 19 | 27 | 17,809 | 81,920 | 81,920 | 0 |
| hardlink-1 | 1 | 17 | 17 | 18,188 | 77,824 | 53,248 | 6,189 apparent |
| clone-1, `cp -c` | 1 | 17 | 22 | 18,188 | 77,824 | 77,824 | 6,189 apparent |

The five shared regular files total 6,189 payload bytes and 24,576 bytes of file `st_blocks` charge: source 24 bytes, toolchain metadata 29 bytes, C artifact 1,295 bytes, ILean 289 bytes, and OLean 4,552 bytes. Each worker's seven private files total 5,810 payload bytes and 28,672 bytes of `st_blocks` charge: proof source 59 bytes, three local metadata/config files 122 bytes, and three proof outputs 5,629 bytes. Directory entries have zero reported `st_blocks` on this volume; symlink target text and inode metadata are **not** included in regular-file payload totals. The CSV includes all directories and symlinks so these namespace costs remain visible as entry/inode counts.

For the copy cases, each worker's five dependency files had distinct inodes from the shared originals and from the other worker; this was an actual byte-write copy loop. For the symlink cases, `deps` itself was one new symlink inode per worker, while resolving `deps/Dep.lean` reached the shared inode. For the hardlink case, the five worker paths were additional directory entries pointing at the **same five inodes** as the shared originals; summing `st_blocks` by path double-counted 24,576 bytes, and unique-inode accounting removed that duplication. Hard links also couple mutations and permissions at the inode level, so they are not by themselves a safe immutable boundary. In the clone case, `cp -c` produced five new inodes with identical SHA-256 contents. The clone's path-summed and distinct-inode `st_blocks` charges both read 77,824 bytes overall, but those counters cannot show whether APFS extents are shared. The experiment therefore does **not** treat that 24,576-byte apparent duplicate as proof of physically duplicated storage, nor treat the clone as proven zero-cost.

All six dependency universes had identical hashes for each of the five files. All 8 worker builds and 8 fresh checks exited 0 with no Lean JSON diagnostics; each `Proof.olean` hash was `0167443fca001f19617fd0734b02d3f965448348e5a70c02fadc1cf2829d8305`. The inventory therefore compares equivalent tiny proof content across link modes, rather than merely comparing empty directory layouts. It does not show safe concurrent writes to any shared file: all shared dependency artifacts were constructed before workers started and were consumed read-only by the serial Lean commands.

## Interpretation and residual work

The observed one-worker marginal regular-file bill is 11,999 payload bytes for a cold copied worker (6,189 dependency plus 5,810 private) versus 5,810 private payload bytes for a warm symlink worker. At two workers, the cold configuration's additional regular payload above its retained producer is 23,998 bytes; the warm configuration's is 11,620 bytes. These figures exclude the Lean toolchain, library imports, runtime memory, page cache, clone extent sharing, directory metadata blocks, temporary peak bytes, and any remote/cache transfer. They also assume one shared universe is already produced: its 6,189 payload bytes remain in all totals.

For J02/I113–I114, the unresolved production question is an **Anneal-generated** worker's complete copied-byte and inode inventory with its actual Mathlib/Lean/Lake dependency graph, setup files, build products, temporary files, and simultaneous cold/warm workers. This tiny direct-Lean fixture cannot give a Mathlib scaling factor, APFS clone physical savings, or peak write amplification. A production follow-up should walk the real generated workspace and shared archive with the same path/role/inode ledger, capture writes and temporary peaks, and use a filesystem extent-aware or volume-level controlled measurement if physical clone savings matter. It should also verify that immutable shared dependencies cannot be mutated through worker paths and that each worker's mutable outputs are isolated.

## Reproduction and evidence

[`support/probe.py`](support/probe.py) constructs all six cases, runs the pinned Lean command and fresh check, inventories every path, and writes [`support/results.json`](support/results.json) plus [`support/inventory.csv`](support/inventory.csv). The JSON retains command arguments, exit status, stdout/stderr, dependency hashes, inode identities, and aggregate counters. Run it with an absent work path on the same local APFS volume:

```console
python3 support/probe.py --lean /absolute/path/to/pinned/lean --work /owned/absent/work --out /owned/output
python3 support/check.py
```

[`support/check.py`](support/check.py) recalculates all six summaries from the CSV and checks role coverage, hashes, proof acceptance, copy/link inode relationships, and two-worker arithmetic. The retained result was checked with this script and with `tools/reference.py` package loading. The raw work trees remain in the conversation-owned Meta/Data scratch area; no fixture touched backup volumes.
