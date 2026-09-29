# APFS and cached Ubuntu overlayfs resource accounting for a bounded proof workspace

Observed 2026-09-29 on the local macOS arm64 APFS Data volume and the already cached Ubuntu 24.04 container in OrbStack. This is R40 for the #3730 J14 filesystem-specific scaling question and #3731 I119/I124, with supporting relevance to I113/I115 resource budgets. It compares counters for a tiny Anneal-like file tree; it does not measure Anneal itself or a large Mathlib environment.

## Fixture and methods

`support/fixture/` retains real pinned Lean `Dep.olean` and `Plugin.olean` from the earlier filesystem-lifetime experiment. `support/probe.py` adds eight deterministic, incompressible-looking 256 KiB blobs to represent dependency/cache payloads and a small `Proof.lean`. The base tree has 11 regular files and 2,147,019 logical bytes. On each filesystem it creates a full copy, requests a clone/reflink copy, adds a read-only hardlink to `Dep.olean`, and changes 4 KiB in one cloned blob. The base blob hash is checked before and after mutation.

The host side uses `/bin/cp -c` for each APFS clone. The Ubuntu side uses GNU `cp -a --reflink=always`; that command exited 0, so this run did not use the ordinary-copy fallback. The cached image identity was `sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254`. Docker reported its host driver as `overlayfs`; `/tmp` inside the `linux/amd64` container also reported `overlayfs`. The container was started with `--pull=never --network=none --memory=512m --cpus=1` and removed afterward. No image pull, package install, host bind mount, or backup volume was used.

For both filesystems, the transcript records each file's logical length, `st_blocks × 512`, device/inode/link count, and tree totals. APFS snapshots also record `statvfs` volume-available bytes. Linux snapshots record GNU `du -B1`, `df -B1`, and Docker `inspect --size` writable-layer `SizeRw`. These counters have different accounting semantics: summing per-file blocks double-counts shared extents and hardlinks; `SizeRw` is a Docker layer-accounting number, not an attested physical allocation; the host volume-free counter can include unrelated writes during the run.

## Observed counters

| Phase | Tree logical bytes | Summed file blocks, either filesystem | APFS volume-free change from previous phase | Docker `SizeRw` change |
|---|---:|---:|---:|---:|
| Base | 2,147,019 | 2,158,592 | 2,162,688 | 2,158,592 |
| Full copy added | 4,294,038 | 4,317,184 | 2,162,688 | 2,158,592 |
| Clone/reflink added | 6,441,057 | 6,475,776 | 8,192 | 2,158,592 |
| `Dep.olean` hardlink added | 6,445,609 | 6,483,968 | 0 | 0 |
| 4 KiB clone write | 6,445,609 | 6,483,968 | 16,384 | 0 |

The full copy cost about one base-tree allocation in the APFS volume-available counter, while the APFS clone cost 8 KiB during this short run. Per-file `st_blocks` nevertheless rose by a full tree after the clone, so that sum is not an exclusive-physical-byte measure on APFS. In the container, `--reflink=always` succeeded and mutation left the base blob unchanged, but `du`, per-file blocks, and Docker `SizeRw` each rose by a full tree at clone time; container `df` did not change at its displayed granularity. Those counters do not establish whether the underlying overlayfs backing extents were physically shared or what their exclusive storage cost was. A storage-budget implementation must name the counter it uses and validate it for the actual host/storage driver.

The read-only `Dep.olean` hardlink had the same device/inode and link count 2 as its base file on both filesystems. It added 4,552 logical bytes to a path-sum and another 8,192 bytes to summed file blocks, but no measured APFS volume-free or Docker `SizeRw` increment. Treating that path-sum as new storage would overcharge it. The hardlink was never mutated because a writable shared inode would also change the base dependency.

## Reproduction and validation

From the checkout, with the existing local Docker/OrbStack and cached image:

```sh
python3 reports/anneal-3730-apfs-overlayfs-resource-accounting-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new-APFS-scratch-directory
python3 reports/anneal-3730-apfs-overlayfs-resource-accounting-2026-09-29/support/verify.py
```

The work path must not exist, reside on the host Data APFS volume, and have at least 15 GiB free. The probe checks the mounted filesystem and fails if the cached image or overlayfs is unavailable; it does not pull or install a substitute. The first command writes `support/results.json` with 50 labeled host/Docker commands, per-file ledgers, counters, hashes, and cleanup record. The verifier checks the retained fixture hashes, ledger arithmetic, hardlink identity, base isolation after mutation, clone counters, container constraints, and successful removal. The exact volume-free deltas are observations from this run, not replay invariants under concurrent host activity.

The verifier requires the APFS available-byte readings to be present, but does not impose a threshold on their phase-to-phase deltas.

## Coverage boundary

This supplies an APFS-versus-cached-overlayfs accounting counterexample for J14/I119/I124: logical size, per-file blocks, APFS free-space changes, and Docker writable-layer size answer different resource questions, especially with clones and hardlinks. It informs I113/I115 budgeting for immutable dependency trees and private worker copies. It does not measure unique physical extents on overlayfs, concurrent multi-GiB jobs, memory pressure from real Lean workers, package-cache GC, copy-up from lower image layers, shared writable build products, backup/network filesystems, or Anneal's actual layout. Those remain separate integration measurements.
