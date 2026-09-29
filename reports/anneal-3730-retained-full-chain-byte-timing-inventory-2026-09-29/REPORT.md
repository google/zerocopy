# Retained one-worker full-chain byte and timing inventory

## Summary

The earlier `anneal-3730-full-lake-server-chain-2026-09-29` report retained a successful single Rust→Charon→Aeneas→direct Lean→Lake→live Lean→fresh batch chain but did not group every retained local byte/inode. This read-only analysis inventoried that exact saved worker tree and extracted its recorded stage times. The 54 regular files and one symlink total 4,524,103 logical bytes and 4,698,112 `st_blocks × 512` bytes. Three generated Lean modules appear byte-identically in the generator output, direct consumer and Lake project, totaling 3,364 extra logical bytes over one copy of each. The symlink points to a shared cached dependency package tree that is deliberately excluded from these worker-local totals.

## Method and results

`support/inventory.py` traversed only the retained `support/work/one/u0` tree of the cited package. It did not follow its `.lake/packages` symlink or rerun any compiler. Each retained file has relative path, family, logical size, allocated blocks, inode/device, link count and SHA-256 in `support/results.json`. The script also read the cited package's `support/results.json` with SHA-256 `8bb8a9d61054e8a6550b102c8985fc1befdac325d701c2814bc9bdc414b50f1c`; `support/check.py` checks all 55 saved path entries against that still-present evidence and the stage times. Neither script edits the source package.

| Retained family | Regular files | Symlinks | Logical bytes | `st_blocks × 512` bytes |
| --- | ---: | ---: | ---: | ---: |
| Rust crate and target | 3 | 0 | 418 | 12,288 |
| Charon LLBC | 1 | 0 | 16,087 | 16,384 |
| Aeneas generated source | 3 | 0 | 1,682 | 12,288 |
| Direct Lean consumer and artifacts | 7 | 0 | 28,422 | 49,152 |
| Lake project source/config | 6 | 0 | 5,829 | 24,576 |
| Lake local build and dependency symlink | 34 | 1 | 4,471,665 | 4,583,424 |
| **Total** | **54** | **1** | **4,524,103** | **4,698,112** |

The three duplicate source groups have exact lengths 20, 542, and 1,120 bytes, each at three distinct paths. Their hashes and paths appear in the saved JSON. Identical content is not proof that APFS physically shares their blocks. `st_blocks` is an allocated-block accounting number per inode, not exclusive physical extent usage or a peak-through-time measure.

| Retained timing field | Seconds |
| --- | ---: |
| Whole admitted one-worker cell | 54.754 |
| Direct Rust-through-Lean chain | 17.068 |
| Lake build | 12.045 |
| Fresh batch check | 7.256 |
| Wall time not assigned to those three non-overlapping aggregates | 18.385 |

The original JSON did not retain a separately isolated server-query elapsed interval; the 18.385-second remainder must **not** be labeled as server latency because it also includes setup, monitoring, copying, orchestration and other gaps. The sampled process-tree RSS peak was 2,590,336 KiB; the prior report explains its double-counting and admission limits. This is a timing partition of retained records, not a new measurement run.

## Coverage and limits

For #3731 **I113**, this adds an exact full-chain *retained worker-local* file/inode bill of materials to prior tiny direct-Lean worker inventories. It does not measure temporary peak bytes, outside-workspace writes, shared dependency store size, exclusive APFS extents, a second worker, or an Anneal generated workspace. The symlink's target is a cached package tree outside the worker and has no attributed bytes here.

For **I118**, it makes explicit which complete-chain stage aggregates are retained and which interval is unmeasured. It does not supply per-edit realistic latency, fine-grained Charon/Aeneas/query decomposition, warm/cold distributions, or bottleneck economics. The original single cell and resource gate remain the only execution evidence; this report reanalyzes its saved files and timings.

## Revalidation

Run `python3 support/check.py` to compare the saved inventory with the published source package. Run `python3 support/inventory.py` to recompute the inventory in place. The script is read-only with respect to the source package and writes only this package's `support/results.json`. Its SHA-256 is `7b843daa6a6396d74d325441fa23f917a6f9f8cbd632b86bf49c5edb6f5d904d`; retained result SHA-256 is `e1675db8fcdecefe3f3eb9d00abc1c11010eaa855aa67a0800ae5443d1fc3aef`.
