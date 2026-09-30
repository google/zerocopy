# R511 RedLeaf and Linux Rust current-source review

## Summary

R511's version-inventory pin `551c722f40809618230001baccf219193e22fc5a` belongs to [`torvalds/linux`](https://github.com/torvalds/linux/commit/551c722f40809618230001baccf219193e22fc5a), not the RedLeaf paper-associated repository. The official Linux `HEAD` and `master` refs still equal that exact commit at the 2026-09-30 observation. Its five claim-mapped Linux files therefore have a zero-commit forward range and unchanged Git blobs. This is bounded source identity for R511's Rust-for-Linux evidence, not a runtime result or a new isolation guarantee.

RedLeaf's cited [`osdi20_camera_ready` branch](https://github.com/mars-research/redleaf/commit/08753faee652495f55fc8cbb420e5123a183affc) still equals R511's paper-associated source pin `08753faee652495f55fc8cbb420e5123a183affc`. Its default [`master`](https://github.com/mars-research/redleaf/commit/7194295d1968c8013ae6b3d104a9192f03516449) is on a **diverged** line (314 commits ahead, 1 behind in the old-branch-to-master comparison). It is not a proven forward successor to the paper-associated artifact. Five of R511's seven RedLeaf source paths are absent at that `master` commit, and the two surviving paths have different blobs. This is a path-level contrast across divergent histories, not evidence that the OSDI 2020 architecture evolved in a particular direction.

## Frozen claim and source map

The [R511 matrix](support/matrix.json) freezes the exact four Summary paragraphs, 14 Findings locators, original evidence map and comparison matrix, report hashes, source subjects, and section locator at reference `d8ebe60bc920363d4e43d95713e7e6a2de5363d7`. R511 is one row in the 581-report version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`; the frozen parent has 615 packages. All 34 additions are reconciled by path and hash.

The [official-source observation](support/official-source-observation.json) records independent [Linux refs](support/linux-refs.txt) and [RedLeaf refs](support/redleaf-refs.txt), direct commit-pinned source URLs, and preserved source snapshots. The five Linux files are `Documentation/rust/general-information.rst`, `rust/kernel/types.rs`, `rust/kernel/interop.rs`, `Documentation/rust/coding-guidelines.rst`, and `Documentation/userspace-api/seccomp_filter.rst`. Their preserved bytes reproduce the five old evidence-map Git blob SHA-1 values and have recorded SHA-256 hashes. Those files support only R511's cited wrapper, foreign-ownership, unsafe-contract, and seccomp-limit clauses under the unchanged Linux commit.

The seven paper-associated RedLeaf files are preserved at the pinned branch. At divergent `master`, `kernel/src/heap.rs` and `kernel/src/unwind.rs` still exist with changed blobs; the five cited `lib/core/...` paths returned 404. GitHub's compare returned its 300-file cap, so the changed-path list is incomplete and no repository-wide path conclusion is drawn from it. R511's OSDI paper remains the authority for publication-era design and evaluation, while the 2021 paper-associated source remains corroboration with its original date limitation.

## Release and tag observations

The official [kernel.org release feed](https://www.kernel.org/releases.json) identified latest stable `7.2.8` at the observation. That stable line is separate from this review's `torvalds/linux` development-branch source comparison. The official `torvalds/linux` [`v7.3-rc5` mainline tag](https://github.com/torvalds/linux/tree/v7.3-rc5) is annotated and peels to commit `72d3fcf802c45d00b300f25b848a93c3a2bd7c7e`, 37 commits behind the pinned/current `master`. Linux's GitHub `releases/latest` endpoint returned 404; the kernel.org feed and mainline tag provide the release context recorded here.

The RedLeaf GitHub `releases/latest` endpoint returned `bcache_v2`, published 2020-05-07. Its name and date do not identify it as a newer RedLeaf paper-architecture release, and this review does not use it as a successor to `osdi20_camera_ready`.

## Limits and revalidation

No Linux kernel, RedLeaf system, compiler component, or Anneal product was installed or executed. `runtime_result` is `unexecuted_in_this_review`; `anneal_product_result` is `unassessed`. No full source archive was acquired. The [offline checker](support/check_matrix.py) validates exact frozen R511 claims and source map, 581-to-615 corpus reconciliation, independent refs, mapped source blobs, bounded divergent-source observations, and the recorded Linux mainline tag. It cannot refresh live refs, prove the OSDI paper's source correspondence, or establish isolation behavior.

Run `python3 reports/redleaf-linux-current-source-review/support/check_matrix.py` from a checkout containing the frozen corpus commits. A stronger RedLeaf version comparison would first identify a genuine forward successor of the paper-associated branch and then inspect its claim-mapped mechanisms. Prompt/setup refinement: resolve which repository each short pin names, and classify divergent source histories before comparing path contents or making product claims.
