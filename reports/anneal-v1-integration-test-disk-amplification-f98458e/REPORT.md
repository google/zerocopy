# Anneal v1 integration-test worker-cache disk amplification

## Summary

Anneal's April 2026 integration-test harness briefly isolated concurrent Lean tests by allocating a persistent worker cache to each active worker. Each worker owned a mutable copy-shaped view of Aeneas's Lean tree and `.lake` state. The implementation avoided copying many large immutable files by symlinking them, but it still replicated mutable metadata and filesystem structure per worker. The pool itself scaled with machine concurrency: it used roughly 1.5 times the available CPU parallelism, capped by an estimate of one worker per 2 GiB of available RAM.

PR #3305 records the operational failure that motivated removing this design: one specific run with roughly 100 parallel worker threads and caches consumed roughly 100 GB of disk. That number is historical incident evidence, not a reproduced benchmark or a claim of exactly 1 GB per worker. The durable lesson is architectural: when many independent Lake consumers need isolation, cloning a broad package/cache tree per worker can multiply filesystem state with concurrency even if the heaviest immutable artifacts are shared indirectly.

The replacement separated ownership domains. PR #3304 moved Aeneas from a directly shared filesystem dependency to a local `file://` Git dependency so each workspace could own mutable checkout state while sharing content-addressed build artifacts. PR #3305 then deleted the flock-guarded worker pool and smart-clone machinery and made tests consume the shared Lake artifact cache. PR #3306 extended local-source materialization to transitive Lean dependencies. Later Anneal work moved farther toward an immutable prepared archive plus workspace-owned Lake state. Current retained v1 at `41f5b37afe7060fd9fe08c00b200672cd76d77b9` no longer contains `WorkerCacheGuard`, `acquire_worker_cache`, `smart_clone_cache`, or `worker_caches`.

## Applicability

The historical implementation described here is the tree immediately before PR #3305, `google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94`, principally `anneal/tests/integration.rs`. The removal is commit `f98458e7eaf54ff34b69e417ee34e79036f06547`, merged as PR #3305 on 2026-04-21.

The approximately 100-worker / 100-GB observation comes from the PR #3305 description and commit message. It applies to a reported integration-test run of this historical architecture. The preserved evidence does not identify the exact host filesystem, exact worker count, exact test selection, preexisting cache contents, or a `du` breakdown. Do not generalize the number into a stable bytes-per-worker coefficient.

The report also examines current retained v1 at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` only to establish that this worker-cache architecture is historical. Current v1 uses the prepared archive and workspace-local state instead; this report does not attempt to characterize the current architecture exhaustively.

## Findings

### The worker pool existed to isolate mutable Lake state

Before PR #3305, every non-mock integration test acquired a `WorkerCacheGuard`. `acquire_worker_cache` maintained persistent directories under `target/worker_caches/<worker>/` and protected each one with an exclusive file lock. A test held that guard for the lifetime of its `TestContext`, so only one test could mutate a worker cache at a time.

The comments state the reason directly: integration tests compiled and manipulated shared Lean environments, so the harness needed isolation to avoid races. The pool was an ownership mechanism, not merely a performance cache.

Basis: **source** at `google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94`, `anneal/tests/integration.rs`, `WorkerCacheGuard`, `acquire_worker_cache`, and `TestContext::new`.

### Pool capacity grew with host concurrency

`acquire_worker_cache` started from `std::thread::available_parallelism()`, multiplied that count by 1.5, rounded up, then capped the result with `calculate_dynamic_lean_concurrency_limit()`. That memory cap divided Linux `MemAvailable` by 2 GiB per Lean worker and fell back to four workers if `/proc/meminfo` was unavailable.

The source therefore made the number of persistent worker directories a function of host resources. On a large machine, the harness intentionally created enough independent mutable cache domains to support high test concurrency.

Basis: **source** at the pre-#3305 revision. The scaling consequence is **derived** directly from the pool-size formula and the per-worker directory layout.

### Each worker materialized broad Aeneas and Lake trees

On first use of a worker, the harness created two persistent subtrees:

- `aeneas/backends/lean`, cloned from the installed Aeneas Lean backend; and
- `lean_lake`, cloned from the backend's `.lake` directory when present.

`smart_clone_cache` did not blindly deep-copy every byte. It recursively recreated directories, symlinked `.git/objects`, copied files classified as mutable metadata, and symlinked other files. The copied class included files anywhere under `.git`, plus extensions such as `.trace`, `.json`, `.hash`, and `.log`, and `lake.lock`. Other ordinary files were symlinked back to the source tree.

That distinction matters. The failure should not be summarized as “100 complete deep copies of every `.olean`.” The implementation was already trying to share heavyweight immutable files. Disk still scaled badly because each worker reproduced a broad package/cache namespace and copied the state it expected Lake might mutate.

Basis: **source** in `smart_clone_cache` at the pre-#3305 revision; **derived** for the distinction between shared immutable bytes and replicated worker-owned state.

### A test also reused the worker's mutable `.lake` directory as its workspace cache

For a normal test, `TestContext::new` copied the toolchain's `lake-manifest.json`, modified it to inject Aeneas, then symlinked the test workspace's `.lake` path to `worker_cache.lean_lake`. The comment says this avoided copying `.lake` for every individual test while relying on the worker lock to grant exclusive mutation rights.

The architecture therefore had two levels:

1. each test got a fresh sandbox;
2. tests serialized through a bounded pool of persistent mutable Lean/Lake caches.

This reduced per-test copying, but the persistent pool still multiplied cache state by the maximum concurrent worker count.

Basis: **source** in `TestContext::new` at the pre-#3305 revision.

### The observed disk failure was about the aggregate worker-cache architecture

PR #3305 states that the prior worker-pool and symlinking infrastructure “required large amounts of disk space,” giving a specific run with approximately 100 parallel worker threads and caches that consumed approximately 100 GB. The same change removed `WorkerCacheGuard`, `acquire_worker_cache`, `calculate_dynamic_lean_concurrency_limit`, and `smart_clone_cache` from the integration harness.

The source diff and incident description align: the code being deleted was exactly the concurrency-isolation layer that created one persistent cache domain per worker. The evidence does not isolate which replicated file classes contributed what fraction of the 100 GB, so attributing the entire total to any one of Git metadata, Lake traces/configuration, generated files, directory entries, or other mutable state would exceed the evidence.

Basis: **documentation** in PR #3305 and the commit message for `f98458e7eaf54ff34b69e417ee34e79036f06547`; **source** in that commit's deletion of the worker-cache implementation.

### The replacement changed the ownership model, not just the copy primitive

PR #3304 preceded #3305 by changing Aeneas from a non-Git filesystem dependency into a local `file://` Git dependency and populating a shared Lake artifact cache. Its description explains the concurrency motivation: treating the installed Aeneas tree as a directly shared path dependency let Lake mutate user-global state and produced races between concurrent Anneal commands.

With a local Git remote, a workspace could own the mutable checkout state while reusable compiled artifacts lived in the shared content-addressed cache. PR #3305 could then remove the test-only worker cache instead of finding a more elaborate way to clone it. PR #3306 subsequently initialized transitive Lean dependencies as local Git repositories so Lake could clone them from the local filesystem rather than the network.

The progression separates three concerns that the worker cache had coupled:

- immutable compiled artifacts can be shared globally;
- mutable checkout/workspace state needs an owner;
- source materialization can be local without being one shared writable tree.

Basis: **documentation + source history** from PRs #3304, #3305, and #3306. The three-way separation is **derived** from those changes and their stated motivations.

### Later Anneal work retained the ownership lesson while changing the mechanism again

Issue #3668 reconstructs the later Lake-integration history. It records the 100-worker / 100-GB incident, then describes subsequent designs that reduced repeated materialization and eventually moved preparation into a Nix-built archive. The current model aims for an immutable prepared dependency universe plus mutable state owned by each generated workspace.

At current main `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/v1/tests/integration.rs` contains no `WorkerCacheGuard`, `acquire_worker_cache`, `smart_clone_cache`, or `worker_caches`. Its archive-consumption regression path asserts that the installed archive has no write bits and runs Lake with `--keep-toolchain --old`. Current `anneal/v1/src/aeneas.rs` generates a complete manifest and invokes `lake --keep-toolchain --old build Generated Anneal` against the prepared toolchain.

The historical failure therefore remains relevant as a constraint on future redesigns, not as a description of current v1 behavior: do not reintroduce isolation by cloning a large prepared dependency/cache universe once per parallel consumer.

Basis: **documentation** in issue #3668 plus **source** at current main. The final design constraint is **derived** from the historical failure and current ownership separation.

## Boundaries

**The 100 GB figure was not reproduced.** This investigation recovered the contemporaneous PR/commit statement and the implementation it referred to. It did not run the old integration suite or measure disk usage.

**The figure is approximate.** The source says a “specific run” with approximately 100 parallel worker threads and caches consumed approximately 100 GB. No exact worker count, baseline disk use, filesystem, sparse-file/reflink behavior, or before/after `du` output was preserved in the evidence examined here.

**The report does not assign the bytes to individual file classes.** `smart_clone_cache` symlinked many immutable files and copied mutable-looking metadata. The aggregate incident does not establish which copied state dominated disk usage.

**PR #3297 was an unmerged exploratory implementation.** Its description independently characterizes the old design as a flock-guarded worker pool that cloned the Lean backend per worker and proposed Lake's artifact cache as the replacement. The merged transition documented here is #3304/#3305/#3306; #3297 is corroborating design history, not part of the canonical merged sequence.

**Later designs had their own materialization costs.** Issue #3668 records a subsequent stage in which verification copied an approximately 5 GB dependency tree containing about 5,000 `.olean` files per workspace before later optimizations. That is a distinct architecture and failure mode; do not merge its measurements with the #3305 incident.

**Current v1 is sampled only enough to establish non-applicability of the old worker pool.** This report is not a complete account of current Lake caching, relocation, read-only behavior, or archive pruning.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary historical source before removal:

- `google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94`, `anneal/tests/integration.rs`, blob `55c9d14f8dbf01e1643cf67013ad24841177188c`.
  - `WorkerCacheGuard` and `acquire_worker_cache`: per-worker lock and persistent cache directories.
  - `calculate_dynamic_lean_concurrency_limit`: 2 GiB available-memory budget per worker and fallback of four.
  - `TestContext::new`: every normal test acquires a worker and symlinks the worker's `.lake` into its fresh sandbox.
  - `smart_clone_cache`: copies mutable metadata, symlinks other files, and symlinks `.git/objects`.

Removal and incident record:

- `google/zerocopy@f98458e7eaf54ff34b69e417ee34e79036f06547`, merged PR #3305, “[anneal] Cleanup test infrastructure and implement atomic setup.” The commit message records the approximately 100-worker / 100-GB run and says removal of the worker pool/cache cloning saves substantial integration-test disk use. The diff deletes the worker-cache machinery above.

Related ownership transition:

- PR #3304, head/merged commit `69e77a55f1b80f051b9dd9555363d2e074c48d3a`: switches Aeneas to a local-filesystem Git dependency and shared Lake artifact cache; its description identifies races caused by treating a user-global directory as writable shared path-dependency state.
- PR #3306, head/merged commit `37d1fef927ec84a9086312ad1bb9840c205b0d87`: recursively initializes transitive Lean dependencies as local Git repositories so later Lake clones can remain local rather than network-backed.
- PR #3297, unmerged head `aa4ef2afe4d36fcc078b8ce3fb6dac8fb21aa03b`: corroborating experiment that explicitly describes replacing the flock-guarded per-worker Lean clone pool with Lake's content-addressed artifact cache.

Historical synthesis:

- `google/zerocopy` issue #3668, “Clarify and simplify Anneal's Lake integration,” observed at `updated_at=2026-09-11T19:04:53Z`. Its historical section records the worker-pool incident and connects #3297, #3304, #3305, and #3306 to the later immutable-archive/workspace-state design.

Current non-applicability check:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/v1/tests/integration.rs`, blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`: no `WorkerCacheGuard`, `acquire_worker_cache`, `smart_clone_cache`, or `worker_caches`; archive regression path checks read-only permissions and invokes Lake with `--keep-toolchain --old`.
- Same revision, `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: current generated-manifest and Lake invocation path.

Evidence roles are **source**, **documentation**, and **derived**. There is no fresh **execution** evidence in this report.

## Revalidation

To confirm the historical claim, inspect commit `f98458e7eaf54ff34b69e417ee34e79036f06547`: its message preserves the incident measurement, and its integration-test diff shows the worker-pool implementation being removed. Then inspect parent/base snapshot `d410c162d51977635ca5afac67d99a3b10327a94` for `WorkerCacheGuard`, `acquire_worker_cache`, `calculate_dynamic_lean_concurrency_limit`, and `smart_clone_cache`.

To detect accidental architectural regression in a future Anneal revision, a cheap source probe is to search the integration/verification paths for any mechanism that creates one broad dependency/cache copy per concurrent worker. Do not search only for the historical symbol names; the invariant is about ownership and scaling, not naming.

If a future design again materializes per-worker package state, the decisive execution probe is to run the integration suite at increasing worker counts on a clean filesystem and record both peak disk usage and a per-directory breakdown. Measure separately:

1. shared immutable artifact storage;
2. source checkouts;
3. package/configuration metadata and traces;
4. workspace-generated outputs; and
5. any per-worker retained state.

That experiment can distinguish unavoidable shared corpus size from disk amplification proportional to concurrency. A passing single-worker run does not test the failure mode preserved here.
