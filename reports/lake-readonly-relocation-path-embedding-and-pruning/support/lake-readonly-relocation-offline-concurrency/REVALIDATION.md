# Revalidation

## Cheapest source check after a Lake update

Before rerunning experiments on a later Lean/Lake revision, diff these areas against the pinned blobs from this report:

1. `Lake/Load/Manifest.lean`, `Load/Resolve.lean`, `Load/Materialize.lean`, and `Load/Workspace.lean` — relative-path semantics, locked materialization, clone/fetch behavior, and missing-manifest fallback;
2. `Lake/CLI/Main.lean` and `CLI/Init.lean` — whether `--offline` is propagated into ordinary workspace/build operations;
3. `Lake/Config/{Env,PackageConfig,Monad,Cache}.lean` — cache read/write defaults, cache paths, output mappings, and locking;
4. `Lake/Build/{Common,Actions,Trace}.lean` — package-local writes, trace/hash writes, artifact restore/download paths, and path-sensitive rebuild inputs; and
5. `Lake/Util/Lock.lean` — whether Lake has introduced a global or workspace build lock.

Any change in those areas can invalidate one or more findings independently.

## Minimal exact-pin probe suite

Use a capable surface with the exact `v4.30.0-rc2` toolchain. Build one tiny package plus one dependency, then preserve a prepared fixture and run the following as separate experiments. Record all filesystem writes and attempted network connections rather than inferring them from success.

### Probe A: relative relocation

1. Prepare a complete workspace with a locked manifest whose path dependencies are relative.
2. Build it once.
3. Copy or rename the entire fixture under a different absolute root while preserving relative topology.
4. Make the prepared dependency tree read-only but leave the generated root workspace writable.
5. Run the target build and Lean diagnostics.
6. Record whether any target rebuilds, any old absolute path is consulted, and every changed file.

Repeat with a substantially different root length/name to catch embedded-path assumptions.

### Probe B: read-only package consumption

Run the relocated fixture under a write-auditing sandbox. Fail the test on any attempted write below the prepared dependency tree. Exercise at least:

- a fully warm cache;
- missing `.hash` files;
- missing `.trace` files;
- a missing locally restored artifact;
- a changed package-configuration environment value; and
- both normal hash mode and `--old`.

The baseline should succeed only in the state the production contract actually promises. The perturbations should demonstrate the specific fallback writes that the contract excludes.

### Probe C: hard offline operation

Run the baseline in a network-denied namespace or equivalent interception environment. Capture failed connection attempts as failures even if Lake later recovers.

Then remove one prerequisite at a time:

- a locked Git dependency checkout;
- a required local cache artifact;
- the manifest;
- a local filesystem Git remote; and
- any Reservoir-resolved dependency state.

This distinguishes “works without network in the prepared state” from “Lake has an offline mode that forbids network”.

### Probe D: concurrent read-only consumers

Create N independent writable root workspaces that all reference the same read-only prepared dependency universe and, if intended by the design, the same read-only artifact cache. Run builds/diagnostics concurrently under write auditing. Verify:

- no writes target the shared dependency tree;
- no process requires a mutable shared package build directory;
- cache reads remain correct under concurrency; and
- outputs match the single-consumer baseline.

### Probe E: deliberately shared writable state

Only if Anneal intends to rely on it, separately run two or more Lake processes against the same writable cache or package/build tree. Stress interruption and simultaneous cache misses. Treat this as a different contract from Probe D. The source in this report does not justify assuming success.

## Preserve a compact fixture

If the exact-pin probes succeed, retain the fixture generator, network-denial wrapper, write-audit wrapper, concurrency driver, and machine-readable list of observed writes. That probe is the cheapest future discriminator when Lake changes.

For Anneal, the most useful regression contract is not merely “the command exited 0.” It is:

- exact prepared-state identity;
- whether the dependency tree was writable;
- whether any writes occurred below it;
- whether any network attempt occurred;
- whether any dependency or build target rebuilt;
- which cache locations were read or written; and
- whether concurrent outputs were equivalent to the single-run baseline.