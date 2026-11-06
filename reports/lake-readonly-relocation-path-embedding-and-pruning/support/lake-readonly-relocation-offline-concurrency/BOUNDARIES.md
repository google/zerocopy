# Boundaries

## No fresh execution

This report did not run Lake, Lean, Aeneas, Nix, or Anneal. The exact v4.30.0-rc2 conclusions about control flow, filesystem operations, cache behavior, and locking come from pinned source inspection. Historical Anneal tests and PR descriptions record prior execution-oriented work, but they are not a substitute for rerunning the exact current-pin experiment.

Accordingly, this report does **not** establish that:

- an arbitrary v4.30.0-rc2 Lake project can be relocated without rebuilding;
- an arbitrary prebuilt package tree can be made read-only and consumed successfully;
- `lake build` performs zero network operations for a given prepared environment;
- a particular cache-seeded build is semantically equivalent to a clean build;
- two arbitrary `lake` processes may safely write the same workspace, package tree, build directory, or cache directory concurrently; or
- Lake's source-level race handling covers every relevant filesystem and platform behavior.

## Historical Anneal evidence is configuration-specific

The checked-in V1 archive regression test belongs to the historical Anneal design under `anneal/v1/`. It depends on an installed Nix-built archive, a particular manifest construction, prepared Lake outputs, `--old`, scrubbed environment variables, and archive preparation rules. It should not be generalized beyond that configuration without reproducing its prerequisites.

In particular, current V1 source removes `CI` before running Lake because Aeneas package configuration historically depended on that environment variable. If the producer and consumer observe different package configuration, Lake can invalidate the prebuilt result and attempt writes in the read-only archive. That example is evidence that environment-dependent package configuration belongs in the prepared-state contract, not evidence that `CI` is the only such dependency.

## Relative paths cover dependency materialization, not every artifact

Lake's manifest path entries are relative, and source code deliberately keeps some path-changing compiler arguments out of strong rebuild traces. This report does not contain a complete inventory of absolute-path material in every generated setup file, native object, `.olean`, `.ilean`, trace payload, compiler diagnostic, or third-party package artifact. The relocation claim is therefore deliberately limited to the dependency-resolution layer plus the historical Anneal design evidence.

## Cache concurrency is not whole-workspace concurrency

The artifact cache contains explicit race-tolerant operations, and cache-map files use file locking. Other cache files and package-local build state use different mechanisms. The report does not infer a global transactional or linearizable cache protocol from those local protections.

## Network denial was not observed

Source inspection identifies several paths that can require network access: Git clone/fetch, Reservoir resolution, and remote artifact-cache download. It also identifies conditions that avoid those paths. A strong “offline” result still requires running the exact prepared environment with network access denied or instrumented, because absence of a source-level reason to fetch is not the same as observing zero network attempts.

## Platform scope

The source revision is cross-platform, but filesystem semantics differ across Unix, macOS, and Windows. Hard-link behavior, permissions, rename atomicity, advisory locks, path syntax, case sensitivity, and executable-bit handling can change observed outcomes. The preserved Anneal V1 read-only assertion uses Unix permission bits and does not establish an equivalent Windows contract.