# June 8 Anneal Build And Setup Investigation

## Summary

The v1 symlink complexity is avoidable. A small reproducible Lake experiment in
`micro-lake-experiments/` verifies a symlink-free strategy that matches the v2
archive design:

- keep the installed archive as the single copy of Aeneas and its Lake path
  dependencies;
- have generated v1 workspaces require Aeneas directly from the installed
  archive;
- keep archive `.lake/build` artifacts read-only and shared;
- make only tiny archive `.lake/config` directories writable so Lake can take
  package config locks; and
- remove per-workspace copying and `.lake/build` symlinking.

The experiment also verified the important negative case: a completely
read-only direct archive fails because Lake tries to create a lock file under
the dependency package's `.lake/config` directory.

## Existing v1 Behavior

Current v1 consumes the v2-style archive, but then reconstructs much of the
archive layout inside each generated Lean workspace:

1. Copy `aeneas/backends/lean` from the installed toolchain into
   `lean/vendor/aeneas/backends/lean`.
2. Copy `aeneas/packages` into `lean/vendor/aeneas/packages`.
3. Preserve ordinary symlinks.
4. Replace copied package `.lake/build` directories with symlinks back to the
   installed archive's `.lake/build` directories.
5. Make copied files writable.
6. Normalize copied Lake input mtimes to the Unix epoch.
7. Run `lake --old build Generated Anneal`.

The symlinks avoid copying several GiB of prebuilt `.olean` artifacts into each
generated workspace. The mtime normalization exists because copied source/config
files would otherwise be newer than the read-only archive build cache, causing
Lake to invalidate or delete artifacts through those symlinks.

## How This Maps To v2

The v2 `flake.nix` already prepares most of the desired archive state:

- dependencies are vendored as path packages under `aeneas/packages`;
- package `.lake/build` directories are seeded with prebuilt cache artifacts;
- Lake requirements and manifests are rewritten to path dependencies;
- trace paths are rewritten to avoid non-portable absolute Nix/build paths;
- source/config mtimes are normalized before `lake --old build`;
- unused artifacts are pruned; and
- the final archive is made read-only.

The gap is not `.lake/build`. The gap is Lake's package configuration area.
When a generated workspace requires `aeneas/backends/lean` directly as a path
dependency, Lake creates or locks files under:

```text
aeneas/backends/lean/.lake/config/aeneas/
```

A fully read-only archive therefore fails before it can replay the already
valid `.lake/build` artifacts.

## New Experiment

I added:

```text
../micro-lake-experiments/experiments/test-symlink-free-toolchain-path.sh
../micro-lake-experiments/artifacts/symlink_free_toolchain_path_analysis.md
```

The script builds a small Anneal-shaped archive fixture:

```text
archive/
  aeneas/
    backends/lean/        # package "aeneas"
    packages/MiniDep/     # transitive path dependency
```

It then:

1. prebuilds the archive packages;
2. rewrites traces to package-relative paths;
3. primes Lake package config while the archive is writable;
4. makes the archive fully read-only;
5. verifies the fully read-only negative control fails on
   `.lake/config/aeneas/lakefile.olean.lock`;
6. makes only `.lake/config` writable;
7. builds two generated workspaces at different paths that require Aeneas
   directly from the archive; and
8. verifies there are no symlinks and no generated-workspace vendor copies.

The successful builds replayed prebuilt archive artifacts:

```text
Replayed MiniDep.Basic
Replayed Aeneas
Built Generated
```

Post-run checks:

- writable files under archive `.lake/build`: `0`
- symlinks under the test fixture: `0`
- writable paths under archive `.lake/config`: `8`
- generated workspace vendor directory: absent

## Implemented v1 Fix

The implementation follows the experiment, with two extra fixes discovered by
running a real v1 example against the Nix-built archive:

1. The v2 archive build primes Aeneas package config for dependency use before
   final archive packaging.
2. The v2 trace rewriter strips upstream Aeneas release trace prefixes ending
   in `backends/lean/`. Without this, Aeneas traces retained paths such as
   `/var/lib/.../dist_staging/backends/lean/AeneasMeta/Utils.lean`, and v1
   invalidated the archive cache.
3. Setup/install restores write permission to archive `.lake/config`
   directories and creates missing config dirs for older installed archives.
4. Setup/install normalizes Lean/Lake source/config input mtimes to the Unix
   epoch while leaving `.lake/build` artifacts read-only.
5. v1 `aeneas.rs` writes `require aeneas from
   "<installed>/aeneas/backends/lean"` directly.
6. v1 no longer copies `aeneas/backends/lean` or `aeneas/packages` into the
   generated workspace.
7. v1 no longer creates `.lake/build` symlinks.
8. v1 no longer preserves `lake-manifest.json` across workspace regeneration,
   because the direct Aeneas dependency path includes the active setup
   location. Preserving the manifest can point Lake at a stale toolchain root.

This should reduce v1 complexity and improve setup/build behavior:

- no per-run tree copy of Aeneas and packages;
- no symlink creation or symlink portability concerns;
- no per-run mtime mutation of copied package inputs;
- no large cache copy;
- package artifacts are still replayed from the shared installed archive; and
- only generated project files are built in each v1 workspace.

## Real Archive Verification

The full Nix archive path was verified after implementation:

```text
nix build ./anneal/v2#omnibus-archive-layout-check --print-build-logs
```

This built the local archive, replayed Aeneas in the config-primer workspace,
rewrote traces, pruned Mathlib, compressed the archive, and passed the updated
layout check requiring:

```text
aeneas/backends/lean/.lake/config/aeneas/lakefile.olean
```

Setup was then tested against the built archive:

```text
ANNEAL_TOOLCHAIN_DIR=/tmp/anneal-toolchain-test... \
cargo run --manifest-path anneal/Cargo.toml -- \
  setup --local-archive /nix/store/...-anneal-toolchain-omnibus-0.1.0
```

Observed setup properties:

- setup time: about 48 seconds for the 1.35 GiB archive;
- writable files under installed archive `.lake/build`: `0`;
- installed archive source input mtime: Unix epoch;
- installed archive build artifact mtime: preserved archive timestamp;
- `aeneas/backends/lean/.lake/config/aeneas` writable: yes.

The `checked_add` example then verified successfully:

```text
ANNEAL_TOOLCHAIN_DIR=/tmp/anneal-toolchain-test... \
cargo run --manifest-path anneal/Cargo.toml -- \
  verify --manifest-path anneal/Cargo.toml --example checked_add --allow-sorry
```

First successful run after the fixes took about 13 seconds. A second run took
about 6.6 seconds. The generated workspace had:

- no `vendor/` directory;
- no symlinks; and
- a generated `lakefile.lean` requiring Aeneas directly from the installed
  archive path.

Additional checks run:

```text
python3 -m unittest discover -s anneal/v2/tests -p 'test_*.py'
cargo test --manifest-path anneal/Cargo.toml setup::tests -- --nocapture
cargo test --manifest-path anneal/Cargo.toml --bin cargo-anneal
bash anneal/v2/check-flake-eval.sh
```

## Remaining Verification

The implementation is now tested against both tiny packages and the full local
Nix archive. Remaining useful checks are broader rather than blocking:

- concurrent v1 runs, since the installed archive will have a small shared
  writable `.lake/config` surface; and
- full GitHub workflow validation across all runner platforms.
