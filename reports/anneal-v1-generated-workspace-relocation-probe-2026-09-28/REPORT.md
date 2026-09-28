# V1 generated workspace relocation execution probe

## Summary

V1 `cargo-anneal generate` created a small Lean workspace using the current V1 generator and a scratch-only local toolchain layout. Moving the generated directory without changing its Lake manifest made its relative dependency paths resolve to the wrong location; offline Lake loading failed immediately with “package directory not found.” Recomputing those manifest paths for the moved workspace allowed `lake --keep-toolchain --old --offline build Generated Anneal` to complete successfully with 1,688 Lake jobs. The log includes replay/build activity and warnings about existing `sorry` declarations and a reducibility annotation. This confirms that workspace-only relocation can work after location-bearing manifest paths are repaired while the toolchain stays fixed; it does not establish zero network attempts or proof correctness.

## Applicability

V1 source is `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, tool package version `cargo-anneal 0.1.0-alpha.24`. The fixture was a one-function Rust library with an empty Anneal proof annotation. Tools were linked into an isolated scratch installation path; Aeneas' release tree and Lean 4.30.0-rc2 were from local assets. To satisfy the V1 generator's manifest contract, the scratch Aeneas package manifest was temporarily converted from Git entries to local path entries and then restored. This is a local shim, not a production archive.

## Findings

### Generated paths are tied to the final generation location

The `generate` command succeeded and emitted the Lean workspace beneath a Cargo target directory. Its Lake manifest contains relative entries for Aeneas and all inherited path packages. Moving the directory to a different depth changed the interpretation of each relative `dir`; without regeneration or repair, `lake --keep-toolchain --old --offline build Generated Anneal` failed at the Aeneas directory lookup. The failure occurred before the build could establish whether prebuilt outputs were reusable.

Basis: execution; raw generator output and stale-move exit/stdout/stderr are preserved in `v1-execution/`.

### Re-seeding the manifest reaches Lake but did not validate reuse

After recalculating each manifest `dir` relative to the moved workspace while leaving the toolchain in place, the offline Lake build exited 0 after 1,688 jobs. At an intermediate sample the Lake process tree used about 1.26 GB RSS; it later completed, and system free memory returned to 48%. Disk free space was about 54 GiB. The generated `Generated` target was built; the log also reports pre-existing admitted declarations in dependencies. This is direct evidence that a corrected workspace-relative manifest can support a successful workspace-only move in this shim environment, not a production archive guarantee.

Basis: execution.

### V1 also embeds toolchain paths in generated configuration

The generated Lakefile's direct `require aeneas from ...` is an absolute path to the installed toolchain. This probe moved the workspace but left the toolchain at its original path, so it does not test moving the archive/toolchain. Relocating both requires regenerating the Lakefile and manifest or otherwise rebinding those paths.

Basis: execution + current V1 source.

## Boundaries

The re-seeded post-move Lake build completed, but `setup-file` and `lean --json` were not run on the moved workspace. The scratch toolchain is symlink-based and differs from a frozen official omnibus archive; package caches were not verified as read-only. Network isolation was not supplied by the test harness, although the Lake invocations used `--offline`. Existing `sorry` warnings mean a successful Lake build is not proof success.

## Evidence

- V1 source: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, particularly `anneal/v1/src/aeneas.rs` manifest generation and final directory swap.
- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Preserved command outputs, fixture, generated Lakefile, and moved/reseeded manifest: `v1-execution/`. The full 1,188-line Lake build output ends with `Build completed successfully (1688 jobs)` and exit code 0.
- V1 source coordinates: `anneal/v1/src/aeneas.rs` (workspace generation, generated Lakefile, manifest rewrite, directory swap) and `anneal/v1/src/setup.rs` (`ANNEAL_TOOLCHAIN_DIR` resolution) at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`. Lake config/build behavior is covered by `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

## Revalidation

Build a real immutable V1 archive with its exact manifest and prebuilt outputs; generate one tiny workspace at A; move it to B; first confirm the stale manifest fails, then regenerate only location-bearing state (Lakefile and manifest) for B before any Lake load. Run `--no-build`, `--old build`, `setup-file`, and batch JSON diagnostics with verified network denial, recording producer hashes/mtimes and full exit status. Test workspace-only and toolchain-plus-workspace relocation as separate cases.
