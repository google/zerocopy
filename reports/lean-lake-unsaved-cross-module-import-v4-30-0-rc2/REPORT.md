# Unsaved producer imports through Lake's Lean server

## Summary

In a tiny dependency-free Lake project launched with pinned `lake serve`, editing an open producer's LSP buffer did not change the imported environment of either a resident or newly opened consumer. Both continued to prove `sharedValue = 3` while the unsaved producer buffer defined `sharedValue := 4` and the compiled `.olean` still defined `3`. After the producer source was written and rebuilt with Lake, a newly opened and a closed/reopened consumer reported the remaining goal `⊢ sharedValue = 3`, agreeing with failing batch Lean. The resident consumer still returned `no goals` and received an imports-out-of-date diagnostic.

This is a measured `lake serve` complement to `lean-unsaved-cross-module-import-v4-30-0-rc2`, which used direct `lean --server`. The two reports agree for these minimal fixtures, while retaining their distinct launch and artifact preparation paths.

## Applicability

- Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, installed release binaries reporting Lean `v4.30.0-rc2` and Lake `5.0.0-src+3dc1a08` on arm64 Apple Darwin.
- Launch: `lake --keep-toolchain --no-cache serve` in a local project with `lean-toolchain` pinned to `leanprover/lean4:v4.30.0-rc2`, `lean_lib Dep`, and `lean_lib Consumer`. No remote dependencies were declared or installed. Builds used the same Lake binary with `--keep-toolchain --no-cache`; batch controls used `lake ... env lean --json`.
- Environment: `LEAN_NUM_THREADS=1`, `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`, `LAKE_CACHE_DIR=""`, and `LAKE_ARTIFACT_CACHE=false`. One server session ran sequentially with the producer and consumer documents concurrently open; internal file-worker identities were not recorded. Disk and memory preflight recorded 49,409,810,432 bytes available and 45% reported free memory on the accepted run.
- Fixture: the producer's version-1 source and compiled module set `sharedValue : Nat := 3`; its version-2 LSP buffer set `4`. The unchanged consumer was `import Dep; theorem current : sharedValue = 3 := by rfl`.

## Findings

### The open producer buffer was not imported by a fresh Lake consumer

Both producer and original consumer were open. After the only `didChange` in the run advanced `Dep.lean` to buffer version 2, `waitForDiagnostics` completed for that producer. The buffer SHA-256 was `c9d2489f2aab1d2e058b7952c3c179fa39a8b9ce2edcf63bb6d0070c27c0943d`; disk `Dep.lean` still had `3f73ffee4b6b6612fd97b89a1a9f46db69eb6a200ce3f4d322fba02e803c0b60`, and `.lake/build/lib/lean/Dep.olean` still had `edb5a5815bd08ea4a0a1011bd155ba187c92cac7c84ebcc2a63cf2f8dfae0bf4`.

The resident consumer's plain goal result was `no goals` before and after the producer edit. Another consumer opened after that edit also returned `no goals`; a batch check against the old artifact exited 0. The fresh consumer result is the discriminating observation: Lake's file-specific preparation did not import `Dep` from its open, unsaved LSP buffer in this fixture.

Basis: **execution**, the ordered messages, hashes, and command results in `support/transcript.json`.

### Rebuilt imports reached fresh workers, while the resident worker stayed old

Writing the producer's `4` source and running `lake --keep-toolchain --no-cache build Dep` changed the imported `.olean` hash to `606f9991b03bfcc24fefc5070bfb6f434ba7377de57541085d271e8eb21552c2`. The consumer text hash remained `304bffdabf0dfc2274583df1773c83655d985883b359f889c56860b407660059`.

After a `workspace/didChangeWatchedFiles` notification, the resident consumer still returned `no goals` and an `Imports are out of date and should be rebuilt` diagnostic was observed. A new consumer and a closed/reopened original consumer each returned `⊢ sharedValue = 3`; the new consumer also received an `rfl` error diagnostic. `lake env lean --json Consumer.lean` exited 1 with the same `rfl` failure. The watcher notification has no completion acknowledgment, so the transcript establishes the observed sequence rather than a guaranteed refresh latency or ordering rule.

Basis: **execution** for the outcomes; **derived** for describing the old and new workers as holding distinct imported generations.

## Boundaries

- This is a local, dependency-free two-module Lake fixture. It does not establish the behavior of Mathlib projects, plugins, generated Anneal packages, concurrent workspaces, or other Lean/Lake versions.
- The unsaved-only, nonexistent producer import case is measured in the companion direct-server report, not here. This Lake run begins with a valid prebuilt `.olean`.
- The run uses plain goals and diagnostics. InfoView RPC handles, editor-specific save behavior, and a complete dependency-refresh protocol were not tested.
- The probe did not record SHA-256 hashes of the Lean or Lake executable. The retained version output and launch path identify the installed toolchain used; exact executable bytes are not attested in this package.
- One accepted run followed a corrected JSON-RPC harness. The first failed attempt is not retained here, so its specific events cannot be independently audited. The preserved transcript has no fatal event and covers the corrected run only; this review did not replay or overwrite it.

## Evidence

- `support/probe.py` (SHA-256 `6813d11267d0b9fb220a20ea7a07cf256bc9c55e48a7f07895db60f4410107d9`) constructs the project, performs disk/memory preflight, builds the old and new artifacts, conducts the ordered LSP session, and runs two batch controls. It requires only the already-installed pinned `lean` and adjacent `lake` binaries.
- `support/transcript.json` (SHA-256 `27571384be052ed23502f45917a46896671a046e9226e53c8f905f9652035bb6`) retains the accepted run's sent and received JSON-RPC messages, Lake and Lean command outputs, source and artifact hashes, preflight, and version strings. Local fixture and toolchain path prefixes are replaced with `$FIXTURE`, `$LEAN_BIN`, `$LAKE_BIN`, and `$TOOLCHAIN`.
- `support/check.py` checks the exact launch commands, producer-only edit, request/reply and diagnostic order, hash separation, resident/fresh/reopened goal contrast, batch controls, and clean server exit. It printed `Lake I038 transcript assertions passed` on 2026-09-29.

## Revalidation

Copy this package to a disposable directory to preserve the retained transcript. From that copy, point `LEAN_BIN` at an installed `v4.30.0-rc2` Lean executable with `lake` beside it and run:

```console
LEAN_BIN=/absolute/path/to/lean python3 support/probe.py
python3 support/check.py
```

The probe creates `support/fixture` and rewrites the transcript. Inspect the preflight and initial `.olean`, verify that only the producer buffer changes before the first fresh consumer opens, then compare goals and batch results after Lake rebuilds the artifact. Treat each server launch mode as a separate observation.
