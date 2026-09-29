# Coherent capture of a multi-file tree under concurrent edits

## Summary

A gated reader of 256 source files, 32 generated outputs, two target files, and one symlink obtained a complete A manifest after it pinned an immutable generation directory, even while a writer changed a live tree and switched the selected generation to B. Resolving the `current` symlink separately for every entry produced a mixed inventory: early A source bytes, B generated output and symlink target, and a missing renamed source. A third run mutated the pinned A directory itself and its manifest check rejected the result. These observations extend the earlier two-file pointer-swap counterexample to a modest tree with a rename, symlink retarget, and generated-output change. They do not establish an Anneal capture implementation.

## Applicability

The fixture used CPython 3.14.7 on macOS 26.6.2 arm64 with an APFS data-volume temporary directory. The input was 256 4 KiB source files, 32 4 KiB generated outputs, `targets/alpha`, `targets/beta`, and a relative symlink called `link`. The two prebuilt generation directories had exact inventories. B changed source files 128–255, renamed `src/200.dat` to `src/200-renamed.dat`, changed `generated/010.bin`, and targeted `link` at `targets/beta` instead of `targets/alpha`. The writer also performed a real source rename, symlink replacement, and generated-output write in a separate mutable `live` directory while the reader was paused. Reader and writer ran in separate threads with events fixing their interleaving; filesystem reads, writes, rename, and `os.replace` were actual OS operations.

The fixture speaks to issue #3731 I010's capture-coherence question and the analogous #3730 A03 race suggestion. It is independent of the earlier `anneal-3730-snapshot-capture-jobs-2026-09-29` two-file probe. Generation names and hashes are fixture values, not Anneal or compiler identities.

## Findings

| Capture method | Retained result | Reason |
| --- | --- | --- |
| Re-resolve `current` for every path | Matched neither A nor B. `src/200.dat` was missing; the retained `link` target and generated output came from B. | The reader crossed the selection change after 128 source files. A single directory listing or per-file successful read cannot authorize a coherent multi-file subject. |
| Resolve `current` once to immutable A | Exact A inventory and manifest digest `c0c9132e1a83...`; no missing path. | Subsequent path opens stayed under A despite the B selection and live edits. |
| Resolve A once, then mutate A during the read | Matched neither manifest; `src/220.dat` differed from expected A. | Pinning a path is insufficient if its directory is writable during capture; the exact manifest check detected this injected violation. |

Basis: **execution** of `support/probe.py`, with exact key entries, manifests, and negative-control outcomes in `support/results.json`. The same script asserts the expected outcome for each trial. `support/check.py` independently checks the retained JSON without invoking the filesystem probe.

The useful design condition is that a coherent witness must bind selection to an immutable or equivalently protected file set and verify its expected inventory. The result does not show that this is the only valid capture design; a coordinated epoch or filesystem snapshot may supply another witness. Basis: **derived** from the paired positive and negative controls.

## Boundaries

- The source and output bytes are invented. No Rust, Charon, Aeneas, Lake, Lean, editor, or Anneal process read this tree.
- The symlink inventory records the link target string; the reader did not open through `link` or test symlink escapes, cycles, or adversarial path substitution. The B target was internal to the fixture.
- The `live` edits are actual concurrent filesystem activity but the successful reader consumed prebuilt immutable A. The experiment does not prove how to capture an arbitrary concurrently edited live source tree without a cooperating publication protocol.
- This was one bounded schedule on one APFS host. It does not establish crash or power-loss durability, cross-filesystem behavior, performance at production size, or a complete production input closure.
- The manifest is a syntactic exact-file/hash inventory. It does not attest semantic dependencies, options, environment, tool versions, or proof acceptance.

## Evidence

- `support/probe.py` (SHA-256 `fd362b30590020adbcf5cddcbd469bae78c346180d790cb17be5953ed3fa159c`) generates all inputs, gates the writer after 128 reads, records each trial, and asserts the result. It does not download or install anything.
- `support/results.json` (SHA-256 `8ac2a81b4190b5a1a4bcd8fa1595530a41d0fdf5776e257525317d4b5d470218`) retains the three inventories' manifest digests, selected paths, missing paths, key file hashes, symlink targets, and live-edit results. Scratch trees were deleted after capture.
- `support/check.py` checks the retained positive and negative outcomes. `anneal-3730-snapshot-capture-jobs-2026-09-29` supplies the earlier two-file comparison, with a different scope.
- The candidate checkout at observation was `a749b3e0787754aa00410900821baa4eb11104f6` on `reference`. The report package was local scratch output and was not published.

## Revalidation

Run `python3 support/check.py` to check the retained result. To repeat the OS experiment, set `ANNEAL_PROBE_SCRATCH` to an owned existing scratch directory and run `python3 support/probe.py`, then rerun the checker. A production capture design needs a real source/output closure, a source-authority protocol, path and symlink policy, and a fresh compiler/proof oracle for any accepted subject.
