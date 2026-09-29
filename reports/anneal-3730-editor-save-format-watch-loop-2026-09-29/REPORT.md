# Direct Lean LSP and watched build loop under save, format, and overwrite events

Observed 2026-09-29 on macOS arm64. This is a bounded component experiment for issue #3731 I063 and the related #3730 editor/update crosswalk. It uses Lean 4.30.0-rc2 directly through `lean --server`, actual `lean -o/-i` compilations, and a Python hash-polling watcher. The Rust-to-Lean marker parser is an illustrative model; there is no Anneal generator, editor adapter, or product watcher in this probe.

## Fixture and event sequence

`support/probe.py` copies a one-theorem Lean file into private scratch, compiles it into private generation directories, and publishes `CURRENT_ARTIFACT.json` only after both `.olean` and `.ilean` are present. The pointer is the harness's consumed-artifact record. A source-hash poll suppresses duplicate events; a cancelled build remains retryable. Each build and LSP message is retained in `support/results.json`, including exact diagnostics, source hashes, stage files, and pointer values. Initial and final source/`.olean` files are retained in `support/artifacts/`.

| Step | LSP buffer / disk | Watch/build observation | Consumed `.olean` SHA-256 prefix |
|---|---|---|---|
| Initial | Version 1 `simp`, disk same; no diagnostics | Compile succeeds | `8ea70a281294` |
| Dirty edit | Version 2 `skip`, disk remains version 1; one `unsolved goals` error | Unchanged disk hash suppresses poll | `8ea70a281294` |
| Save invalid version 2 | Buffer and disk both `skip`; same error | Batch Lean exits 1; duplicate save event suppressed | `8ea70a281294` |
| External overwrite while version 2 remains open | Disk changes to `exact Nat.add_zero n`; open buffer retains version 2 error | Disk compile succeeds | `a787e416748d` |
| Close and reopen | Version 3 opens new disk text; no diagnostics | No further build | `a787e416748d` |
| `rustfmt` on Rust specimen | Formatter changes `Source.rs`, preserving `// lean-proof: simp`; illustrative marker output unchanged | Lean disk and consumed artifact unchanged | `a787e416748d` |
| Lean formatting edit | Version 4 and disk gain a blank line; no diagnostics | Rebuild succeeds; source hash changes, `.olean` and `.ilean` bytes match preceding build | `a787e416748d` |
| Cancel and retry | Version 5/disk use `simp only [Nat.add_zero]`; no diagnostics | Build process group killed with SIGKILL before completion; pointer stays old; same source retried successfully | `18fb83a0a6b6` |

The exact version 2 LSP error is `unsolved goals\nn : Nat\n⊢ n + 0 = n`, severity 1. Batch compilation of the saved version reports the same goal and exits 1. The direct LSP continued diagnosing its open version 2 buffer after the external disk overwrite and successful disk build. Closing and reopening the document at version 3 yielded empty diagnostics. The transcript proves a buffer/disk split for this Lean server session; it does not establish what any editor chooses to display or save.

The watcher rebuilds by source bytes, so a harmless blank-line edit caused a new build even though its `.olean` and `.ilean` hashes were unchanged. This separates **build trigger identity** from **artifact content identity**. The failing save and interrupted build did not replace the harness's consumed pointer. The next successful compilation did. This is a property of the probe's private-generation publication rule, not a guarantee of Lean's ordinary in-place output behavior.

## Replay and validation

From the repository checkout, run:

```sh
python3 reports/anneal-3730-editor-save-format-watch-loop-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new/empty-scratch-directory
python3 reports/anneal-3730-editor-save-format-watch-loop-2026-09-29/support/verify.py
```

The `--work` path must not exist; the script creates it and requires at least 15 GiB of free space as a conservative guard. It uses the pinned Lean executable and existing `/opt/homebrew/bin/rustfmt`; no installation is performed. The script records tool hashes and exits nonzero if the observed diagnostic/build sequence changes. The verifier checks saved raw evidence and retained artifact hashes. `results.json` includes the complete direct JSON-RPC transcript, compiler output, and source/artifact hash transitions. The private scratch build directory is not part of the persisted package.

## I063 coverage and remaining work

This covers a local, direct-tool slice: dirty buffer versus disk state, save failure, external overwrite while the same LSP document stays open, reopen reconciliation, actual Rust formatting, a Lean source formatting edit, duplicate event suppression, hash-triggered rebuild, cancellation, retry, and exact diagnostic/artifact attribution. The Rust formatter is real, but `// lean-proof:` is only a tiny model of a generator input. No Rust-to-LLBC-to-Lean regeneration was exercised.

I063 still requires an actual editor integration and Anneal watcher/generation pipeline to test event ordering, missed or coalesced OS notifications, multi-client buffer ownership, editor save/format semantics, generated-file/source-map updates, artifact-family publication and invalidation, and end-to-end diagnostics shown to a user. This experiment does not establish those behaviors. The process kill is a controlled cancellation, not a power-loss or crash-consistency test.
