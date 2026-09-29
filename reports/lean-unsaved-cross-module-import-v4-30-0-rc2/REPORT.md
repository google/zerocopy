# Unsaved cross-module imports in an open Lean server

## Summary

In a direct Lean 4.30.0-rc2 `lean --server` session, an open proof file did not import the unsaved text of another open file. After the producer buffer changed from `sharedValue := 3` to `sharedValue := 4`, both the already-open proof and a newly opened proof still proved `sharedValue = 3` against the old `.olean`. An open producer that had no source file or `.olean` could not be imported at all: the consumer received `unknown module prefix 'OnlyBuffer'`.

Writing and compiling the changed producer produced a different `.olean`. A newly opened consumer and a closed/reopened consumer then reported a remaining goal, agreeing with fresh batch Lean's failure. The old consumer continued to answer from its old imported environment. The observed document and artifact boundaries distinguish these responses; two open buffers did not form one live cross-module environment in this fixture.

## Applicability

- Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release binary reporting `v4.30.0-rc2` on arm64 Apple Darwin.
- Launch: direct `lean --server`, with `LEAN_PATH` set to the two-module fixture directory and `LEAN_NUM_THREADS=1`. The client used file URIs, `didOpen`, a full-text `didChange`, `textDocument/waitForDiagnostics`, and `$/lean/plainGoal`.
- The initial source and compiled module defined `sharedValue : Nat := 3`. The producer's LSP buffer changed to `4` while its source and compiled artifact stayed at `3`. The proof text, `import Dep; theorem current : sharedValue = 3 := by rfl`, was unchanged throughout.
- This is the direct-server execution slice of #3731 I038. Related source/documentation synthesis is in `lean-generated-file-interactive-workflows-v4-30-0-rc2`; the distinct compiled-artifact refresh case is in `lean-same-server-dependency-generation-v4-30-0-rc2`.

## Findings

### Unsaved producer text was not an import input

Both `Dep.lean` and `Consumer.lean` were open. The producer was changed with one `didChange` to version 2 and `waitForDiagnostics` completed. The producer buffer hash was `c9d2489f2aab1d2e058b7952c3c179fa39a8b9ce2edcf63bb6d0070c27c0943d`, while on-disk `Dep.lean` retained `3f73ffee4b6b6612fd97b89a1a9f46db69eb6a200ce3f4d322fba02e803c0b60` and `Dep.olean` retained `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`.

The old consumer returned `no goals` before and after the producer edit. A second consumer opened **after** the unsaved producer edit also returned `no goals`. Batch Lean with the old artifact exited 0. Thus the new consumer did not silently import the producer's open-buffer definition of `4`; it matched the compiled definition of `3`.

Basis: **execution**, `support/transcript.json` and `support/check.py`.

### An import could not resolve an open-buffer-only producer

`OnlyBuffer.lean` was opened via `didOpen` with `def onlyBufferValue : Nat := 9` while neither its source path nor its `.olean` existed. A second open document importing `OnlyBuffer` received the diagnostic `unknown module prefix 'OnlyBuffer'` and named the missing `.olean`. Opening a producer buffer did not satisfy module resolution in this direct-server fixture.

Basis: **execution**, the `open_only_buffer` event and `ImportsOnlyBuffer.lean` diagnostics in `support/transcript.json`.

### Materializing the new artifact changed fresh consumers

The new producer source was written and compiled. Its `.olean` hash became `142f9093501e0337ed2634fe0070957086cead5140326fd70b7fc6c6e29bbaeb`. After a watched-file notification, the old consumer still returned `no goals`, while a third, newly opened consumer and a closed/reopened original consumer returned `⊢ sharedValue = 3`. Fresh batch Lean over the same proof exited 1 with an `rfl` tactic failure.

The proof hash remained `304bffdabf0dfc2274583df1773c83655d985883b359f889c56860b407660059` through both phases. The changed import artifact and the new-document or close/reopen boundary correlate with the contrast in this fixture. Internal worker generations were not instrumented.

Basis: **execution** for messages, artifacts, and batch outcomes; **derived** for the worker-generation interpretation.

## Boundaries

- This run did not use `lake serve`, `lake env lean --server`, `lake setup-file`, Mathlib, plugins, or an Anneal-generated project. Those modes may prepare imports differently.
- The probe used one producer and three consumers in one server, sequentially. It does not establish fanout, races, crash recovery, or performance behavior.
- It queried plain goals and diagnostics. InfoView RPC handles, save notifications, and client-specific editor behavior were not examined.
- The post-materialization old worker result is one observed stale-artifact case, not a universal rule for how every Lean client should trigger dependency refresh.
- The exact executable bytes were not hashed. The retained version output identifies the release and commit, while `LEAN_BIN` supplies the executable path on replay. The `.olean` files were recorded by hash but are not retained in this package.

## Evidence

- `support/probe.py` contains the exact source texts, subprocess calls, and LSP message sequence. It requires an already-installed pinned Lean binary through `LEAN_BIN` and no dependency installation.
- `support/transcript.json` retains all sent and received JSON-RPC messages in order, command outputs, document and artifact hashes, missing-file facts, and the Lean version. Local fixture and toolchain paths are replaced by `$FIXTURE`, `$LEAN_BIN`, and `$TOOLCHAIN`; message payloads and outcomes are otherwise preserved.
- The retained probe SHA-256 is `dfb4b0d6a351639d489dbc19ce80805d05b7b3b038b2a9ecb9bd21a8005a85d0`; the retained transcript SHA-256 is `0652723327833feb5ff3d5c9d1a7b1db6a60c409732ceb573697ac302e5ab379`.
- `support/check.py` asserts the document transition, request/reply order, hash separation, goals, diagnostics, and batch controls against that transcript. It printed `I038 transcript assertions passed` on 2026-09-29.

## Revalidation

Copy this package to a disposable directory to preserve its retained transcript. From that copy, set `LEAN_BIN` to the installed `v4.30.0-rc2` executable and run:

```console
LEAN_BIN=/absolute/path/to/lean python3 support/probe.py
python3 support/check.py
```

The probe creates `support/fixture` and rewrites the transcript. Compare the unsaved-buffer and artifact hashes first, then the old and newly opened consumers, the missing-module diagnostic, and batch exit statuses. Revalidate other launch modes independently rather than carrying this direct-server result over by assumption.
