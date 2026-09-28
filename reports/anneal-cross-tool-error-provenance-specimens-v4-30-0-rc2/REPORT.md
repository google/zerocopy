# Cross-tool error and provenance specimens for Anneal translation

## Summary

The preserved specimen set follows supported and unsupported Rust fixtures across rustc/Charon, Aeneas, and Lean, and keeps transport/setup errors separate from compiler diagnostics. Supported examples complete the intended stages; explicit unsupported pointer cases retain Aeneas error messages and Rust source locations. Lean batch JSON and LSP diagnostics can be compared after normalizing their coordinate bases, but cancellation and process failures are separate events and must not be fabricated into source diagnostics.

## Applicability

Current Charon/Aeneas subjects are `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`. Lean is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. The specimens were run with the local macOS arm64 release/toolchain bundle. They are diagnostic-provenance fixtures, not a proof of source/model correspondence or a complete supported-Rust survey.

## Findings

### Pipeline specimen classes

The execution suite covers ordinary arithmetic/control flow and mutation, closure, trait, loop, type alias namespace behavior, raw pointers, function pointers, and name collisions. Charon records source contents and spans in LLBC. Aeneas emits Lean for supported cases; unsupported raw-pointer/function-pointer cases produce explicit errors with source locations. A type-alias case fails under a default generated namespace and succeeds when the namespace override is supplied, demonstrating a translation/setup distinction rather than a Rust type-check failure.

Basis: execution. The raw specimen records and coverage tables are preserved in `specimens/`.

### Batch diagnostics and LSP results have different coordinate and lifecycle contracts

For a matching Lean file and imports, batch `lean --json` messages and LSP diagnostics can be compared by severity, message, and source range. Lean batch locations are one-based; LSP ranges are zero-based. Preserve each original range and retain the conversion explicitly. A matching final diagnostic set does not mean a server was queried at the correct document version: the request must follow `didOpen`/`didChange` and the awaited diagnostics for that version before querying tactic state.

Basis: execution + source. Batch/LSP comparison details are in `lean-comparisons.json`.

### Errors carry stage and evidence identity

A usable record distinguishes at least: rustc rejection; Charon failure/panic; Charon success with `has_errors`; Aeneas translation error; generated Lean parse/elaboration error; LSP JSON-RPC cancellation (`-32800`); timeout/crash/setup failure; and verified completion. The transport/setup classes have no Lean source span unless a specific source diagnostic was also returned. A cancellation is an incomplete attempt, not proof failure or success.

Basis: source + execution + derived taxonomy. Concurrent LSP event specimen is `lsp-two-events.json`.

### MCP boundary

No MCP bridge is present in the examined Anneal source checkout. This report does not invent MCP behavior; any future adapter should preserve the same stage, document version, input hashes, error class, and source-map identity.

## Boundaries

The matrix uses a small hand-selected set. It does not exhaust Charon/rustc failure modes, malformed LLBC, all source-map expansion cases, or every Lean diagnostic encoding. Batch and LSP equality is only meaningful with equal file bytes, imports, options, toolchain, working directory, and environment. MCP integration remains untested because no adapter is implemented in this subject.

## Evidence

- Zerocopy source and V1 implementation context: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.
- Charon: `charon-lang/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`; Aeneas: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Preserved evidence: `specimens/RESULTS.md`, `coverage.json`, `canonical-order-check.json`, `lean-comparisons.json`, `lsp-two-events.json`.
- Diagnostic/source-map implementation coordinates: Charon `charon/src/bin/charon-driver/main.rs` and `charon/src/errors.rs` at `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`; Aeneas `src/Errors.ml` and `src/Main.ml` at `ac9f1bc5262a5e4ff1e24ca78617121382202727`; Lean `src/Lean/Message.lean` and `src/Lean/Shell.lean` at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; V1 mapping `anneal/v1/src/diagnostics.rs` and JSON ingestion `anneal/v1/src/aeneas.rs` at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.

## Revalidation

Run every fixture end to end and preserve Rust bytes, LLBC, generated Lean, raw stderr/JSON, source maps, tool identities, and exit codes. Compare batch and LSP only after matching inputs/environment; convert spans without discarding original coordinates. Inject cancellation and restart explicitly, and record them as transport events. Add MCP tests only after the adapter and its protocol implementation are identified.
