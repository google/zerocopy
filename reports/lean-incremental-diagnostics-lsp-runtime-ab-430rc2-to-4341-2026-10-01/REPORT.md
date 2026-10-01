# Lean incremental diagnostic publication: serialized LSP runtime A/B

## Result

The installed Lean 4.30.0-rc2 and 4.34.1 servers both produced the expected diagnostics for the published two-line open/edit fixture. In the six serialized LSP sessions, 4.30.0-rc2 published full replacement arrays with no `isIncremental` field for all three capability settings. Lean 4.34.1 also published full replacement arrays when the capability was absent or false. With `lean.incrementalDiagnosticSupport: true`, its two substantive publications had `isIncremental: false`; no `isIncremental: true` append publication occurred. **This fixture did not exercise the opt-in append branch described by the source-level comparison.** It confirms runtime recognition of the true capability through the `false` marker and the fallback replacement behavior, not runtime append behavior.

## Scope and identities

The fixture was read from the existing `lean-incremental-diagnostics-430rc2-to-4341-source-delta-2026-10-01/fixture` package; it was not modified. `Open.lean` is `#check unknownA` followed by `#check unknownB`; `Edited.lean` changes the first line to `#check Nat.zero` and retains the second. Their SHA-256 values are `d42fbf3d79611aa442bb233680e4f20af6848dc8f1f0c7be3c3dd4df22b5dcc7` and `9caea97a94d2d9d37a3cb507278414674d173507a0ebf9db9e3c5024dc3ebfeb`, respectively.

| Server | `lean --version` commit | `bin/lean` SHA-256 |
| --- | --- | --- |
| 4.30.0-rc2 | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` |
| 4.34.1 | `5045d0056413266e57c625dcd7c365b10e377c52` | `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` |

The client sent `initialize` with the `lean` capability absent, `incrementalDiagnosticSupport: false`, or `incrementalDiagnosticSupport: true`; then `initialized`, `didOpen` version 1, `textDocument/waitForDiagnostics` version 1, `didChange` with the full edited text as version 2, another wait request, `didClose`, `shutdown`, and `exit`. Each case used a fresh server and a distinct in-memory `Probe.lean` URI inside its private evidence directory. Only one server ran at a time. The script used direct `lean --server`, with `LEAN_NUM_THREADS=1`; it did not invoke Lake or build a project.

## Ordered diagnostic publications

Each cell lists `version:diagnostic count` in arrival order. The final zero-count version-2 publication is the close clear. The full notifications, client request order, exact LSP stdout bytes, and server stderr are in `raw/<case>/`.

| Server / capability | Ordered `publishDiagnostics` counts | `isIncremental` on substantive publications | Peak sampled server-group RSS |
| --- | --- | --- | ---: |
| 4.30 / absent | `1:0, 1:0, 1:1, 1:2, 2:2, 2:0` | absent | 293,328 KiB |
| 4.30 / false | `1:0, 1:2, 2:2, 2:0` | absent | 226,688 KiB |
| 4.30 / true | `1:0, 1:2, 2:2, 2:0` | absent | 227,248 KiB |
| 4.34 / absent | `1:0, 1:0, 1:1, 1:2, 2:2, 2:0` | absent | 319,024 KiB |
| 4.34 / false | `1:0, 1:2, 2:2, 2:0` | absent | 248,208 KiB |
| 4.34 / true | `1:0, 1:2, 2:2, 2:0` | `false`, `false` | 248,320 KiB |

The first two cold sessions (old/absent and new/absent) visibly accumulated version-1 diagnostics in separate publications: one error for `unknownA`, then the full two-error array. The other sessions emitted both errors together. This timing difference is an observed delivery pattern, not a claim that the absent capability caused it. In every case, the final version-1 array has the two `lean.unknownIdentifier` errors, at line 0 and line 1. The substantive version-2 array has a severity-3 `Nat.zero : Nat` diagnostic at line 0 and the severity-1 `unknownB` error at line 1. All six final arrays agree on messages, severities, ranges, and codes. The `readout.json` file preserves the per-notification diagnostics and ordering.

## Batch comparison and resource control

Direct batch invocations of each binary on both original fixture files returned 1 because each file retains at least one unknown identifier. Both versions printed the same two unknown-identifier errors for `Open.lean`; both printed `Nat.zero : Nat` and the `unknownB` error for `Edited.lean`. Exact stdout, stderr, arguments, hashes, exit codes, and elapsed time are in the four `raw/batch-*` directories. These CLI observations agree with the final LSP diagnostic messages, allowing for CLI formatting and the LSP informational diagnostic for `#check` output.

The user waived the earlier >30% RAM admission threshold for this isolated probe. `memory_pressure -Q` reported 50–53% free during the six server sessions; the lowest sampled value was 50%. The harness sampled each server process group and would stop its own group above 1,536 MiB RSS or below 10% reported free memory. No guard fired. All six servers answered `shutdown`, exited with code 0 after `exit`, and left no process-group members. A post-run process inventory found no probe Lean processes; see `raw/cleanup.json`. The resource samples and case summaries are in each `raw/<case>/resources.jsonl` and `summary.json`.

## Evidence and limits

`probe.py` is the exact client used. Each `events.jsonl` records client messages and parsed server messages in observed order with timestamps; `server.stdout.lsp` retains the exact framed server byte stream. An independent pass parsed every complete frame and confirmed its count matched the corresponding ordered server events (16 or 25 frames by case). `readout.json` is derived from those raw events. No shared publication checkout, fixture, toolchain, or admin configuration was changed.

The present fixture cannot establish whether or when the 4.34.1 server emits `isIncremental: true` with a capable client. The earlier source report explains that branch; this runtime A/B shows the fallback path actually taken by this fixture.

The exact fixture files are also copied under [`support/fixture/`](support/fixture/) for detached validation. Run `python3 -B support/check.py` from this package to verify fixture hashes, complete LSP frame parsing and event correspondence, clean summaries, the opt-in false-marker observation, and batch output hashes. The checker is offline and does not launch Lean.
