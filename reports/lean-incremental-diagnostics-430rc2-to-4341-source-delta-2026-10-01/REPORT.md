# Lean incremental diagnostic publication: 4.30.0-rc2 to 4.34.1

## Result

The exact Lean 4.34.1 source adds an opt-in diagnostic publication mode absent from the Anneal-pinned Lean 4.30.0-rc2 source. In 4.30, `FileWorker.publishDiagnostics` concatenates sticky and document diagnostics and sends that full array on every publication. In 4.34.1, a client can set `lean.incrementalDiagnosticSupport` in its initialization capabilities. The server then sends a full replacement first and may subsequently send only newly accumulated document diagnostics with `isIncremental: true`; clients must append those to the diagnostics for that document version. If the capability is absent or false, the 4.34.1 source continues to send full replacement arrays without the extension field. A newly added sticky diagnostic resets the next publication to a full replacement.

**This is a source-level behavior difference, not an observed server transcript.** No Lean process or LSP server was launched for this comparison. A fresh resource check found approximately 22–25% reclaimable RAM, below the guarded runtime probe's >30% admission threshold. The two existing fixture files remain unexecuted.

## Exact scope and evidence

| Lean source | 4.30.0-rc2 | 4.34.1 |
| --- | --- | --- |
| Commit | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `5045d0056413266e57c625dcd7c365b10e377c52` |
| `src/Lean/Data/Lsp/Capabilities.lean` blob | `886e54140b4571bfc1e6b28fcb75ad196df0199e` | `12eec11b4270702ec13990fce25913b7f1c67ba4` |
| `src/Lean/Data/Lsp/Diagnostics.lean` blob | `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34` | `9353793f7316dca0ba36b16a9fd6cec46e487441` |
| `src/Lean/Server/FileWorker.lean` blob | `c803034ed8810f13a5ef38a603a21e610efca2bc` | `cf8058ac800a67394e26aa4752539ddd979877c1` |
| `src/Lean/Server/FileWorker/Utils.lean` blob | `824a52e3de861ffbdde9597078d7946cb0306436` | `e46f44a1599800a6bd6bedb8db9729235d37f49e` |

The [4.30 `FileWorker` implementation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L208-L226) constructs `stickyInteractiveDiagnostics ++ docInteractiveDiagnostics` and passes the resulting array to `mkPublishDiagnosticsNotification`. The [4.34 capability definition](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Data/Lsp/Capabilities.lean#L66-L98) defaults `incrementalDiagnosticSupport?` to `none` and resolves absent or false support to `false`. The [4.34 notification type](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Data/Lsp/Diagnostics.lean#L159-L171) adds optional `isIncremental?`; that field is absent from the 4.30 type. The [4.34 `FileWorker` call](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Server/FileWorker.lean#L207-L213) passes resolved support into [`EditableDocumentCore.publishDiagnostics`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Server/FileWorker/Utils.lean#L120-L160).

In that new publisher, `useIncremental := incrementalDiagnosticSupport && ds.isIncremental`. Its incremental branch emits entries after `publishedDiagsAmount` and marks the notification `some true`; its fallback emits sticky plus all document diagnostics and marks a capable client's notification `some false`. Without capability, the marker is `none`. Per-version state starts non-incremental; a sticky diagnostic resets it. The publisher holds the diagnostics mutex across state update and write, explicitly to preserve order between concurrent publishers. The [4.34 protocol overview](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Server/ProtocolOverview.lean#L153-L159) documents the append contract.

The pre-existing `reference` packages `reports/lean-diagnostic-objects-severity-v4-30-0-rc2` and `reports/lean-server-concurrency-experiment-v4-30-0-rc2` describe the pinned diagnostic model and direct 4.30 LSP observations. This report adds the exact newer-source delta. It does not extend those runtime observations to 4.34.1 or establish what a particular editor advertises.

## Reproduction and remaining experiment

Run `python3 support/check.py --source-root /path/to/lean4` (or set `LEAN4_SOURCE_ROOT`). This checks immutable Git blob identities and the specific old/new source branches without building or running Lean. `fixture/Open.lean` and `fixture/Edited.lean` preserve a future open/edit diagnostic probe; their SHA-256 values are checked, but no runtime result is claimed. After a fresh >30% RAM admission, a separate probe can initialize clients with the capability absent, false, and true; collect ordered raw `publishDiagnostics` notifications before and after the edit; and verify replacement or append reconstruction against the batch diagnostic set. Such an experiment must report actual bytes, server revision, resource samples, and cleanup separately.
