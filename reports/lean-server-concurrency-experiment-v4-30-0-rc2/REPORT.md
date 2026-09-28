# Lean server workspace isolation and concurrency

## Summary

Two Lean servers with separate source workspaces shared a read-only OLean and returned isolated goals. The probe observed cancellation and deterministic reconstruction after killing and restarting a server. RSS was not measured, and no MCP bridge exists in the checkout.

## Applicability

Synthetic one-file workspaces with Lean 4.30.0-rc2 on macOS arm64, at most two concurrent servers, and one small shared immutable OLean. Related corpus reports: [lean-server-multi-workspace-isolation-v4-30-0-rc2](../lean-server-multi-workspace-isolation-v4-30-0-rc2/REPORT.md), [lean-server-tactic-state-v4-30-0-rc2](../lean-server-tactic-state-v4-30-0-rc2/REPORT.md), [lake-server-preparation-v4-30-0-rc2](../lake-server-preparation-v4-30-0-rc2/REPORT.md).

## Findings


### Scope and controls

This is a Nix-independent, synthetic Lean 4.30.0-rc2 study for Anneal's current redesign. I read [the principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md), [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md), and [agent guide](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/AGENTS.md), then inspected current `anneal/src` and the local Lean server source. The `v1/` tree is historical evidence. A displayed goal or clean Lean file is **not** Anneal verification: Rust semantics, obligation coverage, proof acceptance, and TCB identity remain separate requirements. In particular, cancellation, timeout, or missing diagnostics cannot be treated as success.

The probe used [scratch](support/lean-server-concurrency) (100 KiB on disk at completion), no Nix, no Mathlib copy, and no broad build. It launched at most two simultaneous `lean --server` watchdogs; their sessions lasted 0.779–1.034 seconds, including one intentionally killed watchdog and one replacement. Every batch child had a 20-second timeout, and each server's receive loop had a 29-second lifetime deadline. `LEAN_NUM_THREADS=1` was set, but that is not a measured global process or RSS cap. Process inspection is denied by this sandbox: `/bin/ps -axo pid=,ppid=,rss=` and `/usr/bin/top -l 1 -n 0 -stats pid,mem` returned `Operation not permitted`. **No RSS value or 1.5 GiB stop claim is made.** The fixture's very small disk size and short life do not bound real Mathlib-backed server memory.

The local Lean source and binary identify commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Lean `4.30.0-rc2`, target `arm64-apple-darwin24.6.0`. Lean binary SHA-256: `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. [Probe script](support/lean-server-concurrency/probe.py) SHA-256: `ad632d2d171d55d92929919d5593e63f5deeb2c86b4444b7b8b379ff6a4e0cd4`. [Raw transcript](support/lean-server-concurrency/transcript.json) SHA-256: `1d499e67adf7177731f6beda67a9b228e8ae2e3a0d057ee9ac00294d51846fa0`. It records exact executable and arguments, cwd, selected environment, PID, source hashes, JSON-RPC messages, batch output, status, and elapsed time. An initial attempt stopped before LSP setup because `ps` was blocked; its transcript was superseded by the completed run, so it is not part of the retained protocol evidence.

### Exact synthetic setup and wire sequence

One shared module contains `def sharedValue : Nat := 3`. The script ran `lean -o shared/Dep.olean shared/Dep.lean`, then set `Dep.olean` mode to `0444`. Its SHA-256 was `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71` before and after all sessions. Two independent directories, `a1/` and `b1/`, each had a `Proof.lean` that imported `Dep` through `LEAN_PATH=<scratch>/shared`. Each file had a hole in a theorem using `sharedValue`, with `h : n = 1` versus `h : n = 2`. Their source hashes were respectively `2f1b9d3265d9685448c8e45d7e9da6a7e8c4eea51111fe333f913ed0268eac09` and `b89c27cc6e74aae4da6a1a68f1ead46c9257561f10ed59181fb19f287f12ad24`. The solved `a2` source hash is retained in its batch transcript entry. There were no workspace clones; both servers read one installed toolchain and one immutable OLean, while their source and cwd were local.

The exact command forms, with absolute paths and per-run arguments in the transcript, were:

```text
LEAN_NUM_THREADS=1 lean -o <shared>/Dep.olean <shared>/Dep.lean
LEAN_NUM_THREADS=1 LEAN_PATH=<shared> lean --json <a1-or-b1>/Proof.lean
LEAN_NUM_THREADS=1 LEAN_PATH=<shared> lean --server    # cwd=<a1-or-b1>
```

For each server the client sent `initialize` (`rootUri` matching its cwd), awaited the response, sent `initialized`, then `textDocument/didOpen` with the full source and version 1. It answered `client/registerCapability`, waited on `textDocument/waitForDiagnostics` with `{uri,version}`, then queried `$/lean/plainGoal` at zero-based line 2, character 2. It sent an unsaved full-content `didChange` version 2 only to `a1`, queried both again, sent a goal request and immediate `$/cancelRequest` for that request to `b1`, then closed and reopened `a1` at version 3. Finally it killed the `a1` watchdog, started a new one at the same cwd with recorded version-1 bytes, reopened the file, waited, queried, and shut both servers down. The experiment killed a watchdog deliberately; it did **not** induce a file-worker crash or test Lean's internal worker recovery.

### Observed results

| Event | Observation | Limit |
|---|---|---|
| Two live servers, same basename | `a1` goal included `h : n = 1` and `⊢ n + sharedValue = 1 + sharedValue`; `b1` included `h : n = 2` and the corresponding target. Each emitted its own two hole-related errors. | One small file per cwd, with no Lake configuration or concurrent edits to imports. |
| Unsaved edit in `a1` | Version 2 changed the tactic to `exact congrArg (fun x => x + sharedValue) h`. Final version-2 diagnostics were empty and a post-tactic query returned `{"goals":[],"rendered":"no goals"}`. `b1` still returned its `n = 2` goal. `a1`'s on-disk file remained version 1. | This proves session snapshot separation for this fixture, not project-wide namespace or cache isolation. A pre-tactic query still showed the expected goal even in the solved file. |
| Explicit cancellation | `b1` received JSON-RPC error `{"code":-32800,"message":""}` for the immediately cancelled goal request ID 5. | Cancellation raced with computation. Another schedule may return a result before cancellation; callers must reject a late result against a superseded input identity. |
| Reuse in one cwd | `a1` `didClose` then `didOpen` version 3 of the original hole source yielded the original two errors and original goal. | No change of cwd or dependency universe within the process was tested. |
| Watchdog replacement | Killing PID 76746 returned `-9`; a fresh `a1` watchdog PID 76754 reopened the recorded source, reproduced both error messages and the original goal, then exited 0. | This is deterministic reconstruction of a tiny, fixed input, not proof of all crash recovery paths. The other watchdog PID 76747 stayed live. |
| Shared dependency | `Dep.olean` stayed byte-identical and read-only. `a1`/`b1` imported it and referenced `sharedValue` in their goals. | `LEAN_PATH` served a bare OLean. Real Lake packages also require manifests, configuration, plugin/dynlib and artifact checks. |

All three batch inputs were also run with `lean --json`: `a1` and `b1` exited 1 with the same two error kinds, `Elab.synthPlaceholder` and `Tactic.unsolvedGoals`; solved `a2` exited 0 with no JSON diagnostics. The LSP error messages matched the corresponding batch messages for each saved variant. Batch positions were one-based (`line:3,column:8` for the placeholder); LSP positions were zero-based (`line:2,character:8`). The `a2` LSP result came from unsaved text whereas the batch `a2` result came from separately saved identical bytes; the comparison is by source hash and environment, not by shared disk state. Interim empty `publishDiagnostics` notifications occurred before final errors, so `waitForDiagnostics` and the requested version matter. A clean result at the wrong version must be ignored.

### Source-backed boundaries

Lean requires `didOpen` before file requests and uses the **server process cwd**, not `initialize.rootUri`, as its workspace root ([protocol overview](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/ProtocolOverview.lean#L58)). The watchdog owns open document text and starts per-file workers; `didChange` updates the watchdog copy and `didClose` terminates the worker ([Watchdog.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1230)). The worker cancels pending requests on edit and forwards explicit cancellation to its request token ([FileWorker.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L596)). It tries to emit `requestCancelled` rather than a partial response after explicit cancellation, but a response may already have won the race ([FileWorker.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker.lean#L869)). `waitForDiagnostics` awaits the requested version's reporter and command snapshots; it is a synchronization point for that document, not a proof certificate ([RequestHandling.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L466)).

For a Lake project, the file worker calls `lake setup-file <file> -` using the parsed header; `dependencyBuildMode=never` adds `--no-build --no-cache`. Setup can return import-out-of-date or other error states, and may load dynlibs ([SetupFile.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/SetupFile.lean#L25)). A crashed file worker yields an error for pending requests and fatal progress; the watchdog restarts that worker only on a later `didChange` ([Watchdog.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L925), [Watchdog.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1531)). The separate [Lake concurrency probe](../lake-cache-concurrency-execution-probe-v4-30-0-rc2/REPORT.md) observed two consumers reading a frozen prebuilt producer without changing it, while two consumers of a writable source-only producer both built to the same output paths. Its relative-manifest and config-lock findings apply before a real `lake serve` session; this direct-Lean fixture does not retest them.

There is no checked-in MCP bridge in the current `anneal/src`, Cargo manifest, principles, or design contract (`rg` for `MCP`, `mcp`, and `model context protocol` returned no matches). **Direct MCP protocol work is blocked by absence of that bridge**, not by an observed MCP failure. An adapter would need to preserve the LSP snapshot, cancellation, and error semantics described here; that remains a proposal.

### Proposed Anneal session and resource policy

Use a distinct mutable generated workspace and server cwd per independently changing Anneal job or project snapshot. Keep a published toolchain and dependency universe immutable and share them among readers. Key reuse by toolchain commit/target, dependency and Lake manifest identities, options/plugins/dynlibs, generated source identity, and promised verification scope. Reuse one server within that fixed universe for sequential proof edits, with strict document versions; do not silently change its cwd, imports, or dependency products underneath it. When any shared artifact changes, publish a new dependency generation and start fresh consumers against it. This is a proposed boundary, not current Anneal behavior.

For parallel integration testing, seed one immutable dependency build and relative manifest before workers start, then allocate only small per-worker generated sources/config/build outputs. Put an explicit semaphore around server sessions and dependency builders; avoid multiple writers to one producer build directory. A failure to set up an import is an incomplete tool result. On crash, retain desired source bytes and source map, toolchain/config/dependency hashes, request transcript, and raw stderr; terminate the old process tree, reconstruct a new cwd from those identities, and reopen full text in a fresh server. Permit a small bounded retry only for an identified transient failure. Repeated crashes of the same snapshot become a reproducible tool failure.

For LSP and a future MCP adapter, route requests by `{session, URI, version, source hash, request ID}`. A new edit cancels or invalidates old requests; accept a result only if its input identity is still current. Treat cancellation, timeout, fatal file progress, worker crash, setup failure, and an absent final diagnostic response as explicit incomplete states. A goal payload is useful interactive guidance; only accepted checking results for the intended source and dependency universe can contribute to a verification claim.

Disk scaling is approximately one shared dependency universe plus `N` small mutable generated workspaces and logs, rather than `N` multi-GiB dependency clones. Live memory is different: each watchdog/file-worker set can load imports and elaboration state in its own processes, so RSS can grow with simultaneous open files and servers even when disk artifacts are shared. No numeric per-server RSS factor was measured here. Start with a small active-server cap, close idle documents, use a bounded session pool or LRU retirement, and measure aggregate descendant RSS under a separately authorized host facility before setting production limits. The requested 1.5 GiB aggregate stop should be enforced by the harness during such a measurement; `LEAN_NUM_THREADS=1` and disk deduplication are not substitutes.

### Cross-tool error and provenance specimen

Preserve raw artifacts and create a normalized comparison record, for example:

```json
{
  "run_id": "a1-v1-bare-lean-rc2",
  "input": {"source_sha256": "2f1b9d3265d9685448c8e45d7e9da6a7e8c4eea51111fe333f913ed0268eac09", "uri": "file:///.../a1/Proof.lean", "version": 1},
  "environment": {"lean_commit": "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", "cwd": ".../a1", "import_olean_sha256": "b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71"},
  "diagnostic": {"severity": "error", "message": "don't know how to synthesize placeholder", "batch_kind": "Elab.synthPlaceholder", "batch_start_1based": [3, 8], "lsp_start_0based": [2, 8]},
  "evidence": {"batch_exit": 1, "lsp_wait_version": 1, "raw_transcript": "transcript.json"},
  "verification_status": "incomplete"
}
```

The actual transcript retains the full messages, paths, exact ranges, and two error instances; the shortened URI above is illustrative. A production record should add original Rust span/obligation identity, generated Lean span, source-map revision, proof-library identity, trust/TCB record, and the precise result unit. Keep batch `--json` and LSP diagnostics as separately attributed observations, not one merged authority. Compare them only after matching source bytes, imports/artifacts, toolchain, cwd, options, and plugin environment. Map Lean's one-based batch locations and zero-based LSP ranges to a common span model; preserve original coordinates because multiline range endings can differ in shape. A transport error (`-32800` cancellation), setup failure, process exit, or timeout belongs in a tool-event record, not a fake Lean diagnostic. An MCP adapter should carry that event and its input identity forward unchanged. The ordinary Rust-facing explanation can cite the obligation and source span while retaining the raw Lean record for specialists and audit.

### Setup/prompt adjustment

For the next real-archive probe, preseed each consumer's relative Lake manifest, freeze and hash one shared dependency universe, and test `lake serve` with two small generated workspaces and identical-source batch `lean --json` comparisons. Require versioned `didOpen` → `waitForDiagnostics` → goal queries, unsaved edit and cancellation traces, a forced restart from recorded inputs, and raw setup/protocol/stderr evidence. Arrange an allowed aggregate process-tree RSS monitor that polls and kills at 1.5 GiB before asking for a many-job capacity claim; retain the two-server, 30-second-child, and 1 GiB-scratch limits. If an MCP bridge is added, name its executable and protocol explicitly before assigning direct MCP integration tests.

## Boundaries

No Mathlib-backed capacity measurement, aggregate RSS, multi-file dependency invalidation, internal worker-crash recovery, or direct MCP behavior was tested. The execution sandbox denied `ps` and `top`; no numeric server-memory estimate is supported.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/lean-server-concurrency/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Run the retained JSON-RPC client with two isolated workspaces, shared read-only dependency, unsaved edit, cancellation, and restart from recorded source bytes. Use an allowed aggregate-process monitor before making any multi-job memory-capacity claim.
