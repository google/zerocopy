# Direct Lean server topology with conflicting imports and scratch workers

## Summary

One direct `lean --server` watchdog opened two files from independent directories whose same-named `Dep` imports disagreed. With the server launched under A's `LEAN_PATH`, both files evaluated `selected` as 11; B's proof expecting 22 failed. With separate A and B watchdogs, A evaluated 11 and B evaluated 22, and B's proof no longer had that error. This is an executable counterexample to treating two document URIs under one direct server as independently configured workspaces.

At the measured loaded point, one watchdog plus two file workers had summed RSS 867,074,048 bytes; two watchdogs plus one worker each had 967,688,192 bytes. A scratch file's old RPC session returned `-32900` after close/reopen spawned a new worker. A fresh RPC session restored the query. These are tiny direct-Lean fixture results, not an MCP or Anneal result.

## Applicability

Lean was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), binary SHA-256 in `REPORT.json`, on arm64 macOS with `LEAN_NUM_THREADS=1`. The host had 8 GiB RAM. The probe used only two tiny open files at once, no Mathlib, Lake workspace, plugins, native extensions, or Anneal implementation. It compiled `A/Dep.olean` and `B/Dep.olean` sequentially before starting any server; both modules define the same `selected` name with values 11 and 22 respectively. Both proof files import `Dep`, run `#eval selected`, contain an `rfl` claim for their expected value, and expose one placeholder goal. Their source and OLean hashes are in [`support/summary.json`](support/summary.json).

The first topology launched one watchdog with cwd and `LEAN_PATH` set to A, opened both absolute file URIs, waited for version-1 diagnostics, queried goals, and sampled the process tree. The second topology launched one watchdog under A and one under B, each opening its own proof file. These phases ran sequentially. A third phase reused one scratch URI through an unsaved version-2 edit, then closed and reopened it at version 1; a fourth started a fresh watchdog on the original scratch bytes. The client records a local server incarnation number because LSP request IDs and document versions alone are reusable.

## Findings

### Same-name import collision under one watchdog

| Topology | B file `#eval selected` | B `rfl` claim | Loaded processes | Summed RSS |
| --- | --- | --- | ---: | ---: |
| One A-configured watchdog, A and B open | `11` | Failed: `selected` did not reduce to `22` | 3 | 867,074,048 bytes |
| Separate A and B watchdogs | `22` | No `rfl` error | 4 | 967,688,192 bytes |

The B source and its local `Dep.olean` were unchanged between phases. The single server inherited A's process-wide import path, so opening B's URI did not select B's independent module of the same name. Separate servers resolved their own imports. A's file evaluated 11 in both phases. The intentionally unfinished placeholder still produced errors in every file; the comparison concerns the independent `rfl` claim and `#eval` diagnostic. Basis: **execution** of direct Lean with the exact source/OLean hashes and raw LSP messages in [`support/transcript.json`](support/transcript.json). It concretely tests the independent-workspace limit derived from pinned source in [`../lean-server-multi-workspace-isolation-v4-30-0-rc2/REPORT.md`](../lean-server-multi-workspace-isolation-v4-30-0-rc2/REPORT.md).

The one-server process snapshot comprised one watchdog at 91,553,792 bytes and two file workers at 388,022,272 and 387,497,984 bytes. The two-server snapshot comprised two watchdogs at 97,517,568 and 95,289,344 bytes and two workers at 387,563,520 and 387,317,760 bytes. The observed difference was 100,614,144 bytes. `ps` RSS is resident size per process; summing it double-counts shared pages, and the sequential samples do not isolate watchdog overhead or predict larger project memory. A 1.5-GiB summed-RSS guard was armed, and neither phase crossed it. Shutdown samples found no surviving processes under the recorded watchdog PIDs. Basis: **execution** of the macOS `ps` process-tree sampler; the stronger resource interpretation is deliberately withheld.

Initialization took 30.0 ms for the shared watchdog and 26.4 ms for each separate watchdog. Each version-1 open through `waitForDiagnostics` took 235.5–239.2 ms; post-wait plain-goal requests took 0.4–1.4 ms. The two separate servers were initialized sequentially before their files were opened, so these are command latencies for one run, not a parallel throughput or statistically reliable latency comparison. The earlier [`lean-server-memory-and-protocol-concurrency`](../lean-server-memory-and-protocol-concurrency-v4-30-0-rc2/REPORT.md) report already measured four independent direct servers; this run adds the matched two-file-versus-two-server topology and conflicting imports.

### Scratch reuse and RPC incarnation

The scratch proof began with `exact ?_`; a plain goal and `Lean.Widget.getInteractiveGoals` RPC call returned the expected goal. The RPC response included a server-side `ctx` reference. An unsaved version-2 edit to `rfl` under the same open worker returned `no goals`; its `waitForDiagnostics` took 211.3 ms. Closing the document and reopening the **same URI at version 1** produced a different file-worker PID (47653 → 47657). The old RPC session returned JSON-RPC error code `-32900`, `Outdated RPC session`; a new `$/lean/rpc/connect` returned a different session ID and restored the interactive goal. Reopening took 240.0 ms. A fresh watchdog then reopened the original bytes at version 1 and produced the same plain goal; its request numbering restarted, as recorded in the transcript.

The local client tagged each message with a watchdog incarnation and retained the old and new RPC session IDs. This shows why a caller must bind RPC references and late responses to a live worker/session as well as URI/version/request number. It does not show an actual delayed response crossing a restart: no request was held in flight while the worker was replaced, and no context reference was dereferenced through a different method after reconnect. Basis: **execution** for the expired session, worker PID change, and goals; **derived** for the client routing rule. The pinned Lean RPC type documentation says sessions can be destroyed and old calls require reconnect, consistent with the observed code.

### Cleanup and score extraction

Every watchdog exited after LSP shutdown/exit. At each phase's post-shutdown process-tree sample, the recorded roots and descendants had zero measured RSS. The intermediate post-close sample still listed the old worker PID transiently at zero RSS; the reopened worker had a new PID. [`support/summarize.py`](support/summarize.py) asserts the collision, separate-server resolution, process counts, worker change, old-session error, restored RPC result, and zero post-shutdown RSS, then emits [`support/summary.json`](support/summary.json). The summary is derived from the raw transcript rather than replacing it.

## Boundaries

- **I044 partial:** one returned interactive context reference was observed, but its individual object lifetime was not exercised across edits, cancellation, or server restart; only its session became unusable after file close/reopen.
- **I045 partial:** request numbers and document version 1 recurred under a fresh watchdog/worker, and the harness supplied its own incarnation labels. No deliberately delayed old response or internal worker crash was injected. Clean shutdown and close/reopen were observed; forced termination was covered in the earlier two-server probe, not repeated here.
- **I153 partial:** the measurement covers one and two direct Lean servers with one or two open tiny files, plus one scratch file reused and reopened. It does not compare an MCP process, external broker, Lake environments, scratch pools of size 2/4/8, long-running memory growth, or configured plugins/options. The import collision is the conflicting environment control.
- **Not established:** that one server is always cheaper or that two are always required. Files sharing a genuinely identical prepared environment can legitimately coexist under one watchdog; independently configured imports cannot be separated by URI alone in this observed mode.
- **Not established:** unique physical memory, production capacity, cross-platform RSS behavior, or process cleanup after a hard kill. Summed RSS and short sequential timings are narrow observations.

## Evidence

- Executable [`support/probe.py`](support/probe.py), SHA-256 `e25dffeefadbd86f7d3eec4f862a8cf882e709fb99365a6730d8359be42288c0`; [`support/transcript.json`](support/transcript.json), SHA-256 `8689cb07deca24a640f729d457383b057e32a6d2bcbb0ec8ecdeb18b05129b0c`. The transcript keeps raw LSP request/notification/response bodies, command outputs, process RSS rows, timestamps, input/artifact hashes, and client incarnation labels. Absolute local paths are replaced with `$WORK`, `$WORK_URI`, `$LEAN_BIN`, and `$LEAN_HOME`.
- Checked summary [`support/summarize.py`](support/summarize.py), SHA-256 `6d3276187c2bae0421b4fb998290efc6bd81928c4b6f4d4c4c26ddd7d125d71a`; [`support/summary.json`](support/summary.json), SHA-256 `2d4646b7feb93e33f4f4322623dc7be165e6bbffd91b67f60add9bc4d4618075`. [`support/work/`](support/work/) retains the small exact source files and compiled `Dep.olean` artifacts.
- Prior direct-server execution: [`lean-server-concurrency-experiment`](../lean-server-concurrency-experiment-v4-30-0-rc2/REPORT.md), [`lean-server-memory-and-protocol-concurrency`](../lean-server-memory-and-protocol-concurrency-v4-30-0-rc2/REPORT.md). Pinned source context: [`lean-server-multi-workspace-isolation`](../lean-server-multi-workspace-isolation-v4-30-0-rc2/REPORT.md), Lean `src/Lean/Data/Lsp/Extra.lean` `RpcConnectParams`/`RpcCallParams`, and `src/Lean/Server/Watchdog.lean` at the revision in `REPORT.json`.
- Scope: [google/zerocopy issue #3731](https://github.com/google/zerocopy/issues/3731), I044/I045/I153, viewed 2026-09-29.

## Revalidation

On a fresh copy of this package, set `LEAN_BIN` to the pinned executable, run `python3 support/probe.py`, then `python3 support/summarize.py`. Confirm the B file's `#eval` and `rfl` difference across topologies, the per-process and aggregate RSS rows, the changed scratch worker PID, `-32900` for the old RPC session, fresh-session success, and no surviving recorded process tree after shutdown. For a future Lean revision or a real Lake project, replace the bare `LEAN_PATH` conflict with two independently configured prepared environments and inspect actual setup-file context; add a deliberately delayed response and stronger process/footprint monitoring before using these numbers to choose a worker pool policy.
