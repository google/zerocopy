# Direct Lean pool fault isolation and guarded restart

Observed 2026-09-29 on an 8 GiB macOS arm64 host with pinned Lean 4.30.0-rc2. This is a direct-server component probe for #3730 J09 and #3731 I105/I110/I139. It uses four independent `lean --server` process groups, each with one tiny proof document. A proposed eight-worker follow-up was denied by the probe's admission guard: system-wide free memory was 42% after the four-worker cell, below its 45% eight-worker threshold. No eight-worker behavior is claimed.

## Guard and fixture

The preflight observed 41% system-wide free memory, 8 GiB physical RAM, and about 54.6 GB free disk. The cell had a monitoring thread and checks after every worker startup and fault phase. Caps were 2.4 GiB summed pool process-tree RSS, 25 MiB scratch disk blocks, a 30% free-memory floor, and 90 seconds elapsed. The highest recorded pool RSS was 620,003,328 bytes; the lowest checked free-memory value was 41%. The private scratch cell occupied 16,384 disk-block bytes after cleanup. These are host and tiny-workload observations, not a production capacity estimate.

Each worker opened `theorem peer_i : True := by trivial`, reached `textDocument/waitForDiagnostics`, and answered `$/lean/plainGoal` with `⊢ True` and empty diagnostics. The harness then changed worker 0's **buffer only** to `exact 0`; its disk source hash remained the original. Lean published one severity-1 diagnostic: `numerals are data in Lean, but the expected type is a proposition\n  True : Prop`. Workers 1–3 retained empty diagnostics and the same goal when queried after the malformed edit.

For worker 1, the harness sent a version-2 change, a `waitForDiagnostics` request, and `$/cancelRequest` for that request, then killed only worker 1's process group with SIGKILL. The server exited `-9`; no process remained in that group when checked. This proves crash cleanup under a process-group kill. The transcript does **not** show a cancellation acknowledgment or establish that Lean processed the cancellation before the kill. A fresh server on worker 1's private root then reopened the saved valid proof, reached the readiness barrier, returned `⊢ True`, and had empty diagnostics. Workers 2 and 3 still answered with empty diagnostics after the crash and restart. Worker 0's malformed-buffer diagnostic remained local to worker 0.

The experiment also runs a separate, explicitly synthetic stale-result fence: an old candidate carries worker epoch 1, document version 2, and its buffer hash; the restarted worker has epoch 2, version 1, and the saved-source hash. Exact epoch/version/hash comparison rejects the old candidate and accepts the fresh one. No late Lean reply was accepted or observed from the killed server; the fence is a contract model, not an Anneal implementation or a demonstrated Lean protocol guarantee.

## Replay and validation

From the checkout:

```sh
python3 reports/anneal-3730-lean-pool-failure-isolation-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new-scratch-directory --max-workers 4
python3 reports/anneal-3730-lean-pool-failure-isolation-2026-09-29/support/verify.py
```

The private path must not exist. The script requires at least 15 GiB free disk and 40% system-wide free memory before starting. Without `--max-workers 4`, it considers an eight-worker cell only if post-four-worker free memory is at least 45%, the earlier peak RSS is below 1.5 GiB, and no watchdog violation occurred. If any hard cap trips, the monitor kills active process groups and the run fails. `support/transcript.json` preserves full normalized JSON-RPC traffic, readiness and goal responses, diagnostic details, resource samples, admission state, process-group cleanup, and the separate fence-model inputs. The verifier checks the retained four-worker run and the recorded eight-worker denial.

The retained-data verifier checks the admission decision and measured samples; it does not require the host's post-cell free-memory percentage to repeat on replay.

## Coverage and limits

The four-worker result supports a narrow J09/I139 failure-isolation observation for independent direct Lean processes: one malformed buffer did not change peer diagnostics/goals, and killing one process group did not stop the other peers. It supports I110 restart reconstruction only for a saved tiny proof; I105 cancellation is limited to a sent request followed by forced crash, without a processed-cancellation claim. Process-group cleanup and memory caps are harness behavior. The experiment does not exercise shared imported dependencies, Anneal's pool/scheduler, real result delivery and stale fencing, a controlled graceful cancel, large proof workloads, or an admitted eight-worker run. Those remain integration and capacity questions.
