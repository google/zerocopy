# Shared real Cargo job with two cancelling consumers

## Question and subject

Can two requests share one actual backend build while cancellation of one leaves the other's build alive, cancellation of both stops the child tree, and a backend failure fans out to both? On this tiny **experimental owner/refcount harness**, yes. The backend was an installed, offline Cargo 1.98.1 build of a dependency-free crate; two consumer records in one Python process shared exactly that one `Popen` handle. The harness is not Anneal's scheduler, editor or MCP transport. This is bounded component evidence for #3731 I007/I107 and #3730 H09 after H09's independent-build cancellation control.

The fixture's build script writes its PID and a spawned `/bin/sleep` PID at an entered marker, waits two seconds, and optionally panics under `FAIL_BUILD=1`. The experiment used three fresh private roots and one Cargo process per root, one after another. Every Cargo call used `--offline -j 1` and `CARGO_NET_OFFLINE=true`; there were no downloads or installs. Preflight measured 53,359,181,824 free disk bytes and 53% free system memory. A 2,000,000-KiB sampled process-group RSS assertion and 25–30-second command deadlines guarded each cell. The three marker samples were 35,728, 35,680 and 35,616 KiB. These are sampled group RSS sums, not hard transient physical-memory peaks.

## Observations

| Cell | First backend outcome | Consumer outcomes | Retry |
| --- | --- | --- | --- |
| Cancel editor only | Cargo exited 0 and produced `libshared_job_probe.rlib`. | Editor cancelled; agent succeeded. The backend was still running immediately after editor cancellation. | Not needed. |
| Cancel both | Last-owner `SIGTERM` made Cargo exit `-15`; no final `.rlib` existed at that checkpoint. | Both cancelled. Cargo, build script and sleep were present at marker and absent after collection. | Fresh offline build exited 0 and produced `.rlib`. |
| Inject build-script failure | Cargo exited 101; no final `.rlib`; stderr contained the injected panic. | Both failed. | `FAIL_BUILD=0` rebuild exited 0 and produced `.rlib`. |

The retained process-group snapshots show Cargo, `build-script-build`, and `/bin/sleep` in each active backend. `support/results.json` preserves command arguments, owner state transitions, exits, stdout/stderr, marker PIDs, sampled RSS and final artifact hashes. All three successful `.rlib` SHA-256 values differ across the three private build paths; Cargo output byte identity across roots is **not** claimed. Each result is checked against its own retained file. The source fixture hashes are identical in all three roots.

## Contract implications and limits

This demonstrates a concrete rule for an owner-aware *single* real process: a departing consumer need not cancel backend work while another consumer is still subscribed; the last departure may stop the process group; a backend error can be returned to every remaining consumer, then retried. The cancellation and fan-out decisions were made by the toy Python harness, and the two consumers were records rather than independent connected clients. There is no actual request multiplexing over LSP/MCP, Anneal generation key, cache hit, Charon/Aeneas/Lake/Lean stage, or cross-process durable job registry. A failed build may leave intermediate target files; the oracle here checked absence of the final library before retry and success afterward, not a full target-tree transaction. A short process-group snapshot cannot rule out unsampled orphan processes.

H09 previously stopped one of **two independent** Cargo builds. This report differs by presenting one shared `Popen` to two request owners and exercising first-owner/last-owner/failure transitions against the real build. I007/I107/H09 remain partial until an Anneal scheduler ties request identity, cancellation, stage generation, publication and cache reuse to this ownership policy under actual editor or MCP clients.

## Evidence and replay

`support/fixture/` contains the exact crate. `support/probe.py` runs all three fresh-root cells and refuses an existing `support/work/`; `support/work/` retains the source, marker and target outputs from this run. `support/check.py` verifies fixture/result hashes, process-tree membership and cleanup, owner transitions, final artifact existence, failure text and retries without rerunning Cargo. `python3 support/check.py` passed. To rerun, copy this package, remove only the copy's `support/work/`, and run `python3 support/probe.py` then `python3 support/check.py`. Compare outcomes and process categories; PIDs, private paths, timing, RSS and `.rlib` bytes can differ.
