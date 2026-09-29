# OS lock ordering and file-descriptor recovery controls

## Summary

Two bounded macOS child processes taking advisory locks in opposite order each held one lock and blocked on the other. Killing one released its lock and let the survivor complete. With both children using the same order, both completed without intervention. In a separate child limited to 32 open descriptors, staging a candidate artifact failed with `EMFILE`; the selected last-good pointer still named A. After releasing descriptors, the child staged and selected B. These are direct OS controls for #3731 I108 and I109, not observations of an Anneal process.

## Method and observations

`support/probe.py` used only the Python standard library on Darwin 25.6.0 arm64 and a temporary owned scratch directory. Every child had a five-second wait or process timeout; all child processes and scratch files were cleaned up. No host-wide resource limit, service, or production state was changed. The `fd-child` changed only its own `RLIMIT_NOFILE` soft limit to 32. The checker validates retained outcomes without rerunning the probe.

| Control | Retained observation | Implication within this fixture |
| --- | --- | --- |
| Opposite order: A takes prepare then publish; B takes publish then prepare | Both first locks and second-lock attempts were marked; neither acquired its second lock after 200 ms. B exited `-9` after `SIGKILL`; A then acquired its second lock and exited 0. | A two-lock cycle can block progress; process death releases this fixture's advisory lock. |
| Same order: both take prepare then publish | B waited for A's first lock, then both acquired both locks and exited 0. | A consistent order avoided the observed cycle under this schedule. |
| Candidate staging after child-only FD exhaustion | 29 extra descriptors opened; staging B failed with `EMFILE`; selected pointer remained A. After descriptors closed, B was written and selected. Artifact hashes are checked against fixture bytes. | Failure before pointer replacement preserved the fixture's selected A; cleanup enabled retry. |

The observed results are in `support/results.json`. `support/check.py` checks the cycle, ordered control, exit codes, `EMFILE`, selected names, and hashes. The probe script's SHA-256 is `f137e4520adc6c793d20b3ecd073c2fed8ee74a1090a763a6c82742fe9aeec0e`; the retained result SHA-256 is `5fb284515ba1a9711d7381aba6a2e8e41284a5c18897b903d2c53ae10fde0b7f`.

## Issue coverage and limits

For **I108**, this adds an actual multi-process, two-lock ordering/death control beyond the prior single publication-lock simulation in `anneal-3730-generation-recovery-2026-09-29`. It does not enumerate Anneal's lock graph, prove that its implementation observes a global order, or test GC/restart interactions with real held locks.

For **I109**, this adds an actual `EMFILE` failure and bounded last-good/retry observation. It does not exercise Anneal's resource accounting, error propagation, memory or disk exhaustion, process-table exhaustion, or recovery with live Lean/Rust workers. The selected pointer and artifact bytes are synthetic. The fixture does not claim crash durability or power-loss behavior.

The exact OS results are single schedules on one host. The five-second bounds prevent a permanently blocked child; they do not establish throughput or production deadlock freedom. No dependency was downloaded or installed.

## Revalidation

Run `python3 support/check.py` from any working directory to inspect the retained evidence. To repeat the bounded OS experiment, run `python3 support/probe.py` and then the checker. Set `ANNEAL_PROBE_SCRATCH` to an owned existing scratch directory if the default temporary directory is unsuitable. A real Anneal acceptance test requires instrumented prepare/cache/publish/restart/GC locks, fault injection at each acquisition, and a product last-good oracle.
