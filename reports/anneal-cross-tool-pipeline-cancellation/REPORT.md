# Cross-Tool Pipeline Cancellation, Process-Group Cleanup, Shared Job Ownership, and Recovery Controls

## Summary

Across six experimental suites exercising Cargo, `rustc`, Charon, Aeneas, Lake, and Lean (`lean --json` and `lean --server`), safe cancellation and recovery require five distinct mechanisms rather than parent-process termination or LSP request cancellation alone:
1. **Process-group signal escalation and descendant cleanup**: Sending `SIGINT`, `SIGTERM`, or `SIGKILL` to an isolated process group at launch, after an `80 ms` cold delay, or at deterministic output/elaboration barriers (`support/cli-graceful-cancel-signals/`, `support/cross-tool-active-cancellation-barriers/`, `support/cross-tool-stage-cancellation-cleanup/`) cleared all observed child processes (`cargo`, `rustc`, `build-script-build`, `/bin/sleep`, `charon`, `charon-driver`, `aeneas`, `lake`, and `lean`) and allowed same-directory or clean-directory retries to exit `0`. When a supervisor inherited `SIGINT` as ignored (`support/cli-graceful-cancel-signals/ignore_int_supervisor.py`), `SIGINT` left the supervisor and Aeneas alive until a bounded `1 s` escalation step delivered `SIGTERM`.
2. **Output-set completeness versus single-file parseability**: Interrupting `charon --format all` with a FIFO barrier after JSON LLBC emission but before Postcard completion left a parseable JSON LLBC alongside an incomplete output set (`support/cli-graceful-cancel-signals/`, `support/cross-tool-active-cancellation-barriers/`). Similarly, interrupting Aeneas split-file generation after `Types.lean` left `Funs.lean` absent, interrupting Lake inside a Lean `run_tac` barrier left `Cancel/A.olean` present and `Cancel/B.olean` absent, and `80 ms` delayed cold kills left `6` partial Cargo target files and `1` Lake build-tree file (`support/cross-tool-stage-cancellation-cleanup/`). Output verification must therefore check complete manifest inventories and hashes before atomic publication.
3. **Lean LSP request cancellation suppresses replies without interrupting running tactics**: In `support/lsp-to-upstream-cancellation-boundaries/`, sending `$/cancelRequest` at `0.4176 s` for a `textDocument/waitForDiagnostics` request on a tactic executing `IO.sleep 3000` returned JSON-RPC error `-32800` at `4.3291 s` (`3.91 s` after cancellation, when the `3 s` tactic finished). Pinned Lean `Watchdog.lean` and `FileWorker.lean` mark the pending request cancelled and suppress result publication, while subsequent requests on the same open document succeed.
4. **Reference-counted shared job ownership across consumers**: While independent process groups isolate peer Cargo builds from `SIGTERM` (`support/lsp-to-upstream-cancellation-boundaries/`), sharing one backend Cargo `Popen` handle across two consumers (`editor` and `agent` in `support/shared-cargo-consumer-ownership/`) requires reference-counted ownership: cancelling `editor` alone left Cargo running so `agent` received `libshared_job_probe.rlib` (exit `0`), cancelling both delivered `SIGTERM` on the last owner's departure (exit `-15`, clearing `cargo`, `build-script-build`, and `/bin/sleep`), and an injected `FAIL_BUILD=1` panic (exit `101`) fanned out failure to both consumers before a clean retry succeeded.
5. **Monotonic generation fencing, lock ordering, and descriptor-exhaustion recovery**: Across `support/cross-tool-active-cancellation-barriers/gated_stage.py`, `support/cross-tool-stage-cancellation-cleanup/fence_oracle.py`, and `support/os-lock-fd-recovery-controls/`, late completions from superseded generation `1` are rejected after authority advances to generation `2`; consistent lock acquisition order (`prepare` then `publish`) prevents the two-process advisory-lock deadlock observed under opposite ordering (resolved on `SIGKILL` of one holder); and candidate staging before pointer replacement preserves the last-known-good pointer `A` when child-scoped `RLIMIT_NOFILE = 32` triggers `EMFILE`.

## Applicability

All experiments ran on macOS arm64 (`26.6.2` / Darwin `25.6.0`) using CPython `3.14.7` and offline cached binaries recorded in `REPORT.json`:
- **Lean 4 and Lake**: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`).
- **Charon and Aeneas**: `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (`0.1.210`, SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`) and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`, SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`).
- **Rust compiler and Cargo (multi-version coverage and shared behavior vs. version deltas)**:
  - `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (`nightly`, SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`) and its paired `nightly` `rustc` toolchain were invoked by `charon` (`0.1.210`) and the cross-tool stage cancellation suites (`support/cli-graceful-cancel-signals/`, `support/cross-tool-active-cancellation-barriers/`, `support/cross-tool-stage-cancellation-cleanup/`).
  - `rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985` (`rustc 1.98.1`, SHA-256 `2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340`) paired with Homebrew `cargo 1.98.1` (`797e8a9bc 2026-08-05`, SHA-256 `778478868dbfe74960e49329bb5813d2f5ba95c8bfb1f37cd626c62cb26a214a`) ran the standalone `build.rs` descendant and shared-consumer Cargo experiments (`support/lsp-to-upstream-cancellation-boundaries/`, `support/shared-cargo-consumer-ownership/`). **Shared behavior vs. version delta**: across both `nightly` and `1.98.1`, process-group `SIGTERM`/`SIGKILL` cleanly terminated `cargo`, `rustc`, `build-script-build`, and spawned children without leaving live group members, and subsequent `--offline -j 1` retries in the same or fresh target directories exited `0`.
- **Anneal workspace**: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.

## Findings

### Active-Barrier CLI Cancellation Signals, Escalation, and Same-Directory Recovery

In `support/cli-graceful-cancel-signals/probe.py` (`support/cli-graceful-cancel-signals/results.json.gz`, `support/cli-graceful-cancel-signals/check.py`), seven active-gate cases compared graceful first signals (`SIGINT` / `SIGTERM`) with `SIGKILL` controls and same-directory retries:

| Active barrier | Graceful first signal | `SIGKILL` control | Same-directory recovery |
| --- | --- | --- | --- |
| Charon (`--format all`) after JSON LLBC and before Postcard FIFO | `SIGINT`; controller exit `-2`; controller and `charon-driver` absent from immediate process-group snapshot. | Exit `-9`; same descendant cleanup. | Retained parseable partial JSON, removed only the blocked FIFO, retried in the **same output directory**; both JSON and Postcard present and independently parsed by Charon. |
| Aeneas (`-split-files`) after `Types.lean` and before `Funs.lean` FIFO | `SIGTERM`; exit `-15`; no group member in immediate post-signal snapshot. | Exit `-9`; same descendant cleanup. | Retained `Types.lean`, removed only the blocked FIFO, retried in the **same output directory**; generated modules compiled and a fresh Lean consumer proved `signal_probe.inc 0 = .ok 1`. |
| Lake build with Lean child inside `run_tac` after module `A`'s `.olean` | `SIGINT`; Lake exit `-2`; Lake and Lean child absent from immediate group snapshot. | Exit `-9`; same descendant cleanup. | Retained `A`'s `.olean`, released the tactic gate, retried in the **same Lake directory**; `B`'s `.olean` and a fresh consumer proof of `chosen = 8` succeeded. |

- **Escalation under ignored `SIGINT`**: `support/cli-graceful-cancel-signals/ignore_int_supervisor.py` launched Aeneas with `SIGINT` inherited as ignored. Both supervisor and CLI remained alive after `SIGINT`; the bounded escalation policy (`1 s` step timeout, `SIGINT → SIGTERM → SIGKILL`) escalated to `SIGTERM`, clearing both processes, and an unsupervised same-directory retry passed the Lean consumer.
- **Open pipe and advisory `flock` observations**: Raw `lsof` snapshots showed open pipes at all active barriers, while nonblocking exclusive `flock` probes on each completed partial artifact succeeded both during the gate and after process termination.

### Causal Cross-Tool Barriers, Cold-Delay Partial State, and Generation Fences

In `support/cross-tool-active-cancellation-barriers/probe.py` (`support/cross-tool-active-cancellation-barriers/results.json`, `support/cross-tool-active-cancellation-barriers/check.py`, `support/cross-tool-active-cancellation-barriers/gated_stage.py`), five causal barrier gates were tested:

| Gate | Observed component outcome | Retry / oracle |
| --- | --- | --- |
| Pre-exec wrapper | Killed while wrapper gate was entered; no CLI had started. | Pre-launch cancellation control. |
| Charon `--format all` | Parseable JSON LLBC existed while Charon and `charon-driver` were alive and Postcard destination was a blocked FIFO; `SIGKILL` left no group members. | Removed interrupted generation; retry regenerated both formats and Charon parsed the Postcard output. |
| Aeneas split-file output | `Types.lean` existed while Aeneas was alive and `Funs.lean` was a blocked FIFO; `SIGKILL` left no group members. | Fresh destination yielded complete `Base` modules; fresh Lean compilation and `inc 0 = .ok 1` proof passed. |
| Lake build / Lean elaboration | `Cancel/A.olean` existed and `Cancel/B.olean` did not while Lake's Lean child was blocked in `run_tac`; `SIGKILL` removed both group members. | Releasing gate and retrying completed `B`; fresh Lake/Lean consumer proved `chosen = 8`. |
| Late stage completion (`gated_stage.py`) | Old job's real Aeneas CLI completed, then wrapper waited while a new source completed real Charon→Aeneas→fresh Lean proof (`inc 0 = .ok 2`) and advanced authority to generation `2`. | Resumed old wrapper's explicit generation check rejected publication of generation `1`, leaving the shared destination untouched. |

In `support/cross-tool-stage-cancellation-cleanup/probe.py` (`support/cross-tool-stage-cancellation-cleanup/results.json`, `support/cross-tool-stage-cancellation-cleanup/verify.py`), eight sequential trials delivered `SIGSTOP`, inspected `ps` group membership, delivered `SIGKILL` (all exiting `-9` with zero surviving PIDs), inventoried partial outputs, and retried in the same private directory (all `8` retries exiting `0`):
- **Five invocation-boundary controls** (Cargo, Charon, Aeneas, Lake, direct `lean --json`): stopped the CLI leader before child spawn and left `0` output files.
- **Three `80 ms` delayed cold controls**:
  - Delayed Cargo stopped `cargo` and `rustc` leaving `6` partial target files; same-directory retry produced `43` Cargo target files (`support/cross-tool-stage-cancellation-cleanup/artifacts/cargo-app.rmeta`).
  - Delayed Charon stopped `charon`, `cargo`, and `charon-driver` leaving `0` destination LLBC files; same-directory retry produced parseable `app_closure` LLBC (`support/cross-tool-stage-cancellation-cleanup/artifacts/charon-app.llbc`).
  - Delayed Lake stopped `lake` leaving `1` build-tree file; same-directory retry produced `Probe.olean` (`support/cross-tool-stage-cancellation-cleanup/artifacts/lake-Probe.olean`), while Aeneas retry produced `3` Lean files (`support/cross-tool-stage-cancellation-cleanup/artifacts/aeneas-Funs.lean`).
- **Synthetic 8-stage generation fence (`support/cross-tool-stage-cancellation-cleanup/fence_oracle.py`, `support/cross-tool-stage-cancellation-cleanup/fence-results.json`)**: For all `8` stage artifact digests, advancing authority to generation `2` rejected late generation-`1` publication attempts without altering pointer bytes before atomically committing generation `2` via `os.replace`.

### Lean LSP Request Cancellation and Shared versus Independent Cargo Ownership

In `support/lsp-to-upstream-cancellation-boundaries/probe.py` (`support/lsp-to-upstream-cancellation-boundaries/results.json`, `support/lsp-to-upstream-cancellation-boundaries/check.py`; preflight `46%` free memory and `53,787,795,456` free disk bytes):
- **Direct `lean --server` cancellation (`support/lsp-to-upstream-cancellation-boundaries/fixture/Slow.lean`)**: The client opened `Slow.lean` (containing a custom tactic with `IO.sleep 3000` followed by `trivial`), sent `textDocument/waitForDiagnostics` (request ID `2`), and sent `$/cancelRequest` for ID `2` at `0.4176 s`. The server returned `{"error":{"code":-32800,"message":""},"id":2}` at `4.3291 s` (`3.91 s` after cancellation). A subsequent `waitForDiagnostics` request (ID `3`) on the same URI/version succeeded with empty diagnostics, and batch `lean --json Slow.lean` exited `0`.
- **Independent Cargo process-group isolation**: While victim group (`cargo` PID `87527`, `build-script-build` PID `87549`, `/bin/sleep 5` PID `87550`) and peer group (`cargo` PID `87553`, `build-script-build` PID `87568`, `/bin/sleep 5` PID `87569`) ran concurrently, sending `SIGTERM` to the victim group caused it to exit `-15` with zero remaining members, while the peer group continued running, exited `0`, and emitted its final library; the victim succeeded on retry.

In `support/shared-cargo-consumer-ownership/probe.py` (`support/shared-cargo-consumer-ownership/results.json`, `support/shared-cargo-consumer-ownership/check.py`; preflight `53%` free memory and `53,359,181,824` free disk bytes; sampled process-group RSS at barrier markers `35,728 KiB`, `35,680 KiB`, and `35,616 KiB` under a `2,000,000 KiB` guard), two consumers (`editor` and `agent`) shared a single Cargo `1.98.1` `Popen` handle:

| Cell | First backend outcome | Consumer outcomes | Retry |
| --- | --- | --- | --- |
| Cancel `editor` only | Cargo exited `0` and produced `libshared_job_probe.rlib`. | `editor` cancelled; `agent` succeeded. Backend remained running after `editor` cancellation. | Not needed. |
| Cancel both (`editor` then `agent`) | Last-owner `SIGTERM` made Cargo exit `-15`; no final `.rlib` existed at checkpoint; `cargo`, `build-script-build`, and `/bin/sleep` cleared. | Both cancelled. | Fresh offline build exited `0` and produced `.rlib`. |
| Inject build-script failure (`FAIL_BUILD=1`) | Cargo exited `101`; no final `.rlib`; stderr contained injected panic. | Both failed. | `FAIL_BUILD=0` rebuild exited `0` and produced `.rlib`. |

### OS Lock-Ordering Deadlock and File-Descriptor Exhaustion Recovery Controls

In `support/os-lock-fd-recovery-controls/probe.py` (`support/os-lock-fd-recovery-controls/results.json`, `support/os-lock-fd-recovery-controls/check.py`), three OS-level recovery controls were verified on Darwin `25.6.0` arm64:

| Control | Retained observation | Implication within fixture |
| --- | --- | --- |
| Opposite lock order (`A` takes `prepare` then `publish`; `B` takes `publish` then `prepare`) | Both first locks and second-lock attempts were marked; neither acquired its second lock after `200 ms`. `B` exited `-9` after `SIGKILL`; `A` then acquired its second lock and exited `0`. | Reversed acquisition order deadlocks; process death releases kernel advisory `flock` locks so surviving waiters progress. |
| Consistent lock order (both take `prepare` then `publish`) | `B` waited for `A`'s first lock, then both acquired both locks and exited `0`. | Strict global lock ordering (`prepare → publish`) avoids the deadlock cycle. |
| Candidate staging under child-only FD exhaustion (`RLIMIT_NOFILE = 32`) | Opening `29` extra descriptors made staging candidate `B` fail with `EMFILE` while the selected pointer still named `A`. After closing descriptors, `B` was staged and selected. | Staging artifacts before atomic pointer replacement preserves the last-known-good generation across `EMFILE` exhaustion. |

## Boundaries

- **Not examined**: An integrated Anneal multi-stage scheduler, daemonized processes that detach from their process group (`setsid`), high-parallel shared-cache stampedes across concurrent Cargo/Lake writers, same-process Charon/Aeneas library reset after mid-flight interruption, or power-loss/crash durability (`fsync` on directory entries).
- **Unknown**: Whether custom Lean tactics that do not poll `Core.checkInterrupted` can be interrupted mid-tactic without terminating the `FileWorker` process.
- **Known not to apply**: Parent process termination without process-group signaling does not guarantee descendant cleanup; parseability of one file (`charon --format all` JSON LLBC or Aeneas `Types.lean`) does not establish output-set completeness; and LSP `$/cancelRequest` (`-32800`) does not authorize terminating a shared upstream Cargo/Charon/Aeneas job while another consumer remains subscribed.

## Evidence

- **Active-barrier and graceful/kill CLI signal suites**:
  - `support/cli-graceful-cancel-signals/probe.py`, `support/cli-graceful-cancel-signals/ignore_int_supervisor.py`, `support/cli-graceful-cancel-signals/check.py`, `support/cli-graceful-cancel-signals/results.json.gz`, and `support/cli-graceful-cancel-signals/work/`.
  - `support/cross-tool-active-cancellation-barriers/probe.py`, `support/cross-tool-active-cancellation-barriers/gated_stage.py`, `support/cross-tool-active-cancellation-barriers/check.py`, `support/cross-tool-active-cancellation-barriers/results.json`, and `support/cross-tool-active-cancellation-barriers/work/`.
  - `support/cross-tool-stage-cancellation-cleanup/probe.py`, `support/cross-tool-stage-cancellation-cleanup/fence_oracle.py`, `support/cross-tool-stage-cancellation-cleanup/verify.py`, `support/cross-tool-stage-cancellation-cleanup/results.json`, `support/cross-tool-stage-cancellation-cleanup/fence-results.json`, `support/cross-tool-stage-cancellation-cleanup/aeneas-input.llbc`, `support/cross-tool-stage-cancellation-cleanup/cargo-fixture/`, and `support/cross-tool-stage-cancellation-cleanup/artifacts/`.
- **LSP cancellation, shared Cargo ownership, and OS lock/FD controls**:
  - `support/lsp-to-upstream-cancellation-boundaries/probe.py`, `support/lsp-to-upstream-cancellation-boundaries/check.py`, `support/lsp-to-upstream-cancellation-boundaries/results.json`, and `support/lsp-to-upstream-cancellation-boundaries/fixture/`.
  - `support/shared-cargo-consumer-ownership/probe.py`, `support/shared-cargo-consumer-ownership/check.py`, `support/shared-cargo-consumer-ownership/results.json`, `support/shared-cargo-consumer-ownership/fixture/`, and `support/shared-cargo-consumer-ownership/work/`.
  - `support/os-lock-fd-recovery-controls/probe.py` (SHA-256 `f137e4520adc6c793d20b3ecd073c2fed8ee74a1090a763a6c82742fe9aeec0e`), `support/os-lock-fd-recovery-controls/results.json` (SHA-256 `5fb284515ba1a9711d7381aba6a2e8e41284a5c18897b903d2c53ae10fde0b7f`), and `support/os-lock-fd-recovery-controls/check.py`.

## Revalidation

All six subprobes provide offline verification scripts that check retained transcripts, process-group snapshots, artifact digests, and fence/lock invariants without launching external compilers:
```sh
python3 support/cli-graceful-cancel-signals/check.py
python3 support/cross-tool-active-cancellation-barriers/check.py
python3 support/cross-tool-stage-cancellation-cleanup/verify.py
python3 support/lsp-to-upstream-cancellation-boundaries/check.py
python3 support/os-lock-fd-recovery-controls/check.py
python3 support/shared-cargo-consumer-ownership/check.py
```
To re-run the live cancellation and OS recovery experiments in a disposable copy of the package with the pinned toolchains installed, execute `support/cli-graceful-cancel-signals/probe.py`, `support/cross-tool-active-cancellation-barriers/probe.py`, `support/cross-tool-stage-cancellation-cleanup/probe.py`, `support/cross-tool-stage-cancellation-cleanup/fence_oracle.py`, `support/lsp-to-upstream-cancellation-boundaries/probe.py`, `support/os-lock-fd-recovery-controls/probe.py`, and `support/shared-cargo-consumer-ownership/probe.py`, then re-run the six offline verification scripts above.
