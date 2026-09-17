# Anneal Playground Performance Notes

## Goal

Make Anneal Playground verification fast in the places users feel, and be able
to explain the improvement with measurements.

The core interview framing is:

> I separated setup latency from steady-state verification cost.

That means "efficient" is not one number. It is a set of measured boundaries:
what the Docker image pays once, what the first verification pays, what repeated
verifications pay, what the backend adds around the verifier, and what
`cargo anneal verify` itself costs.

## Test Workload

Use one tiny Anneal example for all before/after runs unless a change is
specifically about proof complexity.

```rust
/// ```anneal, unsafe(axiom)
/// ```
pub unsafe fn anneal_warmup_identity(x: u32) -> u32 {
    x
}

fn main() {}
```

This example is intentionally boring. It still exercises the Anneal pipeline
through Cargo, Charon, Aeneas, generated Lean, Lake, and diagnostics, but avoids
turning the benchmark into a `scalar_tac` or user-proof benchmark.

## Timing Buckets

### Docker image build time

Definition:
Time to produce the `rust-stable` compiler sandbox image used by the playground.

Measure:
From starting `compiler/build.sh` to the completed `rust-stable` image/tarball.
Record whether Docker layer cache was warm or cold.

Includes:
- Rust toolchain install or reuse
- playground compiler crate builds
- `cargo-anneal` install
- `cargo anneal setup`
- any build-time Anneal warmup verification
- Docker layer export/copy

Excludes:
- backend rebuild
- frontend rebuild
- backend restart
- browser request time

Why it matters:
This is deployment/setup latency. Increasing it can be acceptable if it removes
runtime cost, but the tradeoff must be explicit.

### First/cold Anneal verification run

Definition:
The first successful Anneal Verify request after starting the backend with the
target image, using the chosen tiny workload.

Measure:
End-to-end backend/request duration and inner `cargo anneal verify` duration for
the first run.

Includes:
- request parsing and queueing
- container selection or startup
- file deletion/writes
- Cargo.toml modification
- `cargo anneal verify`
- output streaming and response finalization
- first-use cache checks or materialization that survived image build but not
runtime startup

Excludes:
- Docker image build
- frontend asset build
- manual browser clicking delay

Why it matters:
This is the first user impression after deploy/restart. It should not redo work
that could have been baked into the image.

### Warm repeated verification run

Definition:
The same Anneal Verify request repeated in the same deployment state after one
successful cold run.

Measure:
Run the exact same tiny workload at least three more times. Report each run,
then median and range.

Includes:
- normal backend orchestration
- normal sandbox execution
- `cargo anneal verify`
- any reusable runtime artifacts that legitimately survive between runs

Excludes:
- Docker image build
- backend restart
- intentional cache clearing

Why it matters:
This is steady-state user cost. Warm runs should not rebuild the full
playground dependency graph, rematerialize unchanged Lean packages, or recreate
the whole workspace shape.

### Backend request overhead

Definition:
The time around the verifier: total backend request time minus the inner
`cargo anneal verify` time printed from inside the compiler container.

Formula:

```text
backend_request_overhead_ms =
  backend_execute_total_ms - cargo_anneal_verify_elapsed_ms
```

Includes:
- API/WebSocket receive path
- queue wait
- Docker container acquisition/start
- worker IPC
- deleting/writing source files
- modifying `Cargo.toml`
- command spawn overhead
- output streaming/collection
- response finalization

Excludes:
- time spent inside `cargo anneal verify`

Why it matters:
If `cargo anneal verify` is fast but the playground still feels slow, the
bottleneck is orchestration rather than verification.

### Actual `cargo anneal verify` time

Definition:
Wall-clock time spent inside the compiler container running:

```sh
cargo anneal verify --unsound-allow-is-valid
```

Measure:
Use the shell wrapper around the command to print:

```text
[anneal] starting cargo anneal verify at ...
[anneal] verification succeeded in N ms
```

Further decompose with `cargo_anneal` logs when available:
- resolve/scan
- Charon
- Aeneas
- generated Lean/spec writing
- Lake manifest/package materialization
- `lake build`
- Lean diagnostics

Why it matters:
This is the verifier cost after the playground has handed control to Anneal.
Previous logs showed Charon and Aeneas were small compared with total time, so
the hidden work around Lake/materialization must be measured directly.

## Correctness And Failure Accounting

Do not count failed runs as speed improvements.

Record failures separately with:
- command/run id
- exit code or signal
- timeout/OOM if present
- first meaningful error line
- whether any timing was partial

Examples:
- `SIGKILL` or exit code `137` is an OOM/resource-limit failure, not a slow run.
- browser timeout is a request-budget failure, not proof complexity.
- `mathlib not in manifest` is a cache/materialization correctness bug, not a
  valid benchmark result.

## Baseline Checklist

Before changing code, capture:

```text
date/time:
machine:
VM/provider:
CPU:
RAM:
swap:
disk free:
Docker version:
Git branch:
Git commit:
working tree status:
compiler image id:
cargo-anneal version:
Rust channel:
backend port:
backend env:
RUST_LOG:
test workload:
```

For timing, capture:

```text
docker_image_build_time:
cold_backend_total_ms:
cold_cargo_anneal_verify_ms:
cold_backend_overhead_ms:
warm_1_backend_total_ms:
warm_1_cargo_anneal_verify_ms:
warm_1_backend_overhead_ms:
warm_2_backend_total_ms:
warm_2_cargo_anneal_verify_ms:
warm_2_backend_overhead_ms:
warm_3_backend_total_ms:
warm_3_cargo_anneal_verify_ms:
warm_3_backend_overhead_ms:
failure_notes:
```

## Docker Image Build Measurement

Run the stable image build and keep the full log:

```sh
cd /root/rust-anneal-playground/compiler
CHANNELS_TO_BUILD=stable bash ./build.sh 2>&1 | tee /tmp/anneal-docker-build-before.log
```

After an optimization, run the same command with a new log name:

```sh
cd /root/rust-anneal-playground/compiler
CHANNELS_TO_BUILD=stable bash ./build.sh 2>&1 | tee /tmp/anneal-docker-build-after.log
```

Print only the two duration numbers, in milliseconds:

```sh
grep -h '\[anneal-build-timing\].*image=rust-stable.*event=finish' \
  /tmp/anneal-docker-build-before.log \
  /tmp/anneal-docker-build-after.log \
  | sed -E 's/.*elapsed_ms=([0-9]+).*/\1/'
```

Current measurements from the VM:

```text
current_successful_build_ms: 426586
current_successful_build_human: 7m 6.586s
immediate_cached_rebuild_ms: 1270
immediate_cached_rebuild_human: 1.270s
```

Interpretation:
The first number is the useful Docker image build duration for the current
state. The second number is a warm Docker cache-hit rebuild with no meaningful
work left to do. Keep both numbers, but compare future optimization work against
the first number when the Dockerfile/image layers are invalidated by the change.

## First/Cold Anneal Verification Measurement

After rebuilding and restarting the backend with timing logs enabled, run one
Anneal Verify request in the browser against the tiny test workload.

For a cold request measurement, restart the backend first. This clears the
backend's in-process identical-submission cache. It does not rebuild the Docker
image.

Use a dedicated backend log:

```sh
/tmp/playground-ui-cold.log
```

Print exactly two duration numbers from the first cold run, in milliseconds:

```sh
grep '\[anneal-verify-timing\].*event=finish' /tmp/playground-ui-cold.log \
  | tail -n 1 \
  | sed -E 's/.*backend_total_ms=([0-9]+).*cargo_anneal_verify_ms=([0-9]+).*/\1 \2/' \
  | tr ' ' '\n'
```

Interpretation:

```text
line 1: cold_backend_total_ms
line 2: cold_cargo_anneal_verify_ms
```

Then calculate:

```text
cold_backend_overhead_ms =
  cold_backend_total_ms - cold_cargo_anneal_verify_ms
```

## Biggest Avoidable Costs To Check First

Check these in order:

1. Runtime Anneal is accidentally verifying the full playground crate.
   Bad sign: logs show `/playground/target/anneal/cargo_target` and compile
   crates like `proc-macro2`, `quote`, `serde`, `zerocopy`, `gimli`, or
   `object`.

2. Build-time warmup uses a different path/package than runtime.
   Bad sign: warmup happens in `/tmp/anneal-warmup`, but runtime uses
   `/playground/anneal-workspace`.

3. The warmup directory is deleted after build.
   Bad sign: reusable `target/anneal` or Lake artifacts are removed before the
   final image layer.

4. Lean/Lake package materialization repeats unchanged work.
   Bad sign: logs say Lake has no previous manifest, runs post-update hooks, or
   rematerializes dependency packages every run.

5. Cargo target artifacts do not survive where Anneal expects them.
   Bad sign: every warm run recompiles the same Rust dependencies.

6. Runtime temp/cache directories fight Docker overlay behavior.
   Bad sign: cross-device link errors, writes into read-only image layers, or
   caches under paths that get recreated per request.

7. Docker memory limits turn performance work into OOM failures.
   Bad sign: Lean exits with code `137`, especially while compiling generated
   `Types.lean`.

## Optimization Rule

Make one narrow change at a time, then remeasure the full bucket table.

The preferred order is:
1. Make runtime verify a stable isolated crate.
2. Make build-time warmup use that same stable path and package name.
3. Preserve reusable Cargo/Lake artifacts that are safe to reuse.
4. Avoid baking fragile per-run generated Lean state into the image.
5. Limit concurrency or raise memory only after cache correctness is understood.

## Reporting Format

Use this shape after each experiment:

```text
Change:
Hypothesis:
What should improve:
What should not change:
Commands:
Result:
Before:
After:
Tradeoff:
Next:
```
