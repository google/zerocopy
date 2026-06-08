# rust-anneal-playground investigation

## Project wiring

`platonicsock/rust-anneal-playground` is a fork of the Rust Playground. The
Anneal integration is intentionally thin:

- The frontend sends the execution-tool value `anneal-verify`.
- The Axum server parses that into `ExecutionTool::AnnealVerify`.
- The orchestrator maps it to `cargo anneal verify`.
- `compiler/base/Dockerfile` currently installs `cargo-anneal` version
  `0.1.0-alpha.23` and runs `cargo anneal setup` while building the compiler
  image.

The relevant source locations in the playground checkout are:

- `ui/frontend/actions.ts`: `performCargoAnnealOnly`
- `ui/src/server_axum.rs`: `parse_execution_tool`
- `compiler/base/orchestrator/src/coordinator.rs`: `ExecutionTool::AnnealVerify`
- `compiler/base/Dockerfile`: `cargo install --locked cargo-anneal --version 0.1.0-alpha.23`

HTTP requests build a fresh coordinator and shut it down at the end of the
request. WebSocket sessions keep a coordinator alive for the session/idle
window, so repeated requests in one live session can reuse the same compiler
container.

## Reproduction

I reproduced the workflow with a single-file playground crate containing the
`checked_add` Anneal example. I compared two manifests:

- `minimal`: a tiny `Cargo.toml` with only the `playground` package.
- `playground`: a copy of `compiler/base/Cargo.toml`, which is the real
  playground top-crates manifest.

The reproducer is `reproduce_playground_workflows.sh`. It creates both crates,
runs `cargo metadata`, `cargo-anneal generate`, and `cargo-anneal verify`, and
captures stdout/stderr/timings under `results/`.

Manual probe timings from this machine:

| Case | Elapsed | Key trace time |
| --- | ---: | --- |
| minimal `cargo metadata --no-deps` | 0.01s | n/a |
| playground `cargo metadata --no-deps` | 0.02s | n/a |
| minimal `generate` | 0.70s | Charon 0.13s, Aeneas 0.39s |
| minimal first `verify` | 11.99s | Charon 0.09s, Aeneas 0.39s, Lake 8.11s |
| minimal second `verify` | 6.27s | Charon 0.09s, Aeneas 0.39s, Lake 2.38s |
| playground first `generate` | 37.99s | Charon 32.99s, Aeneas 0.39s |
| playground second `generate` | 1.50s | Charon 0.49s, Aeneas 0.39s |
| playground warm `verify` | 12.56s | Charon 0.49s, Aeneas 0.39s, Lake 7.88s |
| direct Lake build with no rewrite | 0.81s | no Anneal regeneration |
| `lake env true` | 0.40s | Lake environment startup only |
| direct `lean --json` diagnostics | 3.13s | with cached `LEAN_PATH` |

The first playground-manifest run created a `target/anneal/cargo_target` tree of
about 2.8 GiB with hundreds of compiled dependency artifacts. The second run was
fast because that private Anneal target tree was warm.

## Bottlenecks

The playground-specific slowdown is not Aeneas. Aeneas stayed near 0.4s in all
small-code experiments.

The large first-run cost is Charon invoking Cargo against the real playground
manifest. Even though Charon receives `--start-from crate::checked_add`, Cargo
still has to prepare the package dependency graph described by
`compiler/base/Cargo.toml`. Anneal v1 deliberately sets `CARGO_TARGET_DIR` to
`target/anneal/cargo_target`, so this work does not use the normal
`/playground/target` directory built by the playground Dockerfile.

Using the normal target directory is not an obvious Anneal fix. The Anneal
toolchain's Rust is `rustc 1.98.0-nightly (2026-05-30)` in this local archive,
while the playground compiler image builds ordinary Rust artifacts using its
selected stable/beta/nightly channel. Cargo fingerprints are toolchain-sensitive,
so the existing prebuilt `/playground/target` artifacts are not guaranteed to be
reusable by Charon. Mixing Anneal's Rust artifacts into the ordinary playground
target directory would also make the normal Rust Playground paths noisier.

The Lean-side floor for this example is roughly 4-5 seconds when dependencies
are warm:

- `lake build` with no regenerated sources is under 1s.
- `lake env lean --json` diagnostics are around 3s.
- `lake env` startup itself is only about 0.4s, so replacing `lake env lean`
  with direct `lean --json` plus cached `LEAN_PATH` is not a major win.

Current Anneal regeneration swaps in a fresh Lean source tree each run, so Lake
does more work than the no-rewrite case even when generated files are identical.
Preserving mtimes for unchanged generated Lean files would likely save around
1-2s on repeated identical runs. That is a modest win and adds implementation
complexity; it is not the main playground bottleneck.

## Recommended playground-side changes

The cleanest high-impact fix is in the playground image/build strategy:

- During the compiler image build, after `cargo anneal setup`, run an Anneal
  command against the real `compiler/base/Cargo.toml` with a tiny annotated
  `src/main.rs`. `cargo anneal generate` is enough to warm Charon/Cargo without
  paying the Lake proof build.
- Keep the resulting `target/anneal/cargo_target` in the image. This moves the
  30s-plus first Charon/Cargo cost from user request latency to image build
  time.
- Use WebSocket execution for interactive sessions where possible, because a
  live session can reuse the same coordinator/container and its warmed
  `target/anneal` tree.

The Dockerfile already runs `cargo build`, `cargo build --release`, and
`cargo clippy` to prewarm the ordinary Rust Playground cache. Anneal needs an
analogous prewarm for its private `target/anneal/cargo_target`.

## Anneal v1 changes

I did not find a concrete, clean, complexity-reducing Anneal v1 code change to
commit for this task.

The already-pushed symlink-free setup branch helps the playground indirectly by
removing per-run vendor copies/symlinks and making archive setup simpler, but it
does not change the main playground bottleneck: the first Charon/Cargo run over
the full top-crates manifest in a cold Anneal target directory.

Potential Anneal improvements exist, but they are not obvious fixes to push from
this investigation:

- Preserving mtimes for unchanged generated Lean files could shave repeated
  verify runs by roughly 1-2s.
- Caching `LEAN_PATH` and invoking `lean --json` directly instead of
  `lake env lean --json` saves at most a few tenths of a second in this probe.
- A standalone/non-Cargo extraction mode could be very fast for snippets with no
  external crates, but preserving correctness for arbitrary playground code that
  may use top-crates dependencies would require a new design.
