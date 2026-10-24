# Local Cargo-to-Lean proof cost

*Authored by an AI agent acting on joshlf's behalf.*

All five archived PR #97 Cargo subjects now have proofs of the original acceptance
gates and of their accepted bodies' model results. The
[results report](../../../docs/rust-opsem/cargo-lean-cost-results.md) explains the
scope, cost measurements and remaining trust premises. The
[independent review](../../../docs/rust-opsem/cargo-lean-cost-independent-review.md)
checks that factoring the proofs preserved the original conditions and inputs.

## Replay

Start from this follow-up checkout with Python 3 and Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, already installed. Run from the repository
root. These commands use retained captures; they do not rerun Cargo or rustc.

```sh
python3 -B experiments/opsem/cargo-lean-cost/generate_components.py
python3 -B experiments/opsem/cargo-lean-cost/test_run_checks.py
python3 -B experiments/opsem/cargo-lean-cost/run_checks.py \
  --work-dir /absolute/path/outside/experiments/opsem/cargo-cost-replay \
  --label fresh --lean /absolute/path/to/lean \
  AnnealResearch.CargoLeanCostAllCases AnnealResearch.CargoLeanCostControls
```

Choose a new, initially empty work directory for a completely fresh proof replay.
Use a new label for each invocation: an existing log directory causes refusal.
To check cache reuse, repeat the last command with `--label warm` and the same
work directory. To reproduce the four isolated cost comparisons, use another new
label and these targets:

```sh
python3 -B experiments/opsem/cargo-lean-cost/run_checks.py \
  --work-dir /absolute/path/outside/experiments/opsem/cargo-cost-replay \
  --label diagnostics --lean /absolute/path/to/lean \
  AnnealResearch.CargoLeanCostOriginalGate \
  AnnealResearch.CargoLeanCostCold2BindingGround \
  AnnealResearch.CargoLeanCostCold2NativeGround \
  AnnealResearch.CargoLeanCostCold2Monolithic
```

The runner compiles the local import closure serially with
`-j1 -M2048 -DElab.async=false --profile`. Each compiler process has a 60-second
deadline and a 3-GiB sampled direct-process RSS stop. Sampling is not a hard OS or
process-tree limit. A failure stops the run; there is no automatic cap increase.
The runner uses `ps` RSS sampling and was exercised on macOS. A different host
needs its resource observer checked before interpreting its measurements.

The external cache has one writer. Reuse requires matching Lean version, source
SHA-256, direct dependency object hashes and current object hash. Missing,
corrupted or symlinked object files do not qualify. This is a cooperative local
cache, not a verified build system or protection against malicious concurrent
changes. No compiled objects are distributed in this evidence package.

## Inputs and proof organization

The baseline is PR #97 at `0d9f615ccb5898c699aae96de01ce8e817a40c18`. The user
explicitly authorized this bounded follow-up on 2026-10-19. Only that concrete
Cargo proof frontier was reopened; other historical resource stops stay closed.

The generator checks 14 pinned inputs, rehashes all 105 archived members, and
reparses the five raw captures to their retained canonical records. All 21 file
identities per binding, bodies, keys and requested results stay exact. Absolute
paths in inventories remain historical metadata, not paths the generator reads.
The generator reproduces 68 modules; three additional diagnostic modules retain
small isolated checks extracted from the original definitions/source.

Named definitions share complete records. Component lemmas establish the original
binding, identity, type/layout, key, encoding, fingerprint, bridge, admission,
decode and closure predicates. Composition proves the original `checkLifecycle`,
exhibits an original `acceptLifecycle` result, and proves execution of that
result's actual bodies. A kernel-checked equality connects literal bridge bytes
to the original computed bridge. No predicate, manifest or semantic condition is
removed; no new project axiom or `native_decide` is used.

The original failed source and diagnostics remain unchanged under
[post96-pipeline](../post96-pipeline). Acquisition, compiler/OS observations,
hashing, Python transcription and model adequacy retain their reviewed-premise
status. These finite terminal proofs do not prove Rust-to-model refinement or
all-prefix UB freedom.

## Recorded evidence

[evidence/fresh/results.json](evidence/fresh/results.json) records the empty-cache
84-module replay. [evidence/warm/results.json](evidence/warm/results.json) records
84 matching cache entries and zero proof jobs. The
[diagnostic results](evidence/diagnostics/results.json) record four additional
compilations and their matching cached dependency identities. Raw profiles and
stdout/stderr sit beside each result. Source hashes, the final 88-module cache
index, artifact hashes and lightweight cache regression output are also retained.
The old exploratory cache was not used for any of these portable replay results.
