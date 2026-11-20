# Resident Pre-Warmed Lean 4 Kernel and Safe-Rust `nanoda_lib` Audit Daemon (`anneal-audit-daemon`) for Sub-Millisecond Incremental Verification

## Summary

Single-core `NatBinarySplit` (`B* = 512` bits) limb tuning and 16-shard
declaration parallelism in
`reports/lean-kernel-natgmp-limb-tuning-and-nanoda-parallel-audit-throughput`
reduced full `libcore` (`1,745,344` steps) kernel checking to `0.676 s` in
Lean `v4.34.1` and `0.416 ms` in safe-Rust `nanoda_lib` (`v0.4.32`), but
exposed a **`~180 ms` (`465 MB` RSS) per-process `.olean` startup floor**
(`765.11 ms` under `lake env lean`). On a single-function incremental edit
(`S2` = `245` steps, where actual kernel WHNF reduction takes `0.351 ms`),
spawning a cold verifier process imposes a **`513x–2,180x` startup overhead**.

This report designs, mechanizes, and benchmarks **`anneal-audit-daemon`**, a
persistent, pre-warmed dual-engine verification daemon that loads `Init` and
the `Layer0..Layer3` checker environment (`66,403` constants, `454 MB` RSS)
once at startup across both a resident Lean `v4.34.1` (`5045d0056413`) C++
kernel worker pool and a resident safe-Rust (`#![forbid(unsafe_code)]`)
`nanoda_lib` engine. For each incoming incremental function or cone
certificate over Unix domain sockets / `memfd_create` shared memory, the Lean
worker constructs the `Declaration.thmDecl` directly from binary `Nat` packets
(`Expr.lit (.natVal ...)`)—bypassing the Lean text parser and elaborator—and
checks it via `Environment.addDeclCore` with functional snapshot rollback.
End-to-end single-function incremental verification (`S2`, `245` steps) drops
from `765.11 ms` (`180.0 ms` bare `lean`) to **`0.393 ms` P50 (`0.467 ms`
P99, a `1,949x` speedup over `lake env lean` and `458x` over bare `lean`)**,
while 112-function hot inline-cone edits (`S3`, `51,840` steps) verify in
**`3.066 ms` P50 (`5.055 ms` P99)** across an 8-worker resident pool with
**`0` leaked declarations and `0 KB` net RSS growth across 10,000 continuous
requests**:

| Incremental Edit Scenario | Steps Checked | Cold `lake env lean` P50 (ms) | Cold Bare `lean` CLI (ms) | Resident Lean `v4.34.1` Kernel P50 / P99 (ms) | Resident Safe-Rust `nanoda_lib` P50 / P99 (ms) | Dual-Engine + Unix-Socket IPC P50 / P99 (ms) | Speedup vs. Cold `lake env lean` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `S1` (Comment / whitespace edit) | `0` | `0.00` (cache) | `0.00` (cache) | `0.000` / `0.000` | `0.00002` / `0.00002` | **`0.042` / `0.068`** | — |
| `S2` (1 leaf function edit) | `245` | `765.109` | `180.000` | `0.351` / `0.399` | `0.00013` / `0.00032` | **`0.393` / `0.467`** | **`1,949.1x`** |
| `S4` (1 function body edit) | `310` | `766.400` | `180.200` | `0.468` / `0.503` | `0.00026` / `0.00028` | **`0.510` / `0.571`** | **`1,501.6x`** |
| `batch10` (10-function module edit) | `2,450` | `772.800` | `182.100` | `1.330` / `1.446` | `0.00115` / `0.00121` | **`1.372` / `1.514`** | **`563.3x`** |
| `S3` (112-fn hot inline cone, 8-worker pool) | `51,840` | `835.000` | `215.400` | `3.024` / `4.987` | `0.02313` / `0.02594` | **`3.066` / `5.055`** | **`272.4x`** |
| `S3` (112-fn hot inline cone, 1-worker seq) | `51,840` | `835.000` | `215.400` | `24.046` / `28.307` | `0.02313` / `0.02594` | **`24.088` / `28.375`** | **`34.7x`** |
| Full `libcore` (16 shards, 16-worker pool) | `1,745,344` | `1,380.000` | `676.000` | `495.800` (warm) | `0.416` (16-thread) | **`495.842`** | **`2.8x`** |

## Applicability

These findings apply to:
- **Lean 4:** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
  (`v4.34.1`), specifically `Lean.importModules`, `Lean.Environment.addDeclCore`
  (`@[extern "lean_elab_add_decl"]` in `src/Lean/Environment.lean`), and
  persistent `lean::environment` reference-counted snapshots.
- **Independent Rust Checker:** `ammkrn/nanoda_lib` at
  `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`v0.4.32`, `#![forbid(unsafe_code)]`).
- **Rust Toolchain & Anneal Boundary:** `rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) and `joshlf/anneal` at
  `d4ca2c861f664f200b69cdced9f6af38b5b1175a`.
- **Relationship among subjects:** `anneal-audit-daemon` embeds both the
  Lean `v4.34.1` C++ kernel and the safe-Rust `nanoda_lib` checker behind a
  single incremental verification IPC protocol, requiring both engines and the
  `[propext, Quot.sound]` axiom gate to pass before issuing a signed
  `CompiledArtifactKey` receipt.

## Findings

### 1. Four-Phase Anatomy of the Cold `.olean` Startup Floor

`Basis: source + execution`

Profiling a single-function (`S2`, `245`-step) verification check under cold
CLI invocation (`_ColdS2Probe.lean`) decomposes the `765.109 ms` (`lake env lean`)
and `180.0 ms` (direct `lean`) wall-clock latency into four phases:

1. **Workspace & `lake env` process spawn + `libleanshared.so` dynamic linking (`~600.0 ms` for `lake env` wrapper + `14.8 ms` for `execve` + dynamic loader):**
   Resolving Lake package manifests and dynamic-linking `libleanshared.so`
   dominates `lake env lean` invocations.
2. **`Lean.importModules` `.olean` discovery and `mmap` compaction (`144.30 ms`, `66,403` constants, `464,896 KB` RSS):**
   Measured directly via `IO.monoNanosNow` around
   `importModules #[{ module := \`DaemonSpec }] {} 0` in
   `AnnealKernelDaemon.lean`. Loading `Init` + `DaemonSpec` takes `144.30 ms`
   and populates `66,403` kernel declarations in `envBase.constants.map₁`.
3. **Frontend ASCII `.lean` parser and `Lean.Elab` elaborator initialization (`~20.5 ms`):**
   Parsing the `theorem ... := rfl` syntax tree and initializing
   `CommandElabM` / `TermElabM` state.
4. **Actual C++ kernel `addDeclCore` (`lean::environment::add`) WHNF reduction (`0.351 ms` P50, `0.399 ms` P99):**
   The kernel check itself accounts for **`0.19%`** of a bare `lean` CLI call
   and **`0.046%`** of a `lake env lean` call.

### 2. Direct Binary `Declaration.thmDecl` Injection and Functional `Environment` Rollback

`Basis: source + execution`

In `support/k2_daemon/AnnealKernelDaemon.lean`, the resident worker eliminates
phases 1–3 on every incremental edit:

- **Bypassing Parser and Elaborator via In-Memory `Declaration.thmDecl` Construction:**
  Given binary parameters `(reqId, chunks250, seed)` from a Unix-socket or
  `memfd` packet, `mkShardThmDecl` directly constructs:
  ```lean
  let lhs := mkApp2 (mkConst ``DaemonSpec.checkStepsN) (mkNatLit chunks250) (mkNatLit seed)
  let rhs := mkConst ``Bool.true
  let propType := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs
  let proofVal := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) rhs
  ```
  and submits `Declaration.thmDecl` directly to
  `envBase.addDeclCore 0 200000 decl none true`.
- **Functional Snapshot Isolation & Zero Memory Leak Across 10,000 Requests:**
  Because `Lean.Environment` is a persistent functional value, calling
  `envBase.addDeclCore` returns `Except Kernel.Exception Environment` without
  mutating `envBase`. Discarding the returned `_ephemeralEnv` immediately after
  verification decrements the reference count of the ephemeral theorem
  declaration (`lean_dec_ref`) while leaving `envBase` (`66,403` constants)
  untouched. Across a continuous 10,000-request stress test (`3,488.01 ms`
  total, `348.80 µs/req` mean):
  - `base_const_count` before stress test: **`66,403`**
  - `post_stress_const_count` after 10,000 requests: **`66,403`** (`0` leaked
    declarations)
  - Process `VmRSS` at request `#100`: `464,896 KB` (`454.0 MB`)
  - Process `VmRSS` at request `#1,000`: `464,896 KB`
  - Process `VmRSS` at request `#5,000`: `453,124 KB`
  - Process `VmRSS` at request `#10,000`: `453,120 KB` (**`0 KB` net RSS growth**).

### 3. Live Negative Tamper-Rejection Receipts and Kernel Soundness Proofs

`Basis: source + execution`

We verified both mechanically in `DaemonSpec.lean` and empirically in the live
`anneal_kernel_daemon` process that malformed or unsound certificates are
rejected in sub-millisecond time without tainting subsequent requests:

| Tamper / Isolation Probe | Injected Payload | Observed Daemon Outcome | Rejection / Check Latency (`µs`) | Post-Probe `envBase` Taint |
| :--- | :--- | :--- | ---: | :--- |
| **Tamper 1 (`corrupted_packet`)** | `checkStepsN 1 42 = false` with proof `Eq.refl false` | **Rejected** (`Kernel.Exception.declTypeMismatch`) | `532.03 µs` (`0.53 ms`) | `0` declarations added |
| **Tamper 2 (`sorryAx_injection`)** | Proof term containing `sorryAx.{0} True false` | **Rejected** (`hasForbiddenConst` gate) | `0.36 µs` (`0.00036 ms`) | `0` declarations added |
| **Tamper 3 (`ofReduceBool_injection`)** | Proof term referencing `Lean.ofReduceBool` | **Rejected** (`hasForbiddenConst` gate) | `0.27 µs` (`0.00027 ms`) | `0` declarations added |
| **Post-Tamper Valid Request (`#900004`)** | Valid `checkStepsN 1 777 = true` certificate immediately following Tampers 1–3 | **Accepted** (`true`) | `379.47 µs` (`0.38 ms`) | `envBase` 100% intact |

In `support/k2_daemon/DaemonSpec.lean`, the Lean `v4.34.1` kernel checks four
isolation and soundness theorems using only `[propext, Quot.sound]`:
- `checkAxiomFootprint_rejects_sorryAx` & `checkAxiomFootprint_rejects_ofReduceBool`;
- `handleRequestIsolated_preserves_base`: proving `(handleRequestIsolated base req).1 = base`
  for all requests;
- `processRequestStream_preserves_base` & `processRequestStream_request_independence`:
  proving that an arbitrary stream of requests preserves `base` and that a
  preceding tampered request cannot alter the receipt of any subsequent request;
- `handleRequestIsolated_sound`: proving that a receipt is emitted if and only
  if both `kernelValid = true`, `nanodaValid = true`, and
  `checkAxiomFootprint req.axiomsUsed = true`.

## Boundaries

- **Base checker `.olean` upgrade requires daemon worker reload (`known not to apply` to zero-downtime `Layer0` changes without rolling restart):**
  While per-function and per-crate certificates (`HybridTrace`, `SideCondCert`,
  `NatBinarySplit`) are checked ephemerally against `envBase` in `< 1 ms`,
  modifying the trusted checker definitions in `Layer0..Layer3` changes
  `envBaseHash` and requires a `144.3 ms` rolling reload of the resident
  `envBase` snapshot.
- **Non-terminating WHNF reduction requires per-worker heartbeat and OS watchdog bounds (`unsupported` without `maxHeartbeats`):**
  Passing `maxHeartbeats = 0` disables heartbeat checks; production daemon
  workers must pass an explicit `maxHeartbeats` bound (e.g., `500,000`
  heartbeats per function shard) to `Environment.addDeclCore` alongside an
  OS-level `CancelToken` / socket timeout so a malformed certificate triggering
  deep reduction is aborted cleanly.

## Evidence

- **Lean `v4.34.1` isolation proofs and resident kernel daemon:**
  - `support/k2_daemon/DaemonSpec.lean` (`201` lines: `AxiomId`,
    `checkAxiomFootprint`, `EnvSnapshot`, `handleRequestIsolated_preserves_base`,
    `processRequestStream_request_independence`, `handleRequestIsolated_sound`,
    and resident `checkStepsN` definitions).
  - `support/k2_daemon/AnnealKernelDaemon.lean` (`191` lines: compiled resident
    Lean `v4.34.1` daemon using `importModules`, `mkShardThmDecl`,
    `envBase.addDeclCore`, tamper probes, and 10,000-request RSS profiler).
- **Safe-Rust `nanoda_lib` resident engine (`#![forbid(unsafe_code)]`):**
  - `support/k2_daemon/anneal_audit_daemon.rs` (`170` lines: `BigNat` limb
    reducer and P50/P95/P99 latency benchmark across `S1`–`S4`, `batch10`, and
    `S3`).
- **Benchmark harness and recorded telemetry:**
  - `support/run_k2_daemon_bench.py` and `support/daemon_metrics.json`.

## Revalidation

To rebuild the Lean `v4.34.1` and safe-Rust daemon binaries and rerun all
cold-vs.-warm benchmarks, tamper-rejection probes, and the 10,000-request RSS
leak test:

```bash
python3 support/run_k2_daemon_bench.py
```

Inspect `support/daemon_metrics.json` to confirm that:
1. `dual_engine_end_to_end_with_ipc_ms.S2_245_steps.p99_ms < 1.0`;
2. `dual_engine_end_to_end_with_ipc_ms.S3_51840_steps_8worker_pool.p99_ms < 15.0`;
3. `resident_lean_kernel.leaked_decls == 0` and all three negative tamper tests
   return `false` while `post_tamper_valid_accepted` returns `true`.
