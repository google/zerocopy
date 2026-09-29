# Saved Rust subject versus a private materialized overlay

Observed 2026-09-29 on macOS arm64 with pinned Charon 0.1.210, Cargo/rustc nightly 2026-05-31. This bounded component experiment addresses #3730 D01 and #3731 I009/I015/I073–I080. “Overlay” here means a copied, path-isolated Cargo workspace with a private target and LLBC destination. It is not an in-memory rustc editor overlay or an Anneal scheduler.

## Fixture and exact units

The self-contained `support/fixture/` has an app library and independent binary, `build.rs`, a local proc macro, a path dependency, `include!` of generated Rust, `include_str!`, and `env!`. Each of ten requests copies it into an equal-length source path (`saved-00` or `overl-NN`), uses one Cargo job with incremental compilation disabled, runs offline and locked, and gets a distinct `CARGO_TARGET_DIR` and Charon destination. Equal path lengths hold the build script's `CARGO_MANIFEST_DIR` length input fixed, though the full source paths still differ.

Before each Charon request, the harness runs pinned `cargo build -Z unstable-options --unit-graph` with the same package/target flags and retains the complete normalized JSON under `support/graphs/`. The library graph has five units: `app_closure` library, build-script compile and run units, `dep_path` library, and `proc_local` proc macro. The independent binary selection adds a sixth unit. `support/results.json` retains every graph hash, exact source-file hash manifest, explicit environment inputs, selected package/unit, Charon command, full normalized verbose Cargo/Charon log, observed driver-unit sequence, generated Rust text, LLBC hash, and declaration projections. All ten LLBC files are retained in `support/artifacts/`.

The saved and clean overlay copies have identical relative source manifests, the same normalized Cargo unit graph, the same computed subject key (`f1c8ac4ffd7e…`), and identical projected declaration bodies. Their whole LLBC hashes differ (`40a41bade541…` versus `f061ff1c9aa3…`) because Charon also records source/destination path detail. This is a concrete distinction between the materialized source subject and raw output bytes.

| Private overlay change | Evidence relative to saved library |
|---|---|
| `BUILD_VALUE=7` → `8` | Build-script generated Rust and `BUILD_SUBJECT` declaration body change. |
| `PROC_VALUE=3` → `4` | Proc-macro-generated declaration body changes. |
| `include_str!` payload | `app_closure::root` body changes. |
| Path dependency `wrapping_add(11)` → `wrapping_add(12)` | Source/subject hashes change, and Cargo/Charon compile the dependency unit; the primary LLBC projected bodies do not change because the external dependency body is opaque in this extraction. |
| Proc-macro source `wrapping_add` → `wrapping_mul` | The LLBC function table includes `core::num::wrapping_mul`; the projected primary `root` body changes through the resulting function-ID graph. |
| `build.rs` expression | Generated Rust and `BUILD_SUBJECT` body change. |
| `PROBE_ENV=A` → `AA` | `app_closure::root` body changes through `env!`. |

All these library variants have the same *structural* five-unit Cargo graph. Source files and selected environment inputs distinguish their subject manifests. The path-dependency case shows why primary-crate body equality is not enough to prove identical source/build provenance.

## Stale output and wrong-unit controls

The harness computes a request subject key from relative source hashes, selected environment values, normalized unit-graph hash, requested package/unit, and pinned tool hashes. It deliberately asks its `reject` function to accept two changed overlay records under the saved key: a changed include payload and the opaque path-dependency edit. Both fail as `stale or foreign subject manifest`. This rejection is a small contract model layered on Charon outputs, not a native Charon feature.

A separate successful `--bin app_closure_cli` extraction produces parseable LLBC with `translated.crate_name=app_closure_cli`. Presenting it as an `app_closure` library result fails the harness's unit check: `wrong compilation unit: app_closure_cli`. A process exit of zero and parseable LLBC therefore do not identify the requested library unit. The fixture checks crate name and graph target selection; a production key must also cover package identity, target kind/triple, features/profile, host versus target roles, build inputs, and tool configuration.

## Replay and validation

From the checkout, using only the already installed pins:

```sh
python3 reports/anneal-3730-saved-vs-private-rust-overlay-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new-scratch-directory
python3 reports/anneal-3730-saved-vs-private-rust-overlay-2026-09-29/support/verify.py
```

The private work path must be absent. The probe requires at least 15 GiB free as a conservative guard; it overwrites this package's retained graphs/LLBC/results when rerun. The verifier checks all retained file hashes, ten private targets, subject keys, graph sizes, the saved/clean projection comparison, changed-input controls, and wrong-unit rejection. Whole LLBC hashes can change on replay as absolute work paths change; the qualitative and manifest assertions are the replay contract.

## Coverage boundary

D01/I009/I015 gain a concrete saved-versus-materialized-private-subject comparison and an explicit input/graph/tool identity key. I073–I080 gain controlled build-script, proc-macro, include, environment and path-dependency inputs, private outputs/targets, actual Charon commands, raw unit graphs, and stale/wrong-unit negative controls. This is still a tiny Cargo graph and a process-per-request experiment. It does not test a live unsaved editor buffer, arbitrary build-script side effects, all Cargo feature/target/profile combinations, nonlocal dependencies, native overlay APIs, same-process Charon reuse, concurrent target sharing, or Anneal's provenance, cancellation, and publication implementation. Those require separate integration evidence.
