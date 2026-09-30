# Warm selected binary target: a bounded Charon producer control

Observed 2026-09-29 on macOS arm64 with Charon 0.1.210 and nightly Rust/Cargo 2026-05-31. This report adds a narrow `--bin subject_matrix_cli` control for [#3731 I075/I076](https://github.com/google/zerocopy/issues/3731).

## Distinct question

The [subject/output-phase matrix](../anneal-3730-charon-subject-output-phase-matrix-2026-09-29/REPORT.md) had one **cold** `--bin` request. The [warm-target controls](../anneal-3730-charon-warm-target-controls-2026-09-29/REPORT.md) selected `--lib` only. The [v34 warm multi-unit test report](../anneal-3731-i075-warm-multiunit-test-target-2026-09-29/REPORT.md) selected `--test check`; its warm destination contained the binary although the test driver ran. None retained a cold/warm same-source, same-target `--bin subject_matrix_cli` pair with distinct absent destinations. This cell asks whether the warm selected-binary request invokes a Charon producer and produces the requested binary LLBC under this pinned fixture and command.

## Executed pair

The retained fixture is a byte-for-byte copy of the dependency-free `subject_matrix` library, binary and integration test used in the earlier subject matrix. Two sequential calls used the same fixture pathname and unchanged contents, one private Cargo target directory, and fresh distinct destination paths:

`charon cargo --preset aeneas --dest-file <destination> -- --manifest-path <same Cargo.toml> --bin subject_matrix_cli --offline --locked -j 1 -v`

The runner cleared wrapper and Rust flag overrides, set `CARGO_NET_OFFLINE=true`, `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, and `RAYON_NUM_THREADS=1`, and used the already pinned tool paths. No install, download, network request or concurrent job was used. The second call retained the first call's Cargo target and was warm **only in the sense of target-directory reuse**. Its verbose stderr begins `Dirty subject_matrix ... couldn't read metadata for file ...libsubject_matrix-21be0fdd0836da51.rlib`; Cargo then recompiled the library and binary. This is a forced-dirty recompilation, not a cache-fresh hit. Full commands, environment, fixture/tool hashes, stdout/stderr and LLBC bytes are in `support/`.

| Cell | Charon driver crate order in verbose stderr | Exit | New destination's decoded `translated.crate_name` | LLBC SHA-256 |
| --- | --- | ---: | --- | --- |
| Cold baseline | `subject_matrix`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | `5d1ae9cb6d26d618985cd092fd0218faf1a3c6e2c188f77eebd8615fccf20580` |
| Warm repeat | `subject_matrix`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | `6021a295099927891f14c18bfbb0ec2b1e6b851f72b800f1c203443e9d5cbe0d` |

Both outputs parse as Charon 0.1.210 LLBC with `has_errors: false`. Both logs say `Compiling subject_matrix`, include complete `Running ... charon-driver rustc --crate-name ...` lines for the library and binary, and finish the dev profile. In this **retained-target, forced-dirty** case, the second call invoked its requested binary producer and created a new LLBC at an absent destination. Its serialized crate matches the requested binary. The different raw LLBC hashes are retained artifact identities; this cell does not infer a semantic difference or determine why their bytes differ. The run does not test whether a cache-fresh warm bin target would skip Charon or produce the same selected output.

The runner sampled `vm_stat` reclaimable memory (free + inactive + speculative divided by physical memory), disk free bytes, process-group RSS and owned scratch before and during each call. Lowest observed memory estimate was **23.012%**; minimum free disk **40,099,659,776 bytes**; maximum sampled process-group RSS **124,704 KiB**; maximum owned scratch **115,917 bytes**. Each call ended under one second and no guard fired. The private Cargo target, fixture copy and original destinations were removed after exact output retention. RSS samples are not physical peak or unique-memory measurements.

## Scope

- **I075, direct bounded component evidence:** a target directory retained from the first call did not prevent the selected binary producer from running, **because Cargo marked its cached library Dirty after failing to read the cached `.rlib` and recompiled both units**. This does not establish cache-fresh warm behavior. Other targets, wrappers, Charon/Cargo revisions, and an Anneal policy that requires producer attestation remain open.
- **I076, successful control only:** these two requests produced LLBC whose crate name matched the requested binary. The earlier warm `--test check` mismatch remains; this pair does not establish complete compilation-unit identity, output ownership, collision rejection or Anneal publication behavior.

`support/probe.py` is the executed guarded script. `support/results.json` retains per-call command, environment, samples, destination path/hash, recorded tool hashes and decoded crate name; `support/raw/` retains full stdout/stderr, including the Dirty reason; `support/artifacts/` retains both LLBCs. The read-only `python3 -B support/check.py` validates the **retained package** in place or after relocation, using candidate-local artifact bytes while preserving original destination and tool-path provenance. It compares the recorded tool hashes to report metadata but does not require those external binaries to exist or independently rehash them; tool attestation was performed during acquisition. It does not replay Charon.
