# Support material

Text-only probes and their recorded outputs for the report in `../REPORT.md`.
Observation host class: x86-64 Linux workstation (96 vCPU Intel Xeon @ 2.60GHz,
shared, not isolated for benchmarking). Observed 2026-11-20.

| File | What it exercises | Reproduce |
|---|---|---|
| `py_division_probe.py` / `.out` | PEP 238 true vs floor division, int/float mixing, overflow on int->float | `python3 py_division_probe.py` (CPython 3.13.15) |
| `c_conversions_probe.c` / `.compile.out` / `.out` | integer promotions, usual arithmetic conversions, integer division into a double | `cc -std=c11 -O0 -Wall -Wextra -Wsign-compare -Wconversion -fsanitize=undefined c_conversions_probe.c -o c_probe && ./c_probe` (GCC 15.2.0, Debian 15.2.0-14) |
| `rust_casts_probe.rs` / `.out` | `as` cast semantics, `try_from`, `from`, checked/wrapping arithmetic | `rustc --edition 2021 -O rust_casts_probe.rs -o rust_probe && ./rust_probe` |
| `rust_mixed_e0277.rs` / `.out` | absence of implicit numeric promotion (expected compile failure) | `rustc --edition 2021 rust_mixed_e0277.rs` (exit 1; sysroot path redacted as `<rust-sysroot>`) |
| `clippy_casts_probe/` / `clippy_casts_probe.out` / `.run.out` | which pedantic cast lints fire, and which intent errors no lint sees | `cargo clippy` inside `clippy_casts_probe/`, then `cargo run` |
| `pint_probe.py` / `.out` | which unit mistakes pint catches at run time | `pip install "git+https://github.com/hgrecco/pint@072281c5f1b3d5fe30d097cbb0791be03ee24d45"` into a virtualenv, then `python pint_probe.py` |
| `pint_bench.py` / `.out` | pint per-operation overhead vs plain float; import/registry cost; peak RSS (two runs concatenated) | same virtualenv, `python pint_bench.py` |

Rust toolchain: rustc 1.102.0-nightly (commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, 2026-11-11), clippy 0.1.101.
