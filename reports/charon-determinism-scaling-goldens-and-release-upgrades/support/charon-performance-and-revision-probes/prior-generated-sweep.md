# Generated Charon size sweep (2026-09-27)

Ran three serial repetitions each on generated crates with 10, 100, and 1,000 independent small public functions. The local Charon release binary/hash and Rust compiler are recorded in [`summary.json`](summary.json); exact argv, exit codes, child times/RSS, and emitted bytes are in [`runs.jsonl`](runs.jsonl). [`generate.py`](generate.py) and [`measure.py`](measure.py) reproduce the fixture and bounded runner. Each process had a 60-second timeout; disk and system memory were checked before runs. Minimum system-wide free memory was 52%, and disk availability stayed at 71 GiB.

| Functions | Declarations | LLBC bytes | Median wall time | Child max RSS range |
|---:|---:|---:|---:|---:|
| 10 | 11 | 33,433 | 0.051 s | 103,464,960–103,530,496 B |
| 100 | 101 | 303,310 | 0.062 s | 106,217,472–106,463,232 B |
| 1,000 | 1,001 | 3,044,692 | 0.145 s | 132,562,944–133,136,384 B |

All nine corrected runs exited 0, reported `has_errors: false`, and contained the expected local function count. The extra declaration is a referenced foreign `wrapping_add`. The first 10-function run took 0.300 s and was treated as a startup outlier when reporting its median.

This is direct extraction without Cargo builds, on one simple-function template and one host. It does not measure bodies with complex control flow, dependency chasing, many-root resolution, Cargo/workspace overhead, whole-crate scaling beyond 1,000 functions, or process-tree RSS. Do not extrapolate a performance slope from these three points.
