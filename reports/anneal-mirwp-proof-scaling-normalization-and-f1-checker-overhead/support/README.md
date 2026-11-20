# Support Bundle: Real-Kernel `Anneal.MirWp` Scaling & Normalization Benchmark

This directory preserves the runnable benchmark harness and complete real-kernel
measurement dataset backing `../REPORT.md`.

## Files & Digests

| File | Size (B) | Lines | SHA-256 | Role |
| :--- | ---: | ---: | :--- | :--- |
| `e2_8_real_anneal_mirwp_scaling.json` | `45,124` | `1,481` | `69638e2ce2dd1625b27baa0c8f8343fd29f554efc2c30476ba68cd561a718bc8` | Complete `Lean v4.34.1` real-kernel dataset (`64` timed benchmark configurations + helper/bridge compiles + kernel `Expr` DAG/tree counts). |
| `e2_8_real_anneal_mirwp_scaling.py` | `75,276` | `1,277` | `03d87c79268b62af465a86a035e21bd9b77cffe2ce2c3b62416d2cf3711546d1` | Standalone generator, synchronous `Lean v4.34.1` benchmark driver, and batch kernel `Expr` DAG/tree inspector. |

## Sanitization Record

Before public archival, workstation-specific absolute filesystem paths were
replaced with portable placeholders while preserving all numeric measurements,
Lean AST generators, and compiler diagnostics verbatim:

1. **`e2_8_real_anneal_mirwp_scaling.json`:** In the `6` `rc = 1` failure
   records (`Suite A K=16` × `4`, `Suite B K=64` × `2`), the workstation home
   directory and local cgroup wrapper path inside `/usr/bin/time -v` `stderr`
   strings were rewritten to `<LEAN_RUNNER> -- $HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean`.
   All `wall_sec_median`, `wall_sec_all`, `peak_rss_mb_median`, `olean_bytes`,
   `proof_loc`, `type_*`, `proof_*`, `stdout`, and metadata fields are
   byte-for-byte unchanged from the original measurement run (`2026-11-20T21:33:37Z`).
2. **`e2_8_real_anneal_mirwp_scaling.py`:** Hardcoded local directories were
   replaced with environment variables (`ANNEAL_OLEAN_CACHE`, `F1_1B_SRC`,
   `LEAN_BIN`, `LEAN_RUNNER_WRAPPER`, `OUT_JSON`). All generated Lean 4 modules
   (`E28Helpers`, Suites A–D, and `BatchInspect.lean`) are unmodified.

## Re-Running the Benchmark

1. Compile unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`
   (`Trusted.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`,
   `Anneal/MirWp.lean`) under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`
   (`v4.34.1`) into `$ANNEAL_OLEAN_CACHE`.
2. Point `F1_1B_SRC` to
   `reports/anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean`
   (SHA-256 `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c`).
3. Run:

```bash
ANNEAL_OLEAN_CACHE=/tmp/anneal_cache \
F1_1B_SRC=/path/to/AnnealTrustedMirMoveToCopyStorage.lean \
LEAN_BIN="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
OUT_JSON=/tmp/e2_8_reval.json \
python3 support/e2_8_real_anneal_mirwp_scaling.py
```
