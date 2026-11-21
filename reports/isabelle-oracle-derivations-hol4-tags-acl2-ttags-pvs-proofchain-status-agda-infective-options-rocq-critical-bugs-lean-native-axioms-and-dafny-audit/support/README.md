# Support material

Text-only probes and raw outputs cited by `../REPORT.md`.

- `lean-probe/` — two-module Lake project (`lean-toolchain`: `leanprover/lean4:v4.35.0`).
  `Probe/Base.lean` holds theorems A–G and nine `#print axioms` commands;
  `Downstream.lean` imports the compiled module and re-queries eight declarations.
  `time_print_axioms.sh` compares the downstream file with and without its
  `#print axioms` lines (create `DownstreamNoPrint.lean` with
  `grep -v '#print' Downstream.lean > DownstreamNoPrint.lean` first).
  Reproduce: `lake build -v`, `lake env lean Downstream.lean`, `lake check`,
  `lake check --paranoid` (needs `bwrap`).
- `lean-probe-v4291/ReduceBool.lean` — direct use of `Lean.ofReduceBool`; run with
  the v4.29.1 and v4.35.0 `lean` binaries.
- `incident-counts/` — `count_critical_bugs.py` parses Rocq `dev/doc/critical-bugs.md`;
  `label_counts.sh` and `catalogue_coverage.py` query the GitHub search API through an
  authenticated `gh` CLI (read-only).
- `outputs/` — raw outputs from 2026-11-21. Home-directory and probe-root paths are
  rewritten to `~` and `<probe-root>`; lines printed by a local resource-limit wrapper
  were removed. Wall-clock times in the two `lake check` outputs include waiting for a
  host-wide build lock and are not measurements.
