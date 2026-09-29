# I023: proof edits after the current Rust model fails

Observed 2026-09-29 with pinned Charon, one-shot Aeneas and Lean 4.30.0-rc2. The tiny saved Rust source first defined `inc(x: u32) = x + 1`. Charon and Aeneas succeeded, generated Lean modules compiled, and proof v1 of `last_good_probe.inc 0#u32 = .ok 1#u32` passed. The report records the exact source, LLBC, generated-file and proof hashes as **model A**.

Two subsequent revisions changed the intended `inc` body to `x + 2` while the Lean proof was edited. Revision B appended malformed Rust. Charon exited 2, but the `current.llbc` pathname remained populated with byte-identical model-A LLBC. Revision C was syntactically valid but added a raw-pointer dereference. Charon succeeded; Aeneas exited 1 and wrote a partial `Funs.lean` with both the new `inc` body (`wrapping_add x 2#u32`) and `sorry` in the unsupported function. Neither revision produced a complete current model. The exact commands, statuses, stdout/stderr, inputs and artifacts are retained in `support/results.json` and `support/work`.

| Experiment-side policy | B: syntax failure while proof changed to v2 | C: unsupported extraction while proof changed to v3 |
| --- | --- | --- |
| Stop interaction | Suppresses the Lean query; reports current Rust model unavailable. | Suppresses the Lean query; reports current Rust model unavailable. |
| Explicit last-good model | Runs v2 against **model A**; Lean exit 0, labeled **provisional / stale**, with both requested Rust B and model-A hashes; `current_verified = false`. | Runs v3 against **model A**; Lean exit 0, labeled **provisional / stale**, with both requested Rust C and model-A hashes; `current_verified = false`. |

This provides a concrete negative control: interpreting the old-model Lean exit 0 as current verification would mislabel both queries. B has no Rust model; C's generated model is partial and contains an admission. The freshness statuses, query suppression, and labels are **experiment-side policy records**, not metadata emitted by Charon, Aeneas, Lean, or Anneal. Lean batch proof checks stand in for proof interaction; no real Anneal UI, editor request, live goal RPC, or human/agent comprehension study was performed.

**I023 residuals.** This covers one saved-source syntax failure and one Aeneas unsupported-extraction failure after a valid model, with distinct proof edits and both policy responses. It does not measure usability, error comprehension, UI disclosure, unsaved overlays, multiple annotations, actual scheduler/publication behavior, changed function signatures, live goal/context query behavior, or repeated recovery after Rust becomes valid again. Those need a real Anneal implementation and, for comprehension, actual users or agents with the real interface.

**Replay.** From this directory run `python3 support/probe.py`, then `python3 support/check.py`. The standard-library probe replaces only this package's `support/work` and `support/results.json`, uses cached installed pins, requires more than 5 GiB free disk, and performs no installs. Copy the package first to preserve the original observation before replaying.
