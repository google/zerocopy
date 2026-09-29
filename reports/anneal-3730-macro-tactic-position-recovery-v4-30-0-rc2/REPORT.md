# Direct Lean macro tactic goal positions through unsolved and solved edits

## Summary

For one pinned Lean 4.30.0-rc2 direct server, an unsolved macro tactic, a solved edit, and restoration of the unsolved text produced matching live and fresh-batch success/failure classifications. At the same tactic-line positions, `plainGoal` showed the incoming `h : True ⊢ True` before the tactic, then either that open goal or `no goals` after the macro token depending on the current edit. Exact cursor position and current document version matter even for a tiny macro expansion. This adds an actual macro-expanded tactic cell to the existing nested/unsaved position grids; it does not establish generated Rust-to-Lean proof mapping.

## Applicability

The probe ran the cached `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` arm64 binary with `LEAN_NUM_THREADS=1`, direct `lean --server`, and fresh `lean --json` processes. The one-file fixture declares `solve_macro term` as a tactic macro expanding to `exact term`, then edits `solve_macro ?_` (version 1) to `solve_macro h` (version 2) and back to `solve_macro ?_` (version 3). There are no imports, Lake project, plugins, generated Anneal wrapper, or Rust host source. The server received full-text `didChange` notifications at versions 2 and 3; every version completed `waitForDiagnostics` before eight position queries. The host had 51% reported free memory at preflight.

The corresponding #3731 I043 residual names macros, generated proofs, a source map, and broader position classes after the v15 nested grid. This report addresses only the direct Lean macro control. It also informs #3730 C02's plain-goal-versus-rich-RPC boundary; rich RPC was not queried.

## Findings

| Version | Fresh `lean --json` | Live diagnostics | `plainGoal` at tactic line 3, column 8 | Incoming goal at line 3, column 0 |
| --- | --- | --- | --- | --- |
| 1, `solve_macro ?_` | Exit 1; placeholder synthesis and unsolved-goal errors. | Same two error classes at version 1. | `h : True ⊢ True`. | `h : True ⊢ True`. |
| 2, `solve_macro h` | Exit 0. | Empty at version 2. | `no goals`. | `h : True ⊢ True`. |
| 3, `solve_macro ?_` | Exit 1; placeholder synthesis and unsolved-goal errors. | Same two error classes at version 3. | `h : True ⊢ True`. | `h : True ⊢ True`. |

The probe also sampled columns 2, 14, 16, and 20 on the tactic line and columns 0 and 2 at the following empty line. In versions 1 and 3, columns 0–16 and following-line column 0 returned the open goal; column 20 and following-line column 2 returned null. In solved version 2, columns 0–2 returned the incoming goal, columns 8–16 and following-line column 0 returned `no goals`, and the same two beyond-range positions returned null. These are exact LSP positions in this source; they should not be generalized to other whitespace or macro shapes. Basis: **execution**, `support/results.json` `cases[*].positions`, batch outputs, diagnostics, and 107 retained harness wire events.

The fresh-batch results and live diagnostics agree on whether this one theorem closes, while the current-position goal query is finer grained: the incoming goal remains visible before a successful tactic. A caller must avoid interpreting a goal sampled before the tactic as a failed final proof. Basis: **derived** from the position table and independent batch exits.

## Boundaries

- One tactic macro and one theorem were tested. The experiment does not cover term macros, nested macro expansions, generated declaration locations, recovery from malformed macro syntax, or a broad whitespace/comment grid.
- `plainGoal` was queried, not `Lean.Widget.getInteractiveGoals` or context-reference RPC. No lifetime or version envelope was implemented.
- The source file on disk was updated to the same bytes as each live version before fresh batch compilation. The LSP input itself was sent as document text; this does not test unsaved disk divergence.
- The probe does not implement an Anneal annotation parser, generated proof, source map, worker broker, or Rust-level verification claim.
- An LSP `no goals` result is local goal guidance; this fixture's fresh batch exit is a separate check and does not establish complete obligation coverage or trust assumptions.

## Evidence

- `support/probe.py`, SHA-256 `5036644080d121bcfb674a94dd865144ca286b178db88b65ed31103c2274b8c9`, constructs the fixture, runs the three versioned server/batch cells, and asserts the decisive positive/negative outcomes. It reuses only class/function definitions from the prior URI harness, pinned by SHA-256 `9d5d5c7e3d85e8679e1ee04f9f8df485d163be3bd0eebaa0ffadaf27f7dc50a7`; that harness's experiment entry point is guarded.
- `support/results.json`, SHA-256 `66be28d077c110dc3a57b9a2e2077eb18a2fdc8f961f0d2698d35514af557c69`, retains full versioned source, batch stdout/stderr, wait replies, diagnostics, eight goal replies per version, binary/probe/harness hashes, and 107 direct protocol events.
- `support/check.py` checks the retained positive/negative controls offline. `support/work/Macro.lean` retains the final source bytes; earlier versions are in the JSON. The previous `anneal-3730-nested-tactic-position-grid-v4-30-0-rc2` and `anneal-3730-nested-unsaved-recovery-grid-v4-30-0-rc2` reports provide the non-macro controls.

## Revalidation

Run `python3 support/check.py` to verify the retained result. On the cached pin and with at least 25% reported free memory, run `python3 support/probe.py` and then the checker to repeat. The probe replaces only its own `support/work` and `support/results.json`. For an Anneal product test, generate a macro-containing proof from real Rust annotation source, map queried positions back to authored Rust, bind the response to exact version/import identity, and compare the complete obligation set with fresh batch verification.
