# R43: downstream effect of R42's `short_names` permutations

Observed 2026-09-29 with the locally pinned Aeneas CLI, Lean 4.30.0-rc2 and Lake 4.30.0-rc2. This is a direct component follow-up to [R42](../anneal-3730-charon-warm-noop-byte-diff-2026-09-29/REPORT.md), mapped to #3731 I079 and I148. R42 retained five source-unchanged LLBC files whose raw bytes differ only in `translated.short_names` entry order. R43 asks whether that order reached the generated Lean source or a fresh Lean/Lake consumer in this fixture.

## Procedure and oracle

The runner copied each of R42's five exact LLBC files to a private `probe.llbc` path, preserving the input SHA-256 while holding the input basename constant. It invoked the pinned Aeneas CLI with `-backend lean -no-progress-bar -sequential -split-files -gen-lib-entry -dest <private generated directory> <private probe.llbc>`. Separate destination directories retained every generated file. It compared whole-file SHA-256, byte length, declarations and imports.

Each variant then had a fresh, private direct Lean consumer. It compiled `Probe.Types`, the generated `FunsExternal_Template` copied verbatim to `Probe.FunsExternal`, `Probe.Funs`, and `Probe`, then batch-checked `Proof.lean`. The proof file checked the type of `r37u0.combined` and an equality-to-self theorem, printing that theorem's axiom inventory. The two path-dependency functions are **axioms in Aeneas's external-function template**, so the check establishes elaboration and import acceptance, not a model of their Rust behavior or a refinement theorem.

Each variant also had a fresh private Lake project declaring the locally cached Aeneas Lean backend as a path dependency. Its manifest named the already cached transitive packages and its temporary `.lake/packages` symlink pointed to the cached package tree; no package was pulled or installed. `lake build -v` compiled the four generated modules. After the five fresh builds, the run-1 Lake consumer was rebuilt once with no write, then four more times after copying the other variants' generated files over the **same source paths**. Those four copies updated source mtimes while preserving source bytes. Lake's own `Built`/`Replayed` lines, `.trace` files, and `.olean` identities were retained.

## Results

All five input LLBC SHA-256 values were distinct. All five Aeneas calls exited 0 and produced the same four Lean files byte for byte:

| Generated file | Bytes | Distinct SHA-256 values across five variants |
| --- | ---: | ---: |
| `Types.lean` | 506 | 1 |
| `FunsExternal_Template.lean` | 1,125 | 1 |
| `Funs.lean` | 893 | 1 |
| `Probe.lean` | 18 | 1 |

The declaration/import summaries also matched exactly: `Funs.lean` contained the same `def combined (x : Std.U32) : Result Std.U32 := do`, and the external-function template declared the same two dependency axioms. The five fresh direct Lean consumers all exited 0; their four corresponding `.olean` hashes matched across variants. Each proof printed `r37u0.combined (x : Aeneas.Std.U32) : Aeneas.Std.Result Aeneas.Std.U32` and reported precisely `[dep_a.dep_a, dep_b.dep_b]` for `combined_self`, with no `sorryAx`.

All five fresh Lake builds exited 0 and showed the four `Probe` modules as `Built`. The total Lake graph included 1,686 jobs, mostly replayed cached Aeneas dependencies; the four local `Probe` jobs are the relevant newly built subset. Across the five private Lake projects, `Probe.Types`, `Probe.Funs`, and `Probe` `.olean` hashes matched. `Probe.FunsExternal.olean` differed across private project paths despite identical source bytes; its retained bytes contain each private `run-N` pathname. That path-bearing artifact is a useful control against interpreting all fresh-project `.olean` hash differences as LLBC-semantic differences.

In the **same run-1 Lake project**, a no-write rebuild and all four same-path source replacements reported all four `Probe` modules as `Replayed`. The eight retained local `.trace`/`.olean` hashes and mtimes stayed identical to the first build after every rebuild. Thus, for this exact order-only LLBC variation and these pinned tools, Aeneas produced identical Lean bytes and Lake did no local Lean rebuild after replacement with the same bytes. The raw LLBC byte hash still churned; a cache keyed on raw LLBC would see five identities before Aeneas, even though the downstream generated source was the same here.

Aeneas calls took 236–259 ms, fresh direct Lean module/proof runs totaled 8.3–12.0 s per variant, fresh private Lake builds took 9.1–21.5 s, and same-path Lake replay took 1.8–2.3 s. These are sequential observations on a warmed local cache, not a speed comparison or scaling estimate.

## Revalidation and limits

From this checkout, run `python3 reports/anneal-3730-charon-shortname-aeneas-impact-2026-09-29/support/probe.py` to replace only this package's `support/work`, `support/logs`, and `support/results.json`. It requires the existing local pins and at least 5 GiB free disk; calls are sequential. Run `python3 reports/anneal-3730-charon-shortname-aeneas-impact-2026-09-29/support/check.py` to validate retained input/output hashes, raw command logs, direct Lean artifacts and axioms, fresh Lake builds, and unchanged replay traces without rerunning tools. `support/results.json` preserves all 40 exact invocations, cwd, exit status, elapsed time, log hashes, tool/artifact identities and comparisons. `support/logs/` contains their full stdout/stderr; `support/work/` retains all five copied LLBC variants, generated Lean files, consumers, OLeans and Lake traces. The runner itself is the replay specification.

This is one-shot Aeneas CLI behavior on a tiny crate with two external dependency axioms. It does not establish that arbitrary `short_names` reordering is semantics-preserving, that a general LLBC canonicalizer is sound, that Aeneas's same-process API resets state, or that annotation/obligation association remains correct in an Anneal workspace. I079 still needs broader inputs, same-process and provenance controls. I148 still needs the actual generated-file refresh/publishing path and fresh proof acceptance under substantive model changes; the observed no-rebuild result applies only after byte-identical Lean was supplied to Lake at the same paths.
