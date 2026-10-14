# Kraken requested-nightly build and selected proof replay

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Kraken's requested `nightly-2026-09-21` now builds from a fresh, exact source copy. Six unchanged selected proof files also replay successfully against that fresh library. The byte-leaf adapter and binding certificates retain their checked proofs; prior AArch64 and X64 leaf pilots pass as well. This completes the requested-toolchain portion of E27, while its broader ISA-validation work remains open.

## Applicability

The upstream source is [AeneasVerif/kraken 8af78062037bc237b341d20252aafd1797c1bcb7](https://github.com/AeneasVerif/kraken/tree/8af78062037bc237b341d20252aafd1797c1bcb7). The requested toolchain reports Lean `4.36.0-nightly-2026-09-21`, commit `ca39d2bc730f0382e4897ce314b93a4f168ff15e`. Its binary SHA256 is `a4c5d3dfc1672faf014e59bd17724035259ff0d22a4ffbdf5a75e142f564817e`. The independently checked Init.olean identity is recorded in [tool-identities.json](tool-identities.json).

This is a separate toolchain subject from the frozen Lean4.34.1 adapter package. No file in that earlier freeze was changed. Its package name and exact manifest identity are recorded in [companion-manifest.json](companion-manifest.json). Native compilation/execution and Mach-O import belong to that companion evidence; this package replays its unchanged concrete binding certificates with the requested nightly.

## Findings

### Fresh source and actual library build

[source-copy-manifest.json](source-copy-manifest.json) binds all 166 source files, totaling 598,992 bytes. Every copied source byte matched the read-only upstream snapshot; `.lake` and Git metadata were excluded. All 166 source identities remained unchanged after the build. No Lean4.34.1 objects or external build caches were imported.

Actual Lake invocations built 40 module targets covering the two library roots and Kraken submodules, including both example modules and tests within the selected library scope. The executable runners/translator were excluded explicitly in [build-order.json](build-order.json). Lake5 exposes no `-j` build option; invocations ran serially with `LEAN_NUM_THREADS=2` and `--no-cache`. Each log has at most one newly built module. An independent audit of all 98 local dependency edges, including `import all`, found no ordering violation. See [build-order-audit.json](build-order-audit.json), [build-results.json](build-results.json) and the preserved per-module logs.

### Selected proof sources and axiom closure

[selected-proof-sources.json](selected-proof-sources.json) records unchanged copied source hashes. [proof-results.json](proof-results.json) records all six exits and every inspected closure:

| Subject | Audited declarations | Result |
|---|---:|---|
| New byte/resource Adapter | 32 | Foundational axiom subset only |
| Concrete byte BindingCertificates | 8 | Foundational axiom subset only |
| Prior AArch64 addition leaf pilot | 2 | Foundational axiom subset only |
| Prior X64 addition/return/frame/host pilot | 19 | Foundational axiom subset only |
| Selected upstream AArch64 closure audit | 4 | Three foundational; arithmetic-shift theorem retains its native bv_decide axiom |
| Selected upstream X64 and separation-library audit | 7 | Five foundational; `p3_correct` and `dynamic_stack_example_correct` retain `sorryAx` |

The 61 owned/pilot declarations depend only on a subset of `propext`, `Classical.choice` and `Quot.sound`. Across the 11 upstream declarations, eight have that foundational subset, two contain `sorryAx`, and one contains `arith_shift_correct._native.bv_decide.ax_1_10`. Successful import/build does not remove these dependencies. The report does not describe all upstream theorems as closed.

### Pretty-printer diagnostic is separate from theorem checking

Both example modules still emit pretty-printer diagnostics in memory-tactic logging. Their builds exit zero. The selected final theorem closures can be inspected independently of those logs.

Source inspection identifies `Kraken/Tactics.lean` around lines 476–480: it obtains a generated subgoal's type and logs that expression without installing that subgoal's local context. The owned [PrettyContext.lean](support/PrettyContext.lean) recreates this mechanism using a detached local structure value. Its projection expression produces the same failed-pretty-print message outside `goal.withContext`, and prints correctly inside that context. See [pretty-context-projection.log](logs/pretty-context-projection.log). A simpler variable-only precursor prints a raw free-variable identifier outside the context and its name inside. The diagnostic-only theorem has no axioms.

This reproduces the local-context printing defect and bounds the observed failure to the diagnostic presentation path. No upstream source was patched, no fallback message was treated as a proof, and no unexpected panic, assertion failure or semantic disagreement occurred. It is not a general certification of every tactic diagnostic. The first diagnostic-probe elaboration failed because a module-system import was private; [pretty-context-attempt-01.log](logs/pretty-context-attempt-01.log) preserves that failed attempt, which is excluded from proof-success counts.

## Boundaries

The nightly replay changes the toolchain qualification of the selected proofs, not their semantic domain. The byte adapter still covers one admitted byte-load/return contract and its reviewed encoding transcription. It still lacks a formal Arm reference relation, verified Mach-O importer/loader, actual MiniRust allocation/provenance/borrow adequacy and whole Rust caller/context theorem. Arm GCS/tag/fault/address-translation and omitted architectural state remain external configuration obligations, as the companion report explains.

E27's requested-nightly subtask is discharged for the selected libraries and proofs. Motivated broader X64/AArch64 forms, faults, overlaps and SIMD validation are not completed by this build. E28/E30 remain partial scalar proof progress; E29 and E35 remain open. No Sail/Islaris/Jasmin/Vale/HOL proof port was run here.

## Evidence

[validation.json](validation.json) records source identity checks, successful commands, closure classifications, diagnostic counts, scratch-size bound and preservation of the earlier freeze. [tool-identities.json](tool-identities.json) records the exact requested nightly binary/Init and fresh library identities. All selected proof sources, per-command logs and portable helpers are preserved. Fresh generated build objects and the duplicate upstream checkout are excluded from the public projection; their relevant identities and source coordinates are retained.

## Revalidation

Provide the exact requested toolchain and an upstream source snapshot matching every entry in `source-copy-manifest.json`. In a fresh package replay copy, run:

```sh
python3 support/prepare_source.py /path/to/upstream-kraken-source
python3 support/build_nightly.py /path/to/requested-nightly-toolchain
python3 support/replay_proofs.py /path/to/requested-nightly-toolchain
```

The build helper uses real Lake commands with serial target invocation and two Lean runtime threads. The proof helper imports only the fresh local library, stops on failed commands/panic/assertion diagnostics, and rejects extra axioms in owned/pilot proofs. Review the separately classified upstream admissions/native axiom rather than treating their presence as an owned proof failure or silently ignoring them. The diagnostic reproduction is optional and is not part of the semantic proof corpus.
