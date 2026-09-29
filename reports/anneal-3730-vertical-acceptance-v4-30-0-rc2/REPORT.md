# Prototype batch/live claim acceptance with generation failure and late output

## Summary

A disposable prototype used one captured Rust comment annotation and a tiny generated Lean model to drive both a versioned Lean server edit/query path and fresh batch checks. For the A and B model generations, solved local goals agreed with fresh Lean compilation and a fixed proposition consumer. Three controls separated those meanings: an old proof failed against B's model, a weakened `True` theorem compiled but failed the fixed proposition consumer, and a theorem using `sorry` compiled and satisfied the proposition consumer while `#print axioms` exposed `sorryAx`.

A deliberately invalid intermediate generated module did not become the prototype's selected generation. An old A build blocked at a Lean tactic gate, finished after B was published, and its complete output was rejected by a monotonic revision fence. The three runs had the same classifications. This is **a prototype of an acceptance contract**, not execution of current Anneal, Charon, Aeneas, Lake, or a Rust/Lean soundness proof.

## Applicability

Lean was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on arm64 macOS, direct `lean --server` and `lean --json` with `LEAN_NUM_THREADS=1`. The executable SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. One small generated module and one proof were used per isolated directory. The local project source comparison was `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`; its current `anneal/src` does not implement this prototype engine or live server interface.

The prototype's Python `source_parts` function recognizes exactly a decimal `pub const MODEL_VALUE: u8 = N;` and `// anneal:` comment lines. It emits `Generated.lean` with `def modelValue : Nat := N` and projects the comment body into `Proof.lean`. This is a manual test translation for values 3/4/5, not Charon or Aeneas semantics. The source files and compiled outputs under `support/work/` and three raw event transcripts are retained. Each run used sequential direct Lean server sessions; only the late A compiler overlapped a failed F and valid B build. Peak concurrency was one compiler plus ordinary short build/check subprocesses, and no network or Mathlib was used.

## Findings

### One source/projection contract drives the two shells

The initial host bytes contain value 3 and an unfinished `exact ?_` annotation. The A host bytes keep value 3 and replace that tactic with `rfl`. The B host bytes change both value and intended claim to 4. The script records SHA-256 of every host, generated module, proof text, compiled `.olean`, and oracle text; paths are generation-specific. Its in-memory compare-and-swap host authority accepts the initial→A edit only under the initial source hash, later accepts A→F→B, and rejects a stale edit based on A after B is authoritative. That CAS is prototype code, not an editor or Anneal API.

The A live server opens the unfinished projected proof as version 1 and returns `⊢ modelValue = 3`. The proof file on disk remains at those unfinished bytes. It then receives the projected `rfl` proof as an unsaved version-2 `didChange`; after `waitForDiagnostics(2)`, the goal query returns `no goals`. Fresh `lean --json` over the exact captured version-2 proof exits 0 against A's imported `Generated.olean`. A second fresh Lean process compiles `Proof.olean`, and a fixed consumer imports it, checks `example : modelValue = 3 := claim`, and reports that `claim` depends on no axioms. This is **execution** evidence for this narrow Lean-level claim.

B's generated module changes `modelValue` to 4. B's projected proof, `theorem claim : modelValue = 4 := by rfl`, returns `no goals` in a fresh B server, exits 0 in fresh batch Lean, and passes `example : modelValue = 4 := claim` with no reported axioms. This is a same-input, same-artifact comparison between direct server and fresh batch in two small generations, not general batch/live equivalence. The server path and batch path share the prototype's projection logic; batch re-elaborates proof source in a fresh process while importing the compiled generated model.

### Failure and late completion remain attributed to their generations

After A is published as prototype revision 1, the authoritative host text advances to F (value 5). F's deliberately invalid `Generated.lean` (`def modelValue : Nat :=` with no term) makes `lean --json -o Generated.olean` exit 1 with `unexpected end of input`; no F artifact is selected. The transcript records F host revision 2 alongside **last-known-good A revision 1**, so A's prior acceptance is not relabeled as current verification of F.

Before that failure, an A rebuild was started in its own directory. A `run_tac` writes `gate.entered` and blocks on `gate.release`, providing a causal barrier. While it is blocked, F fails; then host authority advances to B and B's generated module, proof, and fixed-claim consumer pass. B publishes as prototype revision 3. Only then does the script release the gate. The late A compiler succeeds, its proof and consumer pass under its own old model, and the complete A-late candidate is rejected because revision 1 is older than selected B revision 3. The final pointer still names B with B's host/module/proof hashes. Basis: **execution** for Lean process ordering and output; **prototype execution** for the revision-fence decision. This does not prove durability or atomic publication under crash or parallel writers.

### Comparator controls separate proof status from claim status

| Captured case | Lean proof batch | Fixed expected-proposition consumer | Axiom query | Live goal where queried | Classification in this fixture |
| --- | --- | --- | --- | --- | --- |
| A final, model 3, claim `modelValue = 3` | exit 0 | exit 0 | no axioms reported | no goals | Lean-level claim accepted for A |
| B final, model 4, claim `modelValue = 4` | exit 0 | exit 0 | no axioms reported | no goals | Lean-level claim accepted for B |
| A proof against B model | exit 1, `rfl` mismatch | not compiled | unavailable | `⊢ modelValue = 3` | stale proof rejected |
| Weak B theorem `claim : True` | exit 0 | exit 1, type mismatch | no axioms reported | not queried | compilation does not preserve intended statement |
| Admitted B theorem `claim : modelValue = 4 := by sorry` | exit 0 | exit 0 | `sorryAx` reported | not queried | type matches, trust condition fails |
| F invalid generated module | generated-module exit 1 | unavailable | unavailable | not queried | preparation failed; A retained only as last-known-good |
| Late A output after B | exit 0 under A | exit 0 under A | no axioms reported | not queried | valid old output, rejected from current pointer |

The table is **execution** except its final classifications, which are **derived from the explicit fixture oracle**. The oracle has separate dimensions: exact host bytes, projected proof bytes, generated source bytes, imported `.olean` hash, local goal and diagnostics, proof-source compilation, fixed theorem proposition, and axiom report. It does not compare timing or `.olean` byte equality as theorem equivalence. The `#print axioms` output is checked for `sorryAx` in the prototype summary; the admitted control shows why a successful type consumer is insufficient when the intended assumption policy excludes admissions. The script keeps raw batch JSON and LSP messages in each transcript rather than normalizing away proposition or diagnostic changes.

### Fresh-process oracle strength and limits

Fresh `lean --json Proof.lean` re-elaborates the captured proof source; it imports the precompiled `Generated.olean` and therefore shares the manually generated model and Lean toolchain with the live path. Compiling `Proof.olean` and checking the separate `Oracle.lean` consumer tests that the exported `claim` has the intended Lean type. The axiom query checks a visible dependency report for this theorem. These steps do not independently retranslate Rust, recheck the imported artifact against Rust, establish obligation coverage, detect all possible trusted axioms, or prove the backend trustworthy. A clean local goal, zero batch errors, and a matching Lean proposition remain distinct observations.

### Backlog coverage and design delta

| Issue #3731 item | Evidence here | Remaining delta |
| --- | --- | --- |
| I001 minimal cross-mode contract | Exact fixture compares source/model/proof identity, proposition, axiom report, diagnostics, and goals | Real translation and obligation/subject identity across modes. |
| I006 stage API/error boundaries | Prototype generation, proof, oracle, failure, and publication records | Charon/Aeneas/Lake adapters, progress/cancellation/resource metadata, write inventory. |
| I129/I131 goal versus verification and fresh oracle | A/B live and fresh batch, stale/weak/admitted negatives | Later-file/sibling errors, larger imports, independent artifact/kernel audit, Rust coverage. |
| I132 comparator calibration | Weakened statement and admission defeat simpler success predicates | Wider semantic changes, diagnostics normalization, assumptions/TCB matrix. |
| I137/I138 vertical slices | Comment projection, hash-checked edit, A/B model, F failure, gated late A | Actual Anneal annotation syntax, Charon/Aeneas, Lake environment, integrated source map and lifecycle. |
| I140 agent proof edit | One scripted repair from placeholder to `rfl` | Human/agent trials, budgets, maintenance, intervention scoring. |
| I144 decision synthesis | Small evidence-backed fallback: separate local goal, batch, proposition, axiom, and selected generation | Ten-contract architecture synthesis after broader evidence. |
| I157 batch/live shells | One Python projection engine drives direct Lean server and fresh batch shells | Current CLI comparison, in-process live engine, cancellation and reconstruction matrix. |
| I159 falsification controls | Stale import, weak statement, admitted theorem, incomplete and late generation | Other simple alternatives and production-scale controls. |

A possible V2 result record would keep goal guidance, Lean file check, fixed claim/assumption check, and Rust-level coverage/TCB status separately. This is a **derived proposal**, not an adopted interface or a statement that the prototype's claim is a real zerocopy obligation.

## Boundaries

- **Not examined:** Charon, Aeneas, Lake, Cargo subject resolution, real Rust annotation parsing, actual Anneal CLI/batch path, editor or MCP transport, Rust-to-Lean semantic preservation, source mapping, proof coverage, and safety claims.
- **Not established:** global concurrency safety or crash durability. The late build is causally gated, but prototype pointer updates are single-process and sequential; no second publisher races the pointer write.
- **Not established:** full theorem/assumption equivalence from the fixed consumer. It checks one expected proposition and one axiom report, not all declarations, imports, proof terms, or metatheory.
- **Known not to apply:** the accepted A proof is not current during F's failed generation or after B publication. The pointer and host source hashes in the transcript make that distinction explicit.

## Evidence

- Executable script: [`support/run.py`](support/run.py). Invocation: `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/run.py`; it requires only Python 3 and the pinned Lean binary.
- Raw runs: [`transcript-run1.json`](support/transcript-run1.json), [`transcript-run2.json`](support/transcript-run2.json), [`transcript-run3.json`](support/transcript-run3.json). Each retains command argv/cwd, exit status, stdout/stderr JSON, protocol requests/notifications/responses, source and artifact hashes, host CAS decisions, gate order, publication decisions, and final pointer. Absolute local paths are replaced by `$WORK`, `$LEAN_BIN`, and `$LEAN_HOME`; the protocol ordering and hashes remain intact.
- Exact fixture inputs and generated outputs: [`support/work/`](support/work/). It contains A-initial, A, F-invalid, B, A-late, stale-on-B, weak-on-B, and admitted-on-B source files, current pointer JSON, and the small compiled Lean artifacts from the final run. `A-late/Generated.lean` includes the gate theorem; it is not byte-identical to A's generated module.
- Primary tool identity: Lean source `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; binary SHA-256 in each transcript. Project context is `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, but the Python prototype is only a report-owned fixture and does not run the project implementation.

## Revalidation

Run `support/run.py` with the pinned Lean binary and inspect the new `support/transcript.json`. Confirm the initial unsolved goal, A edited solved goal with unchanged disk proof hash, A/B fresh batch and fixed proposition success without reported `sorryAx`, F compiler failure, B publication before late A gate release, complete late A output rejected as stale, stale A proof failure under B, weak theorem's oracle failure, admitted theorem's `sorryAx`, and final pointer B. Repeat with separate immutable fixture directories for any new compiler version. A future real Anneal slice must replace the regex projection and hand-built model while preserving these comparator dimensions and negative controls.
