# Acceptance oracle matrix and its untested boundaries

## Summary

Seven disposable Lean fixtures separate proof-source compilation, a fixed expected-proposition consumer, imported-model identity, obligation presence, and reported axiom dependencies. A fresh process re-elaborated exact captured proof bytes with an identical imported `.olean`; a direct Lean server first showed an unsaved open goal and then `no goals` for the repaired bytes. A separately gated fresh consumer was killed after elaboration began: its status remained **interrupted/unknown** even though the local proof goal had been solved. Two runs agreed on these classifications.

The controls demonstrate why a local goal, compiler exit, matching Lean type, and allowed-trust status are distinct. They do **not** establish an Anneal Rust-level proof, independent translation, complete obligation coverage, or a human evaluation. This package combines the new controls with exact residuals from the already persisted vertical, agent, trust, fault, and architecture reports for [#3731](https://github.com/google/zerocopy/issues/3731) I126–I141, I143–I144, and I159.

## Applicability

The executed compiler and server are `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, on macOS arm64 with `LEAN_NUM_THREADS=1`. The script uses Python 3.14.7 standard-library subprocesses and JSON-RPC framing. Scratch files were created and removed under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731`; retained transcripts replace their paths with `$WORK`. No Mathlib, Lake, Charon, Aeneas, Cargo, Nix, editor, MCP transport, actual Anneal program, private source, real secret, or remote service participated in the new run.

Each synthetic fixture has a separate `Generated.lean`/`Generated.olean` defining `modelValue` and a `Proof.lean`. The fixed consumer imports the compiled proof, checks `example : modelValue = 4 := claim`, and runs `#print axioms claim`. The `missing_obligation` consumer additionally requires `missingClaim`. This is a **manually specified Lean-level acceptance relation**; it is not a generated Rust obligation manifest. The "fresh" test copies the exact good proof, fixed consumer, and imported `.olean` bytes into a new directory before launching three new Lean processes. It remains dependent on the same Lean binary, manually constructed model, and imported artifact.

The report uses prior packages for scope beyond the new fixture. In particular, `anneal-3730-vertical-acceptance-v4-30-0-rc2` contains the earlier Rust-comment-to-Lean prototype and its failing intermediate/late generation, `anneal-3730-agent-workflow-evaluation-v4-30-0-rc2` contains one agent repair comparison, `anneal-3730-trust-evidence-boundary-2026-09-29` contains build-script/proc-macro/Lean command execution and evidence minimization, and `anneal-3730-fault-model-2026-09-29` contains a bounded state-machine exploration. Their scopes remain as written; this package does not reclassify them as an integrated Anneal implementation.

## Findings

### The comparator catches four false-success patterns

| Fixture | Proof source | Fixed consumer | Axiom report | What a simpler green predicate misses |
| --- | ---: | ---: | --- | --- |
| Good, model 4 | exit 0 | exit 0 | none | Baseline Lean-level accepted claim. |
| Weak `claim : True` | exit 0 | exit 1 | none | Compiler success does not preserve the intended proposition. |
| Admitted claim | exit 0 | exit 0 | `sorryAx` | Type acceptance does not satisfy a no-admission policy. |
| New `cheat` axiom | exit 0 | exit 0 | `cheat` | A matching type can rely on a newly introduced axiom. |
| Wrong imported model 5 | exit 1 | not run | unavailable | Same proof bytes under a different imported artifact can fail. |
| Missing second claim | exit 0 | exit 1 | no axioms for first claim | One accepted theorem does not cover a required second obligation. |
| Instruction-shaped comment | exit 0 | exit 0 | none | The comment is source data; compiler acceptance gives it no task authority. |

The raw compiler JSON and the exact source/artifact SHA-256 values for both runs are in `support/transcript-run1.json` and `support/transcript-run2.json`; `support/acceptance-cases.csv` is an index, not a replacement for the raw records. The `good`, `weak`, `admitted`, `axiom`, and `missing_obligation` fixtures share the same compiled generated-model hash within each run, so the changed proposition, trust basis, and obligation list are the deliberately varied dimensions. `wrong_import` changes the generated artifact while keeping the good proof hash. The script asserts every expected classification. Basis: **execution** for Lean exits and `#print axioms`; **derived** for their acceptance interpretation under the stated fixed-consumer policy.

The comparator should therefore retain distinct fields for captured source/projection, imported environment and tool identity, declaration/proposition, declared obligation set, proof check, allowed axiom/taint set, and origin-labeled diagnostics. These fields form a **proposed contract**, not a proven sufficient set. Raw diagnostics must be kept alongside any normalized class: the weak theorem and missing obligation both produce consumer errors, but their causes differ; the admission and axiom controls both have compiler exit 0 yet different trust dependencies. A single `passed` boolean erases those distinctions. The fixture does not compare all declarations, axioms inherited through opaque compiled dependencies, native evaluation trust, or Rust-level correspondence.

### Fresh source elaboration, imported artifact, and server state are separate witnesses

The good proof and its `Generated.olean` were copied byte-for-byte to `fresh/`; a new `lean --json Proof.lean` process exited 0, a second new process emitted `Proof.olean`, and a third new process checked the fixed consumer with no reported axioms. The copied proof-source hash was `43e0059e223d61b85eff2a2aac8247c21dd370b681898b982a93eb7d106d1df7`; the imported `.olean` hash was `9ed8713387b59eaf45c0f261cb92ed8ad4663c86301973e57e73ea73f1441a38` in the second retained run. This is fresh **re-elaboration** of the captured source against a pinned artifact. It is not an independent compiler, independent kernel implementation, regenerated model from Rust, or a clean-from-source rebuild of every dependency. Basis: **execution**.

At the same URI, direct Lean LSP opened unsaved `exact ?_` proof bytes (SHA-256 `55e336d1cf04145d4d263a6429238dcfb1c835c4ed3794fff019fc5ab41b2a84`) while disk still held the good proof. After `waitForDiagnostics(1)`, `$/lean/plainGoal` reported `⊢ modelValue = 4`. A full-document version-2 change to the good proof, followed by `waitForDiagnostics(2)`, reported `no goals`. The LSP replies contain neither a statement-coverage result nor the fixed consumer/axiom checks. The earlier vertical report observed a complementary unsaved-good/disk-unfinished case. Basis: **execution** for direct Lean; **derived** for the acceptance boundary.

The harness then launched a new Lean compiler on `InterruptedOracle.lean`, containing the accepted claim consumer plus a separate tactic blocked behind a file gate. After the gate marker appeared, the harness sent `SIGKILL`; both runs recorded exit `-9`. The proof's preceding local `no goals` and the separate completed good oracle remained facts about their own requests. The **interrupted new verification request** has no accepted result, even if some earlier diagnostics or output were available. This is a controlled OS process experiment, not a current Anneal cancellation/status implementation. Basis: **execution**.

### Trust and evidence controls do not certify isolation

A benign `run_tac` in `SideEffect.lean` wrote `TACTIC_EXECUTED` in its owned temporary directory during `lean --json`. It exited 0 in both runs. Together with the prior trust-boundary package's Cargo build-script/proc-macro and Lean `run_cmd` markers, this proves that these selected source callbacks executed under the selected commands. It does not demonstrate an enforced sandbox, identify all execution entrypoints (Lake configuration, native extensions, macros), or determine authorization policy for an untrusted project. Basis: **execution**, with broader inventory from the cited prior report.

A synthetic raw evidence object contained an absolute temporary path and a fake token. The allowlisted shareable object replaced the path with `$WORK` and token with `[synthetic-secret]`; an assertion found neither original string. No ambient environment or real credential was captured. The prior trust-boundary package retains a more complete raw-versus-minimized Cargo/Lean specimen and one worker self-observation of instruction-shaped text. Here the inert Lean comment left theorem behavior unchanged; that is a compiler observation, **not an agent prompt-injection trial** or an interface safeguard. Basis: **execution** for these narrow controls.

### Decision ledger for the twelve I159 alternatives

The table names the strongest simple candidate and the counterexample or successful precondition currently recorded. A package reference means **narrow evidence at its own scope**, not a general architectural verdict.

| Control | Simple candidate and present discriminating evidence | Integrated residual |
| --- | --- | --- |
| N01 | Path/name-only identity: `anneal-3730-charon-subject-identity-2026-09-29` has changed-subject controls. | Full cross-layer path/content ablation. |
| N02 | Document-version-only freshness: `anneal-3730-lean-protocol-races-v4-30-0-rc2` and import-deletion report retain stale environment controls. | Full import/worker attestation across launch modes. |
| N03 | Refresh existing worker instead of restart: import-deletion report demonstrates a fresh worker repair. | Test supported refresh on that existing worker under matched setup. |
| N04 | One server for conflicting workspaces: `anneal-3730-server-topology-v4-30-0-rc2` scopes server launch state. | Actual conflicting model/import workspaces on shared versus separate server. |
| N05 | Shared writable generated state: `anneal-3730-lake-writer-scale-v4-30-0-rc2` has mixed writer outcomes. | Conflicting definitions and interrupted concurrent publication. |
| N06 | Artifact cache alone reconstructs: `anneal-3730-lake-prepared-contract-2026-09-29` has prepared operations. | Empty-home/offline first-query full matrix against exact generated project. |
| N07 | Relocation preserves environment: Lake identity/preparation reports have selected relocation controls. | Native/setup/trace and retained-worker relocation matrix. |
| N08 | Generated Lean as canonical proof source: projection reports demonstrate mapping/ownership hazards. | Real editor round trip and regeneration under alternate ownership. |
| N09 | Spans alone recover editable range: `anneal-3730-cross-tool-provenance-2026-09-29` records source-location limits. | Real macro/Unicode/one-to-many editable-range controls. |
| N10 | Every proof-only edit skips upstream: `anneal-3730-rust-input-snapshot-2026-09-29` records hidden-input/change controls. | Actual Anneal classifier with import, macro, and configuration changes. |
| N11 | `no goals` means acceptance: the present weak/admitted/axiom/missing-obligation fixtures falsify that Lean-level rule. | Complete generated Rust obligation and trust coverage. |
| N12 | Cancellation alone prevents stale acceptance: fault and generation-recovery reports retain late-output controls. | Actual stage cancellation and publication-fence replay in Anneal. |

For a first implementation candidate, keep independent status dimensions and a fresh controlled oracle; retain one-shot subprocesses where reuse or finer invalidation has no measured win. This is a **derived fallback**, not an adopted V2 design. `anneal-3730-architecture-contracts-2026-09-29` records the process-topology and optimization gates in more detail. The table documents supporting evidence, counterexamples, stronger untested claims, and the smallest next probe for I144; a final product decision requires actual implementation and workload results.

### Explicit issue residuals

| ID | Present evidence | Exact residual |
| --- | --- | --- |
| I126 | Prior Cargo/Lean callback markers; new tactic marker. | Lake configuration, native extensions/macros, enforced containment and resource limits, entry trust policy. |
| I127 | Synthetic redaction assertion; prior minimized transcript. | Real private-source protocol/generated-file leak review under controlled disclosure; sanitizer coverage. |
| I128 | Inert comment and prior one-worker self-observation. | Independent blinded agent and interface safeguards across diagnostics/retrieved context. |
| I129 | Direct unsaved goal, good proof, interrupted consumer, weak/admitted/missing controls. | Machine result taxonomy integrated with actual Anneal Rust/model/obligation status and reader interpretation. |
| I130 | `sorryAx` and new `cheat` axiom controls. | Claim-relative taint through callers, native/external model assumptions, cache reuse and every adapter. |
| I131 | Exact fresh proof bytes and identical imported `.olean` in three new processes. | Clean dependency rebuild, independent artifact/kernel audit, and real translator/subject equivalence. |
| I132 | Seven comparator mutations and retained raw JSON. | Broader declaration set, semantic equivalence, diagnostics normalization across tools, real obligation graph. |
| I133 | Prior 76,502-state/11-mutant fault model. | Real engine conformance and longer/higher-order schedules. |
| I134 | Prior gated late generation and filesystem recovery; this gated killed compiler. | Edits/rebuilds inside actual integrated Charon/Aeneas/Lake/Lean requests with worker identities. |
| I135 | Present wrong-import, weak, axiom, missing controls; prior stale/fault controls. | Pairwise and higher-order source/import/cache/launch/lifecycle matrix in actual engine. |
| I136 | Exact pinned local repeat. | Independent operator/environment and selected compatible upgrade matrix. |
| I137 | Prior comment projection, live edit and batch oracle. | Actual annotation grammar/prepared generated model and complete cross-layer identities. |
| I138 | Prior A/F/B failed and late model generations. | Real Rust→Charon→Aeneas model change with visible provisional state. |
| I139 | Other packages measure selected Lake/Lean resource cells. | Integrated parallel Anneal generated-project acceptance and host-budget bounds. |
| I140 | Prior single agent goal-versus-batch repair. | Multiple counterbalanced tasks, matched active budgets and maintenance/agent intervention scoring. |
| I141 | No human trial; prior agent card check is not one. | Human participants and interface comprehension for freshness/failure classes. |
| I143 | No remote test; local evidence has not justified remote orchestration. | Conditional: if actual local workflow needs it, authenticated versioned remote job, retry/cancel/artifact identity and validation. |
| I144 | Present twelve-control decision ledger plus architecture report. | Final evidence-to-interface decision after remaining real integration/workload experiments. |
| I159 | All twelve candidate alternatives identified; N11 newly falsified at Lean level. | Remaining relevant real harness cells listed above; no universal architecture winner. |

Every item is **partial, conditional, or human-gated** at its full requested scope. The table does not equate a package title or synthetic fixture with implementation coverage.

## Boundaries

- The fixed consumer certifies one synthetic expected Lean proposition, not the semantics of a Rust function or the completeness of Anneal's generated obligation set. The missing-claim control shows the comparator is sensitive to a named second requirement; it does not establish that real requirements have been enumerated.
- `#print axioms claim` is a theorem-specific report under this Lean build. It does not by itself inventory native code, imported model soundness, translator assumptions, kernel correctness, or all toolchain trust.
- Fresh Lean processes share the same Lean executable and imported `.olean`; no independent implementation or third-party proof checker ran. `Proof.olean` bytes are not treated as the semantic comparator.
- The live server ran after the fresh checks in the same copied directory and reused the imported artifact. There is no model edit during the LSP session; the direct server has no real Anneal generation pointer or snapshot envelope.
- The killed verifier had reached its gate, but no result was accepted from it. The experiment does not test graceful cancellation, descendant cleanup, or restart reconstruction.
- No real private data, secret, malicious action, independent blinded agent, human participant, other machine, remote execution, or later Lean version was involved. The synthetic comment and fake-token checks are deliberately narrow.
- The twelve-control ledger is a synthesis of the cited package evidence. It is neither twelve new integrated experiments nor an adopted design decision.

## Evidence

- `support/probe.py`, SHA-256 `74b6ef237386a50b811733ddaae1168509767f36196ff88b8180d281ee47684d`, preserves exact generated/proof/oracle strings, subprocess commands, direct LSP framing, kill gate, and assertions. `support/transcript-run1.json` and `support/transcript-run2.json`, SHA-256 `0740ae23f16c9e285fdb9bb16277c58d814f7149e2e3216c888bab95b9e3a846` and `b695401385075d4171e163056d671ca265bbbfadb864f74391b5d866e0421aa0`, preserve raw normalized Lean JSON/LSP messages and all source/import hashes. `support/acceptance-cases.csv`, SHA-256 `8112c56aa4cab9ca7c17723220c2cefaf17d297f4eb0f93341fa47c5d69dcaa9`, indexes the second run. Basis: **execution**.
- The existing vertical, agent workflow, trust evidence, fault model, generation recovery, architecture, Lean protocol, Charon subject, Lake, and projection packages cited by exact directory above supply their own source/execution evidence and limitations. This report's residual and N-control tables are **derived** from those scoped reports and the new fixture, not a rerun of them.
- [Issue #3731](https://github.com/google/zerocopy/issues/3731) supplies the requested I126–I141, I143–I144 and I159 investigation agenda. It is not an approval of this fixture as complete product verification.

## Revalidation

Set `LEAN_BIN` to the pinned absolute Lean executable and `ANNEAL_PROBE_SCRATCH` to an existing owned scratch directory. From this package run `python3 support/probe.py`, which writes `support/results.json`. Compare its classifications against both retained runs: good/fresh accepted; weak and missing consumer failures; admitted and axiom reports; wrong-import proof failure; LSP `⊢ modelValue = 4` then `no goals`; gated fresh verification exit `-9`; tactic marker; and redacted fake evidence. Run the package validator via `tools/reference.py` after catalog integration. For a real acceptance oracle, substitute actual captured Rust/Charon/Aeneas/Lean identities, generated obligation manifests, trust inventory, and both batch/live Anneal shells, then repeat these negative controls with an independently controlled fresh process.
