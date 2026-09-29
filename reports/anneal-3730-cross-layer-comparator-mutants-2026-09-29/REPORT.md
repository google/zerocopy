# Pinned Rust → LLBC → Lean comparator mutants and acceptance gates

## Result and subject

A new three-function Rust fixture ran through pinned rustc, Charon 0.1.210, one-shot Aeneas nightly-2026.06.03, and cached Lean 4.30.0-rc2. Four source cases were checked: base, declaration reorder, changed `wrapping_add(1)` to `wrapping_add(2)`, and a fresh clean rerun of base in a separate directory. Pinned rustc executable oracles confirmed selected `inc`/`twice`/`choose` values 1/2/3 for base, reorder, and clean rerun, and 2/4/5 for changed source. Fresh Lean processes compiled each generated `Source.Types`, `Source.Funs`, and `Source` module and checked all three matching `Result.ok` theorems by `rfl`. `#check` printed the exact types; `#print axioms` listed `[propext, Classical.choice, Quot.sound]` for each accepted theorem, with no `sorryAx`.

The decisive comparator controls show why Lean exit status or proof status alone is insufficient. A theorem named `obl_inc` weakened to `True` compiled and had no axioms, but its elaborated `#check` type and fixture proposition manifest differed from the required `inc 0 = ok 1`. A file missing `obl_choose` compiled; the exact obligation-list gate rejected it. An admitted false claim compiled with `sorryAx`; a stale old import and proof compiled after the captured Rust source changed; and a deliberately weak theorem compiled against a swapped imported model. The manifest rejected these with proposition/completeness, axiom, source-generation, or imported-model reasons. Conversely, the old strong proof against the swapped model failed `rfl` in Lean.

An external-function fixture supplied either Aeneas's axiom template or a concrete user-authored Lean model while holding Aeneas-generated Lean source bytes fixed. The imported `Source.Funs.olean` hashes differed. `#print axioms comparator_probe.call` listed `[external_double]` for the axiom model and no axioms for the concrete model; a selected `call 1 = ok 2` theorem compiled under the concrete model. That definition is an *assumption about a foreign function*, not a verified Rust implementation. The selected observations do not prove general Rust-to-Lean translation soundness.

The subject hashes are in `REPORT.json` and `support/results.json`: Charon `51bb6d23…`, Aeneas `f476001e…`, rustc `2ab7af1e…`, Lean `b48bc5ab…`, and the prebuilt Aeneas Lean library `Aeneas.olean` `67701a9e…`. This report used the installed one-shot binaries and cached dependencies only. No Anneal generator, interactive service, alternative toolchain release, remote machine, or new installation ran.

## Comparison granularity and exact provenance

| Case | Rust source SHA-256 prefix | LLBC prefix | Generated `Funs.lean` prefix | Compiled `Funs.olean` prefix | Selected Rust/Lean result |
| --- | --- | --- | --- | --- | --- |
| Base | `1e7af22d8ddc414b` | `ee36614785a52956` | `bc15e6198147e105` | `741d164fc7a832cb` | 1/2/3 |
| Reordered declarations | `5c47f32fcd6df506` | `734568088d01882d` | `61de570b374752a4` | `96645d3c18c93b48` | 1/2/3 |
| Changed addition | `fc47ac0e8cb34679` | `ec7d0f808f778c29` | `287273a09e0f2cc0` | `92ca23323f42b72d` | 2/4/5 |
| Separate clean base rerun | `1e7af22d8ddc414b` | `aafae3a3fd8885c8` | `e2c59d8fd0ede7ab` | `20097a83eda4600f` | 1/2/3 |

The reordered Rust functions changed Charon local `def_id` assignments from `inc`/`twice`/`choose` = 0/1/2 to `choose`/`twice`/`inc` = 0/1/2. Source line numbers changed accordingly. Aeneas's generated `def` lines for those names remained 21/27/34 in this fixture, but generated file bytes changed. The base and clean rerun had identical source bytes and identical selected Lean proof/axiom output, yet LLBC, generated Lean, and compiled imported OLean bytes differed across their separate absolute paths. The report therefore compares **raw bytes**, **declaration names/spans**, **selected rustc values**, **Lean theorem types**, **axiom inventories**, and **selected theorem acceptance** separately. Equal selected outputs across reorder and clean runs are bounded observations; they do not certify semantic equivalence for all inputs or justify a source-blind LLBC normalization.

`support/results.json` retains all 52 subprocess command lines, working directories, exit codes, stdout/stderr, case file inventories and control decisions. `support/work/` retains the exact Rust, LLBC, generated Lean, compiled OLean, user model and proof files. `support/comparison-manifest.json` records the three manually required theorem propositions, each case's source/LLBC/generated/import/proof hashes, local Charon IDs and spans, generated Lean definition lines, and the axiom/concrete external-model identities. It explicitly sets `proven_item_to_lean_range` to null. These name/span/line correspondences are lexical and manually selected; neither Charon nor Aeneas issued an authenticated Rust-item → generated-declaration → Anneal-obligation map here.

The fixture comparator is intentionally strict: it matches its three theorem names and textual propositions in the captured proof, checks source and compiled imported-model hashes, and rejects `sorryAx` in the batch output. The saved Lean `#check` lines independently show the elaborated type distinction between the strong and weak examples. This comparator can reject alternate syntax for an equivalent proposition; it is a falsification fixture, not a complete semantic proposition decision procedure or an Anneal acceptance implementation.

## Mutant outcomes

| Mutant or control | Lean observation | Separate acceptance observation |
| --- | --- | --- |
| Strong base theorem set | Exit 0, exact three theorem types, ordinary Lean axiom set | Accepted for the captured base source and compiled import hashes. |
| `obl_inc : True` with other claims unchanged | Exit 0; `#check obl_inc` reports `True`, and it has no axioms | Rejected for proposition mismatch despite successful proof. |
| Missing `obl_choose` | Exit 0 | Rejected for incomplete required theorem list. |
| False `obl_inc` admitted by `sorry` | Exit 0; `#print axioms` includes `sorryAx` | Rejected for proposition and admission taint. |
| Current source changed, old import and proof retained | Exit 0 | Rejected by captured source-generation hash mismatch. |
| Changed generated `Funs` compiled under base proof | Strong proof exits 1 with `rfl` failure; weak one-claim file exits 0 | The weak file is still rejected for proposition/completeness and compiled-model hash mismatch. |
| Axiom versus concrete external model | Both imported modules compile; call axiom inventories differ | Model source and imported OLean hashes must be included in the claim context; concrete model semantics are unverified. |

## Exact #3731 residuals

| Item | Added evidence | Remaining distinguishing work |
| --- | --- | --- |
| I126 | Actual local rustc/Charon/Aeneas/Lean execution and pinned subject inventory. | Untrusted Cargo/Lake/Lean execution containment, native extension limits, and authorization policy. |
| I127 | Complete small-fixture source, command, artifact and proof provenance retained. | Private-workspace minimization and leakage scan across logs, paths, environment and replay bundles. |
| I128 | No misleading-instruction or agent-interpretation trial. | Adversarial source/comment/diagnostic text through real interfaces and independent agent/human interpretation. |
| I129 | Status, completeness, proposition, admission, source and import identities separated in a hand-built gate. | Anneal's real goal/file/model/Rust-coverage status taxonomy and user-facing result envelope. |
| I130 | Axiom versus concrete external-model inventories and `sorryAx` mutant. | Claim-relative native/model/axiom taint through callers, reused artifacts and adapters. |
| I131 | Fresh local Rust extraction, Aeneas generation, compiled imports and batch proof in a second clean directory. | Independent machine/operator or checker, complete transitive dependency rebuild and translator soundness boundary. |
| I132 | Weaker proposition, missing claim, source reorder, changed import and raw-versus-selected-output comparisons. | Broader semantic/proposition/diagnostic comparator calibration across realistic Rust and Lean constructs. |
| I135 | Selected source/order/model/proof/control cells with explicit negative controls. | Pairwise/higher-order source/import/cache/launch/lifecycle matrix in the actual service. |
| I147 | Source reorder/body and imported model hashes under the same pin. | Same/older/newer mtime, byte-identical artifact replacement, changed external model with unchanged Aeneas output in a live worker. |
| I148 | Raw Charon/Aeneas output identities and selected proof/axiom behavior under reorder and body mutation. | Cross-process/order/flag/revision semantic comparator plus downstream cost. |
| I149 | Exact five-case file/declaration manifest with intentionally null authenticated link. | Producer-issued Rust→LLBC→Lean→obligation provenance with one-to-many/many-to-one navigation and edit authority. |
| I158 | A small retained pinned replay case. | Compatible Charon/Aeneas/Lean upgrade replay and explicit workaround-deletion probes. |
| I159 | A counterexample to “Lean exit 0 implies the required current claim”: weak, missing, admitted and stale states exit 0. | Challenge the remaining simple alternatives in an integrated Anneal workload. |

No row is claimed complete by this package. In particular, the external concrete Lean definition cannot validate a foreign Rust implementation, and the clean rerun shares the same host, pins and prebuilt Lean dependencies.

## Revalidation

Run `python3 support/check.py` to verify the acquired files, 52 records, positive rustc/Lean observations, seven controls and manifest without executing the tools. `support/build_manifest.py` regenerates the fixture contract from the retained results. To reacquire from the installed pins, run `python3 support/probe.py`; it replaces only this report's `support/work/` and `support/results.json`, then run the manifest builder and checker. Generated source comments and LLBC options can include absolute paths, so a relocated run needs new raw hashes and must be compared at the stated semantic/axiom/proposition level. The procedure neither downloads nor installs dependencies and does not write the catalog, stage Git changes, or publish.
