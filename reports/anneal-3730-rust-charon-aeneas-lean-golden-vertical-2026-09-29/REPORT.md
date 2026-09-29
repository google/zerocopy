# Pinned Cargo → Charon → Aeneas → Lean golden vertical with negative controls

## Result and scope

A new three-function Cargo library compiled through pinned Charon 0.1.210, one-shot Aeneas nightly-2026.06.03, and cached Lean 4.30.0-rc2. The three selected Rust results and translated Lean claims matched for `inc`, `twice`, and `choose`: with `wrapping_add(1)`, the results at zero were 1, 2, and 3; after changing the Rust body to `wrapping_add(2)`, they were 2, 4, and 5. Cargo executed a selected-value test in each source state. Fresh Lean processes compiled the generated modules and proved the three corresponding `Result.ok` equations by `rfl`; their `#print axioms` outputs listed `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` in accepted proofs. These are selected executable observations, not a general translation soundness proof.

The experiment used only already installed executables and cached Lean dependencies on this macOS arm64 host. It did not invoke an Anneal generator or server, implement Anneal's obligation parser, rebuild the prebuilt Aeneas Lean dependency tree, verify on another machine, or compare compatible toolchain upgrades. The doc comments that name `obl_inc`, `obl_twice`, and `obl_choose` are *manual fixture markers*, not a claim about Anneal annotation syntax. `support/probe.py` is the complete replay procedure and `support/results.json` retains all 34 command lines, working directories, exit codes and streams. The 508 KiB `support/work/` tree retains captured crate inputs, four LLBC files, generated Lean, private consumer Lean files and compiled `.olean` files. Large Cargo target directories were measured and removed after the run.

## Stages, identity, and exact comparison

The crate's `Cargo.toml` and offline `Cargo.lock` were fixed. Each case captured its exact `src/lib.rs` before Charon ran under the pinned nightly Rust/Cargo toolchain. `charon cargo --preset aeneas` wrote a private `current.llbc`; Aeneas generated `Current.lean`, `Types.lean`, and `Funs.lean`; fresh Lean batch processes compiled `Current/Types`, `Current/Funs`, and `Current`, then checked `Proof.lean`. All stages succeeded in the base cold, base prepared, base separate clean target, and mutated separate clean target cases. The two Cargo behavior tests passed. The prebuilt `Aeneas.olean` was imported by the Lean consumers; its exact top-level hash is recorded, but its transitive objects were not rebuilt here.

| Case | Captured Rust source SHA-256 prefix | LLBC SHA-256 prefix | Generated `Funs.lean` prefix | Selected Rust/Lean values |
| --- | --- | --- | --- | --- |
| Base cold | `4d39ee7a9118684c` | `7032ef983ec41624` | `e671fd230e9f048c` | 1, 2, 3 |
| Base prepared target | `4d39ee7a9118684c` | `b52420c828c10810` | `e671fd230e9f048c` | 1, 2, 3 |
| Base separate clean target | `4d39ee7a9118684c` | `d046ca6d94e1c980` | `e671fd230e9f048c` | 1, 2, 3 |
| Changed source, separate clean target | `e1d8e8151a057cdb` | `f26a590b0ad5f335` | `f45d572ab60869ad` | 2, 4, 5 |

The three base LLBC files were **not** byte identical. Inspection and a narrow programmatic comparison found two differences: `translated.options.dest_file` recorded each private output path, and the `translated.short_names` array had a different order. Removing only that destination locator and sorting only that array made the parsed LLBC values equal. All three Aeneas-generated Lean files and the three compiled module `.olean` files were byte identical between the base cold, prepared, and separate clean runs. The script retains raw LLBC hashes and applies that exact normalization for comparison; it does not claim that any other differing LLBC field is harmless. On the changed source, `Funs.lean` and `Current/Funs.olean` changed, while selected type and entry modules stayed byte identical.

`support/results.json` contains a manually checked cross-layer declaration manifest. For the three functions, Rust definitions on lines 3/5/7 correspond lexically to local Charon `def_id` 0/1/2 and spans 3:0–3:47, 5:0–5:43, and 7:0–7:71. Aeneas source comments repeat those spans next to Lean `def inc`/`twice`/`choose` on lines 21/27/34 of `Funs.lean`. The fixture then chooses one obligation theorem per function. This is a hand-checked mapping of names, comments and positions, **not** an authenticated producer-issued Charon-ID → Lean-range → Anneal-obligation map. The manifest explicitly records those stronger links as null.

## Falsification controls

- **Wrong result:** Against the changed source and fresh generated import, `inc 0 = ok 1` failed with Lean's `rfl` error. The matching `ok 2` claim passed.
- **Missing obligation:** A file proving only `obl_inc` and `obl_twice` compiled with exit 0. The separate exact-obligation-list gate rejected it because `obl_choose` was missing. Lean's exit status alone is insufficient for fixture coverage.
- **Admission:** A false `ok 99` claim using `by sorry` compiled with exit 0. `#print axioms obl_inc` exposed `sorryAx`, and the acceptance rule rejected it. The accepted three-theorem file had no `sorryAx`; ordinary Lean axioms remained and are reported rather than concealed.
- **Stale source/import:** After capturing the changed source, the old base import and proof still compiled. Comparing captured current-source SHA-256 with imported-generation source SHA-256 rejected that stale result. The identity fence is implemented by this experiment's script, not by Anneal.
- **Changed imported model:** Replacing the base consumer's `Funs.lean` with the changed source's generated `Funs.lean`, recompiling its import, then checking the old proof failed. Its raw generated-file hash also changed. This is an explicit import-content control, distinct from source identity.

The two expected nonzero Lean commands were the wrong-result and changed-import proof checks. Missing-obligation, admission and stale-import controls deliberately exited zero at the batch layer and required separate coverage, taint or identity checks. The package makes those classifications explicit in `support/results.json`.

## Residuals against #3731 investigations

| Item | Contribution here | Remaining work |
| --- | --- | --- |
| I126–I128 | Replayed local executable stages with exact source/artifact capture and honest trust boundary; comments were treated as fixture data. | Execution containment and limits for untrusted Cargo/Lake/Lean, private-source minimization, misleading-instruction/interface trials. |
| I129 | Separated successful local proof, missing coverage, admission and stale generation. | Anneal's actual model/obligation identity and user-facing verification-state taxonomy. |
| I130 | `sorryAx` control and standard-axiom inventory. | Claim-relative taint across callers, native code, external models, reused caches and adapters. |
| I131 | Rebuilt captured Rust through Charon/Aeneas and batch-checked exact private generated modules and proof in fresh Lean processes. | Independent kernel recheck or independent machine/operator; transitive prebuilt Lean artifacts and translator soundness remain trusted. |
| I132 | Raw hash versus narrowly normalized LLBC comparison; source, import, obligation, result and axiom controls. | Broad semantic/proposition/diagnostic comparator calibration, including weaker claims and many Rust constructs. |
| I133–I134 | Concrete sequential four-stage replay and identity counterexamples. | Fault schedules, barriers and true in-flight concurrency in an integrated Anneal engine. This run did not claim a race. |
| I135 | Base cold/prepared/clean, body mutation, wrong import, stale import, missing obligation and admission cells. | Pairwise and higher-order source/import/cache/launch/lifecycle matrix under the actual service. |
| I136 | Second clean local target using identical pins. | Independent environment/operator and selected compatible upgrades. |
| I158 | Retained small pinned replay with exact subject hashes and one bounded LLBC normalization. | Repeat across compatible Charon/Aeneas/Lean upgrades and test deletion of each workaround, rather than generalizing this pin. |
| I159 | Counterexample to “Lean exit 0 means current complete verified result”: missing obligation, admission and stale import each exited zero. | Run the remaining simple-alternative controls in a real integrated harness, including ownership and shared-writer behavior. |

## Revalidation and evidence

Run `python3 support/probe.py` from any working directory while the exact installed tools at the paths in the script remain available. It checks free disk, uses offline Cargo resolution, replaces only its own `support/work` and `support/results.json`, and asserts positive and negative outcomes. The 34 command records include two expected nonzero results and two passing Cargo behavior tests. For relocation, regenerate hashes because LLBC destination paths and tool paths are absolute; do not equate the old raw LLBC hash with a relocated run. The full subject hashes, per-file inventories, normalized comparison rule, command transcripts, controls, and source-to-declaration rows are in `support/results.json`; `support/probe.py` is the replayable code.
