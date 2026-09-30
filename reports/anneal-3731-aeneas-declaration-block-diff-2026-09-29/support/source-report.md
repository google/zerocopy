# Pinned Aeneas CLI identity, output manifest, and invalidation probe

## Summary

A seven-input, nine-option-control CLI matrix shows that exact Aeneas output ownership requires more than an LLBC filename or a Rust item text comparison. At the pinned Aeneas nightly, changing one Rust function, type shape, trait implementation, or one member of a recursive group changed the whole `Funs.lean` byte artifact. Namespace, split layout, and heartbeat flags changed output bytes; clearing LLBC `short_names` did not; a forged Charon schema version was rejected. A complete file and generated-declaration inventory made deletion visible. Successful mode changes in a reused destination left stale files, and a rejected translation overwrote `Funs.lean` with partial `sorry` output. An executable copy failed to start without its relative `libgmp` dependency, then produced identical output once that library was copied alongside it.

This is an executed **one-shot CLI** report for [#3731](https://github.com/google/zerocopy/issues/3731) I082–I088, I148–I149, I156, and I158, and #3730 E04–E12/M04–M05. It does not test same-process Aeneas library calls or an Anneal implementation.

## Applicability and method

The host was macOS arm64 with Python 3.14.7. Charon was `0.1.210`, binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, driven by the locally installed nightly 2026-05-31 Rust toolchain and `--preset aeneas`. Aeneas was local nightly-2026.06.03, executable SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`; its `-version` says `aeneas unknown`. Its bundled `libgmp.10.dylib` SHA-256 was `1b0ae61990da7a4661f2c8c601f55f6c9950279bbfef12453dd5bb0c01e4b0df`. The selected local Aeneas source registry file `ExtractBuiltinLean.ml` had SHA-256 `f0ef34854fb4634303ff70f32d51f43e615b36880e3864975e6d62041470a2a8`; this source hash is context, not proof of the binary's build inputs.

Every Rust variant used the same `support/work/source.rs` path and crate name `identity_probe`; the script saves exact source and LLBC bytes in `support/inputs/`. It overwrote one `current.llbc` handoff path before each independent Aeneas process to keep entry-file naming constant. The baseline flags were `-backend lean -no-progress-bar -sequential -split-files -gen-lib-entry`. Each successful variant translated into a private directory. The base generated `Current.lean`, `Types.lean`, and `Funs.lean`, with 12 parsed Lean declaration heads covering a type, trait, derived/implemented methods, ordinary functions, and two mutually recursive functions. All output bytes and file/declaration/import inventories are retained under `support/outputs/` and `support/handoff-manifest.json`.

The declaration parser recognizes leading Lean `def`, `structure`, and related heads plus the nearest Aeneas source comment. That gives an exact inventory of emitted file bytes, declaration head text, and locations in this fixture. The comments supply **coarse origin hints** only: the manifest deliberately sets `proven_mapping_to_rust_items` and `anneal_obligations` to null. Charon LLBC item IDs/spans are separately enumerated; no authenticated Charon-ID→Aeneas-ID→Lean-range correspondence was established.

## Observations

### Independent request dimensions

| Controlled change from base | Exit | Exact generated-file effect |
| --- | ---: | --- |
| Repeat same LLBC/options; copied binary with matching `libs/` | 0 | All three files byte-identical to base. |
| One `step` function body | 0 | `Funs.lean` changed. |
| `Wrap` from one to two `u32` fields, with its implementation source unchanged | 0 | `Types.lean` and `Funs.lean` changed. |
| One `Bump` trait implementation body | 0 | `Funs.lean` changed. |
| One member of the `even`/`odd` recursive group | 0 | `Funs.lean` changed. |
| Insert an unrelated helper before `step` | 0 | `Funs.lean` changed, including generated source locations. |
| Delete `step` and `use_step` | 0 | `Funs.lean` changed; both generated declarations disappeared in the clean oracle. |
| `-namespace Alternate` | 0 | `Types.lean` and `Funs.lean` changed. |
| No `-split-files`/`-gen-lib-entry` | 0 | Only `Current.lean` emitted; all three base file paths differ as a set. |
| `-max-heartbeats 500000` | 0 | `Types.lean` and `Funs.lean` changed despite the Rust and LLBC being identical. |
| `-impl-namespace`, `-tuple-nested-proj` | 0 | No byte change for this fixture; this does not make the flags generally irrelevant. |
| LLBC `short_names` array cleared, raw JSON bytes changed | 0 | No output byte change; this matches the inspected CLI path that clears short names on load. |
| LLBC `charon_version` marker changed from `0.1.210` to `0.1.999` | 1 | No files; explicit incompatible-version error. This is a schema-marker control, not a real second Charon release. |

The base `use_step` Rust text is unchanged when `step` changes, yet it calls the changed function. The `use_bump` Rust text is unchanged when the `Wrap` representation or trait implementation changes; `odd` is unchanged when `even` changes. These are direct dependency counterexamples to a cache key built solely from each item's own source text. A per-declaration prototype would need a dependency closure and a full-translation oracle, not merely compare text. The experiment did **not** implement such a cache or determine which generated definitions are semantically equivalent after the edit. `support/results.json` records the exact per-case file digests and whole-translation oracles.

The forged schema marker distinguishes compatibility checking from semantic translation: it proves rejection of that marker by this executable, not compatibility with another Charon revision. The copied executable control distinguishes a binary digest from a deployable tool identity: macOS failed with `Library not loaded: @executable_path/libs/libgmp.10.dylib` (exit `-6`), then the same binary bytes plus the pinned library yielded base-identical generated files. This does not compare a genuinely different Aeneas binary or compiled external-model registry.

### Complete output ownership and failure

The machine-readable handoff manifest records source hash, complete LLBC hash and schema marker, Charon declarations, Aeneas flags and binary/runtime-library digests, generated file hashes/imports/declaration heads, and absence of an Anneal obligation mapping. It is an **experiment-side manifest**, not an Aeneas-provided protocol or an Anneal implementation.

The clean deletion oracle removed `identity_probe.step` and `identity_probe.use_step`. A repeated split-output generation into a directory containing a user-authored `UserModel.lean` preserved that file's hash; this only establishes non-overwrite for an unrelated filename in this fixture. Split output followed by successful unsplit output into one directory left `Types.lean` and `Funs.lean` from the old mode, whereas the clean unsplit oracle contained only `Current.lean`. Thus success and an in-place directory listing cannot identify the current generation's file set.

After a successful generation into a shared directory, the preserved raw-pointer failure fixture exited 1, changed `Funs.lean` from SHA-256 `93da487c5699cc7285de9f18817d62afb858da4d9e6ebbea1e51eec330a4a325` to `aec4a4182c5e540ee604e2313d12d5344ee9b5cc28727d237be2d05ae4fc1669`, and left `sorry` in a Lean output. The successful old entry file and authored sentinel also remained. The correct manifest decision for that request is `reject_candidate: true`; the files are evidence of the failed attempt, not a publishable new model. This is a CLI failure/ownership observation, not a repeated-request residual-state test inside one process.

## Scope and unresolved work

| Issue item | Executed slice here | Still unresolved |
| --- | --- | --- |
| I082 | LLBC content/schema/`short_names`, namespace, split, heartbeat, naming flags, binary/runtime-library identity. | Independently mutate the *compiled* external-model registry, normalization rules, and a second real library/binary revision; test option collisions on representative shapes. |
| I083 | Whole-crate oracles for function/type/trait-implementation/recursive-group edits and unchanged caller text. | Trait declaration and external-model edits, dependency graph proof, real finer-grained cache prototype, semantic oracle. |
| I084 | Helper insertion and changed source locations; exact declaration name/head inventory. | Reordering/module moves, broad name/signature/proof-context stability, Lean elaboration effects. |
| I085 | Complete clean output set, user-file sentinel, deletion, successful mode-shrink stale files, partial failure. | User-maintained external model with actual Aeneas registry registration; atomic publication and overwrite collision cases. |
| I086 | File-based LLBC/Lean bytes and copying/runtime dependency are exposed. | In-memory or structured-stream implementation and cost comparison; same-process library access remains pending toolchain approval. |
| I087 | Actual selected-pin Aeneas source comments and generated declaration heads recorded. | Authenticated item-to-declaration/range mapping, source-map completeness, newer `translation.json` comparison, editable proof ranges. |
| I088 | Schema rejection, OS loader failure, and partial translation error with `sorry`. | Warning/crash matrix, structured diagnostics, same-process error reset, cancellation and recovery. |
| I148 | Identical repeat and several byte-affecting option/input changes. | Concurrent and parallel-mode full matrix, calibrated semantic comparator, downstream Lake/Lean cost of harmless textual instability. |
| I149 | Exact experimental input/output/declaration manifest and deletion consumer. | Proven compiler-resolved Rust→Charon→Aeneas→Lean→Anneal mapping, one-to-many helper identity, navigation/edit consumers. |
| I156 | The CLI's actual file-input, private-output, process-exit, and option behaviors support a narrow descriptor. | Versioned backend capability negotiation with an Anneal adapter and unsupported-call handling; never infer same-process or fine-grained support from this CLI. |
| I158 | A pinned replayable CLI suite and explicit schema/runtime dependencies. | Cross-release replay on a compatible selected upgrade, behavior comparison, and obsolete-workaround deletion tests. |

The source/release relationship is the same limitation as the adjacent process-contract report: `aeneas -version` does not prove the installed binary's compiled source commit. The source registry digest therefore belongs in a requested build provenance witness before it is treated as exact binary identity. No local OCaml/Dune installation was performed, and same-process Aeneas use remains explicitly **untested**.

## Evidence and replay

- `support/probe.py` SHA-256 `e561d0eaba807dcc9c23d2df1f084e7b8f6cb97aec88f09ffe0d13deea18426e` generates the Rust variants, runs pinned Charon and Aeneas, asserts fresh-oracle and failure controls, and writes the raw results and handoff manifest.
- `support/results.json` SHA-256 `694c43532ac90504947bd5cfe9e34369cae68e2164683e8c3f772138022d45b4` retains commands, statuses, stdout/stderr, timings, input/tool hashes, and output inventories.
- `support/handoff-manifest.json` SHA-256 `e9870d6f9844eb5ebc192d297d642319333549aac483d9f9a3322c75ba3c8826` retains exact per-generation file/import/declaration inventories and explicit null provenance boundaries. `support/inputs/` contains each source and LLBC, `support/outputs/` the generated Lean trees, and `support/fixture/unsupported.llbc` the prior error specimen (SHA-256 `daab1c093c8af871b3d7751a9625f49137f3bedf03f19e9ab3a3c46b10fb078d`).

Replay from this package with `python3 support/probe.py` while the pinned local binaries remain at the recorded paths. The script replaces its own `inputs/`, `outputs/`, and results files, and deletes transient `support/work/`. Compare semantic classifications and file inventories; wall times, process IDs, and absolute source paths can vary after relocation. A deployment on a new path should first record the new LLBC and generated-file identities rather than assuming path-independent hashes.
