# Aeneas generated Lean stability around nightly-2026.06.03

## Summary

Aeneas's generated Lean is revision-sensitive across the neighboring nightly releases around the version selected by Anneal. The checked-in history provides direct examples where an unchanged Rust test produces different Lean after a Charon/toolchain update, including changes to generated declaration names and function structure. It also provides the converse: nearby Aeneas releases can leave those generated files byte-identical while changing the Lean proof library and tactic environment they depend on.

The nightly date is therefore not a compatibility level for generated Lean. `nightly-2026.06.02` and `nightly-2026.06.03` both point to Aeneas commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`, while `nightly-2026.06.01` points to `f95a80abaf554d4612cb60ef9ec8e849139bec44`. Twenty commits separate the May 31 nightly from the Anneal-selected revision, and fourteen commits separate the June 1 nightly from it. The June 4 and June 5 nightlies then advance to distinct commits again.

For Anneal, the durable unit is the exact toolchain state, not an expectation that generated names, bodies, comments, or proof-facing support remain stable across adjacent Aeneas nightlies. Pin the Aeneas revision and its Charon/Rust and Lean dependencies for any generated artifact or proof that depends on exact output. When upgrading, distinguish three questions: whether the generated Lean text changed, whether its semantics or names changed, and whether the surrounding Aeneas Lean library/tactics changed. A textual diff answers only the first.

No fresh Aeneas, Charon, Rust, or Lean execution was performed. This report uses immutable repository history and checked-in generated test outputs. It does not establish same-revision generation determinism; that remains a separate empirical question.

## Applicability

This report compares the Aeneas nightlies immediately around Anneal's selected `nightly-2026.06.03` release:

| Release tag | Aeneas revision | `charon-pin` | Lean toolchain |
| --- | --- | --- | --- |
| `nightly-2026.06.01` | `f95a80abaf554d4612cb60ef9ec8e849139bec44` | `42836b36b666a980cbc9d438a8aed340ad3b848b` | `leanprover/lean4:v4.30.0-rc2` |
| `nightly-2026.06.02` | `ac9f1bc5262a5e4ff1e24ca78617121382202727` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | `leanprover/lean4:v4.30.0-rc2` |
| `nightly-2026.06.03` | `ac9f1bc5262a5e4ff1e24ca78617121382202727` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | `leanprover/lean4:v4.30.0-rc2` |
| `nightly-2026.06.04` | `ac74e1baafe0973e919df9c86af0d4c521b642ff` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | `leanprover/lean4:v4.30.0-rc2` |
| `nightly-2026.06.05` | `5c70d9b0f648fa1c0becb92cab15a5ace1e6c093` | `a535e914f74db4fd9e6be7048f4233270d8945c0` | `leanprover/lean4:v4.30.0-rc2` |

The release workflow at the Anneal-selected revision runs daily at 04:00 UTC and names the release `nightly-YYYY.MM.DD`. It tags the repository state checked out by that run. The tag date therefore identifies a scheduled release event, not a promise that exactly one day's worth of changes occurred or that every date maps to a different source revision.

The strongest examples below use checked-in Rust inputs and their checked-in generated Lean outputs. Aeneas's compiler-development instructions say to regenerate test outputs after modifying either the compiler or Rust test files; the repository therefore preserves these Lean files as derived regression artifacts. This report compares those preserved artifacts and the commits that changed them. It does not assume that checked-in output is a public compatibility ABI.

All compared revisions use the same Lean `v4.30.0-rc2` toolchain. That controls one source of variation in this window. The Aeneas and Charon revisions, Charon's Rust toolchain, library/model code, extraction logic, options, and input program can still affect generated output.

## Findings

### Neighboring nightly labels do not define neighboring compatibility states

The release tag sequence is not one-to-one with source revisions. `nightly-2026.06.02` and `nightly-2026.06.03` both resolve to `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Conversely, the June 1 nightly resolves to `f95a80abaf554d4612cb60ef9ec8e849139bec44`, and the Anneal-selected revision is fourteen commits ahead of it. Relative to `nightly-2026.05.31` at `0f99a04996b06587fb013b74cd42c10a11a08f0f`, the selected revision is twenty commits ahead.

A consumer cannot infer generated-source continuity from adjacent dates. The useful identity is the immutable Aeneas revision together with the dependencies that determine translation.

Basis: **source** — Git tag refs and commit comparison for `AeneasVerif/aeneas`.

### Upstream treats checked-in generated files as derived test output

At the selected revision, `documentation/skills/aeneas-compiler-dev.instructions.md` instructs compiler developers to run `gmake test` after modifying the compiler or Rust test files. It says that this runs the Charon-to-Aeneas pipeline and updates generated Lean, Coq, and F* files under `tests/`.

That workflow matters when interpreting history. A change to `tests/lean/Foo.lean` in one of these commits is preserved output from the pipeline, not necessarily a hand-maintained interface change. The repository uses those files to expose translation regressions and updates, which makes them useful evidence for how exact generated output moved between revisions.

Basis: **documentation** at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `documentation/skills/aeneas-compiler-dev.instructions.md`.

### Unchanged Rust inputs produced different Lean between the June 1 and June 2/3 revisions

Two checked-in fixtures give a direct source-controlled comparison.

For `derive`:

- `tests/src/derive.rs` has blob `6877ecd11c8e0ad556447526d16ddf3949d1ec77` at both `f95a80a…` and `ac9f1bc…`;
- `tests/lean/Derive.lean` changes from blob `3fb96ffaca5d9de9af4fdd59ece7858192b0fc00` to `cdca874f74333722d8a36ea727f31b5891774058`.

For `order`:

- `tests/src/order.rs` has blob `3ffd618cb4c4dc6d1aed7b7c9675962a17863910` at both revisions;
- `tests/lean/Order.lean` changes from blob `4040455b6dbe8f32e02e8649a09a9c8b3cd676bc` to `ad3a94ea207a91c963aff302598899a945abfbc3`.

The same Rust bytes therefore do not imply the same generated Lean across these neighboring Aeneas releases.

Basis: **source** — immutable Git blobs at `f95a80a…` and `ac9f1bc…`. No fresh generation was run.

### A Charon/toolchain bump can change generated declaration names without changing the Rust fixture

Commit `20a749a6b540b301b489d7276b26b1cd405c3c0d` is an `Update charon` commit between the nearby nightlies. It changes Aeneas's `charon-pin` from `d986428c0225810607e95f858a5b07afcfd15f92` to `42836b36b666a980cbc9d438a8aed340ad3b848b`, adjusts Aeneas's Lean builtin mapping for Rust's `Eq` trait, and regenerates Lean tests without changing `tests/src/derive.rs` or `tests/src/order.rs`.

The generated `Derive.lean` output renames multiple declarations and structure fields from `assert_receiver_is_total_eq` to `assert_fields_are_eq`. The generated `Order.lean` output makes the same rename. A downstream proof or adapter that referred to those generated names literally would need an update even though the user Rust fixture itself had not changed.

This is not merely formatter churn. The generated identifier surface moved because the upstream Rust/Charon-facing trait shape moved and Aeneas's model mapping moved with it.

Basis: **source** — `AeneasVerif/aeneas@20a749a6b540b301b489d7276b26b1cd405c3c0d`, especially `charon-pin`, `backends/lean/Aeneas/Std/Core/Cmp.lean`, `src/extract/ExtractBuiltinLean.ml`, `tests/lean/Derive.lean`, and `tests/lean/Order.lean`.

### Another Charon bump changed generated structure and source metadata

Commit `8a0bdc7177ce6dc0a04a63d8966a31a9cd7a6b94` advances `charon-pin` from `42836b36b666a980cbc9d438a8aed340ad3b848b` to `65dcdb566e05472a6bca8074318c05f729e30177` and updates the Charon-facing Aeneas code for an LLBC representation change. It again changes generated outputs while leaving the relevant Rust fixtures untouched.

The `Order.lean` diff is structurally meaningful. Before this update, the generated `PartialOrd.partial_cmp` for `Wrap` directly called the scalar `PartialOrd` model and the generated `Ord.cmp` declaration appeared later. Afterward, `Ord.cmp` is emitted first and `PartialOrd.partial_cmp` calls that generated `Ord.cmp` function. The Rust `tests/src/order.rs` blob remains unchanged across the release comparison.

The same commit also changes source positions embedded in generated comments because its updated Charon/Rust toolchain sees different standard-library source locations. For example, generated comments for `core::ptr::null`, `core::mem::drop`, and standard-library comparison methods move to new line numbers. Generated text can therefore change even when the translated user operation is semantically the same, simply because provenance metadata from the pinned compiler/toolchain changed.

Basis: **source** — `AeneasVerif/aeneas@8a0bdc7177ce6dc0a04a63d8966a31a9cd7a6b94`, with generated diffs in `tests/lean/Order.lean`, `BuiltinAuto.lean`, `Derive.lean`, `DropBug.lean`, and `RustBorrowCheckIssues.lean`.

### Generated-output drift can be cosmetic, name-affecting, or semantic

Commit `e45609ff4a1c092951f0de4da0e81473053ab95c`, the final Charon update merged into the Anneal-selected Aeneas revision, advances `charon-pin` from `65dcdb566e05472a6bca8074318c05f729e30177` to `a535e914f74db4fd9e6be7048f4233270d8945c0`. Its generated-test changes include a formatting change in Rust item descriptions: const arguments such as `32 : usize` become `32usize` in comments in `Traits.lean` and `ConstShadow.lean`.

Taken together with the earlier commits, the nearby history exhibits at least three distinct classes of generated-source change:

1. provenance or presentation changes, such as standard-library line numbers and const-generic spelling in doc comments;
2. interface/name changes, such as generated `Eq` method identifiers; and
3. translated program-structure changes, such as the `Order.lean` call graph around `PartialOrd` and `Ord`.

A byte diff is therefore useful as an invalidation signal, but its size does not classify the verification impact. A one-line name change can break a proof that names that declaration; a larger source-position-only diff can leave the translated computation unchanged.

Basis: **source** + **derived** classification from commits `20a749a…`, `8a0bdc7…`, and `e45609f…`.

### Translation bug fixes can also alter generated output without changing the tested Rust program

The selected revision also includes commit `601ef6f79e036a031b55b0bb44baa5c83f8b006a`, titled `Fix several issues in the translation`. It changes borrow interpretation, symbolic-to-pure translation, type handling, loop treatment, and invariants, and regenerates or extends Lean tests.

This is a second change path independent of Charon syntax/model drift: Aeneas's own translation semantics and algorithms can change between neighboring releases. A consumer that pins only Charon or Rust does not thereby pin the generated Lean semantics.

Basis: **source** — `AeneasVerif/aeneas@601ef6f79e036a031b55b0bb44baa5c83f8b006a` and the `f95a80a…` to `ac9f1bc…` commit comparison.

### Textual generated-source stability and proof-environment stability are separate

The releases immediately after the Anneal-selected pin provide the converse case.

From `ac9f1bc…` to `ac74e1ba…` (`nightly-2026.06.04`), the only repository change is `backends/lean/Aeneas/Std/String.lean`: a previously admitted string-length obligation receives a proof. The checked-in `Derive.lean` and `Order.lean` blobs stay exactly `cdca874f…` and `ad3a94ea…`.

From `ac9f1bc…` to `5c70d9b…` (`nightly-2026.06.05`), those generated fixtures are still byte-identical, but the proof-facing Aeneas library changes. `backends/lean/Aeneas/Std/WP.lean` changes from blob `018c456bcab5374de0b09b17eda0df1a48e2288b` to `bcb96a4ee8499d9d29e277f71b644dcd244fac4c`, and `backends/lean/Aeneas/Tactic/Step/Init.lean` changes from `afaa4f2243a4d6bfcf08b36eff282886ed175ef2` to `4c25eb50901c8e3d7b18e121caefad5a0c235456`. Commit `5c70d9b…` adds automatic `mvcgen` specification generation for `@[step]` theorems and changes the WP instance to support universe-polymorphic `Result` values.

Thus "the generated Lean file did not change" does not establish "the proof environment did not change." A proof can depend on imported Aeneas definitions, tactics, attributes, or instances that move independently of the generated declaration text.

Basis: **source** — exact blobs at `ac9f1bc…`, `ac74e1ba…`, and `5c70d9b…`; commits `ac74e1ba…` and `5c70d9b…`.

### The compared releases hold Lean fixed but not the full translation toolchain

All four compared Aeneas revisions record `leanprover/lean4:v4.30.0-rc2` in `backends/lean/lean-toolchain`. The observed generated-output changes between June 1 and June 2/3 therefore do not require a Lean-version change.

Aeneas's `charon-pin`, however, moves from `42836b36b666a980cbc9d438a8aed340ad3b848b` at the June 1 tag to `a535e914f74db4fd9e6be7048f4233270d8945c0` at the selected revision. The intervening Charon-update commits also update the locked Rust-overlay/toolchain state. Generated Lean is consequently a product of more than the Aeneas OCaml commit in isolation: its upstream LLBC producer and Rust compiler/toolchain state can alter the input representation, modeled standard-library surface, ordering, and source metadata that Aeneas receives.

For reproducible downstream work, the Aeneas revision is useful because its repository pins these dependencies, but a report or artifact should preserve the concrete dependency identities when they matter rather than replacing them with a release date.

Basis: **source** — `charon-pin`, `flake.lock`, `backends/lean/lean-toolchain`, and the Charon-update commits at the compared revisions.

### There is no evidence here for a stable generated-Lean ABI across nightlies

The examined release workflow creates prerelease nightlies from current repository state, and the compiler-development workflow expects generated tests to be regenerated as compiler/toolchain behavior changes. The nearby history includes generated name and body changes without Rust-input changes. Nothing in these examined mechanisms supplies a compatibility layer that would preserve previous generated Lean spellings or structure across nightlies.

The supported conclusion is therefore negative and bounded: a downstream tool must not assume stability merely because two Aeneas releases are adjacent nightlies. This report does not claim that every generated name is intentionally unstable, nor that Aeneas promises never to preserve interfaces. It records concrete nearby counterexamples to a general continuity assumption.

Basis: **documentation** + **source** + **derived** conclusion from the counterexamples above.

### Anneal should treat an Aeneas upgrade as invalidating exact-output assumptions until rechecked

Current Anneal deliberately does not freeze its exact Aeneas boundary or proof encoding. The relevant reference-level lesson is narrower than a design prescription: any Anneal artifact or adapter that relies on exact generated declarations, helper structure, comments, imports, or Aeneas tactic/library behavior is revision-sensitive.

When an Aeneas pin changes, a cheap first pass is to diff generated golden fixtures and the proof-library surface used by Anneal. If exact output changes, consumers that refer to names or source ranges need revalidation. If exact output does not change, proof-library/tactic dependencies still need a separate check.

Basis: **derived** from the pinned source/history plus current Anneal's explicit non-decision about proof encoding.

## Boundaries

- No fresh Charon extraction, Aeneas translation, Lean elaboration, or test regeneration was performed. All output comparisons use checked-in Git blobs and preserved diffs.
- This report does **not** establish same-revision determinism. Two runs of the exact same Aeneas/Charon/Rust configuration were not compared. The separate #3720 subject "Aeneas generated-source determinism" remains an empirical question.
- A changed generated-file blob does not by itself prove a semantic change. Some observed differences are comments, source spans, or formatting. The report calls out examples where the diff itself shows changed generated names or function structure.
- An unchanged generated-file blob does not prove proof compatibility. Imported Aeneas Lean libraries and tactics can change independently, as the June 5 comparison demonstrates.
- The checked-in test corpus samples Aeneas behavior; it is not exhaustive over every supported Rust construct, extraction flag, crate shape, or backend option.
- The release tags identify repository revisions. This report did not download or hash the neighboring binary release archives, and it does not claim reproducible archive bytes.
- `nightly-2026.06.02` and `nightly-2026.06.03` sharing one Git revision proves that their checked-in source trees are identical. It does not prove independently produced release artifacts or fresh translations are byte-identical.
- The report does not establish a formal upstream compatibility policy for generated Lean. Its actionable conclusion comes from concrete counterexamples to assuming adjacent-nightly stability.
- Later Aeneas releases have additional facilities that are outside this exact comparison. Do not project this report's detailed code shapes forward without revalidation.

## Evidence

**Source — Aeneas release/tag identities, observed 2026-09-26.** `AeneasVerif/aeneas` Git tags:

- `nightly-2026.06.01` → `f95a80abaf554d4612cb60ef9ec8e849139bec44`;
- `nightly-2026.06.02` → `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- `nightly-2026.06.03` → `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- `nightly-2026.06.04` → `ac74e1baafe0973e919df9c86af0d4c521b642ff`;
- `nightly-2026.06.05` → `5c70d9b0f648fa1c0becb92cab15a5ace1e6c093`.

**Source — nightly release construction.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `.github/workflows/release.yml`: daily 04:00 UTC trigger, date-derived `nightly-YYYY.MM.DD` tag, prerelease creation, platform packaging.

**Documentation — generated-test workflow.** Same revision, `documentation/skills/aeneas-compiler-dev.instructions.md`, section `Regenerating Tests`: compiler or Rust-test changes require regenerating outputs with `gmake test`; the command updates generated Lean/Coq/F* test files.

**Source — exact toolchain selections.** At `f95a80abaf554d4612cb60ef9ec8e849139bec44`, `charon-pin` is `42836b36b666a980cbc9d438a8aed340ad3b848b`; at `ac9f1bc5262a5e4ff1e24ca78617121382202727`, it is `a535e914f74db4fd9e6be7048f4233270d8945c0`. All compared revisions have `backends/lean/lean-toolchain` = `leanprover/lean4:v4.30.0-rc2`.

**Source — unchanged Rust / changed generated Lean specimen.** `AeneasVerif/aeneas@f95a80a…` versus `@ac9f1bc…`:

- `tests/src/derive.rs`: blob `6877ecd11c8e0ad556447526d16ddf3949d1ec77` at both revisions;
- `tests/lean/Derive.lean`: `3fb96ffaca5d9de9af4fdd59ece7858192b0fc00` → `cdca874f74333722d8a36ea727f31b5891774058`;
- `tests/src/order.rs`: blob `3ffd618cb4c4dc6d1aed7b7c9675962a17863910` at both revisions;
- `tests/lean/Order.lean`: `4040455b6dbe8f32e02e8649a09a9c8b3cd676bc` → `ad3a94ea207a91c963aff302598899a945abfbc3`.

**Source — Charon/toolchain-induced generated changes.** Aeneas commits:

- `20a749a6b540b301b489d7276b26b1cd405c3c0d`, `Update charon`: changes `charon-pin`, the `Eq` builtin/model name, `ExtractBuiltinLean.ml`, and generated tests including `Derive.lean` and `Order.lean`;
- `8a0bdc7177ce6dc0a04a63d8966a31a9cd7a6b94`, `Update charon`: changes `charon-pin`, Charon-facing Aeneas code, and generated tests; `Order.lean` changes generated call structure and multiple files get new standard-library source spans;
- `e45609ff4a1c092951f0de4da0e81473053ab95c`, `Update charon`: advances `charon-pin` to the Anneal-selected `a535e914…` and changes generated const-generic source descriptions from forms such as `32 : usize` to `32usize`.

**Source — Aeneas translation change.** `AeneasVerif/aeneas@601ef6f79e036a031b55b0bb44baa5c83f8b006a`, `Fix several issues in the translation (#1095)`: changes borrow interpretation, loop handling, symbolic-to-pure translation, type handling, and associated tests.

**Source — proof-environment changes with stable sampled generated files.** From `ac9f1bc…` to `5c70d9b…`:

- `tests/lean/Derive.lean` remains blob `cdca874f74333722d8a36ea727f31b5891774058`;
- `tests/lean/Order.lean` remains blob `ad3a94ea207a91c963aff302598899a945abfbc3`;
- `backends/lean/Aeneas/Std/WP.lean` changes from `018c456bcab5374de0b09b17eda0df1a48e2288b` to `bcb96a4ee8499d9d29e277f71b644dcd244fac4c`;
- `backends/lean/Aeneas/Tactic/Step/Init.lean` changes from `afaa4f2243a4d6bfcf08b36eff282886ed175ef2` to `4c25eb50901c8e3d7b18e121caefad5a0c235456`;
- commit `5c70d9b…` adds automatic `mvcgen` specs derived from `@[step]` theorems and modifies the WP `Result` instance.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Aeneas pin, first resolve the old and new release labels to immutable commits. Do not compare date strings alone.

Then use this narrow source-level check:

1. compare `charon-pin`, `flake.lock`, and `backends/lean/lean-toolchain`;
2. choose several Rust fixtures whose source blobs are unchanged across the revisions;
3. compare the corresponding checked-in `tests/lean/*.lean` blob IDs;
4. inspect any changed generated files and classify changes as provenance/presentation, generated-name/interface, or translated computational structure rather than treating all text churn alike;
5. separately compare the Aeneas Lean modules and tactic files imported by the downstream proof, even if the generated file blobs are unchanged.

On a capable execution surface, add the missing empirical layer. With each exact release/toolchain, translate the same small pinned Rust corpus twice into fresh directories. Compare the first and second outputs to test same-revision determinism, then compare the outputs across releases. Compile one representative downstream proof against each release so that generated-source stability and proof-environment compatibility are tested independently.

This revalidation is deliberately narrower than rerunning broad Aeneas archaeology: immutable tag resolution, dependency pins, a few unchanged-source golden fixtures, and the proof-library modules actually consumed by Anneal are enough to detect the continuity assumption this report warns against.