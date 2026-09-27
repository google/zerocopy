# Aeneas nested borrows and the historical Hermes flaky repro

## Summary

The historical Hermes nested-reference fixture in `google/zerocopy` issue #3227 does not establish that Anneal's current Aeneas pin is still flaky. The reported failure belonged to Hermes's April 2026 Aeneas revision, `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`. Anneal now selects Aeneas `nightly-2026.06.03`, revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

The later pin contains material fixes in the same structural area as the old reproducer. In particular, Aeneas PR #1095, merged June 1 and present in the Anneal pin, changed borrow-projector handling for shared borrows and for mutable borrows nested behind shared borrows. The old Hermes fixture contains exactly such a shape: `&&mut u32`.

That does not prove the old flake is fixed. No fresh execution was performed for this report, and the pinned Aeneas source still contains explicit `Unimplemented` and `Nested borrows are not supported yet` paths for nested-borrow cases. At the same time, the pin contains deliberate sub-abstraction machinery and checked-in generated Lean for some nested mutable-reference signatures. The useful conclusion is therefore narrower: nested-borrow support at the Anneal pin is partial and path-sensitive, the old April failure cannot be carried forward unchanged, and the exact #3227 reproducer needs a repeated fixed-input experiment before Anneal relies on it as either supported or unsupported.

## Applicability

This report distinguishes three subjects that should not be conflated:

1. the historical Hermes fixture as committed in `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3`;
2. the Aeneas revision Hermes pinned for that fixture, `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`; and
3. the later Aeneas release selected by current Anneal, `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

The historical fixture's `hermes/Cargo.toml` also pinned Charon `0.1.174`, Lean `v4.28.0-rc1`, and Rust `nightly-2026-02-07`. Current Anneal selects a different Aeneas release and paired toolchain. This report therefore treats the old issue as historical execution evidence, not as a current compatibility result.

The existing `aeneas-rust-to-lean-translation-nightly-2026-06-03` report already explains how the pinned Aeneas release functionalizes references and generates backward functions. This report is narrower. It preserves the #3227 reproducer, its historical toolchain, the relevant change history between that toolchain and the Anneal pin, and the experiment needed to decide whether the old flake survives.

## Findings

### The old repro exercised three different nested-reference shapes

The fixture in `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/source/src/lib.rs` is:

```rust
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
```

These parameters are not one interchangeable "nested borrow" case. They cover a shared borrow under a shared borrow (`&&u32`), a shared borrow under an outer mutable borrow (`&mut &u32`), and a mutable borrow under an outer shared borrow (`&&mut u32`). Aeneas's own pinned type analysis distinguishes these relationships, including nested borrows, borrows under mutable borrows, and nested mutable borrows.

This matters because later fixes and remaining limitations are sensitive to where mutable and shared layers occur. A result for one of these shapes is not enough to classify the other two.

Basis: **source** + **derived**.

### #3227 records nondeterministic failure, but the fixture does not preserve a failing Aeneas stderr

Issue #3227 reports that the fixture sometimes succeeds and sometimes causes Aeneas to fail with an `unimplemented` error. PR #3223 changed the fixture's Hermes status to `known_flaky` so either outcome would not make the suite itself fail.

The preserved `expected.stderr` does not contain the Aeneas panic. It contains only Hermes's expected warning about a `sorry` in the proof context. Therefore the durable historical evidence establishes the source input, the toolchain pin, the test's `known_flaky` classification, and the issue author's report of nondeterminism. It does not preserve one concrete failing process transcript, the exact Aeneas source location that produced `unimplemented`, or a frequency estimate.

That distinction prevents a future agent from treating `expected.stderr` as a captured failure specimen when it is not.

Basis: historical **source** + issue **documentation** + **derived** interpretation of what the preserved fixture does and does not contain.

### The historical fixture used Aeneas `42c0e90...`, not Anneal's June pin

At `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3`, `hermes/Cargo.toml` records:

- Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`;
- Aeneas build tag `build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`;
- Charon `0.1.174`;
- Lean `leanprover/lean4:v4.28.0-rc1`; and
- Charon's Rust toolchain `nightly-2026-02-07`.

Current Anneal instead fetches Aeneas `nightly-2026.06.03`, which resolves to `ac9f1bc5262a5e4ff1e24ca78617121382202727`. The April flake is therefore not an observation of the tool Anneal currently selects.

Basis: **source**.

### The Anneal pin contains a June fix for mutable borrows behind shared borrows

Aeneas PR #1095, "Fix several issues in the translation," merged on June 1, 2026 and is present in the June 3 Anneal pin. Its stated fixes include intersecting borrow projectors for shared borrows and for mutable borrows used behind shared borrows.

The pinned implementation makes that distinction explicit. `ty_get_mutable_regions` says that a mutable borrow below a shared borrow is effectively shared, and its traversal stops when it enters a shared reference. PR #1095 also changed projection-intersection handling to account separately for shared and non-shared projections instead of assuming a single non-shared projector.

The historical fixture's `z: &&mut u32` has this same outer-shared/inner-mutable structure. It is therefore reasonable to expect PR #1095 to affect the behavior of the reproducer. It is not reasonable to conclude from source inspection alone that PR #1095 eliminated #3227's nondeterminism: the old issue did not identify a stable failing source site, and this report did not execute the fixture under either revision.

Basis: PR **documentation** + pinned **source** + **derived** structural correspondence.

### The pinned release deliberately supports some nested mutable-reference signatures

Aeneas PR #715, merged in January 2026, describes its nested mutable-borrow work as preliminary and "not fully general." Its central mechanism is a sub-abstraction level: a region abstraction can contain nested structure and end a higher-level part without ending the whole abstraction.

The mechanism is present in the Anneal pin. `Values.ml` defines abstraction levels for nested borrows, and the pinned `tests/src/nested-borrows.rs` contains signatures such as:

```rust
fn inner_mut<'a, 'b>(x: &'a mut &'b mut u32) -> &'a mut u32 {
    *x
}
```

The paired checked-in `tests/lean/NestedBorrows.lean` contains a generated definition for `inner_mut` with a forward value and two backward functions. It also contains more involved iterator examples whose generated forms thread backward functions through loop state.

These checked-in artifacts are evidence that the pinned source tree's intended/tested translation supports at least some nested mutable-reference patterns. They do not establish that every pattern accepted by Rust is handled, or that the exact Hermes repro is deterministic.

Basis: PR **documentation** + pinned **source** + preserved generated **execution** artifacts. The generated artifacts pre-existed at the pinned revision; this report did not regenerate them.

### The same pinned release still has explicit unsupported nested-borrow paths

The support above coexists with hard boundaries in the same revision:

- `docs/user/src/README.md` still lists "no nested borrows in function signatures" as ongoing work.
- `SymbolicToPureAbs.ml` raises `Unimplemented` for `AEndedIgnoredMutLoan`, `AIgnoredSharedLoan`, and `AIgnoredMutBorrow` cases that its comments tie to nested borrows.
- several translation functions assert `abs_level = 0` and raise `Unimplemented` otherwise.
- `SymbolicToPureTypes.ml` rejects ADT declarations containing nested mutable borrows.
- `InterpAbs.ml` contains conversion paths that raise `Nested borrows are not supported yet` when concrete nested borrow structure reaches them.

The documentation is therefore too coarse to use as a binary support manifest. The implementation contains both nested-borrow machinery and nested-borrow rejection paths. Support depends on the representation and translation path a program reaches.

Basis: pinned **documentation** + pinned **source** + **derived** synthesis.

### Closing Aeneas issue #181 does not retroactively establish behavior for the Anneal pin

Aeneas issue #181, "Add support for nested borrows in function signatures," was closed as completed on June 30, 2026. Anneal's pinned Aeneas revision is from June 3. The later issue closure therefore cannot establish that all work associated with #181 was present in the Anneal pin.

The issue history also distinguishes the broad feature from specific nested-borrow bugs. In April, an example involving `Option<&T>` in a loop was explicitly described by an Aeneas maintainer as a separate bug and moved to issue #929 rather than treated as the same feature request.

Basis: issue **documentation** + chronology.

## Boundaries

- **Not examined by execution:** this report did not run Aeneas, Charon, Hermes, Lean, or the historical fixture. It does not say whether #3227 now always succeeds, always fails, or remains nondeterministic under Anneal's pin.
- **Unknown:** the exact old `unimplemented` failure site is not preserved in #3227 or the fixture's `expected.stderr`, so source comparison cannot prove that PR #1095 fixed that exact path.
- **Known not to generalize:** generated success for `inner_mut` and other checked-in `NestedBorrows.lean` cases does not imply arbitrary nested-borrow support. The same revision contains explicit unsupported paths.
- **Unsupported in pinned source:** ADT declarations containing nested mutable borrows are explicitly rejected in `SymbolicToPureTypes.ml`.
- **Later upstream state is separate:** issue #181 was closed after the Anneal pin, and later nested-borrow fixes or regressions must not be projected backward onto `ac9f1bc...` without revision-specific evidence.
- This report does not establish semantic correctness of Aeneas's nested-borrow translation. It records acceptance/representation boundaries and the historical regression evidence needed for Anneal engineering.

## Evidence

**Anneal selection.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, selects Aeneas `nightly-2026.06.03`.

**Historical zerocopy evidence.** `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3`:

- issue #3227, "Aeneas is flaky wrt nested mutable references";
- PR #3223, `[hermes] Support known_flaky tests`;
- `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/source/src/lib.rs`, blob `bbb4c462ef48003ed7926e55e96a31f524c7dfbb`;
- `.../hermes.toml`, blob `eaf4c1f3fb0e8468fb8f57c6b3f174d80fee5177`;
- `.../expected.stderr`, blob `d15940a498f1a8b11c8d36237745d58a6aeb4414`; and
- `hermes/Cargo.toml`, which records the historical Aeneas/Charon/Lean/Rust pins.

**Pinned Aeneas source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `docs/user/src/README.md`, blob `fa1cac5c60ac5fdbd212ad4e9c07a9e0917ebd2c`, especially the support caveats at lines 9–16;
- `src/llbc/TypesAnalysis.ml`, blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`, nested-borrow classification at lines 21–30;
- `src/llbc/TypesUtils.ml`, blob `c40ef4fccfefed3d18f0d934a852e56515e3af65`, `ty_get_mutable_regions` at lines 264–302;
- `src/interp/InterpBorrows.mli`, blob `249c1d3aff003a145f55b20ded55e596b00849db`, nested-borrow representation warning around lines 118–121;
- `src/interp/InterpAbs.ml`, blob `0f67ceffc1584d0a801dde84aee953737f2d187e`, nested-borrow rejection paths beginning around lines 20–46;
- `src/symbolic/SymbolicToPureAbs.ml`, blob `7127601439903abb6fb86c56bed2c8f6af103e26`, nested-borrow `Unimplemented` cases at lines 75–80 and 162–164, plus level-zero assertions throughout the translation;
- `src/symbolic/SymbolicToPureValues.ml`, blob `5da7630a187bd4b19b33aad967591d4effa8524c`, nested-borrow projection handling and remaining TODO/unsupported paths;
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`, explicit rejection of ADTs containing nested mutable borrows at lines 294–300;
- `src/llbc/Values.ml`, blob `6f7e8bb746adb2fbc6612a1c442100b3c7a39389`, abstraction-level and given-back representations used for nested borrows;
- `tests/src/nested-borrows.rs`, blob `61d62cf0e0723a4019e024882e35fb8b212a67eb`; and
- `tests/lean/NestedBorrows.lean`, blob `61b3b2b31e50555182867a5b73fa510d05106e22`.

**Relevant Aeneas history.** PR #715, "Add preliminary support for nested (mutable) borrows," merged January 28, 2026. PR #1095, "Fix several issues in the translation," merged June 1, 2026 and is present in the Anneal pin. Issue #181, "Add support for nested borrows in function signatures," closed June 30, 2026, after the Anneal pin.

No fresh **execution** was performed for this report.

## Revalidation

The cheapest useful revalidation is a repeated fixed-input Aeneas probe. It should separate Aeneas nondeterminism from Charon variation:

1. Recreate the exact three-parameter #3227 Rust fixture.
2. With Anneal's exact pinned Charon/rustc configuration, produce the LLBC once. Preserve the command, LLBC bytes, SHA-256, Charon revision/version, rustc identity, and target configuration.
3. Run the exact pinned Aeneas binary on that same LLBC in many fresh processes and fresh destination directories. One hundred runs is a practical first probe. Record exit status, stdout/stderr, generated-file hashes, and any Aeneas source location for every distinct outcome.
4. If every run is identical, report the observed result and the run count; do not call nondeterminism impossible. If outcomes differ, preserve one complete specimen of each outcome and their frequencies.
5. Repeat the same fixed-LLBC protocol with the historical Aeneas `42c0e90...` environment if reproducing the old flake matters. If old and new outcomes differ, narrow the change range before attributing the fix to PR #1095.
6. Separately regenerate the pinned `NestedBorrows.lean` fixture and compile it with the exact selected Lean toolchain. This checks that the checked-in golden still matches the executable toolchain; it does not substitute for the #3227 repeated probe.

After a future Aeneas roll, diff `TypesUtils.ty_get_mutable_regions`, projection-intersection logic in `InterpBorrows*`, sub-abstraction handling, and the `Unimplemented` branches in `SymbolicToPureAbs.ml` before generalizing this report. Re-run the fixed-input probe whenever those areas or the Aeneas/Charon pair changes.