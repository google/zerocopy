# PR-stack pure models: checked laws and their concrete Rust frontier

## Summary

The exact PR #3846 pure model sources compile and their three test modules pass with Lean 4.31.0. The declaration audit checks 252 library declarations against the permitted logical axioms. Additional checked controls distinguish numerical layout, geometry, decoder width, initialization, and input-domain coverage. None supplies pointer-access authority or Rust execution correspondence by construction.

The unmodified source does not pass the same direct compilation procedure under Lean 4.34.1: `BitDecoder.run_map` fails at its `split`/`rfl` proof. This is an observed elaboration compatibility boundary, not a false mathematical theorem or a failure of the selected 4.31 build.

## Applicability

Source is `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, specifically the immutable Git objects under `anneal/lean`. Nine modules are read from those objects and compiled in private scratch. `support/results.json` under each version records module source hashes and command statuses. The successful run uses official Lean 4.31.0 commit `68218e876d2a38b1985b8590fff244a83c321783`; the separate failing run uses 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`.

The independent native-layout observations use Rust 1.99.0 commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, AArch64 macOS, edition 2024, default compiler layout. They do not concern the older compiler bundled with Anneal/Charon. The owned Rust probe uses safe operations only. No Aeneas companion, complete verification project, or omnibus archive was built.

Agenda scope: R017/R018/R061/R071/R072/R097 and T077/T082/T085/T086, plus P081–P085/P130, receive scoped source or execution evidence. Runtime typed-copy, provenance, ABI certification, and cross-target support remain separate questions.

## Findings

### Pure mathematical laws pass their selected checking path

The nine compiled modules are `Rust.Layout`, `Rust.Memory`, `Rust.Bytes`, `Rust.Storage`, `Rust.Arithmetic`, public `Rust`, and the three explicit test modules. Fourteen commands succeed in the 4.31 run: two identities, nine module builds, the owned boundary proof, native compilation, and native execution.

`RustTests` audits every declaration whose defining module belongs to the six-module library, including unused helpers. It permits only `propext`, `Classical.choice`, and `Quot.sound`, rejects missing imports or an empty scan, and reports 252 checked declarations. Representative printed laws use `propext` and `Quot.sound`; the geometric bound-transfer theorem uses no axioms. This is an executed dependency-policy check over the selected compiled environment, not independent verification of Lean's loader, kernel, or complete standard-library implementation.

Basis: **source** + **execution**, immutable modules and retained `lean431/RustTests.stdout.txt`.

### Numerical layout and footprints cannot establish their physical interpretation

`Rust.Layout` contains a size, alignment, alignment proof and divisibility proof. It has no Rust type index. The owned probe constructs a valid numerical layout of size one/alignment one; the native probe observes `u64` size eight/alignment eight. There is no contradiction because no theorem associates that numerical record with `u64`.

`Allocation` and `Referent` bound their admitted address predicates but do not require every numerical address in the interval to be admitted. `FitsInAllocation` combines footprint inclusion with endpoint inequalities; its conditions accommodate empty footprints. The owned proof constructs a zero-size allocation and referent fitting at address 100 without introducing an allocation-liveness or provenance premise. The definitions deliberately prove geometry only.

Consequently a certificate for pointer access needs an independent connection to allocation instances, lifetime, permissions, provenance, actual type layout and target bounds. Matching addresses or checking divisibility supplies only selected parts of that argument.

Basis: **source**, `Rust/Layout.lean` and `Memory.lean`; **execution**, owned construction and native size; **derived**, required interpretation boundary.

### Decoder width, initialization, and completeness are separate propositions

`BitDecoder.run` rejects a wrong byte count before applying the decoder. `Initialized` requires every accepted byte list to contain initialized bytes. The array theorem transfers an element initialization law to the whole representation, with exact element count and final remainder; zero-sized elements are handled by counting elements.

The owned `allInputs` decoder accepts an uninitialized byte and fails the initialization law. The owned `noInputs` decoder rejects every input and satisfies the same law vacuously. Both are legitimate decoder values. Thus the initialization law alone establishes neither completeness for language-valid Rust representations nor existence of any accepted representation.

The checked controls also reject a later uninitialized Boolean array element, accept three zero-sized unit elements using no bytes, and distinguish little-endian `[1,0]` as one from big-endian decoding as 256. These cover the mathematical definitions. They do not validate production of Rust values from physical storage, pointer-bearing bytes, or effects of a runtime typed transfer.

Basis: **source** + **execution**, `Rust.Storage`, upstream tests and `BoundaryProbe.lean`; **derived**, domain-adequacy constraint.

### Native layout observations retain target and representation choices

The safe Rust program observes a `repr(C)` `{u8,u32}` record of size eight/alignment four with field offsets zero/four; nesting it behind a byte gives size twelve and inner offset four. Packing gives size five/alignment one with word offset one. A unit type explicitly aligned to sixteen has size zero and alignment sixteen. Three unit array elements still occupy zero bytes. `Option<NonZeroU8>` occupies one byte in this configuration.

These observations discriminate payload size from complete size, internal padding from placement, zero-sized extent from alignment, and value representation from ordinary integer width. Checked addition of one to `usize::MAX` returns `None`, while wrapping addition returns zero; unbounded natural arithmetic represents neither operation without a bounded interpretation.

The executable sizes corroborate selected model obligations; they are not a proof of the compiler layout algorithm, every niche choice, all DST metadata, or any other target. No performance comparison was made.

Basis: **execution**, `lean431/rust-layout.stdout.txt`; **derived**, interpretation obligations.

### Exact toolchain selection matters to proof elaboration

Lean 4.34.1 compiles the first three library modules but rejects `Rust/Storage.lean:86` because, after `split`, the remaining `if` expression is not definitionally equal to the expected mapped option. The same immutable bytes pass under 4.31. No proof adaptation was used for the successful result.

This observation constrains reuse of a Lean-native semantic library with a different pin: source-level mathematical intent, elaboration compatibility, compiled-artifact compatibility and transitive dependency assumptions are separate matters. It does not classify the library as generally incompatible with every 4.34 build configuration or assert a kernel regression.

Basis: **execution**, retained `lean434/Rust-Storage.stdout.txt` and separate 4.31 results.

## Boundaries

- **Not established:** concrete Rust operational adequacy, source-safety reflection, pointer permission, runtime typed transfers, general padding initialization, or safe-client coverage from these pure laws.
- **Not examined:** Aeneas companion proofs, full PR-stack extraction, bundled Lean archive installation, other targets, or the source cause of the 4.34 tactic-behavior difference.
- **Known observation:** this direct unmodified-source compilation fails under the identified 4.34.1 procedure and passes under the identified 4.31.0 procedure.
- **Unknown:** compatibility with other pins or proof adaptations; no adjacent-version generalization is inferred.
- Native layout is finite implementation evidence. It does not supply a formally checked Rust layout/ABI certificate.

## Evidence

- **source:** [pure library and tests](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/lean); exact per-module SHA-256 values are in version-specific results.
- **execution:** `support/lean431/` and `support/lean434/`, separate statuses and streams. Failed partial compilation is not recorded as successful library checking.
- **execution/source:** owned `BoundaryProbe.lean` and `layout_probe.rs`; `run_probe.py` reads immutable Git objects, compiles privately, and retains observations.
- **source/execution:** [official Lean 4.31 release](https://github.com/leanprover/lean4/releases/tag/v4.31.0), `lean-4.31.0-darwin_aarch64.tar.zst`, verified SHA-256 `264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27`. The archive itself is not mirrored in this report.

## Revalidation

Run `python3 -B support/run_probe.py /path/to/zerocopy-clone /path/to/lean-4.31.0/bin/lean`. Without the second argument the driver explicitly selects the separate 4.34.1 experiment. Inspect tool identities, source hashes, every status and the declaration-audit count. Supply the actual selected binary; the output subdirectory name is not applicability evidence.

For a concrete Rust model, independently bind the type/target layout and decoder domain, then add operational transfer and access rules. Repeat native observations on each claimed target. Preserve an initialization-law negative control and an empty-domain control; either can pass width checks while failing a stronger interpretation claim.

*Authored by an AI agent acting on joshlf's behalf.*
