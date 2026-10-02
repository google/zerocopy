<!-- Copyright 2026 The Fuchsia Authors
SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -->

# Native capability fixtures

These small, independent crates challenge the pinned native extraction without
editing compiler output, deleting associated equalities, or replacing local
helpers with axioms. They are capability probes, not admitted Rust soundness
proofs. Each new observation records the repository's actual HEAD, dirty status,
source digests, and validated runtime metadata.

Run from the repository root with the existing `AENEAS_TOOLCHAIN_DIR` and
`CARGO_HOME` from the verification setup, using a fresh evidence directory:

```bash
python3 -B verification/aeneas/tests/capabilities/probe.py known-layout \
  --runtime "$AENEAS_TOOLCHAIN_DIR" \
  --cargo-home "$CARGO_HOME" \
  --work target/capabilities/known-layout-new \
  --cargo-target target/owned-transmute-capability/cargo-target
```

Replace the case and work directory with `owned-transmute`, `invalid-transmute`,
`raw-pointers`, `std-transmute`, `known-layout-unconstrained`, or
`known-layout-concrete`.
The last two select only their own root from the `known-layout` fixture.
Each run records commands, exit codes, source digest, and
logs in `evidence.json`. Charon also records the pre-transformation ULLBC and
final LLBC. The driver refuses an existing evidence directory and returns the
first failing stage's status. Inspect the recorded stage results to distinguish
the expected negative fixture from an unexpected failure.
The tracked Cargo lockfiles are used with `--locked`; the probe does not
regenerate them. Compilation occurs through the native Charon driver, as in the
verification pipeline.

Observed with the preserved patched runtime on October 14, 2026:

| Case | Charon | Aeneas | Result |
| --- | --- | --- | --- |
| `known-layout` | 0 | 2 | The original `KnownLayout<PointerMetadata = usize>` constraint survives lifting. `SymbolicToPureTypes.ml:1000` requires an empty associated-type constraint list and rejects the generic root signature. |
| `known-layout-unconstrained` | 0 | 2 | The generic root has no associated-type constraints. The original trait's `MaybeUninit` metadata equality survives lifting and triggers the same check while Aeneas translates the trait's method signatures. |
| `known-layout-concrete` | 0 | 0 | The concrete slice root emits, but calls an external associated-constant axiom template; its descriptor value or initializer is not translated or proved. |
| `owned-transmute` | 0 | 2 | The actual production `transmute!` expansion retains its compile-time trait-check helper. `InterpLoops.ml:411` rejects that helper's infinite loop. No conversion theorem is established. |
| `invalid-transmute` | 101 | Not run | Rust rejects `u8 -> bool` because `bool` does not implement `FromBytes` (E0277). This confirms a compilation gate, not a runtime byte-decoder proof. |
| `raw-pointers` | 0 | 0 | Native emission succeeds, but does not establish useful raw-pointer semantics or an admitted proof. |

The raw-pointer result needs particular care. The pinned backend's
`Aeneas/Std/RawPtr.lean` represents a raw pointer by `v : T`; it carries no
address or provenance. Its `RawPtr.cast_scalar` always returns `.fail .undef`.
The emitted slice-pointer constructor and `NonNull::new` are external function
axiom templates, and `NonNull` is an external type axiom template. None of those
templates is an accepted interpretation in this experiment. The existing
admission checker also rejects raw-pointer types. Successful emission therefore
does not provide a pointer-preservation or memory-safety theorem.

The exact `KnownLayout` experiment fails before recursive trait extraction.
Its error must not be relabeled as a recursive-declaration diagnostic. The
trait's recursive `MaybeUninit: KnownLayout` bound and metadata equality remain
in the preserved original compiler evidence; no translation patch or weakened
trait was introduced.

The unconstrained follow-up isolates that retained trait equality from the
explicit equality in the first root. Its final trait constraint identifies
`<Self::MaybeUninit as KnownLayout>::PointerMetadata = Self::PointerMetadata`.
The concrete follow-up emits a call to
`Slice.Insts.ZerocopyKnownLayout.LAYOUT Std.U32`, with the implementation's
associated constant left in `FunsExternal_Template.lean` as an axiom because
zerocopy is a dependency of the independent fixture. This emission cannot stand
in for a proof of the constant's body or of a generic `KnownLayout` dictionary.

## Checked local initializer

The production harness `check_u32_slice_known_layout` in
`zerocopy/src/layout/primitive_checks.rs` compiles inside zerocopy's own crate.
Unlike the independent dependency fixture, it reaches the local slice
implementation's actual associated-constant initializer. The preserved and
final compiler evidence retains that body; admission traverses its execution.
Native output defines `Slice.Insts.ZerocopyKnownLayout.LAYOUT T` by calling
`layout.DstLayout.for_slice T`. No external axiom supplies the descriptor.

The harness checks the actual `[u32]` descriptor fields and its size for every
count against independent checked multiplication. Its Lean proof uses that
retained initializer under the visible ABI-read guards. A development negative
control changes the initializer from `for_slice` to `for_type`: the native module
still elaborates, but the proof fails. The associated constant is thus part of
the checked behavior, rather than an assumed trait promise.

This remains a concrete numerical assertion proof under the existing primitive
interpretations and Rust correspondence premise. It does not supply a generic
`KnownLayout` law, its `MaybeUninit` obligations, or pointer/reference safety.

## Direct standard transmute

`std-transmute` calls the standard primitive directly for `u32 -> [u8; 4]`,
the reverse conversion, and `u8 -> bool` after checking Boolean validity. It
rejects non-little-endian targets at compilation. Native emission succeeds and
retains all local wrapper bodies, with one external `core::intrinsics::transmute`
template. This observation isolates the standard primitive from the production
macro's unsupported compile-time helper loop; it does not prove the macro.

The separate owned-operation proof adds an explicit interpretation-only provider
to that standard boundary. Admission checks each original Rust endpoint pair;
compiled auditing binds every reached call to its canonical provider and checks
the whole provider definitions. Numerical cases use the verified 64-bit
little-endian profile. The Boolean provider checks validity before construction
and returns forbidden execution outside its domain. Neither this boundary nor
its providers cover padding, pointers, resources, or arbitrary Rust types.
