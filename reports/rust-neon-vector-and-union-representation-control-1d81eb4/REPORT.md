# One NEON addition and union-access correspondence control

## Summary

For the observed `u32` four-lane addition, portable SIMD and Arm NEON agree with wrapping scalar addition on 64 edge cases. Checked scalar overflow has a different result interface. Equal lane results do not erase vector alignment, target-feature, initialized-storage, or union-field validity obligations.

## Applicability

The executable case uses Rust 1.101.0-nightly at `1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, `portable_simd`, edition 2024, optimization level 1, and host/target `aarch64-apple-darwin`, LLVM 23.1.3. The runtime feature check returned `neon=true`. Matching portable-SIMD and intrinsic source at that compiler revision is compared with the separately pinned Rust Reference. This is one integer vector operation and one `repr(C)` union; it is not an ISA-wide or ABI-wide theorem.

## Findings

### F1. Representation equality has alignment and padding premises

Basis: source + execution.

The matching portable-SIMD `vector.rs` implements `Simd<T,N>` with SIMD representation and a lane limit. Its introductory layout documentation describes an array-like shape with greater alignment. The same file's actual array loading/conversion implementation explicitly accounts for padding for non-power-of-two lane counts. Thus even that descriptive array analogy must not become a universal size-equality premise. Safe `from_array`/`to_array` use dedicated loads/stores; source comments explain why direct inner-field access or naive copying is inappropriate.

The executed `Simd<u32,4>` has size 16 and alignment 16; `[u32;4]` has alignment 4. This directly distinguishes equal four-element content from interchangeable reference layouts. Reinterpreting an arbitrary array reference as a SIMD reference would need separate vector alignment and validity evidence. The probe uses value conversion and initialized arrays, and forms no such reference.

### F2. The primitive contract includes overflow and feature behavior

Basis: source + normative + execution + derived.

In matching `ops.rs`, integer vector addition invokes `simd_add`; source documentation specifies wrapping integer arithmetic. The Arm-shared NEON definition `vaddq_u32` is marked `target_feature(enable = "neon")` and also invokes `simd_add`. That implementation connection explains the common lane-level candidate specification, `out[i] = (a[i]+b[i]) mod 2^32`.

The original probe compares scalar `wrapping_add`, portable `Simd<u32,4>` addition, and `vaddq_u32` over 64 pairs selected from eight boundary values. All comparisons pass. At `MAX+1`, checked scalar addition yields `None`, while portable addition yields zero. Replacing a checked or panicking scalar operation with this wrapping vector primitive would therefore need a proof of its no-overflow precondition or an explicit change of contract; successful-result equality is insufficient.

The Reference treats executing unsupported platform features as undefined behavior except for explicitly documented platform exceptions. This control checks NEON before invoking its feature-enabled helper. Loads/stores use four live initialized `u32` elements and initialized output storage. No unsupported-feature execution was attempted. Rust's source implementation and this execution do not independently prove LLVM lowering or Arm instruction semantics.

### F3. Union storage must be interpreted at the selected field type

Basis: normative + execution + derived.

The Reference defines shared union storage without an active-field discriminator. Reading a field interprets its bytes at that field's type and requires that value to be valid. `repr(C)` gives the tested union's fields offset zero; size and alignment follow the maximum field requirements, rounded appropriately. These rules differ from a mathematical sum type whose constructor already guarantees valid payload selection.

The control initializes `Word { word: u32 }` and reads `[u8;4]` for eight values. All four bytes are initialized, both field types admit those bits, and the read matches `to_ne_bytes`. Observed union size/alignment are 4/4. This is a permitted representation reinterpretation, not evidence for arbitrary union reads. Reading byte 3 as a `bool`, for example, is explicitly invalid under the Reference and was never executed.

The Reference additionally warns that union fields in patterns may be read even when another subpattern fails. A tagged-union certificate should justify the tag branch first and then the selected field read with its validity premise. Treating an exhaustive mathematical match as evidence for any concrete payload would lose this obligation.

### F4. A bounded primitive certificate can separate four obligations

Basis: derived from F1–F3.

For this case a useful certificate binds: (1) the exact intrinsic/portable operation and target, (2) initialized lane storage with load/store bounds and alignment, (3) the wrapping result relation including failure behavior, and (4) the feature-enabled execution premise. A union certificate separately binds the stored byte relation, field offset, selected destination validity, and permission to read shared storage. These interfaces prevent a convenient pure specification from becoming an unproved trusted replacement.

The observed samples validate the proposed interfaces and expose one failure mismatch. They do not quantify over all `u32` inputs or prove backend/native correspondence. That universal primitive proof is a future implementation task; the concrete operation/representation comparison requested here has actual observations.

## Boundaries

Known not to apply: a proof using only checked scalar successful values as if overflow were impossible, or a reference-layout identification based only on equal lane count. Not examined: other SIMD widths, non-power-of-two vector execution, shifts/division, floating-point/NaN semantics, x86 instructions, vector argument ABI, optimizer/backend validation, and unsupported-target controls. The official Arm intrinsic page could not be retrieved in this session; that operational failure establishes no absence or unsupported result. No invalid union read or invalid Rust execution was performed.

## Evidence

The package preserves `simd_union.rs` and `execution.json`, including final source SHA-256 `fa0773630c004eb1c85cc3d93b2e4ece77ac5e412e9962c56fdf44fadea295d2`, compiler identity, compile/native exit 0, and final output. Native output reports `neon=true`, 64 addition cases, eight union cases, checked overflow `None`, and portable overflow zero. Observation date: 2026-10-14.

- [Matching portable SIMD source](https://github.com/rust-lang/rust/tree/1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6/library/portable-simd/crates/core_simd/src): `vector.rs`, layout documentation, representation, load/store and array conversion; Git blob `55de9dac4637f9842259213ea599bfe0ddfe393f`. `ops.rs`, integer addition and wrapping arithmetic; The full Git blob identities of both files are retained in `source-identities.json`.
- [Matching NEON source](https://github.com/rust-lang/rust/blob/1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6/library/stdarch/crates/core_arch/src/arm_shared/neon/generated.rs), `vaddq_u32`, lines 1980–2001; complete-file SHA-256 `bcc351aa3331769468fc886aca610fc61af89ce10915a4f16493ad0f85517482`. The function's Arm documentation link is a lead rather than retrieved semantic evidence.
- [Rust Reference union rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/unions.md), common storage, field validity, and pattern evaluation warning; [layout rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-layout.md), C union layout; [undefined behavior rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md), target features, intrinsics, and invalid values. The Reference is the language authority examined; library comments are implementation documentation.

## Revalidation

With an explicitly selected compatible nightly compiler, compile `simd_union.rs` using `--edition=2024 -C opt-level=1`, record full `-vV`, and run only on an AArch64 host where its feature check succeeds. Check exact output and exit statuses, not merely compilation. On a changed target or compiler, redetermine the vector size/alignment and diff the intrinsic, arithmetic, and array conversion definitions. For a stronger primitive theorem, specify feature and memory premises and prove all-input wrapping behavior plus the exact lowering relation; increasing sample count alone cannot discharge that relation.

*Authored by an AI agent acting on joshlf's behalf.*
