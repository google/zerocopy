# Compiler-Selected Layout Queries, Slice-Tail DST Extents, and Sparse Allocation Footprints in `rustc`

## Summary

This report audits how `rustc` (`1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`) computes, represents, and lowers static and dynamically sized type (`DST`) layouts across `rustc_abi`, `rustc_ty_utils`, and `rustc_codegen_ssa`, and pairs that source audit with machine-checked Lean `4.34.1` models and counterexamples covering compiler-queried layout-table binding, slice-tail `#[repr(C)]` and `#[repr(C, packed(P))]` dynamic extent recurrences, non-contiguous allocation footprints (`core::ptr` sparse dereferenceability), and nominal type identity preservation across equal-layout `#[repr(C)]` structs.

Key technical findings include:
1. **Dynamic DST Size and Place Projection in `rustc` (`rustc_ty_utils` and `rustc_codegen_ssa`):** For an unsized struct with a slice tail `[T]`, `rustc` records the aligned tail byte offset as the static base `size` in `LayoutData` (`rustc_ty_utils/src/layout.rs:341-705`), and `size_of_val_raw` (`rustc_codegen_ssa/src/size_of_val.rs:11-94`) computes `round_up(head_offset + elem_size * slice_len, align)` at runtime. Applying `#[repr(C, packed(P))]` to an outer struct caps the alignment of its direct fields to $\min(\text{align}, P)$ without recursively flattening internal padding inside an already-sized inner `#[repr(C)]` struct field.
2. **Contiguous Extent vs. Non-Contiguous Active Byte Footprint (`core::ptr`):** Standard-library pointer dereferenceability (`library/core/src/ptr/mod.rs:108-165`) explicitly defines the dereferenceable footprint of a pointer to be a set of byte addresses that need **not** be a single contiguous `[base, base + size_of_val)` interval (for example, when `UnsafeCell` fields or padding bytes are excluded from shared-reference access footprints).
3. **Full-Range Content and Target Binding for Captured Layout Tables:** Binding a compiler-queried layout table solely by crate/SVH/source identity allows substituting mutated field alignments (`4 -> 8`) or empty tables (`PR86AuditRepairs.lean`). Furthermore, encoding `sizeBytes` and `alignBytes` into 16-bit little-endian fields without explicit range admission (`1..=65535`) admits a modular aliasing collision (`u32` size `4 + 65536 = 65540` hashes identically to `4`, proved in `PR92AuditCounterexamples.lean:layout_binding_loses_high_size_bits` and repaired in `q2_repaired_full_range_layout_binding_rejects_aliased_65540_size`).
4. **Universal `#[repr(C)]` Slice-Tail DST Recurrence Equivalence and Nominal Disambiguation:** For `#[repr(C)] struct PacketWithTail { header: u32, flags: u16, payload: [u32] }`, the compiler-queried layout descriptor (`headSize = 8, align = 4, fieldOffsets = [0, 4, 8], tailElemSize = 4`) agrees with the independent `#[repr(C)]` field-accumulation recurrence (`8 + n * 4`) for every slice length `n : Nat` (`PR94AuditCounterexamples.lean:c2_repaired_captured_layout_to_repr_c_universal_law_joined`), while distinct nominal `#[repr(C)]` structs sharing identical `{u32, u32}` geometry (`size = 8, align = 4, fieldOffsets = [0, 4]`) require `DefPathHash`-keyed disambiguation (`OpenHashMultiCrateR5R6R9R10.lean` and `Post96ChallengeGenerated.lean`).

## Applicability

- **Rust compiler and standard library source (`rust`):** `1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`:
  - `compiler/rustc_abi/src/lib.rs` (lines `1395–1565`)
  - `compiler/rustc_ty_utils/src/layout.rs` (lines `341–705`)
  - `compiler/rustc_codegen_ssa/src/size_of_val.rs` (lines `11–94`)
  - `compiler/rustc_codegen_ssa/src/mir/place.rs` (lines `285–355`)
  - `library/core/src/ptr/mod.rs` (lines `108–165`)
- **Compiler layout capture toolchains:**
  - `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` targeting `x86_64-unknown-linux-gnu` ([`support/out_r5_inner_lib_open_hash.json`](support/out_r5_inner_lib_open_hash.json))
  - `rustc 1.100.0-nightly (923c95cdf5ba65cea505aa2ea829f578e1506ed8)` targeting `aarch64-apple-darwin` ([`support/dual_nominal.rs`](support/dual_nominal.rs), [`support/AnnealResearch/Post96ChallengeGenerated.lean`](support/AnnealResearch/Post96ChallengeGenerated.lean))
- **Proof assistant (`lean`):** Lean `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` ([`support/r02-check-results.json`](support/r02-check-results.json)).

## Findings

### 1. `rustc` Source Audit: Static `LayoutData`, Unsized Struct Packing, and `size_of_val_raw` Lowering

Basis: source, documentation

Inspection of `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` establishes four implementation invariants across `rustc_abi`, `rustc_ty_utils`, and `rustc_codegen_ssa`:

1. **`LayoutData` Representation (`compiler/rustc_abi/src/lib.rs:1395-1565`):**
   - `LayoutData<FieldIdx, VariantIdx>` stores `fields: FieldsShape<FieldIdx>`, `variants: Variants<FieldIdx, VariantIdx>`, `backend_repr: BackendRepr`, `largest_niche: Option<Niche>`, `uninhabited: bool`, `align: AbiAndPrefAlign`, and `size: Size`.
   - For sized structs, `size` is the total aligned byte size (a multiple of `align.abi`). For unsized structs with a slice or `dyn Trait` tail, `size` is the byte offset of the unsized tail field (`tail_offset`), and `align.abi` is the static alignment of the header combined with the static alignment of the unsized tail (for `[T]`, $\max(\text{header\_align}, \text{align\_of}::<T>())$).
2. **Default `#[repr(Rust)]` Field Reordering vs. `#[repr(C)]` (`compiler/rustc_ty_utils/src/layout.rs:341-705`):**
   - Under `#[repr(Rust)]`, `layout_of_uncached` sorts fields by decreasing alignment/effective niche compatibility to minimize padding (`can_ireorder_fields`), except that an unsized tail field is always pinned to the final memory offset.
   - This reordering is directly observable in [`support/out_r5_inner_lib_open_hash.json`](support/out_r5_inner_lib_open_hash.json) on `x86_64-unknown-linux-gnu`: for `ScopedTicket<'a>` (whose source declaration order has field 0 of size/align 4 and field 1 `&'a mut AuditCounter` of size/align 8), `rustc` places field 1 at offset `0` and field 0 at offset `8` (`"size_bytes": 16, "align_bytes": 8, "field_offsets_bytes": [8, 0]`).
3. **Non-Recursive Semantics of `#[repr(packed(P))]` on Nested `#[repr(C)]` Structs (`compiler/rustc_ty_utils/src/layout.rs:420-560`):**
   - When computing a struct layout with `repr.pack = Some(P)`, `rustc` lowers each direct field's alignment to `field_align.min(P)` and reduces the outer struct's alignment to `max_field_align.min(P)`.
   - Crucially, `rustc` queries the already-computed `LayoutOf` of each sized field as an opaque `(size, align)` block. If an outer `#[repr(C, packed(1))]` struct contains an inner sized `#[repr(C)] struct Inner { a: u8, b: u32 }` (`size = 8, align = 4` with 3 bytes of internal padding at offsets `1..4`), the inner field is placed at a 1-byte-aligned offset in the outer struct, **preserving all 3 bytes of internal padding inside `Inner`**. Only `Inner`'s external alignment is capped to `1`.
4. **Dynamic `size_of_val_raw` and `align_of_val_raw` Lowering (`compiler/rustc_codegen_ssa/src/size_of_val.rs:11-94`, `mir/place.rs:285-355`):**
   - For slice-tail DSTs (`[T]`, `str`, or a struct ending in `[T]`), `size_of_val_raw` takes the wide pointer metadata `slice_len: usize`, computes `unaligned_size = head_offset + elem_size * slice_len`, and rounds up to the static alignment `align = align_of::<HeadAndElem>()` via `(unaligned_size + (align - 1)) & !(align - 1)`:
     - When `head_offset == 0` (a bare `[T]` slice), since `elem_size` is already a multiple of `align`, `rustc` skips the final rounding mask.
     - When `head_offset > 0` (a struct with a slice tail, such as `PacketWithTail`), `rustc` emits the rounding mask whenever `(head_offset % align != 0) || (elem_size % align != 0)`.
   - For `dyn Trait` tails, `size_of_val_raw` and `align_of_val_raw` load the dynamic size and alignment from vtable slots `COMMON_VTABLE_ENTRIES_SIZE` and `COMMON_VTABLE_ENTRIES_ALIGN`, then add `head_offset` and round up to `max(static_header_align, dynamic_vtable_align)`.

### 2. Sparse Dereferenceability vs. Contiguous Byte Extent

Basis: documentation, source, derived

In `library/core/src/ptr/mod.rs:108-165` (`S06`), the standard library defines what it means for a pointer to be "dereferenceable" by a given operation:
- Rather than universally identifying a pointer's dereferenceable footprint with the contiguous byte interval `[addr, addr + size_of_val)`, the documentation specifies that the dereferenceable footprint is a **set of byte addresses** determined by the pointee type and access kind (for example, shared references `&T` exclude byte ranges inside `UnsafeCell<U>` from read-aliasing uniqueness obligations, and typed value copies do not require padding bytes to be initialized).
- Consequently, any formal layout model must distinguish two separate spatial concepts:
  1. **Bounding Extent (`totalAlignedSize`):** The contiguous interval `[0, size_of_val(ptr))` used for allocation bounds, pointer `offset` / `add` arithmetic (`S24`), and `copy_nonoverlapping` (`S25`).
  2. **Active Field/Element Footprint (`isActivePayloadOffset`):** The subset of offsets `[0, size_of_val(ptr))` occupied by scalar/field payload bytes as opposed to inter-field or trailing padding.
- In [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) (`q5_r10_joined_specimen_and_footprint_boundaries_verified`, lines `1655–1735`), this distinction is mechanized on `#[repr(C)] struct PacketWithTail { header: u32, flags: u16, payload: [u32] }` at runtime slice length `n = 3`:
  - Total aligned extent is `20` bytes (`[0, 20)`), with `header` at `[0, 4)`, `flags` at `[4, 6)`, inter-field padding at `[6, 8)`, and `payload[0..3]` at `[8, 20)`.
  - Offset `6` satisfies `6 < 20` (within the allocation extent) but lies in the inter-field padding gap (`isActivePayloadOffset = false`), whereas offset `8` satisfies both `8 < 20` and `isActivePayloadOffset = true`.

### 3. Compiler-Queried Layout-Table Binding and the 16-Bit Modular Aliasing Counterexample

Basis: execution, derived

When an operational semantics or verification pipeline consumes compiler-queried `(size, align)` facts from `tcx.layout_of(ty)` (such as the 7 `computed_layouts` records in [`support/out_r5_inner_lib_open_hash.json`](support/out_r5_inner_lib_open_hash.json)), two subtle binding vulnerabilities arise if the layout sidecar is not cryptographically/structurally bound to both its full field values and its target triple:

| Vulnerability / Repair | Mechanized Module & Theorem | Technical Mechanism and Checked Result |
| :--- | :--- | :--- |
| **Unbound layout entries (`U7`)** | [`PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) (`checkLayoutTableBindingWithEntries`, lines `84–110`) | Checking only crate name, SVH, and source SHA-256 while ignoring `tbl.entries` allows substituting `sameIdentityAlign8` (mutating `u32` alignment from `4` to `8`) or an empty layout table (`emptyLayout`, causing `size_of`/`align_of` calls to fail with `.missingBody 38`). Hashing `encodeLayoutEntriesPayload` and binding `targetTripleBytes` rejects both mutations. |
| **16-bit modular size/alignment aliasing (`F2` / `Q2` counterexample)** | [`PR92AuditCounterexamples.lean`](support/AnnealResearch/PR92AuditCounterexamples.lean) (`layout_binding_loses_high_size_bits`, lines `59–70`) | Because `encodeLayoutEntryBytes` (`PR86AuditRepairs.lean:53-58`) serializes `sizeBytes` and `alignBytes` as two little-endian bytes (`e.sizeBytes % 256` and `(e.sizeBytes / 256) % 256`), adding $2^{16} = 65536$ to `u32.sizeBytes` (`aliasedSizeLayout`: `sizeBytes = 65540`) yields the **exact same encoded byte list** and 16-bit fingerprint `statefulGenericLibEntriesFp16`, while layout-callee synthesis uses the unreduced `65540`! |
| **Full-range injective layout entry admission (`Q2` repair)** | [`PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) (`encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2`, lines `1318–1432`) and [`PR92AuditCounterexamples.lean`](support/AnnealResearch/PR92AuditCounterexamples.lean) (`q2_repaired_full_range_layout_binding_rejects_aliased_65540_size`, lines `125–135`) | Enforcing `checkLayoutEntryInRangeQ2` (`1 <= sizeBytes <= 65535`, `1 <= alignBytes <= 65535`, power-of-two alignment) makes the 5-byte entry encoding injective (`encodeLayoutEntryBytes e1 = encodeLayoutEntryBytes e2 -> e1.sizeBytes = e2.sizeBytes /\ e1.alignBytes = e2.alignBytes /\ e1.typeTag = e2.typeTag`) and rejects `aliasedSizeLayout` (`65540`), `aliasedAlignLayout` (`65540`), `zeroAlignLayout` (`0`), and wrong target triples while accepting the boundary value `65535`. |

### 4. Compiler-Queried Layout Witnesses and Universal `#[repr(C)]` Slice-Tail DST Recurrence Laws

Basis: execution, derived

In [`support/out_r5_inner_lib_open_hash.json`](support/out_r5_inner_lib_open_hash.json) (captured from `r5_inner_lib.rs` under `rustc 1.98.0-nightly` on `x86_64-unknown-linux-gnu`) and mechanized in [`OpenHashMultiCrateR5R6R9R10.lean`](support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean), [`PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean), and [`PR94AuditCounterexamples.lean`](support/AnnealResearch/PR94AuditCounterexamples.lean), seven representative layout patterns are verified:

| Type in `r5_inner_lib` | Representation | Captured `size_bytes` | Captured `align_bytes` | Captured `field_offsets_bytes` | Special Properties |
| :--- | :--- | ---: | ---: | :--- | :--- |
| `WindowSpec` | `#[repr(C)]` (`usize, usize`) | `16` | `8` | `[0, 8]` | Sized 2-field scalar struct |
| `AuditCounter` | `#[repr(C)]` (`u32, u32`) | `8` | `4` | `[0, 4]` | Sized 2-field counter |
| `ScopedTicket<'a>` | `#[repr(Rust)]` (`u32, &'a mut AuditCounter`) | `16` | `8` | `[8, 0]` | Demonstrates `rustc` field reordering + `Drop` |
| `Option<NonZeroU32>` | Standard library niche (`S18`) | `4` | `4` | `[0]` | `has_niche: true`, zero discriminant niche |
| `ReprCPaddedHeader` | `#[repr(C)]` (`u8, u32, u16`) | `12` | `4` | `[0, 4, 8]` | 3 bytes inter-field pad (`1..4`), 2 bytes trailing pad (`10..12`) |
| `PackedHeader` | `#[repr(C, packed)]` (`u8, u32, u8`) | `6` | `1` | `[0, 1, 5]` | Zero inter-field or trailing padding |
| `PacketWithTail` | `#[repr(C)]` (`u32, u16, [u32]`) | `8` (head) | `4` | `[0, 4, 8]` | `is_unsized_slice_tail: true`, `tail_elem_size_bytes: 4`, `tail_elem_align_bytes: 4` |

On the slice-tail DST `PacketWithTail`, the mechanized proofs establish:
1. **Universal `∀ n : Nat` Agreement Between Captured Descriptor and Independent `#[repr(C)]` Recurrence (`PR94AuditCounterexamples.lean:93-102`, `OpenHashMultiCrateR5R6R9R10.lean:1131-1155`):**
   - `checkCapturedSliceTailDstLayoutAgainstReprCC2` verifies that the captured descriptor `r10PacketWithTailDstLayout` and target triple `x86_64-unknown-linux-gnu` match the independent `#[repr(C)]` recurrence `computeReprCStructAndSliceTailLayoutC2 [(4, 4), (2, 2)] 4 4 none 0`.
   - For every slice length `n : Nat`, both `computeDstTotalSizeChecked r10PacketWithTailDstLayout n` and `computeReprCStructAndSliceTailLayoutC2 [(4, 4), (2, 2)] 4 4 none n` evaluate to `8 + n * 4` with field/tail offsets `[0, 4]` and `8` and alignment `4` (`c2_repaired_captured_layout_to_repr_c_universal_law_joined`).
2. **Contrast with `#[repr(C, packed(2))]` (`PR86AuditRepairs.lean:1675-1695`):**
   - Applying `packCapOpt = some 2` (`q5_r10_packet_with_tail_packed2_universal_law`) caps the tail `u32` element alignment to `2`, eliminating the 2-byte padding gap after `flags: u16` and shifting the tail offset from `8` to `6`, yielding total size `6 + n * 4` and alignment `2` for all `n : Nat`.
3. **Rejection of Descriptor/Target Mismatches (`PR94AuditCounterexamples.lean:78-91`):**
   - Mutating the captured tail offset (`[0, 4, 12]`), tail element size (`4 -> 8`), or target triple (`mutatedTargetTripleBytesC2`) is rejected (`= false`) by `checkCapturedSliceTailDstLayoutAgainstReprCC2`, and substituting a different specimen's `(u16, u32, [u16])` header fields (`size = 16` at `n = 3`) against `PacketWithTail` (`size = 20` at `n = 3`) is caught by `r7_and_r10_use_different_layouts` (`PR92AuditCounterexamples.lean:98-102`).

### 5. Nominal Type Disambiguation Across Identical `#[repr(C)]` Layouts

Basis: execution, derived

Two distinct `#[repr(C)]` structs with identical field types (such as `{ a: u32, b: u32 }`) have identical physical layouts (`size = 8, align = 4, fieldOffsets = [0, 4]`), yet are incompatible nominal types in Rust. Two complementary mechanized experiments establish how consumers must bind nominal `DefPathHash` identities alongside layout records:
1. **Cross-Crate Nominal Pair and Shape-Preserving Return-Swap Challenge (`OpenHashMultiCrateR5R6R9R10.lean:894-1002`, `PR92AuditCounterexamples.lean:175-210`):**
   - `MeterReading` (`DefPathHash(6971513911418584772, 12106348439045982925)`) and `LimitThreshold` (`DefPathHash(6971513911418584772, 3272573844775167984)`) both have two `u32` fields (`size = 8, align = 4`).
   - `checkNominalPairClientBoundToOpenAdtTableC2` resolves compilation-local runtime carrier tags from the per-compilation `open_adt_table` by `DefPathHash`, accepting both baseline and refactored compilations (`= true`), while rejecting table/body cross-substitutions and rejecting the shape-preserving 280-byte mutant `q9ShapePreservingNominalReturnSwapBytes` (`q9_shape_preserving_nominal_return_swap_challenge`) that swaps only the return type tags of `make_meter_reading` and `make_limit_threshold`.
2. **Native Darwin Dual-Nominal `#[repr(C)]` Capture (`support/dual_nominal.rs`, `Post96NativeConsumer.lean`, `Post96ChallengeGenerated.lean`):**
   - Captured under `rustc 1.100.0-nightly (923c95cdf)` on `aarch64-apple-darwin` (raw JSON SHA-256 `a7474461dcc8ea8895849f831250c1c7d464b973ab5e525b53cc17dac2b2897c`), `dualNominal` contains two `#[repr(C)]` `{u32, u32}` structs (`DefPathHash(..., 11641737318210017662)` and `DefPathHash(..., 1661796016192393180)`).
   - `Post96NativeConsumer.checkNativeType` verifies each `#[repr(C)]` struct's `fieldOffsets = [0, 4]`, `sizeBytes = 8`, and `alignBytes = 4` against `accumReprCFields none [(4, 4), (4, 4)]`.
   - `dualNominal_public_gate` and `two_distinct_nominal_keys` pass (`= true`, `= 2`), while `badSecondLayout_public_gate` rejects (`= false`) a mutated capture where the second struct's `fieldOffsets` are altered to `[0, 8]`.

## Boundaries

- **Not examined:**
  - Custom dynamically sized types beyond slice tails (`[T]` / `str`) and `dyn Trait` (such as unstable `extern type` thin DSTs).
  - SIMD vector alignment target variations (`#[repr(simd)]`) and C bitfield layout rules.
- **Unknown / unspecified in Rust:**
  - Field ordering, inter-field padding locations, and niche selection for general `#[repr(Rust)]` structs and enums outside the guaranteed `Option` non-null niche cases (`S13`, `S18`).
  - Ordering of `(data_ptr, metadata)` inside wide pointers (`*const [T]`, `*const dyn Trait`, `S11`).
- **Known not to apply:**
  - `#[repr(C, packed(P))]` on an outer struct does **not** recursively strip internal padding inside a nested sized `#[repr(C)]` struct field (`Finding 1.3`).
  - Contiguous byte extent `[0, size_of_val(ptr))` does **not** imply that every byte in that interval belongs to the active non-padding/non-`UnsafeCell` dereferenceable set (`Finding 2`).
- **Unsupported without explicit range and nominal checks:**
  - Consuming 16-bit serialized layout tables without `1..=65535` range checks (`Finding 3`), or identifying nominal `#[repr(C)]` types solely by their `(size, align, fieldOffsets)` tuple (`Finding 5`).

## Evidence

- [`support/out_r5_inner_lib_open_hash.json`](support/out_r5_inner_lib_open_hash.json) — Retained compiler-queried layout and MIR sidecar from `r5_inner_lib.rs` (`rustc 1.98.0-nightly`, `x86_64-unknown-linux-gnu`), recording `computed_layouts` for `WindowSpec`, `AuditCounter`, `ScopedTicket`, `OptionNonZeroU32`, `ReprCPaddedHeader`, `PackedHeader`, and `PacketWithTail`.
- [`support/dual_nominal.rs`](support/dual_nominal.rs) — Two-nominal-struct `#[repr(C)]` Rust source captured under `rustc 1.100.0-nightly` (`aarch64-apple-darwin`).
- [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) — Mechanization of `checkLayoutTableBindingWithEntries`, `checkLayoutTableBindingFullRangeQ2`, `encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2`, `computeReprCStructAndSliceTailLayout`, and `q5_r10_joined_specimen_and_footprint_boundaries_verified`.
- [`support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`](support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean) — Mechanization of the `R10` compiler-queried layout records, `q5_r10_captured_descriptor_universal_size_law`, `checkNominalPairClientBoundToOpenAdtTableC2`, and `checkCapturedSliceTailDstLayoutAgainstReprCC2`.
- [`support/AnnealResearch/PR92AuditCounterexamples.lean`](support/AnnealResearch/PR92AuditCounterexamples.lean) and [`support/AnnealResearch/PR94AuditCounterexamples.lean`](support/AnnealResearch/PR94AuditCounterexamples.lean) — Mechanization of the 16-bit `65540` size-aliasing counterexample (`layout_binding_loses_high_size_bits`), the two-specimen mismatch (`r7_and_r10_use_different_layouts`), the shape-preserving nominal return swap (`q9_shape_preserving_nominal_return_swap_challenge`), and the repaired universal `∀ n : Nat` DST laws (`c2_repaired_captured_layout_to_repr_c_universal_law_joined`).
- [`support/AnnealResearch/Post96Consumer.lean`](support/AnnealResearch/Post96Consumer.lean), [`support/AnnealResearch/Post96NativeConsumer.lean`](support/AnnealResearch/Post96NativeConsumer.lean), and [`support/AnnealResearch/Post96ChallengeGenerated.lean`](support/AnnealResearch/Post96ChallengeGenerated.lean) — Mechanization of `checkNativeType` (`#[repr(C)]` field-offset recurrence check) and the `dualNominal` / `badSecondLayout` gates.
- [`support/r02-check-results.json`](support/r02-check-results.json) — Complete Lean `4.34.1` check ledger for all 18 modules in the dependency closure (`2026-10-24`, zero `sorryAx`, standard axioms `[propext, Quot.sound]` only).

## Revalidation

All 18 Lean `4.34.1` modules in [`support/AnnealResearch/`](support/AnnealResearch) can be re-checked in topological order from the package directory using an isolated temporary build directory:

```sh
python3 - <<'PY'
import json, os, pathlib, subprocess, tempfile

pkg = pathlib.Path("reports/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit")
sup = pkg / "support"
ledger = json.loads((sup / "r02-check-results.json").read_text())

with tempfile.TemporaryDirectory() as tmp:
    build_dir = pathlib.Path(tmp)
    (build_dir / "AnnealResearch").mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(build_dir)
    for mod in ledger["topological_order"]:
        src = sup / "AnnealResearch" / f"{mod}.lean"
        olean = build_dir / "AnnealResearch" / f"{mod}.olean"
        subprocess.run(
            ["lean", "-j1", "-M2048", "-o", str(olean), str(src)],
            cwd=str(sup),
            env=env,
            check=True,
        )
    print(f"Successfully re-verified all {len(ledger['topological_order'])} Lean 4.34.1 modules.")
PY
```
