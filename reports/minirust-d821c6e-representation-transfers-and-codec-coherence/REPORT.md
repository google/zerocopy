# MiniRust `d821c6e` Byte Representation Transfers, Pointer Provenance Decoding, Dead-Data Correspondence, and Codec Coherence

## Summary

This report documents four interconnected operational-semantics investigations and 20 machine-checked Lean `4.34.1` modules (`zero` added axioms, `zero` `sorry` proofs) examining byte-level value representations, memory transfers, pointer provenance decoding, relational dead-data erasure, and static-versus-dynamic codec coherence against MiniRust (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) and Rust `1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

The mechanized results establish four main technical findings:
1. **Raw vs. Policy-Qualified Typed Memory Transfers (`Representation`, `ByteMemory`, `PartialTransfers`, `Transfers`, `TransferExamples`, `PrefixTransfer`):** Connecting target-parameterized pointer-fragment cells (`Uninit | Init(u8, Option<Fragment>)`) to stateful read/write memory transitions proves that snapshot-based raw byte copying (`ptr::copy` / `ptr::copy_nonoverlapping`) preserves initialized padding, uninitialized cells, and partial pointer fragments (including out-of-order two-piece pointer assembly), whereas typed aggregate transfers (`*dst = *src` / `MaybeUninit` value copies) reset destination padding to `Uninit` and transform pointer provenance through an explicit reborrow/tag map (`raw_and_typed_padding`).
2. **Thin-Pointer Provenance Decoder Discrepancy (`MiniRustDecoder`):** Transcribing `decode_ptr` from `minirust@d821c6e:spec/lang/representation.md:112-133` on `x86_64` (`spec/prelude/target.md:33-45`) proves (`mixed_fragment_counterexample`) that MiniRust's `decode_ptr` silently strips provenance (`provenance = None`) and returns a valid raw pointer when initialized bytes have missing, mixed, or wrong-offset provenance fragments, whereas strict fragment-coherence decoding (`Representation.decodePtr`) rejects incoherent provenance fragments as decode failure (`none`).
3. **Dead-Allocation Byte Erasure vs. Tombstone Preservation (`DeadData`, `DeadDataExecution`, `DeadDataControls`, `DeadDataWitnesses`):** In `BasicMemory` (`spec/mem/basic.md`), `deallocate` marks an allocation dead (`live = false`) while retaining its record and byte map. Erasing the stored bytes of dead allocations to `Uninit` (`DeadData.normalize`) while retaining allocation IDs, `next` counters, and dead tombstones preserves bidirectional finite-prefix coverage and `NoUB` equivalence (`reference_forward_prefix`, `reference_backward_prefix`, `reference_noUB_iff`) across all syntactic states and allocator candidates. However, deleting dead tombstones changes stale-pointer dereference from `UB` to `unsupported`, and arbitrary `DeadData.Same`-related states do **not** transport canonical `StateWF` without normalization (`DeadDataControls`).
4. **Finite Codec Coherence, Instance Binding, and the `minirust#288` Well-Formedness Gap (`CodecAdmission`):** Specializing MiniRust's `Bool`, empty `Tuple`, and 2-variant `Enum` representations (`spec/lang/representation.md:50-68, 249-276, 353-430, 590-763`; `spec/lang/well-formed.md:215-284`) proves that structural well-formedness (`StaticAdmission`), codec coherence (`EnumCoherent`), dispatch instance identity (`advertisedId == selectedId`), and evaluated constant certificates (`ConstCert`) are independent obligations. An enum with `Discriminator::Known(0)` satisfies structural well-formedness (`minirust#288`) yet violates round-trip (`decode(encode(1)) = some 0`), swapping normal and reversed coherent enum instances breaks the caller's contract despite both codecs being internally coherent, and an admitted Boolean operation still dynamically steps to explicit `UB` on byte `0x02`.

## Applicability

- **MiniRust specification (`minirust`):** Commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`):
  - `spec/lang/representation.md` (lines `50–68`, `112–140`, `249–276`, `353–430`, `590–763`)
  - `spec/lang/well-formed.md` (lines `155–284`)
  - `spec/prelude/target.md` (lines `33–45`)
  - `spec/mem/basic.md` (lines `1–265`, `206–212`)
- **Rust documentation and standard library (`rust`):** `1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67` (and bundled Reference `82da570bafd9efed421bdbae0f8603ede8dd308b`):
  - `src/memory-model.md:4-26`, `src/behavior-considered-undefined.md:165-191`, `src/type-layout.md:18-64, 203-216`
  - `library/core/src/ptr/mod.rs:576-611`, `library/core/src/mem/maybe_uninit.rs:267-312`
- **Safe layout probe (`rustc-layout-probe`):** [`support/layout-probe.rs`](support/layout-probe.rs), verified under `rustc 1.99.0 (b940084d7)` on `aarch64-apple-darwin` and re-verified under `rustc 1.101.0-nightly (19833af72 2026-10-20)` on `x86_64-unknown-linux-gnu` ([`support/layout-probe-output.json`](support/layout-probe-output.json)).
- **Proof assistant (`lean`):** Lean `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` ([`support/r03-check-results.json`](support/r03-check-results.json)).

## Findings

### 1. Target-Parameterized Byte/Fragment Representation and Padded `#[repr(C)]` Aggregate Codec

Basis: execution, derived, documentation

In [`support/AnnealResearch/Representation.lean`](support/AnnealResearch/Representation.lean), each physical memory byte is modeled as `Cell := uninit | init (byte : Byte) (frag : Option Fragment)`, where `Fragment` records `(allocId : Nat, generation : Nat, tag : Nat, index : Nat)` (`index` is the byte-significance index, mapped to physical byte offset via `significance : Target -> Fin width -> Nat` supporting both little-endian and big-endian targets):

1. **Universal Thin-Pointer Codec Round-Trip and Rejection Controls:**
   - `significance_involution` proves that the endianness index permutation is an involution for every positive `width` and both endian orders.
   - `decodePtr_encodePtr` and `both_endian_roundTrips` prove `decodePtr t (encodePtr t p) = some p` for every positive target width, both endian orders, every address byte vector, and optional provenance.
   - `decodePtr_eq_some_iff` proves that the finite executable decoder succeeds if and only if every byte in `0..t.width` is initialized and carries a fragment coherent with `p.provenance` at its significance index.
   - Negative controls prove rejection (`= none`) for uninitialized bytes (`decodePtr_reject_uninit`), wrong significance index (`decodePtr_reject_wrong_index`, `scrambled_fragment_rejected`), partially missing fragments (`missing_fragment_rejected`), and mixed provenance from distinct pointers (`decodePtr_reject_mixed`, `mixed_fragments_rejected`).
2. **Conditional `#[repr(C)]` Padded Aggregate Layout (`Packet { tag: u8, ptr: *const u8 }`):**
   - For a `#[repr(C)]` aggregate containing a 1-byte `tag: u8` at offset `0` followed by a thin pointer `ptr: *const u8` of width `w` and alignment `a` (where `a > 0` is a power of two dividing `w`), C-layout rules (`src/type-layout.md:203-216`) place `ptr` at offset `a`, inter-field padding at `1..a`, and total extent `a + w`.
   - `packetLayout_admissible` and `conditional_packet_layouts` discharge the codec admissibility obligations for `(w, a)` in `{(4, 4), (8, 8), (8, 4)}`.
   - Executing [`support/layout-probe.rs`](support/layout-probe.rs) produces [`support/layout-probe-output.json`](support/layout-probe-output.json) (`{"pointer_bytes":8,"pointer_alignment":8,"tag_offset":0,"pointer_offset":8,"packet_size":16,"packet_alignment":8,"little_endian":true}`), matching the `(8, 8)` little-endian instance.

### 2. Raw Snapshot Copies, Out-of-Order Partial Transfers, Typed Reborrow Transfers, and Prefix Execution

Basis: execution, derived, source

Connecting `Representation.Cell` to byte-indexed operational memory in [`ByteMemory.lean`](support/AnnealResearch/ByteMemory.lean), [`PartialTransfers.lean`](support/AnnealResearch/PartialTransfers.lean), [`Transfers.lean`](support/AnnealResearch/Transfers.lean), [`TransferExamples.lean`](support/AnnealResearch/TransferExamples.lean), and [`PrefixTransfer.lean`](support/AnnealResearch/PrefixTransfer.lean) establishes:

| Mechanism / Theorem | Module | Checked Operational Property |
| :--- | :--- | :--- |
| **Snapshot-based raw copy (`rawCopy_success`, `runRawCopy_projection`)** | `ByteMemory.lean`, `Transfers.lean` | Raw reads never decode cells; they capture a cell snapshot and apply read permission effects before checking destination write authority (`library/core/src/ptr/mod.rs:576-611`). Preserves uninitialized bytes, initialized padding, and partial pointer fragments verbatim, including overlapping ranges; if the write fails, `runRawCopy` retains the post-read permission state rather than reverting to the pre-read state. |
| **Out-of-order partial pointer copy (`partial_copies_assemble_pointer`)** | `PartialTransfers.lean` | Copying the upper 2 bytes of a 4-byte pointer first leaves an intermediate destination that fails pointer decoding (`partial_copy_alone_rejected`); subsequently copying the lower 2 bytes into their matching offsets reconstructs the original pointer (`some examplePtr`). |
| **Raw vs. typed padding and provenance (`typedCopyAggregate_supported`, `raw_and_typed_padding`)** | `Transfers.lean`, `Representation.lean` | On the same admitted source and destination, raw copying preserves initialized padding byte `1` (`Init 99 none`) and exact pointer tags, whereas typed aggregate transfer resets destination padding to `Uninit` (`typed_transfer_resets_padding`) and applies the provenance policy map (`withTag 19` in `raw_and_reborrow_differ`, reflecting `library/core/src/mem/maybe_uninit.rs:267-312`). |
| **Two-stage pointer load and pointee read (`loadAndRead_supported`)** | `Transfers.lean`, `TransferExamples.lean` | Loads a 4-byte aligned pointer from storage, decodes its address (`addressNumber_bound < 256^width`) and provenance, resolves allocation liveness/generation/bounds, and reads pointee value `77` in the post-pointer-load permission state. Bumping only the allocation generation rejects the stale pointer while retaining the post-load state; provenance-free pointers decode (`some`) but are rejected on nonzero ordinary-allocation dereference. |
| **Small-step prefix safety & cleanup integration (`PrefixTransfer.lean`)** | `PrefixTransfer.lean`, `Execution.lean` | Embeds multi-step raw and typed transfer plans into the finite-prefix operational machine (`Execution.NoUB` and `Verified`), proving that intermediate permission revocations or uninitialized cleanup reads are caught at the exact failing prefix even if a later continuation could spin forever. |

### 3. Thin-Pointer Provenance Decoder Discrepancy: MiniRust `decode_ptr` vs. Strict Fragment Coherence

Basis: source, execution, derived

[`support/AnnealResearch/MiniRustDecoder.lean`](support/AnnealResearch/MiniRustDecoder.lean) transcribes `decode_ptr` from `minirust@d821c6e:spec/lang/representation.md:112-133` specialized to the pinned 64-bit little-endian target (`spec/prelude/target.md:33-45`):
- In MiniRust (`representation.md:112-133`), `decode_ptr` first requires all 8 bytes to be `Init` (failing to `None` if any byte is `Uninit`), computes the numeric address from the `u8` values, initializes the provenance accumulator from byte `0`'s fragment (`lines 119–120`), and folds over indices `i = 0..7` (`lines 121–129`): if byte `i`'s fragment matches `(alloc_id, i)`, the accumulator is kept; otherwise the accumulator becomes `None` (absent provenance), **and `decode_ptr` still succeeds (`Some(Ptr { addr, provenance: None })`) at line 132**.
- By contrast, the strict canonical decoder (`Representation.decodePtr` via `canonicalDecodeLE8`) requires all 8 bytes to satisfy a single coherent provenance judgment (`all absent` or `all present with matching allocId and byte index`), rejecting mixed/partial/wrong-position fragments as decode failure (`none`).

Both decoders are evaluated on five 8-byte blocks with numeric little-endian address `1`:

| Control Block | Fragment Pattern Across Bytes `0..7` | MiniRust `decodeLE8` (`observeSource`) | Strict `canonicalDecodeLE8` (`observeCanonical`) | Checked Theorem Endpoint in `MiniRustDecoder.lean` |
| :--- | :--- | :--- | :--- | :--- |
| `missingFragment` | Byte `0`: `ID0/pos0`; Byte `1`: `none`; Bytes `2..7`: `ID0/pos2..7` | `some (1, none)` (strips provenance) | `none` (decode failure) | `missingFragment_fallback`, `missingFragment_failure`, `missingFragment_differ`, `mixed_fragment_counterexample` |
| `wrongPositionFragment` | All bytes have `ID0`, but Byte `1` claims `pos = 2` | `some (1, none)` (strips provenance) | `none` (decode failure) | `wrongPositionFragment_fallback`, `wrongPositionFragment_failure`, `wrongPositionFragment_differ` |
| `uniformNoProvenance` | All 8 fragments `none` | `some (1, none)` | `some (1, none)` | `uniformNoProvenance_agrees` |
| `coherentBytes` | Byte `i` has `ID0/pos i` for all `i in 0..7` | `some (1, some 0)` | `some (1, some 0)` | `coherentBytes_agrees` |
| `withUninit` | Byte `3` is `Uninit`; all others coherent | `none` (decode failure) | `none` (decode failure) | `uninit_fails_both` |

### 4. Dead-Allocation Byte Erasure and Relational Memory Correspondence

Basis: execution, derived

In MiniRust's `BasicMemory` (`minirust@d821c6e:spec/mem/basic.md`, mechanized in [`MiniRustReference.lean`](support/AnnealResearch/MiniRustReference.lean) and [`MiniRustFactored.lean`](support/AnnealResearch/MiniRustFactored.lean)), freeing an allocation marks its metadata `live = false` while leaving its historical byte map intact. [`DeadData.lean`](support/AnnealResearch/DeadData.lean), [`DeadDataExecution.lean`](support/AnnealResearch/DeadDataExecution.lean), [`DeadDataControls.lean`](support/AnnealResearch/DeadDataControls.lean), and [`DeadDataWitnesses.lean`](support/AnnealResearch/DeadDataWitnesses.lean) prove the exact boundary of what a raw-memory equivalence relation must retain:

1. **Coarse Equivalence (`DeadData.Same`) and Dead-Only Normalization (`DeadData.normalize`):**
   - `DeadData.normalize` overwrites cells with `Uninit` if and only if their allocation ID has an explicit metadata entry with `live = false`. It preserves `next`, the complete metadata map (including dead tombstones), and all live allocation cells.
   - `DeadData.Same` requires equal `next` counters, equal metadata maps, and equal cells at all offsets of all live allocations, ignoring dead-allocation contents.
2. **Universal Bidirectional Finite-Prefix and `NoUB` Correspondence (`DeadDataExecution.lean`):**
   - Without assuming `StateWF` or prior access safety, every primitive operation (`allocate`, `deallocate`, `load`, `store`, `dereferenceable`) and whole-execution step commutes with `DeadData.Same` for every natural allocator candidate (`reference_forward_prefix`, `reference_backward_prefix`, `reference_noUB_iff`, `encoded_normalized_noUB_iff`).
   - Existing universal family safety proofs and enabled spin/clean-exit execution traces transport across the bridge without re-proving the source safety invariant (`DeadDataWitnesses.lean`).
3. **Discriminating Controls and Why `StateWF` Transport Requires Explicit Normalization (`DeadDataControls.lean`):**
   - **Dead-byte erasure vs. live-byte erasure:** Allocating ID `0`, storing `7`, and freeing leaves `7` in unnormalized dead storage and `Uninit` in normalized storage while preserving `Same`; erasing a *live* byte changes raw `load` replies and falsifies `Same`.
   - **Tombstone deletion mutant:** Deleting a dead allocation's metadata record instead of keeping its `live = false` tombstone changes a stale-pointer dereference from dead-allocation `UB` to `unsupported`, falsifying `Same`.
   - **Failed generic `StateWF` transport across arbitrary `Same`-related states:** Canonical `StateWF` checks that every fragment ID in memory (even inside dead allocations) is `< next`. Placing a forged fragment with `allocId = 1` inside dead allocation `0` when `next = 1` produces a state that is `DeadData.Same`-equivalent to an admitted state, yet violates `StateWF`! By contrast, `DeadData.normalize` erases dead cells to `Uninit` and therefore preserves `StateWF` forward.

### 5. Finite Codec Coherence, Instance Binding, and the `minirust#288` Well-Formedness Gap

Basis: source, execution, derived

[`support/AnnealResearch/CodecAdmission.lean`](support/AnnealResearch/CodecAdmission.lean) specializes MiniRust's scalar value representations (`spec/lang/representation.md:50-68, 249-276, 353-430, 590-763`; `spec/lang/well-formed.md:215-284`) to a 1-byte domain (Booleans and 2-variant empty-tuple Enums with a `tagger` byte table and a 1-level `Discriminator` tree) and proves six sharp discriminators:

| Discriminator in `CodecAdmission.lean` | Static Shape (`DefShape`) | Codec Coherence (`EnumCoherent`) | Instance ID & `ConstCert` | Checked Operational / Algebraic Outcome |
| :--- | :--- | :--- | :--- | :--- |
| **1. Admitted normal, swapped, and Boolean instances** | Holds | Holds | Holds (`val < 256`) | Satisfies full `Admitted`; derived round-trip `decode(encode(v)) = some v` and provenance deflation `encode(v) <= bytes` hold. |
| **2. Incoherent Enum with `Known(0)` (`minirust#288`)** | Holds (`StaticAdmission = true`) | **Fails** | Holds | `tagger` writes `1` for variant `1`, but `Discriminator::Known(0)` decodes every byte to variant `0` without reading the tag (`decode(encode(1)) = some 0 != some 1`). Structural `check_wf` (`StaticAdmission`) does **not** imply round-trip! |
| **3. Swapped coherent Enum dispatch** | Holds | Holds for both normal and swapped | **Fails** (`advertisedId != selectedId`) | Both normal (`0->0, 1->1`) and swapped (`0->1, 1->0`) codecs satisfy their own round-trip and deflation laws, but dispatching `swapped` when `normal` was advertised flips `decode([Init 1 none])` from variant `1` to `0`. |
| **4. Missing or out-of-range `ConstCert`** | Holds | Holds | **Fails** (`none` or `arg = 256`) | Without a certificate proving `arg < 256`, `StaticAdmission` rejects; arithmetic bound theorem refutes any certificate for `256`. |
| **5. Invalid Boolean byte `0x02` at runtime** | Holds | Holds | Holds (`Admitted = true`) | Passing `[Init 2 none]` (length `1`) to the admitted Boolean decode operation avoids wrapper specification failure (`definition_classified`) and steps to explicit object-language `UB`. |
| **6. Provenance deflation on `Bool`** | Holds | Holds | Holds | `[Init 1 (some 7)]` decodes to `true` and re-encodes to `[Init 1 none]`, which satisfies pointwise deflation (`<=`) while refuting exact byte equality (`!=`). |

## Boundaries

- **Not examined:**
  - Multi-byte integer endianness inside `Enum` taggers, nested multi-field `Enum` discriminators, niche-encoded multi-byte `Option` payloads, or concurrent weak-memory `Ordering` interactions with byte fragments.
  - Compiler-to-MiniRust translation (`minimize`) or automatic extraction of `MiniRust` ASTs from `rustc`.
- **Unknown / open in normative Rust:**
  - Whether runtime Rust permits reading mixed/partial pointer fragments as a provenance-free pointer (as MiniRust's `decode_ptr` does in `Finding 3`) or treats incoherent pointer fragments as unusable/uninitialized during typed pointer loads (`S03`, `S20`).
- **Known not to apply:**
  - Raw byte-equality after `encode(decode(bytes))` does **not** hold for provenance-bearing scalar bytes (`Finding 5.6`: only provenance deflation `encode(v) <= bytes` holds) or for padded aggregates under typed copies (`Finding 2`: padding resets to `Uninit`).
  - MiniRust's `Type::check_wf` (`spec/lang/well-formed.md:215-284`) does **not** imply `decode(encode(v)) == Some(v)` for `Type::Enum` without an additional `EnumCoherent` premise (`Finding 5.2`, `minirust#288`).
  - `DeadData.Same` equivalence does **not** transport canonical `StateWF` across arbitrary unnormalized states containing dead-storage fragments (`Finding 4.3`).
- **Unsupported as a security/physical claim:**
  - Mathematical dead-data normalization (`DeadData.normalize`) is a relational proof technique for raw-memory operational equivalence; it does **not** prove physical RAM secret zeroization or hardware side-channel erasure.

## Evidence

- [`support/layout-probe.rs`](support/layout-probe.rs) and [`support/layout-probe-output.json`](support/layout-probe-output.json) — Safe `#[repr(C)] struct Packet { tag: u8, ptr: *const u8 }` layout observation (`size = 16, align = 8, ptr_offset = 8` on 64-bit little-endian targets).
- [`support/AnnealResearch/Representation.lean`](support/AnnealResearch/Representation.lean), [`support/AnnealResearch/ByteMemory.lean`](support/AnnealResearch/ByteMemory.lean), [`support/AnnealResearch/PartialTransfers.lean`](support/AnnealResearch/PartialTransfers.lean), [`support/AnnealResearch/Transfers.lean`](support/AnnealResearch/Transfers.lean), [`support/AnnealResearch/TransferExamples.lean`](support/AnnealResearch/TransferExamples.lean), and [`support/AnnealResearch/PrefixTransfer.lean`](support/AnnealResearch/PrefixTransfer.lean) — Mechanization of target-aware pointer-fragment codecs, padded `#[repr(C)]` layouts, snapshot raw copies, out-of-order partial pointer copies, typed reborrow transfers, and small-step prefix execution.
- [`support/AnnealResearch/MiniRustDecoder.lean`](support/AnnealResearch/MiniRustDecoder.lean) — Audited transcription of `minirust@d821c6e` `decode_ptr` (`spec/lang/representation.md:112-133`) and machine-checked proof of `mixed_fragment_counterexample` against `Representation.decodePtr`.
- [`support/AnnealResearch/DeadData.lean`](support/AnnealResearch/DeadData.lean), [`support/AnnealResearch/DeadDataExecution.lean`](support/AnnealResearch/DeadDataExecution.lean), [`support/AnnealResearch/DeadDataControls.lean`](support/AnnealResearch/DeadDataControls.lean), and [`support/AnnealResearch/DeadDataWitnesses.lean`](support/AnnealResearch/DeadDataWitnesses.lean) — Mechanization of dead-allocation byte erasure, bidirectional finite-prefix and `NoUB` correspondence, tombstone-deletion and `Same`-without-`StateWF` counterexamples, and family safety transport.
- [`support/AnnealResearch/CodecAdmission.lean`](support/AnnealResearch/CodecAdmission.lean) — Mechanization of finite `Bool`/`Enum` codec coherence, the `minirust#288` `Known(0)` round-trip counterexample, swapped coherent instance dispatch rejection, `ConstCert` arithmetic bounds, and runtime invalid-`Bool` `UB`.
- [`support/r03-check-results.json`](support/r03-check-results.json) — Complete Lean `4.34.1` check ledger for all 20 modules in the topological dependency closure (`2026-10-24`, `18.502` seconds total, zero `sorryAx`, standard Lean axioms only).

## Revalidation

To re-compile and run [`support/layout-probe.rs`](support/layout-probe.rs) and re-check all 20 Lean `4.34.1` modules in [`support/AnnealResearch/`](support/AnnealResearch) in topological order from the repository root:

```sh
python3 - <<'PY'
import json, os, pathlib, subprocess, tempfile

pkg = pathlib.Path("reports/minirust-d821c6e-representation-transfers-and-codec-coherence")
sup = pkg / "support"
ledger = json.loads((sup / "r03-check-results.json").read_text())

with tempfile.TemporaryDirectory() as tmp:
    tmp_path = pathlib.Path(tmp)
    probe_bin = tmp_path / "layout-probe"
    subprocess.run(["rustc", str(sup / "layout-probe.rs"), "-o", str(probe_bin)], check=True)
    probe_out = subprocess.run([str(probe_bin)], capture_output=True, text=True, check=True).stdout.strip()
    print("layout-probe output:", probe_out)

    build_dir = tmp_path / "build"
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
