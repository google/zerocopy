# Coupled vs. Factored Operational Correspondence and Permission-Aware Cleanup for MiniRust `BasicMemory` (`d821c6e`)

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) specifies its concrete byte-storage substrate in `spec/mem/basic.md` (`BasicMemory`) as a coupled state in which each allocation record bundles spatial/lifecycle metadata (`address`, `size`, `align`, `kind`, `live`) together with its byte array (`data: List<AbstractByte<Provenance>>`) and per-allocation borrowing metadata (`extra`). Formal verification models, by contrast, frequently factor memory into separate allocation-metadata tables, byte-cell maps, and permission stores so that spatial framing and metadata-only pointer resolution can be reasoned about independently of byte contents.

This report documents a machine-checked Lean 4 (`v4.34.1`) investigation of coupled versus factored `BasicMemory` semantics and its composition with flat Tree Borrows permission tables (`spec/mem/tree_borrows/state_machine_unprotected.md`, `state_machine_protected.md`) and multi-phase cleanup execution. Across 15 primary Lean modules and 2 shared execution/simulation modules (17 modules and 223 kernel-checked `#print axioms` theorem audits in total, all re-verified on `2026-10-24`), the mechanized development establishes:

1. **Exact primitive and all-prefix operational correspondence** between the coupled reference transcription (`MiniRustReference`) and an independent metadata/cell-factored model (`MiniRustFactored`) across `allocateAt`/`Allocate`, `load`, `store`, `free`, `dereferenceable`, and `exit`, preserving all 12 distinct UB diagnostics, demonic allocator `noChoice` pruning, `unsupported` representation guards, and `ExitResult` leak detection (`memory_prefix_iff`, `memory_noUB_iff`, `encoded_noUB_iff`).
2. **Structural invariant preservation and diagnostic precedence** for `BasicMemory` on `x86_64` (`addressLimit = 2^64`, `sizeLimit = 2^63`), including fresh monotonic allocation IDs across deallocation and address reuse (`append_fresh`, `allocation_fresh_identity`), `sizeLimit` checks preceding demonic candidate filtering (`oversized_before_choice`), alignment checks preceding zero-length `check_ptr` bypass (`alignment_precedes_zero_length`), and exact six-stage `deallocate` error precedence (`wrong_free_order_control`, `remaining_free_error_order`).
3. **Spatial framing vs. same-byte multi-tag interference** in the unprotected Tree Borrows byte-permission table (`BorrowFrame`), together with exact coupled/factored correspondence when composed with permission-updating reads and multi-phase cleanup (`MemoryPermissions`, `PermissionCleanup`, `PermissionControls`, `MemoryPermissionInvariants`), including residual permission retention when raw `load` and permission transitions succeed before typed `u8` initialization decoding fails (`uninit_typed_read_retains_permissions`, `decode_preserves_residual`).

## Applicability

- **Upstream specification subject**: `minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`).
  - Primary files examined:
    - `spec/mem/interface.md` (5,530 bytes; SHA-256 `fd8d9bc949469dc9a3b4501ff3ab9063464b1bc0c9942c64694f3c959dd0f6e2`)
    - `spec/mem/basic.md` (10,275 bytes; SHA-256 `8bb62a21b6cd0050e8ac2b0c690be89ef1e7de4b779b18666a98b683b63a3763`)
    - `spec/mem/pointer.md` (2,078 bytes; SHA-256 `78ca53c4ba753257863718d3706ec60c4c3973e9e4c5328d736ed89983a1969a`)
    - `spec/prelude/target.md` (2,331 bytes; SHA-256 `9562a7fa482480e740b50e42f1ddfa2f6d6c3e2a794c4c1f742646670ed708e9`)
    - `spec/lang/step/intrinsics.md` (20,288 bytes; SHA-256 `261fe197e65556bae74cf209c64c5913fdd7c3f3a57d2bf56f0b1fb0e3a34be8`)
    - `spec/mem/tree_borrows/state_machine_unprotected.md` (4,507 bytes; SHA-256 `d21fa9d19e5c828416aa67fffe86137f54d1ffbe26dc42d282f704ff97a65668`)
    - `spec/mem/tree_borrows/state_machine_protected.md` (8,415 bytes; SHA-256 `770e0ebff4699c14284e699b6a48eb5a80147f6965056ca9000f74a353baaf98`)
- **Mechanized verification subject**: Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), using only Lean's standard kernel axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorry` or user-declared `axiom` declarations.
- **Target parameters fixed in the transcription**: `x86_64` target constants from `spec/prelude/target.md:50-66` (`PTR_SIZE = 8`, `PTR_ALIGN = 8`, `MAX_ADDR = 2^64`, `MAX_ALLOC_SIZE = 2^63 - 1`, modeled via strict `< sizeLimit` with `sizeLimit = 2^63`).

## Findings

### 1. Upstream `BasicMemory` Coupled State and Operation Ordering (`spec/mem/basic.md`)

**Basis**: `source`

In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `BasicMemory<T: Target>` (`spec/mem/basic.md:62-90`) stores a monotonic list `allocations: List<Allocation>` where allocation IDs (`AllocId(usize)`) index directly into the list and are never reused after deallocation. Each `Allocation` record couples:

- `address: Address` (`Int`),
- `data: List<AbstractByte<Option<Provenance>>>`, whose length defines the allocation size (`Allocation::size` at `spec/mem/basic.md:83-85`),
- `align: Align`,
- `kind: AllocationKind` (`Stack`, `Heap`, `Global`, `Function`, `VTable`),
- `live: bool`, and
- `extra: T::AllocExtra`.

Inspection of `spec/mem/basic.md` and `spec/lang/step/intrinsics.md` establishes the exact check ordering for every primitive memory operation:

1. **Allocation (`allocate`, `spec/mem/basic.md:92-141`)**:
   - First checks `if !T::valid_size(size) { throw_ub!(" asking for a too large allocation"); }` (`basic.md:100-102`), where `Target::valid_size` (`spec/prelude/target.md:27-29,57`) requires `size <= 2^63 - 1` on `x86_64`.
   - Next performs demonic address selection via `pick(0..T::MAX_ADDR, |addr: Address| { ... })` (`basic.md:116-127`), requiring strictly positive base address (`addr > 0`, i.e., `addr >= align.bytes()`), alignment (`addr % align.bytes() == 0`), in-bounds end (`addr + size < T::MAX_ADDR`), and pairwise non-overlap with every currently `live` allocation (`!alloc.overlaps(addr, size)` where `overlaps` at `basic.md:87-89` explicitly rejects equal bases `self.address == other_addr` even when `size == 0`).
   - Appends the new `Allocation` initialized to ` &[AbstractByte::Uninit; size]` at ID `AllocId(self.allocations.len())`.
2. **Pointer span validation (`check_ptr`, `spec/mem/basic.md:197-224`)**:
   - Immediately returns `ret(None)` when `len == 0` (`basic.md:201-203`), bypassing provenance, liveness, and bounds checks.
   - For `len > 0`, checks in order: provenance presence (`basic.md:204-206`), liveness (`if !alloc.live`, `basic.md:209-211`), and in-bounds range (`ptr.addr >= alloc.address` and `offset + len <= alloc.size()`, `basic.md:215-217`).
3. **Aligned `load` and `store` (`spec/mem/basic.md:227-274,329-335`)**:
   - Both `load` and `store` check `if ! align.is_aligned(ptr.addr)` (`basic.md:232-234,258-260`) **before** calling `self.check_ptr(ptr, len)`. Consequently, a zero-length `load` or `store` on a misaligned address triggers UB (`misalignedLoad` / `misalignedStore`), whereas an aligned zero-length `load` or `store` succeeds even on a provenance-free (`None`), dead, or out-of-bounds pointer.
   - By contrast, `dereferenceable` (`basic.md:337-339`) delegates directly to `check_ptr(ptr, len)` without an alignment check.
4. **Deallocation (`deallocate`, `spec/mem/basic.md:144-184,325-327`)**:
   - Validates six conditions in strict sequential order: (1) provenance present (`freeNoProvenance`), (2) `alloc.live` is true (`doubleFree`), (3) `ptr.addr == alloc.address` (`freeNotBase`), (4) `alloc.kind == kind` (`freeKind`), (5) `alloc.size() == size` (`freeSize`), and (6) `alloc.align == align` (`freeAlign`). Upon success, sets `alloc.live = false` while retaining the record at its `AllocId` index.
5. **Leak check on machine termination (`leak_check`, `spec/mem/basic.md:278-296`; `exit` intrinsic, `spec/lang/step/intrinsics.md:85-100`)**:
   - Scans `self.allocations` for any allocation with `alloc.live && alloc.kind == AllocationKind::Heap`. If found, `leak_check` throws `MachineStop::MemoryLeak` (a distinct termination tag in `TerminationInfo`, not `TerminationInfo::Ub`).

### 2. Coupled vs. Factored `BasicMemory` Correspondence (`MiniRustReference`, `MiniRustFactored`, `MemoryExecution`)

**Basis**: `execution` and `derived`

In [`support/MiniRustReference.lean`](support/MiniRustReference.lean) and [`support/MiniRustFactored.lean`](support/MiniRustFactored.lean), the coupled and factored representations of `BasicMemory` are defined independently and connected by explicit abstraction and encoding maps:

- **Coupled state (`MiniRustReference.State`, `MiniRustReference.lean:46-48`)**:
  `next : Nat` and `allocations : Nat → Option Allocation`, where each `Allocation` (`MiniRustReference.lean:38-44`) bundles `base`, `size`, `align`, `kind`, `live`, and `data : Nat → Byte`.
- **Factored state (`MiniRustFactored.State`, `MiniRustFactored.lean:27-30`)**:
  `next : Nat`, `metadata : Nat → Option Metadata` (holding only `base`, `size`, `align`, `kind`, `live`), and a separate two-dimensional cell array `cells : Nat → Nat → Byte`. Pointer validation (`MiniRustFactored.resolve`, `MiniRustFactored.lean:114-128`) inspects only `state.metadata` without reading `state.cells`.
- **Abstraction (`reify`) and encoding (`encode`) (`MiniRustFactored.lean:64-100`)**:
  `reify : MiniRustFactored.State → MiniRustReference.State` materializes each `Metadata` entry with its slice `state.cells id`, and `encode : MiniRustReference.State → MiniRustFactored.State` splits coupled records into `metadata` and `cells`. Theorem `reify_encode` (`MiniRustFactored.lean:92-100`) proves `reify (encode s) = s` unconditionally (without requiring well-formedness).

Across every primitive operation and result tag (`Result.ok`, `Result.ub`, `Result.noChoice`, `Result.unsupported`), the factored kernel commutes judgmentally and propositionally with `reify`:

| Operation / Property | Lean Theorem | Location | Result |
| :--- | :--- | :--- | :--- |
| Left inverse of `encode` | `MiniRustFactored.reify_encode` | [`MiniRustFactored.lean:92-100`](support/MiniRustFactored.lean#L92-L100) | `reify (encode state) = state` |
| Span resolution | `MiniRustFactored.resolve_reify` | [`MiniRustFactored.lean:244-259`](support/MiniRustFactored.lean#L244-L259) | `checkPtr (reify s) p len = resultMap (Option.map (reifySpan s)) (resolve s p len)` |
| Aligned byte load | `MiniRustFactored.load_reify` | [`MiniRustFactored.lean:320-334`](support/MiniRustFactored.lean#L320-L334) | `load (reify s) p len align = resultMap (Prod.map id reify) (load s p len align)` |
| Aligned byte store | `MiniRustFactored.store_reify` | [`MiniRustFactored.lean:336-355`](support/MiniRustFactored.lean#L336-L355) | `store (reify s) p bytes align = resultMap reify (store s p bytes align)` |
| Deallocation | `MiniRustFactored.free_reify` | [`MiniRustFactored.lean:357-367`](support/MiniRustFactored.lean#L357-L367) | `free (reify s) p kind size align = resultMap reify (free s p kind size align)` |
| Candidate-indexed allocation | `MiniRustFactored.allocateAt_reify` | [`MiniRustFactored.lean:382-387`](support/MiniRustFactored.lean#L382-L387) | `allocateAt (reify s) kind size align addr = resultMap (Prod.map id reify) (allocateAt s kind size align addr)` |
| Relational allocation forward & backward | `MiniRustFactored.Allocate_reify`, `Allocate_coverage` | [`MiniRustFactored.lean:427-447`](support/MiniRustFactored.lean#L427-L447) | Exact bijection of non-`noChoice` allocation branches across `reify` |
| Dereferenceability query | `MiniRustFactored.dereferenceable_reify` | [`MiniRustFactored.lean:389-398`](support/MiniRustFactored.lean#L389-L398) | `dereferenceable (reify s) p len = dereferenceable s p len` |
| Exit / leak check | `MiniRustFactored.exit_reify` | [`MiniRustFactored.lean:400-421`](support/MiniRustFactored.lean#L400-L421) | `MiniRustReference.exit (reify s) = exit s` |

In [`support/MemoryExecution.lean`](support/MemoryExecution.lean), these primitive commutation equations are lifted to a reactive client execution machine (`Plan` with `.done`, `.spin`, and `.call op continuation`, stepped over all demonic allocator candidates `candidate : Nat`, where `.noChoice` yields `none` so invalid allocator addresses produce no transition edge):

- **Single-step simulation (`execute_reify`, `next_commutes`, `map_step`, `lift_step`, `source_simulation`, `target_simulation`)** ([`MemoryExecution.lean:68-199`](support/MemoryExecution.lean#L68-L199)): Forward and backward stuttering-free simulations between `SourceStep` (coupled) and `TargetStep` (factored).
- **All-prefix reachable state correspondence (`memory_prefix_iff`)** ([`MemoryExecution.lean:230-233`](support/MemoryExecution.lean#L230-L233)):
  $$\mathrm{Reach}\;\mathrm{SourceStep}\;(\mathrm{mapCfg}\;\mathrm{reify}\;t)\;s \iff \exists t',\; \mathrm{Reach}\;\mathrm{TargetStep}\;t\;t' \wedge \mathrm{mapCfg}\;\mathrm{reify}\;t' = s$$
- **All-prefix safety equivalence (`memory_noUB_iff`, `encoded_noUB_iff`)** ([`MemoryExecution.lean:235-245`](support/MemoryExecution.lean#L235-L245)):
  $$\mathrm{NoUB}\;\mathrm{SourceStep}\;\mathrm{Bad}\;(\mathrm{mapCfg}\;\mathrm{reify}\;t) \iff \mathrm{NoUB}\;\mathrm{TargetStep}\;\mathrm{Bad}\;t$$
  and for any coupled configuration $s$, $\mathrm{NoUB}\;\mathrm{SourceStep}\;\mathrm{Bad}\;s \iff \mathrm{NoUB}\;\mathrm{TargetStep}\;\mathrm{Bad}\;(\mathrm{mapCfg}\;\mathrm{encode}\;s)$.
- **Separation of `NoUB` from `AllowedStop` and allocator exhaustion (`empty_choice_safe_without_progress`)** ([`MemoryExecution.lean:249-290`](support/MemoryExecution.lean#L249-L290)): When every candidate address returns `.noChoice` (e.g., an alignment request $\ge 2^{64}$ that passes the size check `size < 2^63` but has no valid address below `addressLimit = 2^64`), `NoUB` holds vacuously because no transition is enabled, while `ReachableProgress` to `AllowedStop` is refuted.

### 3. Structural Invariants, Non-Vacuity Witnesses, and Boundary Controls (`ReferenceInvariants`, `MemoryInvariants`, `MemoryExamples`, `MemoryBoundaryControls`, `MemoryWitnesses`)

**Basis**: `execution` and `derived`

- **Structural well-formedness preservation (`ReferenceInvariants`, `MemoryInvariants`)**:
  `StateWF` ([`MiniRustReference.lean:113-126`](support/MiniRustReference.lean#L113-L126)) and `TargetWF` ([`MemoryInvariants.lean:18-32`](support/MemoryInvariants.lean#L18-L32)) require: (1) exact allocation domain `id < next`, (2) positive aligned base addresses with `size < sizeLimit` and `base + size < addressLimit`, (3) all initialized pointer fragments referencing minted IDs `< next`, and (4) pairwise non-overlap of live allocations. Both models preserve well-formedness across `empty`, `allocateAt`, `store`, and `free` (`emptyStateWF`, `allocateAt_preserves_StateWF`, `store_preserves_StateWF`, `free_preserves_StateWF` in [`ReferenceInvariants.lean:45-261`](support/ReferenceInvariants.lean#L45-L261); `encode_targetWF`, `target_allocateAt_preserves_WF`, `target_store_preserves_WF`, `target_free_preserves_WF` in [`MemoryInvariants.lean:47-166`](support/MemoryInvariants.lean#L47-L166)), and guarantee that well-formed pointers (`PtrWF`) and positive power-of-two alignments (`AlignWF`) never return `.unsupported` (`checkPtr_not_unsupported`, `load_not_unsupported`, `store_not_unsupported`, `free_not_unsupported`).
- **Non-vacuity reachability witnesses (`MemoryExamples`, `MemoryWitnesses`)**:
  Because `NoUB` quantifies universally over all demonic allocator choices, [`MemoryWitnesses.lean`](support/MemoryWitnesses.lean) proves existential reachability at concrete candidate address `1` across multi-round `allocate` -> `store` -> `load` -> `free` loops (`one_round_reach`, `rounds_reach`, `sequence_reach`, `empty_sequence_reach_spin`, `empty_sequence_reach_exit`), while [`MemoryExamples.lean`](support/MemoryExamples.lean) proves `NoUB` across all demonic allocator choices for the same programs (`rounds_safe`, `sequenceRounds_safe`, `sequence_plain_blocks_safe`, `repeated_plain_blocks_spin`, `repeated_plain_blocks_exit`) and exhibits concrete address reuse with fresh allocation IDs (`actual_reuse_chain`, [`MemoryExamples.lean:248-262`](support/MemoryExamples.lean#L248-L262)).
- **Boundary and mutation controls (`MemoryBoundaryControls`, `MemoryExamples`)**:
  - `impossible_alignment_admitted`, `impossible_alignment_no_choice`, and `actual_empty_choice_no_progress` ([`MemoryBoundaryControls.lean:28-55`](support/MemoryBoundaryControls.lean#L28-L55)) prove that `align = 2^64` satisfies `AlignWF` (`2^64` is a power of two) and `size = 1 < sizeLimit`, yet `allocateAt` returns `.noChoice` for every `addr : Nat`, yielding a stuck state that is `NoUB` but not `Verified`.
  - `oversized_before_choice` ([`MemoryBoundaryControls.lean:57-62`](support/MemoryBoundaryControls.lean#L57-L62)) proves that when `size = sizeLimit` and `align = 2^64`, `allocateAt` returns `.ub .allocationTooLarge` rather than `.noChoice` because `BasicMemory::allocate` checks `valid_size` before candidate selection.
  - `stale_identity_mutation_control` ([`MemoryExamples.lean:264-275`](support/MemoryExamples.lean#L264-L275)) shows that after freeing allocation `0` at address `16` and reallocating allocation `1` at the same address `16`, accessing address `16` with stale provenance `some 0` triggers `.ub .dead` while provenance `some 1` succeeds.
  - `mutated_bad_then_spin_safe` and `mutation_invalidates_safety_transfer` ([`MemoryBoundaryControls.lean:88-115`](support/MemoryBoundaryControls.lean#L88-L115)) show that if a semantics erroneously discards a bad finite prefix before an infinite `.spin` continuation, an unsafe program (`bad_prefix_before_spin`) is misclassified as safe.

### 4. Flat Permission Tables, Spatial Framing, and Permission-Aware Cleanup (`BorrowFrame`, `MemoryPermissions`, `PermissionCleanup`, `PermissionControls`, `MemoryPermissionInvariants`)

**Basis**: `source`, `execution`, and `derived`

- **Unprotected byte-permission table and spatial vs. same-byte framing (`BorrowFrame.lean`)**:
  [`support/BorrowFrame.lean`](support/BorrowFrame.lean) transcribes the six-state unprotected permission lattice (`Cell`, `Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled`) from `spec/mem/tree_borrows/state_machine_unprotected.md` and the protected-to-unprotected conversion `unprotect` from `spec/mem/tree_borrows/state_machine_protected.md:94-112`.
  - Because an access at `byte : Byte` (`alloc`, `offset`) applies `localTransition` to `a.tag` and `foreignTransition` to every other tag at the same `(alloc, offset)` (`BorrowFrame.update`, `BorrowFrame.lean:86-91`), assertions supported on a byte footprint disjoint from `a.byte` frame unconditionally (`perform_spatial_frame`, `frame_triple`, [`BorrowFrame.lean:111-147`](support/BorrowFrame.lean#L111-L147)).
  - At the **same** `(alloc, offset)`, distinct tags do **not** frame unless the foreign tag's permission is invariant under `foreignTransition` (`same_byte_frame_of_stability`, `Cell_stable`, `Reserved_stable_under_read`, [`BorrowFrame.lean:152-161`](support/BorrowFrame.lean#L152-L161)). Theorem `TagCounterexample.disjoint_tags_do_not_frame` ([`BorrowFrame.lean:230-240`](support/BorrowFrame.lean#L230-L240)) exhibits a concrete counterexample: reading through tag `0` (`Cell`) at byte `⟨0, 0⟩` transitions sibling tag `1` on the same byte from `Unique` to `Frozen`, causing a subsequent write through tag `1` to fault with `.localWriteFrozen`.
  - Theorems `protector_end_unique_implicit_write`, `protector_end_frozen_read_implicit_read`, and `protector_end_is_not_pure_erase` ([`BorrowFrame.lean:262-270`](support/BorrowFrame.lean#L262-L270)) confirm that `unprotect` in `state_machine_protected.md` is not a pure flag erasure: releasing a protected `Unique` permission emits an implicit write (`some .write`), and releasing a protected `Frozen` or `Reserved` permission with `had_local_read = true` emits an implicit read (`some .read`).
- **Coupled/factored correspondence under permission-updating reads and cleanup (`MemoryPermissions.lean`, `PermissionCleanup.lean`)**:
  [`support/MemoryPermissions.lean`](support/MemoryPermissions.lean) composes both `MiniRustReference` and `MiniRustFactored` with the `BorrowFrame` permission store (`CoupledMemory` and `FactoredMemory`, connected by `reify` and `encode` with `reify_encode` at [`MemoryPermissions.lean:62-64`](support/MemoryPermissions.lean#L62-L64)).
  - A typed 1-byte read (`coupledRead` / `factoredRead`, [`MemoryPermissions.lean:105-146`](support/MemoryPermissions.lean#L105-L146)) executes: (1) raw `load` (checking alignment, provenance, liveness, and bounds), (2) `BorrowFrame.perform` at the resolved `(id, offset)` key, and (3) `decodeInitialized` to extract an initialized `u8` (accepting pointer-fragment provenance on integer bytes, matching `spec/lang/values.md`).
  - Crucially, if steps (1) and (2) succeed but step (3) fails because the byte is `.uninit`, the updated permission store is **retained** in the `.ub (.permission .uninitializedRead)` residual state (`uninit_typed_read_retains_permissions`, `uninit_later_write_fails`, [`MemoryPermissions.lean:365-384`](support/MemoryPermissions.lean#L365-L384); `decode_preserves_residual`, [`MemoryPermissionInvariants.lean:94-103`](support/MemoryPermissionInvariants.lean#L94-L103)).
  - [`support/PermissionCleanup.lean`](support/PermissionCleanup.lean) embeds `CoupledMemory` and `FactoredMemory` into an explicit six-phase cleanup machine (`body` -> `testCleanup` -> `consumeObligation` -> `invokeHandler` -> `handlerRead` -> `handlerWrite` -> `finish`, with normal vs. unwind completion and step-cost/event accounting) and proves exact all-prefix and `NoUB` correspondence (`cleanup_prefix_iff`, `cleanup_noUB_iff`, `encoded_cleanup_prefix_iff`, `encoded_cleanup_noUB_iff`, [`PermissionCleanup.lean:265-293`](support/PermissionCleanup.lean#L265-L293)).
  - [`support/PermissionControls.lean`](support/PermissionControls.lean) proves that when body and cleanup access disjoint byte offsets (`DisjointCleanup`), freezing byte `0` during the body leaves byte `1`'s `Unique` permission intact so cleanup succeeds (`DisjointCleanup.cleanup_safe`, [`PermissionControls.lean:160-191`](support/PermissionControls.lean#L160-L191)), whereas a mutated semantics that discards read-induced permission updates (`ReadMutation`) falsely classifies an aliasing cleanup fault as safe (`ReadMutation.mutation_invalidates_cleanup_safety`, [`PermissionControls.lean:297-305`](support/PermissionControls.lean#L297-L305)).

## Boundaries

- **Known not to apply**:
  - Unconditional same-byte tag framing does not hold in MiniRust's unprotected permission table (`TagCounterexample.disjoint_tags_do_not_frame` in [`BorrowFrame.lean:230-236`](support/BorrowFrame.lean#L230-L236)).
  - `StateWF` / `MemoryWF` structural admission does not imply `NoUB`: structurally well-formed memories and pointers can still fault at runtime on aliasing violations (`admitted_aliasing_cleanup_is_unsafe`), uninitialized typed reads (`admitted_uninitialized_cleanup_is_unsafe`), or out-of-bounds accesses (`onePast_admitted_but_access_fails`).
- **Not examined in this package**:
  - Recursive tree-topology traversal, ancestor/child relationship resolution, two-stage protector release across trees, and `GcCow` copy-on-write heap semantics in `spec/mem/tree_borrows/tree.md` and `memory.md` are not modeled in `BorrowFrame` or `MemoryPermissions`; those are examined in the companion Tree Borrows report (`minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence`).
  - Integer-to-pointer cast prediction (`expose` / `predict` in `spec/mem/intptrcast.md`) is not part of `BasicMemory` and is examined in `minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses`.
- **Unsupported / out-of-contract representations**:
  - Non-power-of-two or zero alignments (`align = 0`), negative source addresses, or forged allocation IDs (`id >= next`) are classified as `.unsupported` rather than `.ok` or `.ub`, and are proven unreachable from `StateWF` / `PtrWF` / `AlignWF` inputs (`ReferenceInvariants`, `MemoryInvariants`).
- **Unknown**:
  - Whether normative upstream Rust (`rustc` / Lang Team operational semantics) will adopt `BasicMemory`'s exact diagnostic ordering (such as checking alignment before zero-length `load`/`store` bypass) as normative Rust specification.

## Evidence

All 17 Lean modules (the 15 R04 target modules plus their 2 direct dependencies `Execution.lean` and `PrefixTransfer.lean`) and the fresh execution ledger are archived in [`support/`](support/):

- Execution ledger: [`support/lean-verification-results.json`](support/lean-verification-results.json) (recorded `2026-10-24` on `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`).
- Note on Lean memory flag across host architectures: On `arm64-apple-darwin`, all 17 modules elaborate within `-j1 -M768` (peak RSS 675–723 MiB). On `x86_64-unknown-linux-gnu`, `import Std` has a slightly larger managed-heap footprint (~798–826 MiB RSS), so modules that import `Std` use `-j1 -M1024` while `Std`-free modules pass under `-j1 -M768`. Both produce identical kernel-checked theorem audits using only `{propext, Quot.sound, Classical.choice}`.

| Module | Support File | Source SHA-256 | Flags (`x86_64-linux`) | Wall (s) | Audited Theorems |
| :--- | :--- | :--- | :--- | ---: | ---: |
| `AnnealResearch.Memory` | [`support/Memory.lean`](support/Memory.lean) | `5617d5cfc0716b5c666c6ea0784a311ff8a8252f1b8114d5c927e67493a29db9` | `-j1 -M1024` | 1.5135 | 28 |
| `AnnealResearch.ByteMemory` | [`support/ByteMemory.lean`](support/ByteMemory.lean) | `71c8d31550da7412a1dfead2e2d64d81b18b527933acde46d81e1ad2de9ec3c0` | `-j1 -M1024` | 0.8406 | 7 |
| `AnnealResearch.MiniRustReference` | [`support/MiniRustReference.lean`](support/MiniRustReference.lean) | `f2974b04a15b378f930719a0ad8943e3313abccbabf108b6ad0d24a0478fc778` | `-j1 -M1024` | 0.8719 | 6 |
| `AnnealResearch.ReferenceInvariants` | [`support/ReferenceInvariants.lean`](support/ReferenceInvariants.lean) | `18e7d810df82fe6620fc32bd6a69ad2b9b71b768c1d1baaeeba78086169741ec` | `-j1 -M1024` | 1.2089 | 9 |
| `AnnealResearch.MiniRustFactored` | [`support/MiniRustFactored.lean`](support/MiniRustFactored.lean) | `92eca7fe012cdc43849ab09737fce72c7bbd627ff1776184170af48c2f810c98` | `-j1 -M1024` | 1.1146 | 10 |
| `AnnealResearch.MemoryInvariants` | [`support/MemoryInvariants.lean`](support/MemoryInvariants.lean) | `4da8e16c81e9b786eea9df29e436cd9b2e7459e5937d461af3f55ffe626b8225` | `-j1 -M768` | 0.4055 | 10 |
| `AnnealResearch.Execution` | [`support/Execution.lean`](support/Execution.lean) | `cbe3713b840a8a61b617f2ababaa02e4ad97c81628db7d55fc3641611365bf3a` | `-j1 -M768` | 0.5801 | 16 |
| `AnnealResearch.PrefixTransfer` | [`support/PrefixTransfer.lean`](support/PrefixTransfer.lean) | `764328f9a7dcc13a32ab86f3bdfd3f23194ec95f5982621b21a519b643b360f9` | `-j1 -M768` | 0.4874 | 12 |
| `AnnealResearch.MemoryExecution` | [`support/MemoryExecution.lean`](support/MemoryExecution.lean) | `0caa2ac61c36ab17aa1ce7a7279358830c6f0b1c6acdacb4021908364db2f4e2` | `-j1 -M1024` | 1.0859 | 7 |
| `AnnealResearch.MemoryExamples` | [`support/MemoryExamples.lean`](support/MemoryExamples.lean) | `b2c5057431b808313da5c4d782d7761f506f2411959b42054bc0c41e05f0f1f6` | `-j1 -M1024` | 0.9343 | 15 |
| `AnnealResearch.MemoryBoundaryControls` | [`support/MemoryBoundaryControls.lean`](support/MemoryBoundaryControls.lean) | `9ce36a593859154616f5178fbe38e1e522451f522670b8aae2e229d11296776c` | `-j1 -M768` | 0.4849 | 9 |
| `AnnealResearch.MemoryWitnesses` | [`support/MemoryWitnesses.lean`](support/MemoryWitnesses.lean) | `abd6ab79cece08918c06a9fb3f67c919de0372360b61f26ac0b003537836f1fa` | `-j1 -M1024` | 1.0633 | 12 |
| `AnnealResearch.BorrowFrame` | [`support/BorrowFrame.lean`](support/BorrowFrame.lean) | `d30344a69080a615ac84f7ee3dedc101cb958d8f8e16360da8fc2b3c66d62c9e` | `-j1 -M1024` | 0.7172 | 9 |
| `AnnealResearch.MemoryPermissions` | [`support/MemoryPermissions.lean`](support/MemoryPermissions.lean) | `7c0f2822838ac922f97cacc15f3b9584c3d3d06520f8a62f3789d455dfb17777` | `-j1 -M1024` | 1.1206 | 25 |
| `AnnealResearch.PermissionCleanup` | [`support/PermissionCleanup.lean`](support/PermissionCleanup.lean) | `dec79e5020cad153fb38a9c94ba08a437d184b2beda656cd5e297943c53d0621` | `-j1 -M1024` | 3.0638 | 25 |
| `AnnealResearch.PermissionControls` | [`support/PermissionControls.lean`](support/PermissionControls.lean) | `e376b60169beeb7d0a93b17ea8729e14e7d73ca3c37e2b1dea660616a6cabf6a` | `-j1 -M1024` | 0.6723 | 28 |
| `AnnealResearch.MemoryPermissionInvariants` | [`support/MemoryPermissionInvariants.lean`](support/MemoryPermissionInvariants.lean) | `633d5b9a0e99f7e52810de8ea3eb435b0c280f333489f2418adfd8b1ab818243` | `-j1 -M1024` | 0.6081 | 14 |

## Revalidation

To re-check all 17 Lean modules from the self-contained [`support/`](support/) directory using Lean `v4.34.1`:

```bash
python3 - <<'EOF'
import os, subprocess, tempfile

support_dir = "reports/minirust-d821c6e-basic-memory-factored-correspondence/support"
order = [
    "Memory", "ByteMemory", "MiniRustReference", "ReferenceInvariants",
    "MiniRustFactored", "MemoryInvariants", "Execution", "PrefixTransfer",
    "MemoryExecution", "MemoryExamples", "MemoryBoundaryControls",
    "MemoryWitnesses", "BorrowFrame", "MemoryPermissions",
    "PermissionCleanup", "PermissionControls", "MemoryPermissionInvariants",
]

with tempfile.TemporaryDirectory() as tmp:
    mod_dir = os.path.join(tmp, "AnnealResearch")
    os.makedirs(mod_dir, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = tmp
    for mod in order:
        src = os.path.join(support_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", "-M1024", "-o", olean, src], env=env, check=True)
        print(f"OK: AnnealResearch.{mod}")
EOF
```

Revalidate this report when:
- Updating the pinned `minirust/minirust` commit beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (especially if `spec/mem/basic.md`, `spec/mem/interface.md`, or `spec/mem/tree_borrows/state_machine_*.md` changes), or
- Upgrading the Lean 4 toolchain beyond `v4.34.1`.
