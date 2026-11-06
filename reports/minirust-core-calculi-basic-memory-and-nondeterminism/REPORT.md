# MiniRust Core Semantics, Factored `BasicMemory` Correspondence, Demonic/Angelic Nondeterminism, and Weak-Memory Boundaries

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, paired with `minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`) specifies an operational language parameterized by a pluggable `Memory` interface (`spec/mem/interface.md`), concrete byte and provenance representations (`spec/mem/pointer.md`, `spec/lang/representation.md`), mixed demonic and angelic nondeterminism (`pick` and `predict` in `libspecr/src/nondet.rs` and `spec/mem/intptrcast.md`), and a sequentially consistent concurrent race detector (`ConcurrentMemory<M>` in `spec/mem/concurrent.md`). Choosing MiniRust as a verification target does not fix a single safety semantics without also fixing its memory instance (`BasicMemory` vs. `TreeBorrowsMemory`), target configuration (`Target`), and interpretation of demonic versus angelic choices.

This report synthesizes four complementary investigations—source comparisons against foundational Rust core calculi and weak-memory separation logics, two mechanized Lean 4 (`4.34.1`) developments (21 modules and 268 kernel-checked `#print axioms` theorem audits), and two exhaustive finite-state Python probes—into a unified reference:

1. **Core Calculi vs. MiniRust Memory Interfaces:** MiniRust parameterizes `ThinPointer<Provenance>`, `Pointer<Provenance>`, and `AbstractByte<Provenance>` (`Uninit` vs. `Init(u8, Option<Provenance>)`) over the memory implementation (`BasicMemory` vs. `TreeBorrowsMemory`). Older Rust core calculi ($\lambda_{\text{Rust}}$ / RustBelt POPL 2018, Oxide, Featherweight Rust, Rust Distilled, and KRust) establish type, borrow, or capability soundness for custom surface or CPS calculi that omit byte-level pointer fragments, Tree Borrows aliasing transitions, or relaxed-memory concurrency; reusing their lemmas for MiniRust requires an explicit operational simulation preserving their subject premises.
2. **Coupled vs. Factored `BasicMemory` Correspondence and Permission-Aware Cleanup:** Across 17 Lean 4 modules (223 audited theorems), MiniRust's coupled `BasicMemory` representation (`MiniRustReference`, bundling spatial metadata and byte arrays in each `Allocation` record) is proved operationally equivalent across all finite prefixes and `NoUB` judgments (`memory_prefix_iff`, `memory_noUB_iff`, `encoded_noUB_iff`) to a verification-oriented factored model (`MiniRustFactored`, separating allocation metadata from a two-dimensional byte-cell store). The mechanization also establishes exact diagnostic precedence on `x86_64` (size validation before demonic address choice, alignment validation before zero-length `check_ptr` bypass, and six-stage `deallocate` error ordering) and composes both models with the six-state unprotected Tree Borrows permission table (`BorrowFrame`, `MemoryPermissions`, `PermissionCleanup`), proving spatial framing across disjoint byte offsets, refuting unconditional same-byte multi-tag framing (`disjoint_tags_do_not_frame`), and proving residual permission retention when a typed `u8` read faults on `Uninit` after raw load and permission updates succeed (`uninit_typed_read_retains_permissions`).
3. **Demonic/Angelic Nondeterminism (`pick`/`predict`) and Finite-Choice Strategy Extraction:** In `minirust/specr` (`15200eb5e676e2ee91f43bd79e674f8fc32e5348`), runtime `pick` samples at most 50 random candidates before panicking and `predict` unconditionally panics with `unimplemented!()`. Across the entire MiniRust specification (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`), `predict` is called only in `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md:45-53`), where the suitability predicate restricts eligible answers after $n$ prior `expose` transitions to a finite set $\text{None} \cup \{\text{Some}(p) \mid p \in \text{self.exposed}\}$ of size at most $n + 1$. Across 4 Lean 4 modules (45 audited theorems), unbounded angelic branching is proved to break $\omega$-continuity (`finite_approximants_do_not_establish_greatestSafety`), whereas per-state finite legal action lists (`legalActions : State -> List Action`) make the $\omega$-intersection of finite-horizon safety approximants postfixed (`winning_postfixed`, `winning_unfold`) and suffice to extract a single prefix-coherent causal strategy satisfying both `NoUB` and `ReachableProgress` (`winning_iff_classified_strategy`). An exhaustive Python probe (`witness_probe.py`) confirms invariant preservation across 11,310 positive byte-copy configurations (161,776 primitive events) and separates history-free from alias-sensitive copy models.
4. **Concurrent Race Detection, Alias Events, and Weak-Memory Composition Boundaries:** `ConcurrentMemory<M>` (`spec/mem/concurrent.md`) records `Access { type, atomicity, addr, len }` on loads and stores and compares each machine step only against the immediately preceding step (`spec/lang/machine.md`). An exhaustive 6,400-pair overlap probe (`probe.py`) finds 198 empty-interval disagreements between MiniRust's interval inequality `a + n > b && b + m > a` and byte-set intersection (for example, a zero-byte read at address `2` conflicts with a write to `[1, 3)`). Furthermore, MiniRust delegates Tree Borrows retag and protector-end hooks through `M` without recording race accesses, whereas Miri (`0e1a23b0794bec7860df8c06a774f4316746795a`) reports nonempty retag implicit accesses to its data-race detector. Weak-memory separation logics (RustBelt Meets Relaxed Memory POPL 2020 and the 2024 GPFSL-derived Rocq development `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`) provide view-indexed adequacy (`noprol_adequacy`) over value-cell ORC11/iRC11 machines without SC atomics, byte fragments, or Tree Borrows states.

## Applicability

This report applies to the following pinned upstream revisions, specifications, and verification environments:

- **MiniRust specification and `minimize` tooling (`minirust/minirust`):** Commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (committed `2026-07-27`; source archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`; `rust-toolchain` requests `nightly`). Primary specification files examined:
  - `spec/mem/interface.md` (5,530 bytes; SHA-256 `fd8d9bc949469dc9a3b4501ff3ab9063464b1bc0c9942c64694f3c959dd0f6e2`)
  - `spec/mem/basic.md` (10,275 bytes; SHA-256 `8bb62a21b6cd0050e8ac2b0c690be89ef1e7de4b779b18666a98b683b63a3763`)
  - `spec/mem/pointer.md` (2,078 bytes; SHA-256 `78ca53c4ba753257863718d3706ec60c4c3973e9e4c5328d736ed89983a1969a`)
  - `spec/mem/intptrcast.md` (1,838 bytes; SHA-256 `ddb67b4ef74e05568fced9f1460730b595b4584d73d48c93fd326ff5dd7378b6`)
  - `spec/mem/concurrent.md` and `spec/mem/tree_borrows/{memory.md,reborrow_settings.md,state_machine_unprotected.md,state_machine_protected.md}`
  - `spec/prelude/target.md` (2,331 bytes; SHA-256 `9562a7fa482480e740b50e740b50e42f1ddfa2f6d6c3e2a794c4c1f742646670ed708e9`), `spec/lang/machine.md` (14,940 bytes; SHA-256 `121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c`), `spec/lang/representation.md`, and `spec/lang/step/intrinsics.md` (20,288 bytes; SHA-256 `261fe197e65556bae74cf209c64c5913fdd7c3f3a57d2bf56f0b1fb0e3a34be8`).
- **Specr transpiler and runtime (`minirust/specr`):** Git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (source archive SHA-256 `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`) and published crates.io `libspecr 0.1.41` (crate archive SHA-256 `a3c0c46f39513f6c4b533ec6bea7d623f6761fd0a610b1152db7f2e4dd385a61`), specifically `libspecr/src/nondet.rs` and `libspecr/src/set/{mod.rs,func.rs,iter.rs}`.
- **Miri and Rust standard library comparisons:**
  - `rust-lang/miri` at commit `0e1a23b0794bec7860df8c06a774f4316746795a` (`src/borrow_tracker/tree_borrows/mod.rs` retag data-race reporting comparison).
  - `rust-lang/rust` at commit `d8ef4f3fe7031514cbd7d056b7b058814987ecec` (`library/core/src/sync/atomic.rs` C++20-derived atomic access contract).
- **Comparative Rust core calculi and weak-memory separation-logic subjects:**
  - $\lambda_{\text{Rust}}$ / RustBelt POPL 2018 paper (DOI `10.1145/3158154`, PACMPL 2 POPL Article 66) and technical appendix (`2017-11-09`, SHA-256 `a49b24dbb220d539aa5c70c6e09ea6ed48c8adb01568857ffc456bae0f7dfc83`).
  - Oxide (`arXiv:1903.00982v4`, `2021-10-19`, SHA-256 `23ccf574c9778c533c12125b8da96a033af72da3cd6bb75483b63745846b5555`).
  - Featherweight Rust author-hosted preprint (bibliographic DOI `10.1145/3443420`, footer date March 2020, SHA-256 `4968454d56869166ca39ef8a340e0758ebe13c35cb1bc9f18d25b6ee3e67c586`; distinguished from the published 2021 TOPLAS print edition).
  - Rust Distilled (`arXiv:1806.02693v2`, `2018-08-16`, SHA-256 `5009345fe0de38928c2a7c58970d05ab171e2768de3abafad6f8586141155bd3`).
  - KRust (`arXiv:1804.10806v1`, `2018-04-28`, SHA-256 `c101740fe8f8aa85537bc282ceef950de4d60bc3215fcd543bead8ba72e9dd24`).
  - RustBelt Meets Relaxed Memory (DOI `10.1145/3371102`, PACMPL 4 POPL Article 34, 2020) and the 2024 GPFSL-derived Rocq development `kaist-cp/relaxed-memory-separation-logic` at commit `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472` (`gpfsl/base_logic/adequacy.v`).
- **Mechanized and executable verification environments:**
  - Lean 4 `4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`, verified on `x86_64-unknown-linux-gnu` and compared against `arm64-apple-darwin` object hashes), using only standard kernel axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorry` or user-declared `axiom` declarations.
  - Python 3 execution of the finite-witness byte-copy probe (`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness_probe.py`) and concurrent overlap/litmus probe (`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py`).

## Findings

### 1. Memory Parameterization, Provenance Routes, and Core Calculi Boundaries

**Basis:** `source`, `documentation`, and `derived`

#### 1.1 Pluggable Memory Interfaces (`spec/mem/pointer.md`, `spec/mem/interface.md`, `spec/mem/basic.md`)

In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `ThinPointer<Provenance>` carries an integer `addr` and optional `provenance: Option<Provenance>`; wide `Pointer<Provenance>` adds `metadata`. The `Memory` trait (`spec/mem/interface.md`) supplies the `Provenance` type, `allocate`, `deallocate`, `load`, `store`, `dereferenceable`, `retag`, and `end_call` hooks. Notably, `Memory::load` takes `&mut self` because reads can mutate aliasing state (such as Tree Borrows permissions). Each stored byte is an `AbstractByte<Provenance>`, distinguishing `Uninit` from `Init(u8, Option<Provenance>)` where a provenance fragment also records its byte position within a pointer.

`BasicMemory` (`spec/mem/basic.md`) tracks allocation identity (`AllocId`), base address, byte array, alignment, `AllocationKind`, and `live: bool`, ignoring aliasing rules. `TreeBorrowsMemory` (`spec/mem/tree_borrows/memory.md`) refines `Provenance` with a borrow-tree node path and updates per-byte permissions on reads, writes, retags, and function-exit protector releases. Consequently, safety under `BasicMemory` does not establish safety under `TreeBorrowsMemory`. Although `README.md` contains an outdated introductory sentence stating that no memory implementation is given, it links both `BasicMemory` and `TreeBorrowsMemory`; the executable specification files govern.

#### 1.2 Representation Transmutation vs. Integer-Pointer Cast Prediction (`spec/lang/representation.md`, `spec/mem/intptrcast.md`)

MiniRust separates byte-level pointer/integer transmutation from integer-to-pointer casts:
- **Byte-level representation (`spec/lang/representation.md:73-140`):** Integer decoding (`IntType::decode`) discards byte provenance; integer encoding (`IntType::encode`) emits `Init(u8, None)` bytes. Pointer encoding (`encode_ptr`) attaches `(provenance, byte_offset)` fragments across all `PTR_SIZE` bytes; pointer decoding (`decode_ptr`) retains `Some(provenance)` only if all `PTR_SIZE` bytes are `Init` and carry matching provenance and expected byte offsets, falling back to `provenance = None` when fragments are missing or mixed.
- **Integer-pointer cast subsystem (`spec/mem/intptrcast.md`):** Casting a pointer to an integer invokes `IntPtrCast::expose`, inserting `ptr.provenance` into `self.exposed: Set<Provenance>`. Casting an integer to a pointer invokes `IntPtrCast::int2ptr`, which uses angelic prediction (`predict`) to select `None` or `Some(prov)` with `prov` in `self.exposed`, whereas ordinary machine branching (`pick`) is demonic. Replacing `predict` with demonic branching in a proof assistant alters the specification's semantics.

#### 1.3 `minimize` Translator Defaults and Comparative Core Calculi

`tooling/minimize/src/main.rs` (`lines 105-120`) links `rustc` to lower Rust via MIR into MiniRust ASTs, passing `-Zmir-emit-retag`, `-Zmir-opt-level=0`, `-Zmir-preserve-ub`, and `-Zub-checks=false`. While this operationalizes UB-preserving MIR extraction, no theorem proves that `minimize` reflects all source Rust undefined behavior.

Comparing MiniRust against five foundational Rust calculi clarifies what can and cannot be reused across formal subjects:

| Formal Subject | Reusable Mechanism / Theorem | Unsafe-Verification Boundary Relative to MiniRust `d821c6e` |
| :--- | :--- | :--- |
| **$\lambda_{\text{Rust}}$ / RustBelt** (POPL 2018, DOI `10.1145/3158154`; Appendix `2017-11-09`) | Semantic lifetime logic in Iris + adequacy allows verified `unsafe` libraries to compose safely with syntactically typed clients. Appendix Fig. 2 models block/offset locations and distinct non-atomic vs. sequentially consistent operations. | Operates on a custom MIR-inspired CPS calculus over mathematical integers and high-level values; omits byte-level provenance fragments, Tree Borrows, and relaxed memory (addressed separately in POPL 2020). |
| **Oxide** (`arXiv:1903.00982v4`, `2021-10-19`) | Region sets approximate reference provenance; syntactic progress and preservation cover borrow checking, branches, closures, and non-lexical lifetimes (NLL). | Tested correspondence is typechecking parity on a safe test suite; Section 3.8 explicitly excludes `unsafe` code, raw pointers, and concurrency. |
| **Featherweight Rust** (Author preprint, March 2020, DOI `10.1145/3443420`) | Separates owned vs. borrowed location values with flow-typed borrow safety. | Small lexical core syntax; Section 4.5.2 relies on termination for borrow safety and Section 5.3 notes NLL discrepancies; no byte representation or alias tree. |
| **Rust Distilled** (`arXiv:1806.02693v2`, `2018-08-16`) | Region context tracks fractional capabilities and borrower metadata, restoring parent capability on borrow drop. | Exploratory expressiveness tower; progress/preservation and instrumented-state erasure correspondence remain planned rather than completed in `v2`. |
| **KRust** (`arXiv:1804.10806v1`, `2018-04-28`) | Executable K-framework operational semantics for ownership, borrowing, and a surface Rust subset. | Section VI explicitly leaves `unsafe` code, concurrency, reference-bearing struct fields, closures, and traits unimplemented in the inspected paper version. |

---

### 2. Coupled vs. Factored `BasicMemory` Operational Correspondence and Permission-Aware Cleanup

**Basis:** `source`, `execution`, and `derived`

#### 2.1 Exact Check Ordering in Upstream `BasicMemory` (`spec/mem/basic.md`, `spec/lang/step/intrinsics.md`)

In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `BasicMemory<T: Target>` (`spec/mem/basic.md:62-90`) stores a monotonic list `allocations: List<Allocation>` indexed by `AllocId(usize)`, where each `Allocation` couples `address: Address`, `data: List<AbstractByte<Option<Provenance>>>` (whose length defines `Allocation::size`), `align: Align`, `kind: AllocationKind`, `live: bool`, and `extra: T::AllocExtra`. Source inspection establishes five strict operational orderings:

1. **Allocation (`allocate`, `spec/mem/basic.md:92-141`):** Validates `T::valid_size(size)` (`size <= 2^63 - 1` on `x86_64`, `spec/prelude/target.md:27-29,57`) *before* demonic candidate selection `pick(0..T::MAX_ADDR, ...)`. Valid candidates require `addr > 0` (`addr >= align.bytes()`), `addr % align.bytes() == 0`, `addr + size < T::MAX_ADDR`, and `!alloc.overlaps(addr, size)` for all live allocations (where `overlaps` at `basic.md:87-89` rejects equal base addresses `self.address == other_addr` even when `size == 0`).
2. **Span validation (`check_ptr`, `spec/mem/basic.md:197-224`):** Immediately returns `ret(None)` when `len == 0` (`basic.md:201-203`), bypassing provenance, liveness, and bounds checks. When `len > 0`, checks provenance presence (`basic.md:204-206`), `alloc.live` (`basic.md:209-211`), and `ptr.addr >= alloc.address && offset + len <= alloc.size()` (`basic.md:215-217`).
3. **Alignment before zero-length shortcut (`load` and `store`, `spec/mem/basic.md:227-274,329-335`):** Both `load` and `store` check `if !align.is_aligned(ptr.addr)` *before* calling `self.check_ptr(ptr, len)`. Thus a zero-length `load` or `store` on a misaligned pointer triggers UB (`misalignedLoad` / `misalignedStore`), whereas an aligned zero-length `load` or `store` succeeds even on a provenance-free, dead, or out-of-bounds pointer. By contrast, `dereferenceable` (`basic.md:337-339`) delegates directly to `check_ptr` without checking alignment.
4. **Six-stage deallocation (`deallocate`, `spec/mem/basic.md:144-184`):** Checks sequentially: (1) provenance present (`freeNoProvenance`), (2) `alloc.live` (`doubleFree`), (3) `ptr.addr == alloc.address` (`freeNotBase`), (4) `alloc.kind == kind` (`freeKind`), (5) `alloc.size() == size` (`freeSize`), and (6) `alloc.align == align` (`freeAlign`), then sets `alloc.live = false` while retaining the record at its `AllocId` index.
5. **Termination leak check (`leak_check`, `spec/mem/basic.md:278-296`; `exit`, `spec/lang/step/intrinsics.md:85-100`):** Scans `self.allocations` for any record with `alloc.live && alloc.kind == AllocationKind::Heap`, raising `MachineStop::MemoryLeak` (distinct from `TerminationInfo::Ub`).

#### 2.2 Mechanized Coupled vs. Factored Correspondence (`MiniRustReference`, `MiniRustFactored`, `MemoryExecution`)

In [`support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustReference.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustReference.lean) and [`support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean), the coupled reference state (`next : Nat`, `allocations : Nat -> Option Allocation`) is paired with a factored state (`next : Nat`, `metadata : Nat -> Option Metadata`, `cells : Nat -> Nat -> Byte`) where pointer resolution (`MiniRustFactored.resolve`) inspects only `metadata`. The abstraction map `reify : MiniRustFactored.State -> MiniRustReference.State` and splitting map `encode : MiniRustReference.State -> MiniRustFactored.State` satisfy `reify (encode state) = state` unconditionally (`MiniRustFactored.reify_encode`) and commute with every primitive operation and result constructor (`Result.ok`, `Result.ub`, `Result.noChoice`, `Result.unsupported`):

| Operation / Property | Lean Theorem | Support Location | Verified Equation / Bijection |
| :--- | :--- | :--- | :--- |
| Left inverse of `encode` | `MiniRustFactored.reify_encode` | [`MiniRustFactored.lean:92-100`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L92-L100) | `reify (encode state) = state` |
| Span resolution | `MiniRustFactored.resolve_reify` | [`MiniRustFactored.lean:244-259`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L244-L259) | `checkPtr (reify s) p len = resultMap (Option.map (reifySpan s)) (resolve s p len)` |
| Aligned byte load | `MiniRustFactored.load_reify` | [`MiniRustFactored.lean:320-334`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L320-L334) | `load (reify s) p len align = resultMap (Prod.map id reify) (load s p len align)` |
| Aligned byte store | `MiniRustFactored.store_reify` | [`MiniRustFactored.lean:336-355`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L336-L355) | `store (reify s) p bytes align = resultMap reify (store s p bytes align)` |
| Deallocation | `MiniRustFactored.free_reify` | [`MiniRustFactored.lean:357-367`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L357-L367) | `free (reify s) p kind size align = resultMap reify (free s p kind size align)` |
| Candidate allocation | `MiniRustFactored.allocateAt_reify` | [`MiniRustFactored.lean:382-387`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L382-L387) | `allocateAt (reify s) kind size align addr = resultMap (Prod.map id reify) (allocateAt s kind size align addr)` |
| Relational allocation | `MiniRustFactored.Allocate_reify`, `Allocate_coverage` | [`MiniRustFactored.lean:427-447`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L427-L447) | Exact bijection of non-`noChoice` allocation branches across `reify` |
| Dereferenceability | `MiniRustFactored.dereferenceable_reify` | [`MiniRustFactored.lean:389-398`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L389-L398) | `dereferenceable (reify s) p len = dereferenceable s p len` |
| Termination leak check | `MiniRustFactored.exit_reify` | [`MiniRustFactored.lean:400-421`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean#L400-L421) | `MiniRustReference.exit (reify s) = exit s` |
| All-prefix reachability | `MemoryExecution.memory_prefix_iff` | [`MemoryExecution.lean:230-233`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryExecution.lean#L230-L233) | $\mathrm{Reach}\;\mathrm{SourceStep}\;(\mathrm{mapCfg}\;\mathrm{reify}\;t)\;s \iff \exists t',\; \mathrm{Reach}\;\mathrm{TargetStep}\;t\;t' \wedge \mathrm{mapCfg}\;\mathrm{reify}\;t' = s$ |
| All-prefix `NoUB` equivalence | `MemoryExecution.memory_noUB_iff`, `encoded_noUB_iff` | [`MemoryExecution.lean:235-245`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryExecution.lean#L235-L245) | $\mathrm{NoUB}\;\mathrm{SourceStep}\;\mathrm{Bad}\;(\mathrm{mapCfg}\;\mathrm{reify}\;t) \iff \mathrm{NoUB}\;\mathrm{TargetStep}\;\mathrm{Bad}\;t$ |

Structural well-formedness (`StateWF` in [`ReferenceInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/ReferenceInvariants.lean) and `TargetWF` in [`MemoryInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryInvariants.lean)) is preserved across `empty`, `allocateAt`, `store`, and `free`, ensuring well-formed pointers and power-of-two alignments never yield `.unsupported`. Concrete reachability witnesses in [`MemoryWitnesses.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryWitnesses.lean) and [`MemoryExamples.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryExamples.lean) prove non-vacuous execution and address reuse with fresh allocation IDs (`actual_reuse_chain`, `stale_identity_mutation_control`). Boundary controls in [`MemoryBoundaryControls.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryBoundaryControls.lean) prove that an alignment of $2^{64}$ with `size = 1 < sizeLimit` yields `.noChoice` at every candidate address (`empty_choice_safe_without_progress`: vacuously `NoUB`, but not `Verified`), whereas `size = sizeLimit` triggers `.ub .allocationTooLarge` before candidate filtering (`oversized_before_choice`).

#### 2.3 Flat Permission Framing and Multi-Phase Cleanup (`BorrowFrame`, `MemoryPermissions`, `PermissionCleanup`, `PermissionControls`)

- **Spatial framing vs. same-byte multi-tag interference ([`BorrowFrame.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/BorrowFrame.lean)):** Transcribing the six-state unprotected permission lattice (`Cell`, `Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled`) from `spec/mem/tree_borrows/state_machine_unprotected.md` proves that assertions on byte footprints disjoint from an accessed `(alloc, offset)` frame unconditionally (`perform_spatial_frame`, `frame_triple`). At the *same* byte offset, distinct tags do not frame unless the foreign tag's state is invariant under `foreignTransition` (`same_byte_frame_of_stability`): theorem `TagCounterexample.disjoint_tags_do_not_frame` ([`BorrowFrame.lean:230-240`](support/minirust-d821c6e-basic-memory-factored-correspondence/BorrowFrame.lean#L230-L240)) shows that reading through tag `0` (`Cell`) at byte `⟨0, 0⟩` demotes sibling tag `1` on the same byte from `Unique` to `Frozen`, causing a later write through tag `1` to fault with `.localWriteFrozen`.
- **Residual permission retention on uninitialized typed read ([`MemoryPermissions.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryPermissions.lean), [`MemoryPermissionInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryPermissionInvariants.lean)):** A typed `u8` read executes raw `load`, applies `BorrowFrame.perform`, and then runs `decodeInitialized`. When the byte is `.uninit`, steps 1 and 2 succeed before step 3 faults with `.ub (.permission .uninitializedRead)`, and the updated permission state is retained in the residual configuration (`uninit_typed_read_retains_permissions`, `decode_preserves_residual`).
- **Six-phase cleanup correspondence ([`PermissionCleanup.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/PermissionCleanup.lean), [`PermissionControls.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/PermissionControls.lean)):** Embedding `CoupledMemory` and `FactoredMemory` into a six-phase cleanup state machine (`body` -> `testCleanup` -> `consumeObligation` -> `invokeHandler` -> `handlerRead` -> `handlerWrite` -> `finish`) preserves exact prefix and `NoUB` correspondence (`cleanup_prefix_iff`, `cleanup_noUB_iff`). Disjoint body and cleanup byte offsets succeed (`DisjointCleanup.cleanup_safe`), whereas a mutated semantics that discards read-induced permission updates falsely admits an aliasing cleanup fault (`ReadMutation.mutation_invalidates_cleanup_safety`).

---

### 3. Demonic/Angelic Nondeterminism (`pick`/`predict`), Finite Exposed-Provenance Domains, and Causal Strategy Extraction

**Basis:** `source`, `execution`, and `derived`

#### 3.1 `libspecr` Runtime Implementation vs. `IntPtrCast::int2ptr` State-Indexed Finiteness

In `minirust/specr` at `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (`libspecr/src/nondet.rs:32-50`), `pick` rejection-samples at most 50 candidates from `rand::thread_rng()` before panicking (`panic!("unable to find suitable element in pick")`), and `predict` unconditionally panics with `unimplemented!()`.

In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `predict` has a single callsite across `spec/`, in `IntPtrCast<Provenance>::int2ptr` (`spec/mem/intptrcast.md:45-53`):
```rust
pub fn int2ptr(&self, addr: Address) -> ThinPointer<Provenance> {
    let provenance = predict(|prov: Option<Provenance>| {
        if let Some(prov) = prov {
            self.exposed.contains(prov)
        } else {
            true
        }
    });
    ThinPointer { addr, provenance }
}
```
Because `self.exposed: Set<Provenance>` starts empty at machine creation (`spec/lang/machine.md:113`) and grows only by single-element insertions in `IntPtrCast::expose` (`spec/mem/intptrcast.md:27-31`), after $n$ prior `expose` transitions on any finite prefix, the set of eligible predictions at state $s$ is finite of cardinality at most $n + 1$:
$$\mathcal{A}(s) = \{\text{None}\} \cup \{\text{Some}(p) \mid p \in \text{exposed}(s)\}, \qquad |\mathcal{A}(s)| \le n + 1.$$

#### 3.2 Failure of $\omega$-Continuity Under Unbounded Angelic Branching vs. Finite-List Strategy Extraction

Across the 4 Lean modules in [`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/):

1. **Unbounded angelic branching breaks $\omega$-continuity ([`UnboundedWitness.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/UnboundedWitness.lean), [`Execution.lean:169-279`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/Execution.lean#L169-L279)):**
   In `CountdownState` (`.root` steps angelically to `.ticks n` for any $n : \mathbb{N}$, then counts down to `.ticks 0` = `Bad`), `.root` belongs to every finite-horizon safety approximant (`root_in_every_approximant`: $\forall k,\; \mathrm{Approximant}\;k\;\mathrm{.root}$), yet the $\omega$-intersection `OmegaIntersection` is not postfixed (`omega_intersection_not_postfixed`) and `.root` is outside the greatest safety fixed point (`finite_approximants_do_not_establish_greatestSafety`: $\mathrm{OmegaIntersection}\;\mathrm{.root} \wedge \neg \mathrm{GreatestSafety}\;\mathrm{.root}$). Furthermore, `Execution.ChoiceScope.order_and_information_discriminator` ([`Execution.lean:283-312`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/Execution.lean#L283-L312)) proves $\neg \mathrm{CausalBefore} \wedge \mathrm{PropheticBefore} \wedge \mathrm{CausalAfter}$, isolating causal state-indexed choice from prophetic trace-level quantification.
2. **Per-state finite legal actions yield a single prefix-coherent causal strategy ([`FiniteCausalStrategies.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteCausalStrategies.lean), [`FiniteStrategyDiscriminators.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteStrategyDiscriminators.lean)):**
   When legal angelic actions at each state are given by a finite list `legalActions : State -> List Action` (even with infinite state spaces and unbounded demonic branching), a finite-list König/pigeonhole lemma (`finite_list_intersection`, [`FiniteCausalStrategies.lean:91-118`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteCausalStrategies.lean#L91-L118)) proves that `Winning game state := ∀ n, Approximant game n state` is postfixed (`winning_postfixed`, `winning_unfold`) and characterizes existence of a single state-indexed policy satisfying both `NoUB` and `ReachableProgress` (`winning_iff_classified_strategy`, [`FiniteCausalStrategies.lean:268-288`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteCausalStrategies.lean#L268-L288)). Operational discriminators in [`FiniteStrategyDiscriminators.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteStrategyDiscriminators.lean) contrast one-step committed responses against unbounded demonic streams (`responseGame`) with binary increment/commit search (`searchGame`, where every verified strategy diverges safely in `.search` without ever committing a finite countdown witness: `classified_policy_cannot_reach_commit`).
3. **Exhaustive finite-witness byte-copy probe ([`witness_probe.py`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness_probe.py)):**
   Enumerating `HistoryFree` and `AliasSensitive` byte-copy models over lengths $0 \le n \le 3$ verifies all **11,310** positive well-separated copy cases (**161,776** primitive events), rejects all 6 negative-control families (`uninitialized`, `invalid-bool`, `bounds`, `pointer-arithmetic`, `provenance`, `authority`), accepts zero-length absent-provenance copies, and isolates a concrete trace (`distinct_model_witness`) where a foreign read freezes destination write authority in `AliasSensitive` while `HistoryFree` succeeds.

---

### 4. Concurrent Race Detection, Alias-Event Seams, and Weak-Memory Composition

**Basis:** `source`, `execution`, and `derived`

#### 4.1 `ConcurrentMemory<M>` Granularity and Empty-Interval Overlap Disagreements (`spec/mem/concurrent.md`, `spec/lang/machine.md`)

`ConcurrentMemory<M>` (`spec/mem/concurrent.md`) records `Access { type, atomicity, addr, len }` on every `load` and `store` before delegating to `M`. Its `Atomicity` enum contains only `Atomic` (sequentially consistent) and `None`; two `Atomic` accesses never race, and two reads never race. Otherwise, two accesses `(a, n)` and `(b, m)` conflict when `a + n > b && b + m > a`. `Machine::step` (`spec/lang/machine.md:197-245,355`) checks only the current step's accesses against the *immediately preceding step's* accesses (unless synchronized), rather than maintaining a per-location happens-before history. A three-step schedule in [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py) (`W(byte 1)` on thread 0 -> `R(byte 4)` on thread 1 -> `R(byte 1)` on thread 1) has no adjacent conflict despite racing between steps 1 and 3; relying on `ConcurrentMemory` for all-schedule race completeness therefore requires a commutation proof showing that any non-adjacent conflict can be scheduled adjacently without being blocked early by Tree Borrows alias UB.

Exhaustively testing all 80 single accesses (`addr` in `0..4`, `len` in `0..3`, read/write, atomic/non-atomic — 6,400 ordered pairs) in [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py) reveals:
- **198 empty-interval disagreements** between MiniRust's formula `a + n > b && b + m > a` and byte-set intersection: a zero-byte access strictly inside a nonempty write range (e.g., zero-byte read at `addr = 2, len = 0` vs. write at `addr = 1, len = 2` covering `[1, 3)`) satisfies `2 + 0 > 1 && 1 + 2 > 2` and is flagged as a data race by `ConcurrentMemory`, whereas a zero-byte access at the boundary (`addr = 1` or `addr = 3`) is not.
- **Partial-overlap atomic bypass:** Two `Atomic` accesses with partially overlapping footprints never trigger `ConcurrentMemory`'s race check, whereas Rust's C++20-derived atomic contract (`library/core/src/sync/atomic.rs:26` at `d8ef4f3fe7031514cbd7d056b7b058814987ecec`) forbids unsynchronized conflicting mixed-granularity atomic accesses.
- **Missing race events on Tree Borrows retag and protector release:** In MiniRust (`spec/mem/tree_borrows/memory.md:128-235`), `retag` and `end_call` delegate directly to `M` without pushing `Access` entries into `ConcurrentMemory`. By contrast, Miri (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`, `src/borrow_tracker/tree_borrows/mod.rs:390`) explicitly reports nonempty retag implicit reads and writes to its data-race detector.

#### 4.2 Weak-Memory Separation Logics and View-Sensitive Adequacy (`kaist-cp/relaxed-memory-separation-logic@6fe1475`)

- **RustBelt Meets Relaxed Memory (POPL 2020, DOI `10.1145/3371102`)** rebuilds lifetime logic over ORC11/iRC11 using view-indexed ghost state for synchronized resource transfer and reclamation, but omits sequentially consistent (`SeqCst`) atomics/fences, byte fragments, and Tree Borrows permissions.
- **GPFSL-derived 2024 adequacy (`kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`, `gpfsl/base_logic/adequacy.v:50`):** Direct inspection of `noprol_adequacy` shows that it requires physical state well-formedness `Wf σ`, initial thread view membership `𝓥 ∈ σ.mem`, ghost pre-state resources (freeable, read-event, atomic-write, and thread-view resources), and a weakest-precondition proof for every allocated logic instance and thread ID, concluding finite reachable-state `NotStuck` safety (`adequate NotStuck (e at 𝓥) σ (λ v _, φ v)`).
- **Message-passing litmus discriminator (`probe.py`):** Enumerating all 6 order-preserving sequentially consistent interleavings of producer `Wx = 42; Wflag = 1` and consumer `Rflag; Rx` permits `(0, 0)`, `(0, 42)`, and `(1, 42)` while forbidding `(1, 0)`. A toy relaxed view model in `probe.py` permits `(1, 0)` under relaxed operations and rules it out only when release/acquire synchronization imports the producer's view—illustrating why fractional ownership without view synchronization is insufficient for weak-memory reclamation.

## Boundaries

- **Known not to apply:**
  - `BasicMemory` safety does not imply `TreeBorrowsMemory` safety, and unprotected same-byte multi-tag framing does not hold unconditionally (`BorrowFrame.TagCounterexample.disjoint_tags_do_not_frame`).
  - Finite-horizon safety ($\forall k,\; \mathrm{Approximant}\;k\;s$) does not imply existence of a prefix-coherent strategy when angelic branching is infinite (`Execution.Prediction.finite_approximants_do_not_establish_greatestSafety`).
  - Plain `NoUB` without `ReachableProgress` does not prevent a policy from halting on an exhausted demonic choice set (`MemoryExecution.empty_choice_safe_without_progress`) or before a mandatory countdown to UB (`FiniteStrategyDiscriminators.artificial_countdown_stop`).
  - MiniRust's `ConcurrentMemory` is a single-previous-step sequentially consistent wrapper, not a happens-before detector or a C++20/ORC11 relaxed-memory model; conversely, the inspected ORC11 fragment in RustBelt Meets Relaxed Memory excludes `SeqCst` operations.
- **Not examined:**
  - Recursive tree-topology traversal, two-stage protector release across parent/child subtrees, and `GcCow` copy-on-write mutation in `spec/mem/tree_borrows/{tree.md,memory.md}` (which are examined in the companion package `reports/minirust-tree-borrows-protectors-and-program-logic-correspondence/REPORT.md`).
  - Prophetic or partial-information strategies where `predict` must depend on future demonic choices not yet present in machine state, and constructive strategy synthesis without `Classical.choice`.
  - Complete `minimize` source-to-MiniRust lowering, hardware relaxed-memory model mappings, or verified epoch/hazard-pointer reclamation implementations.
- **Unsupported:**
  - Runtime execution of `predict` in `minirust/specr` (`libspecr/src/nondet.rs:47-50`) is `unimplemented!()`.
  - Unsafe code and concurrency in the compared KRust paper (`arXiv:1804.10806v1`, Section VI).
- **Unknown:**
  - Whether upstream MiniRust will formalize `predict` in `spec/mem/intptrcast.md` as a causal state-indexed choice or a prophetic trace quantifier, and whether `ConcurrentMemory`'s zero-length interior overlap behavior (`a + n > b && b + m > a`) will be retained or aligned with nonempty byte-set intersection.

## Evidence

All preserved Lean 4 modules, Python probes, source excerpts, and verification ledgers live under `support/` inside this package:

1. **Core calculi and MiniRust interface inventory (`support/minirust-core-semantics-d821c6e/`):**
   - [`support/minirust-core-semantics-d821c6e/coverage.json`](support/minirust-core-semantics-d821c6e/coverage.json) — Mapping of MiniRust interface and core-calculus comparison claims (`observed_at: 2026-10-14`).
2. **Coupled vs. factored `BasicMemory` and permission-aware cleanup (`support/minirust-d821c6e-basic-memory-factored-correspondence/`, 17 Lean modules, 223 audited theorems, re-verified `2026-10-24`):**
   - Execution ledger: [`support/minirust-d821c6e-basic-memory-factored-correspondence/lean-verification-results.json`](support/minirust-d821c6e-basic-memory-factored-correspondence/lean-verification-results.json).
   - Lean 4 modules: [`Memory.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/Memory.lean), [`ByteMemory.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/ByteMemory.lean), [`MiniRustReference.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustReference.lean), [`ReferenceInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/ReferenceInvariants.lean), [`MiniRustFactored.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MiniRustFactored.lean), [`MemoryInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryInvariants.lean), [`Execution.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/Execution.lean), [`PrefixTransfer.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/PrefixTransfer.lean), [`MemoryExecution.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryExecution.lean), [`MemoryExamples.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryExamples.lean), [`MemoryBoundaryControls.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryBoundaryControls.lean), [`MemoryWitnesses.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryWitnesses.lean), [`BorrowFrame.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/BorrowFrame.lean), [`MemoryPermissions.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryPermissions.lean), [`PermissionCleanup.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/PermissionCleanup.lean), [`PermissionControls.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/PermissionControls.lean), and [`MemoryPermissionInvariants.lean`](support/minirust-d821c6e-basic-memory-factored-correspondence/MemoryPermissionInvariants.lean).
3. **Demonic/angelic nondeterminism and finite causal strategies (`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/`, 4 Lean modules, 45 audited theorems + Python probe, re-verified `2026-10-24`):**
   - Lean 4 modules: [`UnboundedWitness.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/UnboundedWitness.lean) (0 axioms), [`Execution.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/Execution.lean), [`FiniteCausalStrategies.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteCausalStrategies.lean), and [`FiniteStrategyDiscriminators.lean`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/FiniteStrategyDiscriminators.lean).
   - Verification ledgers: [`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/lean-verification-results.json`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/lean-verification-results.json) and [`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/unbounded-witness-results.json`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/unbounded-witness-results.json).
   - Finite-witness probe and output: [`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness_probe.py`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness_probe.py) and [`support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness-probe-results.json`](support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/witness-probe-results.json).
4. **Concurrent race detection and weak-memory boundaries (`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/`, observed `2026-10-14`):**
   - [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/source-evidence.json`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/source-evidence.json), [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/artifact-hashes.json`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/artifact-hashes.json), [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/coverage.json`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/coverage.json), [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/execution.json`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/execution.json), [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/probe.py), and [`support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/results.json`](support/minirust-race-alias-and-weak-memory-boundaries-d821c6e/results.json).

## Revalidation

To re-check all 21 Lean 4 (`4.34.1`) modules and re-run both Python probes from the repository root:

```bash
python3 - <<'EOF'
import os, subprocess, tempfile

pkg_dir = "reports/minirust-core-calculi-basic-memory-and-nondeterminism"

# 1. Re-verify the 17 BasicMemory and permission-cleanup Lean modules
basic_dir = os.path.join(pkg_dir, "support/minirust-d821c6e-basic-memory-factored-correspondence")
basic_order = [
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
    for mod in basic_order:
        src = os.path.join(basic_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", "-M1024", "-o", olean, src], env=env, check=True)

# 2. Re-verify the 4 nondeterminism and finite-strategy Lean modules + witness_probe.py
nondet_dir = os.path.join(pkg_dir, "support/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses")
subprocess.run(["lean", "-j1", "-M768", os.path.join(nondet_dir, "UnboundedWitness.lean")], check=True)
with tempfile.TemporaryDirectory() as tmp:
    mod_dir = os.path.join(tmp, "AnnealResearch")
    os.makedirs(mod_dir, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = tmp
    for mod, mem in [
        ("Execution", "-M768"),
        ("FiniteCausalStrategies", "-M768"),
        ("FiniteStrategyDiscriminators", "-M1024"),
    ]:
        src = os.path.join(nondet_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", mem, "-o", olean, src], env=env, check=True)
subprocess.run(["python3", os.path.join(nondet_dir, "witness_probe.py")], check=True)

# 3. Re-run the concurrent overlap and message-passing litmus probe
race_dir = os.path.join(pkg_dir, "support/minirust-race-alias-and-weak-memory-boundaries-d821c6e")
subprocess.run(["python3", os.path.join(race_dir, "probe.py")], stdout=subprocess.DEVNULL, check=True)
print("OK: all 21 Lean modules and 2 Python probes verified.")
EOF
```

Revalidate this package when `minirust/minirust` advances beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `minirust/specr` advances beyond `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, or the Lean 4 toolchain changes from `4.34.1`.
