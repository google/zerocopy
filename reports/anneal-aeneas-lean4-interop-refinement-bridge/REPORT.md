# Zero-TCB Lean 4 Refinement Bridge Between Anneal MIR Semantics and Aeneas Functional Extraction

## Summary

Aeneas (`AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f`, Lean `v4.36.0`) extracts safe Rust crates into pure Lean 4 functional programs over `Aeneas.Std.Result α := ITree RustEffect α` with dual Hoare-triple predicates `WP.spec` (total, panic-free via `DWP`) and `WP.dspec` (partial, panic-free via `DWLP`). Functions that Charon/Aeneas cannot translate—most importantly isolated `unsafe` leaves using raw pointers, `MaybeUninit`, byte casting, or SIMD intrinsics—must be manually declared in `FunsExternal.lean` as unverified constructive Lean definitions or `opaque`/`axiom` stubs, creating an unverified trust gap between the Rust implementation and the Aeneas model.

Anneal (`google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1`, `anneal/trusted/lean`, Lean `v4.34.1`) verifies Rust functions directly against a byte-and-allocation operational semantics (`Trusted.MirSemantics`) over `Runtime(PostCleanup)` MIR with explicit `AllocId`, `AllocByte.{uninit, init}`, `Mutability`, alignment, and terminal/diverging outcomes (`WellFormed`, `Behavior`, `Diverges`). Combining both tools inside Lean 4 requires **zero additions to Anneal's Trusted Computing Base (`trusted/lean/`)** and **zero custom Lean axioms** beyond `{propext, Classical.choice, Quot.sound}`:

1. **Value and memory representation bridge (`[source inspection]` + `[kernel-checked proof]` `[toy model]`):**
   - `UScalar`/`IScalar` values refine `Trusted.MirSemantics.Val.scalar` canonically (`truncateBits w bits = bits ∧ bits.truncate w.bitWidth = x.bv`), requiring an explicit 64-bit platform witness `System.Platform.numBits = 64` for `Usize`/`Isize`.
   - `Slice U8` (`&[u8]` / `&mut [u8]`) refinement MUST split `len = 0` (permitting a non-null aligned dangling pointer with no allocation lookup, matching Miri and `Trusted.MirSemantics.readBytes`) from `len > 0` (requiring `len ≤ isize::MAX`, live allocation, alignment, in-bounds range, and fully initialized bytes), and MUST enforce **spatial disjointness** (`DisjointFootprints`) across multiple slice parameters plus **frame preservation** (`FramePreserved`) on all bytes outside `&mut` footprints.
   - Internal `MaybeUninit` scratch allocations inside an `unsafe` leaf remain freely uninitialized during execution as long as no `.uninit` byte is read (`WellFormed`) and all boundary output slices are initialized upon `.returned`.
   - Borrow-returning functions (such as `split_at_mut`) refine Aeneas backward functions `back : (Slice U8 × Slice U8) → Slice U8` via **universal quantification over arbitrary valid future caller mutations** to the returned disjoint footprints (prophecy closure).
   - **MIR Profile v1 endianness gap (`[source inspection]`):** `Trusted.MirSemantics.Layout.profileTargetEndian` is currently fixed to `.big` in MIR profile version 1 (which admits no byte-reinterpreting operations); bridging little-endian byte-cast leaves requires target-endianness parameterization in MIR profile v2+.
2. **Panic, unwind, abort, and divergence alignment (`[source inspection]` + `[kernel-checked proof]` `[toy model]`):**
   - Charon/Aeneas collapses unwinding panics (`core::panicking::panic`) and non-unwinding aborts (`panic_no_unwind`, `panic_in_cleanup`) into `Result.fail .panic` and drops `on_unwind` cleanup edges.
   - A single unified 3-way refinement predicate (`AnnealRefinesAeneas`, covering `.ok b`, `.div`, and `.fail e`) guarantees UB-freedom (`WellFormed`) on all inputs satisfying `SafetyPre` (even panicking inputs on safe-API leaves), forbids spurious normal returns on `.fail`/`.div`, and implies **both** the `WP.spec` total-correctness transfer theorem and (via weakening) the `WP.dspec` partial-correctness transfer theorem.
3. **Toolchain alignment and independent multi-kernel replay (`[source inspection]` + `[real measurement]`):**
   - `Aeneas.Std` core (`Result`, `ITree`, `DWP`, `DWLP`, `UScalar`, `IScalar`, `Slice`, `Array`, `Vec`) introduces **zero** custom axioms (`axiom` declarations exist only for `Slice.get_unchecked` spec, `AtomicBool`, `AtomicU32`, `Pin`/`PinHelper`, and `PanicInfo`, plus `noncomputable opaque` for `Target`).
   - Upstream Aeneas (`v4.36.0`) uses Lean 4 `module` headers and depends on `mathlib4 @ v4.36.0`; Anneal (`v4.34.1`) is strictly Mathlib-free. Because Lean 4 `.olean` binaries are minor-version-locked, native composition requires an optional downstream bridge Lake package (`anneal-aeneas-bridge`) compiled on a **shared Lean toolchain** (leaving core Anneal Mathlib-free). Prefix-relocated environment replay resolves same-version module/symbol collisions across vendor trees, not cross-minor-version `.olean` header mismatch.
   - Lean `v4.35.0` bundles `lake check --paranoid` (`leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, and `con-ron` over `leanexport` NDJSON inside `bwrap`), enabling zero-custom-axiom independent multi-kernel replay of composed proofs.
4. **Hard semantic limits (`[source inspection]` + `[derived]`):**
   - The bridge composes cleanly for first-order safe callers invoking isolated `unsafe` leaves (read-only slices, disjoint `&mut` buffers, borrow-splitting lenses, POD structs/enums, panicking safe APIs).
   - It hits hard limits on re-entrant `FnMut` callbacks from `unsafe` leaves into Aeneas closures over shared memory, cross-call shared interior mutability (`UnsafeCell`/atomics), custom `#[global_allocator]` / pointer-address-observing APIs, and `catch_unwind` across non-trivial `Drop` glue.

## Applicability

- **Subjects examined:**
  1. `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f` (`backends/lean/lakefile.lean`, `lean-toolchain` = `leanprover/lean4:v4.36.0`, `Aeneas/Std/{Primitives,WP,SliceDef,Slice,RawPtr,Target}.lean`, `Aeneas/Std/Scalar/Core.lean`, `Aeneas/Std/Alloc/{Alloc,Boxed,Vec}.lean`, `Aeneas/Std/Core/{Core,Result,CoreOption,Ops,Panic,Atomic}.lean`, `Aeneas/Data/Coinductive/{CoInd,ITree,ITreeWP/DWP,ITreeWP/DWLP,ITreeWP/Taxonomy}.lean`, `tests/lean/Slices.lean`).
  2. `AeneasVerif/jxl-proofs@79ea57c0e9f630e06e9ec3a6d1d61fa9ed50e55d` (`Makefile`, `lean/lean-toolchain` = `v4.31.0`, `lean/JxlProofs/{FunsExternal,Funs,Proofs,Types}.lean`), referencing `BurntSushi/byteorder` tag `1.5.0` (`src/lib.rs`).
  3. `google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1` (`anneal/trusted/lean/lean-toolchain` = `v4.34.1`, `foundation-lock.json`, `Trusted/MirAst/{Types,Terminators}.lean`, `Trusted/MirModel.lean`, `Trusted/MirSemantics/{State,Memory,Bytes,Layout,Step,Boundary}.lean`).
  4. `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, used to kernel-check `support/ToyBridge.lean`) and `v4.35.0` (bundled `lake check --paranoid` CLI and external checker binaries).
- **Relationship among subjects:** This report characterizes the semantic and toolchain interface between Aeneas's pure Lean 4 functional extraction (`Aeneas.Std`) and Anneal's MIR operational semantics (`Trusted.MirSemantics`), using `AeneasVerif/jxl-proofs`'s `FunsExternal.lean` (`byteorder::LittleEndian::read_u64`) as a concrete external-function specimen and `support/ToyBridge.lean` as a self-contained, Mathlib-free Lean `v4.34.1` executable witness.
- **Target constraints:** Anneal's `Trusted.MirSemantics.BodyStaticAdmitted` pins `pointerWidthBits = 64` and `mirProfileVersion = 1`. The slice, fat-pointer, and little-endian byte-cast bridge predicates described here target 64-bit little-endian Rust targets and require Anneal's MIR profile to advance beyond profile version 1 (which currently admits only scalar/unit/fieldless-enum/overflow-pair locals and fixes big-endian layout).

## Findings

### 1. Grounded Comparison of Core Representations (`Aeneas.Std` vs. `Trusted.MirSemantics`)

`Basis: source`

| Semantic Concept | `Aeneas.Std` (`AeneasVerif/aeneas@2e3d4488`) | `Trusted.MirSemantics` (`google/zerocopy@a007a51a`) | Exact Bridge Alignment Requirement |
| :--- | :--- | :--- | :--- |
| **Effect / Execution Monad** | `Result α := ITree RustEffect α` (`Primitives.lean:68`), where `RustEffect.Input := \| fail (e : Error)` and `Output (.fail _) := PEmpty`. Three constructors: `.ok a`, `.fail e`, `.div`. | Small-step `Step` / `Reaches` / `WellFormed` / `Behavior` / `Diverges` over `TerminalOut := \| returned out \| unwound callerMem` (plus `aborted` when distinguishing `panic=abort`). | Four-way outcome map (§3); `WellFormed` (UB-freedom) has no Aeneas counterpart and must be discharged entirely by Anneal. |
| **Hoare Triples** | `WP.spec m P := DWP effectWP m (fun v _ => P v) ()` (least fixpoint, total + panic-free); `WP.dspec m P := DWLP effectWP m ...` (greatest fixpoint, partial + panic-free), with `spec_dspec : spec x p → dspec x p` (`WP.lean:56-63`). | `WellFormed`, `¬ Diverges`, `Behavior _ (.returned o)`, `Behavior _ (.unwound m)`. | `AnnealRefinesAeneas` transfers `WP.spec` to total + panic-free + UB-free MIR execution; `AnnealRefinesAeneasPartial` transfers `WP.dspec` (§3). |
| **Machine Integers** | `UScalar ty` / `IScalar ty` wrapping `bv : BitVec ty.numBits`; `Usize.numBits = Isize.numBits = System.Platform.numBits` (`Scalar/Core.lean:45-77`). | `ScalarVal { width : IntWidth, signed : Bool, bits : BitVec 128 }` with `IntWidth.byteSize` fixing `.isize => 8` and canonicality `truncateBits w bits = bits` (`MirModel.lean:67-71`). | Exact bit equality `bits.truncate w.bitWidth = x.bv` + `truncateBits w bits = bits`; `Usize`/`Isize` requires explicit `System.Platform.numBits = 64` cast. |
| **Byte Slices (`&[u8]`, `&mut [u8]`)** | `structure Slice α where leng : Nat; list : ListN α leng; bound : leng ≤ Usize.max` (`SliceDef.lean:14-18`); `Slice.val : List α`. Fully initialized, provenance-free, no address/alignment. | `CallerMemory` holds `List Allocation`, each `{ allocId, alignLog2, mutability, bytes : List AllocByte, live }` with `AllocByte := .uninit \| .init byte prov` (`MirModel.lean:83-85, 148-153`). | Fat pointer `(ptr, len)` with `len ≤ isize::MAX`; `len = 0` permits non-null aligned dangling `ptr` without live allocation; `len > 0` requires live allocation, alignment, in-bounds, `.init` bytes, plus `mutability = .mut`, `DisjointFootprints`, and `FramePreserved` for `&mut` (§2). |
| **Fixed Arrays (`[T; N]`)** | `structure Array α (n : Usize) where list : ListN α n.val` (`Array/Array.lean:24-26`). | Inline contiguous `N * sizeOf(T)` bytes with alignment `align(T)`. | Zero-sized (`N = 0 ∨ sizeOf(T) = 0`) uses ZST non-null aligned pointer rule; otherwise contiguous element refinement. |
| **`Vec<T>`** | `structure Vec α where slice : Slice α` (`Alloc/Vec.lean:33-34`); capacity and allocator are erased. | Heap allocation of `cap * sizeOf(T)` bytes (`len ≤ cap`, `cap * sizeOf(T) ≤ isize::MAX`), initialized on `0..len`, potentially `.uninit` on `len..cap`. | Existential quantification over `cap ≥ len` at boundary; capacity-observing Rust APIs cannot refine standard `Aeneas.Std.alloc.vec.Vec`. |
| **`Box<T>`** | Erased to `T` (`Alloc/Boxed.lean:1`: *"`Box<T>` is `T` in the extracted code"*). | Unique live mutable heap allocation of `sizeOf(T)` bytes (or non-null aligned dangling pointer for ZST `T`). | Unique owned allocation footprint holding refined `T` bytes; deallocated on drop. |
| **`Option<T>`, `Result<T, E>`, Enums** | `Option T` (`Core/Core.lean:15`), `core.result.Result T E` (`Core/Result.lean:8`), inductive Lean ADTs. | Concrete `rustc_abi::LayoutData` encoding (direct tag `EnumTagRepr.scalar`, niche optimization, or `zeroSized` single-variant). | Layout-indexed decoder `ValRefinesEnum layout` mapping raw tag/niche bytes and payload offsets to Aeneas constructors. |
| **Raw Pointers & Allocators** | `RawPtr T M` is a non-operational marker (`RawPtr.cast_scalar` returns `.fail .undef`); `alloc::alloc::Global` is the sole modeled allocator (`Alloc/Alloc.lean:1-12`). | `PtrVal { allocId : Option AllocId, offsetBytes : UInt64, width : IntWidth }` with provenance & live-allocation checks. | Raw pointers remain strictly internal to Anneal `unsafe` leaves; cross-boundary types must be safe references/slices/ADTs/scalars. |

### 2. Value, Slice, Framing, ZST, and Backward-Function Soundness Conditions

`Basis: source + execution + derived`

#### 2.1 Empty Slices, ZSTs, Alignment, and `MaybeUninit`

In `Trusted.MirSemantics.Memory.lean:148-158`, zero-byte accesses (`size = 0`) succeed immediately without requiring a live allocation, matching `rustc`'s `check_and_deref_ptr` (`if size == 0 { return interp_ok(None); }`). In Rust, `&[][..]` and `&mut [][..]` commonly carry `NonNull::dangling()` (`allocId = none`, `offsetBytes = align_of::<T>() ≠ 0`). Consequently:

- A naive slice refinement predicate that unconditionally requires `∃ a ∈ m.allocations, a.allocId = ptr.allocId ∧ a.live = true` is **unsoundly strong** (it excludes valid empty Rust slices and ZST slices).
- The exact boundary predicate splits on `len * sizeOf(T) = 0`:
  - **Zero-byte case (`len * sizeOf(T) = 0`):** requires `len = s.val.length`, `len ≤ isize::MAX`, `ptr.offsetBytes ≠ 0`, and `ptr.offsetBytes % align(T) = 0` (no allocation lookup).
  - **Non-empty case (`len * sizeOf(T) > 0`):** requires `len = s.val.length`, `len * sizeOf(T) ≤ isize::MAX`, `ptr.allocId = some aid`, live allocation `a` with `a.alignLog2 ≥ alignLog2(T)`, `ptr.offsetBytes % align(T) = 0`, `ptr.offsetBytes + len * sizeOf(T) ≤ a.bytes.length`, and every element byte initialized (`AllocByte.init b prov`). Allowing arbitrary `prov : Option AllocId` on read-only `&[u8]` inputs matches Miri (reading a scalar `u8` ignores provenance), whereas output pointer-free byte buffers should emit `prov = none` unless provenance preservation is explicitly modeled.
- **Internal `MaybeUninit` scratch buffers:** Because `Trusted.MirSemantics.State` separates local stack allocations (`mem : MemoryState`) from caller-visible heap/borrow allocations (`callerMem : CallerMemory`), an Anneal `unsafe` leaf can freely allocate uninitialized `MaybeUninit<[u8; N]>` buffers in `mem`, initialize them via raw pointers, and copy initialized bytes into an output `&mut [u8]` in `callerMem`. `WellFormed` forbids reading `.uninit` bytes; the boundary predicate enforces full initialization strictly at the Aeneas boundary.

#### 2.2 Disjoint `&mut` Framing and Backward-Function (Prophecy) Equivalence

Because Aeneas functionalizes references into independent pure values, linking an Aeneas safe caller against an Anneal `unsafe` leaf taking mutable slices requires **two spatial invariants** (both mechanized and negatively tested in `support/ToyBridge.lean`):

1. **Entry Disjointness (`DisjointFootprints`):** Every `&mut` parameter footprint `(p_mut, byteLen_mut)` must be pairwise disjoint from every other `&` and `&mut` parameter footprint at the call boundary. If `dst` and `src` overlap on a multi-step in-place loop (e.g., `dst[i] ^= src[i]`), the Rust memory execution diverges from Aeneas's pure functional model where `dst` and `src` are independent immutable lists (`overlapping_slices_fail_disjointness` in `support/ToyBridge.lean`).
2. **Exit Frame Preservation (`FramePreserved`):** Every allocation `a'` and every byte offset `off` outside the union of `&mut` parameter footprints must remain identical (`allocId`, `alignLog2`, `mutability`, `live`, `bytes.length`, and `bytes[off]?`) between `q.callerMem` and `out.callerMem`. Without `FramePreserved`, an `unsafe` leaf could overwrite an unrelated caller local that Aeneas's pure caller still holds unchanged (`frame_violation_refuted` in `support/ToyBridge.lean`).
3. **Borrow-Returning Backward Functions (Prophecy Closure):** For functions returning mutable sub-borrows—such as `core::slice::Slice::split_at_mut` (`Aeneas/Std/Slice.lean:740-755`), whose Aeneas signature returns `Result ((Slice T × Slice T) × ((Slice T × Slice T) → Slice T))`—Aeneas's backward function `back (s0', s1')` reconstructs the final parent slice after the caller finishes mutating `(s0, s1)`. Notice `Slice.lean:424-428` and `748-751`: Aeneas guards `back` with length equality (`if s0'.length = s0.length ∧ s1'.length = s1.length then s0' ++ s1' else s`) to keep `back` total. The exact operational refinement obligation on Anneal is:
   - Return pairwise disjoint sub-slice pointers `(p0, l0)` and `(p1, l1)` inside the parent allocation `(ptr, len)` refining `(s0, s1)`, preserving the complement; AND
   - Prove **prophecy closure**: for **every** future caller memory `memAfter` in which the caller updates `(p0, l0)` to any valid `s0'` (`s0'.length = l0`) and `(p1, l1)` to any valid `s1'` (`s1'.length = l1`) while keeping the parent allocation live and mutable, the parent slice `(ptr, len)` in `memAfter` refines **`back (s0', s1')`** (`split_at_mut_prophecy_sound` in `support/ToyBridge.lean`).

#### 2.3 Concrete Real-World Specimen: `AeneasVerif/jxl-proofs` `FunsExternal.lean`

`Basis: source`

Direct inspection of `AeneasVerif/jxl-proofs@79ea57c0` (`lean/JxlProofs/FunsExternal.lean:17-33`, `Funs.lean:84-102`, `Proofs.lean:120-137`) and `BurntSushi/byteorder@1.5.0` (`src/lib.rs:1998-2008, 2138-2140`) shows how external leaves actually appear in Aeneas projects:

- In `jxl-proofs/lean/JxlProofs/FunsExternal.lean`, `byteorder::LittleEndian::read_u64` is NOT left as an `axiom`—it is hand-authored as a constructive Lean `def` taking `bytes : Slice Std.U8`, binding `b0..b7` via `Result.ofOption (bytes.val[k]?) panic`, and returning `ok (UScalar.ofNatCore (b0 * 2^0 + ... + b7 * 2^56) _)`.
- In `Proofs.lean:120-124`, the `@[step]` lemma `read_u64_spec` requires `bytes.len ≥ 8` and is consumed by `BitReader.refill`'s proof (`Funs.lean:87-90`, guarded by `if i >= 8#usize`).
- In `BurntSushi/byteorder@1.5.0`, `LittleEndian::read_u64` itself (`src/lib.rs:2138-2140`) is safe Rust (`u64::from_le_bytes(buf[..8].try_into().unwrap())`)—it landed in `FunsExternal.lean` because the `TryFrom<&[u8]> for [u8; 8]` / external crate call was not extracted—while neighboring `BigEndian::write_uint` (`src/lib.rs:1998-2008`) uses genuine `unsafe { copy_nonoverlapping(...) }`.
- In **both** cases (unextracted external crate OR genuine `unsafe` body), a hand-written constructive `FunsExternal.lean` `def` leaves an **unverified correspondence gap**: Lean verifies `read_u64_spec` against the human-written Lean `def`, NOT against the Rust MIR! Proving `AnnealRefinesAeneas` between the captured Rust MIR and that exact constructive `def` closes the gap without changing a single line of `JxlProofs/Proofs.lean`.

### 3. Panic, Unwind, Abort, and Divergence Alignment

`Basis: source + execution`

Direct inspection of `Aeneas/Std/Primitives.lean`, `WP.lean`, `Core/Panic.lean`, and `Aeneas/Data/Coinductive/ITreeWP/{DWP,DWLP,Taxonomy}.lean` alongside `Trusted/MirModel.lean` and `Trusted/MirSemantics/Boundary.lean` establishes the exact outcome correspondence:

| Rust Operational Outcome | Anneal `Trusted.MirSemantics` | Aeneas `Result β` (`ITree RustEffect β`) | `WP.spec` (`DWP`) | `WP.dspec` (`DWLP`) |
| :--- | :--- | :--- | :---: | :---: |
| **Undefined Behavior** | `¬ WellFormed` (`.fault .undefined`) | Unmodeled (violates Aeneas soundness) | — | — |
| **Normal return `v`** | `WellFormed ∧ Behavior (.returned o)` | `Result.ok b` (`ITree.ret b`) | `P b` | `P b` |
| **Unwinding panic** | `WellFormed ∧ Behavior (.unwound m)` | `Result.fail e` (`ITree.vis (.fail e) PEmpty.elim`) | `False` | `False` |
| **Process abort (`panic=abort`, `panic_nounwind`)** | `WellFormed ∧ Behavior (.aborted m)` *(proposed 3rd constructor alongside `returned`/`unwound`)* | `Result.fail .panic` (`Core/Panic.lean:16-27` maps `panic`, `panic_no_unwind`, `panic_in_cleanup`, `assert_failed` all to `.fail .panic`) | `False` | `False` |
| **Infinite non-faulting loop** | `WellFormed ∧ Diverges` | `Result.div` (`ITree.div`) | `False` | `True` |

Key consequences:

1. **Unified 3-Way Refinement (`AnnealRefinesAeneas`) vs. Partial Refinement (`AnnealRefinesAeneasPartial`):**
   - For any input `(a, q)` satisfying `SafetyPre a ∧ R_in a q` (with `SafetyPre := fun _ => True` for safe-API leaves containing internal `unsafe`), `AnnealRefinesAeneas` requires:
     1. **`WellFormed ep q` unconditionally** (even when `aeneasFn a = .fail e`—a safe-API `unsafe` leaf must panic safely, never trigger UB!).
     2. **If `aeneasFn a = .ok b`:** `¬ Diverges ep q`, `∀ m, ¬ Behavior ep q (.unwound m)`, `∀ m, ¬ Behavior ep q (.aborted m)`, and `∀ o, Behavior ep q (.returned o) → R_out a b q o`.
     3. **If `aeneasFn a = .div`:** no unwind, no abort, and no spurious normal return (`∀ o, ¬ Behavior ep q (.returned o)`).
     4. **If `aeneasFn a = .fail e`:** no spurious normal return (`∀ o, ¬ Behavior ep q (.returned o)`), catching missing bounds/assertion checks in an `unsafe` leaf.
   - `AnnealRefinesAeneasPartial` drops `¬ Diverges ep q` in the `.ok b` branch.
   - **Kernel-checked transfer theorems (`support/ToyBridge.lean`, 0 axioms):**
     - `transfer_wp_spec`: `AnnealRefinesAeneas` + `WP.spec (aeneasFn a) P` implies `WellFormed ∧ ¬ Diverges ∧ noUnwind ∧ noAbort ∧ (Behavior (.returned o) → ∃ b, P b ∧ R_out a b q o)`.
     - `transfer_wp_dspec`: `AnnealRefinesAeneasPartial` + `WP.dspec (aeneasFn a) P` implies `WellFormed ∧ noUnwind ∧ noAbort ∧ (Behavior (.returned o) → ∃ b, P b ∧ R_out a b q o)`.
2. **What breaks when a leaf panics vs. triggers UB vs. loops:**
   - **Leaf triggers UB:** Breaks `WellFormed` (immediately rejected by Anneal). Because Aeneas assumes Rust soundness, an unverified UB leaf completely invalidates every Aeneas caller proof.
   - **Leaf panics on an input where Aeneas caller proved `WP.spec` / `WP.dspec`:** Impossible once `AnnealRefinesAeneas` is proved, because `WP.spec (.fail _) _ ↔ False` and `WP.dspec (.fail _) _ ↔ False`, so `aeneasFn a` must be `.ok b` (or `.div` under `dspec`), where the bridge forbids both `.unwound` and `.aborted`.
   - **Leaf panics on an input NOT ruled out by `WP.spec` (e.g., inside `catch_unwind` or with non-trivial `Drop` glue):** Because Charon drops `on_unwind` edges and `Aeneas/Std/Core/Panic.lean` collapses unwind and abort to `.fail .panic`, Aeneas cannot soundly reason about `catch_unwind` recovery or destructor side effects during unwinding. Bridging panicking leaves is sound when callers discharge panic-freedom (`WP.spec`/`WP.dspec`) or compile with `panic=abort`.
   - **Leaf loops infinitely:** Rejected under `WP.spec` (`¬ Diverges` proved by Anneal), permitted under `WP.dspec` provided no UB or panic occurs.

### 4. Lean Toolchain, `module` System, Axiom Hygiene, and Multi-Kernel Composition

`Basis: source + execution`

1. **Aeneas `Std` Axiom Audit (`[source inspection]`):**
   - Across `Aeneas.Std` and `Aeneas.Data.Coinductive` (`CoInd`, `ITree`, `DWP`, `DWLP`, `WP`, `Scalar`, `Slice`, `Array`, `Vec`, `Option`, `CoreResult`, `Ops`), there are **zero** custom axioms in the core functional/WP stack.
   - The only `axiom` declarations in `Aeneas.Std` are:
     - `Aeneas/Std/Slice.lean`: `axiom core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec` (for `opaque core.slice.Slice.get_unchecked`),
     - `Aeneas/Std/Core/Atomic.lean`: `axiom core.sync.atomic.AtomicBool`, `axiom core.sync.atomic.AtomicU32`,
     - `Aeneas/Std/Core/Pin.lean`: `axiom core.pin.Pin`, `axiom core.pin.helper.PinHelper`,
     - `Aeneas/Std/Core/Panic.lean`: `axiom core.panic.panic_info.PanicInfo`.
   - Additionally, `Aeneas/Std/Target.lean` declares `noncomputable opaque target : String` and `noncomputable opaque target_feature_enabled : String → Bool`.
   - Because `leanexport` exports only the transitive dependency cone of target theorem(s), any composed Aeneas + Anneal theorem that avoids those specific declarations stays strictly within Lean's three standard axioms `{propext, Classical.choice, Quot.sound}`.
2. **Mathlib & `module`-System Compatibility (`[source inspection]`):**
   - `AeneasVerif/aeneas@2e3d4488` (`backends/lean/lakefile.lean:5`) requires `mathlib4 @ v4.36.0` and puts `module` headers (`module`, `public import`, `public section`, `@[expose]`) on every `Aeneas.Std.*` file.
   - `google/zerocopy@a007a51a` (`anneal/trusted/lean/`) pins `leanprover/lean4:v4.34.1`, is strictly Mathlib-free (`foundation-lock.json` allowlists only `Init.*` modules and `{propext, Classical.choice, Quot.sound}`), and currently omits `module` headers.
   - Keeping the bridge in an **optional downstream Lake package (`anneal-aeneas-bridge`)** importing both `Trusted` and `Aeneas` keeps core Anneal 100% Mathlib-free and Aeneas-free.
3. **`.olean` Composition vs. Prefix-Relocated Replay vs. Shared Toolchain (`[source inspection]` + `[execution]`):**
   - Lean 4 `.olean` binary files embed the exact compiler version/hash; `Lean.importModules` and `lean4lean` reject cross-minor-version `.olean`s (`incompatible header`).
   - **Shared Lean Toolchain (Primary):** Upgrading Anneal's Lean toolchain to match Aeneas (e.g., `v4.35.0`+ / `v4.36.0`) and adopting `module` headers with `@[expose] public section` on `Trusted.*` enables direct single-environment composition (`lake build` → `leanexport` → `lake check --paranoid`) with zero relocation glue.
   - **Prefix-Relocated Environment Replay (`relocCInfo`):** Rewriting `ConstantInfo` `Name` prefixes before `Lean.Kernel.Environment.replay` at `trustLevel := 0` solves **same-version namespace/symbol collisions** between heterogeneous vendor trees (e.g., two libraries bundling incompatible shims under colliding names). It does **not** bypass cross-minor-version `.olean` binary header incompatibility; cross-version composition without upgrading would require exporting both sides to version-stable `lean4export` NDJSON (`v3.1.0`) and reconciling shared `Init` declarations at the export level.
4. **Independent Multi-Kernel Verification (`lake check --paranoid` on Lean `v4.35.0`) (`[execution]`):**
   - Direct inspection of `leanprover/lean4:v4.35.0` (`bin/` and `lake check --help`) confirms that `v4.35.0` bundles five independent external checkers alongside Lean's default kernel: `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, and `con-ron` (a Rust kernel verified via Aeneas), invoked inside a `bwrap` sandbox via `lake check --paranoid` over `leanexport` NDJSON and failing closed on any non-standard axiom.
   - Executing `support/ToyBridge.lean` on `leanprover/lean4:v4.34.1` (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) exited `0` with `0` errors, `0` warnings, `0` `sorry`, and `#print axioms` reporting:
     - `transfer_wp_spec`, `transfer_wp_dspec`, `overlapping_slices_fail_disjointness`: **no axioms** (`{}`);
     - `split_at_mut_prophecy_sound`: `[propext, Quot.sound]`;
     - `read_u64_refines`, `bitreader_refill_leaf_composed`, `frame_violation_refuted`: `[propext, Classical.choice, Quot.sound]`.

### 5. Where the Bridge Works Cleanly vs. Hard Limits

`Basis: source + derived`

| Pattern | Bridge Support | Technical Mechanism / Blocking Reason |
| :--- | :--- | :--- |
| **Read-only scalar / `&[u8]` / `[T; N]` `unsafe` leaves** (endian codecs, `zerocopy` casts, SIMD pure kernels) | **Clean** | `ValRefines*` + `MemRefinesByteSlice` + `AnnealRefinesAeneas` (`o.callerMem = q.callerMem`). |
| **In-place `&mut [u8]` / multi-slice `unsafe` leaves** (buffer init from `MaybeUninit`, `copy_nonoverlapping`, codecs) | **Clean** | `MemRefinesByteSliceMut` + `DisjointFootprints` + `FramePreserved`. |
| **Borrow-returning slice splitters** (`split_at_mut`, mutable row accessors) | **Clean** | Universal future-mutation prophecy closure over returned disjoint footprints matching Aeneas's `back` closure. |
| **Panicking safe-API leaves** (`assert!`, bounds checks) | **Clean (under `WP.spec`/`WP.dspec` or `panic=abort`)** | `AnnealRefinesAeneas` enforces `WellFormed` on all inputs and `¬ Behavior (.returned _)` on `.fail`; callers discharge preconditions via `WP.spec`. |
| **Capacity-observing `Vec<T>` / `IterMut` across loop steps** | **Requires external wrapper** | `Aeneas.Std.alloc.vec.Vec` erases capacity; Aeneas rejects `IterMut` in pure translation. Needs explicit capacity/cursor ghost state in `FunsExternal.lean`. |
| **Stateless pure `Fn` callback** (`F: Fn(A) -> B`, no `&mut`/interior-mutable captures, proved total/panic-free in Aeneas) | **Tractable with abstract call contract** | Anneal models the callback via an assumed read-only total `FnContract` refining the Aeneas closure `f : A → Result B`. |
| **General re-entrant `FnMut` callbacks** (Anneal `unsafe` code holding raw pointers / `MaybeUninit` calling back into Aeneas closure) | **Hard limit** | Aeneas `FnMut` (`Core/Ops.lean:51-53`) has no heap/aliasing/unwind model (`EffectWP.State := Unit`); re-entrant aliasing, reallocation, or unwinding across raw pointers requires a shared separation-logic/effect-handler interop layer. |
| **Cross-call shared interior mutability (`UnsafeCell`, `RefCell`, `Mutex`, atomics)** | **Hard limit** | Violates Aeneas's pure `&T` immutability assumption; `AtomicBool`/`AtomicU32` are axiomatic types (`Core/Atomic.lean`). (Strictly encapsulated, observationally pure internal scratch state can still hide behind a pure `FunsExternal.lean` signature.) |
| **Custom `#[global_allocator]` or pointer-address-observing APIs** (`ptr as usize`, `ptr::eq`) | **Hard limit** | `Alloc/Alloc.lean:1-2` explicitly excludes custom allocators; Aeneas erases pointer addresses and allocation identities. |

## Boundaries

- **Toy model scope (`known not to apply` as full MIR proof):** `support/ToyBridge.lean` (`[kernel-checked proof]` `[toy model]`) proves the refinement framework, transfer theorems, `read_u64` refinement, `split_at_mut` prophecy closure, and negative counterexamples over compact Mathlib-free miniatures (`AnnealMini` and `AeneasMini`), not against live `Aeneas.Std` (`v4.36.0`) and live `Trusted.MirSemantics` (`v4.34.1`) simultaneously in one build. Live cross-package composition requires aligning both trees onto a single Lean minor version and advancing Anneal's MIR profile beyond profile version 1 (which currently rejects slice/pointer locals and hardcodes `.big` endianness).
- **Safe-caller translation TCB (`known not to apply`):** Proving `AnnealRefinesAeneas` eliminates unverified `FunsExternal.lean` leaf assumptions, but does not verify Charon/Aeneas's translation of the safe caller itself nor `rustc`/LLVM codegen below `Runtime(PostCleanup)` MIR.
- **Unwinding with observable `Drop` / `catch_unwind` (`unsupported` by Aeneas):** Aeneas's `Result.fail .panic` collapses unwinding and aborting and ignores `on_unwind` cleanup edges; bridging leaves that unwind into `catch_unwind` or non-trivial `Drop` glue is unsupported without extending Aeneas's effect model.
- **Live `Aeneas` `v4.36.0` build (`not examined`):** `AeneasVerif/aeneas@2e3d4488` (`v4.36.0` + `mathlib4`) was inspected directly from immutable GitHub commit contents rather than compiled locally, as `leanprover/lean4:v4.36.0` was not installed in the local test environment.
- **Live `lake check --paranoid` execution timing on `support/ToyBridge.lean` (`not examined` inside `v4.34.1` check):** `support/ToyBridge.lean` was kernel-checked directly under `leanprover/lean4:v4.34.1`; `v4.35.0` `lake check --paranoid` capabilities were verified via the installed `v4.35.0` binary CLI (`lake check --help`) and bundled checker inventory (`leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).

## Evidence

1. **Aeneas `Aeneas.Std` and `ITree` WP sources (`2026-11-22`, `source`):**
   - `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f`:
     - `backends/lean/lean-toolchain` (`leanprover/lean4:v4.36.0`) and `backends/lean/lakefile.lean:5` (`require mathlib ... @ "v4.36.0"`).
     - `backends/lean/Aeneas/Std/Primitives.lean:38-89` (`Error`, `RustEffect`, `Result := ITree RustEffect`, `Result.ok/vis/fail/div`, `Result.match`).
     - `backends/lean/Aeneas/Std/WP.lean:31-118` (`effectWP`, `spec := DWP`, `dspec := DWLP`, `spec_dspec`, `spec_ok/fail/div`).
     - `backends/lean/Aeneas/Data/Coinductive/{CoInd,ITree,ITreeWP/DWP,ITreeWP/DWLP,ITreeWP/Taxonomy}.lean`.
     - `backends/lean/Aeneas/Std/Scalar/Core.lean:28-78` (`UScalarTy`, `IScalarTy`, `numBits`, `UScalar`, `IScalar`).
     - `backends/lean/Aeneas/Std/SliceDef.lean:14-45` (`Slice`), `Slice.lean:283-459, 740-765` (`index_mut_usize`, `SliceIndex`, `opaque get_unchecked`, `split_at_mut`).
     - `backends/lean/Aeneas/Std/Array/Array.lean:24-45`, `Alloc/Vec.lean:33-50`, `Alloc/Alloc.lean:1-16`, `Alloc/Boxed.lean:1-35`, `RawPtr.lean:1-32`, `Core/Ops.lean:12-78`, `Core/Panic.lean:1-30`, `Core/Atomic.lean:1-16`, `Target.lean:1-30`, `tests/lean/Slices.lean:1-75`.
2. **Aeneas `jxl-proofs` and `byteorder` external-function specimen (`2026-11-22`, `source`):**
   - `AeneasVerif/jxl-proofs@79ea57c0e9f630e06e9ec3a6d1d61fa9ed50e55d`: `lean/JxlProofs/FunsExternal.lean:17-33` (`byteorder::LittleEndian::read_u64`), `lean/JxlProofs/Funs.lean:84-102` (`BitReader.refill`), `lean/JxlProofs/Proofs.lean:113-137` (`read_u64_spec`, `refill_does_not_panic`).
   - `BurntSushi/byteorder@1.5.0`: `src/lib.rs:1998-2008` (`BigEndian::write_uint` with `unsafe { copy_nonoverlapping }`), `src/lib.rs:2138-2140` (`LittleEndian::read_u64` via `u64::from_le_bytes(buf[..8].try_into().unwrap())`).
3. **Anneal trusted MIR model and semantics (`2026-11-22`, `source`):**
   - `google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1`: `anneal/trusted/lean/lean-toolchain` (`v4.34.1`), `foundation-lock.json` (`axioms`: `Classical.choice`, `Quot.sound`, `propext`), `Trusted/MirAst/{Types,Terminators}.lean`, `Trusted/MirModel.lean:51-190`, `Trusted/MirSemantics/{State,Memory,Bytes,Layout,Step,Boundary}.lean` (specifically `Memory.lean:148-158` zero-size read rule, `Layout.lean:38-46` profile v1 `.big` endianness, `Boundary.lean:55-185` `WellFormed`/`Behavior`/`Diverges`/`BodyVerified`).
4. **Lean `v4.34.1` kernel-checked toy witness and `v4.35.0` checker inspection (`2026-11-22`, `execution`):**
   - Preserved witness: `support/ToyBridge.lean`.
   - Command: `lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/ToyBridge.lean` on `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): exited `0`, `0` warnings, `0` `sorry`, axioms strictly `⊆ {propext, Classical.choice, Quot.sound}`.
   - `leanprover/lean4:v4.35.0`: `lake check --help` and `bin/` listing confirmed bundled `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`, and `leanexport`.

## Revalidation

1. **Re-run the Mathlib-free toy bridge witness (`~3 s`):**
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/anneal-aeneas-lean4-interop-refinement-bridge/support/ToyBridge.lean
   ```
   Confirm exit code `0`, zero warnings, zero `sorryAx`, and `#print axioms` output strictly within `{propext, Classical.choice, Quot.sound}`.
2. **Re-check Aeneas `Std` interface and axiom stability on a newer `AeneasVerif/aeneas` commit:**
   - Diff `backends/lean/lean-toolchain`, `backends/lean/lakefile.lean`, `Aeneas/Std/{Primitives,WP,SliceDef,Slice,Scalar/Core,Core/Panic}.lean`, and grep `^axiom ` across `backends/lean/Aeneas/Std/`.
   - Confirm whether `Result` remains `ITree RustEffect`, whether `WP.spec`/`WP.dspec` retain `spec_fail`/`spec_div`/`dspec` laws, and whether `Aeneas.Std` introduces any new custom axioms in the core functional cone.
3. **Re-check Anneal MIR profile readiness on a newer `google/zerocopy` commit:**
   - Inspect `anneal/trusted/lean/lean-toolchain`, `Trusted/MirModel.lean` (`TerminalOut`, `Val`), `Trusted/MirSemantics/Layout.lean` (`profileTargetEndian`), and `Trusted/MirSemantics/Boundary.lean` (`isSupportedScalarOrUnitTy`) to confirm when target endianness, fat-pointer slices, `TerminalOut.aborted`, and `module` headers land on `main`.
