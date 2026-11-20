# Field-Split Partial `SROA` (`PartialSroaCert`) and `HybridMemoryLens` for Escaping Fields and `UnsafeCell` Sub-Objects

## Summary

In `bidirectional-mir-minissa-refinement-and-anneal-vc-transport` (`NORM-04` `Mem2Reg_NonEscapingSlot`) and `anneal-spec-minissa-normalization-and-proof-compression` (`FunctionalBorrowReturnLens`), scalar promotion required the **entire** local aggregate `_loc: S` to be non-escaping and the **entire** borrowed referent `&T` / `&mut T` to satisfy `T: Freeze`. In systems Rust crates (`tokio`, `zerocopy`, packet parsers, ring buffers, and reference-counted headers), structs routinely combine pure `Freeze` metadata scalars (`len: usize`, `cap: usize`, `flags: u32`, `epoch: u64`) with either an **address-taken buffer field** (`buf: [u8; 64]` passed as `&mut s.buf` to an external callee) or an **interior-mutable field** (`strong: AtomicUsize`, `counter: Cell<u64>`, `waiter: UnsafeCell<Waker>`). By auditing Miri's Tree Borrows implementation (`src/tools/miri/src/borrow_tracker/tree_borrows/{mod.rs,perms.rs,tree.rs}` in `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), executing a **16-case Miri (`-Zmiri-tree-borrows`) sub-field provenance suite** ([`support/run_partial_sroa_miri_probe.py`](support/run_partial_sroa_miri_probe.py), [`support/partial_sroa_miri_16_results.json`](support/partial_sroa_miri_16_results.json)), and mechanizing **`PartialSroaCert` and `HybridMemoryLens`** in Lean `v4.34.1` ([`support/PartialSroaAndHybridMemoryLensProbe.lean`](support/PartialSroaAndHybridMemoryLensProbe.lean)), we establish four governing results:

1. **Exact Tree Borrows Boundary Between Sub-Place Reference Escape (`&mut _loc.buf`) and Root Raw-Pointer Escape (`&raw mut _loc`):**
   - In `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:331-430` and `tree.rs:132-162, 391-455`, retagging a sub-field reference `r = &mut _loc.buf` (or `r = &_loc.buf`) initializes `inside_perms` (`accessed = true`, `ReservedFrz` or `Frozen`) **only** on the field's byte range $[\text{off}(\text{buf}), \text{off}(\text{buf}) + \text{size}(\text{buf}))$.
   - Bytes outside $[\text{off}(\text{buf}), \text{off}(\text{buf}) + \text{size}(\text{buf}))$ (covering sibling scalar fields $f_i \in \mathcal{F}_{\text{reg}}$ such as `_loc.len` and `_loc.cap`) receive `outside_perm` with **`accessed = false`**. Because `LocationState::perform_access` (`tree.rs:157`: `if protected && self.accessed && transition.produces_disabled()`) fires protector errors **only** on `accessed == true` locations:
     - Parent reads and writes to sibling fields $f_i \in \mathcal{F}_{\text{reg}}$ never trigger protector UB on `r = &mut _loc.buf` (even when `r` carries a function-entry `StrongProtector`, verified in `P01`, `P02`, `P03`); and
     - Any parent write to $f_i \in \mathcal{F}_{\text{reg}}$ transitions `r`'s unaccessed `outside_perm` at $f_i$'s byte offsets to `Disabled`, so any subsequent attempt by a callee to reach $f_i$ from `r` via negative byte offset (`container_of!` / `ptr.sub(offset_of!(S, buf))`) triggers immediate Tree Borrows UB (`ChildAccessForbidden(Disabled)` in `P04`, `P05`, `P06`)!
   - Conversely, taking `&raw mut _loc` at the root struct level (`P07`) skips `tb_reborrow` and inherits the parent's `Unique` tag (`accessed = true` across the entire struct allocation), making `container_of!` round-trips between `.buf` and `.len` legal (`PASS` in `P07`). Therefore, `checkPartialSroaCert` enforces `!cert.rootAddressTaken` (`SubplaceRefOnly`), rejecting root raw-pointer escapes (`rootRawPtrContainerOf_blocks_partialSroa_rejected`).
2. **Field-Disjoint Partial `SROA` (`PartialSroaCert`) and `partialSroa_subplaceEscape_bisimExact`:**
   - Partitioning the leaf fields of an aggregate local `_loc: S` into $\mathcal{F}_{\text{reg}}$ (non-escaping, `Freeze`, definitively initialized scalar fields) and $\mathcal{F}_{\text{mem}}$ (address-taken sub-places or `UnsafeCell` fields) with disjoint byte intervals allows `MiniSSA` to promote every $f_i \in \mathcal{F}_{\text{reg}}$ to an SSA register while shrinking the stack memory footprint to $\mathcal{F}_{\text{mem}}$.
   - Whole-struct moves (`_loc2 = move _loc1`, `P08`) and stores to output pointers (`*out_ptr = move _loc1`, `P16`) decompose into register moves on $\mathcal{F}_{\text{reg}}$ paired with a residual memory copy on $\mathcal{F}_{\text{mem}}$.
3. **`HybridMemoryLens` ($\Sigma_{\text{hybrid}}$) for `&StructWithCell` and `&mut StructWithEscapingBuf`:**
   - `mirHybridLens` ([`support/PartialSroaAndHybridMemoryLensProbe.lean`](support/PartialSroaAndHybridMemoryLensProbe.lean#L142-L198)) splits aggregate verification state into a pure SSA register product $R$ (for $\mathcal{F}_{\text{reg}}$) and a residual memory component $M$ (for $\mathcal{F}_{\text{mem}}$), satisfying `get_put`, `put_get`, `put_put`, and strict **frame commutativity** (`hybridMemoryLens_disjoint_frame_commute`: `putReg (putMem st m) r = putMem (putReg st r) m`).
   - For shared references `s: &StructWithCell` (`P09`, `P10`, `P11`), `visit_freeze_sensitive` (`tree_borrows/mod.rs:355-361`) assigns `Permission::Frozen` to $\mathcal{F}_{\text{reg}}$ and `Permission::Cell` to $\mathcal{F}_{\text{mem}}$, so `hybridMemoryLens_freezeField_invariant_across_cellWrite` lifts `s.meta` and `s.payload_len` into loop-invariant SSA scalars across arbitrary `Cell::set` and `AtomicUsize::fetch_add` operations.
4. **`11.82x` Symbolic AST Reduction and `6.65x` Proof LOC Compression Across 6 Hybrid-Memory Benchmarks:**
   - Across 6 realistic hybrid-memory functions (`H01`–`H06` in [`support/hybrid_lens_6_benchmarks.json`](support/hybrid_lens_6_benchmarks.json)), `PartialSroaCert` + `HybridMemoryLens` eliminates **`78.7%` (`47 → 10`)** of memory read/write operations, compresses symbolic `wp` AST nodes by **`11.82x`** (`4,420` $\rightarrow$ `374`), cuts authored Lean 4 proof lines by **`6.65x`** (`226` $\rightarrow$ `34` LOC), and speeds up Lean `v4.34.1` kernel elaboration by **`13.97x`** (`5,140 ms` $\rightarrow$ `368 ms`).

## Applicability

- **Extends:** `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`, `anneal-spec-minissa-normalization-and-proof-compression`, `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`
- **Subjects:**
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)** and **Miri (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `0.1.0`)**: `src/tools/miri/src/borrow_tracker/tree_borrows/{mod.rs,perms.rs,tree.rs}` (`-Zmiri-tree-borrows`).
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel verification of `PartialSroaAndHybridMemoryLensProbe.lean`.
  - **Anneal (`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`)**: $\Sigma_{\text{spec}}$ contract translation for aggregates mixing scalar fields with buffers or `UnsafeCell`.

## Findings

### 1. Tree Borrows Sub-Field Retagging (`inside_perms` vs. `outside_perm`) and the 16-Case Miri Verification Suite

`Basis: source + execution (src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:157-220,331-430, tree.rs:132-162,391-455, support/run_partial_sroa_miri_probe.py, support/partial_sroa_miri_16_results.json)`

When `Runtime(PostCleanup)` MIR evaluates a sub-field borrow `_r = &mut (_loc.2: [u8; 16])` (or `_r = &(_loc.2: [u8; 16])`), `tb_reborrow` (`tree_borrows/mod.rs:238-430`) computes `base_offset = offset_of!(S, buf)` and `ptr_size = size_of::<[u8; 16]>()` and registers a child tag `new_tag` in the allocation's `Tree` (`tree.rs:391-472`) with two distinct permission regions:
1. **Inside $[\text{base\_offset}, \text{base\_offset} + \text{ptr\_size})$ (`inside_perms`):**
   Populated by `visit_freeze_sensitive` (`mod.rs:355-361`) with `LocationState::new_accessed(perm, sifa)` (`accessed = true`), incurring an immediate `AccessCause::Reborrow` access on the parent tag over `range_in_alloc` (`mod.rs:380-395`).
2. **Outside $[\text{base\_offset}, \text{base\_offset} + \text{ptr\_size})$ (`outside_perm` on `Node.default_initial_perm`, `tree.rs:419`):**
   Locations outside the reborrowed sub-field have **no entry** in `loc.perms` initially (lazily initialized with `accessed = false` and `outside_perm = ReservedFrz` for `&mut` or `Frozen`/`Cell` for `&`, `mod.rs:170-207`).

Crucial operational consequence for Field-Disjoint Partial `SROA`:
- Because `accessed == false` on all bytes outside $[\text{base\_offset}, \text{base\_offset} + \text{ptr\_size})$, when the parent function writes to a sibling scalar field `_loc.len` (or when `MiniSSA` logically promotes `_loc.len` out of the memory allocation), that foreign write transitions `new_tag`'s permission at `_loc.len`'s byte offsets from unaccessed `ReservedFrz` to **`Disabled`** (`perms.rs:215`) **without** triggering `TransitionError::ProtectedDisabled` (`tree.rs:157`)!
- Once `_loc.len`'s bytes are `Disabled` for `new_tag`, any attempt by `callee(_r)` to compute a negative byte offset `(r as *mut u8).sub(offset_of!(S, buf))` (`container_of!`) and read or write `_loc.len` immediately fails with `TransitionError::ChildAccessForbidden(Disabled)` (`P04`, `P05`).
- Note also the `Runtime(PostCleanup)` MIR distinction between `PlaceMention` (`let _ = (*alias).meta;`, which performs **zero** memory read in Miri) and an actual `Load` (`let v = (*alias).meta;`, which performs a `Foreign Read` and sets `ReservedFrz { conflicted: true }` on a protected `&mut WithCell`, verified in `P12`).

Table 1 summarizes all 16 Miri (`0.1.0`, `-Zmiri-tree-borrows`) litmus tests in [`support/partial_sroa_miri_16_results.json`](support/partial_sroa_miri_16_results.json):

| Case ID | Category | Tested Program Pattern | Expected | Miri (`-Zmiri-tree-borrows`) | Key Tree Borrows Mechanism Verified |
| :--- | :--- | :--- | :---: | :---: | :--- |
| **`P01`** | `SubplaceRefOnly` | `fill_buf(&mut p.buf)` while parent mutates `p.len`, `p.cap` | `PASS` | **`PASS`** | Sibling scalar accesses lie outside `p.buf` byte range |
| **`P02`** | `SubplaceRefOnly` | Live `r = &h.buf` while parent mutates `h.len += 10`, `h.flags \|= 2` | `PASS` | **`PASS`** | Foreign write to unaccessed `outside_perm` sets `Disabled` on `h.len` without invalidating `Frozen` on `h.buf` |
| **`P03`** | `SubplaceRefOnly` | `update_both(&mut s.len, &mut s.buf)` with two `FnEntry` protectors | `PASS` | **`PASS`** | `tree.rs:157` (`self.accessed` guard) allows disjoint protected `&mut` fields in one allocation |
| **`P04`** | `ContainerOfHazard` | `r = &mut s.buf`; parent writes `s.len = 2`; `r` reads `s.len` via `sub(offset_of!)` | `UB` | **`UB`** | Parent write transitions `r`'s `outside_perm` at `s.len` to `Disabled` (`read access ... is forbidden`) |
| **`P05`** | `ContainerOfHazard` | `sneaky_callee(&s.len, &mut s.buf)` writes `s.len` via `sub(offset_of!)` from `buf_ref` | `UB` | **`UB`** | Violates `StrongProtector` on `len_ref: &usize` (`write access ... is forbidden`) |
| **`P06`** | `ContainerOfHazard` | `r = &s.buf` writes sibling `s.len` via `sub(offset_of!)` | `UB` | **`UB`** | `outside_perm` on shared `&[u8; 8]` is `Frozen` (`ChildAccessForbidden(Frozen)`) |
| **`P07`** | `RootAddressTaken` | `root_ptr = &raw mut s` offsets to `.buf` and back to `.len` | `PASS` | **`PASS`** | Root `&raw mut s` inherits `Unique` across all of `S` (blocks Partial `SROA`!) |
| **`P08`** | `SubplaceRefOnly` | Whole-struct move `let f2 = f1;` after `touch(&mut f1.data)` | `PASS` | **`PASS`** | Field-wise register move + buffer copy preserves aggregate value |
| **`P09`** | `HybridCellLens` | `s: &WithCell` caches `s.meta` and `s.tail` across `s.counter.set(...)` | `PASS` | **`PASS`** | `visit_freeze_sensitive` marks `meta`/`tail` `Frozen` and `counter` `Cell` |
| **`P10`** | `HybridCellLens` | `r: &WithCell` cast to `*mut u64` writes `Freeze` field `meta` | `UB` | **`UB`** | Bytes `[0..8)` have `Permission::Frozen` despite sibling `Cell<u64>` |
| **`P11`** | `HybridCellLens` | `a: &ArcInnerLike` caches `payload_len` across `strong.fetch_add(1)` | `PASS` | **`PASS`** | Atomic RMW on `UnsafeCell` bytes `[0..16)` preserves `Frozen` payload bytes `[16..32)` |
| **`P12`** | `HybridCellLens` | `callee_mut(x: &mut WithCell, alias)` reads `(*alias).meta` then writes `x.meta = 42` | `UB` | **`UB`** | `FnEntry` `&mut WithCell` uses `ReservedFrz` on all bytes; foreign read sets `conflicted = true` |
| **`P13`** | `HybridMutBorrowLens` | `PacketBuilder` updates `pos` in register and passes `&mut pb.data[p..p+2]` | `PASS` | **`PASS`** | Subslice reborrow of `pb.data` is disjoint from `pb.pos` and `pb.cap` |
| **`P14`** | `SubplaceRefOnly` | Nested `Outer { seq, inner: Inner { tag, buf } }` with `&mut o.inner.buf` | `PASS` | **`PASS`** | Recursive leaf partitioning promotes `o.seq` and `o.inner.tag` |
| **`P15`** | `SubplaceRefOnly` | Tuple `(u64, [u8; 8], u64)` with `touch_arr(&mut t.1)` | `PASS` | **`PASS`** | Positional tuple scalars `.0` and `.2` promoted to SSA registers |
| **`P16`** | `SubplaceRefOnly` | `#[repr(C)] struct WithPad` reconstituted into `out_ptr.write(s)` | `PASS` | **`PASS`** | Partial `SROA` reconstitution into destination memory pointer |

---

### 2. Lean 4.34.1 Mechanization of `PartialSroaCert` and `HybridMemoryLens`

`Basis: execution (support/PartialSroaAndHybridMemoryLensProbe.lean)`

[`support/PartialSroaAndHybridMemoryLensProbe.lean`](support/PartialSroaAndHybridMemoryLensProbe.lean) (`247` lines, checked in `708.22 ms` with **`0` `sorryAx`** and **`0` `Lean.ofReduceBool`**) mechanizes `checkPartialSroaCert`, `mirHybridLens`, and four core theorems:

| Theorem Name | Property Established | Steps (MIR $\rightarrow$ `MiniSSA`) | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :---: | :--- |
| `partialSroa_subplaceEscape_bisimExact` | Promoting $\mathcal{F}_{\text{reg}}$ to SSA registers while $\mathcal{F}_{\text{mem}}$ escapes via `&mut s.buf` is an exact safety-preserving bisimulation when `checkPartialSroaCert cert = true` | `7 → 3` (`2.33x` fewer steps) | `[propext]` |
| `hybridMemoryLens_disjoint_frame_commute` | `putReg` on $\mathcal{F}_{\text{reg}}$ and `putMem` on $\mathcal{F}_{\text{mem}}$ commute strictly and preserve orthogonal `getMem`/`getReg` projections | $O(1)$ (`rfl`) | **None (`[]`)** |
| `hybridMemoryLens_freezeField_invariant_across_cellWrite` | Interior-mutable writes (`TbFieldPerm.cell`) to $\mathcal{F}_{\text{mem}}$ preserve all `Freeze` SSA scalars (`TbFieldPerm.frozen`) in $\mathcal{F}_{\text{reg}}$ | $O(1)$ (`rfl`) | **None (`[]`)** |
| `rootRawPtrContainerOf_blocks_partialSroa_rejected` | Rejects Partial `SROA` (`checkPartialSroaCert = false`) when `rootAddressTaken = true` (`&raw mut _loc`), preventing stale register reads after `container_of!` mutation (`109` vs. `10`) | Counterexample witness | **None (`[]`)** |

---

### 3. Proof-Compression Benchmark Across 6 Hybrid-Memory Functions (`H01`–`H06`)

`Basis: execution + derived (support/hybrid_lens_6_benchmarks.json)`

Table 2 reports the proof complexity reduction across 6 functions whose structs combine scalar fields with escaping buffers or `Atomic`/`Cell` fields:

| ID | Function | Aggregate Structure ($\mathcal{F}_{\text{reg}} \times \mathcal{F}_{\text{mem}}$) | Mem Ops (Before $\rightarrow$ After) | `wp` AST Nodes (Before $\rightarrow$ After) | Proof LOC (Before $\rightarrow$ After) | Elab Time (`ms`, Before $\rightarrow$ After) |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: |
| **`H01`** | `RingBuffer::push_slice` | `{ head, tail, cap } × { buf: [u8; 64] }` | `9 → 2` | `840 → 72` (`11.7x`) | `42 → 6` (`7.0x`) | `980 → 68` (`14.4x`) |
| **`H02`** | `PacketCursor::advance_and_copy` | `{ pos, limit } × { scratch: [u8; 32] }` | `7 → 1` | `690 → 58` (`11.9x`) | `36 → 5` (`7.2x`) | `810 → 59` (`13.7x`) |
| **`H03`** | `ArcHeader::increment_strong_if_valid` | `{ payload_len, flags } × { strong, weak: AtomicUsize }` | `8 → 2` | `760 → 64` (`11.9x`) | `38 → 6` (`6.3x`) | `890 → 62` (`14.4x`) |
| **`H04`** | `SmallBuf::append_byte` | `{ len, inline_cap } × { storage: [u8; 16] }` | `6 → 1` | `580 → 50` (`11.6x`) | `30 → 5` (`6.0x`) | `670 → 52` (`12.9x`) |
| **`H05`** | `CellCounterWithConfig::tick` | `{ step, max } × { count: Cell<u64> }` | `7 → 2` | `640 → 54` (`11.9x`) | `34 → 5` (`6.8x`) | `740 → 56` (`13.2x`) |
| **`H06`** | `FramedHeader::parse_into_scratch` | `{ magic, payload_len, epoch } × { raw_hdr: [u8; 16] }` | `10 → 2` | `910 → 76` (`12.0x`) | `46 → 7` (`6.6x`) | `1,050 → 71` (`14.8x`) |
| **Total** | **6 Hybrid-Memory Workloads** | **Escaping Sub-Buffers & `Atomic`/`Cell` Fields** | **`47 → 10` (`4.70x`)** | **`4,420 → 374` (`11.82x`)** | **`226 → 34` (`6.65x`)** | **`5,140 → 368` (`13.97x`)** |

## Boundaries

1. **Root-Level Raw Pointer Address Capture (`&raw mut _loc` / `addr_of_mut!(_loc)`) (`known not to apply` for `PartialSroaCert`):**
   - As established by Miri test `P07` and theorem `rootRawPtrContainerOf_blocks_partialSroa_rejected`, taking a raw pointer to the root aggregate `_loc` grants provenance over the entire struct allocation without creating a sub-range child node in Tree Borrows. Any local with root raw-pointer address capture must keep all fields accessible through that provenance in memory.
2. **Overlapping `union` Fields and Enum Variants With Conflicting `Freeze` Layouts (`known not to apply` without active-variant domination):**
   - `PartialSroaCert` requires `byteRangesDisjoint = true` between $\mathcal{F}_{\text{reg}}$ and $\mathcal{F}_{\text{mem}}$. Overlapping `union` fields or enum variants where a `Freeze` scalar overlaps an address-taken buffer at the same byte offset cannot be unconditionally split across the whole function body.

## Evidence

1. **Kernel-Checked Lean 4.34.1 Mechanization:**
   - [`support/PartialSroaAndHybridMemoryLensProbe.lean`](support/PartialSroaAndHybridMemoryLensProbe.lean): Proves `partialSroa_subplaceEscape_bisimExact`, `hybridMemoryLens_disjoint_frame_commute`, `hybridMemoryLens_freezeField_invariant_across_cellWrite`, and `rootRawPtrContainerOf_blocks_partialSroa_rejected` in `708.22 ms` (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
2. **16-Case Miri Tree Borrows Suite and 6-Function Benchmark Dataset:**
   - [`support/run_partial_sroa_miri_probe.py`](support/run_partial_sroa_miri_probe.py)
   - [`support/partial_sroa_miri_16_results.json`](support/partial_sroa_miri_16_results.json)
   - [`support/hybrid_lens_6_benchmarks.json`](support/hybrid_lens_6_benchmarks.json)
3. **`rustc 1.99.1` Miri Source Coordinates (`58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:157-220, 238-430` (`NewPermission::new`, `tb_reborrow`, `visit_freeze_sensitive`)
   - `src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:132-162, 391-455` (`LocationState::perform_access`, `Tree::new_child`)

## Revalidation

Run the Miri Tree Borrows probe and Lean `v4.34.1` checker:

```bash
python3 reports/partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses/support/run_partial_sroa_miri_probe.py
```
