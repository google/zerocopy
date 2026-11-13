# Relational Memory Lenses, Tree Borrows Footprint Preservation, and Provenance-Directed Nondeterministic Allocation Scaling in Lean 4

## Summary

Symbolic verification of Rust programs over a canonical byte-level Miri memory
model (`List AbsByte` with per-allocation Tree Borrows state `BorrowTree` and
demonic `StepResult.choice` base-address allocation) faces two potential kernel
scaling bottlenecks in Lean 4:

1. **Byte-Slice and Borrow-Tree Reduction Over Symbolic Values**: Directly
   unfolding byte-slice reads/writes (`readSlice`, `writeSlice`) and Tree
   Borrows range accesses (`BorrowTree.performAccessRange`) over universally
   quantified inputs (`∀ x y z : UInt32`) fails or scales superlinearly for two
   reasons:
   - **Standard-Library `simp` Byte-0 Asymmetry**: Lean 4's default `@[simp]`
     set includes `UInt32.shiftRight_zero : a >>> 0 = a`,
     `UInt32.toUInt8_add : (a + b).toUInt8 = a.toUInt8 + b.toUInt8`, and
     `UInt32.toUInt8_xor`. When `encodeU32LE (v + dx)` is unfolded, `simp`
     distributes `.toUInt8` over `+` and `^^^` on byte 0 (`v.toUInt8 + dx.toUInt8`)
     while leaving bytes 1–3 as shifted expressions `((v + dx) >>> 8).toUInt8`.
     This breaks the 4-byte `packU32` roundtrip pattern (`packU32_extract`),
     causing each subsequent read-modify-write step to substitute an uncollapsed
     `packU32` term into 4 new byte extractions ($O(4^K)$ AST blowup) and
     failing to prove the functional postcondition even at $K = 1$.
   - **WHNF Cache Bypass Under Free Variables (`hasFVar == true`)**: Even when
     `UInt32.toUInt8_add` and `UInt32.toUInt8_xor` are excluded from `simp`,
     reducing `writeSlice`, `readSlice`, and `BorrowTree.performAccessRange`
     (4 tree nodes × 8 bytes × 4 accesses/step = 128 `LocationState` transitions
     per step) inside a context containing free variables bypasses Lean 4's
     `whnfCore` cache. At $K = 30$ sequential mutations, direct unfolding takes
     **26,596.42 ms** (**3.57 GB** peak RSS) on Lean `v4.28.0-rc1` and
     **14,672.92 ms** (**2.32 GB** peak RSS) on Lean `v4.34.1`.
   - **Relational Lens Solution (`TypedAt` + `FootprintAt`)**: Representing both
     byte arrays (`List AbsByte`) and per-node Tree Borrows location arrays
     (`List LocationState`) via contiguous slice operations `readSlice` and
     `writeSlice` allows two foundational slice laws (`readSlice_writeSlice_same`
     and `readSlice_writeSlice_disjoint`) to power both typed value lenses
     (`read_write_same`, `read_write_disjoint`, `typedAt_transmute`) and
     range-wise Tree Borrows footprint preservation
     (`footprintAt_preserve_local_write`, `footprintAt_preserve_disjoint_write`,
     `footprintAt_preserve_foreign_read`). Discharging initial
     `HasUniqueWritePerm` by reflection (`by decide`) once at function entry via
     `checkUniqueWritePerm_sound` (~10 ms) and preserving `TypedAt` and
     `HasUniqueWritePerm` compositionally across writes reduces $K = 30$
     symbolic mutations to **79.26 ms** (unrolled CPS, **335.6x speedup**) and
     **23.57 ms** (inductive schedule engine, **1,128.4x speedup**) on Lean
     `v4.28.0-rc1`, and **54.78 ms** (**267.8x speedup**) / **17.37 ms**
     (**844.7x speedup**) on Lean `v4.34.1`.

2. **Pairwise Address-Disjointness ($O(N^2)$) Under Demonic `baseAddr` Choice**:
   When stack allocations choose a fresh `baseAddr : Nat` via demonic
   nondeterminism (`Comp.choice { baseAddr // ValidFreshBaseAddr as size align baseAddr }`),
   resolving memory accesses by raw virtual address would force every load and
   store to prove `baseAddr_i ≠ baseAddr_j` across all $N$ live allocations
   ($\Theta(N^2)$ `omega` obligations).
   - **Provenance-Directed Offset Cancellation**: Routing allocations by
     provenance (`ptr.prov = some ⟨allocId, tag⟩`) and resolving intra-allocation
     offsets via subtraction (`ptr.addr.toNat - alloc.baseAddr`) cancels
     `(UInt64.ofNat baseAddr + UInt64.ofNat relOff).toNat - baseAddr = relOff`
     (`resolveOffset_offsetPtr_rootPtr`) using *only* the single local
     non-overflow bound `baseAddr + totalSize < 2^64` (`ValidLocalBaseAddr`) and
     **zero** pairwise comparisons `baseAddr_i ≠ baseAddr_j`.
   - **Bounded Slack Window for Inductively Satisfiable `Nonempty`**: To prove
     `Nonempty { baseAddr // ValidFreshBaseAddr as size align baseAddr }` across
     $N$ sequential demonic choices without global address-space fragmentation
     analysis, `ValidFreshBaseAddr` must bound the adversary's choice above the
     high-water mark (`baseAddr ≤ maxEndAddrList as + align + 16`, matching
     `Miri.Memory.AllocAddresses.AddressGenerator.generate` in
     `proofs-rs/lean-miri`). With this slack window, `wp_forceAllocation_choice`
     threads a single scalar bound `maxEndAddrList as ≤ bound`, discards
     `DisjointFromAllLive` immediately, and verifies $N = 10$ nondeterministic
     stack allocations + stores + loads (`wp_ten_nondet_stack_allocs`) in
     **54.80 ms** (`v4.28.0-rc1`) / **34.83 ms** (`v4.34.1`) with zero
     pairwise address-disjointness proofs.

## Applicability

- **Examined Subjects and Relationship**:
  - `leanprover/lean4` at `3b0f2862196c6a8af9eb0025ee650252694013dd`
    (`v4.28.0-rc1`) and `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):
    Used to elaborate, kernel-check, and benchmark all mechanized definitions,
    theorems, and scaling probes in
    [support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean).
  - `proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`:
    Provides the reference Lean 4 formalization of Miri's allocation storage,
    initialization mask, and provenance map
    (`Miri/Memory/{Allocation,InitMask,ProvenanceMap}.lean`), pointer and
    allocation identities (`Miri/Memory/Identity.lean`), Tree Borrows
    permissions, location states, retag policies, traversal schedules, and
    protector release
    (`Miri/TreeBorrows/{Permissions,LocationState,RetagPolicy,Traversal,TreeState,GlobalState}.lean`),
    and monotonic address generation and provenance-directed allocation lookup
    (`Miri/Memory/AllocAddresses/{AddressGenerator,GlobalState}.lean` and
    `Miri/Memory/Access.lean`).
  - `rust-lang/miri` at `7fa591d7d4dd9af8154becbc8332f8096f8323b1`:
    Provides the upstream Rust implementation of Tree Borrows initial retag
    permissions (`src/borrow_tracker/tree_borrows/mod.rs:193-197`) and transition
    tables (`src/borrow_tracker/tree_borrows/perms.rs`).
- **Shared vs. Version-Specific Behavior**:
  - All mathematical definitions, lens theorems, Tree Borrows state transitions,
    and `UInt32` `@[simp]` lemma interactions behave identically across Lean
    `v4.28.0-rc1` and `v4.34.1` with zero source modifications.
  - Elaboration and kernel verification times are uniformly ~25–45% faster on
    Lean `v4.34.1` than on `v4.28.0-rc1`, while the asymptotic scaling gap
    between direct unfolding (Approach A) and relational lens rewriting
    (Approach B) holds on both toolchains (**335.6x–1,128.4x** at $K = 30$ on
    `v4.28.0-rc1`; **267.8x–844.7x** at $K = 30$ on `v4.34.1`).
- **Execution Environment for Benchmarks**:
  - Benchmarks were executed on Linux x86_64 under
    `anneal-lean-run --mode file --concurrency 4 -- lean -j1` using in-process
    monotonic nanosecond timestamps (`IO.monoNanosNow`) and `/usr/bin/time`
    for peak resident set size (RSS). Absolute timings vary with host CPU speed,
    whereas `maxHeartbeats` margins, AST growth rates ($O(4^K)$ vs. $O(K)$ vs.
    $O(1)$), and `simp` rewrite behavior are machine-independent properties of
    the examined Lean 4 revisions.

## Findings

### 1. Unified Contiguous Slice Algebra (`readSlice` / `writeSlice`) Over `List AbsByte` and `BorrowTree`

Basis: `source` + `execution` + `derived`

Both byte-level allocation storage (`Allocation.bytes : List AbsByte`) and
per-node Tree Borrows location arrays (`TreeNode.locs : List LocationState`)
support range reads and range updates through two list operations
([support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
lines `75–81`):

```lean
def readSlice (xs : List α) (off sz : Nat) : List α :=
  (xs.drop off).take sz

def writeSlice (xs : List α) (off : Nat) (val : List α) : List α :=
  xs.take off ++ val ++ xs.drop (off + val.length)
```

Four polymorphic lemmas over `readSlice` and `writeSlice`
([support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
lines `93–199`) discharge all structural list reasoning once and for all:

1. `writeSlice_length`: If `off + val.length ≤ xs.length`, then
   `(writeSlice xs off val).length = xs.length`.
2. `readSlice_length`: If `off + sz ≤ xs.length`, then
   `(readSlice xs off sz).length = sz`.
3. `readSlice_writeSlice_same`: If `val.length = sz` and `off + sz ≤ xs.length`,
   then `readSlice (writeSlice xs off val) off sz = val`.
4. `readSlice_writeSlice_disjoint`: If `off₁ + val.length ≤ xs.length`,
   `off₂ + sz₂ ≤ xs.length`, and `off₁ + val.length ≤ off₂ ∨ off₂ + sz₂ ≤ off₁`,
   then `readSlice (writeSlice xs off₁ val) off₂ sz₂ = readSlice xs off₂ sz₂`.

Because both `Memory.writeTyped` and `BorrowTree.performAccessRange` update
slices via `writeSlice`, these four lemmas simultaneously yield the value-level
lens theorems (`read_write_same`, `read_write_disjoint`) and the permission-level
Tree Borrows footprint preservation theorems
(`footprintAt_preserve_local_write`, `footprintAt_preserve_disjoint_write`,
`footprintAt_preserve_foreign_read`).

### 2. `LayoutCodec` Instances, Pointer Provenance Conservation, and Bit-Level Transmutation (`TransmuteAs`)

Basis: `source` + `execution`

In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, per-allocation
memory state is split across three parallel structures in
`Miri/Memory/Allocation.lean:164-174` (`rawBytes : Array UInt8`),
`Miri/Memory/InitMask.lean` (`initMask : InitMask`), and
`Miri/Memory/ProvenanceMap.lean:17-41` (`PointerFrag` and `ProvenanceMap`).
[support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
(lines `61–74`, `202–438`) unifies those three per-byte components into a single
per-byte cell type `AbsByte` (`uninit` vs. `init (byte : UInt8) (frag : Option ByteProvFrag)`)
and defines `LayoutCodec` over `List AbsByte`:

```lean
structure ByteProvFrag where
  prov : Provenance
  byteIdx : UInt8
  deriving DecidableEq, Repr, Inhabited

inductive AbsByte where
  | uninit
  | init (byte : UInt8) (frag : Option ByteProvFrag)
  deriving DecidableEq, Repr, Inhabited

structure LayoutCodec (α : Type) where
  size : Nat
  encode : α → List AbsByte
  decode : List AbsByte → Option α
  encode_len : ∀ v : α, (encode v).length = size
  decode_encode : ∀ v : α, decode (encode v) = some v
```

Four concrete codec families and a cross-codec transmutation relation are
mechanized:

- **Integer Codecs (`u32Codec`, `u64Codec`, lines `210–316`)**: Little-endian
  4-byte and 8-byte encodings with provenance fragment `none`. Roundtrip
  correctness (`packU32_extract`, `packU64_extract`) is proved in <25 ms via
  `bv_decide` on `UInt32.toBitVec` / `UInt64.toBitVec`.
- **Thin-Pointer Codec (`ptrCodec`, lines `318–371`)**: Encodes
  `ThinPtr := ⟨addr : UInt64, prov : Option Provenance⟩` into 8 little-endian
  bytes where byte $i \in \{0, \dots, 7\}$ carries `frag = prov.map (⟨·, i⟩)`.
  `decodePtrLE` reconstructs `prov = some p` only if all 8 bytes carry
  matching `some ⟨p, 0⟩ .. some ⟨p, 7⟩` fragments; if all 8 bytes carry `none`,
  it decodes `prov = none`; any partial or mixed provenance overwrite returns
  `none` (preventing forged pointer provenance).
- **Composite Struct/Pair Codec (`pairCodec`, lines `373–408`)**: Composes any
  two codecs `c₁ : LayoutCodec α` and `c₂ : LayoutCodec β` into a codec of size
  `c₁.size + c₂.size` via list concatenation (`c₁.encode v.1 ++ c₂.encode v.2`)
  and slice splitting (`xs.take c₁.size`, `xs.drop c₁.size`).
- **Bit-Pattern Reinterpretation (`TransmuteAs`, lines `410–438`, `1276–1291`)**:
  ```lean
  def TransmuteAs (c1 : LayoutCodec α) (c2 : LayoutCodec β) (v1 : α) (v2 : β) : Prop :=
    c1.size = c2.size ∧ c1.encode v1 = c2.encode v2
  ```
  `transmute_u32_pair_u64` proves that `pairCodec u32Codec u32Codec` at `(lo, hi)`
  has the exact same 8-byte `List AbsByte` representation as `u64Codec` at
  `combineU32ToU64 lo hi = lo.toUInt64 ||| (hi.toUInt64 <<< 32)`, and
  `typedAt_transmute` reinterprets `TypedAt c1 mem allocId off v1` into
  `TypedAt c2 mem allocId off v2` without re-reading or unfolding individual
  bytes.

### 3. Five-Constructor Tree Borrows Permission Model, Entry Retag Invariant, and Footprint Preservation

Basis: `source` + `execution` + `derived`

#### A. Bijection with `proofs-rs/lean-miri` and `rust-lang/miri` Permissions

In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
(`Miri/TreeBorrows/Permissions.lean:19-32`), `Miri.TreeBorrows.Permission`
has 6 constructors (`Cell`, `ReservedFrz (conflicted : Bool)`, `ReservedIM`,
`Unique`, `Frozen`, `Disabled`), already parameterizing `ReservedFrz` by
`conflicted : Bool` and naming the active state `Unique`.
[support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
(lines `443–489`) mirrors this 6-constructor type as `LeanMiriPermission`
(naming `Unique` as `Active`) and factors `ReservedFrz (conflicted : Bool)` and
`ReservedIM` by `tyIsFreeze : Bool` and `conflicted : Bool` into the
5-constructor `Permission` type:

```lean
inductive Permission where
  | Reserved (tyIsFreeze : Bool) (conflicted : Bool)
  | Active
  | Frozen
  | Cell
  | Disabled
  deriving DecidableEq, Repr, Inhabited
```

`leanMiriPermission_roundtrip` (lines `485–488`) proves that `toPermission` and
`toLeanMiriPermission` form a roundtrip bijection on `LeanMiriPermission`:
- `.Reserved true false` $\leftrightarrow$ `.ReservedFrz false`
- `.Reserved true true` $\leftrightarrow$ `.ReservedFrz true`
- `.Reserved false false` $\leftrightarrow$ `.ReservedIm` (`ReservedIM` in `Miri/TreeBorrows/Permissions.lean:25`)
- `.Active` $\leftrightarrow$ `.Active` (`Unique` in `Miri/TreeBorrows/Permissions.lean:27`),
  `.Frozen` $\leftrightarrow$ `.Frozen`, `.Cell` $\leftrightarrow$ `.Cell`,
  `.Disabled` $\leftrightarrow$ `.Disabled`.

#### B. Function-Entry (`FnEntry`) Protected `&mut T` Initialization Invariant

In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
(`Miri/TreeBorrows/Permissions.lean:67-99, 299-308`) and
`rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`
(`src/borrow_tracker/tree_borrows/perms.rs`), a protected `ReservedIM` state is
an unreachable invariant violation: `foreignRead` (lines `75–77`), `foreignWrite`
(lines `96–98`), and `Permission.strongestIdempotentForeignAccess` (lines
`299–308`) all return `.ImpossibleProtectedReservedIM` whenever
`state = .ReservedIM` and `isProtected = true` (while `childWrite` in
`Miri/TreeBorrows/Permissions.lean:82-92` maps `.ReservedIM => .Transition .Unique`,
and the probe's `Option`-valued `childWrite` at lines `515–523` also guards
`.Reserved false _` with `if isProtected then none else some .Active`).

Both `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`
(`src/borrow_tracker/tree_borrows/mod.rs:193-197`) and
`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
(`Miri/TreeBorrows/RetagPolicy.lean:56-59, 77-79`) enforce this invariant at
retag time by computing the initial permission for mutable references via:

```lean
if isProtected || frozen then .ReservedFrz false else .ReservedIM
```

and rejecting protected `ReservedIM` states in
`RetagPolicy.initialLocationState` with `InitialStateError.protectedReservedIM`
(`Miri/TreeBorrows/RetagPolicy.lean:99, 108-110`). Therefore, on function-entry
retags (`RetagMode.FnEntry`, where `isProtected == true`), every byte of a
protected `&mut T` or `Box<T>` parameter is initialized to
`Permission.Reserved true false` (`ReservedFrz false`), **even when `T` contains
`UnsafeCell` (`!Freeze`)**.

#### C. Two-Phase Entry Reflection and Inductive Footprint Preservation

Rather than re-evaluating `BorrowTree.performAccessRange` across all nodes and
bytes on every symbolic mutation,
[support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
(lines `612–1092`) factors Tree Borrows reasoning into:

1. **Entry Reflection (`checkUniqueWritePerm_sound`, lines `796–818`)**:
   At function entry, the initial `BorrowTree` has a concrete topology and
   concrete initial permissions. `checkUniqueWritePerm tree prot tag off sz`
   evaluates to `true` by kernel reduction (`by decide` in ~10 ms; see
   `entry_hasUniqueWritePerm_field0` and `entry_hasUniqueWritePerm_field1` at
   lines `1635–1647`), producing a `HasUniqueWritePerm tree prot tag off sz`
   witness.
2. **Compositional Write Preservation (`footprintAt_preserve_local_write`, lines `849–875`, and `footprintAt_preserve_disjoint_write`, lines `932–952`)**:
   - `locWritePerm rel isProt st` holds when a location `st` can undergo a
     `Write` access with relatedness `rel` without UB *and* transitions to a
     state `st'` that again satisfies `locWritePerm rel isProt st'` (specifically:
     for `.LocalAccess`, `st.perm ∈ {.Reserved true b, .Active, .Cell}` transitions
     to `.Active` or `.Cell` with `accessed = true`; for `.ForeignAccess`, either
     `!isProt` and `st.perm` transitions to `.Disabled`/`.Cell`/`.Reserved false false`,
     or `isProt` and `st.perm ∈ {.Disabled, .Cell}`).
   - `footprintAt_preserve_local_write` lifts `locWritePerm_step` through
     `readSlice_writeSlice_same` to prove that `tree.performAccessRange prot tag off sz .Write`
     succeeds (`= some tree'`), sets `tag` and its ancestors to `Active`
     (`accessed = true`) on `[off, off + sz)`, and preserves
     `HasUniqueWritePerm tree' prot tag off sz`.
   - `footprintAt_preserve_disjoint_write` lifts `readSlice_writeSlice_disjoint`
     to prove that a write through `tag₁` on `[off₁, off₁ + sz₁)` preserves
     `HasUniqueWritePerm tree' prot tag₂ off₂ sz₂` on any disjoint byte range
     `off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁`.
3. **Compositional Read Preservation (`footprintAt_preserve_foreign_read`, lines `1063–1092`, and `footprintAt_preserve_local_read_of_writePerm`, lines `989–1010`)**:
   - Proves that `HasSharedReadPerm tree prot sharedTag readerTag off sz` is
     preserved by `tree.performAccessRange prot readerTag off sz .Read`, and
     that `HasUniqueWritePerm tree prot tag off sz` permits local `.Read`
     accesses without losing `HasUniqueWritePerm`.

### 4. Kernel Scaling Comparison Across $K = 1..30$ Sequential Symbolic Mutations

Basis: `execution` + `derived`

Section 5 of
[support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
(lines `1597–2143`) and
[support/run_benchmarks.py](support/run_benchmarks.py) benchmark a symbolic
read-modify-write loop over an 8-byte `(UInt32, UInt32)` struct in memory with
a 4-node `BorrowTree` (`tag 0` root `Active`, `tag 1` caller `Active`, `tag 2`
protected callee `Reserved true false`, `tag 3` sibling `Disabled`). Each step
`stepPairMut mem dx dy` performs two Tree Borrows `.Read` accesses, one `.Write`
access to field 0 (`v0' = v0 + dx`), two `.Read` accesses to fields 0 and 1, and
one `.Write` access to field 1 (`v1' = v0' ^^^ v1 ^^^ dy`) over universally
quantified `x y z : UInt32`.

#### A. Why Default `simp` Unfolding (Approach A1) Fails at $K = 1$

In Lean 4 (`v4.28.0-rc1` and `v4.34.1`), `encodeU32LE v` produces:

```lean
[ .init (v >>> 0).toUInt8 none
, .init (v >>> 8).toUInt8 none
, .init (v >>> 16).toUInt8 none
, .init (v >>> 24).toUInt8 none ]
```

Because `UInt32.shiftRight_zero`, `UInt32.toUInt8_add`, and `UInt32.toUInt8_xor`
are default `@[simp]` lemmas, running `simp` on `encodeU32LE (x + dx)` rewrites
byte 0 from `((x + dx) >>> 0).toUInt8` to `x.toUInt8 + dx.toUInt8`, while
leaving bytes 1–3 as `((x + dx) >>> 8).toUInt8`, `((x + dx) >>> 16).toUInt8`,
and `((x + dx) >>> 24).toUInt8`. When `decodeU32LE` applies `packU32 b0 b1 b2 b3`,
byte 0 no longer shares the uniform pattern `(v >>> 0).toUInt8`, so
`packU32_extract` fails to fire. At step $k + 1$, the uncollapsed `packU32`
expression is substituted into 4 new shifts, creating $4^K$ leaf byte-extractions
and failing to prove `mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1`
even for $K = 1$.

#### B. Why Custom `simp` Unfolding (Approach A2) Scales Superlinearly

Passing `simp [-UInt32.toUInt8_add, -UInt32.toUInt8_xor, packU32_extract_simp, ...]`
(where `packU32_extract_simp` matches `packU32 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v`)
restores the 4-byte `packU32` roundtrip collapse. However, because `mkEntryMemory x y`
and every intermediate `Memory` state contain free variables `x y z : UInt32`,
every surrounding term has `hasFVar == true`. In Lean 4's kernel and elaborator,
`whnfCore` does not cache reductions of expressions with `hasFVar == true`.
Consequently, unfolding `writeSlice`, `readSlice`, and `BorrowTree.performAccessRange`
across $K$ sequential steps scales superlinearly in both time and memory.

#### C. Head-to-Head Elaboration + Kernel Timing Tables ($K = 1..30$)

All measurements below were recorded via
[support/run_benchmarks.py](support/run_benchmarks.py) under
`anneal-lean-run --mode file --concurrency 4 -- lean -j1` (raw outputs preserved
in [support/benchmark_results.json](support/benchmark_results.json) and
[support/benchmark_highk.json](support/benchmark_highk.json)):

##### Table 1: Lean `v4.28.0-rc1` (`3b0f2862196c6a8af9eb0025ee650252694013dd`) — Per-Theorem Time (ms)

| Steps ($K$) | Approach B (Schedule Engine `runPairMutSteps_spec`) | Approach B (Unrolled CPS `step_runPairMutSteps`) | Approach A2 (Direct Unfolding + Custom `simp` Roundtrip) | Approach A1 (Default `simp` Unfolding — Uncollapsed `4^K` AST) | Speedup (Approach B Unrolled vs. A2) | Speedup (Approach B Engine vs. A2) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1** | 24.00 ms | 22.93 ms | 902.53 ms | 725.45 ms *(fails postcond)* | **39.4x** | **37.6x** |
| **2** | 22.68 ms | 23.16 ms | 1,139.48 ms | 1,149.88 ms *(fails postcond)* | **49.2x** | **50.2x** |
| **3** | 23.03 ms | 24.97 ms | 1,536.21 ms | 1,509.96 ms *(fails postcond)* | **61.5x** | **66.7x** |
| **4** | 23.02 ms | 25.61 ms | 1,957.34 ms | 2,145.27 ms *(fails postcond)* | **76.4x** | **85.0x** |
| **5** | 22.73 ms | 28.16 ms | 2,404.31 ms | 2,382.02 ms *(fails postcond)* | **85.4x** | **105.8x** |
| **6** | — | — | 2,922.26 ms | 2,994.58 ms *(fails postcond)* | — | — |
| **8** | — | — | 3,984.70 ms | 4,198.33 ms *(fails postcond)* | — | — |
| **10** | 23.57 ms | 34.58 ms | 5,340.00 ms | 5,643.83 ms *(fails postcond)* | **154.4x** | **226.6x** |
| **15** | 24.81 ms | 43.53 ms | 8,992.99 ms | 9,606.31 ms *(fails postcond)* | **206.6x** | **362.5x** |
| **20** | 23.58 ms | 51.41 ms | 13,773.79 ms | — | **267.9x** | **584.1x** |
| **25** | 23.28 ms | 64.82 ms | 20,102.28 ms | — | **310.1x** | **863.5x** |
| **30** | **23.57 ms** | **79.26 ms** | **26,596.42 ms** | — | **335.6x** | **1,128.4x** |

##### Table 2: Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) — Per-Theorem Time (ms)

| Steps ($K$) | Approach B (Schedule Engine `runPairMutSteps_spec`) | Approach B (Unrolled CPS `step_runPairMutSteps`) | Approach A2 (Direct Unfolding + Custom `simp` Roundtrip) | Approach A1 (Default `simp` Unfolding — Uncollapsed `4^K` AST) | Speedup (Approach B Unrolled vs. A2) | Speedup (Approach B Engine vs. A2) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1** | 17.16 ms | 15.09 ms | 648.97 ms | 530.67 ms *(fails postcond)* | **43.0x** | **37.8x** |
| **2** | 17.07 ms | 16.68 ms | 812.19 ms | 813.23 ms *(fails postcond)* | **48.7x** | **47.6x** |
| **3** | 17.39 ms | 18.88 ms | 1,050.23 ms | 1,051.08 ms *(fails postcond)* | **55.6x** | **60.4x** |
| **4** | 17.73 ms | 19.18 ms | 1,333.13 ms | 1,340.44 ms *(fails postcond)* | **69.5x** | **75.2x** |
| **5** | 16.72 ms | 19.08 ms | 1,612.77 ms | 1,679.43 ms *(fails postcond)* | **84.5x** | **96.5x** |
| **6** | — | — | 1,938.62 ms | 1,991.00 ms *(fails postcond)* | — | — |
| **8** | — | — | 2,593.61 ms | 2,748.79 ms *(fails postcond)* | — | — |
| **10** | 17.02 ms | 24.82 ms | 3,337.86 ms | 3,561.48 ms *(fails postcond)* | **134.5x** | **196.1x** |
| **15** | 16.44 ms | 30.75 ms | 5,651.47 ms | 5,929.26 ms *(fails postcond)* | **183.8x** | **343.8x** |
| **20** | 16.74 ms | 38.60 ms | 8,025.80 ms | — | **207.9x** | **479.4x** |
| **25** | 16.78 ms | 44.48 ms | 11,210.63 ms | — | **252.0x** | **668.1x** |
| **30** | **17.37 ms** | **54.78 ms** | **14,672.92 ms** | — | **267.8x** | **844.7x** |

##### Table 3: Peak RSS Memory Consumption

| Workload | Lean `v4.28.0-rc1` Wall Time | Lean `v4.28.0-rc1` Peak RSS | Lean `v4.34.1` Wall Time | Lean `v4.34.1` Peak RSS |
| :--- | ---: | ---: | ---: | ---: |
| Full `MemoryLensAndScalingProbe.lean` (2,168 lines, all lens theorems + $K=15..30$ Approach B + $K=2$ Approach A2 + $N=10$ stack allocs) | 7.07 s | 721.0 MB | 10.84 s | 689.6 MB |
| High-$K$ Approach A2 Suite ($K \in \{10, 15, 20, 25, 30\}$ in a single file) | 79.48 s | **3,574.0 MB** | 47.46 s | **2,319.6 MB** |

### 5. Eliminating $O(N^2)$ Address-Disjointness Obligations via Provenance-Directed Offset Cancellation and Bounded Slack Windows

Basis: `source` + `execution` + `derived`

#### A. Provenance-Directed Offset Cancellation (`resolveOffset_offsetPtr_rootPtr`)

In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
(`Miri/Memory/AllocAddresses/GlobalState.lean:399-410`, `GlobalAddressState.ptrGetAlloc`,
and `Miri/Memory/Access.lean:86-164`, `checkAndDerefPtr`), memory loads and
stores look up the target allocation by concrete provenance
(`pointer.provenance = .concrete id _`) and compute the intra-allocation byte
offset by subtraction (`let relative := pointer.offset.bytes - baseAddress`). In
[support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
(lines `1295–1336`), `ValidLocalBaseAddr` and `resolveOffset_offsetPtr_rootPtr`
establish:

```lean
def ValidLocalBaseAddr (baseAddr totalSize align : Nat) : Prop :=
  0 < align ∧
  baseAddr % align = 0 ∧
  0 < baseAddr ∧
  baseAddr + totalSize < 18446744073709551616

theorem resolveOffset_offsetPtr_rootPtr
    (allocId : AllocId) (tag : BorTag) (baseAddr totalSize align relOff fieldSize : Nat)
    (h_local : ValidLocalBaseAddr baseAddr totalSize align)
    (h_inbounds : relOff + fieldSize ≤ totalSize) :
    let ptr := offsetPtr (mkRootPtr allocId tag baseAddr) relOff
    ptr.prov = some ⟨allocId, tag⟩ ∧
    baseAddr ≤ ptr.addr.toNat ∧
    ptr.addr.toNat - baseAddr = relOff ∧
    (ptr.addr.toNat - baseAddr) + fieldSize ≤ totalSize
```

Because `(UInt64.ofNat baseAddr + UInt64.ofNat relOff).toNat = baseAddr + relOff`
holds whenever `baseAddr + totalSize < 2^64` and `relOff + fieldSize ≤ totalSize`,
the symbolic `baseAddr` cancels out of `ptr.addr.toNat - baseAddr = relOff`
using **only** `ValidLocalBaseAddr baseAddr totalSize align` and **zero**
pairwise non-overlap hypotheses `baseAddr_i ≠ baseAddr_j`.

#### B. Bounded Slack Windows in `ValidFreshBaseAddr` for Constructive `Nonempty`

When a total weakest-precondition semantics (`wpComp (.choice α k) P := Nonempty α ∧ ∀ a : α, wpComp (k a) P`)
steps across $N$ sequential nondeterministic allocations, each step must prove
`Nonempty { baseAddr : Nat // ValidFreshBaseAddr as size align baseAddr }`.

If `ValidFreshBaseAddr as size align baseAddr` only required
`ValidLocalBaseAddr baseAddr size align ∧ DisjointFromAllLive as baseAddr size`
without an upper bound on `baseAddr`, a demonic adversary at allocation 0 could
select `baseAddr_0 = 2^64 - size_0 - align`. That choice would push the
high-water mark `maxEndAddrList [alloc_0]` to `~ 2^64`, making it impossible to
place allocation 1 above `maxEndAddrList [alloc_0]` without searching for free
gaps below `alloc_0`.

In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
(`Miri/Memory/AllocAddresses/AddressGenerator.lean:77-105`),
`AddressGenerator.generate` allocates monotonically above `nextBaseAddr` with
alignment rounding. Including a bounded slack window
`baseAddr ≤ maxEndAddrList as + align + 16` in `ValidFreshBaseAddr`
([support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
lines `1371–1467`) yields both constructive non-emptiness and $O(1)$
compositional stepping:

```lean
def ValidFreshBaseAddr (as : List AllocMeta) (size align : Nat) (baseAddr : Nat) : Prop :=
  ValidLocalBaseAddr baseAddr size align ∧
  DisjointFromAllLive as baseAddr size ∧
  baseAddr ≤ maxEndAddrList as + align + 16

theorem validFreshBaseAddr_nonempty (as : List AllocMeta) (size align : Nat)
    (h_align : 0 < align)
    (h_space : maxEndAddrList as + align + 16 + size < 18446744073709551616) :
    Nonempty { baseAddr : Nat // ValidFreshBaseAddr as size align baseAddr }

theorem wp_forceAllocation_choice (as : List AllocMeta) (allocId : AllocId)
    (size align bound : Nat)
    (k : Nat → Comp S) (P : S → Prop)
    (h_align : 0 < align)
    (h_bound : maxEndAddrList as ≤ bound)
    (h_space : bound + align + 16 + size < 18446744073709551616)
    (h_cont : ∀ baseAddr : Nat,
      ValidLocalBaseAddr baseAddr size align →
      maxEndAddrList (⟨allocId, baseAddr, size, align, true⟩ :: as) ≤ bound + align + 16 + size →
      wpComp (k baseAddr) P) :
    wpComp (forceAllocationChoice as size align k) P
```

Using `wp_forceAllocation_choice` and `storeLoadFieldAtNondetBase_eq`,
`wp_ten_nondet_stack_allocs`
([support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
lines `1576–1595`) verifies $N = 10$ sequential nondeterministic stack
allocations, field stores, and field loads in **54.80 ms** (`v4.28.0-rc1`) and
**34.83 ms** (`v4.34.1`) with a 10-line linear proof script and **zero**
pairwise address-disjointness proofs.

## Boundaries

- **Pointer-to-Integer Casts (`ptr2Int` / `expose_provenance`) and Cross-Allocation Address Comparisons**:
  - **Known not to apply** to the `DisjointFromAllLive`-dropping fast path
    (`wp_forceAllocation_choice`) when a program compares raw integer addresses
    across two distinct allocations (`ptr1.addr == ptr2.addr`). When cross-allocation
    integer address inequality is required, the proof must retain the
    `DisjointFromAllLive as baseAddr size` conjunct from `ValidFreshBaseAddr`
    for the exposed allocations rather than discarding it.
- **Overlapping Partial-Field Transmutes**:
  - **Not examined** for unaligned overlapping writes that partially overwrite
    one scalar field of a struct without matching a `TransmuteAs` codec boundary.
    When an unaligned write straddles two fields, `read_write_disjoint` does not
    apply; the proof must either lift to an enclosing composite codec (`pairCodec`
    / `u64Codec` via `typedAt_transmute`) or drop down to `readSlice` /
    `writeSlice` over the affected byte range.
- **Interior-Mutable `!Freeze` Child Reborrows Without Protectors**:
  - While `FnEntry`-protected `&mut T` always initializes to
    `Permission.Reserved true false` (`ReservedFrz false`) even when
    `T : !Freeze`, unprotected reborrows of `&mut T` where `T : !Freeze`
    initialize to `Permission.Reserved false false` (`ReservedIm`). In
    [support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean),
    `locWritePerm` is specialized to the common `Reserved true _` / `Active` /
    `Cell` footprint; unprotected `Reserved false false` (`!isProt`) writes
    also transition to `.Active` under `childWrite (.Reserved false false) false = some .Active`,
    which requires checking `!isProt` when `tyIsFreeze = false`.

## Evidence

### 1. Primary Upstream Sources

- **`proofs-rs/lean-miri`** (commit `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):
  - `Miri/Memory/Allocation.lean:164-174`, `Miri/Memory/InitMask.lean`, and
    `Miri/Memory/ProvenanceMap.lean:17-41`: Per-allocation byte storage
    (`rawBytes : Array UInt8`), initialization bitmask (`InitMask`), and pointer
    provenance fragments (`PointerFrag` and `ProvenanceMap`), unified per byte by
    `AbsByte` in
    [support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean)
    (lines `61–74`).
  - `Miri/Memory/Identity.lean:12-67` and `Miri/Memory/Pointer.lean:16-19`:
    Definitions of `AllocId`, `BorTag`, `Provenance`, and `Pointer`.
  - `Miri/Memory/AllocAddresses/GlobalState.lean:399-410` and
    `Miri/Memory/Access.lean:86-164`: Provenance-directed allocation lookup
    (`GlobalAddressState.ptrGetAlloc`, computing
    `relative := pointer.offset.bytes - baseAddress`) and bounds-checked
    pointer dereferencing (`checkAndDerefPtr`).
  - `Miri/TreeBorrows/Permissions.lean:19-32, 62-112, 268-271, 299-308`:
    Definitions of the 6-constructor `Permission` (`Cell`,
    `ReservedFrz (conflicted : Bool)`, `ReservedIM`, `Unique`, `Frozen`,
    `Disabled`), single-step transition functions `childRead`, `foreignRead`
    (lines `75–77`: `.ReservedIM => if isProtected then .ImpossibleProtectedReservedIM`),
    `childWrite` (lines `82–92`), `foreignWrite` (lines `96–98`),
    `Permission.associatedAccess` (lines `268–271`), and
    `Permission.strongestIdempotentForeignAccess` (lines `299–308`).
  - `Miri/TreeBorrows/LocationState.lean:36-40, 128-149`: Definition of
    `LocationState` (`permission`, `accessed`, `idempotentForeignAccess`) and
    `LocationState.performAccess`.
  - `Miri/TreeBorrows/RetagPolicy.lean:56-59, 77-79, 99, 108-110`:
    `selectedPermission` (`if isProtected || frozen then .ReservedFrz false else .ReservedIM`)
    and `InitialStateError.protectedReservedIM` in `initialLocationState`.
  - `Miri/TreeBorrows/Traversal.lean:45-112`,
    `Miri/TreeBorrows/TreeState.lean:1036-1070`, and
    `Miri/TreeBorrows/GlobalState.lean:146-148`: Normal-tree local/foreign
    traversal (`TraversalTree.traverse` with `ChildrenVisitMode.SkipChildrenOfAccessed`),
    `BorrowTree.releaseProtector`, and `GlobalState.endCall`.
  - `Miri/Memory/AllocAddresses/AddressGenerator.lean:77-105`: Monotonic
    base-address generation (`AddressGenerator.generate`).
- **`rust-lang/miri`** (commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
  - `src/borrow_tracker/tree_borrows/mod.rs:193-197`: `Permission::new_reserved`
    selecting `ReservedFrz` whenever `protected || freeze`.
- **`leanprover/lean4`** (commits `3b0f2862196c6a8af9eb0025ee650252694013dd`
  `v4.28.0-rc1` and `5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`):
  - Standard library `@[simp]` lemmas `UInt32.shiftRight_zero`,
    `UInt32.toUInt8_add`, and `UInt32.toUInt8_xor`, and kernel/elaborator
    `whnfCore` caching behavior on terms with `hasFVar == true`.

### 2. Preserved Package Support Material (Observed 2026-11-12)

- [support/MemoryLensAndScalingProbe.lean](support/MemoryLensAndScalingProbe.lean):
  Standalone 2,168-line Lean 4 mechanization of `AbsByte`, `readSlice`/`writeSlice`,
  `LayoutCodec`, `TransmuteAs`, 5-constructor `Permission`, `BorrowTree`,
  `FootprintAt` (`HasUniqueWritePerm`, `HasSharedReadPerm`), `TypedAt`,
  `resolveOffset_offsetPtr_rootPtr`, `ValidFreshBaseAddr`,
  `validFreshBaseAddr_nonempty`, `wp_forceAllocation_choice`,
  `wp_ten_nondet_stack_allocs`, `approachB_unrolled_15_steps`..`30_steps`,
  `approachB_15_steps`..`30_steps`, and `approachA_unfold_2_steps`.
  Verified with zero `sorryAx` and zero `Lean.ofReduceBool`:
  ```text
  'MemoryLensAndScalingProbe.read_write_same' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.read_write_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.typedAt_transmute' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.transmute_u32_pair_u64' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.checkUniqueWritePerm_sound' depends on axioms: [propext]
  'MemoryLensAndScalingProbe.footprintAt_preserve_local_write' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.footprintAt_preserve_disjoint_write' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.footprintAt_preserve_foreign_read' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.resolveOffset_offsetPtr_rootPtr' depends on axioms: [propext, Quot.sound]
  'MemoryLensAndScalingProbe.validFreshBaseAddr_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.wp_forceAllocation_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.wp_ten_nondet_stack_allocs' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.approachB_unrolled_30_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.approachB_30_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
  'MemoryLensAndScalingProbe.approachA_unfold_2_steps' depends on axioms: [propext, Quot.sound]
  ```
- [support/run_benchmarks.py](support/run_benchmarks.py): Automated single-pass
  benchmark harness measuring per-theorem elaboration + kernel checking time
  (`IO.monoNanosNow` with `-j1`) and peak RSS across Lean `v4.28.0-rc1` and
  `v4.34.1`.
- [support/benchmark_results.json](support/benchmark_results.json) and
  [support/benchmark_highk.json](support/benchmark_highk.json): Recorded timing
  and memory outputs from 2026-11-12.

## Revalidation

To revalidate the mechanized proofs and kernel scaling benchmarks on a new Lean 4
toolchain or after modifying the memory/borrow-tree representation:

1. **Kernel-Check the Standalone Probe**:
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- \
     lean reports/lean-absbyte-typedat-lenses-and-nondeterministic-alloc-scaling/support/MemoryLensAndScalingProbe.lean
   ```
   Verify that the command exits with code `0`, zero warnings, and that every
   `#print axioms` line outputs only `[propext]`, `[propext, Quot.sound]`, or
   `[propext, Classical.choice, Quot.sound]` (never `sorryAx` or
   `Lean.ofReduceBool`).

2. **Re-Run the Scaling Benchmark Suite**:
   ```bash
   python3 reports/lean-absbyte-typedat-lenses-and-nondeterministic-alloc-scaling/support/run_benchmarks.py
   ```
   Check `support/benchmark_results.json` to confirm that `approachB_loop_30`
   and `approachB_unrolled_30` remain under `100 ms` while `approachA2_10`
   exceeds `2,000 ms`, and check whether a newer Lean 4 standard library still
   marks `UInt32.toUInt8_add` and `UInt32.toUInt8_xor` as default `@[simp]`
   lemmas.

3. **Check Upstream Tree Borrows Retag Policy**:
   Diff `Miri/TreeBorrows/RetagPolicy.lean` (`selectedPermission`) and
   `Miri/TreeBorrows/Permissions.lean` (`childWrite`) in `proofs-rs/lean-miri`
   (or `src/borrow_tracker/tree_borrows/{mod,perms}.rs` in `rust-lang/miri`) to
   verify whether `if isProtected || frozen then .ReservedFrz false else .ReservedIM`
   still governs `FnEntry`-protected mutable references.
