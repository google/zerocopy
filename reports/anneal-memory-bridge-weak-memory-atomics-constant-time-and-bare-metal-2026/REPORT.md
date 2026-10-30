# Anneal Memory Bridge, Weak-Memory Atomics, Cryptographic Constant-Time, and Bare-Metal ELF Verification

## Summary

A verified Rust compiler backend for Anneal (`joshlf/anneal`) must preserve
source-level memory safety, happens-before concurrency invariants,
microarchitectural side-channel resistance, and bare-metal boot invariants when
lowering abstract `Runtime(PostCleanup)` MIR to flat 64-bit hardware address
spaces. In `joshlf/anneal` (`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`),
`trusted/lean/Trusted/Memory.lean` models memory as an abstract location-indexed
state (`MemState`) equipped with per-location non-atomic values
(`naVal : Nat → Option MirVal`), happens-before read/write timestamps
(`naReadTs`, `naWriteTs`), a thread view map (`curView : Nat → Nat`), and an
append-only release-acquire message pool (`atomicMsgs : List AtomicMsg`). Hardware
ISAs (AArch64, x86-64, and RV64GC), by contrast, execute over flat
byte-addressed `BitVec 64 → UInt8` memory, weak-memory reorder buffers,
microarchitectural address/branch leakage channels, and ELF linker-script
relocation images.

This report establishes the formal memory, concurrency, constant-time, and
bare-metal ELF verification architecture for Anneal's compiler backend,
mechanized in two standalone Lean 4.34.1 proof artifacts totaling 2,305 lines
with zero `sorryAx` and zero custom axioms
(`support/track7_memory_ct_weakmem_elf_probe.lean` and
`support/round2_track6_probe.lean`):

1. **Abstract-to-Concrete Memory Injection (`MemStateInj`)**:
   Adapting CompCert's block-offset memory injection (`Mem.mem_inj` in
   `AbsInt/CompCert` `common/Memory.v`) to Anneal's abstract `MemState`, we
   define a parameterized `LocationLayout` and relational invariant
   `MemStateInj` linking each abstract `loc : Nat` to a non-overlapping,
   naturally aligned hardware byte range `[baseAddr loc, baseAddr loc + 8)` in
   `ConcreteByteMem` (`UInt64 → UInt8`) coupled with a hardware store-buffer /
   cache-coherency protocol state (`HWCoherencyState`). We prove that lowered
   non-atomic reads, non-atomic writes, and release-acquire atomic accesses
   preserve `MemStateInj` (`evalInlineAsm_preserves_inj`), and prove a negative
   adequacy canary (`CanaryA_UnalignedAccessBreaksInj`) demonstrating that
   unaligned concrete accesses corrupt adjacent abstract locations unless the
   byte-range disjointness invariant is enforced.
2. **Cryptographic Constant-Time (`CT`) Preservation (`CTSimulation`)**:
   Drawing on `jasmin-lang/jasmin`, `CompCert-CT`, and `cslib-community/bignum`,
   we instrument MIR and backend lowering passes with a microarchitectural
   leakage trace (`UArchEvent`: `.pcStep`, `.branchTaken`, `.memReadAddr`,
   `.memWriteAddr`, `.divOperand`) and public-projection equivalence
   (`LowEq pubProj`). We prove that any compiler pass satisfying a
   leakage-preserving lockstep simulation (`CTSimulation`) preserves
   `ConstantTimeOn Pre pubProj` (`ctSimulation_preserves_constantTime`), and
   mechanize a concrete vulnerability witness
   (`CanaryB_ConditionalSelectToBranchViolatesCT`) proving that lowering a
   branchless MIR `Rvalue.select` (`cmov`/`csel`) into a diamond CFG
   (`Terminator.switchInt`) leaks secret condition bits via `.branchTaken` and
   diverging `.pcStep` events even though the input-output refinement holds.
3. **Weak-Memory Concurrency (`Acquire`/`Release`, RMW Exclusivity, and `SeqCst` Total Order)**:
   Building on the Intermediate Memory Model (`weakmemory/imm`) and `herdtools7`
   (`aarch64.cat`, `x86tso.cat`, `riscv.cat`), we formalize the exact compilation
   mappings from Anneal's `MemState` to AArch64 (`LDAR`/`STLR`, v8.3 `LDAPR`,
   LL/SC `LDAXR`/`STLXR`, v8.1 LSE `LDADDAL`/`CASAL`, `DMB ISH`), x86-64 TSO
   (`MOV`, `XCHG`, `LOCK XADD`, `LOCK CMPXCHG`, `MFENCE`), and RV64GC RVWMO
   (`ld`/`sd` with `fence`, `lr.d.aqrl`/`sc.d.aqrl`, `amoadd.d.aqrl`). We prove
   soundness of the Message-Passing (`MP`) litmus test under release-acquire
   lowering (`mp_litmus_forbidden_under_acquire_release`), prove that naive
   relaxed lowering violates `MP` (`CanaryC_RelaxedLoweringAllowsStaleRead`),
   extend `AtomicMsg` with modification-order predecessor links (`rmwPrevTs`) to
   prove RMW mutual exclusion (`rmw_atomicity_mutual_exclusion`) and refute
   split load+store RMW lowering
   (`canary_split_load_store_breaks_rmw_exclusivity`), and formalize
   `Ordering::SeqCst` fences (`AtomicFence`) to prove Store-Buffering (`SB`)
   impossibility (`sb_litmus_forbidden_under_seqcst_fences`) while refuting
   relaxed fence lowering (`canary_relaxed_fence_allows_sb_zero_zero`).
4. **Bare-Metal MMIO, `#[unsafe(naked)]`, and ELF Linker-Script Boot Verification**:
   We formalize volatile MMIO (`core::ptr::read_volatile` / `write_volatile`) as
   ordered, non-elidable `IOEvent` trace actions orthogonal to RAM `MemState`,
   specify whole-function `#[unsafe(naked)]` + `naked_asm!` ABI contracts
   forbidding compiler-inserted stack prologues, and verify bare-metal ELF
   linker-script layouts (`.text`, `.rodata`, `.data` LMA-to-VMA flash-to-SRAM
   relocation, and `.bss` zero-initialization). We prove that the startup boot
   stub `elfBootInit` establishes `FullElfMemStateInj` prior to `main`
   (`elfBootInit_establishes_fullMemInj`) and prove three negative canaries
   (`CanaryD_OverlappingBssAndStackRejected`,
   `canary_short_data_copy_breaks_inj`, and `canary_unzeroed_bss_breaks_inj`).

---

## Applicability

This report applies to:

- **Anneal (`joshlf/anneal`)** at commit
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`, specifically:
  - Layer 1 (`trusted/lean/Trusted/Refinement.lean`,
    `trusted/lean/Trusted/StepResult.lean`): `FailureKind`, `Outcome`,
    `TracePrefix`, `Language`, `Compiler`, `Compiler.SoundOn`,
    `Compiler.Verified`, and `SmallStepMachine`.
  - Layer 2 (`trusted/lean/Trusted/Memory.lean`,
    `trusted/lean/Trusted/MirAst.lean`,
    `trusted/lean/Trusted/MirSemantics.lean`): `View`, `AtomicMsg`, `MemState`
    (`curView`, `atomicMsgs`, `naVal`, `naWriteTs`, `naReadTs`),
    `MemState.readNA`, `MemState.writeNA`, `MemState.visibleAtomicMsgs`,
    `MirVal`, and `evalMirStep`.
- **Lean 4 (`leanprover/lean4`)** at `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **CompCert (`AbsInt/CompCert`)** at commit
  `f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`, specifically `common/Values.v`
  (`val`, `Val.inject`) and `common/Memory.v` (`Mem.mem`, `Mem.load`,
  `Mem.store`, `Mem.alloc`, `Mem.free`, `Mem.mem_inj`, `Mem.extends`).
- **Rust Compiler (`rust-lang/rust`)** at commits
  `58cf8f9c35b355199727627d07ae34a4e2846d67`,
  `8006091eb71ae7d9e9bccb66c6122c9d68af4466`,
  `49d734536222bf28bb6d07d885b3a81d145981da`, and
  `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, specifically:
  - `compiler/rustc_middle/src/mir/syntax.rs` (`StatementKind::Intrinsic`,
    `NonDivergingIntrinsic::CopyNonOverlapping`, `TerminatorKind::InlineAsm`).
  - `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` and
    `compiler/rustc_codegen_cranelift/src/intrinsics/llvm.rs` (`atomic_load`,
    `atomic_store`, `atomic_xadd`, `atomic_cxchg`, `atomic_fence`,
    `volatile_load`, `volatile_store`).
  - `compiler/rustc_mir_build/src/builder/mod.rs` and
    `compiler/rustc_codegen_ssa/src/mir/mod.rs` (`#[unsafe(naked)]` function
    lowering and prologue suppression).
- **Weak-Memory Concurrency Models and Backend Lowering**:
  - `weakmemory/imm` at `4ca191b072df081dd3a6d9aa755959dc901b1bd0`
    (`src/basic/Events.v`, `src/basic/Execution.v`, `src/imm/Imm.v`,
    `src/hardware/Arm.v`, `src/hardware/TSO.v`).
  - `herd/herdtools7` at `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`
    (`herd/libdir/aarch64.cat`, `herd/libdir/x86tso.cat`,
    `herd/libdir/riscv.cat`).
  - `llvm/llvm-project` at `3623fe661ae35c6c80ac221f14d85be76aa870f1`
    (`llvm/lib/Target/AArch64/AArch64InstrAtomics.td`,
    `llvm/lib/Target/X86/X86ISelLowering.cpp`,
    `llvm/lib/Target/RISCV/RISCVISelLowering.cpp`).

---

## Findings

### 1. Abstract-to-Concrete Memory Injection (`MemState` to Flat 64-Bit Byte Memory)

`Basis: direct inspection of joshlf/anneal trusted/lean/Trusted/Memory.lean @ e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0 and AbsInt/CompCert common/Memory.v @ f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03 + machine-checked proofs in support/track7_memory_ct_weakmem_elf_probe.lean`

#### 1.1 Structural Gap Between `Trusted/Memory.lean` and Hardware Byte Memory

Anneal's trusted kernel (`trusted/lean/Trusted/Memory.lean:1-77`) defines a
mixed non-atomic / release-acquire operational memory model:

```lean
structure View where
  clock : Nat → Nat

structure AtomicMsg where
  loc : Nat
  val : MirVal
  ts : Nat
  relView : View

structure MemState where
  curView : Nat → Nat
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option MirVal
  naWriteTs : Nat → Nat
  naReadTs : Nat → Nat
```

This representation makes three deliberate simplifications so that source-level
MIR verification in `theory/` remains tractable:
1. **Abstract Location Indexing**: Memory is indexed by an abstract natural
   number `loc : Nat` rather than a 64-bit physical address `BitVec 64`, and
   stores a typed `MirVal` (`.usize`, `.bool`, `.refImm`, `.refMut`, `.boxVal`)
   as an atomic unit rather than an 8-byte little-endian slice.
2. **Implicit Spatial Disjointness**: Distinct indices `loc₁ ≠ loc₂` never
   overlap in `naVal`, whereas in hardware memory two 8-byte accesses at
   addresses $a_1$ and $a_2$ alias whenever $|a_1 - a_2| < 8$.
3. **Happens-Before Timestamp Views**: `readNA` (`Memory.lean:45-49`) checks
   `m.naWriteTs loc ≤ m.curView loc` (detecting write-read data races), and
   `writeNA` (`Memory.lean:54-63`) checks both `m.naWriteTs loc ≤ m.curView loc`
   and `m.naReadTs loc ≤ m.curView loc` (detecting write-write and read-write
   races) before incrementing the location's timestamp.

In CompCert (`AbsInt/CompCert` `common/Memory.v`), the compiler bridges high-level
block-isolated memory `(b : block, ofs : Z)` across optimization passes via a
partial block injection $f : \text{block} \rightharpoonup \text{block} \times \mathbb{Z}$
and the relational invariant `Mem.mem_inj f m1 m2`, which requires:
- **Permission & Alignment Preservation**: Every valid access in `m1` at
  `(b1, ofs)` with alignment $p$ maps via $f(b_1) = \lfloor(b_2, \delta)\rfloor$
  to a valid aligned access at `(b2, ofs + delta)` in `m2`.
- **No-Overlap (`mi_no_overlap`)**: Distinct live source blocks $b_1 \neq b_1'$
  map to disjoint byte intervals in $m_2$.
- **Value Injection (`Val.inject`)**: Every stored byte/value in $m_1$ matches
  the concrete bytes in $m_2$ under $f$.

#### 1.2 The `LocationLayout` and `MemStateInj` Bridge (`support/track7_memory_ct_weakmem_elf_probe.lean:49-290`)

To connect Anneal's `MemState` directly to a 64-bit ISA backend without modifying
the 77-line `Trusted/Memory.lean` kernel, we define an untrusted refinement
relation `MemStateInj` in `theory/` parameterized by a concrete `LocationLayout`:

```lean
structure LocationLayout where
  /-- Maps abstract `loc : Nat` to its 64-bit hardware base address (`UInt64`). -/
  baseAddr : Nat → UInt64
  /-- Set of abstract locations allocated in the current execution. -/
  allocated : Nat → Bool
  /-- Alignment: every allocated location is 8-byte aligned (`baseAddr loc % 8 = 0`). -/
  aligned8 : ∀ loc, allocated loc = true → (baseAddr loc).toNat % 8 = 0
  /-- No-overlap: distinct allocated locations occupy disjoint 8-byte intervals
      in the 64-bit hardware address space (`[base, base + 8)` do not wrap or alias). -/
  noOverlap : ∀ loc₁ loc₂,
    allocated loc₁ = true →
    allocated loc₂ = true →
    loc₁ ≠ loc₂ →
    (baseAddr loc₁).toNat + 8 ≤ (baseAddr loc₂).toNat ∨
    (baseAddr loc₂).toNat + 8 ≤ (baseAddr loc₁).toNat
  /-- Non-overflow: `[baseAddr loc, baseAddr loc + 8)` fits within `2^64`. -/
  noOverflow : ∀ loc, allocated loc = true → (baseAddr loc).toNat + 8 ≤ 18446744073709551616
```

A concrete hardware memory state pairs a flat byte map
`ConcreteByteMem := UInt64 → UInt8` (equipped with little-endian 64-bit word
encoding `readWord64LE` / `writeWord64LE`, proven invertible in
`readWord64LE_writeWord64LE_same` and frame-disjoint in
`readWord64LE_writeWord64LE_other`) with a hardware coherency ghost state
`HWCoherencyState` tracking architectural store-buffer timestamps and barriers.

`MemStateInj layout absMem concMem hwState` holds when:
1. **Non-Atomic Value Agreement (`naInj`)**: For every allocated `loc` whose
   latest non-atomic write is visible in the current thread's happens-before
   view (`absMem.naWriteTs loc ≤ absMem.curView loc` and
   `absMem.naReadTs loc ≤ absMem.curView loc`), if
   `absMem.naVal loc = some v`, then `readWord64LE concMem (layout.baseAddr loc)`
   equals the concrete 64-bit encoding `encodeMirVal layout v` (where `.usize n`
   encodes as `n`, `.bool b` as `0`/`1`, and references `.refImm target` /
   `.refMut target` encode as `layout.baseAddr target`).
2. **Hardware Coherency Agreement (`coherencyInj`)**: The hardware store buffer
   and invalidate queues respect `absMem.curView`, `absMem.naWriteTs`,
   `absMem.naReadTs`, and `absMem.atomicMsgs`.

We machine-check two foundational theorems over `MemStateInj`:
- **`evalInlineAsm_preserves_inj` (`track7_memory_ct_weakmem_elf_probe.lean:245-268`)**:
  Proves that executing an aligned, in-footprint memory access event (or
  sequence of `readNA` / `writeNA` events) synchronously on `absMem` and
  `concMem` preserves `MemStateInj layout absMem' concMem' hwState'` and yields
  identical loaded values.
- **`CanaryA_UnalignedAccessBreaksInj` (`track7_memory_ct_weakmem_elf_probe.lean:270-290`)**:
  Constructs a concrete two-location layout where `loc = 0` is at `0x1000` and
  `loc = 1` is at `0x1004` (violating `noOverlap` because `0x1000 + 8 > 0x1004`),
  and proves that an 8-byte concrete store to `loc = 0` overwrites the lower 4
  bytes of `loc = 1`, refuting `MemStateInj` for `loc = 1`.

---

### 2. Cryptographic Constant-Time (`CT`) Preservation Across Lowering

`Basis: analysis of jasmin-lang/jasmin, CompCert-CT, and cslib-community/bignum + machine-checked proofs in support/track7_memory_ct_weakmem_elf_probe.lean`

#### 2.1 Why Standard Functional Refinement (`Compiler.SoundOn`) Allows Timing Channels

Anneal's `Compiler.SoundOn` (`trusted/lean/Trusted/Refinement.lean:88-100`)
requires that target execution outcomes refine source outcomes (`T.exec tp ≤ S.exec sp`).
Because `Outcome` in standard MIR semantics tracks only returned values,
nontermination, and undefined behavior—not the sequence of program counters,
branch outcomes, or memory addresses presented to the data cache—an optimizing
pass can legally rewrite a branchless select:
$$\text{out} := \text{cond} \mathbin{?} a : b$$
into a conditional branch:
$$\texttt{if (cond) \{ out = a; \} else \{ out = b; \}}$$
In cryptographic primitives (e.g., constant-time Montgomery ladders,
`subtle::ConditionallySelectable`, or post-quantum lattice rejection sampling),
this transformation introduces a catastrophic remote timing vulnerability.

#### 2.2 Leakage-Instrumented Semantics and `CTSimulation` (`support/track7_memory_ct_weakmem_elf_probe.lean:292-484`)

Following `jasmin-lang/jasmin` and `CompCert-CT`, we define the standard
hardware constant-time leakage alphabet `UArchEvent`:

```lean
inductive UArchEvent where
  | pcStep (blockId : Nat) (instIdx : Nat)
  | branchTaken (cond : Bool) (targetBlock : Nat)
  | memReadAddr (addr : UInt64) (width : Nat)
  | memWriteAddr (addr : UInt64) (width : Nat)
  | divOperand (numerator : UInt64) (denominator : UInt64)
  deriving DecidableEq, Repr
```

Two initial states $s_1, s_2 : \text{State}$ are **low-equivalent**
(`LowEq pubProj s₁ s₂`) when their public projections agree
(`pubProj s₁ = pubProj s₂`) while their secret registers or secret memory words
may differ arbitrarily. A program $P$ is **constant-time on precondition
$\text{Pre}$** (`ConstantTimeOn exec Pre pubProj`) if for all $s_1, s_2$
satisfying $\text{Pre}$ and `LowEq pubProj s₁ s₂`, both executions succeed and
emit the **exact same leakage trace** (`trace₁ = trace₂`).

To guarantee that compiler passes (such as ANSSA `mem2reg`, ISLE instruction
selection, and `regalloc2` spill insertion) preserve constant-time execution, we
define a **Constant-Time Simulation (`CTSimulation`)**:
1. **Public-Projection Compatibility**: Source low-equivalence lifts to target
   low-equivalence (`LowEq srcPub s₁ s₂ → LowEq tgtPub (compileState s₁) (compileState s₂)`).
2. **Deterministic Leakage Mapping (`mapLeakage`)**: The target leakage trace of
   any compiled execution is a deterministic function
   `mapLeakage : PublicView → List UArchEvent → List UArchEvent` of the public
   input view and the source leakage trace alone—never of secret values.
   - For `regalloc2` stack spilling, because spill slot offsets depend only on
     the static CFG and virtual register live ranges (`sp + staticOffset`), the
     inserted `.memReadAddr` / `.memWriteAddr` events depend only on the public
     stack base pointer `sp` and the program counter, satisfying `mapLeakage`.
   - For ISLE instruction selection, lowering `Rvalue.select` to AArch64 `csel`
     or x86-64 `cmov` emits a single `.pcStep` independent of the condition
     value, satisfying `mapLeakage`.

We prove two theorems in Section 2 of
`support/track7_memory_ct_weakmem_elf_probe.lean`:
- **`ctSimulation_preserves_constantTime` (`lines 395-425`)**: Any compiler pass
  satisfying `CTSimulation` preserves `ConstantTimeOn` from source to target:
  $$\text{CTSimulation}(C) \;\wedge\; \text{ConstantTimeOn}(S, \text{Pre}, \text{pubProj}) \implies \text{ConstantTimeOn}(C(S), \text{Pre}_T, \text{pubProj}_T)$$
- **`CanaryB_ConditionalSelectToBranchViolatesCT` (`lines 427-484`)**:
  Constructs a concrete branchless source program `ctSelectProg` (using
  `Rvalue.select secretCond a b`) and proves `ctSelectProg_is_constantTime`
  (emitting `[.pcStep 0 0]` regardless of `secretCond : Bool`). We then define
  `branchyLoweringProg` (which lowers `Rvalue.select` into a diamond CFG with
  `Terminator.switchInt secretCond 1 2`), prove that `branchyLoweringProg` is a
  **valid functional refinement** (`branchyLowering_functionally_correct`:
  returns the exact same value on every input), and prove
  `CanaryB_ConditionalSelectToBranchViolatesCT` (`¬ ConstantTimeOn ...` because
  `secretCond = true` emits `[.pcStep 0 0, .branchTaken true 1, .pcStep 1 0]`
  whereas `secretCond = false` emits
  `[.pcStep 0 0, .branchTaken false 2, .pcStep 2 0]`).

---

### 3. Weak-Memory Concurrency Compilation (`Acquire`/`Release`, RMW Exclusivity, and `SeqCst`)

`Basis: inspection of weakmemory/imm @ 4ca191b072df081dd3a6d9aa755959dc901b1bd0, herd/herdtools7 @ 9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34, and llvm/llvm-project @ 3623fe661ae35c6c80ac221f14d85be76aa870f1 + machine-checked proofs in support/track7_memory_ct_weakmem_elf_probe.lean and support/round2_track6_probe.lean`

#### 3.1 Exact Hardware Lowering Table for Rust Atomic Operations

Across `llvm/llvm-project` (`3623fe661ae35c6c80ac221f14d85be76aa870f1`) and
`rustc_codegen_cranelift` (`rust-lang/rust` `8006091eb71ae7d9e9bccb66c6122c9d68af4466`),
Rust's C++20 atomic operations (`core::sync::atomic::Ordering`) lower to
target-specific instruction sequences on AArch64, x86-64, and RV64GC as shown in
Table 1.

| Rust Atomic Operation | `MemState` Transition | AArch64 v8.0 Base | AArch64 v8.1 LSE / v8.3 RCpc | x86-64 (TSO) | RV64GC (RVWMO) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`load(Relaxed)`** | Read `msg ∈ atomicMsgs` with `msg.ts ≥ curView(loc)`; advance `curView(loc) := msg.ts` (no cross-location `View.join`) | `LDR` | `LDR` | `MOV` | `ld` |
| **`load(Acquire)`** | Read `msg ∈ atomicMsgs` with `msg.ts ≥ curView(loc)`; join thread view `curView := View.join curView msg.relView` | `LDAR` | `LDAPR` (v8.3 RCpc) or `LDAR` | `MOV` | `ld; fence r, rw` |
| **`load(SeqCst)`** | `load(Acquire)` + total `SeqCst` order $S$ constraints | `LDAR` | `LDAR` (must follow `STLR` order; `LDAPR` insufficient without `DMB`) | `MOV` | `fence rw, rw; ld; fence r, rw` |
| **`store(Relaxed)`** | Append `msg` with `ts > maxTs(loc)` and `relView := singleton(loc, ts)` | `STR` | `STR` | `MOV` | `sd` |
| **`store(Release)`** | Advance `curView(loc) := ts`; append `msg` with `relView := curView` | `STLR` | `STLR` | `MOV` | `fence rw, w; sd` |
| **`store(SeqCst)`** | `store(Release)` + total `SeqCst` order $S$ constraints | `STLR` | `STLR` | `XCHG` (or `MOV; MFENCE`) | `fence rw, rw; sd` |
| **`fetch_add(Relaxed)`** | Read latest `msg_prev` in modification order (`rmwPrevTs = some msg_prev.ts`), append `msg_new` with `ts = msg_prev.ts + 1` | Loop: `LDXR; ADD; STXR; CBNZ` | `LDADD` | `LOCK XADD` | `amoadd.d` |
| **`fetch_add(AcqRel)`** | Atomic RMW with `curView := View.join curView msg_prev.relView` and `msg_new.relView := curView'` | Loop: `LDAXR; ADD; STLXR; CBNZ` | `LDADDAL` | `LOCK XADD` | `amoadd.d.aqrl` |
| **`compare_exchange(AcqRel, Acquire)`** | On success: atomic RMW (`rmwPrevTs = some msg_prev.ts`, `AcqRel` view join/publish); on failure: `load(Acquire)` of `msg_prev` | Loop: `LDAXR; CMP; B.NE; STLXR; CBNZ` | `CASAL` | `LOCK CMPXCHG` | Loop: `lr.d.aqrl; bne; sc.d.aqrl; bnez` |
| **`fence(AcqRel)`** | Thread view joins accumulated read views into release fence state | `DMB ISH` | `DMB ISH` | *no-op* (implicit in TSO) | `fence rw, rw` (or `fence.tso`) |
| **`fence(SeqCst)`** | `fence(AcqRel)` + global `SeqCst` synchronization entry (`scClock` join/publish) | `DMB ISH` | `DMB ISH` | `MFENCE` (or `LOCK OR [rsp], 0`) | `fence rw, rw` |

#### 3.2 Message-Passing (`MP`) Soundness Under Release-Acquire Lowering (`support/track7_memory_ct_weakmem_elf_probe.lean:486-665`)

In Anneal's `Trusted/Memory.lean`, an atomic release store at location `flag`
captures the writer thread's entire `curView` (including the timestamp of any
prior non-atomic store to `data`) inside `AtomicMsg.relView`. When a reader
thread executes an atomic acquire load at `flag` that observes that message, it
updates its own view via `View.join readerView msg.relView`:
$$\forall \ell,\; \text{readerView}'(\ell) = \max(\text{readerView}(\ell), \text{msg.relView}(\ell))$$
Consequently, the reader's `curView data` is guaranteed to be at least the
writer's non-atomic write timestamp `naWriteTs data`, forcing any subsequent
`readNA data` to observe the updated payload rather than a stale initial value.

In Section 3 of `support/track7_memory_ct_weakmem_elf_probe.lean`:
- **`mp_litmus_forbidden_under_acquire_release` (`lines 585-626`)**: Proves that
  for the two-thread Message-Passing (`MP`) litmus test (`Thread 0`:
  `writeNA data 42; storeRelease flag 1`, `Thread 1`:
  `r1 := loadAcquire flag; if r1 == 1 then r2 := readNA data`), when lowered to
  AArch64 `STLR` / `LDAR` (or x86-64 TSO `MOV` / RV64GC `fence rw,w; sd` and
  `ld; fence r,rw`), no execution trace can ever observe the weak outcome
  `r1 = 1 ∧ r2 = 0`.
- **`CanaryC_RelaxedLoweringAllowsStaleRead` (`lines 628-665`)**: Proves that if
  a buggy backend lowers `store(Release)` / `load(Acquire)` to plain relaxed
  `STR` / `LDR` on AArch64 (omitting the cross-location `View.join` on
  `msg.relView`), the weak outcome `r1 = 1 ∧ r2 = 0` is reachable because
  `Thread 1`'s `curView flag` advances to `1` while `curView data` remains `0`.

#### 3.3 Atomic Read-Modify-Write (`RMW`) Exclusivity and Modification Order (`support/round2_track6_probe.lean:40-265`)

A critical design question for Anneal's `Trusted/Memory.lean` is how to extend
`AtomicMsg` to support atomic Read-Modify-Write operations (`fetch_add`,
`fetch_sub`, `swap`, `compare_exchange`) without permitting lost updates under
concurrent writers. In C++20 and the Intermediate Memory Model (`weakmemory/imm`
`src/basic/Execution.v`), RMW atomicity is defined by the **immediate
predecessor condition (`rmw_atomicity`)** in the per-location modification order
($\text{mo}$): an RMW event pair $(r, w)$ is atomic if and only if $r$ reads from
$w_{\text{prev}}$ ($\text{rf}(w_{\text{prev}}, r)$) and $w$ is the **immediate**
$\text{mo}$-successor of $w_{\text{prev}}$, with no intervening write $w'$
satisfying $w_{\text{prev}} <_{\text{mo}} w' <_{\text{mo}} w$.

In Section 1 of `support/round2_track6_probe.lean`, we extend `AtomicMsg` with a
`rmwPrevTs : Option Nat` field:
- Every RMW write message at location `loc` records `rmwPrevTs = some prev.ts`
  and must read the unique frontier message `prev` (the latest message in
  modification order at `loc`, so no other message in `atomicMsgs` at `loc`
  already claims `rmwPrevTs = some prev.ts`).
- **`rmw_atomicity_mutual_exclusion` (`round2_track6_probe.lean:160-210`)**:
  Proves that two concurrent threads executing `atomicFetchAdd loc 1` from an
  initial state `loc = 0` can never both read `ts = 0` and overwrite each other
  with `val = 1`; every valid interleaved schedule produces a final value of
  `2` at `ts = 2`.
- **`canary_split_load_store_breaks_rmw_exclusivity` (`round2_track6_probe.lean:212-265`)**:
  Proves that if a backend lowers `fetch_add` as a separate `loadAcquire`
  followed by `storeRelease` (without hardware LL/SC exclusivity `LDAXR`/`STLXR`
  or LSE `LDADDAL` / x86 `LOCK XADD`), two threads can both read the initial
  message `val = 0` and both append `val = 1`, producing a lost update (`val = 1`
  instead of `2`).

#### 3.4 `Ordering::SeqCst` Total Order $S$ and Store-Buffering (`SB`) Soundness (`support/round2_track6_probe.lean:267-420`)

While Release-Acquire synchronization (`curView` and `AtomicMsg.relView`) is
sufficient for Message-Passing (`MP`), it intentionally permits the weak
outcome `r0 = 0 ∧ r1 = 0` in the Store-Buffering (`SB`) litmus test:
- **Thread 0**: `x.store(1, Release); r0 = y.load(Acquire)`
- **Thread 1**: `y.store(1, Release); r1 = x.load(Acquire)`

Because neither thread reads a value written by the other, neither `View.join`
transmits information across threads, and hardware store buffers (including
x86-64 TSO and AArch64 `STLR` followed by `LDAPR`) can reorder the store to `x`
past the load of `y`.

To forbid `r0 = 0 ∧ r1 = 0` when `SeqCst` operations or `SeqCst` fences are used,
Section 1.4 of `support/round2_track6_probe.lean` extends `MemState` with a
global `SeqCst` coherence view (`scView : View`) updated by `SeqCst` accesses
and `fence(Ordering::SeqCst)` (`AtomicFence .seqCst`):
- **`sb_litmus_forbidden_under_seqcst_fences` (`round2_track6_probe.lean:345-390`)**:
  Proves that across all 6 valid interleavings of the two-thread Store-Buffering
  program with `fence(SeqCst)` (`DMB ISH` on AArch64, `MFENCE` on x86-64,
  `fence rw,rw` on RV64GC) between each store and load, the outcome
  `r0 = 0 ∧ r1 = 0` is unreachable (`r0 = 1 ∨ r1 = 1` always holds).
- **`canary_relaxed_fence_allows_sb_zero_zero` (`round2_track6_probe.lean:392-420`)**:
  Proves that omitting the `scView` synchronization in the fence lowering makes
  the forbidden `r0 = 0 ∧ r1 = 0` outcome reachable.

---

### 4. Bare-Metal Systems Features: Volatile MMIO, `#[unsafe(naked)]`, and ELF Linker-Script Boot Verification

`Basis: inspection of rust-lang/rust compiler/rustc_codegen_ssa and compiler/rustc_mir_build + machine-checked proofs in support/track7_memory_ct_weakmem_elf_probe.lean and support/round2_track6_probe.lean`

#### 4.1 Volatile MMIO (`read_volatile` / `write_volatile`) vs. Normal RAM

In bare-metal device drivers, Memory-Mapped I/O (MMIO) registers (such as UART
FIFO registers, interrupt controller status words, or DMA descriptors) have
observable hardware side effects on every read and write. Modeling
`core::ptr::read_volatile` and `core::ptr::write_volatile` as ordinary non-atomic
accesses on `MemState.naVal` would be unsound for two reasons:
1. Reading the same MMIO address twice in succession without an intervening CPU
   write can return two distinct hardware status values.
2. Dead-store elimination (DSE) or redundant-load elimination (CSE) on `naVal`
   would erase hardware register strobes.

In `support/track7_memory_ct_weakmem_elf_probe.lean` (Section 4.1, lines
667-715), we partition the physical address space via `LocationLayout` into
**RAM regions** (governed by `MemStateInj`) and **MMIO regions**
(`isMmioAddr : UInt64 → Bool`, disjoint from all `layout.baseAddr loc`). Every
volatile load or store to an MMIO address emits an unremovable external
`IOEvent` (`.mmioRead addr width val` or `.mmioWrite addr width val`) onto the
execution trace while leaving RAM `MemState` unchanged (`mmio_preserves_ram_inj`).

#### 4.2 `#[unsafe(naked)]` Functions (`naked_asm!`) and Prologue-Free Entry

Under RFC 2972 (`#[unsafe(naked)]`, stabilized with `core::arch::naked_asm!`), a
naked function's body consists of a single `naked_asm!` block and `rustc` sets
`FnAbi` / codegen flags so that the backend emits **zero function prologue or
epilogue instructions** (no `stp x29, x30, [sp, #-16]!`, no `push rbp`, no stack
pointer adjustment, and no implicit `ret`). In Anneal's MIR-to-ISA bridge:
- Ordinary functions are verified against a calling-convention wrapper that
  allocates the stack frame `frameSize` before the entry block.
- `#[unsafe(naked)]` functions are verified directly at the raw architectural
  entry state `(pc = symAddr, sp = callerSp, regs = callerRegs)` with
  `prologueBytes = 0`, enabling verification of interrupt vector tables, trap
  handlers, and early boot trampolines (`_start`) before a valid stack pointer
  exists.

#### 4.3 Multi-Region ELF Linker-Script Verification (`.text`, `.rodata`, `.data` LMA-to-VMA Copy, and `.bss` Zeroing)

In bare-metal firmware (`no_std`, `#![no_main]`), a linker script (`memory.x` /
`link.x`) places sections across Read-Only Flash (`ROM`) and Static RAM
(`SRAM`):
- `.text` (executable machine code) and `.rodata` (read-only constants and
  vtables) reside in Flash at `VMA == LMA`.
- `.data` (mutable statics with non-zero initializers) has its **Load Memory
  Address (`LMA`)** in Flash (`__sidata`) and its **Virtual Memory Address
  (`VMA`)** in SRAM (`__sdata .. __edata`). At power-on reset, SRAM contains
  arbitrary uninitialized bytes; the startup routine (`reset_handler` / `r0`)
  must copy `[__sidata, __sidata + (__edata - __sdata))` from Flash to
  `[__sdata, __edata)` before Rust code accesses any mutable `static`.
- `.bss` (zero-initialized mutable statics) occupies `[__sbss, __ebss)` in SRAM
  (`SHT_NOBITS`, occupying zero bytes in the Flash image) and must be zeroed by
  the startup routine before Rust code executes.

We mechanize both the static ELF linker-script layout checker (`verifyLinkerLayout`
in `support/track7_memory_ct_weakmem_elf_probe.lean:717-805`) and the full
operational LMA-to-VMA `.data` copy + `.bss` zero-initialization proof
(`support/round2_track6_probe.lean:422-725`):
1. **Static Section Disjointness (`verifyLinkerLayout_sound`,
   `track7_memory_ct_weakmem_elf_probe.lean:755-780`)**: Verifies that `.text`,
   `.rodata`, `.data` (both VMA and LMA), `.bss`, and `.stack` are 8-byte
   aligned, non-wrapping, within physical Flash/SRAM bounds, and pairwise
   disjoint.
2. **`CanaryD_OverlappingBssAndStackRejected`
   (`track7_memory_ct_weakmem_elf_probe.lean:782-805`)**: Proves that an ELF
   layout where `.bss` (`0x2000_0000 .. 0x2000_1000`) overlaps the downward-growing
   `.stack` region (`0x2000_0800 .. 0x2000_2000`) is rejected by
   `verifyLinkerLayout`.
3. **End-to-End Boot Initialization Theorem
   (`elfBootInit_establishes_fullMemInj`, `round2_track6_probe.lean:585-655`)**:
   Models an ELF image with `.rodata` constants in Flash, `.data` initializers
   stored at Flash LMA `__sidata`, and `.bss` statics in SRAM alongside raw
   uninitialized power-on SRAM garbage (`arbitrarySram`). We prove that running
   `elfBootInit` (which copies `__edata - __sdata` bytes from `__sidata` to
   `__sdata` and zeroes `__ebss - __sbss` bytes at `__sbss`) establishes
   `FullElfMemStateInj` across all three static storage classes (`.rodata`,
   `.data`, and `.bss`) simultaneously.
4. **Negative Boot Initialization Canaries (`round2_track6_probe.lean:657-725`)**:
   - **`canary_short_data_copy_breaks_inj`**: Proves that if the startup loop
     copies fewer than `dataWords` 8-byte words from `__sidata` to `__sdata`
     (an off-by-one linker symbol bug), `FullElfMemStateInj` fails on the trailing
     `.data` static whenever power-on SRAM differs from the Flash initializer.
   - **`canary_unzeroed_bss_breaks_inj`**: Proves that if `.bss` zeroing is
     skipped or truncated, `FullElfMemStateInj` fails for zero-initialized
     statics on non-zero power-on SRAM.

---

## Boundaries

1. **Cache-Line Granularity vs. Byte-Address Leakage in `UArchEvent`**:
   Our `UArchEvent` constant-time trace model enforces exact byte-address
   invariance (`.memReadAddr addr width`, `.memWriteAddr addr width`), which is
   strictly stronger than cache-line (`addr >> 6`) invariance and resists both
   cache-line and cache-bank contention attacks. However, it does not model
   data-dependent power consumption (DPA) or speculative execution beyond
   architectural branch targets (`Spectre-v1`); resisting speculative leakage
   requires inserting architectural speculation barriers (`csdb` on AArch64,
   `lfence` on x86-64) at secret-dependent bounds checks.
2. **Mixed-Size Atomic Accesses**:
   The weak-memory mechanization in `support/track7_memory_ct_weakmem_elf_probe.lean`
   and `support/round2_track6_probe.lean` models same-size 64-bit aligned atomic
   and non-atomic accesses (`LocationLayout.aligned8`). Overlapping mixed-size
   atomic accesses (e.g., an atomic `u32` store aliasing half of an atomic `u64`
   load) are undefined behavior in Rust's memory model and are rejected by
   `LocationLayout.noOverlap`.
3. **Consume Ordering (`Ordering::Consume`)**:
   Rust does not expose `Ordering::Consume` in `core::sync::atomic::Ordering` (it
   is absent or upgraded to `Acquire` in `rustc`), so all dependency-ordered
   loads are verified under `Acquire` semantics (`View.join`).
4. **DMA Concurrent Writers**:
   Our MMIO trace model (`IOEvent.mmioRead` / `IOEvent.mmioWrite`) assumes MMIO
   register spaces are disjoint from normal RAM `LocationLayout`. Verifying
   Direct Memory Access (DMA) controllers that asynchronously mutate RAM buffers
   requires modeling the DMA engine as a concurrent thread participating in
   `MemState` via release/acquire ownership transfer (`dma_GiveBuffer` /
   `dma_TakeBuffer`).

---

## Evidence

1. **Round 1 Track 7 Standalone Lean 4.34.1 Mechanization
   (`support/track7_memory_ct_weakmem_elf_probe.lean`)**:
   - **Path**:
     `reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/track7_memory_ct_weakmem_elf_probe.lean`
   - **Lines**: 843
   - **SHA-256**:
     `4abe15811027f936ff68f92351c827476146eff66d3f062f0cc7140ffed1b09e`
   - **Key Verified Theorems**:
     - `readWord64LE_writeWord64LE_same`, `readWord64LE_writeWord64LE_other`
     - `evalInlineAsm_preserves_inj`
     - `CanaryA_UnalignedAccessBreaksInj`
     - `ctSimulation_preserves_constantTime`, `ctSelectProg_is_constantTime`,
       `branchyLowering_functionally_correct`,
       `CanaryB_ConditionalSelectToBranchViolatesCT`
     - `mp_litmus_forbidden_under_acquire_release`,
       `CanaryC_RelaxedLoweringAllowsStaleRead`
     - `mmio_preserves_ram_inj`, `verifyLinkerLayout_sound`,
       `CanaryD_OverlappingBssAndStackRejected`
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only
     on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`),
     with zero `sorryAx` and zero custom axioms.
2. **Round 2 Track 6 Standalone Lean 4.34.1 Mechanization
   (`support/round2_track6_probe.lean`, Sections 1 & 2)**:
   - **Path**:
     `reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/round2_track6_probe.lean`
   - **Lines**: 1,462
   - **SHA-256**:
     `d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771`
   - **Key Verified Theorems (Sections 1 & 2)**:
     - `rmw_atomicity_mutual_exclusion`
     - `canary_split_load_store_breaks_rmw_exclusivity`
     - `sb_litmus_forbidden_under_seqcst_fences`
     - `canary_relaxed_fence_allows_sb_zero_zero`
     - `elfBootInit_establishes_fullMemInj`
     - `canary_short_data_copy_breaks_inj`
     - `canary_unzeroed_bss_breaks_inj`
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only
     on standard Lean 4 axioms (`propext`, `Quot.sound`), with zero `sorryAx`
     and zero custom axioms.

---

## Revalidation

To typecheck both standalone Lean 4.34.1 proof probes and verify all theorems
and `#guard_msgs in #print axioms` checks with zero errors and zero warnings,
run from the repository root using Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`):

```bash
lean -j1 -M768 \
  reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/track7_memory_ct_weakmem_elf_probe.lean

lean -j1 -M768 \
  reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/round2_track6_probe.lean
```

Expected output: exit code `0` with empty stdout and stderr for both files.

To verify the SHA-256 digests of the preserved proof probes:

```bash
sha256sum \
  reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/track7_memory_ct_weakmem_elf_probe.lean \
  reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026/support/round2_track6_probe.lean
# Expected:
# 4abe15811027f936ff68f92351c827476146eff66d3f062f0cc7140ffed1b09e  .../track7_memory_ct_weakmem_elf_probe.lean
# d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771  .../round2_track6_probe.lean
```
