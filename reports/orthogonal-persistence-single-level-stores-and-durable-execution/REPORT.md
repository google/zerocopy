# Orthogonal Persistence, Single-Level Stores, and Durable Execution

## Summary

Mainstream systems languages and POSIX operating systems hardcode an ephemeral RAM-versus-disk dualism in which every live typed memory graph is destroyed on process exit or power failure and must be marshaled manually across untyped byte streams. Four major paradigms attempt to abolish or automate that boundary—(1) **hardware/virtual-ISA capability Single-Level Stores** (`IBM System/38`, `AS/400`, `IBM i` `TIMI` + `SLS`), (2) **language-level persistence-by-reachability** (`PS-Algol`, `Napier88`, `PJama`) and **type-enforced byte-addressable persistent memory** (`Px86`, `Corundum`), (3) **OS-level atomic checkpointing** (`KeyKOS`, `EROS`, `Coyotos`, `Aurora SLS`), and (4) **WebAssembly and cloud durable execution** (`Golem`, `Motoko` Enhanced Orthogonal Persistence, `Temporal`, `Restate`, `Azure Durable Functions`, `DBOS`).

Every paradigm ultimately confronts the same five irreducible engineering and formal-verification seams:

1. **ISA-neutral observability vs. layout-pinned raw snapshots:** `IBM i` migrated production persistent stores across a complete ISA replacement (48-bit CISC `IMPI` to 64-bit `PowerPC`) without source recompilation because compiled objects retain typed observable `TIMI` metadata alongside 128-bit hardware-tagged capabilities (`__ptr128`). Conversely, raw linear-memory snapshots (`Golem`, classical Wasm canisters) couple durability to compiler-chosen struct layouts and allocator state; as our `rustc 1.98.0-nightly` layout probe demonstrates, adding one trailing `u32` field to an unannotated `#[repr(Rust)]` 16-byte struct keeps `size_of == 16` identical while silently shifting interior field offsets (`tag: 8 -> 12`, `active: 10 -> 14`).
2. **Persistence-by-reachability vs. ephemeral FFI handles and class evolution:** Pure reachability (`PS-Algol`, `Napier88`, `PJama`) converts forgotten references into permanent storage leaks and fails at native FFI seams (`JNI` file descriptors, static initializers `<clinit>`, cached `CLOCK_MONOTONIC` or socket handles in `Aurora`), where opaque integer handles encode session-scoped kernel state that cannot be orthogonally restored.
3. **Whole-system checkpointing vs. granularity and Heisenbug immortality:** Atomic OS checkpointing (`KeyKOS`/`EROS`) guarantees causal consistency across capability graphs, yet couples unrelated workloads into global copy-on-write (`CoW`) epochs and preserves corrupted invariants across reboots ("immortal crash loops"). Per-partition checkpointing (`Aurora`) and explicit ACID workflow tables (`DBOS`) shrink blast radius, but cannot unilaterally roll back external network peers.
4. **Event-sourced replay determinism and code-evolution tombstones:** Stateless replay engines (`Temporal`, `Azure Durable Functions`, `Restate`) require workflow orchestrator code between yield points to be a pure deterministic function of recorded history. Ambient language nondeterminism (randomized hash-map iteration, wall clocks, unguarded FFI calls) or unversioned control-flow refactors trigger `NonDeterminismError`, forcing explicit `PatchMachine` version markers (`Temporal` `patched`/`deprecate_patch`), history compaction (`Continue-As-New` below Temporal's `50 * 1024` event / `50 MiB` limits), or immutable deployment pinning (`Restate`).
5. **The Output Commit boundary:** Across all four paradigms, external side effects cannot be rolled back after crossing the persistence boundary. Without either an output-commit barrier prior to emission or a durably pre-allocated deterministic idempotency key, a crash between external invocation and local journal/checkpoint commit causes duplicate irreversible side effects.

## Applicability

This report synthesizes and compares four distinct persistence and durable-execution families identified in `REPORT.json`:

- **Hardware / Virtual-ISA Single-Level Stores:** `IBM System/38` -> `AS/400` -> `IBM i` (specifically `IBM i 7.5` `ILE` pointer models `__ptr128` vs. Teraspace `__ptr64`, `TIMI` observability, and 16 MB classic single-level storage space limits). Findings about hardware pointer tags apply specifically to tagged-capability hardware (`IBM i` on `POWER` / ECC-multiplexed tag bits) and do not transfer automatically to untagged commodity x86-64/ARM64 page tables.
- **Language-Level Orthogonal Persistence & Persistent Memory:** `PS-Algol` (1983), `Napier88`, and `PJama` (1996–2000) characterize reachability-based orthogonal persistence in garbage-collected runtimes; `Px86` (Raad et al., POPL 2020) and `Corundum` (`NVSL/Corundum` commit `1685af69d9b34d6d2c918c69c3327023ac753f03`, ASPLOS 2021) characterize byte-addressable non-volatile memory (`NVMM`/PMEM) under explicit cache-line persistency (`CLWB`/`CLFLUSHOPT`/`SFENCE`) and Rust static type enforcement.
- **OS Checkpointing Single-Level Stores:** `KeyKOS` (1985), `EROS` (SOSP 1999), and `Coyotos` cover capability-nanokernel whole-system checkpointing; `Aurora SLS` (SOSP 2021) covers per-partition millisecond incremental checkpointing on FreeBSD for unmodified POSIX applications.
- **WebAssembly and Cloud Durable Execution:** Directly inspected at pinned upstream revisions: `golemcloud/golem` (`7ca9863405ba888f897a581e0dd973b3c95fc5e5`), `dfinity/motoko` (`acd6537b74b62801b0927ed9dfba240b3a4692a4`), `bytecodealliance/wasmtime` (`3ce2209872ccf1ea115914a81e020aef66a10c51`), `temporalio/temporal` (`4841d727dae93c08444a94e47149c0fb0e74d226`), `temporalio/sdk-core` (`8e7413bfd77b85ef35326aa4c2cf8473d556c6ea`), `restatedev/restate` (`7e9a3b235011bf749447aa48dda80c1c71e42bb0`), and `dbos-inc/dbos-transact-ts` (`12514c0677f0a5ba98124c8ee3ee38daca6de0a8`), supplemented by formal replay equivalence semantics from `Azure Durable Functions` (OOPSLA 2021) and rollback-recovery theory (Elnozahy et al., 2002).
- **Executable Probes:** Behavioral replay/output-commit traces were executed on CPython 3 on `x86_64-unknown-linux-gnu`; layout-shift measurements were compiled and executed with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` targeting `x86_64-unknown-linux-gnu`.

Findings compare architectural invariants, failure modes, FFI seams, and formal verification obligations across these systems rather than benchmarking peak throughput on a single hardware SKU.

## Findings

### 1. Cross-Paradigm Taxonomy and Architectural Trade-Off Matrix

Basis: normative + documentation + source + derived

Every durable system chooses four orthogonal design coordinates: (a) **unit of persistence** (whole OS, process partition, Wasm linear memory, typed object graph, or workflow event log), (b) **identity of code across time** (virtual ISA, typed GC schema, raw binary, or version-pinned handler), (c) **mechanism for surviving crashes** (atomic page/object checkpointing, hardware cache-line persistency + undo/redo logging, or deterministic replay from an append-only journal), and (d) **strategy at the external-world seam**.

| Paradigm / System | Persistence Unit | Crash Recovery Mechanism | Code / Schema Upgrade Behavior | FFI / Native Handle Seam | Determinism Requirement | Primary Failure Cliff |
|---|---|---|---|---|---|---|
| **IBM i (`TIMI` + `SLS`)** | 128-bit capability-addressed system objects (RAM + disk unified) | Hardware/LIC transparent paging over single-level virtual store | Automatic ISA re-translation via `*OBS` metadata; data objects persist independently | Dual pointer schism (`__ptr128` SLS vs. `__ptr64` transient Teraspace) | None (stateful execution) | 16 MB classic space ceiling; stripping `*OBS` breaks migration; Teraspace drops persistence |
| **PS-Algol / Napier88 / PJama** | Typed GC heap reachable from persistent root | Persistent object store + pointer swizzling + checkpoint/stabilize | Class-identity / closure-environment collision across recompilation | `JNI` C descriptors & `<clinit>` static initializers break silently | None | Accidental persistence leaks; swizzling read-barrier overhead; stale native handles |
| **KeyKOS / EROS / Coyotos** | Whole-system 4 KB pages + kernel capability nodes | Periodic atomic `CoW` whole-system checkpoint + disk log | New domains deployed alongside old; no automatic live struct migration | Non-persistent capabilities / Space Banks invalidated on boot | None | Global checkpoint coupling; `CoW` page-fault storms; immortal crash-loop checkpoints |
| **Aurora SLS** | Per-partition FreeBSD process tree + local kernel objects | 10–100 ms incremental `CoW` / dirty-page partition snapshots to NVMe | Process restart or new partition image | External TCP sockets, GPU/DRM contexts, `CLOCK_MONOTONIC` drift | None | Leaky POSIX FD abstraction at external network/device endpoints |
| **Corundum (`Px86` NVMM)** | Pool-branded Rust persistent heaps (`Pbox<T, P>`, `Prc<T, P>`) | Explicit `CLWB`/`SFENCE` + compiler-enforced undo-log transactions | Manual pool schema migration; fixed-offset pool pointers | `!PSafe` rejects volatile pointers, but `UnsafeCell` / `extern "C"` bypasses checks | None | Unpersisted read-from (`Px86` dirty reads) if flushes missed; C/FFI unlogged writes |
| **Golem (Wasm Component)** | Sandboxed Wasm linear memory + indexed oplog | Oplog replay from genesis or `SnapshotConfirmed` checkpoint | Automatic replay onto new component, or manual `SnapshotAssistedUpdate` | `WIT` types component edge; linear memory inside component stays untyped | Strict between host imports (Wasm NaN / `relaxed-simd` caveats) | Snapshot layout coupling; `FailedUpdate` when replay diverges on upgraded binary |
| **ICP Motoko (`EOP`)** | 64-bit Wasm main memory retained in place across upgrades | Replicated deterministic page-level orthogonal persistence | $O(1)$ in-place retention gated by static stable-subtyping (`M0170`/`M0216`) + multi-migration chains | Rust canisters lack compiler heap maps and fall back to manual `ic-stable-structures` | Strict replicated consensus determinism | Classical `pre_upgrade` instruction-limit bricking (escaped by EOP / stable structures) |
| **Temporal / Azure Durable Functions** | Append-only workflow event history | Deterministic replay of workflow code from entry point | Explicit `patched()` / `deprecate_patch()` tombstones or Build ID worker versioning | Arbitrary library/FFI calls bypass language replay sandboxes | Strict pure determinism of orchestrator between yield points | `NonDeterminismError` on unordered maps/clocks/refactors; `50 * 1024` event / `50 MiB` history caps (`Continue-As-New`) |
| **Restate** | Per-invocation durable execution journal + K/V virtual object state | Deterministic journal replay of `ctx.run` / calls / sleeps | Immutable deployment-revision pinning for in-flight invocations | Unwrapped external I/O outside `ctx.run` violates replay | Strict determinism outside journaled side-effect blocks | Long-lived sleeping workflows pin legacy deployments indefinitely (CVE patching tension) |
| **DBOS (`dbos-transact-ts`)** | Workflow checkpoints + application tables in one PostgreSQL DBMS | ACID commit of app mutation + checkpoint; step replay on restart | Standard app deploy + SQL schema migration (uncoupled unless managed) | External HTTP/Stripe calls fall outside local Postgres ACID -> Saga compensations | Deterministic step ordering; transactions must be retry-safe (`40001`) | Side effects inside `@transaction` replay on Postgres serialization retries; missing Saga compensations |

---

### 2. Hardware/Virtual-ISA Capability Single-Level Stores (`IBM System/38` and `IBM i`)

Basis: documentation + derived

#### 2.1 TIMI Observability (`*OBS`) and 128-Bit Hardware-Tagged Capabilities
Introduced in IBM System/38 (1978) and carried through AS/400 into `IBM i`, the **Technology Independent Machine Interface (`TIMI`)** separates the archival representation of compiled software from the physical processor ISA. High-level compilers (RPG, COBOL, C, C++, CL) target an abstract object-oriented virtual instruction set above **System Licensed Internal Code (`SLIC` / `LIC`)**. Program objects retain **observability (`*OBS`)**—the high-level `TIMI` intermediate representation—alongside the translated native machine code cache. When IBM transitioned the installed base from its 48-bit CISC `IMPI` architecture to 64-bit `PowerPC` RISC in 1995 (and across subsequent `POWER` generations), `LIC` re-translated stored `*OBS` representations to native machine code automatically on program restore or first invocation without source recompilation and while preserving the live persistent object store.

Every single-level-store pointer (`__ptr128`) is a **128-bit hardware-tagged capability** aligned on a 16-byte boundary and protected by an out-of-band hardware tag bit per 16-byte granule (historically stored in wide DRAM and on modern `POWER` silicon multiplexed into memory ECC metadata). Tag integrity obeys a strict hardware invariant:
- Only privileged `TIMI` pointer-construction instructions set the tag bit;
- Any unprivileged integer overwrite, partial-byte overwrite, or unaligned `memcpy` into a 16-byte pointer slot clears the tag bit in hardware;
- Dereferencing an untagged 128-bit word traps synchronously with a pointer-specification/protection exception, preventing arbitrary pointer forgery across the shared persistent address space.

#### 2.2 The 16 MB Single-Level Store Ceiling vs. Teraspace (`__ptr128` vs. `__ptr64`)
Classic `IBM i` Single-Level Storage (`SLS`) encapsulates persistent storage as individually addressed typed system objects whose contiguous byte-addressable space was historically bounded at **16 MB** (16 MB minus one page due to 24-bit intra-space offsets in classic System/38 microcode). Porting POSIX/C/C++/Java applications that assume multi-gigabyte flat heaps forced IBM to add **Teraspace** (introduced in OS/400 V4R4): a job-local, transient contiguous virtual address space spanning hundreds of terabytes, addressed via 8-byte untagged pointers (`__ptr64`, `DTAMDL(*LLP64)`).

This creates an instructive **dual-pointer FFI schism**:
1. **Persistence loss:** Allocations inside Teraspace are job-scoped and transient; they forfeit orthogonal persistence entirely.
2. **ABI and truncation hazards:** Mixing `DTAMDL(*P128)` (16-byte SLS pointers) and `DTAMDL(*LLP64)` (8-byte Teraspace pointers) across `ILE` module calls risks silent pointer truncation or capability-tag stripping when a 128-bit pointer passes through an 8-byte C `void*` or unaligned byte buffer.
3. **Persistent-to-transient escape:** Storing a transient Teraspace address inside a persistent `SLS` object produces a dangling pointer once the originating job terminates.

*Design lesson (derived):* Surviving multi-decade hardware migrations requires retaining typed, ISA-neutral observable IR (`*OBS`) and treating native code strictly as a discardable cache, while decoupling pointer capability width from integer offset width (`usize != sizeof(void*)`) and statically stratifying persistent regions from transient scratch heaps.

---

### 3. Language-Level Orthogonal Persistence (`PS-Algol`, `Napier88`, `PJama`) and Typed NVMM (`Px86`, `Corundum`)

Basis: normative + documentation + source + derived

#### 3.1 Three Axioms of Orthogonal Persistence and Their Failure Modes
Atkinson, Bailey, Chisholm, Cockshott, and Morrison (1983, `DOI:10.1093/comjnl/26.4.360`) defined orthogonal persistence in `PS-Algol` via three principles later extended to first-class persistent closures in `Napier88` and to the JVM in `PJama`:
1. **Persistence Independence:** Programs behave identically over transient and persistent data;
2. **Data Type Orthogonality:** All data types—including closures/procedures and metadata—have equal rights to persistence;
3. **Persistence Identification by Reachability:** Any object transitively reachable from a designated persistent root survives automatically, governed by a persistent garbage collector.

Decades of production and prototype experience (`Napier88`, `PJama` retrospectives by Atkinson & Jordan 1999–2000) exposed four structural friction cliffs:
- **Accidental Persistence Leaks:** Because reachability determines durability, a single forgotten pointer from a persistent root into a transient cache, debug buffer, or closure environment permanently retains megabytes of ephemeral state in the durable store (the persistent dual of a GC memory leak).
- **Pointer Swizzling Overhead:** Persistent Object Identifiers (`PIDs`) on disk exceed RAM address space and must be translated ("swizzled") into in-RAM virtual addresses either lazily via software read barriers (high steady-state CPU tax) or eagerly via virtual-memory page-fault traps (`mprotect` faults, poor for sparse random graphs).
- **Class Identity and `<clinit>` Collision (`PJama`):** Persisting `java.lang.Class` objects and static fields collides with Java's "fresh JVM boot" assumption. Recompiling a class creates a nominal identity clash with existing persisted instances of the older layout, while static initializers (`<clinit>`) that open OS resources ran once at initial class load years earlier and do not re-run on subsequent store mounts—leaving static fields holding stale handles.
- **The `JNI` Native-State Wall:** Standard JDK classes (`java.io.FileDescriptor`, `java.net.Socket`, AWT peers, `java.lang.Thread`) hide opaque C integers or `malloc` pointers to transient OS kernel tables. Persisting those integers orthogonally produces silent handle invalidation or accidental aliasing with unrelated OS descriptors after restart.

#### 3.2 Weak Hardware Persistency (`Px86`) and Compile-Time Persistent Safety (`Corundum`)
Byte-addressable non-volatile memory (`NVMM` / PMEM) reintroduces orthogonal load/store persistence at the hardware level, yet CPU caches remain volatile unless protected by battery-backed `eADR`. Raad, Wickerson, Neiger, and Vafeiadis (POPL 2020, `DOI:10.1145/3371079`) formalized **`Px86`**, demonstrating that coherence visibility order (`rf`/`mo`) and non-volatile persistence order (`nvo`) diverge:
- Under `Px86`, `CLFLUSH` is strongly ordered with stores, whereas `CLFLUSHOPT` and `CLWB` execute asynchronously with respect to ordinary stores and require a subsequent `SFENCE` to guarantee durability ordering before a dependent publish write.
- **Unpersisted Read-From ("Dirty-Read") Anomaly:** Thread 1 writes `x = 1` (sitting dirty in L1/L3 cache, unflushed). Thread 2 reads `x == 1` via cache coherence, then writes `y = 1`, executes `CLWB(&y); SFENCE`. If power fails immediately, NVM recovers with `y == 1` and `x == 0`, breaking causal consistency and Durable Linearizability (Izraelevitz, Mendes, Scott, DISC 2016) unless every causal dependency is flushed before publish or on read ("flush-on-read").

`Corundum` (`NVSL/Corundum` commit `1685af69d9b34d6d2c918c69c3327023ac753f03`; ASPLOS 2021, `DOI:10.1145/3445814.3446710`) proves that Rust's type system can eliminate four classic C/PMDK persistent-memory bug classes at compile time:
1. **Persistent-to-Volatile (`P -> V`) pointer leaks:** Prohibited statically via a `!PSafe` marker trait rejecting raw volatile references/pointers inside persistent structs.
2. **Cross-pool pointer aliasing:** Prevented by pool-branded smart pointers (`Pbox<T, P>`, `Prc<T, P>`, `Parc<T, P>` in `src/boxed.rs`, `src/prc.rs`, `src/sync/parc.rs`) storing pool-relative offsets rather than process-local virtual addresses.
3. **Unlogged partial mutations:** Opening `&mut T` on persistent cells requires passing an active transactional `&Journal<P>` capability token, enforcing undo logging before mutation.
4. **Allocation-before-link crashes:** Allocation and root linkage occur inside the same transactional journal scope.

*FFI and verification boundary (source + derived):* `Corundum` cannot enforce `!PSafe` or transactional undo logging across `extern "C"` boundaries, `UnsafeCell` escape hatches, or standard-library collections (`std::collections::HashMap`, `Box`) that are not polymorphic over pool-branded pointers and transactional journals.

---

### 4. OS-Level Atomic Checkpointing Single-Level Stores (`KeyKOS`, `EROS`, `Coyotos`, `Aurora SLS`)

Basis: normative + documentation + derived

#### 4.1 Whole-System Capability Checkpointing (`KeyKOS`, `EROS`, `Coyotos`)
Norm Hardy's `KeyKOS` (ACM SIGOPS OSR 1985) and Jonathan Shapiro, Jonathan Smith, and David Farber's `EROS` (SOSP 1999, `DOI:10.1145/319151.319163`) implement orthogonal persistence inside a pure capability nanokernel:
- Every persistent kernel object—4 KB pages and fixed-size capability nodes—is cached in RAM as a software single-level store.
- Periodically (seconds to minutes), the kernel freezes scheduling briefly (milliseconds), marks dirty pages copy-on-write (`CoW`), captures a globally consistent snapshot of capability nodes and registers, and flushes dirty pages asynchronously to an on-disk checkpoint log using dependency-ordered state caching.
- **Explicit Ephemeral Capabilities:** Hardware device drivers, network sockets, and volatile scratch spaces are isolated behind **Space Banks** and explicit non-persistent/restart capabilities that are deterministically rescinded upon reboot, avoiding `PJama`'s silent stale-FD corruption.

Three fundamental failure modes emerged across `KeyKOS`, `EROS`, and `Coyotos` (leading `Coyotos` to make whole-system orthogonal persistence optional):
1. **Global Epoch Coupling & `CoW` Storms:** Coupling mutually distrusting applications into one system-wide checkpoint forces high-durability services to trigger global `CoW` page-fault storms across unrelated memory-intensive workloads.
2. **Heisenbug Immortality:** Faithful state restoration preserves corrupted application invariants across reboots. Unlike crash-only stateless software where restarting clears transient state corruption, a corrupted pointer or deadlock committed to a checkpoint traps the system in an **immortal crash loop** unless administrative rollback to an older checkpoint generation or live patching intervenes.
3. **Rollback Replay Against External Peers:** Rolling a whole OS back by 3 seconds unsends messages already observed by remote hosts—causing catastrophic nonce reuse in stateful cryptographic protocols (TLS, WireGuard) unless monotonic hardware/TPM epoch counters are mixed into session state.

#### 4.2 Per-Partition POSIX Single-Level Storage (`Aurora SLS`)
`Aurora` (Tsalapatis, Hancock, Barnes, Mashtizadeh, SOSP 2021, `DOI:10.1145/3477132.3483563`) decouples checkpoint granularity from the whole kernel by introducing **SLS partitions** on FreeBSD, achieving 10–100 ms incremental checkpoints over NVMe for unmodified POSIX applications (`RocksDB`, `Firefox`, `Mosh`). Aurora serializes local FreeBSD kernel objects (`vm_map`s, `vnode` references, pipes, Unix domain sockets, `kqueue`s, SysV/POSIX shared memory), allowing storage engines like `RocksDB` to disable custom WAL persistence without sacrificing durability.

However, Aurora exposes the **POSIX File-Descriptor Seam**: POSIX conflates locally checkpointable kernel state (pipes, local files, `memfd`s) with external distributed endpoints (TCP sockets, GPU/DRM contexts, raw hardware `mmap`s) under a single untyped `int` file descriptor. On partition restore after a crash or migration, external TCP sessions cannot be unilaterally resurrected without remote peer cooperation, and user-space C libraries (`libc`, OpenSSL, `libuv`) that cache `CLOCK_MONOTONIC` timestamps, PIDs, or socket state experience discontinuous time jumps and desynchronized invariants.

---

### 5. WebAssembly Orthogonal Snapshots (`Golem`, `Motoko EOP`, `Wasmtime`)

Basis: source + execution + derived

#### 5.1 Golem Oplog Replay and Snapshot-Assisted Upgrades
Direct inspection of `golemcloud/golem` (`7ca9863405ba888f897a581e0dd973b3c95fc5e5`, `golem-common/src/model/oplog/mod.rs` and `golem-common/src/base_model/oplog/mod.rs`) shows how a WebAssembly Component Model (`WIT`) durable runtime fuses orthogonal linear-memory execution with an indexed append-only oplog:
- Worker execution runs inside a sandboxed Wasm linear memory while every external host interaction (RPC, WASI clocks, randomness, HTTP) is recorded as an `OplogEntry`.
- Periodic linear-memory + filesystem compaction uses a **two-phase confirmation protocol**: `OplogEntry::Snapshot` (`golem-common/src/base_model/oplog/mod.rs`, lines 599–619) explicitly documents that a `filesystem_snapshot` is usable **only after** a matching `OplogEntry::SnapshotConfirmed` entry (lines 1035–1043) is appended to the oplog, preventing partial snapshot corruption on crash.
- **Upgrade Mechanics (`PendingUpdate` / `SuccessfulUpdate` / `FailedUpdate`):** Lines 339–392 define `PendingUpdate { description: UpdateDescription }`, `SuccessfulUpdate { snapshot_assisted_details: Option<SnapshotAssistedUpdateDetails> }`, and `FailedUpdate { snapshot_assisted_details, snapshot_fault }`. Golem explicitly supports two upgrade paths:
  1. *Automatic (replay-based) updates:* Instantiate the new component binary and replay the historical oplog against it—which fails (`FailedUpdate`) if control flow or imported-call sequences diverged.
  2. *Manual (snapshot-assisted) updates:* Invoke a developer-supplied snapshot serializer on the old component version, persist the semantic payload, and feed it to a load hook on the new component version—bypassing raw linear-memory layout incompatibility.

#### 5.2 Empirical Proof of Raw Linear-Memory Snapshot Fragility Across Recompilation
Basis: execution (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`)

Why can a raw byte snapshot of Wasm linear memory (or any LLVM-compiled Rust/C++ heap) never be safely overlaid onto a recompiled binary without compiler layout guarantees? Running our standalone probe `/tmp/probe_layout_shift.rs` (source preserved in **Evidence**) compares `WorkerStateV1 { active: bool, counter: u64, tag: u16 }` against `WorkerStateV2` obtained purely by appending one trailing field `epoch: u32`:

```text
repr(Rust) V1: size=16 offsets=(active:10, counter:0, tag:8)
repr(Rust) V2: size=16 offsets=(active:14, counter:0, tag:12, epoch:8)
repr(C)    V1: size=24 offsets=(active:0, counter:8, tag:16)
repr(C)    V2: size=24 offsets=(active:0, counter:8, tag:16, epoch:20)
```

Under Rust's default `#[repr(Rust)]` layout optimization, **total `size_of` remained identical (`16` bytes)**, yet appending `epoch: u32` caused the compiler to pack `epoch` into offset `8` and shift `tag` (`8 -> 12`) and `active` (`10 -> 14`). Restoring a raw linear-memory image captured under `V1` into `V2` passes any coarse size check while silently misinterpreting `tag` and `active` bytes as `epoch` and reading uninitialized padding as `active: bool` (triggering immediate Rust Undefined Behavior on invalid `bool` bit patterns outside `{0, 1}`). In addition to struct layout shifts, raw linear-memory snapshots also hardcode allocator slab metadata and Wasm `__indirect_function_table` indices that shift across recompilations.

#### 5.3 Hardware-Dependent Wasm Nondeterminism (`Wasmtime`)
Basis: source (`bytecodealliance/wasmtime`, commit `3ce2209872ccf1ea115914a81e020aef66a10c51`)

Strict oplog replay across heterogeneous x86-64 and ARM64 worker fleets requires disabling or canonicalizing two hardware-dependent Wasm features documented directly in `crates/wasmtime/src/config.rs`:
- **`wasm_relaxed_simd` (lines 1251–1263):** Wasmtime explicitly warns that the relaxed SIMD proposal *"introduces instructions that are allowed to have different behavior on different architectures, primarily to afford an efficient implementation on all architectures. This means, however, that the same module may execute differently on one host than another."*
- **`cranelift_nan_canonicalization` (lines 1747–1754):** Sets Cranelift's `"enable_nan_canonicalization"` flag so floating-point arithmetic producing NaN writes canonical bit patterns rather than host-CPU-dependent NaN payloads (which otherwise leak into deterministic replay whenever guest code inspects raw `f32::to_bits`/`f64::to_bits` or hashes floats).

#### 5.4 Internet Computer (`ICP`) Pre-Upgrade Bricking vs. Motoko Enhanced Orthogonal Persistence (`EOP`)
Basis: source (`dfinity/motoko`, commit `acd6537b74b62801b0927ed9dfba240b3a4692a4`) + documentation

On the Internet Computer (`ICP`), replicated Wasm smart-contract actors ("canisters") persist Wasm main linear memory automatically across messages, yet classical canister upgrades wiped Wasm main memory while preserving a separate byte-addressed **Stable Memory** space. Under classical orthogonal persistence, applications had to serialize their entire live heap into Stable Memory inside a `pre_upgrade` hook and deserialize it in `post_upgrade`. Once a canister's live heap grew beyond what could be serialized within a single block's deterministic instruction cap, `pre_upgrade` trapped—**permanently bricking the canister against future upgrades**.

Two divergent architectural escapes emerged on the exact same Wasm runtime:
1. **Rust canisters (`ic-stable-structures`):** Abandoned orthogonal persistence for large state, manually placing fixed-schema B-trees and logs directly inside Stable Memory (reintroducing explicit serialization and manual `#[repr(C)]`/fixed-byte codecs).
2. **Motoko Enhanced Orthogonal Persistence (`EOP`):** Retains 64-bit Wasm main memory **in place across upgrades in $O(1)$ time** independent of heap size, guarded by a static compiler compatibility check in `src/mo_frontend/stability.ml` (lines 223–264). Direct source inspection confirms four exact compiler diagnostics gating safe upgrades:
   - **`M0169`**: `"stable variable '<lab>' of <prev> cannot be implicitly discarded. The variable can only be dropped by an explicit migration function."`
   - **`M0170`**: `"stable variable '<lab>' is not compatible with <prev>. Previous type <T1> is not a subtype of <T2> ... Write an explicit migration function to convert it."`
   - **`M0216`**: `"stable variable '<lab>' implicitly drops data of <prev>. Previous type <T1> is not a stable subtype of <T2> ... The data can only be dropped by an explicit migration function."`
   - **`M0263`**: `"<prev> does not contain the stable variable '<lab>'. The migration function cannot require this variable as input."`
   Moreover, `chain_input_fields` (lines 272+) validates multi-step enhanced migration chains across intermediate versions. Motoko achieves $O(1)$ in-place retention specifically because its compiler controls the managed GC heap graph and tags every stable root—whereas LLVM-compiled Rust/C++ erases heap type descriptors into untyped allocator bytes.

---

### 6. Event-Sourced Deterministic Replay (`Temporal`, `Azure Durable Functions`, `Restate`) and Database-Oriented Workflows (`DBOS`)

Basis: normative + source + execution + derived

#### 6.1 Formal Replay Equivalence and Non-Determinism Traps
Burckhardt, Gillum, Justo, Kallas, McMahon, and Meiklejohn (`Azure Durable Functions`, OOPSLA 2021, `DOI:10.1145/3485510`) prove that event-sourced record-and-replay execution ($E_{\text{replay}}$) refines ideal fault-free execution ($E_{\text{ideal}}$) **if and only if** orchestrator execution between external yield points is a **pure deterministic function of its history prefix**.

In mainstream ambient-effect languages (`Go`, `Java`, `TypeScript`, `Python`, `Rust`), replay soundness is violated silently by:
- Randomized hash-table iteration (`Rust` `HashMap` `SipHash` random seed, `Go` randomized `map` iteration, Python `PYTHONHASHSEED`);
- Ambient wall-clock reads (`System.currentTimeMillis()`, `Instant::now()`), PRNG draws (`Math.random()`), UUIDv4 generation, or thread scheduling races;
- Third-party libraries or native FFI (`libc`, OpenSSL, Python C-extensions) that bypass language-level VM sandboxes (`Temporal` TypeScript/Python sandboxes cannot intercept C extensions);
- Unpatched control-flow refactorings that reorder, insert, or remove emitted commands.

#### 6.2 `Temporal` Patch State Machine and History-Size Cliffs
Direct source inspection of `temporalio/sdk-core` (`8e7413bfd77b85ef35326aa4c2cf8473d556c6ea`, `crates/sdk-core/src/worker/workflow/machines/patch_state_machine.rs`) and `temporalio/temporal` (`4841d727dae93c08444a94e47149c0fb0e74d226`, `common/dynamicconfig/constants.go`) establishes the exact operational mechanics:

1. **The 12-Case `PatchMachine` Contract (`patch_state_machine.rs`, lines 1–18):** To evolve long-running workflows without breaking replay of in-flight histories, developers guard new branches with `patched(change_id)` and later `deprecate_patch(change_id)`. The state machine (`Executing -> MarkerCommandCreated -> Notified` vs. `Replaying -> MarkerCommandCreatedReplaying -> Notified`) records a `PATCH_MARKER_NAME` marker command on fresh execution:
   - When *not replaying* and code calls `patched`: records marker and returns `true`.
   - When *replaying* and history *contains* the marker (normal or deprecated): returns `true`.
   - When *replaying* and history *lacks* the marker: returns `false` (executing the legacy code path!).
   - When *replaying* and history contains a non-deprecated marker while code *removed* `patched`: triggers a mismatch (`No matching command / workflow does not support this version` -> `NonDeterminismError`).
   - Only after all histories carrying a non-deprecated marker drain (via an intermediate `deprecate_patch` deployment whose marker is safely ignored by code with no `patched` call) can the tombstone branch be deleted.
2. **Hard History Caps and Manual `Continue-As-New` (`constants.go`, lines 477–497):** Because replay cost grows as $\Omega(T)$ with event count, Temporal enforces hard per-execution server limits:
   - `HistorySizeLimitError` (`"limit.historySize.error"`): **`50 * 1024 * 1024` bytes (50 MiB)**;
   - `HistoryCountLimitError` (`"limit.historyCount.error"`): **`50 * 1024` events (51,200 events)**.
   Infinite-horizon workflows must periodically invoke **`Continue-As-New`**, manually serializing live local variables into the seed input of a fresh workflow execution—partially reintroducing manual state marshaling.

#### 6.3 `Restate` Immutable Deployment Pinning vs. `DBOS` Co-Located ACID Transactions
- **Restate (`restatedev/restate`, `7e9a3b235011bf749447aa48dda80c1c71e42bb0`):** Uses a durable execution journal paired with Virtual Objects (keyed single-writer K/V actors) and **immutable deployment-revision pinning**: in-flight invocations remain routed to the exact service deployment revision that started them, while new invocations hit the newly registered revision. This avoids `patched()` tombstones for short-to-medium workflows, yet introduces a **security-patching vs. longevity dilemma**: a workflow sleeping for months pins an old container/binary revision indefinitely unless explicitly drained or migrated, obstructing emergency CVE remediation in the pinned binary.
- **DBOS (`dbos-inc/dbos-transact-ts`, `12514c0677f0a5ba98124c8ee3ee38daca6de0a8`; PVLDB 2022, `DOI:10.14778/3485450.3485454`):** Stores workflow step checkpoints, queues, and application state inside one PostgreSQL DBMS. For pure database steps (`transaction`), mutating an application table and recording workflow progress commit in **one local ACID transaction**, eliminating the dual-write / transactional-outbox race between an external orchestrator (`Temporal`) and an application database. Two boundaries remain sharp:
  1. Any unmarked external side effect executed inside a database transaction block re-executes upon PostgreSQL serialization retries (`SQLSTATE 40001`), violating once-only intent.
  2. Any external non-DBMS side effect (`step` calling a payment API, S3, or external microservice) exits local Postgres ACID atomicity and falls back to **Saga compensating transactions** and at-least-once retries.

---

### 7. The Output Commit Problem and Executable Replay / Idempotency Verification

Basis: normative + execution + derived

Elnozahy, Alvisi, Wang, and Johnson (*ACM Computing Surveys* 2002, `DOI:10.1145/568522.568525`) formalize the **Output Commit Problem**: no message or irreversible effect released to the outside world may depend on local state that could be lost in a subsequent crash-recovery rollback. Every paradigm in this report hits this exact physical boundary:
- Whole-OS and partition checkpointing (`EROS`, `Aurora`) must either stall external network output until a durable checkpoint flushes (adding 10–100 ms latency) or risk emitting duplicate/phantom outputs after rollback.
- Event-sourced engines (`Temporal`, `Restate`, `Golem`, `DBOS`) execute external side effects inside activities/steps (`ctx.run`, `ImportedFunctionInvoked`) where a crash **after** the remote API commits but **before** the local journal flushes forces re-execution on recovery.

Running our standalone deterministic replay & output-commit probe `/tmp/probe_durable_persistence.py` (preserved verbatim in **Evidence**) reproduces all six regimes deterministically:

```text
[1A-Clean] initial=90, replayed=90, ledger_calls=1
[1B-HashOrder] caught NonDeterminismError: History divergence at idx=0: recorded=(Activity:Price, 'apple') vs replayed=(Activity:Price, 'pear')
[1C-UnpatchedUpgrade] caught NonDeterminismError: History divergence at idx=0: recorded=(Activity:Price, 'apple') vs replayed=(Activity:Audit, 2)
[1D-PatchedUpgrade] old_history_result=90, new_history_len=5, new_result=90
[1E-OutputCommit-Naive] total_charged=200 (expected 100 -> DUPLICATE SIDE EFFECT)
[1F-OutputCommit-IdemKey] total_charged=100 (exact-once preserved)
```

*Verification architectural consequence (derived):* Compositional verification across crashes requires stratifying FFI and host calls into four explicit effect grades:
1. **`PureDet`**: Pure deterministic computation (freely replayable; forbids ambient clocks, randomized hashing, unguarded FFI).
2. **`LocalDurable`**: Mutations committed atomically within the local persistent store or DBMS transaction (`Corundum` journal, `DBOS` ACID transaction, `Motoko EOP` state).
3. **`IdempotentExternal(Key)`**: Remote side effects gated by a deterministically derived, durably pre-committed idempotency key (preserving end-to-end exact-once effect across crash-before-journal-flush as in `[1F]`).
4. **`IrreversibleExternal`**: Non-idempotent physical/network actions requiring a synchronous **Output Commit barrier** prior to emission and statically forbidding speculative rollback.

## Boundaries

- **Hardware benchmark throughput (not examined):** Quantitative throughput and tail-latency comparisons across real IBM POWER10 `SLS`, Intel Optane/CXL-PMEM `Corundum`, FreeBSD NVMe `Aurora`, and clustered `Temporal`/`Restate`/`DBOS` deployments were not benchmarked in this investigation.
- **Proprietary `IBM i` `LIC` / `TIMI` internals (not examined / unsupported for source inspection):** `IBM i` `SLIC` translation logic and POWER ECC tag-bit microcode are closed-source proprietary artifacts; findings rely on public IBM i 7.5 documentation and architecture literature rather than source inspection.
- **Exact `Coyotos` production deployment history (not examined):** `Coyotos` was examined at the architectural level (capability Space Banks and reconsideration of mandatory whole-system persistence) rather than via full source audit of `CapROS`/`Coyotos` repositories.
- **WasmGC / typed persistent linear-memory proposals (unknown):** Whether future WasmGC + Component Model heap-snapshot standards will enable Motoko-style $O(1)$ layout-checked upgrades for Rust/C++ Wasm guests without forfeiting zero-cost linear-memory performance remains an open research question.
- **Scope boundary (`known not to apply`):** Hardware capability-tagged single-level store invariants (`IBM i __ptr128`) do **not** apply to standard untagged POSIX `mmap`/`MAP_SHARED` persistence, where ordinary integer arithmetic can forge pointers and silent byte overwrites are not trapped by memory hardware. Similarly, `DBOS`'s local PostgreSQL ACID atomicity does **not** extend across external non-PostgreSQL API calls.
- **Stronger conclusion not established:** Passing deterministic replay tests on one CPU architecture (`x86_64`) does **not** establish cross-architecture replay determinism (`x86_64` <-> `aarch64`) for Wasm or native runtimes unless floating-point NaN canonicalization is enabled and architecture-dependent SIMD (`relaxed-simd`) is disabled.

## Evidence

### Normative Specifications and Peer-Reviewed Primary Literature
- **PS-Algol:** M. P. Atkinson, P. J. Bailey, K. J. Chisholm, P. W. Cockshott, R. Morrison, *"An Approach to Persistent Programming"*, *The Computer Journal*, Vol. 26, No. 4, pp. 360–365, 1983 (`DOI:10.1093/comjnl/26.4.360`).
- **EROS / KeyKOS:** J. S. Shapiro, J. M. Smith, D. J. Farber, *"EROS: A Fast Capability System"*, SOSP 1999 (`DOI:10.1145/319151.319163`); N. Hardy, *"The KeyKOS Architecture"*, *ACM SIGOPS Operating Systems Review* 19(4), 1985.
- **Aurora SLS:** E. Tsalapatis, R. Hancock, T. Barnes, A. J. Mashtizadeh, *"The Aurora Single Level Store Operating System"*, SOSP 2021 (`DOI:10.1145/3477132.3483563`).
- **Px86:** A. Raad, J. Wickerson, G. Neiger, V. Vafeiadis, *"Persistency Semantics of the Intel-x86 Architecture"*, PACMPL Vol. 4, POPL 2020, Art. 11 (`DOI:10.1145/3371079`).
- **Corundum:** M. Hoseinzadeh, S. Swanson, *"Corundum: Statically-Enforced Persistent Memory Safety"*, ASPLOS 2021 (`DOI:10.1145/3445814.3446710`).
- **Azure Durable Functions:** S. Burckhardt, C. Gillum, D. Justo, K. Kallas, C. McMahon, C. S. Meiklejohn, *"Durable Functions: Semantics for Stateful Serverless"*, PACMPL Vol. 5, OOPSLA 2021 (`DOI:10.1145/3485510`).
- **DBOS:** A. Skiadopoulos et al., *"DBOS: A DBMS-oriented Operating System"*, PVLDB 2022 (`DOI:10.14778/3485450.3485454`).
- **Output Commit:** E. N. Elnozahy, L. Alvisi, Y.-M. Wang, D. B. Johnson, *"A Survey of Rollback-Recovery Protocols in Message-Passing Systems"*, *ACM Computing Surveys* 34(3), pp. 375–408, 2002 (`DOI:10.1145/568522.568525`).
- **IBM i:** IBM i 7.5 ILE Concepts documentation (Single-Level Storage 16 MB object spaces, `__ptr128` vs. Teraspace `__ptr64` / `*LLP64`, TIMI `*OBS` observability); F. G. Soltis, *Inside the AS/400* / *Fortress Rochester*.

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`golemcloud/golem` @ `7ca9863405ba888f897a581e0dd973b3c95fc5e5`**:
  - `golem-common/src/model/oplog/mod.rs` (`EntityAttribution`, `OplogEntry::check_well_formed`).
  - `golem-common/src/base_model/oplog/mod.rs` lines 339–392 (`PendingUpdate`, `SuccessfulUpdate { snapshot_assisted_details }`, `FailedUpdate { snapshot_assisted_details, snapshot_fault }`), lines 599–619 (`Snapshot`), lines 1035–1043 (`SnapshotConfirmed`).
- **`dfinity/motoko` @ `acd6537b74b62801b0927ed9dfba240b3a4692a4`**:
  - `src/mo_frontend/stability.ml` lines 223–276 (`M0169`, `M0170`, `M0216`, `M0263` stable-subtyping and explicit migration diagnostics; `chain_input_fields` enhanced multi-migration verification).
- **`bytecodealliance/wasmtime` @ `3ce2209872ccf1ea115914a81e020aef66a10c51`**:
  - `crates/wasmtime/src/config.rs` lines 1251–1263 (`wasm_relaxed_simd` cross-architecture nondeterminism warning) and lines 1747–1754 (`cranelift_nan_canonicalization`).
- **`temporalio/sdk-core` @ `8e7413bfd77b85ef35326aa4c2cf8473d556c6ea`**:
  - `crates/sdk-core/src/worker/workflow/machines/patch_state_machine.rs` lines 1–68 (`PatchMachine` 12-case replay/patching truth table and FSM transitions).
- **`temporalio/temporal` @ `4841d727dae93c08444a94e47149c0fb0e74d226`**:
  - `common/dynamicconfig/constants.go` lines 477–497 (`HistorySizeLimitError = 50*1024*1024`, `HistoryCountLimitError = 50*1024`).
- **`restatedev/restate` @ `7e9a3b235011bf749447aa48dda80c1c71e42bb0`**:
  - `Cargo.toml` workspace layout (`restate-service-protocol`, `restate-rocksdb`, `restate-bifrost`, `restate-partition-store`, `restate-invoker-impl`) and `crates/service-protocol/src/lib.rs`.
- **`dbos-inc/dbos-transact-ts` @ `12514c0677f0a5ba98124c8ee3ee38daca6de0a8`** and **`NVSL/Corundum` @ `1685af69d9b34d6d2c918c69c3327023ac753f03`**:
  - `README.md` architectural contracts (Postgres-backed durable workflows/steps in DBOS; `Pbox<T>`, `Prc<T>`, `Parc<T>` and Zenodo DOI `10.5281/zenodo.4539743` in Corundum).

### Preserved Standalone Execution Probes (Observed 2026-11-19)

#### Probe 1A: Deterministic Replay, Patch Tombstones, and Output Commit (`probe_durable_persistence.py`)
```python
#!/usr/bin/env python3
import hashlib

class NonDeterminismError(Exception):
    pass

class ReplayRuntime:
    def __init__(self, history=None, crash_after_step=None):
        self.history = list(history or [])
        self.cursor = 0
        self.crash_after_step = crash_after_step
        self.steps_executed = 0

    def record_or_replay(self, cmd_type, payload, fn):
        if self.cursor < len(self.history):
            ev_type, ev_payload, ev_result = self.history[self.cursor]
            if ev_type != cmd_type or ev_payload != payload:
                raise NonDeterminismError(
                    f"History divergence at idx={self.cursor}: "
                    f"recorded=({ev_type}, {ev_payload!r}) vs replayed=({cmd_type}, {payload!r})"
                )
            self.cursor += 1
            return ev_result
        result = fn()
        if self.crash_after_step is not None and self.steps_executed == self.crash_after_step:
            raise RuntimeError("CRASH_BEFORE_JOURNAL_FLUSH")
        self.history.append((cmd_type, payload, result))
        self.cursor += 1
        self.steps_executed += 1
        return result

    def patched(self, patch_id):
        if self.cursor < len(self.history):
            ev_type, ev_payload, _ = self.history[self.cursor]
            if ev_type == "Marker:Patch" and ev_payload == patch_id:
                self.cursor += 1
                return True
            return False
        self.history.append(("Marker:Patch", patch_id, True))
        self.cursor += 1
        return True

def main():
    bank_ledger = []
    def wf_v1(rt, items):
        total = 0
        for item in items:
            total += rt.record_or_replay("Activity:Price", item, lambda i=item: len(i) * 10)
        return rt.record_or_replay("Activity:Charge", total, lambda t=total: (bank_ledger.append(t), t)[1])

    rt1 = ReplayRuntime()
    res1 = wf_v1(rt1, ["apple", "pear"])
    res1_replay = wf_v1(ReplayRuntime(history=rt1.history), ["apple", "pear"])
    print(f"[1A-Clean] initial={res1}, replayed={res1_replay}, ledger_calls={len(bank_ledger)}")

    try:
        wf_v1(ReplayRuntime(history=rt1.history), ["pear", "apple"])
    except NonDeterminismError as e:
        print(f"[1B-HashOrder] caught {type(e).__name__}: {e}")

    def wf_v2_unpatched(rt, items):
        rt.record_or_replay("Activity:Audit", len(items), lambda: "ok")
        return wf_v1(rt, items)

    try:
        wf_v2_unpatched(ReplayRuntime(history=rt1.history), ["apple", "pear"])
    except NonDeterminismError as e:
        print(f"[1C-UnpatchedUpgrade] caught {type(e).__name__}: {e}")

    def wf_v2_patched(rt, items):
        if rt.patched("add-audit-v2"):
            rt.record_or_replay("Activity:Audit", len(items), lambda: "ok")
        return wf_v1(rt, items)

    res_old_hist = wf_v2_patched(ReplayRuntime(history=rt1.history), ["apple", "pear"])
    rt_new = ReplayRuntime()
    res_new_hist = wf_v2_patched(rt_new, ["apple", "pear"])
    print(f"[1D-PatchedUpgrade] old_history_result={res_old_hist}, new_history_len={len(rt_new.history)}, new_result={res_new_hist}")

    naive_bank = {"charged": 0}
    def wf_naive_charge(rt):
        return rt.record_or_replay("Activity:ExternalCharge", 100,
            lambda: (naive_bank.__setitem__("charged", naive_bank["charged"] + 100), "ok")[1])

    rt_c1 = ReplayRuntime(crash_after_step=0)
    try:
        wf_naive_charge(rt_c1)
    except RuntimeError:
        pass
    wf_naive_charge(ReplayRuntime(history=rt_c1.history))
    print(f"[1E-OutputCommit-Naive] total_charged={naive_bank['charged']} (expected 100 -> DUPLICATE SIDE EFFECT)")

    idem_bank = {"charged": 0, "seen": {}}
    def charge_with_key(key, amount):
        if key not in idem_bank["seen"]:
            idem_bank["charged"] += amount
            idem_bank["seen"][key] = "ok"
        return idem_bank["seen"][key]

    def wf_idem_charge(rt, wf_id):
        idem_key = hashlib.sha256(f"{wf_id}:step0:charge".encode()).hexdigest()[:16]
        return rt.record_or_replay("Activity:ExternalCharge", idem_key, lambda: charge_with_key(idem_key, 100))

    rt_i1 = ReplayRuntime(crash_after_step=0)
    try:
        wf_idem_charge(rt_i1, "wf-42")
    except RuntimeError:
        pass
    wf_idem_charge(ReplayRuntime(history=rt_i1.history), "wf-42")
    print(f"[1F-OutputCommit-IdemKey] total_charged={idem_bank['charged']} (exact-once preserved)")

if __name__ == "__main__":
    main()
```

#### Probe 1B: Raw-Snapshot Struct Layout Fragility (`probe_layout_shift.rs`)
Compiled with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`rustc -O /tmp/probe_layout_shift.rs -o /tmp/probe_layout_shift && /tmp/probe_layout_shift`):
```rust
use std::mem::{offset_of, size_of};

struct WorkerStateV1 { active: bool, counter: u64, tag: u16 }
struct WorkerStateV2 { active: bool, counter: u64, tag: u16, epoch: u32 }

#[repr(C)]
struct WorkerStateV1C { active: bool, counter: u64, tag: u16 }
#[repr(C)]
struct WorkerStateV2C { active: bool, counter: u64, tag: u16, epoch: u32 }

fn main() {
    println!("repr(Rust) V1: size={} offsets=(active:{}, counter:{}, tag:{})",
        size_of::<WorkerStateV1>(), offset_of!(WorkerStateV1, active),
        offset_of!(WorkerStateV1, counter), offset_of!(WorkerStateV1, tag));
    println!("repr(Rust) V2: size={} offsets=(active:{}, counter:{}, tag:{}, epoch:{})",
        size_of::<WorkerStateV2>(), offset_of!(WorkerStateV2, active),
        offset_of!(WorkerStateV2, counter), offset_of!(WorkerStateV2, tag),
        offset_of!(WorkerStateV2, epoch));
    println!("repr(C)    V1: size={} offsets=(active:{}, counter:{}, tag:{})",
        size_of::<WorkerStateV1C>(), offset_of!(WorkerStateV1C, active),
        offset_of!(WorkerStateV1C, counter), offset_of!(WorkerStateV1C, tag));
    println!("repr(C)    V2: size={} offsets=(active:{}, counter:{}, tag:{}, epoch:{})",
        size_of::<WorkerStateV2C>(), offset_of!(WorkerStateV2C, active),
        offset_of!(WorkerStateV2C, counter), offset_of!(WorkerStateV2C, tag),
        offset_of!(WorkerStateV2C, epoch));
}
```
Observed output:
```text
repr(Rust) V1: size=16 offsets=(active:10, counter:0, tag:8)
repr(Rust) V2: size=16 offsets=(active:14, counter:0, tag:12, epoch:8)
repr(C)    V1: size=24 offsets=(active:0, counter:8, tag:16)
repr(C)    V2: size=24 offsets=(active:0, counter:8, tag:16, epoch:20)
```

## Revalidation

1. **Temporal replay and history limits:** Diff `crates/sdk-core/src/worker/workflow/machines/patch_state_machine.rs` in `temporalio/sdk-core` against `8e7413bfd77b85ef35326aa4c2cf8473d556c6ea` and `common/dynamicconfig/constants.go` (`HistorySizeLimitError`, `HistoryCountLimitError`) in `temporalio/temporal` against `4841d727dae93c08444a94e47149c0fb0e74d226` to detect changes to patch-marker replay semantics or history caps.
2. **Golem snapshot confirmation & upgrade protocol:** Diff `golem-common/src/base_model/oplog/mod.rs` in `golemcloud/golem` against `7ca9863405ba888f897a581e0dd973b3c95fc5e5` to check whether linear-memory snapshots gained typed schema-migration metadata or altered the `Snapshot` -> `SnapshotConfirmed` two-phase handshake.
3. **Motoko EOP static compatibility checker:** Diff `src/mo_frontend/stability.ml` in `dfinity/motoko` against `acd6537b74b62801b0927ed9dfba240b3a4692a4` to verify whether `M0169`/`M0170`/`M0216`/`M0263` stable-subtyping rules changed.
4. **Wasmtime determinism flags:** Inspect `crates/wasmtime/src/config.rs` (`wasm_relaxed_simd`, `cranelift_nan_canonicalization`) in `bytecodealliance/wasmtime` against `3ce2209872ccf1ea115914a81e020aef66a10c51`.
5. **Re-run execution probes:** Save Probes 1A and 1B under `/tmp/` and run `python3 /tmp/probe_durable_persistence.py` and `rustc -O /tmp/probe_layout_shift.rs -o /tmp/probe_layout_shift && /tmp/probe_layout_shift` to confirm layout-shift behavior on newer `rustc` releases.
