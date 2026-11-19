# Hypervisor VirtIO Shared Rings, Volatile Guest Memory, and Cross-Language Object-Capability IPC ABIs

## Summary

Shared-memory virtualization rings and cross-language object IPC layers sit at the hardest boundary of systems verification: a host or kernel consumer must parse structured descriptors, memory ranges, and object capabilities whose backing storage may be concurrently mutated by an untrusted peer or serialized by an asymmetric language runtime. Five load-bearing invariants govern soundness across these interfaces:

1. **No Rust Reference Aliasing Over Guest-Writable RAM (`&[u8]` / `&mut [u8]` Unsoundness):** Forming an ordinary Rust shared or mutable reference over memory mapped into an adversarial guest violates LLVM `noalias` / `dereferenceable` and Rust's data-race freedom preconditions, because concurrent guest vCPU writes invalidate immutability assumptions. `rust-vmm/vm-memory` (`VolatileSlice` / `VolatileRef`) avoids Rust slice references at its API boundary, yet direct source inspection at `4837300812be77e9071b3cf0abeaa6c8390a6431` shows `copy_slice` uses `read_volatile`/`write_volatile` only for transfers `<= size_of::<usize>()` and falls back to `std::ptr::copy_nonoverlapping` for larger copies—leaving a formal gap relative to Rust/MiniRust's abstract-machine data-race model that currently rests on out-of-band VM/process isolation rather than a formal volatile-atomic semantics.
2. **Linear Copy-In-Once Defenses Against Double-Fetch TOCTOU:** VirtIO split and packed descriptor rings rely on driver-normative immutability while descriptors are live, which an untrusted guest can break. Sound host backends (`rust-vmm/vm-virtio` `DescriptorChain`, Linux `drivers/vhost/vhost.c`) snapshot each descriptor (`addr`, `len`, `flags`, `next`) into host-private storage once, bound chain traversal (`ttl <= queue_size`, cumulative length `<= 2^32`, non-nested indirect tables), and validate solely against the private snapshot.
3. **Relaxed-Memory Hypervisor Microverification (`SeKVM`):** Proving hypervisor confidentiality and integrity on weak-memory multiprocessors without verifying all of Linux KVM splits the hypervisor into a small verified `KCore` and untrusted `KServ` across 34 security-preserving layers, reducing Promising-Arm relaxed-memory behavior to Sequential Consistency via five `wDRF` obligations (`DRF-Kernel`, `No-Barrier-Misuse`, `Weak-Memory-Isolation`, `Transactional-Page-Table`, `Write-Once-Kernel-Mapping`).
4. **Cross-Language Cursor Conservation in Android Binder Parcels:** Android Binder separates raw payload bytes from kernel-validated object offset tables (`flat_binder_object`, `binder_buffer_object`, `binder_fd_array_object`). Desynchronization between Java (`Parcel`/`BaseBundle`), C++ (`libbinder`), and kernel (`binder.c` / Rust `drivers/android/binder/thread.rs`) cursors breaks type and capability framing; Rust Binder's `PointerFixupEntry` enum (`Fixup` vs `Skip`) preserves explicit byte-count conservation across scatter-gather copies, including zero-length skip entries, without overloading zero as a sentinel.
5. **Capability Lattices vs. Equivalence-Law Object ABIs (`Zircon` vs. `COM`):** Fuchsia Zircon enforces kernel-checked monotonic rights attenuation (`rights_out ⊆ rights_in`, requiring `ZX_RIGHT_TRANSFER` and optionally `ZX_RIGHT_DUPLICATE` on `zx_channel_write_etc`) and explicit VMO child semantics (`SNAPSHOT`, `SNAPSHOT_AT_LEAST_ON_WRITE`, `SNAPSHOT_MODIFIED`, `SLICE`, `REFERENCE`), whereas Microsoft COM relies on caller-enforced algebraic `IUnknown::QueryInterface` laws (identity via `IID_IUnknown`, static interface set, reflexivity, symmetry, transitivity) plus apartment marshaling across concurrency domains.

## Applicability

This report synthesizes primary specifications, upstream source revisions, mechanized proof artifacts, and peer-reviewed formalizations covering five interlocking domains:

- **VirtIO Ring Layouts & Host VMM Backends:** Normative split and packed virtqueue layouts from `oasis-tcs/virtio-spec` (`virtio-v1.4-cs01`, commit `bb1dd2e1fe89b862f38f15873d835a698b196f89`, incorporating split-ring semantics from 1.0/1.2 and packed-ring semantics from 1.1+), evaluated alongside host implementations in `rust-vmm/vm-memory` (`4837300812be77e9071b3cf0abeaa6c8390a6431`), `rust-vmm/vm-virtio` (`87bf424736548126983c278b0d49a7b061e38b12`), `rust-vmm/vhost` (`a3a6b988cb4c3b8530278e80b44590c59697793b`), and Linux `drivers/vhost/vhost.c` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`).
- **Volatile & Concurrent Memory Models:** Rust unsafe memory-model constraints compared against `minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`) and formal double-fetch definitions in Xu et al. (IEEE S&P 2018, `DOI: 10.1109/SP.2018.00017`).
- **Formally Verified Hypervisor Memory Isolation:** SeKVM on Arm64 (`VeriGu/SeKVM-4.18` @ `75e3591e663958c370c919aa36fbd484be341043`, `VeriGu/VRM` @ `683c36a169fae261207dba1cbeb91bc73d16af3b`, Li et al. IEEE S&P 2021 `DOI: 10.1109/SP40001.2021.00049`, Tao et al. SOSP 2021 `DOI: 10.1145/3477132.3483560`).
- **Cross-Language Capability & Object IPC ABIs:** Linux UAPI & Rust Binder (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`), Android `Parcel`/`BaseBundle` (`aosp-mirror/platform_frameworks_base` @ `1cdfff555f4a21f71ccc978290e2e212e2f8b168`), Fuchsia Zircon kernel handle/channel/VMO reference documentation (observed `2026-11-19`), and Microsoft COM `IUnknown::QueryInterface` rules paired with `microsoft/windows-rs` (`004e38f54c9508c9d5c0fd510258663f9fee05f5`).

Findings about Rust aliasing and `vm-memory`'s `copy_slice` implementation apply specifically to 64-bit little-endian hosts using the cited crate revisions; behavior on older `vm-memory` releases or alternative atomic-copy forks differs where noted. Findings about SeKVM apply specifically to Armv8-A EL2 Stage-2/SMMU isolation under Promising-Arm semantics and do not automatically transfer to x86-64 EPT/VT-d without re-discharging architecture-specific memory-model obligations.

## Findings

### 1. VirtIO Split vs. Packed Shared Descriptor Rings

`Basis: normative + source + execution`

The OASIS VirtIO specification (`virtio-v1.4-cs01`, `split-ring.tex` and `packed-ring.tex`) defines two shared-memory queue formats between an untrusted guest driver and a host/hardware device. Both place control metadata and data buffers in guest-physical memory writable by guest vCPUs at arbitrary times.

#### 1.1 Split Virtqueue Layout and Framing Rules

In a split virtqueue (`split-ring.tex:104-116`, `185-204`), guest memory is partitioned into three physically aligned regions (`desc` 16-byte aligned, `avail` 2-byte aligned, `used` 4-byte aligned):

```c
struct virtq_desc {
    le64 addr;   /* Guest-physical address of buffer */
    le32 len;    /* Byte length of buffer */
    le16 flags;  /* NEXT=1, WRITE=2, INDIRECT=4 */
    le16 next;   /* Next descriptor index if VIRTQ_DESC_F_NEXT set */
};

struct virtq_avail {
    le16 flags;
    le16 idx;                /* Free-running modulo-65536 producer index */
    le16 ring[/* Queue Size */];
    le16 used_event;         /* Only if VIRTIO_F_EVENT_IDX */
};

struct virtq_used_elem {
    le32 id;                 /* Head descriptor index of completed chain */
    le32 len;                /* Total bytes written by device */
};

struct virtq_used {
    le16 flags;
    le16 idx;                /* Free-running modulo-65536 consumer index */
    struct virtq_used_elem ring[/* Queue Size */];
    le16 avail_event;        /* Only if VIRTIO_F_EVENT_IDX */
};
```

Key normative constraints (`split-ring.tex:145-153`, `217-222`) create an explicit trust asymmetry:

- **Driver-normative requirements (untrusted when the guest is adversarial):** Drivers must place all device-readable descriptors before any device-writable descriptors in a chain, must not create chains exceeding `2^32` total bytes, must not nest `VIRTQ_DESC_F_INDIRECT` descriptors inside an indirect table, and must not modify descriptors or readable buffers while they remain available to the device.
- **Device-normative requirements (safety-critical for the host):** Devices must not assume any particular descriptor framing split across scatter-gather elements, must not write to device-readable buffers or descriptor-table entries, and may bound maximum chain length (`ttl <= queue_size`).

#### 1.2 Packed Virtqueue Single-Ring Wrap-Counter Protocol

Packed virtqueues (`packed-ring.tex:77-125`, `218-265`) collapse `desc`, `avail`, and `used` into a single descriptor ring of `struct pvirtq_desc` entries (`addr: le64`, `len: le32`, `id: le16`, `flags: le16`) to reduce cache-line bouncing across PCIe/NUMA boundaries. Ownership transfer uses two flag bits rather than separate index arrays:

- `VIRTQ_DESC_F_AVAIL = (1 << 7)` (`0x0080`)
- `VIRTQ_DESC_F_USED  = (1 << 15)` (`0x8000`)

Both driver and device maintain a private 1-bit wrap counter initialized to `1`, flipping on each ring wraparound:

| Ring State (for slot at cursor with wrap bit `w`) | `AVAIL` bit | `USED` bit | Bit Relation | Meaning |
| --- | :---: | :---: | --- | --- |
| Initial / unpopulated (before wrap 1) | `0` | `0` | `AVAIL == USED != w` | Free for driver (`w = 1`) |
| Published by driver (available to device) | `w` | `1 - w` | `AVAIL != USED` and `AVAIL == w` | Owned by device |
| Completed by device (used) | `w` | `w` | `AVAIL == USED == w` | Returned to driver |

For multi-descriptor chains in a packed ring, the driver must write the first descriptor's `flags` *last* (with a release store) so the device's acquire read of `flags` observes initialized `addr`, `len`, `id`, and trailing chain entries. Execution of our wrap-counter verifier across `qsz = 8` for `32` transitions (4 full wrap cycles) confirms strict mutual exclusivity between `packed_is_avail(flags, dev_wrap)` and `packed_is_used(flags, drv_wrap)` at every step (`Basis: execution`).

| Dimension | Split Virtqueue | Packed Virtqueue | Host Verification Impact |
| --- | --- | --- | --- |
| Shared rings | 3 (`desc`, `avail`, `used`) | 1 (`desc` ring + event suppression structs) | Packed removes `avail`/`used` indirection but shares cache lines between driver and device |
| Ownership bit | Separate producer/consumer `idx` (`le16`) | Per-descriptor `AVAIL`/`USED` bits + 1-bit wrap counter | Device must pair acquire load on `flags` with private wrap counter |
| Indirect table | `struct virtq_desc[len/16]`, chained via `next` | `struct pvirtq_desc[len/16]`, strictly sequential (`len/16` entries) | Indirect table itself lives in guest RAM and requires bounds + non-nesting checks |
| Ordering hazard | `avail->idx` load must precede `avail->ring[]` & `desc[]` reads (`smp_rmb` / `Acquire`) | First descriptor `flags` load must precede remaining descriptor fields | Missing acquire barrier permits stale or torn descriptor metadata |

---

### 2. Volatile Guest Memory Semantics, Rust Aliasing UB, and `vm-memory` vs. MiniRust

`Basis: source + normative + derived`

#### 2.1 Why Rust `&[u8]` / `&mut [u8]` Over Guest-Writable Memory Is Immediate UB

In Rust's abstract machine (as formalized in `minirust/minirust` `spec/mem/basic.md:1-42` and the Rust aliasing model), memory accesses are governed by per-allocation provenance, aliasing invariants (LLVM `noalias` and `readonly` on shared references without `UnsafeCell`), and C++11/Rust data-race freedom:

1. **Immutability Violation:** A `&[u8]` without `UnsafeCell` asserts to LLVM that no write occurs to the referent bytes for the lifetime of the reference. A guest vCPU writing to mapped guest RAM violates this precondition even if host Rust code performs only reads, enabling LLVM to hoist, sink, duplicate, or merge loads—silently turning a single-read source expression into a **compiler-introduced double-fetch**.
2. **Unsynchronized Data Races:** Under the Rust/C++11 memory model, a non-atomic read concurrent with a write to the same location is Undefined Behavior (not merely a nondeterministic value). Even `core::ptr::read_volatile` is explicitly *not* atomic and does not synchronize with concurrent threads under the language memory model; it solely constrains compiler elision and reordering relative to other volatile operations.
3. **Byte-Validity vs. Typed Projections:** Guest memory may contain arbitrary bit patterns at any instant. Only `ByteValued` / plain-old-data types whose every bit pattern is valid (no `bool`, `char`, enums with invalid discriminants, or non-null references) may be materialized by copying bytes out of guest RAM.

#### 2.2 Primary-Source Audit of `rust-vmm/vm-memory` (`4837300812be77e9071b3cf0abeaa6c8390a6431`)

`rust-vmm/vm-memory` (`src/volatile_memory.rs`) introduces `VolatileSlice<'a, B>` (`L403-L408`), `VolatileRef<'a, T, B>` (`L892`), and traits `VolatileMemory` (`L108`) and `AtomicAccess` (`src/atomic.rs`) specifically to avoid exposing `&[u8]` over guest-backed `mmap` regions:

- `VolatileSlice<'a, B>` stores a raw pointer `addr: *mut u8`, `size: usize`, dirty-tracking `bitmap: B`, and optional Xen `mmap: Option<&'a MmapInfo>`.
- `VolatileMemory::get_atomic_ref<T: AtomicInteger>(&self, offset)` (`L270-L274`) performs bounds and alignment checks and returns `&T` (an atomic integer type inside `UnsafeCell`), which *does* provide genuine C++11/Rust atomic accesses (`Ordering::Acquire`, `Release`, `Relaxed`) for ring indices (`avail.idx`, `used.idx`, packed `flags`).
- `VolatileRef::load(&self)` (`L987`) reads through `read_volatile(guard.as_ptr() as *const Packed<T>).0`, supporting unaligned scalar reads without creating `&T`.

**Critical Source-Level Discrepancy (`src/volatile_memory.rs:1335-1460`):** Direct inspection of `copy_slice_impl` reveals an important implementation trade-off that documentation summaries often obscure:

```rust
// rust-vmm/vm-memory @ 4837300812be77e9071b3cf0abeaa6c8390a6431
// src/volatile_memory.rs:1409-1427
unsafe fn copy_slice(dst: *mut u8, src: *const u8, total: usize) -> usize {
    if total <= size_of::<usize>() {
        unsafe { copy_slice_volatile(dst, src, total); };
    } else {
        unsafe { std::ptr::copy_nonoverlapping(src, dst, total); }
    }
    total
}
```

Both `copy_from_volatile_slice` (`L1433-L1442`) and `copy_to_volatile_slice` (`L1448-L1459`) delegate to `copy_slice`. Consequently:

| Transfer Size | Actual Primitive in `vm-memory` | Compiler Re-Fetch Prevention | Formal Rust/MiniRust Data-Race Freedom |
| --- | --- | --- | --- |
| `<= size_of::<usize>()` (e.g., `<= 8` B) | `copy_slice_volatile` (`read_volatile`/`write_volatile` at 8/4/2/1-byte alignment) | Prevents LLVM load elision/re-fetching across the copy call | **Not formally data-race free** (`volatile != atomic` in Rust/MiniRust) |
| `> size_of::<usize>()` (e.g., `Descriptor` = 16 B, buffers) | `std::ptr::copy_nonoverlapping` (`memcpy`) | Relies on `memcpy` copying once into private destination; destination buffer is unaliased thereafter | **Not formally data-race free** (non-atomic read racing with guest vCPU write) |
| Ring indices / flags (`get_atomic_ref`) | `AtomicU16`/`AtomicU32`/`AtomicU64` (`Ordering::Acquire`/`Release`) | Full compiler & hardware ordering control | **Formally race-free** if peer also synchronizes via hardware-compatible atomics |

`Derived:` For formal verification frameworks grounded in MiniRust or Rust's abstract machine, treating guest RAM as ordinary Rust memory makes any non-atomic guest copy immediately UB. Sound formalization therefore requires modeling guest-shared memory either as an **external/FFI memory domain** accessed only via opaque volatile/relaxed-atomic intrinsics returning arbitrary `ByteValued` bitvectors (or `MaybeUninit`/frozen bytes without provenance), or via architecture-specific relaxed-atomic byte-copy primitives (`atomic_memcpy` / unordered-atomic semantics).

---

### 3. Linear Copy-In-Once Defenses Against Hypervisor Double-Fetch TOCTOU

`Basis: normative + source + execution`

#### 3.1 Formal Double-Fetch Characterization

In Xu et al. (*DEADLINE*, IEEE S&P 2018, `DOI: 10.1109/SP.2018.00017`), a double-fetch bug arises when a privileged consumer performs two distinct reads $r_1, r_2$ from the same unprivileged shared address $a$ along a feasible execution path, such that a security check $P(v_1)$ constrains the value $v_1$ returned by $r_1$, while a subsequent privileged operation consumes $v_2$ returned by $r_2$ without re-enforcing $P(v_2)$. Because a concurrent guest vCPU (or user thread) can overwrite memory at $a$ between $r_1$ and $r_2$, $P(v_1) \land \neg P(v_2)$ is reachable, invalidating bounds, type-tag, or capability invariants.

Two structural root causes dominate hypervisor ring and paravirtualized device backends (Xen PV rings, KVM `vhost`, userspace VMMs):

1. **Direct Pointer Dereference Across Validation and Use:** Indexing guest memory by raw pointer to check `desc->len` or a command tag, then passing `desc` by pointer to a downstream handler that re-reads `desc->len` or `desc->addr`.
2. **Compiler-Synthesized Double Fetches:** Reading through a non-volatile pointer where register pressure causes the compiler to reload a field from guest RAM after a bounds check.

#### 3.2 Linear `CopyInOnce` Pattern in `vm-virtio` and Linux `vhost`

The canonical structural defense is **linear copy-in-once** (materializing an immutable, host-private value from untrusted guest memory exactly once and forbidding any subsequent read of the guest slot for that request):

$$\text{guest\_read\_once} : \text{GuestAddr} \longrightarrow \text{HostOwned}\langle T \rangle \qquad (\text{where } T : \text{ByteValued})$$

All validation predicates $P(x)$ and all downstream consumer operations operate exclusively on the private `HostOwned<T>` snapshot. Direct inspection confirms this discipline in both production stacks:

- **`rust-vmm/vm-virtio` (`virtio-queue/src/chain.rs:119-203`):** `DescriptorChain::next` computes `desc_addr = table_addr + next_index * 16`, calls `self.mem.read_obj::<Descriptor>(desc_addr)` (`L176`) to copy the 16-byte `#[repr(C)] Descriptor` into a stack-owned Rust value once, and performs every subsequent check on that local value:
  - Rejects nested indirect tables (`if self.is_indirect { return Err(Error::InvalidIndirectDescriptor); }`, `L123-L125`);
  - Rejects misaligned indirect table lengths (`desc.len() & (VRING_DESC_ALIGN_SIZE - 1) != 0`, `L129-L131`);
  - Enforces the VirtIO `2^32`-byte chain limit via `self.yielded_bytes.checked_add(desc.len())` (`L187-L190`);
  - Prevents infinite descriptor cycles via a strictly decreasing `self.ttl` counter initialized to `queue_size` (or indirect table entry count) (`L192-L199`).
- **Linux `drivers/vhost/vhost.c` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):**
  - `vhost_get_avail_idx` pairs user-space reads (`vhost_get_avail`) with `smp_rmb()` (`L1598`) before reading `avail->ring[]` or descriptors, enforcing acquire ordering on weak-memory CPUs.
  - `get_indirect` (`L2821-L2891`) validates `len % sizeof(desc) == 0` (`L2834`), bounds entry count to `<= USHRT_MAX + 1` (`L2853`), enforces loop termination (`++found > count`, `L2861`), copies each indirect descriptor into stack-local `struct vring_desc desc` via `copy_from_iter_full(&desc, sizeof(desc), &from)` (`L2867`), rejects nested `VRING_DESC_F_INDIRECT` (`L2872`), and translates guest physical spans into host `struct iovec` arrays before returning.
- **Userspace `vhost-user` Protocol (`rust-vmm/vhost` @ `a3a6b988cb4c3b8530278e80b44590c59697793b`):** When a VMM offloads VirtIO device backends to an unprivileged userspace process over a Unix domain socket, `BackendReqHandler` (`vhost/src/vhost_user/backend_req_handler.rs:50-107`, `376`, `464`) receives guest memory file descriptors (`VhostUserMemoryRegion`, `vhost/src/vhost_user/message.rs:521`), ring virtual addresses (`VhostUserVringAddr`, `L771`), and shared dirty-page logs (`VhostUserProtocolFeatures::{LOG_SHMFD, REPLY_ACK, CONFIGURE_MEM_SLOTS}`, `L402-L434`). Because both the guest vCPUs and the external `vhost-user` backend concurrently map the same backing `memfd` regions, the backend must enforce the exact same volatile/copy-in-once descriptor snapshotting and `LOG_SHMFD` dirty-bit updates as an in-process VMM.

Our `test_copy_in_once_vs_double_fetch` probe (`Basis: execution`) confirms that snapshotting into an immutable host-private `DescSnapshot` preserves `addr + len <= RAM_LIMIT` under concurrent guest mutation of `len`, whereas re-fetching the shared slot violates the validated bound.

---

### 4. SeKVM: Microverification and Relaxed-Memory Reduction (`wDRF`)

`Basis: source + documentation`

Rather than attempting to verify the entire multi-million-line Linux kernel and KVM subsystem, **SeKVM** (Li et al., IEEE S&P 2021, `DOI: 10.1109/SP40001.2021.00049`; Tao et al., SOSP 2021, `DOI: 10.1145/3477132.3483560`; repos `VeriGu/SeKVM-4.18` @ `75e3591e663958c370c919aa36fbd484be341043` and `VeriGu/VRM` @ `683c36a169fae261207dba1cbeb91bc73d16af3b`) retrofits Linux KVM via **microverification**:

1. **Privilege Split (`KCore` vs. `KServ`):** Security-critical isolation mechanisms—Stage-2 nested page tables (`NPTOps`), SMMU DMA page tables (`MmioSPTOps`), physical page ownership tracking (`PageManager` / `MemRegion`), and VM/vCPU context protection—are isolated in a small verified core (`KCore`) running at Arm EL2. Complex host scheduling, device emulation, and VirtIO/QEMU management remain in an untrusted host service (`KServ`) running at EL1/EL0.
2. **34 Security-Preserving Refinement Layers:** `VeriGu/VRM` (`README.md:45-130`) organizes the Coq proof into 34 certified abstraction layers linking bottom-layer machine semantics to top-layer VM confidentiality and integrity (non-interference) invariants, ensuring that a compromised `KServ` cannot map VM-owned physical pages into host or DMA address spaces (`SMMU`), nor inspect/corrupt protected VM register state except through explicitly shared I/O / MMIO regions.
3. **Promising-Arm to Sequential-Consistency (`wDRF`) Reduction:** Modern Armv8-A multiprocessors exhibit relaxed memory reordering (load/store reordering, speculative reads, and hardware page-table walker visibility). `VeriGu/VRM` (`README.md:47-89`) proves two general reduction theorems (Theorem 2 for isolated kernel execution; Theorem 4 with adversarial user/guest data oracles) showing that if the hypervisor satisfies five **weak Data-Race-Freedom (`wDRF`)** conditions, every observable execution under **Promising-Arm** is also an observable execution under **Sequential Consistency (SC)**:

| `wDRF` Condition (`VeriGu/VRM`) | Security & Concurrency Role |
| --- | --- |
| `DRF-Kernel` | All concurrent `KCore` accesses to shared kernel metadata are synchronized by locks or atomics. |
| `No-Barrier-Misuse` | Hardware memory barriers (`DMB`/`DSB`/`ISB`) and TLB invalidations (`TLBI`) follow disciplined acquire/release and break-before-make patterns. |
| `Weak-Memory-Isolation` | Untrusted guest/host memory accesses cannot race with `KCore`-owned physical pages because Stage-2 / SMMU ownership invariants partition page sets. |
| `Transactional-Page-Table` | Multi-step Stage-2 / SMMU page-table updates appear atomic to hardware walkers via lock-protected break-before-make transitions. |
| `Write-Once-Kernel-Mapping` | `KCore`'s own code and static page-table mappings remain immutable after boot initialization. |

`Derived:` SeKVM's `Weak-Memory-Isolation` condition reveals why VirtIO shared-memory rings must be *explicitly* carved out as untrusted shared I/O pages outside the confidential VM memory domain: any page shared with an untrusted device backend inherits the volatile/TOCTOU threat model of Sections 1–3, while all non-shared guest RAM retains non-interference.

---

### 5. Android Binder: Cross-Language `Parcel` Cursor Desynchronization and Kernel Patch-List Invariants

`Basis: source + normative + derived + execution`

Android Binder implements capability-passing IPC across three distinct layers and languages: Java (`android.os.Parcel`, `android.os.BaseBundle`), C++ (`libbinder` `android::Parcel`), and the Linux kernel driver (`drivers/android/binder.c` and upstream Rust `drivers/android/binder/`).

#### 5.1 Dual-Stream Architecture: Raw Byte Payload vs. Kernel Object Offset Table

In Linux UAPI (`include/uapi/linux/android/binder.h:27-170`, `342-345`), a Binder transaction carries two distinct arrays inside `struct binder_transaction_data` / `binder_transaction_data_sg`:

- A raw byte stream (`data.ptr.buffer`, length `data_size`) written sequentially via a cursor (`mDataPos`), and
- An offset array (`data.ptr.offsets`, length `offsets_size`) listing byte offsets inside the raw buffer where kernel-translated objects reside:
  - `BINDER_TYPE_BINDER` / `BINDER_TYPE_HANDLE` / `BINDER_TYPE_WEAK_*` / `BINDER_TYPE_FD` (`struct flat_binder_object`),
  - `BINDER_TYPE_PTR` (`struct binder_buffer_object` for scatter-gather nested buffers), and
  - `BINDER_TYPE_FDA` (`struct binder_fd_array_object` embedding translated file descriptors inside a parent `binder_buffer_object`).

Only objects listed in the kernel-validated offsets array are translated into genuine capability handles (`IBinder`) or kernel file descriptors in the receiver's address space.

#### 5.2 Structural Root Causes of Cross-Language Cursor Desynchronization ("Polyglot Parcels")

Because `Parcel` is an untyped, self-describing-by-convention byte stream rather than a self-delimiting wire format, serialization soundness depends on exact cursor agreement (`bytes_written == bytes_read`) across every `Parcelable` implementation and across language bindings:

1. **Asymmetric Write/Read Cursor Advance (Parcel/Unparcel Mismatch):** If a `Parcelable`'s `writeToParcel` emits $k_1$ bytes (or interprets a length/count field under one convention) while `createFromParcel` consumes $k_2 \neq k_1$ bytes—or if a Java `Parcel` wrapper (`aosp-mirror/platform_frameworks_base` `Parcel.java`, backed by native pointer `mNativePtr` at `L245`) and a C++/Rust peer disagree on UTF-16 vs. UTF-8 string padding, boolean/int width, or optional field presence—the reader's cursor lands mid-structure on subsequent fields.
2. **Lazy Re-Parceling Amplification in `BaseBundle`:** Direct inspection of `BaseBundle.java` (`L101-L122`, `L446-L494`) confirms that `BaseBundle` stores an unparsed `volatile Parcel mParcelledData` (`L113`) while `mMap == null`, deferring full parsing until `unparcel()` (`L312`) invokes `initializeFromParcelLocked` (`L446`) and `parcelledData.readArrayMap(...)` (`L480`). When a privileged service receives a `Bundle`, checks one key (or forwards it untouched), and re-serializes or unparcels it in another process, a cursor mismatch inside a nested `Parcelable` shifts the remaining byte stream so that key-value boundaries re-align differently on the second pass—allowing untrusted data to be re-interpreted as privileged metadata or shifting cursor alignment onto a kernel-validated `IBinder` offset (`readStrongBinder()`, `Parcel.java:3370`).
3. **Kernel Scatter-Gather Patch-List Cursor Bugs (`drivers/android/binder/thread.rs`):** In upstream Linux Rust Binder (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `drivers/android/binder/thread.rs:47-100`, `900-1023`), scatter-gather transactions build a `ScatterGatherState` containing `ScatterGatherEntry` records, each carrying a sorted list of `PointerFixupEntry` operations:

```rust
// torvalds/linux @ 4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd
// drivers/android/binder/thread.rs:75-91
enum PointerFixupEntry {
    Fixup { pointer_value: u64, target_offset: usize },
    Skip { skip: usize, target_offset: usize },
}
```

When copying a scatter-gather buffer (`L975-L1021`), the kernel iterates over each `PointerFixupEntry`, copies `[end_of_previous_fixup, target_offset)` from the sender's `UserSliceReader`, applies the pointer fixup or skips `skip` bytes already populated by `BINDER_TYPE_FDA` translation (`reader.skip(fixup_len)`, `L1006`), and updates `end_of_previous_fixup = target_offset_end`. Crucially, using an explicit sum type (`Fixup` vs. `Skip`) avoids conflating a legitimate zero-length FD array (`skip == 0`) with a sentinel value that signals a non-skip entry—a subtle cursor-state bug class that causes reader/destination offset divergence even in memory-safe Rust if a single integer field is overloaded as both length and discriminant. Our `test_binder_sg_cursor` probe (`Basis: execution`) confirms exact byte-count conservation (`copied + fixed_or_skipped == total_len`) across mixed `Fixup`, zero-length `Skip(0)`, and non-zero `Skip(8)` sequences.

**Hardening Mitigations Across Binder Layers:**
- **Length-prefixed sub-parcels and `enforceNoDataAvail()`:** Modern AIDL codegen emits trailing-data checks (`Parcel.enforceNoDataAvail`) so any cursor drift fails closed rather than silently shifting subsequent fields.
- **Strict offset-table alignment checks in `libbinder`:** `readStrongBinder()` requires `mDataPos` to match an exact entry in the kernel-verified `mObjects` offset table; raw payload bytes cannot forge a kernel handle, though cursor drift can redirect a read onto an *existing* legitimate handle earlier or later in the parcel.
- **Explicit algebraic sum types in kernel fixup loops:** Representing `Fixup` and `Skip` as disjoint enum variants prevents zero-length sentinel aliasing.

---

### 6. Fuchsia Zircon Capabilities vs. Microsoft COM Equivalence-Law ABIs

`Basis: documentation + source + execution`

Object-capability IPC systems diverge sharply in *where* object identity, rights, and concurrency boundaries are enforced: kernel-enforced capability tables (Zircon) vs. user-space binary vtable contracts and apartment marshaling (COM/WinRT).

#### 6.1 Fuchsia Zircon: Kernel Handle Rights Attenuation and VMO Clone Semantics

In Fuchsia Zircon (`fuchsia.dev` kernel reference, observed `2026-11-19`), user processes hold 32-bit opaque `zx_handle_t` indices (with `ZX_HANDLE_INVALID == 0` and two fixed low bits masked by `ZX_HANDLE_FIXED_BITS_MASK`) pointing to kernel handle entries storing `(object_ref, rights_bitmask, owner_process | in_transit)`.

1. **Monotonic Rights Attenuation (`zx_handle_duplicate`, `zx_handle_replace`, `zx_channel_write_etc`):**
   - No syscall can add a right bit absent from the source handle. `zx_channel_write_etc()` accepts per-handle dispositions specifying `ZX_HANDLE_OP_MOVE` or `ZX_HANDLE_OP_DUPLICATE`, an expected `type`, and requested `rights` (or `ZX_RIGHT_SAME_RIGHTS`).
   - Enforced preconditions: the channel handle must carry `ZX_RIGHT_WRITE`; every transferred handle must carry `ZX_RIGHT_TRANSFER`; `ZX_HANDLE_OP_DUPLICATE` additionally requires `ZX_RIGHT_DUPLICATE`; and `req_rights ⊆ src_rights` (otherwise `ZX_ERR_INVALID_ARGS` or `ZX_ERR_ACCESS_DENIED`).
   - Stripping `ZX_RIGHT_TRANSFER` in flight delivers a **non-re-transferable** capability to the receiver—the receiver can invoke operations allowed by its remaining rights and close the handle, but cannot forward it over any channel. Exhaustive verification over all `2048` 5-bit `(src_rights, req_rights, op)` transitions in our `test_zircon_rights_lattice` probe (`Basis: execution`) confirms `0` rights amplifications.
2. **VMO Child & Userpager Isolation Semantics (`zx_vmo_create_child`):**
   Shared-memory IPC over Zircon channels passes VMO handles rather than raw physical addresses, but VMO mutability and TOCTOU exposure depend strictly on child creation flags:

| `zx_vmo_create_child` Mode | Parent-Write Visibility to Child | Permitted on Pager-Backed VMO? | Permitted on Pinned/Physical/Contiguous VMO? | Immutability / TOCTOU Property |
| --- | --- | :---: | :---: | --- |
| `ZX_VMO_CHILD_SNAPSHOT` | Isolated (eager-copy semantics via lazy CoW on both parent & child writes) | No | No | With `ZX_VMO_CHILD_NO_WRITE` and without `ZX_VMO_CHILD_RESIZABLE`, yields a **truly immutable snapshot** immune to peer TOCTOU |
| `ZX_VMO_CHILD_SNAPSHOT_AT_LEAST_ON_WRITE` | Unwritten pages **may** observe concurrent parent writes; child writes diverge | Yes | No | **Not TOCTOU-safe** against a writable parent until pages are copied or parent write rights are absent |
| `ZX_VMO_CHILD_SNAPSHOT_MODIFIED` | Isolated for already-modified non-pager pages; at-least-CoW for pager-backed pages | Yes (restricted) | No | Preserves snapshot isolation only for non-pager-modified pages |
| `ZX_VMO_CHILD_SLICE` | Direct bidirectional aliasing into parent subrange | Yes | Yes (non-resizable parent only) | Shared mutable view; requires volatile/copy-in-once discipline |
| `ZX_VMO_CHILD_REFERENCE` | Full-span alias (`offset = size = 0`) for `ZX_VMO_ZERO_CHILDREN` tracking | Yes | No | Shared alias; tracks lifecycle without copying |

#### 6.2 Microsoft COM / WinRT `IUnknown::QueryInterface` Laws and `windows-rs` Soundness

Unlike Zircon's kernel-enforced handle tables, Microsoft COM defines a user-space binary ABI where every interface pointer points to a pointer to a vtable whose first three entries are `IUnknown::{QueryInterface, AddRef, Release}`. Normative Microsoft COM rules (`Rules for Implementing QueryInterface`, updated `2020-08-21`) require five algebraic invariants across all interfaces on an object instance:

1. **Object Identity:** `QueryInterface(IID_IUnknown)` called from *any* interface pointer on an object instance must return the exact same physical pointer value.
2. **Static Interface Set:** If `QueryInterface(IID_X)` returns `S_OK` once on an object, it must never later return `E_NOINTERFACE` (and vice versa).
3. **Reflexivity:** Given `IA* pA`, `pA->QueryInterface(IID_IA)` must succeed.
4. **Symmetry:** If `pA->QueryInterface(IID_IB, &pB)` succeeds, `pB->QueryInterface(IID_IA)` must succeed.
5. **Transitivity:** If `pA -> pB` and `pB -> pC` succeed, `pA -> pC` must succeed.

Violation of these laws—most commonly in faulty **COM aggregation** where an inner object returns its own `IUnknown` instead of delegating to the outer controlling `IUnknown`—breaks identity comparison, causes asymmetric/intransitive casts (demonstrated in `test_com_qi`, `Basis: execution`), and corrupts reference-count ownership.

Direct inspection of `microsoft/windows-rs` (`004e38f54c9508c9d5c0fd510258663f9fee05f5`, `crates/libs/core/src/interface.rs:45-140`) highlights how Rust FFI bindings harden against real-world non-compliant COM implementations:
- **Packed-Object Vtable Alignment (`L47`):** `assume_vtable` uses `self.as_raw().cast::<*const T::Vtable>().read_unaligned()` because COM structs may be packed even when vtables themselves are aligned.
- **Failed-Query Out-Param Hygiene (`L116-L140`):** `Interface::cast<T>` initializes `let mut result = MaybeUninit::<Option<T>>::zeroed();` before invoking `self.query(&T::IID, ...)`. If `hr` fails, `result` is abandoned without running `Drop` (guarding against buggy COM servers that write a non-null garbage pointer while returning `E_NOINTERFACE`); if `hr` succeeds, `cast` still checks `if let Some(obj) = result.assume_init()` and returns `E_POINTER` on a null pointer despite `S_OK`.
- **Apartment Concurrency Boundary:** Passing a raw COM interface pointer directly across Single-Threaded Apartment (`STA`) / Multi-Threaded Apartment (`MTA`) boundaries bypasses proxy/stub marshaling (`CoMarshalInterThreadInterfaceInStream` / `IGlobalInterfaceTable`) and causes unsynchronized data races on non-thread-safe STA implementations—analogous to sharing an unsynchronized Rust `!Sync` pointer across threads.

---

### 7. Cross-System Trade-Off Matrix for Verification & FFI Boundaries

`Basis: derived`

| Mechanism / System | Trust Boundary Enforcer | Aliasing / Concurrency Hazard | Primary Invariant / Defense | Residual Verification Gap |
| --- | --- | --- | --- | --- |
| VirtIO Split / Packed Rings (`vm-memory`, `vm-virtio`, `vhost`) | Host VMM / kernel backend (untrusted guest RAM) | Concurrent guest writes; Rust `&[u8]` UB; double-fetch TOCTOU | Linear `CopyInOnce` snapshots; atomic ring indices (`Acquire`/`Release`); `ttl` & `2^32` bounds | `vm-memory` `copy_slice` uses `copy_nonoverlapping` (`>8` B) & `read_volatile` (`<=8` B), outside formal Rust/MiniRust race freedom |
| SeKVM (`KCore` / `KServ`) | Arm EL2 Stage-2 + SMMU hardware + Coq proofs | Relaxed Armv8-A memory & page-table walker reordering | 34-layer refinement + 5 `wDRF` conditions reducing Promising-Arm to SC | Shared VirtIO/MMIO I/O pages sit outside confidential VM isolation and still need copy-in-once parsing |
| Android Binder (`Parcel` / `BaseBundle` / `rust_binder`) | Kernel object offset table + userspace `Parcelable` conventions | Cross-language cursor drift (Java/C++/Rust); lazy re-parceling; zero-length sentinel aliasing | `enforceNoDataAvail()`; kernel `mObjects` verification; explicit `PointerFixupEntry` enum (`Fixup`/`Skip`) | Untyped byte stream still depends on semantic parity across third-party `Parcelable` codecs |
| Fuchsia Zircon (`zx_channel`, `zx_vmo`) | Microkernel handle table & VM subsystem | Writable VMO aliases (`SLICE`, `AT_LEAST_ON_WRITE`) | Monotonic capability rights lattice; `SNAPSHOT + NO_WRITE` immutable VMOs; in-transit handle ownership | Pager-backed VMOs forbid strict `SNAPSHOT` mode, requiring explicit defensive copy-in-once or pager trust |
| Microsoft COM / WinRT (`windows-rs`) | In-process vtable ABI + RPC apartment proxies | Broken aggregation (`QI` laws); cross-apartment raw pointer sharing; buggy `HRESULT`/out-param pairs | 5 `QueryInterface` equivalence/identity axioms; `MaybeUninit` + null-check in `Interface::cast`; STA/MTA marshaling | Laws are dynamically assumed conventions rather than kernel-enforced capabilities |

## Boundaries

- **Linux C `binder.c` vs. Rust `rust_binder` Full Diff (`not examined`):** This report inspected `include/uapi/linux/android/binder.h` and `drivers/android/binder/thread.rs` at `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`PointerFixupEntry` scatter-gather handling), and did not perform a line-by-line equivalence audit of the legacy C driver `drivers/android/binder.c` or Android userspace C++ `libbinder` (`frameworks/native/libs/binder/Parcel.cpp`, whose GitHub mirror path was unavailable without authentication).
- **Xen PV Grant-Table & `xen-blkback`/`xen-netback` Source Audit (`not examined`):** Xen double-fetch patterns are characterized through the general `DEADLINE` formalization and VirtIO shared-ring model; Xen-specific grant-table hypercall implementations in `drivers/block/xen-blkback/` were not directly inspected at source level.
- **Rust Language Formalization of Untrusted Shared-Memory Copies (`unknown`):** Neither `minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`) nor stable Rust currently defines a finalized, high-performance `atomic_memcpy` or hardware-volatile concurrency primitive that formally blesses `rust-vmm/vm-memory`'s `copy_nonoverlapping` fallback under concurrent guest-vCPU writes. Whether LLVM codegen can ever miscompile `copy_nonoverlapping` into a double-fetch on a specific target microarchitecture remains an open compiler-backend hazard rather than a proved guarantee.
- **SeKVM Generalization to x86-64 or Non-KVM Hypervisors (`known not to apply`):** SeKVM's 34-layer Coq proofs and `wDRF` theorems (`VeriGu/VRM` @ `683c36a169fae261207dba1cbeb91bc73d16af3b`) target Armv8-A Promising-Arm, EL2 Stage-2, and Arm SMMU semantics; they do not automatically establish soundness for x86-64 EPT/IOMMU or nested virtualization.
- **Zircon `ZX_VMO_CHILD_SNAPSHOT` on Userpager-Backed or Pinned VMOs (`unsupported`):** As documented in the `zx_vmo_create_child` kernel reference, strict eager-semantics `ZX_VMO_CHILD_SNAPSHOT` is explicitly unsupported on VMOs backed by user pagers, pinned regions, or `zx_vmo_create_physical`/`zx_vmo_create_contiguous` allocations.
- **Non-Generalization of COM `windows-rs` Runtime Defenses (`known not to apply`):** While `windows-rs` `Interface::cast` defends against null success pointers and dirty out-parameters on `E_NOINTERFACE`, it cannot statically enforce `QueryInterface` symmetry/transitivity or apartment-threading compliance on foreign COM servers.

## Evidence

### Primary Specifications & Upstream Source Revisions (Observed `2026-11-19`)

- **OASIS VirtIO (`oasis-tcs/virtio-spec` @ `bb1dd2e1fe89b862f38f15873d835a698b196f89`):**
  - `REVISION:1` (`virtio-v1.4-cs01`).
  - `split-ring.tex:91-116`, `145-153`, `185-222` (`struct virtq`, `struct virtq_desc`, `VIRTQ_DESC_F_{NEXT,WRITE,INDIRECT}`, driver/device normative rules).
  - `packed-ring.tex:77-125`, `218-265` (1-bit wrap counters, `VIRTQ_DESC_F_AVAIL = (1 << 7)`, `VIRTQ_DESC_F_USED = (1 << 15)`, `struct pvirtq_indirect_descriptor_table`).
- **`rust-vmm/vm-memory` (`4837300812be77e9071b3cf0abeaa6c8390a6431`):**
  - `src/volatile_memory.rs:108-115` (`VolatileMemory`), `270-274` (`get_atomic_ref`), `403-422` (`VolatileSlice`), `892-990` (`VolatileRef::load`), `1335-1460` (`copy_slice_impl`: `copy_single`, `copy_slice_volatile`, `copy_slice` threshold `total <= size_of::<usize>()` falling back to `std::ptr::copy_nonoverlapping`).
- **`rust-vmm/vm-virtio` (`87bf424736548126983c278b0d49a7b061e38b12`):**
  - `virtio-queue/src/desc/split.rs:61-75` (`#[repr(C)] pub struct Descriptor`).
  - `virtio-queue/src/chain.rs:119-203` (`switch_to_indirect_table`, `self.mem.read_obj::<Descriptor>`, `yielded_bytes.checked_add`, `self.ttl` cycle bound).
- **`rust-vmm/vhost` (`a3a6b988cb4c3b8530278e80b44590c59697793b`):**
  - `vhost/src/vhost_user/message.rs:402-434` (`VhostUserProtocolFeatures::{LOG_SHMFD, REPLY_ACK, CONFIGURE_MEM_SLOTS}`), `521` (`VhostUserMemoryRegion`), `771` (`VhostUserVringAddr`).
  - `vhost/src/vhost_user/backend_req_handler.rs:50-107`, `376`, `464` (`BackendReqHandler::{set_mem_table, set_vring_addr, set_log_base, handle_request}`).
- **Linux Kernel (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):**
  - `drivers/vhost/vhost.c:1401-1482` (`vhost_copy_from_user`, `__vhost_get_user`), `1594-1600` (`smp_rmb()`), `2821-2891` (`get_indirect` copy-in-once + cycle/nesting checks), `3078-3103` (`vhost_get_vq_desc`).
  - `include/uapi/linux/android/binder.h:27-38` (`BINDER_TYPE_*`), `163-169` (`struct binder_fd_array_object`), `342-345` (`struct binder_transaction_data_sg`).
  - `drivers/android/binder/thread.rs:47-91` (`ScatterGatherState`, `ScatterGatherEntry`, `PointerFixupEntry::{Fixup, Skip}`), `908-1023` (patch-list copy and `reader.skip(fixup_len)`).
- **MiniRust (`minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`):**
  - `spec/mem/basic.md:1-74` (`AllocId`, `Provenance`, `Allocation`, `BasicMemory`).
- **SeKVM (`VeriGu/SeKVM-4.18` @ `75e3591e663958c370c919aa36fbd484be341043`; `VeriGu/VRM` @ `683c36a169fae261207dba1cbeb91bc73d16af3b`):**
  - `VeriGu/VRM` `README.md:45-130` (Theorems 2 & 4, 5 `wDRF` conditions, 34 security-preserving layers including `NPTOps` and `MmioSPTOps`).
  - Li, Li, Gu, Nieh, Hui, *"A Secure and Formally Verified Linux KVM Hypervisor"*, IEEE S&P 2021, `DOI: 10.1109/SP40001.2021.00049`.
  - Tao, Yao, Li, Li, Nieh, Gu, *"Formal Verification of a Multiprocessor Hypervisor on Arm Relaxed Memory Hardware"*, ACM SOSP 2021, `DOI: 10.1145/3477132.3483560`.
- **Double-Fetch Formalization:**
  - Xu, Qian, Lu, Backes, Kim, *"Precise and Scalable Detection of Double-Fetch Bugs in OS Kernels"* (`DEADLINE`), IEEE S&P 2018, `DOI: 10.1109/SP.2018.00017`.
- **Android Frameworks Base (`aosp-mirror/platform_frameworks_base` @ `1cdfff555f4a21f71ccc978290e2e212e2f8b168`):**
  - `core/java/android/os/Parcel.java:245` (`mNativePtr`), `775-776` (`setDataPosition`), `3370-3380` (`readStrongBinder`).
  - `core/java/android/os/BaseBundle.java:101-122` (`mParcelledData` invariant), `312-323` (`unparcel`), `446-494` (`initializeFromParcelLocked`, `readArrayMap`).
- **Fuchsia Zircon Kernel Documentation (Observed `2026-11-19`):**
  - `https://fuchsia.dev/fuchsia-src/concepts/kernel/handles` (`ZX_HANDLE_INVALID`, `ZX_HANDLE_FIXED_BITS_MASK`, in-transit handles).
  - `https://fuchsia.dev/fuchsia-src/reference/syscalls/channel_write_etc` (`ZX_HANDLE_OP_MOVE`, `ZX_HANDLE_OP_DUPLICATE`, `ZX_RIGHT_TRANSFER`, `ZX_RIGHT_DUPLICATE`, `ZX_ERR_INVALID_ARGS`, `ZX_ERR_ACCESS_DENIED`).
  - `https://fuchsia.dev/fuchsia-src/reference/syscalls/vmo_create_child` (`ZX_VMO_CHILD_SNAPSHOT`, `SNAPSHOT_AT_LEAST_ON_WRITE`, `SNAPSHOT_MODIFIED`, `SLICE`, `REFERENCE`, `NO_WRITE`, `RESIZABLE`).
- **Microsoft COM & `windows-rs` (`004e38f54c9508c9d5c0fd510258663f9fee05f5`):**
  - `https://learn.microsoft.com/en-us/windows/win32/com/rules-for-implementing-queryinterface` (identity, static interface set, reflexivity, symmetry, transitivity).
  - `crates/libs/core/src/interface.rs:45-48` (`assume_vtable` unaligned vtable pointer load), `111-140` (`Interface::cast` `MaybeUninit` + null-pointer guard).

### Execution Probe Record (Observed `2026-11-19`)

A standalone Python 3 defensive invariant probe (`probe_virtio_ipc_invariants.py`, using only the Python standard library) verified five state machines directly:

```json
{
  "packed_ring": {"qsz": 8, "steps": 32, "final_wrap": [1, 1], "ok": true},
  "copy_in_once": {"snapshot_preserves_bound": true, "refetch_violates_bound": true},
  "zircon_rights": {
    "checked_transitions": 2048,
    "amplifications": 0,
    "strip_transfer_recv_ok": true,
    "non_transferable_resend_blocked": true
  },
  "com_qi": {
    "compliant_violations": [],
    "broken_aggregation_violations": [
      "identity_violation",
      "symmetry:IA<->IB",
      "symmetry:IB<->IA",
      "transitivity:IB->IUnknown->IA"
    ]
  },
  "binder_sg_cursor": {"total_len": 64, "copied": 48, "fixed_or_skipped": 16, "conserved": true}
}
```

## Revalidation

1. **Check `vm-memory` volatile copy threshold:** Diff `src/volatile_memory.rs` (`mod copy_slice_impl`) in newer `rust-vmm/vm-memory` commits against `4837300812be77e9071b3cf0abeaa6c8390a6431` to check whether `copy_slice` replaces `std::ptr::copy_nonoverlapping` with an atomic byte-copy loop or Rust's future `atomic_memcpy` intrinsic.
2. **Check `vm-virtio` & Linux `vhost` descriptor snapshotting:** Inspect `DescriptorChain::next` (`virtio-queue/src/chain.rs`) and `get_indirect` (`drivers/vhost/vhost.c`) to verify that `read_obj`/`copy_from_iter_full` still materializes every descriptor into host-private storage before indirect-nesting, `ttl`, and `2^32`-byte checks.
3. **Check Linux `rust_binder` fixup cursor logic:** Diff `enum PointerFixupEntry` and the scatter-gather copy loop in `drivers/android/binder/thread.rs` against `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to ensure zero-length FD arrays remain distinct from fixup entries and preserve byte-count conservation.
4. **Check `windows-rs` COM `cast` hardening:** Diff `Interface::cast` and `assume_vtable` in `crates/libs/core/src/interface.rs` against `004e38f54c9508c9d5c0fd510258663f9fee05f5`.
5. **Rerun invariant models:** Re-execute the five state-machine assertions (packed wrap-counter transitions, copy-in-once snapshot preservation, 2048-case Zircon rights-lattice monotonicity, COM `QI` axiom checker, and Binder scatter-gather cursor conservation) whenever protocol flags or capability rules change.
