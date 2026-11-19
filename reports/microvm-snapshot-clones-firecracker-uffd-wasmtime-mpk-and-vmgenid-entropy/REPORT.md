# MicroVM Snapshot Clones, UFFD Demand Paging, Wasmtime MPK Pooling, and Clone Entropy Safety

## Summary

Resuming pre-initialized runtime snapshots collapses serverless cold-start latency from hundreds of milliseconds (`~125 ms` bare microVM boot in Firecracker; `20 ms–60 s` language runtime initialization) down to `~4–10 ms` for KVM microVMs and sub-millisecond slot reuse in pooled WebAssembly runtimes, yet breaks two foundational isolation invariants unless explicitly engineered across hardware, kernel, and userspace boundaries. First, demand-paging mechanisms (`MAP_PRIVATE` file CoW vs. `userfaultfd` in Firecracker, Cloud Hypervisor, and CRIU, and batched `madvise(..., MADV_DONTNEED)` vs. `keep_resident` in-place zeroing and Intel `MPK`/`PKRU` striping in Wasmtime) shift bottlenecks from cold disk reads into cross-core TLB shootdown storms, `EAGAIN` event-queue stalls, handler-crash guest freezes, and subtle protection-key resets on `mmap`. Second, cloning initialized RAM duplicates kernel CRNG state, userspace DRBGs, TLS session keys, and AES-GCM nonces; while Linux `v6.12` exposes `drivers/virt/vmgenid.c` to reseed `base_crng` and vDSO `getrandom()`, ACPI/DT notifications race against resumed vCPUs, `MADV_WIPEONFORK` rejects file-backed `MAP_PRIVATE` snapshot mappings with `-EINVAL`, and mainline Linux never merged the `MADV_WIPEONSUSPEND` or `/dev/SysGenId` synchronous watcher barriers proposed in `arXiv:2102.12892v1`. Across all analyzed systems, safe sub-millisecond multi-tenant snapshot cloning separates three orthogonal concerns: (1) non-escaping slot/region ownership (`Region`), (2) quantitative clone-entropy/residency budgets (`Grade`), and (3) synchronous pre-use reseed and domain-transition proofs (`Certificate`).

## Applicability

This report covers:

- **VMM snapshot and lazy restore engines**: `firecracker-microvm/firecracker` (`4e65d4309c355925872b9d3006f18eef96653645`, plus Agache et al. NSDI 2020), `cloud-hypervisor/cloud-hypervisor` (`a42550845786ec0f504b6cbde8ab705c50e47049`), and `checkpoint-restore/criu` (`3292b937138d045c12905dee89c78b9c05961f3b`). The Firecracker and Cloud Hypervisor findings govern KVM-backed Linux microVMs using `MemBackendType::{File, Uffd}` or `MemoryRestoreMode::{Copy, OnDemand, OnDemandNoBackgroundFetchPages, CopyOnWrite}` on `x86_64` and `aarch64` hosts; CRIU findings cover Linux userspace process checkpoint/restore with `lazy-pages` and `page-server`.
- **In-process sandbox pooling and hardware memory protection**: `bytecodealliance/wasmtime` (`3ce2209872ccf1ea115914a81e020aef66a10c51`, plus Narayan et al. PLAS 2022 ColorGuard) under Linux `x86_64` with `PoolingInstanceAllocator`, `DecommitQueue`, CoW `MemoryImageSlot`, and Intel/AMD Protection Keys for Userspace (`PKU`/`PKRU`). Non-`x86_64` targets and non-Linux hosts map Wasmtime's `mpk` module to no-ops and fall back to full `mmap` zeroing (`DecommitBehavior::Zero`).
- **Kernel uniqueness and memory revocation primitives**: `torvalds/linux` `v6.12` (`adc218676eef25575469234709c2d87185ca223a`) covering `drivers/virt/vmgenid.c`, `drivers/char/random.c`, and `mm/madvise.c`, evaluated directly against the interfaces proposed in Brooker et al. (`arXiv:2102.12892v1`, 2021).
- **Live execution probes**: Run on `Linux 7.1.6-1rodete1-amd64 x86_64` with `Python 3.13.15` to observe kernel `MADV_WIPEONFORK` behavior, `pkey_alloc` availability, multi-threaded `MADV_DONTNEED` vs. `memset` latencies, and `GF(2^128)` AES-GCM nonce-reuse tag forgery.

The subjects are compared orthogonally across memory backing/reset mechanisms, clone-uniqueness timing contracts, six-level performance and resource footprints (`L1`–`L6`), and human/conceptual model complexity (`C1`–`C2`).

## Findings

### 1. Snapshot Memory Restoration: Eager Copy, `MAP_PRIVATE` CoW, and `userfaultfd` Fault Storms

Basis: source + documentation

MicroVM snapshot restoration trades upfront I/O latency against page-fault tail latency and lifecycle coupling to the backing snapshot file:

| Engine & Mode | Backing Setup | Fault Path & I/O | Balloon / Decommit Interaction | Failure / Latency Traps |
|---|---|---|---|---|
| **Firecracker `MemBackendType::File`** | `File::open` + `MAP_PRIVATE` file mmap (`persist.rs:L478-L495,L608-L620`) | Host page cache CoW on write; shared RO pages across clones | `remap_anonymous_range` via `MAP_FIXED \| MAP_ANONYMOUS` (`memory.rs:L775-L777,L853-L865`) | Rejects `hugetlbfs` (`L479-L483`); truncated backing file causes `SIGBUS`; cgroup v1 adds severe restore latency (`snapshot-support.md:L128-L131`) |
| **Firecracker `MemBackendType::Uffd`** | Anonymous `MAP_PRIVATE \| MAP_NORESERVE` (`memory.rs:L182`); `Uffd` passed via `SCM_RIGHTS` UDS (`persist.rs:L639-L747`) | External handler issues `UFFDIO_COPY` / `UFFDIO_ZEROPAGE` | Enables `FeatureFlags::EVENT_REMOVE`; balloon `MADV_DONTNEED` emits `UFFD_EVENT_REMOVE` | Unhandled `remove` blocks all UFFD ioctls with `EAGAIN` (`on_demand_handler.rs:L34-L39`); crashed handler permanently freezes guest (`L735-L737`) |
| **Cloud Hypervisor `Copy` / `CopyOnWrite`** | `copy` reads full `memory-ranges`; `copyonwrite` maps file `MAP_PRIVATE` (`snapshot_restore.md:L127-L216`) | `copy` avoids runtime page-cache I/O; `copyonwrite` shares page cache | `virtio-balloon` `MADV_DONTNEED` on private file mapping causes next touch to reread snapshot bytes (`L199-L205`) | `copyonwrite` silently falls back to `Copy` for `shared=on`, hugepages, NUMA/hotplug/KSM/VFIO (`vm.rs:L1393-L1399`, `snapshot_restore.md:L181-L188`) |
| **Cloud Hypervisor `OnDemand` / `NoBackground`** | Opens `/dev/userfaultfd` (fallback `userfaultfd(2)`), strict failure without `copy` fallback (`L130-L169`) | Background pull (`ondemand`) vs. fault-only (`ondemand_no_background_fetch_pages`) | In `no_background`, VM remains permanently in `VmRestoring` state (`vm.rs:L197`, `doc:L138-L141`) | Rejects VFIO, vDPA, `vfio-user`, `prefault=on`; hot-plugging VFIO post-restore pins and write-faults every page (`L212-L216`) |
| **CRIU `lazy-pages` (+ `page-server`)** | Parasite dump (`criu/mem.c:L318-L746`); per-task UFFD registration (`criu/uffd.c:L1464-L1494`) | `epoll` loop splits IOVs at VMA boundaries (`L673-L678`) before `UFFDIO_COPY` (`L867`) | Uses `UFFDIO_ZEROPAGE` for absent pages (`L940-L946`); optional TCP `page-server` (`L1475-L1480`) | `UFFDIO_COPY` fails across VMA boundaries unless split; remote page-server stalls tail faults over RTT |

Three concrete implementation invariants emerge from reading these paths together:

1. **Firecracker UFFD handshake & handler liveness hazard (`persist.rs:L648-L745`)**: Firecracker creates the UFFD with `FeatureFlags::EVENT_REMOVE`, registers all guest regions, connects to the handler Unix domain socket, sends JSON `GuestRegionUffdMapping` (`base_host_virt_addr`, `size`, `offset`, `page_size`) plus the UFFD file descriptor via `send_with_fd`, and then deliberately calls `std::mem::forget(socket)` (`L744`) because closing the socket immediately can race ahead of the peer reading the mappings message. Crucially, Firecracker keeps its own reference to the UFFD descriptor (`L735-L737`): if the external handler process exits prematurely, guest memory does *not* fall back to zero-filled anonymous pages; instead every vCPU fault stalls indefinitely until external monitoring kills the VMM. Moreover, when `MemBackendType::Uffd` pairs with `virtio-balloon`, any pending `UFFD_EVENT_REMOVE` in the kernel UFFD queue causes all subsequent `UFFDIO_COPY`/`UFFDIO_ZEROPAGE` ioctls to fail with `EAGAIN` until events up to the `remove` are drained and pre-fetched (`on_demand_handler.rs:L34-L39`).
2. **Balloon `MADV_DONTNEED` semantic divergence (`fc_memory.rs:L774-L785` vs. `ch_snapshot_doc.md:L199-L205`)**: On a private file-backed CoW snapshot (`MAP_PRIVATE` over a regular file), calling `madvise(MADV_DONTNEED)` drops private CoW pages and causes subsequent guest reads to reload the *original snapshot bytes* rather than zeros. Firecracker therefore intercepts `MAP_PRIVATE` file-backed discards in `fc_memory.rs:L775-L777` via `remap_anonymous_range` (`mmap(..., MAP_FIXED | MAP_ANONYMOUS | MAP_PRIVATE | MAP_NORESERVE)` at `L853-L865`), converting the discarded range to anonymous zero-pages, whereas Cloud Hypervisor permits `MADV_DONTNEED` directly on `copyonwrite` mappings under the weaker assumption that guests will reinitialize ballooned pages before relying on their contents.
3. **Working-set UFFD fault storms**: Without proactive working-set prefetching (as in `ondemand_no_background_fetch_pages` or naive `on_demand_handler.rs`), each cold `4 KiB` guest access traps VM-exit -> KVM -> kernel UFFD waitqueue -> userspace handler -> `UFFDIO_COPY` kernel copy -> vCPU resume, turning a `16 MiB` (`4,096`-page) runtime working set into thousands of serialized `5–20 µs` fault round-trips (`20–80 ms` tail spikes) unless contiguous prefetching or `2 MiB` hugepage UFFD regions are used.

### 2. Clone Entropy Failures, Nonce Reuse, and Kernel-to-Userspace Uniqueness Gaps

Basis: normative + documentation + source + execution

Restoring $N > 1$ microVMs from an identical memory snapshot breaks the fundamental assumption of stateful cryptographic and distributed uniqueness: every clone inherits identical kernel CRNG state, userspace DRBG pools (`CTR_DRBG`, OpenSSL, Java `SecureRandom`, Go `math/rand`, JS `getRandomValues`), session tickets, and counter states. As noted in NIST SP 800-38D §8 (quoted in `arXiv:2102.12892v1` §2), invoking AES-GCM with the same `(Key, IV)` pair on two distinct messages with probability $> 2^{-32}$ compromises confidentiality and authentication.

```
Snapshot Created (T0) ---> Clones C1, C2 Restored (T1)
   |                           |
   |  [1] VMM writes VMGENID   |---> Firecracker: DeviceManager::restore() after KVM state (builder.rs:L587-L603)
   |      + triggers IRQ/ACPI  |     Cloud Hypervisor: regenerate_vmgenid() before start_restored_vcpus() (vm.rs:L2618)
   |                           |
   |  [2] vCPUs resume (T2)    |===> ASYNCHRONOUS RACE WINDOW: guest vCPUs can execute userspace AES-GCM / TLS
   |                           |     using cloned userspace DRBG BEFORE ACPI notify runs vmgenid_notify()!
   |                           |
   |  [3] Guest Kernel (T3)    |---> drivers/virt/vmgenid.c: vmgenid_notify() -> add_vmfork_randomness()
   |                           |     drivers/char/random.c:L991-L999 -> crng_reseed() -> _vdso_rng_data->generation++ (L293)
   |                           |
   |  [4] Userspace DRBG (T4)  |===> GAP: Unhooked userspace pools (OpenSSL/Java/Go) NEVER reseed on vmgenid IRQ!
   |                           |     Linux MADV_WIPEONFORK returns -EINVAL on file-backed MAP_PRIVATE VM RAM.
   |                           |     arXiv:2102.12892v1 MADV_WIPEONSUSPEND & /dev/SysGenId NOT in mainline Linux v6.12.
```

Source inspection of `torvalds/linux` `v6.12`, `firecracker`, `cloud-hypervisor`, and `criu` exposes four critical realities often conflated in secondary literature:

1. **Mainline Linux `v6.12` vs. Brooker et al. (`arXiv:2102.12892v1`) Disagreement**: In February 2021, Brooker et al. proposed two new kernel interfaces—`MADV_WIPEONSUSPEND` (a memory flag wiping marked pages on VM suspend to protect secrets from snapshot storage and signal DRBGs at `~600 ns` guard-check cost, §3.2) and `/dev/SysGenId` (a char device + `mmap` generation page + `SysGenId_WAIT_WATCHERS` ioctl barrier so orchestrators can block request dispatch until all userspace watchers acknowledge the clone epoch, §3.3). Direct inspection of Linux `v6.12` (`mm/madvise.c:L1067-L1077`, `drivers/virt/vmgenid.c:L1-L181`, `drivers/char/random.c:L254-L298,L991-L1011`) establishes that neither `MADV_WIPEONSUSPEND` nor `/dev/SysGenId` exists in upstream Linux `v6.12`. Instead, Linux `5.18` (ACPI) and `6.10` (DeviceTree) upstreamed Jason Donenfeld's `vmgenid` platform driver, which wires the 16-byte hypervisor UUID directly into `add_vmfork_randomness()` (`random.c:L991-L999`), forcing an immediate kernel `crng_reseed(NULL)`, incrementing `base_crng.generation`, updating the vDSO `getrandom()` generation counter (`_vdso_rng_data->generation` via `smp_store_release` at `L293`), and notifying in-kernel subscribers via `blocking_notifier_call_chain(&vmfork_chain, ...)`.
2. **The Asynchronous `VMGENID` Interrupt Race & Unhooked Userspace DRBGs**: Both Firecracker (`fc_builder.rs:L587-L625`, `fc_vmgenid.rs:L103-L149`) and Cloud Hypervisor (`ch_vm.rs:L2614-L2626`) carefully regenerate the 128-bit `gen_id`, write it to guest physical memory, and trigger the virtual interrupt *after* restoring KVM state and *before* launching vCPUs. However, in Linux `drivers/virt/vmgenid.c`, ACPI delivery (`acpi_install_notify_handler` at `L85-L86`) executes via ACPI workqueues after vCPU entry, creating a nonzero race window (explicitly warned in `fc_random_clones.md:L127-L131`) where an already-running guest thread calling `getrandom()` or reading `/dev/urandom` can observe pre-reseed kernel entropy before `vmgenid_notify()` executes. Worse, any userspace library holding its own seeded DRBG (`OpenSSL`, `BoringSSL`, `JVM SecureRandom` without explicit CRaC/SnapStart hooks, or `PRNG` buffers) ignores `base_crng.generation` completely unless it calls vDSO `getrandom()` per operation or attaches to a custom userspace notification hook (`fc_random_clones.md:L7-L12`; `ch_snapshot_doc.md:L267-L270`).
3. **`MADV_WIPEONFORK` Rejects File-Backed `MAP_PRIVATE` and Ignores VM/CRIU Clones**: In `mm/madvise.c:L1067-L1070`, Linux enforces `if (vma->vm_file || vma->vm_flags & VM_SHARED) return -EINVAL;`. Thus: (a) guest processes on anonymous `MAP_PRIVATE` heaps can wipe intra-guest `fork()` children, (b) hypervisor-side `MAP_PRIVATE` file-backed CoW VM memory cannot even accept `MADV_WIPEONFORK`, (c) VM snapshot restoration does not call `fork()` inside the guest so guest `VM_WIPEONFORK` VMAs are never wiped on VM clone, and (d) CRIU (`criu/mem.c`) has no `VM_WIPEONFORK` special handling during process restore because `fork()` has already completed before parasite memory restoration.
4. **Live Kernel & Algebraic Cryptographic Verification (`Probe 1A` & `Probe 1C`)**: Executed on `Linux 7.1.6-1rodete1-amd64 x86_64`, `Probe 1A` verified `madvise(anon, 4096, MADV_WIPEONFORK=18) -> rc=0` wipes child memory to all zeros (`child_all_zero=True`) while `madvise(file_map_private, 4096, MADV_WIPEONFORK=18) -> rc=-1, errno=22 (EINVAL)`. `Probe 1C` implemented exact NIST SP 800-38D `GF(2^{128})` arithmetic (`R = 0xE1 << 120`): when two restored clones emit single-block ciphertexts $C_1, C_2$ under identical `(K, IV)` with tags $T_1, T_2$, $C_1 \oplus C_2 = P_1 \oplus P_2$ leaks plaintext XOR directly, $H^2 = (T_1 \oplus T_2) \cdot (C_1 \oplus C_2)^{-1}$ recovers the exact `GHASH` authentication subkey $H = (H^2)^{2^{127}}$ in one `GF(2^{128})` inversion, and an attacker immediately computes $E(K, J_0)$ and forges a valid tag for arbitrary $C_3$ (`ghash_H_recovered_exact=True`, `forged_tag_valid=True`).

### 3. Wasmtime Virtual-Memory Pooling, `madvise` TLB Shootdowns, and `MPK`/`PKRU` Striping

Basis: source + documentation + execution

Rather than booting microVMs (`~5 MiB` overhead, `4–10 ms` snapshot restore), Wasmtime's `PoolingInstanceAllocator` achieves `< 100 µs` multi-tenant instantiation inside a single OS process by pre-allocating a contiguous `Mmap` virtual slab (`crates/wasmtime/src/runtime/vm/instance/allocator/pooling/memory_pool.rs:L110-L256`) partitioned into fixed-stride slots:

1. **Virtual Address Exhaustion vs. ColorGuard `MPK` Striping (`memory_pool.rs:L886-L993`)**: Standard bounds-check elision reserves `expected_slot_bytes = 4 GiB` plus `guard_bytes = 2 GiB` (`6 GiB` virtual address space per slot; `SlabConstraints` `L765-L818`), capping a `128 TiB` Linux user space to `~16K–21K` slots. Enabling `MPK` (`MemoryPool::new` `L188-L255`) allocates up to `15` hardware protection keys (`1..15`, leaving key `0` for host/kernel) via `pkey_alloc(0, 0)` into a process-global `OnceLock<Vec<ProtectionKey>>` (`mpk/enabled.rs:L24-L46`, never calling `pkey_free`). `calculate()` (`L915-L966`) stripes slots cyclically (`slot[i]` gets `pkeys[i % num_stripes]`) and shrinks each slot's virtual stride down toward `max_memory_bytes`:
   $$\text{slot\_bytes} = \max\left(\text{max\_memory\_bytes},\; \left\lfloor \frac{\text{faulting\_region\_bytes}}{\text{num\_stripes}} \right\rfloor\right), \quad \text{bytes\_to\_next\_stripe\_slot} = \text{slot\_bytes} \cdot \text{num\_stripes}$$
   Because adjacent slots carry distinct protection keys, an out-of-bounds Wasm load/store within `guard_bytes` hits a slot whose key is disabled in `PKRU` and still raises `SIGSEGV`, expanding per-process slot capacity up to `15x` (`16K` -> `256K` concurrent instances and `~29%` FaaS edge throughput uplift in Narayan et al., PLAS 2022). On entry to guest code, `restrict_to_pkey` (`pooling.rs:L831-L833`) executes `WRPKRU` (`ECX=0, EDX=0`, `pkru.rs:L47-L56`) setting all 2-bit `[WD, AD]` pairs in the 32-bit `PKRU` register except key `0` and the active tenant's key (`ProtectionMask::zero().or(pkey)`, `enabled.rs:L159-L170`), isolating tenant memories in `~20–25` user-space cycles with zero syscalls and zero TLB shootdowns.
2. **The `mmap` Key-Zero Silent Downgrade Trap (`enabled.rs:L112-L139`, `cow.rs:L553-L583`)**: In Linux, calling `mmap(MAP_FIXED)` over existing virtual addresses silently discards the PTE protection-key bits and resets pages to default protection key `0` (accessible to all stripes). Wasmtime therefore explicitly pairs every `image.map_at(&self.base)` (`cow.rs:L553`) and `image.remap_as_zeros_at(...)` (`L575`) with `self.reapply_pkey(...)` -> `ProtectionKey::reprotect` (`pkey_mprotect`), whereas `mprotect()` preserves existing keys. Notice also `MemoryPool::new` (`L206-L218`) initializes host threads with `ProtectionMask::all()`, creating a critical process-global hazard: any unrelated host library touching `PKRU` or running outside `StoreInner::call_hook` breaks isolation invariants unless the entire host binary respects key `0` vs. tenant keys `1..15`.
3. **Decommit `madvise(MADV_DONTNEED)` Shootdown Storms vs. `keep_resident` (`decommit_queue.rs`, `cow.rs:L600-L684`, `Probe 1B`)**: Reclaiming dirty pages across slots via `madvise(MADV_DONTNEED)` requires acquiring the process `mmap_lock` (or per-VMA lock in newer kernels) and issuing cross-CPU TLB shootdown IPIs to all cores running threads in the process, followed by kernel zero-page faults on next reuse. Wasmtime mitigates this through two orthogonal mechanisms:
   - **Sharded `DecommitQueue` batching (`pooling.rs:L205,L419-L495`, `decommit_queue.rs:L42-L233`)**: Thread-local round-robin shards (`thread_shard`) buffer `iovec` entries up to `decommit_batch_size` before calling `decommit_pages`, flushing all shards on `PoolConcurrencyLimitError`. If `decommit_pages` fails, `DecommitQueue::flush` (`L190-L195`) sets the slot's image to `None` (`ImageSlot::Unknown`) so the next allocator forces `reset_with_anon_memory()`.
   - **`linear_memory_keep_resident` in-place reset (`cow.rs:L600-L720`)**: Up to `keep_resident` bytes of accessed pages (tracked via `pagemap`) are overwritten in-place in user space (`manually_reset_region` for CoW backing images, `region.fill(0)` for anonymous heaps), bypassing kernel syscalls and TLB shootdowns entirely.
   - **Live benchmark (`Probe 1B`, `Linux 7.1.6 x86_64`)**: Measuring 64 KiB slot resets across 400 iterations per thread showed `keep_resident_memset` takes **`2,117.8 ns`** (`1` thread), **`21,495.9 ns`** (`4` threads), and **`53,115.4 ns`** (`8` threads), whereas `madvise(MADV_DONTNEED)` + 16-page refault takes **`29,418.6 ns`** (`1` thread — **`13.9x` slower**), **`142,855.1 ns`** (`4` threads), and **`286,452.0 ns`** (`8` threads — **`5.4x` slower**, or `286.5 µs` wall time per reset cycle). Simultaneously, `syscall(330, 0, 0)` (`pkey_alloc`) returned `-1 (EINVAL)` in this container/VM environment (`pku_available=False`), exercising Wasmtime's runtime `mpk::is_supported() == false` fallback to wide `PROT_NONE` guard pages.

### 4. Six-Level Quantitative Performance & Resource Footprint (`L1`–`L6`)

Basis: source + documentation + execution + derived

| Level | Metric / Dimension | Firecracker (`File` / `Uffd` + `VMGenID`) | Cloud Hypervisor (`CoW` / `OnDemand`) | CRIU (`lazy-pages`) | Wasmtime (`Pooling` + `MPK` + `keep_resident`) |
|---|---|---|---|---|---|
| **`L1` Authoring & Maintenance** | Subsystem LoC & proof/audit burden | `persist.rs` `1,139` LoC + `vmgenid.rs` `171` LoC + `memory.rs` `2,938` LoC; manual guest RNG checklist (`random-for-clones.md`) | `memory_manager.rs` `4,475` LoC + `vm.rs` `3,502` LoC; strict mode fallback rules (`copyonwrite` -> `copy`) | `uffd.c` `1,498` LoC + `mem.c` `1,811` LoC; external `compel` parasite injection | `pooling.rs` `981` + `memory_pool.rs` `1,229` + `cow.rs` `1,440` + `mpk/*.rs` `374` LoC |
| **`L2` Toolchain Build** | Host compilation cost | Rust Cargo workspace (`vmm` + `aws-lc-rs` C/asm build), `~1–3 min` release build, `~1–2 GiB` peak `rustc`/linker RSS | Rust Cargo workspace (`vmm` + `vm-migration`), `~1–3 min` release build | C + `protobuf-c` + parasite binary cross-build (`< 30 s` incremental) | Rust Cargo + `cranelift-codegen` build (`~2–4 min` release build, `~2–4 GiB` peak RSS) |
| **`L3` Snapshot / Slot Prep** | Snapshot create & pool init latency | Full snapshot synchronously writes & `fsync`s all guest RAM (`snapshot-support.md:L150-L158`); restore prep `~4 ms` (`arXiv:2102.12892`) | `copyonwrite` checks file size + `MAP_PRIVATE` setup; `send-migration` offload streams fds via `SCM_RIGHTS` | `parasite` seizes task tree, scans `/proc/pid/pagemap`, dumps pages (`mem.c:L555-L746`) | `MemoryPool::new`: 1 `mmap(PROT_NONE)` + `num_slots` `pkey_mprotect` calls at startup (`< 10 ms` for `1K` slots) |
| **`L4` Runtime Execution** | Dispatch, fault & domain-switch latency | `~4 ms` restore; `0.6 µs` `RDRAND`/`11 µs` `/dev/urandom` reseed; `5–20 µs` per UFFD fault; `< 10 ms` total resume | `copyonwrite` page-cache CoW; `ondemand` background pull + fault stalls (`VmRestoring` until complete) | `UFFDIO_COPY` / `ZEROPAGE` per faulted VMA slice; `page-server` adds TCP RTT | `~22 ns` (`~20–25` cycles) `WRPKRU` domain switch; **`2.1 µs`** (`1T`) / **`53.1 µs`** (`8T`) `keep_resident` reset vs **`29.4 µs`–`286.5 µs`** `MADV_DONTNEED` (`Probe 1B`) |
| **`L5` Safety / Admission** | Integrity & isolation validation | 64-bit CRC check on `vmstate` before load (`snapshot-support.md:L108-L113`); KVM EPT + seccomp-bpf filters | `copyonwrite` file-length pre-check (`L189-L190`); `offload_daemon` ACK barrier (`L425-L432`) | Pagemap/VMA boundary validation (`uffd.c:L673-L678`) | Linear-time Wasm bytecode validation + Cranelift bounds/MPK mask invariants; `ImageSlot` state machine (`Unmapped`/`Unknown`/`PreviouslyUsed`) |
| **`L6` Memory & Disk Footprint** | RSS, virtual slab & state artifact sizes | `< 5 MiB` VMM RSS overhead (`Agache et al., NSDI 2020`); `vmstate` + `mem` snapshot files; `16 B` `VMGENID` RAM | `config.json` (`~1 KiB`) + `state.json` (`~200 KiB`) + `memory-ranges`; reflink CoW snapshot on XFS/btrfs (`L206-L211`) | `pages-*.img` + `pagemap-*.img`; zero-copy `UFFDIO_ZEROPAGE` avoids allocating zero pages | `< 380 KiB`–`1 MiB` resident slot footprint; `6 GiB`/slot virtual without MPK (`16K` cap) vs up to `15x` compression (`256K` slots, PLAS 2022) |

*Calibration note on `L1`–`L6`*: By comparison with full-binary deductive verification baselines (such as formally proving `< 64 MiB` safety over `18K` RISC-V instruction libraries in `~600K` LoC Rocq, `> 30:1` proof-to-code expansion), runtime isolation layers (`Firecracker` `~4.2 KLoC` persistence/memory/VMGenID, `Wasmtime` `~4.0 KLoC` pooling/CoW/MPK) achieve high runtime assurance through small, localized `Rust` state machines and hardware MMU/PKU enforcement—yet leave the cross-layer *concurrency and entropy* invariants (snapshot-to-DRBG reseed causality, `mmap`-to-`pkey_mprotect` coupling) unverified by the type system itself.

### 5. Human Comprehensibility (`C1`) and Universal Model Refinement (`C2`)

Basis: derived + source

#### (`C1`) Human Comprehensibility & Mental-Model Ergonomics

A single human systems engineer diagnosing a snapshot clone stack must hold **9+ disjoint, non-local mechanisms** in working memory: (1) `MAP_PRIVATE` file vs. anonymous discard semantics (`MADV_DONTNEED` rereads file bytes vs. zeros), (2) UFFD `EVENT_REMOVE` -> `EAGAIN` queue head-of-line blocking, (3) `forget(socket)` fd-close ordering across `SCM_RIGHTS`, (4) ACPI workqueue latency vs. vCPU entry on `VMGENID`, (5) kernel `base_crng.generation` vDSO update vs. silent userspace `CTR_DRBG` staleness, (6) `MADV_WIPEONFORK` `-EINVAL` on file VMAs, (7) `mmap(MAP_FIXED)` silently clearing PTE `PKRU` keys back to key `0`, (8) `DecommitQueue` failure falling back to `ImageSlot::Unknown`, and (9) process-global `PKRU` pollution from non-Wasm host threads.

While an automated coding agent can syntactically inspect each file independently, **human engineers face acute non-local reasoning traps**: the failure of `MADV_WIPEONFORK` only manifests when combined with file-backed `MAP_PRIVATE`; the `VMGENID` race only manifests in the microsecond window before ACPI IRQ delivery; and the `MPK` key-0 downgrade only triggers on cross-image `mmap(MAP_FIXED)` eviction under `ImageSlot::Unknown` fallback. Worse, none of these failure modes produce local compiler diagnostics—they fail silently at runtime as nonce reuse (`Probe 1C`), `SIGBUS`, frozen vCPUs, or silent cross-tenant read/write exposure (`key 0`).

#### (`C2`) Conceptual Simplicity, Adapter Conservation & Minimal Universal Model

Applying Ousterhout's Deep Module test, Daniel Jackson's Concept Design, and Felleisen's macro-expressibility criterion exposes unnecessary mechanism sprawl across VMM snapshots and pooled sandboxes:

- **Redundant mechanisms enforcing one semantic invariant**: `MADV_WIPEONFORK`, `MADV_WIPEONSUSPEND`, `VMGENID` ACPI notifies, `/dev/SysGenId`, and `pthread_atfork` are five distinct interfaces trying to enforce a single invariant—*clone-epoch linearity on entropy and secret state*. Pushing `MADV_WIPEONFORK` onto anonymous pages only, or relying on async ACPI IRQs, violates **Adapter Conservation**: complexity is pushed into application-level `rerand` ioctls (`fc_random_clones.md:L197-L269`), `boot_id` bind-mounts, and runtime Java SnapStart hooks.
- **Minimal orthogonal model (3 core concepts)**:
  1. **`Region<Brand, Backing>`**: Unifies slot isolation (`MPK` stripe / KVM memslot), discard semantics (strictly zero-on-discard, eliminating `MADV_DONTNEED`-rereads-file leaks), and non-escaping ownership so `mmap(MAP_FIXED)` cannot strip `ProtectionKey` tags without re-establishing the brand invariant in the same atomic capability step.
  2. **`Epoch<Gen>` (Monotonic Clone Generation Token)**: Replaces separate `fork`, `CRIU`, and `VMGenID` ad-hoc hooks with a single synchronous vDSO-readable 128-bit generation counter updated *before* vCPU/thread resumption (`start_restored_vcpus`).
  3. **`Typestate<Entropy, Gen>` (Reseed-Before-Use Obligation)**: Models a userspace DRBG or AES-GCM key/IV generator as `DRBG<Gen>` checked against the current `Epoch<Gen>` via a single branch prior to cryptographic emission (`~600 ns` amortized to `0` across TLS records, `arXiv:2102.12892v1` §4). Under Felleisen expressiveness, this *cannot* be macro-expressed solely via async ACPI interrupts without an external pre-dispatch fence (`SysGenId_WAIT_WATCHERS` or synchronous vDSO epoch check before first branch).

## Boundaries

- **Linux `MADV_WIPEONSUSPEND` and `/dev/SysGenId` adoption in mainline kernels (`known not to apply` to Linux `v6.12`)**: Although `arXiv:2102.12892v1` (§3.2–§3.3) presents both interfaces as Linux kernel contributions, `torvalds/linux` `v6.12` (`adc218676eef25575469234709c2d87185ca223a`) contains only `drivers/virt/vmgenid.c` (`VMGENID` ACPI/DT -> `add_vmfork_randomness()`). Production deployments on upstream kernels cannot rely on `MADV_WIPEONSUSPEND` or `SysGenId_WAIT_WATCHERS`.
- **`x86_64` `PKU`/`PKRU` availability inside nested/containerized environments (`execution` observed `unsupported` on test host)**: `Probe 1B` observed `pkey_alloc(0, 0) -> -1 (EINVAL)` on `Linux 7.1.6-1rodete1-amd64` inside the execution environment, matching Wasmtime's `mpk::is_supported() == false` path (`crates/wasmtime/src/runtime/vm/mpk/enabled.rs`). Latency and slot-density benefits of ColorGuard (`PLAS 2022`) apply only on bare-metal or PKU-passthrough VMs with Intel Skylake-SP+ / AMD Zen 3+ CPUID `PKU` + `OSPKE` enabled, and remain bounded to `15` hardware protection stripes (`pkey 1..15`).
- **Confidential VMs (`SEV-SNP` / `TDX`), `guest_memfd`, and `VFIO` passthrough (`not examined` / `unsupported`)**: Firecracker notes diff snapshots with `guest_memfd` remain in developer preview (`fc_snapshot_doc.md:L123-L124`), Cloud Hypervisor explicitly rejects `offload` snapshot/restore for CVMs (`ch_snapshot_doc.md:L447-L448`) and `ondemand` UFFD for `VFIO`/`vDPA`/`vfio-user` (`L152-L154`). Encrypted guest RAM prevents external VMM page-cache sharing across clones.
- **Process-global `PKRU` integrity against arbitrary host FFI (`known not to apply` beyond Wasmtime hooks)**: `Wasmtime` calls `mpk::allow(ProtectionMask::all())` in `MemoryPool::new` (`L217`) and swaps `PKRU` in store entry/exit hooks; untrusted host C extensions, signal handlers (`SA_ONSTACK` restoring pre-signal `PKRU`), or speculative Meltdown/Spectre gadgets that execute `WRPKRU` or `XRSTOR` within the same address space bypass key `0` protection unless screened by a binary scanner (`L5`) or hardware CET/SFI gate.
- **Non-Linux OSes (`known not to apply` for `keep_resident` / `MADV_DONTNEED` / `MPK`)**: On Windows and macOS (`DecommitBehavior::Zero` in `wasm_cow.rs:L626-L635`), Wasmtime skips `keep_resident` in-place resets and `MPK`, falling back to `reset_with_anon_memory()`.
- **Pre-snapshot cached tokens (`TOCTOU` boundary, `unknown` without application auditing)**: As established in `arXiv:2102.12892v1` §3.7, even synchronous `VMGENID` / `SysGenId` cannot invalidate random UUIDs, nonces, or TLS `ClientRandom` values generated and cached *before* snapshot creation.

## Evidence

All observations were collected on `2026-11-19` directly from pinned upstream commits, verified papers, and executed probes:

### Primary Source Locations
- **Firecracker (`firecracker-microvm/firecracker` @ `4e65d4309c355925872b9d3006f18eef96653645`)**:
  - `src/vmm/src/persist.rs`: `GuestRegionUffdMapping` (`L120-L132`), `create_snapshot` (`L176-L207`), `restore_from_snapshot` (`L419-L515`), `MemBackendType::{File, Uffd}` (`L477-L503`), `guest_memory_from_uffd` (`L639-L671`), `send_uffd_handshake` (`L696-L747`, `forget(socket)` at `L744`).
  - `src/vmm/src/builder.rs`: `build_microvm_from_snapshot` (`L510-L630`), `DeviceManager::restore` ordered after KVM state restore (`L587-L603`), `start_vcpus` (`L615-L621`).
  - `src/vmm/src/devices/acpi/vmgenid.rs`: `VMGENID_MEM_SIZE = 16` (`L18`), `VmGenId::from_parts` (`L57-L73`), `make_genid` (`L93-L97`), `do_post_restore` (`L103-L109`), `activate` (`L112-L122`), `Persist` (`L135-L150`), `Aml` `_SB_.VGEN` (`L152-L171`).
  - `src/vmm/src/vstate/memory.rs`: `MAP_PRIVATE | MAP_NORESERVE | MAP_ANONYMOUS` (`L182`), `remap_anonymous_range` on private file discards (`L775-L777`), `MADV_REMOVE` (`L780-L782`), `MAP_FIXED` anonymous discard (`L853-L865`).
  - `src/firecracker/examples/uffd/on_demand_handler.rs`: `UFFD_EVENT_REMOVE` `EAGAIN` queue blocking (`L34-L39`).
  - `docs/snapshotting/{handling-page-faults-on-snapshot-resume.md, random-for-clones.md, snapshot-support.md}`: UFFD handshake and crash hang behavior (`L60-L165`), clone RNG race window and `rerand` annex (`L127-L269`), 64-bit CRC & cgroup v1 note (`L107-L131`).
- **Cloud Hypervisor (`cloud-hypervisor/cloud-hypervisor` @ `a42550845786ec0f504b6cbde8ab705c50e47049`)**:
  - `vmm/src/vm.rs`: `MemoryRestoreMode::CopyOnWrite` fallback (`L1393-L1399`), `regenerate_vmgenid()` prior to `start_restored_vcpus()` (`L2613-L2627`).
  - `vmm/src/memory_manager.rs`: `UffdRegistry` (`L73-L175`), `MemoryZone` (`L251-L256`), `snapshot_memory_ranges` / `cow_source` (`L383-L385`).
  - `docs/snapshot_restore.md`: `ondemand` / `ondemand_no_background_fetch_pages` / `copyonwrite` (`L120-L216`), `VMGenID` (`L245-L273`), `offload_daemon` (`L275-L448`).
- **CRIU (`checkpoint-restore/criu` @ `3292b937138d045c12905dee89c78b9c05961f3b`)**:
  - `criu/uffd.c`: `lazy_pages_info`, VMA-split `UFFDIO_COPY` (`L673-L678, L867`), `UFFDIO_ZEROPAGE` (`L940-L946`), `page-server` (`L775-L777, L1475-L1480`).
  - `criu/mem.c`: parasite dump (`L318-L746`), `MADV_DONTNEED` (`L1460`), zero occurrences of `WIPEONFORK` in `L1-L1811`.
- **Wasmtime (`bytecodealliance/wasmtime` @ `3ce2209872ccf1ea115914a81e020aef66a10c51`)**:
  - `crates/wasmtime/src/runtime/vm/instance/allocator/pooling.rs`: `PoolingInstanceAllocator`, `decommit_queues`, `with_flush_and_retry`, `restrict_to_pkey` (`L88-L205, L453-L495, L827-L837`).
  - `crates/wasmtime/src/runtime/vm/instance/allocator/pooling/decommit_queue.rs`: `DecommitQueue` (`L42-L233`).
  - `crates/wasmtime/src/runtime/vm/instance/allocator/pooling/memory_pool.rs`: `MemoryPool`, `Stripe`, `ImageSlot`, `SlabConstraints`, `calculate` (`L27-L260, L594-L633, L765-L993`).
  - `crates/wasmtime/src/runtime/vm/mpk/{mod.rs, enabled.rs, pkru.rs}`: `keys()` `OnceLock`, `ProtectionKey::reprotect` (`L112-L139`), `ProtectionMask` (`L148-L170`), `rdpkru`/`wrpkru` (`L34-L56`).
  - `crates/wasmtime/src/runtime/vm/cow.rs`: `instantiate` / `remove_image` `reapply_pkey` (`L480-L583`), `clear_and_remain_ready` / `reset_with_original_mapping` (`L600-L720`).
- **Linux Kernel `v6.12` (`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a`)**:
  - `drivers/virt/vmgenid.c` (`L1-L181`), `drivers/char/random.c` (`L254-L298, L991-L1011`), `mm/madvise.c` (`L1067-L1077`).
- **Literature**: Agache et al. (NSDI 2020), Brooker et al. (`arXiv:2102.12892v1`, Feb 2021), Narayan et al. (PLAS 2022, Segue & ColorGuard).

### Reproducible Execution Probe & Recorded Output

Environment: `Linux 7.1.6-1rodete1-amd64 x86_64`, `Python 3.13.15`. Command: `python3 /tmp/probe_pkg1.py`.

```python
#!/usr/bin/env python3
"""Micro-probes for microVM snapshot clones, MADV_WIPEONFORK, UFFD/madvise decommit, MPK, and GCM nonce reuse."""

from __future__ import annotations

import ctypes
import errno
import os
import tempfile
import threading
import time

libc = ctypes.CDLL("libc.so.6", use_errno=True)
libc.madvise.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
libc.madvise.restype = ctypes.c_int
libc.mmap.argtypes = [
    ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long
]
libc.mmap.restype = ctypes.c_void_p
libc.munmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
libc.munmap.restype = ctypes.c_int
libc.memset.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_size_t]
libc.memset.restype = ctypes.c_void_p
libc.syscall.argtypes = [ctypes.c_long, ctypes.c_uint, ctypes.c_uint]
libc.syscall.restype = ctypes.c_long

MADV_DONTNEED = 4
MADV_WIPEONFORK = 18
MAP_PRIVATE = 0x02
MAP_ANONYMOUS = 0x20
MAP_FAILED = ctypes.c_void_p(-1).value
PROT_READ_WRITE = 0x3
SYS_PKEY_ALLOC_X86_64 = 330
SYS_PKEY_FREE_X86_64 = 331


def probe_1a_wipeonfork() -> None:
    print("=== Probe 1A: Live Linux MADV_WIPEONFORK on Anonymous vs File-Backed MAP_PRIVATE ===")
    size = 4096
    seed = b"DRBG_SEED_0123456789ABCDEF012345"

    anon_addr = libc.mmap(None, size, PROT_READ_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
    assert anon_addr != MAP_FAILED, f"anon mmap failed: {ctypes.get_errno()}"
    ctypes.memmove(anon_addr, seed, len(seed))
    rc_anon = libc.madvise(anon_addr, size, MADV_WIPEONFORK)
    err_anon = ctypes.get_errno()

    r_fd, w_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r_fd)
        child_bytes = ctypes.string_at(anon_addr, len(seed))
        os.write(w_fd, child_bytes)
        os.close(w_fd)
        os._exit(0)
    os.close(w_fd)
    child_seen = os.read(r_fd, len(seed))
    os.close(r_fd)
    os.waitpid(pid, 0)
    parent_seen = ctypes.string_at(anon_addr, len(seed))
    libc.munmap(anon_addr, size)

    print(f"anon_madvise_wipeonfork_rc={rc_anon} errno={err_anon}")
    print(f"anon_parent_preserved={parent_seen == seed} child_all_zero={child_seen == b'\x00' * len(seed)}")

    with tempfile.NamedTemporaryFile() as tf:
        tf.write(b"\xaa" * size)
        tf.flush()
        file_addr = libc.mmap(None, size, PROT_READ_WRITE, MAP_PRIVATE, tf.fileno(), 0)
        assert file_addr != MAP_FAILED, f"file mmap failed: {ctypes.get_errno()}"
        ctypes.set_errno(0)
        rc_file = libc.madvise(file_addr, size, MADV_WIPEONFORK)
        err_file = ctypes.get_errno()
        libc.munmap(file_addr, size)
    print(f"file_map_private_wipeonfork_rc={rc_file} errno={err_file} ({errno.errorcode.get(err_file, 'UNKNOWN')})")


def probe_1b_decommit_vs_keep_resident_and_pku() -> None:
    print("\n=== Probe 1B: Multi-Threaded madvise(MADV_DONTNEED)+Refault vs In-Place Zeroing & PKU ===")
    ctypes.set_errno(0)
    pkey = libc.syscall(SYS_PKEY_ALLOC_X86_64, 0, 0)
    pkey_err = ctypes.get_errno()
    if pkey >= 0:
        libc.syscall(SYS_PKEY_FREE_X86_64, int(pkey), 0)
        print(f"x86_64_pkey_alloc_rc={pkey} pku_available=True")
    else:
        print(f"x86_64_pkey_alloc_rc={pkey} errno={pkey_err} ({errno.errorcode.get(pkey_err, 'UNKNOWN')}) pku_available=False")

    slot_bytes = 65536
    iters = 400

    for mode in ("keep_resident_memset", "madvise_dontneed_refault"):
        for nthreads in (1, 4, 8):
            total_bytes = slot_bytes * nthreads
            base = libc.mmap(None, total_bytes, PROT_READ_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
            assert base != MAP_FAILED
            ctypes.memset(base, 0x5A, total_bytes)
            barrier = threading.Barrier(nthreads)
            t0 = [0.0]
            t1 = [0.0]

            def worker(tid: int) -> None:
                addr = base + tid * slot_bytes
                buf = (ctypes.c_uint8 * slot_bytes).from_address(addr)
                barrier.wait()
                if tid == 0:
                    t0[0] = time.perf_counter_ns()
                for _ in range(iters):
                    if mode == "keep_resident_memset":
                        ctypes.memset(addr, 0, slot_bytes)
                        buf[0] = 1
                    else:
                        rc = libc.madvise(addr, slot_bytes, MADV_DONTNEED)
                        assert rc == 0
                        for off in range(0, slot_bytes, 4096):
                            buf[off] = 1
                barrier.wait()
                if tid == 0:
                    t1[0] = time.perf_counter_ns()

            threads = [threading.Thread(target=worker, args=(i,)) for i in range(nthreads)]
            for th in threads:
                th.start()
            for th in threads:
                th.join()
            libc.munmap(base, total_bytes)
            per_op_ns = (t1[0] - t0[0]) / iters
            print(f"mode={mode} threads={nthreads} wall_ns_per_slot_reset={per_op_ns:.1f}")


R_POLY = 0xE1 << 120


def gf128_mul(x: int, y: int) -> int:
    z = 0
    v = y
    for i in range(128):
        if (x >> (127 - i)) & 1:
            z ^= v
        lsb = v & 1
        v >>= 1
        if lsb:
            v ^= R_POLY
    return z


def gf128_pow(x: int, e: int) -> int:
    res = 1 << 127
    base = x
    while e > 0:
        if e & 1:
            res = gf128_mul(res, base)
        base = gf128_mul(base, base)
        e >>= 1
    return res


def gf128_inv(x: int) -> int:
    return gf128_pow(x, (1 << 128) - 2)


def ghash_1blk(h: int, c_blk: int) -> int:
    len_blk = 128
    y = gf128_mul(c_blk, h)
    return gf128_mul(y ^ len_blk, h)


def probe_1c_gcm_nonce_reuse() -> None:
    print("\n=== Probe 1C: GF(2^128) AES-GCM GHASH Key Recovery Under Clone Nonce Reuse ===")
    h_secret = 0x66E94BD4EF8A2C3B884CFA59CA342B2E
    e_k_j0 = 0x58E2FCCEFA7E3061367F1D57A4E7455A
    keystream_1 = 0x0388DACE60B6A392F328C2B971B2FE78

    p1 = int.from_bytes(b"SECRET_TOKEN_001", "big")
    p2 = int.from_bytes(b"SECRET_TOKEN_002", "big")
    c1 = p1 ^ keystream_1
    c2 = p2 ^ keystream_1
    t1 = ghash_1blk(h_secret, c1) ^ e_k_j0
    t2 = ghash_1blk(h_secret, c2) ^ e_k_j0

    delta_c = c1 ^ c2
    delta_t = t1 ^ t2
    h_sq = gf128_mul(delta_t, gf128_inv(delta_c))
    h_recovered = gf128_pow(h_sq, 1 << 127)
    e_k_j0_recovered = t1 ^ ghash_1blk(h_recovered, c1)
    p3_forged = int.from_bytes(b"FORGED_ADMIN_CMD", "big")
    c3_forged = p3_forged ^ keystream_1
    t3_forged = ghash_1blk(h_recovered, c3_forged) ^ e_k_j0_recovered
    t3_expected = ghash_1blk(h_secret, c3_forged) ^ e_k_j0

    print(f"plaintext_xor_leaked={(c1 ^ c2) == (p1 ^ p2)}")
    print(f"ghash_H_recovered_exact={h_recovered == h_secret}")
    print(f"forged_tag_valid={t3_forged == t3_expected}")


if __name__ == "__main__":
    probe_1a_wipeonfork()
    probe_1b_decommit_vs_keep_resident_and_pku()
    probe_1c_gcm_nonce_reuse()
```

Observed output:

```text
=== Probe 1A: Live Linux MADV_WIPEONFORK on Anonymous vs File-Backed MAP_PRIVATE ===
anon_madvise_wipeonfork_rc=0 errno=0
anon_parent_preserved=True child_all_zero=True
file_map_private_wipeonfork_rc=-1 errno=22 (EINVAL)

=== Probe 1B: Multi-Threaded madvise(MADV_DONTNEED)+Refault vs In-Place Zeroing & PKU ===
x86_64_pkey_alloc_rc=-1 errno=22 (EINVAL) pku_available=False
mode=keep_resident_memset threads=1 wall_ns_per_slot_reset=2117.8
mode=keep_resident_memset threads=4 wall_ns_per_slot_reset=21495.9
mode=keep_resident_memset threads=8 wall_ns_per_slot_reset=53115.4
mode=madvise_dontneed_refault threads=1 wall_ns_per_slot_reset=29418.6
mode=madvise_dontneed_refault threads=4 wall_ns_per_slot_reset=142855.1
mode=madvise_dontneed_refault threads=8 wall_ns_per_slot_reset=286452.0

=== Probe 1C: GF(2^128) AES-GCM GHASH Key Recovery Under Clone Nonce Reuse ===
plaintext_xor_leaked=True
ghash_H_recovered_exact=True
forged_tag_valid=True
```

## Revalidation

1. **Linux Kernel Clone & `VMGENID` Check**:
   - Inspect `mm/madvise.c` (`case MADV_WIPEONFORK` and `MADV_WIPEONSUSPEND` grep) and `drivers/virt/vmgenid.c` on the target kernel tag; verify whether `MADV_WIPEONSUSPEND` or `/dev/sysgenid` has entered mainline or remains out-of-tree.
   - Rerun `Probe 1A` above (`< 100 ms`) to confirm `MADV_WIPEONFORK` still rejects file-backed `MAP_PRIVATE` mappings (`errno=22`).
2. **Firecracker & Cloud Hypervisor Ordering Check**:
   - Diff `src/vmm/src/builder.rs` (`DeviceManager::restore` vs. `kvm_vm.restore_state` and `start_vcpus`) and `src/vmm/src/persist.rs` (`guest_memory_from_uffd` / `forget(socket)`) in `firecracker`, and `vmm/src/vm.rs` (`regenerate_vmgenid()` vs. `start_restored_vcpus()`) in `cloud-hypervisor`.
   - Confirm whether `MemoryRestoreMode::CopyOnWrite` balloon discards (`MADV_DONTNEED`) remain distinct from Firecracker's `remap_anonymous_range`.
3. **Wasmtime `MPK` & Decommit Latency Revalidation**:
   - Check `crates/wasmtime/src/runtime/vm/cow.rs` and `mpk/enabled.rs` to verify every `mmap(MAP_FIXED)` call site (`instantiate`, `remove_image`, `reset_with_anon_memory`) invokes `ProtectionKey::reprotect` (`pkey_mprotect`).
   - Rerun `Probe 1B` on the target production host to measure actual `pkey_alloc` availability (`pku_available=True` vs. `False`) and the live crossover point between `keep_resident` in-place zeroing and batched `MADV_DONTNEED` TLB shootdowns across target worker thread counts.
