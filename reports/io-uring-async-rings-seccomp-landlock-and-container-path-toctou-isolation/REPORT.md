# Linux `io_uring` Shared Rings, `seccomp-BPF` Limits, `Landlock` LSM Object Capabilities, and Container Path-Resolution TOCTOU Isolation

## Summary

Modern Linux I/O and isolation boundaries expose four coupled soundness invariants across shared-memory rings, syscall filtering, Linux Security Module (LSM) object capabilities, and VFS path resolution:

1. **`io_uring` Shared-Memory Rings Trade Syscall-Entry Isolation for Shared-State Concurrency Hazards:** Because submission queue entries (`struct io_uring_sqe`) reside in memory concurrently mapped writable by userspace (`ctx->sq_sqes`), the kernel fetches a live pointer via `io_get_sqe()` rather than atomically snapshotting the entire 64- or 128-byte SQE up front. Preventing SQE double-fetch TOCTOU bugs therefore depends on strict `READ_ONCE()` discipline in `io_init_req()` and every opcode's `def->prep(req, sqe)` handler; unguarded plain reads (such as `if (!def->ioprio && sqe->ioprio)` in `io_uring/io_uring.c:1960`) remain structurally fragile under compiler reload or concurrent userspace mutation. Similarly, `IORING_REGISTER_BUFFERS` pins physical frames via `pin_user_pages_fast(..., FOLL_WRITE | FOLL_LONGTERM, ...)`, causing registered-buffer I/O (`IORING_OP_READ_FIXED`) to continue reading into kernel-pinned physical pages even after userspace calls `munmap(2)` on the corresponding virtual address range.
2. **`seccomp-BPF` Cannot Mediate Pointer-Indirected or Ring-Multiplexed Syscalls, Whereas `Landlock` LSM Enforces at VFS/Object Hooks:** Classic `seccomp-BPF` executes strictly over the 64-byte scalar `struct seccomp_data` snapshot (`nr`, `arch`, `instruction_pointer`, `args[6]`) and cannot dereference user pointers (`const char *path`, `struct open_how *`) or inspect `io_uring` SQEs resident in `mmap`-ed ring buffers. Live execution on Linux `7.1.6` confirms that a `seccomp-BPF` policy returning `EPERM` on `open`, `openat`, and `openat2` is completely bypassed by `io_uring` `IORING_OP_OPENAT` through an already-open ring descriptor. Conversely, `Landlock` LSM enforces object-capability rules inside VFS and socket LSM hooks (`hook_file_open`, `hook_path_rename`, `hook_path_link`, `hook_socket_bind`/`connect`), blocking unauthorized `IORING_OP_OPENAT` operations with `-EACCES` identically to synchronous `openat(2)`. Linux `7.4.0-rc3` additionally introduces in-ring cBPF filtering (`io_uring/bpf_filter.c`, `struct io_uring_bpf_ctx`), which validates kernel-copied opcode metadata (`socket`, `open` flags/mode/resolve, `connect` address/port) after `io_init_req()`, but still cannot inspect filenames and does not substitute for VFS object-capability confinement.
3. **Registered Fixed-File Reference Cycles Require Graph-Exact Garbage Collection and Nested-Ring Exclusion:** Coupling `io_uring` fixed-file tables with `AF_UNIX` `SCM_RIGHTS` descriptor passing previously created cross-subsystem reference-count undercounts and use-after-free races (`CVE-2022-2602`). In Linux `7.4.0-rc3`, `io_uring/rsrc.c` rejects registering any `io_uring` instance (`io_is_uring_fops(file)` -> `-EBADF`), while `net/unix/garbage.c` employs Tarjan's Strongly Connected Components (SCC) graph collector with `total_ref == vertex->out_degree` verification guarded by `unix_peek_seq` sequence counters (`read_seqcount_retry`) to prevent premature reclamation during concurrent `MSG_PEEK`.
4. **Object-Capability Path Confinement (`openat2(2)`) and Pre-Opened FD Hygiene Are Both Required to Prevent Container Breakouts:** `Landlock` mediates *new* file acquisition (`hook_file_open`) and reparenting (`LANDLOCK_ACCESS_FS_REFER`, uniquely denied by default even when unhandled), but does **not** revoke `pread`/`read`/`write` on already-open file descriptors inherited before `landlock_restrict_self(2)`. Container runtimes such as `runc` therefore require three orthogonal defenses verified in source and live execution: (a) sealed `memfd` self-cloning (`libcontainer/exeseal/cloned_binary_linux.go`, `F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE | F_SEAL_EXEC`) against `/proc/self/exe` host-binary overwrites (`CVE-2019-5736`), (b) `openat2(2)` with `RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS` (as implemented in `cyphar/libpathrs` and `runc`'s `internal/pathrs`) backed by kernel `complete_walk()` `path_is_under()` verification, and (c) `close_range(CLOSE_RANGE_CLOEXEC)` (`CloseExecFrom`), Go-runtime-aware descriptor scrubbing (`UnsafeCloseFrom`), and post-`chdir` `verifyCwd()` (`getcwd(2)` `"(unreachable)"` -> `ENOENT`) against leaked host file descriptors (`CVE-2024-21626`).

## Applicability

This report characterizes the interaction among six upstream implementations and three canonical CVE classes:

- **Kernel reference implementation (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `Linux 7.4.0-rc3`):** Authoritative source for `io_uring` ring memory ordering, SQE ingestion, `FOLL_LONGTERM` buffer registration, in-ring cBPF filters (`io_uring/bpf_filter.c`), `AF_UNIX` Tarjan SCC garbage collection (`net/unix/garbage.c`), `seccomp-BPF` (`kernel/seccomp.c`), `Landlock` LSM (ABI version `12` in `security/landlock/syscalls.c:194`), and `openat2(2)` scoped lookup (`fs/open.c`, `fs/namei.c`).
- **Live kernel execution environment (`Linux 7.1.6 x86_64`, Landlock ABI v9, `io_uring` features `0x3ffff`):** Empirical `Basis: execution` syscall probes (`openat2`, `io_uring_setup`/`enter`/`register`, `seccomp`, `landlock_*`) ran on a live `7.1.6` kernel. Where `7.4.0-rc3` source differs from `7.1.6` (specifically Landlock ABI v10 UDP rights and ABI v12 namespace/capability permissions, and Linux `7.4` `io_uring` in-ring cBPF filters), this report explicitly separates behaviors observed at runtime on `7.1.6` from features verified in `7.4.0-rc3` source.
- **Userspace ring, filter, capability, and container libraries:**
  - `axboe/liburing` @ `a10946dc51eeababc48ee10baf0d17489f647a80` characterizes the canonical userspace side of the `io_uring` SQ/CQ memory-ordering contract (`src/queue.c`, `src/include/liburing/barrier.h`).
  - `seccomp/libseccomp` @ `2814474a2bc105f5ffabf4bbc7ae9fb100997028` characterizes cBPF filter synthesis targeting `struct seccomp_data` (`src/gen_bpf.c`).
  - `landlock-lsm/rust-landlock` @ `5991c08320d2ade23db0ae3870709693fd5a213d` (`v0.4.7`) characterizes typed Rust bindings and ABI best-effort downgrade semantics (`ABI::V1`–`ABI::V9` in `src/compat.rs`, `src/ruleset.rs`).
  - `opencontainers/runc` @ `b7dc1304ed9e18f14e626dc06374043b12cf355f` and `cyphar/libpathrs` @ `05a4b54f9843ea1fb0ae86dc2f40550bde244589` characterize production OCI container isolation against symlink, magiclink, `/proc/self/exe`, and `/proc/self/fd` breakouts.

Findings apply to Linux x86_64 and ARM64 kernels supporting `io_uring` (5.1+), `openat2(2)` (5.6+), `close_range(2)` (5.9+; `CLOSE_RANGE_CLOEXEC` 5.11+), and `Landlock` (5.13+, ABI v1–v12). They do **not** generalize without re-verification to non-Linux kernels (FreeBSD Capsicum, OpenBSD `pledge`/`unveil`) or hypervisor-isolated microVMs.

## Findings

### 1. Linux `io_uring` Shared-Memory Ring Ordering and SQE Double-Fetch Races

#### 1.1 Lock-Free User↔Kernel SQ/CQ Memory-Ordering Protocol
Basis: documentation + source (`torvalds/linux/io_uring/io_uring.c:7-28,2121-2135`, `axboe/liburing/src/queue.c:13-37,247-278`, `axboe/liburing/src/include/liburing/barrier.h:28-40`).

`io_uring` replaces per-operation syscall argument marshaling with two memory-mapped single-producer/single-consumer ring buffers (Submission Queue `SQ`, Completion Queue `CQ`) plus a contiguous `sq_sqes` descriptor array. Correctness across weakly ordered CPUs (`ARM64`, `POWER`, `RISC-V`) and compiler optimizations requires paired acquire-release synchronization plus a full `StoreLoad` barrier under `IORING_SETUP_SQPOLL`:

| Ring Transition | Producer Side | Consumer Side | Required Barrier Pair | Failure Mode if Omitted |
| :--- | :--- | :--- | :--- | :--- |
| **SQ Publish (non-SQPOLL)** | Userspace writes `sqes[idx]` + `sq_array[idx]`, updates `*sq->ktail = tail` (`liburing/src/queue.c:269-270`) | Kernel enters `io_uring_enter(2)` and reads `rings->sq.tail` (`smp_load_acquire` in `io_get_sqring`) | Syscall entry barrier + kernel `smp_load_acquire` | Stale/torn SQE fields observed by kernel if syscall barrier absent |
| **SQ Publish (`IORING_SETUP_SQPOLL`)** | Userspace `io_uring_smp_store_release(sq->ktail, tail)` (`queue.c:272`), then **`io_uring_smp_mb()`** (`queue.c:31`), then `IO_URING_READ_ONCE(*ring->sq.kflags) & IORING_SQ_NEED_WAKEUP` (`queue.c:33-34`) | Kernel SQPOLL thread sets `IORING_SQ_NEED_WAKEUP`, issues full barrier, rechecks `sq.tail` before sleeping (`io_uring/sqpoll.c`) | Dekker `StoreLoad` full fence (`smp_mb`) on both sides | **Lost wakeup deadlock**: SQPOLL sleeps while new SQEs sit unconsumed in `sq_sqes` |
| **SQ Consume (Head Advance)** | Kernel finishes reading all SQEs in batch, commits `smp_store_release(&rings->sq.head, ctx->cached_sq_head)` (`io_uring.c:2133`) | Userspace reads `*sq->khead` with acquire semantics before reusing slot `idx` (`io_uring.c:21-23`) | Kernel `smp_store_release` -> User `smp_load_acquire` | Userspace overwrites an SQE slot while kernel is still parsing it |
| **CQ Publish** | Kernel writes `cqes[idx]`, updates `rings->cq.tail` with `smp_wmb()` / `smp_store_release` (`io_uring.c:9-11`) | Userspace reads `cq.tail` with `smp_load_acquire` (`io_uring.c:11`) | Kernel `smp_store_release` -> User `smp_load_acquire` | Userspace observes uninitialized or previous-generation CQE payload |
| **CQ Consume (Head Advance)** | Userspace reads `cqes[idx]`, commits `smp_store_release(cq->khead, head)` (`io_uring.c:12-16`) | Kernel reads `cq.head` with control dependency in `io_get_cqe` (`io_uring.c:13-15`) | User `smp_store_release` -> Kernel control dependency / acquire | Kernel overwrites unread CQE before userspace finishes loading `cqe->res` / `cqe->user_data` |

Notice the asymmetric fast-path optimization in `axboe/liburing/src/queue.c:269-272`: when `IORING_SETUP_SQPOLL` is **not** set, `liburing` performs a plain store `*sq->ktail = tail` relying on the subsequent `io_uring_enter(2)` syscall boundary, whereas `SQPOLL` mode upgrades to `io_uring_smp_store_release` plus an explicit `io_uring_smp_mb()` before inspecting `IORING_SQ_NEED_WAKEUP`. Any custom Rust/C `io_uring` client that omits the `SeqCst` / `smp_mb()` fence between publishing `sq.tail` and reading `sq.kflags` under `SQPOLL` introduces a Dekker store-buffering race causing permanent ring stalls.

#### 1.2 SQE Double-Fetch Architecture and Concrete `READ_ONCE` Fragility
Basis: source (`torvalds/linux/io_uring/io_uring.c:1875-1998,2137-2175`) + execution (formal SQE interleaving probe in `## Evidence`).

Unlike standard syscalls—where arguments are either latched in CPU registers on entry or copied once via `copy_from_user()` into private kernel stack storage—`io_get_sqe()` (`io_uring/io_uring.c:2145-2175`) returns a direct kernel pointer into the user-writable mmap region:

```c
/* io_uring/io_uring.c:2145-2175 */
static bool io_get_sqe(struct io_ring_ctx *ctx, const struct io_uring_sqe **sqe)
{
    unsigned mask = ctx->sq_entries - 1;
    unsigned head = ctx->cached_sq_head++ & mask;
    if (static_branch_unlikely(&io_key_has_sqarray.key) &&
        (!(ctx->flags & IORING_SETUP_NO_SQARRAY))) {
        head = READ_ONCE(ctx->sq_array[head]);
        if (unlikely(head >= ctx->sq_entries)) {
            WRITE_ONCE(ctx->rings->sq_dropped,
                       READ_ONCE(ctx->rings->sq_dropped) + 1);
            return false;
        }
        head = array_index_nospec(head, ctx->sq_entries);
    }
    if (ctx->flags & IORING_SETUP_SQE128)
        head <<= 1;
    *sqe = &ctx->sq_sqes[head];
    return true;
}
```

The kernel comment immediately preceding `io_get_sqe()` (`io_uring/io_uring.c:2138-2143`) explicitly documents the security contract:

> *"Note this returns a pointer to memory that is mapped by userspace. This means that care needs to be taken to ensure that reads are stable, as we cannot rely on userspace always being a good citizen. If members of the sqe are validated and then later used, it's important that those reads are done through `READ_ONCE()` to prevent a re-load down the line."*

Inspection of `io_init_req()` (`io_uring/io_uring.c:1875-1998`) reveals both the defensive pattern and a concrete remaining hazard:

1. **Snapshot discipline in `io_init_req()`:** Core fields are copied via `READ_ONCE()` into private kernel `struct io_kiocb` storage (`req->opcode = READ_ONCE(sqe->opcode)` with `array_index_nospec(req->opcode, IORING_OP_LAST)` at L1884–1898; `sqe_flags = READ_ONCE(sqe->flags)` at L1886; `req->cqe.user_data = READ_ONCE(sqe->user_data)` at L1888; `req->buf_index = READ_ONCE(sqe->buf_group)` at L1936; `req->cqe.fd = READ_ONCE(sqe->fd)` at L1968; `personality = READ_ONCE(sqe->personality)` at L1981).
2. **Residual double-fetch / plain-load surface:**
   - At `io_uring/io_uring.c:1960`, `if (!def->ioprio && sqe->ioprio) return io_init_fail_req(req, -EINVAL);` reads `sqe->ioprio` **without `READ_ONCE()`**. While opcodes with `!def->ioprio` should not re-read `sqe->ioprio`, any opcode with `def->ioprio != 0` delegates parsing of `sqe->ioprio`, `sqe->addr`, `sqe->len`, `sqe->off`, and `sqe->open_flags` directly to `def->prep(req, sqe)` (L1997), passing the live shared-memory pointer `sqe`. Every single opcode handler must therefore maintain zero-re-read `READ_ONCE()` invariants independently; a single validation-then-use re-read in any `prep()` handler reopens a classic kernel double-fetch TOCTOU vulnerability (demonstrated formally in the SQE interleaving probe in `## Evidence`: 1 of 3 canonical interleavings passes an invalid mutated value into `prep` whenever a snapshot is omitted, vs. 0 of 3 with `READ_ONCE` snapshotting).
   - For mixed-size 128-byte SQEs (`IORING_SETUP_SQE_MIXED`, L1901–1927), `def->is_128` requires two contiguous entries and explicitly rejects wraparound at the ring boundary (`(unsigned)(sqe - ctx->sq_sqes) >= ctx->sq_entries - 1`), preventing out-of-bounds kernel reads past the end of `sq_sqes` when an adversary mutates `sqe->opcode` to a 128-byte opcode at the final slot.
3. **Async Chain Assembly (`IOSQE_IO_LINK` / `IOSQE_IO_HARDLINK`):** In `io_submit_sqe()` (`io_uring/io_uring.c:2037-2091`) and `io_submit_fail_init()` (`L2000-2035`), linked SQEs are assembled into `ctx->submit_state.link` and call `io_req_sqe_copy(req, IO_URING_F_INLINE)` (L2065) to materialize deferred async data before `io_commit_sqring()` advances `rings->sq.head`. If any SQE in a link fails `io_init_req()` or BPF filtering, `io_submit_fail_init()` marks the failing request with `ret` and marks the link head with `REQ_F_FAIL` (`-ECANCELED`) while continuing to consume subsequent linked SQEs so SQPOLL chains do not desynchronize and execute orphan tail links.

### 2. Fixed Buffers (`FOLL_LONGTERM` Pinning vs. `munmap`), Fixed Files, and `AF_UNIX` GC Reference Cycles

#### 2.1 `IORING_REGISTER_BUFFERS` Long-Term Page Pinning vs. Userspace Virtual Memory Lifecycle
Basis: source (`torvalds/linux/io_uring/memmap.c:55-95`, `torvalds/linux/io_uring/rsrc.c:947-1051`) + execution (live `io_uring` `FOLL_LONGTERM` probe in `## Evidence`).

Registering fixed I/O buffers via `IORING_REGISTER_BUFFERS` (`io_sqe_buffers_register()` -> `io_sqe_buffer_register()` -> `io_pin_pages()`) invokes:

```c
/* torvalds/linux/io_uring/memmap.c:78-79 */
ret = pin_user_pages_fast(uaddr, nr_pages, FOLL_WRITE | FOLL_LONGTERM, pages);
```

This creates three critical memory-management and security invariants:

1. **Physical Page Detachment from Virtual Address Space (`munmap` / `mremap` / `fork` Hazard):** `pin_user_pages_fast()` with `FOLL_LONGTERM` elevates the physical page's `FOLL_PIN` reference count (`GUP_PIN_COUNTING_BIAS`), migrates pages out of `ZONE_MOVABLE`/CMA, and stores the resolved `struct page *` array inside `struct io_mapped_ubuf` (`imu->bvec[i]`, `io_uring/rsrc.c:1030-1037`). Once registered, `IORING_OP_READ_FIXED` and `IORING_OP_WRITE_FIXED` address memory through `imu->bvec` **without re-walking the process page tables**.
2. **Empirical Proof on Linux `7.1.6`:** In our live `FOLL_LONGTERM` probe (`Child C` in `## Evidence`), registering a 4 KiB anonymous mapping (`register=0`), unmapping it (`munmap=0`), and then issuing `IORING_OP_READ_FIXED` targeting the unmapped virtual address succeeded and transferred **`12 bytes`** directly into the orphaned physical page frame.
3. **Security & Verification Consequence:** In systems languages (C/C++/Rust) wrapping `io_uring`, dropping or unmapping a userspace buffer allocation without first completing `IORING_UNREGISTER_BUFFERS` (or updating the slot with `IO_REGBUF_TYPE_EMPTY` / awaiting all in-flight `io_rsrc_node` references) violates memory-safety ownership models:
   - If the allocator reuses the virtual address range via a new `mmap()`, userspace sees **new physical pages** while `io_uring` fixed-buffer I/O silently reads/writes the **old orphaned physical pages** (silent data loss / secret retention).
   - If a process calls `fork(2)` without `MADV_DONTFORK`, copy-on-write (`COW`) faults can split the child or parent PTE away from the DMA-pinned page unless the kernel honors `page_maybe_dma_pinned()` during write-protect/COW handling.
   - Because `FOLL_LONGTERM` pins are accounted against `RLIMIT_MEMLOCK` / `mm->pinned_vm`, unprivileged processes cannot pin unbounded RAM, but leaking registered buffer tables still exhausts locked-memory quotas until ring teardown calls `unpin_user_folio()` (`io_uring/rsrc.c:1043-1044`) or `unpin_user_pages()` (`io_uring/memmap.c:115`).

#### 2.2 Fixed-File Tables, `CVE-2022-2602`, and Modern Tarjan SCC `unix_gc`
Basis: source (`torvalds/linux/io_uring/rsrc.c:369-396,717-724`, `torvalds/linux/io_uring/filetable.c:43-85`, `torvalds/linux/net/unix/garbage.c:77-140,322-440`) + documentation (`CVE-2022-2602`) + execution (formal Tarjan SCC probe in `## Evidence`).

`io_uring` allows registering open file descriptors into an internal per-ring table (`ctx->file_table`, `IORING_REGISTER_FILES` / `IORING_REGISTER_FILES2`) indexed by `sqe->fd` with `IOSQE_FIXED_FILE`, avoiding atomic `fget()`/`fput()` per operation. Historically, placing `AF_UNIX` sockets inside `io_uring` fixed-file tables—and simultaneously passing the `io_uring` descriptor itself over an `AF_UNIX` socket via `SCM_RIGHTS`—created cross-subsystem reference cycles (`unix_sock -> sk_buff(SCM_RIGHTS) -> io_uring_fd -> file_table -> unix_sock`) that outlived all user file descriptor tables:

- **`CVE-2022-2602` Root Cause:** Earlier Linux kernels attempted to integrate `io_uring` fixed files directly into the legacy `AF_UNIX` garbage collector (`unix_gc`) via an auxiliary `ring_sock` and `scm_fp_list`. A race between `unix_gc()` reclaiming an apparently unreachable cycle and asynchronous `io_uring` cleanup/submission left `io_uring` holding a dangling `struct file *` after `unix_gc()` freed the underlying file—a reliably exploitable kernel UAF (commonly paired with DirtyCred heap spraying for local privilege escalation).
- **Linux `7.4.0-rc3` Structural Remediation:** Inspection of `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` establishes two complementary defenses:
  1. **Strict Nested-Ring Exclusion (`io_uring/rsrc.c:380-384, 720-723`):** Both `io_sqe_files_update()` and `io_sqe_files_register()` explicitly reject registering any `io_uring` file descriptor (`if (io_is_uring_fops(file)) { fput(file); err = -EBADF; break; }`), eliminating ring-to-ring cycles.
  2. **Tarjan SCC Cycle Collector with `MSG_PEEK` Seqcount Synchronization (`net/unix/garbage.c:77-85, 323-395`):** Linux replaced the legacy reference-decrement loop with a Tarjan Strongly Connected Components graph collector over `struct unix_vertex` and `struct unix_edge`. An SCC is declared dead (`unix_scc_dead()`, L374–395) **if and only if**:
     - Every vertex in the SCC has no outgoing `SCM_RIGHTS` edge to a non-inflight socket (`!next_vertex`, L348) or to another SCC (`next_vertex->scc_index != vertex->scc_index`, L354);
     - Every vertex satisfies `file_count(u->sk.sk_socket->file) == vertex->out_degree` (`unix_vertex_dead()`, L362–366), meaning zero external references (including `io_uring` fixed-file slots) remain; and
     - No concurrent `MSG_PEEK` occurred during the SCC scan (`read_seqcount_retry(&unix_peek_seq, seq)`, L391–392).

Our graph model (`## Evidence`, Probe 3) directly verifies this invariant: a closed pure `AF_UNIX` cycle `S1 <-> S2` with `total_ref == 1 == out_degree` yields `dead_sccs=[['S1', 'S2']]`, whereas holding a live `io_uring` fixed-file reference on `S1` (`total_ref[S1] = 2 != 1`) yields `dead_sccs=[]`—preserving liveness until the ring releases its slot, whereas any accounting undercount reproduces the `CVE-2022-2602` premature-reclamation hazard.

### 3. Why `seccomp-BPF` Fails on Pointer/Ring Syscalls vs. In-Ring BPF Filters and `Landlock` LSM

#### 3.1 `seccomp-BPF` Architectural Blindness (`struct seccomp_data`)
Basis: normative + source (`torvalds/linux/include/uapi/linux/seccomp.h:64-69`, `torvalds/linux/kernel/seccomp.c:280-294`, `seccomp/libseccomp/src/gen_bpf.c:113-116`) + execution (live `io_uring` vs. `seccomp-BPF` probe in `## Evidence`).

Linux `seccomp` executes classic BPF (`cBPF`) programs strictly over a 64-byte read-only structure populated from syscall-entry registers:

```c
/* include/uapi/linux/seccomp.h:64-69 */
struct seccomp_data {
    int nr;
    __u32 arch;
    __u64 instruction_pointer;
    __u64 args[6];
};
```

In `kernel/seccomp.c:280-294`, `seccomp_check_filter()` enforces that every `BPF_LD | BPF_W | BPF_ABS` instruction accesses a 4-byte-aligned offset strictly within `sizeof(struct seccomp_data)`. Likewise, `seccomp/libseccomp/src/gen_bpf.c:113-116` generates BPF rules solely against `_BPF_OFFSET_SYSCALL`, `_BPF_OFFSET_ARCH`, and the 32-bit halves of `args[0..5]`. Consequently, `seccomp-BPF` suffers from **two fundamental structural blind spots**:

1. **Pointer Indirection Opacity & User-Space TOCTOU:** For any syscall taking a pointer to userspace memory (`openat(dfd, const char *pathname, ...)`, `openat2(dfd, pathname, struct open_how *how, size)`, `connect(fd, struct sockaddr *addr, ...)`), `seccomp-BPF` sees only the raw virtual address in `args[i]`. Even when delegating to `SECCOMP_RET_USER_NOTIF` (`kernel/seccomp.c:76-79`), if the supervisor reads the tracee's memory via `process_vm_readv()` and replies `SECCOMP_USER_NOTIF_FLAG_CONTINUE`, another thread in the tracee's address space can overwrite the pathname or `struct open_how` between supervisor validation and kernel `copy_from_user()`—a classic cross-thread TOCTOU race. (Safe `seccomp_unotify` mediation must therefore execute the operation in the supervisor and inject the resulting descriptor via `SECCOMP_IOCTL_NOTIF_ADDFD`, never returning `CONTINUE` on unpinned user pointers.)
2. **Complete `io_uring` Syscall Multiplexing Bypass:** Once an `io_uring` instance exists (either created before installing the `seccomp` filter or permitted by an allowlist containing `io_uring_setup`/`io_uring_enter`), `io_uring_enter(fd, to_submit, min_complete, flags, arg, argsz)` carries **zero** operation opcodes or arguments in its six syscall registers. Every filesystem, network, and descriptor operation (`IORING_OP_OPENAT`, `IORING_OP_OPENAT2`, `IORING_OP_CONNECT`, `IORING_OP_UNLINKAT`, `IORING_OP_SOCKET`, etc.) flows invisibly through the shared-memory SQ ring.
   - **Live Execution Proof (`Linux 7.1.6`):** In `Child A` of Execution Probe 2 (`## Evidence`), we installed a strict `seccomp-BPF` filter returning `SECCOMP_RET_ERRNO | EPERM` for `SYS_open`, `SYS_openat`, and `SYS_openat2`. Direct `openat(AT_FDCWD, outside_secret.txt, O_RDONLY)` failed with `-1 (EPERM)`. Submitting `IORING_OP_OPENAT` for the exact same file through the pre-existing `io_uring` succeeded immediately (`fd=7`, read `'HOST_SECRET'`), demonstrating total bypass of syscall-level allowlists. This architectural mismatch is why container runtimes (Docker, containerd) and security-hardened platforms (Android, ChromeOS) default-deny `io_uring_setup` in `seccomp` profiles whenever ring-level or LSM-level controls are absent.

#### 3.2 `IORING_REGISTER_RESTRICTIONS` and Linux `7.4` In-Ring cBPF Filters (`io_uring/bpf_filter.c`)
Basis: source (`torvalds/linux/io_uring/register.c:130-165,201-205`, `torvalds/linux/include/uapi/linux/io_uring/bpf_filter.h:13-82`, `torvalds/linux/io_uring/bpf_filter.c:26-194`, `torvalds/linux/io_uring/io_uring.c:2044-2052`).

To narrow `io_uring`'s attack surface without banning it globally, the Linux kernel provides two ring-native mechanisms:

1. **Static Allowlist Restrictions (`IORING_REGISTER_RESTRICTIONS`):** Configured on a ring created with `IORING_SETUP_R_DISABLED` before `IORING_REGISTER_ENABLE_RINGS` (or task-scoped via `io_register_restrictions_task()` in `register.c:201`). Supports four bitmask restrictions (`register.c:133-152`): `IORING_RESTRICTION_REGISTER_OP`, `IORING_RESTRICTION_SQE_OP`, `IORING_RESTRICTION_SQE_FLAGS_ALLOWED`, and `IORING_RESTRICTION_SQE_FLAGS_REQUIRED` (e.g., forcing `IOSQE_FIXED_FILE` on every SQE so the sandboxed worker can only touch pre-registered descriptors).
2. **Linux `7.4` In-Ring cBPF Filters (`io_uring/bpf_filter.c`):** Invoked in `io_submit_sqe()` (`io_uring.c:2048-2052`) **after** `io_init_req()` + `def->prep()` have snapshotted SQE parameters into `struct io_kiocb` (eliminating SQE double-fetch against the filter itself!). The kernel populates a zero-cleared `struct io_uring_bpf_ctx` (`uapi/linux/io_uring/bpf_filter.h:13-47`) containing `opcode`, `sqe_flags`, `user_data`, and opcode-specific kernel-copied PDUs:
   - `socket`: `{ family, type, protocol }`;
   - `open`: `{ flags, mode, resolve }` (note: enforces `openat2` `RESOLVE_*` flags, **not** pathnames!);
   - `connect`: `{ family, port, v4_addr / v6_addr }` (copied from kernel sockaddr).
   Like `seccomp_check_filter()`, `bpf_filter.c:185-194` validates 32-bit-aligned `BPF_LD | BPF_W | BPF_ABS` loads bounded by `sizeof(struct io_uring_bpf_ctx)` and returns `-EACCES` on filter return `0`. Crucially, however, `io_uring` cBPF filters remain **pathname-blind** and require Linux `7.x+`—they complement rather than replace `Landlock` LSM.

#### 3.3 `Landlock` LSM Unprivileged Object-Capability Hierarchy (`ABI v1–v12`)
Basis: normative + source (`torvalds/linux/include/uapi/linux/landlock.h:25-103,383-632`, `torvalds/linux/security/landlock/syscalls.c:194,230,661,704-715`, `torvalds/linux/security/landlock/fs.c:755-1050,1277-1285`, `landlock-lsm/rust-landlock/src/compat.rs:51-82`, `landlock-lsm/rust-landlock/src/ruleset.rs:101-155`) + execution (live Landlock and `io_uring` probes in `## Evidence`).

`Landlock` is a stackable, unprivileged Linux Security Module (requiring `PR_SET_NO_NEW_PRIVS` or `CAP_SYS_ADMIN` in the current user namespace; Linux `7.4` also adds `LANDLOCK_RESTRICT_SELF_NO_NEW_PRIVS` in `landlock_syscalls.c:704-712`). Unlike `seccomp`, a `Landlock` domain attaches to the task's `cred` and evaluates access inside **kernel VFS and socket LSM hooks** (`security_file_open`, `security_path_rename`, `security_path_link`, `security_socket_bind`, `security_socket_connect`) by walking dentry/inode ancestry (`is_access_to_paths_allowed()` in `security/landlock/fs.c:795-1050`) against the domain's stacked ruleset layers:

| Landlock ABI | Linux Version | Key Capabilities Added (`uapi/linux/landlock.h` & `rust-landlock/src/compat.rs`) |
| :---: | :---: | :--- |
| **V1** | 5.13 | Base FS rights (`EXECUTE`, `WRITE_FILE`, `READ_FILE`, `READ_DIR`, `REMOVE_DIR`, `REMOVE_FILE`, `MAKE_{CHAR,DIR,REG,SOCK,FIFO,BLOCK,SYM}`) via `LANDLOCK_RULE_PATH_BENEATH` |
| **V2** | 5.19 | `LANDLOCK_ACCESS_FS_REFER` (`1ULL << 13`) — cross-directory `link`/`rename` reparenting check; **uniquely denied by default even when omitted from `handled_access_fs`** (`uapi/linux/landlock.h:25-27,465-468`) to prevent privilege escalation by moving a restricted subtree under a more permissive parent |
| **V3** | 6.2 | `LANDLOCK_ACCESS_FS_TRUNCATE` (`1ULL << 14`) — closes `truncate(2)` / `O_TRUNC` gap on files without `WRITE_FILE` rules |
| **V4** | 6.7 | `LANDLOCK_ACCESS_NET_BIND_TCP`, `LANDLOCK_ACCESS_NET_CONNECT_TCP` (port-level TCP confinement) |
| **V5** | 6.10 | `LANDLOCK_ACCESS_FS_IOCTL_DEV` (`1ULL << 15`) — restricts `ioctl(2)` on block/char device files |
| **V6** | 6.12 | `LANDLOCK_SCOPE_ABSTRACT_UNIX_SOCKET`, `LANDLOCK_SCOPE_SIGNAL` — isolates abstract UNIX sockets and cross-domain signaling |
| **V7–V9** | 6.15–7.1 | Audit/errata reporting (`LANDLOCK_CREATE_RULESET_ERRATA`), `rust-landlock` `0.4.7` covers `ABI::V1`–`V9` (`src/compat.rs:51-82`) |
| **V10** | 7.x | `LANDLOCK_ACCESS_NET_BIND_UDP`, `LANDLOCK_ACCESS_NET_CONNECT_SEND_UDP` (`uapi/linux/landlock.h:539-568`), including port `0` ephemeral auto-bind semantics |
| **V12** | 7.4-rc3 | `LANDLOCK_ACCESS_FS_RESOLVE_UNIX` (`1ULL << 16`), `LANDLOCK_PERMISSION_NAMESPACE_USE` (`unshare`/`clone`/`setns`/`open_tree`/`fsmount`), and `LANDLOCK_PERMISSION_CAPABILITY_USE` (`uapi/linux/landlock.h:518,615-631`, `syscalls.c:194`) |

**Three Critical Soundness Properties Verified Directly in Live Execution (`Linux 7.1.6`, ABI v9):**

1. **Mediation Across `io_uring`:** In `Child B` of Execution Probe 2 (`## Evidence`), restricting the process to read-only access under `jail/` caused `io_uring` `IORING_OP_OPENAT` to succeed on `jail/inside.txt` (`O_RDONLY`, `fd=7`), while rejecting `outside_secret.txt` (`O_RDONLY`) and `jail/inside.txt` (`O_WRONLY`) with **`-EACCES` (`-13`)**. Because `io_uring/openclose.c` dispatches into VFS `do_filp_open()` -> `security_file_open()`, Landlock enforces identically across synchronous syscalls and asynchronous ring submissions without pathname TOCTOU.
2. **Pre-Opened Descriptor Non-Revocation vs. `/proc/self/fd` Re-Open:** In Execution Probe 1 (`## Evidence`), a Landlock-confined child process that inherited an already-open `outfd` pointing to `outside_secret.txt` was **blocked (`EACCES`)** when attempting `open("/proc/self/fd/<outfd>", O_RDONLY)` (because reopening invokes `hook_file_open`), **yet succeeded in reading `11 bytes ('HOST_SECRET')` via `pread(outfd, ...)`**. Landlock is strictly an ambient-authority *acquisition* capability filter (plus `truncate`/`ioctl` hooks), not a retroactive FD revoker.
3. **Best-Effort ABI Downgrade Trap (`landlock-lsm/rust-landlock`):** `rust-landlock` (`src/compat.rs`, `src/ruleset.rs`) defaults to `CompatLevel::BestEffort`, silently dropping access bits unsupported by the running kernel and reporting `RulesetStatus::PartiallyEnforced` or `NotEnforced`. Security-critical sandboxes (such as container runtimes or build isolators) must either explicitly set `CompatLevel::HardRequirement` or assert `status.ruleset == RulesetStatus::FullyEnforced` and verify `status.no_new_privs == true`, lest a kernel downgrade silently strip `TRUNCATE`, `REFER`, or `NET_CONNECT_TCP` enforcement.

### 4. Capability-Confined Path Resolution (`openat2(2)`) and Container Runtime `/proc/self/{exe,fd}` Breakouts

#### 4.1 `openat2(2)` Kernel `LOOKUP_*` Semantics and `complete_walk()` Invariants
Basis: normative + source (`torvalds/linux/include/uapi/linux/openat2.h:1-50`, `torvalds/linux/fs/open.c:1208-1450`, `torvalds/linux/fs/namei.c:1056-1093,1138-1182,2046-2049,2192-2231,2724-2728`) + execution (live `openat2(2)` probe in `## Evidence`).

Traditional userspace path sanitization (`filepath.Clean`, `realpath`, or `chroot`-free lexical `..` stripping) is inherently vulnerable to concurrent symlink replacement and directory `renameat2()` TOCTOU races between validation and `openat(2)`. Linux `openat2(2)` (`struct open_how { u64 flags; u64 mode; u64 resolve; }`, validated for extensible forward/backward compatibility via `copy_struct_from_user()` in `fs/open.c`) moves root confinement inside kernel VFS `namei` traversal:

| `open_how.resolve` Flag | Kernel `namei` Flag & Enforcement Sites (`fs/namei.c`) | Semantics on Escape / Special Jump | Live Linux `7.1.6` Execution Result (`## Evidence`, Probe 1) |
| :--- | :--- | :--- | :--- |
| **`RESOLVE_BENEATH`** (`0x08`) | `LOOKUP_BENEATH` (`nd_jump_root` L1140, `follow_dotdot` L2195/L2228, `complete_walk` L1074–1092) | Any absolute path (`/`), `..` stepping above `dfd`, or symlink escaping `dfd` aborts lookup with **`-EXDEV`** | `../outside_secret.txt` -> `EXDEV` (18); `/etc/hostname` -> `EXDEV` (18); `link_escape` -> `EXDEV` (18); `inside.txt` -> `OK` |
| **`RESOLVE_IN_ROOT`** (`0x10`) | `LOOKUP_IN_ROOT` (`path_init` L2725, `follow_dotdot` L2192–2230, `complete_walk` L1074–1092) | Scopes `/` and `..` (including inside absolute symlinks) to `dfd` like per-syscall `chroot(2)` without `CAP_SYS_CHROOT`; clamps `..` at `dfd` | `/inside.txt` -> `OK`; `../../inside.txt` -> `OK`; `link_abs_inside` (`-> /inside.txt`) -> `OK`; `link_escape` (`-> ../outside_secret.txt`) -> `ENOENT` (2) (clamped inside `jail/`) |
| **`RESOLVE_NO_SYMLINKS`** (`0x04`) | `LOOKUP_NO_SYMLINKS` (`get_link` L2046–2048) | Rejects **all** symlink traversal (including intra-root relative symlinks and magiclinks) with **`-ELOOP`** | `link_rel_inside` (`-> inside.txt`) under `BENEATH\|NO_SYMLINKS` -> `ELOOP` (40) |
| **`RESOLVE_NO_MAGICLINKS`** (`0x02`) | `LOOKUP_NO_MAGICLINKS` (`nd_jump_link` L1179–1180) | Permits ordinary symlinks but blocks `/proc/<pid>/fd/*`, `/proc/<pid>/exe`, `/proc/<pid>/root` procfs magiclinks with **`-ELOOP`** | `/proc/self/fd/<outfd>` with `NO_MAGICLINKS` -> `ELOOP` (40); without flag -> `OK ('HOST_SECRET')` |
| **`RESOLVE_NO_XDEV`** (`0x01`) | `LOOKUP_NO_XDEV` (`nd_jump_root` L1142) | Blocks crossing mount points (including bind mounts) with **`-EXDEV`** | Prevents traversing host mounts mounted inside container rootfs |
| **`RESOLVE_CACHED`** (`0x20`) | `LOOKUP_CACHED` (`complete_walk` L1069) | Succeeds only via lockless RCU dcache hit; otherwise returns **`-EAGAIN`** | Enables non-blocking lookup paths (including `io_uring` `IORING_OP_OPENAT2`) |

**Crucial Defense-in-Depth Invariant in `complete_walk()` (`fs/namei.c:1074-1093`):** Because concurrent `renameat2()` on a directory being walked under `LOOKUP_RCU` could theoretically race with `..` resolution, `complete_walk()` drops out of RCU mode (`try_to_unlazy(nd)`) and executes a final `if (!path_is_under(&nd->path, &nd->root)) return -EXDEV;` check whenever `LOOKUP_IS_SCOPED` (`LOOKUP_BENEATH | LOOKUP_IN_ROOT`) is active. As `fs/namei.c:1087-1089` notes, this guarantees the resolved inode was strictly inside `dfd` at linearization time (though a concurrent privileged/sibling rename *after* `complete_walk` returns can still move the already-opened dentry).

In Rust and Go container infrastructure, `cyphar/libpathrs` (`src/resolvers/openat2.rs:51-94`) composes `RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS` into every `open()` and `resolve()` call (returning an `O_PATH` handle then reopening safely via verified `procfs` handles in `src/procfs.rs`), and `opencontainers/runc` (`internal/pathrs/root_pathrslite.go:35-84`) wraps `pathrs-lite` `OpenatInRoot` with `EAGAIN` retry loops and `O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC` single-component leaf creation so no unverified symlink component is ever traversed from the host context.

#### 4.2 Container Breakout Post-Mortems and Hardened `runc` Invariants (`CVE-2019-5736` & `CVE-2024-21626`)
Basis: source (`opencontainers/runc/libcontainer/container_linux.go:502-528`, `libcontainer/exeseal/cloned_binary_linux.go:39-89`, `libcontainer/init_linux.go:271-368`, `libcontainer/standard_init_linux.go:268-288`, `libcontainer/utils/utils_unix.go:27-128`) + documentation (`CVE-2019-5736`, `CVE-2024-21626`).

1. **`CVE-2019-5736` (`/proc/self/exe` Host-Binary Overwrite):**
   - *Mechanism:* During `runc exec` or container startup with a malicious `#!/proc/self/exe` entrypoint, the container obtained a handle to the running host `runc` executable via `/proc/<runc-init-pid>/exe`. Opening it `O_PATH` and later reopening `O_WRONLY` via `/proc/self/fd/<N>` after `runc init` exited (dropping `ETXTBSY`) overwrote the host's `/usr/bin/runc` binary on disk.
   - *Hardened Mitigation in `runc` (`b7dc1304` @ `libcontainer/container_linux.go:502-528` & `libcontainer/exeseal/cloned_binary_linux.go:39-89`):* Before spawning `runc init`, `runc` checks `exeseal.IsSelfExeCloned()` and otherwise copies its own ELF binary into a fresh anonymous `memfd_create("runc_cloned:...", MFD_ALLOW_SEALING | MFD_CLOEXEC | MFD_EXEC)` (`cloned_binary_linux.go:65-88`), applies `chmod(0511)`, and permanently seals it with `F_SEAL_EXEC` (Linux 6.3+) plus `baseMemfdSeals = F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE` (`cloned_binary_linux.go:39-61`). Note the subtle Linux `6.3–6.6+` interaction documented in `cloned_binary_linux.go:68-85`: under `sysctl vm.memfd_noexec=2`, `memfd_create(..., MFD_EXEC)` returns `-EACCES`, forcing fallback to a less secure unlinked `O_TMPFILE` copy, whereas `-EINVAL` is retried without `MFD_EXEC` for pre-6.3 kernels.
2. **`CVE-2024-21626` ("Leaky Vessels": Host FD Leak -> `/proc/self/fd/<N>` `cwd` Breakout):**
   - *Mechanism:* An internal host file descriptor (e.g., `/sys/fs/cgroup` opened during container setup) remained open (even if marked `O_CLOEXEC`!) during `runc init`'s `finalizeNamespace()` execution *before* `execve()`. Setting OCI `process.cwd` to `/proc/self/fd/<N>` caused `unix.Chdir(config.Cwd)` to traverse the procfs magiclink *before* `execve()` closed `O_CLOEXEC` descriptors, placing the container's working directory directly on the host filesystem (`../../..` then escaped the mount namespace root!).
   - *Hardened Mitigation in `runc` (`b7dc1304` @ `libcontainer/init_linux.go:271-368`, `libcontainer/utils/utils_unix.go:74-128`, `libcontainer/standard_init_linux.go:268-288`):*
     1. `CloseExecFrom(config.PassedFilesCount + 3)` (`init_linux.go:304`, `utils_unix.go:76-90`) marks all higher descriptors `O_CLOEXEC` via `close_range(minFd, MAX, CLOSE_RANGE_CLOEXEC)` (with `/proc/thread-self/fd/` fallback), ensuring no descriptor leaks *across* `execve()`.
     2. `verifyCwd()` (`init_linux.go:273-295, 358`) runs **after** `unix.Chdir(config.Cwd)` and calls `unix.Getwd()`. On Linux, `getcwd(2)` prefixes `"(unreachable)"` whenever `current->fs->pwd` is outside the current mount namespace root, which Go's `unix.Getwd()` / glibc `getcwd(3)` translates to `ENOENT`—catching any `/proc/self/fd/<N>` escape before `execve()`.
     3. Prior to final `execve()`, `UnsafeCloseFrom()` (`utils_unix.go:110-128`) explicitly closes remaining non-stdio FDs while skipping Go's internal netpoll descriptors (`runtime_IsPollDescriptor`, L99/L114), and `standard_init_linux.go:287-288` explicitly closes both `fifoFile` and `l.fifoFile` (`O_PATH` exec FIFO) before `execve()` to avoid `CVE-2016-9962` dumpable-reset races.

### 5. Cross-Layer Sandboxing & Path-Confinement Comparison Matrix
Basis: derived from sections 1–4.

| Mechanism | Enforcement Layer | Inspects Pathnames / Inodes? | Mediates `io_uring` Ops? | Immune to Multi-Thread Pointer TOCTOU? | Blocks Pre-Opened Leaked FDs? | Unprivileged (`NO_NEW_PRIVS`)? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`seccomp-BPF`** | Syscall entry (`seccomp_data` registers) | No (raw pointers only) | **No** (unless banning `io_uring_setup`/`enter`) | Yes (scalars copied into registers) | Only if blocking `read`/`write` globally | Yes |
| **`seccomp_unotify` (`CONTINUE`)** | Userspace supervisor via `process_vm_readv` | Fragile (racy) | **No** | **No** (tracee thread mutates memory before kernel copy) | No | Yes |
| **`seccomp_unotify` (`ADDFD`)** | Supervisor performs op & injects FD | Yes (in supervisor) | **No** | Yes (tracee never executes syscall) | No | Yes |
| **`IORING_REGISTER_RESTRICTIONS`** | `io_uring` submission (`io_init_req`) | No (opcode/flags allowlist only) | Yes (single ring / task) | Yes (checked after `READ_ONCE` into `io_kiocb`) | Can require `IOSQE_FIXED_FILE` | Yes |
| **`io_uring` cBPF Filter (Linux 7.4)** | `io_uring` submission (`io_submit_sqe`) | **No** (`open` flags/resolve, `socket`, `connect` addr/port only) | Yes (per-ring/opcode) | Yes (runs on kernel-copied `io_kiocb` PDU) | No | Yes |
| **`Landlock` LSM (ABI v1–v12)** | Kernel VFS / Net / Task LSM hooks | **Yes** (dentry/inode ancestry + port + scope + ns/cap) | **Yes** (VFS/socket hooks fire inside `io_uring` workers) | **Yes** (enforced on kernel dentry after VFS resolution) | **No** (blocks `/proc/self/fd` re-open, not `pread`/`write` on live FD) | Yes |
| **`openat2(2)` (`RESOLVE_*`)** | Kernel VFS `namei` path walk | **Yes** (confined beneath `dfd` + `complete_walk` `path_is_under`) | **Yes** (`IORING_OP_OPENAT2` uses same `do_sys_openat2` path) | **Yes** (atomic kernel walk + `RESOLVE_NO_MAGICLINKS`) | N/A (governs path resolution, not existing FDs) | Yes |

## Boundaries

- **`known not to apply` — Landlock Uncovered VFS Metadata Syscalls:** Per `torvalds/linux/include/uapi/linux/landlock.h:494-499`, `Landlock` up through ABI v12 explicitly cannot restrict `chdir(2)`, `stat(2)`, `flock(2)`, `chmod(2)`, `chown(2)`, `setxattr(2)`, `utime(2)`, `fcntl(2)`, or `access(2)`. Sandboxes requiring metadata confidentiality or `chmod`/`chown` isolation must layer `seccomp-BPF`, mount/user namespaces, or SELinux/AppArmor.
- **`known not to apply` — Landlock Does Not Revoke Inherited FDs:** Empirically confirmed by Execution Probe 1 (`## Evidence`): `pread(outfd, ...)` on a descriptor opened prior to `landlock_restrict_self(2)` still succeeds. Descriptor scrubbing (`close_range` / `O_CLOEXEC`) remains mandatory.
- **`known not to apply` — Linux `7.4` `io_uring` cBPF Filters and Landlock ABI v10–v12 on Older Kernels:** Live execution verified Linux `7.1.6` (Landlock ABI v9, no `io_uring` cBPF filter); ABI v10 UDP rules, ABI v12 namespace/capability rules, and `IORING_REGISTER_BPF_FILTER` were inspected in `torvalds/linux` `7.4.0-rc3` source and are **`unsupported`** on Linux `<= 7.1` kernels.
- **`not examined` — `IORING_OP_URING_CMD` / `DMA-BUF` Registered Buffers / `IORING_SETUP_IOPOLL`:** Device-specific passthrough commands (`NVMe` `uring_cmd`), `IO_REGBUF_TYPE_DMABUF` (`io_uring/rsrc.c:967-968`), and `IORING_SETUP_SQPOLL` credential override hooks (`security_uring_override_creds`, `io_uring/io_uring.c:1989`) were not executed in live probes.
- **`not examined` — `SECCOMP_RET_USER_NOTIF` `ADDFD` Throughput & `ptrace` Tracer Races:** Empirical latency and tracee-interrupt edge cases of `seccomp_unotify` supervisor injection were outside scope.
- **`unknown` — Real-World Compiler Codegen for `sqe->ioprio` Plain Read (`io_uring/io_uring.c:1960`):** Whether GCC/Clang under `-O2` ever emits a duplicate load of `sqe->ioprio` across inlined call paths in `io_init_req()` + `def->prep()` was not checked via disassembly across target architectures; the finding establishes the source-level omission of `READ_ONCE()` relative to `io_get_sqe()`'s documented invariant (`io_uring.c:2141-2143`).

## Evidence

### Primary Source Citations

| Subject | Immutable Commit / ID | File Path & Symbol / Lines | Verified Finding |
| :--- | :--- | :--- | :--- |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`7.4.0-rc3`) | `io_uring/io_uring.c:7-28,1875-2230` (`io_init_req`, `io_submit_fail_init`, `io_submit_sqe`, `io_commit_sqring`, `io_get_sqe`, `io_submit_sqes`) | SQ/CQ barrier contract; live user-mapped `*sqe = &ctx->sq_sqes[head]`; `READ_ONCE` snapshots vs plain `sqe->ioprio` at L1960; `IORING_SETUP_SQE_MIXED` boundary check L1901–1927; link failure propagation L2000–2035 |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `io_uring/memmap.c:55-95` (`io_pin_pages`); `io_uring/rsrc.c:380-384,720-723,947-1051` (`io_sqe_buffer_register`) | `pin_user_pages_fast(..., FOLL_WRITE \| FOLL_LONGTERM, ...)`; `io_is_uring_fops(file)` -> `-EBADF` nested-ring exclusion |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `io_uring/register.c:130-165,201-205`; `include/uapi/linux/io_uring/bpf_filter.h:13-82`; `io_uring/bpf_filter.c:26-194` | `IORING_RESTRICTION_*` masks; Linux 7.4 `struct io_uring_bpf_ctx` (`socket`, `open`, `connect` PDUs, no pathnames) |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `net/unix/garbage.c:77-140,322-440` (`unix_vertex`, `unix_peek_seq`, `unix_vertex_dead`, `unix_scc_dead`) | Tarjan SCC graph GC requiring `total_ref == vertex->out_degree` and `read_seqcount_retry(&unix_peek_seq, seq)` |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `include/uapi/linux/seccomp.h:40-85`; `kernel/seccomp.c:67-79,280-294` (`seccomp_check_filter`) | 64-byte scalar `struct seccomp_data`; `BPF_LD\|BPF_W\|BPF_ABS` strict offset bounds |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `include/uapi/linux/landlock.h:25-103,383-632`; `security/landlock/syscalls.c:194,230,661,704-715`; `security/landlock/fs.c:755-1050,1277-1285` | `landlock_abi_version = 12`; `REFER` default-deny; `is_access_to_paths_allowed`; ABI v10 UDP & v12 namespace/capability permissions; uncovered syscall warning L494–499 |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `include/uapi/linux/openat2.h:1-50`; `fs/open.c:1208-1450`; `fs/namei.c:1056-1093,1138-1182,2046-2049,2192-2231,2724-2728` | `LOOKUP_BENEATH`/`IN_ROOT`/`NO_SYMLINKS`/`NO_MAGICLINKS`; `complete_walk()` `path_is_under(&nd->path, &nd->root)` -> `-EXDEV` |
| `axboe/liburing` | `a10946dc51eeababc48ee10baf0d17489f647a80` | `src/queue.c:13-37,247-278`; `src/include/liburing/barrier.h:28-40` | Non-SQPOLL plain tail write vs SQPOLL `io_uring_smp_store_release` + `io_uring_smp_mb()` before `IORING_SQ_NEED_WAKEUP` |
| `seccomp/libseccomp` | `2814474a2bc105f5ffabf4bbc7ae9fb100997028` | `src/gen_bpf.c:113-116,839,2010` | BPF emission exclusively over `offsetof(struct seccomp_data, ...)` |
| `landlock-lsm/rust-landlock` | `5991c08320d2ade23db0ae3870709693fd5a213d` (`0.4.7`) | `src/compat.rs:51-82` (`ABI::V1`–`V9`); `src/ruleset.rs:101-155` | ABI version enum, `CompatLevel::BestEffort` vs `HardRequirement`, `RulesetStatus` |
| `opencontainers/runc` | `b7dc1304ed9e18f14e626dc06374043b12cf355f` | `libcontainer/container_linux.go:502-528`; `libcontainer/exeseal/cloned_binary_linux.go:39-89`; `libcontainer/init_linux.go:271-368`; `libcontainer/utils/utils_unix.go:27-128`; `internal/pathrs/root_pathrslite.go:35-84` | `exeseal.CloneSelfExe` sealed `memfd` (`CVE-2019-5736`); `CloseExecFrom`, `UnsafeCloseFrom`, `verifyCwd()` (`CVE-2024-21626`); `pathrs.OpenatInRoot` |
| `cyphar/libpathrs` | `05a4b54f9843ea1fb0ae86dc2f40550bde244589` | `src/resolvers/openat2.rs:51-94` | `RESOLVE_IN_ROOT \| RESOLVE_NO_MAGICLINKS` root-confined path resolution |

### Execution Evidence (`2026-11-19`, Linux `7.1.6` x86_64, GCC `-O2`, Python 3)

1. **Execution Probe 1 — Live `openat2(2)` `RESOLVE_*` & `Landlock` Confinement:** Compiled with `gcc -O2` against `<linux/openat2.h>` and `<linux/landlock.h>`. Created `/tmp/probe_jail/inside.txt` (`"INSIDE_JAIL"`), `/tmp/outside_secret.txt` (`"HOST_SECRET"`), symlinks `link_escape -> ../outside_secret.txt`, `link_abs_inside -> /inside.txt`, and `link_rel_inside -> inside.txt`, opened `rootfd` on `/tmp/probe_jail` and `outfd` on `/tmp/outside_secret.txt`, queried `SYS_openat2` across `RESOLVE_BENEATH`, `RESOLVE_IN_ROOT`, `RESOLVE_NO_SYMLINKS`, and `RESOLVE_NO_MAGICLINKS`, queried `SYS_io_uring_setup(8)`, and in a forked child enforced a `LANDLOCK_RULE_PATH_BENEATH` read-only ruleset on `rootfd` after `prctl(PR_SET_NO_NEW_PRIVS, 1)`:
   ```text
   === 1. openat2(2) RESOLVE_* semantics ===
   openat2 BENEATH inside.txt                     -> OK (fd=7, content='INSIDE_JAIL')
   openat2 BENEATH ../outside_secret.txt          -> ERR errno=18 (Invalid cross-device link)
   openat2 BENEATH /etc/hostname                  -> ERR errno=18 (Invalid cross-device link)
   openat2 BENEATH link_escape                    -> ERR errno=18 (Invalid cross-device link)
   openat2 IN_ROOT /inside.txt                    -> OK (fd=7, content='INSIDE_JAIL')
   openat2 IN_ROOT ../../inside.txt               -> OK (fd=7, content='INSIDE_JAIL')
   openat2 IN_ROOT link_abs_inside (/inside.txt)  -> OK (fd=7, content='INSIDE_JAIL')
   openat2 IN_ROOT link_escape (../outside)       -> ERR errno=2 (No such file or directory)
   openat2 BENEATH|NO_SYMLINKS link_rel_inside    -> ERR errno=40 (Too many levels of symbolic links)
   openat2 NO_MAGICLINKS /proc/self/fd/<outfd>    -> ERR errno=40 (Too many levels of symbolic links)
   openat2 plain /proc/self/fd/<outfd>            -> OK (fd=7, content='HOST_SECRET')

   === 2. io_uring_setup(2) probe ===
   io_uring_setup(8) -> OK fd=7 sq=8 cq=16 features=0x3ffff

   === 3. Landlock LSM live ABI & confinement probe ===
   landlock_abi_version = 9 (errno=0)
   Landlock child open(jail/inside.txt, O_RDONLY) -> OK (errno=0)
   Landlock child open(jail/inside.txt, O_WRONLY) -> ERR (errno=13 Permission denied)
   Landlock child open(outside_secret.txt, O_RDONLY) -> ERR (errno=13 Permission denied)
   Landlock child open(/proc/self/fd/<pre-opened outside>, O_RDONLY) -> ERR (errno=13 Permission denied)
   Landlock child pread(pre-opened outfd) -> 11 bytes ('HOST_SECRET')
   ```

2. **Execution Probe 2 — Live `io_uring` vs. `seccomp-BPF` vs. `Landlock` and `FOLL_LONGTERM` `munmap(2)`:** Compiled with `gcc -O2` against `<linux/io_uring.h>`, `<linux/seccomp.h>`, and `<linux/landlock.h>`, spawning three isolated children each initialized with an 8-entry `io_uring`:
   - `Child A` installed a cBPF `SECCOMP_SET_MODE_FILTER` returning `SECCOMP_RET_ERRNO | EPERM` for `SYS_open`, `SYS_openat`, and `SYS_openat2`, then attempted both `openat()` and `IORING_OP_OPENAT` on `/tmp/outside_secret.txt`.
   - `Child B` enforced a `Landlock` read-only `LANDLOCK_RULE_PATH_BENEATH` ruleset on `rootfd`, then submitted `IORING_OP_OPENAT` against `jail/inside.txt` (`O_RDONLY`, `O_WRONLY`) and `outside_secret.txt` (`O_RDONLY`).
   - `Child C` mapped 4 KiB anonymously, registered it via `IORING_REGISTER_BUFFERS`, called `munmap(buf, 4096)`, and submitted `IORING_OP_READ_FIXED` (`buf_index = 0`) targeting the unmapped address.
   ```text
   [Child A: seccomp-BPF blocking open/openat/openat2]
     direct openat(outside)          -> -1 (errno=1 Operation not permitted)
     io_uring IORING_OP_OPENAT(out)  -> fd=7 (BYPASS! content='HOST_SECRET')
   [Child B: Landlock LSM restricting FS to jail/ RO]
     io_uring IORING_OP_OPENAT(jail/inside, RO) -> fd=7 (content='INSIDE_JAIL')
     io_uring IORING_OP_OPENAT(outside, RO)     -> res=-13 (Permission denied)
     io_uring IORING_OP_OPENAT(jail/inside, WO) -> res=-13 (Permission denied)
   [Child C: IORING_REGISTER_BUFFERS FOLL_LONGTERM vs munmap(2)]
     register=0 munmap=0 IORING_OP_READ_FIXED_after_munmap=12 bytes
   ```

3. **Execution Probe 3 — SQE Double-Fetch and Tarjan SCC `unix_gc` Formal Model:** Executed in Python 3, exhaustively checking the 3 schedule positions of a concurrent userspace SQE mutation relative to kernel validation and use (with and without `READ_ONCE` snapshotting), and evaluating `net/unix/garbage.c:338-395`'s exact Tarjan SCC deadness predicate (`total_ref == vertex->out_degree` and no external SCC/non-inflight outgoing edge) over a closed `S1 <-> S2` `AF_UNIX` cycle under three reference-count configurations:
   ```text
   === 1. SQE Double-Fetch Interleaving Probe ===
     use_READ_ONCE_snapshot=False: schedules=3 invalid_value_reached_prep=1
     use_READ_ONCE_snapshot=True : schedules=3 invalid_value_reached_prep=0

   === 2. Tarjan SCC unix_gc vs io_uring Fixed-File Reference Cycle Probe ===
     Case A (closed pure AF_UNIX cycle S1<->S2): dead_sccs=[['S1', 'S2']]
     Case B (AF_UNIX cycle + live io_uring fixed-file ref on S1): dead_sccs=[]
     Case C (CVE-2022-2602 race: undercounted ref while io_uring holds dangling ptr): premature_reclaim=[['S1', 'S2']]
   ```

## Revalidation

To cheaply test whether these invariants still hold on a newer Linux kernel, `liburing`, `rust-landlock`, or `runc` release:

1. **Kernel `io_uring` SQE & Buffer Pinning Diff:** Diff `io_uring/io_uring.c` (`io_get_sqe`, `io_init_req`), `io_uring/memmap.c` (`io_pin_pages`), `io_uring/rsrc.c` (`io_is_uring_fops`), and `io_uring/bpf_filter.c` (`struct io_uring_bpf_ctx`) against commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to check whether the kernel snapshots full SQEs into kernel memory, relaxes nested-ring registration, or extends `io_uring_bpf_ctx` to pathname/VFS mediation.
2. **Landlock ABI & Syscall Coverage Probe:** Run `landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION)` on the target kernel and diff `include/uapi/linux/landlock.h` (specifically the uncovered-syscalls comment block around L494–499 and `security/landlock/syscalls.c:landlock_abi_version`) plus `landlock-lsm/rust-landlock/src/compat.rs` (`enum ABI`) to check newly mediated operations (`stat`, `chmod`, `fcntl`, etc.).
3. **Live Bypass & Confinement Regression Check:** Compile and execute a forked three-child C probe (modeled on `Child A` / `Child B` / `Child C` above) testing: (a) `seccomp-BPF` blocking `SYS_openat`/`SYS_openat2` vs. `IORING_OP_OPENAT`, (b) `Landlock` `LANDLOCK_RULE_PATH_BENEATH` vs. `IORING_OP_OPENAT` and pre-opened FD `pread()`, (c) `IORING_REGISTER_BUFFERS` + `munmap(2)` + `IORING_OP_READ_FIXED`, and (d) `openat2(2)` `RESOLVE_BENEATH` / `RESOLVE_IN_ROOT` / `RESOLVE_NO_MAGICLINKS`.
4. **Container Runtime Breakout Guards:** Diff `opencontainers/runc` `libcontainer/exeseal/cloned_binary_linux.go` (`baseMemfdSeals`, `MFD_EXEC`), `libcontainer/init_linux.go` (`verifyCwd`, `finalizeNamespace`), and `libcontainer/utils/utils_unix.go` (`CloseExecFrom`, `UnsafeCloseFrom`) to verify that no newly introduced host file descriptors bypass `O_CLOEXEC` or `verifyCwd()` prior to container `execve()`.
