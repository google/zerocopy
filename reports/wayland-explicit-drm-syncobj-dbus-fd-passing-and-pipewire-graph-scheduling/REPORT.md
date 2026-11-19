# Wayland Object-ID Lifetimes and Explicit DRM Syncobj Timelines, Lock-Free PipeWire SPA Media Scheduling, and D-Bus SCM_RIGHTS / memfd / pidfd Isolation

## Summary

Modern Linux desktop, compositor, and media pipelines achieve zero-copy data movement across mutually untrusted sandbox boundaries by passing kernel capability descriptors (`DMA-BUF`, `drm_syncobj`, `memfd`, `eventfd`, `pidfd`) over `AF_UNIX` sockets via `SCM_RIGHTS`. Composing Wayland (`Smithay/smithay`, `Smithay/wayland-rs`), PipeWire (`PipeWire/pipewire`), and D-Bus / XDG Portals (`dbus2/zbus`, `bus1/dbus-broker`, `flatpak/xdg-desktop-portal`) over Linux kernel primitives (`drm_syncobj.c`, `af_unix.c`, `garbage.c`, `memfd.c`) exposes four critical correctness and security invariants:

1. **Wayland Asynchronous Object-ID Partitioning, Zombie Lifetimes, and `linux-drm-syncobj-v1` Timeline Hazards:** Wayland splits 32-bit object IDs at `SERVER_ID_LIMIT = 0xFF00_0000` (`wayland-backend/src/rs/map.rs:8`). Because client destructor requests race in-flight server events on `AF_UNIX` streams, reusing a client ID `< 0xFF00_0000` before receiving `wl_display.delete_id` misparses incoming event opcodes and desynchronizes `SCM_RIGHTS` descriptor queues (`Zombie` state in `wayland-backend`). For GPU synchronization, `linux-drm-syncobj-v1` replaces global buffer-inode `dma_resv` implicit fencing with per-commit 64-bit `dma_fence_chain` acquire/release points (`Smithay/smithay` `src/wayland/drm_syncobj/`). Primary-source inspection reveals two subtle compositor hazards: (a) Linux `drm_syncobj_fd_to_handle` (`drm_syncobj.c:727-738`) allocates a fresh IDR handle on every import without deduplicating underlying `struct drm_syncobj` pointers, while Smithay's `DrmTimeline::eq` (`sync_point.rs:90-94`) checks `Arc::ptr_eq`, allowing a client that imports `dup()`d FDs of the same timeline twice to bypass `Error::ConflictingPoints` (`release.point <= acquire.point` at `mod.rs:260`); and (b) unsubmitted or never-signaled client acquire points must be gated behind non-blocking per-surface `DRM_IOCTL_SYNCOBJ_EVENTFD` (`DrmSyncPointBlocker`), never synchronous `Fence::wait` (`wait(i64::MAX)`, `sync_point.rs:286`).
2. **Lock-Free Real-Time `PipeWire` `SPA` Wakeup Chains and Shared-Memory Ring-Buffer Bounds:** PipeWire drives real-time audio/video DAGs without daemon round-trips by mapping `struct pw_node_activation` (`MemFd`) across peers and chaining direct peer-to-peer `eventfd` writes when atomic dependency counters hit zero (`SPA_ATOMIC_DEC(state->pending) == 0` + `SPA_ATOMIC_CAS(a->status, NOT_TRIGGERED, TRIGGERED)` in `private.h:642-668`). Mixing slow `DMA-BUF` screen-cast compositing with sub-millisecond audio requires `PW_NODE_ACTIVATION_FLAG_ASYNC` decoupling so graphics stalls cannot hold audio driver `pending` counts above zero (`XRun`). In `spa_ringbuffer` (`spa/include/spa/utils/ringbuffer.h:78-165`), `readindex` and `writeindex` wrap modulo $2^{32}$, requiring **power-of-two buffer sizes** (a non-power-of-two size such as `48000` jumps backward from offset `23295` to `0` on `0xffffffff -> 0` wrap) and **explicit caller modulo masking `offset = index % size`** before `spa_ringbuffer_read_data` / `write_data` (where unmasked `offset > size` underflows unsigned `uint32_t l0 = SPA_MIN(len, size - offset)` into an out-of-bounds `memcpy`).
3. **The `F_SEAL_FUTURE_WRITE` vs. `F_SEAL_WRITE` Zero-Copy `memfd` TOCTOU Trap:** Passing a `memfd` over `SCM_RIGHTS` without verifying `fcntl(fd, F_GET_SEALS)` exposes receivers to `ftruncate()`-induced **`SIGBUS`** crashes (mitigated by `F_SEAL_SHRINK`) and concurrent payload mutation. Crucially, Linux `mm/memfd.c:249-259` enforces `mapping_deny_writable` and `memfd_wait_for_pins` (`-EBUSY` if any writable `MAP_SHARED` VMA or DMA `get_user_pages` pin exists) **only for `F_SEAL_WRITE` (`0x0008`), NOT for `F_SEAL_FUTURE_WRITE` (`0x0010`)**. Live kernel execution confirms that a sender mapping a `memfd` `MAP_SHARED | PROT_READ | PROT_WRITE` *before* applying `F_SEAL_FUTURE_WRITE | F_SEAL_SHRINK | F_SEAL_GROW` retains full live write access afterward (`b'INIT' -> b'PWN!'`), defeating zero-copy parser validation unless receivers strictly require `F_SEAL_WRITE` (or copy payloads once into private memory before validation).
4. **`SCM_RIGHTS` Descriptor Accounting, Cyclic Socket Garbage Collection, and `SO_PEERPIDFD` Authorization:** Linux caps single-`sendmsg` ancillary arrays at `SCM_MAX_FD = 253` (`EINVAL` at `254`) and per-UID inflight descriptors at `RLIMIT_NOFILE` (`too_many_unix_fds`, `-ETOOMANYREFS`), using Tarjan's SCC algorithm (`net/unix/garbage.c:396-509`) to reclaim closed `AF_UNIX` sockets trapped inside cyclic `SCM_RIGHTS` queues. Because a D-Bus broker runs under its own service UID, `dbus-broker` enforces per-client-UID `USER_SLOT_FDS` quotas (`src/dbus/socket.c:131-137, 672-685`) to prevent cross-tenant FD-table exhaustion. Finally, `dbus-broker`, `zbus` (`ConnectionCredentials::process_fd`), and `xdg-desktop-portal` (`xdp-app-info.c`) bind peer identity at `connect()` time via `SO_PEERPIDFD` (`"ProcessFD"`), eliminating both PID-wraparound TOCTOU authorization races and cross-PID-namespace `ucred.pid == 0` ambiguity.

## Applicability

This report characterizes the coupled protocol, kernel-ABI, and shared-memory safety contracts across eight pinned subjects:

- **Wayland Protocol & Compositor Explicit Sync Stack:**
  - `Smithay/wayland-rs` at `6d60c31e1386c6c954e2037b0a8cb368043ca63e` (`wayland-backend/src/rs/map.rs`, `wayland-backend/src/rs/server_impl/client.rs`, `wayland-backend/src/rs/client_impl/mod.rs`) and `Smithay/smithay` at `7ff0ede4df2af1ce3500da9ef1ee190d48b49103` (`src/wayland/drm_syncobj/mod.rs`, `src/wayland/drm_syncobj/sync_point.rs`), implementing staging protocol `linux-drm-syncobj-v1` (`wp_linux_drm_syncobj_manager_v1`, version 1).
- **Real-Time Shared-Memory Media Graph Engine:**
  - `PipeWire/pipewire` at `89f53e32acc5b711e3eb089e5a42f4292393aabe` (`spa/include/spa/utils/ringbuffer.h`, `src/pipewire/private.h`, `src/pipewire/impl-node.c`), governing `PW_VERSION_NODE_ACTIVATION = 1` real-time scheduling and `SPA_DATA_MemFd` / `SPA_DATA_DmaBuf` transport.
- **D-Bus Descriptor Passing and Sandboxed Desktop Portal Stack:**
  - `dbus2/zbus` at `615620ad61bd286460a861d50c71e0fcece59e70` (`zbus/src/runtime/io/unix.rs`, `zbus/src/fdo/dbus.rs`), `bus1/dbus-broker` at `2956b5d381deeea709c53d02f10e799e50e44f4b` (`src/util/sockopt.c`, `src/util/fdlist.c`, `src/dbus/socket.c`), and `flatpak/xdg-desktop-portal` at `c00a32b7a3d136d7e86e8beb494867eb0babe9a5` (`shared/xdp-app-info.c`).
- **Underlying Linux Kernel Subsystems:**
  - Source inspection against `torvalds/linux` `v6.12` (`adc218676eef25575469234709c2d87185ca223a`: `drivers/gpu/drm/drm_syncobj.c`, `net/unix/af_unix.c`, `net/unix/garbage.c`, `mm/memfd.c`) paired with live user-space syscall execution on Linux `7.1.6` (`x86_64`). Note kernel version thresholds documented in `zbus` (`unix.rs:288-295`) and `dbus-broker` (`sockopt.c:126-153`): `DRM_IOCTL_SYNCOBJ_EVENTFD` requires Linux $\ge 6.6$ (or backport), `SO_PEERPIDFD` requires Linux $\ge 6.5` (`ENOPROTOOPT` on older kernels), and `SO_PEERPIDFD` on already-reaped peers returns `EINVAL`/`ESRCH` on Linux $< 6.16$.

## Findings

### 1. Wayland Object-ID Lifetimes and Explicit GPU Timeline Synchronization (`linux-drm-syncobj-v1`)

`Basis: normative + source + derived`

#### 1.1 Asynchronous Object-ID Reuse Races and the `wl_display.delete_id` Zombie Protocol

Wayland's wire framing encodes every message header as `(sender_id: u32, (size: u16 << 16) | opcode: u16)` without self-describing wire types; both peers decode payload words—and **pop ancillary `SCM_RIGHTS` file descriptors from a FIFO per-connection FD queue**—solely by looking up `(sender_id, opcode)` in a local `ObjectMap` (`wayland-backend/src/rs/client_impl/mod.rs:666-670`).

1. **Split Namespace Invariant (`wayland-backend/src/rs/map.rs:8, 67-85`):** To allow lock-free concurrent object creation without round-trip ID allocation, IDs are partitioned at `SERVER_ID_LIMIT = 0xFF00_0000`:
   - Client-allocated IDs occupy `[1, 0xFEFF_FFFF]` (`1` is permanently `wl_display`; `0` is null).
   - Server-allocated IDs occupy `[0xFF00_0000, 0xFFFF_FFFF]` (e.g., `wl_data_offer`).
   - `insert_in_at` (`map.rs:139-158`) enforces compact dense allocation: requesting any `id > store.len()` or colliding with a non-`None` slot is a fatal protocol error.
2. **Why Immediate Client ID Reuse Corrupts `SCM_RIGHTS` Framing:** When a client emits a destructor request on ID $x < \mathtt{0xFF00\_0000}$, the compositor may have already queued events targeting $x$ in the `AF_UNIX` stream prior to reading the destructor. If the client immediately freed slot $x$ and allocated a new object $x'$ of a different interface at the same numeric ID $x$, in-flight events for old $x$ would be decoded using $x'$'s event signature table—misinterpreting integer arguments as `fd` arguments (or vice versa) and **shifting every subsequent file descriptor attached to the Wayland connection across unrelated protocol objects**.
   - **Two-Phase Zombie Reclamation (`client_impl/mod.rs:635-651`, `server_impl/client.rs:214-233`):** Upon sending a client destructor, `wayland-backend` marks `obj.data.client_destroyed = true` (`Zombie` state: incoming events are parsed using the *original* `Interface` signature so the exact number of `SCM_RIGHTS` FDs are consumed and closed, then discarded). Only when the compositor processes the destructor and emits `wl_display.delete_id(x)` (`sender_id = 1, opcode = 1`, gated by `if object_id.id < SERVER_ID_LIMIT` at `server_impl/client.rs:226`) does the client set `server_destroyed = true` and call `self.map.remove(id)` (`client_impl/mod.rs:645-647`), releasing numeric slot $x$ for reuse. Server-side Rust handles additionally carry a monotonic `serial: u32` (`server_impl/client.rs:250`) so stale `InnerObjectId` wrappers reject ABA generation mismatches with `InvalidId`.

#### 1.2 Explicit Timeline Synchronization (`linux-drm-syncobj-v1`) vs. Implicit DMA-BUF Fencing

Under legacy Wayland `zwp_linux_dmabuf_v1` implicit synchronization, GPU readiness is attached globally to `struct dma_buf`'s kernel `dma_resv` object rather than to a specific Wayland surface commit. When Vulkan/EGL clients pipeline frames or share `DMA-BUF`s across asynchronous compute/compositor queues, implicit fencing causes visual tearing (if a driver omits implicit `dma_resv` writes, as historically occurred on proprietary Vulkan drivers) or false write-after-read stalls across unrelated readers.

`linux-drm-syncobj-v1` (`Smithay/smithay` `src/wayland/drm_syncobj/mod.rs` and `sync_point.rs`) decouples buffer memory from synchronization via timeline `drm_syncobj` (`dma_fence_chain`) file descriptors:

1. **Capability Gate (`supports_syncobj_eventfd`, `mod.rs:71-78`):** Smithay probes kernel `DRM_IOCTL_SYNCOBJ_EVENTFD` support at startup by invoking `drm_ffi::syncobj::eventfd(dev, 0, 0, dev, false)` with invalid handle `0`; kernels implementing `drm_syncobj_eventfd_ioctl` (`drivers/gpu/drm/drm_syncobj.c:1460-1480`) pass feature/flag checks and return `ENOENT` (`ErrorKind::NotFound`) on `drm_syncobj_find(file_private, 0)`, whereas older kernels return `EINVAL`/`ENOTTY`/`EOPNOTSUPP`.
2. **Double-Buffered Surface Commit Validation (`commit_hook`, `mod.rs:227-281, 424-477`):** Clients import a timeline FD (`import_timeline`) and attach 64-bit points encoded as `(point_hi: u32, point_lo: u32)` $\mapsto$ `((point_hi as u64) << 32) + (point_lo as u64)` (`mod.rs:443, 470`). Before `wl_surface.commit` applies pending state, `commit_hook` enforces five protocol errors on `wp_linux_drm_syncobj_surface_v1`:
   - `Error::NoBuffer`: `acquire_point` set without attaching a `NewBuffer`.
   - `Error::NoReleasePoint` / `Error::NoAcquirePoint`: only one of `acquire_point` or `release_point` was set in the commit.
   - `Error::ConflictingPoints`: `acquire.timeline == release.timeline && release.point <= acquire.point` (`mod.rs:260`).
   - `Error::UnsupportedBuffer`: sync points attached to a non-`DMA-BUF` (e.g., `wl_shm`) buffer (`get_dmabuf(buffer).is_err()`, `mod.rs:270`).
   - **Superseded Commit Release Invariant (`merge_into`, `mod.rs:109-119`):** If a client commits a newer buffer+points while a previous committed state `into` has not yet been latched by the renderer, `merge_into` immediately calls `release_point.signal()` on the overwritten `into.release_point` (`lines 111-115`), preventing client swapchain starvation; `destruction_hook` (`mod.rs:283-297`) similarly signals both pending and current `release_point`s on `wl_surface` destruction.
3. **Two Critical Kernel/Compositor Boundary Hazards:**
   - **Duplicate-FD Timeline Aliasing Bypasses `ConflictingPoints` (`drm_syncobj.c:711-744` + `sync_point.rs:90-94`):** Unlike GEM PRIME buffer imports (`drm_gem_prime_fd_to_handle`), which deduplicate handles per `(drm_file, dma_buf)`, Linux's `drm_syncobj_fd_to_handle` (`drivers/gpu/drm/drm_syncobj.c:727-738`) unconditionally executes `idr_alloc(&file_private->syncobj_idr, syncobj, 1, 0, GFP_NOWAIT)`, creating a **distinct IDR handle** referencing the **exact same kernel `struct drm_syncobj`** on every `import_timeline` call. Because Smithay implements `PartialEq for DrmTimeline` via `Arc::ptr_eq(&self.0, &other.0)` (`sync_point.rs:90-94`), a client that calls `import_timeline` twice with `dup()`d FDs of the same `drm_syncobj` obtains two `DrmTimeline` wrappers with `t1 != t2`, **bypassing `acquire.timeline == release.timeline` in `mod.rs:260`** even when `release.point <= acquire.point` on the same kernel timeline! Comparing `(fstat(fd).st_dev, fstat(fd).st_ino)` or `kcmp(pid, pid, KCMP_FILE, fd1, fd2)` at `import_timeline` closes this alias bypass (`Basis: source + derived`).
   - **Unsubmitted / Unsignaled Client Acquire Points (`drm_syncobj.c:1429-1456` + `sync_point.rs:140-155, 263-287`):** Under `linux-drm-syncobj-v1`, a client may legally commit `acquire_point = P` *before* submitting the GPU command buffer that materializes a `dma_fence` at `P`. In `drm_syncobj_eventfd_ioctl` (`flags = 0`, i.e., without `DRM_SYNCOBJ_WAIT_FLAGS_WAIT_AVAILABLE`), `dma_fence_chain_find_seqno(&fence, entry->point)` (`drm_syncobj.c:1429-1433`) leaves `entry` queued on `syncobj->ev_fd_list` until point `P` is both materialized and signaled. Smithay isolates untrusted clients by converting `acquire_point` into an asynchronous `calloop` `DrmSyncPointBlocker` (`BlockerState::Pending`, `sync_point.rs:263-274, 349-356`), stalling *only* that client's surface transaction while compositing all other windows at full refresh rate—whereas invoking `Fence::wait` (`self.wait(i64::MAX)`, `sync_point.rs:285-287`) on a malicious never-signaled client timeline freezes the compositor thread indefinitely. Note also `import_sync_file` (`sync_point.rs:219-257`), which works around a `drm`-crate bug (passing `handle = 0` to `IMPORT_SYNC_FILE` yields `ENOENT` in `drm_syncobj.c:755-759`) by allocating a temporary binary `syncobj`, importing the compositor's `VK_EXTERNAL_SEMAPHORE_HANDLE_TYPE_SYNC_FD_BIT` fence at point 0, transferring it to `self.point`, and destroying the temporary handle.

---

### 2. Lock-Free Real-Time `PipeWire` `SPA` Media Graphs and Ring-Buffer Safety

`Basis: source + execution + derived`

#### 2.1 Zero-Allocation `eventfd` Activation DAG and Dynamic Quantum Decoupling

PipeWire schedules real-time audio and video processing graphs across sandboxed client processes without routing per-quantum IPC through the central `pipewire` daemon (`src/pipewire/private.h:502-689`, `src/pipewire/impl-node.c:1395-1521`):

1. **Shared-Memory Activation State Machine (`struct pw_node_activation`, `private.h:551-668`):** Each node shares a `MemFd`-backed `pw_node_activation` page containing an atomic `status` (`NOT_TRIGGERED = 0`, `TRIGGERED = 1`, `AWAKE = 2`, `FINISHED = 3`, `INACTIVE = 4`) and `state[0]` (`required: int32_t`, `pending: int32_t`). At the start of a graph cycle (driven by an ALSA hardware `timerfd`/IRQ or clock node), the driver resets every active follower's `state->pending = state->required` (`pw_node_activation_state_reset`, `private.h:508-511`) and sets `status = NOT_TRIGGERED`.
2. **Wait-Free Peer-to-Peer Handoff (`trigger_target_v1`, `private.h:642-668`):** Each node holds direct `SCM_RIGHTS`-duplicated `eventfd` descriptors (`t->fd`) for its immediate downstream targets. Upon completing `spa_node_process()`, a producer iterates its `rt.target_list` without locks or heap allocations:
   ```c
   int32_t pending = SPA_ATOMIC_DEC(state->pending);
   if (pending == 0) {
       if (SPA_ATOMIC_CAS(a->status, PW_NODE_ACTIVATION_NOT_TRIGGERED,
                          PW_NODE_ACTIVATION_TRIGGERED)) {
           a->signal_time = nsec;
           spa_system_eventfd_write(t->system, t->fd, 1);
       }
   }
   ```
   Only the **exact final upstream dependency** (`pending == 0`) performs the `CAS` and writes `1` (`8` bytes) to `t->fd`, waking the downstream RT thread directly in kernel `epoll`.
3. **Isolating Real-Time Audio Quanta from `DMA-BUF` Screen-Cast Stalls (`impl-node.c:262-277, 1311-1335, 1449-1465`):** Audio nodes dynamically negotiate power-of-two sample quanta (`quantum = 32..1024` frames at `48 kHz`, i.e., `667 µs` deadlines) via lock-free `position->clock.target_duration` updates (`impl-node.c:835, 1311-1332`) without reallocating `SPA` buffers. If a Wayland compositor exporting `SPA_DATA_DmaBuf` screen-cast frames were scheduled synchronously as a `required` dependency of an audio-driven graph, any GPU fence wait or client crash would leave `state->pending > 0` (`xrun stuck`, `impl-node.c:1449-1465`) and starve audio output. PipeWire prevents cross-domain XRuns via: (a) partitioning independent driver subgraphs (`driver_id`), (b) `PW_NODE_ACTIVATION_FLAG_ASYNC` (`private.h:607`), which decouples asynchronous video/screen-cast consumers across cycle boundaries without contributing to synchronous `state->required`, and (c) server-side `deactivate_target` cleanup (`impl-node.c:262-276`), which marks dead remote clients `FINISHED` and decrements downstream `pending` counts so crashed peers cannot wedge live audio followers.

#### 2.2 `spa_ringbuffer` Shared-Memory Invariants Against Untrusted Peers

`spa/include/spa/utils/ringbuffer.h:39-165` implements a single-producer/single-consumer ring header (`uint32_t readindex; uint32_t writeindex;`) frequently placed inside `SPA_DATA_MemFd` memory shared with untrusted clients:

- **Acquire/Release Memory Ordering (`ringbuffer.h:78-82, 112-115, 128-132, 162-165`):** Consumers load their own `readindex` with `__ATOMIC_RELAXED`, load peer `writeindex` with `__ATOMIC_ACQUIRE`, copy payload bytes, and publish new `readindex` with `__ATOMIC_RELEASE` (symmetrically for producers). Signed fill calculation `int32_t avail = (int32_t)(writeindex - readindex)` detects underrun (`avail < 0`) and overrun (`avail > (int32_t)size`) using local register snapshots, avoiding double-fetch races on the index words themselves.
- **Two Mandatory Caller Preconditions (`Basis: source + execution`):**
  1. **`size` Must Divide $2^{32}$ (Power-of-Two Buffer Size):** Because `readindex` and `writeindex` advance monotonically across `[0, 2^32 - 1]` without modulo reduction on update (`writeindex += len`), `index % size` is continuous across `0xFFFFFFFF -> 0x00000000` wraparound **if and only if $size \mid 2^{32}$** ($size = 2^k$). Live execution at `size = 48000` confirms `0xFFFFFFFF % 48000 == 23295` whereas `0x00000000 % 48000 == 0`—an immediate **23,295-byte backward discontinuity** corrupting ring framing upon `uint32_t` wrap!
  2. **Explicit `offset = index % size` Masking Before `spa_ringbuffer_read_data` / `write_data`:** `spa_ringbuffer_get_read_index` stores the **unmasked** 32-bit `readindex` into `*index`. Inside `spa_ringbuffer_read_data` (`ringbuffer.h:100`) and `spa_ringbuffer_write_data` (`ringbuffer.h:150`), the first chunk length is computed in unsigned 32-bit arithmetic as:
     ```c
     uint32_t l0 = SPA_MIN(len, size - offset), l1 = len - l0;
     ```
     If a caller passes an unmasked `offset` (or reloads `rbuf->readindex` from untrusted shared memory where a malicious peer wrote `offset = 70000 > size = 65536`), `size - offset` wraps modulo $2^{32}$ to `0xFFFFEE90`, `SPA_MIN(256, 0xFFFFEE90)` evaluates to `256`, and `SPA_PTROFF(buffer, 70000, void)` executes an **out-of-bounds `memcpy` 4,464 bytes past the end of `buffer`**.

---

### 3. `D-Bus` `SCM_RIGHTS` Descriptor Passing, `memfd` Sealing, and `pidfd` Portals

`Basis: normative + source + execution`

#### 3.1 `AF_UNIX` `SCM_RIGHTS` Limits, Cyclic Socket GC, and `dbus-broker` Per-UID Quotas

When D-Bus messages carry `UNIX_FD` (`'h'`) arguments—each marshaled in the message body as a 32-bit unsigned index into the `SCM_RIGHTS` ancillary FD array—three kernel and broker layers govern resource safety:

| Mechanism | Source Implementation | Enforced Bound / Algorithm | Failure Mode Prevented & Residual Edge Case |
| :--- | :--- | :--- | :--- |
| Per-`sendmsg` ancillary array cap | Linux `include/net/scm.h`, `net/core/scm.c` (`SCM_MAX_FD`) | Maximum **`253` file descriptors** per `sendmsg`; `254` FDs returns `-EINVAL` (verified via live execution on Linux `7.1.6`) | Bounds single-skb kernel `scm_fp_list` allocation; D-Bus callers passing $> 253$ FDs must split across messages or pass an archive/directory FD |
| Per-UID kernel inflight cap | Linux `net/unix/af_unix.c:1836-1848` (`too_many_unix_fds`) | Rejects `unix_attach_fds` with `-ETOOMANYREFS` when `user->unix_inflight > task_rlimit(current, RLIMIT_NOFILE)` (unless `CAP_SYS_RESOURCE`/`CAP_SYS_ADMIN`) | Prevents unprivileged processes from hiding unlimited open `struct file` references inside unread `AF_UNIX` socket receive queues after `close()`ing local FDs |
| Kernel cyclic `SCM_RIGHTS` garbage collector | Linux `net/unix/garbage.c:396-588` (`__unix_walk_scc`) | Tarjan Strongly Connected Components (`scc_index`, `unix_scc_cyclic`) over `unix_unvisited_vertices` on `system_unbound_wq` | Reclaims closed `AF_UNIX` sockets $S_1 \leftrightarrow S_2$ whose only remaining `f_count` references reside inside each other's unread `SCM_RIGHTS` skbs (`scc_dead == true`) |
| Broker cross-tenant FD isolation | `bus1/dbus-broker` `src/dbus/socket.c:131-137, 672-690` (`USER_SLOT_FDS`) | Charges both incoming and queued outgoing `fdlist_count` against the peer's per-UID `USER_SLOT_FDS` quota; exceeding quota triggers immediate `socket_close` (`SOCKET_E_QUOTA`) | Because the system D-Bus broker runs under a single privileged UID with high `RLIMIT_NOFILE`, kernel `too_many_unix_fds` alone cannot stop one tenant from stalling reads to exhaust the *broker's* FD table across all users |

#### 3.2 Shared-Memory `memfd` Sealing: Why `F_SEAL_FUTURE_WRITE` Does Not Prevent TOCTOU

Zero-copy IPC receivers accepting a `memfd` over `SCM_RIGHTS` face two post-validation attacks from an untrusted sender: (1) shrinking the file via `ftruncate(fd, 0)` while the receiver reads an `mmap`ped region, raising a fatal **`SIGBUS`** in the compositor or daemon; and (2) mutating bytes concurrently between header validation and payload consumption (`TOCTOU`).

Inspection of Linux `mm/memfd.c:118-280` (`v6.12`) and live syscall execution reveal a sharp, security-critical asymmetry among kernel seals:

1. **`F_SEAL_WRITE` (`0x0008`) Guarantees Zero Pre-Existing Writable Mappings or DMA Pins (`memfd.c:249-259`):**
   ```c
   if ((seals & F_SEAL_WRITE) && !(*file_seals & F_SEAL_WRITE)) {
       error = mapping_deny_writable(file->f_mapping);
       if (error)
           goto unlock;
       error = memfd_wait_for_pins(file->f_mapping);
       if (error) {
           mapping_allow_writable(file->f_mapping);
           goto unlock;
       }
   }
   ```
   `mapping_deny_writable` atomically rejects `F_ADD_SEALS` with **`-EBUSY`** if *any* `VM_SHARED` writable `mmap` (`MAP_SHARED` with `VM_MAYWRITE`) exists anywhere, and `memfd_wait_for_pins` (`memfd.c:118-171`) scans XArray folios up to `LAST_SCAN = 4` (~150 ms) to reject elevated `get_user_pages` (`GUP`) DMA references (`-EBUSY`). Thus, observing `(fcntl(fd, F_GET_SEALS) & (F_SEAL_WRITE | F_SEAL_SHRINK)) == (F_SEAL_WRITE | F_SEAL_SHRINK)` (on a verified tmpfs/hugetlbfs `memfd` where `F_GET_SEALS != -EINVAL`) **mathematically guarantees** that no process or DMA engine can shrink or mutate the mapped pages during the receiver's `PROT_READ` access.
2. **The `F_SEAL_FUTURE_WRITE` (`0x0010`) Trap (`Basis: source + execution`):** `F_SEAL_FUTURE_WRITE` blocks *subsequent* `write()`/`pwrite()` syscalls and *new* `PROT_WRITE` shared mappings (allowing receivers to `mmap(..., PROT_READ | PROT_WRITE, MAP_PRIVATE)` CoW), **but intentionally skips `mapping_deny_writable` and `memfd_wait_for_pins`!** As verified by live execution on Linux `7.1.6`, a malicious sender can:
   - Call `fd = memfd_create(..., MFD_ALLOW_SEALING)` and `ftruncate(fd, 4096)`;
   - Keep `mm_rw = mmap(fd, 4096, MAP_SHARED, PROT_READ | PROT_WRITE)` open;
   - Apply `fcntl(fd, F_ADD_SEALS, F_SEAL_FUTURE_WRITE | F_SEAL_SHRINK | F_SEAL_GROW)` (succeeds with `seals = 0x16`);
   - Send `fd` over `SCM_RIGHTS` and **overwrite `mm_rw[0:4]` from `b"INIT"` to `b"PWN!"` in real time** while the receiver reads its `PROT_READ` mapping!
   Therefore, **in-place zero-copy parsers MUST require `F_SEAL_WRITE | F_SEAL_SHRINK`** (never `F_SEAL_FUTURE_WRITE` alone); if `F_SEAL_FUTURE_WRITE` is accepted, the receiver must `memcpy` bytes once into private memory *before* running any bounds or invariant checks. Note also `check_sysctl_memfd_noexec` (`memfd.c:307-328`): under `vm.memfd_noexec = 2`, `memfd_create` without `MFD_NOEXEC_SEAL` fails with `-EACCES`, and `F_SEAL_EXEC` on an executable inode automatically implies `F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE | F_SEAL_FUTURE_WRITE` (`W^X`, `memfd.c:264-265`).

#### 3.3 Eliminating PID-Reuse Authorization Races via `SO_PEERPIDFD` and `ProcessFD`

Sandboxed desktop portals (`flatpak/xdg-desktop-portal`) authorize D-Bus requests by inspecting the caller's container metadata (`/.flatpak-info`, Snap cgroup, PID namespace). Historically, portals queried `org.freedesktop.DBus.GetConnectionUnixProcessID` (`SO_PEERCRED` `ucred.pid`) and opened `/proc/<pid>/root/...`. That numeric-PID pattern suffers two structural flaws:
1. **PID-Wraparound TOCTOU Escape:** A short-lived process inside a sandbox can queue an asynchronous D-Bus method call, keep the `AF_UNIX` connection open via an inherited descriptor, and `_exit()` immediately; under heavy fork churn, the kernel recycles `<pid>` to an unsandboxed host process before the portal opens `/proc/<pid>/root`, causing the portal to classify the sandboxed connection as an unconfined host caller (`xdp_app_info_host_new`).
2. **Cross-Namespace `ucred.pid == 0` Collapse (`zbus/src/runtime/io/unix.rs:254-258`):** When a peer resides in a sibling PID namespace unmapped in the receiver's PID namespace, the kernel translates `ucred.pid` to `0`, making numeric PID lookup impossible.

**End-to-End `pidfd` Binding Across Kernel, Broker, `zbus`, and Portal (`Basis: source + execution`):**
- **Socket Handshake Capture (`dbus-broker` `src/util/sockopt.c:139-157`; `zbus` `zbus/src/runtime/io/unix.rs:260-296`):** Both `dbus-broker` (`sockopt_get_peerpidfd`) and `zbus` invoke `getsockopt(fd, SOL_SOCKET, SO_PEERPIDFD, &pidfd, &len)` on the `AF_UNIX` socket (`net/unix/af_unix.c:976`), obtaining an unforgeable kernel `pidfd` pinned directly to the peer's `struct pid` at `connect()` time (even when `ucred.pid == 0` across namespaces), and expose it in `GetConnectionCredentials` as `"ProcessFD"` (`OwnedFd`, `zbus/src/fdo/dbus.rs:235-238`). Both handle pre-6.5 kernels (`ENOPROTOOPT`), socketless transports (`ENODATA`), and pre-6.16 already-reaped peers (`EINVAL` / `ESRCH` $\mapsto$ `SOCKOPT_E_REAPED`).
- **Portal Sandbox & Document FD Verification (`flatpak/xdg-desktop-portal` `shared/xdp-app-info.c:330-445, 582-611, 720-820`):** `xdp_app_info_new_for_invocation` acquires the caller's `pidfd` (`xdp_connection_get_pidfd`), pins `priv->pidfd` for the lifetime of the `XdpAppInfo` instance, extracts `priv->pidns_id` directly from `priv->pidfd` (`xdp_pidfd_get_pidns`, failing closed at `lines 598-603` if no `pidfd` is present when a PID namespace check is required), and when exporting host/sandbox files via `xdp_app_info_get_path_for_fd` (`lines 720-820`), cross-checks `fstat(fd, &expected_st)` against `stat(remapped_path, &real_st)` on `(st_dev, st_ino)` (`check_same_file`, `lines 688-717`) while rejecting `" (deleted)"` pseudo-paths (`memfd`/`shmem`) outside the FUSE document mountpoint (`lines 661-681`).

## Boundaries

- **`not examined` — Network-Transparent Wayland Proxies (`waypipe`) and Portal FUSE Inode Revocation Races:** Forwarding `linux-drm-syncobj-v1` timelines and `DMA-BUF` pages across hosts (`waypipe`) and concurrent FUSE dcache invalidation inside `document-portal/document-portal-fuse.c` were **not examined**.
- **`unknown` — Worst-Case Compositor GPU Preemption Latency on Malicious Shader Infinite Loops:** While `DrmSyncPointBlocker` (`sync_point.rs:345-357`) prevents an *unsignaled* `acquire_point` from blocking compositor CPU commits, once an `acquire_point` *signals* (or if a client triggers a GPU hang after signaling), whether the kernel DRM scheduler resets the guilty GPU context within a single display refresh frame (`< 16.6 ms`) depends on hardware-specific `drm_sched` TDR timeouts (`amdgpu`/`i915`/`xe`/`nvidia`) and is **unknown** at the Wayland protocol layer alone.
- **`known not to apply` — Assuming `F_SEAL_FUTURE_WRITE` Guarantees Immutability of Received `memfd` Buffers:** Treating `F_SEAL_FUTURE_WRITE | F_SEAL_SHRINK | F_SEAL_GROW` (`0x16`) as equivalent to `F_SEAL_WRITE | F_SEAL_SHRINK | F_SEAL_GROW` (`0x0e`) for zero-copy in-place parsing is **known not to apply**: pre-existing `MAP_SHARED | PROT_WRITE` mappings created by the sender prior to `F_ADD_SEALS` remain writable across `SCM_RIGHTS` transfer.
- **`unsupported` — `linux-drm-syncobj-v1` on `wl_shm` Buffers and `SO_PEERPIDFD` on Linux $< 6.5$:** Attaching `wp_linux_drm_syncobj_surface_v1` acquire/release points to `wl_shm` shared-memory buffers is explicitly **unsupported** (`Error::UnsupportedBuffer` in `Smithay/smithay` `src/wayland/drm_syncobj/mod.rs:270-275`), and `SO_PEERPIDFD` is **unsupported** (`ENOPROTOOPT`) on Linux kernels prior to `6.5`.

## Evidence

1. **Smithay `linux-drm-syncobj-v1` & `wayland-rs` Object Lifetimes:**
   - `Smithay/smithay` (`7ff0ede4df2af1ce3500da9ef1ee190d48b49103`):
     - `src/wayland/drm_syncobj/mod.rs:71-78` (`supports_syncobj_eventfd`), `109-119` (`merge_into` release signaling), `227-297` (`commit_hook` protocol errors `NoBuffer`, `NoReleasePoint`, `NoAcquirePoint`, `ConflictingPoints`, `UnsupportedBuffer`, and `destruction_hook`), `424-477` (`((point_hi as u64) << 32) + (point_lo as u64)`).
     - `src/wayland/drm_syncobj/sync_point.rs:53-60, 90-94` (`Arc::ptr_eq` equality on `DrmTimeline`), `140-180` (`eventfd` with `wait_available = false`), `219-257` (two-step `DRM_IOCTL_SYNCOBJ_FD_TO_HANDLE` `IMPORT_SYNC_FILE` workaround), `263-357` (`DrmSyncPointBlocker` vs. blocking `Fence::wait(i64::MAX)`).
   - `Smithay/wayland-rs` (`6d60c31e1386c6c954e2037b0a8cb368043ca63e`):
     - `wayland-backend/src/rs/map.rs:8, 38-85, 139-158` (`SERVER_ID_LIMIT = 0xFF00_0000`, dense ID table).
     - `wayland-backend/src/rs/server_impl/client.rs:214-233, 248-257` (`send_delete_id` client-ID guard and `serial` check).
     - `wayland-backend/src/rs/client_impl/mod.rs:635-670` (`wl_display.delete_id` zombie teardown and event-signature lookup).
2. **PipeWire Real-Time Activation DAG & `spa_ringbuffer` (`PipeWire/pipewire` @ `89f53e32acc5b711e3eb089e5a42f4292393aabe`):**
   - `src/pipewire/private.h:502-689`: `pw_node_activation_state`, `pw_node_activation` CAS state machine (`NOT_TRIGGERED -> TRIGGERED -> AWAKE -> FINISHED`), `PW_NODE_ACTIVATION_FLAG_ASYNC`, and `trigger_target_v1` (`SPA_ATOMIC_DEC` + `SPA_ATOMIC_CAS` + `spa_system_eventfd_write`).
   - `src/pipewire/impl-node.c:262-277, 835, 1311-1335, 1395-1521`: dead-peer `deactivate_target` cleanup, dynamic `quantum` updates, and `debug_xrun_graph` (`xrun stuck` on `pending > 0`).
   - `spa/include/spa/utils/ringbuffer.h:39-165`: `spa_ringbuffer_get_read_index`, `spa_ringbuffer_get_write_index`, and unsigned `uint32_t l0 = SPA_MIN(len, size - offset)` in `spa_ringbuffer_read_data` / `write_data`.
3. **D-Bus, Portals, and Linux Kernel `v6.12` Primitives:**
   - `dbus2/zbus` (`615620ad61bd286460a861d50c71e0fcece59e70`): `zbus/src/runtime/io/unix.rs:254-296` (`ucred.pid == 0` cross-namespace note and `SO_PEERPIDFD` `getsockopt` with kernel `< 6.5` / `< 6.16` error handling) and `zbus/src/fdo/dbus.rs:228-247` (`ConnectionCredentials::process_fd` `"ProcessFD"`).
   - `bus1/dbus-broker` (`2956b5d381deeea709c53d02f10e799e50e44f4b`): `src/util/sockopt.c:139-157` (`sockopt_get_peerpidfd` / `SOCKOPT_E_REAPED`) and `src/dbus/socket.c:131-137, 672-690` (`user_charge(..., USER_SLOT_FDS, n_fds)`).
   - `flatpak/xdg-desktop-portal` (`c00a32b7a3d136d7e86e8beb494867eb0babe9a5`): `shared/xdp-app-info.c:330-445, 582-611, 661-717, 720-820` (`pidfd` ownership, `xdp_pidfd_get_pidns`, `" (deleted)"` rejection, and `(st_dev, st_ino)` `check_same_file`).
   - `torvalds/linux` `v6.12` (`adc218676eef25575469234709c2d87185ca223a`): `drivers/gpu/drm/drm_syncobj.c:711-765, 1420-1508` (`idr_alloc` without deduplication in `drm_syncobj_fd_to_handle`, `drm_syncobj_eventfd_ioctl`), `net/unix/af_unix.c:976, 1836-1901` (`SO_PEERPIDFD`, `too_many_unix_fds`), `net/unix/garbage.c:396-588` (Tarjan SCC `__unix_walk_scc`), and `mm/memfd.c:118-328` (`memfd_wait_for_pins`, `mapping_deny_writable` on `F_SEAL_WRITE` only, `MFD_NOEXEC_SEAL`).
4. **Live Linux Kernel Execution (`observed_at: 2026-11-19`, Linux `7.1.6-1rodete1-amd64`):**
   - Verified `-EBUSY` on `F_ADD_SEALS(F_SEAL_WRITE)` while `MAP_SHARED | PROT_WRITE` is mapped, live `b'INIT' -> b'PWN!'` TOCTOU mutation across `MAP_SHARED` despite `F_SEAL_FUTURE_WRITE | F_SEAL_SHRINK | F_SEAL_GROW` (`0x16`), `253`-FD `SCM_RIGHTS` delivery vs. `254`-FD `EINVAL` rejection, live `SO_PEERPIDFD` (`77`) extraction, and `spa_ringbuffer` `48000` wrap discontinuity (`23295 -> 0`) + unmasked unsigned underflow (`0xffffee90`).

## Revalidation

1. **Self-Contained Linux Kernel `memfd` / `SCM_RIGHTS` / `SO_PEERPIDFD` / `spa_ringbuffer` Probe (< 1 second, Linux Python 3.10+ stdlib only):**
   Run the following standalone probe on any Linux host ($\ge 6.5$ for `SO_PEERPIDFD`) to re-verify all kernel seal, ancillary FD limit, `pidfd`, and `spa_ringbuffer` arithmetic invariants:

```bash
python3 - <<'EOF'
import array, errno, fcntl, mmap, os, socket

F_ADD_SEALS, F_GET_SEALS = 1033, 1034
F_SEAL_SEAL, F_SEAL_SHRINK, F_SEAL_GROW, F_SEAL_WRITE, F_SEAL_FUTURE_WRITE = 1, 2, 4, 8, 16

fd = os.memfd_create("reval_seal", os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
os.ftruncate(fd, 4096)
mm_rw = mmap.mmap(fd, 4096, mmap.MAP_SHARED, mmap.PROT_READ | mmap.PROT_WRITE)
mm_rw[0:4] = b"INIT"

try:
    fcntl.fcntl(fd, F_ADD_SEALS, F_SEAL_WRITE)
    raise AssertionError("expected EBUSY while MAP_SHARED|PROT_WRITE is active")
except OSError as exc:
    assert exc.errno == errno.EBUSY

fcntl.fcntl(fd, F_ADD_SEALS, F_SEAL_FUTURE_WRITE | F_SEAL_SHRINK | F_SEAL_GROW)
mm_ro = mmap.mmap(fd, 4096, mmap.MAP_SHARED, mmap.PROT_READ)
assert bytes(mm_ro[0:4]) == b"INIT"
mm_rw[0:4] = b"PWN!"
assert bytes(mm_ro[0:4]) == b"PWN!"  # Proves F_SEAL_FUTURE_WRITE permits pre-mapped TOCTOU!
mm_ro.close()
mm_rw.close()

fcntl.fcntl(fd, F_ADD_SEALS, F_SEAL_WRITE | F_SEAL_SEAL)
assert fcntl.fcntl(fd, F_GET_SEALS) == 0x1F
os.close(fd)

s1, s2 = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM)
mfd = os.memfd_create("scm_test", os.MFD_CLOEXEC)
s1.sendmsg([b"1"], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [mfd] * 253))])
_, anc, _, _ = s2.recvmsg(8, socket.CMSG_SPACE(253 * 4))
rfds = array.array("i")
rfds.frombytes(anc[0][2][: len(anc[0][2]) - (len(anc[0][2]) % 4)])
assert len(rfds) == 253
for r in rfds:
    os.close(r)

try:
    s1.sendmsg([b"1"], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [mfd] * 254))])
    raise AssertionError("expected EINVAL on 254 SCM_RIGHTS FDs")
except OSError as exc:
    assert exc.errno == errno.EINVAL

try:
    pfd = s1.getsockopt(socket.SOL_SOCKET, 77)  # SO_PEERPIDFD
    os.close(pfd)
    pidfd_status = "supported"
except OSError as exc:
    assert exc.errno == errno.ENOPROTOOPT
    pidfd_status = "kernel<6.5"

os.close(mfd)
s1.close()
s2.close()

assert (0xFFFFFFFF % 48000) == 23295 and (((0xFFFFFFFF + 1) & 0xFFFFFFFF) % 48000) == 0
assert min(256, (65536 - 70000) & 0xFFFFFFFF) == 256
print("ALL WAYLAND/PIPEWIRE/DBUS/MEMFD INVARIANTS VERIFIED:", {"SO_PEERPIDFD": pidfd_status})
EOF
```

2. **Targeted Source Revalidation Checks Across Upstream Upgrades:**
   - In `Smithay/smithay`, inspect `PartialEq for DrmTimeline` in `src/wayland/drm_syncobj/sync_point.rs` and `commit_hook` in `src/wayland/drm_syncobj/mod.rs` to check whether duplicate `import_timeline` calls on `dup()`d `drm_syncobj` FDs are deduplicated by inode/kcmp or remain `Arc::ptr_eq`-only.
   - In `PipeWire/pipewire`, inspect `spa/include/spa/utils/ringbuffer.h` (`spa_ringbuffer_read_data` / `write_data`) and `src/pipewire/private.h` (`trigger_target_v1`) to confirm atomic ordering and caller modulo preconditions.
   - In `torvalds/linux`, inspect `mm/memfd.c` (`memfd_add_seals`) and `net/unix/garbage.c` (`__unix_walk_scc`) to verify whether new seal flags or `AF_UNIX` inflight accounting alter `F_SEAL_WRITE` vs. `F_SEAL_FUTURE_WRITE` semantics.
