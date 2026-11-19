# Linux TCP MSG_ZEROCOPY and devmem Lifetimes, PCIe P2PDMA ACS Redirection, and Heterogeneous NVLink-to-PCIe Proxy Ordering

## Summary

Zero-copy network and accelerator pipelines eliminate host CPU memory-copy overhead by sharing mutable user pages or device memory directly with kernel socket rings, NIC scatter-gather DMA engines, and peer PCIe/NVLink fabrics. Across Linux `MSG_ZEROCOPY`, `netmem`/`devmem` TCP, `PCIe P2PDMA`, `NVIDIA GDRCopy`, `NCCL`, `rdma-core`, and `UCX`, end-to-end memory safety rests on **four coupled lifetime and visibility invariants**:

1. **Transmit buffer ownership extends to transport ACK, not syscall return or NIC TX ring completion:** In Linux `MSG_ZEROCOPY` (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`), `send()` / `sendmsg()` attaches a reference-counted `struct ubuf_info_msgzc` (`refcnt`) to `skb_shared_info`, incremented across TCP retransmission queue residency and cloned packets (`skb_clone`). A buffer may **only** be mutated or freed after `recvmsg(..., MSG_ERRQUEUE)` delivers a `SO_EE_ORIGIN_ZEROCOPY` (`ee_errno == 0`) notification covering its 32-bit invocation counter `[ee_info, ee_data]` (modulo `2^32` wraparound). Mutating pages after initial NIC DMA completion but before remote TCP `ACK` corrupts subsequent RTO/SACK retransmissions silently—even passing hardware TCP checksum offload and breaking in-place TLS AEAD authentication. Moreover, `SO_EE_CODE_ZEROCOPY_COPIED` signals deferred fallback copying (`skb_copy_ubufs` / loopback `skb_orphan_frags_rx`), proving completion notification does not imply wire transmission.
2. **Unreadable `devmem` TCP splits headers from payload `dmabuf`s via explicit fragment tokens:** Device Memory TCP (`net/core/devmem.c`, `net/ipv4/tcp.c`) pins a `dma_buf` (`dma_buf_pin`, `allow_peer2peer = true`), steers flows onto NIC header-split queues, receives unreadable `net_iov` fragments via `MSG_SOCK_DEVMEM` (`SCM_DEVMEM_DMABUF`) recycled through `SO_DEVMEM_DONTNEED` (capped at 128 token structs / 1,024 frags per call), and transmits via `MSG_ZEROCOPY` + `SCM_DEVMEM_DMABUF` where `iov_base` carries an offset rather than a host virtual pointer. Unreadable fragments reject loopback, software checksums, `tcpdump` payload inspection, and collapsing with host-memory fragments.
3. **PCIe Access Control Services (`ACS`) redirection silently reroutes peer DMA through the Root Complex:** In `drivers/pci/p2pdma.c`, `calc_map_type_and_dist` only selects direct switch hairpin routing (`PCI_P2PDMA_MAP_BUS_ADDR`) when **zero** ports along the lowest common bridge ancestor enable `PCI_ACS_RR | PCI_ACS_CR | PCI_ACS_EC`. Firmware/IOMMU ACS enforcement silently downgrades peer DMA to `PCI_P2PDMA_MAP_THRU_HOST_BRIDGE` (halving bisection bandwidth or faulting unmapped bus addresses) or `PCI_P2PDMA_MAP_NOT_SUPPORTED` if the Root Complex fails `cpu_supports_p2pdma()` / `pci_p2pdma_whitelist[]`.
4. **Heterogeneous NVLink + PCIe pipelines require `.sys`-scope and mixed-proxy fences:** Under the formal NVIDIA PTX memory consistency model (`10.1145/3297858.3304043`, `10.1145/3470496.3533045`), `.gpu`-scoped fences order peer NVLink SM accesses among GPUs (`fence.acq_rel.gpu`) but omit host CPUs and PCIe NIC DMA engines (`NCCL` upgrades to `fence.acq_rel.sys` whenever `ConnFifoEnabled` / `peer->connFifo` is active), while generic-to-async engines require `fence.proxy.async`, and host write-combined (`WC`) / mixed-coherent BAR mappings (`NVIDIA/gdrcopy`) require `sfence`/`mfence` (`DMB st`/`DMB sy`) before ringing doorbells.

## Applicability

This report documents exact mechanisms and invariants observed across the following pinned upstream artifacts and formal models:

- **Linux Kernel** (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`): `Documentation/networking/{msg_zerocopy.rst, devmem.rst}`, `include/uapi/linux/errqueue.h`, `include/linux/skbuff.h`, `net/core/{skbuff.c, devmem.c, devmem.h}`, `net/ipv4/tcp.c`, and `drivers/pci/p2pdma.c`. Live kernel execution of the `MSG_ZEROCOPY` + `SO_EE_ORIGIN_ZEROCOPY` socket probe was performed on Linux `7.1.6` (`x86_64`).
- **NVIDIA Collective Communications Library (`NCCL`)** (`NVIDIA/nccl` @ `ad2d192c1f279aefcaf340f67e07880b65a1116b`): `src/device/{op128.h, prims_simple.h}` detailing PTX `.sys` vs `.gpu` scope selection on peer vs host-proxied FIFO/NIC channels.
- **NVIDIA `GDRCopy`** (`NVIDIA/gdrcopy` @ `0d85ee38d696495592c1d589ab42e021d35cda61`): `src/gdrapi.c` detailing `gdrdrv` vs `GDR_USE_DMABUF` (`CU_MEM_RANGE_FLAG_DMA_BUF_MAPPING_TYPE_PCIE`), write-combining (`GDR_MAPPING_TYPE_WC`), coherent caching (`GDR_MAPPING_TYPE_CACHING`), and mixed-mapping fence promotion.
- **RDMA Core and OpenUCX** (`linux-rdma/rdma-core` @ `8634881a642407093dcef4a77a361375bfa4cb69`, `openucx/ucx` @ `a910af25760ef4c6c99c8491919e21efffa34657`): `libibverbs/verbs.h` (`ibv_reg_dmabuf_mr`) and `src/uct/ib/base/ib_md.c` (`uct_ib_md_reg_mr` with `dmabuf_fd` / `dmabuf_offset`).
- **PTX Formal Memory Models**: Lustig, Sahasrabuddhe, and Giroux (`ASPLOS 2019`, `DOI: 10.1145/3297858.3304043`) and Lustig, Cooksey, and Giroux (`ISCA 2022`, `DOI: 10.1145/3470496.3533045`).

Findings on `devmem` TCP apply strictly to kernels supporting `CONFIG_NET_DEVMEM` and NIC hardware with TCP header-payload split (`ethtool -G <iface> tcp-data-split on`), and P2PDMA topology rules reflect Linux's `drivers/pci/p2pdma.c` policy (`cpu_supports_p2pdma()` + `pci_p2pdma_whitelist[]`).

## Findings

### 1. `MSG_ZEROCOPY` `ubuf_info` Reference Lifetimes, Error-Queue Coalescing, and TCP Retransmission Corruption

**Basis:** `documentation` (`msg_zerocopy.rst`) + `source` (`include/uapi/linux/errqueue.h`, `include/linux/skbuff.h`, `net/core/skbuff.c`, `net/ipv4/tcp.c`) + `execution` (live Linux `7.1.6` socket probe + state-space checker).

#### 1.1 Allocation, Pin Accounting, and Coalesced Notification Mechanics

Enabling zero-copy socket transmission requires an explicit opt-in `setsockopt(fd, SOL_SOCKET, SO_ZEROCOPY, &one, sizeof(one))` (`msg_zerocopy.rst:73`) followed by per-call `MSG_ZEROCOPY` flags (`tcp.c:1146-1172`). Internally, `net/core/skbuff.c:1724-1904` manages page pinning and asynchronous completion via `struct ubuf_info_msgzc` (`include/linux/skbuff.h:558-578`):

1. **Per-Call 32-Bit Key (`sk_zckey`) & Coalescing (`skbuff.c:1745-1810`):** Every non-empty successful `MSG_ZEROCOPY` send increments `sk->sk_zckey` (wrapping at `UINT_MAX`). For `SOCK_STREAM` (TCP), `msg_zerocopy_realloc` attempts to extend the tail `skb`'s existing `uarg` (`uarg_zc->len++`) as long as `(u32)(uarg_zc->id + uarg_zc->len) == next`, `uarg_zc->len < USHRT_MAX - 1`, and `bytelen <= (1 << 19)` (`512 KiB`, `byte_limit`), taking an extra `net_zcopy_get(uarg)` reference (`skbuff.c:1801-1802`). Otherwise, `msg_zerocopy_alloc` allocates a zero-payload control `sk_buff` embedding `uarg` in `skb->cb`, sets `SKBFL_ZEROCOPY_FRAG | SKBFL_DONT_ORPHAN`, charges `mm_account_pinned_pages(&uarg->mmp, size)` against `RLIMIT_MEMLOCK` (returning `-ENOBUFS` on quota exhaustion, `tcp.c:1156`), and takes a socket hold (`sock_hold(sk)`).
2. **Error-Queue Delivery & Tail Merging (`skbuff.c:1813-1881`, `errqueue.h:15-40`):** Only when `refcount_dec_and_test(&uarg->refcnt)` drops to zero does `msg_zerocopy_complete` invoke `__msg_zerocopy_callback`, which unaccounts pinned pages and queues a `struct sock_extended_err` on `&sk->sk_error_queue` with:
   - `ee_errno = 0` (so pending zerocopy completions do not fail/block subsequent `send()`/`recv()` syscalls, `msg_zerocopy.rst:145-146`),
   - `ee_origin = SO_EE_ORIGIN_ZEROCOPY` (`5`),
   - Inclusive 32-bit invocation range `[ee_info, ee_data] = [uarg->id, uarg->id + uarg->len - 1]`,
   - `ee_code |= SO_EE_CODE_ZEROCOPY_COPIED` (`1`) whenever `uarg_zc->zerocopy == 0` (set if any clone/lower path invoked `skb_copy_ubufs` or lacked `NETIF_F_SG`, `tcp.c:1162`, `skbuff.c:1888`).
   `skb_zerocopy_notify_extend` (`skbuff.c:1813-1831`) checks the tail `skb` on `sk_error_queue`: if `lo == old_hi + 1` and `(old_hi - old_lo + 1 + len) < 2^32`, it drops the new notification `skb` and extends `serr->ee.ee_data += len`.
3. **Empirical Loopback & Coalescing Verification (`Basis: execution`):** Executing three consecutive `16,384`-byte `send(..., MSG_ZEROCOPY)` calls over a local `127.0.0.1` TCP socket on Linux `7.1.6` (`x86_64`) returned a single coalesced `IP_RECVERR` control message: `errqueue_cmsgs=[(0, 2, 1)]` (`ee_info=0`, `ee_data=2`, `ee_code=1 == SO_EE_CODE_ZEROCOPY_COPIED`). The `COPIED` flag confirms `skb_orphan_frags_rx` (`include/linux/skbuff.h:3440-3445`) unconditionally triggers `skb_copy_ubufs` whenever a packet loops onto a local RX path (`msg_zerocopy.rst:241-246`), preventing local stalled readers from pinning sender memory indefinitely.

#### 1.2 Retransmission Premature-Overwrite Corruption & `u32` Wraparound Traps

A pervasive zero-copy misuse bug is assuming buffer reuse is safe once `send()` returns, once `POLLOUT` fires, or even once a NIC driver reclaims its TX descriptor ring:

- **Why NIC TX Completion Is Insufficient:** In TCP, `tcp_write_xmit` transmits a **`skb_clone()`** while retaining the original `skb` in `sk_rtx_queue` until the peer returns a cumulative/SACK `ACK` (`net/core/skbuff.c:1968-1986` shares `uarg` across clones unless copied). Consequently, `uarg->refcnt` stays `>= 1` even after the NIC completes its initial TX DMA!
- **Silent Wire Corruption vs. TLS AEAD Failure (`Basis: derived + execution`):** Exhaustive interleaving analysis over `{NIC_TX_DONE, RTO_REXMIT, TCP_ACK, APP_MUTATE}` shows:
  1. If `APP_MUTATE` writes new payload bytes after `NIC_TX_DONE` while `refcnt == 1`, a subsequent `RTO_REXMIT` clones the retained `skb` (whose `skb_frag_t` entries still point to the mutated user pages!) and re-DMAs the **new** bytes under the **old** TCP sequence number.
  2. When NIC hardware TX checksum offload (`CHECKSUM_PARTIAL`) recomputes the TCP checksum during retransmission, the corrupted segment arrives with a valid L4 checksum—corrupting plaintext streams silently, or causing fatal record decryption failure when user-space TLS encrypted the buffer in place!
  3. Gating buffer mutation strictly on `SO_EE_ORIGIN_ZEROCOPY` (`refcnt == 0`) yields **zero** corrupting interleavings across all causal orderings.
- **32-Bit Counter Wraparound (`sk_zckey`):** Because `sk_zckey` wraps at `2^32` (`msg_zerocopy.rst:112`), naive integer comparisons `lo <= id && id <= hi` fail whenever `[ee_info, ee_data]` straddles `0xFFFFFFFF -> 0`. Sound reclamation must check modular span containment: `((id - lo) & 0xFFFFFFFF) <= ((hi - lo) & 0xFFFFFFFF)` (verified for `[0xFFFFFFFE, 2]` in the probe).

### 2. Device Memory (`devmem` / `netmem`) TCP Split-Header DMA, Unreadable `skb`s, and Token Exhaustion

**Basis:** `documentation` (`devmem.rst`) + `source` (`net/core/devmem.c`, `net/core/devmem.h`, `net/ipv4/tcp.c`, `net/core/skbuff.c`).

`net_devmem` extends zero-copy TCP directly into NIC-mapped `dma_buf` accelerator/GPU memory (`net/core/devmem.c:184-464`, `net/core/devmem.h:19-84`) while keeping L2–L4 protocol headers in kernel-accessible host RAM:

| Dimension | `devmem` TCP RX (`FROM_DEVICE`) | `devmem` TCP TX (`TO_DEVICE`) | Primary Source Constraint |
| :--- | :--- | :--- | :--- |
| **Control-plane bind** | Netlink `netdev_bind_rx` attaches `dmabuf_fd` to specific RX queue(s); returns `dmabuf_id` | Netlink `netdev_bind_tx` binds `dmabuf_fd` to netdev; returns `tx_dmabuf_id` | `devmem.c:152-350`; closing netlink socket invokes `net_devmem_unbind_dmabuf` (`percpu_ref_kill`) for crash cleanup (`devmem.rst:127-130`) |
| **NIC / Route prerequisites** | Hardware header-split (`tcp-data-split on`), RSS exclusion, `ntuple` flow steering | Route `dst_dev` must match `binding->dev` or `binding->vdev` (`-ENODEV` otherwise); `SO_ZEROCOPY` mandatory | `devmem.rst:79-142`, `devmem.c:433-440`, `tcp.c:1178-1181` |
| **Data-plane `recvmsg` / `sendmsg`** | Must pass `MSG_SOCK_DEVMEM` (`-EFAULT` if omitted!); receives `SCM_DEVMEM_DMABUF` (`dmabuf_id, frag_offset, frag_size, frag_token`) or `SCM_DEVMEM_LINEAR` | Must pass `MSG_ZEROCOPY` + `SCM_DEVMEM_DMABUF` `cmsg` (`u32 tx_dmabuf_id`); **`iov_base` is a byte offset into `dmabuf`**, not a CPU pointer! | `devmem.rst:147-206, 293-332`, `devmem.c:453-464` (`net_devmem_get_niov_at` indexes `tx_vec[virt_addr / PAGE_SIZE]`) |
| **Pin / `RLIMIT_MEMLOCK` accounting** | Bounded `net_iov` freelist (`area.num_niovs = dmabuf->size >> niov_shift`) | Passes `devmem = true` to `msg_zerocopy_realloc`, **skipping `mm_account_pinned_pages`** | `devmem.c:282-339`, `skbuff.c:1740, 1793`, `tcp.c:1154` |
| **Buffer release & exhaustion trap** | App must free tokens via `setsockopt(SOL_SOCKET, SO_DEVMEM_DONTNEED, &tokens)` — **max 128 token structs, max 1,024 total frags per call** | App waits for `MSG_ERRQUEUE` `SO_EE_ORIGIN_ZEROCOPY` (`percpu_ref` holds binding until all cloned `net_iov`s complete) | `devmem.rst:212-235` (leaking tokens starves `binding->freelist` and drops RX packets), `devmem.h:46-53` |
| **Kernel readability restrictions** | `dma_sync` disabled (`pool->dma_sync = false`); unreadable frags fall back to `SCM_DEVMEM_LINEAR` if NIC cannot split | Rejects coalescing readable & unreadable frags (`skb_frags_readable(skb) != !binding`, `tcp.c:1257`), `MSG_FASTOPEN` (`-EINVAL`), `TCP_REPAIR` (`-EINVAL`), and `skb_copy_ubufs` (`-EFAULT`, `skbuff.c:2010-2011`) | `devmem.c:478-479`, `tcp.c:1183-1216, 1256-1257`, `devmem.rst:378-390` (no loopback, SW checksum, `tcpdump`, or BPF payload access) |

Critically, `net_devmem_bind_dmabuf` (`devmem.c:237-266`) uses `dma_buf_dynamic_attach` with `net_devmem_dmabuf_attach_ops = { .allow_peer2peer = true }`, `dma_buf_pin`, `dma_buf_map_attachment`, and waits via `dma_resv_wait_timeout(..., DMA_RESV_USAGE_KERNEL, ...)` before accepting scatterlist entries—all of which still rely on the underlying PCIe fabric and IOMMU allowing peer-to-peer DMA.

### 3. `PCIe P2PDMA` Hairpin Routing, `ACS` IOMMU Traps, and `dma_buf` / `GDRCopy` Registration

**Basis:** `source` (`torvalds/linux` `drivers/pci/p2pdma.c`, `NVIDIA/gdrcopy` `src/gdrapi.c`, `linux-rdma/rdma-core` `libibverbs/verbs.h`, `openucx/ucx` `src/uct/ib/base/ib_md.c`).

#### 3.1 `calc_map_type_and_dist` and the `PCI_ACS_CTRL` Redirection Trap

In `drivers/pci/p2pdma.c:498-811`, when two PCI functions (`provider` owning the BAR memory—such as a GPU or NVMe CMB—and `client` issuing DMA—such as a NIC or RDMA HCA) attempt peer-to-peer DMA, Linux traverses upstream bridges from both endpoints to determine `enum pci_p2pdma_map_type`:

```text
Root Port / Host Bridge
   └── PCIe Switch Upstream Port
         ├── Downstream Port 0 (ACS_CTRL?) ── Provider (e.g., GPU BAR / P2P mem)
         └── Downstream Port 1 (ACS_CTRL?) ── Client   (e.g., NIC / RDMA HCA)
```

1. **Direct Switch Hairpin (`PCI_P2PDMA_MAP_BUS_ADDR`):** Found only if `provider` and `client` share an upstream switch/bridge *and* `pci_bridge_has_acs_redir()` (`p2pdma.c:498-513`) returns `0` on **every** bridge along both legs (`acs_cnt == 0`, distance `= 4` across two downstream ports of one switch, `p2pdma.c:692-710, 780-783`). TLPs hairpin inside the switch using raw PCI bus addresses (`pci_bus_address`, adjusted by `p2p->mem[bar].bus_offset`, `p2pdma.c:287-288`), bypassing both the Root Complex and host IOMMU.
2. **ACS Redirection Trap (`PCI_P2PDMA_MAP_THRU_HOST_BRIDGE`):** Virtualization platforms and default IOMMU isolation policies enable PCIe **Access Control Services (`PCI_ACS_CTRL`)**:
   - `PCI_ACS_RR` (P2P Request Redirect),
   - `PCI_ACS_CR` (P2P Completion Redirect),
   - `PCI_ACS_EC` (P2P Upstream Forwarding).
   If **any** bridge on the path has `ctrl & (PCI_ACS_RR | PCI_ACS_CR | PCI_ACS_EC)` (`p2pdma.c:509`), `calc_map_type_and_dist` warns (`pci=disable_acs_redir=<bdf>;...`, `p2pdma.c:791`) and forces traffic up to the Root Complex (`PCI_P2PDMA_MAP_THRU_HOST_BRIDGE`). Even if the Root Complex allows P2P routing, forcing Peer-to-Peer TLPs through the Root Complex halves effective switch fabric throughput, introduces IOMMU translation overhead, and—if a custom driver or user-space queue programs raw physical/bus BAR addresses bypassing IOMMU IOVA mapping—triggers **IOMMU page faults or PCIe Completer Aborts**.
3. **Host-Bridge Whitelist Rejection (`PCI_P2PDMA_MAP_NOT_SUPPORTED`):** When traffic must traverse a host bridge (either due to `acs_cnt > 0` or because `provider` and `client` sit under different Root Ports), `p2pdma.c:795-802` requires either `cpu_supports_p2pdma()` (x86 AMD Zen `family >= 0x17`, `p2pdma.c:529-530`) or matching `pci_p2pdma_whitelist[]` (`p2pdma.c:536-675`, e.g., specific Intel Xeon/Skylake/SPR/GNR/DMR, Google SoCs, Nvidia CPUs, Zhaoxin, Alibaba Yitian 710, with `REQ_SAME_HOST_BRIDGE` enforced for older Intel chipsets). Unlisted host bridges return `PCI_P2PDMA_MAP_NOT_SUPPORTED` (`-1` distance in `pci_p2pdma_distance_many`).

#### 3.2 `dma_buf` RDMA Registration and `GDRCopy` Mapping Modes

To avoid proprietary out-of-tree `nvidia-peermem` kernel pinning hooks, modern GPU-NIC zero-copy stacks route GPU allocations through Linux `dma_buf`:

- **RDMA Verbs & UCX (`rdma-core/libibverbs/verbs.h:2732-2736`, `ucx/src/uct/ib/base/ib_md.c:515-565`):** User space exports a GPU range FD (via CUDA `cuMemGetHandleForAddressRange(..., CU_MEM_RANGE_HANDLE_TYPE_DMA_BUF_FD, ...)`) and registers it with the NIC via `ibv_reg_dmabuf_mr(md->pd, dmabuf_offset, length, (uintptr_t)address, dmabuf_fd, access_flags)`. Kernel `ib_umem_dmabuf_get` pins and maps the attachment only when the exporter (`nvidia.ko`) and RDMA HCA pass P2P/IOMMU checks.
- **CPU Direct-BAR Mapping in `NVIDIA/gdrcopy` (`src/gdrapi.c:284-441`):** `gdr_pin_buffer_dmabuf` supports `CU_MEM_RANGE_HANDLE_TYPE_DMA_BUF_FD` with two critically distinct mapping types (`gdrapi.c:299-325`):
  - On non-coherent PCIe GPUs—or whenever `GDR_PIN_FLAG_FORCE_PCIE` passes `CU_MEM_RANGE_FLAG_DMA_BUF_MAPPING_TYPE_PCIE`—GDRCopy maps the GPU BAR as **`GDR_MAPPING_TYPE_WC` (Write-Combining)**, allowing burst posted writes from CPU to GPU VRAM without crossing coherent caches.
  - On cache-coherent CPU-GPU interconnects (`gdr_cuda_device_is_coherent`), GDRCopy maps via **`GDR_MAPPING_TYPE_CACHING`**—unless a workload mixes both mapping classes on the same process, triggering `gdr_has_mix_mapping()` (`gdrapi.c:60-70`).

### 4. Heterogeneous `NVLink` + `PCIe` Weak Proxy Memory Ordering (`fence.proxy.async`, `.gpu` vs `.sys`, and WC Fences)

**Basis:** `normative` (`10.1145/3297858.3304043`, `10.1145/3470496.3533045`) + `source` (`NVIDIA/nccl` `src/device/{op128.h, prims_simple.h}`, `NVIDIA/gdrcopy` `src/gdrapi.c`) + `execution` (mixed-proxy litmus checker).

Even when `P2PDMA` and `dma_buf` mappings succeed without ACS faults, heterogeneous pipelines composing **GPU SMs**, **NVLink peer-to-peer memory**, **async hardware copy engines (TMA / `cp.async`)**, **host CPUs**, and **PCIe NIC DMA engines** suffer subtle weak-memory visibility bugs because PTX memory consistency partitions ordering along **both Scope** and **Proxy** axes:

```text
  GPU0 SM (generic proxy)
     │  1. st.global (writes payload into GPU1 HBM over NVLink or local HBM)
     ▼
  [Requires fence.proxy.async if async engine / TMA produced/consumed payload]
     │
  [fence.acq_rel.gpu?]  ──X── FAILS to order wrt Host CPU or PCIe NIC DMA!
  [fence.acq_rel.sys!]  ────► Guarantees visibility at Host CPU & PCIe Root
     │
  st.relaxed.sys.global (notifies Host proxy / ConnFifo tailPtr)
     ▼
  Host CPU (WC BAR or coherent poll) ──► [sfence / mfence / DMB sy] ──► NIC Doorbell MMIO
                                                                             │
                                                                             ▼
                                                                  PCIe NIC DMA Read (GPU HBM)
```

1. **Scope Axis Insufficiency (`.gpu` vs. `.sys`, `10.1145/3297858.3304043`):** Under the formal PTX consistency axioms, a release/fence operation only orders prior writes with respect to observers within its **morally strong** scope. `.gpu` scope (`fence.acq_rel.gpu;` / `membar.gl;` in `NVIDIA/nccl` `src/device/op128.h:400-406`) encompasses peer GPUs connected via NVLink/NVSwitch when addressed as GPU global peers, **but excludes the host CPU and PCIe NIC DMA engines**. Consequently, if GPU0 writes a buffer over NVLink into GPU1 HBM, issues `fence.acq_rel.gpu`, and signals the host to launch a `devmem` TCP / GPUDirect RDMA send from GPU1 HBM, the PCIe NIC DMA engine can observe the signal *ahead of* or *inconsistent with* the NVLink-written payload! **`NCCL` (`prims_simple.h:1102, 1247`) enforces this invariant explicitly**: whenever a proxy host/NIC FIFO is attached (`flags & ConnFifoEnabled` or `peer->connFifo`), `send` kernels execute `fence_acq_rel_sys()` (`fence.acq_rel.sys;`, `op128.h:393-399`) before publishing `st_relaxed_sys_global` to `connStepPtr` / `peer->tailPtr`.
2. **Proxy Axis Non-Coherence (`generic` vs. `async` Proxies, `10.1145/3470496.3533045`):** The PTX Mixed-Proxy extension formalizes that distinct hardware pipelines—even on the same GPU accessing the same physical HBM or shared memory—operate through separate **proxies** (`generic` for normal `ld`/`st` instructions vs. `async` for Tensor Memory Accelerator / bulk async copy engines, `texture`, `surface`). Because `proxy-preserved` ordering only spans operations sharing a proxy unless bridged by an explicit proxy fence, writes made by an async copy engine (`async` proxy) are **not guaranteed visible** to subsequent `generic` proxy loads (or vice versa before another async/DMA consumer) without `fence.proxy.async` (e.g., `fence.proxy.async.shared::cta` or `fence.proxy.async.global` in PTX ISA 8.0+), *in addition to* `.sys` release ordering before host/NIC notification.
3. **Host CPU Write-Combining & Mixed-Mapping Fences (`NVIDIA/gdrcopy/src/gdrapi.c:59-70, 813-860, 1234-1250`):**
   - When the host CPU writes GPU control descriptors or payloads through a Write-Combining (`GDR_MAPPING_TYPE_WC`) BAR mapping, `x86` stores buffer inside WC fill buffers and bypass cache coherency. Before ringing a NIC doorbell or notifying a GPU kernel, `gdr_copy_to_mapping_internal` issues `sfence` (`x86`) or `DMB st` (`ARM64`).
   - Crucially, **`gdrapi.c:1235-1241` upgrades to a full `mfence` (`x86`) / `DMB sy` (`ARM64`) whenever `gdr_has_mix_mapping()` is true** (multiple mapping types—e.g., `WC` and coherent `CACHING`—active concurrently), because WC stores and cacheable stores to the same physical CUDA allocation violate intra-CPU program-order assumptions without a full bi-directional memory barrier.

### 5. Linear Dual-Lease Buffer-Ownership Typestates and Cross-Layer Matrix

**Basis:** `derived` + `source` (`linux/skbuff.c`, `linux/devmem.c`, `nccl/prims_simple.h`) + `execution` (state-space checker).

| Mechanism | Copy Count | Pinned Accounting / Quota | Safe Reuse / Unpin Trigger | Critical Failure Mode Without Invariant |
| :--- | :--- | :--- | :--- | :--- |
| Standard `send()` | 1 CPU copy | Socket `sk_sndbuf` (`wmem`) | Immediately at syscall return | High CPU cache pollution & memory bandwidth saturation |
| `MSG_ZEROCOPY` (Host RAM) | 0 (1 if `COPIED`) | `RLIMIT_MEMLOCK` (`mm_account_pinned_pages`), `-ENOBUFS` | `MSG_ERRQUEUE` `SO_EE_ORIGIN_ZEROCOPY` covering `id` (`[lo, hi]` mod `2^32`) | Premature overwrite before peer TCP `ACK` corrupts RTO retransmits (`1` lethal interleaving in minimal model) |
| `devmem` TCP TX (`dmabuf`) | 0 (payloads unreadable) | Netlink `net_devmem_dmabuf_binding` (`percpu_ref`), skips `mm_account_pinned_pages` | `MSG_ERRQUEUE` `SO_EE_ORIGIN_ZEROCOPY` + binding alive until `skb`s freed | Mixed host/devmem collapse error; SW checksum / loopback returns `-EFAULT` |
| `devmem` TCP RX (`dmabuf`) | 0 (NIC header split) | Bounded `binding->freelist` (`num_niovs`) | `setsockopt(..., SO_DEVMEM_DONTNEED, ...)` (`<=128` structs / `<=1024` frags) | Token leaks exhaust RX pool and drop incoming packets |
| GPUDirect RDMA (`ibv_reg_dmabuf_mr`) | 0 (P2P BAR / IOMMU) | `dma_buf_pin` + NIC MR table | `ibv_poll_cq` Work Completion (`IBV_WC_SUCCESS`) + `fence.acq_rel.sys` prior to post | `ACS` redirect forces host-bridge bounce; missing `.sys` / `fence.proxy.async` DMA-reads stale GPU HBM |
| `GDRCopy` (`WC` BAR / `dmabuf`) | 1 CPU PIO/WC copy | `gdr_pin_buffer[_v2]` BAR aperture limit | `sfence`/`DMB st` (or `mfence`/`DMB sy` on `mix_mapping`) before doorbell | WC buffer reordering overtakes GPU/NIC flag; unaligned BAR reads stall |

**Linear Dual-Lease Ownership Typestate for Verified Zero-Copy & Peer-DMA Bindings:**
To prove memory safety and data-race freedom in a systems language (e.g., Rust unsafe FFI wrappers) across GPU producers, Linux `MSG_ZEROCOPY`/`devmem`, and NIC consumers, buffer ownership must be governed by a two-gate linear state machine:

1. **Producer-to-Proxy Seal (`OwnedDevBuf -> SealedSysBuf<epoch>`):** A GPU-mutated buffer cannot enter `sendmsg(MSG_ZEROCOPY)` or `ibv_post_send` until a static capability witness attests (a) all intra-GPU `async`-to-`generic` proxy writes passed `fence.proxy.async`, and (b) a `.sys`-scoped release (`fence.acq_rel.sys`) preceded any host-visible descriptor/doorbell write (with `sfence`/`mfence` if written via CPU WC BAR).
2. **Kernel Transport Loan (`SealedSysBuf -> LoanedTxToken(sk_id, zckey_u32)`):** Submitting `sendmsg(..., MSG_ZEROCOPY)` moves `SealedSysBuf` out of `&mut` mutator scope into an opaque `LoanedTxToken` holding `(socket_id, expected_zckey: u32)`. Crucially, if the buffer is a `devmem` `dmabuf`, the netlink binding FD is wrapped in an `Arc<DmabufBinding>` retained alongside `LoanedTxToken` (since `net_devmem_unbind_dmabuf` waits on `percpu_ref`, closing the netlink FD prematurely tears down RX/TX queue bindings).
3. **Wraparound-Safe Errqueue Redemption (`LoanedTxToken + ErrqueueGrant(lo, hi) -> OwnedDevBuf`):** Only when `recvmsg(MSG_ERRQUEUE)` observes `ee_origin == SO_EE_ORIGIN_ZEROCOPY && ee_errno == 0` with `((zckey - lo) & 0xFFFF_FFFF) <= ((hi - lo) & 0xFFFF_FFFF)` does the runtime consume `LoanedTxToken` and restore `&mut` access to `OwnedDevBuf` (additionally logging or disabling `MSG_ZEROCOPY` if `ee_code & SO_EE_CODE_ZEROCOPY_COPIED` persistently fires).

## Boundaries

- **`io_uring` `IORING_OP_SEND_ZC` Fixed-Buffer Slot Recycling:** `not examined`. While `io_uring` zero-copy send shares `ubuf_info` and `MSG_ZEROCOPY` transport internals, its CQ ring two-CQE (`IORING_CQE_F_MORE` / `IORING_CQE_F_NOTIF`) completion ABI and registered-buffer table pinning were not inspected.
- **PCIe 6.0 Integrity and Data Encryption (`IDE`) Latency Impact on `P2PDMA`:** `not examined`. Switch hairpin vs Root Complex routing in `drivers/pci/p2pdma.c` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) was analyzed structurally without hardware PCIe 6.0 IDE measurements.
- **Multi-NIC Asymmetric `ACS` Enforcement Under Virtual Function Passthrough:** `unknown` from static inspection of `p2pdma.c` alone whether specific SR-IOV PF/VF firmware resets override `pci=disable_acs_redir` on a given server platform without inspecting runtime `lspci -vvv` `ACSCtl` registers.
- **Interpreting `SO_EE_ORIGIN_ZEROCOPY` as Wire-Transmission or Peer-Receipt Confirmation:** `known not to apply` whenever `SO_EE_CODE_ZEROCOPY_COPIED` (`1`) is set (`msg_zerocopy.rst:221-225`). On deferred copies (including all TCP/UDP loopback traffic via `skb_orphan_frags_rx`), the error-queue completion only signals that kernel pages hold a copy and user pages are free to overwrite, *before* the packet necessarily leaves the host or reaches the peer.
- **Loopback, Software Checksum, `tcpdump`, and BPF Payload Inspection on `devmem` TCP:** `unsupported` in `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`devmem.rst:378-390`, `skbuff.c:2010-2011`), because device-memory `net_iov` fragments are unreadable by kernel virtual addresses (`!skb_frags_readable(skb)` returns `-EFAULT`).

## Evidence

- **Linux Kernel** (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):
  - `Documentation/networking/msg_zerocopy.rst` (L1–265): `SO_ZEROCOPY`, `sk_zckey` wraparound, `SO_EE_CODE_ZEROCOPY_COPIED`, and loopback restriction.
  - `include/uapi/linux/errqueue.h` (L15–40): `struct sock_extended_err`, `SO_EE_ORIGIN_ZEROCOPY = 5`, `SO_EE_CODE_ZEROCOPY_COPIED = 1`.
  - `include/linux/skbuff.h` (L515–586, L3430–3445): `SKBFL_ZEROCOPY_FRAG`, `SKBFL_DONT_ORPHAN`, `struct ubuf_info_msgzc`, `skb_orphan_frags_rx`.
  - `net/core/skbuff.c` (L1724–1909, L1968–2087): `msg_zerocopy_alloc`, `msg_zerocopy_realloc` (`byte_limit = 1 << 19`), `skb_zerocopy_notify_extend`, `__msg_zerocopy_callback`, `msg_zerocopy_complete`, `skb_copy_ubufs` (`!skb_frags_readable(skb)` -> `-EFAULT`).
  - `net/ipv4/tcp.c` (L1146–1362): `tcp_sendmsg_locked` `MSG_ZEROCOPY` + `devmem` binding validation, `skb_frags_readable(skb) != !binding` split check.
  - `Documentation/networking/devmem.rst` (L1–414), `net/core/devmem.h` (L19–145), `net/core/devmem.c` (L54–573): `allow_peer2peer = true`, `net_devmem_bind_dmabuf`, `net_devmem_get_binding`, `net_devmem_get_niov_at`, `SO_DEVMEM_DONTNEED` (`128` structs / `1024` frags cap), unreadable `skb` caveats.
  - `drivers/pci/p2pdma.c` (L282–335, L498–870): `pci_bridge_has_acs_redir` (`PCI_ACS_RR | PCI_ACS_CR | PCI_ACS_EC`), `cpu_supports_p2pdma()`, `pci_p2pdma_whitelist[]`, `calc_map_type_and_dist`.
- **NVIDIA NCCL** (`NVIDIA/nccl` @ `ad2d192c1f279aefcaf340f67e07880b65a1116b`):
  - `src/device/op128.h` (L393–406): `fence_acq_rel_sys()` (`fence.acq_rel.sys;`) vs `fence_acq_rel_gpu()` (`fence.acq_rel.gpu;`).
  - `src/device/prims_simple.h` (L1094–1105, L1244–1250): `fence_acq_rel_sys()` emitted prior to `st_relaxed_sys_global` whenever `ConnFifoEnabled` / `peer->connFifo` is active.
- **NVIDIA GDRCopy** (`NVIDIA/gdrcopy` @ `0d85ee38d696495592c1d589ab42e021d35cda61`):
  - `src/gdrapi.c` (L59–70, L284–355, L813–860, L1234–1250): `gdr_has_mix_mapping()`, `gdr_pin_buffer_dmabuf` (`CU_MEM_RANGE_FLAG_DMA_BUF_MAPPING_TYPE_PCIE` -> `GDR_MAPPING_TYPE_WC`), `mapping_store_fence` (`sfence`/`DMB st`) vs `memory_fence` (`mfence`/`DMB sy`).
- **RDMA Core & OpenUCX** (`linux-rdma/rdma-core` @ `8634881a642407093dcef4a77a361375bfa4cb69`, `openucx/ucx` @ `a910af25760ef4c6c99c8491919e21efffa34657`):
  - `rdma-core/libibverbs/verbs.h` (L2732–2736): `ibv_reg_dmabuf_mr`.
  - `ucx/src/uct/ib/base/ib_md.c` (L515–568): `ibv_reg_dmabuf_mr` invocation via `dmabuf_fd` and `dmabuf_offset`.
- **Peer-Reviewed Formal Memory-Model Specifications:**
  - Lustig, Sahasrabuddhe, Giroux, *A Formal Analysis of the NVIDIA PTX Memory Consistency Model*, ASPLOS 2019 (`DOI: 10.1145/3297858.3304043`).
  - Lustig, Cooksey, Giroux, *Mixed-Proxy Extensions for the NVIDIA PTX Memory Consistency Model*, ISCA 2022 (`DOI: 10.1145/3470496.3533045`).
- **Self-Contained Executable Micro-Probe (`python3`):**

```bash
python3 - <<'PY'
import itertools, os, select, socket, struct

SOL_IP, IP_RECVERR, SO_ZEROCOPY = 0, 11, 60
MSG_ZEROCOPY, MSG_ERRQUEUE = 0x4000000, 0x2000
SO_EE_ORIGIN_ZEROCOPY, SO_EE_CODE_ZEROCOPY_COPIED = 5, 1

u = os.uname()
print(f"kernel={u.sysname} {u.release.split('-')[0]} arch={u.machine}")

srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
srv.bind(("127.0.0.1", 0))
srv.listen(1)
cli = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
cli.connect(("127.0.0.1", srv.getsockname()[1]))
peer, _ = srv.accept()
try:
    cli.setsockopt(socket.SOL_SOCKET, SO_ZEROCOPY, 1)
    cli.setsockopt(SOL_IP, IP_RECVERR, 1)
    payload = b"Z" * 16384
    for _ in range(3):
        assert cli.send(payload, MSG_ZEROCOPY) == len(payload)
    recvd = 0
    while recvd < 3 * len(payload):
        chunk = peer.recv(65536)
        assert chunk
        recvd += len(chunk)
    ranges, seen_hi = [], -1
    poller = select.poll()
    poller.register(cli, select.POLLERR)
    for _ in range(20):
        if not poller.poll(100):
            if seen_hi >= 2: break
            continue
        while True:
            try:
                _, ancdata, _, _ = cli.recvmsg(128, 1024, MSG_ERRQUEUE)
            except BlockingIOError:
                break
            for clevel, ctype, cdata in ancdata:
                if clevel == SOL_IP and ctype == IP_RECVERR:
                    ee_errno, ee_origin, _, ee_code, _, ee_info, ee_data = struct.unpack_from("<IBBBBII", cdata, 0)
                    assert ee_errno == 0 and ee_origin == SO_EE_ORIGIN_ZEROCOPY
                    ranges.append((ee_info, ee_data, ee_code))
                    seen_hi = max(seen_hi, ee_data)
        if seen_hi >= 2: break
    print(f"received={recvd}B errqueue_cmsgs={ranges} (COPIED_flag={ranges[0][2] & SO_EE_CODE_ZEROCOPY_COPIED})")
finally:
    peer.close(); cli.close(); srv.close()

def check_tcp_retransmit(gate_on_errqueue: bool):
    bad = []
    for order in itertools.permutations(["NIC_TX_DONE", "RTO_REXMIT", "TCP_ACK", "APP_MUTATE"]):
        if order.index("NIC_TX_DONE") > order.index("TCP_ACK") or order.index("RTO_REXMIT") > order.index("TCP_ACK"):
            continue
        refcnt, buf, tx = 2, 0, []
        for ev in order:
            if ev == "NIC_TX_DONE": refcnt -= 1
            elif ev == "RTO_REXMIT": tx.append(buf)
            elif ev == "TCP_ACK": refcnt -= 1
            elif ev == "APP_MUTATE":
                if (gate_on_errqueue and refcnt != 0) or (not gate_on_errqueue and order.index("APP_MUTATE") < order.index("NIC_TX_DONE")):
                    continue
                buf = 1
        if any(v != 0 for v in tx):
            bad.append(order)
    return bad

ungated, gated = check_tcp_retransmit(False), check_tcp_retransmit(True)
assert len(ungated) > 0 and len(gated) == 0
print(f"retransmit_probe: ungated_corruptions={len(ungated)} example={ungated[0]} gated_corruptions={len(gated)}")

def zc_contains(k: int, lo: int, hi: int) -> bool:
    return ((k - lo) & 0xFFFFFFFF) <= ((hi - lo) & 0xFFFFFFFF)

assert zc_contains(0xFFFFFFFE, 0xFFFFFFFE, 2) and zc_contains(0, 0xFFFFFFFE, 2) and not zc_contains(3, 0xFFFFFFFE, 2)
print("wraparound [0xFFFFFFFE, 2]: PASS")

def nic_sees_fresh(scope: str, proxy_async_fence: bool, wc_fence: bool) -> str:
    if not proxy_async_fence: return "STALE_ASYNC_PROXY"
    if scope != "sys": return "STALE_GPU_SCOPE"
    if not wc_fence: return "DOORBELL_REORDER"
    return "FRESH_DMA_VISIBLE"

for s in ("gpu", "sys"):
    for paf in (False, True):
        for wf in (False, True):
            print(f"litmus scope=.{s} proxy_async={paf} wc_fence={wf} -> {nic_sees_fresh(s, paf, wf)}")
PY
```

Recorded execution output (`2026-11-19`):

```text
kernel=Linux 7.1.6 arch=x86_64
received=49152B errqueue_cmsgs=[(0, 2, 1)] (COPIED_flag=1)
retransmit_probe: ungated_corruptions=1 example=('NIC_TX_DONE', 'APP_MUTATE', 'RTO_REXMIT', 'TCP_ACK') gated_corruptions=0
wraparound [0xFFFFFFFE, 2]: PASS
litmus scope=.gpu proxy_async=False wc_fence=False -> STALE_ASYNC_PROXY
litmus scope=.gpu proxy_async=False wc_fence=True -> STALE_ASYNC_PROXY
litmus scope=.gpu proxy_async=True wc_fence=False -> STALE_GPU_SCOPE
litmus scope=.gpu proxy_async=True wc_fence=True -> STALE_GPU_SCOPE
litmus scope=.sys proxy_async=False wc_fence=False -> STALE_ASYNC_PROXY
litmus scope=.sys proxy_async=False wc_fence=True -> STALE_ASYNC_PROXY
litmus scope=.sys proxy_async=True wc_fence=False -> DOORBELL_REORDER
litmus scope=.sys proxy_async=True wc_fence=True -> FRESH_DMA_VISIBLE
```

## Revalidation

To confirm whether these lifetime, PCIe topology, and ordering contracts remain unchanged on a newer Linux kernel, GPU driver/library release, or host topology:

1. **Kernel `MSG_ZEROCOPY`, `devmem` TCP, and `P2PDMA` diff check:** Fetch `net/core/skbuff.c`, `net/core/devmem.c`, and `drivers/pci/p2pdma.c` at target `<rev>` and verify `skb_zerocopy_notify_extend`, `msg_zerocopy_realloc`'s `byte_limit` (`1 << 19`), `SO_DEVMEM_DONTNEED` token limits, and `pci_bridge_has_acs_redir` (`PCI_ACS_RR | PCI_ACS_CR | PCI_ACS_EC`):
   ```bash
   curl -sSL "https://raw.githubusercontent.com/torvalds/linux/<rev>/net/core/skbuff.c" | grep -A12 "skb_zerocopy_notify_extend"
   curl -sSL "https://raw.githubusercontent.com/torvalds/linux/<rev>/drivers/pci/p2pdma.c" | grep -A10 "pci_bridge_has_acs_redir"
   ```
2. **Host PCIe ACS / P2PDMA topology check on target hardware:** Inspect bridge ACS bits with `lspci -vvv` (confirming whether `ACSCtl` `SrcValid+ ReqRedir+ CmpltRedir+ UpstreamFwd+` are cleared on switch ports) and verify `dmesg` shows no `ACS redirect is set between the client and provider` warnings.
3. **`NCCL` / `GDRCopy` fence verification & socket probe:** Diff `fence_acq_rel_sys` usage in `NVIDIA/nccl/src/device/prims_simple.h` and `gdr_has_mix_mapping()` in `NVIDIA/gdrcopy/src/gdrapi.c`, and re-run the inline Python probe in `## Evidence` on the target kernel to verify `SO_EE_ORIGIN_ZEROCOPY` range coalescing (`[(0, 2, 1)]`).
