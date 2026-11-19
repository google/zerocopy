# AF_XDP UMEM Shared-Ring TOCTOU, Multi-Buffer XDP Scatter-Gather Slicing, and RFC 1624 Checksum Offload Traps

## Summary

High-speed Linux packet processing across `XDP` (eXpress Data Path) and `AF_XDP` (`XSK`) zero-copy sockets achieves multi-million-packet-per-second per-core throughput by eliminating per-packet `sk_buff` allocations, kernel-to-user payload copies, and per-packet system calls (`Basis: documentation, source`). That throughput rests on three low-level invariants spanning shared DMA memory, scatter-gather buffer topology, and finite-ring arithmetic—each of which fails silently or catastrophically when abstracted naively:

1. **`AF_XDP` `UMEM` Lockless Ring Ordering, Double-Fetch TOCTOU, and Frame Aliasing (`Basis: source, execution, derived`)**: `AF_XDP` registers a contiguous user-space memory arena (`UMEM`) partitioned into chunks (`2048` or `4096` bytes aligned, or arbitrary offsets under `XDP_UMEM_UNALIGNED_CHUNK_FLAG`) and coordinates ownership across four single-producer/single-consumer (`SPSC`) `mmap`-shared rings (`FILL`, `COMPLETION`, `RX`, `TX`). Because user threads retain writable mappings to `FILL` and `TX` descriptor rings while the kernel consumes them, the kernel (`net/xdp/xsk_queue.h:249-318`) must copy each `struct xdp_desc { __u64 addr; __u32 len; __u32 options; }` once into kernel-private memory after an acquire load on `producer` before running `xp_aligned_validate_desc` / `xp_unaligned_validate_desc`; validating fields in place and re-reading `ring->desc[idx]` creates a classic shared-DMA double-fetch time-of-check-to-time-of-use (`TOCTOU`) vulnerability. Conversely, user-space libraries (`libxdp`, Rust bindings) do not prevent a buggy user allocator from enqueuing the same `UMEM` chunk simultaneously on `FILL` (authorizing NIC RX DMA writes) and `TX` (authorizing NIC TX DMA reads), causing silent wire-data corruption without kernel faults.
2. **Multi-Buffer `XDP` (`XDP_FLAGS_HAS_FRAGS` / `BPF_F_XDP_HAS_FRAGS`) Scatter-Gather Slicing and Pointer Invalidation (`Basis: source, execution`)**: Jumbo frames, TSO/GRO segments, and multi-descriptor `AF_XDP` frames (`XDP_PKT_CONTD`) split packet bytes across a linear head buffer (`[xdp->data, xdp->data_end)`) and up to `MAX_SKB_FRAGS` paged fragments stored in `struct skb_shared_info` at `xdp_data_hard_end(xdp)`. Direct eBPF pointer checks (`ptr + sizeof(hdr) <= data_end`) inspect only the linear head segment, silently dropping or misparsing headers or payloads that straddle a fragment boundary unless accessed via `bpf_xdp_load_bytes` / `bpf_xdp_store_bytes` (`net/core/filter.c:4272-4405`) or `bpf_dynptr_from_xdp`. Furthermore, `bpf_helper_changes_pkt_data` (`net/core/filter.c:8525-8556`) marks `bpf_xdp_adjust_head`, `bpf_xdp_adjust_meta`, `bpf_xdp_adjust_tail`, and `bpf_tail_call` as packet-pointer-invalidating helpers, forcing the eBPF verifier to erase all live packet-pointer provenance across every header push/pop or tail resize.
3. **`RFC 1624` One's-Complement Incremental Checksum vs. `RFC 1141`, UDP `0x0000 -> 0xFFFF` Mangling, and `CHECKSUM_COMPLETE` Stale Metadata (`Basis: normative, source, execution`)**: One's-complement addition modulo $2^{16}-1$ possesses two representations of zero: `+0` (`0x0000`) and `-0` (`0xFFFF`). The obsolete `RFC 1141` incremental formula $HC' = HC + m + \sim m'$ emits `-0` (`0xFFFF`) whenever the updated header sum equals `0xFFFF`, whereas `RFC 1624` Equation 3, $HC' = \sim(\sim HC + \sim m + m')$, matches full recomputation (`0x0000`) across all $65{,}536$ 16-bit word transitions (`Basis: normative, execution`). However, UDP (`RFC 768`, `RFC 1624` §5) assigns `0x0000` the out-of-band meaning *"no checksum computed"*: an incremental L4 updater (`bpf_l4_csum_replace` in `net/core/filter.c:2000-2041` and Cilium's XDP `l4_csum_replace` in `bpf/include/bpf/ctx/xdp.h:200-240` with `BPF_F_MARK_MANGLED_0`) must both leave an incoming `0x0000` UDP checksum untouched (`!*sum -> return 0`) and rewrite a newly computed `0x0000` result to `CSUM_MANGLED_0` (`0xFFFF`). Independently, when NIC RX hardware populates `CHECKSUM_COMPLETE` over the wire Ethernet payload and an `XDP_PASS` program mutates or strips outer headers (`bpf_xdp_adjust_head`), passing an unadjusted hardware checksum into `sk_buff` causes false L4 checksum drops in the kernel stack.

## Applicability

This report applies to zero-copy packet I/O engines, eBPF/XDP L4 load balancers, NAT64/tunnel decapsulators, user-space network stacks, and static verification or capability type systems modeling DMA ownership, non-contiguous packet views, and modular network arithmetic (`Basis: derived`).

- **Systems and Verification Tooling**: Any safe Rust wrapper or verifier targeting `AF_XDP` (`UMEM` slab allocators, `xsk-rs`/`libxdp` bindings) or eBPF/XDP (`aya-ebpf`, Cilium datapath programs) must distinguish kernel memory safety (guaranteed by `xsk_queue.h` single-fetch validation and the eBPF verifier) from protocol and DMA-aliasing soundness (which neither `libxdp` nor the eBPF verifier checks).
- **Performance and Footprint Hierarchy (`L1`–`L6`)**: These invariants sit directly on the `14.88 Mpps` (`67.2 ns` at `10 GbE`) to `148.8 Mpps` (`6.72 ns` at `100 GbE`) per-packet critical path, where a single cache-line bounce, branch misprediction, or `sk_buff` fallback destroys line-rate forwarding (`Basis: documentation, derived`).
- **Human Comprehensibility and Core-Model Simplicity (`C1`–`C2`)**: Exposing raw ring indices, manual `smp_rmb`/`smp_wmb` barriers, implicit `data_end` invalidation, and ad-hoc `0xFFFF` flags forces systems engineers to juggle four coupled failure modes simultaneously; factoring them into linear DMA capabilities, segmented packet cursors, and typed one's-complement checksum states collapses accidental API surface without runtime overhead (`Basis: derived`).

## Findings

### 1. `AF_XDP` `UMEM` Ring Ordering, Single-Fetch Validation, and Frame Aliasing

#### 1.1 Four-Ring `SPSC` Architecture and Cache-Line Isolation
**Basis: `source, documentation`**

In `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `include/uapi/linux/if_xdp.h:67-185` and `net/xdp/xsk_queue.h:16-54`) and Høiland-Jørgensen et al. (`DOI: 10.1145/3281411.3281443`, ACM CoNEXT 2018), an `AF_XDP` socket binds a user-allocated `UMEM` region (`XDP_UMEM_REG`) to a netdev queue (`ifindex`, `queue_id`) via four power-of-two circular rings mapped across the user/kernel boundary:

| Ring | Producer | Consumer | Entry Type | Wire / Ownership Transfer |
| :--- | :--- | :--- | :--- | :--- |
| `FILL` | User space | Kernel / NIC RX | `__u64` base/offset | User lends empty `UMEM` frame to kernel for RX DMA |
| `RX` | Kernel / NIC RX | User space | `struct xdp_desc` | Kernel hands received packet (`addr`, `len`, `options`) to user |
| `TX` | User space | Kernel / NIC TX | `struct xdp_desc` | User submits populated `UMEM` frame (`addr`, `len`, `options`) for TX DMA |
| `COMPLETION` | Kernel / NIC TX | User space | `__u64` base/offset | Kernel returns transmitted `UMEM` frame to user after TX DMA completes |

In `net/xdp/xsk_queue.h:16-26`, `struct xdp_ring` separates `producer`, `consumer`, and `flags` onto distinct SMP cache lines (`____cacheline_aligned_in_smp`) with explicit padding words (`pad1`, `pad2`, `pad3`) specifically to defeat hardware adjacent-cache-line prefetchers from pulling `consumer` into exclusive state when `producer` is updated (`Basis: source`). On the user-space side (`xdp-project/xdp-tools` @ `db6858ff0b18c2b73e5c8c71cad2f92abaaf32ff`, `headers/xdp/xsk.h:33-171`), `struct xsk_ring_prod` and `struct xsk_ring_cons` maintain thread-local `cached_prod` and `cached_cons` shadows (biasing `prod->cached_cons` by `+ r->size` at `xsk.h:106-107` to save an addition on the fast path) and synchronize shared indices strictly with `__atomic_load_n(..., __ATOMIC_ACQUIRE)` (`xsk.h:106, 117`) and `__atomic_store_n(..., __ATOMIC_RELEASE)` (`xsk.h:145, 170`). Notably, `libbpf/libbpf` (`4f05fb027a08a8a66d03916cf6a68a91e2c720ea`) deprecated and removed its legacy `xsk.h` user-space ring helpers in `libbpf 1.0`, consolidating canonical user-space `AF_XDP` ring management in `libxdp` (`xdp-tools`) (`Basis: source, documentation`).

#### 1.2 Shared-`mmap` Double-Fetch TOCTOU vs. Copy-Then-Validate Discipline
**Basis: `source, execution`**

Because `struct xdp_rxtx_ring` (`net/xdp/xsk_queue.h:29-32`) and `struct xdp_umem_ring` (`xsk_queue.h:35-38`) remain writable in user virtual memory while the kernel TX/FILL consumer executes on another CPU core, every field inside `ring->desc[idx]` is untrusted, concurrently mutable shared memory (`Basis: source`).

If a kernel consumer validated `ring->desc[idx].addr` and `ring->desc[idx].len` directly in place and subsequently re-read `ring->desc[idx]` to program a NIC TX DMA descriptor, a concurrent user thread could mutate `len` from `64` to `8192` or `addr` past `pool->addrs_cnt` between check and use (`TOCTOU`), triggering out-of-bounds kernel/IOMMU DMA reads or arbitrary page disclosure (`Basis: execution, derived`). Linux closes this window in `xskq_cons_read_desc` (`net/xdp/xsk_queue.h:249-263`) and `xskq_cons_read_desc_batch` (`xsk_queue.h:278-320`):

1. After observing `q->cached_prod` via an acquire barrier (`smp_rmb()` pairing with user `STORE.rel ->producer`, documented at `xsk_queue.h:79-98`), line `257` copies the entire `16`-byte descriptor by value into a kernel stack local (`*desc = ring->desc[idx];`, or `descs[nb_entries] = ring->desc[idx];` at line `294`).
2. `xskq_cons_is_valid_desc` (`xsk_queue.h:238-247`) then validates exclusively that local snapshot via `xp_aligned_validate_desc` (`xsk_queue.h:159-189`) or `xp_unaligned_validate_desc` (`xsk_queue.h:191-224`):
   - Rejects `len == 0` (`xsk_queue.h:165, 197`).
   - Uses `check_sub_overflow(desc->addr, pool->tx_metadata_len, &addr)` (`xsk_queue.h:169, 206`) so a small `desc->addr < tx_metadata_len` cannot wrap `u64` underflow past `addrs_cnt`.
   - In aligned mode, verifies `(addr & (pool->chunk_size - 1)) + len + pool->tx_metadata_len <= pool->chunk_size` and `addr < pool->addrs_cnt` (`xsk_queue.h:172-183`).
   - In unaligned mode (`XDP_UMEM_UNALIGNED_CHUNK_FLAG`, where the upper 16 bits of `addr` encode an offset added via `xp_unaligned_add_offset_to_addr`), verifies `check_add_overflow(addr, len, &end)`, `end <= pool->addrs_cnt`, and `!xp_desc_crosses_non_contig_pg(pool, addr, len)` so a DMA transfer never crosses two physically non-contiguous pages (`xsk_queue.h:206-218`).
   - Rejects unknown option bits via `xp_unused_options_set`: `options & ~(XDP_PKT_CONTD | XDP_TX_METADATA)` (`xsk_queue.h:154-157`).

#### 1.3 Unchecked User-Space `UMEM` Frame Aliasing and Ownership Races
**Basis: `source, execution, derived`**

While `xp_validate_desc` protects the **kernel** from out-of-bounds `UMEM` descriptors, the kernel intentionally avoids maintaining a per-chunk ownership bitmap on the `AF_XDP` zero-copy fast path (`net/xdp/xsk_queue.h:136-263`, `net/xdp/xsk.c`). Consequently, **nothing in the kernel or `libxdp` (`headers/xdp/xsk.h`) prevents user space from aliasing a single `UMEM` chunk across multiple active rings or descriptors (`Basis: source, derived`)**:

- **Cross-Ring `FILL` + `TX` Race**: Submitting chunk `0x1000` to `FILL` hands write ownership to the NIC RX DMA engine, while simultaneously submitting `XdpDesc { addr: 0x1040, len: 128 }` to `TX` hands read ownership of the same 4 KiB frame to the NIC TX DMA engine. Incoming packets overwrite outgoing TX headers mid-DMA, transmitting torn frames whose wire payload differs from any checksummed buffer.
- **Duplicate `FILL` Submission**: Enqueuing chunk `0x2000` twice in `FILL` allows two back-to-back RX packets to DMA into the same `UMEM` frame; two `RX` ring descriptors then point to `0x2000`, silently clobbering the earlier packet while user space parses it.
- **Premature Reuse Before `COMPLETION`**: Modifying a `TX` chunk after `xsk_ring_prod__submit(&tx, 1)` (`libxdp/xsk.h:140-146`) before its base address reappears on `COMPLETION` (`xsk_ring_cons__comp_addr`, `libxdp/xsk.h:64-69`) mutates live TX DMA payload in flight.

In a safe systems language, a `UMEM` chunk is therefore not a shareable integer offset `__u64`; it is an **affine DMA token** transitioning through a strict typestate cycle:
$$\text{UserOwned} \xrightarrow{\text{fill\_submit}} \text{NicRxDma} \xrightarrow{\text{rx\_peek}} \text{UserOwned} \xrightarrow{\text{tx\_submit}} \text{NicTxDma} \xrightarrow{\text{comp\_peek}} \text{UserOwned}$$

---

### 2. Multi-Buffer `XDP` (`XDP_FLAGS_HAS_FRAGS`) Scatter-Gather Topology and Verifier Erasure

#### 2.1 Linear Head vs. `skb_shared_info` Paged Fragments
**Basis: `source, execution`**

Classic `XDP` required every Ethernet frame to reside inside a single physically contiguous linear page (`<= 3.5 KiB` after `xdp_frame` headroom and `skb_shared_info` tailroom), precluding `MTU 9000` jumbo frames and GRO/LRO coalesced segments (`Basis: documentation, source`). Multi-buffer `XDP` (`torvalds/linux` `include/net/xdp.h:74-127`, `BPF_F_XDP_HAS_FRAGS` / `xdp.frags` ELF section) sets `XDP_FLAGS_HAS_FRAGS = BIT(0)` in `xdp_buff->flags`:

- `xdp->data` through `xdp->data_end` (`aya-rs/aya` @ `44a6709164d2ac0c19c7845101e7b033e25b3f3f`, `ebpf/aya-ebpf/src/programs/xdp.rs:15-23`) still bounds **only the first linear head buffer**, *not* the full packet length (`Basis: source`).
- Trailing payload bytes reside in `sinfo = xdp_get_shared_info_from_buff(xdp)` (`sinfo->frags[0 .. sinfo->nr_frags)`), located at `xdp_data_hard_end(xdp)` (`net/core/filter.c:4273-4295`). Total wire length requires calling `bpf_xdp_get_buff_len(ctx)` rather than `ctx->data_end - ctx->data`.
- When redirected into an `AF_XDP` socket, multi-buffer frames span multiple consecutive `RX` or `TX` descriptors linked by `XDP_PKT_CONTD = (1 << 0)` in `xdp_desc.options` (`include/uapi/linux/if_xdp.h:180`). Every non-terminal fragment carries `options & XDP_PKT_CONTD != 0`, and the final fragment clears `XDP_PKT_CONTD`. In `xskq_cons_read_desc_batch` (`net/xdp/xsk_queue.h:278-318`), if *any* fragment in a multi-buffer chain fails validation (`!parsed.valid`) or exceeds `pool->xdp_zc_max_segs` (`line 316`), the kernel sets `drain = true` (`xs->drain_cont`), discarding the entire multi-descriptor packet atomically into `batch.reclaim_descs` so partial torn frames are never transmitted (`Basis: source`).

#### 2.2 Cross-Fragment Header Traps and Packet-Pointer Invalidation
**Basis: `source, execution`**

Two subtle verifier and runtime failure modes arise when XDP programs process multi-buffer or encapsulated traffic:

1. **Silent Cross-Fragment Drop under Direct Pointer Slicing**: An eBPF program attached with `BPF_F_XDP_HAS_FRAGS` that checks `if ((void *)(hdr + 1) > data_end) return XDP_DROP;` (or `XDP_PASS`) succeeds whenever `hdr` fits inside the linear head buffer, but **fails whenever variable-length IPv6 extension headers, Geneve TLVs, or deep L7 headers push `hdr + 1` across `data_end` into `sinfo->frags[0]`**, even though the packet is completely valid and truncated nowhere (`Basis: source, execution`). Reading or mutating cross-fragment ranges requires `bpf_xdp_load_bytes` / `bpf_xdp_store_bytes` (`net/core/filter.c:4351-4405`), which fast-paths `xdp->data_end - xdp->data >= off + len` via `bpf_xdp_pointer` / `memcpy` (`filter.c:4281-4286`) and falls back to walking `sinfo->frags[]` in `bpf_xdp_copy_buf` (`filter.c:4288-4315`), or `bpf_dynptr_from_xdp` + `bpf_dynptr_slice` / `bpf_dynptr_slice_rdwr`.
2. **Global Verifier Erasure Across `bpf_xdp_adjust_{head,meta,tail}`**: In `net/core/filter.c:8525-8556`, `bpf_helper_changes_pkt_data` returns `true` for `BPF_FUNC_xdp_adjust_head`, `BPF_FUNC_xdp_adjust_meta`, `BPF_FUNC_xdp_adjust_tail`, and `BPF_FUNC_tail_call`. Upon seeing any of these calls, the kernel eBPF verifier invokes `clear_all_pkt_pointers`, turning every previously bounds-checked `PTR_TO_PACKET` register into `SCALAR_VALUE` (`UNKNOWN`) and requiring complete reloading of `ctx->data` and `ctx->data_end` plus fresh `ptr + K <= data_end` dominance proofs. Note also two runtime asymmetries in `filter.c`:
   - `bpf_xdp_adjust_head` (`filter.c:4244-4262`) shifts **only** the linear head pointer (`xdp->data += offset`, `memmove`ing `xdp->data_meta` if `metalen > 0`) and fails with `-EINVAL` if `data > xdp->data_end - ETH_HLEN`—it cannot pull bytes out of `sinfo->frags[0]` if an outer tunnel header spans the head/frag boundary (`Basis: source`).
   - `bpf_xdp_adjust_tail` (`filter.c:4512-4538`) branches on `xdp_buff_has_frags(xdp)` (`line 4517`), delegating to `bpf_xdp_frags_shrink_tail` (which unmaps/frees trailing page frags when shrinking across fragment boundaries) or `bpf_xdp_frags_increase_tail` (growing only within tailroom of the final frag), and explicitly `memset`s newly exposed tail bytes to zero (`line 4533`) to prevent leaking uninitialized kernel page-pool memory onto the wire (`Basis: source`).

---

### 3. `RFC 1624` Incremental Checksums, UDP `0x0000 -> 0xFFFF`, and Hardware Offload Traps

#### 3.1 Algebraic Defect in `RFC 1141` vs. `RFC 1624` Equation 3
**Basis: `normative, source, execution`**

Internet headers (`IPv4` `RFC 791`, `TCP` `RFC 9293`, `UDP` `RFC 768`, `ICMPv6` `RFC 4443`) compute a 16-bit one's-complement checksum by summing 16-bit big-endian words with end-around carry (arithmetic in $\mathbb{Z}/(2^{16}-1)\mathbb{Z}$) and taking the bitwise one's complement `~S`. Because $2^{16}-1 = \text{0xFFFF} \equiv 0 \pmod{65535}$, the ring has two encodings of the additive identity: `+0 = 0x0000` and `-0 = 0xFFFF`. Standard full recomputation (`csum = ~sum`) folds all non-zero carries into `1 .. 0xFFFF` before complementing, so `~0xFFFF = 0x0000`, and for an all-zero word vector (impossible in valid IPv4 headers due to `version = 4` and non-zero `TTL`, and impossible in valid TCP/UDP pseudo-headers due to non-zero protocol/length) `~0x0000 = 0xFFFF`. Thus **any valid packet with non-zero sum produces `0x0000`, never `0xFFFF`, when its complement is `0` (`Basis: normative, execution`)**.

When an XDP load balancer or NAT rewrites one 16-bit header word $m \to m'$, recomputing over the whole payload is $O(N)$ and breaks zero-copy line rate. `RFC 1141` proposed $HC' = HC + m + \sim m'$, which preserves congruence modulo $65535$ **but produces `0xFFFF` (`-0`) instead of `0x0000` (`+0`) whenever $\sim HC + \sim m + m' \equiv \text{0xFFFF}$** (`Basis: normative, execution`). Strict receivers or hardware offloads checking explicit field equality against `0x0000` or misinterpreting `0xFFFF` fail.

`RFC 1624` (§3, Equation 3) fixes this unconditionally across all $65{,}536$ word values:
$$HC' = \sim(\sim HC + \sim m + m')$$
Because the inner one's-complement addition $\sim HC + \sim m + m'$ produces `0xFFFF` (never `0x0000`, unless every addend is `0x0000`), the outer bitwise negation `~` maps `0xFFFF` cleanly to `0x0000`. Cilium's XDP datapath (`cilium/cilium` @ `71947297d7c3a2b5659e06d7e86c434e4af3c951`, `bpf/include/bpf/ctx/xdp.h:154-164`) implements this exact `RFC 1624` equation in eBPF:

```c
static __always_inline __maybe_unused void
__csum_replace_by_diff(__sum16 *sum, __wsum diff)
{
    *sum = csum_fold(csum_add(diff, ~csum_unfold(*sum)));
}
```
where `diff = csum_add(~from, to)` (`ctx/xdp.h:163`) or `bpf_csum_diff` (`net/core/filter.c:2054-2078`). Exhaustive execution across $4 \times 65{,}536 = 262{,}144$ transitions confirms zero discrepancies between `RFC 1624` and full packet recomputation, whereas `RFC 1141` emits `0xFFFF` on every zero-checksum boundary (`Basis: execution`).

#### 3.2 The Dual UDP `0x0000` / `0xFFFF` Trap (`BPF_F_MARK_MANGLED_0` / `CSUM_MANGLED_0`)
**Basis: `normative, source, execution`**

UDP (`RFC 768`, `RFC 1624` §5, `RFC 8200` §8.1 for IPv6 where UDP checksums are mandatory except specific tunnel exceptions in `RFC 6935`) overloads checksum value `0x0000` to mean **"transmitter generated no checksum"**:

1. **Outbound `0x0000 -> 0xFFFF` Substitution**: If a valid UDP checksum calculation (full or incremental `RFC 1624`) evaluates to `0x0000` (`+0`), writing `0x0000` into `udphdr->check` either strips checksum protection on IPv4 or causes **unconditional packet drop on IPv6** (`RFC 8200` requires receivers to discard IPv6 UDP packets with `check == 0`). The stack must substitute `CSUM_MANGLED_0 = 0xFFFF` (`-0`). Crucially, if a downstream hop performs *another* `RFC 1624` incremental update starting from `HC = 0xFFFF`, `~HC = 0x0000`, which is algebraically identical to `~0x0000 = 0xFFFF` in $\mathbb{Z}/(2^{16}-1)\mathbb{Z}$ (`0x0000 + x == 0xFFFF + x` for any non-zero `x`), so subsequent incremental updates remain exact (`Basis: execution, derived`)!
2. **Inbound `0x0000` Preservation**: Conversely, if an IPv4 UDP packet arrives with `udphdr->check == 0x0000` (no checksum), applying `RFC 1624` on a NAT port/IP rewrite (`m -> m'`) turns `0x0000` into a *non-zero garbage checksum* covering only the delta `m' - m`, causing the destination host to drop the packet for bad UDP checksum!

Both Linux's TC helper `bpf_l4_csum_replace` (`net/core/filter.c:2004, 2018-2019, 2038-2039`) and Cilium's XDP implementation (`bpf/lib/csum.h:37-40` + `bpf/include/bpf/ctx/xdp.h:200-240`) guard both directions via `BPF_F_MARK_MANGLED_0`:
- Pre-check (`ctx/xdp.h:232-233`, `filter.c:2018-2019`): `if (is_mmzero && !*sum) return 0;` — leaves unchecksummed IPv4 UDP `0x0000` untouched unless `BPF_F_MARK_ENFORCE` is set.
- Post-check (`ctx/xdp.h:236-237`, `filter.c:2038-2039`): `if (is_mmzero && !*sum) *sum = CSUM_MANGLED_0;` — rewrites newly computed `0x0000` to `0xFFFF`.
- Protocol asymmetry (`bpf/lib/csum.h:33-58`): TCP and ICMPv6 do **not** set `BPF_F_MARK_MANGLED_0` (`0x0000` is a normal valid checksum in TCP/ICMPv6), while SCTP uses CRC-32c (`RFC 4960`) over only the SCTP header + chunks (ignoring L3 pseudo-headers, so pure L3 NAT needs no L4 update, whereas L4 port NAT cannot use one's-complement `csum_diff` at all).

#### 3.3 Hardware RX `CHECKSUM_COMPLETE` Desynchronization Across XDP Mutations
**Basis: `source, execution, derived`**

Unlike TC (`struct __sk_buff`), XDP executes *before* `sk_buff` allocation and therefore has no `bpf_l3_csum_replace`, `bpf_l4_csum_replace`, or `bpf_csum_update` kernel helpers (`cilium/cilium` `bpf/include/bpf/ctx/xdp.h:242-251` explicitly implements `csum_update` as a no-op comment noting no `sk_buff` exists yet). When an `XDP_PASS` program strips an outer VLAN/VXLAN/Geneve header via `bpf_xdp_adjust_head` or rewrites L3/L4 fields in place, any 16-bit whole-frame sum cached by the NIC in its RX descriptor (`CHECKSUM_COMPLETE`) still includes the *old* pre-XDP bytes (`Basis: source, execution`). Unless the NIC driver either updates the hardware csum across `bpf_xdp_adjust_head` / payload edits or downgrades `skb->ip_summed` to `CHECKSUM_NONE` when building the `sk_buff` after `XDP_PASS`, the kernel TCP/UDP stack validates `skb->csum` against the mutated inner packet and silently increments `InCsumErrors` (`Basis: execution, derived`). Conversely, on `AF_XDP` TX (`XDP_TX_METADATA`, `include/uapi/linux/if_xdp.h:183`), requesting hardware TX L4 checksum offload requires user space to pre-seed `udphdr->check` / `tcphdr->check` with the **uncomplemented** L3 pseudo-header one's-complement sum (`csum_tcpudp_nofold`), *not* `0x0000` and *not* the complemented checksum (`Basis: source, documentation`).

---

### 4. Multi-Level Performance/Footprint (`L1`–`L6`) and Comprehensibility/Simplicity (`C1`–`C2`) Analysis

#### 4.1 `L1`–`L6` Hardware-Software Performance and Footprint Matrix
**Basis: `source, documentation, derived`**

| Level | Subsystem Dimension | Fast-Path Mechanism & Quantitative Cost | Trap / Fallback Penalty |
| :--- | :--- | :--- | :--- |
| **`L1`** | CPU Instruction & Branch Pipeline | Single-fetch `struct xdp_desc` load (`16 B`, 2 `MOV`s) + branchless mask `idx & ring_mask` + inline `RFC 1624` `csum_fold` (~6–10 ALU ops); Cilium inline BPF asm (`ctx/xdp.h:180-193`) bounds-checks `off` in 8 instructions without helper call overhead. | Verifier erasure on `bpf_xdp_adjust_head` forces full header pointer re-derivation; full payload checksum recomputation scales at ~0.5–1.0 cycle/byte (~750–1500 cycles on `1500 B` MTU vs. ~8 cycles incremental). |
| **`L2`** | Cache Hierarchy (`L1d`/`L2`/`LLC`) & DDIO | `UMEM` frames (`2 KiB`/`4 KiB`) stay warm in `L3` via PCIe DDIO/TPH; `____cacheline_aligned_in_smp` + `pad1..pad3` in `struct xdp_ring` (`xsk_queue.h:16-26`) prevents adjacent-line prefetcher false sharing between producer and consumer cores; batched `cached_prod`/`cached_cons` amortizes cross-core `MESI` invalidations to `1` per `32–64` packets. | Updating shared `*producer` on every single packet triggers a cross-core `L1d` RFO miss (~40–80 ns), cutting `AF_XDP` throughput by 3x–6x. |
| **`L3`** | Allocator, Syscall & Kernel Crossing | Zero per-packet allocations (`UMEM` slab pre-pinned once via `XDP_UMEM_REG`); `XDP_USE_NEED_WAKEUP` (`XDP_RING_NEED_WAKEUP`, `libxdp/xsk.h:87-90`) eliminates `sendto()`/`poll()` syscalls entirely while the NAPI busy/softirq loop stays active. | Falling back from `XDP_ZEROCOPY` to `XDP_COPY` or `SKB` mode allocates `sk_buff` + copies `1500–9000 B` per packet, dropping single-core throughput from ~14–22 Mpps to ~2–4 Mpps. |
| **`L4`** | Memory Layout & Multi-Buffer Footprint | Aligned `4096 B` `UMEM` chunks enable single-AND `addr & (chunk_size - 1)` validation (`xsk_queue.h:172`); `XDP_UMEM_UNALIGNED_CHUNK_FLAG` packs `2048 B` or `1536 B` MTU frames densely without internal fragmentation (`xsk_queue.h:191-224`); `XDP_FLAGS_HAS_FRAGS` chains `4 KiB` page-pool frags for `9000 B` jumbo frames without order-2 page allocation stalls. | Cross-fragment `bpf_xdp_load_bytes` copies stack bounce buffers (`filter.c:4272-4315`) when headers straddle `data_end` rather than fitting in the linear head. |
| **`L5`** | NIC DMA, PCIe & Offload Co-Design | NIC RX/TX rings DMA directly into/out of `UMEM` physical pages mapped once in the IOMMU (`MEM_TYPE_XSK_BUFF_POOL`, `include/net/xdp.h:47`); `XDP_PKT_CONTD` maps multi-descriptor scatter-gather chains directly to hardware `Scatter/Gather` descriptors. | `UMEM` `FILL`/`TX` aliasing causes silent PCIe read/write races on the same physical RAM cache line; stale RX `CHECKSUM_COMPLETE` causes software L4 drops downstream. |
| **`L6`** | Operational Observability & Tail Latency | `xsk_queue.h:46-47` exports monotonic `invalid_descs` and `queue_empty_descs` via `XDP_STATISTICS` (`getsockopt`), isolating malformed descriptor drops from `FILL`-ring starvation without per-packet logging. | Silent `UDP 0x0000` mis-rewrites or cross-frag `data_end` drops increment no kernel error counter inside XDP unless explicitly instrumented by the eBPF program. |

#### 4.2 `C1`–`C2` Human Comprehensibility and Conceptual Simplicity Synthesis
**Basis: `derived, source`**

- **`C1` Cognitive Load Diagnosis (Why Engineers Write Buggy XDP/`AF_XDP` Code)**:
  1. *Untyped `__u64` `UMEM` Addresses*: `libxdp` exposes raw `__u64` offsets for `FILL`, `COMPLETION`, `RX`, and `TX` alike. Nothing in the C or thin-FFI surface distinguishes an empty RX buffer (`FILL`), a received read-only slice (`RX`), an in-flight TX buffer (`TX`), or an unaligned `(offset << 48) | addr` packed word (`libxdp/xsk.h:178-191`).
  2. *Deceptive `data .. data_end` Contiguity Illusion*: Writing `(void *)(tcp + 1) <= data_end` looks like a bounds check against packet length, so developers port linear XDP programs to `xdp.frags` (`BPF_F_XDP_HAS_FRAGS`) unaware that `data_end` silently means *"end of first scatter-gather segment"* rather than *"end of packet"*.
  3. *Three Incompatible Meanings of Checksum `0x0000`*: Across `IPv4`/`TCP` (`0x0000` = valid checksum), `UDP` wire header (`0x0000` = checksum disabled; valid `+0` encoded as `0xFFFF`), and hardware TX offload seed (`csum_start`/`csum_offset` expects uncomplemented pseudo-header sum), a bare `__be16` checksum field conflates three algebraically distinct states.
- **`C2` Minimal Orthogonal Core Abstractions (Zero-Cost Static Elimination)**:
  All three hazard families collapse into **three orthogonal, zero-runtime-overhead compile-time abstractions**:
  1. **Linear `UmemChunk<State>` Typestate Token**: Parameterize chunk handles by ghost state `Free | InFill | RxReady | InTx` (and multi-frag chain head/tail typestate for `XDP_PKT_CONTD`). Moving `UmemChunk<Free>` into `fill.submit()` consumes the handle until `rx.peek()` returns `UmemChunk<RxReady>`, making `FILL`+`TX` aliasing, double-`FILL`, and premature pre-`COMPLETION` mutation unrepresentable in safe code while compiling to the exact `__u64` offset in registers.
  2. **Epoch-Indexed `PacketView<'epoch>` + Segmented Cursor**: Bind every direct packet slice `&'epoch [u8]` to a ghost `'epoch` token consumed by `adjust_head` / `adjust_tail` / `tail_call` (mirroring `bpf_helper_changes_pkt_data` in the host type checker before eBPF verification), and distinguish `LinearHeadSlice<'epoch>` from `PacketCursor` (which lowers to direct load when provably `< MIN_LINEAR_HEAD` and to `bpf_xdp_load_bytes` / `bpf_dynptr_slice` otherwise).
  3. **Algebraic `OnesComp16` vs. `UdpWireCsum` Types**: Separate the ring element `OnesComp16` (supporting only `RFC 1624` `replace_word(old, new)`) from protocol-specific wire encodings (`IpTcpWireCsum` vs. `UdpWireCsum::Disabled | UdpWireCsum::Checked(NonZeroU16)`), enforcing `BPF_F_MARK_MANGLED_0` (`0x0000` skip on input, `0x0000 -> 0xFFFF` on output) and tainting hardware `RxCsumComplete` upon uncompensated `adjust_head`.

## Boundaries

- **`not examined`**: Vendor-specific NIC driver zero-copy `ndo_xsk_wakeup` / descriptor-ring implementations (`mlx5e`, `ice`, `i40e`, `igc`, `bnxt`) and hardware-specific `XDP_TX_METADATA` BTF kfunc layouts (`bpf_xdp_metadata_rx_checksum`) were **not examined** at driver-register level; driver-specific bugs in clearing or adjusting `CHECKSUM_COMPLETE` after `XDP_PASS` vary by NIC driver.
- **`unknown`**: Exact IOMMU IOTLB shootdown latencies when dynamically unmapping `UMEM` regions across multi-socket NUMA PCIe root complexes under concurrent `XDP_ZEROCOPY` traffic remain **unknown** from static source inspection and require hardware-specific benchmarking.
- **`known not to apply`**: `RFC 1624` one's-complement incremental checksum equations are **known not to apply** to `SCTP` (`IPPROTO_SCTP`, `RFC 4960`, which uses CRC-32c; confirmed at `cilium/cilium` `bpf/lib/csum.h:41-55`), `QUIC`/TLS AEAD integrity tags, or Ethernet FCS (`CRC-32`). Similarly, `BPF_F_MARK_MANGLED_0` (`0x0000 -> 0xFFFF`) is **known not to apply** to `IPv4` header checksums, `TCP`, or `ICMPv6`, where `0x0000` is a valid computed wire checksum.
- **`unsupported`**: Calling `bpf_l3_csum_replace`, `bpf_l4_csum_replace`, or `bpf_csum_update` directly as kernel BPF helpers inside `BPF_PROG_TYPE_XDP` programs is **unsupported** by the Linux kernel (`net/core/filter.c` exposes them only to `sk_buff` program types; XDP programs must use `bpf_csum_diff` or inline `RFC 1624` folding as Cilium does in `bpf/include/bpf/ctx/xdp.h:154-240`). Likewise, `bpf_xdp_adjust_head` pulling header bytes across the end of the linear head buffer into `skb_shared_info->frags[0]` is **unsupported** (`filter.c:4251-4253` enforces `data <= xdp->data_end - ETH_HLEN`).

## Evidence

1. **Linux Kernel `AF_XDP` Ring Barriers, Single-Fetch Copy, and Descriptor Validation (`Basis: source`)**:
   - Repository: `https://github.com/torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b`
   - `include/uapi/linux/if_xdp.h:16-185`: Defines `XDP_SHARED_UMEM`, `XDP_COPY`, `XDP_ZEROCOPY`, `XDP_USE_NEED_WAKEUP`, `XDP_UMEM_UNALIGNED_CHUNK_FLAG`, `struct xdp_desc`, `XDP_PKT_CONTD` (`1 << 0`), and `XDP_TX_METADATA` (`1 << 1`).
   - `net/xdp/xsk_queue.h:16-132`: Defines SMP cache-line-padded `struct xdp_ring` (`pad1`, `pad2`, `pad3`) and documents the four-point `(A)`–`(D)` producer/consumer memory-ordering proof.
   - `net/xdp/xsk_queue.h:154-320`: Implements `xp_aligned_validate_desc` (`check_sub_overflow` on `tx_metadata_len`, chunk boundary check), `xp_unaligned_validate_desc` (`xp_desc_crosses_non_contig_pg`), single-fetch snapshot `*desc = ring->desc[idx]` in `xskq_cons_read_desc` (`line 257`), and multi-buffer `XDP_PKT_CONTD` atomic drain recovery (`xs->drain_cont`) in `xskq_cons_read_desc_batch` (`lines 278-318`).
2. **Linux Kernel Multi-Buffer `XDP`, Helper Slicing, and Checksum Primitives (`Basis: source`)**:
   - Repository: `https://github.com/torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b`
   - `include/net/xdp.h:74-127`: Defines `XDP_FLAGS_HAS_FRAGS = BIT(0)` and `struct xdp_buff` (`data`, `data_end`, `data_meta`, `data_hard_start`, `frame_sz`, `flags`).
   - `net/core/filter.c:2000-2102`: Implements `bpf_l4_csum_replace` (`BPF_F_MARK_MANGLED_0` skip at `2018-2019` and `CSUM_MANGLED_0` rewrite at `2038-2039`), `bpf_csum_diff` (`2054-2078`), and `bpf_csum_update` (`2092-2102`).
   - `net/core/filter.c:4244-4565`: Implements `bpf_xdp_adjust_head` (`4244-4262`), `bpf_xdp_copy_buf` walking `skb_shared_info->frags[]` (`4272-4315`), `bpf_xdp_load_bytes` / `bpf_xdp_store_bytes` (`4351-4405`), and multi-buffer-aware `bpf_xdp_adjust_tail` (`4512-4538`).
   - `net/core/filter.c:8525-8556`: `bpf_helper_changes_pkt_data` enumerates `BPF_FUNC_xdp_adjust_head`, `BPF_FUNC_xdp_adjust_meta`, `BPF_FUNC_xdp_adjust_tail`, and `BPF_FUNC_tail_call` for verifier packet-pointer invalidation.
3. **`libxdp`, `libbpf`, `Cilium`, and `Aya` Ecosystem Sources (`Basis: source`)**:
   - `https://github.com/xdp-project/xdp-tools` @ `db6858ff0b18c2b73e5c8c71cad2f92abaaf32ff`: `headers/xdp/xsk.h:33-191` (`xsk_ring_prod__reserve`, `xsk_ring_prod__submit` with `__ATOMIC_RELEASE`, `xsk_ring_cons__peek` with `__ATOMIC_ACQUIRE`, `xsk_umem__extract_addr`/`offset`) and `lib/libxdp/xsk.c`.
   - `https://github.com/libbpf/libbpf` @ `4f05fb027a08a8a66d03916cf6a68a91e2c720ea`: `src/bpf_helper_defs.h` (`bpf_xdp_adjust_head`, `bpf_xdp_load_bytes`, `bpf_xdp_get_buff_len`, `bpf_dynptr_from_xdp`, `BPF_F_XDP_HAS_FRAGS`).
   - `https://github.com/cilium/cilium` @ `71947297d7c3a2b5659e06d7e86c434e4af3c951`: `bpf/lib/csum.h:29-63` (`csum_l4_offset_and_flags` setting `BPF_F_MARK_MANGLED_0` exclusively on `IPPROTO_UDP` and disabling `IPPROTO_SCTP`), `bpf/lib/l4.h:99-149`, and `bpf/include/bpf/ctx/xdp.h:154-251` (`__csum_replace_by_diff`, `CSUM_MANGLED_0 = 0xffff`, `l4_csum_replace`, and XDP `csum_update` no-op rationale).
   - `https://github.com/aya-rs/aya` @ `44a6709164d2ac0c19c7845101e7b033e25b3f3f`: `ebpf/aya-ebpf/src/programs/xdp.rs:1-54` (`XdpContext::data()` and `data_end()` raw `usize` projections over `xdp_md`).
4. **Normative Specifications and Peer-Reviewed Literature (`Basis: normative, documentation`)**:
   - Anil Rijsinghani, *Computation of the Internet Checksum via Incremental Update*, IETF `RFC 1624` (May 1994), superseding `RFC 1141`.
   - Jon Postel, *User Datagram Protocol*, IETF `RFC 768` (August 1980), defining `0x0000` uncomputed checksum semantics and `0xFFFF` all-ones substitution.
   - Toke Høiland-Jørgensen, Jesper Dangaard Brouer, Daniel Borkmann, John Fastabend, Tom Herbert, David Ahern, and David Miller, *The eXpress Data Path: Fast Programmable Packet Processing in the Operating System Kernel*, ACM CoNEXT 2018 (`DOI: 10.1145/3281411.3281443`).
5. **Executable Verification Probe (`Basis: execution`)**:
   The standalone Python 3 probe below exhaustively checks all $4 \times 65{,}536$ 16-bit word transitions comparing `RFC 1624` vs. `RFC 1141` and `BPF_F_MARK_MANGLED_0` UDP semantics, demonstrates stale `CHECKSUM_COMPLETE` failure after XDP VLAN pop, contrasts vulnerable shared-ring double-fetch against Linux's single-copy `xskq_cons_read_desc` + `UMEM` `FILL`/`TX` chunk aliasing, and verifies cross-fragment `bpf_xdp_load_bytes` vs. linear `data_end` rejection:

```python
from dataclasses import dataclass


def ones_comp_add16(a: int, b: int) -> int:
    s = (a & 0xFFFF) + (b & 0xFFFF)
    s = (s & 0xFFFF) + (s >> 16)
    return (s & 0xFFFF) + (s >> 16)


def csum_compute16(words: list[int]) -> int:
    acc = 0
    for w in words:
        acc = ones_comp_add16(acc, w)
    return (~acc) & 0xFFFF


def rfc1141_update(hc: int, m: int, m_prime: int) -> int:
    return ones_comp_add16(ones_comp_add16(hc, m), (~m_prime) & 0xFFFF)


def rfc1624_update(hc: int, m: int, m_prime: int) -> int:
    inv_hc = (~hc) & 0xFFFF
    inv_m = (~m) & 0xFFFF
    acc = ones_comp_add16(ones_comp_add16(inv_hc, inv_m), m_prime & 0xFFFF)
    return (~acc) & 0xFFFF


def udp_l4_csum_replace(hc: int, m: int, m_prime: int, mark_mangled_0: bool = True) -> int:
    if mark_mangled_0 and hc == 0x0000:
        return 0x0000
    hc_prime = rfc1624_update(hc, m, m_prime)
    if mark_mangled_0 and hc_prime == 0x0000:
        return 0xFFFF
    return hc_prime


w0 = 0x5555
rfc1141_neg_zero_bugs = 0
for m in (0x0000, 0x1234, 0xAAAA, 0xFFFF):
    hc = csum_compute16([w0, m])
    for m_prime in range(0x10000):
        expected = csum_compute16([w0, m_prime])
        got_1624 = rfc1624_update(hc, m, m_prime)
        got_1141 = rfc1141_update(hc, m, m_prime)
        assert got_1624 == expected
        assert got_1624 != 0xFFFF
        if got_1141 != expected:
            assert got_1141 == 0xFFFF and expected == 0x0000
            rfc1141_neg_zero_bugs += 1

hc_ex = csum_compute16([0xCD7A, 0x5555])
assert hc_ex == 0xDD2F
assert rfc1624_update(hc_ex, 0x5555, 0x3285) == 0x0000
assert rfc1141_update(hc_ex, 0x5555, 0x3285) == 0xFFFF
assert udp_l4_csum_replace(hc_ex, 0x5555, 0x3285, mark_mangled_0=True) == 0xFFFF
assert udp_l4_csum_replace(0xFFFF, 0x3285, 0x5555, mark_mangled_0=True) == 0xDD2F
assert udp_l4_csum_replace(0x0000, 0x5555, 0x3285, mark_mangled_0=True) == 0x0000
assert rfc1141_neg_zero_bugs == 4

# Stale NIC RX CHECKSUM_COMPLETE after XDP outer VLAN pop
outer_vlan = [0x8100, 0x0064]
inner_pkt = [0x4500, 0x001C, 0xCD7A, 0x3285]
rx_hw_sum = 0
for w in outer_vlan + inner_pkt:
    rx_hw_sum = ones_comp_add16(rx_hw_sum, w)
inner_sum = 0
for w in inner_pkt:
    inner_sum = ones_comp_add16(inner_sum, w)
assert inner_sum != rx_hw_sum


@dataclass
class XdpDesc:
    addr: int
    length: int
    options: int = 0


class SharedMmapTxSlot:
    def __init__(self, benign: XdpDesc, raced: XdpDesc):
        self.benign = benign
        self.raced = raced
        self.reads = 0

    def fetch(self) -> XdpDesc:
        self.reads += 1
        return self.benign if self.reads == 1 else self.raced


def xp_aligned_validate_desc(desc: XdpDesc, umem_len: int = 65536, chunk_size: int = 4096) -> bool:
    if desc.length == 0:
        return False
    offset = desc.addr & (chunk_size - 1)
    if offset + desc.length > chunk_size or desc.addr >= umem_len:
        return False
    return (desc.options & ~0x3) == 0


slot_bad = SharedMmapTxSlot(XdpDesc(4096, 64), XdpDesc(61440, 8192))
assert xp_aligned_validate_desc(slot_bad.fetch()) is True
assert xp_aligned_validate_desc(slot_bad.fetch()) is False

slot_safe = SharedMmapTxSlot(XdpDesc(4096, 64), XdpDesc(61440, 8192))
local_desc = slot_safe.fetch()
assert xp_aligned_validate_desc(local_desc) is True and local_desc.length == 64

fill_chunks = {a & ~4095 for a in [0x0000, 0x1000]}
tx_chunks = {d.addr & ~4095 for d in [XdpDesc(0x1040, 128)]}
assert (fill_chunks & tx_chunks) == {0x1000}


@dataclass
class MultiBufXdp:
    linear_head: bytearray
    frags: list[bytearray]

    def direct_slice(self, offset: int, size: int) -> bytes | None:
        if offset < 0 or offset + size > len(self.linear_head):
            return None
        return bytes(self.linear_head[offset : offset + size])

    def bpf_xdp_load_bytes(self, offset: int, size: int) -> bytes | None:
        total = len(self.linear_head) + sum(len(f) for f in self.frags)
        if offset < 0 or size <= 0 or offset + size > total:
            return None
        out, cur = bytearray(), 0
        for seg in [self.linear_head, *self.frags]:
            seg_end = cur + len(seg)
            if offset < seg_end and offset + size > cur:
                out.extend(seg[max(0, offset - cur) : min(len(seg), offset + size - cur)])
            cur = seg_end
        return bytes(out)


mb = MultiBufXdp(bytearray(b"A" * 50), [bytearray(b"BCDEFG"), bytearray(b"HIJKLM")])
assert mb.direct_slice(48, 6) is None
assert mb.bpf_xdp_load_bytes(48, 6) == b"AABCDE"
```

## Revalidation

Revalidate this package when any of the following change (`Basis: derived`):

1. **Linux Kernel `AF_XDP` or `XDP` Core Revisions**:
   - Inspect `net/xdp/xsk_queue.h` (`xp_aligned_validate_desc`, `xp_unaligned_validate_desc`, `xskq_cons_read_desc_batch`, and `xp_unused_options_set`) if new `XDP_*` descriptor option flags or `UMEM` registration modes are introduced in `include/uapi/linux/if_xdp.h`.
   - Inspect `net/core/filter.c` (`bpf_helper_changes_pkt_data`, `bpf_xdp_adjust_head`, `bpf_xdp_adjust_tail`, `bpf_xdp_load_bytes`) and `kernel/bpf/verifier.c` if new XDP kfuncs (such as `bpf_dynptr_adjust` or native XDP checksum kfuncs) alter packet-pointer invalidation or cross-fragment write semantics.
2. **Cilium / `libxdp` / `Aya` Datapath Updates**:
   - Re-check `cilium/cilium` `bpf/include/bpf/ctx/xdp.h` (`l3_csum_replace`, `l4_csum_replace`) if Cilium migrates XDP programs from `[data, data_end)` inline assembly to multi-buffer `bpf_xdp_load_bytes` / `bpf_dynptr` checksum helpers.
   - Re-check `xdp-project/xdp-tools` `headers/xdp/xsk.h` and `aya-rs/aya` `ebpf/aya-ebpf/src/programs/xdp.rs` if safe multi-buffer or `AF_XDP` ring wrappers are added upstream.
3. **Automated Executable Check**:
   - Extract and run the Python 3 verification script in `## Evidence` (`python3 -c ...`), confirming zero assertion failures across all $262{,}144$ `RFC 1624` / `UDP` transitions, `TOCTOU` single-fetch snapshots, `UMEM` chunk aliasing checks, and multi-buffer scatter-gather boundary reads.
