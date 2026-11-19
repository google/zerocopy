#!/usr/bin/env python3
"""Self-contained multi-protocol state-space verifier for SW<->HW FFI boundaries.

Exhaustively verifies four hardware-software boundary models using finite-state
breadth-first exploration and graph cycle analysis (Python 3.10+ stdlib only):

  1. Non-coherent ARMv8-style Cache + DRAM + DMA litmus model:
     - Proves cache-line false-sharing tearing corruption for unaligned
       DMA_FROM_DEVICE buffers sharing a 64B cache line with an adjacent CPU
       field under EVERY ARMv8 cache maintenance op (DC CVAC, DC IVAC, DC CIVAC).
     - Proves that even CacheLineAligned linear DMA_FROM_DEVICE suffers stale
       reads from hardware speculative prefetch if post-DMA DC IVAC is omitted.
     - Proves 0-violation soundness under CacheLineAligned linear DMA ownership
       + pre-DMA DC CIVAC + post-DMA DC IVAC + DSB SY even with unconstrained
       speculative prefetching, and contrasts non-coherent DMA_TO_DEVICE
       (with/without DC CVAC) against hardware-coherent CXL.cache snooping.

  2. On-chip interconnect causality & deadlock verification:
     - ARM AMBA AXI4 (ARM IHI 0022 Sec. A3.3.1) 5-channel VALID/READY
       combinational dependency cycle detector + 4 KiB burst boundary verifier.
     - TileLink-C (Spec v1.8.1 / v1.9.3) channel-priority acyclicity checker
       (A < B < C < D < E) + 2-client coherent directory deadlock-trace finder
       when priority isolation is violated.

  3. Linear typestate FPGA Dynamic Partial Reconfiguration (DPR) decoupler:
     - Demonstrates (i) PCIe/AXI bus-wedge (orphaned in-flight burst) under
       naive decoupling, (ii) floating RP glitch leak without decoupling, and
       (iii) post-swap ABI mismatch without linear ABI witnesses.
     - Proves 0 bus wedges, 0 floating-signal leaks, and 0 ABI mismatches under
       AxiShutdownManager + DfxDecoupler + linear typestate token handoff.

  4. Preemptive IRQ & Baker Stack Resource Policy (SRP) verifier:
     - Contrasts unprotected preemption (data race witnessed) against Baker SRP
       priority-ceiling discipline matching RTIC BASEPRI save/restore semantics
       (0 races, 0 deadlocks, 0 LIFO stack violations across all interleavings).
     - Demonstrates edge-triggered IRQ lost-wakeup deadlock vs 0-lost-wakeup
       verified mask-before-poll driver-device product automaton.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from typing import Any


# =============================================================================
# Part 1: Non-Coherent ARMv8 Cache + DRAM + DMA Litmus State-Space Explorer
# =============================================================================

def verify_dma_cache_coherence() -> dict[str, Any]:
    """Exhaustive BFS over ARMv8 non-coherent cache + DRAM + DMA interleavings."""

    def explore_shared_line_from_device(post_op: str) -> dict[str, Any]:
        """Unaligned DMA_FROM_DEVICE sharing a 64B cache line with CPU variable C."""
        # State: (dram_d, dram_c, cache, dma_done, cpu_wrote_c, synced, rd_d, rd_c)
        # cache: None | (cd, cc, dirty)
        init = (0, 1, None, False, False, False, None, None)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        witness: list[str] | None = None
        terminal_states = 0
        corrupt_terminals = 0

        while q:
            st, trace = q.popleft()
            dram_d, dram_c, cache, dma_done, cpu_wrote_c, synced, rd_d, rd_c = st

            if synced and rd_d is not None and rd_c is not None:
                terminal_states += 1
                final_d = cache[0] if cache is not None else dram_d
                final_c = cache[1] if cache is not None else dram_c
                if rd_d != 0xAA or rd_c != 2 or final_d != 0xAA or final_c != 2:
                    corrupt_terminals += 1
                    if witness is None:
                        witness = trace + [
                            f"CORRUPTION: cpu_read=(D={rd_d:#x}, C={rd_c}), "
                            f"final_visible=(D={final_d:#x}, C={final_c}), dram=({dram_d:#x}, {dram_c})"
                        ]
                continue

            nexts: list[tuple[Any, str]] = []

            if cache is None:
                nexts.append((
                    (dram_d, dram_c, (dram_d, dram_c, False), dma_done, cpu_wrote_c, synced, rd_d, rd_c),
                    "HW_SPEC_PREFETCH",
                ))

            if cache is not None:
                cd, cc, dirty = cache
                if dirty:
                    nexts.append((
                        (cd, cc, None, dma_done, cpu_wrote_c, synced, rd_d, rd_c),
                        "HW_DIRTY_EVICT_WB",
                    ))
                else:
                    nexts.append((
                        (dram_d, dram_c, None, dma_done, cpu_wrote_c, synced, rd_d, rd_c),
                        "HW_CLEAN_EVICT",
                    ))

            if not dma_done:
                nexts.append((
                    (0xAA, dram_c, cache, True, cpu_wrote_c, synced, rd_d, rd_c),
                    "DMA_WRITE_DRAM_D=0xAA",
                ))

            if not cpu_wrote_c:
                new_cache = (dram_d, 2, True) if cache is None else (cache[0], 2, True)
                nexts.append((
                    (dram_d, dram_c, new_cache, dma_done, True, synced, rd_d, rd_c),
                    "CPU_STORE_ADJ_C=2",
                ))

            if dma_done and cpu_wrote_c and not synced:
                if post_op == "DC_CIVAC":
                    if cache is not None and cache[2]:
                        nexts.append((
                            (cache[0], cache[1], None, dma_done, cpu_wrote_c, True, rd_d, rd_c),
                            "CPU_DC_CIVAC+DSB_SY",
                        ))
                    else:
                        nexts.append((
                            (dram_d, dram_c, None, dma_done, cpu_wrote_c, True, rd_d, rd_c),
                            "CPU_DC_CIVAC+DSB_SY",
                        ))
                elif post_op == "DC_IVAC":
                    nexts.append((
                        (dram_d, dram_c, None, dma_done, cpu_wrote_c, True, rd_d, rd_c),
                        "CPU_DC_IVAC+DSB_SY",
                    ))
                elif post_op == "DC_CVAC":
                    if cache is not None and cache[2]:
                        nexts.append((
                            (cache[0], cache[1], (cache[0], cache[1], False), dma_done, cpu_wrote_c, True, rd_d, rd_c),
                            "CPU_DC_CVAC+DSB_SY",
                        ))
                    else:
                        nexts.append((
                            (dram_d, dram_c, cache, dma_done, cpu_wrote_c, True, rd_d, rd_c),
                            "CPU_DC_CVAC+DSB_SY",
                        ))
                else:
                    raise ValueError(post_op)

            if synced and rd_d is None:
                obs_d = cache[0] if cache is not None else dram_d
                obs_c = cache[1] if cache is not None else dram_c
                nexts.append((
                    (dram_d, dram_c, cache, dma_done, cpu_wrote_c, synced, obs_d, obs_c),
                    "CPU_READ_D_AND_C",
                ))

            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "post_op": post_op,
            "states_explored": len(visited),
            "terminal_states": terminal_states,
            "corrupt_terminals": corrupt_terminals,
            "corruption_found": corrupt_terminals > 0,
            "minimal_witness": witness,
        }

    def explore_aligned_linear_from_device(do_post_ivac: bool = True) -> dict[str, Any]:
        """CacheLineAligned linear DMA_FROM_DEVICE: D on line L0, C on disjoint line L1."""
        # Start with stale dirty CPU line (0x55, True) in L0 to test pre-sync completeness.
        init = (0, 1, (0x55, True), None, False, False, False, False, None, None)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        terminal_states = 0
        violations = 0
        witness: list[str] | None = None

        while q:
            st, trace = q.popleft()
            dram_d, dram_c, c0, c1, pre_sync, dma_done, wrote_c, post_sync, rd_d, rd_c = st

            if post_sync and rd_d is not None and rd_c is not None:
                terminal_states += 1
                final_d = c0[0] if c0 is not None else dram_d
                final_c = c1[0] if c1 is not None else dram_c
                if rd_d != 0xAA or rd_c != 2 or final_d != 0xAA or final_c != 2:
                    violations += 1
                    if witness is None:
                        witness = trace + [
                            f"STALE_PREFETCH_READ: cpu_read=(D={rd_d:#x}, C={rd_c}), dram_d={dram_d:#x}"
                        ]
                continue

            nexts: list[tuple[Any, str]] = []

            if not pre_sync:
                nd = c0[0] if (c0 is not None and c0[1]) else dram_d
                nexts.append((
                    (nd, dram_c, None, c1, True, False, wrote_c, False, None, None),
                    "PRE_DMA_DC_CIVAC_L0+DSB_SY",
                ))

            # Hardware speculative prefetch of L0 (clean) and L1 (clean) anytime
            if c0 is None:
                nexts.append((
                    (dram_d, dram_c, (dram_d, False), c1, pre_sync, dma_done, wrote_c, post_sync, rd_d, rd_c),
                    "HW_SPEC_PREFETCH_L0",
                ))
            if c1 is None:
                nexts.append((
                    (dram_d, dram_c, c0, (dram_c, False), pre_sync, dma_done, wrote_c, post_sync, rd_d, rd_c),
                    "HW_SPEC_PREFETCH_L1",
                ))

            if c0 is not None:
                nd = c0[0] if c0[1] else dram_d
                nexts.append((
                    (nd, dram_c, None, c1, pre_sync, dma_done, wrote_c, post_sync, rd_d, rd_c),
                    "HW_EVICT_L0",
                ))
            if c1 is not None:
                nc = c1[0] if c1[1] else dram_c
                nexts.append((
                    (dram_d, nc, c0, None, pre_sync, dma_done, wrote_c, post_sync, rd_d, rd_c),
                    "HW_EVICT_L1",
                ))

            if not wrote_c:
                nexts.append((
                    (dram_d, dram_c, c0, (2, True), pre_sync, dma_done, True, post_sync, rd_d, rd_c),
                    "CPU_STORE_C_ON_L1=2",
                ))

            if pre_sync and not dma_done:
                nexts.append((
                    (0xAA, dram_c, c0, c1, pre_sync, True, wrote_c, post_sync, rd_d, rd_c),
                    "DMA_WRITE_DRAM_D=0xAA",
                ))

            if dma_done and not post_sync:
                assert c0 is None or not c0[1], f"Invariant violated: L0 dirty during DMA: {trace}"
                if do_post_ivac:
                    nexts.append((
                        (dram_d, dram_c, None, c1, pre_sync, dma_done, wrote_c, True, rd_d, rd_c),
                        "POST_DMA_DC_IVAC_L0+DSB_SY",
                    ))
                else:
                    nexts.append((
                        (dram_d, dram_c, c0, c1, pre_sync, dma_done, wrote_c, True, rd_d, rd_c),
                        "SKIP_POST_DMA_IVAC",
                    ))

            if post_sync and wrote_c and rd_d is None:
                obs_d = c0[0] if c0 is not None else dram_d
                obs_c = c1[0] if c1 is not None else dram_c
                nexts.append((
                    (dram_d, dram_c, c0, c1, pre_sync, dma_done, wrote_c, post_sync, obs_d, obs_c),
                    "CPU_READ_D_AND_C",
                ))

            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "do_post_ivac": do_post_ivac,
            "states_explored": len(visited),
            "terminal_states": terminal_states,
            "violations": violations,
            "proven_sound": violations == 0 and terminal_states > 0,
            "minimal_witness": witness,
        }

    def explore_to_device(use_clean: bool, use_cxl_coherent: bool = False) -> dict[str, Any]:
        """DMA_TO_DEVICE: CPU writes 0xBB, then device reads DRAM (or snoops via CXL.cache)."""
        init = (0, (0xBB, True), False, None)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        violations = 0
        terminal_states = 0
        witness: list[str] | None = None

        while q:
            st, trace = q.popleft()
            dram_d, c0, cleaned, dma_val = st
            if dma_val is not None:
                terminal_states += 1
                if dma_val != 0xBB:
                    violations += 1
                    if witness is None:
                        witness = trace + [f"STALE_DMA_READ: observed={dma_val:#x}, expected=0xbb"]
                continue

            nexts: list[tuple[Any, str]] = []
            if c0 is not None:
                nd = c0[0] if c0[1] else dram_d
                nexts.append(((nd, None, cleaned, dma_val), "HW_EVICT_L0"))
            if use_clean and not cleaned:
                nd = c0[0] if (c0 is not None and c0[1]) else dram_d
                nc0 = (c0[0], False) if c0 is not None else None
                nexts.append(((nd, nc0, True, dma_val), "CPU_DC_CVAC+DSB_SY"))
            if (not use_clean) or cleaned:
                if use_cxl_coherent:
                    obs = c0[0] if (c0 is not None and c0[1]) else dram_d
                    nexts.append(((dram_d, c0, cleaned, obs), "CXL_CACHE_SNOOP_READ"))
                else:
                    nexts.append(((dram_d, c0, cleaned, dram_d), "DMA_READ_DRAM"))

            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "use_clean": use_clean,
            "use_cxl_coherent": use_cxl_coherent,
            "states_explored": len(visited),
            "terminal_states": terminal_states,
            "violations": violations,
            "proven_sound": violations == 0 and terminal_states > 0,
            "minimal_witness": witness,
        }

    shared_civac = explore_shared_line_from_device("DC_CIVAC")
    shared_ivac = explore_shared_line_from_device("DC_IVAC")
    shared_cvac = explore_shared_line_from_device("DC_CVAC")
    aligned_no_post = explore_aligned_linear_from_device(do_post_ivac=False)
    aligned_from = explore_aligned_linear_from_device(do_post_ivac=True)
    to_dev_buggy = explore_to_device(use_clean=False)
    to_dev_clean = explore_to_device(use_clean=True)
    to_dev_cxl = explore_to_device(use_clean=False, use_cxl_coherent=True)

    assert shared_civac["corruption_found"]
    assert shared_ivac["corruption_found"]
    assert shared_cvac["corruption_found"]
    assert not aligned_no_post["proven_sound"], "Expected speculative prefetch stale read without post DC_IVAC"
    assert aligned_from["proven_sound"]
    assert not to_dev_buggy["proven_sound"]
    assert to_dev_clean["proven_sound"]
    assert to_dev_cxl["proven_sound"]

    return {
        "unaligned_shared_line_from_device": {
            "DC_CIVAC": shared_civac,
            "DC_IVAC": shared_ivac,
            "DC_CVAC": shared_cvac,
        },
        "aligned_linear_from_device_missing_post_ivac": aligned_no_post,
        "aligned_linear_from_device": aligned_from,
        "to_device_no_clean": to_dev_buggy,
        "to_device_dc_cvac": to_dev_clean,
        "to_device_cxl_cache": to_dev_cxl,
    }


# =============================================================================
# Part 2: AXI4 Combinational Causality + 4 KiB Rule & TileLink-C Acyclicity
# =============================================================================

def find_cycle(graph: dict[str, list[str]]) -> list[str] | None:
    """Deterministic DFS cycle finder on directed graph."""
    color: dict[str, int] = {}
    parent: dict[str, str | None] = {}

    def dfs(u: str) -> list[str] | None:
        color[u] = 1
        for v in sorted(graph.get(u, [])):
            if color.get(v, 0) == 1:
                cyc = [v, u]
                cur = parent.get(u)
                while cur is not None and cur != v:
                    cyc.append(cur)
                    cur = parent.get(cur)
                cyc.append(v)
                cyc.reverse()
                return cyc
            if color.get(v, 0) == 0:
                parent[v] = u
                res = dfs(v)
                if res is not None:
                    return res
        color[u] = 2
        return None

    for node in sorted(graph.keys()):
        if color.get(node, 0) == 0:
            parent[node] = None
            cyc = dfs(node)
            if cyc is not None:
                return cyc
    return None


def verify_axi4_and_tilelink() -> dict[str, Any]:
    """Verify ARM AMBA AXI4 handshake causality, 4 KiB burst boundary, and TileLink-C deadlock freedom."""

    # ARM IHI 0022 Sec. A3.3.1: edge u -> v means "signal u waits for signal v before asserting"
    legal_slave_edges: dict[str, list[str]] = {
        "AWREADY": ["AWVALID", "WVALID"],
        "WREADY": ["AWVALID", "WVALID"],
        "BVALID": ["AWVALID", "AWREADY", "WVALID", "WREADY"],
        "ARREADY": ["ARVALID"],
        "RVALID": ["ARVALID", "ARREADY"],
    }
    legal_master_edges: dict[str, list[str]] = {
        "AWVALID": [],
        "WVALID": [],
        "BREADY": ["BVALID"],
        "ARVALID": [],
        "RREADY": ["RVALID"],
    }

    def compose(m_edges: dict[str, list[str]], s_edges: dict[str, list[str]]) -> dict[str, list[str]]:
        g: dict[str, list[str]] = {k: list(v) for k, v in m_edges.items()}
        for k, v in s_edges.items():
            g.setdefault(k, []).extend(v)
        return g

    cyc_ok = find_cycle(compose(legal_master_edges, legal_slave_edges))
    assert cyc_ok is None

    cyc_bad1 = find_cycle(compose({**legal_master_edges, "AWVALID": ["AWREADY"]}, legal_slave_edges))
    assert cyc_bad1 is not None

    cyc_bad2 = find_cycle(compose({**legal_master_edges, "WVALID": ["AWREADY"]}, legal_slave_edges))
    assert cyc_bad2 is not None

    cyc_bad3 = find_cycle(compose(
        legal_master_edges,
        {**legal_slave_edges, "BVALID": ["AWVALID", "AWREADY", "WVALID", "WREADY", "BREADY"]},
    ))
    assert cyc_bad3 is not None

    # AXI4 4 KiB burst boundary rule (ARM IHI 0022 Sec. A3.4.1)
    def check_axi4_4kb_burst(start_addr: int, axsize_log2: int, axlen: int, burst_type: str = "INCR") -> tuple[bool, int]:
        beat_bytes = 1 << axsize_log2
        aligned_start = (start_addr // beat_bytes) * beat_bytes
        total_bytes = beat_bytes * (axlen + 1)
        if burst_type == "INCR":
            last_byte = aligned_start + total_bytes - 1
            return (start_addr // 4096) == (last_byte // 4096), total_bytes
        raise ValueError(burst_type)

    burst_legal, b1_sz = check_axi4_4kb_burst(0x1000_0F80, axsize_log2=3, axlen=15)
    burst_cross, b2_sz = check_axi4_4kb_burst(0x1000_0F80, axsize_log2=3, axlen=16)
    assert burst_legal and not burst_cross

    # TileLink-C Channel Priority Acyclicity (A < B < C < D < E)
    tl_priorities = {"A": 0, "B": 1, "C": 2, "D": 3, "E": 4}
    tl_protocol_deps: dict[str, list[str]] = {
        "A": ["B", "D"],
        "B": ["C"],
        "C": ["D"],
        "D": ["E"],
        "E": [],
    }
    assert find_cycle(tl_protocol_deps) is None
    monotonic = all(tl_priorities[u] < tl_priorities[v] for u, vs in tl_protocol_deps.items() for v in vs)
    assert monotonic

    tl_broken_ac = {k: list(v) for k, v in tl_protocol_deps.items()}
    tl_broken_ac["C"].append("A")
    tl_cyc_ac = find_cycle(tl_broken_ac)
    assert tl_cyc_ac is not None

    tl_broken_ae = {k: list(v) for k, v in tl_protocol_deps.items()}
    tl_broken_ae["E"].append("A")
    tl_cyc_ae = find_cycle(tl_broken_ae)
    assert tl_cyc_ae is not None

    def simulate_tlc_2client(shared_ac_queue: bool) -> dict[str, Any]:
        init = (True, True, True, False, False, False, False, False)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        deadlocks: list[list[str]] = []
        completed = 0

        while q:
            st, trace = q.popleft()
            mshr_busy, probe_pend, a_q, c_q, c_done, d_sent, e_done, a_done = st
            if e_done and a_done:
                completed += 1
                continue

            nexts: list[tuple[Any, str]] = []
            if probe_pend and not c_q and not c_done:
                if not (shared_ac_queue and a_q):
                    nexts.append(((mshr_busy, False, a_q, True, False, d_sent, e_done, a_done), "C0_SEND_PROBEACK_C"))
            if c_q and not d_sent:
                nexts.append(((mshr_busy, probe_pend, a_q, False, True, True, e_done, a_done), "DIR_RECV_C_SEND_GRANT_D"))
            if d_sent and not e_done:
                nexts.append(((False, probe_pend, a_q, c_q, c_done, d_sent, True, a_done), "C1_SEND_GRANTACK_E_FREE_MSHR"))
            if a_q and not mshr_busy and not a_done:
                nexts.append(((True, probe_pend, False, c_q, c_done, d_sent, e_done, True), "DIR_ACCEPT_C0_ACQUIRE_A"))

            if not nexts:
                deadlocks.append(trace + ["DEADLOCK: MSHR_FULL_WAITING_C_AND_SHARED_FIFO_BLOCKED_BY_A"])
            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "shared_ac_queue": shared_ac_queue,
            "states_explored": len(visited),
            "completed_states": completed,
            "deadlock_count": len(deadlocks),
            "deadlock_witness": deadlocks[0] if deadlocks else None,
        }

    tlc_sep = simulate_tlc_2client(shared_ac_queue=False)
    tlc_shared = simulate_tlc_2client(shared_ac_queue=True)
    assert tlc_sep["deadlock_count"] == 0 and tlc_sep["completed_states"] > 0
    assert tlc_shared["deadlock_count"] > 0 and tlc_shared["completed_states"] == 0

    return {
        "axi4_causality": {
            "compliant_cycle": cyc_ok,
            "bug_awvalid_waits_awready_cycle": cyc_bad1,
            "bug_wvalid_waits_awready_cycle": cyc_bad2,
            "bug_bvalid_waits_bready_cycle": cyc_bad3,
            "burst_4kb_legal_example": {"addr": "0x10000f80", "bytes": b1_sz, "legal": burst_legal},
            "burst_4kb_crossing_example": {"addr": "0x10000f80", "bytes": b2_sz, "legal": burst_cross},
        },
        "tilelink_c_acyclicity": {
            "channel_order": ["A", "B", "C", "D", "E"],
            "compliant_acyclic": True,
            "strict_priority_monotonic": monotonic,
            "broken_ac_shared_cycle": tl_cyc_ac,
            "broken_ae_shared_cycle": tl_cyc_ae,
            "two_client_separate_channels": tlc_sep,
            "two_client_shared_ac_fifo": tlc_shared,
        },
    }


# =============================================================================
# Part 3: Linear Typestate FPGA Dynamic Partial Reconfiguration (DPR) Verifier
# =============================================================================

def verify_fpga_dpr_typestate() -> dict[str, Any]:
    """Exhaustive BFS comparing unsafe DPR variants vs AxiShutdownManager + Linear Typestate."""

    def explore_dpr(mode: str) -> dict[str, Any]:
        """Modes:
          - 'naive_decouple': toggles decoupler directly without draining in-flight AXI bursts
          - 'no_decouple': drains AXI bursts but omits DfxDecoupler isolation during ICAP bitstream load
          - 'no_abi_witness': drains & decouples safely, swaps AbiV1 -> AbiV2, but SW keeps stale AbiV1 handle
          - 'linear_typestate': AxiShutdownManager drain + DfxDecoupler isolation + linear ABI token swap
        """
        init = ("ACTIVE", 0, 0, False, "ABI_V1", "ABI_V1", False, False, False, False, False)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        wedged_witness: list[str] | None = None
        glitch_witness: list[str] | None = None
        abi_witness: list[str] | None = None
        wedged_count = 0
        glitch_count = 0
        abi_count = 0
        clean_terminal_states = 0

        MAX_INFLIGHT = 2

        while q:
            st, trace = q.popleft()
            phase, rd, wr, dec, hw_abi, sw_abi, rdone, post_ok, wedged, glitch, abim = st

            if wedged:
                wedged_count += 1
                if wedged_witness is None:
                    wedged_witness = trace
                continue
            if glitch:
                glitch_count += 1
                if glitch_witness is None:
                    glitch_witness = trace
                continue
            if abim:
                abi_count += 1
                if abi_witness is None:
                    abi_witness = trace
                continue
            if rdone and post_ok and rd == 0 and wr == 0:
                clean_terminal_states += 1
                continue

            nexts: list[tuple[Any, str]] = []

            if phase in ("ACTIVE", "RESUMED"):
                if rd < MAX_INFLIGHT and not post_ok:
                    if sw_abi != hw_abi:
                        nexts.append((
                            (phase, rd, wr, dec, hw_abi, sw_abi, rdone, post_ok, False, False, True),
                            f"HOST_ISSUE_RD_WITH_STALE_{sw_abi}_VS_HW_{hw_abi}",
                        ))
                    else:
                        nexts.append((
                            (phase, rd + 1, wr, dec, hw_abi, sw_abi, rdone, post_ok, False, False, False),
                            "HOST_ISSUE_AXI_READ",
                        ))
                if wr < MAX_INFLIGHT and not post_ok:
                    if sw_abi != hw_abi:
                        nexts.append((
                            (phase, rd, wr, dec, hw_abi, sw_abi, rdone, post_ok, False, False, True),
                            f"HOST_ISSUE_WR_WITH_STALE_{sw_abi}_VS_HW_{hw_abi}",
                        ))
                    else:
                        nexts.append((
                            (phase, rd, wr + 1, dec, hw_abi, sw_abi, rdone, post_ok, False, False, False),
                            "HOST_ISSUE_AXI_WRITE",
                        ))

            if not dec and phase in ("ACTIVE", "DRAINING", "RESUMED"):
                if rd > 0:
                    np = post_ok or (phase == "RESUMED")
                    nexts.append((
                        (phase, rd - 1, wr, dec, hw_abi, sw_abi, rdone, np, False, False, False),
                        "RP_COMPLETE_AXI_RLAST",
                    ))
                if wr > 0:
                    np = post_ok or (phase == "RESUMED")
                    nexts.append((
                        (phase, rd, wr - 1, dec, hw_abi, sw_abi, rdone, np, False, False, False),
                        "RP_COMPLETE_AXI_BVALID",
                    ))

            if phase == "DRAINING":
                nexts.append((
                    (phase, rd, wr, dec, hw_abi, sw_abi, rdone, post_ok, False, False, False),
                    "SHUTDOWN_MGR_REJECT_NEW_TX_WITH_SLVERR",
                ))

            if phase == "ACTIVE" and not rdone:
                if mode == "naive_decouple":
                    if rd > 0 or wr > 0:
                        nexts.append((
                            ("DECOUPLED", rd, wr, True, hw_abi, sw_abi, rdone, post_ok, True, False, False),
                            f"NAIVE_DECOUPLE_ORPHANS_INFLIGHT(rd={rd},wr={wr})->PCIE_BUS_WEDGE",
                        ))
                    else:
                        nexts.append((
                            ("DECOUPLED", 0, 0, True, hw_abi, sw_abi, rdone, post_ok, False, False, False),
                            "NAIVE_DECOUPLE_LUCKY_IDLE",
                        ))
                else:
                    next_sw = "NONE_CONSUMED" if mode == "linear_typestate" else sw_abi
                    nexts.append((
                        ("DRAINING", rd, wr, False, hw_abi, next_sw, rdone, post_ok, False, False, False),
                        "SHUTDOWN_REQ_ENTER_DRAINING",
                    ))

            if phase == "DRAINING" and rd == 0 and wr == 0:
                if mode == "no_decouple":
                    nexts.append((
                        ("RECONFIGURING", 0, 0, False, "RECONFIG_X", sw_abi, rdone, post_ok, False, False, False),
                        "SKIP_DECOUPLE_START_ICAP_V2",
                    ))
                else:
                    nexts.append((
                        ("DECOUPLED", 0, 0, True, hw_abi, sw_abi, rdone, post_ok, False, False, False),
                        "QUIESCED_ASSERT_DFX_DECOUPLE",
                    ))

            if phase == "DECOUPLED":
                nexts.append((
                    ("RECONFIGURING", rd, wr, dec, "RECONFIG_X", sw_abi, rdone, post_ok, False, False, False),
                    "ICAP_START_PARTIAL_BITSTREAM_V2",
                ))

            if phase == "RECONFIGURING":
                if not dec:
                    nexts.append((
                        (phase, rd, wr, dec, hw_abi, sw_abi, rdone, post_ok, False, True, False),
                        "FLOATING_RP_GLITCH_LEAKED_TO_STATIC_SHELL",
                    ))
                else:
                    new_sw = "ABI_V2" if mode == "linear_typestate" else sw_abi
                    nexts.append((
                        ("RESUMED", 0, 0, False, "ABI_V2", new_sw, True, False, False, False, False),
                        "DECOUPLED_GLITCH_ABSORBED+BITSTREAM_V2_DONE+RELEASE_DECOUPLE",
                    ))

            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "mode": mode,
            "states_explored": len(visited),
            "clean_terminal_states": clean_terminal_states,
            "bus_wedge_states": wedged_count,
            "floating_glitch_leaks": glitch_count,
            "abi_mismatch_states": abi_count,
            "proven_safe": (wedged_count == 0 and glitch_count == 0 and abi_count == 0 and clean_terminal_states > 0),
            "bus_wedge_witness": wedged_witness,
            "glitch_leak_witness": glitch_witness,
            "abi_mismatch_witness": abi_witness,
        }

    r_naive = explore_dpr("naive_decouple")
    r_nodec = explore_dpr("no_decouple")
    r_no_abi = explore_dpr("no_abi_witness")
    r_linear = explore_dpr("linear_typestate")

    assert r_naive["bus_wedge_states"] > 0
    assert r_nodec["floating_glitch_leaks"] > 0
    assert r_no_abi["abi_mismatch_states"] > 0
    assert r_linear["proven_safe"]

    return {
        "naive_decouple": r_naive,
        "drain_without_decoupler": r_nodec,
        "drain_without_abi_witness": r_no_abi,
        "linear_typestate_dpr": r_linear,
    }


# =============================================================================
# Part 4: Baker SRP Priority-Ceiling & Edge-IRQ Lost-Wakeup Verifier
# =============================================================================

def verify_srp_and_irq_lost_wakeup() -> dict[str, Any]:
    """Verify Baker SRP single-stack/race-freedom and edge-IRQ lost-wakeup freedom."""

    tasks = {"T1": 1, "T2": 2, "T3": 3}
    ceiling_R = max(tasks["T1"], tasks["T3"])  # 3

    def explore_srp(enforce_srp: bool) -> dict[str, Any]:
        # Stack frame entry: (task_name, saved_basepri) matching rtic/src/export/cortex_basepri.rs
        init = ((), 0, 0, 0, None, 0)
        q: deque[tuple[Any, list[str]]] = deque([(init, [])])
        visited = {init}
        races = 0
        deadlocks = 0
        lifo_violations = 0
        completed = 0
        race_witness: list[str] | None = None

        while q:
            st, trace = q.popleft()
            stack, p1, p2, p3, r_holder, pi = st
            if stack == () and p1 == 3 and p2 == 2 and p3 == 3:
                completed += 1
                continue

            cur_prio = tasks[stack[-1][0]] if stack else 0
            active_names = {f[0] for f in stack}
            nexts: list[tuple[Any, str]] = []

            for name, prio, pc in [("T1", 1, p1), ("T2", 2, p2), ("T3", 3, p3)]:
                can_preempt = (prio > cur_prio) and ((not enforce_srp) or (prio > pi))
                if pc == 0 and name not in active_names and can_preempt:
                    np1, np2, np3 = p1, p2, p3
                    if name == "T1":
                        np1 = 1
                    elif name == "T2":
                        np2 = 1
                    else:
                        np3 = 1
                    nexts.append((
                        (stack + ((name, pi),), np1, np2, np3, r_holder, pi),
                        f"PREEMPT_ENTER_{name}(saved_pi={pi})",
                    ))

            if stack:
                top, saved_pi = stack[-1]
                if top == "T1":
                    if p1 == 1:
                        if r_holder is not None:
                            races += 1
                            if race_witness is None:
                                race_witness = trace + [f"DATA_RACE: T1_ENTER_R_WHILE_HELD_BY_{r_holder}"]
                            continue
                        new_pi = max(pi, ceiling_R) if enforce_srp else pi
                        nexts.append((
                            (stack, 2, p2, p3, "T1", new_pi),
                            f"T1_LOCK_R(pi={new_pi})",
                        ))
                    elif p1 == 2:
                        if r_holder != "T1":
                            lifo_violations += 1
                        nexts.append((
                            (stack[:-1], 3, p2, p3, None, saved_pi),
                            f"T1_UNLOCK_R_RESTORE_PI={saved_pi}_EXIT",
                        ))
                elif top == "T2":
                    if p2 == 1:
                        nexts.append((
                            (stack[:-1], p1, 2, p3, r_holder, saved_pi),
                            "T2_WORK_EXIT",
                        ))
                elif top == "T3":
                    if p3 == 1:
                        if r_holder is not None:
                            races += 1
                            if race_witness is None:
                                race_witness = trace + [f"DATA_RACE: T3_PREEMPTED_AND_ENTERED_R_WHILE_HELD_BY_{r_holder}"]
                            continue
                        new_pi = max(pi, ceiling_R) if enforce_srp else pi
                        nexts.append((
                            (stack, p1, p2, 2, "T3", new_pi),
                            f"T3_LOCK_R(pi={new_pi})",
                        ))
                    elif p3 == 2:
                        if r_holder != "T3":
                            lifo_violations += 1
                        nexts.append((
                            (stack[:-1], p1, p2, 3, None, saved_pi),
                            f"T3_UNLOCK_R_RESTORE_PI={saved_pi}_EXIT",
                        ))

            if not nexts:
                deadlocks += 1
            for nst, act in nexts:
                if nst not in visited:
                    visited.add(nst)
                    q.append((nst, trace + [act]))

        return {
            "enforce_srp": enforce_srp,
            "ceiling_R": ceiling_R,
            "states_explored": len(visited),
            "completed_states": completed,
            "data_races": races,
            "deadlocks": deadlocks,
            "lifo_stack_violations": lifo_violations,
            "proven_safe": races == 0 and deadlocks == 0 and lifo_violations == 0 and completed > 0,
            "race_witness": race_witness,
        }

    def explore_edge_irq(mask_before_poll: bool) -> dict[str, Any]:
        init_irq = ("START", False, False, False, False, False)
        q2: deque[tuple[Any, list[str]]] = deque([(init_irq, [])])
        vis2 = {init_irq}
        lost_wakeups = 0
        lost_witness: list[str] | None = None
        processed = 0

        while q2:
            st, trace = q2.popleft()
            pc, masked, ready, irq_pend, isr_ran, consumed = st
            if consumed:
                processed += 1
                continue

            nexts: list[tuple[Any, str]] = []

            if not ready and not isr_ran:
                nexts.append(((pc, masked, True, True, False, False), "DEV_DATA_READY_PULSE_EDGE_IRQ"))

            if irq_pend and not masked:
                if pc == "SLEEPING":
                    nexts.append((("CONSUME", False, ready, False, True, False), "EDGE_IRQ_WAKES_WFI"))
                else:
                    nexts.append(((pc, False, ready, False, True, False), "EDGE_IRQ_PREEMPTS_BEFORE_WFI_ACKED"))

            if pc == "START":
                if mask_before_poll:
                    nexts.append((("POLL", True, ready, irq_pend, isr_ran, False), "DRV_MASK_IRQ"))
                else:
                    nexts.append((("POLL", False, ready, irq_pend, isr_ran, False), "DRV_ENTER_POLL_UNMASKED"))
            elif pc == "POLL":
                if ready:
                    nexts.append((("CONSUME", False, ready, irq_pend, isr_ran, False), "DRV_POLL_SAW_DATA"))
                else:
                    nexts.append((("PRE_WFI", masked, ready, irq_pend, isr_ran, False), "DRV_POLL_SAW_EMPTY"))
            elif pc == "PRE_WFI":
                if mask_before_poll:
                    if irq_pend or ready:
                        nexts.append((("CONSUME", False, ready, False, True, False), "DRV_WFI_MASKED_IMMEDIATE_WAKE"))
                    else:
                        nexts.append((("SLEEPING_MASKED", True, ready, irq_pend, isr_ran, False), "DRV_WFI_MASKED_SLEEP"))
                else:
                    nexts.append((("SLEEPING", False, ready, irq_pend, isr_ran, False), "DRV_WFI_UNMASKED_SLEEP"))
            elif pc == "SLEEPING_MASKED":
                if irq_pend:
                    nexts.append((("CONSUME", False, ready, False, True, False), "PENDING_EDGE_IRQ_WAKES_MASKED_WFI"))
            elif pc == "CONSUME":
                nexts.append((("DONE", False, False, False, isr_ran, True), "DRV_CONSUME_DATA_DONE"))

            if not nexts and not consumed:
                lost_wakeups += 1
                if lost_witness is None:
                    lost_witness = trace + ["LOST_WAKEUP_DEADLOCK: drv=SLEEPING, dev_data_ready=True, irq_pend=False"]
            for nst, act in nexts:
                if nst not in vis2:
                    vis2.add(nst)
                    q2.append((nst, trace + [act]))

        return {
            "mask_before_poll": mask_before_poll,
            "states_explored": len(vis2),
            "processed_states": processed,
            "lost_wakeup_deadlocks": lost_wakeups,
            "proven_liveness": lost_wakeups == 0 and processed > 0,
            "lost_wakeup_witness": lost_witness,
        }

    srp_buggy = explore_srp(enforce_srp=False)
    srp_safe = explore_srp(enforce_srp=True)
    irq_buggy = explore_edge_irq(mask_before_poll=False)
    irq_safe = explore_edge_irq(mask_before_poll=True)

    assert srp_buggy["data_races"] > 0
    assert srp_safe["proven_safe"]
    assert irq_buggy["lost_wakeup_deadlocks"] > 0
    assert irq_safe["proven_liveness"]

    return {
        "unprotected_preemption": srp_buggy,
        "baker_srp": srp_safe,
        "edge_irq_unmasked_poll": irq_buggy,
        "edge_irq_masked_wfi": irq_safe,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit full machine-readable JSON results")
    args = ap.parse_args()

    results = {
        "dma_cache_coherence": verify_dma_cache_coherence(),
        "interconnect_causality": verify_axi4_and_tilelink(),
        "fpga_dpr_typestate": verify_fpga_dpr_typestate(),
        "irq_and_srp": verify_srp_and_irq_lost_wakeup(),
    }

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        dma = results["dma_cache_coherence"]
        ic = results["interconnect_causality"]
        dpr = results["fpga_dpr_typestate"]
        irq = results["irq_and_srp"]
        print("[PASS] 1. Non-coherent ARMv8 Cache+DRAM+DMA Litmus Verifier:")
        for op, r in dma["unaligned_shared_line_from_device"].items():
            print(f"       - Unaligned shared-line DMA_FROM_DEVICE ({op}): "
                  f"states={r['states_explored']}, corrupt_terminals={r['corrupt_terminals']}/{r['terminal_states']}")
        mp = dma["aligned_linear_from_device_missing_post_ivac"]
        print(f"       - Aligned DMA_FROM_DEVICE missing post DC_IVAC (spec-prefetch hazard): "
              f"states={mp['states_explored']}, violations={mp['violations']}/{mp['terminal_states']}")
        al = dma["aligned_linear_from_device"]
        print(f"       - CacheLineAligned linear DMA_FROM_DEVICE + pre-CIVAC + post-IVAC: "
              f"states={al['states_explored']}, violations={al['violations']}/{al['terminal_states']} (PROVEN SOUND)")
        print(f"       - DMA_TO_DEVICE: no_clean violations={dma['to_device_no_clean']['violations']}, "
              f"dc_cvac violations={dma['to_device_dc_cvac']['violations']}, "
              f"cxl_cache violations={dma['to_device_cxl_cache']['violations']}")
        print("[PASS] 2. AXI4 Causality & TileLink-C Priority Acyclicity Verifier:")
        ax = ic["axi4_causality"]
        tl = ic["tilelink_c_acyclicity"]
        print(f"       - AXI4 compliant cycle={ax['compliant_cycle']}; "
              f"AWVALID->AWREADY={ax['bug_awvalid_waits_awready_cycle']}; "
              f"WVALID->AWREADY={ax['bug_wvalid_waits_awready_cycle']}; "
              f"BVALID->BREADY={ax['bug_bvalid_waits_bready_cycle']}")
        print(f"       - AXI4 4KiB burst rule: 0x10000f80+128B legal={ax['burst_4kb_legal_example']['legal']}, "
              f"0x10000f80+136B legal={ax['burst_4kb_crossing_example']['legal']}")
        print(f"       - TileLink-C A<B<C<D<E acyclic={tl['compliant_acyclic']}, "
              f"shared A/C cycle={tl['broken_ac_shared_cycle']}, "
              f"shared A/E cycle={tl['broken_ae_shared_cycle']}, "
              f"2-client separate deadlocks={tl['two_client_separate_channels']['deadlock_count']}, "
              f"shared-A/C deadlocks={tl['two_client_shared_ac_fifo']['deadlock_count']}")
        print("[PASS] 3. Linear Typestate FPGA DPR Decoupler Verifier:")
        print(f"       - Naive decouple: states={dpr['naive_decouple']['states_explored']}, "
              f"bus_wedges={dpr['naive_decouple']['bus_wedge_states']}")
        print(f"       - Drain w/o decoupler: states={dpr['drain_without_decoupler']['states_explored']}, "
              f"glitch_leaks={dpr['drain_without_decoupler']['floating_glitch_leaks']}")
        print(f"       - Drain w/o ABI witness: states={dpr['drain_without_abi_witness']['states_explored']}, "
              f"abi_mismatches={dpr['drain_without_abi_witness']['abi_mismatch_states']}")
        print(f"       - Linear typestate + AxiShutdownManager: states={dpr['linear_typestate_dpr']['states_explored']}, "
              f"wedges={dpr['linear_typestate_dpr']['bus_wedge_states']}, "
              f"glitch_leaks={dpr['linear_typestate_dpr']['floating_glitch_leaks']}, "
              f"abi_mismatches={dpr['linear_typestate_dpr']['abi_mismatch_states']} (PROVEN SAFE)")
        print("[PASS] 4. Baker SRP Priority-Ceiling & Edge-IRQ Lost-Wakeup Verifier:")
        print(f"       - Unprotected preemption: states={irq['unprotected_preemption']['states_explored']}, "
              f"races={irq['unprotected_preemption']['data_races']}")
        srp = irq["baker_srp"]
        print(f"       - Baker SRP (ceiling={srp['ceiling_R']}): states={srp['states_explored']}, "
              f"races={srp['data_races']}, deadlocks={srp['deadlocks']}, lifo_violations={srp['lifo_stack_violations']}")
        print(f"       - Edge IRQ unmasked-poll: states={irq['edge_irq_unmasked_poll']['states_explored']}, "
              f"lost_wakeups={irq['edge_irq_unmasked_poll']['lost_wakeup_deadlocks']}")
        print(f"       - Edge IRQ masked-WFI: states={irq['edge_irq_masked_wfi']['states_explored']}, "
              f"lost_wakeups={irq['edge_irq_masked_wfi']['lost_wakeup_deadlocks']} (PROVEN LIVE)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
