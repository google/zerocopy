#!/usr/bin/env python3
"""Executable model verifier for GPU scoped memory models, mbarrier pipelines, and WGSL uniformity.

Verifies three formal models directly grounded in primary specifications:
1. Scoped weak memory consistency (NVIDIA PTX ISA 9.5 Section 8 / Lustig et al. ASPLOS '19,
   Khronos Vulkan Memory Model availability/visibility chains, and HRF-direct scope matching),
   including cross-proxy ordering (generic vs async/TMA proxy).
2. Explicit-state BFS model checking of N-stage SMEM mbarrier circular-buffer pipelines
   (phase parity alternation, expect_tx / complete_tx byte accounting, and elect.sync
   single-lane arrival), proving safety for valid protocols and synthesizing minimal
   counterexample traces for parity, non-elected-lane, and byte-count bugs.
3. W3C WGSL static uniformity dependency-graph analysis (RequiredToBeUniform ->* MayBeNonUniform)
   across uniform/divergent conditionals, divergent early returns, reconvergent blocks, and loops.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from enum import Enum
import json
import sys
from typing import Any


# =============================================================================
# PART 1: AXIOMATIC SCOPED WEAK MEMORY VERIFIER (PTX / VULKAN / HRF-DIRECT)
# =============================================================================

class Scope(Enum):
    THREAD = 0
    CTA = 1       # Workgroup in Vulkan/WGSL
    CLUSTER = 2   # Hopper SM90+ Thread Block Cluster
    GPU = 3       # Device / QueueFamily in Vulkan
    SYS = 4       # System / CrossDevice


class Proxy(Enum):
    GENERIC = "generic"
    ASYNC = "async"
    TENSORMAP = "tensormap"


@dataclass(frozen=True)
class ThreadLoc:
    tid: str
    cta: int
    cluster: int
    gpu: int


@dataclass(frozen=True)
class Event:
    eid: str
    thread: ThreadLoc
    po_idx: int
    kind: str                 # "W", "R", "F", "F_PROXY"
    addr: str | None = None   # None for fences
    val: int | None = None    # Written or read value
    sem: str = "weak"         # weak, relaxed, acquire, release, acq_rel, sc
    scope: Scope = Scope.THREAD
    proxy: Proxy = Proxy.GENERIC
    proxy_from: Proxy | None = None
    proxy_to: Proxy | None = None
    # Vulkan Memory Model availability/visibility annotations on non-atomic accesses / fences
    vk_make_avail_domain: Scope | None = None
    vk_make_vis_domain: Scope | None = None

    @property
    def is_strong(self) -> bool:
        return self.sem in {"relaxed", "acquire", "release", "acq_rel", "sc"}


def scope_includes(op_thread: ThreadLoc, op_scope: Scope, target: ThreadLoc) -> bool:
    """PTX ISA 9.5 Section 8.5 / Vulkan Memory Model scope membership."""
    if op_scope == Scope.THREAD:
        return op_thread.tid == target.tid
    if op_scope == Scope.CTA:
        return op_thread.gpu == target.gpu and op_thread.cluster == target.cluster and op_thread.cta == target.cta
    if op_scope == Scope.CLUSTER:
        return op_thread.gpu == target.gpu and op_thread.cluster == target.cluster
    if op_scope == Scope.GPU:
        return op_thread.gpu == target.gpu
    if op_scope == Scope.SYS:
        return True
    raise ValueError(f"Unknown scope {op_scope}")


def morally_strong(a: Event, b: Event) -> bool:
    """PTX ISA 9.5 Section 8.7 & ptx.als (strong_r): mutual scope inclusion + same proxy + overlap."""
    if a.proxy != b.proxy:
        return False
    if a.kind in {"W", "R"} and b.kind in {"W", "R"} and a.addr != b.addr:
        return False
    if a.thread.tid == b.thread.tid:
        return True
    if not (a.is_strong and b.is_strong):
        return False
    return (
        scope_includes(a.thread, a.scope, b.thread)
        and scope_includes(b.thread, b.scope, a.thread)
    )


def transitive_closure(nodes: set[str], edges: set[tuple[str, str]]) -> set[tuple[str, str]]:
    adj: dict[str, set[str]] = {n: set() for n in nodes}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
    res: set[tuple[str, str]] = set()
    for start in nodes:
        seen: set[str] = set()
        q = deque(adj.get(start, ()))
        while q:
            cur = q.popleft()
            if cur in seen:
                continue
            seen.add(cur)
            res.add((start, cur))
            for nxt in adj.get(cur, ()):
                if nxt not in seen:
                    q.append(nxt)
    return res


def check_ptx_execution(
    events: list[Event],
    rf: set[tuple[str, str]],
    co: set[tuple[str, str]],
    sc: set[tuple[str, str]] | None = None,
    hrf_direct_mode: bool = False,
) -> dict[str, Any]:
    """Evaluate PTX ISA 9.5 Section 8 (or HRF-direct) axioms on a candidate execution.

    rf: set of (write_eid, read_eid); reads not targeted by rf read from initial value 0.
    co: strict partial coherence order over writes to the same address.
    sc: strict partial Fence-SC order over morally strong fence.sc pairs.
    """
    sc = sc or set()
    by_id = {e.eid: e for e in events}
    all_ids = set(by_id.keys())

    # 1. Program order (po)
    po: set[tuple[str, str]] = set()
    by_thread: dict[str, list[Event]] = {}
    for e in events:
        by_thread.setdefault(e.thread.tid, []).append(e)
    for t_events in by_thread.values():
        t_events.sort(key=lambda x: x.po_idx)
        for i in range(len(t_events)):
            for j in range(i + 1, len(t_events)):
                po.add((t_events[i].eid, t_events[j].eid))

    po_loc = {
        (u, v) for (u, v) in po
        if by_id[u].kind in {"W", "R"} and by_id[v].kind in {"W", "R"} and by_id[u].addr == by_id[v].addr
    }

    # 2. From-reads (fr): read-from-init precedes all writes to that address; else ~rf;co
    reads_from_write = {r for (_, r) in rf}
    fr: set[tuple[str, str]] = set()
    for w, r in rf:
        for w2_u, w2_v in co:
            if w2_u == w:
                fr.add((r, w2_v))
    for e in events:
        if e.kind == "R" and e.eid not in reads_from_write:
            for w in events:
                if w.kind == "W" and w.addr == e.addr:
                    fr.add((e.eid, w.eid))

    # 3. Observation order (PTX 8.9.2): morally strong rf (no RMWs needed for these litmus tests)
    obs = {(w, r) for (w, r) in rf if morally_strong(by_id[w], by_id[r])}

    # 4. Release / Acquire patterns (PTX 8.8)
    # Release pattern: (first_op, write_op)
    rel_patterns: list[tuple[str, str]] = []
    for e in events:
        if e.kind == "W" and e.sem in {"release", "acq_rel"}:
            rel_patterns.append((e.eid, e.eid))
        if e.kind == "F" and e.sem in {"release", "acq_rel", "sc"}:
            for w in events:
                if w.kind == "W" and w.is_strong and (e.eid, w.eid) in po:
                    rel_patterns.append((e.eid, w.eid))

    # Acquire pattern: (read_op, last_op)
    acq_patterns: list[tuple[str, str]] = []
    for e in events:
        if e.kind == "R" and e.sem in {"acquire", "acq_rel"}:
            acq_patterns.append((e.eid, e.eid))
        if e.kind == "F" and e.sem in {"acquire", "acq_rel", "sc"}:
            for r in events:
                if r.kind == "R" and r.is_strong and (r.eid, e.eid) in po:
                    acq_patterns.append((r.eid, e.eid))

    # 5. Synchronizes-with (PTX 8.9.4):
    # (a) Release pattern X -> Acquire pattern Y if write in X obs read in Y and first(X), last(Y) morally strong
    sw: set[tuple[str, str]] = set()
    sw_scopes: dict[tuple[str, str], Scope] = {}
    for x_first, x_w in rel_patterns:
        for y_r, y_last in acq_patterns:
            if (x_w, y_r) in obs and morally_strong(by_id[x_first], by_id[y_last]):
                sw.add((x_first, y_last))
                sw_scopes[(x_first, y_last)] = min(
                    by_id[x_first].scope, by_id[y_last].scope, key=lambda s: s.value
                )
    # (b) Fence-SC order between morally strong fence.sc pairs
    for f1, f2 in sc:
        e1, e2 = by_id[f1], by_id[f2]
        if e1.kind == "F" and e2.kind == "F" and e1.sem == "sc" and e2.sem == "sc" and morally_strong(e1, e2):
            sw.add((f1, f2))
            sw_scopes[(f1, f2)] = min(e1.scope, e2.scope, key=lambda s: s.value)

    # 6. Base causality order (PTX 8.9.5) vs HRF-direct (equal-scope non-transitive chains)
    if not hrf_direct_mode:
        # Transitive closure of (po U sw) that traverses at least one edge
        base_cause = transitive_closure(all_ids, po | sw)
    else:
        # HRF-direct restricts inter-thread chains to identical scope levels
        base_cause = set(po)
        for s in Scope:
            scoped_sw = {edge for edge, es in sw_scopes.items() if es == s}
            base_cause |= transitive_closure(all_ids, po | scoped_sw)

    # 7. Proxy-preserved base causality order (PTX ISA 9.5 Section 8.9.5)
    # Two memory ops X -> Y in base_cause are proxy-preserved iff:
    #  - Both use generic proxy (same address), OR
    #  - Both use the same proxy and same CTA, OR
    #  - There exists a matching proxy fence F along a base_cause path X ->* F ->* Y
    proxy_preserved: set[tuple[str, str]] = set()
    for u, v in base_cause:
        eu, ev = by_id[u], by_id[v]
        if eu.kind not in {"W", "R"} or ev.kind not in {"W", "R"}:
            proxy_preserved.add((u, v))
            continue
        if eu.proxy == Proxy.GENERIC and ev.proxy == Proxy.GENERIC:
            proxy_preserved.add((u, v))
        elif eu.proxy == ev.proxy and scope_includes(eu.thread, Scope.CTA, ev.thread):
            proxy_preserved.add((u, v))
        else:
            # Check for a bi-directional or matching uni-directional proxy fence on a base_cause path
            for f in events:
                if f.kind != "F_PROXY":
                    continue
                if (u == f.eid or (u, f.eid) in base_cause) and (f.eid == v or (f.eid, v) in base_cause):
                    # Bi-directional generic <-> async fence (e.g., fence.proxy.async.shared::cta)
                    proxies_pair = {eu.proxy, ev.proxy}
                    fence_pair = {f.proxy_from, f.proxy_to}
                    if proxies_pair == fence_pair:
                        proxy_preserved.add((u, v))
                        break

    # 8. Causality order (PTX 8.9.5): proxy_preserved U (obs ; proxy_preserved)
    cause = set(proxy_preserved)
    for w, r in obs:
        for u, v in proxy_preserved:
            if u == r:
                cause.add((w, v))

    # 9. Check axioms
    violations: list[str] = []

    # Axiom: Coherence ([W]; cause; [W] in co)
    for u, v in cause:
        if by_id[u].kind == "W" and by_id[v].kind == "W" and by_id[u].addr == by_id[v].addr:
            if (u, v) not in co:
                violations.append(f"Coherence: {u} -cause-> {v} missing from co")

    # Axiom: Fence-SC (irreflexive(sc; cause))
    for f1, f2 in sc:
        if (f2, f1) in cause:
            violations.append(f"Fence-SC: cycle {f1} -sc-> {f2} -cause-> {f1}")

    # Axiom: SC-per-Location (acyclic(strong(rf U co U fr) U po_loc))
    strong_com = {(u, v) for (u, v) in (rf | co | fr) if morally_strong(by_id[u], by_id[v])}
    sc_loc_tc = transitive_closure(all_ids, strong_com | po_loc)
    for n in all_ids:
        if (n, n) in sc_loc_tc:
            violations.append(f"SC-per-Location: cycle through {n}")
            break

    # Axiom: Causality (irreflexive((rf U fr); cause))
    for u, v in (rf | fr):
        if (v, u) in cause:
            violations.append(f"Causality: cycle {u} -(rf|fr)-> {v} -cause-> {u}")

    # Data-race detection (PTX 8.7.1)
    races: list[tuple[str, str]] = []
    for i, e1 in enumerate(events):
        if e1.kind not in {"W", "R"}:
            continue
        for e2 in events[i + 1 :]:
            if e2.kind not in {"W", "R"} or e1.addr != e2.addr:
                continue
            if e1.kind == "R" and e2.kind == "R":
                continue
            if not morally_strong(e1, e2) and (e1.eid, e2.eid) not in cause and (e2.eid, e1.eid) not in cause:
                races.append((e1.eid, e2.eid))

    return {
        "allowed": len(violations) == 0,
        "violations": violations,
        "races": races,
        "sw": sorted(sw),
    }


def check_vulkan_availability_visibility(
    events: list[Event],
    rf: set[tuple[str, str]],
    w_eid: str,
    r_eid: str,
    chains_enabled: bool,
) -> dict[str, Any]:
    """Check Vulkan Memory Model location-order between non-atomic W and R.

    Follows Khronos Vulkan-Docs appendices/memorymodel.adoc L865-891 & L1056-1068:
    - Without vulkanMemoryModelAvailabilityVisibilityChains (chains_enabled=False),
      availability/visibility chains have maximum length 1: W's own availability op
      must directly reach a domain D shared by both W and R, and R's own visibility
      op must pull directly from D.
    - With chains_enabled=True, an intermediate agent in W's destination domain can
      extend availability to a broader domain via happens-before.
    """
    res = check_ptx_execution(events, rf=rf, co=set(), hrf_direct_mode=False)
    by_id = {e.eid: e for e in events}
    all_ids = set(by_id.keys())

    # Build happens-before edges (po U sw) for non-atomic ordering
    po: set[tuple[str, str]] = set()
    by_thread: dict[str, list[Event]] = {}
    for e in events:
        by_thread.setdefault(e.thread.tid, []).append(e)
    for t_events in by_thread.values():
        t_events.sort(key=lambda x: x.po_idx)
        for i in range(len(t_events)):
            for j in range(i + 1, len(t_events)):
                po.add((t_events[i].eid, t_events[j].eid))
    hb = transitive_closure(all_ids, po | set(res["sw"]))

    w = by_id[w_eid]
    r = by_id[r_eid]

    # Minimum domain covering both w and r
    if scope_includes(w.thread, Scope.CTA, r.thread):
        needed_domain = Scope.CTA
    elif scope_includes(w.thread, Scope.GPU, r.thread):
        needed_domain = Scope.GPU
    else:
        needed_domain = Scope.SYS

    # Collect availability ops happening-after (or at) w on the same agent/domain
    av_ops = [e for e in events if e.vk_make_avail_domain is not None]
    vis_ops = [e for e in events if e.vk_make_vis_domain is not None]

    # Compute reachable availability domains for W
    # Step 1: length-1 availability ops executed by w's thread with w ->^rcpo av1
    reached_domains: list[tuple[Event, Scope]] = []
    for av in av_ops:
        if av.thread.tid == w.thread.tid and (av.eid == w.eid or (w.eid, av.eid) in po):
            assert av.vk_make_avail_domain is not None
            reached_domains.append((av, av.vk_make_avail_domain))

    if chains_enabled:
        # Allow availability chain expansion: av_next in dual scope of dom_cur with av_cur ->_hb av_next
        changed = True
        while changed:
            changed = False
            for av_cur, dom_cur in list(reached_domains):
                for av_nxt in av_ops:
                    assert av_nxt.vk_make_avail_domain is not None
                    if (
                        av_nxt.vk_make_avail_domain.value > dom_cur.value
                        and scope_includes(av_cur.thread, dom_cur, av_nxt.thread)
                        and (av_cur.eid, av_nxt.eid) in hb
                    ):
                        entry = (av_nxt, av_nxt.vk_make_avail_domain)
                        if entry not in reached_domains:
                            reached_domains.append(entry)
                            changed = True

    # Check if any reached domain >= needed_domain happens-before a visibility op covering r
    location_ordered = False
    for av_end, dom in reached_domains:
        if dom.value < needed_domain.value:
            continue
        for vis in vis_ops:
            assert vis.vk_make_vis_domain is not None
            if (
                vis.vk_make_vis_domain.value >= needed_domain.value
                and vis.thread.tid == r.thread.tid
                and (vis.eid == r.eid or (vis.eid, r.eid) in po)
                and (av_end.eid, vis.eid) in hb
            ):
                location_ordered = True
                break
        if location_ordered:
            break

    return {
        "chains_enabled": chains_enabled,
        "needed_domain": needed_domain.name,
        "location_ordered": location_ordered,
        "stale_read_allowed_or_race": not location_ordered,
    }


def run_scoped_memory_litmus_suite() -> dict[str, Any]:
    tA = ThreadLoc("T_A", cta=0, cluster=0, gpu=0)
    tB = ThreadLoc("T_B", cta=0, cluster=0, gpu=0)  # Same CTA as A
    tC = ThreadLoc("T_C", cta=1, cluster=0, gpu=0)  # Different CTA, same GPU

    results: dict[str, Any] = {}

    # Litmus 1: Direct mismatched scope (A: rel.cta -> C: acq.gpu, different CTAs), testing stale r_x == 0
    e_l1 = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("W_f", tA, 1, "W", "f", 1, "release", Scope.CTA),
        Event("R_f", tC, 0, "R", "f", 1, "acquire", Scope.GPU),
        Event("R_x", tC, 1, "R", "x", 0, "weak", Scope.THREAD),
    ]
    r_l1 = check_ptx_execution(e_l1, rf={("W_f", "R_f")}, co=set())
    assert r_l1["allowed"] is True, "Direct CTA->GPU mismatch across CTAs must allow stale read"
    assert ("W_x", "R_x") in r_l1["races"]
    results["1_mp_direct_cta_to_gpu_mismatch"] = r_l1

    # Litmus 2: Chain with broken second hop (A: rel.cta -> B: acq.cta; rel.cta -> C: acq.gpu)
    e_l2 = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("W_f1", tA, 1, "W", "f1", 1, "release", Scope.CTA),
        Event("R_f1", tB, 0, "R", "f1", 1, "acquire", Scope.CTA),
        Event("W_f2", tB, 1, "W", "f2", 1, "release", Scope.CTA),   # BUG: .cta excludes tC
        Event("R_f2", tC, 0, "R", "f2", 1, "acquire", Scope.GPU),
        Event("R_x", tC, 1, "R", "x", 0, "weak", Scope.THREAD),
    ]
    r_l2 = check_ptx_execution(e_l2, rf={("W_f1", "R_f1"), ("W_f2", "R_f2")}, co=set())
    assert r_l2["allowed"] is True, "Broken second hop (.cta -> .gpu across CTAs) must allow stale read"
    results["2_mp_chain_broken_second_hop"] = r_l2

    # Litmus 3: Mixed-scope chain A(CTA0) -.cta-> B(CTA0) -.gpu-> C(CTA1)
    # Discriminates PTX cumulative cause_base & Vulkan(chains=True) vs HRF-direct & Vulkan(chains=False)
    e_l3 = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("W_f1", tA, 1, "W", "f1", 1, "release", Scope.CTA, vk_make_avail_domain=Scope.CTA),
        Event("R_f1", tB, 0, "R", "f1", 1, "acquire", Scope.CTA, vk_make_vis_domain=Scope.CTA),
        Event("W_f2", tB, 1, "W", "f2", 1, "release", Scope.GPU, vk_make_avail_domain=Scope.GPU),
        Event("R_f2", tC, 0, "R", "f2", 1, "acquire", Scope.GPU, vk_make_vis_domain=Scope.GPU),
        Event("R_x", tC, 1, "R", "x", 0, "weak", Scope.THREAD),
    ]
    rf_l3 = {("W_f1", "R_f1"), ("W_f2", "R_f2")}
    r_l3_ptx = check_ptx_execution(e_l3, rf=rf_l3, co=set(), hrf_direct_mode=False)
    r_l3_hrf = check_ptx_execution(e_l3, rf=rf_l3, co=set(), hrf_direct_mode=True)
    r_l3_vk_no_chains = check_vulkan_availability_visibility(e_l3, rf_l3, "W_x", "R_x", chains_enabled=False)
    r_l3_vk_chains = check_vulkan_availability_visibility(e_l3, rf_l3, "W_x", "R_x", chains_enabled=True)

    assert r_l3_ptx["allowed"] is False, "PTX cumulative cause_base forbids stale read when every hop is morally strong"
    assert r_l3_hrf["allowed"] is True, "HRF-direct forbids composing .cta and .gpu scopes transitively"
    assert r_l3_vk_no_chains["stale_read_allowed_or_race"] is True, "Vulkan without AvailabilityVisibilityChains is a data race"
    assert r_l3_vk_chains["stale_read_allowed_or_race"] is False, "Vulkan with AvailabilityVisibilityChains establishes location-order"
    results["3_mp_chain_cta_then_gpu_model_comparison"] = {
        "ptx_stale_allowed": r_l3_ptx["allowed"],
        "hrf_direct_stale_allowed": r_l3_hrf["allowed"],
        "vulkan_chains_false_race": r_l3_vk_no_chains["stale_read_allowed_or_race"],
        "vulkan_chains_true_race": r_l3_vk_chains["stale_read_allowed_or_race"],
    }

    # Litmus 4: Sound .gpu-scoped synchronization A(CTA0) -.gpu-> C(CTA1)
    e_l4 = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("W_f", tA, 1, "W", "f", 1, "release", Scope.GPU, vk_make_avail_domain=Scope.GPU),
        Event("R_f", tC, 0, "R", "f", 1, "acquire", Scope.GPU, vk_make_vis_domain=Scope.GPU),
        Event("R_x", tC, 1, "R", "x", 0, "weak", Scope.THREAD),
    ]
    r_l4_ptx = check_ptx_execution(e_l4, rf={("W_f", "R_f")}, co=set())
    r_l4_vk = check_vulkan_availability_visibility(e_l4, {("W_f", "R_f")}, "W_x", "R_x", chains_enabled=False)
    assert r_l4_ptx["allowed"] is False
    assert r_l4_vk["location_ordered"] is True
    results["4_mp_sound_gpu_scope"] = {
        "ptx_stale_allowed": r_l4_ptx["allowed"],
        "vulkan_no_chains_location_ordered": r_l4_vk["location_ordered"],
    }

    # Litmus 5: Store Buffering (SB) with mismatched fence.sc (.cta vs .gpu) vs sound (.gpu vs .gpu)
    e_sb_bad = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("F1", tA, 1, "F", None, None, "sc", Scope.CTA),  # BUG: .cta excludes tC
        Event("R_y", tA, 2, "R", "y", 0, "weak", Scope.THREAD),
        Event("W_y", tC, 0, "W", "y", 1, "weak", Scope.THREAD),
        Event("F2", tC, 1, "F", None, None, "sc", Scope.GPU),
        Event("R_x", tC, 2, "R", "x", 0, "weak", Scope.THREAD),
    ]
    # Because F1 and F2 are not morally strong, sc may leave them unordered!
    r_sb_bad = check_ptx_execution(e_sb_bad, rf=set(), co=set(), sc=set())
    assert r_sb_bad["allowed"] is True, "Mismatched fence.sc (.cta vs .gpu) allows SB r0=0, r1=0"

    e_sb_good = [
        Event("W_x", tA, 0, "W", "x", 1, "weak", Scope.THREAD),
        Event("F1", tA, 1, "F", None, None, "sc", Scope.GPU),
        Event("R_y", tA, 2, "R", "y", 0, "weak", Scope.THREAD),
        Event("W_y", tC, 0, "W", "y", 1, "weak", Scope.THREAD),
        Event("F2", tC, 1, "F", None, None, "sc", Scope.GPU),
        Event("R_x", tC, 2, "R", "x", 0, "weak", Scope.THREAD),
    ]
    # Any total sc order over morally strong F1, F2 must forbid (0, 0)
    r_sb_good_12 = check_ptx_execution(e_sb_good, rf=set(), co=set(), sc={("F1", "F2")})
    r_sb_good_21 = check_ptx_execution(e_sb_good, rf=set(), co=set(), sc={("F2", "F1")})
    assert r_sb_good_12["allowed"] is False and r_sb_good_21["allowed"] is False
    results["5_sb_fence_sc_scope_mismatch_vs_sound"] = {
        "mismatched_cta_gpu_allows_00": r_sb_bad["allowed"],
        "sound_gpu_gpu_allows_00_f1_lt_f2": r_sb_good_12["allowed"],
        "sound_gpu_gpu_allows_00_f2_lt_f1": r_sb_good_21["allowed"],
    }

    # Litmus 6: Hopper/Blackwell cross-proxy SMEM write (generic) -> TMA store (async)
    e_proxy_bad = [
        Event("W_smem", tA, 0, "W", "smem_tile", 1, "weak", Scope.THREAD, proxy=Proxy.GENERIC),
        Event("TMA_R_smem", tA, 1, "R", "smem_tile", 0, "weak", Scope.THREAD, proxy=Proxy.ASYNC),
    ]
    r_proxy_bad = check_ptx_execution(e_proxy_bad, rf=set(), co=set())
    assert r_proxy_bad["allowed"] is True, "Missing fence.proxy.async.shared::cta allows TMA to read stale SMEM"

    e_proxy_good = [
        Event("W_smem", tA, 0, "W", "smem_tile", 1, "weak", Scope.THREAD, proxy=Proxy.GENERIC),
        Event(
            "F_proxy", tA, 1, "F_PROXY", None, None, "acq_rel", Scope.CTA,
            proxy=Proxy.GENERIC, proxy_from=Proxy.GENERIC, proxy_to=Proxy.ASYNC,
        ),
        Event("TMA_R_smem", tA, 2, "R", "smem_tile", 0, "weak", Scope.THREAD, proxy=Proxy.ASYNC),
    ]
    r_proxy_good = check_ptx_execution(e_proxy_good, rf=set(), co=set())
    assert r_proxy_good["allowed"] is False, "fence.proxy.async.shared::cta forbids TMA reading stale SMEM"
    results["6_tma_cross_proxy_fence"] = {
        "without_fence_proxy_async_stale_allowed": r_proxy_bad["allowed"],
        "with_fence_proxy_async_stale_allowed": r_proxy_good["allowed"],
    }

    return results


# =============================================================================
# PART 2: EXPLICIT-STATE BFS MODEL CHECKER FOR N-STAGE MBARRIER PIPELINE
# =============================================================================

@dataclass(frozen=True)
class MBarrierState:
    phase: int            # 0 or 1 (PTX 9.7.15.16.5: initialized to phase 0)
    expected_arr: int     # Initialized expected arrival count
    pending_arr: int      # Current pending arrival count
    tx_count: int         # Current transaction byte count (PTX 9.7.15.16.6)


def mbarrier_try_complete(b: MBarrierState) -> tuple[MBarrierState, bool]:
    """PTX 9.7.15.16.8: phase completes atomically when pending_arr == 0 and tx_count == 0."""
    if b.pending_arr == 0 and b.tx_count == 0:
        return MBarrierState(
            phase=b.phase ^ 1,
            expected_arr=b.expected_arr,
            pending_arr=b.expected_arr,
            tx_count=0,
        ), True
    return b, False


def mbarrier_try_wait_parity(b: MBarrierState, expected_parity: int) -> bool:
    """PTX 9.7.15.16.19: returns True iff expected_parity is the immediately preceding phase (i.e. != current phase)."""
    return expected_parity != b.phase


def model_check_mbarrier_pipeline(
    num_stages: int = 2,
    total_tiles: int = 5,
    tile_bytes: int = 128,
    init_prod_phase: int = 1,
    init_cons_phase: int = 0,
    flip_prod_parity: bool = True,
    flip_cons_parity: bool = True,
    producer_arriving_lanes: int = 1,
    expect_tx_delta: int = 0,
) -> dict[str, Any]:
    """Exhaustive BFS state-space explorer over Producer warp, TMA async engine, and Consumer warp."""

    # Producer PCs:
    # 0 = WAIT_EMPTY (try_wait.parity empty[p_stage], p_phase)
    # 1 = ISSUE_TMA  (mbarrier.arrive.expect_tx full[p_stage] + launch DMA)
    # Consumer PCs:
    # 0 = WAIT_FULL  (try_wait.parity full[c_stage], c_phase)
    # 1 = READ_AND_RELEASE (read slot[c_stage], mbarrier.arrive empty[c_stage])
    # Slot status: 0=FREE, 1=DMA_WRITING, 2=READY, 3=CONSUMING

    init_full = tuple(MBarrierState(0, 1, 1, 0) for _ in range(num_stages))
    init_empty = tuple(MBarrierState(0, 1, 1, 0) for _ in range(num_stages))
    # Track: (p_pc, p_tile, p_stage, p_phase, c_pc, c_tile, c_stage, c_phase,
    #         slot_status, slot_gen, dma_inflight_bytes, full_bars, empty_bars)
    start_state = (
        0, 0, 0, init_prod_phase,
        0, 0, 0, init_cons_phase,
        tuple(0 for _ in range(num_stages)),
        tuple(-1 for _ in range(num_stages)),
        tuple(0 for _ in range(num_stages)),
        init_full,
        init_empty,
    )

    visited: set[Any] = {start_state}
    parent: dict[Any, tuple[Any, str]] = {}
    q: deque[Any] = deque([start_state])

    terminal_ok = 0
    deadlocks: list[list[str]] = []
    safety_violations: list[tuple[str, list[str]]] = []

    def reconstruct_trace(st: Any) -> list[str]:
        trace: list[str] = []
        cur = st
        while cur in parent:
            prev, act = parent[cur]
            trace.append(act)
            cur = prev
        trace.reverse()
        return trace

    while q:
        st = q.popleft()
        (
            p_pc, p_tile, p_stage, p_phase,
            c_pc, c_tile, c_stage, c_phase,
            slot_st, slot_gen, dma_bytes,
            full_bars, empty_bars,
        ) = st

        if p_tile == total_tiles and c_tile == total_tiles and all(b == 0 for b in dma_bytes):
            terminal_ok += 1
            continue

        transitions: list[tuple[str, Any]] = []

        # --- Action 1: Producer WAIT_EMPTY ---
        if p_tile < total_tiles and p_pc == 0:
            if mbarrier_try_wait_parity(empty_bars[p_stage], p_phase):
                nxt = (
                    1, p_tile, p_stage, p_phase,
                    c_pc, c_tile, c_stage, c_phase,
                    slot_st, slot_gen, dma_bytes,
                    full_bars, empty_bars,
                )
                transitions.append((f"P:wait_empty(slot={p_stage},par={p_phase})->OK", nxt))

        # --- Action 2: Producer ISSUE_TMA (arrive.expect_tx + async TMA launch) ---
        if p_tile < total_tiles and p_pc == 1:
            # Safety check: cannot overwrite a slot currently being DMA-written or consumed!
            if slot_st[p_stage] in (1, 3):
                kind = "DMA_OVERLAP_RACE" if slot_st[p_stage] == 1 else "OVERWRITE_CONSUMING_SLOT_RACE"
                safety_violations.append((
                    f"{kind}: Producer writing tile {p_tile} into slot {p_stage} while state={slot_st[p_stage]} (gen={slot_gen[p_stage]})",
                    reconstruct_trace(st) + [f"P:issue_tma(tile={p_tile},slot={p_stage})"],
                ))
                break

            b = full_bars[p_stage]
            tx_add = max(0, tile_bytes + expect_tx_delta)
            # Model producer_arriving_lanes executing mbarrier.arrive.expect_tx on b
            b_cur = b
            underflow = False
            for lane in range(producer_arriving_lanes):
                b_cur = MBarrierState(
                    phase=b_cur.phase,
                    expected_arr=b_cur.expected_arr,
                    pending_arr=b_cur.pending_arr - 1,
                    tx_count=b_cur.tx_count + tx_add,
                )
                if b_cur.pending_arr < 0:
                    underflow = True
                    break
                b_cur, _ = mbarrier_try_complete(b_cur)

            if underflow:
                safety_violations.append((
                    f"ARRIVAL_UNDERFLOW_UB: {producer_arriving_lanes} lanes arrived on full[{p_stage}] (expected={b.expected_arr})",
                    reconstruct_trace(st) + [f"P:arrive_expect_tx_x{producer_arriving_lanes}(slot={p_stage})"],
                ))
                break

            new_full = list(full_bars)
            new_full[p_stage] = b_cur
            new_slot_st = list(slot_st)
            new_slot_st[p_stage] = 1  # DMA_WRITING
            new_slot_gen = list(slot_gen)
            new_slot_gen[p_stage] = p_tile
            new_dma = list(dma_bytes)
            new_dma[p_stage] = tile_bytes

            next_stage = (p_stage + 1) % num_stages
            next_phase = (p_phase ^ 1) if (flip_prod_parity and next_stage == 0) else p_phase

            nxt = (
                0, p_tile + 1, next_stage, next_phase,
                c_pc, c_tile, c_stage, c_phase,
                tuple(new_slot_st), tuple(new_slot_gen), tuple(new_dma),
                tuple(new_full), empty_bars,
            )
            transitions.append((
                f"P:issue_tma(tile={p_tile},slot={p_stage},lanes={producer_arriving_lanes},tx={tx_add})",
                nxt,
            ))

        # --- Action 3: Async TMA Engine completes a slot DMA (complete_tx) ---
        for s in range(num_stages):
            if dma_bytes[s] > 0:
                b = full_bars[s]
                rem_tx = b.tx_count - dma_bytes[s]
                if rem_tx < 0:
                    safety_violations.append((
                        f"TX_COUNT_UNDERFLOW_UB: TMA completed {dma_bytes[s]}B on full[{s}] with tx_count={b.tx_count}B",
                        reconstruct_trace(st) + [f"TMA:complete_tx(slot={s},bytes={dma_bytes[s]})"],
                    ))
                    break
                b_nxt, _ = mbarrier_try_complete(
                    MBarrierState(b.phase, b.expected_arr, b.pending_arr, rem_tx)
                )
                new_full = list(full_bars)
                new_full[s] = b_nxt
                new_dma = list(dma_bytes)
                new_dma[s] = 0
                new_slot_st = list(slot_st)
                # If consumer already raced into CONSUMING, preserve 3 so next check catches or flag now
                if new_slot_st[s] == 1:
                    new_slot_st[s] = 2  # READY
                nxt = (
                    p_pc, p_tile, p_stage, p_phase,
                    c_pc, c_tile, c_stage, c_phase,
                    tuple(new_slot_st), slot_gen, tuple(new_dma),
                    tuple(new_full), empty_bars,
                )
                transitions.append((f"TMA:complete_tx(slot={s},bytes={dma_bytes[s]})", nxt))
        if safety_violations:
            break

        # --- Action 4: Consumer WAIT_FULL ---
        if c_tile < total_tiles and c_pc == 0:
            if mbarrier_try_wait_parity(full_bars[c_stage], c_phase):
                # Safety check: slot MUST be READY with exact tile generation c_tile!
                if slot_st[c_stage] != 2 or slot_gen[c_stage] != c_tile:
                    safety_violations.append((
                        f"STALE_OR_INFLIGHT_READ_RACE: Consumer unblocked on full[{c_stage}] (par={c_phase}) "
                        f"expecting tile {c_tile}, found slot_state={slot_st[c_stage]}, slot_gen={slot_gen[c_stage]}",
                        reconstruct_trace(st) + [f"C:wait_full(slot={c_stage},par={c_phase})->PREMATURE_OK"],
                    ))
                    break
                new_slot_st = list(slot_st)
                new_slot_st[c_stage] = 3  # CONSUMING
                nxt = (
                    p_pc, p_tile, p_stage, p_phase,
                    1, c_tile, c_stage, c_phase,
                    tuple(new_slot_st), slot_gen, dma_bytes,
                    full_bars, empty_bars,
                )
                transitions.append((f"C:wait_full(slot={c_stage},par={c_phase},tile={c_tile})->OK", nxt))

        # --- Action 5: Consumer FINISH_READ & ARRIVE_EMPTY ---
        if c_tile < total_tiles and c_pc == 1:
            b = empty_bars[c_stage]
            b_nxt, _ = mbarrier_try_complete(
                MBarrierState(b.phase, b.expected_arr, b.pending_arr - 1, b.tx_count)
            )
            new_empty = list(empty_bars)
            new_empty[c_stage] = b_nxt
            new_slot_st = list(slot_st)
            new_slot_st[c_stage] = 0  # FREE
            next_c_stage = (c_stage + 1) % num_stages
            next_c_phase = (c_phase ^ 1) if (flip_cons_parity and next_c_stage == 0) else c_phase
            nxt = (
                p_pc, p_tile, p_stage, p_phase,
                0, c_tile + 1, next_c_stage, next_c_phase,
                tuple(new_slot_st), slot_gen, dma_bytes,
                full_bars, tuple(new_empty),
            )
            transitions.append((f"C:consume_and_arrive_empty(slot={c_stage},tile={c_tile})", nxt))

        if not transitions:
            deadlocks.append(reconstruct_trace(st))
            break

        for act, nxt in transitions:
            if nxt not in visited:
                visited.add(nxt)
                parent[nxt] = (st, act)
                q.append(nxt)

    return {
        "states_explored": len(visited),
        "terminal_ok_states": terminal_ok,
        "deadlock_found": len(deadlocks) > 0,
        "deadlock_trace": deadlocks[0] if deadlocks else None,
        "safety_violation": safety_violations[0][0] if safety_violations else None,
        "violation_trace": safety_violations[0][1] if safety_violations else None,
    }


def run_mbarrier_verification_suite() -> dict[str, Any]:
    out: dict[str, Any] = {}

    # 1. Sound 2-stage and 3-stage pipelines
    ok2 = model_check_mbarrier_pipeline(num_stages=2, total_tiles=5)
    assert not ok2["deadlock_found"] and ok2["safety_violation"] is None and ok2["terminal_ok_states"] > 0
    out["1_sound_2stage_pipeline"] = ok2

    ok3 = model_check_mbarrier_pipeline(num_stages=3, total_tiles=6)
    assert not ok3["deadlock_found"] and ok3["safety_violation"] is None and ok3["terminal_ok_states"] > 0
    out["2_sound_3stage_pipeline"] = ok3

    # 2. Bug: Wrong initial producer parity (0 instead of 1) -> immediate deadlock
    bug_init = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, init_prod_phase=0)
    assert bug_init["deadlock_found"] is True
    out["3_bug_wrong_initial_parity_deadlock"] = bug_init

    # 3a. Bug: Consumer omits phase parity flip on wraparound -> stale-tile / premature unblock race
    bug_cons_noflip = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, flip_cons_parity=False)
    assert bug_cons_noflip["safety_violation"] is not None and "STALE_OR_INFLIGHT_READ_RACE" in bug_cons_noflip["safety_violation"]
    out["4a_bug_missing_consumer_parity_flip_race"] = bug_cons_noflip

    # 3b. Bug: Producer omits phase parity flip on wraparound -> immediate DMA overwrite race on slot 0
    bug_prod_noflip = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, flip_prod_parity=False)
    assert bug_prod_noflip["safety_violation"] is not None and "DMA_OVERLAP_RACE" in bug_prod_noflip["safety_violation"]
    out["4b_bug_missing_producer_parity_flip_overwrite_race"] = bug_prod_noflip

    # 4. Bug: Non-elected 32 warp lanes arrive instead of 1 elect.sync leader -> arrival underflow UB
    bug_32lanes = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, producer_arriving_lanes=32)
    assert bug_32lanes["safety_violation"] is not None and "ARRIVAL_UNDERFLOW_UB" in bug_32lanes["safety_violation"]
    out["5_bug_non_elected_32_lane_arrive"] = bug_32lanes

    # 5. Bug: expect_tx byte-count mismatch (+64 extra bytes expected) -> permanent GPU hang
    bug_tx_hi = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, expect_tx_delta=64)
    assert bug_tx_hi["deadlock_found"] is True
    out["6_bug_expect_tx_overcount_hang"] = bug_tx_hi

    # 6. Bug: expect_tx undercount (-64 bytes expected) -> tx_count underflow UB
    bug_tx_lo = model_check_mbarrier_pipeline(num_stages=2, total_tiles=4, expect_tx_delta=-64)
    assert bug_tx_lo["safety_violation"] is not None and "TX_COUNT_UNDERFLOW_UB" in bug_tx_lo["safety_violation"]
    out["7_bug_expect_tx_undercount_ub"] = bug_tx_lo

    return out


# =============================================================================
# PART 3: W3C WGSL STATIC UNIFORMITY DEPENDENCY-GRAPH CHECKER
# =============================================================================

@dataclass
class UniformityGraph:
    """Implements the WGSL uniformity dependency graph (gpuweb/gpuweb wgsl/index.bs Section Uniformity)."""

    edges: dict[str, set[str]] = field(default_factory=dict)

    REQ_UNIFORM: str = "RequiredToBeUniform.error"
    MAY_NONUNIFORM: str = "MayBeNonUniform"

    def add_edge(self, src: str, dst: str) -> None:
        self.edges.setdefault(src, set()).add(dst)

    def find_violation_path(self) -> list[str] | None:
        """Return shortest path RequiredToBeUniform.error ->* MayBeNonUniform, or None if uniform."""
        q: deque[tuple[str, list[str]]] = deque([(self.REQ_UNIFORM, [self.REQ_UNIFORM])])
        seen = {self.REQ_UNIFORM}
        while q:
            u, path = q.popleft()
            if u == self.MAY_NONUNIFORM:
                return path
            for v in sorted(self.edges.get(u, ())):
                if v not in seen:
                    seen.add(v)
                    q.append((v, path + [v]))
        return None


def analyze_wgsl_stmt(
    g: UniformityGraph,
    cf: str,
    stmt: tuple[Any, ...],
    var_nodes: dict[str, str],
    counter: list[int],
) -> tuple[str, set[str]]:
    """Analyze a structured WGSL statement under control-flow node `cf`.

    Returns (exit_cf_node, behavior_set) following WGSL behaviors & uniformity rules
    (wgsl/index.bs L13130-L13260).
    """
    def fresh(prefix: str) -> str:
        counter[0] += 1
        return f"{prefix}_{counter[0]}"

    def analyze_expr(cur_cf: str, expr: tuple[Any, ...]) -> str:
        ekind = expr[0]
        if ekind == "const":
            return fresh("V_const")
        if ekind == "uniform_buf":
            return fresh("V_uniform")
        if ekind == "builtin_lid":
            v = fresh("V_lid")
            g.add_edge(v, g.MAY_NONUNIFORM)
            return v
        if ekind == "var":
            v = fresh(f"V_load_{expr[1]}")
            g.add_edge(v, var_nodes[expr[1]])
            return v
        if ekind == "binop":
            v = fresh("V_binop")
            v1 = analyze_expr(cur_cf, expr[1])
            v2 = analyze_expr(cur_cf, expr[2])
            g.add_edge(v, v1)
            g.add_edge(v, v2)
            return v
        raise ValueError(f"Unknown expr {expr}")

    kind = stmt[0]
    if kind == "seq":
        cur_cf = cf
        beh: set[str] = {"Next"}
        for sub in stmt[1]:
            if "Next" not in beh:
                break  # Statically unreachable statements do not contribute (wgsl L13164)
            cur_cf, sub_beh = analyze_wgsl_stmt(g, cur_cf, sub, var_nodes, counter)
            beh = (beh - {"Next"}) | sub_beh
        return cur_cf, beh

    if kind == "assign":
        _, name, rhs = stmt
        v_rhs = analyze_expr(cf, rhs)
        v_var = fresh(f"Var_{name}")
        # Variable uniformity depends on BOTH RHS value and controlling CF (wgsl value analysis)
        g.add_edge(v_var, v_rhs)
        g.add_edge(v_var, cf)
        var_nodes[name] = v_var
        return cf, {"Next"}

    if kind == "barrier":
        # workgroupBarrier() / subgroupAdd() requires uniform control flow
        call_node = fresh(f"Call_{stmt[1]}")
        g.add_edge(g.REQ_UNIFORM, call_node)
        g.add_edge(call_node, cf)
        return cf, {"Next"}

    if kind == "texture_sample":
        # textureSample requires BOTH uniform CF and uniform derivative-triggering execution
        call_node = fresh("Call_textureSample")
        v_coord = analyze_expr(cf, stmt[1])
        g.add_edge(g.REQ_UNIFORM, call_node)
        g.add_edge(call_node, cf)
        # Also model explicit uniform-value argument check if requested (e.g., subgroupBroadcast lane)
        if len(stmt) > 2 and stmt[2]:
            g.add_edge(call_node, v_coord)
        return cf, {"Next"}

    if kind == "return":
        return cf, {"Return"}

    if kind == "break":
        return cf, {"Break"}

    if kind == "break_if":
        v_cond = analyze_expr(cf, stmt[1])
        cf_end = fresh("CF_break_if")
        g.add_edge(cf_end, v_cond)
        g.add_edge(cf_end, cf)
        return cf_end, {"Next", "Break"}

    if kind == "if":
        _, cond, s_then, s_else = stmt
        v_cond = analyze_expr(cf, cond)
        v_branch = fresh("CF_branch")
        g.add_edge(v_branch, v_cond)
        g.add_edge(v_branch, cf)

        vars_then = dict(var_nodes)
        vars_else = dict(var_nodes)
        cf1, beh1 = analyze_wgsl_stmt(g, v_branch, s_then, vars_then, counter)
        cf2, beh2 = analyze_wgsl_stmt(g, v_branch, s_else, vars_else, counter)

        # Merge variable value nodes across branches
        for name in set(vars_then) | set(vars_else):
            t_node = vars_then.get(name)
            e_node = vars_else.get(name)
            if t_node != e_node:
                merged = fresh(f"VarMerge_{name}")
                if t_node:
                    g.add_edge(merged, t_node)
                if e_node:
                    g.add_edge(merged, e_node)
                g.add_edge(merged, v_branch)
                var_nodes[name] = merged

        beh = beh1 | beh2
        # WGSL wgsl/index.bs L13168-13178:
        # If behavior == {Next}, reconvergence restores CF; otherwise CFend -> {CF1, CF2}.
        if beh == {"Next"}:
            return cf, {"Next"}
        cf_end = fresh("CF_if_end")
        if "Next" in beh1:
            g.add_edge(cf_end, cf1)
        if "Next" in beh2:
            g.add_edge(cf_end, cf2)
        if not ("Next" in beh1 or "Next" in beh2):
            g.add_edge(cf_end, cf1)
            g.add_edge(cf_end, cf2)
        return cf_end, beh

    if kind == "loop":
        # WGSL wgsl/index.bs L13181-13199: CF' -> {CF1, CF} if s1 intersects {Next, Continue}
        _, body = stmt
        cf_hdr = fresh("CF_loop_hdr")
        g.add_edge(cf_hdr, cf)
        cf1, beh1 = analyze_wgsl_stmt(g, cf_hdr, body, var_nodes, counter)
        if beh1 & {"Next", "Continue"}:
            g.add_edge(cf_hdr, cf1)
        exit_beh = (beh1 - {"Break", "Continue"}) | ({"Next"} if "Break" in beh1 else set())
        if "Return" not in beh1:
            return cf, exit_beh
        return cf1, exit_beh

    raise ValueError(f"Unknown stmt {stmt}")


def run_wgsl_uniformity_suite() -> dict[str, Any]:
    cases: dict[str, tuple[Any, ...]] = {
        "1_uniform_if_barrier_pass": (
            "if",
            ("uniform_buf",),
            ("barrier", "workgroupBarrier"),
            ("seq", []),
        ),
        "2_divergent_if_barrier_reject": (
            "if",
            ("builtin_lid",),
            ("barrier", "workgroupBarrier"),
            ("seq", []),
        ),
        "3_divergent_early_return_then_barrier_reject": (
            "seq",
            [
                ("if", ("builtin_lid",), ("return",), ("seq", [])),
                ("barrier", "workgroupBarrier"),
            ],
        ),
        "4_divergent_break_if_loop_subgroup_reject": (
            "loop",
            (
                "seq",
                [
                    ("barrier", "subgroupAdd"),
                    ("break_if", ("builtin_lid",)),
                ],
            ),
        ),
        "5_reconverged_if_then_barrier_pass": (
            "seq",
            [
                (
                    "if",
                    ("builtin_lid",),
                    ("assign", "x", ("const", 1)),
                    ("assign", "x", ("const", 2)),
                ),
                ("barrier", "workgroupBarrier"),
            ],
        ),
        "6_reconverged_if_nonuniform_value_to_uniform_arg_reject": (
            "seq",
            [
                (
                    "if",
                    ("builtin_lid",),
                    ("assign", "x", ("const", 1)),
                    ("assign", "x", ("const", 2)),
                ),
                ("texture_sample", ("var", "x"), True),
            ],
        ),
    }

    expected_reject = {
        "1_uniform_if_barrier_pass": False,
        "2_divergent_if_barrier_reject": True,
        "3_divergent_early_return_then_barrier_reject": True,
        "4_divergent_break_if_loop_subgroup_reject": True,
        "5_reconverged_if_then_barrier_pass": False,
        "6_reconverged_if_nonuniform_value_to_uniform_arg_reject": True,
    }

    results: dict[str, Any] = {}
    for name, prog in cases.items():
        g = UniformityGraph()
        analyze_wgsl_stmt(g, "CF_start", prog, {"x": "Var_x_init"}, [0])
        path = g.find_violation_path()
        rejected = path is not None
        assert rejected == expected_reject[name], f"WGSL case {name}: expected rejected={expected_reject[name]}, got {rejected} (path={path})"
        results[name] = {"rejected": rejected, "violation_path": path}
    return results


def main() -> int:
    summary = {
        "part1_scoped_memory_litmus": run_scoped_memory_litmus_suite(),
        "part2_mbarrier_pipeline_model_checker": run_mbarrier_verification_suite(),
        "part3_wgsl_uniformity_checker": run_wgsl_uniformity_suite(),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
