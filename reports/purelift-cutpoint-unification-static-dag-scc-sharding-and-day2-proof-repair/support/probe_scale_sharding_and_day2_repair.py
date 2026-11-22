#!/usr/bin/env python3
"""Self-contained verification probe for:
1. MemoryState R3 AddressTakenPreserved soundness vs. unsafe .indirect StorageLive deletion;
2. Depth-1 ShardCert static-DAG nominal/fixed-slot sharding + ShardAuditReceiptV2 Merkle linker;
3. Canonical RPO locally-nameless H_unit hashing + Const::Unevaluated cone + Cone-(G, Delta) reuse.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


# --- Probe 1: MemoryState R3 AddressTakenPreserved Soundness Witness ---
def run_mem_prog(stmts: List[Tuple[str, int]], indirect_locals: Set[int]) -> Tuple[int, Dict[int, int]]:
    next_alloc = 1
    slot_alloc: Dict[int, int] = {}
    for op, loc in stmts:
        if op == "StorageLive":
            if loc in indirect_locals:
                slot_alloc[loc] = next_alloc
                next_alloc += 1
        elif op == "StorageDead":
            slot_alloc.pop(loc, None)
    return next_alloc, slot_alloc


def probe_memory_state_r3() -> str:
    # Local 1 is dead scalar (non-indirect); local 2 is address-taken (.indirect); local 3 is live .indirect.
    orig = [("StorageLive", 1), ("StorageLive", 2), ("StorageLive", 3), ("StorageDead", 1)]
    indirect = {2, 3}
    base_next, base_allocs = run_mem_prog(orig, indirect)

    # Unsound R3: deletes StorageLive(2) because local 2 is never dereferenced, shifting local 3's AllocId!
    unsound_r3 = [s for s in orig if s[1] not in {1, 2}]
    bad_next, bad_allocs = run_mem_prog(unsound_r3, indirect)
    assert bad_allocs[3] != base_allocs[3] and bad_next != base_next

    # Sound R3 (AddressTakenPreserved): compacts non-indirect local 1 only, keeping indirect local 2 pinned.
    sound_r3 = [s for s in orig if s[1] != 1]
    ok_next, ok_allocs = run_mem_prog(sound_r3, indirect)
    assert ok_allocs == base_allocs and ok_next == base_next
    return f"PROBE1_MEM_R3_OK: base_alloc3={base_allocs[3]} unsound_alloc3={bad_allocs[3]} sound_alloc3={ok_allocs[3]}"


# --- Probe 2: Depth-1 ShardCert Static-DAG Bin-Packing + ShardAuditReceiptV2 Merkle Linker ---
def tarjan_sccs(nodes: List[str], edges: Dict[str, List[str]]) -> List[List[str]]:
    cnt, idx, low, st, on, out = 0, {}, {}, [], set(), []

    def sc(v: str) -> None:
        nonlocal cnt
        idx[v] = low[v] = cnt
        cnt += 1
        st.append(v)
        on.add(v)
        for w in edges.get(v, []):
            if w not in idx:
                sc(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop()
                on.remove(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))

    for v in sorted(nodes):
        if v not in idx:
            sc(v)
    return out


def pack_sccs_into_static_slots(sccs: List[List[str]], num_slots: int) -> Dict[int, List[str]]:
    # Deterministic least-loaded bin-packing keeping every multi-node SCC indivisible.
    slots: Dict[int, List[str]] = {i: [] for i in range(num_slots)}
    for comp in sorted(sccs, key=lambda c: (-len(c), c[0])):
        target = min(range(num_slots), key=lambda i: (len(slots[i]), i))
        slots[target].extend(comp)
    return {k: sorted(v) for k, v in slots.items()}


@dataclass(frozen=True)
class ShardReceipt:
    shard_id: str
    rank: int
    olean_sha: str
    owned: Tuple[str, ...]
    # stub_name -> (provider_shard, provider_rank, expected_h_sig, observed_provider_olean, observed_provider_digest)
    stubs: Dict[str, Tuple[str, int, str, str, str]]
    local_axioms: Tuple[str, ...]
    local_opaques: Tuple[str, ...]
    digest: str


def compute_receipt_digest(
    shard_id: str,
    rank: int,
    olean_sha: str,
    owned: Tuple[str, ...],
    stubs: Dict[str, Tuple[str, int, str, str, str]],
    ax_trans: Tuple[str, ...],
    opq_trans: Tuple[str, ...],
) -> str:
    payload = {
        "shard_id": shard_id,
        "rank": rank,
        "olean_sha": olean_sha,
        "owned": list(owned),
        "stubs": {k: list(v) for k, v in sorted(stubs.items())},
        "ax_trans": list(ax_trans),
        "opq_trans": list(opq_trans),
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:16]


def verify_shard_link(
    receipts: Dict[str, ShardReceipt],
    live_sigs: Dict[str, str],
    roots: Set[str],
    allowed_axioms: Set[str],
) -> Tuple[bool, str]:
    owner: Dict[str, str] = {}
    for sid, r in receipts.items():
        for name in r.owned:
            if name in owner:
                return False, f"DUP_OWNER:{name}"
            owner[name] = sid
    for rt in sorted(roots):
        if rt not in owner:
            return False, f"MISSING_ROOT:{rt}"

    ax_trans: Dict[str, Set[str]] = {}
    opq_trans: Dict[str, Set[str]] = {}
    for r in sorted(receipts.values(), key=lambda x: x.rank):
        ax = set(r.local_axioms)
        opq = set(r.local_opaques)
        for st_name, (pid, prank, h_sig, obs_olean, obs_dig) in r.stubs.items():
            if owner.get(st_name) != pid:
                return False, f"UNKNOWN_STUB_OWNER:{st_name}"
            prov = receipts[pid]
            if prov.rank != prank or prov.rank >= r.rank:
                return False, f"RANK_CYCLE:{r.shard_id}->{pid}"
            if live_sigs.get(st_name) != h_sig:
                return False, f"HSIG_DRIFT:{st_name}"
            if obs_olean != prov.olean_sha or obs_dig != prov.digest:
                return False, f"TOCTOU_SKEW:{r.shard_id}->{pid}"
            ax |= ax_trans[pid]
            opq |= opq_trans[pid]
        ax_trans[r.shard_id] = ax
        opq_trans[r.shard_id] = opq

    for rt in sorted(roots):
        sid = owner[rt]
        if ax_trans[sid] - allowed_axioms:
            return False, f"FORBIDDEN_AXIOM:{sorted(ax_trans[sid] - allowed_axioms)}"
        if opq_trans[sid]:
            return False, f"FORBIDDEN_OPAQUE:{sorted(opq_trans[sid])}"
    return True, "OK"


def probe_sharding_and_linker() -> str:
    # Call graph with a 2-node mutual recursion cycle (m1 <-> m2) and depth-3 chain
    edges = {"leaf": [], "m1": ["m2", "leaf"], "m2": ["m1"], "top": ["m1"]}
    sccs = tarjan_sccs(list(edges.keys()), edges)
    assert ["m1", "m2"] in sccs and len(sccs) == 3
    slots = pack_sccs_into_static_slots(sccs, 4)
    # Multi-node SCC stays atomic inside a single static slot; all 4 slots are D=1 parallelizable.
    m1_slot = [k for k, v in slots.items() if "m1" in v][0]
    m2_slot = [k for k, v in slots.items() if "m2" in v][0]
    assert m1_slot == m2_slot

    sigs = {"leaf": "sig_leaf", "m1": "sig_m1", "top": "sig_top"}
    allowed = {"propext", "Classical.choice", "Quot.sound"}

    # Valid D=1 receipt graph
    d_leaf = compute_receipt_digest("s_leaf", 0, "ol_leaf", ("leaf",), {}, ("propext",), ())
    r_leaf = ShardReceipt("s_leaf", 0, "ol_leaf", ("leaf",), {}, ("propext",), (), d_leaf)
    st_top = {"leaf": ("s_leaf", 0, "sig_leaf", "ol_leaf", d_leaf)}
    d_top = compute_receipt_digest("s_top", 1, "ol_top", ("top",), st_top, ("propext",), ())
    r_top = ShardReceipt("s_top", 1, "ol_top", ("top",), st_top, ("propext",), (), d_top)
    assert verify_shard_link({"s_leaf": r_leaf, "s_top": r_top}, sigs, {"top"}, allowed) == (True, "OK")

    # Attack 1: .opaqueInfo smuggling in leaf propagates to top and fails closed
    d_opq = compute_receipt_digest("s_leaf", 0, "ol_leaf", ("leaf",), {}, ("propext",), ("opaque_spec",))
    r_opq = ShardReceipt("s_leaf", 0, "ol_leaf", ("leaf",), {}, ("propext",), ("opaque_spec",), d_opq)
    st_top_opq = {"leaf": ("s_leaf", 0, "sig_leaf", "ol_leaf", d_opq)}
    r_top_opq = ShardReceipt("s_top", 1, "ol_top", ("top",), st_top_opq, ("propext",), (), "d_top_opq")
    ok_opq, msg_opq = verify_shard_link({"s_leaf": r_opq, "s_top": r_top_opq}, sigs, {"top"}, allowed)
    assert not ok_opq and msg_opq.startswith("FORBIDDEN_OPAQUE")

    # Attack 2: .olean swap TOCTOU (top observed old ol_leaf while leaf rebuilt to ol_leaf_v2)
    r_leaf_swapped = ShardReceipt("s_leaf", 0, "ol_leaf_v2", ("leaf",), {}, ("propext",), (), d_leaf)
    ok_t, msg_t = verify_shard_link({"s_leaf": r_leaf_swapped, "s_top": r_top}, sigs, {"top"}, allowed)
    assert not ok_t and msg_t.startswith("TOCTOU_SKEW")

    # Attack 3: Split-brain cycle (s0 rank 0 consumes s1 rank 1)
    r_c0 = ShardReceipt("s0", 0, "o0", ("a",), {"b": ("s1", 1, "sb", "o1", "d1")}, (), (), "d0")
    r_c1 = ShardReceipt("s1", 1, "o1", ("b",), {"a": ("s0", 0, "sa", "o0", "d0")}, (), (), "d1")
    ok_c, msg_c = verify_shard_link({"s0": r_c0, "s1": r_c1}, {"a": "sa", "b": "sb"}, {"a"}, allowed)
    assert not ok_c and msg_c.startswith("RANK_CYCLE")

    return f"PROBE2_SHARD_OK: sccs={len(sccs)} m_slot={m1_slot} blocked=[{msg_opq}, {msg_t}, {msg_c}]"


# --- Probe 3: Canonical RPO Locally-Nameless H_unit + Const::Unevaluated Cone + Cone-(G, Delta) ---
def canon_rpo_mir(
    argc: int,
    blocks: Dict[int, Tuple[List[Tuple[str, Optional[int], Optional[int]]], Tuple[int, ...]]],
    entry: int = 0,
) -> str:
    # Deterministic RPO numbering for BBs + first-definition numbering for non-ABI temporaries (> argc).
    visited: Set[int] = set()
    post: List[int] = []

    def dfs(u: int) -> None:
        visited.add(u)
        for v in blocks[u][1]:
            if v not in visited:
                dfs(v)
        post.append(u)

    dfs(entry)
    rpo = list(reversed(post))
    bb_map = {b: i for i, b in enumerate(rpo)}
    tmp_map: Dict[int, int] = {}

    def norm_loc(loc: Optional[int]) -> Optional[int]:
        if loc is None or loc <= argc:
            return loc
        if loc not in tmp_map:
            tmp_map[loc] = argc + 1 + len(tmp_map)
        return tmp_map[loc]

    canon_blocks = []
    for b in rpo:
        stmts, succs = blocks[b]
        c_stmts = [(op, norm_loc(dst), norm_loc(src)) for op, dst, src in stmts]
        c_succs = [bb_map[v] for v in succs]
        canon_blocks.append((bb_map[b], c_stmts, c_succs))
    return hashlib.sha256(json.dumps(canon_blocks, separators=(",", ":")).encode()).hexdigest()[:16]


def h_unit(
    def_path: str,
    sem_profile: str,
    canon_mir_hash: str,
    const_cone: Dict[str, str],
    callee_sigs: Dict[str, str],
) -> str:
    payload = {
        "v": 1,
        "sem": sem_profile,
        "def": def_path,
        "mir": canon_mir_hash,
        "consts": sorted(const_cone.items()),
        "callees": sorted(callee_sigs.items()),
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:16]


def probe_day2_hashing_and_cone() -> str:
    # Two alpha-equivalent MIR bodies with renumbered non-ABI temporaries (_10/_11 vs _42/_99) and BB IDs (1/2 vs 7/9)
    b1 = {0: ([("add", 10, 1), ("mov", 11, 10)], (1, 2)), 1: ([("ret", 0, 11)], ()), 2: ([("ret", 0, 1)], ())}
    b2 = {0: ([("add", 42, 1), ("mov", 99, 42)], (7, 9)), 7: ([("ret", 0, 99)], ()), 9: ([("ret", 0, 1)], ())}
    m1 = canon_rpo_mir(1, b1)
    m2 = canon_rpo_mir(1, b2)
    assert m1 == m2

    # Non-semantic edit (renumbering + span stripped): H_unit identical -> 0% churn
    h1 = h_unit("crate::decode", "v1_102", m1, {"BASE_EXTRA_MASK": "31"}, {"read_bits": "sig1"})
    h2 = h_unit("crate::decode", "v1_102", m2, {"BASE_EXTRA_MASK": "31"}, {"read_bits": "sig1"})
    assert h1 == h2

    # Const::Unevaluated change (31 -> 15) with identical syntactic MIR: H_unit MUST change!
    h3 = h_unit("crate::decode", "v1_102", m1, {"BASE_EXTRA_MASK": "15"}, {"read_bits": "sig1"})
    assert h3 != h1

    # Backward cone Cone-(G, Delta) on a 64-block binary dispatch tree editing 1 leaf (block 63)
    cfg = {i: ((2 * i + 1, 2 * i + 2) if 2 * i + 2 < 64 else ()) for i in range(64)}
    dirty = {62}
    cone, work = set(dirty), list(dirty)
    while work:
        cur = work.pop()
        for u, succs in cfg.items():
            if cur in succs and u not in cone:
                cone.add(u)
                work.append(u)
    reuse_pct = 100.0 * (64 - len(cone)) / 64.0
    assert len(cone) == 6 and reuse_pct > 90.0
    return f"PROBE3_DAY2_OK: rpo_match={m1 == m2} const_cone_detect={h3 != h1} cone64={len(cone)}/64 reuse={reuse_pct:.2f}%"


def main() -> None:
    print(probe_memory_state_r3())
    print(probe_sharding_and_linker())
    print(probe_day2_hashing_and_cone())


if __name__ == "__main__":
    main()
