#!/usr/bin/env python3
"""Executable verification suite for software architecture recovery, modularization
metrics, and cross-language API compatibility oracles (JVM & Go).

Pure Python 3.10+ standard library only (`python3 -I -B`). Deterministic across
`PYTHONHASHSEED` values with zero external dependencies or filesystem writes.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
import math
import random
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


# =============================================================================
# PROBE 1: Louvain Disconnected-Community Pathology vs. Leiden Refinement
# Pinned references:
#   - networkx/networkx@6c1a31d1613ad04cf2b2e3d63090b94979521981
#     (networkx/algorithms/community/louvain.py:257-364)
#   - vtraag/leidenalg@9890a99a4bfe49b839905b8faba1bd4f9e5beec8
#     (src/leidenalg/functions.py:21-94)
#   - vtraag/libleidenalg@fe2d4e79949048b7b79cce40892ce01490f7a24f
#     (src/Optimiser.cpp:16-30, 241-288, 1346-1404; src/MutableVertexPartition.cpp:901-918)
#   - Traag, Waltman, & van Eck, Sci. Rep. 9:5233 (2019), Algorithm A.2 & Thms 4-7
# =============================================================================


class WeightedGraph:
    """Deterministic undirected weighted graph preserving insertion node order."""

    def __init__(self, nodes: Iterable[int] = ()) -> None:
        self.nodes: Dict[int, Set[int]] = {}
        self.adj: Dict[int, Dict[int, float]] = {}
        for u in nodes:
            self.add_node(u, {u})

    def add_node(self, u: int, member_nodes: Optional[Set[int]] = None) -> None:
        if u not in self.nodes:
            self.nodes[u] = set(member_nodes) if member_nodes is not None else {u}
            self.adj[u] = {}
        elif member_nodes is not None:
            self.nodes[u] = set(member_nodes)

    def add_edge(self, u: int, v: int, weight: float = 1.0) -> None:
        self.add_node(u)
        self.add_node(v)
        self.adj[u][v] = float(weight)
        self.adj[v][u] = float(weight)

    def add_weight(self, u: int, v: int, weight: float) -> None:
        self.add_node(u)
        self.add_node(v)
        if u == v:
            self.adj[u][u] = self.adj[u].get(u, 0.0) + float(weight)
        else:
            w = self.adj[u].get(v, 0.0) + float(weight)
            self.adj[u][v] = w
            self.adj[v][u] = w

    def total_edge_weight(self) -> float:
        total = 0.0
        seen: Set[Tuple[int, int]] = set()
        for u in self.nodes:
            for v, wt in self.adj[u].items():
                a, b = (u, v) if u <= v else (v, u)
                if (a, b) not in seen:
                    seen.add((a, b))
                    total += wt
        return total

    def degrees(self) -> Dict[int, float]:
        deg: Dict[int, float] = {}
        for u in self.nodes:
            s = 0.0
            for v, wt in self.adj[u].items():
                # Undirected degree counts self-loop twice in modularity Stot.
                s += (2.0 * wt) if u == v else wt
            deg[u] = s
        return deg


def modularity_undirected(
    g: WeightedGraph, partition: Sequence[Set[int]], resolution: float = 1.0
) -> float:
    m = g.total_edge_weight()
    if m == 0.0:
        return 0.0
    deg = g.degrees()
    q = 0.0
    for comm in partition:
        c_sorted = sorted(comm)
        c_set = set(c_sorted)
        e_in = 0.0
        for u in c_sorted:
            for v, wt in g.adj[u].items():
                if v in c_set:
                    if u == v:
                        e_in += wt
                    elif u < v:
                        e_in += wt
        k_c = sum(deg[u] for u in c_sorted)
        q += (e_in / m) - resolution * ((k_c / (2.0 * m)) ** 2)
    return q


def count_connected_components(g: WeightedGraph, subset: Set[int]) -> int:
    if not subset:
        return 0
    rem = set(subset)
    cc = 0
    for start in sorted(subset):
        if start not in rem:
            continue
        cc += 1
        queue = deque([start])
        rem.remove(start)
        while queue:
            cur = queue.popleft()
            for nbr in sorted(g.adj[cur]):
                if nbr in rem and g.adj[cur][nbr] > 0.0:
                    rem.remove(nbr)
                    queue.append(nbr)
    return cc


def nx_louvain_one_level(
    g: WeightedGraph,
    m: float,
    partition: List[Set[int]],
    resolution: float,
    rng: random.Random,
) -> Tuple[List[Set[int]], List[Set[int]], bool]:
    """Exact port of networkx@6c1a31d1613ad04cf2b2e3d63090b94979521981
    louvain.py:257-343 (_one_level, undirected).
    """
    node_list = list(g.nodes.keys())
    node2com = {u: i for i, u in enumerate(node_list)}
    inner_partition: List[Set[int]] = [{u} for u in node_list]
    gamma = resolution / 2.0
    degrees = g.degrees()
    stot = [degrees[u] for u in node_list]
    nbrs = {
        u: {v: wt for v, wt in g.adj[u].items() if v != u}
        for u in node_list
    }

    rand_nodes = list(node_list)
    rng.shuffle(rand_nodes)
    nb_moves = 1
    improvement = False
    while nb_moves > 0:
        nb_moves = 0
        for u in rand_nodes:
            u_com = node2com[u]
            u_deg_by_com: Dict[int, float] = defaultdict(float)
            for nbr, wt in nbrs[u].items():
                u_deg_by_com[node2com[nbr]] += wt

            degree = degrees[u]
            stot[u_com] -= degree
            x = stot[u_com] * degree
            remove_cost = u_deg_by_com[u_com] * m - gamma * x

            best_gain = remove_cost
            best_com = u_com
            for nbr_com, wt in u_deg_by_com.items():
                x_cand = stot[nbr_com] * degree
                gain = wt * m - gamma * x_cand
                if gain > best_gain:
                    best_gain = gain
                    best_com = nbr_com

            stot[best_com] += degree
            if best_com != u_com:
                u_nodes = g.nodes[u]
                partition[u_com].difference_update(u_nodes)
                partition[best_com].update(u_nodes)
                inner_partition[u_com].remove(u)
                inner_partition[best_com].add(u)
                improvement = True
                nb_moves += 1
                node2com[u] = best_com

    partition = [p for p in partition if p]
    inner_partition = [p for p in inner_partition if p]
    return partition, inner_partition, improvement


def nx_aggregate_graph(
    g: WeightedGraph, inner_partition: Sequence[Set[int]]
) -> WeightedGraph:
    """Exact port of networkx@6c1a31d1613ad04cf2b2e3d63090b94979521981
    louvain.py:346-364 (_aggregate_graph).
    """
    h = WeightedGraph()
    node2com: Dict[int, int] = {}
    for i, part in enumerate(inner_partition):
        merged_orig: Set[int] = set()
        for node in sorted(part):
            node2com[node] = i
            merged_orig.update(g.nodes[node])
        h.add_node(i, merged_orig)

    seen_edges: Set[Tuple[int, int]] = set()
    for u in g.nodes:
        for v, wt in g.adj[u].items():
            a, b = (u, v) if u <= v else (v, u)
            if (a, b) in seen_edges:
                continue
            seen_edges.add((a, b))
            c1, c2 = node2com[a], node2com[b]
            h.add_weight(c1, c2, wt)
    return h


def nx_louvain_communities(
    g: WeightedGraph,
    resolution: float = 1.0,
    threshold: float = 1e-7,
    seed: int = 0,
) -> List[Set[int]]:
    """Exact port of networkx@6c1a31d1613ad04cf2b2e3d63090b94979521981
    louvain_communities / louvain_partitions.
    """
    rng = random.Random(seed)
    m = g.total_edge_weight()
    partition = [{u} for u in g.nodes]
    mod = modularity_undirected(g, partition, resolution=resolution)
    cur_graph = g
    partition, inner_partition, improvement = nx_louvain_one_level(
        cur_graph, m, partition, resolution, rng
    )
    while improvement:
        new_mod = modularity_undirected(g, partition, resolution=resolution)
        if new_mod - mod <= threshold:
            return partition
        mod = new_mod
        cur_graph = nx_aggregate_graph(cur_graph, inner_partition)
        # Re-seed partition list aligned with aggregated node indices 0..|V_H|-1
        partition = [set(cur_graph.nodes[u]) for u in cur_graph.nodes]
        partition, inner_partition, improvement = nx_louvain_one_level(
            cur_graph, m, partition, resolution, rng
        )
    return partition


def leiden_communities(
    g: WeightedGraph,
    resolution: float = 1.0,
    mode: str = "paper_gibbs",
    theta: float = 0.01,
    seed: int = 0,
    max_levels: int = 10,
) -> List[Set[int]]:
    """Single-outer-pass Leiden hierarchy (`n_iterations=1`; note `leidenalg.find_partition`
    in vtraag/leidenalg@9890a99a4bfe49b839905b8faba1bd4f9e5beec8 defaults to `n_iterations=2`):
      - mode='paper_gibbs': Traag et al. (2019) Algorithm A.2 gamma-connected
        filtering + exp(Delta H / theta) sampling within prior partition P.
      - mode='libleidenalg_rand_neigh': vtraag/libleidenalg@fe2d4e79949048b7b79cce40892ce01490f7a24f
        Optimiser.cpp:241-288, 1346-1404 RAND_NEIGH_COMM constrained singleton merge.
    """
    rng = random.Random(seed)
    m = g.total_edge_weight()
    two_m = 2.0 * m
    gamma_mod = resolution / two_m  # CPM-form scale so wt - gamma_mod * k_u * k_C

    cur_graph = g
    # Initial outer membership: singletons on cur_graph
    outer_membership = {u: i for i, u in enumerate(cur_graph.nodes)}

    for _ in range(max_levels):
        node_list = list(cur_graph.nodes.keys())
        degrees = cur_graph.degrees()

        # --- Phase 1: Fast local moving on cur_graph (seeded from outer_membership) ---
        comm_nodes: Dict[int, Set[int]] = defaultdict(set)
        for u in node_list:
            comm_nodes[outer_membership[u]].add(u)
        active_comms = sorted(comm_nodes.keys())
        remap = {c: idx for idx, c in enumerate(active_comms)}
        node2com = {u: remap[outer_membership[u]] for u in node_list}
        stot: Dict[int, float] = defaultdict(float)
        for u in node_list:
            stot[node2com[u]] += degrees[u]
        next_empty_com = len(active_comms)

        rng.shuffle(node_list)
        queue = deque(node_list)
        in_queue = set(node_list)

        while queue:
            u = queue.popleft()
            in_queue.discard(u)
            u_com = node2com[u]
            deg_u = degrees[u]
            u_deg_by_com: Dict[int, float] = defaultdict(float)
            for nbr, wt in cur_graph.adj[u].items():
                if nbr != u:
                    u_deg_by_com[node2com[nbr]] += wt

            stot[u_com] -= deg_u
            remove_cost = u_deg_by_com[u_com] - gamma_mod * deg_u * stot[u_com]

            best_gain = remove_cost
            best_com = u_com
            # Consider neighbor communities + an empty community (Traag 2019)
            cand_comms = sorted(u_deg_by_com.keys()) + [next_empty_com]
            for c_cand in cand_comms:
                wt = u_deg_by_com.get(c_cand, 0.0)
                gain = wt - gamma_mod * deg_u * stot.get(c_cand, 0.0)
                if gain > best_gain + 1e-14:
                    best_gain = gain
                    best_com = c_cand

            stot[best_com] += deg_u
            if best_com != u_com:
                node2com[u] = best_com
                if best_com == next_empty_com:
                    next_empty_com += 1
                for nbr in sorted(cur_graph.adj[u]):
                    if nbr != u and node2com[nbr] != best_com and nbr not in in_queue:
                        queue.append(nbr)
                        in_queue.add(nbr)

        # Group rough communities S in P
        rough_groups: Dict[int, List[int]] = defaultdict(list)
        for u in node_list:
            rough_groups[node2com[u]].append(u)
        rough_parts = [sorted(v) for _, v in sorted(rough_groups.items()) if v]

        # Termination check: every rough community is a single node of cur_graph
        if len(rough_parts) == len(node_list) and all(len(s) == 1 for s in rough_parts):
            outer_membership = dict(node2com)
            break

        # --- Phase 2: Constrained Refinement P_refined within each S in P ---
        refined_parts: List[Set[int]] = []
        refined_to_rough: List[int] = []

        for rough_idx, s_nodes in enumerate(rough_parts):
            s_set = set(s_nodes)
            s_vol = sum(degrees[u] for u in s_nodes)
            # Start from singletons inside S
            sub_id = {u: idx for idx, u in enumerate(s_nodes)}
            sub_members: Dict[int, Set[int]] = {idx: {u} for idx, u in enumerate(s_nodes)}
            sub_vol: Dict[int, float] = {idx: degrees[u] for idx, u in enumerate(s_nodes)}

            def cut_within_s(c_set: Set[int]) -> float:
                total_cut = 0.0
                for x in sorted(c_set):
                    for y, wt in cur_graph.adj[x].items():
                        if y in s_set and y not in c_set:
                            total_cut += wt
                return total_cut

            visit_order = list(s_nodes)
            rng.shuffle(visit_order)

            for v in visit_order:
                v_cid = sub_id[v]
                # Only merge unmerged singleton nodes (Algorithm A.2 / merge_nodes_constrained)
                if len(sub_members[v_cid]) != 1:
                    continue
                deg_v = degrees[v]

                if mode == "paper_gibbs":
                    # Algorithm A.2 L35-38: singleton v must itself be gamma-well-connected in S
                    if cut_within_s({v}) < gamma_mod * deg_v * (s_vol - deg_v) - 1e-12:
                        continue
                    wt_to_sub: Dict[int, float] = defaultdict(float)
                    for nbr, wt in cur_graph.adj[v].items():
                        if nbr in s_set and nbr != v:
                            wt_to_sub[sub_id[nbr]] += wt
                    cands: List[Tuple[int, float]] = []
                    for cid in sorted(wt_to_sub.keys()):
                        if cid == v_cid or not sub_members[cid]:
                            continue
                        c_vol = sub_vol[cid]
                        if cut_within_s(sub_members[cid]) >= gamma_mod * c_vol * (s_vol - c_vol) - 1e-12:
                            delta_h = wt_to_sub[cid] - gamma_mod * deg_v * c_vol
                            if delta_h >= -1e-14:
                                cands.append((cid, max(0.0, delta_h)))
                    if cands:
                        weights = [math.exp(min(50.0, dh / theta)) for _, dh in cands]
                        tot_w = sum(weights)
                        pick = rng.random() * tot_w
                        acc = 0.0
                        chosen = cands[-1][0]
                        for (cid, _), w_prob in zip(cands, weights):
                            acc += w_prob
                            if pick <= acc:
                                chosen = cid
                                break
                        sub_members[chosen].add(v)
                        sub_vol[chosen] += deg_v
                        sub_members[v_cid].clear()
                        sub_vol[v_cid] = 0.0
                        sub_id[v] = chosen

                elif mode == "libleidenalg_rand_neigh":
                    # Optimiser.cpp:1346-1404 RAND_NEIGH_COMM inside constrained_partition:
                    # MutableVertexPartition::get_neigh_comms (MutableVertexPartition.cpp:901-918)
                    # pushes neighbor communities per incident neighbor/multiedge (ignoring scalar
                    # edge weights, aided by a no-op `comm_added[comm];` statement at line 913).
                    neigh_comms_incl_dupes: List[int] = []
                    for nbr in sorted(cur_graph.adj[v]):
                        if nbr in s_set and nbr != v:
                            neigh_comms_incl_dupes.append(sub_id[nbr])
                    k_len = len(neigh_comms_incl_dupes)
                    if k_len > 0 and rng.randint(0, k_len) > 0:
                        rand_comm = neigh_comms_incl_dupes[rng.randint(0, k_len - 1)]
                        if rand_comm != v_cid and sub_members[rand_comm]:
                            wt_to_rand = sum(
                                wt
                                for nbr, wt in cur_graph.adj[v].items()
                                if nbr in sub_members[rand_comm]
                            )
                            diff_move = wt_to_rand - gamma_mod * deg_v * sub_vol[rand_comm]
                            if diff_move >= -1e-14:
                                sub_members[rand_comm].add(v)
                                sub_vol[rand_comm] += deg_v
                                sub_members[v_cid].clear()
                                sub_vol[v_cid] = 0.0
                                sub_id[v] = rand_comm
                else:
                    raise ValueError(f"Unknown Leiden mode: {mode}")

            for cid in sorted(sub_members.keys()):
                if sub_members[cid]:
                    refined_parts.append(set(sub_members[cid]))
                    refined_to_rough.append(rough_idx)

        # --- Phase 3: Aggregate on P_refined, initialize coarse membership from P ---
        next_graph = nx_aggregate_graph(cur_graph, refined_parts)
        outer_membership = {i: refined_to_rough[i] for i in range(len(refined_parts))}
        cur_graph = next_graph

    # Project final coarse communities back to original graph vertices
    final_groups: Dict[int, Set[int]] = defaultdict(set)
    for u in cur_graph.nodes:
        final_groups[outer_membership[u]].update(cur_graph.nodes[u])
    return [final_groups[k] for k in sorted(final_groups.keys()) if final_groups[k]]


def build_17node_louvain_witness() -> WeightedGraph:
    """Deterministic 17-node weighted graph (`m = 441`, `K_{1..6} = 66`, `K_{0 U T} = 696`)
    where full multi-level singleton-initialized Louvain (`louvain_communities`, seed=0, and
    25/60 = 41.7% of seeds 0..59) converges and terminates with permanently disconnected
    community `{1,2,3,4,5,6}` (`cc=2`, zero edges between `{1,2,3}` and `{4,5,6}`).
    Satisfies Pass-1 capture (`wb = 5 > wc = 3`, `6 * w0t = 108 > 6 * wb = 30`), single-node
    trap (`2 * wc = 6 > wb = 5`), and Level-2 non-remerge
    (`6 * wb * m = 30 * 441 = 13,230 < 0.5 * 66 * 696 = 22,968`).
    """
    g = WeightedGraph(range(17))
    # Two disjoint K3 cliques L={1,2,3} and R={4,5,6}, zero edges between L and R (weight 18)
    for clique in [(1, 2, 3), (4, 5, 6)]:
        for i in range(3):
            for j in range(i + 1, 3):
                g.add_edge(clique[i], clique[j], 3.0)
    # Bridge node 0 connects to L U R with weight 5 (weight 30)
    for v in (1, 2, 3, 4, 5, 6):
        g.add_edge(0, v, 5.0)
    # Target K6 clique T={7..12} of weight 15 (weight 225), pulling bridge 0 via weight 18 (weight 108)
    t_nodes = (7, 8, 9, 10, 11, 12)
    for i in range(6):
        for j in range(i + 1, 6):
            g.add_edge(t_nodes[i], t_nodes[j], 15.0)
        g.add_edge(0, t_nodes[i], 18.0)
    # Decoupled K4 subsystem {13..16} of weight 10 (weight 60) -> total m = 441
    bg = (13, 14, 15, 16)
    for i in range(4):
        for j in range(i + 1, 4):
            g.add_edge(bg[i], bg[j], 10.0)
    return g


def build_seeded_hub_bridge_graph(seed: int) -> WeightedGraph:
    """Perturbed 17/18-node hub-bridge witness instance (`w_c in [2.8, 3.2]`,
    `w_b in [4.9, 5.2]`, `w_t in [14.5, 16.0]`, `w_{0T} in [17.5, 18.8]`,
    `w_bg in [8.5, 11.0]`) testing non-knife-edge parameter stability around the
    Traag et al. (2019) Fig. 2 bridge-articulation topology.
    """
    rng = random.Random(seed)
    n_bg = rng.choice([4, 5])
    g = WeightedGraph(range(13 + n_bg))
    for clique in [(1, 2, 3), (4, 5, 6)]:
        for i in range(3):
            for j in range(i + 1, 3):
                g.add_edge(clique[i], clique[j], rng.uniform(2.8, 3.2))
    for v in (1, 2, 3, 4, 5, 6):
        g.add_edge(0, v, rng.uniform(4.9, 5.2))
    t_nodes = (7, 8, 9, 10, 11, 12)
    for i in range(6):
        for j in range(i + 1, 6):
            g.add_edge(t_nodes[i], t_nodes[j], rng.uniform(14.5, 16.0))
        g.add_edge(0, t_nodes[i], rng.uniform(17.5, 18.8))
    bg = tuple(range(13, 13 + n_bg))
    for i in range(len(bg)):
        for j in range(i + 1, len(bg)):
            g.add_edge(bg[i], bg[j], rng.uniform(8.5, 11.0))
    return g


def run_probe_1() -> None:
    print("PROBE 1: Louvain Disconnected-Supernode Pathology vs. Leiden Refinement")
    print("  Provenance: [exact reproduction of pinned repository logic] + [exact calculation of published algorithm/metric]")

    g17 = build_17node_louvain_witness()
    louv_p = nx_louvain_communities(g17, resolution=1.0, seed=0)
    leid_gibbs = leiden_communities(g17, resolution=1.0, mode="paper_gibbs", seed=0)
    leid_lib = leiden_communities(g17, resolution=1.0, mode="libleidenalg_rand_neigh", seed=0)

    louv_ccs = [count_connected_components(g17, c) for c in louv_p]
    gibbs_ccs = [count_connected_components(g17, c) for c in leid_gibbs]
    lib_ccs = [count_connected_components(g17, c) for c in leid_lib]

    q_louv = modularity_undirected(g17, louv_p, resolution=1.0)
    q_gibbs = modularity_undirected(g17, leid_gibbs, resolution=1.0)
    q_lib = modularity_undirected(g17, leid_lib, resolution=1.0)

    # Exact analytical witness quantities & Delta Q from splitting disconnected L={1,2,3} and R={4,5,6}:
    # E(L, R) = 0 => Q({L, R}) - Q({L U R}) = + 2 * gamma * (K_L / 2m) * (K_R / 2m) = K_L * K_R / (2 * m^2)
    m17 = g17.total_edge_weight()
    deg17 = g17.degrees()
    k_left = sum(deg17[u] for u in (1, 2, 3))
    k_right = sum(deg17[u] for u in (4, 5, 6))
    k_1_6 = k_left + k_right
    k_0_t = sum(deg17[u] for u in (0, 7, 8, 9, 10, 11, 12))
    lhs_nonmerge = 30.0 * m17
    rhs_nonmerge = 0.5 * k_1_6 * k_0_t
    expected_dq = (k_left * k_right) / (2.0 * (m17 ** 2))

    g17_disc_60 = sum(
        1
        for s in range(60)
        if any(count_connected_components(g17, c) >= 2 for c in nx_louvain_communities(g17, 1.0, seed=s))
    )

    assert m17 == 441.0 and k_1_6 == 66.0 and k_0_t == 696.0
    assert lhs_nonmerge == 13230.0 and rhs_nonmerge == 22968.0 and lhs_nonmerge < rhs_nonmerge
    assert g17_disc_60 == 25, f"Expected 25/60 disconnected seeds on g17, got {g17_disc_60}/60"
    assert max(louv_ccs) == 2 and {1, 2, 3, 4, 5, 6} in louv_p, "Louvain must weld {1..6} with cc=2"
    assert max(gibbs_ccs) == 1 and max(lib_ccs) == 1, "Both Leiden modes must guarantee cc=1"
    assert abs((q_gibbs - q_louv) - expected_dq) < 1e-12, "Analytical modularity delta mismatch"
    assert abs((q_lib - q_louv) - expected_dq) < 1e-12, "libleidenalg modularity delta mismatch"

    print(
        f"  17-node witness (m={int(m17)}, Level2: {int(lhs_nonmerge)}<{int(rhs_nonmerge)}, "
        f"disc_seeds={g17_disc_60}/60={100.0 * g17_disc_60 / 60.0:.1f}%): "
        f"Louvain communities={len(louv_p)} max_cc={max(louv_ccs)} Q={q_louv:.8f} | "
        f"Leiden(Gibbs,n_iter=1) max_cc={max(gibbs_ccs)} Q={q_gibbs:.8f} | "
        f"Leiden(libleidenalg,n_iter=1) max_cc={max(lib_ccs)} Q={q_lib:.8f} | "
        f"exact_dQ=+{expected_dq:.8f}"
    )

    print("  Provenance: [controlled simulation]")
    n_trials = 80
    louv_disc_graphs = 0
    louv_disc_comms = 0
    louv_total_comms = 0
    gibbs_disc_comms = 0
    lib_disc_comms = 0
    dq_sum = 0.0

    for seed in range(n_trials):
        gs = build_seeded_hub_bridge_graph(1000 + seed)
        lp = nx_louvain_communities(gs, resolution=1.0, seed=seed)
        gp = leiden_communities(gs, resolution=1.0, mode="paper_gibbs", seed=seed)
        kp = leiden_communities(gs, resolution=1.0, mode="libleidenalg_rand_neigh", seed=seed)

        l_cc = [count_connected_components(gs, c) for c in lp]
        g_cc = [count_connected_components(gs, c) for c in gp]
        k_cc = [count_connected_components(gs, c) for c in kp]

        n_bad = sum(1 for x in l_cc if x >= 2)
        if n_bad > 0:
            louv_disc_graphs += 1
        louv_disc_comms += n_bad
        louv_total_comms += len(lp)
        gibbs_disc_comms += sum(1 for x in g_cc if x >= 2)
        lib_disc_comms += sum(1 for x in k_cc if x >= 2)
        dq_sum += modularity_undirected(gs, gp, 1.0) - modularity_undirected(gs, lp, 1.0)

    mean_dq = dq_sum / n_trials
    assert louv_disc_graphs == 24 and louv_total_comms == 290
    assert gibbs_disc_comms == 0 and lib_disc_comms == 0, "Leiden produced a disconnected community"
    assert mean_dq > 0.0, "Leiden mean modularity must exceed welded Louvain"

    print(
        f"  Perturbed hub-bridge 80-seed sweep: Louvain_graphs_with_cc>=2={louv_disc_graphs}/{n_trials} "
        f"({100.0 * louv_disc_graphs / n_trials:.1f}%), "
        f"Louvain_disconnected_comms={louv_disc_comms}/{louv_total_comms} "
        f"({100.0 * louv_disc_comms / louv_total_comms:.2f}%), "
        f"Leiden_disconnected_comms=0 (Gibbs=0, libleidenalg=0), mean_dQ=+{mean_dq:.6f}"
    )


# =============================================================================
# PROBE 2: Bunch BasicMQ / TurboMQ Cycle-Blindness & k-Inflation vs. DSM PC
# Primary references:
#   - Mancoridis et al., ICSM 1999, DOI 10.1109/ICSM.1999.792498 (BasicMQ)
#   - Mitchell & Mancoridis, IEEE TSE 32(3), 2006, DOI 10.1109/TSE.2006.31 (TurboMQ)
#   - MacCormack, Rusnak, & Baldwin, Mgmt. Sci. 52(7), 2006, DOI 10.1287/mnsc.1060.0552 (DSM PC)
# =============================================================================


def compute_basic_mq(
    n_nodes: int, edges: Sequence[Tuple[int, int, float]], clusters: Sequence[Sequence[int]]
) -> float:
    del n_nodes
    k = len(clusters)
    node_to_c: Dict[int, int] = {}
    sizes = [len(c) for c in clusters]
    for ci, c in enumerate(clusters):
        for u in c:
            node_to_c[u] = ci

    mu = [0] * k
    eps: Dict[Tuple[int, int], int] = defaultdict(int)
    for u, v, wt in edges:
        if wt <= 0 or u == v:
            continue
        cu, cv = node_to_c[u], node_to_c[v]
        if cu == cv:
            mu[cu] += 1
        else:
            a, b = (cu, cv) if cu < cv else (cv, cu)
            eps[(a, b)] += 1

    mean_a = sum((mu[i] / (sizes[i] ** 2)) for i in range(k)) / k
    if k <= 1:
        return mean_a
    num_pairs = k * (k - 1) // 2
    sum_e = 0.0
    for i in range(k):
        for j in range(i + 1, k):
            sum_e += eps.get((i, j), 0) / (2.0 * sizes[i] * sizes[j])
    return mean_a - (sum_e / num_pairs)


def compute_turbo_mq(
    edges: Sequence[Tuple[int, int, float]], clusters: Sequence[Sequence[int]]
) -> float:
    k = len(clusters)
    node_to_c: Dict[int, int] = {}
    for ci, c in enumerate(clusters):
        for u in c:
            node_to_c[u] = ci

    mu = [0.0] * k
    ext = [0.0] * k
    for u, v, wt in edges:
        if wt <= 0 or u == v:
            continue
        cu, cv = node_to_c[u], node_to_c[v]
        if cu == cv:
            mu[cu] += wt
        else:
            ext[cu] += wt
            ext[cv] += wt

    total_cf = 0.0
    for i in range(k):
        if mu[i] > 0.0:
            total_cf += (2.0 * mu[i]) / (2.0 * mu[i] + ext[i])
    return total_cf


def compute_dsm_propagation_cost(
    n_nodes: int, edges: Sequence[Tuple[int, int, float]]
) -> Tuple[float, int]:
    """Exact transitive reachability closure V = bool(sum_{r=0}^N M^r) via bitsets,
    returning (Propagation Cost in [0,1], largest SCC size).
    """
    adj: List[List[int]] = [[] for _ in range(n_nodes)]
    radj: List[List[int]] = [[] for _ in range(n_nodes)]
    reach = [1 << i for i in range(n_nodes)]
    for u, v, wt in edges:
        if wt > 0 and u != v:
            adj[u].append(v)
            radj[v].append(u)
            reach[u] |= 1 << v

    # Warshall bitset transitive closure in O(N^2) Python int word operations
    for k in range(n_nodes):
        rk = reach[k]
        bit_k = 1 << k
        for i in range(n_nodes):
            if reach[i] & bit_k:
                reach[i] |= rk

    total_ones = sum(r.bit_count() for r in reach)
    pc = total_ones / float(n_nodes * n_nodes)

    # Kosaraju largest SCC size for structural verification
    visited = [False] * n_nodes
    order: List[int] = []

    def dfs1(start: int) -> None:
        stack = [(start, 0)]
        visited[start] = True
        while stack:
            u, idx = stack[-1]
            if idx < len(adj[u]):
                nxt = adj[u][idx]
                stack[-1] = (u, idx + 1)
                if not visited[nxt]:
                    visited[nxt] = True
                    stack.append((nxt, 0))
            else:
                stack.pop()
                order.append(u)

    for i in range(n_nodes):
        if not visited[i]:
            dfs1(i)

    visited2 = [False] * n_nodes
    max_scc = 0
    for u in reversed(order):
        if visited2[u]:
            continue
        comp_sz = 0
        q = deque([u])
        visited2[u] = True
        while q:
            cur = q.popleft()
            comp_sz += 1
            for w in radj[cur]:
                if not visited2[w]:
                    visited2[w] = True
                    q.append(w)
        max_scc = max(max_scc, comp_sz)

    return pc, max_scc


def run_probe_2() -> None:
    print("\nPROBE 2: Bunch BasicMQ/TurboMQ Cycle-Blindness & k-Inflation vs. DSM Propagation Cost")
    print("  Provenance: [exact calculation of published algorithm/metric]")

    # 2A & 2B: N=64 files in k=8 cohesive 8-node modules (directed internal ring)
    k_mods, mod_sz = 8, 8
    n64 = k_mods * mod_sz
    gold_clusters = [list(range(m * mod_sz, (m + 1) * mod_sz)) for m in range(k_mods)]

    base_internal: List[Tuple[int, int, float]] = [
        (c[idx], c[(idx + 1) % mod_sz], 1.0)
        for c in gold_clusters
        for idx in range(mod_sz)
    ]

    # Architecture 1 (Clean Layered DAG): 2 forward edges C_m -> C_{m+1}, 0 backward
    dag_edges = list(base_internal)
    for m in range(k_mods - 1):
        c_src, c_dst = gold_clusters[m], gold_clusters[m + 1]
        dag_edges.append((c_src[0], c_dst[0], 1.0))
        dag_edges.append((c_src[1], c_dst[1], 1.0))

    # Architecture 2 (Cyclic Feedback Architecture): 1 forward C_m -> C_{m+1}, 1 backward C_{m+1} -> C_m
    cyc_edges = list(base_internal)
    for m in range(k_mods - 1):
        c_src, c_dst = gold_clusters[m], gold_clusters[m + 1]
        cyc_edges.append((c_src[0], c_dst[0], 1.0))
        cyc_edges.append((c_dst[1], c_src[1], 1.0))

    bmq_dag = compute_basic_mq(n64, dag_edges, gold_clusters)
    bmq_cyc = compute_basic_mq(n64, cyc_edges, gold_clusters)
    tmq_dag = compute_turbo_mq(dag_edges, gold_clusters)
    tmq_cyc = compute_turbo_mq(cyc_edges, gold_clusters)
    pc_dag, scc_dag = compute_dsm_propagation_cost(n64, dag_edges)
    pc_cyc, scc_cyc = compute_dsm_propagation_cost(n64, cyc_edges)

    # Shatter into 32 2-node micro-clusters along internal ring edges [2*i, 2*i+1]
    micro_clusters = [[2 * i, 2 * i + 1] for i in range(n64 // 2)]
    tmq_micro_cyc = compute_turbo_mq(cyc_edges, micro_clusters)

    assert abs(bmq_dag - bmq_cyc) == 0.0, "BasicMQ must be algebraically blind to cross-module edge reversal"
    assert abs(tmq_dag - tmq_cyc) == 0.0, "TurboMQ must be algebraically blind to cross-module edge reversal"
    assert scc_dag == 8 and scc_cyc == 64, "Expected SCC explosion 8 -> 64"
    assert pc_cyc == 1.0 and pc_cyc > 1.75 * pc_dag, "Expected PC spike to 100% under cycle formation"
    assert tmq_micro_cyc > 2.1 * tmq_cyc, "Expected >2.1x 2-node micro-cluster inflation of unnormalized TurboMQ"

    print(
        f"  Cycle-blindness (N={n64}, k={k_mods}): "
        f"DAG[BasicMQ={bmq_dag:.6f}, TurboMQ={tmq_dag:.6f}, PC={100.0 * pc_dag:.2f}%, maxSCC={scc_dag}] vs "
        f"Cyclic[BasicMQ={bmq_cyc:.6f}, TurboMQ={tmq_cyc:.6f}, PC={100.0 * pc_cyc:.2f}%, maxSCC={scc_cyc}]"
    )
    print(
        f"  k-Inflation (k=8 -> k=32 pairs on Cyclic system): "
        f"TurboMQ {tmq_cyc:.4f} -> {tmq_micro_cyc:.4f} ({tmq_micro_cyc / tmq_cyc:.2f}x inflation while global PC stays 100.00%)"
    )

    # 2C: Linux-vs-Mozilla Direct-Density vs. Transitive-Visibility Inversion
    print("  Provenance: [derived analytical model]")
    n120 = 120
    # System A (Layered + Vertical Utility Bus, denser first-order edges, zero cross-module cycles):
    # 10 independent 10-file feature modules (dense internal DAGs) calling 20 leaf utility headers (sink bus).
    edges_sys_a: List[Tuple[int, int, float]] = []
    for mod_idx in range(10):
        base = mod_idx * 10
        # All 45 internal DAG pairs within each 10-node module -> 450 edges
        for i in range(10):
            for j in range(i + 1, 10):
                edges_sys_a.append((base + i, base + j, 1.0))
        # Every feature file calls 4 shared sink utility files in [100..119] -> 400 edges (total 850)
        for i in range(10):
            for u_off in range(4):
                edges_sys_a.append((base + i, 100 + ((mod_idx * 2 + i + u_off) % 20), 1.0))

    # System B (Sparser first-order edges, entangled 70-node strongly connected core):
    edges_sys_b: List[Tuple[int, int, float]] = []
    # Sparse 70-node entangled core: each node has 3 cyclic chords -> 210 edges
    for i in range(70):
        edges_sys_b.append((i, (i + 1) % 70, 1.0))
        edges_sys_b.append((i, (i + 7) % 70, 1.0))
        edges_sys_b.append((i, (i + 19) % 70, 1.0))
    # 50 peripheral files emit 3 edges each (2 for p=119) -> 149 edges (total 210 + 149 = 359 < 850)
    for p in range(70, 120):
        edges_sys_b.append((p, (p - 70) % 70, 1.0))
        edges_sys_b.append((p, (p - 53) % 70, 1.0))
        if p + 1 < 120:
            edges_sys_b.append((p, p + 1, 1.0))

    dens_a = 1000.0 * len(edges_sys_a) / (n120 * (n120 - 1))
    dens_b = 1000.0 * len(edges_sys_b) / (n120 * (n120 - 1))
    pc_a, scc_a = compute_dsm_propagation_cost(n120, edges_sys_a)
    pc_b, scc_b = compute_dsm_propagation_cost(n120, edges_sys_b)

    assert len(edges_sys_a) == 850 and len(edges_sys_b) == 359
    assert dens_a > 1.8 * dens_b and pc_b > 5.0 * pc_a, "Density-vs-PC inversion failed"
    print(
        f"  Density-vs-PC Inversion (N={n120}): "
        f"LayeredBus[edges={len(edges_sys_a)}, density={dens_a:.2f}‰, PC={100.0 * pc_a:.2f}%, maxSCC={scc_a}] vs "
        f"EntangledCore[edges={len(edges_sys_b)}, density={dens_b:.2f}‰, PC={100.0 * pc_b:.2f}%, maxSCC={scc_b}] "
        f"({pc_b / pc_a:.2f}x higher PC at {dens_b / dens_a:.2f}x direct density)"
    )


# =============================================================================
# PROBE 3: MoJoFM vs. a2a / a2a_adj / c2c_cvg / ARI & Extractor/Folder Confounders
# Pinned & Primary references:
#   - usc-softarch/arcade_core@53e6f4f6e35098b260290e5cda794ec78f6df4df
#     (src/main/java/mojo/MoJoCalculator.java:261-358)
#   - xjtu-enre/TSE2025SemArc@b635e5d9b14c910308af62f39e464ff2b58fa192
#     (SemArc/algorithm/comparing_clusters.py:86-103, 254-320, 534-672)
#   - Lutellier et al., ICSE 2015; Zhang et al. (SemRef), ICSE 2026; Quadri, July 2026
# =============================================================================


def max_cardinality_bipartite_matching(
    n_left: int, n_right: int, adj: Sequence[Sequence[int]]
) -> int:
    """Deterministic Kuhn augmenting-path maximum cardinality bipartite matching."""
    match_r = [-1] * n_right

    def dfs(u: int, seen: List[bool]) -> bool:
        for v in adj[u]:
            if not seen[v]:
                seen[v] = True
                if match_r[v] == -1 or dfs(match_r[v], seen):
                    match_r[v] = u
                    return True
        return False

    matched = 0
    for u in range(n_left):
        if dfs(u, [False] * n_right):
            matched += 1
    return matched


def max_weight_bipartite_assignment(weights: Sequence[Sequence[int]]) -> int:
    """Exact Hungarian algorithm (O(K^3) pure stdlib) for maximum-weight matching
    on rectangular integer matrix `weights` (n_rows x n_cols).
    """
    n_r = len(weights)
    n_c = len(weights[0]) if n_r > 0 else 0
    if n_r == 0 or n_c == 0:
        return 0
    transpose = n_r > n_c
    if transpose:
        mat = [[weights[r][c] for r in range(n_r)] for c in range(n_c)]
        n, m = n_c, n_r
    else:
        mat = [list(row) for row in weights]
        n, m = n_r, n_c

    max_val = max(max(row) for row in mat)
    u = [0] * (n + 1)
    v = [0] * (m + 1)
    p = [0] * (m + 1)
    way = [0] * (m + 1)

    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [10**15] * (m + 1)
        used = [False] * (m + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = 10**15
            j1 = 0
            for j in range(1, m + 1):
                if not used[j]:
                    cur = (max_val - mat[i0 - 1][j - 1]) - u[i0] - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(m + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break

    total_w = 0
    for j in range(1, m + 1):
        if p[j] > 0:
            total_w += mat[p[j] - 1][j - 1]
    return total_w


def _dense_clusters(labels: Sequence[int]) -> List[List[int]]:
    by_id: Dict[int, List[int]] = defaultdict(list)
    for idx, cid in enumerate(labels):
        by_id[cid].append(idx)
    return [by_id[k] for k in sorted(by_id.keys())]


def mojofm(labels_a: Sequence[int], labels_b: Sequence[int]) -> float:
    """Exact MoJoFM in [0, 100] matching ARCADE MoJoCalculator.java:261-358."""
    assert len(labels_a) == len(labels_b)
    n = len(labels_a)
    ca = _dense_clusters(labels_a)
    cb = _dense_clusters(labels_b)
    l, m = len(ca), len(cb)
    b_of = [0] * n
    for j, grp in enumerate(cb):
        for x in grp:
            b_of[x] = j

    moves = 0
    bipartite_adj: List[List[int]] = []
    for grp_a in ca:
        counts = Counter(b_of[x] for x in grp_a)
        max_tag = max(counts.values())
        moves += len(grp_a) - max_tag
        bipartite_adj.append(sorted(j for j, cnt in counts.items() if cnt == max_tag))

    non_empty_groups = max_cardinality_bipartite_matching(l, m, bipartite_adj)
    mno = moves + l - non_empty_groups

    # Exact maxDistanceTo(B, n) from MoJoCalculator.java:300-322
    b_sizes = sorted(len(grp) for grp in cb)
    group_number = 0
    for sz in b_sizes:
        if group_number < sz:
            group_number += 1
    max_dis = n - group_number
    if max_dis == 0:
        return 100.0 if mno == 0 else 0.0
    return (1.0 - (mno / float(max_dis))) * 100.0


def adjusted_rand_index(labels_a: Sequence[int], labels_b: Sequence[int]) -> float:
    """Exact Hubert-Arabie (1985) Adjusted Rand Index."""
    assert len(labels_a) == len(labels_b)
    n = len(labels_a)

    def cn2(x: int) -> float:
        return 0.5 * x * (x - 1)

    nij = Counter(zip(labels_a, labels_b))
    ai = Counter(labels_a)
    bj = Counter(labels_b)
    sum_nij = sum(cn2(v) for v in nij.values())
    sum_a = sum(cn2(v) for v in ai.values())
    sum_b = sum(cn2(v) for v in bj.values())
    total_pairs = cn2(n)
    if total_pairs == 0:
        return 1.0
    expected = (sum_a * sum_b) / total_pairs
    denom = 0.5 * (sum_a + sum_b) - expected
    if abs(denom) < 1e-15:
        return 1.0 if abs(sum_nij - expected) < 1e-15 else 0.0
    return (sum_nij - expected) / denom


def a2a_metrics(
    labels_a: Sequence[int], labels_b: Sequence[int]
) -> Tuple[float, float, float]:
    """Returns (a2a_lutellier, a2a_semref_zyr, a2a_adj_v3) in [0, 1] using exact
    Hungarian maximum-weight matching (Lutellier ICSE 2015 & SemArc comparing_clusters.py).
    """
    assert len(labels_a) == len(labels_b)
    n = len(labels_a)
    ca = _dense_clusters(labels_a)
    cb = _dense_clusters(labels_b)
    k1, k2 = len(ca), len(cb)
    b_sets = [set(g) for g in cb]
    weights = [[len(set(ga) & gb) for gb in b_sets] for ga in ca]
    matched_entities = max_weight_bipartite_assignment(weights)

    mto_move = n - matched_entities
    mto_ar = abs(k1 - k2)
    mto_total = mto_move + mto_ar

    # 1. ARCADE A2a.java:104-140 / Lutellier ICSE 2015 Section IV: aco(A_i) = k_i + 2N
    aco_lut = (k1 + 2 * n) + (k2 + 2 * n)
    a2a_lut = 1.0 - (mto_total / float(aco_lut))

    # 2. Zhang et al. SemArc/SemRef fun_a2a_zyr (comparing_clusters.py:301-320):
    aco_zyr = (n + k1) + (n + k2)
    a2a_zyr = 1.0 - (mto_total / (2.0 * float(aco_zyr)))

    # 3. Zhang et al. SARIF / SemRef fun_a2a_adj_v3 (comparing_clusters.py:534-639):
    # Note: upstream TSE2025SemArc max_distance_a2a (comparing_clusters.py:538-539) computes
    # `a = max(result) + 1, b = max(result_gt) + 1`, which equals `k1, k2` iff cluster IDs
    # are contiguous `0..k-1` (and can diverge on sparse/non-zero-indexed label arrays).
    q = max(k1, k2)
    max_mto = n - (n // q)
    move_entity = n + min(k1, k2)
    ar_entity = abs(k1 - k2)
    move_factor = move_entity / float(move_entity + ar_entity)
    ar_factor = ar_entity / float(move_entity + ar_entity)
    move_term = (mto_move / float(max_mto)) * move_factor if max_mto > 0 else 0.0
    ar_term = (mto_ar / float(aco_zyr)) * ar_factor if aco_zyr > 0 else 0.0
    a2a_adj = 1.0 - move_term - ar_term

    return a2a_lut, a2a_zyr, a2a_adj


def c2c_cvg(
    labels_a: Sequence[int], labels_b: Sequence[int], thresh: float = 0.66
) -> float:
    """Exact cluster-to-cluster coverage (SemArc comparing_clusters.py:640-672)."""
    ca = _dense_clusters(labels_a)
    cb = _dense_clusters(labels_b)
    b_sets = [set(g) for g in cb]
    hits = 0
    for ga in ca:
        sa = set(ga)
        best = max(len(sa & sb) / float(max(len(sa), len(sb))) for sb in b_sets)
        if best > thresh:
            hits += 1
    return hits / float(len(ca))


def acdc_hub_surrogate_cluster(
    n_nodes: int, edges: Sequence[Tuple[int, int, float]], num_roots: int
) -> List[int]:
    """Fixed-k ACDC-like in-degree hub-affinity surrogate (distinct from Tzerpos & Holt
    WCRE 2000's full body-header conglomeration + parameter-free directed dominator-tree
    induction): selects top `num_roots` high-indegree controllers, assigns dependents by
    strongest controller affinity (strict `>` tie-break), and sweeps 1-hop orphans.
    """
    indeg = [0.0] * n_nodes
    undir: List[Dict[int, float]] = [defaultdict(float) for _ in range(n_nodes)]
    for u, v, wt in edges:
        if u != v and wt > 0:
            indeg[v] += wt
            undir[u][v] += wt
            undir[v][u] += wt

    controllers = [
        u for u, _ in sorted(enumerate(indeg), key=lambda kv: (-kv[1], kv[0]))[:num_roots]
    ]
    labels = [-1] * n_nodes
    for cid, root in enumerate(controllers):
        labels[root] = cid

    for u in range(n_nodes):
        if labels[u] != -1:
            continue
        best_c, best_w = 0, -1.0
        for cid, root in enumerate(controllers):
            w = undir[u].get(root, 0.0)
            if w > best_w:
                best_w = w
                best_c = cid
        if best_w > 0:
            labels[u] = best_c

    for u in range(n_nodes):
        if labels[u] == -1:
            aff: Dict[int, float] = defaultdict(float)
            for v, wt in undir[u].items():
                if labels[v] != -1:
                    aff[labels[v]] += wt
            labels[u] = max(sorted(aff), key=lambda c: aff[c]) if aff else 0
    return labels


def bunch_hill_climb(
    n_nodes: int,
    edges: Sequence[Tuple[int, int, float]],
    k_init: int,
    seed: int,
) -> List[int]:
    """Deterministic steepest-ascent hill climbing (Bunch-SAHC style) maximizing TurboMQ."""
    rng = random.Random(seed)
    labels = [rng.randrange(k_init) for _ in range(n_nodes)]
    pos_edges = [(u, v, wt) for (u, v, wt) in edges if wt > 0.0 and u != v]

    def score_labels(lbls: Sequence[int]) -> float:
        mu = [0.0] * k_init
        ext = [0.0] * k_init
        for u, v, wt in pos_edges:
            cu, cv = lbls[u], lbls[v]
            if cu == cv:
                mu[cu] += wt
            else:
                ext[cu] += wt
                ext[cv] += wt
        total_cf = 0.0
        for i in range(k_init):
            if mu[i] > 0.0:
                total_cf += (2.0 * mu[i]) / (2.0 * mu[i] + ext[i])
        return total_cf

    cur_score = score_labels(labels)
    for _ in range(25):
        best_move: Optional[Tuple[int, int]] = None
        best_score = cur_score
        active_c = sorted(set(labels))
        for u in range(n_nodes):
            orig = labels[u]
            for c in active_c:
                if c == orig:
                    continue
                labels[u] = c
                sc = score_labels(labels)
                if sc > best_score + 1e-12:
                    best_score = sc
                    best_move = (u, c)
            labels[u] = orig
        if best_move is None:
            break
        labels[best_move[0]] = best_move[1]
        cur_score = best_score
    return labels


def run_probe_3() -> None:
    print("\nPROBE 3: MoJoFM vs. a2a/a2a_adj/ARI Gaming & Dependency/Directory Confounders")
    print("  Provenance: [exact reproduction of pinned repository logic] + [exact calculation of published algorithm/metric]")

    n = 120
    gold = [i // 12 for i in range(n)]
    over_split_pairs = [i // 2 for i in range(n)]
    monolith = [0] * n
    rng = random.Random(42)
    rand10 = [i % 10 for i in range(n)]
    rng.shuffle(rand10)

    mf_forward = mojofm(over_split_pairs, gold)
    mf_reverse = mojofm(gold, over_split_pairs)
    asym_pp = mf_forward - mf_reverse

    ari_mono = adjusted_rand_index(monolith, gold)
    a2a_lut_mono, a2a_zyr_mono, a2a_adj_mono = a2a_metrics(monolith, gold)
    cvg_mono = c2c_cvg(monolith, gold, thresh=0.66)

    ari_rand = adjusted_rand_index(rand10, gold)
    a2a_lut_rand, a2a_zyr_rand, a2a_adj_rand = a2a_metrics(rand10, gold)
    cvg_rand = c2c_cvg(rand10, gold, thresh=0.66)

    assert asym_pp > 35.0, f"Expected severe MoJoFM asymmetry (>35 pp), got {asym_pp:.2f}"
    assert abs(ari_mono) < 1e-12 and cvg_mono == 0.0
    assert a2a_lut_mono > 0.75 and a2a_zyr_mono > 0.75 and a2a_adj_mono < 0.12
    assert abs(ari_rand) < 0.05 and cvg_rand == 0.0
    assert a2a_lut_rand > 0.75 and a2a_zyr_rand > 0.80 and a2a_adj_rand < 0.20

    print(
        f"  MoJoFM Join-Free Asymmetry (N={n}, 60 pairs vs 10 modules): "
        f"MoJoFM(pairs->gold)={mf_forward:.2f}% vs MoJoFM(gold->pairs)={mf_reverse:.2f}% "
        f"(asymmetry=+{asym_pp:.2f} pp)"
    )
    print(
        f"  a2a Baseline Inflation vs ARI/a2a_adj: "
        f"Monolith[ARI={ari_mono:.4f}, c2c_66={cvg_mono:.4f}, a2a_Lut={a2a_lut_mono:.4f}, a2a_SemRef={a2a_zyr_mono:.4f}, a2a_adj={a2a_adj_mono:.4f}] | "
        f"Random10[ARI={ari_rand:.4f}, c2c_66={cvg_rand:.4f}, a2a_Lut={a2a_lut_rand:.4f}, a2a_SemRef={a2a_zyr_rand:.4f}, a2a_adj={a2a_adj_rand:.4f}]"
    )

    print("  Provenance: [controlled simulation]")
    n_mdg = 48
    gt_mdg = [i // 8 for i in range(n_mdg)]
    sym_edges: List[Tuple[int, int, float]] = []
    for m_idx in range(6):
        base = m_idx * 8
        ctrl = base
        for off in range(1, 8):
            sym_edges.append((base + off, ctrl, 1.0))
            sym_edges.append((base + off, base + ((off % 7) + 1), 1.0))
        sym_edges.append((base + 7, ((m_idx + 1) % 6) * 8, 1.0))

    # Synthetic C/C++ #include transitive bloat (4.58x edges): umbrella header exposes 7 headers in module 0
    inc_edges = list(sym_edges)
    umbrella_targets = [1, 2, 3, 4, 5, 6, 7]
    for u in range(n_mdg):
        for hdr in umbrella_targets:
            if u != hdr and (u, hdr, 1.0) not in inc_edges:
                inc_edges.append((u, hdr, 1.0))

    # Synthetic Java `import` intra-package omission: same-package symbol edges need no `import`
    imp_edges = [
        (u, v, wt)
        for (u, v, wt) in sym_edges
        if (u // 8) != (v // 8) or (u % 3 == 0 and v == (u // 8) * 8)
    ]

    bloat_ratio = len(inc_edges) / float(len(sym_edges))
    miss_pct = 100.0 * (1.0 - len(imp_edges) / float(len(sym_edges)))

    hub_inc = mojofm(acdc_hub_surrogate_cluster(n_mdg, inc_edges, 6), gt_mdg)
    bunch_inc = mojofm(bunch_hill_climb(n_mdg, inc_edges, 6, seed=7), gt_mdg)
    hub_sym = mojofm(acdc_hub_surrogate_cluster(n_mdg, sym_edges, 6), gt_mdg)
    bunch_sym = mojofm(bunch_hill_climb(n_mdg, sym_edges, 6, seed=7), gt_mdg)
    bunch_imp = mojofm(bunch_hill_climb(n_mdg, imp_edges, 6, seed=7), gt_mdg)

    dir_paths = [
        f"src/mod_{(i // 8 + 1) % 6 if i % 10 == 9 else (i // 8)}/f_{i}.c"
        for i in range(n_mdg)
    ]
    flat_paths = [f"src/f_{i:03d}.c" for i in range(n_mdg)]
    dir_map: Dict[str, int] = {}
    dir_labels = [dir_map.setdefault(p.rsplit("/", 1)[0], len(dir_map)) for p in dir_paths]
    flat_map: Dict[str, int] = {}
    flat_labels = [flat_map.setdefault(p.rsplit("/", 1)[0], len(flat_map)) for p in flat_paths]
    ari_dir = adjusted_rand_index(dir_labels, gt_mdg)
    ari_flat = adjusted_rand_index(flat_labels, gt_mdg)

    assert bloat_ratio > 4.0 and miss_pct > 45.0
    assert bunch_inc > hub_inc and hub_sym > bunch_sym + 25.0
    assert bunch_sym > bunch_imp + 15.0
    assert ari_dir > 0.70 and abs(ari_flat) < 1e-12

    print(
        f"  Extractor Confounders (N={n_mdg}): Include_bloat={bloat_ratio:.2f}x ({len(inc_edges)} vs {len(sym_edges)} sym edges), "
        f"Java_import_omission=-{miss_pct:.1f}% ({len(imp_edges)} edges) | "
        f"MoJoFM Include[ACDC_hub_surrogate={hub_inc:.1f}%, Bunch={bunch_inc:.1f}%] -> "
        f"Symbol[ACDC_hub_surrogate={hub_sym:.1f}%, Bunch={bunch_sym:.1f}%] vs Import[Bunch={bunch_imp:.1f}%]"
    )
    print(
        f"  Folder-Tree Shortcut Baseline: Immediate-parent directory ARI={ari_dir:.4f} vs Flattened ARI={ari_flat:.4f}"
    )


# =============================================================================
# PROBE 4: JVM 3-Axis (SOURCE, BINARY, SEMANTIC) Compatibility Lattice
# Pinned references:
#   - revapi/revapi@9ed5780461749706433bc1cdcef8023ad49046a9
#     (Code.java:93-216, Util.java:332-374, ConstantValueChanged.java:42-67,
#      ReturnTypeChanged.java:100-117, ParameterTypeChanged.java:66-114,
#      FormalTypeParametersChanged.java:85-107)
#   - siom79/japicmp@6262cf51923e20be3124a87b0a030a86b747cfbc
#     (JApiCompatibilityChangeType.java:9-95, CompatibilityChanges.java:449-509)
#   - alien-tools/maracas@01e7a0653169b40411c24d205bcafc98d066130a
#     (MissingJApiCompatibilityChange.java:8-10, JApiCmpDeltaFilter.java:25-37)
# =============================================================================


JVM_SUBTYPES: Dict[str, Set[str]] = {
    "Object": {"Object"},
    "CharSequence": {"CharSequence", "Object"},
    "Comparable": {"Comparable", "Object"},
    "CharSequence&Comparable": {"CharSequence&Comparable", "CharSequence", "Comparable", "Object"},
    "String": {"String", "CharSequence&Comparable", "CharSequence", "Comparable", "Object"},
    "Number": {"Number", "Object"},
    "Integer": {"Integer", "Number", "Comparable", "Object"},
    "void": {"void"},
    "int": {"int"},
    "boolean": {"boolean"},
}


def is_jvm_subtype(sub: str, sup: str) -> bool:
    return sup in JVM_SUBTYPES.get(sub, {sub, "Object"})


@dataclass(frozen=True)
class JvmMethod:
    name: str
    param_types: Tuple[str, ...]
    erased_params: Tuple[str, ...]
    return_type: str
    erased_return: str
    visibility: str = "public"  # "public" | "protected"
    is_static: bool = False
    is_bridge: bool = False
    is_default: bool = False
    type_param_sig: str = ""  # revapi Util.toUniqueString formal type-parameter representation
    checked_exceptions: Tuple[str, ...] = ()
    throws_checked_at_runtime: bool = False
    return_val: str = "ok"


@dataclass(frozen=True)
class JvmField:
    name: str
    ftype: str
    is_static: bool = True
    is_final: bool = True
    constant_value: Optional[int] = None  # ConstantValue attribute -> javac ldc inlining


@dataclass(frozen=True)
class JvmApiSnapshot:
    is_final_class: bool = False
    methods: Tuple[JvmMethod, ...] = ()
    fields: Tuple[JvmField, ...] = ()
    iface_a_default: Optional[str] = None
    iface_b_default: Optional[str] = None
    expected_protocol_ver: Optional[int] = None


@dataclass(frozen=True)
class JvmClientUse:
    kind: str
    # "call_method" | "call_null_arg" | "subclass_override" | "read_const" | "check_const_ver" | "diamond_impl"
    target_name: str
    arg_type: str = ""
    expected_ret_type: str = "Object"
    override_vis: str = "protected"
    override_ret: str = "CharSequence"
    catches_checked: Tuple[str, ...] = ()


def evaluate_jls_jvms_ground_truth(
    old_api: JvmApiSnapshot, new_api: JvmApiSnapshot, client: JvmClientUse
) -> Tuple[int, int, int]:
    """Operational JLS (§4.6, §4.9, §8.4.8.3, §9.4.1.3, §13, §15.12.2.5) + JVMS
    (§5.4.3.3, §5.4.6, §6.5) evaluator returning (SOURCE_COMPAT, BINARY_COMPAT,
    SEMANTIC_COMPAT) in {0, 1}^3. Excludes (0, 0, 1) by operational definition
    when S=0 and B=0 leave no runnable client artifact.
    """
    if client.kind == "diamond_impl":
        # JLS §9.4.1.3 & JVMS §5.4.3.3/§6.5 invokeinterface: unrelated default methods conflict
        conflict = (
            new_api.iface_a_default is not None
            and new_api.iface_b_default is not None
        )
        if conflict:
            return (0, 0, 0)
        return (1, 1, 1)

    if client.kind == "read_const":
        old_f = next(f for f in old_api.fields if f.name == client.target_name)
        new_f = next((f for f in new_api.fields if f.name == client.target_name), None)
        s_ok = int(new_f is not None)
        # ConstantValue inlined via bipush/ldc into precompiled Client.class -> zero field link ref
        b_ok = 1 if old_f.constant_value is not None else int(new_f is not None)
        sem_ok = 1 if (b_ok == 1 and (not s_ok or new_f.constant_value == old_f.constant_value)) else 0
        return (s_ok, b_ok, sem_ok)

    if client.kind == "check_const_ver":
        old_f = next(f for f in old_api.fields if f.name == client.target_name)
        new_f = next((f for f in new_api.fields if f.name == client.target_name), None)
        s_ok = int(new_f is not None)
        b_ok = 1 if old_f.constant_value is not None else int(new_f is not None)
        bin_runtime_matches = (old_f.constant_value == new_api.expected_protocol_ver)
        src_runtime_matches = (
            new_f is not None and new_f.constant_value == new_api.expected_protocol_ver
        )
        sem_ok = int(b_ok == 1 and bin_runtime_matches and (not s_ok or src_runtime_matches))
        return (s_ok, b_ok, sem_ok)

    if client.kind == "subclass_override":
        non_bridge_new = [
            m for m in new_api.methods if m.name == client.target_name and not m.is_bridge
        ]
        m_new = non_bridge_new[0]
        vis_rank = {"protected": 1, "public": 2}
        # JLS §8.4.8.3: cannot reduce visibility of overridden method; return must be subtype
        s_ok = int(
            not new_api.is_final_class
            and vis_rank[client.override_vis] >= vis_rank[m_new.visibility]
            and is_jvm_subtype(client.override_ret, m_new.return_type)
        )
        # JVMS §5.4.6 method selection: precompiled protected override of widened public method
        # and precompiled override matching synthetic ACC_BRIDGE descriptor slot both link and run
        has_matching_slot = any(
            m.name == client.target_name and m.erased_return == client.override_ret
            for m in new_api.methods
        )
        b_ok = int(not new_api.is_final_class and has_matching_slot)
        sem_ok = int(b_ok == 1)
        return (s_ok, b_ok, sem_ok)

    if client.kind in ("call_method", "call_null_arg"):
        old_candidates = [
            m for m in old_api.methods if m.name == client.target_name and not m.is_bridge
        ]
        old_target = old_candidates[0]

        new_non_bridge = [
            m for m in new_api.methods if m.name == client.target_name and not m.is_bridge
        ]
        if client.kind == "call_null_arg":
            applicable = [
                m for m in new_non_bridge if len(m.param_types) == 1 and m.param_types[0] != "int"
            ]
            most_specific = [
                m
                for m in applicable
                if all(is_jvm_subtype(m.param_types[0], o.param_types[0]) for o in applicable)
            ]
            resolved_src = most_specific[0] if len(most_specific) == 1 else None
        else:
            applicable = [
                m
                for m in new_non_bridge
                if (len(m.param_types) == 0 and client.arg_type == "")
                or (len(m.param_types) == 1 and is_jvm_subtype(client.arg_type, m.param_types[0]))
            ]
            most_specific = [
                m
                for m in applicable
                if all(
                    len(m.param_types) == 0
                    or is_jvm_subtype(m.param_types[0], o.param_types[0])
                    for o in applicable
                )
            ]
            resolved_src = most_specific[0] if len(most_specific) == 1 else None

        s_ok = 0
        if resolved_src is not None:
            ret_ok = is_jvm_subtype(resolved_src.return_type, client.expected_ret_type)
            uncaught = [
                ex for ex in resolved_src.checked_exceptions if ex not in client.catches_checked
            ]
            unreachable_catch = [
                ex for ex in client.catches_checked if ex not in resolved_src.checked_exceptions
            ]
            if ret_ok and not uncaught and not unreachable_catch:
                s_ok = 1

        # JVMS §5.4.3.3: exact erased name + descriptor + static flag match
        matched_bin = next(
            (
                m
                for m in new_api.methods
                if m.name == old_target.name
                and m.erased_params == old_target.erased_params
                and m.erased_return == old_target.erased_return
                and m.is_static == old_target.is_static
            ),
            None,
        )
        b_ok = int(matched_bin is not None)

        # Operational definition: when S=0 and B=0, no compiled or linked artifact survives to execute
        if s_ok == 0 and b_ok == 0:
            return (0, 0, 0)
        sem_ok = 1
        if b_ok == 1:
            assert matched_bin is not None
            if matched_bin.throws_checked_at_runtime or matched_bin.return_val != old_target.return_val:
                sem_ok = 0
        if s_ok == 1:
            assert resolved_src is not None
            if resolved_src.throws_checked_at_runtime or resolved_src.return_val != old_target.return_val:
                sem_ok = 0
        return (s_ok, b_ok, sem_ok)

    raise ValueError(f"Unknown client kind: {client.kind}")


def japicmp_oracle(old_api: JvmApiSnapshot, new_api: JvmApiSnapshot) -> Tuple[int, int, str]:
    """Exact decision logic of siom79/japicmp@6262cf51923e20be3124a87b0a030a86b747cfbc
    (JApiCompatibilityChangeType.java & CompatibilityChanges.java:449-509),
    returning (sourceCompat, binaryCompat, rule).
    """
    if old_api.iface_b_default is None and new_api.iface_b_default is not None:
        return (1, 1, "METHOD_NEW_DEFAULT")

    for f_old in old_api.fields:
        f_new = next((f for f in new_api.fields if f.name == f_old.name), None)
        if f_new is None:
            return (0, 0, "FIELD_REMOVED")
        if f_old.constant_value != f_new.constant_value:
            return (1, 1, "UNCHANGED_NO_CONSTANT_CHECK")

    old_non_bridge = [m for m in old_api.methods if not m.is_bridge]
    new_non_bridge = [m for m in new_api.methods if not m.is_bridge]
    if len(new_non_bridge) > len(old_non_bridge):
        return (1, 1, "METHOD_ADDED_TO_PUBLIC_CLASS")
    if not new_non_bridge and old_non_bridge:
        return (0, 0, "METHOD_REMOVED")

    if old_non_bridge and new_non_bridge:
        m0, m1 = old_non_bridge[0], new_non_bridge[0]
        if m0.is_static != m1.is_static:
            return (0, 0, "METHOD_NOW_STATIC")
        if m0.erased_params != m1.erased_params:
            return (0, 0, "METHOD_REMOVED_AND_ADDED")
        if m0.erased_return != m1.erased_return:
            has_bridge = any(
                b.is_bridge
                and b.name == m0.name
                and b.erased_params == m0.erased_params
                and b.erased_return == m0.erased_return
                for b in new_api.methods
            )
            if has_bridge and is_jvm_subtype(m1.return_type, m0.return_type):
                return (1, 1, "METHOD_RETURN_TYPE_COVARIANT_CHANGED")
            return (0, 0, "METHOD_RETURN_TYPE_CHANGED")
        if m0.visibility == "protected" and m1.visibility == "public":
            return (1, 1, "NONE_MISSING_METHOD_MORE_ACCESSIBLE")
        if set(m1.checked_exceptions) - set(m0.checked_exceptions):
            return (0, 1, "METHOD_NOW_THROWS_CHECKED_EXCEPTION")
        if set(m0.checked_exceptions) - set(m1.checked_exceptions):
            return (0, 1, "METHOD_NO_LONGER_THROWS_CHECKED_EXCEPTION")

    return (1, 1, "UNCHANGED")


def _revapi_code_tuple(
    src_sev: Optional[str], bin_sev: Optional[str], sem_sev: Optional[str], code: str
) -> Tuple[int, int, int, str]:
    """Uniform projection of revapi Code.java:209-216 DifferenceSeverity tuples:
    BREAKING / POTENTIALLY_BREAKING -> 0; NON_BREAKING / EQUIVALENT / None (null) -> 1.
    """
    breaking = ("BREAKING", "POTENTIALLY_BREAKING")
    return (
        0 if src_sev in breaking else 1,
        0 if bin_sev in breaking else 1,
        0 if sem_sev in breaking else 1,
        code,
    )


def revapi_oracle(old_api: JvmApiSnapshot, new_api: JvmApiSnapshot) -> Tuple[int, int, int, str]:
    """Exact 3-axis classification of revapi/revapi@9ed5780461749706433bc1cdcef8023ad49046a9
    (Code.java:93-216, Util.java:332-374, ConstantValueChanged.java:42-67,
    ReturnTypeChanged.java:100-117, ParameterTypeChanged.java:66-114,
    FormalTypeParametersChanged.java:85-107).
    """
    if old_api.iface_b_default is None and new_api.iface_b_default is not None:
        return _revapi_code_tuple(
            "NON_BREAKING", "NON_BREAKING", None, "METHOD_DEFAULT_METHOD_ADDED_TO_INTERFACE"
        )

    for f_old in old_api.fields:
        f_new = next((f for f in new_api.fields if f.name == f_old.name), None)
        if f_new is None:
            if f_old.constant_value is not None:
                return _revapi_code_tuple(
                    "BREAKING", "NON_BREAKING", "POTENTIALLY_BREAKING", "FIELD_CONSTANT_REMOVED"
                )
            return _revapi_code_tuple("BREAKING", "BREAKING", None, "FIELD_REMOVED")
        if f_old.constant_value != f_new.constant_value:
            return _revapi_code_tuple(
                "NON_BREAKING", "NON_BREAKING", "BREAKING", "FIELD_CONSTANT_VALUE_CHANGED"
            )

    # revapi-java analyzes javax.lang.model elements (JavacTask), which hide ACC_BRIDGE methods
    old_nb = [m for m in old_api.methods if not m.is_bridge]
    new_nb = [m for m in new_api.methods if not m.is_bridge]
    if len(new_nb) > len(old_nb):
        return _revapi_code_tuple("NON_BREAKING", "NON_BREAKING", None, "METHOD_ADDED")
    if not new_nb and old_nb:
        return _revapi_code_tuple("BREAKING", "BREAKING", None, "METHOD_REMOVED")

    if old_nb and new_nb:
        m0, m1 = old_nb[0], new_nb[0]
        if not m0.is_static and m1.is_static:
            return _revapi_code_tuple("NON_BREAKING", "BREAKING", None, "METHOD_NOW_STATIC")
        if m0.erased_params != m1.erased_params:
            # Util.toUniqueString (Util.java:340-343) serializes non-method IntersectionType bounds
            # in declaration order; when type_param_sig differs, FormalTypeParametersChanged.java:88-92
            # + ParameterTypeChanged.java:107 report GENERICS_FORMAL_TYPE_PARAMETER_CHANGED (BREAKING,
            # NON_BREAKING, null) + METHOD_PARAMETER_TYPE_CHANGED (POTENTIALLY_BREAKING, BREAKING, null).
            # When oldParam.equals(newParam) holds (e.g., generic superclass pull-up in
            # MethodChecksTest.java:485-504), ParameterTypeChanged.java:99-104 emits
            # METHOD_PARAMETER_TYPE_ERASURE_CHANGED (NON_BREAKING, BREAKING, null).
            if m0.type_param_sig != m1.type_param_sig or m0.param_types != m1.param_types:
                return _revapi_code_tuple(
                    "BREAKING",
                    "BREAKING",
                    None,
                    "GENERICS_FORMAL_TYPE_PARAMETER_CHANGED+METHOD_PARAMETER_TYPE_CHANGED",
                )
            return _revapi_code_tuple(
                "NON_BREAKING", "BREAKING", None, "METHOD_PARAMETER_TYPE_ERASURE_CHANGED"
            )
        if m0.erased_return != m1.erased_return and is_jvm_subtype(m1.return_type, m0.return_type):
            # ReturnTypeChanged.java:104-105 unconditionally emits METHOD_RETURN_TYPE_CHANGED_COVARIANTLY
            # (ignoring bytecode ACC_BRIDGE), inverting both S and B on bridge-backed subclass overrides!
            return _revapi_code_tuple(
                "NON_BREAKING", "BREAKING", None, "METHOD_RETURN_TYPE_CHANGED_COVARIANTLY"
            )
        if m0.visibility == "protected" and m1.visibility == "public":
            if new_api.is_final_class:
                return _revapi_code_tuple(
                    "NON_BREAKING", "EQUIVALENT", None, "METHOD_VISIBILITY_INCREASED_IN_FINAL_CLASS"
                )
            return _revapi_code_tuple(
                "POTENTIALLY_BREAKING", "EQUIVALENT", None, "METHOD_VISIBILITY_INCREASED"
            )
        if set(m1.checked_exceptions) - set(m0.checked_exceptions):
            return _revapi_code_tuple(
                "BREAKING", "NON_BREAKING", None, "METHOD_CHECKED_EXCEPTION_ADDED"
            )

    return _revapi_code_tuple("EQUIVALENT", "EQUIVALENT", "EQUIVALENT", "EQUIVALENT")


def run_probe_4() -> None:
    print("\nPROBE 4: JVM 3-Axis (SOURCE, BINARY, SEMANTIC) Lattice — revapi vs. japicmp")
    print("  Provenance: [exact reproduction of pinned repository logic] + [derived analytical model]")

    # Verify harmonized `null` semantic severity mapping on pure removals (Code.java:110, 150)
    assert revapi_oracle(
        JvmApiSnapshot(fields=(JvmField("X", "int", constant_value=None),)),
        JvmApiSnapshot(),
    ) == (0, 0, 1, "FIELD_REMOVED")
    assert revapi_oracle(
        JvmApiSnapshot(methods=(JvmMethod("f", (), (), "void", "void"),)),
        JvmApiSnapshot(),
    ) == (0, 0, 1, "METHOD_REMOVED")

    transitions: List[Tuple[str, JvmApiSnapshot, JvmApiSnapshot, JvmClientUse]] = [
        # 1. Cell (1, 1, 1): Fully compatible addition on final class
        (
            "final_class_helper_added",
            JvmApiSnapshot(is_final_class=True, methods=(JvmMethod("f", ("String",), ("String",), "String", "String"),)),
            JvmApiSnapshot(
                is_final_class=True,
                methods=(
                    JvmMethod("f", ("String",), ("String",), "String", "String"),
                    JvmMethod("ping", (), (), "String", "String"),
                ),
            ),
            JvmClientUse("call_method", "f", arg_type="String", expected_ret_type="String"),
        ),
        # 2. Cell (1, 1, 0): ConstantValue 1 -> 2 ldc inlining behavioral break
        (
            "constant_value_changed_ldc",
            JvmApiSnapshot(fields=(JvmField("VER", "int", constant_value=1),), expected_protocol_ver=1),
            JvmApiSnapshot(fields=(JvmField("VER", "int", constant_value=2),), expected_protocol_ver=2),
            JvmClientUse("check_const_ver", "VER"),
        ),
        # 3. Cell (1, 1, 0) #2: Overload specialization capturing String argument on recompile
        (
            "overload_specialization_shift",
            JvmApiSnapshot(methods=(JvmMethod("fmt", ("Object",), ("Object",), "String", "String", return_val="obj"),)),
            JvmApiSnapshot(
                methods=(
                    JvmMethod("fmt", ("Object",), ("Object",), "String", "String", return_val="obj"),
                    JvmMethod("fmt", ("CharSequence",), ("CharSequence",), "String", "String", return_val="cs"),
                )
            ),
            JvmClientUse("call_method", "fmt", arg_type="String", expected_ret_type="String"),
        ),
        # 4. Cell (0, 1, 1): Constant field removed (inlined ldc survives binary linkage)
        (
            "constant_field_removed_ldc",
            JvmApiSnapshot(fields=(JvmField("MAGIC", "int", constant_value=42),)),
            JvmApiSnapshot(fields=()),
            JvmClientUse("read_const", "MAGIC"),
        ),
        # 5. Cell (0, 1, 1) #2: Non-final protected -> public visibility widening vs subclass override
        (
            "protected_to_public_subclass",
            JvmApiSnapshot(methods=(JvmMethod("hook", (), (), "String", "String", visibility="protected"),)),
            JvmApiSnapshot(methods=(JvmMethod("hook", (), (), "String", "String", visibility="public"),)),
            JvmClientUse("subclass_override", "hook", override_vis="protected", override_ret="String"),
        ),
        # 6. Cell (0, 1, 1) #3: Overriding covariant return WITH ACC_BRIDGE vs subclass override
        (
            "covariant_return_with_bridge_subclass",
            JvmApiSnapshot(methods=(JvmMethod("m", (), (), "CharSequence", "CharSequence"),)),
            JvmApiSnapshot(
                methods=(
                    JvmMethod("m", (), (), "String", "String"),
                    JvmMethod("m", (), (), "CharSequence", "CharSequence", is_bridge=True),
                )
            ),
            JvmClientUse("subclass_override", "m", override_vis="public", override_ret="CharSequence"),
        ),
        # 7. Cell (0, 1, 1) #4: Overloaded null literal call ambiguity
        (
            "overload_null_ambiguity",
            JvmApiSnapshot(methods=(JvmMethod("f", ("String",), ("String",), "String", "String"),)),
            JvmApiSnapshot(
                methods=(
                    JvmMethod("f", ("String",), ("String",), "String", "String"),
                    JvmMethod("f", ("Integer",), ("Integer",), "String", "String"),
                )
            ),
            JvmClientUse("call_null_arg", "f", expected_ret_type="String"),
        ),
        # 8. Cell (1, 0, 1): Standalone covariant return WITHOUT ACC_BRIDGE vs caller
        (
            "standalone_covariant_no_bridge",
            JvmApiSnapshot(methods=(JvmMethod("m", (), (), "CharSequence", "CharSequence"),)),
            JvmApiSnapshot(methods=(JvmMethod("m", (), (), "String", "String"),)),
            JvmClientUse("call_method", "m", expected_ret_type="CharSequence"),
        ),
        # 9. Cell (1, 0, 1) #2: Instance method promoted to static on final class
        (
            "instance_method_now_static",
            JvmApiSnapshot(is_final_class=True, methods=(JvmMethod("id", (), (), "String", "String", is_static=False),)),
            JvmApiSnapshot(is_final_class=True, methods=(JvmMethod("id", (), (), "String", "String", is_static=True),)),
            JvmClientUse("call_method", "id", expected_ret_type="String"),
        ),
        # 10. Cell (1, 0, 1) #3: Intersection-bound order reversal
        # (<T extends CharSequence & Comparable<T>> T echo(T) -> <T extends Comparable<T> & CharSequence> T echo(T))
        (
            "intersection_bound_erasure_shift",
            JvmApiSnapshot(
                methods=(
                    JvmMethod(
                        "echo",
                        ("CharSequence&Comparable",),
                        ("CharSequence",),
                        "CharSequence&Comparable",
                        "CharSequence",
                        type_param_sig="CharSequence+Comparable<%>+",
                    ),
                )
            ),
            JvmApiSnapshot(
                methods=(
                    JvmMethod(
                        "echo",
                        ("CharSequence&Comparable",),
                        ("Comparable",),
                        "CharSequence&Comparable",
                        "Comparable",
                        type_param_sig="Comparable<%>+CharSequence+",
                    ),
                )
            ),
            JvmClientUse("call_method", "echo", arg_type="String", expected_ret_type="CharSequence"),
        ),
        # 11. Cell (0, 1, 0): Checked exception added to signature AND thrown at runtime
        (
            "checked_exception_added_thrown",
            JvmApiSnapshot(methods=(JvmMethod("read", (), (), "String", "String", return_val="fallback"),)),
            JvmApiSnapshot(
                methods=(
                    JvmMethod(
                        "read",
                        (),
                        (),
                        "String",
                        "String",
                        checked_exceptions=("IOException",),
                        throws_checked_at_runtime=True,
                    ),
                )
            ),
            JvmClientUse("call_method", "read", expected_ret_type="String"),
        ),
        # 12. Cell (1, 0, 0): Standalone covariant return + altered return value
        (
            "covariant_no_bridge_altered_val",
            JvmApiSnapshot(methods=(JvmMethod("mode", (), (), "CharSequence", "CharSequence", return_val="v1"),)),
            JvmApiSnapshot(methods=(JvmMethod("mode", (), (), "String", "String", return_val="v2"),)),
            JvmClientUse("call_method", "mode", expected_ret_type="CharSequence"),
        ),
        # 13. Cell (0, 0, 0): Default interface method diamond conflict (A.f vs B.f)
        (
            "default_method_diamond_conflict",
            JvmApiSnapshot(iface_a_default="A", iface_b_default=None),
            JvmApiSnapshot(iface_a_default="A", iface_b_default="B"),
            JvmClientUse("diamond_impl", "f"),
        ),
    ]

    inhabited_cells: Set[Tuple[int, int, int]] = set()
    japicmp_false_neg = 0
    japicmp_false_pos = 0
    revapi_exact_catches_over_japicmp = 0
    bridge_dual_inversion = False

    for label, old_s, new_s, client in transitions:
        gt = evaluate_jls_jvms_ground_truth(old_s, new_s, client)
        inhabited_cells.add(gt)
        j_s, j_b, _ = japicmp_oracle(old_s, new_s)
        r_s, r_b, r_sem, r_rule = revapi_oracle(old_s, new_s)

        gt_all_ok = (gt == (1, 1, 1))
        j_all_ok = (j_s == 1 and j_b == 1)

        if not gt_all_ok and j_all_ok:
            japicmp_false_neg += 1
            if (r_s, r_b, r_sem) == gt:
                revapi_exact_catches_over_japicmp += 1
        if (gt[0] == 1 and j_s == 0) or (gt[1] == 1 and j_b == 0):
            japicmp_false_pos += 1
        if label == "covariant_return_with_bridge_subclass":
            bridge_dual_inversion = (
                gt == (0, 1, 1)
                and (j_s, j_b) == (1, 1)
                and (r_s, r_b, r_sem) == (1, 0, 1)
                and r_rule == "METHOD_RETURN_TYPE_CHANGED_COVARIANTLY"
            )

    expected_7_cells = {
        (1, 1, 1),
        (1, 1, 0),
        (0, 1, 1),
        (1, 0, 1),
        (0, 1, 0),
        (1, 0, 0),
        (0, 0, 0),
    }
    assert inhabited_cells == expected_7_cells, f"Missing feasible lattice cell: {expected_7_cells - inhabited_cells}"
    assert (0, 0, 1) not in inhabited_cells
    assert japicmp_false_neg == 6 and japicmp_false_pos == 5
    assert revapi_exact_catches_over_japicmp == 2
    assert bridge_dual_inversion, "Expected dual japicmp (1,1) vs revapi (1,0,1) failure on ACC_BRIDGE override"

    print(
        f"  Lattice Coverage: {len(inhabited_cells)}/7 operationally feasible (SOURCE, BINARY, SEMANTIC) cells inhabited "
        f"((0,0,1) excluded by operational definition when S=0 & B=0 leave no runnable client artifact)"
    )
    print(
        f"  Oracle Audit ({len(transitions)} transitions): "
        f"japicmp_false_negatives={japicmp_false_neg} "
        f"(ConstantValue, 2x overload [specialization + null ambiguity], protected->public, ACC_BRIDGE subclass, default diamond), "
        f"japicmp_axis_false_positives={japicmp_false_pos} (2x standalone covariant S, static S, erasure S, const-removal B), "
        f"exact_axis_revapi_catches_where_japicmp_silent={revapi_exact_catches_over_japicmp} "
        f"(FIELD_CONSTANT_VALUE_CHANGED, METHOD_VISIBILITY_INCREASED), "
        f"bridge_covariant_dual_inversion=japicmp(1,1)_vs_revapi(1,0,1)_on_gt(0,1,1)"
    )


# =============================================================================
# PROBE 5: Go golang/exp apidiff Correspondence & Pointer-Receiver Soundness Bug
# Pinned reference:
#   - golang/exp@e1094eeca1b508317bb24413555d977dea6bb30c
#     (apidiff/apidiff.go:111-235, compatibility.go:110-162, 265-355, correspondence.go:30-308)
# =============================================================================


@dataclass(frozen=True)
class GoSig:
    params: Tuple["GoType", ...] = ()
    results: Tuple["GoType", ...] = ()


@dataclass(frozen=True)
class GoField:
    name: str
    typ: "GoType"
    exported: bool


@dataclass
class GoType:
    kind: str  # "basic" | "map" | "pointer" | "struct" | "interface" | "named"
    name: str = ""
    exported: bool = False
    elem: Optional["GoType"] = None
    fields: Tuple[GoField, ...] = ()
    iface_methods: Dict[str, Tuple[GoSig, bool]] = field(default_factory=dict)
    underlying: Optional["GoType"] = None
    value_methods: Dict[str, Tuple[GoSig, bool]] = field(default_factory=dict)
    ptr_methods: Dict[str, Tuple[GoSig, bool]] = field(default_factory=dict)


def go_is_comparable(t: GoType) -> bool:
    if t.kind == "named":
        assert t.underlying is not None
        return go_is_comparable(t.underlying)
    if t.kind in ("basic", "pointer", "interface"):
        return True
    if t.kind == "map":
        return False
    if t.kind == "struct":
        return all(go_is_comparable(f.typ) for f in t.fields)
    return False


def go_method_set(t: GoType) -> Dict[str, Tuple[GoSig, bool]]:
    if t.kind == "pointer" and t.elem is not None and t.elem.kind == "named":
        merged = dict(t.elem.value_methods)
        merged.update(t.elem.ptr_methods)
        return merged
    if t.kind == "named":
        if t.underlying is not None and t.underlying.kind == "interface":
            return dict(t.underlying.iface_methods)
        return dict(t.value_methods)
    if t.kind == "interface":
        return dict(t.iface_methods)
    return {}


def go_implements(t: GoType, iface: GoType) -> bool:
    ms = go_method_set(t)
    req = iface.underlying.iface_methods if iface.kind == "named" and iface.underlying else iface.iface_methods
    for m_name, (m_sig, m_exp) in req.items():
        if m_name not in ms:
            return False
        got_sig, got_exp = ms[m_name]
        if got_exp != m_exp or len(got_sig.params) != len(m_sig.params) or len(got_sig.results) != len(m_sig.results):
            return False
    return True


@dataclass
class GoPackage:
    types: Dict[str, GoType] = field(default_factory=dict)
    funcs: Dict[str, GoSig] = field(default_factory=dict)


class GoApidiffPort:
    """Faithful port of golang/exp@e1094eeca1b508317bb24413555d977dea6bb30c
    apidiff.{checkPackage, establishCorrespondence, checkCompatibleDefined,
    checkCompatibleInterface, checkCompatibleStruct}.
    """

    def __init__(self, old_pkg: GoPackage, new_pkg: GoPackage, fix_pointer_implements: bool = False) -> None:
        self.old_pkg = old_pkg
        self.new_pkg = new_pkg
        self.fix_pointer_implements = fix_pointer_implements
        self.correspond_map: Dict[str, GoType] = {}
        self.incompatibles: List[str] = []
        self.compatibles: List[str] = []

    def correspond(self, old: GoType, new: GoType) -> bool:
        if old.kind == "named":
            return self.establish_correspondence(old, new)
        if old.kind != new.kind:
            return False
        if old.kind == "basic":
            return old.name == new.name
        if old.kind == "pointer":
            assert old.elem is not None and new.elem is not None
            return self.correspond(old.elem, new.elem)
        if old.kind == "map":
            assert old.elem is not None and new.elem is not None
            return self.correspond(old.elem, new.elem)
        return old.name == new.name

    def corresp_sig(self, s1: GoSig, s2: GoSig) -> bool:
        if len(s1.params) != len(s2.params) or len(s1.results) != len(s2.results):
            return False
        p_ok = all(self.correspond(a, b) for a, b in zip(s1.params, s2.params))
        r_ok = all(self.correspond(a, b) for a, b in zip(s1.results, s2.results))
        return p_ok and r_ok

    def establish_correspondence(self, old: GoType, new: GoType) -> bool:
        # correspondence.go:211-213
        if old.name in self.correspond_map:
            prev = self.correspond_map[old.name]
            return prev.kind == new.kind and prev.name == new.name
        # correspondence.go:214-229: exported old named type must resolve by same name in new
        if old.exported:
            looked = self.new_pkg.types.get(old.name)
            if looked is None or looked.name != new.name:
                return False
        if new.kind not in ("named", "basic"):
            return False
        # correspondence.go:304-306
        self.correspond_map[old.name] = new
        self.check_compatible_defined(old, new)
        return True

    def check_compatible_defined(self, old: GoType, new: GoType) -> None:
        assert old.underlying is not None
        new_u = new.underlying if new.kind == "named" and new.underlying is not None else new
        if old.underlying.kind != new_u.kind:
            self.incompatibles.append(f"{old.name}: underlying kind changed")
            return
        if old.underlying.kind == "interface":
            self.check_compatible_interface(old.name, old.underlying, new_u)
            return
        if old.underlying.kind == "struct":
            self.check_compatible_struct(old.name, old.underlying, new_u)
        # compatibility.go:279-280 checks exported methods on value AND pointer
        self.check_method_set(old.name, old, new, add_compat=True)
        self.check_method_set(
            "*" + old.name,
            GoType(kind="pointer", elem=old),
            GoType(kind="pointer", elem=new),
            add_compat=True,
        )

    def check_compatible_interface(self, name: str, old_i: GoType, new_i: GoType) -> None:
        # compatibility.go:113-126
        has_unexported_old = any(not exp for _, exp in old_i.iface_methods.values())
        if has_unexported_old:
            self.check_method_set(name, old_i, new_i, add_compat=True)
        else:
            self.check_method_set(name, old_i, new_i, add_compat=False)
            for m_name, (_, exp) in sorted(new_i.iface_methods.items()):
                if not exp:
                    self.incompatibles.append(f"{name}.{m_name}: added unexported method")

    def check_compatible_struct(self, name: str, old_s: GoType, new_s: GoType) -> None:
        # compatibility.go:155-162
        old_exp = {f.name: f.typ for f in old_s.fields if f.exported}
        new_exp = {f.name: f.typ for f in new_s.fields if f.exported}
        for fname in sorted(old_exp):
            if fname not in new_exp:
                self.incompatibles.append(f"{name}.{fname}: removed")
            elif not self.correspond(old_exp[fname], new_exp[fname]):
                self.incompatibles.append(f"{name}.{fname}: type changed")
        for fname in sorted(new_exp):
            if fname not in old_exp:
                self.compatibles.append(f"{name}.{fname}: added")
        if go_is_comparable(old_s) and not go_is_comparable(new_s):
            self.incompatibles.append(f"{name}: old is comparable, new is not")

    def check_method_set(self, label: str, old_t: GoType, new_t: GoType, add_compat: bool) -> None:
        old_ms = {k: sig for k, (sig, exp) in go_method_set(old_t).items() if exp}
        new_ms = {k: sig for k, (sig, exp) in go_method_set(new_t).items() if exp}
        for m_name in sorted(old_ms):
            if m_name not in new_ms:
                self.incompatibles.append(f"{label}.{m_name}: removed")
            elif not self.corresp_sig(old_ms[m_name], new_ms[m_name]):
                self.incompatibles.append(f"{label}.{m_name}: signature changed")
        for m_name in sorted(new_ms):
            if m_name not in old_ms:
                if add_compat:
                    self.compatibles.append(f"{label}.{m_name}: added")
                else:
                    self.incompatibles.append(f"{label}.{m_name}: added")

    def run(self) -> Tuple[List[str], List[str]]:
        # Pass 1: exported defined types (apidiff.go:158-169)
        for name in sorted(self.old_pkg.types):
            ot = self.old_pkg.types[name]
            if not ot.exported:
                continue
            nt = self.new_pkg.types.get(name)
            if nt is None or not nt.exported:
                self.incompatibles.append(f"{name}: removed")
                continue
            if not self.correspond(ot, nt):
                self.incompatibles.append(f"{name}: changed")

        # Pass 2: exported functions (apidiff.go:172-183)
        for fname in sorted(self.old_pkg.funcs):
            osig = self.old_pkg.funcs[fname]
            nsig = self.new_pkg.funcs.get(fname)
            if nsig is None:
                self.incompatibles.append(f"{fname}: removed")
            elif not self.corresp_sig(osig, nsig):
                self.incompatibles.append(f"{fname}: changed")

        # Whole-package satisfaction (apidiff.go:205-234):
        # Upstream bug at L228: checks ONLY `types.Implements(otn2.Type(), oIface)` (value type),
        # omitting `types.NewPointer(otn2.Type())` (`*Impl` pointer implementors).
        pairs = sorted(self.correspond_map.items(), key=lambda kv: kv[0])
        for o_name1, nt1 in pairs:
            ot1 = self.old_pkg.types[o_name1]
            if ot1.underlying is None or ot1.underlying.kind != "interface":
                continue
            nt1_u = nt1.underlying if nt1.kind == "named" else nt1
            if nt1_u is None or nt1_u.kind != "interface":
                continue
            for o_name2, nt2 in pairs:
                if o_name1 == o_name2:
                    continue
                ot2 = self.old_pkg.types[o_name2]
                if go_implements(ot2, ot1) and not go_implements(nt2, nt1):
                    self.incompatibles.append(f"{o_name2}: no longer implements {o_name1}")
                if self.fix_pointer_implements and nt2.kind == "named":
                    opt2 = GoType(kind="pointer", elem=ot2)
                    npt2 = GoType(kind="pointer", elem=nt2)
                    if go_implements(opt2, ot1) and not go_implements(npt2, nt1):
                        self.incompatibles.append(f"*{o_name2}: no longer implements {o_name1}")

        return self.incompatibles, self.compatibles


def run_probe_5() -> None:
    print("\nPROBE 5: Go golang/exp apidiff Correspondence & Sealed-Interface Soundness")
    print("  Provenance: [exact reproduction of pinned repository logic]")

    t_int = GoType(kind="basic", name="int")
    t_map = GoType(kind="map", name="map[string]int", elem=t_int)

    # 5A: Valid unexported type rename vs invalid 1-to-2 split (correspondence.go:211-213)
    old_priv = GoType(
        kind="named",
        name="oldTok",
        exported=False,
        underlying=GoType(kind="struct", fields=(GoField("ID", t_int, True),)),
    )
    new_priv_a = GoType(
        kind="named",
        name="newTokA",
        exported=False,
        underlying=GoType(kind="struct", fields=(GoField("ID", t_int, True),)),
    )
    new_priv_b = GoType(
        kind="named",
        name="newTokB",
        exported=False,
        underlying=GoType(kind="struct", fields=(GoField("ID", t_int, True),)),
    )
    pkg_old_corr = GoPackage(
        types={"oldTok": old_priv},
        funcs={"Open": GoSig((), (old_priv,)), "Use": GoSig((old_priv,), ())},
    )
    pkg_new_valid_rename = GoPackage(
        types={"newTokA": new_priv_a},
        funcs={"Open": GoSig((), (new_priv_a,)), "Use": GoSig((new_priv_a,), ())},
    )
    pkg_new_broken_split = GoPackage(
        types={"newTokA": new_priv_a, "newTokB": new_priv_b},
        funcs={"Open": GoSig((), (new_priv_a,)), "Use": GoSig((new_priv_b,), ())},
    )

    inc_rename, _ = GoApidiffPort(pkg_old_corr, pkg_new_valid_rename).run()
    inc_split, _ = GoApidiffPort(pkg_old_corr, pkg_new_broken_split).run()
    assert len(inc_rename) == 0, "Consistent unexported rename must be compatible"
    assert len(inc_split) == 1 and "Use: changed" in inc_split[0], "Inconsistent 1->2 split must break Use(Open())"

    # 5B: Unexported non-comparable struct field breaks client map[pkg.Key]V (compatibility.go:159-161)
    key_old = GoType(
        kind="named",
        name="Key",
        exported=True,
        underlying=GoType(kind="struct", fields=(GoField("X", t_int, True),)),
    )
    key_new = GoType(
        kind="named",
        name="Key",
        exported=True,
        underlying=GoType(
            kind="struct",
            fields=(GoField("X", t_int, True), GoField("cache", t_map, False)),
        ),
    )
    inc_comp, _ = GoApidiffPort(GoPackage(types={"Key": key_old}), GoPackage(types={"Key": key_new})).run()
    assert inc_comp == ["Key: old is comparable, new is not"]

    # 5C: Sealed interface evolution — Value Receiver (CAUGHT at apidiff.go:228 despite stale
    # compatibility.go:110-112 TODO) vs Pointer Receiver `*PtrImpl` (MISSED at apidiff.go:228)
    sig0 = GoSig()
    iface_old = GoType(
        kind="named",
        name="I",
        exported=True,
        underlying=GoType(kind="interface", iface_methods={"seal": (sig0, False), "M1": (sig0, True)}),
    )
    iface_new = GoType(
        kind="named",
        name="I",
        exported=True,
        underlying=GoType(
            kind="interface",
            iface_methods={"seal": (sig0, False), "M1": (sig0, True), "M2": (sig0, True)},
        ),
    )
    val_impl = GoType(
        kind="named",
        name="ValImpl",
        exported=True,
        underlying=GoType(kind="struct"),
        value_methods={"seal": (sig0, False), "M1": (sig0, True)},
    )
    ptr_impl = GoType(
        kind="named",
        name="PtrImpl",
        exported=True,
        underlying=GoType(kind="struct"),
        ptr_methods={"seal": (sig0, False), "M1": (sig0, True)},
    )

    inc_val, _ = GoApidiffPort(
        GoPackage(types={"I": iface_old, "ValImpl": val_impl}),
        GoPackage(types={"I": iface_new, "ValImpl": val_impl}),
    ).run()
    client_val_old = go_implements(val_impl, iface_old)
    client_val_new = go_implements(val_impl, iface_new)

    inc_ptr_upstream, comp_ptr_upstream = GoApidiffPort(
        GoPackage(types={"I": iface_old, "PtrImpl": ptr_impl}),
        GoPackage(types={"I": iface_new, "PtrImpl": ptr_impl}),
        fix_pointer_implements=False,
    ).run()
    inc_ptr_repaired, _ = GoApidiffPort(
        GoPackage(types={"I": iface_old, "PtrImpl": ptr_impl}),
        GoPackage(types={"I": iface_new, "PtrImpl": ptr_impl}),
        fix_pointer_implements=True,
    ).run()
    client_ptr_old = go_implements(GoType(kind="pointer", elem=ptr_impl), iface_old)
    client_ptr_new = go_implements(GoType(kind="pointer", elem=ptr_impl), iface_new)

    assert client_val_old and not client_val_new and inc_val == ["ValImpl: no longer implements I"]
    assert client_ptr_old and not client_ptr_new
    assert inc_ptr_upstream == [] and comp_ptr_upstream == ["I.M2: added"]
    assert inc_ptr_repaired == ["*PtrImpl: no longer implements I"]

    print(
        f"  Correspondence & Comparability: valid_unexported_rename_incompat={len(inc_rename)}, "
        f"inconsistent_1to2_split_incompat={len(inc_split)} ({inc_split[0]}), "
        f"unexported_map_field='{inc_comp[0]}'"
    )
    print(
        f"  Sealed-Interface Verification: "
        f"ValueReceiver[client_breaks={not client_val_new}, apidiff_incompat={inc_val}] | "
        f"PointerReceiver_Bug[client_breaks={not client_ptr_new}, upstream_apidiff_incompat={inc_ptr_upstream}, "
        f"repaired_apidiff_incompat={inc_ptr_repaired}]"
    )


def main() -> None:
    print("=== ARCHITECTURE RECOVERY & API COMPATIBILITY VERIFICATION SUITE ===")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 PROBE PILLARS PASSED ALL DETERMINISTIC INVARIANTS.")


if __name__ == "__main__":
    main()
