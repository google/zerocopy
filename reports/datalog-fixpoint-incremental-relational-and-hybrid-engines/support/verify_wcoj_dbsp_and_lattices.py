#!/usr/bin/env python3
"""Standalone relational engine probe for WCOJ/Free Join, DBSP Z-set IVM, and lattice/negation semantics.

Requires Python 3.10+ and only the Python standard library.
Verifies four properties with deterministic synthetic workloads:
  1. Cyclic triangle query R(x,y) ^ S(y,z) ^ T(z,x): compares all three binary
     hash-join plans (O(N^2) intermediate blowup on adversarial skew graphs)
     against Generic Join (WCOJ) and Free Join (O(N) on skew, O(N^{3/2}) AGM
     bound on dense cliques).
  2. DBSP Z-set incremental view maintenance (Q^Delta = D o Q o I): verifies
     exact algebraic equivalence against full from-scratch recomputation across
     bilinear joins, incremental distinct, and 2D-nested recursive transitive
     closure under arbitrary insertions, duplicate weights, diamond retractions,
     and cycle-breaking deletions.
  3. Monotone finite-height lattice semi-naive evaluation vs. infinite-height
     divergence without widening (and convergence with widening).
  4. Unstratified negation (odd cycle oscillation / no stable model; even cycle
     multiple stable models; 3-valued Well-Founded Semantics) and non-monotone /
     stateful host FFI corruption of semi-naive confluence.
"""

from __future__ import annotations

import math
import random
from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, DefaultDict, Dict, Hashable, Iterable, List, Set, Tuple


# =============================================================================
# Part 1: Cyclic Triangle Join — Binary Hash Join vs. Generic Join vs. Free Join
# =============================================================================

Edge = Tuple[int, int]
Triangle = Tuple[int, int, int]


def build_skew_triangle_instance(m: int) -> Tuple[List[Edge], List[Edge], List[Edge]]:
    """Adversarial hub-and-spoke skew instance (Ngo et al. 2018 / Wang et al. 2023).

    Each relation has |R| = |S| = |T| = 2m + 1 edges:
      {(0, 0)} U {(0, i) | 1 <= i <= m} U {(i, 0) | 1 <= i <= m}.
    Exact triangle count is 3m + 1 = Theta(N), yet every binary join of any two
    relations produces >= m^2 = Theta(N^2) intermediate tuples through hub 0.
    """
    edges = [(0, 0)]
    for i in range(1, m + 1):
        edges.append((0, i))
        edges.append((i, 0))
    return list(edges), list(edges), list(edges)


def build_dense_clique_instance(v: int) -> Tuple[List[Edge], List[Edge], List[Edge]]:
    """Directed complete graph K_v with N = v^2 edges and v^3 = N^{3/2} triangles (tight AGM bound)."""
    edges = [(i, j) for i in range(v) for j in range(v)]
    return list(edges), list(edges), list(edges)


@dataclass
class JoinStats:
    result_count: int
    intermediate_tuples: int
    probe_steps: int


def binary_hash_join_triangle(
    r: List[Edge], s: List[Edge], t: List[Edge], order: str = "RS_T"
) -> Tuple[Set[Triangle], JoinStats]:
    """Execute R(x,y) ^ S(y,z) ^ T(z,x) via a two-stage binary hash-join plan."""
    t_set = set(t)
    r_set = set(r)
    s_set = set(s)
    out: Set[Triangle] = set()
    inter = 0
    probes = 0

    if order == "RS_T":
        s_by_y: DefaultDict[int, List[int]] = defaultdict(list)
        for y, z in s:
            s_by_y[y].append(z)
        intermediate: List[Triangle] = []
        for x, y in r:
            for z in s_by_y.get(y, ()):
                intermediate.append((x, y, z))
                probes += 1
        inter = len(intermediate)
        for x, y, z in intermediate:
            probes += 1
            if (z, x) in t_set:
                out.add((x, y, z))
    elif order == "ST_R":
        t_by_z: DefaultDict[int, List[int]] = defaultdict(list)
        for z, x in t:
            t_by_z[z].append(x)
        intermediate = []
        for y, z in s:
            for x in t_by_z.get(z, ()):
                intermediate.append((x, y, z))
                probes += 1
        inter = len(intermediate)
        for x, y, z in intermediate:
            probes += 1
            if (x, y) in r_set:
                out.add((x, y, z))
    elif order == "TR_S":
        r_by_x: DefaultDict[int, List[int]] = defaultdict(list)
        for x, y in r:
            r_by_x[x].append(y)
        intermediate = []
        for z, x in t:
            for y in r_by_x.get(x, ()):
                intermediate.append((x, y, z))
                probes += 1
        inter = len(intermediate)
        for x, y, z in intermediate:
            probes += 1
            if (y, z) in s_set:
                out.add((x, y, z))
    else:
        raise ValueError(f"Unknown binary plan order: {order}")

    return out, JoinStats(len(out), inter, probes)


def generic_join_triangle(
    r: List[Edge], s: List[Edge], t: List[Edge]
) -> Tuple[Set[Triangle], JoinStats]:
    """Generic Join (WCOJ) over variable order (x, y, z) using hash-trie levels and smallest-set-first intersection."""
    # Level-1 tries: R indexed by x -> set(y), S indexed by y -> set(z), T indexed by x -> set(z)
    r_x: DefaultDict[int, Set[int]] = defaultdict(set)
    for x, y in r:
        r_x[x].add(y)
    s_y: DefaultDict[int, Set[int]] = defaultdict(set)
    for y, z in s:
        s_y[y].add(z)
    t_x: DefaultDict[int, Set[int]] = defaultdict(set)
    for z, x in t:
        t_x[x].add(z)

    out: Set[Triangle] = set()
    probes = 0

    def intersect_smallest(a: Set[int], b: Set[int]) -> List[int]:
        nonlocal probes
        small, big = (a, b) if len(a) <= len(b) else (b, a)
        res: List[int] = []
        for val in small:
            probes += 1
            if val in big:
                res.append(val)
        return res

    r_x_keys = set(r_x.keys())
    t_x_keys = set(t_x.keys())
    s_y_keys = set(s_y.keys())

    # Variable 1: x in R.x ^ T.x
    for x in intersect_smallest(r_x_keys, t_x_keys):
        # Variable 2: y in R[x] ^ S.y
        ys = intersect_smallest(r_x[x], s_y_keys)
        tz = t_x[x]
        for y in ys:
            # Variable 3: z in S[y] ^ T[x]
            for z in intersect_smallest(s_y[y], tz):
                out.add((x, y, z))

    # Generic Join materializes zero intermediate join tuples outside final outputs
    return out, JoinStats(len(out), 0, probes)


def free_join_triangle(
    r: List[Edge], s: List[Edge], t: List[Edge]
) -> Tuple[Set[Triangle], JoinStats]:
    """Free Join plan using generalized hash tries (Wang, Willsey & Suciu, SIGMOD 2023).

    Plan:
      Stage 1: Cover {x} from smaller of R.x, T.x; probe other trie on x.
      Stage 2: Dynamically choose cover for {y, z}:
        - if |R[x]| <= |T[x]|, iterate y in R[x] (probing S[y]) and then smallest-set intersect S[y] ^ T[x];
        - else iterate z in T[x] (probing S_rev[z]) and intersect S_rev[z] ^ R[x].
    On dense sub-tries this fuses multi-column probes like hash join; on skewed hubs
    it collapses to O(min(|R[x]|, |T[x]|)) probes like Generic Join.
    """
    r_x: DefaultDict[int, Set[int]] = defaultdict(set)
    for x, y in r:
        r_x[x].add(y)
    s_y: DefaultDict[int, Set[int]] = defaultdict(set)
    s_z: DefaultDict[int, Set[int]] = defaultdict(set)
    for y, z in s:
        s_y[y].add(z)
        s_z[z].add(y)
    t_x: DefaultDict[int, Set[int]] = defaultdict(set)
    for z, x in t:
        t_x[x].add(z)

    out: Set[Triangle] = set()
    probes = 0
    r_keys = set(r_x.keys())
    t_keys = set(t_x.keys())
    small_x, big_x = (r_keys, t_keys) if len(r_keys) <= len(t_keys) else (t_keys, r_keys)

    for x in small_x:
        probes += 1
        if x not in big_x:
            continue
        ry = r_x[x]
        tz = t_x[x]
        if len(ry) <= len(tz):
            for y in ry:
                probes += 1
                sz = s_y.get(y)
                if sz is None:
                    continue
                small, big = (sz, tz) if len(sz) <= len(tz) else (tz, sz)
                for z in small:
                    probes += 1
                    if z in big:
                        out.add((x, y, z))
        else:
            for z in tz:
                probes += 1
                sy = s_z.get(z)
                if sy is None:
                    continue
                small, big = (sy, ry) if len(sy) <= len(ry) else (ry, sy)
                for y in small:
                    probes += 1
                    if y in big:
                        out.add((x, y, z))

    return out, JoinStats(len(out), 0, probes)


def run_wcoj_probe() -> None:
    print("=== [1] WCOJ / Free Join vs. Binary Hash Join on Cyclic Triangle Queries ===")
    print("  1a. Adversarial hub-and-spoke skew graph (|R|=|S|=|T|=2m+1, exact |out|=3m+1):")
    prev_m = None
    prev_bin = None
    prev_gj = None
    for m in (32, 64, 128, 256):
        r, s, t = build_skew_triangle_instance(m)
        n_edges = len(r)
        agm = math.sqrt(len(r) * len(s) * len(t))
        res_rs, st_rs = binary_hash_join_triangle(r, s, t, "RS_T")
        res_st, st_st = binary_hash_join_triangle(r, s, t, "ST_R")
        res_tr, st_tr = binary_hash_join_triangle(r, s, t, "TR_S")
        res_gj, st_gj = generic_join_triangle(r, s, t)
        res_fj, st_fj = free_join_triangle(r, s, t)

        assert res_rs == res_st == res_tr == res_gj == res_fj
        assert len(res_gj) == 3 * m + 1
        # Every binary plan suffers quadratic intermediate blowup >= m^2
        assert st_rs.intermediate_tuples >= m * m
        assert st_st.intermediate_tuples >= m * m
        assert st_tr.intermediate_tuples >= m * m
        assert st_gj.intermediate_tuples == 0
        assert st_fj.intermediate_tuples == 0

        exp_str = ""
        if prev_m is not None:
            bin_exp = math.log2(st_rs.probe_steps / prev_bin)
            gj_exp = math.log2(st_gj.probe_steps / prev_gj)
            exp_str = f" | doubling exponent: bin={bin_exp:.2f}, gj={gj_exp:.2f}"
            assert bin_exp > 1.85, f"Expected ~2.0 binary exponent, got {bin_exp}"
            assert gj_exp < 1.15, f"Expected ~1.0 WCOJ skew exponent, got {gj_exp}"
        print(
            f"      m={m:3d} (N={n_edges:3d}, AGM={agm:7.1f}, |out|={len(res_gj):3d}): "
            f"BinJoin inter={st_rs.intermediate_tuples:6d} probes={st_rs.probe_steps:6d} | "
            f"GJ probes={st_gj.probe_steps:4d} | FJ probes={st_fj.probe_steps:4d}{exp_str}"
        )
        prev_m, prev_bin, prev_gj = m, st_rs.probe_steps, st_gj.probe_steps

    print("  1b. Dense directed clique K_v (N=v^2, |out|=v^3=N^{3/2}, AGM bound tight):")
    for v in (8, 16):
        r, s, t = build_dense_clique_instance(v)
        res_bin, st_bin = binary_hash_join_triangle(r, s, t, "RS_T")
        res_gj, st_gj = generic_join_triangle(r, s, t)
        res_fj, st_fj = free_join_triangle(r, s, t)
        agm = round(math.sqrt(len(r) * len(s) * len(t)))
        assert res_bin == res_gj == res_fj
        assert len(res_gj) == v**3 == agm
        print(
            f"      v={v:2d} (N={len(r):3d}, AGM={agm:4d}, |out|={len(res_gj):4d}): "
            f"BinJoin probes={st_bin.probe_steps:5d} | GJ probes={st_gj.probe_steps:5d} | FJ probes={st_fj.probe_steps:5d}"
        )

    # 1c. COLT (Column-Oriented Lazy Trie) vs eager full trie build on selective acyclic join
    # A(x, y) has 2000 rows over 200 distinct x; B(x, z, w) has 2000 rows over 200 distinct x;
    # Filter selects only x in {0, 1} (1% selectivity). Eager trie hashes all 2000 B rows into
    # nested (x -> z -> w) maps; COLT builds only top-level x buckets lazily and partitions z->w
    # ONLY for the 2 matched x keys!
    n_keys, per_key = 200, 10
    a_filtered = [(x, y) for x in (0, 1) for y in range(per_key)]
    b_rows = [(x, z, (x * 31 + z) % 7) for x in range(n_keys) for z in range(per_key)]

    eager_hash_inserts = 0
    eager_trie: DefaultDict[int, DefaultDict[int, List[int]]] = defaultdict(lambda: defaultdict(list))
    for x, z, w in b_rows:
        eager_trie[x][z].append(w)
        eager_hash_inserts += 2  # level-1 x insert + level-2 z insert

    # COLT lazy trie: store raw slice per x, only partition level-2 z->w when x is probed
    colt_buckets: DefaultDict[int, List[Tuple[int, int]]] = defaultdict(list)
    colt_hash_inserts = 0
    for x, z, w in b_rows:
        colt_buckets[x].append((z, w))
        colt_hash_inserts += 1  # level-1 x bucket only
    colt_level2_cache: Dict[int, Dict[int, List[int]]] = {}
    out_eager: Set[Tuple[int, int, int, int]] = set()
    out_colt: Set[Tuple[int, int, int, int]] = set()
    for x, y in a_filtered:
        for z, ws in eager_trie.get(x, {}).items():
            for w in ws:
                out_eager.add((x, y, z, w))
        if x in colt_buckets:
            if x not in colt_level2_cache:
                sub: DefaultDict[int, List[int]] = defaultdict(list)
                for z, w in colt_buckets[x]:
                    sub[z].append(w)
                    colt_hash_inserts += 1
                colt_level2_cache[x] = dict(sub)
            for z, ws in colt_level2_cache[x].items():
                for w in ws:
                    out_colt.add((x, y, z, w))
    assert out_eager == out_colt and len(out_colt) == 200
    assert len(colt_level2_cache) == 2 and colt_hash_inserts < eager_hash_inserts
    print(
        f"  1c. COLT lazy trie vs eager trie (200 keys, 1% selectivity): exact match (|out|={len(out_colt)}); "
        f"level-2 tries built={len(colt_level2_cache)}/{n_keys}, total hash inserts: COLT={colt_hash_inserts} vs eager={eager_hash_inserts}."
    )


# =============================================================================
# Part 2: DBSP Z-Set Algebra & 2D-Nested Incremental Recursive Transitive Closure
# =============================================================================

class ZSet:
    """Finitely supported map A -> Z (the free abelian group Z[A] in DBSP)."""

    __slots__ = ("_m",)

    def __init__(self, items: Iterable[Tuple[Hashable, int]] = ()) -> None:
        self._m: Dict[Hashable, int] = {}
        for k, w in items:
            if w:
                nw = self._m.get(k, 0) + w
                if nw == 0:
                    self._m.pop(k, None)
                else:
                    self._m[k] = nw

    def __getitem__(self, k: Hashable) -> int:
        return self._m.get(k, 0)

    def __len__(self) -> int:
        return len(self._m)

    def __bool__(self) -> bool:
        return bool(self._m)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, ZSet) and self._m == other._m

    def __repr__(self) -> str:
        return f"ZSet({sorted(self._m.items())!r})"

    def items(self):
        return self._m.items()

    def copy(self) -> ZSet:
        z = ZSet()
        z._m = dict(self._m)
        return z

    def __add__(self, other: ZSet) -> ZSet:
        res = self.copy()
        for k, w in other._m.items():
            nw = res._m.get(k, 0) + w
            if nw == 0:
                res._m.pop(k, None)
            else:
                res._m[k] = nw
        return res

    def __neg__(self) -> ZSet:
        z = ZSet()
        z._m = {k: -w for k, w in self._m.items()}
        return z

    def __sub__(self, other: ZSet) -> ZSet:
        return self + (-other)

    def distinct(self) -> ZSet:
        """Non-linear threshold projection: weight > 0 -> 1, weight <= 0 -> 0."""
        return ZSet((k, 1) for k, w in self._m.items() if w > 0)

    def support(self) -> Set[Hashable]:
        return {k for k, w in self._m.items() if w > 0}


def zset_compose_edges(left: ZSet, right: ZSet) -> Tuple[ZSet, int]:
    """Bilinear relational composition: (x, y) in left, (y, z) in right -> (x, z) with w1*w2."""
    right_by_y: DefaultDict[Hashable, List[Tuple[Hashable, int]]] = defaultdict(list)
    for (y, z), w2 in right.items():
        right_by_y[y].append((z, w2))
    acc: DefaultDict[Tuple[Hashable, Hashable], int] = defaultdict(int)
    ops = 0
    for (x, y), w1 in left.items():
        for z, w2 in right_by_y.get(y, ()):
            acc[(x, z)] += w1 * w2
            ops += 1
    return ZSet(acc.items()), ops


def stream_integrate(deltas: List[ZSet]) -> List[ZSet]:
    """DBSP integration operator I: I(s)[t] = sum_{i=0..t} s[i]."""
    acc = ZSet()
    out: List[ZSet] = []
    for d in deltas:
        acc = acc + d
        out.append(acc.copy())
    return out


def stream_differentiate(snapshots: List[ZSet]) -> List[ZSet]:
    """DBSP differentiation operator D: D(s)[t] = s[t] - z^{-1}(s)[t]."""
    prev = ZSet()
    out: List[ZSet] = []
    for s in snapshots:
        out.append(s - prev)
        prev = s
    return out


def incremental_distinct_step(prev_integral: ZSet, delta: ZSet) -> ZSet:
    """Exact DBSP incremental distinct (cf. Feldera crates/dbsp/src/operator/dynamic/distinct.rs).

    Emits +1 when old_weight <= 0 and new_weight > 0;
          -1 when old_weight > 0 and new_weight <= 0;
           0 otherwise.
    Touches ONLY keys present in `delta`.
    """
    out_items: List[Tuple[Hashable, int]] = []
    for k, dw in delta.items():
        old_w = prev_integral[k]
        new_w = old_w + dw
        old_bit = 1 if old_w > 0 else 0
        new_bit = 1 if new_w > 0 else 0
        diff = new_bit - old_bit
        if diff:
            out_items.append((k, diff))
    return ZSet(out_items)


def tc_from_scratch(edges: ZSet) -> Tuple[ZSet, int]:
    """Reference from-scratch Kleene least fixpoint for Transitive Closure over ZSet edges."""
    e_pos = edges.distinct()
    tc = e_pos.copy()
    ops = 0
    while True:
        step_join, jops = zset_compose_edges(tc, e_pos)
        ops += jops
        nxt = (e_pos + step_join).distinct()
        if nxt == tc:
            return tc, ops
        tc = nxt


class DBSPIncrementalTC:
    """DBSP 2D-nested incremental Transitive Closure circuit (Budiu et al., PVLDB 2023).

    Outer stream time t tracks input graph mutations dE_t.
    Inner iteration time i tracks fixpoint approximation steps:
      R(t, i) = distinct( E(t) + (z_i^{-1}(R)(t, i) o E(t)) )
    By lifting Q^Delta into the nested stream (stream of streams), each outer step t
    maintains per-iteration integrals across outer time t:
      - E_prev: E(t-1), dE: E(t) - E(t-1) (applied to distinct positive edges e_pos)
      - R_prev[i]: R(t-1, i) (inner-step distinct reachability at previous outer tick)
      - P_prev[i]: pre-distinct multiset P(t-1, i) = E(t-1) + R(t-1, i-1) o E(t-1)
    At outer tick t, given only dE_t, we propagate 2D deltas:
      dP(t, i) = dE_pos(t) + (dR(t, i-1) o dE_pos(t))
                           + (R_prev[i-1] o dE_pos(t))
                           + (dR(t, i-1) o E_prev)
      dR(t, i) = distinct^Delta(P_prev[i], dP(t, i))
    Wait: since R(t, i) stabilizes at finite i_max(t), summing inner differences or
    taking the stabilized iteration delta yields exact outer Delta TC(t) = TC(t) - TC(t-1)
    under BOTH insertions AND deletions (including cycle deletions and diamond rederivations)!
    """

    def __init__(self) -> None:
        self.raw_edges_integral = ZSet()
        self.pos_edges_integral = ZSet()
        # Per-inner-iteration history from outer tick t-1:
        # P_prev[i] = pre-distinct multiset at iteration i for tick t-1
        # R_prev[i] = distinct TC approximation at iteration i for tick t-1
        self.p_prev: List[ZSet] = []
        self.r_prev: List[ZSet] = []
        self.tc_prev = ZSet()

    def step(self, raw_edge_delta: ZSet) -> Tuple[ZSet, int]:
        # Step 0: incremental distinct on input edge multiset
        de_pos = incremental_distinct_step(self.raw_edges_integral, raw_edge_delta)
        self.raw_edges_integral = self.raw_edges_integral + raw_edge_delta
        if not de_pos:
            return ZSet(), 0

        e_prev = self.pos_edges_integral
        e_curr = e_prev + de_pos
        ops = 0

        # Ensure iteration history covers stabilized prefix
        new_p_prev: List[ZSet] = []
        new_r_prev: List[ZSet] = []

        # Base case i = 0: P(t, 0) = E(t), R(t, 0) = distinct(E(t)) = E_pos(t)
        p0_prev = self.p_prev[0] if self.p_prev else ZSet()
        r0_prev = self.r_prev[0] if self.r_prev else ZSet()
        dp = de_pos
        dr = incremental_distinct_step(p0_prev, dp)
        p_curr = p0_prev + dp
        r_curr = r0_prev + dr
        new_p_prev.append(p_curr)
        new_r_prev.append(r_curr)

        # Iterative inner loop i = 1, 2, ... until BOTH:
        #   (a) outer delta dr has settled beyond previous history AND
        #   (b) current outer tick's inner approximation has reached fixpoint (r_curr == r_prev_iter)
        i = 1
        prev_r_iter_curr = r_curr
        max_old_iters = len(self.r_prev)
        while True:
            # Retrieve R(t-1, i-1), P(t-1, i), R(t-1, i); beyond previous stabilization,
            # the sequence at tick t-1 is constant equal to its fixpoint!
            r_tprev_im1 = self.r_prev[i - 1] if (i - 1) < max_old_iters else self.tc_prev
            p_tprev_i = self.p_prev[i] if i < max_old_iters else (self.p_prev[-1] if self.p_prev else ZSet())
            r_tprev_i = self.r_prev[i] if i < max_old_iters else self.tc_prev

            # Bilinear incremental join formula (DBSP Theorem 3.7):
            # Delta(R_{i-1} o E) = (dR_{i-1} o dE) + (R_{t-1, i-1} o dE) + (dR_{i-1} o E_{t-1})
            j1, o1 = zset_compose_edges(dr, de_pos)
            j2, o2 = zset_compose_edges(r_tprev_im1, de_pos)
            j3, o3 = zset_compose_edges(dr, e_prev)
            ops += o1 + o2 + o3

            dp = de_pos + j1 + j2 + j3
            dr = incremental_distinct_step(p_tprev_i, dp)

            p_curr = p_tprev_i + dp
            r_curr = r_tprev_i + dr
            new_p_prev.append(p_curr)
            new_r_prev.append(r_curr)

            # Inner fixpoint reached when current tick stops changing AND we have processed
            # at least as many iterations as previous tick needed (so retractions finish propagating).
            if r_curr == prev_r_iter_curr and i >= max_old_iters:
                break
            prev_r_iter_curr = r_curr
            i += 1
            if i > 128:
                raise RuntimeError("DBSP inner iteration bound exceeded")

        delta_tc = r_curr - self.tc_prev
        self.pos_edges_integral = e_curr
        self.p_prev = new_p_prev
        self.r_prev = new_r_prev
        self.tc_prev = r_curr
        return delta_tc, ops


def run_dbsp_probe() -> None:
    print("\n=== [2] DBSP Z-Set Algebra & Incremental Recursive Transitive Closure ===")
    # 2a. Verify I o D = id and D o I = id plus bilinear join theorem
    rng = random.Random(20261119)
    delta_a = [
        ZSet([((0, 1), 1), ((1, 2), 2)]),
        ZSet([((1, 2), -1), ((2, 3), 1)]),
        ZSet([((0, 1), -1), ((0, 2), 1)]),
        ZSet([((2, 3), -1), ((1, 2), -1)]),
    ]
    delta_b = [
        ZSet([((1, 10), 1), ((2, 20), 1)]),
        ZSet([((2, 20), 1), ((3, 30), 1)]),
        ZSet([((1, 10), -1), ((2, 20), -2)]),
        ZSet([((3, 30), -1), ((2, 99), 1)]),
    ]
    assert stream_differentiate(stream_integrate(delta_a)) == delta_a
    assert stream_integrate(stream_differentiate(stream_integrate(delta_a))) == stream_integrate(delta_a)

    # Bilinear join incrementalization check: (A o B)^Delta == D(I(A) o I(B))
    ia = stream_integrate(delta_a)
    ib = stream_integrate(delta_b)
    ref_join_snaps = [zset_compose_edges(a, b)[0] for a, b in zip(ia, ib)]
    ref_join_deltas = stream_differentiate(ref_join_snaps)
    inc_join_deltas: List[ZSet] = []
    prev_a, prev_b = ZSet(), ZSet()
    for da, db in zip(delta_a, delta_b):
        j1, _ = zset_compose_edges(da, db)
        j2, _ = zset_compose_edges(prev_a, db)
        j3, _ = zset_compose_edges(da, prev_b)
        inc_join_deltas.append(j1 + j2 + j3)
        prev_a = prev_a + da
        prev_b = prev_b + db
    assert inc_join_deltas == ref_join_deltas
    print("  2a. Verified I(D(s))=s, D(I(s))=s, and exact bilinear join Q^Delta = D(Q(I(.))) over 4 ticks.")

    # 2b. Adversarial + randomized recursive Transitive Closure stream (insertions, duplicates, diamonds, cycle breaks)
    scripted_deltas: List[Tuple[str, ZSet]] = [
        ("build 3-cycle + diamond", ZSet([((0, 1), 1), ((1, 2), 1), ((2, 0), 1), ((0, 3), 1), ((3, 4), 1), ((0, 5), 1), ((5, 4), 1)])),
        ("insert duplicate edge (0,3) weight +1 (total 2)", ZSet([((0, 3), 1)])),
        ("delete one diamond branch (0,5) -> (0,4) persists", ZSet([((0, 5), -1)])),
        ("decrement (0,3) from 2->1 -> (0,4) still persists", ZSet([((0, 3), -1)])),
        ("delete remaining (0,3) 1->0 -> (0,4) retracts", ZSet([((0, 3), -1)])),
        ("break cycle edge (2,0) -> retract cyclic reachability", ZSet([((2, 0), -1)])),
        ("re-close cycle via (2,1) + add tail (4,6)", ZSet([((2, 1), 1), ((4, 6), 1)])),
        ("bridge (2,3) restoring (0,4),(0,6) via cycle", ZSet([((2, 3), 1)])),
        ("delete (1,2) severing bridge and cycle simultaneously", ZSet([((1, 2), -1)])),
        ("re-insert (0,1) duplicate and clear (4,6)", ZSet([((0, 1), 1), ((4, 6), -1)])),
    ]

    # Add 30 deterministic pseudo-random edge insertion/deletion steps over 10 nodes
    active_counts: DefaultDict[Edge, int] = defaultdict(int)
    for _, z in scripted_deltas:
        for e, w in z.items():
            active_counts[e] += w

    random_deltas: List[Tuple[str, ZSet]] = []
    for step_idx in range(30):
        batch: List[Tuple[Edge, int]] = []
        for _ in range(rng.randint(1, 3)):
            u, v = rng.randrange(10), rng.randrange(10)
            if active_counts[(u, v)] > 0 and rng.random() < 0.5:
                w = -1
            else:
                w = 1
            active_counts[(u, v)] += w
            batch.append(((u, v), w))
        random_deltas.append((f"rand_tick_{step_idx}", ZSet(batch)))

    all_steps = scripted_deltas + random_deltas
    engine = DBSPIncrementalTC()
    running_edges = ZSet()
    running_tc_from_deltas = ZSet()
    ref_tc_snaps: List[ZSet] = []
    inc_tc_deltas: List[ZSet] = []
    total_inc_ops = 0
    total_ref_ops = 0

    for idx, (label, d_edge) in enumerate(all_steps):
        running_edges = running_edges + d_edge
        d_tc, inc_ops = engine.step(d_edge)
        ref_tc, ref_ops = tc_from_scratch(running_edges)
        running_tc_from_deltas = running_tc_from_deltas + d_tc
        inc_tc_deltas.append(d_tc)
        ref_tc_snaps.append(ref_tc)
        total_inc_ops += inc_ops
        total_ref_ops += ref_ops

        # Fundamental DBSP invariant: I(TC^Delta(dE))[t] == TC(I(dE)[t])
        assert running_tc_from_deltas == ref_tc, f"Mismatch at tick {idx} ({label})"
        if idx < len(scripted_deltas):
            pos_changes = sum(1 for _, w in d_tc.items() if w > 0)
            neg_changes = sum(1 for _, w in d_tc.items() if w < 0)
            print(
                f"      tick {idx:2d} [{label:52s}]: |TC|={len(ref_tc):2d}, "
                f"dTC=(+{pos_changes}, -{neg_changes}), inc_ops={inc_ops:3d} vs scratch_ops={ref_ops:3d}"
            )

    assert inc_tc_deltas == stream_differentiate(ref_tc_snaps)
    print(
        f"  2b. Verified exact DBSP equivalence I(TC^Delta(dE)) == TC(I(dE)) & TC^Delta == D(TC(I(.))) "
        f"across all {len(all_steps)} ticks (10 adversarial + 30 random; "
        f"total join ops: inc={total_inc_ops} vs scratch={total_ref_ops})."
    )

    # 2c. Localized sparse-graph workload (12 disconnected 6-node chains = 72 nodes, 60 edges):
    # Contrast single-edge localized update cost against full recomputation.
    sparse_init = []
    for comp in range(12):
        base = comp * 6
        for j in range(5):
            sparse_init.append(((base + j, base + j + 1), 1))
    sparse_engine = DBSPIncrementalTC()
    sparse_edges = ZSet(sparse_init)
    _, _ = sparse_engine.step(sparse_edges)
    sparse_ref0, _ = tc_from_scratch(sparse_edges)
    assert sparse_engine.tc_prev == sparse_ref0

    localized_mutations = [
        ZSet([((0, 5), 1)]),    # shortcut in component 0 only
        ZSet([((0, 5), -1)]),   # retract shortcut in component 0 only
        ZSet([((2, 3), -1)]),   # split chain in component 0 only
        ZSet([((2, 3), 1)]),    # restore chain in component 0 only
    ]
    loc_inc_total = 0
    loc_ref_total = 0
    for mut in localized_mutations:
        sparse_edges = sparse_edges + mut
        d_tc, iops = sparse_engine.step(mut)
        ref_tc, rops = tc_from_scratch(sparse_edges)
        assert sparse_engine.tc_prev == ref_tc
        loc_inc_total += iops
        loc_ref_total += rops
    assert loc_inc_total * 5 < loc_ref_total
    print(
        f"  2c. Localized sparse updates (12 components x 6 nodes, 4 single-edge mutations): "
        f"exact match on all ticks; join ops: DBSP={loc_inc_total} vs scratch={loc_ref_total} "
        f"({loc_ref_total / loc_inc_total:.1f}x reduction)."
    )


# =============================================================================
# Part 3: Finite-Height Lattice Semi-Naive vs. Infinite-Height Divergence & Widening
# =============================================================================

# Constant Propagation Lattice (height 2):
#   BOT < Const(c) < TOP
BOT = ("BOT",)
TOP = ("TOP",)


def cp_const(c: int) -> Tuple[str, int]:
    return ("C", c)


def cp_join(a: Tuple, b: Tuple) -> Tuple:
    if a == BOT:
        return b
    if b == BOT:
        return a
    if a == b:
        return a
    return TOP


def cp_add(a: Tuple, b: Tuple) -> Tuple:
    if a == BOT or b == BOT:
        return BOT
    if a == TOP or b == TOP:
        return TOP
    return cp_const(a[1] + b[1])


def solve_const_prop_naive(
    assigns: List[Tuple[str, int]],
    adds: List[Tuple[str, str, str]],
    copies: List[Tuple[str, str]],
) -> Tuple[Dict[str, Tuple], int]:
    """Naive Kleene iteration over the Constant Propagation join-semilattice."""
    env: Dict[str, Tuple] = {}
    evals = 0
    for var, c in assigns:
        env[var] = cp_join(env.get(var, BOT), cp_const(c))
    while True:
        changed = False
        nxt = dict(env)
        for dst, src in copies:
            evals += 1
            v = env.get(src, BOT)
            if v != BOT:
                joined = cp_join(nxt.get(dst, BOT), v)
                if joined != nxt.get(dst, BOT):
                    nxt[dst] = joined
                    changed = True
        for dst, x, y in adds:
            evals += 1
            vx, vy = env.get(x, BOT), env.get(y, BOT)
            if vx != BOT and vy != BOT:
                joined = cp_join(nxt.get(dst, BOT), cp_add(vx, vy))
                if joined != nxt.get(dst, BOT):
                    nxt[dst] = joined
                    changed = True
        env = nxt
        if not changed:
            return env, evals


def solve_const_prop_seminaive(
    assigns: List[Tuple[str, int]],
    adds: List[Tuple[str, str, str]],
    copies: List[Tuple[str, str]],
) -> Tuple[Dict[str, Tuple], int]:
    """Semi-naive lattice fixpoint (Flix PLDI 2016 / Ascent CC 2022) tracking Delta lattice updates."""
    total: Dict[str, Tuple] = {}
    delta: Dict[str, Tuple] = {}
    evals = 0

    for var, c in assigns:
        joined = cp_join(total.get(var, BOT), cp_const(c))
        if joined != total.get(var, BOT):
            total[var] = joined
            delta[var] = joined

    copies_by_src: DefaultDict[str, List[str]] = defaultdict(list)
    for dst, src in copies:
        copies_by_src[src].append(dst)
    adds_by_arg: DefaultDict[str, List[Tuple[str, str, str]]] = defaultdict(list)
    for rule in adds:
        dst, x, y = rule
        adds_by_arg[x].append(rule)
        if y != x:
            adds_by_arg[y].append(rule)

    while delta:
        new_delta: Dict[str, Tuple] = {}
        for src, v in delta.items():
            for dst in copies_by_src.get(src, ()):
                evals += 1
                cur = total.get(dst, BOT)
                cand = cp_join(cur, v)
                if cand != cur:
                    new_delta[dst] = cp_join(new_delta.get(dst, BOT), cand)
            for dst, x, y in adds_by_arg.get(src, ()):
                evals += 1
                vx, vy = total.get(x, BOT), total.get(y, BOT)
                if vx != BOT and vy != BOT:
                    cur = total.get(dst, BOT)
                    cand = cp_join(cur, cp_add(vx, vy))
                    if cand != cur:
                        new_delta[dst] = cp_join(new_delta.get(dst, BOT), cand)
        for k, v in new_delta.items():
            total[k] = cp_join(total.get(k, BOT), v)
        delta = new_delta

    return total, evals


def run_lattice_and_negation_probe() -> None:
    print("\n=== [3] Lattice Semi-Naive Convergence, Infinite-Height Divergence, Negation & Impure FFI ===")

    # 3a. Finite-height Constant Propagation lattice: naive vs semi-naive equivalence & work savings
    # Program: x=2; y=3; z=x+y (5); w=z; w=7 -> w becomes TOP; chain u0=w -> u1 -> ... -> u15; side chain c0=1 -> ... -> c15
    assigns = [("x", 2), ("y", 3), ("w", 7), ("c0", 1)]
    adds = [("z", "x", "y")]
    copies = [("w", "z"), ("u0", "w")]
    copies += [(f"u{i+1}", f"u{i}") for i in range(15)]
    copies += [(f"c{i+1}", f"c{i}") for i in range(15)]

    res_naive, evals_naive = solve_const_prop_naive(assigns, adds, copies)
    res_sn, evals_sn = solve_const_prop_seminaive(assigns, adds, copies)
    assert res_naive == res_sn
    assert res_sn["z"] == cp_const(5)
    assert res_sn["w"] == TOP
    assert res_sn["u15"] == TOP
    assert res_sn["c15"] == cp_const(1)
    assert evals_sn < evals_naive
    print(
        f"  3a. Constant-propagation lattice (height 2): naive==semi-naive verified "
        f"(z={res_sn['z']}, w={res_sn['w']}, u15={res_sn['u15']}, c15={res_sn['c15']}); "
        f"rule evaluations: semi-naive={evals_sn} vs naive={evals_naive}."
    )

    # 3b. Infinite-height lattice (unbounded BigInt with max, mirroring Flix JoinLattice[BigInt]):
    # Rule: A(0; 0). A(0; v + 1) :- A(0; v).
    # Without widening: diverges indefinitely; with Cousot-Cousot widening threshold -> +inf: converges in 2 steps.
    cap = 50
    val = 0
    steps_no_widen = 0
    while steps_no_widen < cap:
        nxt = max(val, val + 1)
        if nxt == val:
            break
        val = nxt
        steps_no_widen += 1
    assert steps_no_widen == cap and val == cap  # failed to reach fixpoint!

    INF = math.inf
    def widen(old_v: float, new_v: float, threshold: int = 8) -> float:
        return INF if new_v > old_v and new_v > threshold else max(old_v, new_v)

    w_val: float = 0
    steps_widen = 0
    while True:
        cand = w_val + 1 if math.isfinite(w_val) else INF
        nxt_w = widen(w_val, cand, threshold=8)
        steps_widen += 1
        if nxt_w == w_val:
            break
        w_val = nxt_w
    assert w_val == INF and steps_widen == 10
    print(
        f"  3b. Infinite-height BigInt lattice: without widening hit cap={cap} (v={val}, non-terminating); "
        f"with threshold widening converged to {w_val} in {steps_widen} iterations."
    )

    # 3c. Unstratified negation: SCC stratifier + odd-cycle oscillation + even-cycle non-uniqueness + WFS
    def check_stratifiable(edges: List[Tuple[str, str, bool]]) -> Tuple[bool, List[Tuple[str, str]]]:
        """Tarjan SCC + check for any negative edge (is_neg=True) inside an SCC."""
        nodes: Set[str] = set()
        adj: DefaultDict[str, List[str]] = defaultdict(list)
        for u, v, _ in edges:
            nodes.add(u)
            nodes.add(v)
            adj[u].append(v)

        index_counter = 0
        indices: Dict[str, int] = {}
        lowlink: Dict[str, int] = {}
        stack: List[str] = []
        on_stack: Set[str] = set()
        scc_id: Dict[str, int] = {}
        scc_count = 0

        def strongconnect(v: str) -> None:
            nonlocal index_counter, scc_count
            indices[v] = lowlink[v] = index_counter
            index_counter += 1
            stack.append(v)
            on_stack.add(v)
            for w in adj[v]:
                if w not in indices:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], indices[w])
            if lowlink[v] == indices[v]:
                while True:
                    w = stack.pop()
                    on_stack.remove(w)
                    scc_id[w] = scc_count
                    if w == v:
                        break
                scc_count += 1

        for n in sorted(nodes):
            if n not in indices:
                strongconnect(n)

        bad_edges = [(u, v) for u, v, is_neg in edges if is_neg and scc_id[u] == scc_id[v]]
        return (len(bad_edges) == 0), bad_edges

    # Odd negative cycle: p :- not p
    ok_odd, bad_odd = check_stratifiable([("p", "p", True)])
    assert not ok_odd and bad_odd == [("p", "p")]
    # Immediate-consequence operator T_P oscillates: 0 -> 1 -> 0 -> 1 ...
    tp_seq = []
    state = False
    for _ in range(6):
        tp_seq.append(state)
        state = not state
    assert tp_seq == [False, True, False, True, False, True]
    # Verify NO 2-valued stable model exists (neither p=False nor p=True satisfies Gelfond-Lifschitz reduct)
    stable_odd = [m for m in (False, True) if (not m) == m]
    assert stable_odd == []

    # Even negative cycle: a :- not b. b :- not a.
    ok_even, bad_even = check_stratifiable([("a", "b", True), ("b", "a", True)])
    assert not ok_even and len(bad_even) == 2
    # Check 2-valued stable models: both (a=True, b=False) and (a=False, b=True) are distinct minimal stable models!
    stable_even = [(a, b) for a in (False, True) for b in (False, True) if a == (not b) and b == (not a)]
    assert stable_even == [(False, True), (True, False)]

    # 3-valued Well-Founded Semantics (alternating fixpoint: U_0 = empty, O_0 = all,
    # U_{k+1} = lfp(T_{P/O_k}), O_{k+1} = lfp(T_{P/U_k}) -> UNKNOWN = O_inf \ U_inf)
    # For odd cycle p :- not p: U_0={}, O_0={p} => U_1={}, O_1={p} => WFS(p) = UNKNOWN
    # For even cycle a :- not b; b :- not a: U_0={}, O_0={a,b} => U_1={}, O_1={a,b} => WFS(a)=WFS(b)=UNKNOWN
    wfs_u, wfs_o = set(), {"a", "b"}
    for _ in range(4):
        next_u = ({ "a" } if "b" not in wfs_o else set()) | ({ "b" } if "a" not in wfs_o else set())
        next_o = ({ "a" } if "b" not in wfs_u else set()) | ({ "b" } if "a" not in wfs_u else set())
        wfs_u, wfs_o = next_u, next_o
    assert wfs_u == set() and wfs_o == {"a", "b"}  # Both UNKNOWN under WFS

    # Stratified program: reach(x) -> unreachable(x) :- node(x), not reach(x)
    ok_strat, bad_strat = check_stratifiable([("reach", "reach", False), ("unreachable", "reach", True)])
    assert ok_strat and bad_strat == []
    print(
        f"  3c. Stratification & non-monotone negation: odd cycle rejected ({bad_odd}, T_P oscillates {tp_seq[:4]}, "
        f"0 stable models); even cycle rejected ({len(bad_even)} cyclic neg edges, {len(stable_even)} stable models, "
        f"WFS assigns UNKNOWN to {sorted(wfs_o - wfs_u)}); stratified reach/unreachable accepted."
    )

    # 3d. Host FFI violation: non-monotone user callback breaks semi-naive vs naive equivalence!
    # Lattice: Int with max (0 < 1 < 2).
    # Rule 1: A(0; 1).  Rule 2: A(0; 2) :- Trigger(0).  Rule 3: Out(0; f(v)) :- A(0; v).
    # If f is NON-MONOTONE: f(1) = 10, f(2) = 5 (decreasing!).
    # Under naive evaluation starting from A(0;1), Trigger(0) fired in same step:
    #   Schedule 1 (batch all EDB first -> A(0;2) before f fires): Out(0) = f(2) = 5.
    #   Schedule 2 (semi-naive fires f(1)=10 on step 1, then f(2)=5 on step 2, joined with max): Out(0) = max(10, 5) = 10!
    def bad_nonmonotone_ffi(v: int) -> int:
        return 10 if v == 1 else 5

    # Schedule 1: A converges to 2 before Out evaluates
    out_sched1 = bad_nonmonotone_ffi(max(1, 2))
    # Schedule 2: semi-naive evaluates Out on intermediate A=1, then joins with Out on A=2
    out_sched2 = max(bad_nonmonotone_ffi(1), bad_nonmonotone_ffi(2))
    assert out_sched1 == 5 and out_sched2 == 10 and out_sched1 != out_sched2
    print(
        f"  3d. Host FFI monotonicity violation: non-monotone callback f(1)=10, f(2)=5 produces "
        f"schedule-dependent lattice results (batched={out_sched1} vs incremental-join={out_sched2})."
    )


def main() -> int:
    run_wcoj_probe()
    run_dbsp_probe()
    run_lattice_and_negation_probe()
    print("\nALL PROBE ASSERTIONS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
