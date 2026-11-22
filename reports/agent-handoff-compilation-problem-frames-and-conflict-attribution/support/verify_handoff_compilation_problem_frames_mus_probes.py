#!/usr/bin/env python3
"""Standalone Python 3.10+ stdlib verification suite for multi-stage handoff
compilation, WRSPM/KAOS problem-frame obligations, QuickXplain preferred
conflicts and relaxations, and MARCO/WMaxSAT minimal-conflict attribution.

All four probes use strictly the Python 3.10+ standard library, fixed
instance-scoped PRNG seeds, zero disk writes, zero network calls, zero local
filesystem paths in stdout, and explicit evidence-role banners aligned with
the reference-corpus/1 contract:
  1. probe_quickxplain_and_junker_duality
  2. probe_marco_duality_and_wmaxsat_shadow_prices
  3. probe_wrspm_obligations_and_kaos_refinement
  4. probe_metagpt_fill_defects_and_declarative_gsm
"""

from __future__ import annotations

import ast
import collections
import hashlib
import itertools
import json
import math
import random
import re
import types
import typing
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Iterable, Sequence


# =============================================================================
# PROBE 1: QuickXplain (Junker, AAAI 2004, pp. 167-172: Fig. 1, Defs. 3 & 6,
#          Propositions 3 & 4, Theorem 1, and Table 4)
# [evidence_role: normative + derived]
# =============================================================================


class CountingConsistencyOracle:
    """Monotone consistency oracle counting exact invocations."""

    def __init__(self, predicate: Callable[[frozenset[int]], bool]) -> None:
        self._predicate = predicate
        self.calls = 0

    def is_consistent(self, constraints: Iterable[int]) -> bool:
        self.calls += 1
        return self._predicate(frozenset(constraints))


def quickxplain(
    background: Sequence[int],
    soft_constraints: Sequence[int],
    oracle: CountingConsistencyOracle,
    split_fn: Callable[[int], int] = lambda m: m // 2,
) -> list[int] | None:
    """Exact transcription of QUICKXPLAIN(B, C, <) (Junker, AAAI 2004, Fig. 1, p. 169).

    Lines 1-3 implement QUICKXPLAIN(B, C, <); lines 4-11 implement recursive
    QUICKXPLAIN'(B, Delta, C, <). Line 3 passes Delta = B into the root
    recursive call, triggering one root consistency check on B at Line 4
    whenever B is non-empty.
    """
    b_list = list(background)
    c_list = list(soft_constraints)
    # Line 1: if isConsistent(B U C) then return 'no conflict'
    if oracle.is_consistent(b_list + c_list):
        return None
    # Line 2: else if C = empty then return empty
    if not c_list:
        return []

    def qx_prime(b_cur: list[int], delta: list[int], c_cur: list[int]) -> list[int]:
        # Line 4: if Delta != empty and not isConsistent(B) then return empty
        if delta and not oracle.is_consistent(b_cur):
            return []
        # Line 5: if C = {alpha} then return {alpha}
        if len(c_cur) == 1:
            return [c_cur[0]]
        # Lines 6-8: split C = [alpha_1..alpha_n] into C_1 = [1..k], C_2 = [k+1..n]
        k_split = split_fn(len(c_cur))
        if not (1 <= k_split < len(c_cur)):
            raise ValueError(f"Invalid split index {k_split} for len={len(c_cur)}")
        c1, c2 = c_cur[:k_split], c_cur[k_split:]
        # Line 9: Delta_2 := QUICKXPLAIN'(B U C_1, C_1, C_2, <)
        delta2 = qx_prime(b_cur + c1, c1, c2)
        # Line 10: Delta_1 := QUICKXPLAIN'(B U Delta_2, Delta_2, C_1, <)
        delta1 = qx_prime(b_cur + delta2, delta2, c1)
        # Line 11: return Delta_1 U Delta_2
        return delta1 + delta2

    # Line 3: return QUICKXPLAIN'(B, B, C, <)
    return qx_prime(b_list, b_list, c_list)


def is_lex_smaller(x: frozenset[int], y: frozenset[int], order: Sequence[int]) -> bool:
    """Definition 3 of Junker (AAAI 2004, p. 168): lexicographic order <_lex.

    X <_lex Y iff at the highest-priority element c_k in order where X and Y
    differ, c_k in X \\ Y (so relaxation X retains higher-priority c_k than Y).
    """
    for elem in order:
        if (elem in x) != (elem in y):
            return elem in x and elem not in y
    return False


def is_antilex_smaller(x: frozenset[int], y: frozenset[int], order: Sequence[int]) -> bool:
    """Definition 6 of Junker (AAAI 2004, p. 168): anti-lexicographic order <_antilex.

    X <_antilex Y iff at the lowest-priority element c_k in order where X and Y
    differ, c_k in Y \\ X (so conflict X avoids lower-priority elements relative to Y).
    """
    for elem in reversed(order):
        if (elem in x) != (elem in y):
            return elem in y and elem not in x
    return False


def _min_in_order(subset: frozenset[int], order: Sequence[int]) -> int:
    for elem in order:
        if elem in subset:
            return elem
    raise ValueError("Empty subset has no minimum in order")


def _max_in_order(subset: frozenset[int], order: Sequence[int]) -> int:
    for elem in reversed(order):
        if elem in subset:
            return elem
    raise ValueError("Empty subset has no maximum in order")


def enumerate_minimal_conflicts_bruteforce(
    background: Sequence[int],
    universe: Sequence[int],
    pred: Callable[[frozenset[int]], bool],
) -> set[frozenset[int]]:
    """Brute-force enumeration of all minimal conflicts (MUSes) of (B, C)."""
    b_set = frozenset(background)
    unsat_sets: list[frozenset[int]] = []
    u_list = list(universe)
    for r in range(len(u_list) + 1):
        for comb in itertools.combinations(u_list, r):
            cand = frozenset(comb)
            if not pred(b_set | cand):
                if not any(prev < cand for prev in unsat_sets):
                    unsat_sets.append(cand)
    return set(unsat_sets)


def enumerate_maximal_relaxations_bruteforce(
    background: Sequence[int],
    universe: Sequence[int],
    pred: Callable[[frozenset[int]], bool],
) -> set[frozenset[int]]:
    """Brute-force enumeration of all maximal relaxations (MSSes) of (B, C)."""
    b_set = frozenset(background)
    sat_sets: list[frozenset[int]] = []
    u_list = list(universe)
    for r in range(len(u_list), -1, -1):
        for comb in itertools.combinations(u_list, r):
            cand = frozenset(comb)
            if pred(b_set | cand):
                if not any(cand < prev for prev in sat_sets):
                    sat_sets.append(cand)
    return set(sat_sets)


def _verify_primal_and_dual_junker_props(
    background: Sequence[int],
    perm: Sequence[int],
    primal_pred: Callable[[frozenset[int]], bool],
    all_muses: set[frozenset[int]],
    all_msses: set[frozenset[int]],
) -> None:
    """Verify Theorem 1 (<_antilex MUS), Proposition 3 (dual <_lex MSS), and Proposition 4."""
    b_set = frozenset(background)
    c_all = frozenset(perm)

    # Primal QuickXplain: unique <_antilex-minimum MUS X*
    primal_oracle = CountingConsistencyOracle(primal_pred)
    qx_mus = frozenset(quickxplain(background, perm, primal_oracle) or [])
    assert qx_mus in all_muses
    assert all(is_antilex_smaller(qx_mus, other, perm) for other in all_muses if other != qx_mus)

    # Junker (AAAI 2004, p. 168) Proposition 3:
    # A subset S' of C is consistent in the negated dual problem iff B U (C \ S')
    # is INCONSISTENT in the primal problem. Running QuickXplain on the reversed
    # priority order <' = reversed(perm) isolates the preferred MCS Y* = C \ R*,
    # whose complement R* = C \ Y* is the unique <_lex-minimum relaxation (MSS)!
    dual_pred: Callable[[frozenset[int]], bool] = lambda s_neg: not primal_pred(
        b_set | (c_all - s_neg)
    )
    dual_oracle = CountingConsistencyOracle(dual_pred)
    dual_mcs = frozenset(quickxplain([], list(reversed(perm)), dual_oracle) or [])
    pref_mss = c_all - dual_mcs
    assert pref_mss in all_msses
    assert all(is_lex_smaller(pref_mss, other_r, perm) for other_r in all_msses if other_r != pref_mss)

    # Junker (AAAI 2004, p. 168) Proposition 4:
    # On the same prioritized problem (B, C, <), min_<(C \ R*) == max_<(X*).
    assert _min_in_order(c_all - pref_mss, perm) == _max_in_order(qx_mus, perm)


def probe_quickxplain_and_junker_duality() -> dict[str, Any]:
    # 1A. Tight best-case and worst-case query counts (Junker Table 4, p. 170)
    # across n in {64, 256} and k in {1, 2, 4, 8}
    complexity_rows: list[dict[str, int]] = []
    for n in (64, 256):
        c_seq = list(range(1, n + 1))
        for k in (1, 2, 4, 8):
            block = n // k
            best_target = frozenset(range(1, k + 1))
            worst_target = frozenset((i + 1) * block for i in range(k))

            best_pred = lambda s, t=best_target: not (0 in s and t.issubset(s))
            worst_pred = lambda s, t=worst_target: not (0 in s and t.issubset(s))

            o_best = CountingConsistencyOracle(best_pred)
            res_best = quickxplain([0], c_seq, o_best)
            expected_best = int(round(math.log2(n // k))) + 2 * k
            assert res_best is not None and frozenset(res_best) == best_target
            assert o_best.calls == expected_best, (n, k, o_best.calls, expected_best)

            o_worst = CountingConsistencyOracle(worst_pred)
            res_worst = quickxplain([0], c_seq, o_worst)
            expected_worst = 2 * k * int(round(math.log2(n // k))) + 2 * k
            assert res_worst is not None and frozenset(res_worst) == worst_target
            assert o_worst.calls == expected_worst, (n, k, o_worst.calls, expected_worst)

            # Empty-background identity: Delta = B = [] skips Line 4 at the root
            o_best_empty = CountingConsistencyOracle(lambda s, t=best_target: not t.issubset(s))
            res_best_empty = quickxplain([], c_seq, o_best_empty)
            assert res_best_empty is not None and frozenset(res_best_empty) == best_target
            assert o_best_empty.calls == expected_best - 1

            o_worst_empty = CountingConsistencyOracle(lambda s, t=worst_target: not t.issubset(s))
            res_worst_empty = quickxplain([], c_seq, o_worst_empty)
            assert res_worst_empty is not None and frozenset(res_worst_empty) == worst_target
            assert o_worst_empty.calls == expected_worst - 1

            complexity_rows.append(
                {
                    "n": n,
                    "k": k,
                    "best_calls": o_best.calls,
                    "worst_calls": o_worst.calls,
                }
            )

    # 1B. Exhaustive 120-permutation check on Junker Example 1 (station-wagon budget)
    wagon_costs = {1: 500, 2: 500, 3: 800, 4: 500, 5: 2600}
    wagon_pred = lambda s: (0 not in s) or sum(wagon_costs.get(i, 0) for i in s) <= 3000
    wagon_muses = enumerate_minimal_conflicts_bruteforce([0], [1, 2, 3, 4, 5], wagon_pred)
    wagon_msses = enumerate_maximal_relaxations_bruteforce([0], [1, 2, 3, 4, 5], wagon_pred)
    assert wagon_muses == {
        frozenset({1, 5}),
        frozenset({2, 5}),
        frozenset({3, 5}),
        frozenset({4, 5}),
    }
    assert wagon_msses == {frozenset({1, 2, 3, 4}), frozenset({5})}

    for perm in itertools.permutations([1, 2, 3, 4, 5]):
        _verify_primal_and_dual_junker_props([0], perm, wagon_pred, wagon_muses, wagon_msses)

    # 1C. Multi-size overlapping conflict family (n = 10, 7 MUSes of sizes 2, 3, 4)
    planted_cores = (
        frozenset({1, 6}),
        frozenset({2, 7}),
        frozenset({1, 3, 8}),
        frozenset({2, 4, 9}),
        frozenset({3, 5, 10}),
        frozenset({4, 5, 6, 7}),
        frozenset({1, 2, 5, 8}),
    )
    overlap_pred = lambda s: (0 not in s) or not any(core.issubset(s) for core in planted_cores)
    exact_muses = enumerate_minimal_conflicts_bruteforce([0], range(1, 11), overlap_pred)
    exact_msses = enumerate_maximal_relaxations_bruteforce([0], range(1, 11), overlap_pred)
    assert len(exact_muses) == 7
    assert {frozenset(range(1, 11)) - r for r in exact_msses} == minimal_hitting_sets(
        exact_muses, 10
    )

    rng = random.Random(20040725)
    base_items = list(range(1, 11))
    for _ in range(200):
        perm_10 = list(base_items)
        rng.shuffle(perm_10)
        _verify_primal_and_dual_junker_props([0], perm_10, overlap_pred, exact_muses, exact_msses)

    return {
        "evidence_role": "normative + derived",
        "complexity_rows": complexity_rows,
        "n64_k4_best_worst": [complexity_rows[2]["best_calls"], complexity_rows[2]["worst_calls"]],
        "n256_k8_best_worst": [complexity_rows[7]["best_calls"], complexity_rows[7]["worst_calls"]],
        "wagon_permutations_verified": 120,
        "wagon_mus_mss_counts": [len(wagon_muses), len(wagon_msses)],
        "overlapping_permutations_verified": 200,
        "overlapping_mus_mss_counts": [len(exact_muses), len(exact_msses)],
        "junker_prop3_lex_relaxation_verified": True,
        "junker_prop4_min_cut_equals_max_conflict_verified": True,
    }


# =============================================================================
# PROBE 2: MARCO / MARCO+ (liffiton/MARCO@27e056bd), Hitting-Set Duality,
#          and Multi-MUS Shadow-Price Cliff Attribution via Stratified WMaxSAT
# [evidence_role: normative + source + derived]
# =============================================================================


def dpll_sat(
    num_vars: int,
    clauses: Sequence[frozenset[int]],
    assumptions: Iterable[int] = (),
    default_phase: bool = True,
) -> list[bool] | None:
    """Pure-stdlib DPLL + unit propagation SAT solver returning a 1-indexed assignment."""
    assign: dict[int, bool] = {}
    for lit in assumptions:
        var, val = abs(lit), (lit > 0)
        if var in assign and assign[var] != val:
            return None
        assign[var] = val

    branch_order = (default_phase, not default_phase)

    def solve(cur: dict[int, bool]) -> dict[int, bool] | None:
        cur = dict(cur)
        while True:
            changed = False
            for cl in clauses:
                satisfied = False
                unassigned: list[int] = []
                for lit in cl:
                    v = abs(lit)
                    if v in cur:
                        if cur[v] == (lit > 0):
                            satisfied = True
                            break
                    else:
                        unassigned.append(lit)
                if satisfied:
                    continue
                if not unassigned:
                    return None
                if len(unassigned) == 1:
                    u_lit = unassigned[0]
                    cur[abs(u_lit)] = u_lit > 0
                    changed = True
            if not changed:
                break

        if len(cur) == num_vars:
            return cur
        next_var = next(v for v in range(1, num_vars + 1) if v not in cur)
        for choice in branch_order:
            nxt = dict(cur)
            nxt[next_var] = choice
            ans = solve(nxt)
            if ans is not None:
                return ans
        return None

    res = solve(assign)
    if res is None:
        return None
    return [False] + [res.get(v, False) for v in range(1, num_vars + 1)]


class MarcoMapSolver:
    """Port of MapSolver, MinicardMapSolver, and MinisatMapSolver in
    liffiton/MARCO@27e056bd (src/marco/mapsolvers.py:L7-244).
    """

    def __init__(
        self,
        n: int,
        bias: bool | None = True,
        maximize_mode: str = "cardinality",
    ) -> None:
        assert maximize_mode in ("cardinality", "subset", "none")
        self.n = n
        self.bias = bias  # True: high/MUSes (maximal); False: low/MCSes (minimal); None: unmaximized
        self.maximize_mode = "none" if bias is None else maximize_mode
        self.all_n = frozenset(range(1, n + 1))
        self.clauses: list[frozenset[int]] = []
        self.maximize_seed_calls = 0

    def complement(self, aset: Iterable[int]) -> frozenset[int]:
        return self.all_n - frozenset(aset)

    def add_clause(self, clause: Iterable[int]) -> None:
        self.clauses.append(frozenset(clause))

    def block_down(self, frompoint: Iterable[int]) -> None:
        # mapsolvers.py:L120-123: clause = complement(frompoint)
        self.add_clause(self.complement(frompoint))

    def block_up(self, frompoint: Iterable[int]) -> None:
        # mapsolvers.py:L125-128: clause = [-i for i in frompoint]
        self.add_clause(-i for i in frompoint)

    def implies(self) -> set[int]:
        """mapsolvers.py:L38-46: level-0 backbone literals implied by map clauses."""
        hard: set[int] = set()
        for i in range(1, self.n + 1):
            if dpll_sat(self.n, self.clauses, assumptions=(-i,)) is None:
                hard.add(i)
            elif dpll_sat(self.n, self.clauses, assumptions=(i,)) is None:
                hard.add(-i)
        return hard

    def _model_to_seed(self, model: list[bool]) -> list[int]:
        return [i for i in range(1, self.n + 1) if model[i]]

    def maximize_seed(self, seed: Sequence[int], direction: bool) -> list[int]:
        """Port of MapSolver.maximize_seed (mapsolvers.py:L81-108): inclusion-maximal/minimal."""
        self.maximize_seed_calls += 1
        cur = list(seed)
        while True:
            comp = sorted(self.complement(cur))
            if direction:
                if not comp:
                    return sorted(cur)
                extra = [frozenset(comp)]
                model = dpll_sat(self.n, list(self.clauses) + extra, assumptions=cur)
            else:
                if not cur:
                    return []
                extra = [frozenset(-i for i in cur)]
                model = dpll_sat(
                    self.n,
                    list(self.clauses) + extra,
                    assumptions=[-i for i in comp],
                    default_phase=False,
                )
            if model is None:
                return sorted(cur)
            cur = self._model_to_seed(model)

    def next_seed(self) -> list[int] | None:
        if self.maximize_mode == "cardinality" and self.bias is True:
            # MinicardMapSolver (mapsolvers.py:L131-221, bias=True): cardinality-maximal seed
            for r in range(self.n, -1, -1):
                for comb in itertools.combinations(range(1, self.n + 1), r):
                    chosen = set(comb)
                    assumps = [i if i in chosen else -i for i in range(1, self.n + 1)]
                    if dpll_sat(self.n, self.clauses, assumptions=assumps) is not None:
                        return list(comb)
            return None
        if self.maximize_mode == "cardinality" and self.bias is False:
            # MinicardMapSolver (mapsolvers.py:L131-221, bias=False): cardinality-minimal seed
            for r in range(self.n + 1):
                for comb in itertools.combinations(range(1, self.n + 1), r):
                    chosen = set(comb)
                    assumps = [i if i in chosen else -i for i in range(1, self.n + 1)]
                    if dpll_sat(self.n, self.clauses, assumptions=assumps) is not None:
                        return list(comb)
            return None
        if self.maximize_mode == "subset" and self.bias is not None:
            # MinisatMapSolver (mapsolvers.py:L224-244): arbitrary model refined via maximize_seed
            # Use opposite default_phase first so maximize_seed performs non-trivial iterative steps.
            model = dpll_sat(self.n, self.clauses, default_phase=not self.bias)
            if model is None:
                return None
            return self.maximize_seed(self._model_to_seed(model), direction=self.bias)
        model = dpll_sat(self.n, self.clauses)
        return None if model is None else self._model_to_seed(model)


class PropositionalSubsetSolver:
    """Port of MinisatSubsetSolver in liffiton/MARCO@27e056bd (CNFsolvers.py:L114-178)."""

    def __init__(
        self,
        num_vars: int,
        hard_clauses: Sequence[frozenset[int]],
        soft_clauses: Sequence[frozenset[int]],
    ) -> None:
        self.num_vars = num_vars
        self.hard_clauses = list(hard_clauses)
        self.soft_clauses = list(soft_clauses)
        self.n = len(soft_clauses)
        self._msolver: MarcoMapSolver | None = None
        self.sat_calls = 0

    def set_msolver(self, msolver: MarcoMapSolver) -> None:
        self._msolver = msolver

    def check_subset(
        self, seed: Iterable[int], improve_seed: bool = False
    ) -> tuple[bool, list[int]] | bool:
        self.sat_calls += 1
        seed_list = sorted(set(seed))
        active_clauses = self.hard_clauses + [self.soft_clauses[i - 1] for i in seed_list]
        model = dpll_sat(self.num_vars, active_clauses)
        is_sat = model is not None
        if not improve_seed:
            return is_sat
        if is_sat and model is not None:
            # CNFsolvers.py:L118: include any other soft clauses satisfied by the witness model
            sat_superset = [
                idx
                for idx, cl in enumerate(self.soft_clauses, 1)
                if any((model[abs(lit)] if lit > 0 else not model[abs(lit)]) for lit in cl)
            ]
            return True, sorted(set(seed_list) | set(sat_superset))
        return False, seed_list

    def shrink(self, seed: Sequence[int]) -> list[int]:
        """CNFsolvers.py:L128-141: deletion-based MUS shrink with map-implication skip."""
        hard = self._msolver.implies() if self._msolver is not None else set()
        current = set(seed)
        for i in sorted(seed):
            if i not in current or i in hard:
                continue
            current.remove(i)
            if self.check_subset(current):
                current.add(i)
        return sorted(current)

    def grow(self, seed: Sequence[int]) -> list[int]:
        """CNFsolvers.py:L156-178: linear MSS extension with sat_subset acceleration."""
        current = set(seed)
        for x in range(1, self.n + 1):
            if x in current:
                continue
            trial = current | {x}
            is_sat, improved = self.check_subset(trial, improve_seed=True)  # type: ignore[misc]
            if is_sat:
                current = set(improved)
        return sorted(current)


def marco_polo_enumerate(
    csolver: PropositionalSubsetSolver,
    bias_mode: str = "MUSes",
    maximize: bool = True,
    maximize_mode: str = "cardinality",
) -> tuple[set[frozenset[int]], set[frozenset[int]], dict[str, int]]:
    """Exact port of MarcoPolo.enumerate (MarcoPolo.py:L54-139)."""
    bias_flag: bool | None = None if not maximize else (bias_mode == "MUSes")
    eff_mode = "none" if not maximize else maximize_mode
    msolver = MarcoMapSolver(csolver.n, bias=bias_flag, maximize_mode=eff_mode)
    csolver.set_msolver(msolver)
    bias_high = bias_mode == "MUSes"

    muses: set[frozenset[int]] = set()
    msses: set[frozenset[int]] = set()
    stats = {"seeds": 0, "grow_calls": 0, "shrink_calls": 0, "maximize_seed_calls": 0}

    while (seed := msolver.next_seed()) is not None:
        stats["seeds"] += 1
        known_max = maximize
        seed_is_sat, improved_seed = csolver.check_subset(seed, improve_seed=True)  # type: ignore[misc]
        seed = improved_seed
        # MarcoPolo.py:L67
        known_max = known_max and (seed_is_sat == bias_high)

        if seed_is_sat:
            if known_max:
                mss = frozenset(seed)
            else:
                stats["grow_calls"] += 1
                mss = frozenset(csolver.grow(seed))
            msses.add(mss)
            msolver.block_down(mss)
        else:
            if known_max:
                mus = frozenset(seed)
            else:
                stats["shrink_calls"] += 1
                mus = frozenset(csolver.shrink(seed))
            muses.add(mus)
            msolver.block_up(mus)

    stats["maximize_seed_calls"] = msolver.maximize_seed_calls
    return muses, msses, stats


def minimal_hitting_sets(family: Iterable[frozenset[int]], n: int) -> set[frozenset[int]]:
    """Exact minimal hitting sets over universe {1..n}."""
    fam = list(family)
    all_hitting: list[frozenset[int]] = []
    for r in range(n + 1):
        for comb in itertools.combinations(range(1, n + 1), r):
            cand = frozenset(comb)
            if all(bool(cand & target) for target in fam):
                if not any(prev < cand for prev in all_hitting):
                    all_hitting.append(cand)
    return set(all_hitting)


def rc2_stratified_wmaxsat(
    num_base_vars: int,
    hard_clauses: Sequence[frozenset[int]],
    soft_weighted_clauses: Sequence[tuple[frozenset[int], int]],
) -> tuple[int, list[bool], frozenset[int]]:
    """Core-guided OLL / stratified WMaxSAT solver (Ignatiev et al., JSAT 2019, RC2Stratified)."""
    next_var = num_base_vars
    work_hard = [frozenset(cl) for cl in hard_clauses]
    sel_weights: dict[int, int] = {}
    orig_sel_vars: list[int] = []

    for cl, w in soft_weighted_clauses:
        assert w > 0
        next_var += 1
        b_var = next_var
        orig_sel_vars.append(b_var)
        work_hard.append(frozenset(set(cl) | {b_var}))
        sel_weights[-b_var] = w

    cost = 0
    distinct_levels = sorted({w for w in sel_weights.values()}, reverse=True)
    threshold = distinct_levels[0] if distinct_levels else 0

    def extract_minimal_selector_core(active_assumps: list[int]) -> list[int]:
        cur = list(active_assumps)
        for lit in list(active_assumps):
            trial = [x for x in cur if x != lit]
            if dpll_sat(next_var, work_hard, assumptions=trial) is None:
                cur = trial
        return cur

    def add_at_least_two_relaxation(core_relax_lits: list[int]) -> list[int]:
        nonlocal next_var
        r_lits = [-a for a in core_relax_lits]
        m = len(r_lits)
        if m == 1:
            return []
        prev_unary: list[int] = [r_lits[0]]
        for idx in range(1, m):
            cur_lit = r_lits[idx]
            new_len = len(prev_unary) + 1
            new_unary: list[int] = []
            for _ in range(new_len):
                next_var += 1
                new_unary.append(next_var)
            for p_idx, p_var in enumerate(prev_unary):
                work_hard.append(frozenset({-p_var, new_unary[p_idx]}))
                work_hard.append(frozenset({-p_var, -cur_lit, new_unary[p_idx + 1]}))
            work_hard.append(frozenset({-cur_lit, new_unary[0]}))
            prev_unary = new_unary
        work_hard.append(frozenset({prev_unary[0]}))
        return [-u for u in prev_unary[1:]]

    while threshold > 0:
        while True:
            active = sorted([lit for lit, w in sel_weights.items() if w >= threshold], key=abs)
            model = dpll_sat(next_var, work_hard, assumptions=active)
            if model is not None:
                break
            core = extract_minimal_selector_core(active)
            min_w = min(sel_weights[lit] for lit in core)
            cost += min_w
            for lit in core:
                rem = sel_weights[lit] - min_w
                if rem == 0:
                    del sel_weights[lit]
                else:
                    sel_weights[lit] = rem
            for new_assump in add_at_least_two_relaxation(core):
                sel_weights[new_assump] = min_w

        lower_weights = [w for w in sel_weights.values() if w < threshold]
        threshold = max(lower_weights) if lower_weights else 0

    final_assumps = sorted(sel_weights.keys(), key=abs)
    final_model = dpll_sat(next_var, work_hard, assumptions=final_assumps)
    assert final_model is not None
    violated = frozenset(idx for idx, b_var in enumerate(orig_sel_vars, 1) if final_model[b_var])
    actual_cost = sum(soft_weighted_clauses[idx - 1][1] for idx in violated)
    assert actual_cost == cost, (actual_cost, cost)
    return cost, final_model[: num_base_vars + 1], violated


def probe_marco_duality_and_wmaxsat_shadow_prices() -> dict[str, Any]:
    # 2A. Propositional CNF system with 6 soft clauses + hard (x4) over 4 variables:
    hard_cnf = [frozenset({4})]
    soft_cnf = [
        frozenset({1}),          # 1
        frozenset({-1}),         # 2
        frozenset({2}),          # 3
        frozenset({3}),          # 4
        frozenset({-1, -2, -3}), # 5
        frozenset({-2, -4}),     # 6
    ]
    muses_unmax, msses_unmax, stats_unmax = marco_polo_enumerate(
        PropositionalSubsetSolver(4, hard_cnf, soft_cnf),
        bias_mode="MUSes",
        maximize=False,
    )
    muses_card_hi, msses_card_hi, stats_card_hi = marco_polo_enumerate(
        PropositionalSubsetSolver(4, hard_cnf, soft_cnf),
        bias_mode="MUSes",
        maximize=True,
        maximize_mode="cardinality",
    )
    muses_sub_hi, msses_sub_hi, stats_sub_hi = marco_polo_enumerate(
        PropositionalSubsetSolver(4, hard_cnf, soft_cnf),
        bias_mode="MUSes",
        maximize=True,
        maximize_mode="subset",
    )
    muses_card_lo, msses_card_lo, stats_card_lo = marco_polo_enumerate(
        PropositionalSubsetSolver(4, hard_cnf, soft_cnf),
        bias_mode="MCSes",
        maximize=True,
        maximize_mode="cardinality",
    )
    muses_sub_lo, msses_sub_lo, stats_sub_lo = marco_polo_enumerate(
        PropositionalSubsetSolver(4, hard_cnf, soft_cnf),
        bias_mode="MCSes",
        maximize=True,
        maximize_mode="subset",
    )

    assert muses_unmax == muses_card_hi == muses_sub_hi == muses_card_lo == muses_sub_lo
    assert msses_unmax == msses_card_hi == msses_sub_hi == msses_card_lo == msses_sub_lo
    assert stats_card_hi["grow_calls"] == 0 and stats_sub_hi["grow_calls"] == 0
    assert stats_card_lo["shrink_calls"] == 0 and stats_sub_lo["shrink_calls"] == 0
    assert stats_sub_hi["maximize_seed_calls"] > 0 and stats_sub_lo["maximize_seed_calls"] > 0
    assert stats_unmax["maximize_seed_calls"] == 0

    all_idx = frozenset(range(1, len(soft_cnf) + 1))
    mcses = {all_idx - mss for mss in msses_card_hi}
    assert minimal_hitting_sets(muses_card_hi, len(soft_cnf)) == mcses
    assert minimal_hitting_sets(mcses, len(soft_cnf)) == muses_card_hi

    # 2B. Coupled Architectural Constraint Tiers & Zero-Shadow-Price Cliff
    # Variables 1..4 = requirements r1, r2, r3, r4
    # Variables 5..8 = architectural mechanisms m1(w=3), m2(w=4), m3(w=20), m4(w=6)
    b_arch = [
        frozenset({-1, 5, 7}),
        frozenset({-2, 6, 7}),
        frozenset({-3, 5, 7}),
        frozenset({-4, 8}),
        frozenset({-1, -3, 7}),
        frozenset({-2, -4, 7}),
    ]
    mech_weights = {5: 3, 6: 4, 7: 20, 8: 6}
    soft_mechs = [(frozenset({-m_var}), w) for m_var, w in sorted(mech_weights.items())]

    def arch_min_cost(active_reqs: Iterable[int]) -> int:
        req_unit_clauses = [frozenset({r}) for r in active_reqs]
        opt_cost, _, _ = rc2_stratified_wmaxsat(8, b_arch + req_unit_clauses, soft_mechs)
        bf_cost = min(
            sum(mech_weights[m] for m in chosen_mechs)
            for k_m in range(len(mech_weights) + 1)
            for chosen_mechs in itertools.combinations(sorted(mech_weights), k_m)
            if dpll_sat(
                8,
                b_arch + req_unit_clauses,
                assumptions=[m if m in chosen_mechs else -m for m in sorted(mech_weights)],
            )
            is not None
        )
        assert opt_cost == bf_cost
        return opt_cost

    all_reqs = frozenset({1, 2, 3, 4})
    full_cost = arch_min_cost(all_reqs)
    assert full_cost == 26  # {m3(20), m4(6)}

    leave_one_out = {f"r{r}": full_cost - arch_min_cost(all_reqs - {r}) for r in sorted(all_reqs)}
    assert leave_one_out == {"r1": 0, "r2": 0, "r3": 0, "r4": 6}

    joint_r1_r2_saving = full_cost - arch_min_cost(all_reqs - {1, 2})
    assert joint_r1_r2_saving == 17  # 26 -> 9 ({m1(3), m4(6)})
    assert joint_r1_r2_saving > leave_one_out["r1"] + leave_one_out["r2"]

    no_m3_hard = b_arch + [frozenset({-7})]
    req_soft = [frozenset({1}), frozenset({2}), frozenset({3}), frozenset({4})]
    tier_muses, tier_msses, _ = marco_polo_enumerate(
        PropositionalSubsetSolver(8, no_m3_hard, req_soft),
        bias_mode="MUSes",
        maximize=True,
        maximize_mode="subset",
    )
    tier_mcses = {all_reqs - mss for mss in tier_msses}
    assert tier_muses == {frozenset({1, 3}), frozenset({2, 4})}
    assert tier_mcses == {
        frozenset({1, 2}),
        frozenset({1, 4}),
        frozenset({2, 3}),
        frozenset({3, 4}),
    }
    assert minimal_hitting_sets(tier_muses, 4) == tier_mcses

    req_relax_soft = [(frozenset({1}), 2), (frozenset({2}), 2), (frozenset({3}), 8), (frozenset({4}), 10)]
    joint_opt_cost, _, violated_indices = rc2_stratified_wmaxsat(8, b_arch, req_relax_soft + soft_mechs)
    relaxed_reqs = frozenset(i for i in violated_indices if i <= 4)
    active_mechs = frozenset(i for i in violated_indices if i > 4)
    assert relaxed_reqs == frozenset({1, 2})
    assert joint_opt_cost == (2 + 2) + (3 + 6) == 13
    assert len(active_mechs) == 2

    return {
        "evidence_role": "normative + source + derived",
        "cnf_mus_mcs_counts": [len(muses_card_hi), len(mcses)],
        "marco_plus_grow_calls_card_and_subset": [
            stats_card_hi["grow_calls"],
            stats_sub_hi["grow_calls"],
        ],
        "marco_low_shrink_calls_card_and_subset": [
            stats_card_lo["shrink_calls"],
            stats_sub_lo["shrink_calls"],
        ],
        "subset_maximize_seed_calls_high_and_low": [
            stats_sub_hi["maximize_seed_calls"],
            stats_sub_lo["maximize_seed_calls"],
        ],
        "full_arch_cost": full_cost,
        "leave_one_out_shadow_prices": leave_one_out,
        "joint_r1_r2_saving": joint_r1_r2_saving,
        "tier_mcs_count": len(tier_mcses),
        "wmaxsat_optimal_joint_cost": joint_opt_cost,
    }


# =============================================================================
# PROBE 3: Gunter-Jackson-Zave 4-Phenomenon WRSPM Adequacy/Vacuity (Eqs. 2-7)
#          and KAOS Obstacle Consistency, Obstruction, Completeness,
#          Complete OR-Refinement, & Minimal AND-Refinement (Sec. 3.1-3.3)
# [evidence_role: normative + derived]
# =============================================================================

EH_VARS = ("moving_on_runway", "wheels_out", "wheels_blocked", "aquaplaning")
EV_VARS = ("wheel_pulse_on", "wow_airspeed_on")
SV_VARS = ("reverse_thrust_cmd",)
SH_VARS = ("kalman_register_ok",)
ALL_PHENOMENA = EH_VARS + EV_VARS + SV_VARS + SH_VARS


def _assignments(var_names: Sequence[str]) -> list[dict[str, bool]]:
    return [
        dict(zip(var_names, bits))
        for bits in itertools.product((False, True), repeat=len(var_names))
    ]


ALL_WRSPM_STATES = _assignments(ALL_PHENOMENA)


def semantic_free_vars(pred: Callable[[dict[str, bool]], bool]) -> frozenset[str]:
    """Compute exact semantic variable support of a Boolean predicate over all 2^8 states."""
    essential: set[str] = set()
    for var in ALL_PHENOMENA:
        for st in ALL_WRSPM_STATES:
            flipped = dict(st)
            flipped[var] = not st[var]
            if pred(st) != pred(flipped):
                essential.add(var)
                break
    return frozenset(essential)


def check_wrspm_obligations(
    W: Callable[[dict[str, bool]], bool],
    S: Callable[[dict[str, bool]], bool],
    R: Callable[[dict[str, bool]], bool],
    M: Callable[[dict[str, bool]], bool],
    P: Callable[[dict[str, bool]], bool],
) -> dict[str, bool]:
    """Check Gunter et al. (IEEE Software 2000, pp. 38-40) 5-artifact vocabulary & Eqs. 2, 4, 5, 6, 7."""
    eh_set = frozenset(EH_VARS)
    ev_set = frozenset(EV_VARS)
    sv_set = frozenset(SV_VARS)
    sh_set = frozenset(SH_VARS)

    free_w = semantic_free_vars(W)
    free_r = semantic_free_vars(R)
    free_s = semantic_free_vars(S)
    free_m = semantic_free_vars(M)
    free_p = semantic_free_vars(P)

    # Designated terminology restrictions across ALL FIVE artifacts (Gunter et al. 2000, p. 38):
    w_vocab_ok = free_w.issubset(eh_set | ev_set | sv_set)
    r_vocab_ok = free_r.issubset(eh_set | ev_set | sv_set)
    s_vocab_ok = free_s.issubset(ev_set | sv_set)
    m_vocab_ok = free_m.issubset(ev_set | sv_set | sh_set)
    p_vocab_ok = free_p.issubset(ev_set | sv_set | sh_set)
    vocab_ok = w_vocab_ok and r_vocab_ok and s_vocab_ok and m_vocab_ok and p_vocab_ok

    eh_space = _assignments(EH_VARS)
    ev_space = _assignments(EV_VARS)
    s_space = [{**sv, **sh} for sv in _assignments(SV_VARS) for sh in _assignments(SH_VARS)]
    e_space = [{**eh, **ev} for eh in eh_space for ev in ev_space]

    # Verify semantic invariance of S over hidden phenomena (e_h U s_h) iff s_vocab_ok
    if s_vocab_ok:
        for ev in ev_space:
            for sv in _assignments(SV_VARS):
                ref_val = S({**ev, **sv, **eh_space[0], ** _assignments(SH_VARS)[0]})
                for eh in eh_space:
                    for sh in _assignments(SH_VARS):
                        assert S({**ev, **sv, **eh, **sh}) == ref_val

    # Eq. (2): Domain consistency (exists e, s. W)
    eq2_domain_consistent = any(W(st) for st in ALL_WRSPM_STATES)
    # Bare satisfiability (exists e, s. W /\ S) - misses partial-input vacuity!
    bare_ws_sat = any(W(st) and S(st) for st in ALL_WRSPM_STATES)
    # Eq. (4): Adequacy (forall e, s. W /\ S => R)
    eq4_adequacy = all((not (W(st) and S(st))) or R(st) for st in ALL_WRSPM_STATES)

    # Eq. (7) weak relative consistency vs. Eq. (5) strengthened relative consistency
    eq7_weak_rel = True
    eq5_strengthened_rel = s_vocab_ok
    for ev in ev_space:
        w_feasible_ev = any(W({**ev, **eh, **s}) for eh in eh_space for s in s_space)
        if not w_feasible_ev:
            continue
        if not any(W({**ev, **eh, **s}) and S({**ev, **eh, **s}) for eh in eh_space for s in s_space):
            eq7_weak_rel = False
        if s_vocab_ok:
            eh_rep = eh_space[0]
            exists_s = any(S({**ev, **eh_rep, **s}) for s in s_space)
            forall_s_w = all(
                (not S({**ev, **eh_rep, **s}))
                or any(W({**ev, **eh, **s}) for eh in eh_space)
                for s in s_space
            )
            if not (exists_s and forall_s_w):
                eq5_strengthened_rel = False

    # Eq. (6): System-side implementability: forall e. (exists s. S) => ((exists s. M /\ P) /\ (forall s. M /\ P => S))
    eq6_system_impl = m_vocab_ok and p_vocab_ok
    if eq6_system_impl:
        for e in e_space:
            if any(S({**e, **s}) for s in s_space):
                ex_mp = any(M({**e, **s}) and P({**e, **s}) for s in s_space)
                fa_mp = all(
                    (not (M({**e, **s}) and P({**e, **s}))) or S({**e, **s})
                    for s in s_space
                )
                if not (ex_mp and fa_mp):
                    eq6_system_impl = False
                    break

    return {
        "w_vocab_ok": w_vocab_ok,
        "r_vocab_ok": r_vocab_ok,
        "s_vocab_ok": s_vocab_ok,
        "m_vocab_ok": m_vocab_ok,
        "p_vocab_ok": p_vocab_ok,
        "vocab_ok": vocab_ok,
        "eq2_domain_consistent": eq2_domain_consistent,
        "bare_ws_sat": bare_ws_sat,
        "eq4_adequacy": eq4_adequacy,
        "eq7_weak_rel": eq7_weak_rel,
        "eq5_strengthened_rel": eq5_strengthened_rel,
        "eq6_system_impl": eq6_system_impl,
    }


def check_kaos_obstacles(
    dom: Callable[[dict[str, bool]], bool],
    goal: Callable[[dict[str, bool]], bool],
    obstacles: Sequence[Callable[[dict[str, bool]], bool]],
) -> dict[str, Any]:
    """Check van Lamsweerde & Letier (IEEE TSE 2000, Sec. 3.1-3.2, pp. 983-984) conditions."""
    per_obstacle: list[tuple[bool, bool]] = []
    for obs in obstacles:
        consistent = any(obs(st) and dom(st) for st in ALL_WRSPM_STATES)
        obstructs = all((not (obs(st) and dom(st))) or (not goal(st)) for st in ALL_WRSPM_STATES)
        per_obstacle.append((consistent, obstructs))

    residual_witnesses = [
        st
        for st in ALL_WRSPM_STATES
        if dom(st) and all(not obs(st) for obs in obstacles) and (not goal(st))
    ]
    return {
        "all_consistent": all(c for c, _ in per_obstacle),
        "all_obstruct": all(o for _, o in per_obstacle),
        "domain_complete": len(residual_witnesses) == 0,
        "residual_count": len(residual_witnesses),
    }


def check_kaos_complete_or_refinement(
    dom: Callable[[dict[str, bool]], bool],
    parent_obs: Callable[[dict[str, bool]], bool],
    sub_obstacles: Sequence[Callable[[dict[str, bool]], bool]],
) -> dict[str, bool]:
    """Check van Lamsweerde & Letier (IEEE TSE 2000, Sec. 3.3, p. 984) complete OR-refinement:
      1. Entailment: forall i. {O_i, Dom} |= O
      2. Domain consistency: forall i. {O_i, Dom} |/= false
      3. Completeness: {~O_1 /\\ ... /\\ ~O_n, Dom} |= ~O
      4. Optional disjointness: forall i != j. {O_i /\\ O_j, Dom} |= false
    """
    all_entail = all(
        all((not (sub(st) and dom(st))) or parent_obs(st) for st in ALL_WRSPM_STATES)
        for sub in sub_obstacles
    )
    all_consistent = all(
        any(sub(st) and dom(st) for st in ALL_WRSPM_STATES) for sub in sub_obstacles
    )
    or_complete = all(
        (not (dom(st) and all(not sub(st) for sub in sub_obstacles))) or (not parent_obs(st))
        for st in ALL_WRSPM_STATES
    )
    disjoint = all(
        not any(sub_obstacles[i](st) and sub_obstacles[j](st) and dom(st) for st in ALL_WRSPM_STATES)
        for i in range(len(sub_obstacles))
        for j in range(i + 1, len(sub_obstacles))
    )
    return {
        "all_entail_parent": all_entail,
        "all_consistent": all_consistent,
        "complete": or_complete,
        "valid_complete_or_refinement": all_entail and all_consistent and or_complete,
        "mutually_disjoint": disjoint,
    }


def check_kaos_minimal_and_refinement(
    dom: Callable[[dict[str, bool]], bool],
    parent_obs: Callable[[dict[str, bool]], bool],
    conjuncts: Sequence[Callable[[dict[str, bool]], bool]],
) -> dict[str, bool]:
    """Check van Lamsweerde & Letier (IEEE TSE 2000, Sec. 3.3, p. 984) minimal AND-refinement:
      1. Entailment: {O_1 /\\ ... /\\ O_n, Dom} |= O
      2. Consistency: {O_1 /\\ ... /\\ O_n, Dom} |/= false
      3. Minimality: forall i. {/\\_{j != i} O_j, Dom} |/= O
    """
    conj_all = lambda st: all(c(st) for c in conjuncts)
    entails_parent = all(
        (not (conj_all(st) and dom(st))) or parent_obs(st) for st in ALL_WRSPM_STATES
    )
    consistent = any(conj_all(st) and dom(st) for st in ALL_WRSPM_STATES)
    minimal = True
    for drop_idx in range(len(conjuncts)):
        others = [c for j, c in enumerate(conjuncts) if j != drop_idx]
        without_i_entails = all(
            (not (dom(st) and all(c(st) for c in others))) or parent_obs(st)
            for st in ALL_WRSPM_STATES
        )
        if without_i_entails:
            minimal = False
            break
    return {
        "entails_parent": entails_parent,
        "consistent": consistent,
        "minimal": minimal,
        "valid_minimal_and_refinement": entails_parent and consistent and minimal,
    }


def probe_wrspm_obligations_and_kaos_refinement() -> dict[str, Any]:
    W_runway = lambda st: (
        st["wheel_pulse_on"]
        == (
            st["moving_on_runway"]
            and st["wheels_out"]
            and (not st["wheels_blocked"])
            and (not st["aquaplaning"])
        )
        and (st["wow_airspeed_on"] == st["moving_on_runway"])
    )
    # Bidirectional flight-safety + landing-braking requirement:
    # (moving_on_runway => reverse_thrust_cmd) /\ (~moving_on_runway => ~reverse_thrust_cmd)
    R_safety = lambda st: st["reverse_thrust_cmd"] == st["moving_on_runway"]
    M_unconstrained = lambda st: True

    # Case 1: Warsaw A320 single wheel-pulse spec (adequate=False on aquaplaning/gear/block)
    S_single = lambda st: st["reverse_thrust_cmd"] == st["wheel_pulse_on"]
    P_single = lambda st: st["reverse_thrust_cmd"] == st["wheel_pulse_on"]
    res_single = check_wrspm_obligations(W_runway, S_single, R_safety, M_unconstrained, P_single)
    assert res_single["vocab_ok"] and res_single["eq2_domain_consistent"] and res_single["eq5_strengthened_rel"]
    assert not res_single["eq4_adequacy"]

    # Case 2: Partial-input-restricting vacuity trap (forbids wow_airspeed_on /\ ~wheel_pulse_on)
    S_partial_vac = lambda st: (
        ((not st["wow_airspeed_on"]) or st["wheel_pulse_on"])
        and (st["reverse_thrust_cmd"] == st["wheel_pulse_on"])
    )
    res_vac = check_wrspm_obligations(
        W_runway, S_partial_vac, R_safety, M_unconstrained, S_partial_vac
    )
    assert res_vac["vocab_ok"] and res_vac["bare_ws_sat"] and res_vac["eq4_adequacy"]
    assert not res_vac["eq5_strengthened_rel"]

    # Case 3: Output-coupled W separating weak Eq. (7) from strengthened Eq. (5)
    W_coupled = lambda st: W_runway(st) and not (
        st["wow_airspeed_on"] and (not st["reverse_thrust_cmd"]) and (not st["aquaplaning"])
    )
    S_permits_unsafe_out = lambda st: True
    res_eq5_vs_eq7 = check_wrspm_obligations(
        W_coupled, S_permits_unsafe_out, lambda st: True, M_unconstrained, S_permits_unsafe_out
    )
    assert res_eq5_vs_eq7["eq7_weak_rel"] and (not res_eq5_vs_eq7["eq5_strengthened_rel"])

    # Case 4: Specification-as-requirement / implementation-bias conflation (references e_h and s_h)
    S_conflated = lambda st: st["reverse_thrust_cmd"] == (
        st["moving_on_runway"] and st["kalman_register_ok"]
    )
    res_conflated = check_wrspm_obligations(
        W_runway, S_conflated, R_safety, M_unconstrained, S_conflated
    )
    assert (not res_conflated["s_vocab_ok"]) and (not res_conflated["p_vocab_ok"])
    assert not res_conflated["vocab_ok"]

    # Case 5: Sound sensor-redundant fusion specification + platform/program realization over s_h
    S_sound = lambda st: st["reverse_thrust_cmd"] == (
        st["wheel_pulse_on"] or st["wow_airspeed_on"]
    )
    M_platform_kalman = lambda st: st["kalman_register_ok"] == st["wow_airspeed_on"]
    P_sound = lambda st: st["reverse_thrust_cmd"] == (
        st["wheel_pulse_on"] or st["kalman_register_ok"]
    )
    res_sound = check_wrspm_obligations(W_runway, S_sound, R_safety, M_platform_kalman, P_sound)
    assert all(res_sound.values())
    # Verify zero mid-air reverse thrust across all realizable W /\ M /\ P states:
    assert not any(
        (not st["moving_on_runway"]) and st["reverse_thrust_cmd"]
        for st in ALL_WRSPM_STATES
        if W_runway(st) and M_platform_kalman(st) and P_sound(st)
    )
    # Verify M_platform_kalman is genuinely load-bearing for P_sound (fails Eq. 6 if M = True):
    assert not check_wrspm_obligations(W_runway, S_sound, R_safety, M_unconstrained, P_sound)[
        "eq6_system_impl"
    ]

    # KAOS Obstacle Analysis on bridge assumption G_bridge: moving_on_runway => wheel_pulse_on
    G_bridge = lambda st: (not st["moving_on_runway"]) or st["wheel_pulse_on"]
    O_root = lambda st: st["moving_on_runway"] and (not st["wheel_pulse_on"])

    # Unscoped ~wheels_out fails obstruction when airborne (moving_on_runway=False, wheels_out=False)
    O_unscoped = lambda st: not st["wheels_out"]
    kaos_unscoped = check_kaos_obstacles(W_runway, G_bridge, [O_unscoped])
    assert kaos_unscoped["all_consistent"] and (not kaos_unscoped["all_obstruct"])

    # Scoped A320 braking obstacles O1, O2, O3 (van Lamsweerde & Letier 2000, Sec. 3.2-3.3, p. 984)
    O1_gear = lambda st: st["moving_on_runway"] and (not st["wheels_out"])
    O2_blocked = lambda st: st["moving_on_runway"] and st["wheels_blocked"]
    O3_aqua = lambda st: st["moving_on_runway"] and st["aquaplaning"]

    kaos_incomplete = check_kaos_obstacles(W_runway, G_bridge, [O1_gear, O2_blocked])
    assert kaos_incomplete["all_consistent"] and kaos_incomplete["all_obstruct"]
    assert (not kaos_incomplete["domain_complete"]) and kaos_incomplete["residual_count"] > 0

    kaos_complete = check_kaos_obstacles(W_runway, G_bridge, [O1_gear, O2_blocked, O3_aqua])
    assert kaos_complete["all_consistent"] and kaos_complete["all_obstruct"] and kaos_complete["domain_complete"]

    # Complete OR-refinement verification (Sec. 3.3, p. 984) on {O1_gear, O2_blocked, O3_aqua}
    or_ref_two = check_kaos_complete_or_refinement(W_runway, O_root, [O1_gear, O2_blocked])
    or_ref_three = check_kaos_complete_or_refinement(W_runway, O_root, [O1_gear, O2_blocked, O3_aqua])
    assert (not or_ref_two["valid_complete_or_refinement"]) and (not or_ref_two["complete"])
    assert or_ref_three["valid_complete_or_refinement"] and (not or_ref_three["mutually_disjoint"])

    # Minimal AND-refinement verification (Sec. 3.3, p. 984, Condition 3 minimality)
    c_runway = lambda st: st["moving_on_runway"]
    c_retracted = lambda st: not st["wheels_out"]
    c_redundant = lambda st: not st["wheels_blocked"]
    and_minimal = check_kaos_minimal_and_refinement(W_runway, O1_gear, [c_runway, c_retracted])
    and_nonminimal = check_kaos_minimal_and_refinement(
        W_runway, O1_gear, [c_runway, c_retracted, c_redundant]
    )
    assert and_minimal["valid_minimal_and_refinement"]
    assert and_nonminimal["entails_parent"] and and_nonminimal["consistent"]
    assert (not and_nonminimal["minimal"]) and (not and_nonminimal["valid_minimal_and_refinement"])

    # Goal-substitution resolution G_substituted: moving_on_runway => (wheel_pulse_on V wow_airspeed_on)
    G_substituted = lambda st: (not st["moving_on_runway"]) or (
        st["wheel_pulse_on"] or st["wow_airspeed_on"]
    )
    kaos_resolved = check_kaos_obstacles(W_runway, G_substituted, [])
    assert kaos_resolved["domain_complete"]

    return {
        "evidence_role": "normative + derived",
        "single_sensor_adequacy": res_single["eq4_adequacy"],
        "partial_vacuity_bare_sat": res_vac["bare_ws_sat"],
        "partial_vacuity_eq4": res_vac["eq4_adequacy"],
        "partial_vacuity_eq5": res_vac["eq5_strengthened_rel"],
        "eq7_vs_eq5_separated": res_eq5_vs_eq7["eq7_weak_rel"]
        and (not res_eq5_vs_eq7["eq5_strengthened_rel"]),
        "conflated_vocab_rejected": not res_conflated["vocab_ok"],
        "sound_spec_all_pass": all(res_sound.values()),
        "unscoped_obstacle_obstructs": kaos_unscoped["all_obstruct"],
        "kaos_three_obstacle_or_refinement_complete": or_ref_three["valid_complete_or_refinement"],
        "kaos_and_refinement_minimality_separated": and_minimal["minimal"]
        and (not and_nonminimal["minimal"]),
    }


# =============================================================================
# PROBE 4: MetaGPT@11cdf466 ActionNode.fill Defects (xml_fill + create_class()
#          + code_fill/single_fill NameError), Derived H=1..6 Handoff Model,
#          and Declarative GSM PAC/PDG Lifecycle Operational Semantics
# [evidence_role: normative + source + documentation + derived]
# =============================================================================


@dataclass(frozen=True)
class ActionNodeFieldSpec:
    key: str
    expected_type: Any
    example: Any


def _is_optional_type(tp: Any) -> bool:
    origin = typing.get_origin(tp)
    return origin in (typing.Union, types.UnionType) and type(None) in typing.get_args(tp)


def metagpt_xml_fill_repro(field_types: dict[str, Any], raw_llm_output: str) -> dict[str, Any]:
    """Faithful reproduction of ActionNode.xml_fill (metagpt/actions/action_node.py:L553-594).

    Uses ast.literal_eval in place of bare eval() for safe execution while
    preserving exact branch equality checks (field_type == str/int/bool/list/dict),
    silent fallback coercions (0 / False / [] / {}), missing-tag omission, and
    parameterized-generic blindness (List[str] == list and Optional[str] == str are False).
    """
    extracted_data: dict[str, Any] = {}
    for field_name, field_type in field_types.items():
        pattern = rf"<{re.escape(field_name)}>(.*?)</{re.escape(field_name)}>"
        match = re.search(pattern, raw_llm_output, re.DOTALL)
        if match:
            raw_value = match.group(1).strip()
            if field_type == str:
                extracted_data[field_name] = raw_value
            elif field_type == int:
                try:
                    extracted_data[field_name] = int(raw_value)
                except ValueError:
                    extracted_data[field_name] = 0
            elif field_type == bool:
                extracted_data[field_name] = raw_value.lower() in ("true", "yes", "1", "on", "True")
            elif field_type == list:
                try:
                    val = ast.literal_eval(raw_value)
                    if not isinstance(val, list):
                        raise ValueError
                    extracted_data[field_name] = val
                except Exception:
                    extracted_data[field_name] = []
            elif field_type == dict:
                try:
                    val = ast.literal_eval(raw_value)
                    if not isinstance(val, dict):
                        raise ValueError
                    extracted_data[field_name] = val
                except Exception:
                    extracted_data[field_name] = {}
    return extracted_data


def metagpt_fill_xml_end_to_end_repro(
    specs: Sequence[ActionNodeFieldSpec], raw_llm_output: str
) -> dict[str, Any]:
    """Reproduce ActionNode.fill(mode='xml_fill') end-to-end (action_node.py:L231, L251-262, L641-643):
      1. result = xml_fill(context)
      2. create_class()(**result):
         - check_fields (L251-262) raises ValueError('Missing fields: ...') on any omitted
           non-Optional field (such as required List[str] dropped by xml_fill!);
         - Optional[T] fields bypass check_fields (L256) and silently fall back to
           Field(default=child.example) (L231), overwriting valid LLM XML with static
           prompt-template example text!
    """
    field_types = {sp.key: sp.expected_type for sp in specs}
    result = metagpt_xml_fill_repro(field_types, raw_llm_output)

    required_fields = {sp.key for sp in specs if not _is_optional_type(sp.expected_type)}
    missing_fields = required_fields - set(result.keys())
    if missing_fields:
        raise ValueError(f"Missing fields: {sorted(missing_fields)}")

    instantiated: dict[str, Any] = {}
    for sp in specs:
        if sp.key in result:
            instantiated[sp.key] = result[sp.key]
        else:
            # _get_children_mapping (action_node.py:L231): Field(default=child.example)
            instantiated[sp.key] = sp.example
    return instantiated


def metagpt_11cdf466_fill_dispatch_repro(*, req: str, mode: str) -> str:
    """Reproduce the unbound `context` NameError in FoundationAgents/MetaGPT@11cdf466
    ActionNode.fill (action_node.py:L597-664) after renaming positional `context`
    (v0.8.2 df9bc185 L594) to keyword-only `*, req` (L597):
      - mode='xml_fill' (L641) binds local `context = req` -> succeeds;
      - mode='code_fill' (L636) and mode='single_fill' (L647) reference bare
        unbound `context` -> raises NameError("name 'context' is not defined").
    """
    saved_context = req
    if mode == "code_fill":
        return str(context)  # type: ignore[name-defined]  # noqa: F821
    if mode == "xml_fill":
        context = f"<compiled>{saved_context}</compiled>"
        return context
    if mode == "single_fill":
        return str(context)  # type: ignore[name-defined]  # noqa: F821
    return saved_context


def strict_typed_json_validate(field_types: dict[str, Any], raw_json: str) -> dict[str, Any]:
    """Strict typed JSON schema validator preserving generics and Optional[T] without template leaks."""
    payload = json.loads(raw_json)
    if not isinstance(payload, dict):
        raise ValueError("Top-level payload must be a JSON object")
    required = {k for k, tp in field_types.items() if not _is_optional_type(tp)}
    missing = required - set(payload)
    if missing:
        raise ValueError(f"Missing required fields: {sorted(missing)}")
    unknown = set(payload) - set(field_types)
    if unknown:
        raise ValueError(f"Unrecognized fields: {sorted(unknown)}")

    for k, val in payload.items():
        expected = field_types[k]
        if _is_optional_type(expected):
            if val is None:
                continue
            inner_types = [t for t in typing.get_args(expected) if t is not type(None)]
            expected = inner_types[0]
        origin = typing.get_origin(expected)
        args = typing.get_args(expected)
        if origin is list:
            if not isinstance(val, list) or (args and not all(isinstance(x, args[0]) for x in val)):
                raise TypeError(f"Field {k!r} failed list[{args}] check")
        elif expected is int:
            if isinstance(val, bool) or not isinstance(val, int):
                raise TypeError(f"Field {k!r} expected int")
        elif expected is bool:
            if not isinstance(val, bool):
                raise TypeError(f"Field {k!r} expected bool")
        elif not isinstance(val, expected):
            raise TypeError(f"Field {k!r} expected {expected}")
    return payload


@dataclass(frozen=True)
class PACRule:
    """Declarative GSM Prerequisite-Antecedent-Consequent rule (Hull et al., DEBS 2011, Sec. 4)."""

    rule_id: str
    target_kind: str  # "stage" or "milestone"
    target_name: str
    target_polarity: bool  # True for +S/+m, False for -S/-m
    # Polarized internal status dependencies (e.g. "+Stage_2", "-M2_ok") inducing PDG edges:
    internal_triggers: tuple[str, ...] = ()
    # Optional external event name triggering this rule (e.g. "StartPipeline", "StageCompleted"):
    external_event: str | None = None
    # Prerequisite over current working state (must hold just before consequent fires):
    prerequisite: Callable[[dict[str, bool], dict[str, bool]], bool] = lambda stg, mst: True
    # Guard over pre-snapshot state + event payload:
    guard: Callable[[dict[str, bool], dict[str, bool], dict[str, Any]], bool] = (
        lambda pre_stg, pre_mst, ev_payload: True
    )

    @property
    def consequent_node(self) -> str:
        sign = "+" if self.target_polarity else "-"
        return f"{sign}{self.target_name}"


class DeclarativeGSMEngine:
    """Declarative Guard-Stage-Milestone operational engine with explicit PDG topological
    evaluation and GSM-1, GSM-2, GSM-3, and Toggle-Once verification (Hull et al., DEBS 2011;
    Damaggio, Hull, & Vaculin, Information Systems 2013).
    """

    def __init__(
        self,
        stages: Sequence[str],
        substages: dict[str, tuple[str, ...]],
        owns: dict[str, tuple[str, ...]],
        explicit_rules: Sequence[PACRule],
    ) -> None:
        self.stages = tuple(stages)
        self.substages = dict(substages)
        self.owns = dict(owns)
        self.milestones = tuple(m for ms in self.owns.values() for m in ms)
        self.parent_of: dict[str, str] = {
            ch: parent for parent, children in self.substages.items() for ch in children
        }

        # Compile implicit GSM-1 and GSM-2 PAC rules alongside explicit Guards / Ach / Inv rules:
        compiled: list[PACRule] = list(explicit_rules)
        for stg, owned_ms in self.owns.items():
            for m in owned_ms:
                # GSM-1a: opening stage S invalidates every achieved milestone m in Owns(S)
                compiled.append(
                    PACRule(
                        rule_id=f"gsm1_open_invalidates_{stg}_{m}",
                        target_kind="milestone",
                        target_name=m,
                        target_polarity=False,
                        internal_triggers=(f"+{stg}",),
                        prerequisite=lambda _s, cur_m, m_name=m: cur_m[m_name],
                    )
                )
                # GSM-1b: achieving milestone m in Owns(S) closes active stage S
                compiled.append(
                    PACRule(
                        rule_id=f"gsm1_achieve_closes_{m}_{stg}",
                        target_kind="stage",
                        target_name=stg,
                        target_polarity=False,
                        internal_triggers=(f"+{m}",),
                        prerequisite=lambda cur_s, _m, s_name=stg: cur_s[s_name],
                    )
                )
        for parent, children in self.substages.items():
            for ch in children:
                # GSM-2: closing parent stage automatically closes any active substage
                compiled.append(
                    PACRule(
                        rule_id=f"gsm2_parent_closes_{parent}_{ch}",
                        target_kind="stage",
                        target_name=ch,
                        target_polarity=False,
                        internal_triggers=(f"-{parent}",),
                        prerequisite=lambda cur_s, _m, c_name=ch: cur_s[c_name],
                    )
                )

        self.rules = tuple(compiled)
        self.topo_nodes, self.pdg_edge_count = self._build_and_toposort_pdg()

    def _build_and_toposort_pdg(self) -> tuple[tuple[str, ...], int]:
        nodes: list[str] = []
        for s in self.stages:
            nodes.extend((f"+{s}", f"-{s}"))
        for m in self.milestones:
            nodes.extend((f"+{m}", f"-{m}"))

        adj: dict[str, set[str]] = {u: set() for u in nodes}
        indeg: dict[str, int] = {u: 0 for u in nodes}
        for rule in self.rules:
            dst = rule.consequent_node
            for src in rule.internal_triggers:
                if dst not in adj[src]:
                    adj[src].add(dst)
                    indeg[dst] += 1

        queue = collections.deque(sorted(u for u, d in indeg.items() if d == 0))
        order: list[str] = []
        work_indeg = dict(indeg)
        while queue:
            u = queue.popleft()
            order.append(u)
            for v in sorted(adj[u]):
                work_indeg[v] -= 1
                if work_indeg[v] == 0:
                    queue.append(v)

        if len(order) != len(nodes):
            raise ValueError("GSM Polarized Dependency Graph (PDG) contains a cycle!")
        total_edges = sum(len(vs) for vs in adj.values())
        return tuple(order), total_edges

    def verify_snapshot_invariants(
        self, active_stages: dict[str, bool], milestones: dict[str, bool]
    ) -> None:
        for stg, owned_ms in self.owns.items():
            if active_stages[stg]:
                assert not any(milestones[m] for m in owned_ms), f"GSM-1 violated on {stg}"
            assert sum(1 for m in owned_ms if milestones[m]) <= 1, f"GSM-3 violated on {stg}"
        for parent, children in self.substages.items():
            if not active_stages[parent]:
                assert not any(active_stages[ch] for ch in children), f"GSM-2 violated under {parent}"

    def execute_external_event(
        self,
        active_stages: dict[str, bool],
        milestones: dict[str, bool],
        event_name: str,
        payload: dict[str, Any] | None = None,
    ) -> set[str]:
        """Compute one atomic B-step from a single external event via topological PDG evaluation."""
        ev_payload = dict(payload or {})
        pre_stg = dict(active_stages)
        pre_mst = dict(milestones)
        fired_polarities: set[str] = set()
        toggled_attrs: set[tuple[str, str]] = set()

        rules_by_node: dict[str, list[PACRule]] = collections.defaultdict(list)
        for r in self.rules:
            rules_by_node[r.consequent_node].append(r)

        for pol_node in self.topo_nodes:
            for rule in rules_by_node.get(pol_node, ()):
                ext_match = rule.external_event is not None and rule.external_event == event_name
                int_match = bool(rule.internal_triggers) and any(
                    trig in fired_polarities for trig in rule.internal_triggers
                )
                if not (ext_match or int_match):
                    continue
                if not rule.prerequisite(active_stages, milestones):
                    continue
                if not rule.guard(pre_stg, pre_mst, ev_payload):
                    continue
                # Enforce parent-active containment for substage opening (GSM-2):
                if rule.target_kind == "stage" and rule.target_polarity is True:
                    parent = self.parent_of.get(rule.target_name)
                    if parent is not None and not active_stages[parent]:
                        continue

                table = active_stages if rule.target_kind == "stage" else milestones
                if table[rule.target_name] != rule.target_polarity:
                    attr_key = (rule.target_kind, rule.target_name)
                    assert attr_key not in toggled_attrs, f"Toggle-Once violated on {attr_key}"
                    toggled_attrs.add(attr_key)
                    table[rule.target_name] = rule.target_polarity
                    fired_polarities.add(pol_node)
                    break

        self.verify_snapshot_invariants(active_stages, milestones)
        return fired_polarities


def probe_metagpt_fill_defects_and_declarative_gsm() -> dict[str, Any]:
    # 4A. MetaGPT@11cdf466 ActionNode.fill(mode="xml_fill") + create_class()(**result)
    #     and 11cdf466 code_fill/single_fill NameError
    prim_specs = (
        ActionNodeFieldSpec("retry_budget", int, 3),
        ActionNodeFieldSpec("strict_gate", bool, True),
        ActionNodeFieldSpec("endpoints", list, ["/v1/health"]),
        ActionNodeFieldSpec("limits", dict, {"rpm": 60}),
    )
    malformed_xml = (
        "<retry_budget>N/A</retry_budget>"
        "<strict_gate>invalid_bool</strict_gate>"
        "<endpoints>[unterminated</endpoints>"
        "<limits>{bad_dict</limits>"
    )
    coerced = metagpt_fill_xml_end_to_end_repro(prim_specs, malformed_xml)
    assert coerced == {"retry_budget": 0, "strict_gate": False, "endpoints": [], "limits": {}}

    # Required generic List[str] (e.g. WRITE_PRD_NODE Product Goals / DESIGN_API_NODE File list):
    # xml_fill drops valid <file_list> tag, causing create_class()(**result) (L643) to crash!
    design_api_required_specs = (
        ActionNodeFieldSpec("implementation_approach", str, "example approach"),
        ActionNodeFieldSpec("file_list", list[str], ["example_2048.py"]),
    )
    valid_required_xml = (
        "<implementation_approach>Modular clean architecture</implementation_approach>"
        "<file_list>['main.py', 'schema.py']</file_list>"
    )
    raw_xml_dict = metagpt_xml_fill_repro(
        {sp.key: sp.expected_type for sp in design_api_required_specs}, valid_required_xml
    )
    assert "file_list" not in raw_xml_dict
    required_generic_crashed = False
    try:
        metagpt_fill_xml_end_to_end_repro(design_api_required_specs, valid_required_xml)
    except ValueError as exc:
        required_generic_crashed = "file_list" in str(exc)
    assert required_generic_crashed

    # Optional[str] generic (e.g. DESIGN_API_NODE Data structures and interfaces: Optional[str]):
    # xml_fill drops valid XML tag, check_fields skips Optional, and Field(default=child.example) (L231)
    # silently overwrites LLM output with the static template example string!
    static_2048_template = "classDiagram\n    class Game2048 {\n        +start()\n    }"
    design_api_optional_specs = (
        ActionNodeFieldSpec("implementation_approach", str, "example approach"),
        ActionNodeFieldSpec("data_structures_and_interfaces", typing.Optional[str], static_2048_template),
    )
    valid_optional_xml = (
        "<implementation_approach>Event-sourced ledger</implementation_approach>"
        "<data_structures_and_interfaces>classDiagram\n    class Ledger</data_structures_and_interfaces>"
    )
    optional_end_to_end = metagpt_fill_xml_end_to_end_repro(
        design_api_optional_specs, valid_optional_xml
    )
    assert optional_end_to_end["data_structures_and_interfaces"] == static_2048_template

    # 11cdf466 NameError on mode="code_fill" (L636) and mode="single_fill" (L647) vs. xml_fill (L641):
    assert metagpt_11cdf466_fill_dispatch_repro(req="spec", mode="xml_fill") == "<compiled>spec</compiled>"
    broken_modes: list[str] = []
    for bad_mode in ("code_fill", "single_fill"):
        try:
            metagpt_11cdf466_fill_dispatch_repro(req="spec", mode=bad_mode)
        except NameError:
            broken_modes.append(bad_mode)
    assert broken_modes == ["code_fill", "single_fill"]

    # Strict JSON schema validator rejects malformed primitives and preserves both list[str] & Optional[str]:
    rejected_malformed = False
    try:
        strict_typed_json_validate(
            {sp.key: sp.expected_type for sp in prim_specs},
            '{"retry_budget": "N/A", "strict_gate": "invalid_bool", "endpoints": [], "limits": {}}',
        )
    except TypeError:
        rejected_malformed = True
    assert rejected_malformed

    accepted_typed = strict_typed_json_validate(
        {
            "implementation_approach": str,
            "file_list": list[str],
            "data_structures_and_interfaces": typing.Optional[str],
        },
        json.dumps(
            {
                "implementation_approach": "Event-sourced ledger",
                "file_list": ["main.py", "schema.py"],
                "data_structures_and_interfaces": "classDiagram\n    class Ledger",
            }
        ),
    )
    assert accepted_typed["file_list"] == ["main.py", "schema.py"]
    assert accepted_typed["data_structures_and_interfaces"] == "classDiagram\n    class Ledger"

    # 4B. Derived Illustrative Parametric Multi-Hop Handoff Model (H = 1..6)
    # Explicitly separated into (i) verbatim primary-source anchors and (ii) derived parametric curves:
    # - Mohamed et al. (ACL 2025, arXiv:2502.20258v2):
    #   * Sec. 4.4 & App. D.4 Table 8 (News2024 monolingual English Rephrasing, 1 iter = 1 handoff):
    #     Iter 0 = 0.945 -> Iter 3 = 0.645 (Llama), 0.593 (Mistral), 0.614 (Llama+Mistral),
    #     0.587 (Llama+Mistral+Gemma); Iter 10 = 0.602 / 0.562 / 0.572 / 0.531; Iter 100 = 0.490 (concave!).
    #   * Table 5 / App. D.2 (News2024 Bilingual EN<->FR, 1 iter = 2 handoffs): 0.949 -> 0.684 at Iter 3 (6 hops).
    # - Tam et al. (EMNLP 2024, arXiv:2408.02442v3, Table 2 & Table 11, GSM8K):
    #   * gpt-4o-mini NL = 0.9457, CFG JSON-Schema = 0.9171 (-2.86 pp), answer-first JSON-Mode = 0.8695 (-7.62 pp);
    #   * Gemini-1.5-Flash NL = 0.8930 -> JSON-mode = 0.4778 (-41.52 pp, Table 11).
    # Assumed illustrative transport/projection parameters (explicitly declared as derived):
    #   r_typed_transport = 0.999, p_compile_step = 0.997, r_prose_optimistic_geom = 0.947.
    r_prose_geom = Fraction(947, 1000)
    r_rephrase_h3_concave = Fraction(614, 945)  # Mohamed et al. Table 8 Llama+Mistral Iter 3 / Iter 0
    p_nl_reason = Fraction(9457, 10000)         # Tam et al. Table 2 gpt-4o-mini NL (94.57%)
    p_cfg_json_schema = Fraction(9171, 10000)   # Tam et al. Table 2 gpt-4o-mini JSON-Schema (91.71%)
    p_json_mode_mild = Fraction(8695, 10000)    # Tam et al. Table 2 gpt-4o-mini JSON-Mode (86.95%)
    p_json_mode_flash_rel = Fraction(4778, 8930) * p_nl_reason  # scaled Gemini-Flash JSON-mode ratio
    r_typed_transport = Fraction(999, 1000)
    p_compile_step = Fraction(997, 1000)

    hop_curve: list[dict[str, float]] = []
    for h in range(1, 7):
        k_reason = (h + 1) // 2
        prose_geom_score = float((r_prose_geom ** h) * (p_nl_reason ** k_reason))
        cfg_schema_score = float((r_typed_transport ** h) * (p_cfg_json_schema ** k_reason))
        json_mode_mild_score = float((r_typed_transport ** h) * (p_json_mode_mild ** k_reason))
        json_mode_severe_score = float((r_typed_transport ** h) * (p_json_mode_flash_rel ** k_reason))
        gsm_two_phase_score = float(((r_typed_transport * p_compile_step) ** h) * (p_nl_reason ** k_reason))

        assert gsm_two_phase_score > cfg_schema_score > json_mode_mild_score > json_mode_severe_score
        assert gsm_two_phase_score > prose_geom_score
        hop_curve.append(
            {
                "hops": h,
                "free_prose_geom_upper": round(prose_geom_score, 4),
                "single_pass_cfg_json_schema": round(cfg_schema_score, 4),
                "single_pass_answer_first_json_mode": round(json_mode_mild_score, 4),
                "single_pass_severe_json_mode": round(json_mode_severe_score, 4),
                "two_phase_deliberate_compile_gsm": round(gsm_two_phase_score, 4),
            }
        )

    prose_concave_h3 = round(float(r_rephrase_h3_concave * (p_nl_reason ** 2)), 4)
    assert prose_concave_h3 < hop_curve[2]["free_prose_geom_upper"]
    assert hop_curve[0]["free_prose_geom_upper"] > hop_curve[0]["single_pass_answer_first_json_mode"]
    assert hop_curve[5]["free_prose_geom_upper"] < hop_curve[5]["single_pass_answer_first_json_mode"]

    # 4C. Declarative 6-stage GSM lifecycle with topological PDG evaluation (zero scripted reset lists!)
    stage_names = tuple(f"Stage_{i}" for i in range(1, 7))
    all_stages = ("PipelineRoot",) + stage_names
    substages = {"PipelineRoot": stage_names}
    owns = {f"Stage_{i}": (f"M{i}_ok", f"M{i}_blocked") for i in range(1, 7)}

    explicit_rules: list[PACRule] = [
        # Root guards
        PACRule(
            rule_id="guard_open_root",
            target_kind="stage",
            target_name="PipelineRoot",
            target_polarity=True,
            external_event="StartPipeline",
            prerequisite=lambda cur_s, _m: not cur_s["PipelineRoot"],
        ),
        PACRule(
            rule_id="guard_close_root",
            target_kind="stage",
            target_name="PipelineRoot",
            target_polarity=False,
            external_event="ClosePipeline",
            prerequisite=lambda cur_s, _m: cur_s["PipelineRoot"],
        ),
        # Stage_1 opens automatically when PipelineRoot opens
        PACRule(
            rule_id="guard_open_stage_1",
            target_kind="stage",
            target_name="Stage_1",
            target_polarity=True,
            internal_triggers=("+PipelineRoot",),
            prerequisite=lambda cur_s, _m: not cur_s["Stage_1"],
        ),
    ]

    for i in range(1, 7):
        stg = f"Stage_{i}"
        m_ok = f"M{i}_ok"
        m_blk = f"M{i}_blocked"

        # Achieving sentries for M{i}_ok and M{i}_blocked on external StageCompleted event
        explicit_rules.append(
            PACRule(
                rule_id=f"ach_{m_ok}",
                target_kind="milestone",
                target_name=m_ok,
                target_polarity=True,
                external_event="StageCompleted",
                prerequisite=lambda cur_s, cur_m, s=stg, m=m_ok: cur_s[s] and not cur_m[m],
                guard=lambda pre_s, _pm, ev, idx=i, s=stg: (
                    pre_s[s] and ev.get("stage") == idx and ev.get("outcome") == "ok"
                ),
            )
        )
        explicit_rules.append(
            PACRule(
                rule_id=f"ach_{m_blk}",
                target_kind="milestone",
                target_name=m_blk,
                target_polarity=True,
                external_event="StageCompleted",
                prerequisite=lambda cur_s, cur_m, s=stg, m=m_blk: cur_s[s] and not cur_m[m],
                guard=lambda pre_s, _pm, ev, idx=i, s=stg: (
                    pre_s[s] and ev.get("stage") == idx and ev.get("outcome") == "blocked"
                ),
            )
        )

        # Explicit repair re-opening guard on upstream stage when a downstream stage is blocked
        explicit_rules.append(
            PACRule(
                rule_id=f"guard_reopen_{stg}",
                target_kind="stage",
                target_name=stg,
                target_polarity=True,
                external_event="ReopenStageForRepair",
                prerequisite=lambda cur_s, _m, s=stg: cur_s["PipelineRoot"] and not cur_s[s],
                guard=lambda _ps, pre_m, ev, idx=i: (
                    ev.get("target_stage") == idx
                    and any(pre_m[f"M{k}_blocked"] for k in range(idx + 1, 7))
                ),
            )
        )

        if i >= 2:
            prev_ok = f"M{i - 1}_ok"
            # Forward sequential stage guard: achieving M{i-1}_ok opens Stage_{i}
            explicit_rules.append(
                PACRule(
                    rule_id=f"guard_seq_open_{stg}",
                    target_kind="stage",
                    target_name=stg,
                    target_polarity=True,
                    internal_triggers=(f"+{prev_ok}",),
                    prerequisite=lambda cur_s, _m, s=stg: cur_s["PipelineRoot"] and not cur_s[s],
                )
            )
            # Declarative downstream milestone invalidating sentries (Inv):
            # invalidating M{i-1}_ok cascades via PDG to invalidate M{i}_ok and M{i}_blocked!
            for downstream_m in (m_ok, m_blk):
                explicit_rules.append(
                    PACRule(
                        rule_id=f"inv_cascade_{prev_ok}_to_{downstream_m}",
                        target_kind="milestone",
                        target_name=downstream_m,
                        target_polarity=False,
                        internal_triggers=(f"-{prev_ok}",),
                        prerequisite=lambda _cs, cur_m, dm=downstream_m: cur_m[dm],
                    )
                )

    engine = DeclarativeGSMEngine(all_stages, substages, owns, explicit_rules)

    active_stages = {s: False for s in all_stages}
    milestones = {m: False for ms in owns.values() for m in ms}
    engine.verify_snapshot_invariants(active_stages, milestones)

    b_steps = 0
    # 1. Start pipeline -> opens PipelineRoot AND Stage_1 in one B-step
    b_steps += 1
    f1 = engine.execute_external_event(active_stages, milestones, "StartPipeline")
    assert f1 == {"+PipelineRoot", "+Stage_1"}

    # 2. Stages 1..3 complete ok -> each achieves M_i_ok, closes Stage_i, opens Stage_{i+1}
    for idx in (1, 2, 3):
        b_steps += 1
        engine.execute_external_event(
            active_stages, milestones, "StageCompleted", {"stage": idx, "outcome": "ok"}
        )
    assert active_stages["Stage_4"] and milestones["M1_ok"] and milestones["M2_ok"] and milestones["M3_ok"]

    # 3. Stage 4 discovers an obstacle -> achieves M4_blocked and closes Stage_4 (Stage_5 stays closed)
    b_steps += 1
    f_blk = engine.execute_external_event(
        active_stages, milestones, "StageCompleted", {"stage": 4, "outcome": "blocked"}
    )
    assert f_blk == {"+M4_blocked", "-Stage_4"} and not active_stages["Stage_5"]

    # 4. Single external event ReopenStageForRepair(target_stage=2) — NO caller reset list!
    #    Topological PDG cascade fires +Stage_2 -> -M2_ok (GSM-1) -> -M3_ok (Inv) -> -M4_blocked (Inv)!
    b_steps += 1
    f_reopen = engine.execute_external_event(
        active_stages, milestones, "ReopenStageForRepair", {"target_stage": 2}
    )
    assert f_reopen == {"+Stage_2", "-M2_ok", "-M3_ok", "-M4_blocked"}
    assert milestones["M1_ok"] and (not milestones["M2_ok"]) and (not milestones["M3_ok"])
    assert not milestones["M4_blocked"]

    # 5. Re-run Stages 2..6 to completion, then close PipelineRoot
    for idx in (2, 3, 4, 5, 6):
        b_steps += 1
        engine.execute_external_event(
            active_stages, milestones, "StageCompleted", {"stage": idx, "outcome": "ok"}
        )
    b_steps += 1
    engine.execute_external_event(active_stages, milestones, "ClosePipeline")
    assert not any(active_stages.values())
    assert all(milestones[f"M{i}_ok"] for i in range(1, 7))
    assert not any(milestones[f"M{i}_blocked"] for i in range(1, 7))

    # 6. Also verify GSM-2 parent-close cascade when PipelineRoot closes mid-substage
    abort_stages = {s: False for s in all_stages}
    abort_ms = {m: False for ms in owns.values() for m in ms}
    engine.execute_external_event(abort_stages, abort_ms, "StartPipeline")
    engine.execute_external_event(abort_stages, abort_ms, "StageCompleted", {"stage": 1, "outcome": "ok"})
    assert abort_stages["Stage_2"]
    f_abort = engine.execute_external_event(abort_stages, abort_ms, "ClosePipeline")
    assert f_abort == {"-PipelineRoot", "-Stage_2"} and not abort_stages["Stage_2"]

    return {
        "evidence_role": "normative + source + documentation + derived",
        "xml_fill_coerced_defaults": coerced,
        "xml_fill_required_list_str_crashes_create_class": required_generic_crashed,
        "xml_fill_optional_str_leaks_child_example": (
            optional_end_to_end["data_structures_and_interfaces"] == static_2048_template
        ),
        "metagpt_11cdf466_unbound_context_modes": broken_modes,
        "derived_parametric_handoff_model": {
            "model_kind": "derived_illustrative_parametric_model",
            "mohamed_table8_rephrasing_concave_h3_score": prose_concave_h3,
            "hop_1": hop_curve[0],
            "hop_3": hop_curve[2],
            "hop_6": hop_curve[5],
        },
        "declarative_gsm_pdg_acyclic": True,
        "declarative_gsm_pdg_edges": engine.pdg_edge_count,
        "declarative_gsm_reopen_cascade": sorted(f_reopen),
        "declarative_gsm_b_steps_verified": b_steps,
    }


def main() -> None:
    banner_specs = [
        (
            "PROBE 1",
            "probe_quickxplain_and_junker_duality",
            "normative + derived",
            probe_quickxplain_and_junker_duality,
        ),
        (
            "PROBE 2",
            "probe_marco_duality_and_wmaxsat_shadow_prices",
            "normative + source + derived",
            probe_marco_duality_and_wmaxsat_shadow_prices,
        ),
        (
            "PROBE 3",
            "probe_wrspm_obligations_and_kaos_refinement",
            "normative + derived",
            probe_wrspm_obligations_and_kaos_refinement,
        ),
        (
            "PROBE 4",
            "probe_metagpt_fill_defects_and_declarative_gsm",
            "normative + source + documentation + derived",
            probe_metagpt_fill_defects_and_declarative_gsm,
        ),
    ]

    results: dict[str, Any] = {}
    for code, fn_name, ev_role, fn in banner_specs:
        print(f"=== [{code}] {fn_name} | [evidence_role: {ev_role}] ===")
        results[fn_name] = fn()

    payload = json.dumps(results, indent=2, sort_keys=True)
    digest_full = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    print(
        f"=== ALL 4 VERIFICATION PROBES PASSED DETERMINISTICALLY "
        f"(payload_sha256_12={digest_full[:12]}, payload_sha256={digest_full}) ==="
    )
    print(payload)


if __name__ == "__main__":
    main()
