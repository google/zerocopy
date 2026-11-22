#!/usr/bin/env python3
"""Deterministic Python 3.10+ stdlib verification probes for syntactic and
equational anti-unification, top-down library compression, rare-token clone
filtering, reuse break-even amortization, and concurrent helper scheduling:

1. Syntactic AST anti-unification (Plotkin 1970; Reynolds 1970) + Stitch
   branch-and-bound top-down library learner (Bowers et al., POPL 2023,
   Eqs. 8-15 & Footnote 2; mlb2251/stitch@350804b7b3), comparing paper Eq. 14
   vs. Rust tighter upper bounds, dual-adversarial self-overlapping DP against
   greedy top-down/bottom-up and brute-force independent-set enumeration, and
   automatic inverse_argument_capture recovery.
2. Pairwise 2-way (Id, Id) DFTA equational anti-unification with conditional
   holes (upstream dcao/babble@115f920db5 src/dfta.rs:93-112,
   src/learn.rs:105-130, 300-306) vs. generalized m-way all-hole product-DFTA
   anti-unification, showing decomposed DSR-simplification vs. library CRs,
   single-round pairwise incompleteness on h(a,a,b), h(a,b,a), h(b,a,a), and
   finitary commutativity C(+) minimal complete sets (Cerna & Kutsia 2023).
3. SourcererCC rare-token partial-index and positional upper-bound filter
   exactness (Sajnani et al., ICSE 2016; Mondego/SourcererCC@88314f51fd) in
   compressed (token, freq) form across Zipfian and high-collision multiset
   bags—comparing upstream CloneValidator.java:112-117 frozen
   candidateMatchPosition against tighter per-frame advancement—plus complete
   Juergens et al. (ICSE 2009) Table 1-2 fault/density audit.
4. Exact rational Rule-of-Three reuse break-even k*, boolean-flag quadratic
   coupling window [k_min*, k_max*], premature argument-capture p_wrong(m)
   under non-degeneracy (max_v P_j(v) < 1), uniform i.i.d. shared-vocabulary
   parameter aliasing, and distribution-free Pigeonhole impossibility (r > V^m - V).
5. Symmetric-integration, symmetric-beta, and symmetric-API-comprehension
   concurrent Producer/Consumer helper scheduling across matched k-worker
   (in-band) and (k+1)-worker (dedicated) topologies, active compute vs.
   wall-slot-hours, and the two-regime non-concave stochastic crossover law
   for E[min(T_{H,shared}, max_{1<=i<=k} T_{C,i})].
"""
from __future__ import annotations

import ast
import fractions
import heapq
import itertools
import json
import math
import random
from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple


# ============================================================================
# Probe 1: First-Order / Python-AST Anti-Unification & Stitch B&B Compressor
# ============================================================================

@dataclass(frozen=True)
class Term:
    op: str
    args: Tuple["Term", ...] = ()

    def size(self) -> int:
        return 1 + sum(a.size() for a in self.args)

    def is_hole(self) -> bool:
        return self.op == "??"

    def is_avar(self) -> bool:
        return self.op.startswith("#")

    def pretty(self) -> str:
        if not self.args:
            return self.op
        return f"({self.op} " + " ".join(a.pretty() for a in self.args) + ")"


def py_expr_to_term(src: str) -> Term:
    node = ast.parse(src.strip(), mode="eval").body

    def conv(n: ast.AST) -> Term:
        if isinstance(n, ast.BinOp):
            return Term(type(n.op).__name__, (conv(n.left), conv(n.right)))
        if isinstance(n, ast.UnaryOp):
            return Term(type(n.op).__name__, (conv(n.operand),))
        if isinstance(n, ast.Call):
            fn = n.func.id if isinstance(n.func, ast.Name) else ast.unparse(n.func)
            return Term(f"call:{fn}", tuple(conv(a) for a in n.args))
        if isinstance(n, ast.Name):
            return Term(f"var:{n.id}")
        if isinstance(n, ast.Constant):
            return Term(f"const:{repr(n.value)}")
        if isinstance(n, ast.Subscript):
            return Term("index", (conv(n.value), conv(n.slice)))
        raise ValueError(f"Unsupported AST node: {type(n)}")

    return conv(node)


def lgg_many(terms: Sequence[Term]) -> Tuple[Term, List[Dict[str, Term]]]:
    """Plotkin (1970) / Reynolds (1970) syntactic least general generalization
    over m >= 1 terms using injective disagreement table phi."""
    if not terms:
        raise ValueError("lgg_many requires at least one term")
    if len(terms) == 1:
        return terms[0], [{}]
    phi: Dict[Tuple[Term, ...], str] = {}
    substs: List[Dict[str, Term]] = [{} for _ in terms]

    def go(tup: Tuple[Term, ...]) -> Term:
        first = tup[0]
        if all(t.op == first.op and len(t.args) == len(first.args) for t in tup[1:]):
            return Term(first.op, tuple(go(tuple(t.args[i] for t in tup)) for i in range(len(first.args))))
        if tup not in phi:
            v = f"#{len(phi)}"
            phi[tup] = v
            for idx, sub in enumerate(tup):
                substs[idx][v] = sub
        return Term(phi[tup])

    return go(tuple(terms)), substs


def apply_subst(pattern: Term, subst: Dict[str, Term]) -> Term:
    if pattern.is_avar() and pattern.op in subst:
        return subst[pattern.op]
    return Term(pattern.op, tuple(apply_subst(a, subst) for a in pattern.args))


COST_APP = 1
COST_PRIM = 100
COST_ABS = 100


def stitch_cost(t: Term, star: bool = False) -> int:
    if t.is_avar():
        return 0 if star else COST_ABS
    if t.is_hole():
        return 0
    return COST_PRIM + len(t.args) * COST_APP + sum(stitch_cost(a, star=star) for a in t.args)


def match_pattern(pat: Term, expr: Term, env: Optional[Dict[str, Term]] = None) -> Optional[Dict[str, Term]]:
    if env is None:
        env = {}
    if pat.is_hole():
        return env
    if pat.is_avar():
        if pat.op in env:
            return env if env[pat.op] == expr else None
        out = dict(env)
        out[pat.op] = expr
        return out
    if pat.op != expr.op or len(pat.args) != len(expr.args):
        return None
    cur = env
    for pa, ea in zip(pat.args, expr.args):
        cur = match_pattern(pa, ea, cur)
        if cur is None:
            return None
    return cur


def count_avar_usages(pat: Term) -> Dict[str, int]:
    counts: Dict[str, int] = {}

    def walk(t: Term) -> None:
        if t.is_avar():
            counts[t.op] = counts.get(t.op, 0) + 1
        for a in t.args:
            walk(a)

    walk(pat)
    return counts


def ordered_avars(pat: Term) -> List[str]:
    seen: List[str] = []

    def walk(t: Term) -> None:
        if t.is_avar() and t.op not in seen:
            seen.append(t.op)
        for a in t.args:
            walk(a)

    walk(pat)
    return seen


def arity_of(pat: Term) -> int:
    return len(count_avar_usages(pat))


def dp_optimal_rewrite_and_utility(pat: Term, corpus: Sequence[Term]) -> Tuple[int, List[Term], int]:
    """Exact Stitch Sec. 4.4 bottom-up DP optimal non-overlapping rewrite (Eq. 15)
    cross-checked against local utility decomposition (Eqs. 11-12) and Eq. 8."""
    avars = ordered_avars(pat)
    usages = count_avar_usages(pat)
    arity = len(avars)
    cost_star_a = stitch_cost(pat, star=True)
    cost_a = stitch_cost(pat, star=False)

    total_local_gain = 0
    rewritten_corpus: List[Term] = []
    chosen_sites = 0

    for root in corpus:
        def solve(e: Term) -> Tuple[int, Term, int]:
            child_res = [solve(c) for c in e.args]
            util_r = sum(r[0] for r in child_res)
            rew_r = Term(e.op, tuple(r[1] for r in child_res))
            sites_r = sum(r[2] for r in child_res)

            m = match_pattern(pat, e)
            if m is None:
                return util_r, rew_r, sites_r

            multiuse = sum((usages[v] - 1) * stitch_cost(m[v]) for v in avars)
            u_local = cost_star_a - (COST_PRIM + COST_APP * arity) + multiuse
            arg_solves = [solve(m[v]) for v in avars]
            util_a = u_local + sum(s[0] for s in arg_solves)
            if util_a > util_r:
                rew_a = Term("call:fn_0", tuple(s[1] for s in arg_solves))
                return util_a, rew_a, 1 + sum(s[2] for s in arg_solves)
            return util_r, rew_r, sites_r

        gain, rew_tree, n_sites = solve(root)
        total_local_gain += gain
        rewritten_corpus.append(rew_tree)
        chosen_sites += n_sites

    global_util = -cost_a + total_local_gain
    orig_cost = sum(stitch_cost(p) for p in corpus)
    new_cost = sum(stitch_cost(p) for p in rewritten_corpus)
    assert global_util == -cost_a + (orig_cost - new_cost)
    return global_util, rewritten_corpus, chosen_sites


def greedy_top_down_rewrite_utility(pat: Term, corpus: Sequence[Term]) -> Tuple[int, int]:
    """Greedy top-down rewrite baseline (rewrites topmost positive-local-gain match)."""
    avars = ordered_avars(pat)
    usages = count_avar_usages(pat)
    arity = len(avars)
    cost_star_a = stitch_cost(pat, star=True)
    cost_a = stitch_cost(pat, star=False)

    sites = 0
    rew_corpus: List[Term] = []
    for root in corpus:
        def go(e: Term) -> Term:
            nonlocal sites
            m = match_pattern(pat, e)
            if m is not None:
                multiuse = sum((usages[v] - 1) * stitch_cost(m[v]) for v in avars)
                u_local = cost_star_a - (COST_PRIM + COST_APP * arity) + multiuse
                if u_local > 0:
                    sites += 1
                    return Term("call:fn_0", tuple(go(m[v]) for v in avars))
            return Term(e.op, tuple(go(c) for c in e.args))

        rew_corpus.append(go(root))

    orig_cost = sum(stitch_cost(p) for p in corpus)
    new_cost = sum(stitch_cost(p) for p in rew_corpus)
    return -cost_a + (orig_cost - new_cost), sites


def greedy_bottom_up_rewrite_utility(pat: Term, corpus: Sequence[Term]) -> Tuple[int, int]:
    """Greedy bottom-up rewrite baseline (rewrites children before checking parent)."""
    avars = ordered_avars(pat)
    usages = count_avar_usages(pat)
    arity = len(avars)
    cost_star_a = stitch_cost(pat, star=True)
    cost_a = stitch_cost(pat, star=False)

    sites = 0
    rew_corpus: List[Term] = []
    for root in corpus:
        def go(e: Term) -> Term:
            nonlocal sites
            rew_e = Term(e.op, tuple(go(c) for c in e.args))
            m = match_pattern(pat, rew_e)
            if m is not None:
                multiuse = sum((usages[v] - 1) * stitch_cost(m[v]) for v in avars)
                u_local = cost_star_a - (COST_PRIM + COST_APP * arity) + multiuse
                if u_local > 0:
                    sites += 1
                    return Term("call:fn_0", tuple(m[v] for v in avars))
            return rew_e

        rew_corpus.append(go(root))

    orig_cost = sum(stitch_cost(p) for p in corpus)
    new_cost = sum(stitch_cost(p) for p in rew_corpus)
    return -cost_a + (orig_cost - new_cost), sites


def brute_force_optimal_rewrite_utility(pat: Term, corpus: Sequence[Term]) -> int:
    """Independent exponential oracle enumerating all valid non-overlapping rewrite
    decisions on small trees to verify Eq. 15 DP optimality without circularity."""
    avars = ordered_avars(pat)
    cost_a = stitch_cost(pat, star=False)

    def all_rewrites(e: Term) -> Set[Term]:
        child_sets = [all_rewrites(c) for c in e.args]
        out: Set[Term] = {Term(e.op, prod) for prod in itertools.product(*child_sets)}
        m = match_pattern(pat, e)
        if m is not None:
            arg_sets = [all_rewrites(m[v]) for v in avars]
            for prod in itertools.product(*arg_sets):
                out.add(Term("call:fn_0", prod))
        return out

    orig_cost = sum(stitch_cost(p) for p in corpus)
    min_new_cost = sum(min(stitch_cost(r) for r in all_rewrites(p)) for p in corpus)
    return -cost_a + (orig_cost - min_new_cost)


def inverse_argument_capture_pass(
    pat: Term,
    corpus: Sequence[Term],
    max_arity: int = 4,
) -> Tuple[Term, int]:
    """Post-hoc inverse_argument_capture (mlb2251/stitch@350804b7b3
    src/compression.rs:1669-1707, enabled under --inv-arg-cap): lifts repeated
    invariant subtrees e out of a finished abstraction body whenever
    -(cost(e) + cost_app) * r + (cost(e) - cost_abs) * u > 0."""
    cur_pat = pat
    cur_util, _, cur_sites = dp_optimal_rewrite_and_utility(cur_pat, corpus)

    while arity_of(cur_pat) < max_arity and cur_sites > 0:
        sub_counts: Dict[Term, int] = {}

        def count_subs(t: Term) -> None:
            if t.is_avar() or t.is_hole():
                return
            if not count_avar_usages(t):
                sub_counts[t] = sub_counts.get(t, 0) + 1
            for a in t.args:
                count_subs(a)

        for child in cur_pat.args:
            count_subs(child)

        best_cand: Optional[Tuple[int, str, Term]] = None
        for sub, u_cnt in sub_counts.items():
            c_e = stitch_cost(sub)
            if u_cnt > cur_sites and c_e > COST_ABS:
                delta = -(c_e + COST_APP) * cur_sites + (c_e - COST_ABS) * u_cnt
                if delta > 0:
                    cand_key = (delta, sub.pretty())
                    if best_cand is None or cand_key > (best_cand[0], best_cand[1]):
                        best_cand = (delta, sub.pretty(), sub)

        if best_cand is None:
            break

        target_sub = best_cand[2]
        next_var = Term(f"#{arity_of(cur_pat)}")

        def lift_sub(t: Term) -> Term:
            if t == target_sub:
                return next_var
            return Term(t.op, tuple(lift_sub(a) for a in t.args))

        lifted_pat = Term(cur_pat.op, tuple(lift_sub(a) for a in cur_pat.args))
        lifted_util, _, lifted_sites = dp_optimal_rewrite_and_utility(lifted_pat, corpus)
        if lifted_util <= cur_util:
            break
        cur_pat, cur_util, cur_sites = lifted_pat, lifted_util, lifted_sites

    return cur_pat, cur_util


def stitch_top_down_search(
    corpus: Sequence[Term],
    max_arity: int = 3,
    ub_mode: str = "rust_tight",
    prune_single_task: bool = False,
) -> Tuple[Optional[Term], int, int]:
    """Top-down corpus-guided branch-and-bound search (Bowers et al., POPL 2023,
    Secs. 3-4; mlb2251/stitch@350804b7b3 src/compression.rs, src/pattern_args.rs):
    - ub_mode in {'none', 'paper_eq14', 'rust_tight'};
    - applies redundant-argument pruning during partial-pattern expansion;
    - prunes single match location (< 2 sites) by default, matching Stitch."""
    if ub_mode not in ("none", "paper_eq14", "rust_tight"):
        raise ValueError(f"Unsupported ub_mode: {ub_mode}")

    all_subterms: List[Tuple[int, int, Term]] = []
    sid_counter = 0
    for tid, root in enumerate(corpus):
        def collect(n: Term) -> None:
            nonlocal sid_counter
            all_subterms.append((tid, sid_counter, n))
            sid_counter += 1
            for a in n.args:
                collect(a)
        collect(root)

    def first_hole_path(t: Term) -> Optional[Tuple[int, ...]]:
        if t.is_hole():
            return ()
        for idx, a in enumerate(t.args):
            sub = first_hole_path(a)
            if sub is not None:
                return (idx,) + sub
        return None

    def get_at_path(t: Term, path: Tuple[int, ...]) -> Optional[Term]:
        cur = t
        for idx in path:
            if idx >= len(cur.args):
                return None
            cur = cur.args[idx]
        return cur

    def replace_at_path(t: Term, path: Tuple[int, ...], repl: Term) -> Term:
        if not path:
            return repl
        idx = path[0]
        new_args = list(t.args)
        new_args[idx] = replace_at_path(new_args[idx], path[1:], repl)
        return Term(t.op, tuple(new_args))

    def matching_sites(pat: Term) -> List[Tuple[int, int, Term, Dict[str, Term]]]:
        out = []
        for tid, sid, sub in all_subterms:
            m = match_pattern(pat, sub)
            if m is not None:
                out.append((tid, sid, sub, m))
        return out

    def has_sufficient_support(sites: Sequence[Tuple[int, int, Term, Dict[str, Term]]]) -> bool:
        if len(sites) < 2:
            return False
        if prune_single_task and len({tid for tid, _, _, _ in sites}) < 2:
            return False
        return True

    def is_redundant_or_captured(
        avars: Sequence[str],
        sites: Sequence[Tuple[int, int, Term, Dict[str, Term]]],
        check_capture: bool,
    ) -> bool:
        if check_capture and any(len({m[v] for _, _, _, m in sites}) == 1 for v in avars):
            return True
        return any(
            all(m[avars[i]] == m[avars[j]] for _, _, _, m in sites)
            for i in range(len(avars))
            for j in range(i + 1, len(avars))
        )

    def upper_bound(sites: Sequence[Tuple[int, int, Term, Dict[str, Term]]]) -> int:
        if ub_mode == "rust_tight":
            return sum(max(0, stitch_cost(sub) - COST_PRIM) for _, _, sub, _ in sites)
        return sum(stitch_cost(sub) for _, _, sub, _ in sites)

    use_ub = ub_mode != "none"
    best_pat: Optional[Term] = None
    best_util = 0
    explored = 0
    counter = 0

    root_hole = Term("??")
    root_sites = matching_sites(root_hole)
    pq: List[Tuple[int, int, Term]] = [(-upper_bound(root_sites), counter, root_hole)]
    seen_completed: Set[str] = set()

    while pq:
        neg_ub, _, pat = heapq.heappop(pq)
        ub = -neg_ub
        if use_ub and ub <= best_util:
            continue
        explored += 1
        sites = matching_sites(pat)
        if not has_sufficient_support(sites):
            continue

        avars = ordered_avars(pat)
        path = first_hole_path(pat)
        if is_redundant_or_captured(avars, sites, check_capture=True):
            continue

        if path is None:
            key = pat.pretty()
            if key in seen_completed:
                continue
            seen_completed.add(key)
            u, _, _ = dp_optimal_rewrite_and_utility(pat, corpus)
            assert u <= ub, f"Admissibility violated: {u} > {ub} for {key}"
            if u > best_util or (u == best_util and (best_pat is None or key < best_pat.pretty())):
                best_util = u
                best_pat = pat
            continue

        constructors: Set[Tuple[str, int]] = set()
        for _, _, sub, _ in sites:
            focus = get_at_path(sub, path)
            if focus is not None:
                constructors.add((focus.op, len(focus.args)))

        next_candidates: List[Term] = []
        for op, ar in sorted(constructors):
            next_candidates.append(replace_at_path(pat, path, Term(op, tuple(Term("??") for _ in range(ar)))))
        for existing_v in avars:
            next_candidates.append(replace_at_path(pat, path, Term(existing_v)))
        if len(avars) < max_arity and path != ():
            next_candidates.append(replace_at_path(pat, path, Term(f"#{len(avars)}")))

        for cand in next_candidates:
            csites = matching_sites(cand)
            if not has_sufficient_support(csites):
                continue
            cavars = ordered_avars(cand)
            if is_redundant_or_captured(cavars, csites, check_capture=True):
                continue
            cub = upper_bound(csites)
            assert cub <= ub
            if use_ub and cub <= best_util:
                continue
            counter += 1
            heapq.heappush(pq, (-cub, counter, cand))

    return best_pat, best_util, explored


def run_probe_1() -> dict:
    # 1. Syntactic lgg properties: soundness, size contraction, relational repeat-var, m=2->3
    rel_t1 = py_expr_to_term("f(a, g(a, b))")
    rel_t2 = py_expr_to_term("f(c, g(c, d))")
    rel_lgg, rel_substs = lgg_many([rel_t1, rel_t2])
    assert rel_lgg.pretty() == "(call:f #0 (call:g #0 #1))"
    assert apply_subst(rel_lgg, rel_substs[0]) == rel_t1
    assert apply_subst(rel_lgg, rel_substs[1]) == rel_t2

    py_snippets = [
        "clamp(normalize(row['latency'], 0.0, 100.0) * weight_a, 0.0, 1.0)",
        "clamp(normalize(row['tokens'], 0.0, 500.0) * weight_b, 0.0, 1.0)",
        "clamp(normalize(item['cost'], 0.0, 250.0) * factor_c, 0.0, 1.0)",
    ]
    terms = [py_expr_to_term(s) for s in py_snippets]
    gen2, _ = lgg_many(terms[:2])
    gen3, substs3 = lgg_many(terms)
    for t, sb in zip(terms, substs3):
        assert apply_subst(gen3, sb) == t
    assert gen3.size() <= min(t.size() for t in terms)
    arity_m2 = arity_of(gen2)
    arity_m3 = arity_of(gen3)
    assert arity_m2 == 3 and arity_m3 == 4

    # 2. Stitch B&B search across no-UB, paper Eq. 14 UB, and Rust tight UB
    b_corpus = [
        py_expr_to_term("wrap(norm(x1 + 1, s1) + bias) + seq(h(h(a1)), h(h(b1)), h(h(c1)))"),
        py_expr_to_term("wrap(norm(x2 + 1, s2) + bias) + seq(h(h(a2)), h(h(b2)), h(h(c2)))"),
        py_expr_to_term("wrap(norm(x3 + 1, s3) + bias) + tup(p(p(a1)), p(p(b1)), p(p(c1)))"),
        py_expr_to_term("wrap(norm(x4 + 1, s4) + bias) + tup(p(p(a2)), p(p(b2)), p(p(c2)))"),
        py_expr_to_term("wrap(norm(x5 + 1, s5) + bias) + rec(q(q(a1)), q(q(b1)), q(q(c1)))"),
        py_expr_to_term("wrap(norm(x6 + 1, s6) + bias) + rec(q(q(a2)), q(q(b2)), q(q(c2)))"),
        py_expr_to_term("wrap(norm(x7 + 1, s7) + bias)"),
        py_expr_to_term("wrap(norm(x8 + 1, s8) + bias)"),
        py_expr_to_term("wrap(norm(x9 + 1, s9) + bias)"),
        py_expr_to_term("wrap(norm(x10 + 1, s10) + bias)"),
    ]
    p_tight, u_tight, n_tight = stitch_top_down_search(b_corpus, max_arity=3, ub_mode="rust_tight")
    p_eq14, u_eq14, n_eq14 = stitch_top_down_search(b_corpus, max_arity=3, ub_mode="paper_eq14")
    p_none, u_none, n_none = stitch_top_down_search(b_corpus, max_arity=3, ub_mode="none")
    assert p_tight is not None and p_tight == p_eq14 == p_none
    assert u_tight == u_eq14 == u_none == 4243
    assert n_tight <= n_eq14 < n_none and n_eq14 * 4 < n_none

    # 3a. Unary foo^5(bar): confirm greedy TD, greedy BU, and DP all tie (vacuous case)
    nested = py_expr_to_term("foo(foo(foo(foo(foo(bar)))))")
    pat_unary = Term("call:foo", (Term("call:foo", (Term("#0"),)),))
    u_unary_dp, _, sites_unary = dp_optimal_rewrite_and_utility(pat_unary, [nested, nested, nested])
    u_unary_td, _ = greedy_top_down_rewrite_utility(pat_unary, [nested, nested, nested])
    u_unary_bu, _ = greedy_bottom_up_rewrite_utility(pat_unary, [nested, nested, nested])
    assert sites_unary == 6 and u_unary_dp == u_unary_td == u_unary_bu

    # 3b. Dual-adversarial self-overlapping ASTs separating Eq. 15 DP from BOTH greedies
    def build_bin_tree(depth: int, leaf: Term) -> Term:
        if depth == 0:
            return leaf
        sub = build_bin_tree(depth - 1, leaf)
        return Term("call:b", (sub, sub))

    t3_distinct = py_expr_to_term(
        "b(b(b(v0, v1), b(v2, v3)), b(b(v4, v5), b(v6, v7)))"
    )
    pat_bin4 = Term(
        "call:b",
        (Term("call:b", (Term("#0"), Term("#1"))), Term("call:b", (Term("#2"), Term("#3")))),
    )
    corpus_td_fail = [t3_distinct, t3_distinct]
    u_td_dp, _, _ = dp_optimal_rewrite_and_utility(pat_bin4, corpus_td_fail)
    u_td_greedy_td, _ = greedy_top_down_rewrite_utility(pat_bin4, corpus_td_fail)
    u_td_oracle = brute_force_optimal_rewrite_utility(pat_bin4, corpus_td_fail)
    assert u_td_dp == u_td_oracle > u_td_greedy_td

    big_leaf = py_expr_to_term("h(k(c))")
    t3_sym_big = build_bin_tree(3, big_leaf)
    pat_mu4 = Term("call:b", (Term("call:b", (Term("#0"), Term("#0"))), Term("call:b", (Term("#0"), Term("#0")))))
    corpus_bu_fail = [t3_sym_big, t3_sym_big]
    u_bu_dp, _, _ = dp_optimal_rewrite_and_utility(pat_mu4, corpus_bu_fail)
    u_bu_greedy_bu, _ = greedy_bottom_up_rewrite_utility(pat_mu4, corpus_bu_fail)
    u_bu_oracle = brute_force_optimal_rewrite_utility(pat_mu4, corpus_bu_fail)
    assert u_bu_dp == u_bu_oracle > u_bu_greedy_bu
    # Both adversarial gaps are independently verified against brute_force_optimal_rewrite_utility:
    # greedy TD loses by 202/tree on pat_bin4 (-302 vs +102); greedy BU loses by 101/tree on pat_mu4 (3738 vs 3940).

    # 4. Footnote 2 & automatic inverse_argument_capture recovery
    prog = Term("call:f", (Term("call:g", (big_leaf, big_leaf)), Term("call:g", (big_leaf, big_leaf))))
    corpus_ic = [prog, prog]
    pat_captured = prog
    u_captured, _, _ = dp_optimal_rewrite_and_utility(pat_captured, corpus_ic)
    recovered_pat, u_inv_cap = inverse_argument_capture_pass(pat_captured, corpus_ic, max_arity=4)
    expected_pat = Term("call:f", (Term("call:g", (Term("#0"), Term("#0"))), Term("call:g", (Term("#0"), Term("#0")))))
    cost_e = stitch_cost(big_leaf)
    expected_delta = -(cost_e + COST_APP) * 2 + (cost_e - COST_ABS) * 4
    assert recovered_pat == expected_pat
    assert u_inv_cap - u_captured == expected_delta == 202

    return {
        "ast_lgg_arity_m2_vs_m3": [arity_m2, arity_m3],
        "ast_lgg_m2_captured_row": "var:row" in gen2.pretty() and "var:row" not in gen3.pretty(),
        "relational_repeat_var_lgg": rel_lgg.pretty(),
        "stitch_bb_best_pattern": p_tight.pretty(),
        "stitch_bb_best_utility": u_tight,
        "stitch_bb_nodes_rust_tight_vs_eq14_vs_none": [n_tight, n_eq14, n_none],
        "stitch_bb_pruning_speedup_eq14_x": round(n_none / n_eq14, 2),
        "stitch_bb_pruning_speedup_rust_tight_x": round(n_none / n_tight, 2),
        "unary_chain5_all_tie_utility": u_unary_dp,
        "overlap_td_suboptimal_greedy_vs_dp": [u_td_greedy_td, u_td_dp],
        "overlap_bu_suboptimal_greedy_vs_dp": [u_bu_greedy_bu, u_bu_dp],
        "inverse_arg_capture_u_captured": u_captured,
        "inverse_arg_capture_u_lifted": u_inv_cap,
        "inverse_arg_capture_exact_delta": expected_delta,
    }


# ============================================================================
# Probe 2: Pairwise (babble) vs. m-Way Product-DFTA AU & C(+) mcsg
# ============================================================================

class MiniEGraph:
    def __init__(self) -> None:
        self.parent: List[int] = []
        self.nodes: Dict[Tuple[str, Tuple[int, ...]], int] = {}
        self.class_nodes: Dict[int, Set[Tuple[str, Tuple[int, ...]]]] = {}

    def find(self, i: int) -> int:
        while self.parent[i] != i:
            self.parent[i] = self.parent[self.parent[i]]
            i = self.parent[i]
        return i

    def add_enode(self, op: str, children: Tuple[int, ...]) -> int:
        canon = (op, tuple(self.find(c) for c in children))
        if canon in self.nodes:
            return self.find(self.nodes[canon])
        cid = len(self.parent)
        self.parent.append(cid)
        self.nodes[canon] = cid
        self.class_nodes[cid] = {canon}
        return cid

    def add_term(self, t: Term) -> int:
        return self.add_enode(t.op, tuple(self.add_term(a) for a in t.args))

    def union(self, a: int, b: int) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        lo, hi = (ra, rb) if ra < rb else (rb, ra)
        self.parent[hi] = lo
        self.class_nodes[lo] |= self.class_nodes.pop(hi, set())
        return True

    def rebuild(self) -> None:
        changed = True
        while changed:
            changed = False
            new_nodes: Dict[Tuple[str, Tuple[int, ...]], int] = {}
            for (op, ch) in sorted(self.nodes.keys()):
                cid = self.nodes[(op, ch)]
                rc = self.find(cid)
                canon = (op, tuple(self.find(c) for c in ch))
                if canon in new_nodes:
                    prev = self.find(new_nodes[canon])
                    if prev != rc:
                        self.parent[max(prev, rc)] = min(prev, rc)
                        changed = True
                else:
                    new_nodes[canon] = rc
            self.nodes = {k: self.find(v) for k, v in new_nodes.items()}
            self.class_nodes = {}
            for k, v in self.nodes.items():
                self.class_nodes.setdefault(v, set()).add(k)

    def min_cost_term(self, cid: int, max_depth: int = 5) -> Term:
        def enum_terms(c: int, d: int) -> List[Term]:
            c = self.find(c)
            res: List[Term] = []
            for op, ch in sorted(self.class_nodes[c]):
                if not ch:
                    res.append(Term(op))
                elif d > 0:
                    for prod in itertools.product(*(enum_terms(x, d - 1) for x in ch)):
                        res.append(Term(op, prod))
            return res

        cands = enum_terms(cid, max_depth)
        return min(cands, key=lambda t: (stitch_cost(t), t.pretty()))


def saturate_arith(eg: MiniEGraph, steps: int = 4) -> None:
    for _ in range(steps):
        merges: List[Tuple[int, int]] = []
        snapshot = [(cid, sorted(enodes)) for cid, enodes in sorted(eg.class_nodes.items())]
        for cid, enodes in snapshot:
            for op, ch in enodes:
                if op in ("Add", "Mult") and len(ch) == 2:
                    merges.append((cid, eg.add_enode(op, (ch[1], ch[0]))))
                if op == "Mult" and len(ch) == 2:
                    for idx, other in ((0, 1), (1, 0)):
                        if ("const:1", ()) in eg.class_nodes.get(eg.find(ch[idx]), set()):
                            merges.append((cid, ch[other]))
                if op == "call:scale" and len(ch) == 2:
                    if ("const:1", ()) in eg.class_nodes.get(eg.find(ch[1]), set()):
                        merges.append((cid, ch[0]))
        any_merged = any([eg.union(a, b) for a, b in merges])
        eg.rebuild()
        if not any_merged:
            break


def _canonicalize_state_vars(t: Term) -> Term:
    mapping: Dict[str, str] = {}

    def walk(n: Term) -> Term:
        if n.op.startswith("__state_"):
            if n.op not in mapping:
                mapping[n.op] = f"#{len(mapping)}"
            return Term(mapping[n.op])
        return Term(n.op, tuple(walk(a) for a in n.args))

    return walk(t)


def babble_pairwise_dfta_au(eg: MiniEGraph, r1: int, r2: int, max_depth: int = 5) -> Set[Term]:
    """Exact upstream dcao/babble@115f920db5 binary (2-way) product DFTA
    (src/dfta.rs:93-112 Dfta::cross_over; src/learn.rs:105-130, 300-306):
    intersects pairs of e-classes (Id, Id) and emits PartialExpr::Hole(state)
    only when (same && different) || aus.is_empty()."""
    root_pair = (eg.find(r1), eg.find(r2))

    def raw_pair_au(
        state: Tuple[int, int],
        depth: int,
        seen: FrozenSet[Tuple[int, int]],
    ) -> List[Term]:
        c1, c2 = eg.find(state[0]), eg.find(state[1])
        state = (c1, c2)
        var_tok = f"__state_{c1}_{c2}"
        if depth <= 0 or state in seen:
            return [Term(var_tok)]
        nseen = seen | {state}

        enodes1 = sorted(eg.class_nodes.get(c1, set()))
        enodes2 = sorted(eg.class_nodes.get(c2, set()))
        same = False
        different = False
        aus: List[Term] = []

        for op1, ch1 in enodes1:
            for op2, ch2 in enodes2:
                if op1 == op2 and len(ch1) == len(ch2):
                    same = True
                    if not ch1:
                        aus.append(Term(op1))
                    else:
                        child_trees = [
                            raw_pair_au((ch1[pos], ch2[pos]), depth - 1, nseen)
                            for pos in range(len(ch1))
                        ]
                        for prod in itertools.product(*child_trees):
                            aus.append(Term(op1, prod))
                else:
                    different = True

        # Exact upstream hole emission condition (dcao/babble src/learn.rs:300-306)
        if (same and different) or not aus:
            aus.append(Term(var_tok))
        return aus

    return {_canonicalize_state_vars(t) for t in raw_pair_au(root_pair, max_depth, frozenset())}


def egraph_product_dfta_au(eg: MiniEGraph, roots: Sequence[int], max_depth: int = 5) -> Set[Term]:
    """Generalized m-way all-hole product-DFTA anti-unification across len(roots) >= 2
    e-classes (unconditionally admitting a state variable at every product state)."""
    root_tup = tuple(eg.find(r) for r in roots)

    def raw_au(state: Tuple[int, ...], depth: int, seen: FrozenSet[Tuple[int, ...]]) -> List[Term]:
        state = tuple(eg.find(c) for c in state)
        var_tok = "__state_" + "_".join(str(c) for c in state)
        out: List[Term] = [Term(var_tok)]
        if depth <= 0 or state in seen:
            return out
        nseen = seen | {state}

        by_op: List[Dict[Tuple[str, int], List[Tuple[int, ...]]]] = []
        for cid in state:
            d: Dict[Tuple[str, int], List[Tuple[int, ...]]] = {}
            for op, ch in sorted(eg.class_nodes.get(cid, set())):
                d.setdefault((op, len(ch)), []).append(ch)
            by_op.append(d)

        shared_sigs = sorted(set.intersection(*(set(d.keys()) for d in by_op)))
        for op, arity in shared_sigs:
            if arity == 0:
                out.append(Term(op))
            else:
                for ch_combo in itertools.product(*(d[(op, arity)] for d in by_op)):
                    child_states = [tuple(ch_combo[idx][pos] for idx in range(len(state))) for pos in range(arity)]
                    child_trees = [raw_au(cs, depth - 1, nseen) for cs in child_states]
                    for prod in itertools.product(*child_trees):
                        out.append(Term(op, prod))
        return out

    return {_canonicalize_state_vars(t) for t in raw_au(root_tup, max_depth, frozenset())}


def c_variants(t: Term) -> FrozenSet[Term]:
    """Deduplicated equivalence class [t]_C under commutativity of Add and Mult."""
    if not t.args:
        return frozenset({t})
    child_sets = [sorted(c_variants(a), key=lambda x: x.pretty()) for a in t.args]
    res: Set[Term] = set()
    for prod in itertools.product(*child_sets):
        res.add(Term(t.op, prod))
        if t.op in ("Add", "Mult") and len(prod) == 2 and prod[0] != prod[1]:
            res.add(Term(t.op, (prod[1], prod[0])))
    return frozenset(res)


def is_more_specific_syn(g1: Term, g2: Term) -> bool:
    return match_pattern(g2, g1) is not None


def is_more_specific_mod_c(g1: Term, g2: Term) -> bool:
    return any(match_pattern(g2, v) is not None for v in sorted(c_variants(g1), key=lambda x: x.pretty()))


def minimal_complete_set(cands: Set[Term], mod_c: bool = False) -> List[Term]:
    cmp_fn = is_more_specific_mod_c if mod_c else is_more_specific_syn
    lst = sorted(cands, key=lambda t: (-t.size(), arity_of(t), t.pretty()))
    kept: List[Term] = []
    for c in lst:
        if not any(cmp_fn(k, c) for k in kept):
            kept = [k for k in kept if not cmp_fn(c, k)]
            kept.append(c)
    return sorted(kept, key=lambda t: t.pretty())


def run_probe_2() -> dict:
    s_exprs = [
        "scale(poly(3), 1) + (2 * offset_a)",
        "(offset_b * 2) + poly(4)",
        "(2 * offset_c) + scale(poly(6), 1)",
    ]
    raw_terms = [py_expr_to_term(s) for s in s_exprs]
    syn_lgg, _ = lgg_many(raw_terms)
    syn_util, _, _ = dp_optimal_rewrite_and_utility(syn_lgg, raw_terms)

    eg = MiniEGraph()
    roots = [eg.add_term(t) for t in raw_terms]
    saturate_arith(eg, steps=4)

    # Pure DSR simplification baseline (0 learned abstractions)
    dsr_only_terms = [eg.min_cost_term(r, max_depth=4) for r in roots]
    orig_raw_cost = sum(stitch_cost(t) for t in raw_terms)
    dsr_only_cost = sum(stitch_cost(t) for t in dsr_only_terms)

    # Compare upstream 2-way pairwise DFTA union vs. generalized 3-way all-hole DFTA
    cands_pairwise_union: Set[Term] = set()
    for r_i, r_j in itertools.combinations(roots, 2):
        cands_pairwise_union |= babble_pairwise_dfta_au(eg, r_i, r_j, max_depth=5)
    cands_3way = egraph_product_dfta_au(eg, roots, max_depth=5)

    # Pre-enumerate bounded terms per root e-class once for fast candidate scoring
    def enum_root_terms(cid: int, depth: int = 4) -> List[Term]:
        cid = eg.find(cid)
        res: List[Term] = []
        for op, ch in sorted(eg.class_nodes[cid]):
            if not ch:
                res.append(Term(op))
            elif depth > 0:
                for prod in itertools.product(*(enum_root_terms(x, depth - 1) for x in ch)):
                    res.append(Term(op, prod))
        return res

    root_term_sets = [enum_root_terms(r, 4) for r in roots]

    def select_best_pattern(cand_pool: Set[Term]) -> Tuple[Optional[Term], int, int]:
        best_pat: Optional[Term] = None
        best_cost = dsr_only_cost
        best_util = 0
        for cand in sorted(cand_pool, key=lambda t: t.pretty()):
            if cand.is_avar():
                continue
            reps: List[Term] = []
            ok = True
            for r_terms in root_term_sets:
                matches = [t for t in r_terms if match_pattern(cand, t) is not None]
                if not matches:
                    ok = False
                    break
                reps.append(min(matches, key=lambda t: (stitch_cost(t), t.pretty())))
            if not ok:
                continue
            u_cand, rew_cand, _ = dp_optimal_rewrite_and_utility(cand, reps)
            tot_cost = stitch_cost(cand) + sum(stitch_cost(t) for t in rew_cand)
            if tot_cost < best_cost or (
                tot_cost == best_cost and best_pat is not None and cand.pretty() < best_pat.pretty()
            ):
                best_cost = tot_cost
                best_pat = cand
                best_util = u_cand
        return best_pat, best_cost, best_util

    best_pair_pat, best_pair_cost, best_pair_util = select_best_pattern(cands_pairwise_union)
    best_eau_pat, best_final_cost, best_eq_util = select_best_pattern(cands_3way)
    assert best_eau_pat is not None and best_pair_pat == best_eau_pat
    assert best_pair_cost == best_final_cost and best_pair_util == best_eq_util == 304

    cr_dsr_only = orig_raw_cost / dsr_only_cost
    cr_lib_over_dsr = dsr_only_cost / best_final_cost
    cr_total_vs_raw = orig_raw_cost / best_final_cost
    assert syn_util < 0 and best_eq_util > 0
    assert cr_dsr_only > 1.15 and cr_lib_over_dsr > 1.20 and cr_total_vs_raw > 1.45

    # Single-round pairwise 2-way DFTA boundary on h(a, a, b), h(a, b, a), h(b, a, a):
    # Every pair shares one ground slot 'a', so learn.rs:300-306 ((same && different) || aus.is_empty())
    # suppresses the hole at that slot and misses 3-way lgg h(#0, #1, #2) in a single round!
    eg_sym3 = MiniEGraph()
    sym3_terms = [
        py_expr_to_term("h(a, a, b)"),
        py_expr_to_term("h(a, b, a)"),
        py_expr_to_term("h(b, a, a)"),
    ]
    sym3_roots = [eg_sym3.add_term(t) for t in sym3_terms]
    pair_sym3_cands: Set[Term] = set()
    for r_i, r_j in itertools.combinations(sym3_roots, 2):
        pair_sym3_cands |= babble_pairwise_dfta_au(eg_sym3, r_i, r_j, max_depth=3)
    mway_sym3_cands = egraph_product_dfta_au(eg_sym3, sym3_roots, max_depth=3)
    lgg_sym3, _ = lgg_many(sym3_terms)

    pair_sym3_max_sites = max(
        sum(1 for t in sym3_terms if match_pattern(c, t) is not None)
        for c in pair_sym3_cands
        if not c.is_avar()
    )
    assert sorted(c.pretty() for c in pair_sym3_cands) == [
        "(call:h #0 #1 var:a)",
        "(call:h #0 var:a #1)",
        "(call:h var:a #0 #1)",
    ]
    assert pair_sym3_max_sites == 2
    assert lgg_sym3.pretty() == "(call:h #0 #1 #2)"
    assert lgg_sym3 in mway_sym3_cands
    assert sum(1 for t in sym3_terms if match_pattern(lgg_sym3, t) is not None) == 3

    # Finitary C(+) mcsg verification on pair(a + b, a) vs. pair(a + b, b)
    eg2 = MiniEGraph()
    t_c1 = py_expr_to_term("pair(a + b, a)")
    t_c2 = py_expr_to_term("pair(a + b, b)")
    c_r1 = eg2.add_term(t_c1)
    c_r2 = eg2.add_term(t_c2)
    saturate_arith(eg2, steps=2)
    raw_cands = egraph_product_dfta_au(eg2, [c_r1, c_r2], max_depth=4)
    mcs_syn = minimal_complete_set(raw_cands, mod_c=False)
    mcs_mod_c = minimal_complete_set(raw_cands, mod_c=True)
    assert len(mcs_syn) == 4 and len(mcs_mod_c) == 2
    for g in mcs_mod_c:
        assert is_more_specific_mod_c(t_c1, g) and is_more_specific_mod_c(t_c2, g)
    assert not is_more_specific_mod_c(mcs_mod_c[0], mcs_mod_c[1])
    assert not is_more_specific_mod_c(mcs_mod_c[1], mcs_mod_c[0])

    return {
        "syntactic_lgg_pattern": syn_lgg.pretty(),
        "syntactic_lgg_utility": syn_util,
        "babble_learned_eau_pattern": best_eau_pat.pretty(),
        "babble_pairwise_matches_3way_on_arith": best_pair_pat == best_eau_pat,
        "babble_eau_utility_over_dsr": best_eq_util,
        "cr_dsr_simplification_only": round(cr_dsr_only, 4),
        "cr_library_over_dsr_normal_form": round(cr_lib_over_dsr, 4),
        "cr_total_babble_vs_raw": round(cr_total_vs_raw, 4),
        "pairwise_sym3_single_round_cands": sorted(c.pretty() for c in pair_sym3_cands),
        "pairwise_sym3_max_sites_vs_3way": [pair_sym3_max_sites, 3],
        "c_commutativity_dfta_syntactic_reps": len(mcs_syn),
        "c_commutativity_mod_C_mcs_count": len(mcs_mod_c),
        "c_commutativity_mod_C_mcs": [m.pretty() for m in mcs_mod_c],
    }


# ============================================================================
# Probe 3: SourcererCC Compressed Partial-Index/Positional Filter & Juergens
# ============================================================================

def verify_sourcerercc_compressed_index(
    raw_bags: Sequence[Sequence[str]],
    thetas: Sequence[str],
) -> Dict[str, dict]:
    """Exact SourcererCC compressed (token_id, freq) partial index + positional
    upper-bound filter (BlockInfo.java:11-45, Util.java:161-167,
    CloneValidator.java:97-158) using exact rational thresholds.
    Verifies BOTH upstream CloneValidator.java:112-117 (which passes the frozen
    prefix simInfo.candidateMatchPosition from TermSearcher.java:108) AND the
    tighter per-frame positional bound (advancing c_ms = c_seen_prev on every
    suffix frame), confirming 0 FN and 0 FP for both."""
    corpus_tok_freq: Dict[str, int] = {}
    for b in raw_bags:
        for tok in b:
            corpus_tok_freq[tok] = corpus_tok_freq.get(tok, 0) + 1

    ordered_vocab = sorted(corpus_tok_freq.keys(), key=lambda tok: (corpus_tok_freq[tok], tok))
    tok_to_rank = {tok: idx for idx, tok in enumerate(ordered_vocab)}

    comp_bags: List[Tuple[int, List[Tuple[int, int]], Dict[int, int]]] = []
    for b in raw_bags:
        counts: Dict[int, int] = {}
        for tok in b:
            rk = tok_to_rank[tok]
            counts[rk] = counts.get(rk, 0) + 1
        frames = sorted(counts.items())
        comp_bags.append((len(b), frames, counts))

    n = len(comp_bags)
    all_pairs = n * (n - 1) // 2
    naive_frame_comps = sum(len(comp_bags[i][1]) + len(comp_bags[j][1]) for i in range(n) for j in range(i + 1, n))

    # Precompute exact ground-truth pairwise bag overlaps directly via multiset intersection
    pair_overlaps: List[Tuple[int, int, int, int]] = []
    for i in range(n):
        sz_i, _, cnt_i = comp_bags[i]
        keys_i = cnt_i.keys()
        for j in range(i + 1, n):
            sz_j, _, cnt_j = comp_bags[j]
            shared = keys_i & cnt_j.keys()
            if shared:
                ov = sum(cnt_i[rk] if cnt_i[rk] < cnt_j[rk] else cnt_j[rk] for rk in shared)
                pair_overlaps.append((i, j, sz_i if sz_i > sz_j else sz_j, ov))

    total_tokens = sum(sz for sz, _, _ in comp_bags)
    max_bag_sz = max(sz for sz, _, _ in comp_bags)
    out: Dict[str, dict] = {}

    for th_str in thetas:
        th_q = fractions.Fraction(th_str)
        ceil_th = [math.ceil(th_q * sz) for sz in range(max_bag_sz + 1)]
        floor_div_th = [math.floor(fractions.Fraction(sz) / th_q) for sz in range(max_bag_sz + 1)]

        gt_clones: Set[Tuple[int, int]] = {
            (i, j) for (i, j, max_sz, ov) in pair_overlaps if ov >= ceil_th[max_sz]
        }

        inv_index: Dict[int, List[Tuple[int, int, int]]] = {}
        indexed_tokens = 0
        q_prefix_maps: List[Tuple[int, Dict[int, Tuple[int, int]], Dict[int, Tuple[int, int]]]] = []

        for bid, (sz, frames, _) in enumerate(comp_bags):
            comp_th = ceil_th[sz]
            pref_tokens_target = sz - comp_th + 1
            seen = 0
            pref_map: Dict[int, Tuple[int, int]] = {}
            suff_map: Dict[int, Tuple[int, int]] = {}
            for rk, fq in frames:
                if seen < pref_tokens_target:
                    seen += fq
                    indexed_tokens += fq
                    inv_index.setdefault(rk, []).append((bid, seen, fq))
                    pref_map[rk] = (seen, fq)
                else:
                    seen += fq
                    suff_map[rk] = (seen, fq)
            q_prefix_maps.append((pref_tokens_target, pref_map, suff_map))

        found_upstream: Set[Tuple[int, int]] = set()
        found_tight: Set[Tuple[int, int]] = set()
        cand_pairs_evaluated = 0
        scc_frame_comps_upstream = 0
        scc_frame_comps_tight = 0

        for qid, (q_sz, q_frames, _) in enumerate(comp_bags):
            min_len = ceil_th[q_sz]
            max_len = floor_div_th[q_sz]
            pref_target, q_pref_map, q_suff_map = q_prefix_maps[qid]

            cands: Dict[int, List[int]] = {}
            q_seen = 0
            for rk, q_fq in q_frames:
                if q_seen >= pref_target:
                    break
                q_seen += q_fq
                for cid, c_seen, c_fq in inv_index.get(rk, ()):
                    if cid <= qid:
                        continue
                    c_sz = comp_bags[cid][0]
                    if c_sz < min_len or c_sz > max_len:
                        continue
                    req = ceil_th[q_sz if q_sz > c_sz else c_sz]
                    inc = q_fq if q_fq < c_fq else c_fq
                    st = cands.get(cid)
                    if st is None:
                        if inc + min(q_sz - q_seen, c_sz - c_seen) >= req:
                            cands[cid] = [inc, q_seen, c_seen]
                    else:
                        new_sim = st[0] + inc
                        if new_sim + min(q_sz - q_seen, c_sz - c_seen) >= req:
                            st[0] = new_sim
                            st[1] = q_seen
                            st[2] = c_seen
                        else:
                            del cands[cid]

            for cid, (sim0, q_match_seen, c_match_seen) in cands.items():
                cand_pairs_evaluated += 1
                c_sz, c_frames, _ = comp_bags[cid]
                req = ceil_th[q_sz if q_sz > c_sz else c_sz]
                if sim0 >= req:
                    found_upstream.add((qid, cid))
                    found_tight.add((qid, cid))
                    continue

                # 1. Upstream CloneValidator.java:112-117 (frozen c_match_seen in isSatisfyPosFilter)
                sim_u = sim0
                q_ms_u = q_match_seen
                c_seen_cur = 0
                for rk, c_fq in c_frames:
                    c_seen_cur += c_fq
                    if c_seen_cur <= c_match_seen:
                        continue
                    scc_frame_comps_upstream += 1
                    if sim_u + min(q_sz - q_ms_u, c_sz - c_match_seen) < req:
                        break
                    info = q_pref_map.get(rk) if q_ms_u < pref_target else None
                    if info is None:
                        info = q_suff_map.get(rk)
                    if info is not None:
                        q_ms_u = info[0]
                        sim_u += info[1] if info[1] < c_fq else c_fq
                        if sim_u >= req:
                            found_upstream.add((qid, cid))
                            break

                # 2. Tighter per-frame positional bound (c_ms advances to tokens seen before rk)
                sim_t = sim0
                q_ms_t = q_match_seen
                c_ms_t = c_match_seen
                c_seen_cur = 0
                for rk, c_fq in c_frames:
                    c_seen_prev = c_seen_cur
                    c_seen_cur += c_fq
                    if c_seen_cur <= c_match_seen:
                        continue
                    c_ms_t = c_seen_prev
                    scc_frame_comps_tight += 1
                    if sim_t + min(q_sz - q_ms_t, c_sz - c_ms_t) < req:
                        break
                    info = q_pref_map.get(rk) if q_ms_t < pref_target else None
                    if info is None:
                        info = q_suff_map.get(rk)
                    if info is not None:
                        q_ms_t = info[0]
                        sim_t += info[1] if info[1] < c_fq else c_fq
                        if sim_t >= req:
                            found_tight.add((qid, cid))
                            break

        assert found_upstream == gt_clones and found_tight == gt_clones, (
            f"Mismatch at theta={th_str}: upstream_diff={len(found_upstream ^ gt_clones)}, "
            f"tight_diff={len(found_tight ^ gt_clones)}"
        )
        assert scc_frame_comps_tight <= scc_frame_comps_upstream
        out[th_str] = {
            "exact_clones": len(gt_clones),
            "false_negatives": 0,
            "false_positives": 0,
            "index_token_reduction_pct": round(100.0 * (1.0 - indexed_tokens / total_tokens), 2),
            "candidate_pair_reduction_pct": round(100.0 * (1.0 - cand_pairs_evaluated / all_pairs), 2),
            "frame_comp_reduction_upstream_pct": round(
                100.0 * (1.0 - scc_frame_comps_upstream / naive_frame_comps), 2
            ),
            "frame_comp_reduction_tight_pct": round(
                100.0 * (1.0 - scc_frame_comps_tight / naive_frame_comps), 2
            ),
        }

    return out


def run_probe_3() -> dict:
    rng = random.Random(20261122)
    vocab = [f"tok_{i}" for i in range(400)]
    weights = [1.0 / ((i + 1) ** 0.85) for i in range(400)]
    bags: List[List[str]] = [rng.choices(vocab, weights=weights, k=rng.randint(25, 85)) for _ in range(220)]
    for idx in range(80):
        base = list(bags[idx])
        edits = int(len(base) * (idx % 9) * 0.05)
        for _ in range(edits):
            pos = rng.randrange(len(base))
            if rng.random() < 0.5 and len(base) > 20:
                base.pop(pos)
            else:
                base[pos] = rng.choices(vocab, weights=weights, k=1)[0]
        bags.append(base)

    zipf_results = verify_sourcerercc_compressed_index(bags, ("0.7", "0.8", "0.9"))

    # High-collision 6-token multiset stress test (200 bags -> 19,900 pairs)
    dense_vocab = [f"d_{i}" for i in range(6)]
    dense_bags = [rng.choices(dense_vocab, k=rng.randint(5, 18)) for _ in range(200)]
    dense_results = verify_sourcerercc_compressed_index(dense_bags, ("0.6", "0.7", "0.8", "0.9"))

    # Juergens et al. (ICSE 2009) Tables 1-2 complete audit (including inconsistent logical LOC & fault density)
    systems = [
        ("A", 317, 286, 159, 51, 19, 442, 43.0),
        ("B", 454, 160, 89, 29, 18, 197, 91.4),
        ("C", 495, 326, 179, 66, 42, 797, 52.7),
        ("D", 197, 352, 151, 15, 5, 1476, 3.4),
        ("Sysiphus", 281, 303, 146, 42, 23, 459, 50.1),
    ]
    tot_kloc = sum(s[1] for s in systems)
    tot_c = sum(s[2] for s in systems)
    tot_ic = sum(s[3] for s in systems)
    tot_uic = sum(s[4] for s in systems)
    tot_f = sum(s[5] for s in systems)
    tot_inc_lloc = sum(s[6] for s in systems)
    assert (tot_kloc, tot_c, tot_ic, tot_uic, tot_f, tot_inc_lloc) == (1744, 1427, 724, 203, 107, 3371)

    computed_densities = [1000.0 * s[5] / s[6] for s in systems]
    for comp_d, pub_d in zip(computed_densities, [s[7] for s in systems]):
        assert abs(round(comp_d, 1) - pub_d) <= 0.1
    mean_density = sum(computed_densities) / len(systems)
    pooled_density = 1000.0 * tot_f / tot_inc_lloc
    assert round(mean_density, 1) == 48.1

    return {
        "sourcerercc_zipf_compressed_filter": zipf_results,
        "sourcerercc_dense_multiset_stress_zero_fn_fp": all(
            v["false_negatives"] == 0 and v["false_positives"] == 0 for v in dense_results.values()
        ),
        "juergens_totals": {
            "kLOC": tot_kloc,
            "C": tot_c,
            "IC": tot_ic,
            "UIC": tot_uic,
            "F": tot_f,
            "inconsistent_logical_lines": tot_inc_lloc,
        },
        "juergens_intentional_divergence_share_of_IC": round((tot_ic - tot_uic) / tot_ic, 4),
        "juergens_pooled_P_fault_given_UIC": round(tot_f / tot_uic, 4),
        "juergens_system_mean_P_fault_given_UIC": round(sum(s[5] / s[4] for s in systems) / len(systems), 4),
        "juergens_system_mean_faults_per_inconsistent_kLOC": round(mean_density, 2),
        "juergens_pooled_faults_per_inconsistent_kLOC": round(pooled_density, 2),
    }


# ============================================================================
# Probe 4: Exact Break-Even k*, Capture p_wrong(m), & Shared-Vocab Aliasing
# ============================================================================

def break_even_k_star_exact(
    c_inline: fractions.Fraction,
    c_extract: fractions.Fraction,
    c_call: fractions.Fraction,
    c_sync: fractions.Fraction,
    mu_sync: fractions.Fraction,
    c_edit: fractions.Fraction,
    p_miss: fractions.Fraction,
    p_fault_uic: fractions.Fraction,
    c_bug: fractions.Fraction,
    p_div: fractions.Fraction,
    c_div: fractions.Fraction,
) -> Optional[int]:
    g = (
        (c_inline - c_call)
        + mu_sync * (c_edit + p_miss * p_fault_uic * c_bug)
        - c_sync
        - p_div * c_div
    )
    if g <= 0:
        return None
    return max(2, 1 + math.ceil((c_extract + c_call) / g))


def shared_vocab_lgg_wrong_prob_exact(r: int, vocab_size: int, m: int) -> fractions.Fraction:
    """Exact probability under i.i.d. uniform draws over an untagged literal domain
    of size V that syntactic lgg on m witnesses fails to recover all r independent
    parameters (due to constant capture OR cross-slot disagreement-tuple aliasing).
    Note: when r > V^m - V, the failure probability 1 is strictly distribution-free
    by Pigeonhole even for adversarially or oracle-chosen witnesses."""
    non_const = vocab_size ** m - vocab_size
    if non_const < r:
        return fractions.Fraction(1, 1)
    falling = 1
    for q in range(r):
        falling *= non_const - q
    return fractions.Fraction(1, 1) - fractions.Fraction(falling, vocab_size ** (r * m))


def run_probe_4() -> dict:
    rng = random.Random(20261122)
    F = fractions.Fraction
    p_f = F(107, 203)
    regimes = {
        "security_protocol_invariant": dict(
            c_inline=F("1.0"), c_extract=F("1.40"), c_call=F("0.15"), c_sync=F("0.15"),
            mu_sync=F("2.0"), c_edit=F("0.25"), p_miss=F("0.28"), p_fault_uic=p_f, c_bug=F("8.0"),
            p_div=F("0.10"), c_div=F("0.80"),
        ),
        "standard_intra_repo_helper": dict(
            c_inline=F("1.0"), c_extract=F("1.10"), c_call=F("0.15"), c_sync=F("0.10"),
            mu_sync=F("0.5"), c_edit=F("0.25"), p_miss=F("0.28"), p_fault_uic=p_f, c_bug=F("2.0"),
            p_div=F("0.25"), c_div=F("0.85"),
        ),
        "cross_team_innersource_lib": dict(
            c_inline=F("1.0"), c_extract=F("1.80"), c_call=F("0.20"), c_sync=F("0.35"),
            mu_sync=F("0.6"), c_edit=F("0.25"), p_miss=F("0.28"), p_fault_uic=p_f, c_bug=F("2.5"),
            p_div=F("0.20"), c_div=F("0.90"),
        ),
        "high_divergence_boilerplate": dict(
            c_inline=F("1.0"), c_extract=F("1.20"), c_call=F("0.25"), c_sync=F("0.25"),
            mu_sync=F("0.1"), c_edit=F("0.20"), p_miss=F("0.20"), p_fault_uic=p_f, c_bug=F("1.0"),
            p_div=F("0.72"), c_div=F("0.95"),
        ),
    }

    regime_summary: Dict[str, Optional[int]] = {}
    for name, kw in regimes.items():
        ks = break_even_k_star_exact(**kw)
        empirical_ks: Optional[int] = None
        for k in range(1, 30):
            c_in = k * kw["c_inline"] + kw["mu_sync"] * (
                k * kw["c_edit"] + (k - 1) * kw["p_miss"] * kw["p_fault_uic"] * kw["c_bug"]
            )
            c_sh = (
                kw["c_inline"] + kw["c_extract"] + k * kw["c_call"] + (k - 1) * kw["c_sync"]
                + kw["mu_sync"] * kw["c_edit"] + (k - 1) * kw["p_div"] * kw["c_div"]
            )
            if c_sh <= c_in:
                empirical_ks = k
                break
        assert ks == empirical_ks, (name, ks, empirical_ks)
        regime_summary[name] = ks

    assert regime_summary["security_protocol_invariant"] == 2
    assert regime_summary["standard_intra_repo_helper"] == 3
    assert regime_summary["cross_team_innersource_lib"] == 5
    assert regime_summary["high_divergence_boilerplate"] is None

    # Disjoint-alphabet premature argument capture p_wrong(m) + non-degeneracy check
    slot_dists = [(0.5, 0.5), (0.7, 0.3), (0.6, 0.25, 0.15)]
    assert all(abs(sum(d) - 1.0) < 1e-12 and max(d) < 1.0 for d in slot_dists)

    # Verify degenerate axis (P_j(v*) == 1.0) pins p_wrong(m) == 1.0 for every m
    degenerate_dists = [(0.5, 0.5), (1.0,)]
    for m_deg in (1, 2, 5, 20):
        p_deg = 1.0 - math.prod(1.0 - sum(p ** m_deg for p in d) for d in degenerate_dists)
        assert p_deg == 1.0

    # Fast compact lgg arity check over pre-interned Term leaves
    t0_a, t0_b = Term("const:s0_0"), Term("const:s0_1")
    t1_a, t1_b = Term("const:s1_0"), Term("const:s1_1")
    t2_a, t2_b, t2_c = Term("const:s2_0"), Term("const:s2_1"), Term("const:s2_2")
    rand = rng.random

    capture_table = {}
    trials = 10000
    for m in (1, 2, 3, 4, 5):
        analytic = 1.0 - math.prod(1.0 - sum(p ** m for p in dist) for dist in slot_dists)
        m_trials = 64 if m == 1 else trials
        misses = 0
        for _ in range(m_trials):
            sample_terms = []
            for _i in range(m):
                a0 = t0_a if rand() <= 0.5 else t0_b
                a1 = t1_a if rand() <= 0.7 else t1_b
                u2 = rand()
                a2 = t2_a if u2 <= 0.6 else (t2_b if u2 <= 0.85 else t2_c)
                sample_terms.append(Term("call:work", (a0, a1, a2)))
            gen, _ = lgg_many(sample_terms)
            if arity_of(gen) < 3:
                misses += 1
        mc = misses / m_trials
        assert abs(analytic - mc) < 0.012
        capture_table[f"m={m}"] = {"analytic": round(analytic, 4), "mc_lgg": round(mc, 4)}

    # Shared-vocabulary Plotkin aliasing & distribution-free Pigeonhole impossibility
    bin_lits = (Term("const:0"), Term("const:1"))
    shared_vocab_audit = {}
    max_achievable_arity_m2_r3 = 0
    for r in (2, 3):
        row = {}
        for m in (2, 3):
            const_cap_only = 1.0 - (1.0 - 2 * (0.5 ** m)) ** r
            exact_q = shared_vocab_lgg_wrong_prob_exact(r=r, vocab_size=2, m=m)
            all_tuples = list(itertools.product((0, 1), repeat=r))
            total_outcomes = 0
            wrong_outcomes = 0
            for witness_seq in itertools.product(all_tuples, repeat=m):
                total_outcomes += 1
                ast_witnesses = [
                    Term("call:cfg", tuple(bin_lits[val] for val in tup)) for tup in witness_seq
                ]
                gen_sv, _ = lgg_many(ast_witnesses)
                ar = arity_of(gen_sv)
                if r == 3 and m == 2 and ar > max_achievable_arity_m2_r3:
                    max_achievable_arity_m2_r3 = ar
                if ar < r:
                    wrong_outcomes += 1
            assert fractions.Fraction(wrong_outcomes, total_outcomes) == exact_q
            row[f"m={m}"] = {
                "constant_capture_only": round(const_cap_only, 5),
                "true_lgg_shared_vocab_wrong": round(float(exact_q), 5),
                "aliasing_excess_pp": round(100.0 * (float(exact_q) - const_cap_only), 2),
            }
        shared_vocab_audit[f"r={r}_V=2"] = row

    assert shared_vocab_audit["r=2_V=2"]["m=2"]["true_lgg_shared_vocab_wrong"] == 0.875
    assert shared_vocab_audit["r=3_V=2"]["m=2"]["true_lgg_shared_vocab_wrong"] == 1.0
    assert max_achievable_arity_m2_r3 == 2  # Distribution-free Pigeonhole ceiling: 2^2 - 2 = 2 < 3

    # Concave boolean-flag entanglement window [k_min*, k_max*]
    c_ext_call = F("1.25")
    g_base = F("0.85")
    delta_flag = F("0.12")
    profitable_ks = [
        k for k in range(1, 20)
        if -c_ext_call + (k - 1) * g_base - F(k * (k - 1), 2) * delta_flag >= 0
    ]
    assert profitable_ks[0] == 3 and profitable_ks[-1] == 12

    return {
        "k_star_by_regime": regime_summary,
        "premature_capture_disjoint_p_wrong_by_m": capture_table,
        "shared_vocab_aliasing_and_pigeonhole": shared_vocab_audit,
        "distribution_free_max_arity_r3_V2_m2": max_achievable_arity_m2_r3,
        "flag_entangled_profitable_window": [profitable_ks[0], profitable_ks[-1]],
    }


# ============================================================================
# Probe 5: Symmetric Concurrent Helper Scheduling & Non-Concave Crossover Law
# ============================================================================

def exact_lognormal_min_th_max_tc(
    th_mean: float,
    tc_mean: float,
    sigma: float,
    k: int,
    steps: int = 3000,
) -> float:
    """Exact deterministic 1D tail-integral quadrature for E[min(X, max_{1<=i<=k} Y_i)]
    with independent X ~ Lognormal(mu_X, sigma^2), Y_i ~ i.i.d. Lognormal(mu_Y, sigma^2),
    using E[min(X, M_k)] = int_0^inf P(X > t) * (1 - P(Y <= t)^k) dt."""
    half_var = 0.5 * sigma * sigma
    mu_x = math.log(th_mean) - half_var
    mu_y = math.log(tc_mean) - half_var
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    u_lo = min(mu_x, mu_y) - 14.0 * sigma
    u_hi = max(mu_x, mu_y) + 12.0 * sigma
    du = (u_hi - u_lo) / steps
    acc = 0.0
    erf = math.erf
    exp = math.exp
    for idx in range(steps):
        u = u_lo + (idx + 0.5) * du
        t = exp(u)
        fx = 0.5 * (1.0 + erf((u - mu_x) / sigma * inv_sqrt2))
        fy = 0.5 * (1.0 + erf((u - mu_y) / sigma * inv_sqrt2))
        acc += (1.0 - fx) * (1.0 - (fy ** k)) * t
    return exp(u_lo) + acc * du


def run_probe_5() -> dict:
    rng = random.Random(20261122)
    T_H_in = 1.00
    T_ext = 0.50
    T_H_sh = T_H_in + T_ext
    T_C = 1.60
    t_stub = 0.12
    t_stub_read = 0.03
    t_int = 0.10
    W_rew = 2.40
    c_rew_H = 0.40
    c_rew_C = 0.90
    T_cons = 0.65
    sigma = 0.45

    p_drift_star_det = (min(T_H_sh, T_C) - t_stub) / W_rew
    assert abs(p_drift_star_det - 0.575) < 1e-9

    # Two-regime stochastic crossover verification via exact 1D quadrature:
    # Functional (X, Y_1..Y_k) -> min(X, max_i Y_i) composes concave min with convex max:
    # - Regime 1 (E[T_C] >= E[T_{H,shared}]): p_drift^{*,stoch}(k) < p_drift^{*,det} for all k,
    #   approaching p_drift^{*,det} from below as k -> inf.
    # - Regime 2 (E[T_{H,shared}] > E[T_C]): convex straggler envelope E[max_{i<=k} T_{C,i}]
    #   pushes p_drift^{*,stoch}(k) strictly ABOVE p_drift^{*,det} for k >= 3!
    ks_quad = (2, 3, 5, 8, 12)
    quad_regime_tc_ge_th = {
        f"k={k}": round((exact_lognormal_min_th_max_tc(1.50, 1.60, sigma, k) - t_stub) / W_rew, 4)
        for k in ks_quad
    }
    quad_regime_equal = {
        f"k={k}": round((exact_lognormal_min_th_max_tc(1.00, 1.00, sigma, k) - t_stub) / W_rew, 4)
        for k in ks_quad
    }
    p_det_equal = round((min(1.00, 1.00) - t_stub) / W_rew, 4)
    T_C_short = 1.20
    p_det_th_gt_tc = round((min(T_H_sh, T_C_short) - t_stub) / W_rew, 4)
    assert p_det_th_gt_tc == 0.45
    quad_regime_th_gt_tc = {
        f"k={k}": round((exact_lognormal_min_th_max_tc(T_H_sh, T_C_short, sigma, k) - t_stub) / W_rew, 4)
        for k in ks_quad
    }

    assert (
        quad_regime_tc_ge_th["k=2"]
        < quad_regime_tc_ge_th["k=3"]
        < quad_regime_tc_ge_th["k=5"]
        < quad_regime_tc_ge_th["k=8"]
        < quad_regime_tc_ge_th["k=12"]
        < p_drift_star_det
    )
    assert all(v < p_det_equal for v in quad_regime_equal.values())
    assert quad_regime_th_gt_tc["k=2"] < p_det_th_gt_tc
    assert (
        p_det_th_gt_tc
        < quad_regime_th_gt_tc["k=3"]
        < quad_regime_th_gt_tc["k=5"]
        < quad_regime_th_gt_tc["k=8"]
        < quad_regime_th_gt_tc["k=12"]
    )

    half_var = 0.5 * sigma * sigma
    mu_th_sh = math.log(T_H_sh) - half_var
    mu_tc = math.log(T_C) - half_var
    mu_tc_short = math.log(T_C_short) - half_var
    mu_th_in = math.log(T_H_in) - half_var
    mu_w_rew = math.log(W_rew) - half_var
    mu_t_cons = math.log(T_cons) - half_var
    exp = math.exp
    gauss = rng.gauss
    rand = rng.random

    trials = 10000
    grid_rows = []
    mc_crossovers_tc_ge_th: Dict[str, float] = {}

    for k in (2, 3, 5, 8):
        # Common Random Numbers (CRN) across schedules, beta in {0.5, 1.0}, and p_drift
        w_block_ded_sum = 0.0
        w_block_inband_b10_sum = w_block_inband_b05_sum = 0.0
        w_inline_feat_sum = w_inline_cons_sum = 0.0
        e_block_ded_act_sum = e_block_inband_act_sum = e_inline_act_sum = 0.0
        min_th_mc_sum = 0.0
        w_rw_all_sum = 0.0

        stub_base_ded_sum = 0.0
        stub_base_inband_b10_sum = stub_base_inband_b05_sum = 0.0
        stub_base_ded_act_sum = stub_base_inband_act_sum = stub_base_slot_sum = 0.0
        drift_draws: List[Tuple[float, float]] = []

        for _ in range(trials):
            th_sh = exp(gauss(mu_th_sh, sigma))
            tcs = [exp(gauss(mu_tc, sigma)) for _ in range(k)]
            th_ins = [exp(gauss(mu_th_in, sigma)) for _ in range(k)]
            t_cons_s = exp(gauss(mu_t_cons, sigma)) if k >= 3 else 0.0
            w_rw_sample = exp(gauss(mu_w_rew, sigma))
            u_drift = rand()
            drift_draws.append((u_drift, w_rw_sample))
            w_rw_all_sum += w_rw_sample

            max_tc = max(tcs)
            sum_tc = sum(tcs)
            min_th_mc_sum += th_sh if th_sh < max_tc else max_tc

            # Schedule A: Blocking Producer-First with symmetric beta in {1.0, 0.5}
            # and symmetric API-comprehension token cost (k*t_stub_read dedicated, (k-1)*t_stub_read in-band)
            w_block_ded_sum += th_sh + max_tc + t_int
            w_block_inband_b10_sum += th_sh + max_tc + t_int
            a1_block = th_sh + tcs[0]
            rest_block_b05 = max(max(th_sh, 0.5 * tcs[i]) + 0.5 * tcs[i] for i in range(1, k))
            w_block_inband_b05_sum += (a1_block if a1_block > rest_block_b05 else rest_block_b05) + t_int
            e_block_ded_act_sum += th_sh + k * t_stub_read + sum_tc + k * t_int
            e_block_inband_act_sum += th_sh + (k - 1) * t_stub_read + sum_tc + k * t_int

            # Schedule B: Interface-Stub First with symmetric beta in {1.0, 0.5}
            # and symmetric API-comprehension token cost
            stub_base_ded_sum += t_stub + (th_sh if th_sh > max_tc else max_tc) + t_int
            a1_stub = t_stub + th_sh + tcs[0]
            rest_stub_b10 = max(t_stub + tcs[i] for i in range(1, k))
            stub_base_inband_b10_sum += (a1_stub if a1_stub > rest_stub_b10 else rest_stub_b10) + t_int
            rest_stub_b05 = max(max(t_stub, 0.5 * tcs[i]) + 0.5 * tcs[i] for i in range(1, k))
            stub_base_inband_b05_sum += (a1_stub if a1_stub > rest_stub_b05 else rest_stub_b05) + t_int

            stub_base_ded_act_sum += t_stub + th_sh + k * t_stub_read + sum_tc + k * t_int
            stub_base_inband_act_sum += t_stub + th_sh + (k - 1) * t_stub_read + sum_tc + k * t_int
            stub_base_slot_sum += (k + 1) * t_stub + th_sh + k * t_stub_read + sum_tc + k * t_int

            # Schedule C: Inline-First + Conditional Sleep Consolidation (symmetric t_int)
            wf = max(th_ins[i] + tcs[i] for i in range(k)) + t_int
            w_inline_feat_sum += wf
            w_inline_cons_sum += wf + (t_cons_s + t_int if k >= 3 else 0.0)
            e_inline_act_sum += sum(th_ins) + sum_tc + k * t_int + (t_cons_s + k * t_int if k >= 3 else 0.0)

        # Consistent MC ratio using sample rework expectation E[W_rework | drift] = E[W_rework]
        e_min_th_mc = min_th_mc_sum / trials
        e_w_rw_mc = w_rw_all_sum / trials
        mc_cross = (e_min_th_mc - t_stub) / e_w_rw_mc
        assert abs(mc_cross - quad_regime_tc_ge_th[f"k={k}"]) < 0.012
        mc_crossovers_tc_ge_th[f"k={k}"] = round(mc_cross, 4)

        c_rw_const = c_rew_H + k * c_rew_C
        for p_drift in (0.05, 0.25, 0.52, 0.65):
            extra_w_rw = 0.0
            drift_hits = 0
            for u_d, w_rw_s in drift_draws:
                if u_d < p_drift:
                    extra_w_rw += w_rw_s
                    drift_hits += 1
            extra_c_rw = drift_hits * c_rw_const

            grid_rows.append({
                "k": k,
                "p_drift": p_drift,
                "W_block_ded": round(w_block_ded_sum / trials, 3),
                "W_stub_ded": round((stub_base_ded_sum + extra_w_rw) / trials, 3),
                "W_block_inband_b10": round(w_block_inband_b10_sum / trials, 3),
                "W_stub_inband_b10": round((stub_base_inband_b10_sum + extra_w_rw) / trials, 3),
                "W_block_inband_b05": round(w_block_inband_b05_sum / trials, 3),
                "W_stub_inband_b05": round((stub_base_inband_b05_sum + extra_w_rw) / trials, 3),
                "W_inline_feat": round(w_inline_feat_sum / trials, 3),
                "W_inline_cons": round(w_inline_cons_sum / trials, 3),
                "E_block_active": round(e_block_ded_act_sum / trials, 3),
                "E_stub_active": round((stub_base_ded_act_sum + extra_c_rw) / trials, 3),
                "E_block_inband_active": round(e_block_inband_act_sum / trials, 3),
                "E_stub_inband_active": round((stub_base_inband_act_sum + extra_c_rw) / trials, 3),
                "E_stub_slot_hours": round((stub_base_slot_sum + extra_c_rw) / trials, 3),
                "E_inline_active": round(e_inline_act_sum / trials, 3),
            })

    # Empirical CRN verification of Regime 2 (T_{H,shared}=1.50 > T_C=1.20, p_det=0.4500):
    # At k=8 and p_drift=0.48 in (0.4500, 0.5173), convex max_i T_{C,i} makes Stub_ded BEAT Block_ded!
    k_r2 = 8
    p_r2 = 0.48
    wb_r2 = ws_r2 = 0.0
    for _ in range(trials):
        th_s = exp(gauss(mu_th_sh, sigma))
        max_tc_s = max(exp(gauss(mu_tc_short, sigma)) for _ in range(k_r2))
        w_rw_s = exp(gauss(mu_w_rew, sigma)) if rand() < p_r2 else 0.0
        wb_r2 += th_s + max_tc_s + t_int
        ws_r2 += t_stub + (th_s if th_s > max_tc_s else max_tc_s) + t_int + w_rw_s
    w_block_ded_r2 = round(wb_r2 / trials, 3)
    w_stub_ded_r2 = round(ws_r2 / trials, 3)
    assert w_stub_ded_r2 < w_block_ded_r2

    # Regime 1 witness: at k=2, p_drift=0.52 (< deterministic 0.575 but > exact stochastic 0.4922),
    # Stub_ded ALREADY loses to Block_ded!
    r_k2_r1 = next(r for r in grid_rows if r["k"] == 2 and r["p_drift"] == 0.52)
    assert r_k2_r1["W_stub_ded"] > r_k2_r1["W_block_ded"]

    # Symmetric equal-headcount assertions across k and beta in {0.5, 1.0} at low drift (p_drift=0.05):
    for k_chk in (2, 3, 5, 8):
        row_low = next(r for r in grid_rows if r["k"] == k_chk and r["p_drift"] == 0.05)
        # Matched beta=1.0: Stub_inband_b10 strictly beats Block_inband_b10 for every k in {2,3,5,8}
        assert row_low["W_stub_inband_b10"] < row_low["W_block_inband_b10"]
        # Matched beta=0.5: Block_inband_b05 beats Stub_inband_b05 for k <= 8 due to Agent 1 bottleneck
        assert row_low["W_block_inband_b05"] < row_low["W_stub_inband_b05"]
        # Dedicated (k+1)-th worker: Stub_ded wins across all schedules
        assert row_low["W_stub_ded"] < row_low["W_block_inband_b05"]
        assert row_low["W_stub_ded"] < row_low["W_inline_feat"]

    r_k2_low = next(r for r in grid_rows if r["k"] == 2 and r["p_drift"] == 0.05)
    assert r_k2_low["W_inline_feat"] < r_k2_low["W_block_inband_b05"] < r_k2_low["W_stub_inband_b05"]
    assert r_k2_low["W_inline_feat"] < r_k2_low["W_stub_inband_b10"] < r_k2_low["W_block_inband_b10"]

    r_k5_low = next(r for r in grid_rows if r["k"] == 5 and r["p_drift"] == 0.05)
    assert r_k5_low["W_stub_inband_b10"] < r_k5_low["W_inline_feat"] < r_k5_low["W_block_inband_b10"]
    assert r_k5_low["E_block_active"] < r_k5_low["E_stub_active"] < r_k5_low["E_inline_active"]

    r_k5_high = next(r for r in grid_rows if r["k"] == 5 and r["p_drift"] == 0.65)
    assert r_k5_high["W_inline_feat"] < r_k5_high["W_block_ded"] < r_k5_high["W_stub_ded"]
    assert r_k5_high["E_block_active"] < r_k5_high["E_stub_active"] < r_k5_high["E_inline_active"]

    return {
        "stochastic_crossover_regimes": {
            "regime_1_tc1.60_ge_th1.50": {
                "deterministic_p_drift_star": round(p_drift_star_det, 4),
                "exact_quadrature_by_k": quad_regime_tc_ge_th,
                "mc_sample_ratio_by_k": mc_crossovers_tc_ge_th,
            },
            "regime_1b_tc1.00_eq_th1.00": {
                "deterministic_p_drift_star": p_det_equal,
                "exact_quadrature_by_k": quad_regime_equal,
            },
            "regime_2_th1.50_gt_tc1.20_convex_straggler": {
                "deterministic_p_drift_star": p_det_th_gt_tc,
                "exact_quadrature_by_k": quad_regime_th_gt_tc,
                "k8_p0.48_W_stub_ded_vs_W_block_ded": [w_stub_ded_r2, w_block_ded_r2],
            },
        },
        "lognormal_grid": grid_rows,
    }


def main() -> None:
    results = {
        "probe_1_ast_lgg_and_stitch": run_probe_1(),
        "probe_2_egraph_dfta_au": run_probe_2(),
        "probe_3_sourcerercc_and_juergens": run_probe_3(),
        "probe_4_rule_of_three_and_capture": run_probe_4(),
        "probe_5_concurrent_scheduling": run_probe_5(),
    }
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
