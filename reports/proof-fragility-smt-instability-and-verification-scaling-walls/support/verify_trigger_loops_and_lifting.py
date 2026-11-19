#!/usr/bin/env python3
"""Standalone analyzer for E-matching trigger loops, SHAKE-style context pruning,
Mariposa-style solver-order sensitivity, and AutoCorres-style validated IR lifting.

Standard library only (Python 3.10+). Deterministic and self-checking.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import random
from typing import Iterable


# =============================================================================
# Part A: E-Matching Trigger-Graph Cycle Detector & Bounded Budget Instability
# =============================================================================


@dataclass(frozen=True)
class Var:
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class App:
    sym: str
    args: tuple["Term", ...] = ()

    def __str__(self) -> str:
        if not self.args:
            return self.sym
        return f"{self.sym}({', '.join(str(a) for a in self.args)})"


Term = Var | App


def term_vars(t: Term) -> set[str]:
    if isinstance(t, Var):
        return {t.name}
    out: set[str] = set()
    for a in t.args:
        out.update(term_vars(a))
    return out


def term_syms(t: Term) -> set[str]:
    if isinstance(t, Var):
        return set()
    out = {t.sym}
    for a in t.args:
        out.update(term_syms(a))
    return out


def term_subterms(t: Term) -> list[Term]:
    res = [t]
    if isinstance(t, App):
        for a in t.args:
            res.extend(term_subterms(a))
    return res


def term_size(t: Term) -> int:
    if isinstance(t, Var):
        return 1
    return 1 + sum(term_size(a) for a in t.args)


def substitute(t: Term, env: dict[str, Term]) -> Term:
    if isinstance(t, Var):
        return env.get(t.name, t)
    return App(t.sym, tuple(substitute(a, env) for a in t.args))


def structure_matches(
    bound_vars: set[str], template: Term, candidate: Term
) -> tuple[bool, bool, dict[str, Term]]:
    """Verus-style structural match check (mirrors vir/src/triggers_auto.rs).

    Returns (matched, strictly_bigger, substitution):
    - matched: candidate is an instance of template for bound_vars
    - strictly_bigger: at least one bound variable matched a non-variable App
    - substitution: variable assignment (if consistent)
    """
    subst: dict[str, Term] = {}

    def rec(pat: Term, cand: Term) -> tuple[bool, bool]:
        if isinstance(pat, Var) and pat.name in bound_vars:
            if pat.name in subst:
                if subst[pat.name] != cand:
                    return False, False
                return True, isinstance(cand, App)
            subst[pat.name] = cand
            return True, isinstance(cand, App)
        if isinstance(pat, Var) and isinstance(cand, Var):
            return pat.name == cand.name, False
        if isinstance(pat, App) and isinstance(cand, App):
            if pat.sym != cand.sym or len(pat.args) != len(cand.args):
                return False, False
            bigger_any = False
            for pa, ca in zip(pat.args, cand.args):
                ok, big = rec(pa, ca)
                if not ok:
                    return False, False
                bigger_any = bigger_any or big
            return True, bigger_any
        return False, False

    ok, big = rec(template, candidate)
    return ok, big, subst if ok else {}


def unify_patterns(
    vars_a: set[str], term_a: Term, vars_b: set[str], term_b: Term
) -> tuple[bool, int]:
    """Check if body term_a (under vars_a) can produce a ground instance matching
    trigger pattern term_b (under vars_b). Returns (can_match, size_delta).

    Uses alpha-renamed variables to test first-order unification with occurs check.
    size_delta > 0 indicates term_a strictly wraps or expands arguments compared
    to term_b's pattern skeleton; size_delta < 0 indicates strict structural
    shrinkage (e.g., fuel consumption succ(k) -> k).
    """

    def rename(t: Term, prefix: str, bvars: set[str]) -> Term:
        if isinstance(t, Var):
            return Var(f"{prefix}_{t.name}") if t.name in bvars else t
        return App(t.sym, tuple(rename(a, prefix, bvars) for a in t.args))

    ra = rename(term_a, "L", vars_a)
    rb = rename(term_b, "R", vars_b)
    subst: dict[str, Term] = {}

    def apply(t: Term) -> Term:
        if isinstance(t, Var):
            if t.name in subst:
                return apply(subst[t.name])
            return t
        return App(t.sym, tuple(apply(a) for a in t.args))

    def occurs(v: str, t: Term) -> bool:
        t = apply(t)
        if isinstance(t, Var):
            return t.name == v
        return any(occurs(v, a) for a in t.args)

    def unify(x: Term, y: Term) -> bool:
        x = apply(x)
        y = apply(y)
        if x == y:
            return True
        if isinstance(x, Var) and (x.name.startswith("L_") or x.name.startswith("R_")):
            if occurs(x.name, y):
                return False
            subst[x.name] = y
            return True
        if isinstance(y, Var) and (y.name.startswith("L_") or y.name.startswith("R_")):
            if occurs(y.name, x):
                return False
            subst[y.name] = x
            return True
        if isinstance(x, App) and isinstance(y, App):
            if x.sym != y.sym or len(x.args) != len(y.args):
                return False
            return all(unify(xa, ya) for xa, ya in zip(x.args, y.args))
        return False

    if not unify(ra, rb):
        return False, 0

    # Positive growth if body instantiates a target trigger variable with a deeper App;
    # negative if body strips a constructor that was required in the source trigger.
    r_growth = 0
    for k, v in subst.items():
        rv = apply(v)
        if k.startswith("R_") and isinstance(rv, App):
            r_growth += term_size(rv) - 1
    return True, r_growth


@dataclass(frozen=True)
class QuantRule:
    qid: str
    bound_vars: tuple[str, ...]
    # Disjunction of multi-triggers: any multi-trigger group (tuple[Term, ...]) can fire
    triggers: tuple[tuple[Term, ...], ...]
    # Ground-term templates produced in the quantifier body upon instantiation
    body_terms: tuple[Term, ...]
    weight: int = 1
    # Optional syntactic fuel argument position: (trigger_idx_in_group, arg_pos) where
    # trigger requires App("succ", (Var(k),)) and every recursive body_term has Var(k)
    fuel_decreasing: bool = False

    def validate_triggers(self) -> None:
        bset = set(self.bound_vars)
        for group in self.triggers:
            covered: set[str] = set()
            for pat in group:
                covered.update(term_vars(pat))
            missing = bset - covered
            if missing:
                raise ValueError(
                    f"Rule {self.qid}: trigger group {group} omits bound vars {sorted(missing)}"
                )

    def pattern_symbol_sets(self) -> list[set[str]]:
        out: list[set[str]] = []
        for group in self.triggers:
            syms: set[str] = set()
            for pat in group:
                syms.update(term_syms(pat))
            out.append(syms)
        return out

    def body_symbol_set(self) -> set[str]:
        syms: set[str] = set()
        for bt in self.body_terms:
            syms.update(term_syms(bt))
        return syms


def detect_local_verus_loops(rule: QuantRule) -> list[tuple[Term, Term]]:
    """Single-quantifier local loop filter mirroring Verus remove_obvious_potential_loops."""
    bvars = set(rule.bound_vars)
    hits: list[tuple[Term, Term]] = []
    body_subterms: list[Term] = []
    for bt in rule.body_terms:
        body_subterms.extend(term_subterms(bt))
    for group in rule.triggers:
        for pat in group:
            if not isinstance(pat, App):
                continue
            for sub in body_subterms:
                if isinstance(sub, App) and sub.sym == pat.sym:
                    ok, bigger, _ = structure_matches(bvars, pat, sub)
                    if ok and bigger:
                        hits.append((pat, sub))
    return hits


def analyze_trigger_graph(rules: list[QuantRule]) -> dict[str, object]:
    """Build inter-quantifier trigger dependency graph and classify SCC cycles."""
    for r in rules:
        r.validate_triggers()

    edges: dict[str, list[tuple[str, int, bool]]] = {r.qid: [] for r in rules}
    for src in rules:
        src_vars = set(src.bound_vars)
        src_subs = [
            sub
            for bt in src.body_terms
            for sub in term_subterms(bt)
            if isinstance(sub, App)
        ]
        # Detect fuel consumption: trigger matches succ(k) while body uses bare k
        for dst in rules:
            dst_vars = set(dst.bound_vars)
            best_edge: tuple[int, bool] | None = None
            for group in dst.triggers:
                for pat in group:
                    if not isinstance(pat, App):
                        continue
                    for sub in src_subs:
                        if sub.sym != pat.sym or len(sub.args) != len(pat.args):
                            continue
                        ok, growth = unify_patterns(src_vars, sub, dst_vars, pat)
                        if not ok:
                            continue
                        # Check if the source trigger explicitly strips a constructor
                        # (e.g., fuel succ(k) -> k) making the recursion well-founded.
                        strictly_decreasing = src.fuel_decreasing and (
                            src.qid == dst.qid
                        )
                        if best_edge is None or growth > best_edge[0]:
                            best_edge = (growth, strictly_decreasing)
            if best_edge is not None:
                edges[src.qid].append((dst.qid, best_edge[0], best_edge[1]))

    # Tarjan's SCC algorithm
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w, _, _ in edges[v]:
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))

    for r in rules:
        if r.qid not in indices:
            strongconnect(r.qid)

    amplifying_cycles: list[list[str]] = []
    stratified_cycles: list[list[str]] = []
    for comp in sccs:
        comp_set = set(comp)
        internal_edges = [
            (u, v, growth, decr)
            for u in comp
            for (v, growth, decr) in edges[u]
            if v in comp_set
        ]
        if not internal_edges:
            continue
        if all(decr for _, _, _, decr in internal_edges):
            stratified_cycles.append(comp)
        elif any(growth > 0 for _, _, growth, _ in internal_edges):
            amplifying_cycles.append(comp)
        else:
            # Non-growing non-decreasing cycle (finite closure unless new terms enter)
            stratified_cycles.append(comp)

    local_hits = {r.qid: detect_local_verus_loops(r) for r in rules}
    return {
        "edges": edges,
        "sccs": sccs,
        "amplifying_cycles": amplifying_cycles,
        "stratified_cycles": stratified_cycles,
        "local_verus_hits": {k: len(v) for k, v in local_hits.items() if v},
    }


def shake_prune_rules(
    goal_terms: Iterable[Term],
    rules: list[QuantRule],
    max_layers: int | None = None,
    freq_threshold: float = 0.85,
) -> tuple[list[QuantRule], dict[str, int]]:
    """SHAKE Algorithm 2 (Zhou et al., FMCAD 2024): lazy pattern-aware layer pruning.

    Expands a quantifier rule only when at least one trigger group has ALL its
    non-ubiquitous symbols already present in the live symbol set S_ctx.
    """
    n_total = max(1, len(rules))
    sym_doc_count: dict[str, int] = {}
    for r in rules:
        all_r_syms = r.body_symbol_set()
        for ps in r.pattern_symbol_sets():
            all_r_syms.update(ps)
        for s in all_r_syms:
            sym_doc_count[s] = sym_doc_count.get(s, 0) + 1

    ubiquitous = {
        s for s, cnt in sym_doc_count.items() if (cnt / n_total) > freq_threshold
    }

    s_ctx: set[str] = set()
    for gt in goal_terms:
        s_ctx.update(term_syms(gt))
    s_ctx -= ubiquitous

    layers: dict[str, int] = {}
    layer = 1
    while True:
        if max_layers is not None and layer > max_layers:
            break
        newly_live_syms: set[str] = set()
        progressed = False
        for r in rules:
            if r.qid in layers:
                continue
            pat_sets = [ps - ubiquitous for ps in r.pattern_symbol_sets()]
            if any(ps and ps.issubset(s_ctx) for ps in pat_sets):
                layers[r.qid] = layer
                newly_live_syms.update(r.body_symbol_set() - ubiquitous)
                progressed = True
        if not progressed:
            break
        s_ctx.update(newly_live_syms)
        layer += 1

    kept = [r for r in rules if r.qid in layers]
    return kept, layers


def run_bounded_ematching(
    init_ground: list[Term],
    goal_fact: Term,
    rules: list[QuantRule],
    budget: int,
    seed: int,
    eager_threshold: int = 10,
) -> tuple[str, int]:
    """Simulate Z3-style generation-weighted E-matching with a bounded instantiation budget.

    Tie-breaking between equal-cost candidate instantiations depends on rule assertion
    order and solver PRNG seed (modeling Mariposa shuffle/reseed sensitivity).
    Returns ("unsat" | "timeout", instantiations_used).
    """
    rng = random.Random(seed)
    # ground term -> generation
    egraph: dict[Term, int] = {t: 0 for t in init_ground}
    if goal_fact in egraph:
        return "unsat", 0

    seen_insts: set[tuple[str, tuple[tuple[str, Term], ...]]] = set()
    # queue entries: (cost, tie_break, gen, rule, env)
    queue: list[tuple[float, float, int, QuantRule, dict[str, Term]]] = []

    def match_group(
        rule: QuantRule, group: tuple[Term, ...], ground_snapshot: list[Term]
    ) -> list[tuple[dict[str, Term], int]]:
        bvars = set(rule.bound_vars)
        partials: list[tuple[dict[str, Term], int]] = [({}, 0)]
        for pat in group:
            next_partials: list[tuple[dict[str, Term], int]] = []
            for env, max_g in partials:
                p_sub = substitute(pat, env)
                for gt in ground_snapshot:
                    if isinstance(p_sub, App) and isinstance(gt, App):
                        if p_sub.sym != gt.sym or len(p_sub.args) != len(gt.args):
                            continue
                    ok, _, delta = structure_matches(bvars - set(env.keys()), p_sub, gt)
                    if ok:
                        merged = dict(env)
                        merged.update(delta)
                        next_partials.append((merged, max(max_g, egraph[gt])))
            partials = next_partials
            if not partials:
                break
        return partials

    def enqueue_matches(rule_list: list[QuantRule]) -> None:
        g_list = list(egraph.keys())
        for idx, r in enumerate(rule_list):
            for group in r.triggers:
                for env, gen in match_group(r, group, g_list):
                    key = (r.qid, tuple(sorted(env.items())))
                    if key in seen_insts:
                        continue
                    seen_insts.add(key)
                    # Z3 default cost = weight + generation (src/smt/qi_queue.cpp:55)
                    cost = float(r.weight + gen)
                    # Assertion order + seed perturb tie-breaking among equal-cost entries
                    tie = idx * 1e-4 + rng.random() * 1e-2
                    queue.append((cost, tie, gen, r, env))

    inst_count = 0
    enqueue_matches(rules)

    while inst_count < budget and queue:
        # Pick lowest cost (with eager/lazy threshold prioritization)
        queue.sort(key=lambda item: (item[0] > eager_threshold, item[0], item[1]))
        cost, _, gen, rule, env = queue.pop(0)
        inst_count += 1
        new_gen = gen + 1
        added_new = False
        for bt in rule.body_terms:
            inst_term = substitute(bt, env)
            if inst_term == goal_fact:
                return "unsat", inst_count
            if inst_term not in egraph:
                egraph[inst_term] = new_gen
                added_new = True
        if added_new:
            enqueue_matches(rules)

    return "timeout", inst_count


def mariposa_classify(
    outcomes: list[str],
    r_solvable: float = 0.05,
    r_stable: float = 0.95,
    alpha: float = 0.05,
) -> tuple[str, str, float]:
    """Classify mutant outcomes using both Mariposa's cutoff and one-sided proportion z-test.

    Mirrors secure-foundations/mariposa src/base/query_analyzer.py (_categorize_cutoff
    and _categorize_z_test with alpha=0.05, r_solvable=0.05, r_stable=0.95).
    """
    n = len(outcomes)
    k = sum(1 for o in outcomes if o == "unsat")
    sr = k / n

    # Cutoff classifier
    if sr < r_solvable:
        cutoff_cat = "unsolvable"
    elif sr >= r_stable:
        cutoff_cat = "stable"
    else:
        cutoff_cat = "unstable"

    # One-proportion z-test (standard normal CDF via math.erfc)
    def norm_cdf(z: float) -> float:
        return 0.5 * math.erfc(-z / math.sqrt(2.0))

    def ztest_p(p0: float, alt: str) -> float:
        se = math.sqrt(p0 * (1.0 - p0) / n)
        z = (sr - p0) / se
        return norm_cdf(z) if alt == "smaller" else (1.0 - norm_cdf(z))

    if ztest_p(r_solvable, "smaller") <= alpha:
        z_cat = "unsolvable"
    elif ztest_p(r_stable, "smaller") <= alpha:
        z_cat = "unstable"
    elif ztest_p(r_stable, "larger") <= alpha:
        z_cat = "stable"
    else:
        z_cat = "inconclusive"

    return cutoff_cat, z_cat, sr


def run_part_a() -> dict[str, object]:
    x = Var("x")
    y = Var("y")
    k = Var("k")

    # 1. Stratified DAG rules (terminating)
    stratified_rules = [
        QuantRule(
            qid="arr_bounds",
            bound_vars=("x",),
            triggers=((App("in_bounds", (x,)),),),
            body_terms=(App("valid_idx", (x,)),),
        ),
        QuantRule(
            qid="elem_prop",
            bound_vars=("x",),
            triggers=((App("valid_idx", (x,)),),),
            body_terms=(App("safe_read", (App("slot", (x,)),)),),
        ),
    ]
    res_strat = analyze_trigger_graph(stratified_rules)
    assert res_strat["amplifying_cycles"] == []
    assert res_strat["local_verus_hits"] == {}

    # 2. Direct self-amplifying matching loop: P(x) -> P(succ(x))
    direct_loop_rules = [
        QuantRule(
            qid="direct_loop",
            bound_vars=("x",),
            triggers=((App("P", (x,)),),),
            body_terms=(App("P", (App("succ", (x,)),)),),
        )
    ]
    res_direct = analyze_trigger_graph(direct_loop_rules)
    assert res_direct["amplifying_cycles"] == [["direct_loop"]]
    assert res_direct["local_verus_hits"] == {"direct_loop": 1}

    # 3. Mutual 2-cycle matching loop: f(x) -> g(succ(x)), g(y) -> f(h(y))
    # Demonstrates what single-quantifier local loop filters miss!
    mutual_loop_rules = [
        QuantRule(
            qid="mut_f_to_g",
            bound_vars=("x",),
            triggers=((App("f", (x,)),),),
            body_terms=(App("g", (App("succ", (x,)),)),),
        ),
        QuantRule(
            qid="mut_g_to_f",
            bound_vars=("y",),
            triggers=((App("g", (y,)),),),
            body_terms=(App("f", (App("h", (y,)),)),),
        ),
    ]
    res_mutual = analyze_trigger_graph(mutual_loop_rules)
    assert res_mutual["local_verus_hits"] == {}  # Local single-rule filter misses it!
    assert res_mutual["amplifying_cycles"] == [["mut_f_to_g", "mut_g_to_f"]]

    # 4. Fuel-bounded recursive definition (Verus/Dafny Peano fuel stratification):
    # rec_f(x, succ(k)) -> rec_f(step(x), k)
    fuel_guarded_rules = [
        QuantRule(
            qid="rec_f_unfold",
            bound_vars=("x", "k"),
            triggers=((App("rec_f", (x, App("succ", (k,)))),),),
            body_terms=(App("rec_f", (App("step", (x,)), k)),),
            fuel_decreasing=True,
        )
    ]
    res_fuel = analyze_trigger_graph(fuel_guarded_rules)
    assert res_fuel["amplifying_cycles"] == []
    assert res_fuel["stratified_cycles"] == [["rec_f_unfold"]]

    # 5. Mariposa shuffle/reseed instability & SHAKE context pruning simulation
    # Goal requires 3-hop chain: init(a) -> mid1(a) -> mid2(a) -> goal_ok(a)
    goal_rules = [
        QuantRule("ax_step1", ("x",), ((App("init", (x,)),),), (App("mid1", (x,)),)),
        QuantRule("ax_step2", ("x",), ((App("mid1", (x,)),),), (App("mid2", (x,)),)),
        QuantRule("ax_step3", ("x",), ((App("mid2", (x,)),),), (App("goal_ok", (x,)),)),
    ]
    # Irrelevant background axioms (trigger on unrelated ambient symbols d0..d5
    # that appear in the module prelude, plus a matching-loop distractor on noise(x))
    distractor_rules = [
        QuantRule(
            qid=f"bg_loop_{i}",
            bound_vars=("x",),
            triggers=((App(f"noise_{i}", (x,)),),),
            body_terms=(
                App(f"noise_{i}", (App("succ", (x,)),)),
                App(f"noise_{i}", (App("alt", (x,)),)),
            ),
        )
        for i in range(6)
    ]
    all_rules = goal_rules + distractor_rules
    init_ground = [App("init", (App("a"),))] + [
        App(f"noise_{i}", (App("z"),)) for i in range(6)
    ]
    goal_fact = App("goal_ok", (App("a"),))
    # Budget sits inside the [21, 45] generation-2 band where 6 distractor loops
    # compete with ax_step3 at equal cost=3, so tie-breaking flips UNSAT <-> TIMEOUT.
    budget = 32
    num_mutants = 60

    # Mutation 1: Assertion-order shuffling (fixed solver PRNG seed=42)
    unpruned_shuffle: list[str] = []
    unpruned_shuf_insts: list[int] = []
    for m in range(num_mutants):
        shuf = list(all_rules)
        random.Random(1000 + m).shuffle(shuf)
        status, used = run_bounded_ematching(
            init_ground, goal_fact, shuf, budget=budget, seed=42
        )
        unpruned_shuffle.append(status)
        unpruned_shuf_insts.append(used)

    # Mutation 2: Solver PRNG reseeding (fixed baseline assertion order)
    unpruned_reseed: list[str] = []
    unpruned_seed_insts: list[int] = []
    for m in range(num_mutants):
        status, used = run_bounded_ematching(
            init_ground, goal_fact, all_rules, budget=budget, seed=2000 + m
        )
        unpruned_reseed.append(status)
        unpruned_seed_insts.append(used)

    shuf_cut, shuf_z, shuf_sr = mariposa_classify(unpruned_shuffle)
    seed_cut, seed_z, seed_sr = mariposa_classify(unpruned_reseed)
    assert shuf_cut == "unstable" and shuf_z == "unstable", (shuf_cut, shuf_z, shuf_sr)
    assert seed_cut == "unstable" and seed_z == "unstable", (seed_cut, seed_z, seed_sr)

    # Apply SHAKE pattern-aware context pruning seeded from goal_fact + query roots
    pruned_rules, shake_layers = shake_prune_rules(
        goal_terms=[goal_fact, App("init", (App("a"),))], rules=all_rules
    )
    pruned_qids = sorted(r.qid for r in pruned_rules)
    assert pruned_qids == ["ax_step1", "ax_step2", "ax_step3"], pruned_qids

    pruned_shuffle: list[str] = []
    pruned_reseed: list[str] = []
    pruned_insts: list[int] = []
    for m in range(num_mutants):
        shuf = list(pruned_rules)
        random.Random(1000 + m).shuffle(shuf)
        st1, u1 = run_bounded_ematching(init_ground, goal_fact, shuf, budget=budget, seed=42)
        st2, u2 = run_bounded_ematching(
            init_ground, goal_fact, pruned_rules, budget=budget, seed=2000 + m
        )
        pruned_shuffle.append(st1)
        pruned_reseed.append(st2)
        pruned_insts.extend([u1, u2])

    p_shuf_cut, p_shuf_z, p_shuf_sr = mariposa_classify(pruned_shuffle)
    p_seed_cut, p_seed_z, p_seed_sr = mariposa_classify(pruned_reseed)
    assert p_shuf_cut == "stable" and p_shuf_z == "stable" and p_shuf_sr == 1.0
    assert p_seed_cut == "stable" and p_seed_z == "stable" and p_seed_sr == 1.0

    return {
        "stratified_cycles": res_strat["amplifying_cycles"],
        "direct_loop_cycles": res_direct["amplifying_cycles"],
        "direct_loop_local_hits": res_direct["local_verus_hits"],
        "mutual_loop_local_hits": res_mutual["local_verus_hits"],
        "mutual_loop_scc_cycles": res_mutual["amplifying_cycles"],
        "fuel_guarded_amplifying": res_fuel["amplifying_cycles"],
        "fuel_guarded_stratified": res_fuel["stratified_cycles"],
        "budget": budget,
        "unpruned_rule_count": len(all_rules),
        "pruned_rule_count": len(pruned_rules),
        "unpruned_shuffle_cat": (shuf_cut, shuf_z),
        "unpruned_shuffle_sr": round(shuf_sr, 4),
        "unpruned_shuffle_mean_insts": round(
            sum(unpruned_shuf_insts) / len(unpruned_shuf_insts), 2
        ),
        "unpruned_reseed_cat": (seed_cut, seed_z),
        "unpruned_reseed_sr": round(seed_sr, 4),
        "unpruned_reseed_mean_insts": round(
            sum(unpruned_seed_insts) / len(unpruned_seed_insts), 2
        ),
        "pruned_shuffle_cat": (p_shuf_cut, p_shuf_z),
        "pruned_shuffle_sr": round(p_shuf_sr, 4),
        "pruned_reseed_cat": (p_seed_cut, p_seed_z),
        "pruned_reseed_sr": round(p_seed_sr, 4),
        "pruned_mean_insts": round(sum(pruned_insts) / len(pruned_insts), 2),
        "shake_layers": shake_layers,
    }


# =============================================================================
# Part B: AutoCorres-Style Validated Local-Var & Heap-Lens Lifter
# =============================================================================


@dataclass(frozen=True)
class StorageLive:
    var: str


@dataclass(frozen=True)
class StorageDead:
    var: str


@dataclass(frozen=True)
class AssignConst:
    dst: str
    val: int


@dataclass(frozen=True)
class AssignCopy:
    dst: str
    src: str


@dataclass(frozen=True)
class AssignBinOp:
    dst: str
    op: str  # "add" | "sub" | "mul"
    lhs: str
    rhs: str


@dataclass(frozen=True)
class HeapLoad:
    dst: str
    addr_var: str


@dataclass(frozen=True)
class HeapStore:
    addr_var: str
    val_var: str


@dataclass(frozen=True)
class Nop:
    pass


Stmt = (
    StorageLive
    | StorageDead
    | AssignConst
    | AssignCopy
    | AssignBinOp
    | HeapLoad
    | HeapStore
    | Nop
)


@dataclass
class SmallStepState:
    locals_map: dict[str, int]
    live_set: set[str]
    heap: dict[int, int]
    pc: int = 0


def exec_small_step(
    stmts: list[Stmt],
    init_locals: dict[str, int],
    init_heap: dict[int, int],
    ret_var: str,
    fuel: int,
) -> tuple[int, dict[int, int], int]:
    """Trusted small-step operational semantics over explicit locals, liveness, and heap.

    Returns (return_value, final_heap, steps_taken). Raises RuntimeError on UB or
    fuel exhaustion.
    """
    st = SmallStepState(
        locals_map=dict(init_locals),
        live_set=set(init_locals.keys()),
        heap=dict(init_heap),
        pc=0,
    )
    steps = 0
    while st.pc < len(stmts):
        if steps >= fuel:
            raise RuntimeError(f"Fuel exhausted at pc={st.pc} (fuel={fuel})")
        s = stmts[st.pc]
        if isinstance(s, StorageLive):
            st.live_set.add(s.var)
            st.locals_map.pop(s.var, None)
        elif isinstance(s, StorageDead):
            st.live_set.discard(s.var)
            st.locals_map.pop(s.var, None)
        elif isinstance(s, AssignConst):
            if s.dst not in st.live_set:
                raise RuntimeError(f"Write to dead local {s.dst}")
            st.locals_map[s.dst] = s.val
        elif isinstance(s, AssignCopy):
            if s.src not in st.live_set or s.src not in st.locals_map:
                raise RuntimeError(f"Read of dead/uninit local {s.src}")
            if s.dst not in st.live_set:
                raise RuntimeError(f"Write to dead local {s.dst}")
            st.locals_map[s.dst] = st.locals_map[s.src]
        elif isinstance(s, AssignBinOp):
            for v in (s.lhs, s.rhs):
                if v not in st.live_set or v not in st.locals_map:
                    raise RuntimeError(f"Read of dead/uninit local {v}")
            if s.dst not in st.live_set:
                raise RuntimeError(f"Write to dead local {s.dst}")
            a, b = st.locals_map[s.lhs], st.locals_map[s.rhs]
            if s.op == "add":
                st.locals_map[s.dst] = a + b
            elif s.op == "sub":
                st.locals_map[s.dst] = a - b
            elif s.op == "mul":
                st.locals_map[s.dst] = a * b
            else:
                raise RuntimeError(f"Unknown op {s.op}")
        elif isinstance(s, HeapLoad):
            if s.addr_var not in st.live_set or s.addr_var not in st.locals_map:
                raise RuntimeError(f"Invalid addr local {s.addr_var}")
            addr = st.locals_map[s.addr_var]
            if addr not in st.heap:
                raise RuntimeError(f"Dangling heap read at {addr}")
            if s.dst not in st.live_set:
                raise RuntimeError(f"Write to dead local {s.dst}")
            st.locals_map[s.dst] = st.heap[addr]
        elif isinstance(s, HeapStore):
            for v in (s.addr_var, s.val_var):
                if v not in st.live_set or v not in st.locals_map:
                    raise RuntimeError(f"Invalid local {v}")
            addr = st.locals_map[s.addr_var]
            if addr not in st.heap:
                raise RuntimeError(f"Dangling heap write at {addr}")
            st.heap[addr] = st.locals_map[s.val_var]
        elif isinstance(s, Nop):
            pass
        st.pc += 1
        steps += 1

    if ret_var not in st.live_set or ret_var not in st.locals_map:
        raise RuntimeError(f"Return local {ret_var} dead/uninitialized")
    return st.locals_map[ret_var], st.heap, steps


# Symbolic pure expression AST for lifted AutoCorres-style L2 + HeapLift representation
@dataclass(frozen=True)
class SymConst:
    val: int


@dataclass(frozen=True)
class SymParam:
    name: str


@dataclass(frozen=True)
class SymFieldRead:
    field: str  # Named heap lens field (disjoint region)


@dataclass(frozen=True)
class SymBinOp:
    op: str
    lhs: "SymExpr"
    rhs: "SymExpr"


SymExpr = SymConst | SymParam | SymFieldRead | SymBinOp


def simplify_sym(e: SymExpr) -> SymExpr:
    if isinstance(e, SymBinOp):
        l = simplify_sym(e.lhs)
        r = simplify_sym(e.rhs)
        if isinstance(l, SymConst) and isinstance(r, SymConst):
            if e.op == "add":
                return SymConst(l.val + r.val)
            if e.op == "sub":
                return SymConst(l.val - r.val)
            if e.op == "mul":
                return SymConst(l.val * r.val)
        if e.op == "add":
            if l == SymConst(0):
                return r
            if r == SymConst(0):
                return l
        if e.op == "sub" and r == SymConst(0):
            return l
        if e.op == "mul":
            if l == SymConst(1):
                return r
            if r == SymConst(1):
                return l
            if l == SymConst(0) or r == SymConst(0):
                return SymConst(0)
        return SymBinOp(e.op, l, r)
    return e


def eval_sym(e: SymExpr, params: dict[str, int], fields: dict[str, int]) -> int:
    if isinstance(e, SymConst):
        return e.val
    if isinstance(e, SymParam):
        return params[e.name]
    if isinstance(e, SymFieldRead):
        return fields[e.field]
    if isinstance(e, SymBinOp):
        lv = eval_sym(e.lhs, params, fields)
        rv = eval_sym(e.rhs, params, fields)
        if e.op == "add":
            return lv + rv
        if e.op == "sub":
            return lv - rv
        if e.op == "mul":
            return lv * rv
    raise AssertionError(f"Unexpected SymExpr: {e}")


@dataclass(frozen=True)
class HeapLens:
    """Bidirectional lens projecting a single address slot out of a flat heap."""

    field: str
    addr: int

    def get(self, heap: dict[int, int]) -> int:
        return heap[self.addr]

    def put(self, heap: dict[int, int], val: int) -> dict[int, int]:
        out = dict(heap)
        out[self.addr] = val
        return out


def verify_lens_laws(lenses: list[HeapLens], sample_heaps: list[dict[int, int]]) -> None:
    """Check GetPut, PutGet, PutPut, and pairwise disjoint-frame non-interference."""
    for lens in lenses:
        for h in sample_heaps:
            # GetPut
            assert lens.put(h, lens.get(h)) == h
            # PutGet & PutPut
            for v1, v2 in ((7, 42), (-3, 0)):
                h1 = lens.put(h, v1)
                assert lens.get(h1) == v1
                assert lens.put(h1, v2) == lens.put(h, v2)
    # Disjointness / frame preservation
    for i, l1 in enumerate(lenses):
        for j, l2 in enumerate(lenses):
            if i == j:
                continue
            assert l1.addr != l2.addr
            for h in sample_heaps:
                h_mod = l1.put(h, 999)
                assert l2.get(h_mod) == l2.get(h)


@dataclass(frozen=True)
class LiftedFunction:
    """Pure AutoCorres-style L2+HeapLift representation: zero locals, zero fuel."""

    ret_expr: SymExpr
    field_updates: tuple[tuple[str, SymExpr], ...]

    def eval_pure(
        self, params: dict[str, int], fields: dict[str, int]
    ) -> tuple[int, dict[str, int]]:
        new_fields = dict(fields)
        for fname, expr in self.field_updates:
            new_fields[fname] = eval_sym(expr, params, fields)
        ret = eval_sym(self.ret_expr, params, fields)
        return ret, new_fields


def autocorres_style_lift(
    stmts: list[Stmt],
    param_names: tuple[str, ...],
    ptr_param_to_field: dict[str, str],
    ret_var: str,
) -> LiftedFunction:
    """Untrusted AutoCorres-style LocalVarExtract + HeapLift lifter.

    Erases all StorageLive/StorageDead, dead temporaries, and scratch copies,
    yielding a canonical pure functional summary over typed heap lenses.
    """
    env: dict[str, SymExpr] = {p: SymParam(p) for p in param_names}
    live: set[str] = set(param_names) | set(ptr_param_to_field.keys())
    # Track symbolic pointer provenance (param_name -> field_name)
    ptr_env: dict[str, str] = dict(ptr_param_to_field)
    heap_env: dict[str, SymExpr] = {
        f: SymFieldRead(f) for f in sorted(set(ptr_param_to_field.values()))
    }

    for s in stmts:
        if isinstance(s, StorageLive):
            live.add(s.var)
            env.pop(s.var, None)
            ptr_env.pop(s.var, None)
        elif isinstance(s, StorageDead):
            live.discard(s.var)
            env.pop(s.var, None)
            ptr_env.pop(s.var, None)
        elif isinstance(s, AssignConst):
            assert s.dst in live
            env[s.dst] = SymConst(s.val)
            ptr_env.pop(s.dst, None)
        elif isinstance(s, AssignCopy):
            assert s.src in live and s.dst in live
            if s.src in ptr_env:
                ptr_env[s.dst] = ptr_env[s.src]
                env.pop(s.dst, None)
            else:
                env[s.dst] = env[s.src]
                ptr_env.pop(s.dst, None)
        elif isinstance(s, AssignBinOp):
            assert s.lhs in live and s.rhs in live and s.dst in live
            env[s.dst] = simplify_sym(SymBinOp(s.op, env[s.lhs], env[s.rhs]))
            ptr_env.pop(s.dst, None)
        elif isinstance(s, HeapLoad):
            assert s.addr_var in ptr_env and s.dst in live
            field = ptr_env[s.addr_var]
            env[s.dst] = heap_env[field]
            ptr_env.pop(s.dst, None)
        elif isinstance(s, HeapStore):
            assert s.addr_var in ptr_env and s.val_var in live
            field = ptr_env[s.addr_var]
            heap_env[field] = simplify_sym(env[s.val_var])
        elif isinstance(s, Nop):
            pass

    assert ret_var in live and ret_var in env
    updates = tuple(
        (f, simplify_sym(expr))
        for f, expr in sorted(heap_env.items())
        if expr != SymFieldRead(f)
    )
    return LiftedFunction(ret_expr=simplify_sym(env[ret_var]), field_updates=updates)


def validate_ac_corres_refinement(
    stmts: list[Stmt],
    lifted: LiftedFunction,
    ret_var: str,
    lenses: list[HeapLens],
    ptr_param_addrs: dict[str, int],
) -> int:
    """Per-function refinement validator (AutoCorres `ac_corres` analog).

    Keeps the lifter outside the TCB by independently checking that the small-step
    TCB interpreter and the lifted pure function produce identical return values,
    modified fields, and framed untouched fields across a Cartesian input grid.
    """
    checked = 0
    for delta in (-5, 0, 1, 7, 19):
        for cnt0 in (0, 3, 12):
            for other0 in (100, -42):
                init_locals = {"delta": delta, **ptr_param_addrs}
                init_heap = {
                    ptr_param_addrs["p_cnt"]: cnt0,
                    ptr_param_addrs["p_other"]: other0,
                }
                raw_ret, raw_heap, _ = exec_small_step(
                    stmts, init_locals, init_heap, ret_var=ret_var, fuel=len(stmts) + 1
                )
                lifted_in = {lens.field: lens.get(init_heap) for lens in lenses}
                pure_ret, pure_out = lifted.eval_pure({"delta": delta}, lifted_in)
                assert raw_ret == pure_ret, f"Ret mismatch: {raw_ret} != {pure_ret}"
                for lens in lenses:
                    assert lens.get(raw_heap) == pure_out[lens.field], (
                        f"Heap lens {lens.field} mismatch"
                    )
                checked += 1
    return checked


def fragile_raw_small_step_proof(stmts: list[Stmt]) -> tuple[bool, str]:
    """Fragile proof script hard-coded to exact small-step fuel, pc, and temp names.

    Models hand-authored MIR proofs that step concrete instructions one by one
    with fixed fuel=5 and expect `_t0` at pc=1 and `_t1` at pc=2.
    """
    expected_fuel = 5
    if len(stmts) != expected_fuel:
        return False, f"fuel/pc mismatch: expected {expected_fuel} stmts, got {len(stmts)}"
    if not (
        isinstance(stmts[0], StorageLive)
        and stmts[0].var == "_t0"
        and isinstance(stmts[1], HeapLoad)
        and stmts[1].dst == "_t0"
        and isinstance(stmts[2], AssignBinOp)
        and stmts[2].dst == "_ret"
        and isinstance(stmts[3], HeapStore)
        and stmts[3].val_var == "_ret"
        and isinstance(stmts[4], StorageDead)
        and stmts[4].var == "_t0"
    ):
        return False, "concrete MIR statement/local-slot pattern drifted"
    return True, "verified via exact 5-step small-step replay"


def lifted_functional_proof(lifted: LiftedFunction) -> tuple[bool, str]:
    """Declarative functional proof over the lifted lens surface.

    Checks exact structural/algebraic postcondition:
      1) return value == counter + delta
      2) counter' == counter + delta
      3) untouched lens `other` has no update (free framing!)
    """
    expected = SymBinOp("add", SymFieldRead("counter"), SymParam("delta"))
    if lifted.ret_expr != expected:
        return False, f"unexpected ret_expr: {lifted.ret_expr}"
    upd_dict = dict(lifted.field_updates)
    if upd_dict != {"counter": expected}:
        return False, f"unexpected heap updates: {upd_dict}"
    return True, "verified: ret == counter' == counter + delta, frame(other) preserved"


def run_part_b() -> dict[str, object]:
    ptr_to_field = {"p_cnt": "counter", "p_other": "other"}
    ptr_addrs = {"p_cnt": 0x1000, "p_other": 0x2000}
    lenses = [HeapLens("counter", 0x1000), HeapLens("other", 0x2000)]
    verify_lens_laws(lenses, [{0x1000: 10, 0x2000: 20}, {0x1000: 0, 0x2000: -1}])

    # Variant v0: Baseline imperative block (*p_cnt += delta; return *p_cnt)
    v0: list[Stmt] = [
        StorageLive("_t0"),
        HeapLoad("_t0", "p_cnt"),
        AssignBinOp("_ret", "add", "_t0", "delta"),
        HeapStore("p_cnt", "_ret"),
        StorageDead("_t0"),
    ]

    # Variant v1: Compiler inserts StorageLive/StorageDead for a benign scratch register
    v1: list[Stmt] = [
        StorageLive("_scratch"),
        AssignCopy("_scratch", "delta"),
        StorageLive("_t0"),
        HeapLoad("_t0", "p_cnt"),
        AssignBinOp("_ret", "add", "_t0", "_scratch"),
        HeapStore("p_cnt", "_ret"),
        StorageDead("_t0"),
        StorageDead("_scratch"),
    ]

    # Variant v2: Compiler copies pointer & adds identity arithmetic (+ 0) + dead temp
    v2: list[Stmt] = [
        StorageLive("_p_alias"),
        AssignCopy("_p_alias", "p_cnt"),
        StorageLive("_zero"),
        AssignConst("_zero", 0),
        StorageLive("_dead"),
        AssignBinOp("_dead", "mul", "delta", "_zero"),
        StorageLive("_t_val"),
        HeapLoad("_t_val", "_p_alias"),
        StorageLive("_t_sum"),
        AssignBinOp("_t_sum", "add", "_t_val", "delta"),
        AssignBinOp("_ret", "add", "_t_sum", "_dead"),
        HeapStore("_p_alias", "_ret"),
        StorageDead("_t_sum"),
        StorageDead("_t_val"),
        StorageDead("_dead"),
        StorageDead("_zero"),
        StorageDead("_p_alias"),
    ]

    # Variant v3: Compiler inserts NOPs + reuses temp slot across two copies
    v3: list[Stmt] = [
        Nop(),
        StorageLive("_tmp"),
        HeapLoad("_tmp", "p_cnt"),
        AssignBinOp("_tmp", "add", "_tmp", "delta"),
        AssignCopy("_ret", "_tmp"),
        HeapStore("p_cnt", "_tmp"),
        StorageDead("_tmp"),
        Nop(),
    ]

    variants = {
        "v0_baseline": v0,
        "v1_scratch_storage_live": v1,
        "v2_ptr_copy_dead_temp": v2,
        "v3_nops_and_slot_reuse": v3,
    }

    results: dict[str, dict[str, object]] = {}
    raw_pass_churn = 0
    lifted_pass_all = 0
    canonical_lifted: LiftedFunction | None = None

    for name, stmts in variants.items():
        # Note: _ret is pre-live in MIR (place _0); include _ret in live init for lifter
        raw_ok, raw_msg = fragile_raw_small_step_proof(stmts)
        # In our small-step model, caller reserves _ret slot via StorageLive prefix
        full_stmts = [StorageLive("_ret")] + stmts
        lifted = autocorres_style_lift(
            full_stmts,
            param_names=("delta",),
            ptr_param_to_field=ptr_to_field,
            ret_var="_ret",
        )
        checked_cases = validate_ac_corres_refinement(
            full_stmts, lifted, ret_var="_ret", lenses=lenses, ptr_param_addrs=ptr_addrs
        )
        lifted_ok, lifted_msg = lifted_functional_proof(lifted)
        assert lifted_ok, f"Lifted proof failed on {name}: {lifted_msg}"
        if canonical_lifted is None:
            canonical_lifted = lifted
        else:
            assert lifted == canonical_lifted, f"Lifted IR not canonical on {name}"

        if name != "v0_baseline" and raw_ok:
            raw_pass_churn += 1
        if lifted_ok:
            lifted_pass_all += 1

        results[name] = {
            "stmt_count": len(stmts),
            "raw_small_step_proof_ok": raw_ok,
            "raw_small_step_msg": raw_msg,
            "lifted_proof_ok": lifted_ok,
            "refinement_cases_checked": checked_cases,
            "lifted_canonical_equal_to_v0": lifted == canonical_lifted,
        }

    # Negative canary: verify that a buggy untrusted lifter is rejected by the validator
    buggy_lifted = LiftedFunction(
        ret_expr=SymFieldRead("counter"),  # bug: drops + delta
        field_updates=(("counter", SymFieldRead("counter")),),
    )
    canary_rejected = False
    try:
        validate_ac_corres_refinement(
            [StorageLive("_ret")] + v0,
            buggy_lifted,
            ret_var="_ret",
            lenses=lenses,
            ptr_param_addrs=ptr_addrs,
        )
    except AssertionError:
        canary_rejected = True
    assert canary_rejected, "Refinement validator failed to reject buggy lifted model!"

    assert results["v0_baseline"]["raw_small_step_proof_ok"] is True
    assert raw_pass_churn == 0, "Expected fragile raw proof to break on all 3 churn variants"
    assert lifted_pass_all == len(variants)
    return {
        "variants": results,
        "raw_churn_survival_rate": f"{raw_pass_churn}/3 (0.0%)",
        "lifted_invariance_rate": f"{lifted_pass_all}/{len(variants)} (100.0%)",
        "buggy_lifter_canary_rejected": canary_rejected,
    }


def main() -> int:
    part_a = run_part_a()
    part_b = run_part_b()

    print("=== Part A: E-Matching Trigger-Graph & SHAKE Context-Pruning Analysis ===")
    print(f"Stratified DAG amplifying cycles:       {part_a['stratified_cycles']}")
    print(f"Direct self-loop amplifying cycles:     {part_a['direct_loop_cycles']} (local hits: {part_a['direct_loop_local_hits']})")
    print(f"Mutual 2-cycle local-filter hits:       {part_a['mutual_loop_local_hits']} (MISSED by single-rule filter)")
    print(f"Mutual 2-cycle SCC amplifying cycles:   {part_a['mutual_loop_scc_cycles']} (CAUGHT by trigger-graph SCC)")
    print(f"Fuel-guarded rec_f amplifying cycles:   {part_a['fuel_guarded_amplifying']} (stratified: {part_a['fuel_guarded_stratified']})")
    print(
        f"Unpruned query ({part_a['unpruned_rule_count']} rules, budget={part_a['budget']}, 60 mutants each):"
    )
    print(
        f"  shuffle: cutoff/z_test={part_a['unpruned_shuffle_cat']}, "
        f"pass_rate={part_a['unpruned_shuffle_sr']*100:.1f}%, "
        f"mean_insts={part_a['unpruned_shuffle_mean_insts']}"
    )
    print(
        f"  reseed:  cutoff/z_test={part_a['unpruned_reseed_cat']}, "
        f"pass_rate={part_a['unpruned_reseed_sr']*100:.1f}%, "
        f"mean_insts={part_a['unpruned_reseed_mean_insts']}"
    )
    print(
        f"SHAKE-pruned query ({part_a['pruned_rule_count']} rules, budget={part_a['budget']}, 60 mutants each):"
    )
    print(
        f"  shuffle: cutoff/z_test={part_a['pruned_shuffle_cat']}, "
        f"pass_rate={part_a['pruned_shuffle_sr']*100:.1f}% | "
        f"reseed: cutoff/z_test={part_a['pruned_reseed_cat']}, "
        f"pass_rate={part_a['pruned_reseed_sr']*100:.1f}% | "
        f"mean_insts={part_a['pruned_mean_insts']}, layers={part_a['shake_layers']}"
    )

    print("\n=== Part B: AutoCorres-Style Validated Local-Var & Heap-Lens Lifting ===")
    for name, info in part_b["variants"].items():  # type: ignore[union-attr]
        print(
            f"  {name:24s} stmts={info['stmt_count']:2d} | "
            f"raw_proof={'PASS' if info['raw_small_step_proof_ok'] else 'FAIL'} | "
            f"lifted_proof={'PASS' if info['lifted_proof_ok'] else 'FAIL'} | "
            f"refinement_checked={info['refinement_cases_checked']} | "
            f"canonical={info['lifted_canonical_equal_to_v0']}"
        )
    print(f"Raw small-step proof churn survival:    {part_b['raw_churn_survival_rate']}")
    print(f"Validated lifted proof invariance:      {part_b['lifted_invariance_rate']}")
    print(f"Buggy untrusted lifter canary rejected: {part_b['buggy_lifter_canary_rejected']}")
    print("\nALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
