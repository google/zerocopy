#!/usr/bin/env python3
"""Standalone probabilistic-programming semantics and inference verification probe.

Requires Python 3.10+ (standard library only). Deterministically demonstrates
and verifies three foundational PPL semantic hazards and compiler techniques:

  1. Exact discrete inference via ROBDD compilation + Weighted Model Counting
     (Dice-style): verifies exact rational posterior agreement against
     exhaustive 2^n enumeration (including branch-guarded observations), linear
     O(k) BDD scaling on factored Markov chains, and exponential 2^k BDD width
     blowup on unfactored / badly ordered parity systems.
  2. Borel-Kolmogorov coordinate-change paradox under naive epsilon-ball
     measure-zero conditioning on X = Y for X, Y ~ i.i.d. Uniform(0, 1):
     shows |X - Y| <= eps converges to Uniform(0, 1) (E[X] = 1/2) while
     |X / Y - 1| <= eps converges to Beta(2, 1) (E[X] = 2/3), matching exact
     Radon-Nikodym / symbolic disintegration Jacobian factors, plus the
     classical meridian-vs-equator spherical great-circle discrepancy.
  3. Variational guide-support static checker (supp(q) subseteq supp(p) and
     absolute continuity q << p) catching the Pyro Bayesian Regression
     Uniform(0, 10) vs Normal(1.0, 0.05) bug and LDA Dirichlet vs Delta
     singularity, contrasted with finite-sample Monte Carlo ELBO estimation
     silently masking KL(q || p) = +inf over 100,000 draws.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
import math
import random
import sys
from typing import Any


# =============================================================================
# Part 1: Dice-style ROBDD + Exact Rational Weighted Model Counting Compiler
# =============================================================================


class ROBDDManager:
    """Minimal reduced ordered BDD manager with hash-consed unique table."""

    FALSE = 0
    TRUE = 1

    def __init__(self) -> None:
        # node_id -> (var_index, low_id, high_id); 0 and 1 are terminal nodes
        self.nodes: list[tuple[int, int, int] | None] = [None, None]
        self.unique: dict[tuple[int, int, int], int] = {}
        self.ite_cache: dict[tuple[int, int, int], int] = {}
        self.weights: dict[int, tuple[Fraction, Fraction]] = {}
        self.var_names: dict[int, str] = {}
        self._next_var = 0

    def new_var(self, p_true: Fraction, name: str | None = None) -> tuple[int, int]:
        """Allocate a fresh ordered BDD variable with exact weights (1-p, p)."""
        if not (Fraction(0) <= p_true <= Fraction(1)):
            raise ValueError(f"Flip probability {p_true} outside [0, 1]")
        v = self._next_var
        self._next_var += 1
        self.weights[v] = (Fraction(1) - p_true, p_true)
        self.var_names[v] = name or f"f{v}"
        return v, self.mk(v, self.FALSE, self.TRUE)

    def mk(self, var: int, low: int, high: int) -> int:
        if low == high:
            return low
        key = (var, low, high)
        existing = self.unique.get(key)
        if existing is not None:
            return existing
        nid = len(self.nodes)
        self.nodes.append(key)
        self.unique[key] = nid
        return nid

    def _top_var(self, u: int) -> int | None:
        if u <= 1:
            return None
        node = self.nodes[u]
        assert node is not None
        return node[0]

    def _cofactor(self, u: int, var: int, val: bool) -> int:
        if u <= 1:
            return u
        node = self.nodes[u]
        assert node is not None
        v, lo, hi = node
        if v == var:
            return hi if val else lo
        return u

    def ite(self, f: int, g: int, h: int) -> int:
        if f == self.TRUE:
            return g
        if f == self.FALSE:
            return h
        if g == h:
            return g
        if g == self.TRUE and h == self.FALSE:
            return f
        key = (f, g, h)
        cached = self.ite_cache.get(key)
        if cached is not None:
            return cached
        candidates = [v for v in (self._top_var(f), self._top_var(g), self._top_var(h)) if v is not None]
        v = min(candidates)
        hi = self.ite(self._cofactor(f, v, True), self._cofactor(g, v, True), self._cofactor(h, v, True))
        lo = self.ite(self._cofactor(f, v, False), self._cofactor(g, v, False), self._cofactor(h, v, False))
        res = self.mk(v, lo, hi)
        self.ite_cache[key] = res
        return res

    def not_(self, u: int) -> int:
        return self.ite(u, self.FALSE, self.TRUE)

    def and_(self, u: int, v: int) -> int:
        return self.ite(u, v, self.FALSE)

    def or_(self, u: int, v: int) -> int:
        return self.ite(u, self.TRUE, v)

    def xor_(self, u: int, v: int) -> int:
        return self.ite(u, self.not_(v), v)

    def iff_(self, u: int, v: int) -> int:
        return self.ite(u, v, self.not_(v))

    def wmc(self, root: int) -> Fraction:
        """Linear-time memoized exact rational Weighted Model Count over BDD DAG."""
        memo: dict[int, Fraction] = {self.FALSE: Fraction(0), self.TRUE: Fraction(1)}

        def rec(u: int) -> Fraction:
            if u in memo:
                return memo[u]
            node = self.nodes[u]
            assert node is not None
            v, lo, hi = node
            w_lo, w_hi = self.weights[v]
            val = w_lo * rec(lo) + w_hi * rec(hi)
            memo[u] = val
            return val

        return rec(root)

    def reachable_stats(self, roots: list[int]) -> tuple[int, dict[int, int]]:
        """Return (total reachable non-terminal nodes, width per variable level)."""
        visited: set[int] = set()
        stack = list(roots)
        by_level: dict[int, int] = {}
        while stack:
            u = stack.pop()
            if u <= 1 or u in visited:
                continue
            visited.add(u)
            node = self.nodes[u]
            assert node is not None
            v, lo, hi = node
            by_level[v] = by_level.get(v, 0) + 1
            stack.append(lo)
            stack.append(hi)
        return len(visited), by_level


# Mini Dice-style AST matching core grammar (Flip, Observe, Ite, Let, Boolean ops)
@dataclass(frozen=True)
class Const:
    val: bool


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Flip:
    p: Fraction
    label: str = ""


@dataclass(frozen=True)
class Not:
    e: Expr


@dataclass(frozen=True)
class BinOp:
    op: str  # "and", "or", "xor", "iff"
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Observe:
    cond: Expr


@dataclass(frozen=True)
class Let:
    name: str
    bound: Expr
    body: Expr


@dataclass(frozen=True)
class Ite:
    cond: Expr
    then_e: Expr
    else_e: Expr


Expr = Const | Var | Flip | Not | BinOp | Observe | Let | Ite


@dataclass(frozen=True)
class CompiledExpr:
    state: int  # unnormalized value formula (phi)
    z: int  # accepting formula (gamma): all executed observes hold


def compile_dice(mgr: ROBDDManager, expr: Expr, env: dict[str, int] | None = None) -> CompiledExpr:
    """Compositional Dice compilation rule: e ~> (phi, gamma)."""
    if env is None:
        env = {}
    match expr:
        case Const(v):
            return CompiledExpr(mgr.TRUE if v else mgr.FALSE, mgr.TRUE)
        case Var(name):
            return CompiledExpr(env[name], mgr.TRUE)
        case Flip(p, label):
            _, nid = mgr.new_var(p, label or None)
            return CompiledExpr(nid, mgr.TRUE)
        case Not(e):
            c = compile_dice(mgr, e, env)
            return CompiledExpr(mgr.not_(c.state), c.z)
        case BinOp(op, lhs, rhs):
            c1 = compile_dice(mgr, lhs, env)
            c2 = compile_dice(mgr, rhs, env)
            op_fn = {"and": mgr.and_, "or": mgr.or_, "xor": mgr.xor_, "iff": mgr.iff_}[op]
            return CompiledExpr(op_fn(c1.state, c2.state), mgr.and_(c1.z, c2.z))
        case Observe(cond):
            c = compile_dice(mgr, cond, env)
            return CompiledExpr(mgr.TRUE, mgr.and_(c.state, c.z))
        case Let(name, bound, body):
            c1 = compile_dice(mgr, bound, env)
            env2 = dict(env)
            env2[name] = c1.state
            c2 = compile_dice(mgr, body, env2)
            return CompiledExpr(c2.state, mgr.and_(c1.z, c2.z))
        case Ite(cond, then_e, else_e):
            cg = compile_dice(mgr, cond, env)
            ct = compile_dice(mgr, then_e, env)
            ce = compile_dice(mgr, else_e, env)
            state = mgr.ite(cg.state, ct.state, ce.state)
            # Crucial Dice rule (Compiler.ml:107): guard branch observations by cg.state
            z = mgr.and_(cg.z, mgr.ite(cg.state, ct.z, ce.z))
            return CompiledExpr(state, z)
    raise AssertionError(f"Unhandled expr: {expr}")


def exact_posterior_bdd(expr: Expr) -> tuple[Fraction, Fraction, int, dict[int, int]]:
    """Compile expr to ROBDD and return (P(ret=True | obs), P(obs), nodes, level_widths)."""
    mgr = ROBDDManager()
    comp = compile_dice(mgr, expr)
    z_mass = mgr.wmc(comp.z)
    joint_true = mgr.wmc(mgr.and_(comp.state, comp.z))
    post = joint_true / z_mass if z_mass != 0 else Fraction(0)
    nodes, widths = mgr.reachable_stats([comp.state, comp.z])
    return post, z_mass, nodes, widths


def exact_posterior_enumerate(expr: Expr) -> tuple[Fraction, Fraction]:
    """Reference operational semantics by exhaustive 2^n path enumeration."""
    def eval_paths(e: Expr, env: dict[str, bool]) -> list[tuple[bool, bool, Fraction]]:
        # Returns list of (value, accepted, weight)
        match e:
            case Const(v):
                return [(v, True, Fraction(1))]
            case Var(name):
                return [(env[name], True, Fraction(1))]
            case Flip(p, _):
                return [(True, True, p), (False, True, Fraction(1) - p)]
            case Not(sub):
                return [(not v, acc, w) for v, acc, w in eval_paths(sub, env)]
            case BinOp(op, lhs, rhs):
                out: list[tuple[bool, bool, Fraction]] = []
                for v1, a1, w1 in eval_paths(lhs, env):
                    for v2, a2, w2 in eval_paths(rhs, env):
                        if op == "and":
                            res = v1 and v2
                        elif op == "or":
                            res = v1 or v2
                        elif op == "xor":
                            res = v1 != v2
                        elif op == "iff":
                            res = v1 == v2
                        else:
                            raise ValueError(op)
                        out.append((res, a1 and a2, w1 * w2))
                return out
            case Observe(cond):
                return [(True, acc and v, w) for v, acc, w in eval_paths(cond, env)]
            case Let(name, bound, body):
                out = []
                for v1, a1, w1 in eval_paths(bound, env):
                    env2 = dict(env)
                    env2[name] = v1
                    for v2, a2, w2 in eval_paths(body, env2):
                        out.append((v2, a1 and a2, w1 * w2))
                return out
            case Ite(cond, then_e, else_e):
                out = []
                for vg, ag, wg in eval_paths(cond, env):
                    branch = then_e if vg else else_e
                    for vb, ab, wb in eval_paths(branch, env):
                        out.append((vb, ag and ab, wg * wb))
                return out
        raise AssertionError(e)

    paths = eval_paths(expr, {})
    z_mass = sum((w for _, acc, w in paths if acc), Fraction(0))
    true_mass = sum((w for v, acc, w in paths if acc and v), Fraction(0))
    return (true_mass / z_mass if z_mass != 0 else Fraction(0)), z_mass


def build_markov_chain(steps: int) -> Expr:
    """Factored k-step Markov chain with intermediate observations (O(k) BDD, 2^(2k) paths)."""
    # s_0 ~ Flip(1/2); for i in 1..steps: s_i = if s_{i-1} then Flip(4/5) else Flip(1/5);
    # observe (if s_i then Flip(3/4) else Flip(1/4)) at even steps.
    def step_body(i: int) -> Expr:
        if i > steps:
            return Var(f"s{steps}")
        prev = Var(f"s{i - 1}")
        nxt = Ite(prev, Flip(Fraction(4, 5), f"t{i}"), Flip(Fraction(1, 5), f"f{i}"))
        rest = step_body(i + 1)
        if i % 2 == 0:
            obs_expr = Ite(Var(f"s{i}"), Flip(Fraction(3, 4), f"ot{i}"), Flip(Fraction(1, 4), f"of{i}"))
            rest = Let(f"_o{i}", Observe(obs_expr), rest)
        return Let(f"s{i}", nxt, rest)

    return Let("s0", Flip(Fraction(1, 2), "s0"), step_body(1))


def build_parity_coupling(k: int, paired_order: bool) -> Expr:
    """Observe conjunction_{i=0..k-1} (x_i XOR y_i == True) under paired vs separated variable orders."""
    # Separated order allocates x_0..x_{k-1} first, then y_0..y_{k-1}, forcing 2^k cut width.
    # Paired order allocates (x_0, y_0), (x_1, y_1), ..., giving O(k) BDD width.
    def make_checks(i: int) -> Expr:
        if i == k:
            return Var("x0")
        chk = Observe(BinOp("xor", Var(f"x{i}"), Var(f"y{i}")))
        return Let(f"_c{i}", chk, make_checks(i + 1))

    body: Expr = make_checks(0)
    if paired_order:
        for i in reversed(range(k)):
            body = Let(f"x{i}", Flip(Fraction(3, 5), f"x{i}"),
                       Let(f"y{i}", Flip(Fraction(2, 5), f"y{i}"), body))
    else:
        for i in reversed(range(k)):
            body = Let(f"y{i}", Flip(Fraction(2, 5), f"y{i}"), body)
        for i in reversed(range(k)):
            body = Let(f"x{i}", Flip(Fraction(3, 5), f"x{i}"), body)
    return body


def build_dense_parity_system(k: int) -> Expr:
    """High-coupling 2k-variable system with k full-rank cross-cut parity observations.

    Variables x_0..x_{k-1} and y_0..y_{k-1} are coupled by a full-rank lower-triangular
    plus wraparound parity system: for each r in 0..k-1,
      (XOR_{j=0..r} x_j) XOR y_r == (r % 2 == 0).
    This couples the prefix (x_0..x_{k-1}) to the suffix (y_0..y_{k-1}) with cut rank k,
    forcing BDD width >= 2^k at level k.
    """
    def xor_prefix(r: int) -> Expr:
        acc: Expr = Var("x0")
        for j in range(1, r + 1):
            acc = BinOp("xor", acc, Var(f"x{j}"))
        return acc

    body: Expr = Var("x0")
    for r in reversed(range(k)):
        rhs = Const(r % 2 == 0)
        eq_expr = BinOp("iff", BinOp("xor", xor_prefix(r), Var(f"y{r}")), rhs)
        body = Let(f"_p{r}", Observe(eq_expr), body)
    for i in reversed(range(k)):
        body = Let(f"y{i}", Flip(Fraction(1, 3), f"y{i}"), body)
    for i in reversed(range(k)):
        body = Let(f"x{i}", Flip(Fraction(2, 3), f"x{i}"), body)
    return body


def run_probe_dice_wmc() -> dict[str, Any]:
    # 1. Dice paper ObsProg (OOPSLA 2020 Sec 3.2)
    obs_prog = Let(
        "x", Flip(Fraction(3, 5), "x"),
        Let("y", Flip(Fraction(3, 10), "y"),
            Let("_", Observe(BinOp("or", Var("x"), Var("y"))), Var("x"))),
    )
    bdd_p, bdd_z, obs_nodes, _ = exact_posterior_bdd(obs_prog)
    enum_p, enum_z = exact_posterior_enumerate(obs_prog)
    assert bdd_p == enum_p == Fraction(5, 6), f"ObsProg mismatch: {bdd_p} vs {enum_p}"
    assert bdd_z == enum_z == Fraction(18, 25), f"ObsProg Z mismatch: {bdd_z}"

    # 2. Branch-guarded conditional observe (verifies Compiler.ml:107 Ite guarding)
    branch_obs = Let(
        "c", Flip(Fraction(1, 2), "c"),
        Ite(
            Var("c"),
            Let("_", Observe(Flip(Fraction(1, 4), "a")), Const(True)),
            Let("_", Observe(Flip(Fraction(3, 4), "b")), Const(False)),
        ),
    )
    br_p, br_z, _, _ = exact_posterior_bdd(branch_obs)
    br_ep, br_ez = exact_posterior_enumerate(branch_obs)
    assert br_p == br_ep == Fraction(1, 4), f"Branch observe mismatch: {br_p} vs {br_ep}"
    assert br_z == br_ez == Fraction(1, 2), f"Branch Z mismatch: {br_z}"

    # 3. Classic Burglary-Earthquake-Alarm Bayesian Network
    bn = Let(
        "b", Flip(Fraction(1, 1000), "burglary"),
        Let(
            "e", Flip(Fraction(2, 1000), "earthquake"),
            Let(
                "alarm",
                Ite(
                    Var("b"),
                    Ite(Var("e"), Flip(Fraction(95, 100)), Flip(Fraction(94, 100))),
                    Ite(Var("e"), Flip(Fraction(29, 100)), Flip(Fraction(1, 1000))),
                ),
                Let(
                    "john", Ite(Var("alarm"), Flip(Fraction(90, 100)), Flip(Fraction(5, 100))),
                    Let(
                        "mary", Ite(Var("alarm"), Flip(Fraction(70, 100)), Flip(Fraction(1, 100))),
                        Let("_1", Observe(Var("john")), Let("_2", Observe(Var("mary")), Var("b"))),
                    ),
                ),
            ),
        ),
    )
    bn_p, bn_z, bn_nodes, _ = exact_posterior_bdd(bn)
    bn_ep, bn_ez = exact_posterior_enumerate(bn)
    assert bn_p == bn_ep and bn_z == bn_ez, f"BN mismatch: {bn_p} vs {bn_ep}"

    # 4. Factored Markov chain linear scaling (exact agreement vs enumeration for k=4)
    markov_rows: list[dict[str, Any]] = []
    for steps in (2, 4, 6, 8, 12, 16):
        prog = build_markov_chain(steps)
        p_bdd, z_bdd, nodes, widths = exact_posterior_bdd(prog)
        verified_enum = False
        if steps <= 4:
            p_enum, z_enum = exact_posterior_enumerate(prog)
            assert p_bdd == p_enum and z_bdd == z_enum
            verified_enum = True
        markov_rows.append({
            "steps": steps,
            "bdd_nodes": nodes,
            "max_level_width": max(widths.values(), default=0),
            "posterior_float": float(p_bdd),
            "enum_checked": verified_enum,
        })
    # Verify linear growth: nodes at k=16 should be <= 8 * nodes at k=2
    assert markov_rows[-1]["max_level_width"] <= 4, f"Expected constant width on Markov chain: {markov_rows[-1]}"

    # 5. Exponential BDD blowup on unfactored/separated parity coupling vs paired order
    parity_rows: list[dict[str, Any]] = []
    for k in (2, 4, 6, 8, 10):
        sep_prog = build_parity_coupling(k, paired_order=False)
        pair_prog = build_parity_coupling(k, paired_order=True)
        p_sep, z_sep, n_sep, w_sep = exact_posterior_bdd(sep_prog)
        p_pair, z_pair, n_pair, w_pair = exact_posterior_bdd(pair_prog)
        assert p_sep == p_pair and z_sep == z_pair
        if k <= 4:
            p_enum, z_enum = exact_posterior_enumerate(sep_prog)
            assert p_sep == p_enum and z_sep == z_enum
        cut_width_sep = w_sep.get(k, 0)
        assert cut_width_sep == (1 << k), f"Expected exact 2^{k}={1 << k} cut width, got {cut_width_sep}"
        parity_rows.append({
            "k": k,
            "paired_nodes": n_pair,
            "paired_max_width": max(w_pair.values(), default=0),
            "separated_nodes": n_sep,
            "separated_cut_width_at_k": cut_width_sep,
            "expected_2_pow_k": 1 << k,
        })

    # 6. Dense cross-cut parity system (exact WMC + exponential cut width)
    dense_rows: list[dict[str, Any]] = []
    for k in (2, 4, 6, 8):
        dprog = build_dense_parity_system(k)
        p_d, z_d, n_d, w_d = exact_posterior_bdd(dprog)
        if k <= 4:
            p_de, z_de = exact_posterior_enumerate(dprog)
            assert p_d == p_de and z_d == z_de
        dense_rows.append({
            "k": k,
            "bdd_nodes": n_d,
            "cut_width_at_k": w_d.get(k, 0),
            "posterior_x0": str(p_d),
        })
        assert w_d.get(k, 0) == (1 << k)

    return {
        "obs_prog": {"posterior": str(bdd_p), "accepting_prob": str(bdd_z), "bdd_nodes": obs_nodes},
        "branch_guarded_observe": {"posterior": str(br_p), "accepting_prob": str(br_z)},
        "burglary_alarm_bn": {"posterior_burglary": float(bn_p), "exact_fraction": str(bn_p), "bdd_nodes": bn_nodes},
        "factored_markov_scaling": markov_rows,
        "parity_coupling_blowup": parity_rows,
        "dense_parity_blowup": dense_rows,
    }


# =============================================================================
# Part 2: Borel-Kolmogorov Coordinate-Change Measure-Zero Conditioning Paradox
# =============================================================================


def exact_epsilon_band_moments(eps: float) -> tuple[float, float]:
    """Exact analytical (E[X], P(X <= 0.5)) for X, Y ~ Uniform(0, 1) given |X - Y| <= eps.

    For 0 < eps < 0.5, the slice length L(x) = min(1, x + eps) - max(0, x - eps):
      - x in [0, eps]:      L(x) = x + eps
      - x in [eps, 1-eps]:  L(x) = 2*eps
      - x in [1-eps, 1]:    L(x) = 1 - x + eps
    """
    assert 0.0 < eps < 0.5
    # Total area: int_0^eps (x+eps) dx + int_eps^{1-eps} 2*eps dx + int_{1-eps}^1 (1-x+eps) dx
    area_left = 1.5 * eps * eps
    area_mid = 2.0 * eps * (1.0 - 2.0 * eps)
    area_right = 1.5 * eps * eps
    total_area = area_left + area_mid + area_right  # = 2*eps - eps^2

    # First moment int_0^1 x * L(x) dx (by symmetry around x=0.5, E[X] == 0.5 identically!)
    ex_left = (eps ** 3) / 3.0 + (eps ** 3) / 2.0
    ex_mid = eps * ((1.0 - eps) ** 2 - eps ** 2)
    # int_{1-eps}^1 x*(1 + eps - x) dx = [(1+eps)x^2/2 - x^3/3]_{1-eps}^1
    def F_right(x: float) -> float:
        return 0.5 * (1.0 + eps) * x * x - (x ** 3) / 3.0
    ex_right = F_right(1.0) - F_right(1.0 - eps)
    mean_x = (ex_left + ex_mid + ex_right) / total_area

    # P(X <= 0.5) = (area_left + int_eps^{0.5} 2*eps dx) / total_area = 0.5 identically
    p_le_half = (area_left + 2.0 * eps * (0.5 - eps)) / total_area
    return mean_x, p_le_half


def exact_epsilon_ratio_moments(eps: float) -> tuple[float, float]:
    """Exact analytical (E[X], P(X <= 0.5)) for X, Y ~ Uniform(0, 1) given |X / Y - 1| <= eps.

    For 0 < eps < 0.5, |x/y - 1| <= eps <=> x/(1+eps) <= y <= min(1, x/(1-eps)):
      - x in [0, 1-eps]:  L(x) = x * (1/(1-eps) - 1/(1+eps)) = 2*eps*x / (1 - eps^2)
      - x in [1-eps, 1]:  L(x) = 1 - x/(1+eps)
    """
    assert 0.0 < eps < 0.5
    c = 2.0 * eps / (1.0 - eps * eps)
    x_split = 1.0 - eps

    # Area on [0, 1-eps]: c * x_split^2 / 2
    area_1 = 0.5 * c * x_split * x_split
    # Area on [1-eps, 1]: [x - x^2 / (2*(1+eps))]_{1-eps}^1
    def A2(x: float) -> float:
        return x - (x * x) / (2.0 * (1.0 + eps))
    area_2 = A2(1.0) - A2(x_split)
    total_area = area_1 + area_2

    # First moment int_0^1 x * L(x) dx
    ex_1 = c * (x_split ** 3) / 3.0
    def M2(x: float) -> float:
        return 0.5 * x * x - (x ** 3) / (3.0 * (1.0 + eps))
    ex_2 = M2(1.0) - M2(x_split)
    mean_x = (ex_1 + ex_2) / total_area

    # P(X <= 0.5): since eps < 0.5, 0.5 < 1 - eps, so all in first region
    area_le_half = 0.5 * c * (0.5 * 0.5)
    p_le_half = area_le_half / total_area
    return mean_x, p_le_half


def run_probe_borel_kolmogorov() -> dict[str, Any]:
    eps_values = [0.1, 0.05, 0.01, 0.002, 0.0005]
    band_series = []
    ratio_series = []
    for eps in eps_values:
        bm, bp = exact_epsilon_band_moments(eps)
        rm, rp = exact_epsilon_ratio_moments(eps)
        band_series.append({"eps": eps, "mean_x": round(bm, 6), "p_x_le_half": round(bp, 6)})
        ratio_series.append({"eps": eps, "mean_x": round(rm, 6), "p_x_le_half": round(rp, 6)})

    # Deterministic 2D midpoint quadrature at eps=0.01 (550x550 grid; eps*550 = 5.5 avoids boundary aliasing)
    n_grid = 550
    eps_q = 0.01
    band_cnt = band_sum_x = band_le_half = 0.0
    ratio_cnt = ratio_sum_x = ratio_le_half = 0.0
    for i in range(n_grid):
        x = (i + 0.5) / n_grid
        for j in range(n_grid):
            y = (j + 0.5) / n_grid
            if abs(x - y) <= eps_q:
                band_cnt += 1.0
                band_sum_x += x
                if x <= 0.5:
                    band_le_half += 1.0
            if abs(x / y - 1.0) <= eps_q:
                ratio_cnt += 1.0
                ratio_sum_x += x
                if x <= 0.5:
                    ratio_le_half += 1.0
    quad_band_mean = band_sum_x / band_cnt
    quad_band_p = band_le_half / band_cnt
    quad_ratio_mean = ratio_sum_x / ratio_cnt
    quad_ratio_p = ratio_le_half / ratio_cnt

    # Compare 2D quadrature against exact analytical values at eps = 0.01 and limiting values
    exact_bm_01, exact_bp_01 = exact_epsilon_band_moments(eps_q)
    exact_rm_01, exact_rp_01 = exact_epsilon_ratio_moments(eps_q)
    assert abs(band_series[-1]["mean_x"] - 0.5) < 1e-6
    assert abs(band_series[-1]["p_x_le_half"] - 0.5) < 1e-6
    assert abs(ratio_series[-1]["mean_x"] - (2.0 / 3.0)) < 1e-3
    assert abs(ratio_series[-1]["p_x_le_half"] - 0.25) < 1e-3
    assert abs(quad_band_mean - exact_bm_01) < 1e-3
    assert abs(quad_band_p - exact_bp_01) < 1e-3
    assert abs(quad_ratio_mean - exact_rm_01) < 5e-3
    assert abs(quad_ratio_p - exact_rp_01) < 5e-3
    assert abs(quad_ratio_mean - quad_band_mean) > 0.15

    # Verify classical spherical great-circle paradox via 1D Simpson/midpoint quadrature:
    # Meridian wedge (|phi| <= eps): density on latitude theta in [-pi/2, pi/2] is (1/2) cos(theta)
    #   => E[|sin(theta)|] = int_0^{pi/2} sin(theta) cos(theta) dtheta = 1/2 = 0.5
    # Equator band (|theta| <= eps): uniform density (1/pi) on angle psi in [-pi/2, pi/2]
    #   => E[|sin(psi)|] = (2/pi) * int_0^{pi/2} sin(psi) dpsi = 2/pi ~= 0.636620
    n_sph = 10000
    d_ang = (math.pi / 2.0) / n_sph
    e_meridian = sum(math.sin((i + 0.5) * d_ang) * math.cos((i + 0.5) * d_ang) * d_ang for i in range(n_sph))
    e_equator = (2.0 / math.pi) * sum(math.sin((i + 0.5) * d_ang) * d_ang for i in range(n_sph))
    assert abs(e_meridian - 0.5) < 1e-7
    assert abs(e_equator - (2.0 / math.pi)) < 1e-7

    return {
        "cartesian_difference_limit": {"density": "1 on (0,1) [Uniform(0,1)]", "mean": 0.5, "p_le_half": 0.5, "jacobian_at_diag": "1"},
        "ratio_wedge_limit": {"density": "2x on (0,1) [Beta(2,1)]", "mean": round(2.0 / 3.0, 6), "p_le_half": 0.25, "jacobian_at_diag": "x"},
        "analytical_band_series": band_series,
        "analytical_ratio_series": ratio_series,
        "quadrature_eps_0.01": {
            "band_mean_x": round(quad_band_mean, 6),
            "band_p_le_half": round(quad_band_p, 6),
            "ratio_mean_x": round(quad_ratio_mean, 6),
            "ratio_p_le_half": round(quad_ratio_p, 6),
            "mean_discrepancy": round(abs(quad_ratio_mean - quad_band_mean), 6),
        },
        "spherical_great_circle": {
            "meridian_E_abs_sin": round(e_meridian, 6),
            "equator_E_abs_sin": round(e_equator, 6),
            "discrepancy": round(abs(e_equator - e_meridian), 6),
        },
    }


# =============================================================================
# Part 3: Variational Guide-Support Checker & Silent Monte Carlo ELBO Masking
# =============================================================================


@dataclass(frozen=True)
class SupportSpec:
    """Typed support and reference-measure descriptor (inspired by pyppai adom_distty)."""

    measure_kind: str  # "lebesgue_1d", "simplex", "counting", "dirac"
    lo: float = -math.inf
    hi: float = math.inf
    lo_closed: bool = False
    hi_closed: bool = False
    dim: int = 1
    label: str = ""

    @staticmethod
    def normal() -> SupportSpec:
        return SupportSpec("lebesgue_1d", -math.inf, math.inf, False, False, 1, "Normal(R)")

    @staticmethod
    def uniform(lo: float, hi: float) -> SupportSpec:
        return SupportSpec("lebesgue_1d", lo, hi, True, True, 1, f"Uniform([{lo}, {hi}])")

    @staticmethod
    def gamma() -> SupportSpec:
        return SupportSpec("lebesgue_1d", 0.0, math.inf, False, False, 1, "Gamma((0, inf))")

    @staticmethod
    def beta() -> SupportSpec:
        return SupportSpec("lebesgue_1d", 0.0, 1.0, False, False, 1, "Beta((0, 1))")

    @staticmethod
    def dirichlet(k: int) -> SupportSpec:
        return SupportSpec("simplex", 0.0, 1.0, False, False, k, f"Dirichlet(Delta^{k - 1})")

    @staticmethod
    def delta(dim: int = 1) -> SupportSpec:
        return SupportSpec("dirac", 0.0, 0.0, True, True, dim, f"Delta(dim={dim})")

    @staticmethod
    def categorical(k: int) -> SupportSpec:
        return SupportSpec("counting", 0.0, float(k - 1), True, True, 1, f"Categorical(0..{k - 1})")


def check_support_containment(q_supp: SupportSpec, p_supp: SupportSpec) -> tuple[bool, str]:
    """Check absolute continuity q << p and support containment supp(q) <= supp(p) for finite KL(q || p)."""
    if q_supp.measure_kind != p_supp.measure_kind:
        return (
            False,
            f"MEASURE_SINGULARITY: guide {q_supp.label} ({q_supp.measure_kind}) "
            f"is singular w.r.t. model {p_supp.label} ({p_supp.measure_kind})",
        )
    if q_supp.dim != p_supp.dim:
        return (
            False,
            f"DIM_MISMATCH: guide dim={q_supp.dim} != model dim={p_supp.dim}",
        )
    if q_supp.measure_kind == "simplex":
        return True, "OK (matching open simplex support)"
    # Interval / discrete range containment: [q.lo, q.hi] subseteq [p.lo, p.hi]
    # Note: for Lebesgue measures, boundary singletons have measure 0; strict excess mass
    # occurs whenever q.lo < p.lo or q.hi > p.hi.
    if q_supp.lo < p_supp.lo or q_supp.hi > p_supp.hi:
        return (
            False,
            f"SUPPORT_VIOLATION: supp(q)={q_supp.label} not subseteq supp(p)={p_supp.label} => KL(q || p) = +inf",
        )
    strict_subset = q_supp.lo > p_supp.lo or q_supp.hi < p_supp.hi
    if strict_subset:
        return (
            True,
            f"OK_STRICT_SUBSET: supp(q)={q_supp.label} strictly inside supp(p)={p_supp.label} "
            f"(KL(q||p) finite, but reverse dominance p << q fails)",
        )
    return True, f"OK_EXACT_MATCH: supp(q)={q_supp.label} == supp(p)={p_supp.label}"


def verify_model_guide_pair(
    name: str,
    model_sites: dict[str, SupportSpec],
    guide_sites: dict[str, SupportSpec],
    auxiliary_sites: set[str] | None = None,
) -> dict[str, Any]:
    aux = auxiliary_sites or set()
    errors: list[str] = []
    warnings: list[str] = []

    m_keys = set(model_sites.keys())
    g_keys = set(guide_sites.keys()) - aux
    if m_keys != g_keys:
        missing_in_guide = sorted(m_keys - g_keys)
        extra_in_guide = sorted(g_keys - m_keys)
        errors.append(
            f"SITE_SET_MISMATCH: missing_in_guide={missing_in_guide}, extra_in_guide={extra_in_guide}"
        )

    for site in sorted(m_keys & g_keys):
        ok, msg = check_support_containment(guide_sites[site], model_sites[site])
        if not ok:
            errors.append(f"site '{site}': {msg}")
        elif msg.startswith("OK_STRICT_SUBSET"):
            warnings.append(f"site '{site}': {msg}")

    return {"pair": name, "valid": len(errors) == 0, "errors": errors, "warnings": warnings}


def normal_cdf(x: float) -> float:
    """Use erfc(-x / sqrt(2)) / 2 to avoid catastrophic cancellation in deep tails."""
    return 0.5 * math.erfc(-x / math.sqrt(2.0))


def normal_logpdf(x: float, loc: float, scale: float) -> float:
    z = (x - loc) / scale
    return -0.5 * math.log(2.0 * math.pi) - math.log(scale) - 0.5 * z * z


def uniform_logpdf(x: float, lo: float, hi: float) -> float:
    if lo <= x <= hi:
        return -math.log(hi - lo)
    return -math.inf


def mc_elbo_experiment(loc: float, scale: float, lo: float, hi: float, n_samples: int, seed: int) -> dict[str, Any]:
    """Estimate E_q[log p(x) - log q(x)] for p=Uniform(lo, hi), q=Normal(loc, scale)."""
    rng = random.Random(seed)
    out_of_support = 0
    total_elbo = 0.0
    for _ in range(n_samples):
        x = rng.gauss(loc, scale)
        lp = uniform_logpdf(x, lo, hi)
        lq = normal_logpdf(x, loc, scale)
        if math.isinf(lp):
            out_of_support += 1
            total_elbo = -math.inf
        elif not math.isinf(total_elbo):
            total_elbo += lp - lq
    emp_elbo = -math.inf if math.isinf(total_elbo) else total_elbo / n_samples
    # Exact analytical escape probability P(X < lo or X > hi)
    p_low = normal_cdf((lo - loc) / scale)
    p_high = 1.0 - normal_cdf((hi - loc) / scale)
    p_escape = p_low + p_high
    return {
        "guide_loc": loc,
        "guide_scale": scale,
        "n_samples": n_samples,
        "out_of_support_draws": out_of_support,
        "empirical_elbo": emp_elbo if math.isfinite(emp_elbo) else "-inf",
        "exact_escape_prob": p_escape,
        "exact_kl_q_p": "+inf",
    }


def run_probe_svi_support() -> dict[str, Any]:
    # 1. Exact Pyro Bayesian Regression original bug (br_original_modelguide.py)
    br_bug = verify_model_guide_pair(
        "pyro_bayesian_regression_original",
        model_sites={
            "a": SupportSpec.normal(),
            "bA": SupportSpec.normal(),
            "bR": SupportSpec.normal(),
            "bAR": SupportSpec.normal(),
            "sigma": SupportSpec.uniform(0.0, 10.0),
        },
        guide_sites={
            "a": SupportSpec.normal(),
            "bA": SupportSpec.normal(),
            "bR": SupportSpec.normal(),
            "bAR": SupportSpec.normal(),
            "sigma": SupportSpec.normal(),  # Normal(sigma_loc, 0.05) -> R not subseteq [0, 10]
        },
    )
    assert not br_bug["valid"] and any("SUPPORT_VIOLATION" in e for e in br_bug["errors"])

    # 2. Fixed Bayesian Regression (br_model1.py / br_guide1.py)
    br_fixed = verify_model_guide_pair(
        "pyro_bayesian_regression_fixed",
        model_sites={"a": SupportSpec.normal(), "sigma": SupportSpec.uniform(0.1, 10.0)},
        guide_sites={"a": SupportSpec.normal(), "sigma": SupportSpec.uniform(0.1, 10.0)},
    )
    assert br_fixed["valid"]

    # 3. Pyro LDA non-standard Dirac-Delta guide (lda_original_modelguide.py)
    lda_singular = verify_model_guide_pair(
        "pyro_lda_dirac_guide",
        model_sites={"topic_weights": SupportSpec.gamma(), "doc_topics": SupportSpec.dirichlet(8)},
        guide_sites={"topic_weights": SupportSpec.gamma(), "doc_topics": SupportSpec.delta(8)},
    )
    assert not lda_singular["valid"] and any("MEASURE_SINGULARITY" in e for e in lda_singular["errors"])

    # 4. Transdimensional / missing-site mismatch
    site_mismatch = verify_model_guide_pair(
        "missing_latent_site",
        model_sites={"z1": SupportSpec.normal(), "z2": SupportSpec.normal()},
        guide_sites={"z1": SupportSpec.normal()},
    )
    assert not site_mismatch["valid"] and any("SITE_SET_MISMATCH" in e for e in site_mismatch["errors"])

    # 5. Strict subset warning (KL(q||p) finite, but reverse p << q fails for IS/MH)
    strict_sub = verify_model_guide_pair(
        "strict_subset_gamma_in_normal",
        model_sites={"theta": SupportSpec.normal()},
        guide_sites={"theta": SupportSpec.gamma()},
    )
    assert strict_sub["valid"] and len(strict_sub["warnings"]) == 1

    # 6. Silent Monte Carlo ELBO masking on the exact Pyro Bayesian Regression bug
    mc_masked = mc_elbo_experiment(loc=1.0, scale=0.05, lo=0.0, hi=10.0, n_samples=100_000, seed=20261119)
    assert mc_masked["out_of_support_draws"] == 0
    assert isinstance(mc_masked["empirical_elbo"], float) and math.isfinite(mc_masked["empirical_elbo"])

    # 7. Boundary drift: once SGD moves sigma_loc from 1.0 to 0.15 (3*sigma), -inf explodes
    mc_drift = mc_elbo_experiment(loc=0.15, scale=0.05, lo=0.0, hi=10.0, n_samples=100_000, seed=20261119)
    assert mc_drift["out_of_support_draws"] > 50
    assert mc_drift["empirical_elbo"] == "-inf"

    return {
        "static_checks": [br_bug, br_fixed, lda_singular, site_mismatch, strict_sub],
        "mc_elbo_masked_at_init": mc_masked,
        "mc_elbo_crash_after_drift": mc_drift,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit structured JSON summary")
    args = parser.parse_args()

    results = {
        "probe_1_dice_wmc": run_probe_dice_wmc(),
        "probe_2_borel_kolmogorov": run_probe_borel_kolmogorov(),
        "probe_3_svi_support": run_probe_svi_support(),
    }

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        p1 = results["probe_1_dice_wmc"]
        p2 = results["probe_2_borel_kolmogorov"]
        p3 = results["probe_3_svi_support"]
        print("[PASS] Probe 1 (Dice ROBDD + Exact Rational WMC):")
        print(f"  ObsProg: P(x=T|x||y)={p1['obs_prog']['posterior']} (Z={p1['obs_prog']['accepting_prob']})")
        print(f"  Branch-guarded observe: P(ret=T)={p1['branch_guarded_observe']['posterior']} (Z={p1['branch_guarded_observe']['accepting_prob']})")
        print(f"  Burglary-Alarm BN: P(B|J,M)={p1['burglary_alarm_bn']['posterior_burglary']:.6f} ({p1['burglary_alarm_bn']['bdd_nodes']} BDD nodes)")
        print(f"  Markov chain k=16: {p1['factored_markov_scaling'][-1]['bdd_nodes']} BDD nodes (max width {p1['factored_markov_scaling'][-1]['max_level_width']})")
        last_par = p1["parity_coupling_blowup"][-1]
        print(f"  Parity coupling k={last_par['k']}: paired={last_par['paired_nodes']} nodes (width {last_par['paired_max_width']}) vs separated={last_par['separated_nodes']} nodes (cut width {last_par['separated_cut_width_at_k']} == 2^{last_par['k']})")
        last_dense = p1["dense_parity_blowup"][-1]
        print(f"  Dense cross-cut parity k={last_dense['k']}: {last_dense['bdd_nodes']} nodes (cut width {last_dense['cut_width_at_k']} == 2^{last_dense['k']})")

        print("[PASS] Probe 2 (Borel-Kolmogorov Measure-Zero Conditioning):")
        q = p2["quadrature_eps_0.01"]
        print(f"  |X - Y| <= 0.01 (quad):    E[X]={q['band_mean_x']:.6f} (limit 0.500000), P(X<=0.5)={q['band_p_le_half']:.6f} (limit 0.500000)")
        print(f"  |X / Y - 1| <= 0.01 (quad): E[X]={q['ratio_mean_x']:.6f} (limit 0.666667), P(X<=0.5)={q['ratio_p_le_half']:.6f} (limit 0.250000)")
        s = p2["spherical_great_circle"]
        print(f"  Spherical great circle: meridian E[|sin|]={s['meridian_E_abs_sin']:.6f} vs equator E[|sin|]={s['equator_E_abs_sin']:.6f}")

        print("[PASS] Probe 3 (SVI Support Violation & Silent MC ELBO Masking):")
        for chk in p3["static_checks"]:
            status = "VALID" if chk["valid"] else "REJECTED"
            print(f"  {chk['pair']}: {status}")
        m1 = p3["mc_elbo_masked_at_init"]
        m2 = p3["mc_elbo_crash_after_drift"]
        print(f"  MC ELBO at loc={m1['guide_loc']}, scale={m1['guide_scale']}: {m1['out_of_support_draws']}/{m1['n_samples']} escapes, empirical_elbo={m1['empirical_elbo']:.6f} (exact KL=+inf, P_escape={m1['exact_escape_prob']:.2e})")
        print(f"  MC ELBO at loc={m2['guide_loc']}, scale={m2['guide_scale']}: {m2['out_of_support_draws']}/{m2['n_samples']} escapes, empirical_elbo={m2['empirical_elbo']} (P_escape={m2['exact_escape_prob']:.6f})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
