#!/usr/bin/env python3
"""Standalone verification probe for type-error localization and giant-step CE validation.

Demonstrates two core diagnostic mechanisms analyzed in the accompanying reference report:

1. Hindley-Milner Type-Error Localization:
   - Compares standard left-to-right Algorithm W (Robinson unification), top-down
     bidirectional checking (Algorithm M style expected-type propagation, Lee & Yi 1998),
     exact Minimal Unsatisfiable Subset (MUS) enumeration (type-error slicing, Haack & Wells),
     Minimum-Weight Correction Subset (MCS / MaxSMT MinErrLoc, Pavlinovic et al. 2014),
     and SHErrLoc-style Bayesian satisfiable-vs-unsatisfiable constraint-graph blame
     ranking (Zhang & Myers 2014) across classic multi-site polymorphic and higher-order
     benchmarks.

2. Giant-Step Assertion Checking (Why3-style Counterexample Classification):
   - Compares Concrete (Normal) Run-Time Assertion Checking (RAC) against Giant-Step RAC
     (Becker, Belo Lourenco & Marche, F-IDE 2021; Why3 `src/mlw/check_ce.ml`) to classify
     candidate SMT models into:
       NC         (genuine program bug / non-conformity),
       SW         (too-weak loop invariant or callee contract),
       NC_SW      (concrete RAC incomplete; giant-step fails),
       BAD_CE     (spurious SMT model from uninterpreted helper axioms / missing triggers / timeout),
       INCOMPLETE (validation inconclusive).

Requires Python 3.10+ and uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
import math
from typing import Any, Callable


# =============================================================================
# Part 1: Mini-ML AST, Types, Unification, Algorithm W, Algorithm M, MUS/MCS/SHErrLoc
# =============================================================================


class Type:
    pass


@dataclass(frozen=True)
class TCon(Type):
    name: str  # "Int", "Bool", "Str"

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class TVar(Type):
    id: int

    def __str__(self) -> str:
        return f"t{self.id}"


@dataclass(frozen=True)
class TFun(Type):
    arg: Type
    ret: Type

    def __str__(self) -> str:
        lhs = f"({self.arg})" if isinstance(self.arg, TFun) else str(self.arg)
        return f"{lhs} -> {self.ret}"


@dataclass(frozen=True)
class TTuple(Type):
    elems: tuple[Type, ...]

    def __str__(self) -> str:
        return "(" + ", ".join(str(e) for e in self.elems) + ")"


@dataclass(frozen=True)
class Scheme:
    quantified: frozenset[int]
    ty: Type


T_INT = TCon("Int")
T_BOOL = TCon("Bool")
T_STR = TCon("Str")


class Expr:
    span: str


@dataclass(frozen=True)
class EInt(Expr):
    value: int
    span: str


@dataclass(frozen=True)
class EBool(Expr):
    value: bool
    span: str


@dataclass(frozen=True)
class EStr(Expr):
    value: str
    span: str


@dataclass(frozen=True)
class EVar(Expr):
    name: str
    span: str


@dataclass(frozen=True)
class EApp(Expr):
    func: Expr
    arg: Expr
    span: str


@dataclass(frozen=True)
class ELam(Expr):
    param: str
    body: Expr
    span: str


@dataclass(frozen=True)
class ELet(Expr):
    name: str
    rhs: Expr
    body: Expr
    span: str


@dataclass(frozen=True)
class EAnn(Expr):
    expr: Expr
    ty: Type
    span: str


@dataclass(frozen=True)
class ETuple(Expr):
    elems: tuple[Expr, ...]
    span: str


@dataclass(frozen=True)
class EIf(Expr):
    cond: Expr
    then_br: Expr
    else_br: Expr
    span: str


def apply_subst(subst: dict[int, Type], t: Type) -> Type:
    if isinstance(t, TCon):
        return t
    if isinstance(t, TVar):
        if t.id in subst:
            return apply_subst(subst, subst[t.id])
        return t
    if isinstance(t, TFun):
        return TFun(apply_subst(subst, t.arg), apply_subst(subst, t.ret))
    if isinstance(t, TTuple):
        return TTuple(tuple(apply_subst(subst, e) for e in t.elems))
    raise TypeError(f"Unknown type: {t}")


def ftv_type(t: Type) -> set[int]:
    if isinstance(t, TCon):
        return set()
    if isinstance(t, TVar):
        return {t.id}
    if isinstance(t, TFun):
        return ftv_type(t.arg) | ftv_type(t.ret)
    if isinstance(t, TTuple):
        out: set[int] = set()
        for e in t.elems:
            out |= ftv_type(e)
        return out
    raise TypeError(t)


def ftv_scheme(sc: Scheme) -> set[int]:
    return ftv_type(sc.ty) - set(sc.quantified)


def ftv_env(env: dict[str, Scheme]) -> set[int]:
    out: set[int] = set()
    for sc in env.values():
        out |= ftv_scheme(sc)
    return out


def compose_subst(s1: dict[int, Type], s2: dict[int, Type]) -> dict[int, Type]:
    out = {k: apply_subst(s1, v) for k, v in s2.items()}
    for k, v in s1.items():
        if k not in out:
            out[k] = v
    return out


class UnifyError(Exception):
    def __init__(self, t1: Type, t2: Type, span: str, detail: str = "") -> None:
        self.t1 = t1
        self.t2 = t2
        self.span = span
        self.detail = detail
        super().__init__(f"At {span}: cannot unify {t1} with {t2} {detail}".strip())


def unify(t1: Type, t2: Type, span: str) -> dict[int, Type]:
    if t1 == t2:
        return {}
    if isinstance(t1, TVar):
        if t1.id in ftv_type(t2):
            raise UnifyError(t1, t2, span, "(occurs check)")
        return {t1.id: t2}
    if isinstance(t2, TVar):
        if t2.id in ftv_type(t1):
            raise UnifyError(t1, t2, span, "(occurs check)")
        return {t2.id: t1}
    if isinstance(t1, TFun) and isinstance(t2, TFun):
        s1 = unify(t1.arg, t2.arg, span)
        s2 = unify(apply_subst(s1, t1.ret), apply_subst(s1, t2.ret), span)
        return compose_subst(s2, s1)
    if isinstance(t1, TTuple) and isinstance(t2, TTuple) and len(t1.elems) == len(t2.elems):
        s: dict[int, Type] = {}
        for a, b in zip(t1.elems, t2.elems):
            si = unify(apply_subst(s, a), apply_subst(s, b), span)
            s = compose_subst(si, s)
        return s
    raise UnifyError(t1, t2, span)


class FreshGen:
    def __init__(self) -> None:
        self._n = 0

    def fresh(self) -> TVar:
        v = TVar(self._n)
        self._n += 1
        return v


def instantiate(sc: Scheme, gen: FreshGen) -> Type:
    mapping = {vid: gen.fresh() for vid in sc.quantified}
    return apply_subst(mapping, sc.ty)


def generalize(env: dict[str, Scheme], t: Type) -> Scheme:
    q = frozenset(ftv_type(t) - ftv_env(env))
    return Scheme(q, t)


# Standard library primitives (including polymorphic combinators `id` and `same`)
BASE_ENV: dict[str, Scheme] = {
    "add1": Scheme(frozenset(), TFun(T_INT, T_INT)),
    "not": Scheme(frozenset(), TFun(T_BOOL, T_BOOL)),
    "str_len": Scheme(frozenset(), TFun(T_STR, T_INT)),
    "id": Scheme(frozenset({998}), TFun(TVar(998), TVar(998))),
    # Polymorphic equality-enforcing combinator: ∀a. a -> a -> a
    "same": Scheme(frozenset({999}), TFun(TVar(999), TFun(TVar(999), TVar(999)))),
}


# --- 1A. Standard Left-to-Right Algorithm W ---


def infer_w(expr: Expr, env: dict[str, Scheme], gen: FreshGen) -> tuple[dict[int, Type], Type]:
    if isinstance(expr, EInt):
        return {}, T_INT
    if isinstance(expr, EBool):
        return {}, T_BOOL
    if isinstance(expr, EStr):
        return {}, T_STR
    if isinstance(expr, EVar):
        if expr.name not in env:
            raise KeyError(f"Unbound var {expr.name} at {expr.span}")
        return {}, instantiate(env[expr.name], gen)
    if isinstance(expr, ELam):
        tv = gen.fresh()
        env2 = dict(env)
        env2[expr.param] = Scheme(frozenset(), tv)
        s1, t1 = infer_w(expr.body, env2, gen)
        return s1, TFun(apply_subst(s1, tv), t1)
    if isinstance(expr, EApp):
        s1, t1 = infer_w(expr.func, env, gen)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        s2, t2 = infer_w(expr.arg, env1, gen)
        tv = gen.fresh()
        s3 = unify(apply_subst(s2, t1), TFun(t2, tv), expr.span)
        return compose_subst(s3, compose_subst(s2, s1)), apply_subst(s3, tv)
    if isinstance(expr, ELet):
        s1, t1 = infer_w(expr.rhs, env, gen)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        env1[expr.name] = generalize(env1, t1)
        s2, t2 = infer_w(expr.body, env1, gen)
        return compose_subst(s2, s1), t2
    if isinstance(expr, EAnn):
        s1, t1 = infer_w(expr.expr, env, gen)
        s2 = unify(t1, expr.ty, expr.span)
        return compose_subst(s2, s1), apply_subst(s2, expr.ty)
    if isinstance(expr, ETuple):
        s: dict[int, Type] = {}
        ts: list[Type] = []
        cur_env = dict(env)
        for el in expr.elems:
            si, ti = infer_w(el, cur_env, gen)
            s = compose_subst(si, s)
            ts = [apply_subst(si, t) for t in ts] + [ti]
            cur_env = {k: Scheme(v.quantified, apply_subst(si, v.ty)) for k, v in cur_env.items()}
        return s, TTuple(tuple(ts))
    if isinstance(expr, EIf):
        s1, t1 = infer_w(expr.cond, env, gen)
        s_cond = unify(t1, T_BOOL, expr.cond.span)
        s1 = compose_subst(s_cond, s1)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        s2, t2 = infer_w(expr.then_br, env1, gen)
        env2 = {k: Scheme(v.quantified, apply_subst(s2, v.ty)) for k, v in env1.items()}
        s3, t3 = infer_w(expr.else_br, env2, gen)
        s4 = unify(apply_subst(s3, t2), t3, expr.span)
        return compose_subst(s4, compose_subst(s3, compose_subst(s2, s1))), apply_subst(s4, t3)
    raise TypeError(expr)


# --- 1B. Top-Down Context-Sensitive Algorithm M / Bidirectional Checking ---


def check_m(expr: Expr, expected: Type, env: dict[str, Scheme], gen: FreshGen) -> dict[int, Type]:
    """Top-down Algorithm M (Lee & Yi 1998) / Bidirectional expected-type checking."""
    if isinstance(expr, EInt):
        return unify(T_INT, expected, expr.span)
    if isinstance(expr, EBool):
        return unify(T_BOOL, expected, expr.span)
    if isinstance(expr, EStr):
        return unify(T_STR, expected, expr.span)
    if isinstance(expr, EVar):
        t_var = instantiate(env[expr.name], gen)
        return unify(t_var, expected, expr.span)
    if isinstance(expr, ELam):
        tv_arg = gen.fresh()
        tv_ret = gen.fresh()
        s1 = unify(expected, TFun(tv_arg, tv_ret), expr.span)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        env1[expr.param] = Scheme(frozenset(), apply_subst(s1, tv_arg))
        s2 = check_m(expr.body, apply_subst(s1, tv_ret), env1, gen)
        return compose_subst(s2, s1)
    if isinstance(expr, EApp):
        tv_arg = gen.fresh()
        s1 = check_m(expr.func, TFun(tv_arg, expected), env, gen)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        s2 = check_m(expr.arg, apply_subst(s1, tv_arg), env1, gen)
        return compose_subst(s2, s1)
    if isinstance(expr, EAnn):
        s1 = unify(expr.ty, expected, expr.span)
        s2 = check_m(expr.expr, apply_subst(s1, expr.ty), env, gen)
        return compose_subst(s2, s1)
    if isinstance(expr, ETuple):
        tvs = tuple(gen.fresh() for _ in expr.elems)
        s = unify(expected, TTuple(tvs), expr.span)
        cur_env = {k: Scheme(v.quantified, apply_subst(s, v.ty)) for k, v in env.items()}
        for el, tv in zip(expr.elems, tvs):
            si = check_m(el, apply_subst(s, tv), cur_env, gen)
            s = compose_subst(si, s)
            cur_env = {k: Scheme(v.quantified, apply_subst(si, v.ty)) for k, v in cur_env.items()}
        return s
    if isinstance(expr, EIf):
        s1 = check_m(expr.cond, T_BOOL, env, gen)
        env1 = {k: Scheme(v.quantified, apply_subst(s1, v.ty)) for k, v in env.items()}
        s2 = check_m(expr.then_br, apply_subst(s1, expected), env1, gen)
        env2 = {k: Scheme(v.quantified, apply_subst(s2, v.ty)) for k, v in env1.items()}
        s3 = check_m(expr.else_br, apply_subst(compose_subst(s2, s1), expected), env2, gen)
        return compose_subst(s3, compose_subst(s2, s1))
    raise TypeError(expr)


# --- 1C. Provenance-Carrying Constraint Generation + Exact MUS / Weighted MCS / SHErrLoc ---


@dataclass(frozen=True)
class Constraint:
    cid: int
    lhs: Type
    rhs: Type
    site: str
    weight: float = 1.0
    hard: bool = False  # Structural plumbing edges (hard) vs blameable site constraints (soft)


def generate_constraints(
    expr: Expr,
    env: dict[str, Scheme],
    gen: FreshGen,
    out: list[Constraint],
) -> Type:
    """Emit fine-grained equality constraints tagged with source-site provenance.

    Hard constraints represent structural AST wiring (variable identity, tuple shape,
    branch result merge); soft constraints correspond to programmer-authored expression
    sites that can be blamed as error sources.
    """

    def add(lhs: Type, rhs: Type, site: str, weight: float = 1.0, hard: bool = False) -> None:
        out.append(Constraint(len(out), lhs, rhs, site, weight, hard))

    if isinstance(expr, EInt):
        tv = gen.fresh()
        add(tv, T_INT, expr.span)
        return tv
    if isinstance(expr, EBool):
        tv = gen.fresh()
        add(tv, T_BOOL, expr.span)
        return tv
    if isinstance(expr, EStr):
        tv = gen.fresh()
        add(tv, T_STR, expr.span)
        return tv
    if isinstance(expr, EVar):
        tv = gen.fresh()
        inst = instantiate(env[expr.name], gen)
        is_local = expr.name not in BASE_ENV
        add(tv, inst, expr.span, hard=is_local)
        return tv
    if isinstance(expr, ELam):
        tv_p = gen.fresh()
        env2 = dict(env)
        env2[expr.param] = Scheme(frozenset(), tv_p)
        t_body = generate_constraints(expr.body, env2, gen, out)
        return TFun(tv_p, t_body)
    if isinstance(expr, EApp):
        # Cohesive two-argument polymorphic `same a b` call: one soft site equating arg1 == arg2
        if (
            isinstance(expr.func, EApp)
            and isinstance(expr.func.func, EVar)
            and expr.func.func.name == "same"
        ):
            t_a = generate_constraints(expr.func.arg, env, gen, out)
            t_b = generate_constraints(expr.arg, env, gen, out)
            add(t_a, t_b, expr.span)
            return t_a
        # Cohesive unary primitive call like `not x` or `add1 x`
        if isinstance(expr.func, EVar) and expr.func.name in BASE_ENV:
            t_arg = generate_constraints(expr.arg, env, gen, out)
            tv_ret = gen.fresh()
            prim_ty = instantiate(BASE_ENV[expr.func.name], gen)
            add(prim_ty, TFun(t_arg, tv_ret), expr.span)
            return tv_ret
        t_fn = generate_constraints(expr.func, env, gen, out)
        t_arg = generate_constraints(expr.arg, env, gen, out)
        tv_ret = gen.fresh()
        add(t_fn, TFun(t_arg, tv_ret), expr.span)
        return tv_ret
    if isinstance(expr, ELet):
        # Monomorphic shared variable for let-bound value exposes definition-vs-use blame
        t_rhs = generate_constraints(expr.rhs, env, gen, out)
        env2 = dict(env)
        env2[expr.name] = Scheme(frozenset(), t_rhs)
        return generate_constraints(expr.body, env2, gen, out)
    if isinstance(expr, EAnn):
        t_sub = generate_constraints(expr.expr, env, gen, out)
        add(t_sub, expr.ty, expr.span, weight=1.5)  # Higher prior trust on explicit type annotations
        return expr.ty
    if isinstance(expr, ETuple):
        return TTuple(tuple(generate_constraints(e, env, gen, out) for e in expr.elems))
    if isinstance(expr, EIf):
        t_c = generate_constraints(expr.cond, env, gen, out)
        add(t_c, T_BOOL, expr.cond.span)
        t_t = generate_constraints(expr.then_br, env, gen, out)
        t_e = generate_constraints(expr.else_br, env, gen, out)
        tv = gen.fresh()
        add(t_t, tv, f"{expr.span}:then_merge", hard=True)
        add(t_e, tv, f"{expr.span}:else_merge", hard=True)
        return tv
    raise TypeError(expr)


def is_satisfiable(constraints: list[Constraint]) -> bool:
    subst: dict[int, Type] = {}
    for c in constraints:
        try:
            s = unify(apply_subst(subst, c.lhs), apply_subst(subst, c.rhs), c.site)
            subst = compose_subst(s, subst)
        except UnifyError:
            return False
    return True


def enumerate_all_muses(constraints: list[Constraint]) -> list[frozenset[int]]:
    """Exact enumeration of all Minimal Unsatisfiable Subsets (MUSes) of soft constraints."""
    hard = [c for c in constraints if c.hard]
    soft = [c for c in constraints if not c.hard]
    soft_by_id = {c.cid: c for c in soft}
    soft_ids = [c.cid for c in soft]
    muses: list[frozenset[int]] = []

    for r in range(1, len(soft_ids) + 1):
        for comb in combinations(soft_ids, r):
            cand = frozenset(comb)
            if any(m.issubset(cand) for m in muses):
                continue
            if not is_satisfiable(hard + [soft_by_id[i] for i in comb]):
                muses.append(cand)
    return muses


def enumerate_minimal_mcses(
    constraints: list[Constraint], muses: list[frozenset[int]]
) -> list[tuple[float, frozenset[int]]]:
    """Enumerate Minimal Correction Subsets (minimal hitting sets of all MUSes) sorted by weight."""
    by_id = {c.cid: c for c in constraints}
    hitting_sets: list[frozenset[int]] = []

    def search(cur: frozenset[int], idx: int) -> None:
        if idx == len(muses):
            if any(h.issubset(cur) for h in hitting_sets):
                return
            hitting_sets[:] = [h for h in hitting_sets if not cur.issubset(h)]
            hitting_sets.append(cur)
            return
        mus = muses[idx]
        if cur & mus:
            search(cur, idx + 1)
            return
        for cid in sorted(mus):
            search(cur | {cid}, idx + 1)

    search(frozenset(), 0)
    weighted = [(sum(by_id[cid].weight for cid in hs), hs) for hs in hitting_sets]
    weighted.sort(key=lambda item: (item[0], len(item[1]), sorted(by_id[c].site for c in item[1])))
    return weighted


def sherrloc_bayesian_rank(
    constraints: list[Constraint],
    muses: list[frozenset[int]],
    mcses: list[tuple[float, frozenset[int]]],
    p_err: float = 0.05,
) -> list[dict[str, Any]]:
    """SHErrLoc-inspired Bayesian ranking over candidate MCS explanations."""
    hard = [c for c in constraints if c.hard]
    soft = [c for c in constraints if not c.hard]
    by_id = {c.cid: c for c in soft}

    hard_subst: dict[int, Type] = {}
    for hc in hard:
        hard_subst = compose_subst(
            unify(apply_subst(hard_subst, hc.lhs), apply_subst(hard_subst, hc.rhs), hc.site),
            hard_subst,
        )

    def enforced_con(c: Constraint) -> set[str]:
        s = unify(apply_subst(hard_subst, c.lhs), apply_subst(hard_subst, c.rhs), c.site)
        cons: set[str] = set()

        def walk(t: Type) -> None:
            if isinstance(t, TCon):
                cons.add(t.name)
            elif isinstance(t, TFun):
                walk(t.arg)
                walk(t.ret)
            elif isinstance(t, TTuple):
                for e in t.elems:
                    walk(e)

        for v in s.values():
            walk(v)
        return cons

    sat_corroborations: dict[int, int] = {c.cid: 0 for c in soft}
    con_map = {c.cid: enforced_con(c) for c in soft}
    var_map = {
        c.cid: ftv_type(apply_subst(hard_subst, c.lhs)) | ftv_type(apply_subst(hard_subst, c.rhs))
        for c in soft
    }
    for c1, c2 in combinations(soft, 2):
        if (var_map[c1.cid] & var_map[c2.cid]) and (con_map[c1.cid] & con_map[c2.cid]):
            if is_satisfiable(hard + [c1, c2]):
                sat_corroborations[c1.cid] += 1
                sat_corroborations[c2.cid] += 1

    mus_freq: dict[int, int] = {c.cid: 0 for c in soft}
    for m in muses:
        for cid in m:
            mus_freq[cid] += 1

    n_soft = len(soft)
    ranked: list[dict[str, Any]] = []
    for weight, hs in mcses:
        k = len(hs)
        log_prior = k * math.log(p_err) + (n_soft - k) * math.log(1.0 - p_err)
        corrob = sum(sat_corroborations[cid] for cid in hs)
        log_likelihood = -1.2 * corrob - 0.5 * (weight - k) + 0.15 * sum(mus_freq[cid] for cid in hs)
        log_posterior = log_prior + log_likelihood
        ranked.append(
            {
                "sites": sorted(by_id[cid].site for cid in hs),
                "mcs_size": k,
                "mcs_weight": weight,
                "mus_hits": sum(mus_freq[cid] for cid in hs),
                "corroborated_sat_peers": corrob,
                "log_posterior": round(log_posterior, 4),
            }
        )
    ranked.sort(key=lambda r: (-r["log_posterior"], r["mcs_weight"], r["sites"]))
    return ranked


def app2(fn: str, a: Expr, b: Expr, span: str) -> Expr:
    return EApp(EApp(EVar(fn, f"v_{fn}"), a, f"{span}:partial"), b, span)


def run_type_localization_benchmarks() -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []

    # Benchmark 1: Order-Sensitive Multi-Use Tuple (Classic Algorithm W left-to-right bias)
    b1 = ELam(
        "x",
        ETuple(
            (
                EApp(EVar("not", "v_not"), EVar("x", "x0"), "site:not_x"),
                EApp(EVar("add1", "v_add1_1"), EVar("x", "x1"), "site:add1_x_1"),
                EApp(EVar("add1", "v_add1_2"), EVar("x", "x2"), "site:add1_x_2"),
                EApp(EVar("add1", "v_add1_3"), EVar("x", "x3"), "site:add1_x_3"),
            ),
            "site:tuple",
        ),
        "site:lam_x",
    )

    # Benchmark 2: Reversed order of B1 — shows Algorithm W flips blame while MUS/MCS is invariant
    b2 = ELam(
        "x",
        ETuple(
            (
                EApp(EVar("add1", "v_add1_1"), EVar("x", "x1"), "site:add1_x_1"),
                EApp(EVar("add1", "v_add1_2"), EVar("x", "x2"), "site:add1_x_2"),
                EApp(EVar("add1", "v_add1_3"), EVar("x", "x3"), "site:add1_x_3"),
                EApp(EVar("not", "v_not"), EVar("x", "x0"), "site:not_x"),
            ),
            "site:tuple",
        ),
        "site:lam_x",
    )

    # Benchmark 3: Multi-Site Polymorphic Propagation Chain
    b3 = ELam(
        "x",
        ELam(
            "y",
            ELet(
                "zero",
                EBool(False, "site:zero_false"),
                ELet(
                    "p1",
                    app2("same", EVar("zero", "z1"), EVar("x", "x1"), "site:same_zero_x"),
                    ELet(
                        "p2",
                        app2("same", EVar("x", "x2"), EVar("y", "y1"), "site:same_x_y"),
                        ETuple(
                            (
                                EVar("p1", "use_p1"),
                                EVar("p2", "use_p2"),
                                EApp(EVar("add1", "v_a1"), EVar("y", "y2"), "site:add1_y_innocent"),
                                EApp(EVar("add1", "v_a2"), EVar("x", "x3"), "site:add1_x_innocent"),
                                EApp(EVar("add1", "v_a3"), EVar("zero", "z2"), "site:add1_zero_innocent"),
                            ),
                            "site:result_tuple",
                        ),
                        "site:let_p2",
                    ),
                    "site:let_p1",
                ),
                "site:let_zero",
            ),
            "site:lam_y",
        ),
        "site:lam_x",
    )

    # Benchmark 4: Defective helper definition vs 3 consistent call sites
    b4 = ELet(
        "f",
        ELam("x", EApp(EVar("add1", "v_add1"), EVar("x", "x_body"), "site:def_body_add1"), "site:def_f"),
        ETuple(
            (
                EApp(EVar("f", "f1"), EBool(True, "site:call1_arg_true"), "site:call1"),
                EApp(EVar("f", "f2"), EBool(False, "site:call2_arg_false"), "site:call2"),
                EApp(EVar("f", "f3"), EBool(True, "site:call3_arg_true"), "site:call3"),
            ),
            "site:calls_tuple",
        ),
        "site:let_f",
    )

    # Benchmark 5: Lee & Yi (1998) Algorithm W late failure vs Algorithm M early failure
    b5 = EAnn(
        ELam("x", EApp(EVar("add1", "v_add1"), EVar("x", "site:leaf_x"), "site:body_add1_x"), "site:lam"),
        TFun(T_BOOL, T_INT),
        "site:outer_annotation",
    )

    # Benchmark 6: Symmetric 2-site conflict (genuinely non-unique blame)
    b6 = EIf(
        EBool(True, "site:cond_true"),
        EInt(1, "site:then_int"),
        EStr("oops", "site:else_str"),
        "site:if_expr",
    )

    benchmarks = [
        ("B1_tuple_bug_first", b1, ["site:not_x"]),
        ("B2_tuple_bug_last", b2, ["site:not_x"]),
        ("B3_poly_chain_propagated_bug", b3, ["site:zero_false"]),
        ("B4_defective_helper_3_callers", b4, ["site:def_body_add1"]),
        ("B5_annotated_lambda_W_vs_M", b5, ["site:body_add1_x"]),
        ("B6_symmetric_if_branches", b6, None),
    ]

    for name, expr, expected_top in benchmarks:
        w_blame = "TYPECHECKED"
        try:
            infer_w(expr, BASE_ENV, FreshGen())
        except UnifyError as e:
            w_blame = e.span

        m_blame: str | None = None
        if name in ("B1_tuple_bug_first", "B2_tuple_bug_last", "B5_annotated_lambda_W_vs_M", "B6_symmetric_if_branches"):
            m_gen = FreshGen()
            try:
                check_m(expr, m_gen.fresh(), BASE_ENV, m_gen)
                m_blame = "TYPECHECKED"
            except UnifyError as e:
                m_blame = e.span

        cs: list[Constraint] = []
        generate_constraints(expr, BASE_ENV, FreshGen(), cs)
        muses = enumerate_all_muses(cs)
        mcses = enumerate_minimal_mcses(cs, muses)
        ranked = sherrloc_bayesian_rank(cs, muses, mcses)
        by_id = {c.cid: c for c in cs}
        mus_sites = [sorted(by_id[i].site for i in m) for m in muses]

        top_sites = ranked[0]["sites"]
        if expected_top is not None:
            assert top_sites == expected_top, f"{name}: expected top {expected_top}, got {top_sites}"

        results.append(
            {
                "benchmark": name,
                "algorithm_w_blame": w_blame,
                "algorithm_m_blame": m_blame,
                "num_muses": len(muses),
                "muses": mus_sites,
                "top_mcs_sherrloc": ranked[0],
                "runner_up": ranked[1] if len(ranked) > 1 else None,
            }
        )

    assert results[0]["algorithm_w_blame"] == "site:add1_x_1"
    assert results[1]["algorithm_w_blame"] == "site:not_x"
    assert results[2]["algorithm_w_blame"] == "site:add1_y_innocent"
    assert results[3]["algorithm_w_blame"] == "site:call1"
    assert results[4]["algorithm_w_blame"] == "site:outer_annotation"
    assert results[4]["algorithm_m_blame"] == "site:leaf_x"
    assert results[0]["top_mcs_sherrloc"]["sites"] == ["site:not_x"]
    assert results[1]["top_mcs_sherrloc"]["sites"] == ["site:not_x"]
    assert results[2]["top_mcs_sherrloc"]["sites"] == ["site:zero_false"]
    assert results[2]["top_mcs_sherrloc"]["mus_hits"] == 3
    assert results[3]["top_mcs_sherrloc"]["sites"] == ["site:def_body_add1"]
    assert results[3]["top_mcs_sherrloc"]["corroborated_sat_peers"] == 0
    assert results[5]["top_mcs_sherrloc"]["log_posterior"] == results[5]["runner_up"]["log_posterior"]
    assert {
        results[5]["top_mcs_sherrloc"]["sites"][0],
        results[5]["runner_up"]["sites"][0],
    } == {"site:then_int", "site:else_str"}

    return results


# =============================================================================
# Part 2: Why3-Style Giant-Step RAC Counterexample Validation & Classification
# =============================================================================


@dataclass(frozen=True)
class RacOutcome:
    kind: str  # "NORMAL" | "FAIL" | "STUCK" | "INCOMPLETE"
    loc: str | None = None
    reason: str = ""
    trace: tuple[str, ...] = ()


def classify_ce(vc_loc: str, normal: RacOutcome, giant: RacOutcome) -> tuple[str, str]:
    """Exact translation of Why3 `Check_ce.classify` (`src/mlw/check_ce.ml` lines 153-188)."""
    if normal.kind == "FAIL":
        if normal.loc == vc_loc:
            return "NC", f"Concrete execution violated VC at {vc_loc}: {normal.reason}"
        return "BAD_CE", f"Concrete execution failed at non-VC location {normal.loc}: {normal.reason}"
    if normal.kind == "STUCK":
        return "BAD_CE", f"Concrete execution stuck (invalid input/assumption): {normal.reason}"
    if normal.kind == "NORMAL":
        if giant.kind == "FAIL":
            return "SW", f"Program conforms concretely, but giant-step violated {giant.loc}: {giant.reason}"
        if giant.kind == "STUCK":
            return "BAD_CE", f"Giant-step stuck (spurious oracle violates contract/axiom): {giant.reason}"
        if giant.kind == "NORMAL":
            return "BAD_CE", "no failure in either concrete or giant-step execution"
        if giant.kind == "INCOMPLETE":
            return "INCOMPLETE", f"abstract RAC {giant.reason}"
    if normal.kind == "INCOMPLETE":
        if giant.kind == "FAIL":
            return "NC_SW", f"Concrete RAC incomplete ({normal.reason}), giant-step failed: {giant.reason}"
        if giant.kind == "NORMAL":
            return "INCOMPLETE", normal.reason
        if giant.kind == "INCOMPLETE":
            return "INCOMPLETE", f"concrete RAC {normal.reason}, abstract RAC {giant.reason}"
        if giant.kind == "STUCK":
            return "BAD_CE", f"Giant-step stuck: {giant.reason}"
    raise ValueError(f"Unhandled RAC pair: {normal}, {giant}")


@dataclass
class LoopProgram:
    """Imperative routine with contracts for Normal (concrete) and Giant-Step RAC."""

    name: str
    vc_loc: str
    requires: Callable[[dict[str, int]], bool]
    ensures: Callable[[dict[str, int], int], bool]
    concrete_run: Callable[[dict[str, int], int], tuple[int | None, str | None]]
    giant_step_run: Callable[[dict[str, int], dict[str, Any]], RacOutcome]


def run_normal_rac(prog: LoopProgram, oracle: dict[str, Any], step_limit: int = 10_000) -> RacOutcome:
    args = dict(oracle["inputs"])
    if not prog.requires(args):
        return RacOutcome("STUCK", reason="oracle inputs violate function precondition")
    ret, inc_reason = prog.concrete_run(args, step_limit)
    if inc_reason is not None:
        return RacOutcome("INCOMPLETE", reason=inc_reason)
    assert ret is not None
    if not prog.ensures(args, ret):
        return RacOutcome("FAIL", loc=prog.vc_loc, reason=f"ensures violated for inputs={args}, ret={ret}")
    return RacOutcome("NORMAL", trace=(f"inputs={args} -> ret={ret}",))


def run_giant_step_validation_suite() -> list[dict[str, Any]]:
    cases: list[tuple[str, LoopProgram, dict[str, Any], str]] = []

    def abs_concrete(args: dict[str, int], _limit: int) -> tuple[int | None, str | None]:
        return args["x"], None

    def abs_giant(args: dict[str, int], _oracle: dict[str, Any]) -> RacOutcome:
        ret = args["x"]
        if not (ret >= 0):
            return RacOutcome("FAIL", loc="vc:abs_post", reason=f"ret={ret} < 0")
        return RacOutcome("NORMAL")

    cases.append(
        (
            "CE1_real_program_bug_NC",
            LoopProgram(
                name="abs_buggy",
                vc_loc="vc:abs_post",
                requires=lambda a: True,
                ensures=lambda a, r: r >= 0,
                concrete_run=abs_concrete,
                giant_step_run=abs_giant,
            ),
            {"inputs": {"x": -5}},
            "NC",
        )
    )

    def count_concrete(args: dict[str, int], limit: int) -> tuple[int | None, str | None]:
        n = args["n"]
        i, s = 0, 0
        steps = 0
        while i < n:
            steps += 1
            if steps > limit:
                return None, f"step limit {limit} exceeded"
            s += 1
            i += 1
        return s, None

    def count_giant_weak_inv(args: dict[str, int], oracle: dict[str, Any]) -> RacOutcome:
        n = args["n"]
        if not (0 <= 0 <= n):
            return RacOutcome("FAIL", loc="vc:inv_init", reason="loop invariant init failed")
        st = oracle["loop_exit"]
        i_end, s_end = st["i"], st["s"]
        if not (0 <= i_end <= n and not (i_end < n)):
            return RacOutcome("STUCK", reason="oracle post-loop state violates invariant or exit guard")
        if not (s_end == n):
            return RacOutcome("FAIL", loc="vc:count_post", reason=f"giant-step s={s_end} != n={n}")
        return RacOutcome("NORMAL")

    cases.append(
        (
            "CE2_weak_loop_invariant_SW",
            LoopProgram(
                name="count_to_n_weak_inv",
                vc_loc="vc:count_post",
                requires=lambda a: a["n"] >= 0,
                ensures=lambda a, r: r == a["n"],
                concrete_run=count_concrete,
                giant_step_run=count_giant_weak_inv,
            ),
            {"inputs": {"n": 2}, "loop_exit": {"i": 2, "s": 99}},
            "SW",
        )
    )

    def caller_sq_concrete(args: dict[str, int], _limit: int) -> tuple[int | None, str | None]:
        x = args["x"]
        return x * x, None

    def caller_sq_giant(args: dict[str, int], oracle: dict[str, Any]) -> RacOutcome:
        x = args["x"]
        y_oracle = oracle["callee_ret"]["sq"]
        if not (y_oracle == x * x and y_oracle >= 0):
            return RacOutcome(
                "STUCK",
                reason=f"spurious SMT oracle sq({x})={y_oracle} violates callee postcondition result==x*x && result>=0",
            )
        if not (y_oracle >= 0):
            return RacOutcome("FAIL", loc="vc:sq_nonneg", reason=f"y={y_oracle} < 0")
        return RacOutcome("NORMAL")

    cases.append(
        (
            "CE3_spurious_uninterpreted_axiom_BAD_CE",
            LoopProgram(
                name="caller_sq_untriggered_axiom",
                vc_loc="vc:sq_nonneg",
                requires=lambda a: True,
                ensures=lambda a, r: r >= 0,
                concrete_run=caller_sq_concrete,
                giant_step_run=caller_sq_giant,
            ),
            {"inputs": {"x": 3}, "callee_ret": {"sq": -7}},
            "BAD_CE",
        )
    )

    cases.append(
        (
            "CE4_timeout_trivial_model_BAD_CE",
            LoopProgram(
                name="caller_sq_timeout_default",
                vc_loc="vc:sq_nonneg",
                requires=lambda a: True,
                ensures=lambda a, r: r >= 0,
                concrete_run=caller_sq_concrete,
                giant_step_run=caller_sq_giant,
            ),
            {"inputs": {"x": 0}, "callee_ret": {"sq": 0}},
            "BAD_CE",
        )
    )

    cases.append(
        (
            "CE5_large_loop_concrete_incomplete_NC_SW",
            LoopProgram(
                name="count_to_n_large_bound",
                vc_loc="vc:count_post",
                requires=lambda a: a["n"] >= 0,
                ensures=lambda a, r: r == a["n"],
                concrete_run=count_concrete,
                giant_step_run=count_giant_weak_inv,
            ),
            {"inputs": {"n": 10_000_000}, "loop_exit": {"i": 10_000_000, "s": 42}},
            "NC_SW",
        )
    )

    summary: list[dict[str, Any]] = []
    for label, prog, oracle, expected_verdict in cases:
        norm = run_normal_rac(prog, oracle)
        giant = prog.giant_step_run(dict(oracle["inputs"]), oracle)
        verdict, explanation = classify_ce(prog.vc_loc, norm, giant)
        assert verdict == expected_verdict, (
            f"{label}: expected {expected_verdict}, got {verdict} ({explanation})"
        )
        summary.append(
            {
                "case": label,
                "normal_rac": norm.kind,
                "giant_step_rac": giant.kind,
                "verdict": verdict,
                "explanation": explanation,
            }
        )
    return summary


def main() -> int:
    print("=== Part 1: Type-Error Localization (Algorithm W vs M vs MUS/MCS/SHErrLoc) ===")
    type_results = run_type_localization_benchmarks()
    for r in type_results:
        top = r["top_mcs_sherrloc"]
        ru = r["runner_up"]
        ru_str = (
            f" | runner_up={ru['sites']} (size={ru['mcs_size']}, logP={ru['log_posterior']})"
            if ru is not None
            else ""
        )
        print(
            f"  {r['benchmark']}: W={r['algorithm_w_blame']} | M={r['algorithm_m_blame']} | "
            f"#MUS={r['num_muses']} | Top={top['sites']} (size={top['mcs_size']}, "
            f"mus_hits={top['mus_hits']}, sat_peers={top['corroborated_sat_peers']}, "
            f"logP={top['log_posterior']}){ru_str}"
        )

    print("\n=== Part 2: Giant-Step RAC Counterexample Validation (Why3 Classification) ===")
    ce_results = run_giant_step_validation_suite()
    for c in ce_results:
        print(
            f"  {c['case']}: normal={c['normal_rac']} | giant={c['giant_step_rac']} "
            f"-> {c['verdict']} ({c['explanation']})"
        )

    print("\n[OK] All type-error localization and giant-step CE validation assertions passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
