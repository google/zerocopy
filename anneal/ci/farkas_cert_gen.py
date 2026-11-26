# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Synthesize verified `Anneal.LinearArith` Farkas and cut certificates."""

from __future__ import annotations

import argparse
from collections import deque
from functools import reduce
import json
import math
import re
import sys
from typing import Any

_TOK_RE = re.compile(r"\s*(<=|<|>=|>|==|=|\+|-|\*|\(|\)|[A-Za-z_][A-Za-z0-9_']*|\d+)")
_IDENT_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_REL_OPS = frozenset({"<=", "<", ">=", ">", "=", "=="})
_MAG_CAP_128, _MAX_LITERAL_DIGITS = 1 << 128, 40
_MAX_AST_DEPTH, _MAX_EXPR_NODES, _MAX_PARSE_NESTING, _MAX_CERT_DEPTH = 16, 48, 32, 16
_KERNEL_CAPS = {"nat": (30, 30, 176, 88, 68), "int": (44, 44, 1000, 500, 96)}
_NAT_MAX_JOINT_WORK = 360
_LEAN_KEYWORDS = frozenset((
    "Prop Sort StateRefT Type _ abbrev add_decl_doc admit assert_not_exists assert_not_imported at "
    "attribute axiom bif binder_predicate break builtin_cbv_simproc builtin_cbv_simproc_decl "
    "builtin_dsimproc builtin_dsimproc_decl builtin_grind_propagator builtin_initialize "
    "builtin_simproc builtin_simproc_decl by by_elab calc catch cbv_eval cbv_simproc "
    "cbv_simproc_decl class coinductive coinductive_fixpoint continue dbg_trace "
    "declare_bitwise_int_theorems declare_bitwise_uint_theorems declare_command_config_elab "
    "declare_command_config_elab_legacy declare_config_elab declare_config_elab_legacy "
    "declare_core_config_elab declare_eval_bin declare_eval_bin_bitwise declare_eval_bin_bool_pred "
    "declare_int_theorems declare_simp_like_tactic declare_sint_simprocs declare_syntax_cat "
    "declare_term_config_elab declare_uint_simprocs declare_uint_theorems decreasing_by def "
    "def_eval_config_item deprecated_module deprecated_syntax deriving do docs_to_verso dsimproc "
    "dsimproc_decl elab elab_rules elab_stx_quot else end eval_prec eval_prio example exists "
    "export extends false finally for forall from fun generalizing grind_annotated grind_pattern "
    "grind_propagator have haveI hiding idbg if import in include include_str inductive "
    "inductive_fixpoint inferInstanceAs infix infixl infixr init_grind_norm init_quot initialize "
    "instance leading_parser lemma let letI let_delayed let_expr let_fun let_tmp local "
    "logNamedError logNamedErrorAt logNamedWarning logNamedWarningAt macro macro_rules match "
    "match_expr matches max_prec meta mod_cast module mut mutual namespace nat_lit no_index nofun "
    "nomatch noncomputable nonrec norm_cast_add_elim notation omit opaque open partial "
    "partial_fixpoint postfix prefix prelude private protected public rec recommended_spelling "
    "register_builtin_option register_error_explanation register_grind_attr register_label_attr "
    "register_linter_set register_option register_parser_alias register_simp_attr "
    "register_sym_dsimp register_sym_simp register_sym_simp_attr register_tactic_tag renaming "
    "repeat reprove return rfl run_cmd run_elab run_meta scoped seal section "
    "set_library_suggestions set_option show show_panel_widgets show_term show_term_elab simproc "
    "simproc_decl sorry sorryAx structure suffices syntax tactic_alt tactic_extension tactic_name "
    "tactic_tag termination_by test_extern then theorem throwError throwErrorAt throwNamedError "
    "throwNamedErrorAt trailing_parser true try unif_hint universe unless unlock_limits unsafe "
    "unseal until using variable where while with with_annotate_term with_weak_namespace "
    "without_expected_type Nat Int List CutStep NatCutGoal IntCutGoal checkNatCutGoal_sound "
    "checkIntCutGoal_sound Anneal LinearArith Init Lean"
).split())


class ParseError(ValueError):
    """Raised on unsupported or malformed linear arithmetic input."""


def _as_const(n: tuple[Any, ...]) -> int | None:
    if n[0] in ("cst", "var"):
        return n[1] if n[0] == "cst" else None
    if n[0] in ("neg", "mulC"):
        return None if (v := _as_const(n[-1])) is None else (-v if n[0] == "neg" else n[1] * v)
    a, b = _as_const(n[1]), _as_const(n[2])
    return None if (a is None or b is None) else (a + b if n[0] == "add" else a - b)


def _eval_linear(n: tuple[Any, ...]) -> tuple[dict[str, int], int]:
    if n[0] in ("cst", "var"):
        return ({}, n[1]) if n[0] == "cst" else ({n[1]: 1}, 0)
    if n[0] in ("neg", "mulC"):
        c, c0 = _eval_linear(n[-1])
        s = -1 if n[0] == "neg" else n[1]
        return {v: s * w for v, w in c.items() if s * w}, s * c0
    lc, lk = _eval_linear(n[1])
    rc, rk = _eval_linear(n[2])
    sgn = 1 if n[0] == "add" else -1
    return {v: nv for v in (*lc, *rc) if (nv := lc.get(v, 0) + sgn * rc.get(v, 0))}, lk + sgn * rk


def _walk_ast(
    n: tuple[Any, ...], domain: str, vars_out: dict[str, None] | None = None, *, caps: bool = False
) -> tuple[int, int, int, bool]:
    k = n[0]
    if k == "cst":
        if caps and ((domain == "nat" and n[1] < 0) or abs(n[1]) > _MAG_CAP_128):
            raise ParseError("Constant out of range (`< 0` in nat or `> 2^128`).")
        d, cnt, vo, hv = 0, 1, 0, False
    elif k == "var":
        if vars_out is not None:
            vars_out.setdefault(n[1], None)
        d, cnt, vo, hv = 0, 1, 1, True
    elif k in ("neg", "mulC"):
        if caps and k == "mulC" and abs(n[1]) > _MAG_CAP_128:
            raise ParseError("Multiplier exceeds `magCap128` (`2^128`).")
        sd, sc, vo, hv = _walk_ast(n[-1], domain, vars_out, caps=caps)
        d, cnt = 1 + sd, 1 + sc
    else:
        ld, lc, lv, lhv = _walk_ast(n[1], domain, vars_out, caps=caps)
        rd, rc, rv, rhv = _walk_ast(n[2], domain, vars_out, caps=caps)
        d, cnt, vo, hv = 1 + max(ld, rd), 1 + lc + rc, lv + rv, lhv or rhv
    if caps and (d > _MAX_AST_DEPTH or cnt > _MAX_EXPR_NODES):
        raise ParseError(f"Expression exceeds kernel limits (depth {d}, nodes {cnt}).")
    return d, cnt, vo, hv


def _parse_expr(tokens: list[str], domain: str, *, reserved: frozenset[str]) -> tuple[Any, ...]:
    pos = 0

    def pop(exp: str | None = None) -> str:
        nonlocal pos
        tok = tokens[pos] if pos < len(tokens) else None
        if tok is None or (exp is not None and tok != exp):
            raise ParseError(f"Expected `{exp or 'expr'}`, got {tok or 'EOF'}")
        pos += 1
        return tok

    def int_lit(tok: str, neg: bool = False) -> int:
        if len(tok) > _MAX_LITERAL_DIGITS:
            raise ParseError("Constant exceeds `magCap128` (`2^128`).")
        return -int(tok) if neg else int(tok)

    def expr(depth: int = 0) -> tuple[Any, ...]:
        if depth > _MAX_PARSE_NESTING:
            raise ParseError("Expression nesting depth exceeded.")
        acc = term(depth)
        while pos < len(tokens) and tokens[pos] in ("+", "-"):
            if (op := pop()) == "-" and domain == "nat":
                raise ParseError("Subtraction disallowed in `--domain nat`; use `--domain int`.")
            acc = ("add" if op == "+" else "sub", acc, term(depth))
        return acc

    def term(depth: int) -> tuple[Any, ...]:
        acc = unary(depth)
        while pos < len(tokens) and tokens[pos] == "*":
            pop("*")
            lc, rc = _as_const(acc), _as_const(rhs := unary(depth))
            if lc is not None and rc is not None:
                if abs(prod := lc * rc) > _MAG_CAP_128:
                    raise ParseError("Constant exceeds `magCap128` (`2^128`).")
                acc = ("cst", prod)
            elif lc is not None:
                acc = ("mulC", lc, rhs)
            else:
                raise ParseError("Put scalar multiplier on left (`2 * x`), no var*var.")
        return acc

    def unary(depth: int) -> tuple[Any, ...]:
        if depth > _MAX_PARSE_NESTING:
            raise ParseError("Expression nesting depth exceeded.")
        nxt = tokens[pos] if pos < len(tokens) else None
        if nxt == "+":
            return pop("+") and unary(depth + 1)
        if nxt == "-":
            if domain == "nat":
                raise ParseError("Unary `-` disallowed in `--domain nat`; use `--domain int`.")
            pop("-")
            if pos < len(tokens) and tokens[pos].isdigit():
                return ("cst", int_lit(pop(), True))
            return ("neg", unary(depth + 1))
        if nxt == "(":
            pop("(")
            res = expr(depth + 1)
            pop(")")
            return res
        tok = pop()
        if tok.isdigit():
            return ("cst", int_lit(tok))
        if (not _IDENT_RE.match(tok) or tok in _LEAN_KEYWORDS
                or tok in reserved or re.match(r"\Ah\d+\Z", tok)):
            raise ParseError(f"Unsupported or reserved Lean variable: `{tok}`")
        return ("var", tok)

    out = expr()
    if pos != len(tokens):
        raise ParseError(f"Trailing token `{tokens[pos]}`")
    return out


def parse_inequalities(
    text: str, domain: str, *, reserved: frozenset[str] = frozenset()
) -> list[tuple[tuple[Any, ...], str, tuple[Any, ...]]]:
    """Parse linear relation(s) into `(lhs_ast, rel_op, rhs_ast)` tuples."""
    pos, toks = 0, []
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif m := _TOK_RE.match(text, pos):
            toks.append(m.group(1))
            pos = m.end()
        else:
            raise ParseError(f"Unexpected syntax at col {pos + 1} in `{text}`")
    rels = [i for i, t in enumerate(toks) if t in _REL_OPS]
    if len(rels) != 1:
        raise ParseError(f"Expected one comparison operator in `{text}`")
    rpos, op = rels[0], toks[rels[0]]
    lhs = _parse_expr(toks[:rpos], domain, reserved=reserved)
    rhs = _parse_expr(toks[rpos + 1 :], domain, reserved=reserved)
    _walk_ast(lhs, domain, caps=True)
    _walk_ast(rhs, domain, caps=True)
    return [(lhs, "<=", rhs), (rhs, "<=", lhs)] if op in ("=", "==") else [(lhs, op, rhs)]


def _ast_to_le(lhs: tuple[Any, ...], op: str, rhs: tuple[Any, ...]) -> tuple[Any, Any, str]:
    if op in ("<=", "<"):
        return (lhs, rhs, "≤") if op == "<=" else (("add", lhs, ("cst", 1)), rhs, "<")
    return (rhs, lhs, "≤") if op == ">=" else (("add", rhs, ("cst", 1)), lhs, "<")


def _sint(k: int, *, ascii_lean: bool = False) -> str:
    neg = "true" if k < 0 else "false"
    return f"{{ neg := {neg}, mag := {abs(k)} }}" if ascii_lean else f"⟨{neg}, {abs(k)}⟩"


def _render_pair(
    n: tuple[Any, ...], vidx: dict[str, int], domain: str,
    *, min_prec: int = 0, ascii_lean: bool = False,
) -> tuple[str, str]:
    op = n[0]
    if op == "cst":
        if domain == "nat":
            return f".cst {n[1]}", str(n[1])
        surf = f"Int.negOfNat {abs(n[1])}" if n[1] < 0 else str(n[1])
        if n[1] < 0 and min_prec >= 90:
            surf = f"({surf})"
        return f".cst {_sint(n[1], ascii_lean=ascii_lean)}", surf
    if op == "var":
        return f".var {vidx[n[1]]}", n[1]
    if op == "neg":
        sa, sp = _render_pair(n[1], vidx, domain, min_prec=100, ascii_lean=ascii_lean)
        p = f"Int.neg {sp}"
        return f".neg ({sa})", f"({p})" if min_prec >= 90 else p
    if op == "mulC":
        sa, sp = _render_pair(n[2], vidx, domain, min_prec=75, ascii_lean=ascii_lean)
        ka = str(n[1]) if domain == "nat" else _sint(n[1], ascii_lean=ascii_lean)
        kp = str(n[1]) if (domain == "nat" or n[1] >= 0) else f"Int.negOfNat {abs(n[1])}"
        p = f"{kp} * {sp}"
        return f".mulC {ka} ({sa})", f"({p})" if 70 < min_prec else p
    la, lp = _render_pair(n[1], vidx, domain, min_prec=65, ascii_lean=ascii_lean)
    ra, rp = _render_pair(n[2], vidx, domain, min_prec=66, ascii_lean=ascii_lean)
    sym, ctor = ("+", ".add") if op == "add" else ("-", ".sub")
    p = f"{lp} {sym} {rp}"
    return f"{ctor} ({la}) ({ra})", f"({p})" if 65 < min_prec else p


def _comb_rows(
    r1: tuple[tuple[tuple[int, int], ...], int], k1: int,
    r2: tuple[tuple[tuple[int, int], ...], int], k2: int,
) -> tuple[tuple[tuple[int, int], ...], int] | None:
    if k1 > _MAG_CAP_128 or k2 > _MAG_CAP_128:
        return None
    m: dict[int, int] = {}
    for row, k in ((r1, k1), (r2, k2)):
        for i, c in row[0]:
            m[i] = m.get(i, 0) + k * c
    terms = tuple(sorted((i, c) for i, c in m.items() if c))
    rhs = k1 * r1[1] + k2 * r2[1]
    if abs(rhs) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in terms):
        return None
    return terms, rhs


def _step_dict(st: tuple[Any, ...]) -> dict[str, Any]:
    return {"op": st[0], **(
        {"idx": st[1]} if st[0] == "hyp"
        else {"g": st[1], "s": st[2]} if st[0] == "divCut"
        else {"s1": st[1], "k1": st[2], "s2": st[3], "k2": st[4]}
    )}


def _rebalance_steps(
    raw: list[tuple[Any, ...]], hyp_map: dict[int, tuple[tuple[tuple[int, int], ...], int]]
) -> list[dict[str, Any]]:
    """Collapse `.comb` subtrees into balanced `O(log n)` binary reductions."""
    weights: list[dict[int, int]] = []
    for sid, st in enumerate(raw):
        if st[0] != "comb":
            weights.append({sid: 1})
            continue
        w: dict[int, int] = {}
        for ch, mult in ((st[1], st[2]), (st[3], st[4])):
            for aid, aw in weights[ch].items():
                if (nw := w.get(aid, 0) + mult * aw) > _MAG_CAP_128:
                    return [_step_dict(s) for s in raw]
                if nw:
                    w[aid] = nw
        weights.append(w)
    out_steps, out_rows, emitted = [], [], {}

    def emit(step: tuple[Any, ...], row: Any) -> int:
        out_steps.append(step)
        out_rows.append(row)
        return len(out_steps) - 1

    def mat(sid: int) -> int | None:
        if sid in emitted:
            return emitted[sid]
        st = raw[sid]
        if st[0] == "hyp":
            return emitted.setdefault(sid, emit(st, hyp_map[st[1]]))
        if st[0] == "divCut":
            if (cid := mat(st[2])) is None:
                return None
            t, r, g = *out_rows[cid], st[1]
            return emitted.setdefault(
                sid, emit(("divCut", g, cid), (tuple((i, c // g) for i, c in t if c // g), r // g))
            )
        layer = []
        for aid, w in sorted(weights[sid].items()):
            if (eid := mat(aid)) is None:
                return None
            layer.append((eid, w))
        if len(layer) == 1:
            eid, w = layer[0]
            if w == 1:
                return emitted.setdefault(sid, eid)
            layer = [(eid, w - 1), (eid, 1)]
        while len(layer) > 1:
            nxt = []
            for j in range(0, len(layer), 2):
                if j + 1 >= len(layer):
                    nxt.append(layer[j])
                else:
                    (s1, k1), (s2, k2) = layer[j], layer[j + 1]
                    if (row := _comb_rows(out_rows[s1], k1, out_rows[s2], k2)) is None:
                        return None
                    nxt.append((emit(("comb", s1, k1, s2, k2), row), 1))
            layer = nxt
        return emitted.setdefault(sid, layer[0][0])

    rid = mat(len(raw) - 1) if raw else None
    final = raw if (rid is None or out_rows[rid][0] or out_rows[rid][1] >= 0) else out_steps
    return [_step_dict(s) for s in final]


def solve_cut_refutation(
    indexed_rows: list[tuple[int, tuple[tuple[tuple[int, int], ...], int]]], max_nodes: int = 2500
) -> list[dict[str, Any]] | None:
    """Search Fourier-Motzkin + Chvatal-Gomory steps deriving `0 <= -1`."""
    nodes, best, q, hyp_map = [], {}, deque(), dict(indexed_rows)

    def push(t: tuple[tuple[int, int], ...], r: int, st: tuple[Any, ...]) -> int | None:
        if abs(r) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in t):
            return None
        if (prev := best.get(t)) is not None and prev[0] <= r:
            return None
        nodes.append((t, r, st))
        nid = len(nodes) - 1
        best[t] = (r, nid)
        q.append(nid)
        return nid

    def replay(gid: int) -> list[dict[str, Any]]:
        need, stack = set(), [gid]
        while stack:
            if (cur := stack.pop()) not in need:
                need.add(cur)
                st = nodes[cur][2]
                if st[0] != "hyp":
                    stack.extend((st[1], st[3]) if st[0] == "comb" else (st[2],))
        remap, out = {}, []
        for idx, oid in enumerate(sorted(need)):
            remap[oid], st = idx, nodes[oid][2]
            out.append(st if st[0] == "hyp" else (
                ("comb", remap[st[1]], st[2], remap[st[3]], st[4]) if st[0] == "comb"
                else ("divCut", st[1], remap[st[2]])
            ))
        return _rebalance_steps(out, hyp_map)

    for hyp_idx, (t, r) in indexed_rows:
        if (nid := push(t, r, ("hyp", hyp_idx))) is not None and not t and r < 0:
            return replay(nid)
    while q and len(nodes) < max_nodes:
        nid = q.popleft()
        terms, rhs, _ = nodes[nid]
        if terms and (g := reduce(math.gcd, (abs(c) for _, c in terms))) > 1:
            push(tuple((i, c // g) for i, c in terms), rhs // g, ("divCut", g, nid))
        tmap = dict(terms)
        for _, oid in list(best.values()):
            if oid == nid or len(nodes) >= max_nodes:
                continue
            ot, orhs, _ = nodes[oid]
            otmap = dict(ot)
            for vid, c1 in tmap.items():
                if not ((c2 := otmap.get(vid, 0)) and ((c1 > 0) != (c2 > 0))):
                    continue
                g = math.gcd(abs(c1), abs(c2))
                k1, k2 = abs(c2) // g, abs(c1) // g
                comb = _comb_rows((terms, rhs), k1, (ot, orhs), k2)
                if comb and len(comb[0]) <= max(len(terms), len(ot)) + 2:
                    if (cid := push(*comb, ("comb", nid, k1, oid, k2))) is not None:
                        if not comb[0] and comb[1] < 0:
                            return replay(cid)
                if len(nodes) >= max_nodes:
                    break
    return None


def _goal_stats(
    hyps: list[tuple[Any, ...]], gl: Any, gr: Any, domain: str
) -> tuple[list[str], int, int]:
    vset: dict[str, None] = {}
    nodes = voccs = 0
    for la, ra in [*((r[1], r[2]) for r in hyps), (gl, gr)]:
        _, ln, lv, _ = _walk_ast(la, domain, vset)
        _, rn, rv, _ = _walk_ast(ra, domain, vset)
        nodes, voccs = nodes + ln + rn, voccs + lv + rv
    return list(vset), nodes, voccs


def _prune_and_check(
    le_hyps: list[tuple[Any, ...]], gl_le: Any, gr_le: Any,
    orig_vars: list[str], steps: list[dict[str, Any]], domain: str,
) -> tuple[list[tuple[Any, ...]], list[str], dict[str, int], list[dict[str, Any]], list[int]]:
    orig_n = len(le_hyps)
    orig_neg = orig_n + (len(orig_vars) if domain == "nat" else 0)
    used = sorted({s["idx"] for s in steps if s["op"] == "hyp" and s["idx"] < orig_n})
    pruned = [le_hyps[i] for i in used]
    vars_, nodes, voccs = _goal_stats(pruned, gl_le, gr_le, domain)
    umap, vidx = {old: new for new, old in enumerate(used)}, {nm: i for i, nm in enumerate(vars_)}
    new_neg = len(pruned) + (len(vars_) if domain == "nat" else 0)
    depths: list[int] = []
    for st in steps:
        if st["op"] == "hyp":
            si = st["idx"]
            st["idx"] = (umap[si] if si < orig_n else
                         len(pruned) + vidx[orig_vars[si - orig_n]] if si < orig_neg else new_neg)
        depths.append(1 if st["op"] == "hyp" else (
            1 + depths[st["s"]] if st["op"] == "divCut"
            else 1 + max(depths[st["s1"]], depths[st["s2"]])
        ))
    mv, mh, mn, mvo, ms = _KERNEL_CAPS[domain]
    jwork = 2 * len(vars_) + 2 * len(pruned) + nodes + voccs + len(steps)
    if (len(vars_) > mv or len(pruned) > mh or nodes > mn or voccs > mvo
            or len(steps) > ms or max(depths, default=0) > _MAX_CERT_DEPTH
            or (domain == "nat" and jwork > _NAT_MAX_JOINT_WORK)):
        raise ParseError(f"Certificate exceeds Lean maxRecDepth bounds (`--domain {domain}`: "
                         f"vars {len(vars_)}/{mv}, hyps {len(pruned)}/{mh}, nodes {nodes}/{mn}).")
    return pruned, vars_, vidx, steps, sorted({le_hyps[i][0] for i in used})


def generate_certificate(
    domain: str, hyp_strings: list[str], goal_string: str,
    thm_name: str = "linear_bound", max_nodes: int = 2500, *, ascii_lean: bool = False,
) -> dict[str, Any]:
    """Synthesize a `CutStep` certificate and `Anneal.LinearArith` snippet."""
    if max_nodes < 1:
        raise ParseError("`--max-nodes` must be >= 1.")
    if not _IDENT_RE.match(thm_name) or thm_name in _LEAN_KEYWORDS:
        raise ParseError(f"Unsupported or reserved Lean name: `{thm_name}`")
    reserved = frozenset({thm_name, f"{thm_name}_goal", f"{thm_name}_cert"})
    parsed_hyps = [(i, iq) for i, hs in enumerate(hyp_strings)
                   for iq in parse_inequalities(hs, domain, reserved=reserved)]
    goals = parse_inequalities(goal_string, domain, reserved=reserved)
    if len(goals) != 1:
        raise ParseError("`--goal` must be a single inequality (`<=`, `<`, `>=`, or `>`).")
    le_hyps = [(i, *_ast_to_le(l, op, r), l, op, r) for i, (l, op, r) in parsed_hyps]
    gl_le, gr_le, g_sym, gl_orig, g_op, gr_orig = (*_ast_to_le(*goals[0]), *goals[0])
    vars_, _, _ = _goal_stats(le_hyps, gl_le, gr_le, domain)
    vidx = {nm: i for i, nm in enumerate(vars_)}

    def to_sparse(lhs: Any, rhs: Any) -> tuple[tuple[tuple[int, int], ...], int]:
        lc, lk = _eval_linear(lhs)
        rc, rk = _eval_linear(rhs)
        m = {vidx[nm]: lc.get(nm, 0) - rc.get(nm, 0) for nm in (*lc, *rc)}
        terms, delta = tuple(sorted((i, c) for i, c in m.items() if c)), rk - lk
        if abs(delta) > _MAG_CAP_128 or any(abs(c) > _MAG_CAP_128 for _, c in terms):
            raise ParseError("Normalized row exceeds `magCap128` (`2^128`).")
        return terms, delta

    hyp_rows = [to_sparse(la, ra) for _, la, ra, *_ in le_hyps]
    neg_row = to_sparse(("add", gr_le, ("cst", 1)), gl_le)
    neg_idx = len(le_hyps) + (len(vars_) if domain == "nat" else 0)
    steps = solve_cut_refutation([*enumerate(hyp_rows), (neg_idx, neg_row)], max_nodes)
    if steps is None and domain == "nat" and vars_:
        nn = [to_sparse(("cst", 0), ("var", nm)) for nm in vars_]
        steps = solve_cut_refutation(list(enumerate([*hyp_rows, *nn, neg_row])), max_nodes)
    if steps is None:
        return {"solved": False, "domain": domain, "variables": vars_,
                "error": f"No Farkas/Chvatal-Gomory refutation found within max_nodes={max_nodes}."}
    le_hyps, vars_, vidx, steps, kept = _prune_and_check(
        le_hyps, gl_le, gr_le, vars_, steps, domain
    )
    rp = lambda node: _render_pair(node, vidx, domain, ascii_lean=ascii_lean)  # noqa: E731
    pair = lambda a, b: f"{{ lhs := {a}, rhs := {b} }}" if ascii_lean else f"⟨{a}, {b}⟩"

    def prop_rel(ol: Any, op: str, or_: Any, sym: str) -> str:
        ln, rn = (or_, ol) if op in (">=", ">") else (ol, or_)
        osym = "<=" if (ascii_lean and sym == "≤") else sym
        if domain == "int" and not _walk_ast(ln, domain)[3] and not _walk_ast(rn, domain)[3]:
            return f"({rp(ln)[1]} : Int) {osym} ({rp(rn)[1]} : Int)"
        return f"{rp(ln)[1]} {osym} {rp(rn)[1]}"

    hyp_lits = ", ".join(pair(rp(la)[0], rp(ra)[0]) for _, la, ra, *_ in le_hyps)
    step_lits = ", ".join(
        f".hyp {s['idx']}" if s["op"] == "hyp"
        else f".comb {s['s1']} {s['k1']} {s['s2']} {s['k2']}" if s["op"] == "comb"
        else f".divCut {s['g']} {s['s']}" for s in steps
    )
    gty, thm, vty = (("NatCutGoal", "checkNatCutGoal_sound", "Nat") if domain == "nat"
                     else ("IntCutGoal", "checkIntCutGoal_sound", "Int"))
    h_bind = "".join(f" (h{i} : {prop_rel(lo, op, ro, sym)})"
                     for i, (_, _, _, sym, lo, op, ro) in enumerate(le_hyps))
    p_args = " ".join(f"h{i}" for i in range(len(le_hyps)))
    v_bind = f"({' '.join(vars_)} : {vty})" if vars_ else ""
    tail = f"[{', '.join(vars_)}]{(' ' + p_args) if p_args else ''}"
    snippet = (
        f"import Anneal.LinearArith\nopen Anneal.LinearArith\n\n"
        f"private def {thm_name}_goal : {gty} :=\n"
        f"  {{ hyps := [{hyp_lits}],\n    concl := {pair(rp(gl_le)[0], rp(gr_le)[0])} }}\n\n"
        f"private def {thm_name}_cert : List CutStep :=\n  [{step_lits}]\n\n"
        f"private theorem {thm_name} {v_bind}{h_bind} :\n"
        f"    {prop_rel(gl_orig, g_op, gr_orig, g_sym)} :=\n"
        f"  {thm} {thm_name}_goal {thm_name}_cert rfl {tail}"
    )
    return {"solved": True, "domain": domain, "variables": vars_,
            "kept_hyp_indices": kept, "steps": steps, "lean_snippet": snippet}


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    p.add_argument("--domain", choices=("nat", "int"), default="nat")
    p.add_argument("--hyp", action="append", default=[], dest="hyps")
    p.add_argument("--goal", required=True)
    p.add_argument("--name", default="linear_bound")
    p.add_argument("--max-nodes", type=int, default=2500)
    p.add_argument("--json", action="store_true")
    raw = sys.argv[1:] if argv is None else list(argv)
    stops = {"-h", "--help", "--domain", "--hyp", "--goal", "--name", "--max-nodes", "--json", "--"}
    norm, i = [], 0
    while i < len(raw):
        tok, nxt = raw[i], (raw[i + 1] if i + 1 < len(raw) else "")
        if tok == "--":
            norm.extend(raw[i:])
            break
        pair_neg = (tok in ("--hyp", "--goal") and nxt.startswith("-")
                    and not nxt.startswith("--") and nxt not in stops)
        norm.append(f"{tok}={nxt}" if pair_neg else tok)
        i += 2 if pair_neg else 1
    ns, utf8_out = p.parse_args(norm), True
    try:
        "⟨≤".encode(getattr(sys.stdout, "encoding", None) or "utf-8")
    except (UnicodeEncodeError, LookupError):
        utf8_out = False

    def fail(rc: int, msg: Any) -> int:
        err = str(msg).encode("utf-8", "replace").decode("utf-8")
        out = json.dumps({"solved": False, "error": err}, indent=2, ensure_ascii=not utf8_out)
        print(out if ns.json else f"[ERROR] {err}", file=(sys.stdout if ns.json else sys.stderr))
        return rc

    try:
        for tok in raw:
            tok.encode("utf-8", errors="strict")
        res = generate_certificate(
            ns.domain, ns.hyps, ns.goal, ns.name,
            max_nodes=ns.max_nodes, ascii_lean=(not ns.json and not utf8_out),
        )
    except Exception as exc:
        return fail(2, exc)
    if ns.json:
        print(json.dumps(res, indent=2, ensure_ascii=not utf8_out))
        return 0 if res["solved"] else 1
    return (print(res["lean_snippet"]) or 0) if res["solved"] else fail(1, res["error"])


if __name__ == "__main__":
    sys.exit(main())
