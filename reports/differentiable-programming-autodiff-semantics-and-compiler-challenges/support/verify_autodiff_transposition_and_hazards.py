#!/usr/bin/env python3
"""Standalone verification suite for AD semantics, compiler transposition, and hazards.

Demonstrates and verifies four core automatic differentiation properties using
only the Python 3.10+ standard library:

  (a) Dex / Radul-et-al. 3-pass reverse-mode decomposition:
      Primal + Linearize (JVP + residual unzipping) + Structural Linear Transpose (VJP),
      including pointful indexed loops (`for_index`) whose fan-out array reads transpose
      into associative cotangent accumulation with zero dynamic tape. Verified to
      machine precision against exact dual numbers, analytical gradients, the adjoint
      inner-product identity <Jv, u> == <v, J^T u>, and central finite differences.

  (b) Perturbation confusion (Siskind & Pearlmutter 2005/2008; Manzyuk et al. 2019):
      Concrete failure of naive untagged dual numbers on nested differentiation
      d/dx [x * d/dy (x + y)|_{y=1}] and d/dx [x * d/dy (x * y)|_{y=1}], fix via
      strictly ordered lexical tag gensyms, plus the higher-order curried escaping-tag
      failure when a tag is minted at operator creation rather than per evaluation.

  (c) Non-differentiable branch traps, Clarke subdifferential chain-rule failure,
      and IEEE-754 0.0 * inf = NaN branch-masking hazards (Lee et al. 2020;
      Bolte & Pauwels 2021; Mazza & Pagani 2021; Enzyme strongZero / JAX double-where).

  (d) Griewank & Walther (2000) Algorithm 799 (Revolve) binomial checkpointing:
      Verifies beta(c, r) = C(c + r, c), exact agreement between dynamic programming
      p(l, c), closed-form r*l - C(c + r, c + 1), and a live Revolve state-machine
      adjoint execution on a 100-step nonlinear recurrence.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Callable


# =============================================================================
# Part (a): Dex-Style 3-Pass AD (Primal + Linearize + Structural Transpose)
# =============================================================================
#
# A tiny typed SSA/ANF array IR modeled after Dex's SimpIR (Linearize.hs /
# Transpose.hs) and Radul et al. (POPL 2023):
#   - Scalar operations: add, sub, mul, div, neg, sin, cos, exp
#   - Indexed array loops: ForLoop(var, length, index_exprs, body, out_var)
#     where reads from input arrays via `arr[idx_fn(i)]` transpose into
#     associative cotangent accumulation `ct_arr[idx_fn(i)] += ct` in a
#     reversed `ForLoop(Rev, ...)` with ZERO dynamic tape.


@dataclass(frozen=True)
class ScalarOp:
    out: str
    op: str
    args: tuple[str, ...]


@dataclass(frozen=True)
class ArrayRead:
    out: str
    arr: str
    idx_fn: Callable[[int], int]


@dataclass(frozen=True)
class SumFor:
    """Computes out = sum_{i=0}^{length-1} body(i), where body produces a scalar."""
    out: str
    length: int
    body: tuple[Any, ...]
    body_out: str


@dataclass(frozen=True)
class LinOp:
    """Explicitly linear tangent operation (all primal/residual factors in `consts`)."""
    out: str
    kind: str  # "add", "sub", "neg", "scale", "read_idx", "zero"
    lin_args: tuple[str, ...]
    const_keys: tuple[str, ...] = ()
    idx_fn: Callable[[int], int] | None = None


@dataclass(frozen=True)
class LinSumFor:
    out: str
    length: int
    body: tuple[LinOp, ...]
    body_out: str
    res_prefix: str


def eval_primal(
    ops: tuple[Any, ...], env: dict[str, Any], out_var: str
) -> tuple[float, dict[str, Any]]:
    local = dict(env)
    for stmt in ops:
        if isinstance(stmt, ScalarOp):
            vals = [local[a] for a in stmt.args]
            if stmt.op == "add":
                local[stmt.out] = vals[0] + vals[1]
            elif stmt.op == "sub":
                local[stmt.out] = vals[0] - vals[1]
            elif stmt.op == "mul":
                local[stmt.out] = vals[0] * vals[1]
            elif stmt.op == "div":
                local[stmt.out] = vals[0] / vals[1]
            elif stmt.op == "neg":
                local[stmt.out] = -vals[0]
            elif stmt.op == "sin":
                local[stmt.out] = math.sin(vals[0])
            elif stmt.op == "cos":
                local[stmt.out] = math.cos(vals[0])
            elif stmt.op == "exp":
                local[stmt.out] = math.exp(vals[0])
            else:
                raise ValueError(f"unknown op {stmt.op}")
        elif isinstance(stmt, SumFor):
            acc = 0.0
            for i in range(stmt.length):
                sub = dict(local)
                for bstmt in stmt.body:
                    if isinstance(bstmt, ArrayRead):
                        sub[bstmt.out] = sub[bstmt.arr][bstmt.idx_fn(i)]
                    elif isinstance(bstmt, ScalarOp):
                        vals = [sub[a] for a in bstmt.args]
                        if bstmt.op == "add":
                            sub[bstmt.out] = vals[0] + vals[1]
                        elif bstmt.op == "sub":
                            sub[bstmt.out] = vals[0] - vals[1]
                        elif bstmt.op == "mul":
                            sub[bstmt.out] = vals[0] * vals[1]
                        elif bstmt.op == "div":
                            sub[bstmt.out] = vals[0] / vals[1]
                        elif bstmt.op == "neg":
                            sub[bstmt.out] = -vals[0]
                        elif bstmt.op == "sin":
                            sub[bstmt.out] = math.sin(vals[0])
                        elif bstmt.op == "cos":
                            sub[bstmt.out] = math.cos(vals[0])
                        elif bstmt.op == "exp":
                            sub[bstmt.out] = math.exp(vals[0])
                        else:
                            raise ValueError(f"unknown op {bstmt.op}")
                    else:
                        raise TypeError(f"unsupported loop stmt {bstmt}")
                acc += sub[stmt.body_out]
            local[stmt.out] = acc
        else:
            raise TypeError(f"unsupported stmt {stmt}")
    return local[out_var], local


def _linearize_scalar_op(
    stmt: ScalarOp,
    primal_env: dict[str, Any],
    residuals: dict[str, Any],
    res_prefix: str,
    idx_suffix: str,
) -> list[LinOp]:
    """Emit linear tangent ops for a scalar op, unzipping nonlinear residuals."""
    a = stmt.args
    if stmt.op == "add":
        primal_env[stmt.out] = primal_env[a[0]] + primal_env[a[1]]
        return [LinOp(stmt.out, "add", (a[0], a[1]))]
    if stmt.op == "sub":
        primal_env[stmt.out] = primal_env[a[0]] - primal_env[a[1]]
        return [LinOp(stmt.out, "sub", (a[0], a[1]))]
    if stmt.op == "neg":
        primal_env[stmt.out] = -primal_env[a[0]]
        return [LinOp(stmt.out, "neg", (a[0],))]
    if stmt.op == "mul":
        x_val, y_val = primal_env[a[0]], primal_env[a[1]]
        primal_env[stmt.out] = x_val * y_val
        rx = f"{res_prefix}{stmt.out}_l{idx_suffix}"
        ry = f"{res_prefix}{stmt.out}_r{idx_suffix}"
        residuals[rx] = x_val
        residuals[ry] = y_val
        # Canonicalized linear-on-LHS scaling: d(x*y) = (dx * y_res) + (dy * x_res)
        t1 = f"{stmt.out}_m1"
        t2 = f"{stmt.out}_m2"
        return [
            LinOp(t1, "scale", (a[0],), (ry,)),
            LinOp(t2, "scale", (a[1],), (rx,)),
            LinOp(stmt.out, "add", (t1, t2)),
        ]
    if stmt.op == "div":
        x_val, y_val = primal_env[a[0]], primal_env[a[1]]
        primal_env[stmt.out] = x_val / y_val
        r_inv = f"{res_prefix}{stmt.out}_invy{idx_suffix}"
        r_neg = f"{res_prefix}{stmt.out}_negxy2{idx_suffix}"
        residuals[r_inv] = 1.0 / y_val
        residuals[r_neg] = -x_val / (y_val * y_val)
        t1 = f"{stmt.out}_d1"
        t2 = f"{stmt.out}_d2"
        return [
            LinOp(t1, "scale", (a[0],), (r_inv,)),
            LinOp(t2, "scale", (a[1],), (r_neg,)),
            LinOp(stmt.out, "add", (t1, t2)),
        ]
    if stmt.op == "sin":
        x_val = primal_env[a[0]]
        primal_env[stmt.out] = math.sin(x_val)
        rc = f"{res_prefix}{stmt.out}_cos{idx_suffix}"
        residuals[rc] = math.cos(x_val)
        return [LinOp(stmt.out, "scale", (a[0],), (rc,))]
    if stmt.op == "cos":
        x_val = primal_env[a[0]]
        primal_env[stmt.out] = math.cos(x_val)
        rs = f"{res_prefix}{stmt.out}_nsin{idx_suffix}"
        residuals[rs] = -math.sin(x_val)
        return [LinOp(stmt.out, "scale", (a[0],), (rs,))]
    if stmt.op == "exp":
        x_val = primal_env[a[0]]
        ex = math.exp(x_val)
        primal_env[stmt.out] = ex
        re = f"{res_prefix}{stmt.out}_exp{idx_suffix}"
        residuals[re] = ex
        return [LinOp(stmt.out, "scale", (a[0],), (re,))]
    raise ValueError(f"unknown op {stmt.op}")


def linearize(
    ops: tuple[Any, ...], primal_env: dict[str, Any], out_var: str
) -> tuple[float, dict[str, Any], tuple[Any, ...]]:
    """Pass 1+2: Evaluate primal, unzip minimal nonlinear residuals, emit linear IR."""
    local = dict(primal_env)
    residuals: dict[str, Any] = {}
    lin_ir: list[Any] = []
    for stmt in ops:
        if isinstance(stmt, ScalarOp):
            lin_ir.extend(_linearize_scalar_op(stmt, local, residuals, "", ""))
        elif isinstance(stmt, SumFor):
            # Each iteration records only its own unzipped nonlinear scalar residuals
            # indexed by i, matching Dex's `ReconWithData` table of residuals.
            res_prefix = f"{stmt.out}__"
            acc = 0.0
            loop_lin_template: list[LinOp] | None = None
            for i in range(stmt.length):
                sub = dict(local)
                iter_lin: list[LinOp] = []
                for bstmt in stmt.body:
                    if isinstance(bstmt, ArrayRead):
                        sub[bstmt.out] = sub[bstmt.arr][bstmt.idx_fn(i)]
                        iter_lin.append(
                            LinOp(bstmt.out, "read_idx", (bstmt.arr,), idx_fn=bstmt.idx_fn)
                        )
                    elif isinstance(bstmt, ScalarOp):
                        iter_lin.extend(
                            _linearize_scalar_op(bstmt, sub, residuals, res_prefix, f"@{i}")
                        )
                    else:
                        raise TypeError(f"unsupported loop stmt {bstmt}")
                acc += sub[stmt.body_out]
                if loop_lin_template is None:
                    # Strip `@0` from const keys to obtain the index-parametric template
                    loop_lin_template = [
                        LinOp(
                            lo.out,
                            lo.kind,
                            lo.lin_args,
                            tuple(k.rsplit("@", 1)[0] for k in lo.const_keys),
                            lo.idx_fn,
                        )
                        for lo in iter_lin
                    ]
            local[stmt.out] = acc
            assert loop_lin_template is not None
            lin_ir.append(
                LinSumFor(
                    stmt.out,
                    stmt.length,
                    tuple(loop_lin_template),
                    stmt.body_out,
                    res_prefix,
                )
            )
        else:
            raise TypeError(f"unsupported stmt {stmt}")
    return local[out_var], residuals, tuple(lin_ir)


def eval_linear_jvp(
    lin_ir: tuple[Any, ...],
    residuals: dict[str, Any],
    tangents: dict[str, Any],
    out_var: str,
) -> float:
    """Evaluate the unzipped linear tangent program (forward-mode JVP)."""
    t_env = dict(tangents)
    for stmt in lin_ir:
        if isinstance(stmt, LinOp):
            if stmt.kind == "add":
                t_env[stmt.out] = t_env[stmt.lin_args[0]] + t_env[stmt.lin_args[1]]
            elif stmt.kind == "sub":
                t_env[stmt.out] = t_env[stmt.lin_args[0]] - t_env[stmt.lin_args[1]]
            elif stmt.kind == "neg":
                t_env[stmt.out] = -t_env[stmt.lin_args[0]]
            elif stmt.kind == "scale":
                t_env[stmt.out] = t_env[stmt.lin_args[0]] * residuals[stmt.const_keys[0]]
            else:
                raise ValueError(f"unexpected top-level linear op {stmt}")
        elif isinstance(stmt, LinSumFor):
            acc = 0.0
            for i in range(stmt.length):
                sub = dict(t_env)
                for lo in stmt.body:
                    if lo.kind == "read_idx":
                        assert lo.idx_fn is not None
                        sub[lo.out] = sub[lo.lin_args[0]][lo.idx_fn(i)]
                    elif lo.kind == "add":
                        sub[lo.out] = sub[lo.lin_args[0]] + sub[lo.lin_args[1]]
                    elif lo.kind == "sub":
                        sub[lo.out] = sub[lo.lin_args[0]] - sub[lo.lin_args[1]]
                    elif lo.kind == "neg":
                        sub[lo.out] = -sub[lo.lin_args[0]]
                    elif lo.kind == "scale":
                        sub[lo.out] = (
                            sub[lo.lin_args[0]] * residuals[f"{lo.const_keys[0]}@{i}"]
                        )
                    else:
                        raise ValueError(f"unexpected loop linear op {lo}")
                acc += sub[stmt.body_out]
            t_env[stmt.out] = acc
        else:
            raise TypeError(f"unexpected stmt {stmt}")
    return t_env[out_var]


@dataclass(frozen=True)
class TransposedOp:
    """Cotangent accumulation step synthesized by structural transposition."""
    kind: str  # "accum_scalar", "accum_scale", "accum_neg", "accum_idx"
    src_ct: str
    dst_var: str
    const_key: str | None = None
    idx_fn: Callable[[int], int] | None = None


@dataclass(frozen=True)
class TransposedForRev:
    """Reversed index-set loop (`For Rev` in Dex Transpose.hs) with zero tape."""
    src_ct: str
    length: int
    body_out: str
    body_rev: tuple[TransposedOp, ...]


def structural_transpose(lin_ir: tuple[Any, ...]) -> tuple[Any, ...]:
    """Pass 3: Structurally transpose linear IR into reverse-mode VJP IR.

    Mirrors `google-research/dex-lang` `src/lib/Transpose.hs`:
      - Reverses statement order (`transposeWithDecls`).
      - Maps fan-out reads (`read_idx`) into associative accumulator extends
        (`MExtend` / `+=`).
      - Flips `For Fwd` into `For Rev` without allocating a dynamic tape.
    """
    def transpose_linop(lo: LinOp) -> list[TransposedOp]:
        if lo.kind == "add":
            return [
                TransposedOp("accum_scalar", lo.out, lo.lin_args[0]),
                TransposedOp("accum_scalar", lo.out, lo.lin_args[1]),
            ]
        if lo.kind == "sub":
            return [
                TransposedOp("accum_scalar", lo.out, lo.lin_args[0]),
                TransposedOp("accum_neg", lo.out, lo.lin_args[1]),
            ]
        if lo.kind == "neg":
            return [TransposedOp("accum_neg", lo.out, lo.lin_args[0])]
        if lo.kind == "scale":
            return [
                TransposedOp("accum_scale", lo.out, lo.lin_args[0], const_key=lo.const_keys[0])
            ]
        if lo.kind == "read_idx":
            return [
                TransposedOp("accum_idx", lo.out, lo.lin_args[0], idx_fn=lo.idx_fn)
            ]
        raise ValueError(f"cannot transpose {lo}")

    transposed: list[Any] = []
    for stmt in reversed(lin_ir):
        if isinstance(stmt, LinOp):
            transposed.extend(transpose_linop(stmt))
        elif isinstance(stmt, LinSumFor):
            body_rev: list[TransposedOp] = []
            for lo in reversed(stmt.body):
                body_rev.extend(transpose_linop(lo))
            transposed.append(
                TransposedForRev(stmt.out, stmt.length, stmt.body_out, tuple(body_rev))
            )
        else:
            raise TypeError(f"cannot transpose {stmt}")
    return tuple(transposed)


def eval_transposed_vjp(
    vjp_ir: tuple[Any, ...],
    residuals: dict[str, Any],
    input_shapes: dict[str, int | None],  # None => scalar, int => array length
    out_var: str,
    out_cotangent: float,
) -> dict[str, Any]:
    """Execute transposed VJP IR using zero-initialized monoidal accumulators."""
    ct_env: dict[str, Any] = {
        k: (0.0 if sz is None else [0.0] * sz) for k, sz in input_shapes.items()
    }
    ct_env[out_var] = out_cotangent

    for stmt in vjp_ir:
        if isinstance(stmt, TransposedOp):
            src = ct_env.get(stmt.src_ct, 0.0)
            if stmt.kind == "accum_scalar":
                ct_env[stmt.dst_var] = ct_env.get(stmt.dst_var, 0.0) + src
            elif stmt.kind == "accum_neg":
                ct_env[stmt.dst_var] = ct_env.get(stmt.dst_var, 0.0) - src
            elif stmt.kind == "accum_scale":
                assert stmt.const_key is not None
                ct_env[stmt.dst_var] = (
                    ct_env.get(stmt.dst_var, 0.0) + src * residuals[stmt.const_key]
                )
            else:
                raise ValueError(f"unexpected top-level op {stmt}")
        elif isinstance(stmt, TransposedForRev):
            loop_ct = ct_env.get(stmt.src_ct, 0.0)
            # Reversed traversal (`For Rev`) over the static index set
            for i in range(stmt.length - 1, -1, -1):
                local_ct: dict[str, float] = {stmt.body_out: loop_ct}
                for to in stmt.body_rev:
                    src = local_ct.get(to.src_ct, 0.0)
                    if to.kind == "accum_scalar":
                        local_ct[to.dst_var] = local_ct.get(to.dst_var, 0.0) + src
                    elif to.kind == "accum_neg":
                        local_ct[to.dst_var] = local_ct.get(to.dst_var, 0.0) - src
                    elif to.kind == "accum_scale":
                        assert to.const_key is not None
                        val = src * residuals[f"{to.const_key}@{i}"]
                        if to.dst_var in input_shapes and input_shapes[to.dst_var] is None:
                            ct_env[to.dst_var] += val
                        else:
                            local_ct[to.dst_var] = local_ct.get(to.dst_var, 0.0) + val
                    elif to.kind == "accum_idx":
                        assert to.idx_fn is not None
                        ct_env[to.dst_var][to.idx_fn(i)] += src
                    else:
                        raise ValueError(f"unexpected loop op {to}")
        else:
            raise TypeError(f"unexpected vjp stmt {stmt}")
    return {k: ct_env[k] for k in input_shapes}


def verify_part_a() -> None:
    # 1. Nonlinear scalar program: f(x, y) = sin(x * y) + exp(x / (1 + y*y))
    scalar_prog = (
        ScalarOp("xy", "mul", ("x", "y")),
        ScalarOp("s1", "sin", ("xy",)),
        ScalarOp("y2", "mul", ("y", "y")),
        ScalarOp("denom", "add", ("one", "y2")),
        ScalarOp("q", "div", ("x", "denom")),
        ScalarOp("e1", "exp", ("q",)),
        ScalarOp("out", "add", ("s1", "e1")),
    )
    x0, y0 = 1.3, -0.7
    p_env = {"x": x0, "y": y0, "one": 1.0}
    primal_val, residuals, lin_ir = linearize(scalar_prog, p_env, "out")
    vjp_ir = structural_transpose(lin_ir)
    grads = eval_transposed_vjp(
        vjp_ir, residuals, {"x": None, "y": None, "one": None}, "out", 1.0
    )

    # Exact analytical derivatives
    d = 1.0 + y0 * y0
    eq = math.exp(x0 / d)
    exact_dx = math.cos(x0 * y0) * y0 + eq / d
    exact_dy = math.cos(x0 * y0) * x0 + eq * (-2.0 * x0 * y0 / (d * d))

    # JVP directional derivatives along basis vectors e_x, e_y
    jvp_dx = eval_linear_jvp(lin_ir, residuals, {"x": 1.0, "y": 0.0, "one": 0.0}, "out")
    jvp_dy = eval_linear_jvp(lin_ir, residuals, {"x": 0.0, "y": 1.0, "one": 0.0}, "out")

    # Central finite differences
    h = 1e-6
    fd_dx = (
        eval_primal(scalar_prog, {"x": x0 + h, "y": y0, "one": 1.0}, "out")[0]
        - eval_primal(scalar_prog, {"x": x0 - h, "y": y0, "one": 1.0}, "out")[0]
    ) / (2 * h)
    fd_dy = (
        eval_primal(scalar_prog, {"x": x0, "y": y0 + h, "one": 1.0}, "out")[0]
        - eval_primal(scalar_prog, {"x": x0, "y": y0 - h, "one": 1.0}, "out")[0]
    ) / (2 * h)

    assert abs(grads["x"] - exact_dx) < 1e-13
    assert abs(grads["y"] - exact_dy) < 1e-13
    assert abs(jvp_dx - exact_dx) < 1e-13
    assert abs(jvp_dy - exact_dy) < 1e-13
    assert abs(grads["x"] - fd_dx) < 1e-7
    assert abs(grads["y"] - fd_dy) < 1e-7

    # 2. Dex-style pointful indexed array loop with fan-out gather reads:
    #    g(a, w) = sum_{i=0}^{7} (cos(a[i] * w[i % 3]) + a[i] * a[i] * w[(i + 1) % 3])
    # Multiple loop iterations read the same w[j]; transposition turns gather
    # reads into associative scatter-add cotangent accumulation without any tape.
    N, K = 8, 3
    arr_prog = (
        SumFor(
            out="out",
            length=N,
            body=(
                ArrayRead("ai", "a", lambda i: i),
                ArrayRead("w1", "w", lambda i: i % K),
                ArrayRead("w2", "w", lambda i: (i + 1) % K),
                ScalarOp("p1", "mul", ("ai", "w1")),
                ScalarOp("c1", "cos", ("p1",)),
                ScalarOp("a2", "mul", ("ai", "ai")),
                ScalarOp("p2", "mul", ("a2", "w2")),
                ScalarOp("term", "add", ("c1", "p2")),
            ),
            body_out="term",
        ),
    )
    a0 = [0.2 * (i + 1) for i in range(N)]
    w0 = [0.5, -0.8, 1.1]
    primal_g, res_g, lin_g = linearize(arr_prog, {"a": a0, "w": w0}, "out")
    vjp_g = structural_transpose(lin_g)
    cot_u = 2.75
    vjp_grads = eval_transposed_vjp(vjp_g, res_g, {"a": N, "w": K}, "out", cot_u)

    # Check adjoint identity <J v, u> == <v, J^T u> for an arbitrary tangent vector v
    va = [(-1.0) ** i * (0.3 + 0.1 * i) for i in range(N)]
    vw = [0.7, -0.4, 0.9]
    jv = eval_linear_jvp(lin_g, res_g, {"a": va, "w": vw}, "out")
    lhs = jv * cot_u
    rhs = sum(x * g for x, g in zip(va, vjp_grads["a"])) + sum(
        x * g for x, g in zip(vw, vjp_grads["w"])
    )
    assert abs(lhs - rhs) < 1e-12, f"adjoint mismatch: {lhs} vs {rhs}"

    # Verify every component of d(g)/d(a_i) and d(g)/d(w_j) against central FD
    vjp_unit = eval_transposed_vjp(vjp_g, res_g, {"a": N, "w": K}, "out", 1.0)
    max_fd_err = 0.0
    for j in range(K):
        wp = list(w0)
        wm = list(w0)
        wp[j] += h
        wm[j] -= h
        fd_wj = (
            eval_primal(arr_prog, {"a": a0, "w": wp}, "out")[0]
            - eval_primal(arr_prog, {"a": a0, "w": wm}, "out")[0]
        ) / (2 * h)
        max_fd_err = max(max_fd_err, abs(vjp_unit["w"][j] - fd_wj))
    for i in range(N):
        ap = list(a0)
        am = list(a0)
        ap[i] += h
        am[i] -= h
        fd_ai = (
            eval_primal(arr_prog, {"a": ap, "w": w0}, "out")[0]
            - eval_primal(arr_prog, {"a": am, "w": w0}, "out")[0]
        ) / (2 * h)
        max_fd_err = max(max_fd_err, abs(vjp_unit["a"][i] - fd_ai))
    assert max_fd_err < 1e-7, f"FD error too large: {max_fd_err}"

    print(
        f"[PASS] (a) Dex 3-pass AD: primal={primal_val:.6f}, "
        f"|JVP-exact|={max(abs(jvp_dx-exact_dx), abs(jvp_dy-exact_dy)):.2e}, "
        f"|<Jv,u>-<v,J^Tu>|={abs(lhs-rhs):.2e}, max_array_FD_err={max_fd_err:.2e}"
    )


# =============================================================================
# Part (b): Perturbation Confusion (Untagged vs Tagged vs Higher-Order Escaping)
# =============================================================================


class UntaggedDual:
    """Naive forward-mode dual number without perturbation tags."""

    __slots__ = ("val", "dot")

    def __init__(self, val: float, dot: float = 0.0):
        self.val = float(val)
        self.dot = float(dot)

    def __add__(self, other: Any) -> UntaggedDual:
        o = other if isinstance(other, UntaggedDual) else UntaggedDual(other, 0.0)
        return UntaggedDual(self.val + o.val, self.dot + o.dot)

    __radd__ = __add__

    def __mul__(self, other: Any) -> UntaggedDual:
        o = other if isinstance(other, UntaggedDual) else UntaggedDual(other, 0.0)
        return UntaggedDual(self.val * o.val, self.dot * o.val + self.val * o.dot)

    __rmul__ = __mul__


def diff_untagged(f: Callable[[Any], Any], x: Any) -> float:
    res = f(UntaggedDual(x.val if isinstance(x, UntaggedDual) else x, 1.0))
    return res.dot if isinstance(res, UntaggedDual) else 0.0


_TAG_COUNTER = 0


def _fresh_tag() -> int:
    global _TAG_COUNTER
    _TAG_COUNTER += 1
    return _TAG_COUNTER


class TaggedDual:
    """Lexically tagged dual number ordered by strictly monotonic tag ID.

    Ordering invariant: when combining TaggedDual(t1, p1, d1) and TaggedDual(t2, p2, d2)
    with t1 < t2 (outer tag t1, inner tag t2), the outer dual is lifted as a constant
    with respect to the inner tag t2: Dual(t2, outer, 0). This mirrors Siskind &
    Pearlmutter (2008) tag ordering and JAX's TraceTag separation.
    """

    __slots__ = ("tag", "val", "dot")

    def __init__(self, tag: int, val: Any, dot: Any):
        self.tag = tag
        self.val = val
        self.dot = dot

    def __add__(self, other: Any) -> Any:
        if isinstance(other, TaggedDual):
            if self.tag == other.tag:
                return TaggedDual(self.tag, self.val + other.val, self.dot + other.dot)
            if self.tag < other.tag:
                return TaggedDual(other.tag, self + other.val, other.dot)
            return TaggedDual(self.tag, self.val + other, self.dot)
        return TaggedDual(self.tag, self.val + other, self.dot)

    __radd__ = __add__

    def __mul__(self, other: Any) -> Any:
        if isinstance(other, TaggedDual):
            if self.tag == other.tag:
                return TaggedDual(
                    self.tag,
                    self.val * other.val,
                    self.dot * other.val + self.val * other.dot,
                )
            if self.tag < other.tag:
                return TaggedDual(other.tag, self * other.val, self * other.dot)
            return TaggedDual(self.tag, self.val * other, self.dot * other)
        return TaggedDual(self.tag, self.val * other, self.dot * other)

    __rmul__ = __mul__


def _extract_tangent(val: Any, tag: int) -> Any:
    if isinstance(val, TaggedDual):
        if val.tag == tag:
            return val.dot
        if val.tag > tag:
            return TaggedDual(
                val.tag, _extract_tangent(val.val, tag), _extract_tangent(val.dot, tag)
            )
    return 0.0


def diff_tagged(f: Callable[[Any], Any], x: Any) -> Any:
    tag = _fresh_tag()
    out = f(TaggedDual(tag, x, 1.0))
    if callable(out):
        return lambda *args: _extract_tangent(out(*args), tag)
    return _extract_tangent(out, tag)


_DEPTH = 0


def diff_dynamic_depth_bug(f: Callable[[Any], Any], x: Any) -> Any:
    """Flawed dynamic-depth tagging (recycles tags after escaping closures return)."""
    global _DEPTH
    _DEPTH += 1
    tag = _DEPTH
    try:
        out = f(TaggedDual(tag, x, 1.0))
        if callable(out):
            # Closure escapes the dynamic extent of diff_dynamic_depth_bug;
            # once finally decrements _DEPTH, a later call reuses the same tag!
            return lambda *args: _extract_tangent(out(*args), tag)
        return _extract_tangent(out, tag)
    finally:
        _DEPTH -= 1


def verify_part_b() -> None:
    # Siskind & Pearlmutter (2005/2008) canonical example:
    #   g1(x) = x * (d/dy (x + y)|_{y=1}) = x * 1 = x, so g1'(x) == 1 for all x.
    # With naive untagged dual numbers:
    #   inner (Dual(x, 1) + Dual(1, 1)).dot == 2 (confuses dx=1 with dy=1),
    #   so outer computes Dual(x, 1) * 2 = Dual(2x, 2): wrong primal 2x, wrong deriv 2!
    x_test = 3.5
    bad_g1_inner_val = (UntaggedDual(x_test, 1.0) + UntaggedDual(1.0, 1.0)).dot
    bad_g1_primal = (UntaggedDual(x_test, 1.0) * bad_g1_inner_val).val
    bad_g1_deriv = diff_untagged(lambda x: x * diff_untagged(lambda y: x + y, 1.0), x_test)
    assert bad_g1_inner_val == 2.0
    assert bad_g1_primal == 2.0 * x_test
    assert bad_g1_deriv == 2.0  # Bug! True derivative is 1.0

    # Second classic nested bug:
    #   g2(x) = x * (d/dy (x * y)|_{y=1}) = x^2, so g2'(x) == 2x (== 7.0 at x=3.5).
    # Untagged dual returns x + 1 == 4.5 instead of 2x == 7.0!
    bad_g2_deriv = diff_untagged(lambda x: x * diff_untagged(lambda y: x * y, 1.0), x_test)
    assert bad_g2_deriv == x_test + 1.0  # Bug! True derivative is 2 * x_test == 7.0

    # Dynamic nesting-depth tagging fixes first-order nested AD...
    assert diff_dynamic_depth_bug(
        lambda x: x * diff_dynamic_depth_bug(lambda y: x + y, 1.0), x_test
    ) == 1.0
    # ...but FAILS on higher-order escaping closures (Manzyuk et al. JFP 2019)!
    # c(z) = (d/dx (x + z))|_{x=2.0} == 1.0, so d/dz [z * c(z)] == 1.0.
    # Dynamic depth resets to 0 after c escapes, so the outer call recycles tag 1!
    c_bug = diff_dynamic_depth_bug(lambda x: (lambda y: x + y), 2.0)
    ho_depth_bug = diff_dynamic_depth_bug(lambda z: z * c_bug(z), 3.0)
    assert ho_depth_bug == 2.0  # Bug! True derivative is 1.0

    # Strictly monotonic fresh gensym tags fix first-order AND escaping higher-order AD:
    good_g1_deriv = diff_tagged(lambda x: x * diff_tagged(lambda y: x + y, 1.0), x_test)
    good_g2_deriv = diff_tagged(lambda x: x * diff_tagged(lambda y: x * y, 1.0), x_test)
    c_good = diff_tagged(lambda x: (lambda y: x + y), 2.0)
    good_ho_deriv = diff_tagged(lambda z: z * c_good(z), 3.0)
    assert good_g1_deriv == 1.0
    assert good_g2_deriv == 2.0 * x_test
    assert good_ho_deriv == 1.0

    print(
        f"[PASS] (b) Perturbation confusion: untagged d/dx[x*d/dy(x+y)]={bad_g1_deriv} "
        f"(primal={bad_g1_primal:.1f}=2x, true=1.0), "
        f"untagged d/dx[x*d/dy(x*y)]={bad_g2_deriv} (true={2*x_test}); "
        f"dynamic-depth escaping-closure bug={ho_depth_bug} (true=1.0); "
        f"monotonic-tag fixed=({good_g1_deriv}, {good_g2_deriv}, {good_ho_deriv})"
    )


# =============================================================================
# Part (c): Non-Differentiable Branches, Clarke Failure & NaN*0 Masking Hazard
# =============================================================================


def ad_branch(f: Callable[[TaggedDual], Any], x: float) -> float:
    """Operational forward-mode AD over branch-taking Python code."""
    tag = _fresh_tag()
    out = f(TaggedDual(tag, x, 1.0))
    return float(_extract_tangent(out, tag))


def _val(x: Any) -> float:
    return x.val if isinstance(x, TaggedDual) else float(x)


def relu_gt(x: Any) -> Any:
    return x if _val(x) > 0.0 else 0.0


def relu_ge(x: Any) -> Any:
    return x if _val(x) >= 0.0 else 0.0


def verify_part_c() -> None:
    # 1. Extensionally identical functions on all R disagreeing under operational AD at x=0
    def id_plain(x: Any) -> Any:
        return x

    def id_piecewise(x: Any) -> Any:
        return 0.0 if _val(x) == 0.0 else x

    for test_x in [-2.0, -0.5, 0.0, 0.5, 2.0]:
        assert id_plain(test_x) == id_piecewise(test_x)

    d_plain_0 = ad_branch(id_plain, 0.0)
    d_piece_0 = ad_branch(id_piecewise, 0.0)
    assert d_plain_0 == 1.0 and d_piece_0 == 0.0  # Wrong derivative at x=0!

    # 2. ReLU asymmetry and Clarke subdifferential chain-rule failure:
    #    h(x) = relu(x) - relu(-x) == x everywhere (C^infty, true h'(0) = 1, Clarke={1}).
    #    Yet operational AD returns 0.0 (for relu_gt) or 2.0 (for relu_ge) — BOTH outside {1}!
    for test_x in [-3.0, -1e-9, 0.0, 1e-9, 3.0]:
        assert relu_gt(test_x) - relu_gt(-test_x) == test_x
        assert relu_ge(test_x) - relu_ge(-test_x) == test_x

    d_relu_gt_0 = ad_branch(relu_gt, 0.0)
    d_relu_ge_0 = ad_branch(relu_ge, 0.0)
    assert d_relu_gt_0 == 0.0 and d_relu_ge_0 == 1.0

    # Implement negation on TaggedDual via (-1.0) * x
    d_clarke_fail_gt = ad_branch(lambda x: relu_gt(x) + (-1.0) * relu_gt((-1.0) * x), 0.0)
    d_clarke_fail_ge = ad_branch(lambda x: relu_ge(x) + (-1.0) * relu_ge((-1.0) * x), 0.0)
    assert d_clarke_fail_gt == 0.0  # OUTSIDE Clarke subdifferential {1}!
    assert d_clarke_fail_ge == 2.0  # OUTSIDE Clarke subdifferential {1}!

    # 3. IEEE-754 0.0 * inf = NaN branch-masking hazard in predicated/vector AD:
    #    y = where(x > 0, sqrt(x), 0.0) at x = 0.0
    #    Naive predicated reverse pass computes:
    #      ct_true  = 1.0 if cond else 0.0  (= 0.0 at x=0)
    #      local_d  = 0.5 / sqrt(x)         (= +inf at x=0)
    #      ct_x     = ct_true * local_d     (= 0.0 * inf = NaN!)
    x0 = 0.0
    cond = x0 > 0.0
    ct_true = 1.0 if cond else 0.0
    local_sqrt_deriv = math.inf if x0 == 0.0 else 0.5 / math.sqrt(x0)
    naive_predicated_grad = ct_true * local_sqrt_deriv
    assert math.isnan(naive_predicated_grad), "expected IEEE-754 0.0 * inf == NaN"

    # Fix 1 (JAX double-where): guard primal argument before sqrt
    safe_x = x0 if cond else 1.0
    double_where_grad = ct_true * (0.5 / math.sqrt(safe_x))
    assert double_where_grad == 0.0

    # Fix 2 (Enzyme strongZero): select(ct == 0.0, 0.0, ct * local_deriv)
    strong_zero_grad = 0.0 if ct_true == 0.0 else ct_true * local_sqrt_deriv
    assert strong_zero_grad == 0.0

    print(
        f"[PASS] (c) Branch & NaN hazards: id_branch'(0)={d_piece_0} (true=1.0), "
        f"[relu(x)-relu(-x)]'(0)={{gt:{d_clarke_fail_gt}, ge:{d_clarke_fail_ge}}} "
        f"outside Clarke={{1}}; predicated where(x>0,sqrt(x),0) naive={naive_predicated_grad}, "
        f"double_where={double_where_grad}, strongZero={strong_zero_grad}"
    )


# =============================================================================
# Part (d): Griewank & Walther (2000) Algorithm 799 (Revolve) Checkpointing
# =============================================================================


def beta(c: int, r: int) -> int:
    """Maximum chain length reversible with c checkpoints and <= r recomputations."""
    return math.comb(c + r, c)


def revolve_closed_form_advances(l: int, c: int) -> int:
    """Griewank & Walther (2000) exact optimal advance count p(l, c) for l >= 1, c >= 1."""
    if l <= 1:
        return 0
    if c <= 0:
        raise ValueError("c must be >= 1 for l > 1")
    r = 0
    while beta(c, r) < l:
        r += 1
    return r * l - math.comb(c + r, c + 1)


def revolve_dp_table(max_l: int, max_c: int) -> tuple[list[list[int]], list[list[int]]]:
    """Exact dynamic program for minimum advance steps p(l, c) and optimal split k*."""
    INF = 10**18
    dp = [[INF] * (max_c + 1) for _ in range(max_l + 1)]
    split = [[0] * (max_c + 1) for _ in range(max_l + 1)]
    for c in range(max_c + 1):
        dp[1][c] = 0
    for l in range(2, max_l + 1):
        for c in range(1, max_c + 1):
            best = INF
            best_k = 1
            for k in range(1, l):
                cost = k + dp[l - k][c - 1] + dp[k][c]
                if cost < best:
                    best = cost
                    best_k = k
            dp[l][c] = best
            split[l][c] = best_k
    return dp, split


def revolve_binomial_split(l: int, c: int) -> int:
    """Griewank & Walther (2000) Algorithm 799 optimal binomial split step count."""
    assert l > 1 and c >= 1
    if c == 1:
        return l - 1
    r = 1
    while beta(c, r) < l:
        r += 1
    # Standard Revolve split placing the checkpoint inside the optimal window
    b0 = beta(c, r - 1)
    b1 = beta(c - 1, r)
    b2 = beta(c, r - 2) if r >= 2 else 0
    # Valid optimal split k satisfies: b2 <= k <= b0 and beta(c-1, r-1) <= l - k <= b1
    lo = max(1, b2, l - b1)
    hi = min(l - 1, b0, l - beta(c - 1, r - 1))
    assert lo <= hi, f"empty optimal split window for l={l}, c={c}, r={r}"
    # Choose Griewank's canonical split (largest valid k <= b0)
    return hi


def simulate_revolve_adjoint(
    l: int,
    c: int,
    s0: float,
    theta: float,
    step_fwd: Callable[[float, float, int], float],
    step_vjp: Callable[[float, float, int, float], tuple[float, float]],
    loss_grad_final: Callable[[float], float],
) -> tuple[float, float, int, int]:
    """Execute binomial Revolve checkpointing on an l-step nonlinear recurrence.

    Returns (final_state, dL_dtheta, advance_count, peak_checkpoints).
    """
    checkpoints: dict[int, float] = {}
    advance_count = 0
    peak_ckpts = 0
    d_theta = 0.0
    s_final: float | None = None
    adj_state: float | None = None

    def record_ckpt(t: int, val: float) -> None:
        nonlocal peak_ckpts
        checkpoints[t] = val
        peak_ckpts = max(peak_ckpts, len(checkpoints))

    def reverse_interval(start: int, length: int, avail_c: int, cur_state: float) -> None:
        nonlocal advance_count, d_theta, s_final, adj_state
        if length == 1:
            # YOUTURN: evaluate forward step `start` and immediately pull back
            nxt = step_fwd(cur_state, theta, start)
            if start == l - 1:
                s_final = nxt
                adj_state = loss_grad_final(nxt)
            assert adj_state is not None
            adj_prev, g_th = step_vjp(cur_state, theta, start, adj_state)
            adj_state = adj_prev
            d_theta += g_th
            return

        assert avail_c >= 1
        # TAKESHOT at `start` (occupying 1 slot while reversing right subinterval)
        already_stored = start in checkpoints
        if not already_stored:
            record_ckpt(start, cur_state)

        k = revolve_binomial_split(length, avail_c)
        # ADVANCE k steps from `start` to `start + k`
        st = cur_state
        for t in range(start, start + k):
            st = step_fwd(st, theta, t)
            advance_count += 1

        # Reverse right subinterval [start + k, start + length) with avail_c - 1 slots
        reverse_interval(start + k, length - k, avail_c - 1, st)

        # RESTORE checkpoint at `start`, then release if we created it at this level
        restored = checkpoints[start]
        if not already_stored:
            del checkpoints[start]
        # Reverse left subinterval [start, start + k) with all avail_c slots
        reverse_interval(start, k, avail_c, restored)

    reverse_interval(0, l, c, s0)
    assert s_final is not None
    return s_final, d_theta, advance_count, peak_ckpts


def verify_part_d() -> None:
    # 1. Exhaustive DP vs closed-form optimality check for all 1 <= l <= 120, 1 <= c <= 8
    max_l, max_c = 120, 8
    dp, _ = revolve_dp_table(max_l, max_c)
    for l in range(1, max_l + 1):
        for c in range(1, max_c + 1):
            cf = revolve_closed_form_advances(l, c)
            assert dp[l][c] == cf, f"DP vs closed-form mismatch at l={l}, c={c}: {dp[l][c]} != {cf}"

    # 2. Live Revolve adjoint execution on a 100-step nonlinear recurrence:
    #    s_{t+1} = 0.6 * sin(s_t + 0.1 * t) + 0.35 * theta * cos(s_t)
    #    L(s_L)  = 0.5 * s_L^2
    L = 100
    s0, theta0 = 0.42, 0.73

    def step_fwd(s: float, th: float, t: int) -> float:
        return 0.6 * math.sin(s + 0.1 * t) + 0.35 * th * math.cos(s)

    def step_vjp(s: float, th: float, t: int, adj_next: float) -> tuple[float, float]:
        ds = 0.6 * math.cos(s + 0.1 * t) - 0.35 * th * math.sin(s)
        dth = 0.35 * math.cos(s)
        return adj_next * ds, adj_next * dth

    # Full-tape ground truth (O(L) memory)
    tape = [s0]
    for t in range(L):
        tape.append(step_fwd(tape[-1], theta0, t))
    adj = tape[L]  # d(0.5 * s_L^2)/d(s_L) = s_L
    ref_grad = 0.0
    for t in range(L - 1, -1, -1):
        adj, g_th = step_vjp(tape[t], theta0, t, adj)
        ref_grad += g_th

    # Central finite difference ground truth
    h = 1e-6

    def full_loss(th: float) -> float:
        s = s0
        for t in range(L):
            s = step_fwd(s, th, t)
        return 0.5 * s * s

    fd_grad = (full_loss(theta0 + h) - full_loss(theta0 - h)) / (2 * h)
    assert abs(ref_grad - fd_grad) < 1e-7

    # Test Revolve across tight checkpoint budgets c in {2, 3, 4, 5, 10}
    summary_parts = []
    for c in (2, 3, 4, 5, 10):
        s_fin, rev_grad, adv, peak = simulate_revolve_adjoint(
            L, c, s0, theta0, step_fwd, step_vjp, lambda sf: sf
        )
        opt_adv = revolve_closed_form_advances(L, c)
        assert s_fin == tape[L], f"final state drift at c={c}"
        assert abs(rev_grad - ref_grad) < 1e-13, f"grad mismatch at c={c}: {rev_grad} vs {ref_grad}"
        assert peak <= c, f"checkpoint budget exceeded: {peak} > {c}"
        assert adv == opt_adv, f"non-optimal advance count at c={c}: {adv} != {opt_adv}"
        summary_parts.append(f"c={c}:adv={adv}(peak={peak})")

    # Confirm logarithmic scaling at diagonal c = r: beta(6, 6) = 924 steps with only 6 slots!
    assert beta(6, 6) == 924
    print(
        f"[PASS] (d) Revolve checkpointing (L={L}, DP==closed-form on 120x8 grid, "
        f"|rev-tape|<1e-13, |tape-FD|={abs(ref_grad-fd_grad):.2e}): "
        + ", ".join(summary_parts)
    )


def main() -> int:
    verify_part_a()
    verify_part_b()
    verify_part_c()
    verify_part_d()
    print("ALL AD VERIFICATION PROBES PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
