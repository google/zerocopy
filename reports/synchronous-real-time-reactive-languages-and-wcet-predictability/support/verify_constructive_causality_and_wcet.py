#!/usr/bin/env python3
"""Standalone verification probe for synchronous causality, dependent clock typing,
and out-of-order microprocessor WCET timing anomalies.

Verifies three core semantic/architectural properties:
  1. Berry's 3-valued Kleene (0, 1, bottom) constructive causality fixpoint analysis
     for Pure Esterel and cyclic combinational logic, proving the strict hierarchy:
       syntactic acyclicity  <  constructive causality  <  unique classical model.
  2. Lustre/Velus dependent clock-calculus checker and node-instantiation unifier,
     accepting aligned sampled/merged streams and rejecting mismatched `when` phases.
  3. Cycle-accurate reservation-station out-of-order (OoO) CPU timing simulator
     reproducing:
       (a) a 2-functional-unit OoO timing anomaly where reducing instruction A's
           latency from 4 cycles (cache miss) to 1 cycle (cache hit) increases
           total schedule makespan from 12 cycles to 14 cycles;
       (b) Lundqvist & Stenstrom (RTSS 1999, Fig. 2) 3-FU PowerPC anomaly
           (2-cycle hit -> 12 cycles vs 10-cycle miss -> 11 cycles);
       (c) Lundqvist & Stenstrom (RTSS 1999, Fig. 3) miss-penalty amplification
           (+8-cycle local cache miss causes +11-cycle global delay); and
       (d) strict in-order resource allocation baseline restoring monotonicity.

Requires Python 3.10+ and the Python standard library only.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from itertools import product
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


# =============================================================================
# PART 1: BERRY'S 3-VALUED KLEENE CONSTRUCTIVE CAUSALITY CHECKER
# =============================================================================


class K3(Enum):
    """Kleene 3-valued flat information lattice: BOT < ZERO, BOT < ONE."""

    BOT = "⊥"
    ZERO = "0"
    ONE = "1"


def k3_not(a: K3) -> K3:
    if a is K3.ZERO:
        return K3.ONE
    if a is K3.ONE:
        return K3.ZERO
    return K3.BOT


def k3_and(a: K3, b: K3) -> K3:
    if a is K3.ZERO or b is K3.ZERO:
        return K3.ZERO
    if a is K3.ONE and b is K3.ONE:
        return K3.ONE
    return K3.BOT


def k3_or(a: K3, b: K3) -> K3:
    if a is K3.ONE or b is K3.ONE:
        return K3.ONE
    if a is K3.ZERO and b is K3.ZERO:
        return K3.ZERO
    return K3.BOT


# --- Pure Esterel single-instant AST (Berry 1999, Constructive Semantics) ---


class Stmt:
    """Base class for Pure Esterel instantaneous statements."""


@dataclass(frozen=True)
class Nothing(Stmt):
    pass


@dataclass(frozen=True)
class Pause(Stmt):
    pass


@dataclass(frozen=True)
class Emit(Stmt):
    sig: str


@dataclass(frozen=True)
class Seq(Stmt):
    first: Stmt
    second: Stmt


@dataclass(frozen=True)
class Par(Stmt):
    left: Stmt
    right: Stmt


@dataclass(frozen=True)
class Present(Stmt):
    sig: str
    then_br: Stmt
    else_br: Stmt


def _eval_must_can(stmt: Stmt, env: Dict[str, K3]) -> Tuple[Set[str], Set[str], bool, bool]:
    """Compute (Must_emit, Can_emit, must_terminate, can_terminate) in Kleene K3.

    Crucially, in Berry's constructive semantics (Draft Book v3, Ch. 3-5):
      When env[s] == BOT in `present s then p else q`:
        - Neither branch is proven taken, so Must = empty and must_terminate = False
          (this rejects classical tautologies such as `present S then emit S else emit S`
           and `present S then emit O else emit O` when S is unresolved).
        - Either branch might execute, so Can = Can(p) U Can(q) and
          can_terminate = can_term(p) or can_term(q).
    """
    if isinstance(stmt, Nothing):
        return set(), set(), True, True
    if isinstance(stmt, Pause):
        return set(), set(), False, False
    if isinstance(stmt, Emit):
        return {stmt.sig}, {stmt.sig}, True, True
    if isinstance(stmt, Seq):
        m1, c1, mt1, ct1 = _eval_must_can(stmt.first, env)
        m2, c2, mt2, ct2 = _eval_must_can(stmt.second, env)
        must = m1 | (m2 if mt1 else set())
        can = c1 | (c2 if ct1 else set())
        return must, can, (mt1 and mt2), (ct1 and ct2)
    if isinstance(stmt, Par):
        m1, c1, mt1, ct1 = _eval_must_can(stmt.left, env)
        m2, c2, mt2, ct2 = _eval_must_can(stmt.right, env)
        return (m1 | m2), (c1 | c2), (mt1 and mt2), (ct1 and ct2)
    if isinstance(stmt, Present):
        v = env[stmt.sig]
        if v is K3.ONE:
            return _eval_must_can(stmt.then_br, env)
        if v is K3.ZERO:
            return _eval_must_can(stmt.else_br, env)
        _, c1, _, ct1 = _eval_must_can(stmt.then_br, env)
        _, c2, _, ct2 = _eval_must_can(stmt.else_br, env)
        return set(), (c1 | c2), False, (ct1 or ct2)
    raise TypeError(f"Unsupported statement: {stmt!r}")


def syntactic_dependencies(stmt: Stmt, guards: Tuple[str, ...] = ()) -> Set[Tuple[str, str]]:
    """Collect static syntactic dependency edges (guard_sig -> emitted_sig)."""
    if isinstance(stmt, (Nothing, Pause)):
        return set()
    if isinstance(stmt, Emit):
        return {(g, stmt.sig) for g in guards}
    if isinstance(stmt, Seq):
        return syntactic_dependencies(stmt.first, guards) | syntactic_dependencies(stmt.second, guards)
    if isinstance(stmt, Par):
        return syntactic_dependencies(stmt.left, guards) | syntactic_dependencies(stmt.right, guards)
    if isinstance(stmt, Present):
        next_guards = guards + (stmt.sig,)
        return (
            syntactic_dependencies(stmt.then_br, next_guards)
            | syntactic_dependencies(stmt.else_br, next_guards)
        )
    raise TypeError(f"Unsupported statement: {stmt!r}")


def has_cycle(edges: Set[Tuple[str, str]]) -> bool:
    """Return True iff the directed edge set contains a cycle (including self-loops)."""
    adj: Dict[str, Set[str]] = {}
    nodes: Set[str] = set()
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
        nodes.add(u)
        nodes.add(v)
    state: Dict[str, int] = {}  # 0=unvisited, 1=visiting, 2=done

    def dfs(u: str) -> bool:
        state[u] = 1
        for w in adj.get(u, ()):
            st = state.get(w, 0)
            if st == 1 or (st == 0 and dfs(w)):
                return True
        state[u] = 2
        return False

    return any(state.get(n, 0) == 0 and dfs(n) for n in sorted(nodes))


def constructive_fixpoint(
    stmt: Stmt,
    inputs: Dict[str, K3],
    locals_and_outputs: Sequence[str],
) -> Tuple[Dict[str, K3], int]:
    """Compute least fixpoint in Kleene K3 via Berry's Must/Can monotone propagation."""
    env: Dict[str, K3] = {k: v for k, v in inputs.items()}
    for s in locals_and_outputs:
        env[s] = K3.BOT

    steps = 0
    while True:
        steps += 1
        must, can, _, _ = _eval_must_can(stmt, env)
        next_env = dict(env)
        for s in locals_and_outputs:
            if env[s] is not K3.BOT:
                continue
            if s in must:
                next_env[s] = K3.ONE
            elif s not in can:
                next_env[s] = K3.ZERO
        if next_env == env:
            return env, steps
        env = next_env


def classical_solutions(
    stmt: Stmt,
    inputs: Dict[str, K3],
    locals_and_outputs: Sequence[str],
) -> List[Dict[str, K3]]:
    """Enumerate all classical Boolean coherent models (sigma(s)=1 iff s emitted)."""
    sols: List[Dict[str, K3]] = []
    for bits in product((K3.ZERO, K3.ONE), repeat=len(locals_and_outputs)):
        env = dict(inputs)
        for s, b in zip(locals_and_outputs, bits):
            env[s] = b
        must, can, _, _ = _eval_must_can(stmt, env)
        assert must == can, "Total Boolean environment must yield Must == Can"
        if all((env[s] is K3.ONE) == (s in must) for s in locals_and_outputs):
            sols.append({s: env[s] for s in locals_and_outputs})
    return sols


def check_esterel_constructiveness(
    name: str,
    stmt: Stmt,
    input_names: Sequence[str],
    local_names: Sequence[str],
) -> Dict[str, object]:
    """Exhaustively check syntactic acyclicity, classical uniqueness, and constructive causality."""
    edges = syntactic_dependencies(stmt)
    cyclic = has_cycle(edges)
    all_constructive = True
    classical_counts: List[int] = []
    traces: List[Tuple[Dict[str, str], Dict[str, str], int]] = []

    for bits in product((K3.ZERO, K3.ONE), repeat=len(input_names)):
        inp = dict(zip(input_names, bits))
        fp, steps = constructive_fixpoint(stmt, inp, local_names)
        sols = classical_solutions(stmt, inp, local_names)
        classical_counts.append(len(sols))
        resolved = all(fp[s] is not K3.BOT for s in local_names)
        if not resolved:
            all_constructive = False
        traces.append(
            (
                {k: v.value for k, v in inp.items()},
                {s: fp[s].value for s in local_names},
                steps,
            )
        )

    return {
        "name": name,
        "syntactically_cyclic": cyclic,
        "classical_solution_counts": classical_counts,
        "constructively_causal": all_constructive,
        "traces": traces,
    }


def check_malik_cyclic_combinational_circuit() -> bool:
    """Verify Malik (1994) / Berry (1999) cyclic combinational mux-network in Kleene K3:
      y1 = (not c and x1) or (c and y2)
      y2 = (c and x2) or (not c and y1)
    Syntactic graph has cycle y1 <-> y2, yet stabilizes for all (c, x1, x2) in {0,1}^3.
    """
    for c, x1, x2 in product((K3.ZERO, K3.ONE), repeat=3):
        y1, y2 = K3.BOT, K3.BOT
        for _ in range(8):
            ny1 = k3_or(k3_and(k3_not(c), x1), k3_and(c, y2))
            ny2 = k3_or(k3_and(c, x2), k3_and(k3_not(c), y1))
            if (ny1, ny2) == (y1, y2):
                break
            y1, y2 = ny1, ny2
        if y1 is K3.BOT or y2 is K3.BOT:
            return False
        # Verify functional equivalence: when c=0, y1=y2=x1; when c=1, y1=y2=x2
        expected = x1 if c is K3.ZERO else x2
        if y1 is not expected or y2 is not expected:
            return False
    return True


def run_part1_constructive_causality() -> None:
    print("=== PART 1: Berry 3-Valued Kleene Constructive Causality ===")

    # Case 1A: Constructively causal syntactic cycle (branch-guarded A->B / B->A)
    #   present I then (present A then emit B else nothing || emit A)
    #             else (present B then emit A else nothing || emit B)
    p_cyclic_ok_1 = Present(
        "I",
        Par(Present("A", Emit("B"), Nothing()), Emit("A")),
        Par(Present("B", Emit("A"), Nothing()), Emit("B")),
    )
    r1a = check_esterel_constructiveness("cyclic_branch_guarded_emit", p_cyclic_ok_1, ["I"], ["A", "B"])
    assert r1a["syntactically_cyclic"] is True
    assert r1a["classical_solution_counts"] == [1, 1]
    assert r1a["constructively_causal"] is True

    # Case 1B: Constructively causal syntactic cycle relying on absence (Can-elimination)
    #   present I then (present A then emit B else nothing)
    #             else (present B then emit A else nothing || emit B)
    p_cyclic_ok_2 = Present(
        "I",
        Present("A", Emit("B"), Nothing()),
        Par(Present("B", Emit("A"), Nothing()), Emit("B")),
    )
    r1b = check_esterel_constructiveness("cyclic_with_absence_propagation", p_cyclic_ok_2, ["I"], ["A", "B"])
    assert r1b["syntactically_cyclic"] is True
    assert r1b["classical_solution_counts"] == [1, 1]
    assert r1b["constructively_causal"] is True
    # Confirm I=1 yields A=0, B=0 and I=0 yields A=1, B=1
    trace_map = {t[0]["I"]: t[1] for t in r1b["traces"]}
    assert trace_map["1"] == {"A": "0", "B": "0"}
    assert trace_map["0"] == {"A": "1", "B": "1"}

    # Case 1C: Contradictory cycle (0 classical models): present S then nothing else emit S
    p_contra = Present("S", Nothing(), Emit("S"))
    r1c = check_esterel_constructiveness("contradictory_neg_feedback", p_contra, [], ["S"])
    assert r1c["syntactically_cyclic"] is True
    assert r1c["classical_solution_counts"] == [0]
    assert r1c["constructively_causal"] is False

    # Case 1D: Self-fulfilling / ambiguous cycle (2 classical models): present S then emit S else nothing
    p_ambig = Present("S", Emit("S"), Nothing())
    r1d = check_esterel_constructiveness("self_fulfilling_ambiguous", p_ambig, [], ["S"])
    assert r1d["syntactically_cyclic"] is True
    assert r1d["classical_solution_counts"] == [2]
    assert r1d["constructively_causal"] is False

    # Case 1E: Non-constructive classical tautology (1 unique classical model S=1, yet REJECTED!)
    #   present S then emit S else emit S
    p_taut = Present("S", Emit("S"), Emit("S"))
    r1e = check_esterel_constructiveness("nonconstructive_tautology", p_taut, [], ["S"])
    assert r1e["syntactically_cyclic"] is True
    assert r1e["classical_solution_counts"] == [1]
    assert r1e["constructively_causal"] is False

    # Case 1F: Malik (1994) / Berry (1999) cyclic combinational gate circuit
    assert check_malik_cyclic_combinational_circuit() is True

    for r in (r1a, r1b, r1c, r1d, r1e):
        print(
            f"  [OK] {r['name']:32s} cyclic={str(r['syntactically_cyclic']):5s} "
            f"classical_models={r['classical_solution_counts']} "
            f"constructive={r['constructively_causal']}"
        )
    print("  [OK] malik_1994_cyclic_mux_circuit    stabilizes in K3 for all 8 input vectors\n")


# =============================================================================
# PART 2: LUSTRE / VELUS DEPENDENT CLOCK-CALCULUS UNIFIER
# =============================================================================


class ClockError(Exception):
    """Raised when a synchronous dataflow expression violates dependent clock typing."""


class Clock:
    """Clock term mirroring INRIA/velus src/Clocks.v: Cbase | Con ck x tag, plus CVar."""


@dataclass(frozen=True)
class CBase(Clock):
    def __str__(self) -> str:
        return "base"


@dataclass(frozen=True)
class CVar(Clock):
    name: str

    def __str__(self) -> str:
        return f"?{self.name}"


@dataclass(frozen=True)
class COn(Clock):
    parent: Clock
    cond: str
    tag: bool

    def __str__(self) -> str:
        phase = self.cond if self.tag else f"not {self.cond}"
        return f"({self.parent} on {phase})"


class LExpr:
    """Core Lustre expression AST."""


@dataclass(frozen=True)
class LConst(LExpr):
    value: int
    clock: Optional[Clock] = None


@dataclass(frozen=True)
class LVar(LExpr):
    name: str


@dataclass(frozen=True)
class LBinOp(LExpr):
    op: str
    left: LExpr
    right: LExpr


@dataclass(frozen=True)
class LFby(LExpr):
    init: LExpr
    step: LExpr


@dataclass(frozen=True)
class LWhen(LExpr):
    expr: LExpr
    cond: str
    tag: bool = True


@dataclass(frozen=True)
class LMerge(LExpr):
    cond: str
    true_br: LExpr
    false_br: LExpr


@dataclass(frozen=True)
class LCurrent(LExpr):
    expr: LExpr


@dataclass(frozen=True)
class LNodeSig:
    name: str
    params: Tuple[Tuple[str, Clock], ...]  # polymorphic over CBase
    ret_clock: Clock


@dataclass(frozen=True)
class LApp(LExpr):
    node: LNodeSig
    args: Tuple[LExpr, ...]


class ClockUnifier:
    """First-order unifier for dependent Lustre clocks (base, vars, and `on x=tag`)."""

    def __init__(self) -> None:
        self.subst: Dict[str, Clock] = {}

    def deref(self, ck: Clock) -> Clock:
        if isinstance(ck, CVar) and ck.name in self.subst:
            return self.deref(self.subst[ck.name])
        if isinstance(ck, COn):
            return COn(self.deref(ck.parent), ck.cond, ck.tag)
        return ck

    def _occurs(self, vname: str, ck: Clock) -> bool:
        ck = self.deref(ck)
        if isinstance(ck, CVar):
            return ck.name == vname
        if isinstance(ck, COn):
            return self._occurs(vname, ck.parent)
        return False

    def unify(self, a: Clock, b: Clock, context: str) -> Clock:
        a = self.deref(a)
        b = self.deref(b)
        if a == b:
            return a
        if isinstance(a, CVar):
            if self._occurs(a.name, b):
                raise ClockError(f"{context}: cyclic clock unification {a} = {b}")
            self.subst[a.name] = b
            return b
        if isinstance(b, CVar):
            if self._occurs(b.name, a):
                raise ClockError(f"{context}: cyclic clock unification {b} = {a}")
            self.subst[b.name] = a
            return a
        if isinstance(a, COn) and isinstance(b, COn):
            if a.cond != b.cond or a.tag != b.tag:
                raise ClockError(f"{context}: incompatible sampling clocks {a} vs {b}")
            parent = self.unify(a.parent, b.parent, context)
            return COn(parent, a.cond, a.tag)
        raise ClockError(f"{context}: clock mismatch {a} vs {b}")


def instck(base_ck: Clock, var_sub: Dict[str, str], ck: Clock) -> Clock:
    """Instantiate a node's polymorphic clock (mirrors INRIA/velus Clocks.v:instck)."""
    if isinstance(ck, CBase):
        return base_ck
    if isinstance(ck, COn):
        if ck.cond not in var_sub:
            raise ClockError(f"Dependent carrier '{ck.cond}' not bound to variable argument")
        return COn(instck(base_ck, var_sub, ck.parent), var_sub[ck.cond], ck.tag)
    return ck


def infer_clock(
    expr: LExpr,
    env: Dict[str, Clock],
    unifier: ClockUnifier,
    fresh_counter: List[int],
) -> Clock:
    """Dependent clock checker corresponding to Velus LClocking.v (`wc_exp`)."""
    if isinstance(expr, LConst):
        if expr.clock is not None:
            return expr.clock
        fresh_counter[0] += 1
        return CVar(f"k{fresh_counter[0]}")
    if isinstance(expr, LVar):
        if expr.name not in env:
            raise ClockError(f"Unbound stream variable '{expr.name}'")
        return unifier.deref(env[expr.name])
    if isinstance(expr, LBinOp):
        c1 = infer_clock(expr.left, env, unifier, fresh_counter)
        c2 = infer_clock(expr.right, env, unifier, fresh_counter)
        return unifier.unify(c1, c2, f"binop '{expr.op}'")
    if isinstance(expr, LFby):
        c0 = infer_clock(expr.init, env, unifier, fresh_counter)
        c1 = infer_clock(expr.step, env, unifier, fresh_counter)
        return unifier.unify(c0, c1, "fby")
    if isinstance(expr, LWhen):
        if expr.cond not in env:
            raise ClockError(f"Unbound clock carrier '{expr.cond}'")
        c_cond = unifier.deref(env[expr.cond])
        c_expr = infer_clock(expr.expr, env, unifier, fresh_counter)
        aligned = unifier.unify(c_expr, c_cond, f"when({expr.cond}={expr.tag})")
        return COn(aligned, expr.cond, expr.tag)
    if isinstance(expr, LMerge):
        if expr.cond not in env:
            raise ClockError(f"Unbound merge carrier '{expr.cond}'")
        c_cond = unifier.deref(env[expr.cond])
        ct = infer_clock(expr.true_br, env, unifier, fresh_counter)
        cf = infer_clock(expr.false_br, env, unifier, fresh_counter)
        unifier.unify(ct, COn(c_cond, expr.cond, True), f"merge({expr.cond}).true")
        unifier.unify(cf, COn(c_cond, expr.cond, False), f"merge({expr.cond}).false")
        return unifier.deref(c_cond)
    if isinstance(expr, LCurrent):
        ce = unifier.deref(infer_clock(expr.expr, env, unifier, fresh_counter))
        if not isinstance(ce, COn):
            raise ClockError(f"current requires sampled subclock, got {ce}")
        return ce.parent
    if isinstance(expr, LApp):
        if len(expr.args) != len(expr.node.params):
            raise ClockError(f"Arity mismatch calling node '{expr.node.name}'")
        fresh_counter[0] += 1
        call_base = CVar(f"base_{expr.node.name}_{fresh_counter[0]}")
        var_sub: Dict[str, str] = {}
        for (pname, _), arg in zip(expr.node.params, expr.args):
            if isinstance(arg, LVar):
                var_sub[pname] = arg.name
        for (pname, pck), arg in zip(expr.node.params, expr.args):
            expected = instck(call_base, var_sub, pck)
            actual = infer_clock(arg, env, unifier, fresh_counter)
            unifier.unify(actual, expected, f"call {expr.node.name} param '{pname}'")
        return unifier.deref(instck(call_base, var_sub, expr.node.ret_clock))
    raise TypeError(f"Unsupported Lustre expression: {expr!r}")


def check_lustre(expr: LExpr, env: Dict[str, Clock]) -> Clock:
    u = ClockUnifier()
    ck = infer_clock(expr, env, u, [0])
    return u.deref(ck)


def run_part2_clock_calculus() -> None:
    print("=== PART 2: Lustre / Velus Dependent Clock-Calculus Unifier ===")
    env: Dict[str, Clock] = {
        "x": CBase(),
        "y": CBase(),
        "c": CBase(),
        "b": CBase(),
        "d": COn(CBase(), "c", True),
    }

    # Valid 1: merge c (x when c) (y when not c) : base
    e_merge_ok = LMerge("c", LWhen(LVar("x"), "c", True), LWhen(LVar("y"), "c", False))
    ck1 = check_lustre(e_merge_ok, env)
    assert ck1 == CBase(), f"Expected base, got {ck1}"
    print(f"  [PASS] merge c (x when c) (y when not c)         -> {ck1}")

    # Valid 2: nested dependent subclock (x when c) when d : (base on c) on d
    e_nested_ok = LWhen(LWhen(LVar("x"), "c", True), "d", True)
    ck2 = check_lustre(e_nested_ok, env)
    assert ck2 == COn(COn(CBase(), "c", True), "d", True)
    print(f"  [PASS] (x when c) when d                         -> {ck2}")

    # Valid 3: polymorphic node instantiated on subclock (base on c)
    node_inc = LNodeSig(
        name="counter",
        params=(("inc", CBase()),),
        ret_clock=CBase(),
    )
    e_app_ok = LApp(node_inc, (LWhen(LVar("x"), "c", True),))
    ck3 = check_lustre(e_app_ok, env)
    assert ck3 == COn(CBase(), "c", True)
    print(f"  [PASS] counter(x when c) [polymorphic instck]    -> {ck3}")

    # Valid 4: classic Lustre V4 `current(x when c) + y` projects subclock back to base
    e_curr_ok = LBinOp("+", LCurrent(LWhen(LVar("x"), "c", True)), LVar("y"))
    ck4 = check_lustre(e_curr_ok, env)
    assert ck4 == CBase()
    print(f"  [PASS] current(x when c) + y [Lustre V4 hold]    -> {ck4}")

    # Invalid cases that MUST be rejected at compile time
    bad_cases: List[Tuple[str, LExpr]] = [
        (
            "x + (x when c) [base vs subclock]",
            LBinOp("+", LVar("x"), LWhen(LVar("x"), "c", True)),
        ),
        (
            "(x when c) + (y when not c) [opposite phases]",
            LBinOp("+", LWhen(LVar("x"), "c", True), LWhen(LVar("y"), "c", False)),
        ),
        (
            "(x when c) + (y when b) [distinct carriers]",
            LBinOp("+", LWhen(LVar("x"), "c", True), LWhen(LVar("y"), "b", True)),
        ),
        (
            "(x when c) when b [carrier b not on c]",
            LWhen(LWhen(LVar("x"), "c", True), "b", True),
        ),
        (
            "merge c (x when c) y [unaligned false branch]",
            LMerge("c", LWhen(LVar("x"), "c", True), LVar("y")),
        ),
    ]
    for label, expr in bad_cases:
        try:
            got = check_lustre(expr, env)
        except ClockError as err:
            print(f"  [REJECT] {label:46s} -> {err}")
        else:
            raise AssertionError(f"Expected ClockError for {label}, got {got}")
    print()


# =============================================================================
# PART 3: CYCLE-ACCURATE OoO CPU TIMING ANOMALY SIMULATOR
# =============================================================================


@dataclass(frozen=True)
class Insn:
    name: str
    unit: str
    dispatch: int
    latency: int
    deps: Tuple[str, ...] = ()
    order: int = 0


@dataclass(frozen=True)
class ExecRecord:
    name: str
    unit: str
    dispatch: int
    start: int
    finish: int


def simulate_pipeline(
    insns: Sequence[Insn],
    in_order_units: Set[str],
) -> Tuple[int, Dict[str, ExecRecord]]:
    """Cycle-accurate functional-unit reservation-station scheduler.

    - Each functional unit executes at most one instruction at a time (non-pipelined
      occupancy for `latency` cycles: occupies `[start, start + latency)`).
    - Data dependencies (`deps`) must finish (`dep.finish <= cycle`) before an
      instruction can initiate execution.
    - Out-of-order units select the oldest ready instruction (lowest `order`) among
      all dispatched, unstarted instructions targeting that unit.
    - In-order units (in `in_order_units`) only allow the oldest unstarted
      instruction targeting that unit to initiate (strict program-order resource
      allocation, as defined in Lundqvist & Stenstrom 1999 Section 2.1).
    """
    numbered = [
        Insn(
            name=ins.name,
            unit=ins.unit,
            dispatch=ins.dispatch,
            latency=ins.latency,
            deps=ins.deps,
            order=idx,
        )
        for idx, ins in enumerate(insns)
    ]
    units = sorted({ins.unit for ins in numbered})
    unit_free_at: Dict[str, int] = {u: 0 for u in units}
    started: Set[str] = set()
    records: Dict[str, ExecRecord] = {}

    cycle = min(ins.dispatch for ins in numbered)
    max_cycle = cycle + sum(ins.latency for ins in numbered) + 500

    while len(records) < len(numbered):
        if cycle > max_cycle:
            raise RuntimeError("Simulation failed to terminate (possible dependency cycle)")

        for u in units:
            if unit_free_at[u] > cycle:
                continue
            pending_u = [
                ins for ins in numbered if ins.unit == u and ins.name not in started
            ]
            if not pending_u:
                continue

            if u in in_order_units:
                head = pending_u[0]
                if head.dispatch <= cycle and all(
                    d in records and records[d].finish <= cycle for d in head.deps
                ):
                    chosen = head
                else:
                    chosen = None
            else:
                ready = [
                    ins
                    for ins in pending_u
                    if ins.dispatch <= cycle
                    and all(d in records and records[d].finish <= cycle for d in ins.deps)
                ]
                chosen = ready[0] if ready else None  # oldest-ready priority

            if chosen is not None:
                started.add(chosen.name)
                finish = cycle + chosen.latency
                unit_free_at[u] = finish
                records[chosen.name] = ExecRecord(
                    name=chosen.name,
                    unit=chosen.unit,
                    dispatch=chosen.dispatch,
                    start=cycle,
                    finish=finish,
                )
        cycle += 1

    makespan = max(r.finish for r in records.values())
    return makespan, records


def _fmt_schedule(records: Dict[str, ExecRecord], names: Sequence[str]) -> str:
    return ", ".join(
        f"{n}@{records[n].unit}[{records[n].start}..{records[n].finish})" for n in names
    )


def run_part3_wcet_timing_anomalies() -> None:
    print("=== PART 3: Cycle-Accurate OoO CPU Timing Anomaly Verification ===")

    # -------------------------------------------------------------------------
    # Scenario A: 2-Functional-Unit (FU1, FU2) OoO Timing Anomaly (4 -> 1 cycle)
    # Reducing A's latency from 4 cycles (cache miss) to 1 cycle (cache hit)
    # INCREASES total schedule completion time from 12 cycles to 14 cycles!
    # -------------------------------------------------------------------------
    def make_2fu(a_latency: int) -> List[Insn]:
        return [
            Insn("A", "FU1", dispatch=0, latency=a_latency, deps=()),
            Insn("B", "FU2", dispatch=0, latency=4, deps=("A",)),
            Insn("C", "FU2", dispatch=1, latency=1, deps=()),
            Insn("D", "FU1", dispatch=2, latency=4, deps=("C",)),
            Insn("E", "FU1", dispatch=3, latency=4, deps=("D",)),
        ]

    ms_2fu_miss, rec_2fu_miss = simulate_pipeline(make_2fu(4), in_order_units={"FU1"})
    ms_2fu_hit, rec_2fu_hit = simulate_pipeline(make_2fu(1), in_order_units={"FU1"})
    assert ms_2fu_miss == 12, f"Expected 12 cycles on 4-cycle miss, got {ms_2fu_miss}"
    assert ms_2fu_hit == 14, f"Expected 14 cycles on 1-cycle hit, got {ms_2fu_hit}"
    assert ms_2fu_hit > ms_2fu_miss, "Expected cache hit to take strictly longer than miss!"

    print("  [ANOMALY 1A: 2-FU OoO Hit-Worse-Than-Miss (A: 4c miss -> 1c hit)]")
    print(f"    Cache MISS (A=4c): makespan={ms_2fu_miss}c | {_fmt_schedule(rec_2fu_miss, 'ABCDE')}")
    print(f"    Cache HIT  (A=1c): makespan={ms_2fu_hit}c | {_fmt_schedule(rec_2fu_hit, 'ABCDE')}")
    print(f"    Delta: local={1 - 4:+d}c, global={ms_2fu_hit - ms_2fu_miss:+d}c (NON-MONOTONIC!)")

    # Control: Strict in-order on BOTH FU1 and FU2 restores monotonicity
    ms_2fu_io_miss, _ = simulate_pipeline(make_2fu(4), in_order_units={"FU1", "FU2"})
    ms_2fu_io_hit, _ = simulate_pipeline(make_2fu(1), in_order_units={"FU1", "FU2"})
    assert ms_2fu_io_hit <= ms_2fu_io_miss
    assert (ms_2fu_io_miss - ms_2fu_io_hit) <= (4 - 1)
    print(
        f"    In-order control: hit={ms_2fu_io_hit}c <= miss={ms_2fu_io_miss}c "
        f"(delta={ms_2fu_io_miss - ms_2fu_io_hit:+d}c <= +3c, monotonic)"
    )

    # -------------------------------------------------------------------------
    # Scenario B: Exact Lundqvist & Stenstrom (RTSS 1999, Fig. 2) PowerPC model
    #   A (LD, LSU, disp=1, 2c hit / 10c miss), B (ADD, IU, disp=2, 1c, dep A),
    #   C (ADD, IU, disp=3, 1c), D (MUL, MCIU, disp=4, 4c, dep C),
    #   E (MUL, MCIU, disp=5, 4c, dep D).
    #   Units: LSU in-order; IU and MCIU out-of-order.
    #   Note: Lundqvist & Stenstrom number cycles 1-based; dispatch=0 corresponds
    #   to cycle 1 start, so finish times match their Fig. 2 (12c hit vs 11c miss).
    # -------------------------------------------------------------------------
    def make_ls99_fig2(a_latency: int) -> List[Insn]:
        return [
            Insn("A", "LSU", dispatch=0, latency=a_latency, deps=()),
            Insn("B", "IU", dispatch=1, latency=1, deps=("A",)),
            Insn("C", "IU", dispatch=2, latency=1, deps=()),
            Insn("D", "MCIU", dispatch=3, latency=4, deps=("C",)),
            Insn("E", "MCIU", dispatch=4, latency=4, deps=("D",)),
        ]

    ms_ls2_hit, rec_ls2_hit = simulate_pipeline(make_ls99_fig2(2), in_order_units={"LSU"})
    ms_ls2_miss, rec_ls2_miss = simulate_pipeline(make_ls99_fig2(10), in_order_units={"LSU"})
    assert ms_ls2_hit == 12, f"Expected 12 cycles on LS99 Fig.2 hit, got {ms_ls2_hit}"
    assert ms_ls2_miss == 11, f"Expected 11 cycles on LS99 Fig.2 miss, got {ms_ls2_miss}"
    print("  [ANOMALY 1B: Lundqvist & Stenstrom RTSS 1999 Fig. 2 (LSU/IU/MCIU)]")
    print(f"    Cache HIT  (A=2c):  makespan={ms_ls2_hit}c | {_fmt_schedule(rec_ls2_hit, 'ABCDE')}")
    print(f"    Cache MISS (A=10c): makespan={ms_ls2_miss}c | {_fmt_schedule(rec_ls2_miss, 'ABCDE')}")
    print(f"    Delta: local=+8c, global={ms_ls2_miss - ms_ls2_hit:+d}c (hit is 1c slower than miss!)")

    # -------------------------------------------------------------------------
    # Scenario C: Exact Lundqvist & Stenstrom (RTSS 1999, Fig. 3) Amplification
    #   A (LD, LSU, disp=0, 2c hit / 10c miss), B (MUL, MCIU, disp=1, 4c, dep A),
    #   C (LD, LSU, disp=2, 10c miss, dep B), D (MUL, MCIU, disp=9, 4c).
    #   Global penalty = +11c > +8c local cache miss penalty!
    # -------------------------------------------------------------------------
    def make_ls99_fig3(a_latency: int) -> List[Insn]:
        return [
            Insn("A", "LSU", dispatch=0, latency=a_latency, deps=()),
            Insn("B", "MCIU", dispatch=1, latency=4, deps=("A",)),
            Insn("C", "LSU", dispatch=2, latency=10, deps=("B",)),
            Insn("D", "MCIU", dispatch=9, latency=4, deps=()),
        ]

    ms_ls3_hit, rec_ls3_hit = simulate_pipeline(make_ls99_fig3(2), in_order_units={"LSU"})
    ms_ls3_miss, rec_ls3_miss = simulate_pipeline(make_ls99_fig3(10), in_order_units={"LSU"})
    assert ms_ls3_hit == 16, f"Expected 16 cycles on LS99 Fig.3 hit, got {ms_ls3_hit}"
    assert ms_ls3_miss == 27, f"Expected 27 cycles on LS99 Fig.3 miss, got {ms_ls3_miss}"
    assert (ms_ls3_miss - ms_ls3_hit) == 11 > 8
    print("  [ANOMALY 2: Lundqvist & Stenstrom RTSS 1999 Fig. 3 (Miss Amplification)]")
    print(f"    Cache HIT  (A=2c):  makespan={ms_ls3_hit}c | {_fmt_schedule(rec_ls3_hit, 'ABCD')}")
    print(f"    Cache MISS (A=10c): makespan={ms_ls3_miss}c | {_fmt_schedule(rec_ls3_miss, 'ABCD')}")
    print(f"    Delta: local=+8c, global={ms_ls3_miss - ms_ls3_hit:+d}c (+3c amplification over miss penalty!)")


def main() -> int:
    run_part1_constructive_causality()
    run_part2_clock_calculus()
    run_part3_wcet_timing_anomalies()
    print("ALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
