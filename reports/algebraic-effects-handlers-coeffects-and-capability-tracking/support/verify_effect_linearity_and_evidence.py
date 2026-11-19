#!/usr/bin/env python3
"""Small-step effect-handler machine plus a graded linearity checker.

Self-contained probe (Python 3.10+, standard library only, no I/O besides
stdout).  It models a call-by-value lambda calculus with deep effect handlers,
first-class resumptions, linear resource handles and `finally` frames, and it
mechanically checks the claims listed in CHECKS at the bottom of this file:

  (a) handler nesting order is observable: State/Exn and State/Choice;
  (b) unchecked multi-shot resumption double-frees a captured linear handle,
      and a dynamic one-shot check turns that into a resumption error;
  (c) unchecked 0-shot abort leaks a captured handle unless the continuation
      is unwound through a registered finalizer;
  (d) a checker that grades each operation's resumption multiplicity in
      {0, 1, w} accepts only programs that run without leak, double-free or
      use-after-free, over an enumerated family of programs; the same family
      shows that value linearity alone accepts unsafe programs;
  (e) evidence-vector dispatch agrees with dynamic stack search, whereas
      lexical capability binding differs under accidental handler capture
      and fails when a capability escapes its handler;
  (f) an opaque foreign frame is a barrier for effect dispatch;
  (g) the grade algebra {0, 1, w} satisfies the coeffect-scalar axioms.

Exit status 0 means every check passed.  `--json` prints a machine-readable
summary; `--list` prints the per-program verdicts of the enumerated family.
"""

from __future__ import annotations

import itertools
import json
import sys
from dataclasses import dataclass, field
from typing import Any, Iterator, Optional

# --------------------------------------------------------------------------
# Syntax
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Lit:
    v: Any


@dataclass(frozen=True)
class Var:
    x: str


@dataclass(frozen=True)
class Lam:
    x: str
    body: Any


@dataclass(frozen=True)
class App:
    f: Any
    a: Any


@dataclass(frozen=True)
class Let:
    x: str
    e: Any
    body: Any


@dataclass(frozen=True)
class If:
    c: Any
    t: Any
    e: Any


@dataclass(frozen=True)
class Prim:
    op: str
    args: tuple


@dataclass(frozen=True)
class Open:
    """Allocate a linear resource; evaluates to its handle."""

    name: str


@dataclass(frozen=True)
class Write:
    """Use a handle without consuming it."""

    r: Any


@dataclass(frozen=True)
class Close:
    """Consume a handle."""

    r: Any


@dataclass(frozen=True)
class Do:
    """Perform operation `label` with an argument."""

    label: str
    arg: Any


@dataclass(frozen=True)
class Clause:
    x: str
    k: str
    body: Any


@dataclass(frozen=True)
class Handle:
    """Deep handler: `ret` is (x, term); `clauses` is ((label, Clause), ...)."""

    body: Any
    ret: tuple
    clauses: tuple

    def clause(self, label: str) -> Optional[Clause]:
        for name, cl in self.clauses:
            if name == label:
                return cl
        return None


@dataclass(frozen=True)
class Resume:
    """Reinstate resumption `k` and return `v` at the perform site."""

    k: Any
    v: Any


@dataclass(frozen=True)
class Discontinue:
    """Unwind resumption `k`: run its `finally` cleanups, then discard it."""

    k: Any


@dataclass(frozen=True)
class Finally:
    """Run `cleanup` when `body` returns or when the frame is unwound."""

    body: Any
    cleanup: Any


@dataclass(frozen=True)
class Foreign:
    """Evaluate `body` above an opaque foreign frame."""

    body: Any


UNIT = Lit(None)


def seq(*terms: Any) -> Any:
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = Let("_", t, out)
    return out


def prim(op: str, *args: Any) -> Prim:
    return Prim(op, tuple(args))


# --------------------------------------------------------------------------
# Small-step machine (CEK style; the continuation is a persistent cons list,
# so a captured segment can be reinstated any number of times)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Closure:
    x: str
    body: Any
    env: Any


@dataclass(frozen=True)
class Res:
    rid: int


@dataclass
class Resumption:
    segment: tuple  # frames, innermost first; the last one is the HandleK
    evv: Any  # evidence vector at the perform site
    label: str
    uses: int = 0


@dataclass(frozen=True)
class LetK:
    x: str
    body: Any
    env: Any


@dataclass(frozen=True)
class AppFK:
    a: Any
    env: Any


@dataclass(frozen=True)
class AppAK:
    f: Any


@dataclass(frozen=True)
class IfK:
    t: Any
    e: Any
    env: Any


@dataclass(frozen=True)
class PrimK:
    op: str
    done: tuple
    rest: tuple
    env: Any


@dataclass(frozen=True)
class WriteK:
    pass


@dataclass(frozen=True)
class CloseK:
    pass


@dataclass(frozen=True)
class DoK:
    label: str
    env: Any


@dataclass(frozen=True)
class HandleK:
    h: Handle
    env: Any
    marker: int
    saved_evv: Any


@dataclass(frozen=True)
class ResumeFK:
    v: Any
    env: Any


@dataclass(frozen=True)
class ResumeAK:
    res: Any


@dataclass(frozen=True)
class DiscK:
    pass


@dataclass(frozen=True)
class FinallyK:
    cleanup: Any
    env: Any


@dataclass(frozen=True)
class CleanupK:
    pending: tuple
    final: Any


@dataclass(frozen=True)
class ForeignK:
    saved_evv: Any


@dataclass(frozen=True)
class ClauseEndK:
    res: Any


class MachineError(Exception):
    def __init__(self, kind: str, detail: str = "") -> None:
        super().__init__(f"{kind}: {detail}")
        self.kind = kind
        self.detail = detail


@dataclass
class Outcome:
    kind: str  # ok | leak | double-free | use-after-free | ...
    value: Any = None
    detail: str = ""
    steps: int = 0
    opened: int = 0
    closes: int = 0
    leaked: tuple = ()
    evidence_mismatches: int = 0


EV = "%ev"  # environment slot holding lexically bound capabilities


class Machine:
    """dispatch: 'search' walks the stack for the innermost handler of a
    label; 'evidence' reads a dynamically scoped evidence vector; 'lexical'
    reads the capability captured in the lexical environment.
    one_shot: a second resume/discontinue of a resumption is an error.
    auto_finalize: a clause that returns without consuming its resumption
    has that resumption unwound for it."""

    def __init__(self, dispatch: str = "search", one_shot: bool = False,
                 auto_finalize: bool = False, max_steps: int = 200_000) -> None:
        assert dispatch in ("search", "evidence", "lexical")
        self.dispatch = dispatch
        self.one_shot = one_shot
        self.auto_finalize = auto_finalize
        self.max_steps = max_steps

    # -- driver ----------------------------------------------------------
    def run(self, term: Any) -> Outcome:
        self.resources: dict[int, list] = {}
        self.closes = 0
        self.evv: dict = {}
        self.next_marker = 0
        self.mismatches = 0
        steps = 0
        ctrl: tuple = ("E", term, {EV: {}})
        kont: Any = None
        try:
            while True:
                steps += 1
                if steps > self.max_steps:
                    raise MachineError("step-limit")
                if ctrl[0] == "E":
                    ctrl, kont = self._eval(ctrl[1], ctrl[2], kont)
                elif kont is None:
                    break
                else:
                    ctrl, kont = self._ret(ctrl[1], kont)
        except MachineError as exc:
            return self._outcome(exc.kind, None, exc.detail, steps)
        leaked = tuple(n for n, st in self.resources.values() if st == "open")
        return self._outcome("leak" if leaked else "ok", ctrl[1], "", steps)

    def _outcome(self, kind: str, value: Any, detail: str, steps: int) -> Outcome:
        leaked = tuple(n for n, st in self.resources.values() if st == "open")
        return Outcome(kind, value, detail, steps, len(self.resources),
                       self.closes, leaked, self.mismatches)

    # -- evaluation of a term -------------------------------------------
    def _eval(self, t: Any, env: dict, kont: Any) -> tuple:
        match t:
            case Lit(v):
                return ("R", v), kont
            case Var(x):
                if x not in env:
                    raise MachineError("stuck", f"unbound variable {x}")
                return ("R", env[x]), kont
            case Lam(x, body):
                return ("R", Closure(x, body, env)), kont
            case App(f, a):
                return ("E", f, env), (AppFK(a, env), kont)
            case Let(x, e, body):
                return ("E", e, env), (LetK(x, body, env), kont)
            case If(c, th, el):
                return ("E", c, env), (IfK(th, el, env), kont)
            case Prim(op, args):
                if not args:
                    return ("R", self._prim(op, ())), kont
                return ("E", args[0], env), (PrimK(op, (), args[1:], env), kont)
            case Open(name):
                rid = len(self.resources)
                self.resources[rid] = [name, "open"]
                return ("R", Res(rid)), kont
            case Write(r):
                return ("E", r, env), (WriteK(), kont)
            case Close(r):
                return ("E", r, env), (CloseK(), kont)
            case Do(label, arg):
                return ("E", arg, env), (DoK(label, env), kont)
            case Handle(body, _, clauses):
                self.next_marker += 1
                marker = self.next_marker
                frame = HandleK(t, env, marker, self.evv)
                added = {label: marker for label, _ in clauses}
                self.evv = {**self.evv, **added}
                body_env = {**env, EV: {**env[EV], **added}}
                return ("E", body, body_env), (frame, kont)
            case Resume(k, v):
                return ("E", k, env), (ResumeFK(v, env), kont)
            case Discontinue(k):
                return ("E", k, env), (DiscK(), kont)
            case Finally(body, cleanup):
                return ("E", body, env), (FinallyK(cleanup, env), kont)
            case Foreign(body):
                frame = ForeignK(self.evv)
                self.evv = {}
                return ("E", body, env), (frame, kont)
        raise MachineError("stuck", f"unknown term {t!r}")

    # -- return of a value to the top frame -----------------------------
    def _ret(self, v: Any, kont: tuple) -> tuple:
        frame, rest = kont
        match frame:
            case LetK(x, body, env):
                return ("E", body, {**env, x: v}), rest
            case AppFK(a, env):
                return ("E", a, env), (AppAK(v), rest)
            case AppAK(f):
                if not isinstance(f, Closure):
                    raise MachineError("stuck", "application of a non-function")
                return ("E", f.body, {**f.env, f.x: v}), rest
            case IfK(th, el, env):
                return ("E", th if v else el, env), rest
            case PrimK(op, done, more, env):
                done = done + (v,)
                if more:
                    return ("E", more[0], env), (PrimK(op, done, more[1:], env), rest)
                return ("R", self._prim(op, done)), rest
            case WriteK():
                self._live(v, "use-after-free")
                return ("R", None), rest
            case CloseK():
                self._live(v, "double-free")
                self.resources[v.rid][1] = "closed"
                self.closes += 1
                return ("R", None), rest
            case DoK(label, env):
                return self._perform(label, v, env, rest)
            case HandleK(h, env, _, saved):
                self.evv = saved
                x, body = h.ret
                return ("E", body, {**env, x: v}), rest
            case ResumeFK(vt, env):
                if not isinstance(v, Resumption):
                    raise MachineError("stuck", "resume of a non-resumption")
                return ("E", vt, env), (ResumeAK(v), rest)
            case ResumeAK(res):
                return self._resume(res, v, rest)
            case DiscK():
                if not isinstance(v, Resumption):
                    raise MachineError("stuck", "discontinue of a non-resumption")
                return self._unwind(v, rest, None)
            case FinallyK(cleanup, env):
                return ("E", cleanup, env), (CleanupK((), v), rest)
            case CleanupK(pending, final):
                if pending:
                    (cleanup, env), more = pending[0], pending[1:]
                    return ("E", cleanup, env), (CleanupK(more, final), rest)
                return ("R", final), rest
            case ForeignK(saved):
                self.evv = saved
                return ("R", v), rest
            case ClauseEndK(res):
                if self.auto_finalize and res.uses == 0:
                    return self._unwind(res, rest, v)
                return ("R", v), rest
        raise MachineError("stuck", f"unknown frame {frame!r}")

    def _live(self, v: Any, kind: str) -> None:
        if not isinstance(v, Res):
            raise MachineError("stuck", "resource operation on a non-handle")
        if self.resources[v.rid][1] != "open":
            raise MachineError(kind, self.resources[v.rid][0])

    @staticmethod
    def _prim(op: str, a: tuple) -> Any:
        match op:
            case "add":
                return a[0] + a[1]
            case "eq":
                return a[0] == a[1]
            case "pair":
                return (a[0], a[1])
            case "single":
                return (a[0],)
            case "concat":
                return a[0] + a[1]
        raise MachineError("stuck", f"unknown primitive {op}")

    # -- effect operations ----------------------------------------------
    def _perform(self, label: str, v: Any, env: dict, kont: Any) -> tuple:
        if self.dispatch == "search":
            target = None
        elif self.dispatch == "evidence":
            target = self.evv.get(label)
            if target is None:
                raise MachineError("unhandled-effect", label)
        else:
            target = env[EV].get(label)
            if target is None:
                raise MachineError("unhandled-effect", label)
        segment = []
        innermost = None  # marker of the innermost handler that has `label`
        k = kont
        while k is not None:
            frame, k = k
            segment.append(frame)
            if isinstance(frame, ForeignK):
                raise MachineError("unhandled-effect", f"{label}: foreign-frame barrier")
            if isinstance(frame, HandleK) and frame.h.clause(label) is not None:
                if innermost is None:
                    innermost = frame.marker
                if target is None or frame.marker == target:
                    if self.dispatch == "evidence" and innermost != frame.marker:
                        self.mismatches += 1
                    res = Resumption(tuple(segment), self.evv, label)
                    self.evv = frame.saved_evv
                    cl = frame.h.clause(label)
                    cenv = {**frame.env, cl.x: v, cl.k: res}
                    return ("E", cl.body, cenv), (ClauseEndK(res), k)
        if self.dispatch == "lexical":
            raise MachineError("capability-escaped", label)
        raise MachineError("unhandled-effect", label)

    def _consume(self, res: Resumption) -> None:
        if self.one_shot and res.uses >= 1:
            raise MachineError("continuation-already-resumed", res.label)
        res.uses += 1

    def _resume(self, res: Resumption, v: Any, kont: Any) -> tuple:
        self._consume(res)
        if self.dispatch == "evidence" and self.evv != res.segment[-1].saved_evv:
            raise MachineError("non-scoped-resumption", res.label)
        for frame in reversed(res.segment):
            kont = (frame, kont)
        self.evv = res.evv
        return ("R", v), kont

    def _unwind(self, res: Resumption, kont: Any, final: Any) -> tuple:
        self._consume(res)
        pending = tuple((f.cleanup, f.env) for f in res.segment
                        if isinstance(f, FinallyK))
        return ("R", None), (CleanupK(pending, final), kont)


# --------------------------------------------------------------------------
# Grade algebra {0, 1, w}: the multiplicity semiring used as a coeffect scalar
# --------------------------------------------------------------------------

GRADES = ("0", "1", "w")


def g_add(a: str, b: str) -> str:  # context sharing (contraction)
    if a == "0":
        return b
    if b == "0":
        return a
    return "w"


def g_mul(a: str, b: str) -> str:  # sequencing (application)
    if a == "0" or b == "0":
        return "0"
    if a == "1":
        return b
    if b == "1":
        return a
    return "w"


def g_le(a: str, b: str) -> bool:  # sub-coeffecting: exact usage refines w
    return a == b or b == "w"


def coeffect_scalar_axioms() -> list[str]:
    """Axioms of a coeffect scalar (C, mul, add, use=1, ign=0, <=)."""
    bad = []
    for r, s, t in itertools.product(GRADES, repeat=3):
        if g_mul(g_mul(r, s), t) != g_mul(r, g_mul(s, t)):
            bad.append(f"mul not associative at {r}{s}{t}")
        if g_add(g_add(r, s), t) != g_add(r, g_add(s, t)):
            bad.append(f"add not associative at {r}{s}{t}")
        if g_mul(g_add(r, s), t) != g_add(g_mul(r, t), g_mul(s, t)):
            bad.append(f"right distributivity fails at {r}{s}{t}")
        if g_mul(t, g_add(r, s)) != g_add(g_mul(t, r), g_mul(t, s)):
            bad.append(f"left distributivity fails at {r}{s}{t}")
        if g_le(r, s) and g_le(s, t) and not g_le(r, t):
            bad.append(f"<= not transitive at {r}{s}{t}")
    for r in GRADES:
        if g_mul("1", r) != r or g_mul(r, "1") != r:
            bad.append(f"use is not a unit of mul at {r}")
        if g_add("0", r) != r or g_add(r, "0") != r:
            bad.append(f"ign is not a unit of add at {r}")
        if not g_le(r, r):
            bad.append(f"<= not reflexive at {r}")
    return bad


# --------------------------------------------------------------------------
# Static checker: flow-sensitive value linearity + graded control-flow rules
# --------------------------------------------------------------------------


class _Escapes(Exception):
    pass


def _mentions(t: Any, name: str) -> bool:
    match t:
        case Var(x):
            return x == name
        case Lit(_) | Open(_):
            return False
        case Lam(x, body):
            return x != name and _mentions(body, name)
        case Let(x, e, body):
            return _mentions(e, name) or (x != name and _mentions(body, name))
        case Handle(body, (rx, rbody), clauses):
            if _mentions(body, name) or (rx != name and _mentions(rbody, name)):
                return True
            return any(name not in (cl.x, cl.k) and _mentions(cl.body, name)
                       for _, cl in clauses)
        case Prim(_, args):
            return any(_mentions(a, name) for a in args)
    return any(_mentions(c, name) for c in _children(t))


def _children(t: Any) -> tuple:
    match t:
        case App(f, a):
            return (f, a)
        case If(c, th, el):
            return (c, th, el)
        case Write(r) | Close(r) | Discontinue(r):
            return (r,)
        case Do(_, arg):
            return (arg,)
        case Resume(k, v):
            return (k, v)
        case Finally(body, cleanup):
            return (body, cleanup)
        case Foreign(body):
            return (body,)
    return ()


def resumption_usage(body: Any, k: str) -> frozenset:
    """Abstract per-path use of resumption `k` in a clause body.

    Each path is summarised as one of: 'D' (dropped: never resumed, never
    unwound), 'U' (unwound exactly once), '1' (resumed exactly once),
    'W' (anything else: two or more uses, or the resumption escapes)."""

    def add(xs: set, ys: set) -> set:
        return {(min(2, a + c), min(2, b + d)) for a, b in xs for c, d in ys}

    zero = {(0, 0)}

    def go(t: Any) -> set:
        match t:
            case Lit(_) | Open(_):
                return zero
            case Var(x):
                if x == k:
                    raise _Escapes()
                return zero
            case Lam(x, b):
                if x != k and _mentions(b, k):
                    raise _Escapes()
                return zero
            case Let(x, e, b):
                return add(go(e), zero if x == k else go(b))
            case If(c, th, el):
                return add(go(c), go(th) | go(el))
            case Prim(_, args):
                acc = zero
                for a in args:
                    acc = add(acc, go(a))
                return acc
            case Resume(Var(x), v) if x == k:
                return add({(1, 0)}, go(v))
            case Discontinue(Var(x)) if x == k:
                return {(0, 1)}
            case Handle(b, (rx, rbody), clauses):
                inner = (rx != k and _mentions(rbody, k)) or any(
                    k not in (cl.x, cl.k) and _mentions(cl.body, k)
                    for _, cl in clauses)
                if inner:
                    raise _Escapes()
                return go(b)
        acc = zero
        for c in _children(t):
            acc = add(acc, go(c))
        return acc

    try:
        paths = go(body)
    except _Escapes:
        return frozenset({"W"})
    names = {(0, 0): "D", (1, 0): "1", (0, 1): "U"}
    return frozenset(names.get(p, "W") for p in paths)


def admits(grade: str, usage: frozenset) -> bool:
    """Which clause behaviours a declared grade permits."""
    if grade == "1":
        return usage == frozenset({"1"})
    if grade == "0":
        return usage == frozenset({"U"})
    return grade == "w"


def _scope_vars(t: Any) -> frozenset:
    """Linear names opened or closed in `t`, not looking inside lambdas."""
    match t:
        case Let(x, Open(_), body):
            return frozenset({x}) | _scope_vars(body)
        case Let(_, e, body):
            return _scope_vars(e) | _scope_vars(body)
        case Close(Var(x)):
            return frozenset({x})
        case Lam(_, _) | Lit(_) | Var(_) | Open(_):
            return frozenset()
        case Prim(_, args):
            return frozenset().union(*map(_scope_vars, args)) if args else frozenset()
        case Handle(body, (_, rbody), clauses):
            out = _scope_vars(body) | _scope_vars(rbody)
            for _, cl in clauses:
                out |= _scope_vars(cl.body)
            return out
    out = frozenset()
    for c in _children(t):
        out |= _scope_vars(c)
    return out


def _labels(t: Any, under_lam: bool, acc: dict) -> None:
    match t:
        case Do(label, arg):
            acc["all"].add(label)
            if under_lam:
                acc["latent"].add(label)
            _labels(arg, under_lam, acc)
        case Lam(_, body):
            _labels(body, True, acc)
        case Let(_, e, body):
            _labels(e, under_lam, acc)
            _labels(body, under_lam, acc)
        case Prim(_, args):
            for a in args:
                _labels(a, under_lam, acc)
        case Handle(body, (_, rbody), clauses):
            _labels(body, under_lam, acc)
            _labels(rbody, under_lam, acc)
            for _, cl in clauses:
                _labels(cl.body, under_lam, acc)
        case _:
            for c in _children(t):
                _labels(c, under_lam, acc)


@dataclass(frozen=True)
class _Ctx:
    lin: frozenset = frozenset()  # linear names in scope
    hstack: tuple = ()  # (labels | None for a foreign barrier, scope_vars)
    guards: tuple = ()  # (handler depth, names closed by the cleanup)
    ambient: frozenset = frozenset()  # outer handles held around a clause
    own: frozenset = frozenset()  # labels of the handler whose clause this is


class Checker:
    """mode 'graded': value linearity plus the multiplicity rules.
    mode 'value-linear': value linearity only (single-entry/single-exit
    control flow is assumed, as in a linear type system without handlers)."""

    RULES = ("site-w", "site-0", "clause", "resume-site", "app-site")

    def __init__(self, sig: dict, mode: str = "graded",
                 disabled: frozenset = frozenset()) -> None:
        assert mode in ("graded", "value-linear")
        assert disabled <= frozenset(self.RULES)
        self.sig = sig
        self.mode = mode
        self.disabled = disabled  # graded rules switched off (ablation only)
        self.errors: list[str] = []

    def check(self, term: Any) -> list[str]:
        self.errors = []
        acc = {"all": set(), "latent": set()}
        _labels(term, False, acc)
        self.all_labels = sorted(acc["all"])
        self.latent = sorted(acc["latent"])
        out = self._go(term, frozenset(), _Ctx())
        if out:
            self._err(f"linear handle(s) {sorted(out)} live at program end")
        return list(self.errors)

    def _err(self, msg: str) -> None:
        if msg not in self.errors:
            self.errors.append(msg)

    def _site(self, label: str, live: frozenset, ctx: _Ctx) -> None:
        """Obligation at a point where `label` may be performed."""
        if self.mode != "graded":
            return
        grade = self.sig.get(label)
        if grade is None:
            self._err(f"operation {label} has no declared grade")
            return
        held = live | ctx.ambient
        depth = None
        for i in range(len(ctx.hstack) - 1, -1, -1):
            labels, scope = ctx.hstack[i]
            if labels is None:
                self._err(f"operation {label} would cross a foreign frame")
                return
            if label in labels:
                depth, held = i, held & scope
                break
        guarded = frozenset().union(
            *(names for d, names in ctx.guards if depth is None or d > depth))
        if grade == "w" and held and "site-w" not in self.disabled:
            self._err(f"{label} is graded w but its continuation holds linear "
                      f"{sorted(held)}")
        if grade == "0" and held - guarded and "site-0" not in self.disabled:
            self._err(f"{label} is graded 0 but its continuation holds linear "
                      f"{sorted(held - guarded)} without a finalizer")

    def _go(self, t: Any, live: frozenset, ctx: _Ctx) -> frozenset:
        match t:
            case Lit(_):
                return live
            case Var(x):
                if x in ctx.lin:
                    self._err(f"linear handle {x} used as a first-class value")
                return live
            case Lam(x, body):
                for name in sorted(ctx.lin):
                    if name != x and _mentions(body, name):
                        self._err(f"closure captures linear handle {name}")
                out = self._go(body, frozenset(), _Ctx())
                if out:
                    self._err(f"linear handle(s) {sorted(out)} live at function end")
                return live
            case App(f, a):
                # A call may perform any operation that occurs under a lambda.
                live = self._go(a, self._go(f, live, ctx), ctx)
                if "app-site" not in self.disabled:
                    for label in self.latent:
                        self._site(label, live, ctx)
                return live
            case Let(x, Open(_), body):
                if x in ctx.lin:
                    self._err(f"linear handle {x} is shadowed")
                inner = _Ctx(ctx.lin | {x}, ctx.hstack, ctx.guards, ctx.ambient, ctx.own)
                out = self._go(body, live | {x}, inner)
                if x in out:
                    self._err(f"linear handle {x} is not consumed on some path")
                return out - {x}
            case Let(x, e, body):
                if x in ctx.lin:
                    self._err(f"linear handle {x} is shadowed")
                return self._go(body, self._go(e, live, ctx), ctx)
            case If(c, th, el):
                live = self._go(c, live, ctx)
                a, b = self._go(th, live, ctx), self._go(el, live, ctx)
                if a != b:
                    self._err("branches disagree on consumed linear handles")
                return a & b
            case Prim(_, args):
                for a in args:
                    live = self._go(a, live, ctx)
                return live
            case Open(_):
                self._err("open must be bound by let")
                return live
            case Write(Var(x)):
                if x not in live:
                    self._err(f"write to {x}, which is not a live linear handle")
                return live
            case Close(Var(x)):
                if x not in live:
                    self._err(f"close of {x}, which is not a live linear handle")
                return live - {x}
            case Write(_) | Close(_):
                self._err("resource operations take a variable")
                return live
            case Do(label, arg):
                live = self._go(arg, live, ctx)
                self._site(label, live, ctx)
                return live
            case Handle(body, (_, rbody), clauses):
                labels = frozenset(name for name, _ in clauses)
                inner = _Ctx(ctx.lin, ctx.hstack + ((labels, _scope_vars(body)),),
                             ctx.guards, ctx.ambient, ctx.own)
                out = self._go(body, live, inner)
                outer = _Ctx(frozenset(), ctx.hstack, ctx.guards, ctx.ambient | live,
                             labels)
                if self._go(rbody, frozenset(), outer):
                    self._err("return clause leaves a linear handle live")
                for name, cl in clauses:
                    if self._go(cl.body, frozenset(), outer):
                        self._err(f"clause {name} leaves a linear handle live")
                    if self.mode == "graded":
                        usage = resumption_usage(cl.body, cl.k)
                        grade = self.sig.get(name)
                        if grade is None:
                            self._err(f"operation {name} has no declared grade")
                        elif "clause" not in self.disabled and not admits(grade, usage):
                            self._err(f"clause {name} uses its resumption as "
                                      f"{sorted(usage)}, not admitted by grade {grade}")
                return out
            case Resume(Var(_), v):
                # The resumed body runs under its reinstated (deep) handler, so
                # only labels that handler forwards can capture this clause.
                live = self._go(v, live, ctx)
                if "resume-site" not in self.disabled:
                    for label in self.all_labels:
                        if label not in ctx.own:
                            self._site(label, live, ctx)
                return live
            case Discontinue(Var(_)):
                return live
            case Resume(_, _) | Discontinue(_):
                self._err("resumptions are used through their variable")
                return live
            case Finally(body, cleanup):
                if not _simple(cleanup):
                    self._err("finally cleanup must be effect-free")
                closes = _scope_vars(cleanup)
                inner = _Ctx(ctx.lin, ctx.hstack,
                             ctx.guards + ((len(ctx.hstack), closes),), ctx.ambient,
                             ctx.own)
                return self._go(cleanup, self._go(body, live, inner), ctx)
            case Foreign(body):
                inner = _Ctx(ctx.lin, ctx.hstack + ((None, frozenset()),),
                             ctx.guards, ctx.ambient, ctx.own)
                return self._go(body, live, inner)
        self._err(f"unknown term {t!r}")
        return live


def _simple(t: Any) -> bool:
    match t:
        case Lit(_) | Var(_):
            return True
        case Write(Var(_)) | Close(Var(_)):
            return True
        case Let(_, e, body):
            return _simple(e) and _simple(body)
    return False


# --------------------------------------------------------------------------
# Demonstration programs
# --------------------------------------------------------------------------


def run_state(init: Any, body: Any) -> Any:
    """State as a parameter-passing handler: the handled body denotes a
    function from the current state to (result, final state)."""
    h = Handle(
        body,
        ("x", Lam("s", prim("pair", Var("x"), Var("s")))),
        (("get", Clause("_", "k", Lam("s", App(Resume(Var("k"), Var("s")), Var("s"))))),
         ("put", Clause("v", "k", Lam("_s", App(Resume(Var("k"), UNIT), Var("v")))))),
    )
    return App(h, init)


def run_exn(body: Any) -> Any:
    return Handle(body, ("x", prim("pair", Lit("ok"), Var("x"))),
                  (("raise", Clause("e", "k", prim("pair", Lit("err"), Var("e")))),))


def run_choice(body: Any) -> Any:
    both = prim("concat", Resume(Var("k"), Lit(True)), Resume(Var("k"), Lit(False)))
    return Handle(body, ("x", prim("single", Var("x"))),
                  (("choose", Clause("_", "k", both)),))


PUT_THEN_RAISE = seq(Do("put", Lit(1)), Do("raise", Lit("boom")))

COUNT_BRANCH = seq(
    Do("choose", UNIT),
    Let("s", Do("get", UNIT), seq(Do("put", prim("add", Var("s"), Lit(1))),
                                  Do("get", UNIT))))

ID_RET = ("x", Var("x"))


def ask_handler(body: Any, answer: int) -> Handle:
    return Handle(body, ID_RET,
                  (("ask", Clause("_", "k", Resume(Var("k"), Lit(answer)))),))


# A higher-order function that privately handles `ask` around its callback.
ACCIDENTAL = Let(
    "hof", Lam("g", ask_handler(App(Var("g"), UNIT), 100)),
    ask_handler(App(Var("hof"), Lam("_", Do("ask", UNIT))), 1))

# A closure that performs `ask` and outlives the handler that bound it.
ESCAPE_INNER = Let("f", ask_handler(Lam("_", Do("ask", UNIT)), 1), App(Var("f"), UNIT))
ESCAPE_OUTER = ask_handler(ESCAPE_INNER, 7)

PLACEMENTS = ("none", "inside-unguarded", "inside-guarded", "outer-open-inner-close",
              "outer-open-outer-close", "closed-before-perform",
              "opened-after-perform", "in-callee", "caller-holds",
              "close-first", "held-by-inner-clause")

CLAUSES = {
    "drop": Lit(0),
    "unwind": seq(Discontinue(Var("k")), Lit(0)),
    "once": Resume(Var("k"), Var("x")),
    "twice": seq(Resume(Var("k"), Lit(True)), Resume(Var("k"), Lit(False))),
    "once-or-drop": If(Var("x"), Resume(Var("k"), Var("x")), Lit(0)),
    "once-or-unwind": If(Var("x"), Resume(Var("k"), Var("x")),
                         seq(Discontinue(Var("k")), Lit(0))),
    "once-then-unwind": seq(Resume(Var("k"), Var("x")), Discontinue(Var("k"))),
}

SHAPES = ("direct", "nested")


def build(placement: str, clause: str, arg: bool, shape: str = "direct") -> Any:
    """One member of the enumerated family: where a linear handle `f` lives
    relative to a perform of `op`, and what the handler does with `k`."""
    perform = Do("op", Lit(arg))
    f = Var("f")
    wrap = lambda h: h  # noqa: E731
    match placement:
        case "none":
            body = perform
        case "inside-unguarded":
            body = Let("f", Open("r"), Let("b", perform, seq(Write(f), Close(f), Var("b"))))
        case "inside-guarded":
            body = Let("f", Open("r"),
                       Finally(Let("b", perform, seq(Write(f), Var("b"))), Close(f)))
        case "outer-open-inner-close":
            body = Let("b", perform, seq(Write(f), Close(f), Var("b")))
            wrap = lambda h: Let("f", Open("r"), h)  # noqa: E731
        case "outer-open-outer-close":
            body = Let("b", perform, seq(Write(f), Var("b")))
            wrap = lambda h: Let("f", Open("r"),  # noqa: E731
                                 Let("res", h, seq(Close(f), Var("res"))))
        case "closed-before-perform":
            body = Let("f", Open("r"), seq(Write(f), Close(f), perform))
        case "opened-after-perform":
            body = Let("b", perform, Let("f", Open("r"), seq(Write(f), Close(f), Var("b"))))
        case "in-callee":
            callee = Lam("_", Let("f", Open("r"), Let("b", perform, seq(Close(f), Var("b")))))
            body = App(Var("g"), UNIT)
            wrap = lambda h: Let("g", callee, h)  # noqa: E731
        case "caller-holds":
            body = Let("f", Open("r"), Let("b", App(Var("g"), UNIT), seq(Close(f), Var("b"))))
            wrap = lambda h: Let("g", Lam("_", perform), h)  # noqa: E731
        case "close-first":
            body = Let("f", Open("r"), Let("b", perform, seq(Close(f), Var("b"))))
        case "held-by-inner-clause":
            # An inner handler's clause holds `g` across its own resume while
            # the resumed body performs `op`, which that handler forwards.
            holding = Let("g", Open("r"), Let("res", Resume(Var("k2"), Lit(0)),
                                              seq(Close(Var("g")), Var("res"))))
            body = Handle(seq(Do("noop", UNIT), perform), ID_RET,
                          (("noop", Clause("_", "k2", holding)),))
        case _:
            raise ValueError(placement)
    if shape == "nested":
        body = Handle(seq(Do("noop", UNIT), body), ID_RET,
                      (("noop", Clause("_", "k2", Resume(Var("k2"), Lit(0)))),))
    return wrap(Handle(body, ID_RET, (("op", Clause("x", "k", CLAUSES[clause])),)))


def family() -> Iterator[tuple]:
    for placement, clause, grade, arg, shape in itertools.product(
            PLACEMENTS, CLAUSES, GRADES, (True, False), SHAPES):
        name = f"{placement}/{clause}/grade={grade}/arg={arg}/{shape}"
        yield name, build(placement, clause, arg, shape), {"op": grade, "noop": "1"}


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------


@dataclass
class Report:
    results: list = field(default_factory=list)
    facts: dict = field(default_factory=dict)

    def check(self, name: str, ok: bool, detail: str = "") -> None:
        self.results.append((name, bool(ok), detail))

    @property
    def ok(self) -> bool:
        return all(r[1] for r in self.results)


def run(term: Any, **kw: Any) -> Outcome:
    return Machine(**kw).run(term)


def checks_ordering(rep: Report) -> None:
    state_outside = run(run_state(Lit(0), run_exn(PUT_THEN_RAISE)))
    exn_outside = run(run_exn(run_state(Lit(0), PUT_THEN_RAISE)))
    rep.facts["state_outside_exn"] = repr(state_outside.value)
    rep.facts["exn_outside_state"] = repr(exn_outside.value)
    rep.check("a1 State outside Exn keeps the write made before the raise",
              state_outside.value == (("err", "boom"), 1), repr(state_outside.value))
    rep.check("a2 Exn outside State discards the state with the continuation",
              exn_outside.value == ("err", "boom"), repr(exn_outside.value))
    rep.check("a3 the two nestings are observably different",
              state_outside.value != exn_outside.value)
    shared = run(run_state(Lit(0), run_choice(COUNT_BRANCH)))
    forked = run(run_choice(run_state(Lit(0), COUNT_BRANCH)))
    rep.facts["state_outside_choice"] = repr(shared.value)
    rep.facts["choice_outside_state"] = repr(forked.value)
    rep.check("a4 State outside Choice threads one state through both branches",
              shared.value == ((1, 2), 2), repr(shared.value))
    rep.check("a5 Choice outside State gives each branch its own state",
              forked.value == ((1, 1), (1, 1)), repr(forked.value))


def checks_resources(rep: Report) -> None:
    dup = build("close-first", "twice", True)
    out = run(dup)
    rep.check("b1 unchecked multi-shot resumption double-frees the handle",
              out.kind == "double-free" and out.closes == 1, f"{out.kind} closes={out.closes}")
    out = run(build("inside-unguarded", "twice", True))
    rep.check("b1' if the duplicated continuation writes first, it is a use-after-free",
              out.kind == "use-after-free" and out.closes == 1,
              f"{out.kind} closes={out.closes}")
    out = run(dup, one_shot=True)
    rep.check("b2 a one-shot check turns the second resume into an error",
              out.kind == "continuation-already-resumed" and out.closes == 1,
              f"{out.kind} closes={out.closes}")
    rep.check("b3 value linearity alone accepts the double-free program",
              Checker({"op": "w"}, "value-linear").check(dup) == [])
    errs = Checker({"op": "w"}).check(dup)
    rep.check("b4 the graded checker rejects it at the perform site",
              any("graded w" in e for e in errs), "; ".join(errs))
    errs = Checker({"op": "1"}).check(dup)
    rep.check("b5 a grade-1 signature rejects the multi-shot clause instead",
              any("not admitted by grade 1" in e for e in errs), "; ".join(errs))

    leak = build("inside-unguarded", "drop", True)
    out = run(leak)
    rep.check("c1 unchecked 0-shot abort leaks the handle",
              out.kind == "leak" and out.leaked == ("r",), f"{out.kind} {out.leaked}")
    guarded_drop = build("inside-guarded", "drop", True)
    out = run(guarded_drop)
    rep.check("c2 a finally frame does not run when the resumption is merely dropped",
              out.kind == "leak", out.kind)
    out = run(build("inside-guarded", "unwind", True))
    rep.check("c3 unwinding the resumption runs the finalizer: no leak",
              out.kind == "ok" and out.closes == 1, f"{out.kind} closes={out.closes}")
    out = run(guarded_drop, auto_finalize=True)
    rep.check("c4 implicit finalization of an unresumed clause also closes it",
              out.kind == "ok" and out.closes == 1, f"{out.kind} closes={out.closes}")
    out = run(build("inside-unguarded", "unwind", True))
    rep.check("c5 unwinding without a registered finalizer still leaks",
              out.kind == "leak", out.kind)
    rep.check("c6 value linearity alone accepts the leaking program",
              Checker({"op": "w"}, "value-linear").check(leak) == [])
    errs = Checker({"op": "0"}).check(build("inside-unguarded", "unwind", True))
    rep.check("c7 grade 0 requires a finalizer for every captured handle",
              any("without a finalizer" in e for e in errs), "; ".join(errs))
    rep.check("c8 grade 0 with a guarded handle and an unwinding clause is accepted",
              Checker({"op": "0"}).check(build("inside-guarded", "unwind", True)) == [])


def checks_family(rep: Report, listing: Optional[list] = None) -> None:
    table = {"accepted-safe": 0, "accepted-unsafe": 0, "rejected-safe": 0,
             "rejected-unsafe": 0}
    ablation = {"accepted-safe": 0, "accepted-unsafe": 0, "rejected-safe": 0,
                "rejected-unsafe": 0}
    unsafe_kinds: dict[str, int] = {}
    by_grade = {g: 0 for g in GRADES}
    witnesses = {"multi-shot": 0, "abort-with-finalizer": 0, "linear-capture": 0}
    disagreements = mismatches = total = 0
    conservative = {"clause-not-admitted-by-grade": 0, "perform-site-rule": 0}
    counterexamples = []
    members = [(name, term, sig, run(term)) for name, term, sig in family()]
    for name, term, sig, dyn in members:
        total += 1
        safe = dyn.kind == "ok"
        ev = run(term, dispatch="evidence")
        mismatches += ev.evidence_mismatches
        if (ev.kind, ev.value, ev.closes) != (dyn.kind, dyn.value, dyn.closes):
            disagreements += 1
        accepted = Checker(sig).check(term) == []
        table[f"{'accepted' if accepted else 'rejected'}-{'safe' if safe else 'unsafe'}"] += 1
        if accepted and not safe:
            counterexamples.append(f"{name}: {dyn.kind}")
        if safe and not accepted:
            clause = name.split("/")[1]
            conforming = admits(sig["op"], resumption_usage(CLAUSES[clause], "k"))
            conservative["perform-site-rule" if conforming
                         else "clause-not-admitted-by-grade"] += 1
        if accepted:
            by_grade[sig["op"]] += 1
            if "/twice/" in name:
                witnesses["multi-shot"] += 1
            if name.startswith("inside-guarded/unwind/grade=0"):
                witnesses["abort-with-finalizer"] += 1
            if name.startswith("inside-unguarded/once/grade=1"):
                witnesses["linear-capture"] += 1
        plain = Checker(sig, "value-linear").check(term) == []
        ablation[f"{'accepted' if plain else 'rejected'}-{'safe' if safe else 'unsafe'}"] += 1
        if plain and not safe:
            unsafe_kinds[dyn.kind] = unsafe_kinds.get(dyn.kind, 0) + 1
        if listing is not None:
            listing.append(f"{'ACCEPT' if accepted else 'reject'} {dyn.kind:<12} {name}")
    rep.facts.update({"family_size": total, "graded": table, "value_linear_only": ablation,
                      "value_linear_unsafe_kinds": unsafe_kinds,
                      "accepted_by_grade": by_grade, "witnesses": witnesses,
                      "rejected_safe_reasons": conservative})
    rep.check("d1 graded checker: every accepted program runs resource-safe",
              table["accepted-unsafe"] == 0, "; ".join(counterexamples[:5]) or str(table))
    rep.check("d2 graded checker accepts programs at each grade 0, 1 and w",
              all(by_grade[g] > 0 for g in GRADES), str(by_grade))
    rep.check("d3 accepted set includes multi-shot, finalized abort and linear capture",
              all(v > 0 for v in witnesses.values()), str(witnesses))
    rep.check("d4 every dynamically unsafe program is in the rejected set",
              table["rejected-unsafe"] > 0 and table["accepted-unsafe"] == 0, str(table))
    rep.check("d5 value linearity alone accepts double-free and leak programs",
              unsafe_kinds.get("double-free", 0) > 0 and unsafe_kinds.get("leak", 0) > 0,
              str(unsafe_kinds))
    necessity = {}
    for rule in Checker.RULES:
        off = frozenset({rule})
        necessity[rule] = sum(1 for _, term, sig, dyn in members
                              if dyn.kind != "ok" and Checker(sig, disabled=off).check(term) == [])
    rep.facts["unsafe_accepted_when_rule_disabled"] = necessity
    rep.check("d6 each graded rule is necessary: disabling it admits an unsafe program",
              all(n > 0 for n in necessity.values()), str(necessity))
    rep.check("e1 evidence-vector dispatch agrees with stack search on the family",
              disagreements == 0 and mismatches == 0,
              f"disagreements={disagreements} mismatches={mismatches}")


def checks_dispatch(rep: Report) -> None:
    for term, label in ((run_state(Lit(0), run_exn(PUT_THEN_RAISE)), "State/Exn"),
                        (run_state(Lit(0), run_choice(COUNT_BRANCH)), "State/Choice"),
                        (run_choice(run_state(Lit(0), COUNT_BRANCH)), "Choice/State")):
        a, b = run(term), run(term, dispatch="evidence")
        rep.check(f"e2 evidence dispatch agrees with search on {label}",
                  (a.kind, a.value) == (b.kind, b.value) and b.evidence_mismatches == 0,
                  f"{a.value!r} vs {b.value!r}")
    dyn, evd, lex = (run(ACCIDENTAL, dispatch=d) for d in ("search", "evidence", "lexical"))
    rep.facts["accidental_capture"] = {"search": dyn.value, "evidence": evd.value,
                                       "lexical": lex.value}
    rep.check("e3 dynamic dispatch lets a callee's private handler capture the callback",
              dyn.value == 100 and evd.value == 100, f"{dyn.value} {evd.value}")
    rep.check("e4 lexical capability binding reaches the handler the callback closed over",
              lex.value == 1, repr(lex.value))
    out = run(ESCAPE_INNER, dispatch="lexical")
    rep.check("e5 an escaped capability fails when its handler has returned",
              out.kind == "capability-escaped", out.kind)
    out = run(ESCAPE_OUTER, dispatch="lexical")
    rep.check("e6 it fails even when an outer handler of the same label exists",
              out.kind == "capability-escaped", out.kind)
    out = run(ESCAPE_OUTER)
    rep.check("e7 dynamic dispatch silently rebinds the escaped perform outward",
              out.kind == "ok" and out.value == 7, f"{out.kind} {out.value!r}")
    out = run(ESCAPE_INNER)
    rep.check("e8 with no outer handler the escaped perform is unhandled",
              out.kind == "unhandled-effect", out.kind)

    crossing = ask_handler(Foreign(Do("ask", UNIT)), 5)
    inside = Foreign(ask_handler(Do("ask", UNIT), 5))
    for d in ("search", "evidence", "lexical"):
        out = run(crossing, dispatch=d)
        rep.facts.setdefault("foreign_barrier_detail", {})[d] = out.detail
        rep.check(f"f1 effect cannot cross a foreign frame ({d})",
                  out.kind == "unhandled-effect", out.kind)
        out = run(inside, dispatch=d)
        rep.check(f"f2 a handler installed above the foreign frame still works ({d})",
                  out.kind == "ok" and out.value == 5, f"{out.kind} {out.value!r}")
    errs = Checker({"ask": "1"}).check(crossing)
    rep.check("f3 the checker reports the foreign-frame crossing statically",
              any("foreign frame" in e for e in errs), "; ".join(errs))


def checks_algebra(rep: Report) -> None:
    bad = coeffect_scalar_axioms()
    rep.check("g1 {0,1,w} with (mul, add, 1, 0, <=) satisfies the coeffect-scalar axioms",
              not bad, "; ".join(bad[:3]))
    usage = {name: sorted(resumption_usage(body, "k")) for name, body in CLAUSES.items()}
    rep.facts["clause_usage"] = usage
    expect = {"drop": ["D"], "unwind": ["U"], "once": ["1"], "twice": ["W"],
              "once-or-drop": ["1", "D"], "once-or-unwind": ["1", "U"],
              "once-then-unwind": ["W"]}
    rep.check("g2 inferred resumption usage of each clause is as expected",
              usage == expect, str(usage))
    state_clauses = run_state(Lit(0), UNIT).f.clauses
    rep.check("g3 a resumption captured under a lambda is graded w (conservative)",
              all(resumption_usage(cl.body, cl.k) == frozenset({"W"})
                  for _, cl in state_clauses))


def main(argv: list[str]) -> int:
    rep = Report()
    listing: Optional[list] = [] if "--list" in argv else None
    checks_ordering(rep)
    checks_resources(rep)
    checks_family(rep, listing)
    checks_dispatch(rep)
    checks_algebra(rep)
    if "--json" in argv:
        print(json.dumps({"ok": rep.ok, "facts": rep.facts,
                          "checks": [{"name": n, "ok": ok, "detail": d}
                                     for n, ok, d in rep.results]},
                         indent=2, sort_keys=True, default=str))
        return 0 if rep.ok else 1
    if listing:
        print("\n".join(listing))
    for name, ok, detail in rep.results:
        print(f"[{'PASS' if ok else 'FAIL'}] {name}" + ("" if ok else f"  <- {detail}"))
    print("facts:")
    for key in sorted(rep.facts):
        print(f"  {key} = {rep.facts[key]}")
    passed = sum(1 for r in rep.results if r[1])
    print(f"RESULT: {'PASS' if rep.ok else 'FAIL'} ({passed}/{len(rep.results)} checks)")
    return 0 if rep.ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
