#!/usr/bin/env python3
"""Standalone executable probe for Choreographic EPP, MPST behavioral checking, and CALM/CRDT laws.

Implements and mechanically checks three core formal artifacts discussed in REPORT.md:
  1. Choreographic Endpoint Projection (EPP) with partial branch merge (join) and
     exact Knowledge-of-Choice (KoC) violation counterexamples, plus an exhaustive
     asynchronous FIFO interleaving simulator verifying 0 deadlocks and 0 orphan messages.
  2. Bounded Multiparty Session Types (MPST) local-type tuple verifier in the style of
     Scalas & Yoshida (POPL 2019 / mpstk), comparing synchronous vs. asynchronous FIFO
     semantics across safety, deadlock-freedom, weak liveness, and unconditional liveness,
     plus coinductive synchronous subtyping vs. asynchronous send-anticipation.
  3. Join-semilattice CRDT algebraic law verifier (idempotence, commutativity, associativity,
     monotonic order, and change-flag accuracy), CALM delivery-order confluence experiment
     (deadlock detection vs. distributed garbage collection), and mixed-version wire evolution
     (Protobuf unknown-field preservation vs. pre-3.5 dropping and closed session duality).

Requires Python 3.10+ and only the Python standard library. Exits 0 iff all checks pass.
"""

from __future__ import annotations

import itertools
from collections import deque
from dataclasses import dataclass
from typing import Any, Callable, Iterable


# =============================================================================
# PART 1: CHOREOGRAPHIC ENDPOINT PROJECTION (EPP), PARTIAL MERGE & FIFO SIM
# =============================================================================


class MergeError(Exception):
    """Raised when partial merge (⊔) fails for a role during Endpoint Projection."""

    def __init__(self, role: str, left: Endpoint, right: Endpoint, reason: str) -> None:
        self.role = role
        self.left = left
        self.right = right
        self.reason = reason
        super().__init__(
            f"Knowledge-of-Choice / merge violation at role {role!r}: {reason} "
            f"(left={left}, right={right})"
        )


# --- Global Choreography AST ---


class Chor:
    pass


@dataclass(frozen=True)
class CEnd(Chor):
    pass


@dataclass(frozen=True)
class CComm(Chor):
    sender: str
    receiver: str
    msg: str
    cont: Chor


@dataclass(frozen=True)
class CSelect(Chor):
    sender: str
    receiver: str
    label: str
    cont: Chor


@dataclass(frozen=True)
class CIf(Chor):
    decider: str
    cond: str
    then_b: Chor
    else_b: Chor


# --- Projected Local Endpoint AST ---


class Endpoint:
    pass


@dataclass(frozen=True)
class PEnd(Endpoint):
    def __str__(self) -> str:
        return "end"


@dataclass(frozen=True)
class PSend(Endpoint):
    to: str
    msg: str
    cont: Endpoint

    def __str__(self) -> str:
        return f"send({self.to}, {self.msg}); {self.cont}"


@dataclass(frozen=True)
class PRecv(Endpoint):
    frm: str
    msg: str
    cont: Endpoint

    def __str__(self) -> str:
        return f"recv({self.frm}, {self.msg}); {self.cont}"


@dataclass(frozen=True)
class PSel(Endpoint):
    to: str
    label: str
    cont: Endpoint

    def __str__(self) -> str:
        return f"sel({self.to}, {self.label}); {self.cont}"


@dataclass(frozen=True)
class PBranch(Endpoint):
    frm: str
    branches: tuple[tuple[str, Endpoint], ...]

    def as_dict(self) -> dict[str, Endpoint]:
        return dict(self.branches)

    def __str__(self) -> str:
        inner = ", ".join(f"{k} => {v}" for k, v in self.branches)
        return f"offer({self.frm}){{{inner}}}"


@dataclass(frozen=True)
class PIf(Endpoint):
    cond: str
    then_ep: Endpoint
    else_ep: Endpoint

    def __str__(self) -> str:
        return f"if({self.cond}) {{{self.then_ep}}} else {{{self.else_ep}}}"


def chor_roles(c: Chor) -> set[str]:
    if isinstance(c, CEnd):
        return set()
    if isinstance(c, (CComm, CSelect)):
        return {c.sender, c.receiver} | chor_roles(c.cont)
    if isinstance(c, CIf):
        return {c.decider} | chor_roles(c.then_b) | chor_roles(c.else_b)
    raise TypeError(f"Unknown Chor node: {c!r}")


def chor_conds(c: Chor) -> set[tuple[str, str]]:
    if isinstance(c, CEnd):
        return set()
    if isinstance(c, (CComm, CSelect)):
        return chor_conds(c.cont)
    if isinstance(c, CIf):
        return {(c.decider, c.cond)} | chor_conds(c.then_b) | chor_conds(c.else_b)
    raise TypeError(f"Unknown Chor node: {c!r}")


def merge_endpoints(role: str, e1: Endpoint, e2: Endpoint) -> Endpoint:
    """Partial merge operator (⊔) following Pirouette §5.2 & Choral StatementsMerger.

    Identical prefixes merge homomorphically; branching offers (`PBranch`) from the
    same sender union disjoint label sets and recursively merge overlapping labels.
    Any divergent send/receive/selection/termination at an uninformed role fails.
    """
    if isinstance(e1, PEnd) and isinstance(e2, PEnd):
        return PEnd()
    if isinstance(e1, PSend) and isinstance(e2, PSend):
        if e1.to == e2.to and e1.msg == e2.msg:
            return PSend(e1.to, e1.msg, merge_endpoints(role, e1.cont, e2.cont))
        raise MergeError(role, e1, e2, "divergent send target or payload")
    if isinstance(e1, PRecv) and isinstance(e2, PRecv):
        if e1.frm == e2.frm and e1.msg == e2.msg:
            return PRecv(e1.frm, e1.msg, merge_endpoints(role, e1.cont, e2.cont))
        raise MergeError(role, e1, e2, "divergent receive source or payload")
    if isinstance(e1, PSel) and isinstance(e2, PSel):
        if e1.to == e2.to and e1.label == e2.label:
            return PSel(e1.to, e1.label, merge_endpoints(role, e1.cont, e2.cont))
        raise MergeError(role, e1, e2, "divergent outgoing selection without prior notification")
    if isinstance(e1, PIf) and isinstance(e2, PIf):
        if e1.cond == e2.cond:
            return PIf(
                e1.cond,
                merge_endpoints(role, e1.then_ep, e2.then_ep),
                merge_endpoints(role, e1.else_ep, e2.else_ep),
            )
        raise MergeError(role, e1, e2, "divergent local conditional guard")
    if isinstance(e1, PBranch) and isinstance(e2, PBranch):
        if e1.frm != e2.frm:
            raise MergeError(role, e1, e2, f"branch offers from distinct senders {e1.frm!r} vs {e2.frm!r}")
        d1 = e1.as_dict()
        d2 = e2.as_dict()
        merged: dict[str, Endpoint] = {}
        for lbl in sorted(set(d1) | set(d2)):
            if lbl in d1 and lbl in d2:
                merged[lbl] = merge_endpoints(role, d1[lbl], d2[lbl])
            elif lbl in d1:
                merged[lbl] = d1[lbl]
            else:
                merged[lbl] = d2[lbl]
        return PBranch(e1.frm, tuple(merged.items()))
    raise MergeError(
        role,
        e1,
        e2,
        f"incompatible endpoint behaviors ({type(e1).__name__} vs {type(e2).__name__})",
    )


def project_role(c: Chor, role: str) -> Endpoint:
    """Project choreography `c` onto a single role `role`."""
    if isinstance(c, CEnd):
        return PEnd()
    if isinstance(c, CComm):
        if c.sender == c.receiver:
            raise ValueError(f"Self-communication disallowed at {c.sender!r}")
        cont = project_role(c.cont, role)
        if role == c.sender:
            return PSend(c.receiver, c.msg, cont)
        if role == c.receiver:
            return PRecv(c.sender, c.msg, cont)
        return cont
    if isinstance(c, CSelect):
        if c.sender == c.receiver:
            raise ValueError(f"Self-selection disallowed at {c.sender!r}")
        cont = project_role(c.cont, role)
        if role == c.sender:
            return PSel(c.receiver, c.label, cont)
        if role == c.receiver:
            return PBranch(c.sender, ((c.label, cont),))
        return cont
    if isinstance(c, CIf):
        ep_t = project_role(c.then_b, role)
        ep_e = project_role(c.else_b, role)
        if role == c.decider:
            return PIf(c.cond, ep_t, ep_e)
        return merge_endpoints(role, ep_t, ep_e)
    raise TypeError(f"Unknown Chor node: {c!r}")


def epp(c: Chor) -> dict[str, Endpoint]:
    """Full Endpoint Projection across all roles in `c`."""
    roles = sorted(chor_roles(c))
    return {r: project_role(c, r) for r in roles}


def simulate_fifo_network(
    endpoints: dict[str, Endpoint],
    valuation: dict[tuple[str, str], bool],
    max_queue_depth: int = 8,
) -> dict[str, int]:
    """Exhaustive BFS over all asynchronous per-pair FIFO interleavings.

    Returns metrics and raises AssertionError on any deadlock, message mismatch,
    orphan message at termination, or queue overflow.
    """
    roles = tuple(sorted(endpoints.keys()))
    init_eps = tuple(endpoints[r] for r in roles)
    role_idx = {r: i for i, r in enumerate(roles)}
    # Queues stored as canonical tuple of ((sender, receiver), tuple[tuple[kind, val], ...])
    init_state = (init_eps, ())

    visited: set[Any] = {init_state}
    queue = deque([init_state])
    terminal_states = 0
    transitions = 0

    while queue:
        eps, qs_tuple = queue.popleft()
        qs: dict[tuple[str, str], tuple[tuple[str, str], ...]] = dict(qs_tuple)
        next_states: list[Any] = []

        for i, r in enumerate(roles):
            ep = eps[i]
            if isinstance(ep, PEnd):
                continue
            elif isinstance(ep, PIf):
                branch = ep.then_ep if valuation[(r, ep.cond)] else ep.else_ep
                new_eps = eps[:i] + (branch,) + eps[i + 1 :]
                next_states.append((new_eps, qs_tuple))
            elif isinstance(ep, PSend):
                ch = (r, ep.to)
                q = qs.get(ch, ())
                if len(q) >= max_queue_depth:
                    raise AssertionError(f"FIFO queue overflow on {ch}")
                nqs = dict(qs)
                nqs[ch] = q + (("msg", ep.msg),)
                new_eps = eps[:i] + (ep.cont,) + eps[i + 1 :]
                next_states.append((new_eps, tuple(sorted(nqs.items()))))
            elif isinstance(ep, PSel):
                ch = (r, ep.to)
                q = qs.get(ch, ())
                if len(q) >= max_queue_depth:
                    raise AssertionError(f"FIFO queue overflow on {ch}")
                nqs = dict(qs)
                nqs[ch] = q + (("sel", ep.label),)
                new_eps = eps[:i] + (ep.cont,) + eps[i + 1 :]
                next_states.append((new_eps, tuple(sorted(nqs.items()))))
            elif isinstance(ep, PRecv):
                ch = (ep.frm, r)
                q = qs.get(ch, ())
                if q:
                    kind, val = q[0]
                    if kind != "msg" or val != ep.msg:
                        raise AssertionError(
                            f"Communication mismatch at {r}: expected msg {ep.msg!r} from {ep.frm}, got {(kind, val)}"
                        )
                    nqs = dict(qs)
                    if len(q) == 1:
                        del nqs[ch]
                    else:
                        nqs[ch] = q[1:]
                    new_eps = eps[:i] + (ep.cont,) + eps[i + 1 :]
                    next_states.append((new_eps, tuple(sorted(nqs.items()))))
            elif isinstance(ep, PBranch):
                ch = (ep.frm, r)
                q = qs.get(ch, ())
                if q:
                    kind, val = q[0]
                    bdict = ep.as_dict()
                    if kind != "sel" or val not in bdict:
                        raise AssertionError(
                            f"Selection mismatch at {r}: expected one of {sorted(bdict)} from {ep.frm}, got {(kind, val)}"
                        )
                    nqs = dict(qs)
                    if len(q) == 1:
                        del nqs[ch]
                    else:
                        nqs[ch] = q[1:]
                    new_eps = eps[:i] + (bdict[val],) + eps[i + 1 :]
                    next_states.append((new_eps, tuple(sorted(nqs.items()))))
            else:
                raise TypeError(f"Unknown Endpoint node: {ep!r}")

        if not next_states:
            # Terminal state: verify 0 deadlocks and 0 orphan messages
            if not all(isinstance(ep, PEnd) for ep in eps):
                stuck = {roles[i]: str(eps[i]) for i in range(len(roles)) if not isinstance(eps[i], PEnd)}
                raise AssertionError(f"Deadlock reached! Stuck roles: {stuck}, queues={qs}")
            if qs:
                raise AssertionError(f"Orphan messages left at termination: {qs}")
            terminal_states += 1
        else:
            for ns in next_states:
                transitions += 1
                if ns not in visited:
                    visited.add(ns)
                    queue.append(ns)

    return {
        "states": len(visited),
        "transitions": transitions,
        "terminal_states": terminal_states,
        "roles": len(role_idx),
    }


def verify_suite_a() -> dict[str, Any]:
    results: dict[str, Any] = {}

    # Case A1: Two-Buyer Protocol with Explicit Selection (valid)
    two_buyers = CComm(
        "B1",
        "S",
        "title",
        CComm(
            "S",
            "B1",
            "quote",
            CComm(
                "S",
                "B2",
                "quote",
                CComm(
                    "B1",
                    "B2",
                    "split",
                    CIf(
                        "B2",
                        "accepts",
                        CSelect(
                            "B2",
                            "S",
                            "ok",
                            CSelect(
                                "B2",
                                "B1",
                                "ok",
                                CComm("B2", "S", "address", CComm("S", "B2", "delivery_date", CEnd())),
                            ),
                        ),
                        CSelect("B2", "S", "quit", CSelect("B2", "B1", "quit", CEnd())),
                    ),
                ),
            ),
        ),
    )
    proj_tb = epp(two_buyers)
    assert isinstance(proj_tb["S"], PRecv)
    tb_runs = {}
    for val in (True, False):
        tb_runs[val] = simulate_fifo_network(proj_tb, {("B2", "accepts"): val})
    results["two_buyers_valid"] = {"projected_roles": sorted(proj_tb.keys()), "fifo_runs": tb_runs}

    # Case A2: Pirouette §5.2 prefix-shared merge before choice
    # if L1.e then L2.3 ~> L1; L1[L] ~> L2; L2.0 else L2.3 ~> L1; L1[R] ~> L2; L2.1
    pirouette_ex = CIf(
        "L1",
        "e",
        CComm("L2", "L1", "3", CSelect("L1", "L2", "L", CComm("L2", "L1", "res_0", CEnd()))),
        CComm("L2", "L1", "3", CSelect("L1", "L2", "R", CComm("L2", "L1", "res_1", CEnd()))),
    )
    proj_pir = epp(pirouette_ex)
    assert isinstance(proj_pir["L2"], PSend) and isinstance(proj_pir["L2"].cont, PBranch)
    pir_runs = {val: simulate_fifo_network(proj_pir, {("L1", "e"): val}) for val in (True, False)}
    results["pirouette_sec5_2_merge"] = {"L2_projection": str(proj_pir["L2"]), "fifo_runs": pir_runs}

    # Case A3: Unmerged Knowledge-of-Choice violation (Bob/Carol diverge without Alice informing them)
    bad_koc = CIf(
        "Alice",
        "cond",
        CComm("Bob", "Carol", "m1", CEnd()),
        CComm("Bob", "Carol", "m2", CEnd()),
    )
    koc_errors: dict[str, str] = {}
    for r in sorted(chor_roles(bad_koc)):
        try:
            project_role(bad_koc, r)
        except MergeError as exc:
            koc_errors[r] = exc.reason
    assert "Alice" not in koc_errors
    assert "Bob" in koc_errors and "Carol" in koc_errors
    results["koc_violation_3role"] = koc_errors

    # Case A4: Instrument-control unprojectable global protocol (Honda-Yoshida-Carbone JACM 2016 Ex. 3.10)
    bad_instr = CComm(
        "User",
        "Op",
        "privilege",
        CIf(
            "Op",
            "allow",
            CSelect(
                "Op",
                "User",
                "ok",
                CComm("User", "Instr", "move", CComm("Instr", "Op", "status", CEnd())),
            ),
            CSelect("Op", "User", "no", CEnd()),
        ),
    )
    instr_err: MergeError | None = None
    try:
        epp(bad_instr)
    except MergeError as exc:
        instr_err = exc
    assert instr_err is not None and instr_err.role == "Instr"
    results["instrument_control_unprojectable"] = {
        "failing_role": instr_err.role,
        "reason": instr_err.reason,
    }

    return results


# =============================================================================
# PART 2: SCALAS & YOSHIDA (POPL 2019) MPST LOCAL-TYPE EXPLORER & SUBTYPING
# =============================================================================


class LType:
    pass


@dataclass(frozen=True)
class LEnd(LType):
    def __str__(self) -> str:
        return "end"


@dataclass(frozen=True)
class LVar(LType):
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class LRec(LType):
    var: str
    body: LType

    def __str__(self) -> str:
        return f"μ({self.var}).{self.body}"


@dataclass(frozen=True)
class LSel(LType):
    to: str
    choices: tuple[tuple[str, str, LType], ...]  # (label, payload, cont)

    def __str__(self) -> str:
        inner = ", ".join(f"{l}({p}).{c}" for l, p, c in self.choices)
        return f"{self.to}⊕{{{inner}}}"


@dataclass(frozen=True)
class LBra(LType):
    frm: str
    choices: tuple[tuple[str, str, LType], ...]  # (label, payload, cont)

    def __str__(self) -> str:
        inner = ", ".join(f"{l}({p}).{c}" for l, p, c in self.choices)
        return f"{self.frm}&{{{inner}}}"


def lsubst(t: LType, var: str, repl: LType) -> LType:
    if isinstance(t, LEnd):
        return t
    if isinstance(t, LVar):
        return repl if t.name == var else t
    if isinstance(t, LRec):
        return t if t.var == var else LRec(t.var, lsubst(t.body, var, repl))
    if isinstance(t, LSel):
        return LSel(t.to, tuple((l, p, lsubst(c, var, repl)) for l, p, c in t.choices))
    if isinstance(t, LBra):
        return LBra(t.frm, tuple((l, p, lsubst(c, var, repl)) for l, p, c in t.choices))
    raise TypeError(t)


def lunfold(t: LType) -> LType:
    while isinstance(t, LRec):
        t = lsubst(t.body, t.var, t)
    return t


# --- Synchronous Subtyping (Gay & Hole 2005 / mpstk Subtyping.scala) ---


def sync_subtype(t1: LType, t2: LType, seen: frozenset[tuple[LType, LType]] = frozenset()) -> bool:
    """Coinductive synchronous session subtyping t1 <= t2 (outputs covariant, inputs contravariant)."""
    if (t1, t2) in seen:
        return True
    seen2 = seen | {(t1, t2)}
    if isinstance(t1, LRec):
        return sync_subtype(lsubst(t1.body, t1.var, t1), t2, seen2)
    if isinstance(t2, LRec):
        return sync_subtype(t1, lsubst(t2.body, t2.var, t2), seen2)
    if isinstance(t1, LEnd) and isinstance(t2, LEnd):
        return True
    if isinstance(t1, LSel) and isinstance(t2, LSel):
        # Channel-oriented Gay-Hole / mpstk Subtyping.scala convention:
        # Select(to, c1) <= Select(to, c2) iff c2.keys <= c1.keys
        # Branch(frm, c1) <= Branch(frm, c2) iff c1.keys <= c2.keys
        if t1.to != t2.to:
            return False
        d1 = {l: (p, c) for l, p, c in t1.choices}
        d2 = {l: (p, c) for l, p, c in t2.choices}
        if not set(d2).issubset(set(d1)):
            return False
        return all(d1[l][0] == d2[l][0] and sync_subtype(d1[l][1], d2[l][1], seen2) for l in d2)
    if isinstance(t1, LBra) and isinstance(t2, LBra):
        if t1.frm != t2.frm:
            return False
        d1 = {l: (p, c) for l, p, c in t1.choices}
        d2 = {l: (p, c) for l, p, c in t2.choices}
        if not set(d1).issubset(set(d2)):
            return False
        return all(d1[l][0] == d2[l][0] and sync_subtype(d1[l][1], d2[l][1], seen2) for l in d1)
    return False


# --- Bounded MPST Context LTS Explorer (Sync and Async FIFO) ---


@dataclass(frozen=True)
class MPSTReport:
    mode: str
    states: int
    transitions: int
    safe: bool
    deadlock_free: bool
    weak_live: bool
    fair_live_plus: bool
    strong_live_pp: bool
    truncated: bool
    witness: str


def explore_mpst_context(
    ctx: dict[str, LType],
    asynchronous: bool = False,
    queue_bound: int = 2,
    max_states: int = 500,
    unreliable_roles: frozenset[str] = frozenset(),
) -> MPSTReport:
    """Build LTS of typing context Γ and check Scalas-Yoshida behavioral properties.

    When `unreliable_roles` is non-empty (synchronous crash-stop mode, Barwell et al.
    CONCUR 2022), any active unreliable role may crash to `LStop` at any step; receivers
    blocked on a crashed sender must offer a `crash` branch label to avoid deadlock/error.
    """
    roles = tuple(sorted(ctx.keys()))
    init_state = (tuple(ctx[r] for r in roles), ())

    adj: dict[Any, list[tuple[tuple[str, ...], Any]]] = {}
    state_enabled_io: dict[Any, set[tuple[str, str, str]]] = {}
    visited: set[Any] = {init_state}
    work = deque([init_state])

    safe = True
    safety_witness = ""
    truncated = False
    edge_count = 0

    while work:
        st = work.popleft()
        types_t, qs_t = st
        unfolded = [lunfold(t) for t in types_t]
        qs: dict[tuple[str, str], tuple[tuple[str, str], ...]] = dict(qs_t)

        # Collect enabled I/O actions for liveness/deadlock checks
        enabled_io: set[tuple[str, str, str]] = set()
        for i, r in enumerate(roles):
            u = unfolded[i]
            if isinstance(u, LSel):
                enabled_io.add(("out", r, u.to))
            elif isinstance(u, LBra):
                enabled_io.add(("in", u.frm, r))
        state_enabled_io[st] = enabled_io

        edges: list[tuple[tuple[str, ...], Any]] = []

        if not asynchronous:
            # Synchronous semantics (mpstk + optional Barwell et al. crash-stop transitions)
            for i, p in enumerate(roles):
                up = unfolded[i]
                # Unreliable active role may crash to LVar("__STOP__")
                if p in unreliable_roles and not (isinstance(up, LEnd) or (isinstance(up, LVar) and up.name == "__STOP__")):
                    nt = list(types_t)
                    nt[i] = LVar("__STOP__")
                    edges.append((("crash", p, p, "stop"), (tuple(nt), ())))
                if isinstance(up, LSel):
                    q = up.to
                    j = roles.index(q)
                    uq = unfolded[j]
                    if isinstance(uq, LVar) and uq.name == "__STOP__":
                        # Sending to a crashed role drops the message and advances sender (Barwell et al. §2)
                        for lbl, _pay, cont_p in up.choices:
                            nt = list(types_t)
                            nt[i] = cont_p
                            edges.append((("sync", p, q, lbl), (tuple(nt), ())))
                    elif isinstance(uq, LBra) and uq.frm == p:
                        q_map = {l: (pay, cont) for l, pay, cont in uq.choices}
                        for lbl, pay, cont_p in up.choices:
                            if lbl not in q_map or q_map[lbl][0] != pay:
                                safe = False
                                if not safety_witness:
                                    safety_witness = f"sync mismatch {p}->{q}: label {lbl}({pay}) rejected by {uq}"
                            else:
                                cont_q = q_map[lbl][1]
                                nt = list(types_t)
                                nt[i] = cont_p
                                nt[j] = cont_q
                                edges.append((("sync", p, q, lbl), (tuple(nt), ())))
                elif isinstance(up, LBra):
                    q = up.frm
                    j = roles.index(q)
                    uq = unfolded[j]
                    if isinstance(uq, LVar) and uq.name == "__STOP__":
                        p_map = {l: (pay, cont) for l, pay, cont in up.choices}
                        if "crash" in p_map:
                            nt = list(types_t)
                            nt[i] = p_map["crash"][1]
                            edges.append((("sync", q, p, "crash"), (tuple(nt), ())))
                        else:
                            safe = False
                            if not safety_witness:
                                safety_witness = f"unhandled crash: {p} waiting on crashed {q} with no 'crash' branch"
        else:
            # Asynchronous FIFO semantics (unbounded channels approximated up to queue_bound)
            for i, r in enumerate(roles):
                ur = unfolded[i]
                if isinstance(ur, LBra):
                    ch = (ur.frm, r)
                    qbuf = qs.get(ch, ())
                    if qbuf:
                        lbl, pay = qbuf[0]
                        rmap = {l: (p, c) for l, p, c in ur.choices}
                        if lbl not in rmap or rmap[lbl][0] != pay:
                            safe = False
                            if not safety_witness:
                                safety_witness = f"async queue mismatch at {r} from {ur.frm}: head {(lbl, pay)} rejected by {ur}"
                        else:
                            nqs = dict(qs)
                            if len(qbuf) == 1:
                                del nqs[ch]
                            else:
                                nqs[ch] = qbuf[1:]
                            nt = list(types_t)
                            nt[i] = rmap[lbl][1]
                            ns = (tuple(nt), tuple(sorted(nqs.items())))
                            edges.append((("in", ur.frm, r, lbl), ns))
                elif isinstance(ur, LSel):
                    ch = (r, ur.to)
                    qbuf = qs.get(ch, ())
                    if len(qbuf) < queue_bound:
                        for lbl, pay, cont in ur.choices:
                            nqs = dict(qs)
                            nqs[ch] = qbuf + ((lbl, pay),)
                            nt = list(types_t)
                            nt[i] = cont
                            ns = (tuple(nt), tuple(sorted(nqs.items())))
                            edges.append((("out", r, ur.to, lbl), ns))
                    else:
                        truncated = True

        adj[st] = edges
        edge_count += len(edges)
        for _, ns in edges:
            if ns not in visited:
                if len(visited) >= max_states:
                    truncated = True
                    continue
                visited.add(ns)
                work.append(ns)

    # Deadlock-freedom: no terminal state has pending I/O or non-empty queues
    deadlock_free = True
    dl_witness = ""
    for st in visited:
        if not adj.get(st):
            if state_enabled_io[st] or st[1]:
                deadlock_free = False
                dl_witness = f"deadlock at enabled_io={sorted(state_enabled_io[st])}, queues={st[1]}"
                break

    def action_fires(edge_lbl: tuple[str, ...], io_req: tuple[str, str, str]) -> bool:
        kind, src, dst = io_req
        if edge_lbl[0] == "sync":
            return edge_lbl[1] == src and edge_lbl[2] == dst
        return edge_lbl[0] == kind and edge_lbl[1] == src and edge_lbl[2] == dst

    weak_live = True
    weak_witness = ""
    fair_live_plus = True
    fair_witness = ""
    strong_live_pp = True
    strong_witness = ""

    # Exact modal mu-calculus least fixed point (μ Y) checks matching mpstk liveness{,+,++}.mcf:
    # For each distinct io_req appearing in any reachable state:
    all_io_reqs = sorted({io for s in visited for io in state_enabled_io[s]})
    for io_req in all_io_reqs:
        # Compute Y_weak: states that can reach an action_fires edge along SOME path
        y_weak = {s for s in visited if any(action_fires(lbl, io_req) for lbl, _ in adj.get(s, []))}
        changed = True
        while changed:
            changed = False
            for s in visited:
                if s not in y_weak:
                    if any(nxt in y_weak for _, nxt in adj.get(s, [])):
                        y_weak.add(s)
                        changed = True

        # Compute Y_plus (liveness+.mcf): either fires immediately, OR exists sender role r3
        # that has >=1 sync transition AND ALL sync transitions initiated by r3 land in Y_plus.
        y_plus = {s for s in visited if any(action_fires(lbl, io_req) for lbl, _ in adj.get(s, []))}
        changed = True
        while changed:
            changed = False
            for s in visited:
                if s not in y_plus:
                    by_sender: dict[str, list[Any]] = {}
                    for lbl, nxt in adj.get(s, []):
                        if lbl[0] != "crash":
                            by_sender.setdefault(lbl[1], []).append(nxt)
                    if any(nxts and all(n in y_plus for n in nxts) for nxts in by_sender.values()):
                        y_plus.add(s)
                        changed = True

        # Compute Y_pp (liveness++.mcf): either fires immediately, OR has >=1 transition AND
        # ALL non-crash transitions land in Y_pp.
        y_pp = {s for s in visited if any(action_fires(lbl, io_req) for lbl, _ in adj.get(s, []))}
        changed = True
        while changed:
            changed = False
            for s in visited:
                if s not in y_pp:
                    non_crash = [nxt for lbl, nxt in adj.get(s, []) if lbl[0] != "crash"]
                    if non_crash and all(nxt in y_pp for nxt in non_crash):
                        y_pp.add(s)
                        changed = True

        for s in visited:
            if io_req in state_enabled_io[s]:
                if s not in y_weak:
                    weak_live = False
                    if not weak_witness:
                        weak_witness = f"not live: {io_req} cannot reach firing transition"
                if s not in y_plus:
                    fair_live_plus = False
                    if not fair_witness:
                        fair_witness = f"not live+: role choice can infinitely defer {io_req}"
                if s not in y_pp:
                    strong_live_pp = False
                    if not strong_witness:
                        strong_witness = f"not live++: unfair scheduling or cycle can defer {io_req}"

    witness = safety_witness or dl_witness or weak_witness or fair_witness or strong_witness or "all properties hold"
    return MPSTReport(
        mode="async_fifo" if asynchronous else ("crash_stop_sync" if unreliable_roles else "sync"),
        states=len(visited),
        transitions=edge_count,
        safe=safe,
        deadlock_free=deadlock_free,
        weak_live=weak_live,
        fair_live_plus=fair_live_plus,
        strong_live_pp=strong_live_pp,
        truncated=truncated,
        witness=witness,
    )


def verify_suite_b() -> dict[str, Any]:
    reports: dict[str, Any] = {}

    # B1: popl19-sec2.3.ctx — unsafe context
    ctx_unsafe = {
        "p": LSel("q", (("foo", "unit", LEnd()),)),
        "q": LBra("p", (("bar", "unit", LEnd()),)),
    }
    r_unsafe = explore_mpst_context(ctx_unsafe, asynchronous=False)
    assert not r_unsafe.safe
    reports["popl19_sec2_3_unsafe"] = r_unsafe.__dict__

    # B2: popl19-ex5.11-a.ctx — safe, deadlocked 3-way cycle
    ctx_cycle = {
        "p": LBra("q", (("m1", "u", LSel("r", (("m3", "u", LEnd()),))),)),
        "q": LBra("r", (("m2", "u", LSel("p", (("m1", "u", LEnd()),))),)),
        "r": LBra("p", (("m3", "u", LSel("q", (("m2", "u", LEnd()),))),)),
    }
    r_cycle_sync = explore_mpst_context(ctx_cycle, asynchronous=False)
    r_cycle_async = explore_mpst_context(ctx_cycle, asynchronous=True)
    assert r_cycle_sync.safe and not r_cycle_sync.deadlock_free
    assert r_cycle_async.safe and not r_cycle_async.deadlock_free
    reports["popl19_ex5_11_a_cycle"] = {"sync": r_cycle_sync.__dict__, "async": r_cycle_async.__dict__}

    # B3: popl19-sec7-m3.ctx — safe, DEADLOCKED synchronously, DEADLOCK-FREE & LIVE++ asynchronously!
    ctx_crossover = {
        "p": LSel("q", (("m1", "u", LBra("q", (("m2", "u", LEnd()),))),)),
        "q": LSel("p", (("m2", "u", LBra("p", (("m1", "u", LEnd()),))),)),
    }
    r_cross_sync = explore_mpst_context(ctx_crossover, asynchronous=False)
    r_cross_async = explore_mpst_context(ctx_crossover, asynchronous=True, queue_bound=2)
    assert r_cross_sync.safe and not r_cross_sync.deadlock_free
    assert r_cross_async.safe and r_cross_async.deadlock_free and r_cross_async.strong_live_pp
    reports["popl19_sec7_m3_sync_vs_async"] = {
        "sync": r_cross_sync.__dict__,
        "async": r_cross_async.__dict__,
    }

    # B4: popl19-ex5.11-b.ctx — safe & deadlock-free, NOT live (r permanently starved)
    ctx_starve = {
        "p": LRec("t", LSel("q", (("m1", "u", LVar("t")),))),
        "q": LRec("t", LBra("p", (("m1", "u", LVar("t")),))),
        "r": LBra("q", (("m2", "u", LEnd()),)),
    }
    r_starve = explore_mpst_context(ctx_starve, asynchronous=False)
    assert r_starve.safe and r_starve.deadlock_free and not r_starve.weak_live
    reports["popl19_ex5_11_b_starvation"] = r_starve.__dict__

    # B5: popl19-ex5.6.ctx — safe, deadlock-free, live, NOT live+, NOT live++ (unfair loop on m1)
    ctx_ex56 = {
        "p": LRec("t", LSel("q", (("m1", "u", LVar("t")), ("m2", "u", LEnd())))),
        "q": LRec("t", LBra("p", (("m1", "u", LVar("t")), ("m2", "u", LSel("r", (("m3", "u", LEnd()),)))))),
        "r": LBra("q", (("m3", "u", LEnd()),)),
    }
    r_ex56 = explore_mpst_context(ctx_ex56, asynchronous=False)
    assert r_ex56.safe and r_ex56.deadlock_free and r_ex56.weak_live and not r_ex56.fair_live_plus and not r_ex56.strong_live_pp
    reports["popl19_ex5_6_weak_vs_strong_live"] = r_ex56.__dict__

    # B6: popl19-ex5.7.ctx — safe, deadlock-free, live, live+, NOT live++ (independent loop r1<->r2)
    ctx_ex57 = {
        "p": LSel("q", (("m1", "u", LSel("q2", (("m2", "u", LEnd()),))),)),
        "q": LBra("p", (("m1", "u", LEnd()),)),
        "q2": LBra("p", (("m2", "u", LEnd()),)),
        "r1": LRec("t", LSel("r2", (("m2", "u", LVar("t")),))),
        "r2": LRec("t", LBra("r1", (("m2", "u", LVar("t")),))),
    }
    r_ex57 = explore_mpst_context(ctx_ex57, asynchronous=False)
    assert r_ex57.safe and r_ex57.deadlock_free and r_ex57.weak_live and r_ex57.fair_live_plus and not r_ex57.strong_live_pp
    reports["popl19_ex5_7_independent_loop"] = r_ex57.__dict__

    # B7: Instrument Control (Honda-Yoshida-Carbone JACM 2016 Ex. 3.10) — safe, DEADLOCKED on 'no' branch
    ctx_instr_bad = {
        "User": LSel(
            "Op",
            (
                (
                    "priv",
                    "int",
                    LBra(
                        "Op",
                        (
                            (
                                "ok",
                                "u",
                                LRec(
                                    "t",
                                    LSel(
                                        "Instr",
                                        (("move", "u", LVar("t")), ("quit", "u", LEnd())),
                                    ),
                                ),
                            ),
                            ("no", "u", LEnd()),
                        ),
                    ),
                ),
            ),
        ),
        "Op": LBra(
            "User",
            (
                (
                    "priv",
                    "int",
                    LSel(
                        "User",
                        (
                            ("ok", "u", LBra("Instr", (("status", "str", LEnd()),))),
                            ("no", "u", LEnd()),
                        ),
                    ),
                ),
            ),
        ),
        "Instr": LRec(
            "t",
            LBra(
                "User",
                (
                    ("move", "u", LVar("t")),
                    ("quit", "u", LSel("Op", (("status", "str", LEnd()),))),
                ),
            ),
        ),
    }
    r_instr = explore_mpst_context(ctx_instr_bad, asynchronous=False)
    assert r_instr.safe and not r_instr.deadlock_free
    reports["instrument_control_deadlock"] = r_instr.__dict__

    # B8: Coinductive Synchronous Subtyping vs Asynchronous Send-Anticipation
    # Channel-oriented Gay-Hole/mpstk: Select(more) <= Select(fewer); Branch(fewer) <= Branch(more)
    t_sel_wide = LSel("q", (("ok", "int", LEnd()), ("quit", "u", LEnd())))
    t_sel_narrow = LSel("q", (("ok", "int", LEnd()),))
    assert sync_subtype(t_sel_wide, t_sel_narrow) is True
    assert sync_subtype(t_sel_narrow, t_sel_wide) is False

    # Asynchronous send-before-receive anticipation:
    # T_opt = μt. q⊕a. q&b. t   vs   T_spec = μt. q&b. q⊕a. t
    t_opt = LRec("t", LSel("q", (("a", "u", LBra("q", (("b", "u", LVar("t")),))),)))
    t_spec = LRec("t", LBra("q", (("b", "u", LSel("q", (("a", "u", LVar("t")),))),)))
    assert sync_subtype(t_opt, t_spec) is False  # Rejected by decidable synchronous subtyping!
    # Yet composing T_opt with the exact dual of T_spec (q⊕b. q&a. t) is safe & deadlock-free under FIFO!
    t_spec_dual = LRec("t", LSel("p", (("b", "u", LBra("p", (("a", "u", LVar("t")),))),)))
    r_anticip_sync = explore_mpst_context({"p": t_opt, "q": t_spec_dual}, asynchronous=False)
    r_anticip_async = explore_mpst_context({"p": t_opt, "q": t_spec_dual}, asynchronous=True, queue_bound=2)
    assert not r_anticip_sync.deadlock_free
    assert r_anticip_async.safe and r_anticip_async.deadlock_free
    reports["sync_subtyping_vs_async_anticipation"] = {
        "sync_subtype_opt_le_spec": False,
        "sync_exec_deadlock_free": r_anticip_sync.deadlock_free,
        "async_fifo_safe": r_anticip_async.safe,
        "async_fifo_deadlock_free": r_anticip_async.deadlock_free,
    }

    # B9: Crash-Stop MPST (Barwell et al. CONCUR 2022) — DNS client p, unreliable server q, failover r
    # Without crash branch on p: safe when q is reliable, UNSAFE & DEADLOCKED when q can crash!
    dns_no_handler = {
        "p": LSel("q", (("req", "str", LBra("q", (("resp", "ip", LEnd()),))),)),
        "q": LBra("p", (("req", "str", LSel("p", (("resp", "ip", LEnd()),))),)),
    }
    r_dns_rel = explore_mpst_context(dns_no_handler, unreliable_roles=frozenset())
    r_dns_unrel_bad = explore_mpst_context(dns_no_handler, unreliable_roles=frozenset({"q"}))
    assert r_dns_rel.safe and r_dns_rel.deadlock_free
    assert not r_dns_unrel_bad.safe and not r_dns_unrel_bad.deadlock_free

    # With crash branch on p failing over to reliable r (and notifying r to stop on normal path):
    dns_with_failover = {
        "p": LSel(
            "q",
            (
                (
                    "req",
                    "str",
                    LBra(
                        "q",
                        (
                            ("resp", "ip", LSel("r", (("done", "u", LEnd()),))),
                            ("crash", "u", LSel("r", (("req", "str", LBra("r", (("resp", "ip", LEnd()),))),))),
                        ),
                    ),
                ),
            ),
        ),
        "q": LBra("p", (("req", "str", LSel("p", (("resp", "ip", LEnd()),))),)),
        "r": LBra(
            "p",
            (
                ("done", "u", LEnd()),
                ("req", "str", LSel("p", (("resp", "ip", LEnd()),))),
            ),
        ),
    }
    r_dns_failover = explore_mpst_context(dns_with_failover, unreliable_roles=frozenset({"q"}))
    assert r_dns_failover.safe and r_dns_failover.deadlock_free and r_dns_failover.strong_live_pp
    reports["crash_stop_dns"] = {
        "reliable_states": r_dns_rel.states,
        "unreliable_no_handler_safe": r_dns_unrel_bad.safe,
        "unreliable_failover_safe": r_dns_failover.safe,
        "unreliable_failover_df": r_dns_failover.deadlock_free,
        "unreliable_failover_states": r_dns_failover.states,
        "unreliable_failover_transitions": r_dns_failover.transitions,
    }

    return reports


# =============================================================================
# PART 3: SEMILATTICE CRDT VERIFIER, CALM CONFLUENCE & WIRE EVOLUTION
# =============================================================================


def check_join_semilattice(
    name: str,
    domain: list[Any],
    join_fn: Callable[[Any, Any], tuple[Any, bool]],
) -> dict[str, Any]:
    """Exhaustively check ACI laws, partial-order compatibility, and change-flag accuracy.

    `join_fn(x, y)` returns `(merged, changed)` where `changed` must be `merged != x`
    (matching Hydro `lattices::Merge::merge(&mut self, other) -> bool`).
    """
    violations: list[str] = []

    # 1. Idempotence & change-flag accuracy
    for x in domain:
        m, ch = join_fn(x, x)
        if m != x:
            violations.append(f"idempotence failed: {x} ⊔ {x} = {m}")
            break
        if ch is not False:
            violations.append(f"change-flag wrong on self-merge: {x} ⊔ {x} returned changed=True")
            break

    # 2. Commutativity & change-flag accuracy
    for x in domain:
        for y in domain:
            m_xy, ch_xy = join_fn(x, y)
            m_yx, ch_yx = join_fn(y, x)
            if ch_xy != (m_xy != x):
                violations.append(f"change-flag mismatch: ({x}, {y}) -> ({m_xy}, {ch_xy})")
                break
            if m_xy != m_yx:
                violations.append(f"commutativity failed: {x} ⊔ {y} = {m_xy} != {m_yx} = {y} ⊔ {x}")
                break
        if violations:
            break

    # 3. Associativity
    if not violations:
        for x in domain:
            for y in domain:
                m_xy, _ = join_fn(x, y)
                for z in domain:
                    lhs, _ = join_fn(m_xy, z)
                    m_yz, _ = join_fn(y, z)
                    rhs, _ = join_fn(x, m_yz)
                    if lhs != rhs:
                        violations.append(
                            f"associativity failed: ({x} ⊔ {y}) ⊔ {z} = {lhs} != {rhs} = {x} ⊔ ({y} ⊔ {z})"
                        )
                        break
                if violations:
                    break
            if violations:
                break

    # 4. Induced partial order anti-symmetry & transitivity (a <= b iff a ⊔ b == b)
    if not violations:
        def leq(a: Any, b: Any) -> bool:
            return join_fn(a, b)[0] == b

        for x in domain:
            for y in domain:
                if leq(x, y) and leq(y, x) and x != y:
                    violations.append(f"antisymmetry failed: {x} <= {y} and {y} <= {x}")
                    break
            if violations:
                break

    return {
        "name": name,
        "domain_size": len(domain),
        "valid_semilattice": not violations,
        "violations": violations,
    }


def verify_suite_c() -> dict[str, Any]:
    out: dict[str, Any] = {}

    # --- C1: Valid CRDT join-semilattices ---
    # 1. GSet (SetUnion over {0, 1, 2})
    gset_dom = [
        frozenset(s)
        for r in range(4)
        for s in itertools.combinations((0, 1, 2), r)
    ]

    def gset_join(a: frozenset[int], b: frozenset[int]) -> tuple[frozenset[int], bool]:
        m = a | b
        return m, m != a

    res_gset = check_join_semilattice("GSet (SetUnion)", gset_dom, gset_join)
    assert res_gset["valid_semilattice"]

    # 2. GCounter (2 replicas, counts in 0..3; pointwise Max)
    gcounter_dom = [(a, b) for a in range(4) for b in range(4)]

    def gcounter_join(x: tuple[int, int], y: tuple[int, int]) -> tuple[tuple[int, int], bool]:
        m = (max(x[0], y[0]), max(x[1], y[1]))
        return m, m != x

    res_gcounter = check_join_semilattice("GCounter (MapUnion<Replica, Max>)", gcounter_dom, gcounter_join)
    assert res_gcounter["valid_semilattice"]

    # 3. 2P-Set (Two-Phase Set with tombstones: monotonic pair (adds, removes))
    sub2 = [frozenset(s) for r in range(3) for s in itertools.combinations(("x", "y"), r)]
    twop_dom = [(a, r) for a in sub2 for r in sub2]

    def twop_join(
        x: tuple[frozenset[str], frozenset[str]],
        y: tuple[frozenset[str], frozenset[str]],
    ) -> tuple[tuple[frozenset[str], frozenset[str]], bool]:
        m = (x[0] | y[0], x[1] | y[1])
        return m, m != x

    res_2p = check_join_semilattice("2P-Set (SetUnionWithTombstones)", twop_dom, twop_join)
    assert res_2p["valid_semilattice"]

    # 4. OR-Set (Observed-Remove Set: (observed_tagged_adds, tombstoned_tags))
    # Elements tagged by (elem, uid); add-wins semantics over concurrent remove because
    # remove only tombstones tags already observed!
    tags = [("k", 1), ("k", 2)]
    tag_sets = [frozenset(s) for r in range(3) for s in itertools.combinations(tags, r)]
    orset_dom = [(a, t) for a in tag_sets for t in tag_sets if t.issubset(a)]

    def orset_join(
        x: tuple[frozenset[tuple[str, int]], frozenset[tuple[str, int]]],
        y: tuple[frozenset[tuple[str, int]], frozenset[tuple[str, int]]],
    ) -> tuple[tuple[frozenset[tuple[str, int]], frozenset[tuple[str, int]]], bool]:
        m = (x[0] | y[0], x[1] | y[1])
        return m, m != x

    res_orset = check_join_semilattice("OR-Set (Observed-Remove tagged lattice)", orset_dom, orset_join)
    assert res_orset["valid_semilattice"]
    # Verify add-wins: replica 1 adds ('k', 1) & removes ('k', 1); replica 2 concurrently adds ('k', 2)
    r1_state = (frozenset({("k", 1)}), frozenset({("k", 1)}))
    r2_state = (frozenset({("k", 2)}), frozenset())
    merged_or, _ = orset_join(r1_state, r2_state)
    live_elems = {elem for (elem, _uid) in (merged_or[0] - merged_or[1])}
    assert live_elems == {"k"}

    # --- C2: Buggy non-semilattice designs (must be caught with counterexamples) ---
    # Bug 1: LWW-Register with biased equal-timestamp tie-break (returns self on ts1 == ts2)
    lww_dom = [(ts, val) for ts in (0, 1, 2) for val in ("A", "B")]

    def buggy_lww_join(x: tuple[int, str], y: tuple[int, str]) -> tuple[tuple[int, str], bool]:
        m = y if y[0] > x[0] else x  # BUG: non-commutative when x[0] == y[0] and x[1] != y[1]!
        return m, m != x

    res_buggy_lww = check_join_semilattice("Buggy LWW-Register (biased tie-break)", lww_dom, buggy_lww_join)
    assert not res_buggy_lww["valid_semilattice"]
    assert any("commutativity failed" in v for v in res_buggy_lww["violations"])

    # Bug 2: Fixed LWW-Register with deterministic total tie-break on (ts, replica_id/val)
    def fixed_lww_join(x: tuple[int, str], y: tuple[int, str]) -> tuple[tuple[int, str], bool]:
        m = max(x, y)
        return m, m != x

    res_fixed_lww = check_join_semilattice("Fixed LWW-Register (total tie-break)", lww_dom, fixed_lww_join)
    assert res_fixed_lww["valid_semilattice"]

    # Bug 3: Integer midpoint/average merge (idempotent & commutative, NOT associative!)
    avg_dom = [0, 2, 4, 8]

    def buggy_avg_join(x: int, y: int) -> tuple[int, bool]:
        m = (x + y) // 2
        return m, m != x

    res_buggy_avg = check_join_semilattice("Buggy Average Merge", avg_dom, buggy_avg_join)
    assert not res_buggy_avg["valid_semilattice"]
    assert any("associativity failed" in v for v in res_buggy_avg["violations"])

    out["semilattices"] = {
        "valid": [res_gset, res_gcounter, res_2p, res_orset, res_fixed_lww],
        "rejected_bugs": [res_buggy_lww, res_buggy_avg],
    }

    # --- C3: CALM Monotonicity vs Non-Monotonicity (Hellerstein & Alvaro §1.3) ---
    # 3-partition distributed graph: edges arrive asynchronously in arbitrary order.
    # (a) Distributed Deadlock Detection (cycle existence) is MONOTONIC: once a cycle is
    #     observed in any prefix of arriving edges, no future edge can retract it!
    # (b) Distributed Garbage Collection (unreachability from root) is NON-MONOTONIC:
    #     evaluating reachability before a delayed remote edge arrives falsely marks a
    #     live object as garbage and reclaims it!
    edges = [("T1", "T2"), ("T2", "T3"), ("T3", "T1")]

    def has_cycle(edge_set: Iterable[tuple[str, str]]) -> bool:
        adj_g: dict[str, list[str]] = {}
        for u, v in edge_set:
            adj_g.setdefault(u, []).append(v)
        for start in adj_g:
            seen: set[str] = set()
            stack = list(adj_g.get(start, []))
            while stack:
                n = stack.pop()
                if n == start:
                    return True
                if n not in seen:
                    seen.add(n)
                    stack.extend(adj_g.get(n, []))
        return False

    deadlock_false_positives = 0
    deadlock_final_outcomes = set()
    for perm in itertools.permutations(edges):
        acc: list[tuple[str, str]] = []
        emitted_deadlock = False
        for e in perm:
            acc.append(e)
            if has_cycle(acc):
                emitted_deadlock = True
                # Check if final full graph indeed has a cycle (no retraction ever needed)
                if not has_cycle(edges):
                    deadlock_false_positives += 1
        deadlock_final_outcomes.add(emitted_deadlock)
    assert deadlock_false_positives == 0 and deadlock_final_outcomes == {True}

    # Distributed GC: Root -> A -> B; object B is live, but edge (A, B) arrives asynchronously!
    gc_edges = [("Root", "A"), ("A", "B")]
    all_objs = {"A", "B"}

    def unreachable_from_root(edge_set: Iterable[tuple[str, str]]) -> frozenset[str]:
        adj_g: dict[str, list[str]] = {}
        for u, v in edge_set:
            adj_g.setdefault(u, []).append(v)
        seen = {"Root"}
        stack = ["Root"]
        while stack:
            n = stack.pop()
            for nxt in adj_g.get(n, []):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return frozenset(all_objs - seen)

    # Without coordination barrier, inspecting intermediate state after only ("Root", "A") arrives
    # falsely concludes "B" is unreachable and would reclaim a live object!
    premature_gc_reclamations = 0
    for perm in itertools.permutations(gc_edges):
        # Partial snapshot after 1st message arrives (before 2nd remote edge arrives)
        partial_garbage = unreachable_from_root(perm[:1])
        true_garbage = unreachable_from_root(gc_edges)
        if partial_garbage - true_garbage:
            premature_gc_reclamations += 1
    assert premature_gc_reclamations == 2  # Both delivery orders have false GC on partial prefix!
    out["calm_confluence"] = {
        "deadlock_detection_permutations": 6,
        "deadlock_false_positives": deadlock_false_positives,
        "gc_permutations_with_premature_reclamation_without_barrier": premature_gc_reclamations,
    }

    # --- C4: Rolling-Upgrade Wire Evolution (Protobuf Unknown Fields vs Closed Session Duality) ---
    # Wire format: list of (field_num: int, raw_bytes: bytes)
    v2_wire = [(1, b"order-42"), (2, b"100"), (3, b"sig-v2-hmac")]
    v1_known_fields = {1, 2}

    def proxy_v1_proto3_pre_3_5(wire: list[tuple[int, bytes]]) -> list[tuple[int, bytes]]:
        # Drops unknown fields (pre-3.5 proto3 behavior)
        return [(fn, val) for fn, val in wire if fn in v1_known_fields]

    def proxy_v1_proto_preserve(wire: list[tuple[int, bytes]]) -> list[tuple[int, bytes]]:
        # Preserves unknown fields in unknown-field set and re-emits on serialization (proto2 & proto3 >= 3.5)
        known = [(fn, val) for fn, val in wire if fn in v1_known_fields]
        unknown = [(fn, val) for fn, val in wire if fn not in v1_known_fields]
        return known + unknown

    dropped_out = proxy_v1_proto3_pre_3_5(v2_wire)
    preserved_out = proxy_v1_proto_preserve(v2_wire)
    assert dict(dropped_out).get(3) is None  # Silent data loss!
    assert dict(preserved_out).get(3) == b"sig-v2-hmac"  # Lossless round-trip!
    out["rolling_upgrade_wire"] = {
        "proto3_pre_3_5_dropped_field_3": dict(dropped_out).get(3) is None,
        "proto_preserve_roundtrip_intact": preserved_out == v2_wire,
    }

    return out


def main() -> int:
    a = verify_suite_a()
    b = verify_suite_b()
    c = verify_suite_c()

    print("[PASS] Suite A (Choreographic EPP + Partial Merge + Async FIFO Sim):")
    print(f"  - Two-Buyers projected roles={a['two_buyers_valid']['projected_roles']}, "
          f"FIFO states(T/F)={a['two_buyers_valid']['fifo_runs'][True]['states']}/"
          f"{a['two_buyers_valid']['fifo_runs'][False]['states']} (0 deadlocks, 0 orphans)")
    print(f"  - Pirouette §5.2 merged L2: {a['pirouette_sec5_2_merge']['L2_projection']}")
    print(f"  - Unmerged 3-role KoC rejected at roles={sorted(a['koc_violation_3role'].keys())}")
    print(f"  - Instrument-Control unprojectable rejected at role={a['instrument_control_unprojectable']['failing_role']!r}")

    print("[PASS] Suite B (Scalas-Yoshida MPST Explorer + Subtyping):")
    print(f"  - popl19-sec2.3: safe={b['popl19_sec2_3_unsafe']['safe']}")
    print(f"  - popl19-ex5.11-a (cycle): sync_df={b['popl19_ex5_11_a_cycle']['sync']['deadlock_free']}, "
          f"async_df={b['popl19_ex5_11_a_cycle']['async']['deadlock_free']}")
    print(f"  - popl19-sec7-m3 (crossover): sync_df={b['popl19_sec7_m3_sync_vs_async']['sync']['deadlock_free']}, "
          f"async_df={b['popl19_sec7_m3_sync_vs_async']['async']['deadlock_free']}, "
          f"async_live++={b['popl19_sec7_m3_sync_vs_async']['async']['strong_live_pp']}")
    print(f"  - popl19-ex5.11-b (starvation): df={b['popl19_ex5_11_b_starvation']['deadlock_free']}, "
          f"weak_live={b['popl19_ex5_11_b_starvation']['weak_live']}")
    print(f"  - popl19-ex5.6 (unfair choice): live={b['popl19_ex5_6_weak_vs_strong_live']['weak_live']}, "
          f"live+={b['popl19_ex5_6_weak_vs_strong_live']['fair_live_plus']}, "
          f"live++={b['popl19_ex5_6_weak_vs_strong_live']['strong_live_pp']}")
    print(f"  - popl19-ex5.7 (indep loop): live={b['popl19_ex5_7_independent_loop']['weak_live']}, "
          f"live+={b['popl19_ex5_7_independent_loop']['fair_live_plus']}, "
          f"live++={b['popl19_ex5_7_independent_loop']['strong_live_pp']}")
    print(f"  - instrument-control.ctx: safe={b['instrument_control_deadlock']['safe']}, "
          f"df={b['instrument_control_deadlock']['deadlock_free']}")
    print(f"  - sync subtyping vs async anticipation: "
          f"sync_sub={b['sync_subtyping_vs_async_anticipation']['sync_subtype_opt_le_spec']}, "
          f"async_fifo_df={b['sync_subtyping_vs_async_anticipation']['async_fifo_deadlock_free']}")
    print(f"  - crash-stop DNS (Barwell et al.): rel_states={b['crash_stop_dns']['reliable_states']}, "
          f"no_handler_safe={b['crash_stop_dns']['unreliable_no_handler_safe']}, "
          f"failover_safe={b['crash_stop_dns']['unreliable_failover_safe']} "
          f"(states={b['crash_stop_dns']['unreliable_failover_states']}, "
          f"transitions={b['crash_stop_dns']['unreliable_failover_transitions']})")

    print("[PASS] Suite C (Semilattice CRDT Verifier + CALM Confluence + Rolling-Upgrade Wire):")
    print(f"  - Valid join-semilattices verified: {[x['name'] for x in c['semilattices']['valid']]}")
    print(f"  - Buggy merges caught: {[x['name'] + ' -> ' + x['violations'][0] for x in c['semilattices']['rejected_bugs']]}")
    print(f"  - CALM confluence: deadlock_false_positives={c['calm_confluence']['deadlock_false_positives']}, "
          f"uncoordinated_gc_corruptions={c['calm_confluence']['gc_permutations_with_premature_reclamation_without_barrier']}/2")
    print(f"  - Rolling-upgrade wire: pre3.5_dropped_f3={c['rolling_upgrade_wire']['proto3_pre_3_5_dropped_field_3']}, "
          f"preserve_roundtrip={c['rolling_upgrade_wire']['proto_preserve_roundtrip_intact']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
