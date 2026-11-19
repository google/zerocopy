#!/usr/bin/env python3
"""Standalone executable semantic and type-system witnesses for HDL design.

Implements self-contained Python 3.10+ (stdlib-only) checkers demonstrating four
foundational semantic mechanisms examined in the accompanying reference report:

1. IEEE 1800-2023 Clause 4 & Clause 12.4 SystemVerilog anomalies:
   (a) Stratified event-queue nondeterminism for blocking ('=') vs. deterministic
       separation for nonblocking ('<=') assignments across concurrent always blocks.
   (b) Four-valued (0/1/X/Z) X-optimism divergence between IEEE 1800-2023 Section 12.4
       if-else simulation, Section 11.4.11 ternary evaluation, Kleene three-valued
       pessimistic propagation, and synthesis don't-care concretization.
2. Filament-style Presburger linear-interval & initiation-interval (II) typechecking
   (modeling cucapra/filament IntervalCheck constraints):
   - Well-formed ranges (start < end) and positive event delays (II > 0)
   - Bundle availability <= event recurrence delay
   - Port connection containment (src.start <= dst.start and src.end >= dst.end)
   - Event recurrence binding (caller_II >= callee_II)
   - Shared-instance modular disjointness (catching structural double-booking and
     wrap-around modulo-II collisions as well as 1-cycle pipeline wire skews).
3. Koika intra-cycle Ephemeral History Register (EHR) conflict matrix and
   One-Rule-at-a-Time (ORAAT) serializability checker (modeling mit-plv/koika
   coq/Logs.v, coq/TypedSemantics.v, and coq/OneRuleAtATime.v):
   - Exhaustive 16-entry pairwise (P0/P1 x Read/Write) conflict matrix verification
   - Dynamic rule commit/abort evaluation with intra-cycle W0 -> R1 forwarding
   - Exhaustive ORAAT equivalence verification across schedules and initial states.
4. Dahlia time-sensitive affine SRAM bank-port checker (modeling cucapra/dahlia
   AffineCheck.scala):
   - Conflict-free unrolling across banked arrays vs. bank-conflict rejection
   - Logical step capability refresh across sequential barriers ('---').
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import itertools
import sys
from typing import Callable


# =============================================================================
# Part 1: IEEE 1800-2023 Stratified Event Queue & 4-Valued X-Optimism Witnesses
# =============================================================================


class Logic4(Enum):
    L0 = "0"
    L1 = "1"
    X = "X"
    Z = "Z"

    def __str__(self) -> str:
        return self.value


def sv_if_cond_is_true(cond: Logic4) -> bool:
    """IEEE 1800-2023 Section 12.4: true iff nonzero known value (1'b1)."""
    return cond is Logic4.L1


def sv_eval_if_else(sel: Logic4, then_val: Logic4, else_val: Logic4) -> Logic4:
    """IEEE 1800-2023 Section 12.4 X-optimistic if-else evaluation."""
    return then_val if sv_if_cond_is_true(sel) else else_val


def sv_eval_ternary(sel: Logic4, then_val: Logic4, else_val: Logic4) -> Logic4:
    """IEEE 1800-2023 Section 11.4.11 conditional operator (?:) evaluation."""
    if sel is Logic4.L1:
        return then_val
    if sel is Logic4.L0:
        return else_val
    # Ambiguous condition (X or Z): bitwise optimistic merge of both branches
    if then_val == else_val and then_val in (Logic4.L0, Logic4.L1):
        return then_val
    return Logic4.X


def kleene_pessimistic_mux(sel: Logic4, then_val: Logic4, else_val: Logic4) -> Logic4:
    """Pessimistic 3-valued (Kleene / Xprop tmerge) semantics over all concrete bits."""
    def concretize(v: Logic4) -> tuple[Logic4, ...]:
        if v in (Logic4.L0, Logic4.L1):
            return (v,)
        return (Logic4.L0, Logic4.L1)

    outcomes = {
        t if s is Logic4.L1 else e
        for s in concretize(sel)
        for t in concretize(then_val)
        for e in concretize(else_val)
    }
    if len(outcomes) == 1:
        return next(iter(outcomes))
    return Logic4.X


def simulate_shift_register_blocking(
    d_in: int, q1_init: int, q2_init: int, order: tuple[str, str]
) -> tuple[int, int]:
    """Simulate two posedge-triggered always blocks using blocking '=' in Active."""
    state = {"d": d_in, "q1": q1_init, "q2": q2_init}
    for block in order:
        if block == "B1":
            state["q1"] = state["d"]
        elif block == "B2":
            state["q2"] = state["q1"]
        else:
            raise ValueError(f"unknown block: {block}")
    return (state["q1"], state["q2"])


def simulate_shift_register_nonblocking(
    d_in: int, q1_init: int, q2_init: int, order: tuple[str, str]
) -> tuple[int, int]:
    """Simulate two posedge-triggered always blocks using nonblocking '<=' (Active + NBA)."""
    state = {"d": d_in, "q1": q1_init, "q2": q2_init}
    nba_queue: list[tuple[str, int]] = []
    # Active region: evaluate RHS in arbitrary legal order, enqueue LHS updates in NBA
    for block in order:
        if block == "B1":
            nba_queue.append(("q1", state["d"]))
        elif block == "B2":
            nba_queue.append(("q2", state["q1"]))
        else:
            raise ValueError(f"unknown block: {block}")
    # NBA region: commit deferred LHS updates
    for reg, val in nba_queue:
        state[reg] = val
    return (state["q1"], state["q2"])


def verify_systemverilog_anomalies() -> dict[str, str]:
    # (1a) Blocking vs. nonblocking event-queue race witness
    d_in, q1_0, q2_0 = 1, 0, 0
    blk_12 = simulate_shift_register_blocking(d_in, q1_0, q2_0, ("B1", "B2"))
    blk_21 = simulate_shift_register_blocking(d_in, q1_0, q2_0, ("B2", "B1"))
    assert blk_12 == (1, 1), f"expected collapsed shift (1, 1), got {blk_12}"
    assert blk_21 == (1, 0), f"expected 2-stage shift (1, 0), got {blk_21}"
    assert blk_12 != blk_21, "blocking race must exhibit schedule dependence"

    nba_12 = simulate_shift_register_nonblocking(d_in, q1_0, q2_0, ("B1", "B2"))
    nba_21 = simulate_shift_register_nonblocking(d_in, q1_0, q2_0, ("B2", "B1"))
    assert nba_12 == nba_21 == (1, 0), f"NBA must be order-invariant, got {nba_12}, {nba_21}"

    # (1b) Four-valued X-optimism simulation-vs-synthesis divergence witness
    sel = Logic4.X
    a, b = Logic4.L1, Logic4.L0
    sim_if = sv_eval_if_else(sel, a, b)
    sim_ternary = sv_eval_ternary(sel, a, b)
    kleene_val = kleene_pessimistic_mux(sel, a, b)
    # Gate-level / synthesis concretization when uninitialized sel powers up to 1'b1
    # (or synthesis exploits don't-care freedom to choose sel=1)
    synth_sel_1 = sv_eval_if_else(Logic4.L1, a, b)
    synth_sel_0 = sv_eval_if_else(Logic4.L0, a, b)

    assert sim_if is Logic4.L0, "IEEE 1800-2023 §12.4 if(1'bx) must take else branch (0)"
    assert sim_ternary is Logic4.X, "IEEE 1800-2023 §11.4.11 (1'bx ? 1 : 0) must yield X"
    assert kleene_val is Logic4.X, "Kleene pessimistic join must propagate X"
    assert synth_sel_1 is Logic4.L1 and synth_sel_0 is Logic4.L0
    assert sim_if != synth_sel_1, "simulation (0) must diverge from sel=1 silicon (1)"

    # Also verify equal-branch agreement: if (1'bx) y=1 else y=1 -> all models agree on 1
    assert sv_eval_if_else(Logic4.X, Logic4.L1, Logic4.L1) is Logic4.L1
    assert sv_eval_ternary(Logic4.X, Logic4.L1, Logic4.L1) is Logic4.L1
    assert kleene_pessimistic_mux(Logic4.X, Logic4.L1, Logic4.L1) is Logic4.L1

    return {
        "blocking_race": f"order(B1,B2)={blk_12} != order(B2,B1)={blk_21}",
        "nba_confluent": f"order(B1,B2)=order(B2,B1)={nba_12}",
        "x_divergence": (
            f"if(X,1,0)={sim_if} vs ternary(X,1,0)={sim_ternary} vs "
            f"kleene={kleene_val} vs synth(sel=1)={synth_sel_1}"
        ),
    }


# =============================================================================
# Part 2: Filament-Style Presburger Timeline & II Pipeline Typechecker
# =============================================================================


@dataclass(frozen=True)
class TimeExpr:
    """Affine Presburger time expression G + offset relative to event G."""
    event: str
    offset: int

    def shift(self, delta: int) -> TimeExpr:
        return TimeExpr(self.event, self.offset + delta)

    def __str__(self) -> str:
        return f"{self.event}+{self.offset}" if self.offset else self.event


@dataclass(frozen=True)
class Interval:
    """Half-open availability window @[start, end) in clock cycles."""
    start: TimeExpr
    end: TimeExpr

    def width(self) -> int:
        if self.start.event != self.end.event:
            raise ValueError("cross-event interval width requires explicit relation")
        return self.end.offset - self.start.offset

    def __str__(self) -> str:
        return f"@[{self.start}, {self.end}]"


@dataclass(frozen=True)
class ComponentSig:
    """Filament component timing interface."""
    name: str
    event: str
    ii: int  # Initiation interval (minimum recurrence delay L > 0)
    inputs: dict[str, Interval]
    outputs: dict[str, Interval]


@dataclass(frozen=True)
class InstanceDecl:
    inst_name: str
    sig: ComponentSig


@dataclass(frozen=True)
class InvokeDecl:
    inv_name: str
    inst_name: str
    start_time: TimeExpr  # Event argument binding callee's event to caller's G + k


@dataclass(frozen=True)
class WireConn:
    src_label: str
    src_interval: Interval
    dst_label: str
    dst_interval: Interval


@dataclass
class ComponentDef:
    sig: ComponentSig
    instances: list[InstanceDecl] = field(default_factory=list)
    invocations: list[InvokeDecl] = field(default_factory=list)
    connections: list[WireConn] = field(default_factory=list)


def check_filament_component(comp: ComponentDef) -> list[str]:
    """Verify Filament IntervalCheck Presburger obligations; return error list."""
    errors: list[str] = []
    ev_name = comp.sig.event
    caller_ii = comp.sig.ii

    # 1. delay_wf: event delay (II) must be strictly positive
    if caller_ii <= 0:
        errors.append(f"{comp.sig.name}: event {ev_name} delay II={caller_ii} must be > 0")

    # 2. range_wf & bundle availability <= event delay for interface ports
    for port_name, rng in list(comp.sig.inputs.items()) + list(comp.sig.outputs.items()):
        if rng.start.event != ev_name or rng.end.event != ev_name:
            errors.append(f"{comp.sig.name}.{port_name}: unknown event in {rng}")
            continue
        if not (rng.end.offset > rng.start.offset):
            errors.append(f"{comp.sig.name}.{port_name}: malformed interval {rng} (end <= start)")
        if rng.width() > caller_ii:
            errors.append(
                f"{comp.sig.name}.{port_name}: availability width {rng.width()} exceeds event delay II={caller_ii}"
            )

    inst_map = {inst.inst_name: inst.sig for inst in comp.instances}
    inv_by_inst: dict[str, list[InvokeDecl]] = {}

    # 3. event_binding: caller event delay >= callee event delay (II_caller >= II_callee)
    for inv in comp.invocations:
        if inv.inst_name not in inst_map:
            errors.append(f"{comp.sig.name}: invoke {inv.inv_name} references unknown instance {inv.inst_name}")
            continue
        callee = inst_map[inv.inst_name]
        if inv.start_time.event != ev_name:
            errors.append(f"{comp.sig.name}: invoke {inv.inv_name} uses unknown event {inv.start_time.event}")
            continue
        if caller_ii < callee.ii:
            errors.append(
                f"{comp.sig.name}: invoke {inv.inv_name} triggers every {caller_ii} cycles, "
                f"violating callee {callee.name} delay II={callee.ii}"
            )
        inv_by_inst.setdefault(inv.inst_name, []).append(inv)

    # 4. Shared hardware instance modular disjointness (structural hazard check):
    # For any two invocations of the same shared instance at G + o1 and G + o2,
    # their busy windows [o1 + k*II_caller, o1 + k*II_caller + II_callee) and
    # [o2 + m*II_caller, o2 + m*II_caller + II_callee) must be disjoint for all integers k, m.
    # By Presburger arithmetic modulo II_caller, this holds iff for all distinct i, j:
    #   ((o_j - o_i) mod II_caller) >= II_callee  AND  ((o_i - o_j) mod II_caller) >= II_callee
    # (and total busy demand len(invs) * II_callee <= II_caller).
    for inst_name, invs in inv_by_inst.items():
        callee = inst_map[inst_name]
        for inv_a, inv_b in itertools.combinations(invs, 2):
            oa = inv_a.start_time.offset
            ob = inv_b.start_time.offset
            dist_ab = (ob - oa) % caller_ii
            dist_ba = (oa - ob) % caller_ii
            if dist_ab < callee.ii or dist_ba < callee.ii:
                errors.append(
                    f"{comp.sig.name}: structural double-booking on shared instance '{inst_name}' "
                    f"(II={callee.ii}) between {inv_a.inv_name}@{inv_a.start_time} and "
                    f"{inv_b.inv_name}@{inv_b.start_time} under caller II={caller_ii} "
                    f"(cyclic gaps {dist_ab}, {dist_ba} < {callee.ii})"
                )

    # 5. connect containment: src.start <= dst.start and src.end >= dst.end (for same event G)
    for conn in comp.connections:
        s, d = conn.src_interval, conn.dst_interval
        if s.start.event != d.start.event or s.end.event != d.end.event:
            errors.append(f"{comp.sig.name}: cross-event wire {conn.src_label} -> {conn.dst_label}")
            continue
        if not (s.start.offset <= d.start.offset and s.end.offset >= d.end.offset):
            errors.append(
                f"{comp.sig.name}: timeline skew on {conn.src_label} {s} -> {conn.dst_label} {d} "
                f"(source must contain destination interval)"
            )

    return errors


def verify_filament_timelines() -> dict[str, str]:
    mult_ii1 = ComponentSig(
        name="PipeMult_L3_II1",
        event="G",
        ii=1,
        inputs={"a": Interval(TimeExpr("G", 0), TimeExpr("G", 1)), "b": Interval(TimeExpr("G", 0), TimeExpr("G", 1))},
        outputs={"out": Interval(TimeExpr("G", 3), TimeExpr("G", 4))},
    )
    add_ii1 = ComponentSig(
        name="PipeAdd_L1_II1",
        event="G",
        ii=1,
        inputs={"x": Interval(TimeExpr("G", 0), TimeExpr("G", 1)), "y": Interval(TimeExpr("G", 0), TimeExpr("G", 1))},
        outputs={"out": Interval(TimeExpr("G", 1), TimeExpr("G", 2))},
    )
    mult_ii2 = ComponentSig(
        name="SharedMult_L3_II2",
        event="G",
        ii=2,
        inputs={"a": Interval(TimeExpr("G", 0), TimeExpr("G", 1)), "b": Interval(TimeExpr("G", 0), TimeExpr("G", 1))},
        outputs={"out": Interval(TimeExpr("G", 3), TimeExpr("G", 4))},
    )

    # Case 2.1: Valid aligned pipelined MAC (delay register shifts c by 3 cycles to @[G+3, G+4])
    valid_mac = ComponentDef(
        sig=ComponentSig(
            name="ValidMAC",
            event="G",
            ii=1,
            inputs={
                "a": Interval(TimeExpr("G", 0), TimeExpr("G", 1)),
                "b": Interval(TimeExpr("G", 0), TimeExpr("G", 1)),
                "c": Interval(TimeExpr("G", 0), TimeExpr("G", 1)),
            },
            outputs={"out": Interval(TimeExpr("G", 4), TimeExpr("G", 5))},
        ),
        instances=[InstanceDecl("m", mult_ii1), InstanceDecl("ad", add_ii1)],
        invocations=[InvokeDecl("m0", "m", TimeExpr("G", 0)), InvokeDecl("a0", "ad", TimeExpr("G", 3))],
        connections=[
            WireConn("m0.out", Interval(TimeExpr("G", 3), TimeExpr("G", 4)), "a0.x", Interval(TimeExpr("G", 3), TimeExpr("G", 4))),
            WireConn("c_reg3", Interval(TimeExpr("G", 3), TimeExpr("G", 4)), "a0.y", Interval(TimeExpr("G", 3), TimeExpr("G", 4))),
        ],
    )
    errs_valid = check_filament_component(valid_mac)
    assert errs_valid == [], f"expected valid MAC to pass, got {errs_valid}"

    # Case 2.2: 1-cycle wire skew (c delayed by only 2 cycles -> @[G+2, G+3] into @[G+3, G+4])
    skewed_mac = ComponentDef(
        sig=valid_mac.sig,
        instances=valid_mac.instances,
        invocations=valid_mac.invocations,
        connections=[
            WireConn("m0.out", Interval(TimeExpr("G", 3), TimeExpr("G", 4)), "a0.x", Interval(TimeExpr("G", 3), TimeExpr("G", 4))),
            WireConn("c_reg2", Interval(TimeExpr("G", 2), TimeExpr("G", 3)), "a0.y", Interval(TimeExpr("G", 3), TimeExpr("G", 4))),
        ],
    )
    errs_skew = check_filament_component(skewed_mac)
    assert len(errs_skew) == 1 and "timeline skew" in errs_skew[0], f"expected skew error, got {errs_skew}"

    # Case 2.3: Structural double-booking on shared multiplier (II=2) invoked at G+0 and G+1
    double_booked = ComponentDef(
        sig=ComponentSig(name="DoubleBooked", event="G", ii=4, inputs={}, outputs={}),
        instances=[InstanceDecl("sm", mult_ii2)],
        invocations=[InvokeDecl("u0", "sm", TimeExpr("G", 0)), InvokeDecl("u1", "sm", TimeExpr("G", 1))],
        connections=[],
    )
    errs_db = check_filament_component(double_booked)
    assert len(errs_db) == 1 and "structural double-booking" in errs_db[0], f"expected double-book error, got {errs_db}"

    # Case 2.4: Valid time-multiplexed reuse (G+0 and G+2 with caller II=4) vs wrap-around clash (caller II=3)
    valid_tm = ComponentDef(
        sig=ComponentSig(name="ValidTimeMux", event="G", ii=4, inputs={}, outputs={}),
        instances=[InstanceDecl("sm", mult_ii2)],
        invocations=[InvokeDecl("u0", "sm", TimeExpr("G", 0)), InvokeDecl("u1", "sm", TimeExpr("G", 2))],
        connections=[],
    )
    assert check_filament_component(valid_tm) == []

    wrap_clash = ComponentDef(
        sig=ComponentSig(name="WrapClash", event="G", ii=3, inputs={}, outputs={}),
        instances=[InstanceDecl("sm", mult_ii2)],
        invocations=[InvokeDecl("u0", "sm", TimeExpr("G", 0)), InvokeDecl("u1", "sm", TimeExpr("G", 2))],
        connections=[],
    )
    errs_wrap = check_filament_component(wrap_clash)
    assert len(errs_wrap) == 1 and "cyclic gaps 2, 1 < 2" in errs_wrap[0], f"expected wrap clash, got {errs_wrap}"

    return {
        "valid_mac": "PASS",
        "skew_1cycle": errs_skew[0],
        "double_booked": errs_db[0],
        "wrap_around_clash": errs_wrap[0],
    }


# =============================================================================
# Part 3: Koika EHR Conflict Matrix & ORAAT Serializability Checker
# (Directly mirrors mit-plv/koika coq/Logs.v, TypedSemantics.v, OneRuleAtATime.v)
# =============================================================================


class Port(Enum):
    P0 = 0
    P1 = 1


class EntryKind(Enum):
    READ = "R"
    WRITE = "W"


@dataclass(frozen=True)
class LogEntry:
    kind: EntryKind
    port: Port
    val: int | None = None  # None for READ, int for WRITE


RegLog = dict[str, list[LogEntry]]  # newest entry at index 0 (mirrors Coq list cons)


def log_empty(regs: tuple[str, ...]) -> RegLog:
    return {r: [] for r in regs}


def log_app(l1: RegLog, l2: RegLog) -> RegLog:
    return {r: l1[r] + l2[r] for r in l1}


def log_exists(log: RegLog, reg: str, kind: EntryKind, port: Port) -> bool:
    return any(e.kind is kind and e.port is port for e in log[reg])


def may_read(sched_log: RegLog, port: Port, reg: str) -> bool:
    """Exact transcription of mit-plv/koika coq/Logs.v:70-75."""
    if port is Port.P0:
        return (not log_exists(sched_log, reg, EntryKind.WRITE, Port.P0)) and (
            not log_exists(sched_log, reg, EntryKind.WRITE, Port.P1)
        )
    return not log_exists(sched_log, reg, EntryKind.WRITE, Port.P1)


def may_write(sched_log: RegLog, rule_log: RegLog, port: Port, reg: str) -> bool:
    """Exact transcription of mit-plv/koika coq/Logs.v:95-101."""
    combined = log_app(rule_log, sched_log)
    if port is Port.P0:
        return (
            (not log_exists(combined, reg, EntryKind.READ, Port.P1))
            and (not log_exists(combined, reg, EntryKind.WRITE, Port.P0))
            and (not log_exists(combined, reg, EntryKind.WRITE, Port.P1))
        )
    return not log_exists(combined, reg, EntryKind.WRITE, Port.P1)


def latest_write0(log: RegLog, reg: str) -> int | None:
    """Exact transcription of mit-plv/koika coq/Logs.v:77-84."""
    for e in log[reg]:
        if e.kind is EntryKind.WRITE and e.port is Port.P0:
            return e.val
    return None


def latest_write(log: RegLog, reg: str) -> int | None:
    """Exact transcription of mit-plv/koika coq/Logs.v:103-110."""
    for e in log[reg]:
        if e.kind is EntryKind.WRITE:
            return e.val
    return None


def commit_update(r0: dict[str, int], log: RegLog) -> dict[str, int]:
    """Exact transcription of mit-plv/koika coq/Logs.v:112-116."""
    return {k: (v if (v := latest_write(log, k)) is not None else r0[k]) for k in r0}


@dataclass(frozen=True)
class KoikaOp:
    kind: EntryKind
    port: Port
    reg: str
    # For WRITE: computes value from rule-local read results dict; ignored for READ
    fn: Callable[[dict[str, int]], int] | None = None
    bind_as: str | None = None


@dataclass(frozen=True)
class KoikaRule:
    name: str
    ops: tuple[KoikaOp, ...]


def interp_rule(
    r0: dict[str, int], sched_log: RegLog, rule: KoikaRule
) -> RegLog | None:
    """Exact transcription of mit-plv/koika coq/TypedSemantics.v:86-112."""
    regs = tuple(r0.keys())
    action_log = log_empty(regs)
    locals_env: dict[str, int] = {}
    for op in rule.ops:
        if op.kind is EntryKind.READ:
            if not may_read(sched_log, op.port, op.reg):
                return None  # Dynamic conflict abort!
            if op.port is Port.P0:
                val = r0[op.reg]
            else:
                fwd = latest_write0(log_app(action_log, sched_log), op.reg)
                val = fwd if fwd is not None else r0[op.reg]
            action_log[op.reg] = [LogEntry(EntryKind.READ, op.port)] + action_log[op.reg]
            if op.bind_as is not None:
                locals_env[op.bind_as] = val
        else:
            assert op.fn is not None
            val = op.fn(locals_env)
            if not may_write(sched_log, action_log, op.port, op.reg):
                return None  # Dynamic conflict abort!
            action_log[op.reg] = [LogEntry(EntryKind.WRITE, op.port, val)] + action_log[op.reg]
    return action_log


def interp_schedule_with_trace(
    r0: dict[str, int], schedule: list[KoikaRule]
) -> tuple[dict[str, int], list[KoikaRule]]:
    """Run explicit static schedule in one hardware cycle; return (next_state, committed_rules)."""
    sched_log = log_empty(tuple(r0.keys()))
    committed: list[KoikaRule] = []
    for rule in schedule:
        rule_log = interp_rule(r0, sched_log, rule)
        if rule_log is not None:
            sched_log = log_app(rule_log, sched_log)
            committed.append(rule)
    return commit_update(r0, sched_log), committed


def interp_oraat_sequential(
    r0: dict[str, int], committed: list[KoikaRule]
) -> dict[str, int]:
    """One-Rule-at-a-Time sequential reference semantics (each rule runs alone on latest state)."""
    state = dict(r0)
    for rule in committed:
        empty = log_empty(tuple(state.keys()))
        rule_log = interp_rule(state, empty, rule)
        assert rule_log is not None, f"committed rule {rule.name} must succeed sequentially"
        state = commit_update(state, rule_log)
    return state


def verify_koika_ehr_oraat() -> dict[str, str]:
    # 3.1 Verify all 16 pairwise conflict-matrix cells (op1 in earlier rule -> op2 in later rule)
    ops_order = [
        ("R0", EntryKind.READ, Port.P0),
        ("W0", EntryKind.WRITE, Port.P0),
        ("R1", EntryKind.READ, Port.P1),
        ("W1", EntryKind.WRITE, Port.P1),
    ]
    matrix: dict[tuple[str, str], bool] = {}
    for n1, k1, p1 in ops_order:
        sched_log = {"x": [LogEntry(k1, p1, 42 if k1 is EntryKind.WRITE else None)]}
        empty_rule_log = {"x": []}
        for n2, k2, p2 in ops_order:
            allowed = may_read(sched_log, p2, "x") if k2 is EntryKind.READ else may_write(sched_log, empty_rule_log, p2, "x")
            matrix[(n1, n2)] = allowed

    # Expected exact conflict matrix from coq/Logs.v:70-101:
    # Row = earlier op in sched_log, Col = later op
    expected = {
        ("R0", "R0"): True,  ("R0", "W0"): True,  ("R0", "R1"): True,  ("R0", "W1"): True,
        ("W0", "R0"): False, ("W0", "W0"): False, ("W0", "R1"): True,  ("W0", "W1"): True,
        ("R1", "R0"): True,  ("R1", "W0"): False, ("R1", "R1"): True,  ("R1", "W1"): True,
        ("W1", "R0"): False, ("W1", "W0"): False, ("W1", "R1"): False, ("W1", "W1"): False,
    }
    assert matrix == expected, f"EHR matrix mismatch:\n got={matrix}\n exp={expected}"

    # 3.2 Concrete intra-cycle forwarding pipeline (W0 -> R1 succeeds; reversed R1 -> W0 aborts)
    rule_exec = KoikaRule(
        name="exec_stage",
        ops=(
            KoikaOp(EntryKind.READ, Port.P0, "buf", bind_as="v"),
            KoikaOp(EntryKind.WRITE, Port.P0, "buf", fn=lambda env: (env["v"] + 1) % 8),
            KoikaOp(EntryKind.WRITE, Port.P0, "out", fn=lambda env: env["v"]),
        ),
    )
    rule_decode = KoikaRule(
        name="decode_stage",
        ops=(
            KoikaOp(EntryKind.READ, Port.P1, "buf", bind_as="fwd"),
            KoikaOp(EntryKind.WRITE, Port.P1, "buf", fn=lambda env: (env["fwd"] * 2 + 1) % 8),
        ),
    )
    rule_bad_order_reader = KoikaRule(
        name="early_p1_reader",
        ops=(KoikaOp(EntryKind.READ, Port.P1, "buf", bind_as="x"),),
    )

    # Exhaustive ORAAT theorem verification across all initial states (buf in 0..7, out in 0..3)
    # and all 3 schedule permutations!
    checked_cases = 0
    for buf_val in range(8):
        for out_val in range(4):
            r0 = {"buf": buf_val, "out": out_val}
            for sched in (
                [rule_exec, rule_decode],
                [rule_decode, rule_exec],
                [rule_bad_order_reader, rule_exec, rule_decode],
            ):
                hw_next, committed = interp_schedule_with_trace(r0, sched)
                oraat_next = interp_oraat_sequential(r0, committed)
                assert hw_next == oraat_next, (
                    f"ORAAT violation! r0={r0} sched={[r.name for r in sched]} "
                    f"hw={hw_next} != oraat={oraat_next}"
                )
                checked_cases += 1

    # Verify specific forwarding vs abort behavior on r0={"buf": 2, "out": 0}
    fwd_next, fwd_committed = interp_schedule_with_trace({"buf": 2, "out": 0}, [rule_exec, rule_decode])
    assert [r.name for r in fwd_committed] == ["exec_stage", "decode_stage"]
    # exec reads 2, writes buf=3, out=2; decode reads forwarded 3 on P1, writes buf=(3*2+1)%8=7
    assert fwd_next == {"buf": 7, "out": 2}

    abort_next, abort_committed = interp_schedule_with_trace({"buf": 2, "out": 0}, [rule_bad_order_reader, rule_exec])
    assert [r.name for r in abort_committed] == ["early_p1_reader"]
    assert abort_next == {"buf": 2, "out": 0}

    return {
        "ehr_matrix_16_cells": "EXACT_MATCH(coq/Logs.v)",
        "forwarding_case": f"committed={[r.name for r in fwd_committed]}, next={fwd_next}",
        "conflict_abort_case": f"committed={[r.name for r in abort_committed]}, next={abort_next}",
        "oraat_exhaustive_states": f"{checked_cases}/{checked_cases} PASS",
    }


# =============================================================================
# Part 4: Dahlia Time-Sensitive Affine SRAM Bank-Port Checker
# (Models cucapra/dahlia src/main/scala/typechecker/AffineCheck.scala)
# =============================================================================


@dataclass
class BankedArray:
    name: str
    length: int
    banks: int


def check_dahlia_par_block(arrays: dict[str, BankedArray], accesses: list[tuple[str, int]]) -> list[str]:
    """Check one parallel logical step: each physical bank may be consumed at most once."""
    consumed: set[tuple[str, int]] = set()
    errors: list[str] = []
    for arr_name, idx in accesses:
        arr = arrays[arr_name]
        bank = idx % arr.banks
        if (arr_name, bank) in consumed:
            errors.append(
                f"affine bank conflict on {arr_name}[{idx}]: bank {bank} (mod {arr.banks}) already consumed in current step"
            )
        consumed.add((arr_name, bank))
    return errors


def check_dahlia_seq_steps(arrays: dict[str, BankedArray], steps: list[list[tuple[str, int]]]) -> list[str]:
    """Sequential barrier ('---') refreshes all bank capabilities (AffineCheck.scala:219 toFresh)."""
    all_errors: list[str] = []
    for step_idx, accesses in enumerate(steps):
        for err in check_dahlia_par_block(arrays, accesses):
            all_errors.append(f"step {step_idx}: {err}")
    return all_errors


def verify_dahlia_affine_banks() -> dict[str, str]:
    # Unroll 4 on bank 4: accesses [0, 1, 2, 3] hit banks {0, 1, 2, 3} -> PASS
    arr_b4 = {"a": BankedArray("a", length=16, banks=4)}
    assert check_dahlia_par_block(arr_b4, [("a", i) for i in range(4)]) == []

    # Unroll 4 on bank 2: accesses [0, 1, 2, 3] collide on banks 0 and 1 -> REJECT
    arr_b2 = {"a": BankedArray("a", length=16, banks=2)}
    errs_conflict = check_dahlia_par_block(arr_b2, [("a", i) for i in range(4)])
    assert len(errs_conflict) == 2 and "bank 0" in errs_conflict[0] and "bank 1" in errs_conflict[1]

    # Separating into two sequential steps ('---') refreshes bank capabilities -> PASS
    errs_seq = check_dahlia_seq_steps(arr_b2, [[("a", 0), ("a", 1)], [("a", 2), ("a", 3)]])
    assert errs_seq == []

    return {
        "unroll4_bank4": "PASS",
        "unroll4_bank2_conflict": errs_conflict[0],
        "seq_barrier_refresh": "PASS",
    }


def main() -> int:
    sv = verify_systemverilog_anomalies()
    fil = verify_filament_timelines()
    koi = verify_koika_ehr_oraat()
    dah = verify_dahlia_affine_banks()

    print("[PASS] 1. SystemVerilog IEEE 1800-2023 Event-Queue & X-Optimism Witnesses:")
    for k, v in sv.items():
        print(f"       {k}: {v}")
    print("[PASS] 2. Filament Presburger Timeline & II Typechecker:")
    for k, v in fil.items():
        print(f"       {k}: {v}")
    print("[PASS] 3. Koika EHR Conflict Matrix & ORAAT Serializability:")
    for k, v in koi.items():
        print(f"       {k}: {v}")
    print("[PASS] 4. Dahlia Time-Sensitive Affine Bank-Port Checker:")
    for k, v in dah.items():
        print(f"       {k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
