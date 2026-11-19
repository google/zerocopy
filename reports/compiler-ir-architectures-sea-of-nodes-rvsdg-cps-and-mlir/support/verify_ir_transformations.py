#!/usr/bin/env python3
"""Comparative IR transformation and invariant verification probe.

Translates a single effectful diamond+loop kernel across three IR paradigms:
  (a) Block-argument CFG SSA (explicit blocks, parallel-copy edges, domtree GVN/LICM),
  (b) Sea-of-Nodes (Click & Paleczny unified data/control/effect graph with GCM
      schedule_early/schedule_late, demonstrating both sound pinned division and
      the unsound lost-control-dependency trap bug when a guard edge is dropped),
  (c) RVSDG structured regions (acyclic Gamma/Theta regions with explicit state
      tokens, invariant node push-out, dead-node elimination, and irreducible-CFG
      predicate restructuring overhead).

Also includes compact executable checks for two mid-end e-graph invariants:
  (d) Acyclic e-graph (aegraph) tree-DP extraction suboptimality under DAG sharing
      and `subsume` dominance soundness when a rewrite drops an operand.

Standard library only; Python 3.10+. Exits 0 iff all equivalence and invariant
checks pass.
"""

from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass, field
import json
import sys
from typing import Any


# ---------------------------------------------------------------------------
# 0. Reference concrete semantics (effectful diamond + loop)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TrapResult:
    kind: str


@dataclass(frozen=True)
class OkResult:
    acc: int
    mem0: int
    mem1: int
    trace: tuple[tuple[str, int, int], ...]


EvalResult = OkResult | TrapResult


def eval_reference(a: int, b: int, n: int, m0: int, m1: int) -> EvalResult:
    """Reference operational semantics of the effectful diamond+loop program."""
    mem = [m0, m1]
    trace: list[tuple[str, int, int]] = []
    acc = 0
    i = 0
    while i < n:
        inv = (a * 2) + 1
        if b != 0:
            # Truncated-toward-zero integer division matching typical IR sdiv.
            q = int( (a + inv) / b )
            mem[0] = mem[0] + q
            trace.append(("store", 0, mem[0]))
            step = q + inv
        else:
            inv2 = (a * 2) + 1  # Redundant pure expression (GVN target)
            mem[1] = mem[1] + inv2
            trace.append(("store", 1, mem[1]))
            step = inv2
        acc = acc + step
        i = i + 1
    return OkResult(acc=acc, mem0=mem[0], mem1=mem[1], trace=tuple(trace))


def trunc_div(lhs: int, rhs: int) -> int | None:
    if rhs == 0:
        return None
    return int(lhs / rhs)


# ---------------------------------------------------------------------------
# 1. Block-Argument CFG SSA IR
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CfgInst:
    res: str | None
    op: str
    args: tuple[Any, ...]
    pure: bool = True
    can_trap: bool = False


@dataclass(frozen=True)
class CfgTerm:
    op: str  # "br", "cond_br", "ret"
    args: tuple[Any, ...]  # e.g. ("bb_hdr", (v0, v1)) or (cond, t_bb, t_args, f_bb, f_args)


@dataclass
class CfgBlock:
    name: str
    params: list[str]
    insts: list[CfgInst]
    term: CfgTerm


@dataclass
class CfgFunction:
    entry: str
    blocks: dict[str, CfgBlock]

    def successors(self, bb: str) -> list[str]:
        t = self.blocks[bb].term
        if t.op == "br":
            return [t.args[0]]
        if t.op == "cond_br":
            return [t.args[1], t.args[3]]
        return []

    def predecessors(self) -> dict[str, list[str]]:
        preds: dict[str, list[str]] = {b: [] for b in self.blocks}
        for b in self.blocks:
            for s in self.successors(b):
                preds[s].append(b)
        return preds

    def compute_dominators(self) -> tuple[dict[str, set[str]], dict[str, str | None]]:
        all_bbs = set(self.blocks.keys())
        preds = self.predecessors()
        dom: dict[str, set[str]] = {
            b: ({self.entry} if b == self.entry else set(all_bbs))
            for b in self.blocks
        }
        changed = True
        while changed:
            changed = False
            for b in self.blocks:
                if b == self.entry:
                    continue
                if not preds[b]:
                    new_dom = {b}
                else:
                    new_dom = set.intersection(*(dom[p] for p in preds[b])) | {b}
                if new_dom != dom[b]:
                    dom[b] = new_dom
                    changed = True
        idom: dict[str, str | None] = {self.entry: None}
        for b in self.blocks:
            if b == self.entry:
                continue
            strict = dom[b] - {b}
            # Immediate dominator is the strict dominator dominated by all others
            cand = [d for d in strict if strict <= dom[d]]
            assert len(cand) == 1, f"idom failure for {b}: {cand}"
            idom[b] = cand[0]
        return dom, idom

    def verify_ssa(self) -> None:
        dom, _ = self.compute_dominators()
        def_block: dict[str, str] = {}
        for bname, blk in self.blocks.items():
            for p in blk.params:
                assert p not in def_block, f"duplicate SSA def {p}"
                def_block[p] = bname
            for inst in blk.insts:
                if inst.res is not None:
                    assert inst.res not in def_block, f"duplicate SSA def {inst.res}"
                    def_block[inst.res] = bname
        # Verify dominance & block-argument arities
        for bname, blk in self.blocks.items():
            seen_in_blk: set[str] = set(blk.params)
            for inst in blk.insts:
                for a in inst.args:
                    if isinstance(a, str) and a.startswith("%"):
                        db = def_block[a]
                        assert db in dom[bname], f"use of {a} in {bname} not dominated by {db}"
                        if db == bname:
                            assert a in seen_in_blk, f"use-before-def of {a} in {bname}"
                if inst.res is not None:
                    seen_in_blk.add(inst.res)
            t = blk.term
            if t.op == "br":
                tgt, targs = t.args
                assert len(targs) == len(self.blocks[tgt].params)
                for a in targs:
                    assert def_block[a] in dom[bname]
            elif t.op == "cond_br":
                cond, t_bb, t_args, f_bb, f_args = t.args
                assert def_block[cond] in dom[bname]
                assert len(t_args) == len(self.blocks[t_bb].params)
                assert len(f_args) == len(self.blocks[f_bb].params)
                for a in (*t_args, *f_args):
                    assert def_block[a] in dom[bname]
            elif t.op == "ret":
                for a in t.args:
                    assert def_block[a] in dom[bname]


def build_cfg_ssa() -> CfgFunction:
    return CfgFunction(
        entry="bb_entry",
        blocks={
            "bb_entry": CfgBlock(
                name="bb_entry",
                params=["%a", "%b", "%n"],
                insts=[
                    CfgInst("%c0", "const", (0,)),
                    CfgInst("%c1", "const", (1,)),
                    CfgInst("%c2", "const", (2,)),
                ],
                term=CfgTerm("br", ("bb_hdr", ("%c0", "%c0"))),
            ),
            "bb_hdr": CfgBlock(
                name="bb_hdr",
                params=["%i", "%acc"],
                insts=[
                    CfgInst("%lt", "lt", ("%i", "%n")),
                ],
                term=CfgTerm("cond_br", ("%lt", "bb_body", (), "bb_exit", ())),
            ),
            "bb_body": CfgBlock(
                name="bb_body",
                params=[],
                insts=[
                    CfgInst("%mul1", "mul", ("%a", "%c2")),
                    CfgInst("%inv1", "add", ("%mul1", "%c1")),
                    CfgInst("%nz", "ne", ("%b", "%c0")),
                ],
                term=CfgTerm("cond_br", ("%nz", "bb_then", (), "bb_else", ())),
            ),
            "bb_then": CfgBlock(
                name="bb_then",
                params=[],
                insts=[
                    CfgInst("%num", "add", ("%a", "%inv1")),
                    CfgInst("%q", "sdiv", ("%num", "%b"), pure=True, can_trap=True),
                    CfgInst("%m0_old", "load", (0,), pure=False),
                    CfgInst("%m0_new", "add", ("%m0_old", "%q")),
                    CfgInst(None, "store", (0, "%m0_new"), pure=False),
                    CfgInst("%step_t", "add", ("%q", "%inv1")),
                ],
                term=CfgTerm("br", ("bb_merge", ("%step_t",))),
            ),
            "bb_else": CfgBlock(
                name="bb_else",
                params=[],
                insts=[
                    CfgInst("%mul2", "mul", ("%a", "%c2")),
                    CfgInst("%inv2", "add", ("%mul2", "%c1")),
                    CfgInst("%m1_old", "load", (1,), pure=False),
                    CfgInst("%m1_new", "add", ("%m1_old", "%inv2")),
                    CfgInst(None, "store", (1, "%m1_new"), pure=False),
                ],
                term=CfgTerm("br", ("bb_merge", ("%inv2",))),
            ),
            "bb_merge": CfgBlock(
                name="bb_merge",
                params=["%step"],
                insts=[
                    CfgInst("%acc_next", "add", ("%acc", "%step")),
                    CfgInst("%i_next", "add", ("%i", "%c1")),
                ],
                term=CfgTerm("br", ("bb_hdr", ("%i_next", "%acc_next"))),
            ),
            "bb_exit": CfgBlock(
                name="bb_exit",
                params=[],
                insts=[
                    CfgInst("%m0_fin", "load", (0,), pure=False),
                    CfgInst("%m1_fin", "load", (1,), pure=False),
                ],
                term=CfgTerm("ret", ("%acc", "%m0_fin", "%m1_fin")),
            ),
        },
    )


def optimize_cfg_ssa(fn: CfgFunction) -> tuple[CfgFunction, dict[str, int]]:
    """Run explicit Dominator-Tree GVN + Loop-Invariant Code Motion (LICM)."""
    _, idom = fn.compute_dominators()
    dom_children: dict[str, list[str]] = {b: [] for b in fn.blocks}
    for b, p in idom.items():
        if p is not None:
            dom_children[p].append(b)

    # Pass 1: Scoped dominator-tree GVN (pure, non-trapping ops)
    new_blocks: dict[str, CfgBlock] = {}
    rename: dict[str, str] = {}
    gvn_eliminated = 0

    def subst(x: Any) -> Any:
        while isinstance(x, str) and x in rename:
            x = rename[x]
        return x

    def visit_gvn(bb_name: str, scopes: list[dict[tuple[str, tuple[Any, ...]], str]]) -> None:
        nonlocal gvn_eliminated
        blk = fn.blocks[bb_name]
        local_scope: dict[tuple[str, tuple[Any, ...]], str] = {}
        scopes.append(local_scope)
        kept: list[CfgInst] = []
        for inst in blk.insts:
            new_args = tuple(subst(a) for a in inst.args)
            if inst.pure and not inst.can_trap and inst.res is not None:
                key = (inst.op, new_args)
                found = None
                for sc in reversed(scopes):
                    if key in sc:
                        found = sc[key]
                        break
                if found is not None:
                    rename[inst.res] = found
                    gvn_eliminated += 1
                    continue
                local_scope[key] = inst.res
            kept.append(CfgInst(inst.res, inst.op, new_args, inst.pure, inst.can_trap))
        t = blk.term
        if t.op == "br":
            new_t = CfgTerm("br", (t.args[0], tuple(subst(a) for a in t.args[1])))
        elif t.op == "cond_br":
            new_t = CfgTerm(
                "cond_br",
                (
                    subst(t.args[0]),
                    t.args[1],
                    tuple(subst(a) for a in t.args[2]),
                    t.args[3],
                    tuple(subst(a) for a in t.args[4]),
                ),
            )
        else:
            new_t = CfgTerm("ret", tuple(subst(a) for a in t.args))
        new_blocks[bb_name] = CfgBlock(blk.name, list(blk.params), kept, new_t)
        for ch in dom_children[bb_name]:
            visit_gvn(ch, scopes)
        scopes.pop()

    visit_gvn(fn.entry, [])
    opt_fn = CfgFunction(fn.entry, new_blocks)

    # Pass 2: Explicit natural-loop detection (back-edge bb_merge -> bb_hdr) + LICM
    dom, _ = opt_fn.compute_dominators()
    preds = opt_fn.predecessors()
    loop_blocks: set[str] = set()
    loop_header = None
    for b in opt_fn.blocks:
        for s in opt_fn.successors(b):
            if s in dom[b]:
                loop_header = s
                # Backward walk from b to s
                work = [b]
                loop_blocks.add(s)
                while work:
                    cur = work.pop()
                    if cur not in loop_blocks:
                        loop_blocks.add(cur)
                        work.extend(preds[cur])
    assert loop_header is not None
    preheader = [p for p in preds[loop_header] if p not in loop_blocks][0]

    # Compute defs inside loop
    loop_defs: set[str] = set()
    for b in loop_blocks:
        loop_defs.update(opt_fn.blocks[b].params)
        for inst in opt_fn.blocks[b].insts:
            if inst.res:
                loop_defs.add(inst.res)

    licm_hoisted = 0
    licm_blocked_trapping_ids: set[str] = set()
    changed = True
    while changed:
        changed = False
        for b in sorted(loop_blocks):
            kept_insts: list[CfgInst] = []
            for inst in opt_fn.blocks[b].insts:
                args_invariant = all(
                    not (isinstance(a, str) and a in loop_defs) for a in inst.args
                )
                if inst.pure and args_invariant:
                    if inst.can_trap:
                        # Cannot hoist trapping op out of guarded branch / loop!
                        if inst.res is not None:
                            licm_blocked_trapping_ids.add(inst.res)
                        kept_insts.append(inst)
                    else:
                        opt_fn.blocks[preheader].insts.append(inst)
                        if inst.res:
                            loop_defs.discard(inst.res)
                        licm_hoisted += 1
                        changed = True
                        continue
                else:
                    kept_insts.append(inst)
            opt_fn.blocks[b].insts = kept_insts

    opt_fn.verify_ssa()
    stats = {
        "blocks": len(opt_fn.blocks),
        "insts": sum(len(b.insts) for b in opt_fn.blocks.values()),
        "block_params": sum(len(b.params) for b in opt_fn.blocks.values()),
        "gvn_eliminated": gvn_eliminated,
        "licm_hoisted": licm_hoisted,
        "licm_blocked_trapping": len(licm_blocked_trapping_ids),
        "required_analyses": 2,  # DomTree + NaturalLoopInfo
    }
    return opt_fn, stats


def eval_cfg_ssa(fn: CfgFunction, a: int, b: int, n: int, m0: int, m1: int) -> EvalResult:
    env: dict[str, int] = {"%a": a, "%b": b, "%n": n}
    mem = [m0, m1]
    trace: list[tuple[str, int, int]] = []
    cur = fn.entry
    while True:
        blk = fn.blocks[cur]
        for inst in blk.insts:
            if inst.op == "const":
                val = inst.args[0]
            elif inst.op == "add":
                val = env[inst.args[0]] + env[inst.args[1]]
            elif inst.op == "mul":
                val = env[inst.args[0]] * env[inst.args[1]]
            elif inst.op == "lt":
                val = int(env[inst.args[0]] < env[inst.args[1]])
            elif inst.op == "ne":
                val = int(env[inst.args[0]] != env[inst.args[1]])
            elif inst.op == "sdiv":
                q = trunc_div(env[inst.args[0]], env[inst.args[1]])
                if q is None:
                    return TrapResult("div_by_zero")
                val = q
            elif inst.op == "load":
                val = mem[inst.args[0]]
            elif inst.op == "store":
                idx, vname = inst.args
                mem[idx] = env[vname]
                trace.append(("store", idx, mem[idx]))
                val = None
            else:
                raise ValueError(f"unknown op {inst.op}")
            if inst.res is not None:
                assert val is not None
                env[inst.res] = val
        t = blk.term
        if t.op == "br":
            tgt, targs = t.args
            vals = [env[x] for x in targs]
            for p, v in zip(fn.blocks[tgt].params, vals, strict=True):
                env[p] = v
            cur = tgt
        elif t.op == "cond_br":
            cond, t_bb, t_args, f_bb, f_args = t.args
            if env[cond]:
                vals = [env[x] for x in t_args]
                for p, v in zip(fn.blocks[t_bb].params, vals, strict=True):
                    env[p] = v
                cur = t_bb
            else:
                vals = [env[x] for x in f_args]
                for p, v in zip(fn.blocks[f_bb].params, vals, strict=True):
                    env[p] = v
                cur = f_bb
        elif t.op == "ret":
            acc_v, m0_v, m1_v = (env[x] for x in t.args)
            return OkResult(acc=acc_v, mem0=m0_v, mem1=m1_v, trace=tuple(trace))


# ---------------------------------------------------------------------------
# 2. Sea-of-Nodes IR (Click & Paleczny 1995 / GCM schedule_early + schedule_late)
# ---------------------------------------------------------------------------

@dataclass
class SoNNode:
    nid: int
    op: str
    control_in: int | None = None
    effect_in: int | None = None
    data_ins: list[int] = field(default_factory=list)
    imm: Any = None
    is_cfg: bool = False
    is_pinned: bool = False
    is_effect: bool = False
    can_trap: bool = False


class SeaOfNodesGraph:
    """Unified control/effect/data graph with hash-consed pure nodes and GCM."""

    def __init__(self) -> None:
        self.nodes: dict[int, SoNNode] = {}
        self._next_id = 0
        self._gvn_table: dict[tuple[Any, ...], int] = {}
        self.gvn_hits = 0

    def add(
        self,
        op: str,
        *,
        control_in: int | None = None,
        effect_in: int | None = None,
        data_ins: list[int] | None = None,
        imm: Any = None,
        is_cfg: bool = False,
        is_pinned: bool = False,
        is_effect: bool = False,
        can_trap: bool = False,
        pure_gvn: bool = False,
    ) -> int:
        dins = list(data_ins or [])
        if pure_gvn and not is_cfg and not is_effect:
            key = (op, control_in, tuple(dins), imm)
            if key in self._gvn_table:
                self.gvn_hits += 1
                return self._gvn_table[key]
        nid = self._next_id
        self._next_id += 1
        node = SoNNode(
            nid=nid,
            op=op,
            control_in=control_in,
            effect_in=effect_in,
            data_ins=dins,
            imm=imm,
            is_cfg=is_cfg,
            is_pinned=is_pinned,
            is_effect=is_effect,
            can_trap=can_trap,
        )
        self.nodes[nid] = node
        if pure_gvn and not is_cfg and not is_effect:
            self._gvn_table[(op, control_in, tuple(dins), imm)] = nid
        return nid


def build_sea_of_nodes(*, pin_div_to_guard: bool) -> tuple[SeaOfNodesGraph, dict[str, int]]:
    """Build the effectful diamond+loop program in Sea-of-Nodes with free GVN."""
    g = SeaOfNodesGraph()
    start = g.add("Start", is_cfg=True, is_pinned=True)
    ctrl0 = g.add("ProjCtrl", control_in=start, is_cfg=True, is_pinned=True)
    eff0 = g.add("ProjEffect", control_in=start, is_pinned=True, is_effect=True)
    p_a = g.add("Param", control_in=start, imm="a", is_pinned=True)
    p_b = g.add("Param", control_in=start, imm="b", is_pinned=True)
    p_n = g.add("Param", control_in=start, imm="n", is_pinned=True)
    c0 = g.add("Const", control_in=start, imm=0, pure_gvn=True)
    c1 = g.add("Const", control_in=start, imm=1, pure_gvn=True)
    c2 = g.add("Const", control_in=start, imm=2, pure_gvn=True)

    # Loop header Region + value Phis + EffectPhi (backedge patched below)
    loop_reg = g.add("Loop", control_in=ctrl0, data_ins=[ctrl0, -1], is_cfg=True, is_pinned=True)
    phi_i = g.add("Phi", control_in=loop_reg, data_ins=[c0, -1], is_pinned=True)
    phi_acc = g.add("Phi", control_in=loop_reg, data_ins=[c0, -1], is_pinned=True)
    phi_eff = g.add("EffectPhi", control_in=loop_reg, data_ins=[eff0, -1], is_pinned=True, is_effect=True)

    # Loop exit branch
    lt_node = g.add("Lt", data_ins=[phi_i, p_n], pure_gvn=True)
    if_loop = g.add("If", control_in=loop_reg, data_ins=[lt_node], is_cfg=True, is_pinned=True)
    body_ctrl = g.add("ProjTrue", control_in=if_loop, is_cfg=True, is_pinned=True)
    exit_ctrl = g.add("ProjFalse", control_in=if_loop, is_cfg=True, is_pinned=True)

    # Pure invariant expression (floating: control_in=None)
    mul1 = g.add("Mul", data_ins=[p_a, c2], pure_gvn=True)
    inv1 = g.add("Add", data_ins=[mul1, c1], pure_gvn=True)

    # Diamond branch on b != 0
    nz_node = g.add("Ne", data_ins=[p_b, c0], pure_gvn=True)
    if_b = g.add("If", control_in=body_ctrl, data_ins=[nz_node], is_cfg=True, is_pinned=True)
    then_ctrl = g.add("ProjTrue", control_in=if_b, is_cfg=True, is_pinned=True)
    else_ctrl = g.add("ProjFalse", control_in=if_b, is_cfg=True, is_pinned=True)

    # Then branch: div (either soundly pinned to then_ctrl or unsafely unpinned!)
    num = g.add("Add", data_ins=[p_a, inv1], pure_gvn=True)
    div_node = g.add(
        "SDiv",
        control_in=then_ctrl if pin_div_to_guard else None,
        data_ins=[num, p_b],
        can_trap=True,
        pure_gvn=True,
    )
    ld0 = g.add("Load", control_in=then_ctrl, effect_in=phi_eff, imm=0, is_effect=True)
    m0_new = g.add("Add", data_ins=[ld0, div_node], pure_gvn=True)
    st0 = g.add("Store", control_in=then_ctrl, effect_in=ld0, data_ins=[m0_new], imm=0, is_pinned=True, is_effect=True)
    step_t = g.add("Add", data_ins=[div_node, inv1], pure_gvn=True)

    # Else branch: redundant (a * 2) + 1 automatically hits hash-cons GVN!
    mul2 = g.add("Mul", data_ins=[p_a, c2], pure_gvn=True)
    inv2 = g.add("Add", data_ins=[mul2, c1], pure_gvn=True)
    assert mul2 == mul1 and inv2 == inv1, "Sea-of-Nodes hash-consing must deduplicate pure nodes"
    ld1 = g.add("Load", control_in=else_ctrl, effect_in=phi_eff, imm=1, is_effect=True)
    m1_new = g.add("Add", data_ins=[ld1, inv2], pure_gvn=True)
    st1 = g.add("Store", control_in=else_ctrl, effect_in=ld1, data_ins=[m1_new], imm=1, is_pinned=True, is_effect=True)

    # Merge Region + value Phi + EffectPhi
    merge_reg = g.add("Region", data_ins=[then_ctrl, else_ctrl], is_cfg=True, is_pinned=True)
    phi_step = g.add("Phi", control_in=merge_reg, data_ins=[step_t, inv2], is_pinned=True)
    merge_eff = g.add("EffectPhi", control_in=merge_reg, data_ins=[st0, st1], is_pinned=True, is_effect=True)

    acc_next = g.add("Add", data_ins=[phi_acc, phi_step], pure_gvn=True)
    i_next = g.add("Add", data_ins=[phi_i, c1], pure_gvn=True)

    # Wire loop back-edges
    g.nodes[loop_reg].data_ins[1] = merge_reg
    g.nodes[phi_i].data_ins[1] = i_next
    g.nodes[phi_acc].data_ins[1] = acc_next
    g.nodes[phi_eff].data_ins[1] = merge_eff

    # Exit reads and Return
    fin_ld0 = g.add("Load", control_in=exit_ctrl, effect_in=phi_eff, imm=0, is_effect=True)
    fin_ld1 = g.add("Load", control_in=exit_ctrl, effect_in=fin_ld0, imm=1, is_effect=True)
    ret = g.add("Return", control_in=exit_ctrl, effect_in=fin_ld1, data_ins=[phi_acc, fin_ld0, fin_ld1], is_cfg=True, is_pinned=True, is_effect=True)

    handles = {
        "start": start,
        "ctrl0": ctrl0,
        "loop_reg": loop_reg,
        "body_ctrl": body_ctrl,
        "then_ctrl": then_ctrl,
        "else_ctrl": else_ctrl,
        "merge_reg": merge_reg,
        "exit_ctrl": exit_ctrl,
        "inv1": inv1,
        "div_node": div_node,
        "ret": ret,
    }
    return g, handles


def schedule_sea_of_nodes_to_cfg(
    g: SeaOfNodesGraph, handles: dict[str, int]
) -> tuple[dict[int, str], dict[str, list[int]], dict[str, Any]]:
    """Click 1995 GCM (schedule_early + schedule_late with loop-depth selection).

    Maps every Sea-of-Nodes node to a basic block and produces a linearized
    per-block instruction order so the scheduled CFG can be executed directly.
    """
    # Fixed CFG skeleton derived from control nodes:
    cfg_blocks = ["bb_entry", "bb_hdr", "bb_body", "bb_then", "bb_else", "bb_merge", "bb_exit"]
    ctrl_to_bb = {
        handles["start"]: "bb_entry",
        handles["ctrl0"]: "bb_entry",
        handles["loop_reg"]: "bb_hdr",
        handles["body_ctrl"]: "bb_body",
        handles["then_ctrl"]: "bb_then",
        handles["else_ctrl"]: "bb_else",
        handles["merge_reg"]: "bb_merge",
        handles["exit_ctrl"]: "bb_exit",
    }
    # Dominator tree & loop nesting depth on the CFG skeleton
    idom = {
        "bb_entry": None,
        "bb_hdr": "bb_entry",
        "bb_body": "bb_hdr",
        "bb_then": "bb_body",
        "bb_else": "bb_body",
        "bb_merge": "bb_body",
        "bb_exit": "bb_hdr",
    }
    dom_depth = {
        "bb_entry": 0,
        "bb_hdr": 1,
        "bb_body": 2,
        "bb_then": 3,
        "bb_else": 3,
        "bb_merge": 3,
        "bb_exit": 2,
    }
    loop_depth = {
        "bb_entry": 0,
        "bb_hdr": 1,
        "bb_body": 1,
        "bb_then": 1,
        "bb_else": 1,
        "bb_merge": 1,
        "bb_exit": 0,
    }

    def lca(b1: str, b2: str) -> str:
        x, y = b1, b2
        while dom_depth[x] > dom_depth[y]:
            x = idom[x]  # type: ignore[assignment]
        while dom_depth[y] > dom_depth[x]:
            y = idom[y]  # type: ignore[assignment]
        while x != y:
            x = idom[x]  # type: ignore[assignment]
            y = idom[y]  # type: ignore[assignment]
        return x

    def deepest(b1: str, b2: str) -> str:
        return b1 if dom_depth[b1] >= dom_depth[b2] else b2

    # Build user lists for schedule_late
    uses: dict[int, list[tuple[int, int | None]]] = {nid: [] for nid in g.nodes}
    for nid, node in g.nodes.items():
        if node.op in ("Phi", "EffectPhi"):
            reg = g.nodes[node.control_in]  # type: ignore[index]
            for idx, din in enumerate(node.data_ins):
                # Phi input i is used along predecessor control edge reg.data_ins[i]
                pred_ctrl = reg.data_ins[idx]
                uses[din].append((nid, pred_ctrl))
        else:
            for din in node.data_ins:
                if din in g.nodes:
                    uses[din].append((nid, None))
            if node.effect_in is not None:
                uses[node.effect_in].append((nid, None))

    # Phase 1: schedule_early (deepest domtree block among inputs & control_in)
    early: dict[int, str] = {}

    def compute_early(nid: int) -> str:
        if nid in early:
            return early[nid]
        node = g.nodes[nid]
        if nid in ctrl_to_bb:
            early[nid] = ctrl_to_bb[nid]
            return early[nid]
        if node.is_cfg:
            assert node.control_in is not None
            early[nid] = ctrl_to_bb[node.control_in]
            return early[nid]
        if node.op in ("Phi", "EffectPhi"):
            assert node.control_in is not None
            early[nid] = ctrl_to_bb[node.control_in]
            return early[nid]
        blk = "bb_entry"
        if node.control_in is not None:
            blk = deepest(blk, ctrl_to_bb[node.control_in])
        if node.effect_in is not None:
            blk = deepest(blk, compute_early(node.effect_in))
        for din in node.data_ins:
            if din in g.nodes:
                blk = deepest(blk, compute_early(din))
        early[nid] = blk
        return blk

    for nid in g.nodes:
        compute_early(nid)

    # Phase 2: schedule_late (LCA of uses, then pick shallowest loop_depth in [early, late])
    placed: dict[int, str] = {}

    def compute_late(nid: int) -> str:
        if nid in placed:
            return placed[nid]
        node = g.nodes[nid]
        if node.is_pinned or node.is_cfg or node.is_effect:
            placed[nid] = early[nid]
            return placed[nid]
        u_list = uses[nid]
        if not u_list:
            placed[nid] = early[nid]
            return placed[nid]
        cur_lca: str | None = None
        for user_id, pred_ctrl in u_list:
            ublk = ctrl_to_bb[pred_ctrl] if pred_ctrl is not None else compute_late(user_id)
            cur_lca = ublk if cur_lca is None else lca(cur_lca, ublk)
        assert cur_lca is not None
        # Walk up dominator tree from cur_lca to early[nid], choosing least loop_depth
        best = cur_lca
        probe = cur_lca
        while True:
            if loop_depth[probe] < loop_depth[best]:
                best = probe
            if probe == early[nid]:
                break
            nxt = idom[probe]
            if nxt is None:
                break
            probe = nxt
        placed[nid] = best
        return best

    for nid in g.nodes:
        compute_late(nid)

    # Local topological ordering inside each basic block
    per_block_raw: dict[str, list[int]] = {b: [] for b in cfg_blocks}
    for nid, bb in placed.items():
        node = g.nodes[nid]
        if node.op in ("Start", "ProjCtrl", "ProjEffect", "Param", "Loop", "Region", "ProjTrue", "ProjFalse", "Phi", "EffectPhi", "If", "Return"):
            continue
        per_block_raw[bb].append(nid)

    ordered: dict[str, list[int]] = {}
    for bb, nids in per_block_raw.items():
        nid_set = set(nids)
        indeg: dict[int, int] = {n: 0 for n in nids}
        adj: dict[int, list[int]] = {n: [] for n in nids}
        for n in nids:
            node = g.nodes[n]
            deps = list(node.data_ins) + ([node.effect_in] if node.effect_in is not None else [])
            for d in deps:
                if d in nid_set:
                    adj[d].append(n)
                    indeg[n] += 1
        q = deque(sorted(n for n, deg in indeg.items() if deg == 0))
        res: list[int] = []
        while q:
            u = q.popleft()
            res.append(u)
            for v in adj[u]:
                indeg[v] -= 1
                if indeg[v] == 0:
                    q.append(v)
        assert len(res) == len(nids), f"local scheduling cycle in {bb}"
        ordered[bb] = res

    # Compute structural metrics (how many nodes sit on control/effect chains vs truly float)
    total_nodes = len(g.nodes)
    start_consts_params = sum(
        1 for nd in g.nodes.values() if nd.op in ("Param", "Const")
    )
    cfg_and_effect_nodes = sum(
        1
        for nd in g.nodes.values()
        if nd.is_cfg or nd.is_effect or (nd.control_in is not None and nd.op not in ("Param", "Const"))
    )
    floating_pure = total_nodes - cfg_and_effect_nodes - start_consts_params

    # Count edge rewirings required to fold the else-branch dead (assuming b != 0 is statically true):
    # - CFG SSA: rewrite 1 terminator (cond_br -> br bb_then); bb_else becomes unreachable automatically.
    # - Sea-of-Nodes: must patch Region control input, value Phi input, EffectPhi input, and unlink
    #   both control (ProjFalse) and effect chain (Load -> Store) edges before dead nodes disappear.
    # - RVSDG: replace Gamma node with its selected subregion body (inlining 1 structural node).
    else_chain_edges_to_patch = sum(
        1
        for nd in g.nodes.values()
        if nd.nid == handles["else_ctrl"]
        or nd.control_in == handles["else_ctrl"]
        or (nd.op in ("Region", "Phi", "EffectPhi") and nd.nid != handles["loop_reg"] and nd.control_in != handles["loop_reg"])
    )
    metrics = {
        "total_nodes": total_nodes,
        "cfg_effect_or_guard_pinned_nodes": cfg_and_effect_nodes,
        "start_bound_params_and_consts": start_consts_params,
        "truly_floating_pure_nodes": floating_pure,
        "gvn_hits": g.gvn_hits,
        "inv1_block": placed[handles["inv1"]],
        "div_block": placed[handles["div_node"]],
        "dead_else_branch_son_nodes_to_patch": else_chain_edges_to_patch,
    }
    return placed, ordered, metrics


def eval_scheduled_son(
    g: SeaOfNodesGraph,
    handles: dict[str, int],
    ordered: dict[str, list[int]],
    a: int,
    b: int,
    n: int,
    m0: int,
    m1: int,
) -> EvalResult:
    """Execute the scheduled Sea-of-Nodes graph block-by-block."""
    env: dict[int, int] = {}
    mem = [m0, m1]
    trace: list[tuple[str, int, int]] = []

    for nid, nd in g.nodes.items():
        if nd.op == "Param":
            env[nid] = {"a": a, "b": b, "n": n}[nd.imm]

    def exec_block_insts(bb: str) -> TrapResult | None:
        for nid in ordered[bb]:
            nd = g.nodes[nid]
            if nd.op == "Const":
                env[nid] = nd.imm
            elif nd.op == "Add":
                env[nid] = env[nd.data_ins[0]] + env[nd.data_ins[1]]
            elif nd.op == "Mul":
                env[nid] = env[nd.data_ins[0]] * env[nd.data_ins[1]]
            elif nd.op == "Lt":
                env[nid] = int(env[nd.data_ins[0]] < env[nd.data_ins[1]])
            elif nd.op == "Ne":
                env[nid] = int(env[nd.data_ins[0]] != env[nd.data_ins[1]])
            elif nd.op == "SDiv":
                q = trunc_div(env[nd.data_ins[0]], env[nd.data_ins[1]])
                if q is None:
                    return TrapResult("div_by_zero")
                env[nid] = q
            elif nd.op == "Load":
                env[nid] = mem[nd.imm]
            elif nd.op == "Store":
                mem[nd.imm] = env[nd.data_ins[0]]
                trace.append(("store", nd.imm, mem[nd.imm]))
            else:
                raise ValueError(f"unexpected SoN op {nd.op}")
        return None

    # Locate Phis & terminators by region
    loop_phis = [nd for nd in g.nodes.values() if nd.op == "Phi" and nd.control_in == handles["loop_reg"]]
    merge_phis = [nd for nd in g.nodes.values() if nd.op == "Phi" and nd.control_in == handles["merge_reg"]]
    if_loop = [nd for nd in g.nodes.values() if nd.op == "If" and nd.control_in == handles["loop_reg"]][0]
    if_b = [nd for nd in g.nodes.values() if nd.op == "If" and nd.control_in == handles["body_ctrl"]][0]
    ret_nd = g.nodes[handles["ret"]]

    # Entry block
    trap = exec_block_insts("bb_entry")
    if trap:
        return trap
    # Initial loop Phi assignment (index 0)
    init_vals = {p.nid: env[p.data_ins[0]] for p in loop_phis}
    env.update(init_vals)

    while True:
        trap = exec_block_insts("bb_hdr")
        if trap:
            return trap
        if not env[if_loop.data_ins[0]]:
            break
        trap = exec_block_insts("bb_body")
        if trap:
            return trap
        if env[if_b.data_ins[0]]:
            trap = exec_block_insts("bb_then")
            if trap:
                return trap
            branch_idx = 0
        else:
            trap = exec_block_insts("bb_else")
            if trap:
                return trap
            branch_idx = 1
        mvals = {p.nid: env[p.data_ins[branch_idx]] for p in merge_phis}
        env.update(mvals)
        trap = exec_block_insts("bb_merge")
        if trap:
            return trap
        next_vals = {p.nid: env[p.data_ins[1]] for p in loop_phis}
        env.update(next_vals)

    trap = exec_block_insts("bb_exit")
    if trap:
        return trap
    acc_v, m0_v, m1_v = (env[x] for x in ret_nd.data_ins)
    return OkResult(acc=acc_v, mem0=m0_v, mem1=m1_v, trace=tuple(trace))


# ---------------------------------------------------------------------------
# 3. RVSDG Structured Region IR (Gamma / Theta + Explicit State Tokens)
# ---------------------------------------------------------------------------

@dataclass
class RvsdgNode:
    nid: str
    op: str
    inputs: list[str]
    outputs: list[str]
    imm: Any = None
    can_trap: bool = False
    is_stateful: bool = False
    # For structural nodes:
    subregions: list[RvsdgRegion] = field(default_factory=list)


@dataclass
class RvsdgRegion:
    name: str
    args: list[str]  # region entry ports (values + state tokens)
    nodes: list[RvsdgNode]
    results: list[str]  # region exit ports (values + state tokens)

    def verify_acyclic_and_scoped(self) -> None:
        """Verify strict acyclicity and lexical region scoping (no cross-region edges)."""
        defined: set[str] = set(self.args)
        for nd in self.nodes:
            for inp in nd.inputs:
                assert inp in defined, (
                    f"RVSDG scope/acyclicity violation in {self.name}: "
                    f"node {nd.nid} reads undefined/future port {inp}"
                )
            for sub in nd.subregions:
                sub.verify_acyclic_and_scoped()
            for out in nd.outputs:
                assert out not in defined, f"duplicate RVSDG port {out} in {self.name}"
                defined.add(out)
        for res in self.results:
            assert res in defined, f"RVSDG result {res} undefined in {self.name}"


def build_rvsdg() -> RvsdgRegion:
    """Build the effectful diamond+loop program as nested Gamma/Theta regions.

    Because Theta is tail-controlled (do-while), a head-controlled `while (i < n)`
    wraps Theta inside an outer Gamma guarded by `n > 0` (matching Reissmann et al.
    TECS 2020 §4-5 and Bahmann et al. TACO 2015). Memory ordering is encoded
    explicitly via threaded state tokens (`s_*`).
    """
    # Inner Gamma (b != 0): subregion 0 = else, subregion 1 = then
    else_reg = RvsdgRegion(
        name="gamma_b_else",
        args=["e_a", "e_b", "e_inv1", "e_s0"],
        nodes=[
            RvsdgNode("e_c2", "const", [], ["v_e_c2"], imm=2),
            RvsdgNode("e_c1", "const", [], ["v_e_c1"], imm=1),
            RvsdgNode("e_mul", "mul", ["e_a", "v_e_c2"], ["v_e_mul"]),
            RvsdgNode("e_inv2", "add", ["v_e_mul", "v_e_c1"], ["v_e_inv2"]),
            RvsdgNode("e_ld1", "load", ["e_s0"], ["v_e_m1", "e_s1"], imm=1, is_stateful=True),
            RvsdgNode("e_add1", "add", ["v_e_m1", "v_e_inv2"], ["v_e_m1n"]),
            RvsdgNode("e_st1", "store", ["e_s1", "v_e_m1n"], ["e_s2"], imm=1, is_stateful=True),
            # Include a dead pure computation to verify DNE
            RvsdgNode("e_dead", "mul", ["e_a", "e_a"], ["v_e_dead"]),
        ],
        results=["v_e_inv2", "e_s2"],
    )
    then_reg = RvsdgRegion(
        name="gamma_b_then",
        args=["t_a", "t_b", "t_inv1", "t_s0"],
        nodes=[
            RvsdgNode("t_num", "add", ["t_a", "t_inv1"], ["v_t_num"]),
            RvsdgNode("t_div", "sdiv", ["v_t_num", "t_b"], ["v_t_q"], can_trap=True),
            RvsdgNode("t_ld0", "load", ["t_s0"], ["v_t_m0", "t_s1"], imm=0, is_stateful=True),
            RvsdgNode("t_add0", "add", ["v_t_m0", "v_t_q"], ["v_t_m0n"]),
            RvsdgNode("t_st0", "store", ["t_s1", "v_t_m0n"], ["t_s2"], imm=0, is_stateful=True),
            RvsdgNode("t_step", "add", ["v_t_q", "t_inv1"], ["v_t_step"]),
        ],
        results=["v_t_step", "t_s2"],
    )

    # Theta body (tail-controlled loop): args = [a, b, n, i, acc, state]
    # results = [repeat_pred, a, b, n, i_next, acc_next, state_next]
    theta_body = RvsdgRegion(
        name="theta_loop_body",
        args=["l_a", "l_b", "l_n", "l_i", "l_acc", "l_s0"],
        nodes=[
            RvsdgNode("l_c0", "const", [], ["v_l_c0"], imm=0),
            RvsdgNode("l_c1", "const", [], ["v_l_c1"], imm=1),
            RvsdgNode("l_c2", "const", [], ["v_l_c2"], imm=2),
            RvsdgNode("l_mul", "mul", ["l_a", "v_l_c2"], ["v_l_mul"]),
            RvsdgNode("l_inv", "add", ["v_l_mul", "v_l_c1"], ["v_l_inv"]),
            RvsdgNode("l_nz", "ne", ["l_b", "v_l_c0"], ["v_l_nz"]),
            RvsdgNode(
                "gamma_b",
                "gamma",
                ["v_l_nz", "l_a", "l_b", "v_l_inv", "l_s0"],
                ["v_l_step", "l_s1"],
                subregions=[else_reg, then_reg],
            ),
            RvsdgNode("l_acc_n", "add", ["l_acc", "v_l_step"], ["v_l_acc_n"]),
            RvsdgNode("l_i_n", "add", ["l_i", "v_l_c1"], ["v_l_i_n"]),
            RvsdgNode("l_cont", "lt", ["v_l_i_n", "l_n"], ["v_l_cont"]),
        ],
        results=["v_l_cont", "l_a", "l_b", "l_n", "v_l_i_n", "v_l_acc_n", "l_s1"],
    )

    # Outer Gamma (n > 0): subregion 0 = skip loop, subregion 1 = execute Theta
    skip_reg = RvsdgRegion(
        name="gamma_n_skip",
        args=["sk_a", "sk_b", "sk_n", "sk_i0", "sk_acc0", "sk_s0"],
        nodes=[],
        results=["sk_acc0", "sk_s0"],
    )
    run_reg = RvsdgRegion(
        name="gamma_n_run",
        args=["rn_a", "rn_b", "rn_n", "rn_i0", "rn_acc0", "rn_s0"],
        nodes=[
            RvsdgNode(
                "theta_main",
                "theta",
                ["rn_a", "rn_b", "rn_n", "rn_i0", "rn_acc0", "rn_s0"],
                ["rn_a_o", "rn_b_o", "rn_n_o", "rn_i_o", "rn_acc_o", "rn_s_o"],
                subregions=[theta_body],
            )
        ],
        results=["rn_acc_o", "rn_s_o"],
    )

    root = RvsdgRegion(
        name="lambda_root",
        args=["r_a", "r_b", "r_n", "r_s0"],
        nodes=[
            RvsdgNode("r_c0", "const", [], ["v_r_c0"], imm=0),
            RvsdgNode("r_gt0", "lt", ["v_r_c0", "r_n"], ["v_r_gt0"]),
            RvsdgNode(
                "gamma_n",
                "gamma",
                ["v_r_gt0", "r_a", "r_b", "r_n", "v_r_c0", "v_r_c0", "r_s0"],
                ["v_r_acc", "r_s1"],
                subregions=[skip_reg, run_reg],
            ),
            RvsdgNode("r_ld0", "load", ["r_s1"], ["v_r_m0", "r_s2"], imm=0, is_stateful=True),
            RvsdgNode("r_ld1", "load", ["r_s2"], ["v_r_m1", "r_s3"], imm=1, is_stateful=True),
        ],
        results=["v_r_acc", "v_r_m0", "v_r_m1", "r_s3"],
    )
    root.verify_acyclic_and_scoped()
    return root


def optimize_rvsdg(root: RvsdgRegion) -> tuple[RvsdgRegion, dict[str, int]]:
    """Apply RVSDG Dead Node Elimination (DNE) + Loop-Invariant Node Push-Out (PSH).

    Note: Neither DNE nor PSH needs a dominator tree, CFG loop finder, or
    control+effect chain patching — region boundaries carry exact scope!
    """
    dne_removed = 0
    psh_hoisted = 0
    psh_blocked_trapping = 0

    def run_dne(reg: RvsdgRegion) -> None:
        nonlocal dne_removed
        # First recurse into subregions
        for nd in reg.nodes:
            for sub in nd.subregions:
                run_dne(sub)
        # Backward reachability from region results
        live_ports: set[str] = set(reg.results)
        kept: list[RvsdgNode] = []
        for nd in reversed(reg.nodes):
            if any(o in live_ports for o in nd.outputs):
                kept.append(nd)
                live_ports.update(nd.inputs)
            else:
                dne_removed += 1
        kept.reverse()
        reg.nodes = kept

    def run_theta_psh(parent_reg: RvsdgRegion) -> None:
        """Push loop-invariant pure, non-trapping simple nodes out of Theta."""
        nonlocal psh_hoisted, psh_blocked_trapping
        new_parent_nodes: list[RvsdgNode] = []
        for nd in parent_reg.nodes:
            if nd.op == "gamma":
                for sub in nd.subregions:
                    run_theta_psh(sub)
                new_parent_nodes.append(nd)
                continue
            if nd.op != "theta":
                new_parent_nodes.append(nd)
                continue

            body = nd.subregions[0]
            # Loop-invariant region args: arg[k] == result[k+1] (unchanged across iterations)
            inv_port_to_parent: dict[str, str] = {}
            for k, arg_name in enumerate(body.args):
                if body.results[k + 1] == arg_name:
                    inv_port_to_parent[arg_name] = nd.inputs[k]

            hoisted_nodes: list[RvsdgNode] = []
            kept_body: list[RvsdgNode] = []
            for bnd in body.nodes:
                if bnd.op in ("gamma", "theta"):
                    # Count trapping ops inside inner gamma that cannot cross region boundary
                    for sub in bnd.subregions:
                        for snd in sub.nodes:
                            if snd.can_trap:
                                psh_blocked_trapping += 1
                    kept_body.append(bnd)
                    continue
                if (
                    not bnd.is_stateful
                    and not bnd.can_trap
                    and all(inp in inv_port_to_parent for inp in bnd.inputs)
                ):
                    # Hoist node out into parent_reg and route result as new loop-invariant arg
                    parent_out = f"hoisted_{bnd.outputs[0]}"
                    parent_inps = [inv_port_to_parent[inp] for inp in bnd.inputs]
                    hoisted_nodes.append(
                        RvsdgNode(
                            nid=f"hoisted_{bnd.nid}",
                            op=bnd.op,
                            inputs=parent_inps,
                            outputs=[parent_out],
                            imm=bnd.imm,
                        )
                    )
                    # Add invariant pass-through port on Theta
                    nd.inputs.append(parent_out)
                    nd.outputs.append(f"hoisted_out_{bnd.outputs[0]}")
                    body.args.append(bnd.outputs[0])
                    body.results.append(bnd.outputs[0])
                    inv_port_to_parent[bnd.outputs[0]] = parent_out
                    psh_hoisted += 1
                else:
                    kept_body.append(bnd)
            body.nodes = kept_body
            new_parent_nodes.extend(hoisted_nodes)
            new_parent_nodes.append(nd)
        parent_reg.nodes = new_parent_nodes

    run_dne(root)
    run_theta_psh(root)
    run_dne(root)
    root.verify_acyclic_and_scoped()

    def count_nodes(reg: RvsdgRegion) -> tuple[int, int]:
        n_nodes = len(reg.nodes)
        n_regions = 1
        for nd in reg.nodes:
            for sub in nd.subregions:
                sn, sr = count_nodes(sub)
                n_nodes += sn
                n_regions += sr
        return n_nodes, n_regions

    total_nodes, total_regions = count_nodes(root)
    stats = {
        "total_nodes": total_nodes,
        "total_regions": total_regions,
        "dne_removed": dne_removed,
        "psh_hoisted_from_theta": psh_hoisted,
        "psh_blocked_trapping_in_gamma": psh_blocked_trapping,
        "required_cfg_analyses": 0,  # No domtree or loop-finder required!
    }
    return root, stats


def eval_rvsdg(root: RvsdgRegion, a: int, b: int, n: int, m0: int, m1: int) -> EvalResult:
    mem = [m0, m1]
    trace: list[tuple[str, int, int]] = []
    state_token = 0

    def eval_region(reg: RvsdgRegion, arg_vals: list[Any]) -> list[Any] | TrapResult:
        nonlocal state_token
        env: dict[str, Any] = dict(zip(reg.args, arg_vals, strict=True))
        for nd in reg.nodes:
            in_vals = [env[i] for i in nd.inputs]
            if nd.op == "const":
                outs: list[Any] = [nd.imm]
            elif nd.op == "add":
                outs = [in_vals[0] + in_vals[1]]
            elif nd.op == "mul":
                outs = [in_vals[0] * in_vals[1]]
            elif nd.op == "lt":
                outs = [int(in_vals[0] < in_vals[1])]
            elif nd.op == "ne":
                outs = [int(in_vals[0] != in_vals[1])]
            elif nd.op == "sdiv":
                q = trunc_div(in_vals[0], in_vals[1])
                if q is None:
                    return TrapResult("div_by_zero")
                outs = [q]
            elif nd.op == "load":
                assert in_vals[0] == state_token, "linear state token violated on load"
                state_token += 1
                outs = [mem[nd.imm], state_token]
            elif nd.op == "store":
                assert in_vals[0] == state_token, "linear state token violated on store"
                mem[nd.imm] = in_vals[1]
                trace.append(("store", nd.imm, mem[nd.imm]))
                state_token += 1
                outs = [state_token]
            elif nd.op == "gamma":
                pred = int(bool(in_vals[0]))
                sub_res = eval_region(nd.subregions[pred], in_vals[1:])
                if isinstance(sub_res, TrapResult):
                    return sub_res
                outs = sub_res
            elif nd.op == "theta":
                cur_vals = list(in_vals)
                while True:
                    sub_res = eval_region(nd.subregions[0], cur_vals)
                    if isinstance(sub_res, TrapResult):
                        return sub_res
                    repeat = int(bool(sub_res[0]))
                    cur_vals = sub_res[1:]
                    if not repeat:
                        break
                outs = cur_vals
            else:
                raise ValueError(f"unknown RVSDG op {nd.op}")
            for o, v in zip(nd.outputs, outs, strict=True):
                env[o] = v
        return [env[r] for r in reg.results]

    res = eval_region(root, [a, b, n, state_token])
    if isinstance(res, TrapResult):
        return res
    acc_v, m0_v, m1_v, final_tok = res
    assert final_tok == state_token
    return OkResult(acc=acc_v, mem0=m0_v, mem1=m1_v, trace=tuple(trace))


# ---------------------------------------------------------------------------
# 4. Irreducible CFG Restructuring Probe (Bahmann et al. 2015 / jlm)
# ---------------------------------------------------------------------------

def probe_irreducible_restructuring() -> dict[str, Any]:
    """Compare original 2-entry irreducible loop vs predicate-restructured form.

    Original irreducible CFG:
      entry: if enter_at_b -> L2 else -> L1
      L1: x = x + 1; if x < limit -> L2 else -> exit
      L2: x = x + 2; if x < limit -> L1 else -> exit

    Bahmann et al. (TACO 2015) / jlm ControlFlowRestructuring transforms this
    without duplicating L1/L2 by introducing:
      - entry selector predicate `#q` in {0 (L1), 1 (L2)}
      - loop repetition predicate `#r` in {0 (exit), 1 (repeat)}
    wrapping a single tail-controlled Theta containing a Gamma dispatching on `#q`.
    """
    def run_irreducible(enter_at_b: bool, x0: int, limit: int) -> tuple[int, int]:
        x = x0
        branches = 0
        # Entry branch
        branches += 1
        pc = "L2" if enter_at_b else "L1"
        while True:
            if pc == "L1":
                x += 1
                branches += 1
                if x < limit:
                    pc = "L2"
                else:
                    return x, branches
            else:
                x += 2
                branches += 1
                if x < limit:
                    pc = "L1"
                else:
                    return x, branches

    def run_restructured_theta_gamma(enter_at_b: bool, x0: int, limit: int) -> tuple[int, int]:
        x = x0
        branches = 0
        # Set initial entry selector #q (0=L1, 1=L2)
        branches += 1
        q = 1 if enter_at_b else 0
        while True:
            # Synthetic Gamma dispatch on #q
            branches += 1
            if q == 0:
                x += 1
                branches += 1
                if x < limit:
                    q, r = 1, 1
                else:
                    r = 0
            else:
                x += 2
                branches += 1
                if x < limit:
                    q, r = 0, 1
                else:
                    r = 0
            # Synthetic tail-controlled Theta repetition branch on #r
            branches += 1
            if r == 0:
                return x, branches

    orig_branches_total = 0
    restruct_branches_total = 0
    for enter_at_b in (False, True):
        for x0 in (0, 3, 10):
            for limit in (0, 5, 12):
                ox, ob = run_irreducible(enter_at_b, x0, limit)
                rx, rb = run_restructured_theta_gamma(enter_at_b, x0, limit)
                assert ox == rx, f"irreducible mismatch: {ox} != {rx}"
                orig_branches_total += ob
                restruct_branches_total += rb

    return {
        "equivalence_verified": True,
        "synthetic_predicate_vars": 2,  # #q (entry/state selector) and #r (repetition)
        "duplicated_body_blocks": 0,  # Avoids exponential node splitting
        "dynamic_branches_original": orig_branches_total,
        "dynamic_branches_restructured": restruct_branches_total,
        "dynamic_branch_ratio": round(restruct_branches_total / orig_branches_total, 3),
    }


# ---------------------------------------------------------------------------
# 5. Cranelift aegraph Invariants: Shared-DAG Extraction & `subsume` Dominance
# ---------------------------------------------------------------------------

def probe_aegraph_invariants() -> dict[str, Any]:
    """Verify two core aegraph invariants from Cranelift & Fallin (2026):
      1. Tree-DP extraction ignoring DAG sharing picks cost 14 vs optimal 10
         on `v0 = union(v10, v11); v1 = union(v10, v12)` with costs 10, 7, 7.
      2. Dropping a value operand in a rewrite (`select 1 x y => x`) without
         `subsume` allows an e-class union whose available_block is wider than
         `y`'s definition block, producing an SSA dominance violation if extracted
         in a scope dominating `y`.
    """
    # (1) Shared-DAG extraction counterexample
    costs = {"v10": 10, "v11": 7, "v12": 7}
    eclasses = {"v0": ("v10", "v11"), "v1": ("v10", "v12")}
    # Tree DP picks independent minimum per root:
    dp_pick = {c: min(opts, key=lambda n: costs[n]) for c, opts in eclasses.items()}
    dp_total_cost = sum(costs[n] for n in set(dp_pick.values()))
    # Exhaustive DAG-aware optimum over 2x2 assignments:
    best_dag_cost = min(
        sum(costs[n] for n in {c0, c1})
        for c0 in eclasses["v0"]
        for c1 in eclasses["v1"]
    )
    assert dp_total_cost == 14 and best_dag_cost == 10

    # (2) `subsume` dominance check:
    # Block bb0 (entry) defines %x; dominated child bb1 defines %y and computes
    # %s = select(1, %x, %y) => rewritten to %x.
    # Dominator depths: bb0=0, bb1=1, bb2=1 (sibling of bb1, does NOT see %y).
    def_block = {"%x": "bb0", "%y": "bb1", "%s_orig": "bb1"}
    doms = {
        "bb0": {"bb0"},
        "bb1": {"bb0", "bb1"},
        "bb2": {"bb0", "bb2"},
    }
    # Without subsume, union(%s_orig, %x) contains an e-node referencing %y.
    # Its minimum available block must be bb1 (cannot be promoted to bb0!),
    # or if aliased to %x at bb0, using it in bb2 breaks dominance:
    union_members_no_subsume = [("%s_orig", ("%x", "%y")), ("%x", ())]
    def is_eclass_legal_at(members: list[tuple[str, tuple[str, ...]]], use_bb: str) -> bool:
        for _, deps in members:
            for d in deps:
                if def_block[d] not in doms[use_bb]:
                    return False
        return True

    no_subsume_legal_in_bb2 = is_eclass_legal_at(union_members_no_subsume, "bb2")
    with_subsume_legal_in_bb2 = is_eclass_legal_at([("%x", ())], "bb2")
    assert not no_subsume_legal_in_bb2 and with_subsume_legal_in_bb2

    return {
        "tree_dp_cost": dp_total_cost,
        "dag_optimal_cost": best_dag_cost,
        "no_subsume_legal_in_sibling_block": no_subsume_legal_in_bb2,
        "with_subsume_legal_in_sibling_block": with_subsume_legal_in_bb2,
    }


# ---------------------------------------------------------------------------
# 6. Main test driver
# ---------------------------------------------------------------------------

def main() -> int:
    test_vectors = [
        # (a, b, n, m0, m1)
        (10, 2, 4, 1, 5),     # normal nonzero divisor, multiple iterations
        (-7, 3, 5, 0, 0),     # negative dividend
        (10, 0, 3, 1, 5),     # b == 0: else branch taken; div MUST NOT trap!
        (10, 0, 0, 7, 9),     # n == 0 and b == 0: loop skipped; div MUST NOT trap!
        (42, 5, 0, 3, 4),     # n == 0: zero-iteration head-controlled loop
        (0, -1, 2, 10, 20),   # negative divisor
    ]

    # (a) Block-Arg CFG SSA
    cfg_orig = build_cfg_ssa()
    cfg_orig.verify_ssa()
    cfg_opt, cfg_stats = optimize_cfg_ssa(cfg_orig)

    # (b) Sea-of-Nodes (sound pinned vs unsound unpinned division)
    son_pinned, h_pinned = build_sea_of_nodes(pin_div_to_guard=True)
    _, ord_pinned, son_pinned_stats = schedule_sea_of_nodes_to_cfg(son_pinned, h_pinned)

    son_unpinned, h_unpinned = build_sea_of_nodes(pin_div_to_guard=False)
    _, ord_unpinned, son_unpinned_stats = schedule_sea_of_nodes_to_cfg(son_unpinned, h_unpinned)

    # (c) RVSDG (original and optimized with DNE + Theta PSH)
    rvsdg_orig = build_rvsdg()
    rvsdg_opt, rvsdg_stats = optimize_rvsdg(build_rvsdg())

    # Verify observational equivalence across all valid IRs and all vectors
    spurious_traps_unpinned = 0
    for vec in test_vectors:
        ref = eval_reference(*vec)
        r_cfg_orig = eval_cfg_ssa(cfg_orig, *vec)
        r_cfg_opt = eval_cfg_ssa(cfg_opt, *vec)
        r_son_pin = eval_scheduled_son(son_pinned, h_pinned, ord_pinned, *vec)
        r_son_unpin = eval_scheduled_son(son_unpinned, h_unpinned, ord_unpinned, *vec)
        r_rvsdg_orig = eval_rvsdg(rvsdg_orig, *vec)
        r_rvsdg_opt = eval_rvsdg(rvsdg_opt, *vec)

        assert r_cfg_orig == ref, f"CFG orig mismatch on {vec}: {r_cfg_orig} != {ref}"
        assert r_cfg_opt == ref, f"CFG opt mismatch on {vec}: {r_cfg_opt} != {ref}"
        assert r_son_pin == ref, f"SoN pinned mismatch on {vec}: {r_son_pin} != {ref}"
        assert r_rvsdg_orig == ref, f"RVSDG orig mismatch on {vec}: {r_rvsdg_orig} != {ref}"
        assert r_rvsdg_opt == ref, f"RVSDG opt mismatch on {vec}: {r_rvsdg_opt} != {ref}"

        if vec[1] == 0:
            # Unpinned SoN hoists division into bb_entry -> spurious trap!
            assert r_son_unpin == TrapResult("div_by_zero"), (
                f"Expected spurious trap for unpinned SoN on {vec}, got {r_son_unpin}"
            )
            spurious_traps_unpinned += 1
        else:
            assert r_son_unpin == ref

    # Verify placement properties directly
    assert son_pinned_stats["inv1_block"] == "bb_entry", "Pure invariant should float to entry"
    assert son_pinned_stats["div_block"] == "bb_then", "Pinned div must stay in guarded bb_then"
    assert son_unpinned_stats["div_block"] == "bb_entry", "Unpinned div illegally floats to bb_entry"
    assert spurious_traps_unpinned == 2

    irred_stats = probe_irreducible_restructuring()
    aegraph_stats = probe_aegraph_invariants()

    summary = {
        "test_vectors_checked": len(test_vectors),
        "cfg_ssa": cfg_stats,
        "sea_of_nodes_pinned": son_pinned_stats,
        "sea_of_nodes_unpinned_bug": {
            "div_scheduled_block": son_unpinned_stats["div_block"],
            "spurious_traps_observed": spurious_traps_unpinned,
        },
        "rvsdg": rvsdg_stats,
        "irreducible_cfg_restructuring": irred_stats,
        "aegraph_invariants": aegraph_stats,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
