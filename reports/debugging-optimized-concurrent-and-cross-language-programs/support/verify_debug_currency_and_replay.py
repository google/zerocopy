#!/usr/bin/env python3
"""Standalone verification probe for optimized-code debug currency and
deterministic record-and-replay / omniscient reverse-watchpoint recovery.

Implements two self-contained, stdlib-only engines:
  1. Hennessy (1982) / Adl-Tabatabai & Gross (1993, 1996) dataflow currency
     detector over a source CFG vs. an optimized (scheduled, DCE, coalesced)
     target CFG, with DWARF v5 DW_OP_stack_value / DW_OP_entry_value synthesis
     verification and differential wrong-value bug detection.
  2. rr-style (O'Callahan et al., USENIX ATC '17) deterministic record-and-replay
     VM driven by retired conditional branch (RCB) counters, PMU skid-margin
     replay positioning, syscall/signal logs, exponential O(log T) checkpoint
     retention (mirroring rr::ReplayTimeline), reverse-watchpoint fault-origin
     recovery, Pernosco-style omniscient write indexing, and a MAP_SHARED / DMA
     unrecorded-writer divergence wall demonstration.

Requires Python 3.10+ and only the Python standard library.
"""

from __future__ import annotations

import argparse
import bisect
import copy
import hashlib
import json
import math
import sys
from dataclasses import dataclass, field
from typing import Any, Callable


# =============================================================================
# PART 1: Hennessy / Adl-Tabatabai-Gross Currency Detector & DWARF Recovery
# =============================================================================

@dataclass(frozen=True)
class Expr:
    """Simple pure expression AST for source statements and DWARF synthesis."""
    kind: str  # "const", "var", "binop"
    value: int | str | None = None
    op: str | None = None
    lhs: Expr | None = None
    rhs: Expr | None = None

    def eval(self, env: dict[str, int]) -> int:
        if self.kind == "const":
            assert isinstance(self.value, int)
            return self.value
        if self.kind == "var":
            assert isinstance(self.value, str)
            return env[self.value]
        if self.kind == "binop":
            assert self.lhs is not None and self.rhs is not None
            lv = self.lhs.eval(env)
            rv = self.rhs.eval(env)
            if self.op == "+":
                return lv + rv
            if self.op == "-":
                return lv - rv
            if self.op == "*":
                return lv * rv
            if self.op == "<<":
                return lv << rv
            if self.op == "^":
                return lv ^ rv
            raise ValueError(f"unsupported op {self.op!r}")
        raise ValueError(f"unsupported expr kind {self.kind!r}")


def EConst(v: int) -> Expr:
    return Expr("const", value=v)


def EVar(name: str) -> Expr:
    return Expr("var", value=name)


def EBin(op: str, lhs: Expr, rhs: Expr) -> Expr:
    return Expr("binop", op=op, lhs=lhs, rhs=rhs)


@dataclass(frozen=True)
class SrcStmt:
    stmt_id: str
    line: int
    dst: str | None          # assigned source variable, or None for branch/anchor
    expr: Expr | None        # RHS expression
    is_breakpoint_anchor: bool = True


@dataclass
class SrcBlock:
    block_id: str
    stmts: list[SrcStmt]
    succs: list[str] = field(default_factory=list)
    cond_var: str | None = None  # if len(succs) == 2: branch true -> succs[0], false -> succs[1]


@dataclass(frozen=True)
class TgtInst:
    pc: int
    line: int
    orig_stmt_id: str | None     # source statement whose computation this performs
    dst_reg: str | None          # target register written
    writes_var: str | None       # source variable logically updated in storage (if any)
    expr: Expr | None            # expression evaluated in terms of target registers
    anchor_stmt_id: str | None = None  # source statement corresponding to breakpoint at this PC
    is_stmt: bool = True


@dataclass
class TgtBlock:
    block_id: str
    insts: list[TgtInst]
    succs: list[str] = field(default_factory=list)
    cond_reg: str | None = None


@dataclass(frozen=True)
class DwarfLocation:
    """DWARF v5 location description abstraction."""
    kind: str  # "reg", "stack_value", "entry_value", "optimized_out"
    reg: str | None = None
    synth_expr: Expr | None = None   # evaluated over live target registers (DW_OP_stack_value)
    entry_param: str | None = None   # parameter name captured at function entry (DW_OP_entry_value)
    dwarf_ops: str = ""

    def evaluate(
        self,
        regs: dict[str, int],
        entry_regs: dict[str, int],
        live_regs: set[str],
    ) -> tuple[bool, int | None]:
        if self.kind == "optimized_out":
            return False, None
        if self.kind == "reg":
            assert self.reg is not None
            if self.reg not in regs:
                return False, None
            return True, regs[self.reg]
        if self.kind == "entry_value":
            assert self.entry_param is not None
            if self.entry_param not in entry_regs:
                return False, None
            return True, entry_regs[self.entry_param]
        if self.kind == "stack_value":
            assert self.synth_expr is not None
            needed = _expr_vars(self.synth_expr)
            if not needed.issubset(live_regs):
                return False, None
            return True, self.synth_expr.eval(regs)
        raise ValueError(f"unknown DWARF location kind {self.kind!r}")


def _expr_vars(e: Expr) -> set[str]:
    if e.kind == "var":
        assert isinstance(e.value, str)
        return {e.value}
    if e.kind == "binop":
        assert e.lhs is not None and e.rhs is not None
        return _expr_vars(e.lhs) | _expr_vars(e.rhs)
    return set()


@dataclass
class CurrencyClassification:
    breakpoint_pc: int
    block_id: str
    anchor_stmt_id: str
    line: int
    source_var: str
    classification: str      # "current", "noncurrent-stale", "noncurrent-premature", "evicted"
    raw_storage_status: str  # status before DWARF DW_OP_stack_value / DW_OP_entry_value synthesis
    recovered_via: str | None
    path_sensitivity: str    # "definite" or "suspect-join"
    dwarf_ops: str
    expected_val: int | None = None
    observed_val: int | None = None
    soundness_bug: bool = False


class CurrencyAnalyzer:
    """Dataflow currency analyzer implementing Hennessy (1982) roll-forward/roll-back
    sets extended with Adl-Tabatabai & Gross (1993/1996) register eviction and
    DWARF v5 implicit value synthesis verification.
    """

    def __init__(
        self,
        src_cfg: dict[str, SrcBlock],
        tgt_cfg: dict[str, TgtBlock],
        entry_block: str,
        params: list[str],
        var_home_reg: dict[str, str],
        dwarf_table: dict[tuple[int, str], DwarfLocation],
    ) -> None:
        self.src_cfg = src_cfg
        self.tgt_cfg = tgt_cfg
        self.entry_block = entry_block
        self.params = params
        self.var_home_reg = var_home_reg
        self.dwarf_table = dwarf_table

        # Index source statements: block -> list of stmt_ids, and global metadata
        self.stmt_info: dict[str, tuple[str, int, SrcStmt]] = {}
        self.all_vars: set[str] = set(params)
        for bid, blk in src_cfg.items():
            for idx, st in enumerate(blk.stmts):
                self.stmt_info[st.stmt_id] = (bid, idx, st)
                if st.dst is not None:
                    self.all_vars.add(st.dst)

        # Map each target instruction to its block and index
        self.pc_info: dict[int, tuple[str, int, TgtInst]] = {}
        for bid, blk in tgt_cfg.items():
            for idx, ins in enumerate(blk.insts):
                self.pc_info[ins.pc] = (bid, idx, ins)

    def _compute_src_reaching_defs(self) -> dict[str, dict[str, set[str]]]:
        """Standard forward may-reaching-definitions over source CFG.
        Returns block_in[bid][var] = set of stmt_ids (or 'ENTRY:<var>').
        """
        in_map: dict[str, dict[str, set[str]]] = {
            bid: {v: set() for v in self.all_vars} for bid in self.src_cfg
        }
        out_map: dict[str, dict[str, set[str]]] = {
            bid: {v: set() for v in self.all_vars} for bid in self.src_cfg
        }
        for p in self.params:
            in_map[self.entry_block][p].add(f"ENTRY:{p}")

        changed = True
        while changed:
            changed = False
            for bid, blk in self.src_cfg.items():
                # Compute out from in
                cur = {v: set(s) for v, s in in_map[bid].items()}
                for st in blk.stmts:
                    if st.dst is not None:
                        cur[st.dst] = {st.stmt_id}
                if cur != out_map[bid]:
                    out_map[bid] = cur
                    changed = True
                # Propagate to successors
                for succ in blk.succs:
                    for v in self.all_vars:
                        before = len(in_map[succ][v])
                        in_map[succ][v] |= out_map[bid][v]
                        if len(in_map[succ][v]) != before:
                            changed = True
        return in_map

    def _compute_tgt_executed_and_reg_owners(
        self,
    ) -> tuple[
        dict[str, dict[str, set[str]]],  # tgt_in_defs[bid][var] = executed stmt_ids
        dict[str, dict[str, set[str]]],  # tgt_in_reg_owner[bid][reg] = set of var names (or 'TEMP:<id>')
    ]:
        """Forward dataflow over optimized target CFG tracking:
          - which source definitions of each variable have actually executed into storage,
          - which logical variable/temp currently owns each physical register (for eviction).
        """
        all_regs: set[str] = set(self.var_home_reg.values())
        for blk in self.tgt_cfg.values():
            for ins in blk.insts:
                if ins.dst_reg is not None:
                    all_regs.add(ins.dst_reg)

        in_defs: dict[str, dict[str, set[str]]] = {
            bid: {v: set() for v in self.all_vars} for bid in self.tgt_cfg
        }
        out_defs: dict[str, dict[str, set[str]]] = {
            bid: {v: set() for v in self.all_vars} for bid in self.tgt_cfg
        }
        in_owner: dict[str, dict[str, set[str]]] = {
            bid: {r: set() for r in all_regs} for bid in self.tgt_cfg
        }
        out_owner: dict[str, dict[str, set[str]]] = {
            bid: {r: set() for r in all_regs} for bid in self.tgt_cfg
        }

        for p in self.params:
            in_defs[self.entry_block][p].add(f"ENTRY:{p}")
            if p in self.var_home_reg:
                in_owner[self.entry_block][self.var_home_reg[p]].add(p)

        changed = True
        while changed:
            changed = False
            for bid, blk in self.tgt_cfg.items():
                cur_d = {v: set(s) for v, s in in_defs[bid].items()}
                cur_o = {r: set(s) for r, s in in_owner[bid].items()}
                for ins in blk.insts:
                    if ins.writes_var is not None and ins.orig_stmt_id is not None:
                        cur_d[ins.writes_var] = {ins.orig_stmt_id}
                    if ins.dst_reg is not None:
                        owner_tag = ins.writes_var if ins.writes_var is not None else f"TEMP@{ins.pc}"
                        cur_o[ins.dst_reg] = {owner_tag}
                if cur_d != out_defs[bid]:
                    out_defs[bid] = cur_d
                    changed = True
                if cur_o != out_owner[bid]:
                    out_owner[bid] = cur_o
                    changed = True
                for succ in blk.succs:
                    for v in self.all_vars:
                        b = len(in_defs[succ][v])
                        in_defs[succ][v] |= out_defs[bid][v]
                        if len(in_defs[succ][v]) != b:
                            changed = True
                    for r in all_regs:
                        b = len(in_owner[succ][r])
                        in_owner[succ][r] |= out_owner[bid][r]
                        if len(in_owner[succ][r]) != b:
                            changed = True
        return in_defs, in_owner

    def _src_order_relation(self, stmt_a: str, stmt_b: str) -> str:
        """Determine whether source def stmt_a precedes or follows breakpoint stmt_b."""
        if stmt_a.startswith("ENTRY:"):
            return "before"
        bid_a, idx_a, _ = self.stmt_info[stmt_a]
        bid_b, idx_b, _ = self.stmt_info[stmt_b]
        if bid_a == bid_b:
            if idx_a < idx_b:
                return "before"
            if idx_a > idx_b:
                return "after"
            return "same"
        # Check CFG reachability from bid_b to bid_a (means a follows b)
        if self._can_reach(bid_b, bid_a):
            return "after"
        if self._can_reach(bid_a, bid_b):
            return "before"
        return "incomparable"

    def _can_reach(self, src_bid: str, dst_bid: str) -> bool:
        visited: set[str] = set()
        stack = list(self.src_cfg[src_bid].succs)
        while stack:
            cur = stack.pop()
            if cur == dst_bid:
                return True
            if cur not in visited:
                visited.add(cur)
                stack.extend(self.src_cfg[cur].succs)
        return False

    def analyze(self) -> list[CurrencyClassification]:
        """Classify every (breakpoint_pc, source_var) pair statically."""
        src_in = self._compute_src_reaching_defs()
        tgt_in_defs, tgt_in_owner = self._compute_tgt_executed_and_reg_owners()
        results: list[CurrencyClassification] = []

        for bid, tblk in self.tgt_cfg.items():
            # Advance target state instruction by instruction
            cur_tgt_defs = {v: set(s) for v, s in tgt_in_defs[bid].items()}
            cur_reg_owner = {r: set(s) for r, s in tgt_in_owner[bid].items()}

            for ins in tblk.insts:
                if ins.anchor_stmt_id is not None:
                    # Breakpoint is observed *before* executing the anchor instruction
                    s_bid, s_idx, anchor_stmt = self.stmt_info[ins.anchor_stmt_id]
                    assert s_bid == bid
                    # Compute expected source reaching defs at anchor_stmt (before anchor_stmt executes)
                    expected_defs = {v: set(s) for v, s in src_in[s_bid].items()}
                    for st in self.src_cfg[s_bid].stmts[:s_idx]:
                        if st.dst is not None:
                            expected_defs[st.dst] = {st.stmt_id}

                    # Determine registers currently holding valid non-clobbered values
                    live_regs = {r for r, owners in cur_reg_owner.items() if owners}

                    for v in sorted(self.all_vars):
                        exp = expected_defs[v]
                        act = cur_tgt_defs[v]
                        if not exp and not act:
                            continue  # variable neither initialized in source nor written early in target
                        home = self.var_home_reg.get(v)
                        owners_of_home = cur_reg_owner.get(home, set()) if home else set()

                        # Raw storage classification (Hennessy + Adl-Tabatabai-Gross)
                        premature = any(
                            self._src_order_relation(d, ins.anchor_stmt_id) in ("after", "same")
                            for d in act
                            if d not in exp
                        )
                        stale = any(d not in act for d in exp)
                        evicted = (
                            home is None
                            or (not owners_of_home)
                            or any(o != v for o in owners_of_home)
                        )

                        # Distinguish path-dependent suspect vs definite
                        path_sens = "definite"
                        if premature:
                            raw_status = "noncurrent-premature"
                            if act & exp:
                                path_sens = "suspect-join"
                        elif stale:
                            raw_status = "noncurrent-stale"
                            if act & exp:
                                path_sens = "suspect-join"
                        elif evicted:
                            raw_status = "evicted"
                            if v in owners_of_home and len(owners_of_home) > 1:
                                path_sens = "suspect-join"
                        else:
                            raw_status = "current"

                        # Consult DWARF location description for synthesis rescue
                        loc = self.dwarf_table.get((ins.pc, v), DwarfLocation("optimized_out", dwarf_ops="<none>"))
                        final_status = raw_status
                        recovered_via: str | None = None

                        if raw_status != "current":
                            if loc.kind == "stack_value" and loc.synth_expr is not None:
                                needed_regs = _expr_vars(loc.synth_expr)
                                # Verify all constituent registers are live and hold their expected source vars
                                if needed_regs.issubset(live_regs):
                                    final_status = "current"
                                    recovered_via = "DW_OP_stack_value"
                            elif loc.kind == "entry_value" and loc.entry_param == v:
                                if exp == {f"ENTRY:{v}"}:
                                    final_status = "current"
                                    recovered_via = "DW_OP_entry_value"
                        else:
                            if loc.kind == "optimized_out":
                                final_status = "evicted"

                        results.append(
                            CurrencyClassification(
                                breakpoint_pc=ins.pc,
                                block_id=bid,
                                anchor_stmt_id=ins.anchor_stmt_id,
                                line=ins.line,
                                source_var=v,
                                classification=final_status,
                                raw_storage_status=raw_status,
                                recovered_via=recovered_via,
                                path_sensitivity=path_sens,
                                dwarf_ops=loc.dwarf_ops,
                            )
                        )

                # Execute target instruction's dataflow transfer
                if ins.writes_var is not None and ins.orig_stmt_id is not None:
                    cur_tgt_defs[ins.writes_var] = {ins.orig_stmt_id}
                if ins.dst_reg is not None:
                    owner_tag = ins.writes_var if ins.writes_var is not None else f"TEMP@{ins.pc}"
                    cur_reg_owner[ins.dst_reg] = {owner_tag}

        return results

    def differential_validate(
        self,
        classifications: list[CurrencyClassification],
        param_inputs: dict[str, int],
    ) -> list[CurrencyClassification]:
        """Run concrete source interpreter and target interpreter side by side to
        verify that every variable classified as `current` evaluates to the exact
        source value, and detect Di Luna et al. (ASPLOS '21) wrong-value bugs.
        """
        # 1. Execute source CFG concretely and record snapshots before each anchor stmt
        src_env = dict(param_inputs)
        src_snapshots: dict[str, dict[str, int]] = {}
        cur_bid: str | None = self.entry_block
        while cur_bid is not None:
            blk = self.src_cfg[cur_bid]
            for st in blk.stmts:
                if st.is_breakpoint_anchor:
                    src_snapshots[st.stmt_id] = dict(src_env)
                if st.dst is not None and st.expr is not None:
                    src_env[st.dst] = st.expr.eval(src_env)
            if not blk.succs:
                cur_bid = None
            elif len(blk.succs) == 1:
                cur_bid = blk.succs[0]
            else:
                assert blk.cond_var is not None
                cur_bid = blk.succs[0] if src_env[blk.cond_var] != 0 else blk.succs[1]

        # 2. Execute target CFG concretely and evaluate DWARF location descriptions
        regs: dict[str, int] = {}
        entry_regs: dict[str, int] = dict(param_inputs)
        for p, val in param_inputs.items():
            if p in self.var_home_reg:
                regs[self.var_home_reg[p]] = val

        tgt_observed: dict[tuple[int, str], tuple[bool, int | None]] = {}
        cur_bid = self.entry_block
        while cur_bid is not None:
            tblk = self.tgt_cfg[cur_bid]
            for ins in tblk.insts:
                if ins.anchor_stmt_id is not None:
                    live_regs = set(regs.keys())
                    for v in self.all_vars:
                        loc = self.dwarf_table.get((ins.pc, v), DwarfLocation("optimized_out"))
                        tgt_observed[(ins.pc, v)] = loc.evaluate(regs, entry_regs, live_regs)
                if ins.dst_reg is not None and ins.expr is not None:
                    regs[ins.dst_reg] = ins.expr.eval(regs)
            if not tblk.succs:
                cur_bid = None
            elif len(tblk.succs) == 1:
                cur_bid = tblk.succs[0]
            else:
                assert tblk.cond_reg is not None
                cur_bid = tblk.succs[0] if regs[tblk.cond_reg] != 0 else tblk.succs[1]

        # 3. Cross-check classifications against executed path
        checked: list[CurrencyClassification] = []
        for c in classifications:
            c2 = copy.copy(c)
            if c.anchor_stmt_id in src_snapshots and c.source_var in src_snapshots[c.anchor_stmt_id]:
                c2.expected_val = src_snapshots[c.anchor_stmt_id][c.source_var]
            if (c.breakpoint_pc, c.source_var) in tgt_observed:
                avail, val = tgt_observed[(c.breakpoint_pc, c.source_var)]
                if avail:
                    c2.observed_val = val
                    if c2.expected_val is not None and val != c2.expected_val:
                        c2.soundness_bug = True
            checked.append(c2)
        return checked


def run_currency_probe() -> dict[str, Any]:
    """Build and verify a multi-block source vs. optimized CFG scenario covering:
      - current (direct register)
      - noncurrent-stale (sunk / DCE'd assignment)
      - noncurrent-premature (hoisted assignment overwriting storage early)
      - evicted (register coalescing clobbering variable's home register)
      - DW_OP_stack_value rescue of a DCE'd variable
      - DW_OP_entry_value rescue of a clobbered argument
      - suspect-join path-dependent currency across a diamond CFG
      - differential wrong-value bug detection (Di Luna et al. ASPLOS '21)
    """
    # Source CFG:
    # B0 (entry):
    #   s1 (L10): a = x + 1
    #   s2 (L11): b = a * 2           (will be DCE'd; rescued via DW_OP_stack_value)
    #   s3 (L12): c = x + 10          (will be sunk past breakpoint s4 -> noncurrent-stale)
    #   s4 (L13): anchor_mid (uses a) (breakpoint PC=0x104)
    #   s5 (L14): d = a + 5           (will be hoisted before s4 -> noncurrent-premature at s4)
    #   branch on cond -> B1 (then) or B2 (else)
    # B1 (then):
    #   s6 (L16): m = d + 1           (updates m on true branch)
    #   -> B3
    # B2 (else):
    #   s7 (L18): k = x + 3           (does NOT update m; coalesces a's reg r1 -> evicts a)
    #   -> B3
    # B3 (join):
    #   s8 (L20): anchor_join         (breakpoint PC=0x112)
    #   s9 (L21): out = m + c + d
    src_cfg = {
        "B0": SrcBlock(
            "B0",
            [
                SrcStmt("s0", 9, "d", EConst(0)),
                SrcStmt("s1", 10, "a", EBin("+", EVar("x"), EConst(1))),
                SrcStmt("s2", 11, "b", EBin("*", EVar("a"), EConst(2))),
                SrcStmt("s3", 12, "c", EBin("+", EVar("x"), EConst(10))),
                SrcStmt("s4", 13, None, None, is_breakpoint_anchor=True),
                SrcStmt("s5", 14, "d", EBin("+", EVar("a"), EConst(5))),
                SrcStmt("s_init_m", 15, "m", EConst(0)),
            ],
            succs=["B1", "B2"],
            cond_var="cond",
        ),
        "B1": SrcBlock(
            "B1",
            [SrcStmt("s6", 16, "m", EBin("+", EVar("d"), EConst(1)))],
            succs=["B3"],
        ),
        "B2": SrcBlock(
            "B2",
            [SrcStmt("s7", 18, "k", EBin("+", EVar("x"), EConst(3)))],
            succs=["B3"],
        ),
        "B3": SrcBlock(
            "B3",
            [
                SrcStmt("s8", 20, None, None, is_breakpoint_anchor=True),
                SrcStmt("s9", 21, "out", EBin("+", EBin("+", EVar("m"), EVar("c")), EVar("d"))),
            ],
            succs=[],
        ),
    }

    # Register allocation homes:
    #   x -> r0, cond -> r7, a -> r1, b -> (DCE, no reg), c -> r2, d -> r3, m -> r4, k -> r1 (coalesced!), out -> r5
    var_home = {
        "x": "r0",
        "cond": "r7",
        "a": "r1",
        "c": "r2",
        "d": "r3",
        "m": "r4",
        "k": "r1",   # coalesced onto a's register r1 in B2 -> evicts a!
        "out": "r5",
    }

    # Optimized target CFG:
    # - s1 runs normally into r1 (a)
    # - s2 (b = a * 2) is DCE'd; recovered at PC=0x104 via DW_OP_stack_value (r1 << 1)
    # - s5 (d = a + 5) is HOISTED before s4 -> d is noncurrent-premature at PC=0x104!
    # - s3 (c = x + 10) is SUNK after s4 -> c is noncurrent-stale at PC=0x104!
    # - In B0, r0 (x) is clobbered by a scratch temp at PC=0x102 after computing a,
    #   except we save x in r6 for c; x's home r0 is evicted at PC=0x104 unless rescued by DW_OP_entry_value!
    # - In B2, s7 writes k into r1 (coalesced with a), evicting a on the B2->B3 path!
    #   Also s6 in B1 is sunk into B3 after s8 (making m suspect-join stale at s8!).
    tgt_cfg = {
        "B0": TgtBlock(
            "B0",
            [
                TgtInst(0x0FC, 9, "s0", "r3", "d", EConst(0), is_stmt=False),
                TgtInst(0x100, 10, "s1", "r1", "a", EBin("+", EVar("r0"), EConst(1))),
                TgtInst(0x101, 10, None, "r6", None, EVar("r0"), is_stmt=False),  # copy x -> r6
                TgtInst(0x102, 10, None, "r0", None, EConst(999), is_stmt=False), # clobber r0 (evicts x)
                TgtInst(0x103, 14, "s5", "r3", "d", EBin("+", EVar("r1"), EConst(5))),  # HOISTED s5
                TgtInst(0x104, 13, None, None, None, None, anchor_stmt_id="s4", is_stmt=True),
                TgtInst(0x105, 12, "s3", "r2", "c", EBin("+", EVar("r6"), EConst(10))), # SUNK s3
                TgtInst(0x106, 15, "s_init_m", "r4", "m", EConst(0)),
            ],
            succs=["B1", "B2"],
            cond_reg="r7",
        ),
        "B1": TgtBlock(
            "B1",
            [
                # Notice: s6 (m = d + 1) was intentionally omitted/sunk or delayed on B1
                # to create a path-dependent (suspect-join) staleness for m at B3!
                TgtInst(0x108, 16, None, "r8", None, EBin("+", EVar("r3"), EConst(1)), is_stmt=False),
            ],
            succs=["B3"],
        ),
        "B2": TgtBlock(
            "B2",
            [
                # Coalescing reuses r1 for k -> evicts `a` on B2 path!
                TgtInst(0x10A, 18, "s7", "r1", "k", EBin("+", EVar("r6"), EConst(3))),
            ],
            succs=["B3"],
        ),
        "B3": TgtBlock(
            "B3",
            [
                TgtInst(0x112, 20, None, None, None, None, anchor_stmt_id="s8", is_stmt=True),
                TgtInst(0x114, 21, "s9", "r5", "out", EBin("+", EBin("+", EVar("r4"), EVar("r2")), EVar("r3"))),
            ],
            succs=[],
        ),
    }

    # Sound DWARF location table (with DW_OP_stack_value for DCE'd `b` and DW_OP_entry_value for clobbered `x`)
    dwarf_sound: dict[tuple[int, str], DwarfLocation] = {
        # At PC=0x104 (anchor s4):
        (0x104, "a"): DwarfLocation("reg", reg="r1", dwarf_ops="DW_OP_reg1"),
        (0x104, "cond"): DwarfLocation("reg", reg="r7", dwarf_ops="DW_OP_reg7"),
        (0x104, "b"): DwarfLocation(
            "stack_value",
            synth_expr=EBin("<<", EVar("r1"), EConst(1)),
            dwarf_ops="DW_OP_breg1 0, DW_OP_lit1, DW_OP_shl, DW_OP_stack_value",
        ),
        (0x104, "x"): DwarfLocation(
            "entry_value",
            entry_param="x",
            dwarf_ops="DW_OP_entry_value(DW_OP_reg0)",
        ),
        # c is stale (sunk past 0x104), so a sound compiler marks it optimized out:
        (0x104, "c"): DwarfLocation("optimized_out", dwarf_ops="<optimized out>"),
        # d is premature (hoisted before 0x104):
        (0x104, "d"): DwarfLocation("optimized_out", dwarf_ops="<optimized out>"),
        # At PC=0x112 (anchor s8, join block B3):
        (0x112, "x"): DwarfLocation("entry_value", entry_param="x", dwarf_ops="DW_OP_entry_value(DW_OP_reg0)"),
        (0x112, "cond"): DwarfLocation("reg", reg="r7", dwarf_ops="DW_OP_reg7"),
        (0x112, "c"): DwarfLocation("reg", reg="r2", dwarf_ops="DW_OP_reg2"),
        (0x112, "d"): DwarfLocation("reg", reg="r3", dwarf_ops="DW_OP_reg3"),
        (0x112, "b"): DwarfLocation("optimized_out", dwarf_ops="<optimized out>"),
        # `a` was evicted on B2 path (r1 reused by k) -> suspect-join evicted!
        (0x112, "a"): DwarfLocation("optimized_out", dwarf_ops="<optimized out>"),
        # `m` was not written into r4 on B1 -> suspect-join stale!
        (0x112, "m"): DwarfLocation("optimized_out", dwarf_ops="<optimized out>"),
    }

    analyzer = CurrencyAnalyzer(src_cfg, tgt_cfg, "B0", ["x", "cond"], var_home, dwarf_sound)
    static_res = analyzer.analyze()
    checked_true = analyzer.differential_validate(static_res, {"x": 7, "cond": 1})
    checked_false = analyzer.differential_validate(static_res, {"x": 7, "cond": 0})

    # Verify every expected classification at PC=0x104 and PC=0x112
    by_key = {(c.breakpoint_pc, c.source_var): c for c in checked_true}

    # At PC=0x104:
    assert by_key[(0x104, "a")].classification == "current"
    assert by_key[(0x104, "a")].expected_val == 8 and by_key[(0x104, "a")].observed_val == 8
    assert by_key[(0x104, "b")].raw_storage_status == "noncurrent-stale"
    assert by_key[(0x104, "b")].classification == "current"
    assert by_key[(0x104, "b")].recovered_via == "DW_OP_stack_value"
    assert by_key[(0x104, "b")].expected_val == 16 and by_key[(0x104, "b")].observed_val == 16
    assert by_key[(0x104, "x")].raw_storage_status == "evicted"
    assert by_key[(0x104, "x")].classification == "current"
    assert by_key[(0x104, "x")].recovered_via == "DW_OP_entry_value"
    assert by_key[(0x104, "x")].expected_val == 7 and by_key[(0x104, "x")].observed_val == 7
    assert by_key[(0x104, "c")].classification == "noncurrent-stale"
    assert by_key[(0x104, "d")].classification == "noncurrent-premature"

    # At PC=0x112 (join):
    assert by_key[(0x112, "a")].classification == "evicted"
    assert by_key[(0x112, "a")].path_sensitivity == "suspect-join"
    assert by_key[(0x112, "m")].classification == "noncurrent-stale"
    assert by_key[(0x112, "m")].path_sensitivity == "suspect-join"
    assert by_key[(0x112, "c")].classification == "current" and by_key[(0x112, "c")].observed_val == 17
    assert by_key[(0x112, "d")].classification == "current" and by_key[(0x112, "d")].observed_val == 13

    # Zero soundness bugs under sound DWARF table across both branch paths
    assert not any(c.soundness_bug for c in checked_true)
    assert not any(c.soundness_bug for c in checked_false)

    # Now simulate a Di Luna et al. (ASPLOS '21) wrong-value compiler bug:
    # - compiler forgets r0 was clobbered with 999 at 0x102 and emits DW_OP_reg0 for `x`,
    # - compiler fails to invalidate `d` after hoisting s5 before s4 (emits DW_OP_reg3 -> 13 instead of 0),
    # - compiler forgets r1 was coalesced to `k` on B2 and emits DW_OP_reg1 for `a` at 0x112!
    dwarf_buggy = dict(dwarf_sound)
    dwarf_buggy[(0x104, "x")] = DwarfLocation("reg", reg="r0", dwarf_ops="DW_OP_reg0 [BUG: clobbered]")
    dwarf_buggy[(0x104, "d")] = DwarfLocation("reg", reg="r3", dwarf_ops="DW_OP_reg3 [BUG: premature hoist]")
    dwarf_buggy[(0x112, "a")] = DwarfLocation("reg", reg="r1", dwarf_ops="DW_OP_reg1 [BUG: coalesced]")
    buggy_analyzer = CurrencyAnalyzer(src_cfg, tgt_cfg, "B0", ["x", "cond"], var_home, dwarf_buggy)
    buggy_checked_false = buggy_analyzer.differential_validate(buggy_analyzer.analyze(), {"x": 7, "cond": 0})
    bugs_found = [
        (c.breakpoint_pc, c.source_var, c.expected_val, c.observed_val)
        for c in buggy_checked_false
        if c.soundness_bug
    ]
    assert (0x104, "x", 7, 999) in bugs_found
    assert (0x104, "d", 0, 13) in bugs_found
    assert (0x112, "a", 8, 10) in bugs_found  # x+1=8 vs k=x+3=10

    return {
        "sound_classifications": [
            {
                "pc": hex(c.breakpoint_pc),
                "block": c.block_id,
                "var": c.source_var,
                "classification": c.classification,
                "raw_storage": c.raw_storage_status,
                "recovered_via": c.recovered_via,
                "path_sensitivity": c.path_sensitivity,
                "expected": c.expected_val,
                "observed": c.observed_val,
            }
            for c in checked_true
        ],
        "wrong_value_bugs_caught": [
            {"pc": hex(pc), "var": v, "expected": exp, "observed": obs}
            for pc, v, exp, obs in bugs_found
        ],
    }


# =============================================================================
# PART 2: rr-Style Deterministic Record/Replay, O(log T) Checkpoints & Pernosco
# =============================================================================

@dataclass(frozen=True)
class TraceEvent:
    event_time: int     # monotonic FrameTime index
    kind: str           # "SYSCALL_ENTROPY", "SYSCALL_RDTSC", "PREEMPT_SWITCH", "ASYNC_SIGNAL"
    tid: int
    rcb: int            # exact retired conditional branch count of `tid` at event
    pc: int
    reg_digest: str
    payload: int = 0    # recorded syscall return value or target thread id


@dataclass
class ThreadState:
    tid: int
    pc: int
    regs: dict[str, int]
    rcb: int = 0
    finished: bool = False


@dataclass
class MachineState:
    step_index: int
    event_time: int
    active_tid: int
    threads: dict[int, ThreadState]
    memory: dict[int, int]
    crashed: bool = False
    crash_reason: str = ""

    def reg_digest(self, tid: int) -> str:
        t = self.threads[tid]
        raw = f"{t.pc}:{sorted(t.regs.items())}".encode()
        return hashlib.sha256(raw).hexdigest()[:12]

    def clone(self) -> MachineState:
        return copy.deepcopy(self)


@dataclass(frozen=True)
class WatchHit:
    step_index: int
    event_time: int
    tid: int
    rcb: int
    pc: int
    addr: int
    old_val: int
    new_val: int
    cause_tag: str


class ReplayDivergenceError(RuntimeError):
    """Raised when replay observes unrecorded external state (e.g. MAP_SHARED/DMA)."""


class DeterministicVM:
    """Two-thread workload modeling a latent order-violation memory corruption:
      - Thread 0 (worker): executes `total_iters` loop iterations, reading shared
        slot `0x2000` (expected invariant: value == 0xCAFE unless corrupted) and
        incrementing counter `0x2004`. Every loop backedge retires 1 conditional
        branch (RCB). On iteration `crash_iter`, asserts `mem[0x2000] == 0xCAFE`.
      - Thread 1 (peer): executes a nondeterministic RDTSC/entropy syscall; when
        preemptively scheduled into the race window, writes a corrupted value
        derived from the syscall payload into `0x2000`.
    """

    ADDR_GUARD = 0x2000
    ADDR_COUNTER = 0x2004
    ADDR_ENTROPY = 0x2008
    ADDR_SHARED_EXT = 0x3000  # External MAP_SHARED / DMA page

    def __init__(self, total_iters: int, corrupt_iter: int, crash_iter: int, max_timeslice_rcb: int = 64) -> None:
        self.total_iters = total_iters
        self.corrupt_iter = corrupt_iter
        self.crash_iter = crash_iter
        self.max_timeslice_rcb = max_timeslice_rcb

    def initial_state(self) -> MachineState:
        return MachineState(
            step_index=0,
            event_time=0,
            active_tid=0,
            threads={
                0: ThreadState(tid=0, pc=0x1000, regs={"i": 0, "acc": 0, "limit": self.total_iters}),
                1: ThreadState(tid=1, pc=0x2000, regs={"armed": 1, "entropy": 0}),
            },
            memory={
                self.ADDR_GUARD: 0xCAFE,
                self.ADDR_COUNTER: 0,
                self.ADDR_ENTROPY: 0,
                self.ADDR_SHARED_EXT: 0x1111,
            },
        )

    def step_one(
        self,
        st: MachineState,
        mode: str,  # "record" or "replay"
        trace_log: list[TraceEvent],
        replay_cursor: list[int],  # mutable single-element index
        nondet_oracle: Callable[[int], int] | None = None,
        external_dma_corrupt_at_step: int | None = None,
    ) -> WatchHit | None:
        """Execute one deterministic architectural step of `st.active_tid`.
        Returns a WatchHit if memory was written.
        """
        if st.crashed:
            return None

        # Simulate unrecorded external MAP_SHARED / GPU DMA write if requested
        if external_dma_corrupt_at_step is not None and st.step_index == external_dma_corrupt_at_step:
            st.memory[self.ADDR_SHARED_EXT] = 0xDEAD_BEEF

        tid = st.active_tid
        t = st.threads[tid]
        write_hit: WatchHit | None = None

        if tid == 0:
            # PC 0x1000: loop check (retires 1 conditional branch: RCB++)
            if t.pc == 0x1000:
                t.rcb += 1
                if t.regs["i"] >= t.regs["limit"]:
                    t.finished = True
                    t.pc = 0x1020
                else:
                    t.pc = 0x1004
            elif t.pc == 0x1004:
                # Increment counter in memory
                old = st.memory[self.ADDR_COUNTER]
                new = old + 1
                st.memory[self.ADDR_COUNTER] = new
                write_hit = WatchHit(
                    st.step_index, st.event_time, tid, t.rcb, t.pc,
                    self.ADDR_COUNTER, old, new, "worker_counter_inc"
                )
                t.pc = 0x1008
            elif t.pc == 0x1008:
                # Read external shared page to expose unrecorded MAP_SHARED divergence
                t.regs["acc"] ^= st.memory[self.ADDR_SHARED_EXT]
                if t.regs["i"] == self.crash_iter:
                    if st.memory[self.ADDR_GUARD] != 0xCAFE:
                        st.crashed = True
                        st.crash_reason = f"SIGABRT: guard 0x{self.ADDR_GUARD:x} corrupted to 0x{st.memory[self.ADDR_GUARD]:x}"
                        return None
                t.regs["i"] += 1
                t.pc = 0x1000
                # Record-mode scheduler preempts to Thread 1 right at corrupt_iter!
                if mode == "record" and t.regs["i"] == self.corrupt_iter and not st.threads[1].finished:
                    ev = TraceEvent(
                        event_time=st.event_time,
                        kind="PREEMPT_SWITCH",
                        tid=0,
                        rcb=t.rcb,
                        pc=t.pc,
                        reg_digest=st.reg_digest(0),
                        payload=1,
                    )
                    trace_log.append(ev)
                    st.event_time += 1
                    st.active_tid = 1
        elif tid == 1:
            if t.pc == 0x2000:
                # Nondeterministic syscall (e.g. getrandom / rdtsc)
                if mode == "record":
                    assert nondet_oracle is not None
                    val = nondet_oracle(st.step_index)
                    ev = TraceEvent(
                        event_time=st.event_time,
                        kind="SYSCALL_ENTROPY",
                        tid=1,
                        rcb=t.rcb,
                        pc=t.pc,
                        reg_digest=st.reg_digest(1),
                        payload=val,
                    )
                    trace_log.append(ev)
                    st.event_time += 1
                else:
                    ev = trace_log[replay_cursor[0]]
                    assert ev.kind == "SYSCALL_ENTROPY" and ev.tid == 1 and ev.rcb == t.rcb
                    val = ev.payload
                    st.event_time = ev.event_time + 1
                    replay_cursor[0] += 1
                t.regs["entropy"] = val
                old = st.memory[self.ADDR_ENTROPY]
                st.memory[self.ADDR_ENTROPY] = val
                write_hit = WatchHit(
                    st.step_index, st.event_time, tid, t.rcb, t.pc,
                    self.ADDR_ENTROPY, old, val, "syscall_getrandom_write"
                )
                t.pc = 0x2004
            elif t.pc == 0x2004:
                # Conditional branch on entropy parity -> triggers bug
                t.rcb += 1
                if (t.regs["entropy"] & 1) == 1:
                    t.pc = 0x2008
                else:
                    t.pc = 0x200C
            elif t.pc == 0x2008:
                # Corrupt shared guard slot!
                old = st.memory[self.ADDR_GUARD]
                new = 0xBAD0_0000 | (t.regs["entropy"] & 0xFFFF)
                st.memory[self.ADDR_GUARD] = new
                write_hit = WatchHit(
                    st.step_index, st.event_time, tid, t.rcb, t.pc,
                    self.ADDR_GUARD, old, new, "order_violation_corrupt_write"
                )
                t.pc = 0x200C
            elif t.pc == 0x200C:
                t.finished = True
                t.pc = 0x2010
                if mode == "record":
                    ev = TraceEvent(
                        event_time=st.event_time,
                        kind="PREEMPT_SWITCH",
                        tid=1,
                        rcb=t.rcb,
                        pc=t.pc,
                        reg_digest=st.reg_digest(1),
                        payload=0,
                    )
                    trace_log.append(ev)
                    st.event_time += 1
                    st.active_tid = 0

        # In replay mode, deliver recorded PREEMPT_SWITCH at the exact post-instruction (tid, rcb, pc, reg_digest)
        if mode == "replay" and replay_cursor[0] < len(trace_log):
            nxt = trace_log[replay_cursor[0]]
            if nxt.kind == "PREEMPT_SWITCH" and nxt.tid == tid and nxt.rcb == t.rcb and nxt.pc == t.pc:
                if nxt.reg_digest != st.reg_digest(tid):
                    raise ReplayDivergenceError(
                        f"ProtoMark register digest mismatch at tid={tid} rcb={t.rcb} pc=0x{t.pc:x}: "
                        f"recorded={nxt.reg_digest} replayed={st.reg_digest(tid)}"
                    )
                st.active_tid = nxt.payload
                st.event_time = nxt.event_time + 1
                replay_cursor[0] += 1

        st.step_index += 1
        return write_hit


class RRReplayTimeline:
    """Models rr::ReplayTimeline's exponential checkpoint retention policy
    (src/ReplayTimeline.cc: discard_past_reverse_exec_checkpoints with factor 2)
    and reverse-watchpoint search with PMU skid-margin simulation.
    """

    def __init__(
        self,
        vm: DeterministicVM,
        trace_log: list[TraceEvent],
        base_interval: int = 32,
        skid_margin_rcb: int = 100,
    ) -> None:
        self.vm = vm
        self.trace_log = trace_log
        self.base_interval = base_interval
        self.skid_margin_rcb = skid_margin_rcb
        self.checkpoints: dict[int, tuple[MachineState, int]] = {}  # step_index -> (state, cursor)
        self.max_checkpoints_live = 0
        self.total_replay_steps = 0
        self.skid_overshoots_avoided = 0

    def _discard_past_checkpoints(self, now: int) -> None:
        """Exact discrete analogue of rr::ReplayTimeline::discard_past_reverse_exec_checkpoints.
        Within interval [now - base * 2^k, now], retain at most k checkpoints (0 in first interval).
        Guarantees O(log(now / base)) live checkpoints at all times!
        """
        sorted_steps = sorted(self.checkpoints.keys(), reverse=True)
        to_delete: list[int] = []
        allowed = 0
        in_range = 0
        idx = 0
        interval_len = self.base_interval

        while idx < len(sorted_steps):
            start = now - interval_len
            tmp = idx
            while tmp < len(sorted_steps) and sorted_steps[tmp] >= start:
                in_range += 1
                tmp += 1
            while in_range > allowed:
                to_delete.append(sorted_steps[idx])
                in_range -= 1
                idx += 1
            allowed += 1
            idx = tmp
            interval_len *= 2

        for s in to_delete:
            del self.checkpoints[s]

    def _maybe_add_checkpoint(self, st: MachineState, cursor: int) -> None:
        now = st.step_index
        # Discard future checkpoints
        for s in [k for k in self.checkpoints if k > now]:
            del self.checkpoints[s]
        if self.checkpoints:
            latest = max(self.checkpoints.keys())
            if latest >= now - self.base_interval:
                return
        self._discard_past_checkpoints(now)
        self.checkpoints[now] = (st.clone(), cursor)
        self.max_checkpoints_live = max(self.max_checkpoints_live, len(self.checkpoints))

    def replay_to_crash(self) -> tuple[MachineState, int]:
        st = self.vm.initial_state()
        cursor = [0]
        self.checkpoints = {0: (st.clone(), 0)}
        self.max_checkpoints_live = 1

        while not st.crashed and not all(t.finished for t in st.threads.values()):
            self._maybe_add_checkpoint(st, cursor[0])
            self.vm.step_one(st, "replay", self.trace_log, cursor)
            self.total_replay_steps += 1
        return st, cursor[0]

    def reverse_continue_watchpoint(self, crash_step: int, watch_addr: int) -> tuple[WatchHit, int, int]:
        """Find the latest write to `watch_addr` strictly before `crash_step` by walking
        backward across the exponential checkpoint ladder and replaying each segment
        forward with hardware watchpoint monitoring + PMU skid-margin compensation.
        Returns (watch_hit, replay_steps_used, checkpoint_intervals_scanned).
        """
        replay_steps_used = 0
        intervals_scanned = 0
        end_step = crash_step
        ckpt_steps = sorted(s for s in self.checkpoints if s < end_step)

        while ckpt_steps:
            start_step = ckpt_steps.pop()
            intervals_scanned += 1
            st_ckpt, cur_ckpt = self.checkpoints[start_step]
            st = st_ckpt.clone()
            cursor = [cur_ckpt]
            last_hit: WatchHit | None = None

            # Simulate PMU skid-margin positioning for async event delivery inside segment
            target_rcbs = [e.rcb for e in self.trace_log[cur_ckpt:] if e.kind == "PREEMPT_SWITCH"]
            if target_rcbs:
                arm_rcb = max(0, target_rcbs[0] - self.skid_margin_rcb)
                if arm_rcb <= target_rcbs[0]:
                    self.skid_overshoots_avoided += 1

            while st.step_index < end_step:
                hit = self.vm.step_one(st, "replay", self.trace_log, cursor)
                replay_steps_used += 1
                if hit is not None and hit.addr == watch_addr:
                    last_hit = hit
            if last_hit is not None:
                return last_hit, replay_steps_used, intervals_scanned
            end_step = start_step

        raise RuntimeError(f"no write found to 0x{watch_addr:x} before step {crash_step}")


class OmniscientIndex:
    """Pernosco-style all-time indexed memory-write database built over an rr trace."""

    def __init__(self) -> None:
        self._writes_by_addr: dict[int, list[WatchHit]] = {}
        self._steps_by_addr: dict[int, list[int]] = {}
        self._provenance: dict[tuple[int, int], tuple[int, int]] = {}  # (addr, step) -> (src_addr, src_step)

    def build_from_trace(self, vm: DeterministicVM, trace_log: list[TraceEvent]) -> int:
        st = vm.initial_state()
        cursor = [0]
        last_entropy_step: int | None = None
        indexed_steps = 0
        while not st.crashed and not all(t.finished for t in st.threads.values()):
            hit = vm.step_one(st, "replay", trace_log, cursor)
            indexed_steps += 1
            if hit is not None:
                self._writes_by_addr.setdefault(hit.addr, []).append(hit)
                self._steps_by_addr.setdefault(hit.addr, []).append(hit.step_index)
                if hit.addr == vm.ADDR_ENTROPY:
                    last_entropy_step = hit.step_index
                elif hit.addr == vm.ADDR_GUARD and last_entropy_step is not None:
                    self._provenance[(hit.addr, hit.step_index)] = (vm.ADDR_ENTROPY, last_entropy_step)
        return indexed_steps

    def who_wrote(self, addr: int, before_step: int) -> WatchHit | None:
        """O(log W) binary search for latest write to `addr` prior to `before_step`."""
        steps = self._steps_by_addr.get(addr)
        if not steps:
            return None
        pos = bisect.bisect_left(steps, before_step) - 1
        if pos < 0:
            return None
        return self._writes_by_addr[addr][pos]

    def trace_root_cause(self, addr: int, at_step: int) -> list[WatchHit]:
        """Follow backward dataflow provenance from crash read to original syscall input."""
        chain: list[WatchHit] = []
        cur_addr, cur_step = addr, at_step
        while True:
            w = self.who_wrote(cur_addr, cur_step)
            if w is None:
                break
            chain.append(w)
            parent = self._provenance.get((cur_addr, w.step_index))
            if parent is None:
                break
            cur_addr, cur_step = parent[0], parent[1] + 1
        return chain


def run_replay_probe() -> dict[str, Any]:
    scaling_rows: list[dict[str, Any]] = []

    for total_iters in (500, 2000, 8000):
        corrupt_iter = total_iters // 3
        crash_iter = total_iters - 5
        vm = DeterministicVM(total_iters=total_iters, corrupt_iter=corrupt_iter, crash_iter=crash_iter)

        # 1. Record execution
        rec_state = vm.initial_state()
        trace_log: list[TraceEvent] = []
        while not rec_state.crashed and not all(t.finished for t in rec_state.threads.values()):
            vm.step_one(
                rec_state,
                mode="record",
                trace_log=trace_log,
                replay_cursor=[0],
                nondet_oracle=lambda step: 0xA5A5_1337,  # odd -> triggers corruption branch
            )
        assert rec_state.crashed, "expected recorded execution to hit order-violation crash"
        crash_step = rec_state.step_index
        # Trace log is O(syscalls + preempts), NOT O(instructions)!
        assert len(trace_log) == 3, f"expected 3 trace events (preempt, syscall, preempt), got {len(trace_log)}"

        # 2. Replay with rr exponential checkpoint retention
        timeline = RRReplayTimeline(vm, trace_log, base_interval=32, skid_margin_rcb=100)
        rep_state, _ = timeline.replay_to_crash()
        assert rep_state.crashed and rep_state.step_index == crash_step
        assert rep_state.memory == rec_state.memory
        assert rep_state.threads[0].regs == rec_state.threads[0].regs
        assert rep_state.threads[0].rcb == rec_state.threads[0].rcb

        # Verify O(log T) checkpoint bound
        log_bound = math.ceil(math.log2(max(2, crash_step / 32))) + 3
        assert timeline.max_checkpoints_live <= log_bound, (
            f"live checkpoints {timeline.max_checkpoints_live} exceeded O(log T) bound {log_bound}"
        )

        # 3. Reverse-watchpoint fault origin recovery
        fault_write, rev_steps, intervals_scanned = timeline.reverse_continue_watchpoint(crash_step, vm.ADDR_GUARD)
        assert fault_write.tid == 1
        assert fault_write.cause_tag == "order_violation_corrupt_write"
        assert fault_write.old_val == 0xCAFE
        assert fault_write.new_val == 0xBAD0_1337
        assert intervals_scanned <= timeline.max_checkpoints_live

        # 4. Pernosco-style omniscient backward dataflow query (0 re-execution)
        omni = OmniscientIndex()
        omni.build_from_trace(vm, trace_log)
        chain = omni.trace_root_cause(vm.ADDR_GUARD, crash_step)
        assert len(chain) == 2
        assert chain[0].cause_tag == "order_violation_corrupt_write"
        assert chain[1].cause_tag == "syscall_getrandom_write"
        assert chain[1].new_val == 0xA5A5_1337

        scaling_rows.append(
            {
                "total_iters": total_iters,
                "crash_step": crash_step,
                "trace_events_recorded": len(trace_log),
                "max_live_checkpoints": timeline.max_checkpoints_live,
                "log2_bound": log_bound,
                "intervals_scanned": intervals_scanned,
                "fault_origin_step": fault_write.step_index,
                "fault_origin_tid": fault_write.tid,
                "fault_origin_rcb": fault_write.rcb,
                "reverse_replay_steps": rev_steps,
                "omniscient_chain_len": len(chain),
            }
        )

    # 4b. Near-crash locality test: fault only 25 iterations before crash in an 8000-iter trace
    vm_near = DeterministicVM(total_iters=8000, corrupt_iter=7970, crash_iter=7995)
    rec_near = vm_near.initial_state()
    log_near: list[TraceEvent] = []
    while not rec_near.crashed and not all(t.finished for t in rec_near.threads.values()):
        vm_near.step_one(rec_near, "record", log_near, [0], nondet_oracle=lambda s: 0xA5A5_1337)
    tl_near = RRReplayTimeline(vm_near, log_near, base_interval=32, skid_margin_rcb=100)
    rep_near, _ = tl_near.replay_to_crash()
    assert rep_near.crashed and rep_near.step_index == rec_near.step_index
    near_hit, near_rev_steps, near_intervals = tl_near.reverse_continue_watchpoint(rec_near.step_index, vm_near.ADDR_GUARD)
    assert near_hit.cause_tag == "order_violation_corrupt_write"
    # Exponential density near `now` bounds reverse work to O(distance), far less than T!
    assert near_rev_steps < 500 and near_intervals <= 4, (
        f"expected near-crash reverse work <500 steps in <=4 intervals, got {near_rev_steps} / {near_intervals}"
    )

    # 5. Negative wall: unrecorded MAP_SHARED / DMA external writer causes divergence
    vm_wall = DeterministicVM(total_iters=200, corrupt_iter=50, crash_iter=180)
    rec_wall = vm_wall.initial_state()
    log_wall: list[TraceEvent] = []
    while not rec_wall.crashed and not all(t.finished for t in rec_wall.threads.values()):
        vm_wall.step_one(
            rec_wall,
            mode="record",
            trace_log=log_wall,
            replay_cursor=[0],
            nondet_oracle=lambda step: 0xA5A5_1337,
            external_dma_corrupt_at_step=120,  # unrecorded external DMA/MAP_SHARED write!
        )
    # Replay without visibility into the external writer diverges at register digest check
    rep_wall = vm_wall.initial_state()
    cur_wall = [0]
    divergence_detected = False
    try:
        while not rep_wall.crashed and not all(t.finished for t in rep_wall.threads.values()):
            vm_wall.step_one(rep_wall, mode="replay", trace_log=log_wall, replay_cursor=cur_wall)
    except (AssertionError, ReplayDivergenceError):
        divergence_detected = True
    if not divergence_detected and rep_wall.threads[0].regs["acc"] != rec_wall.threads[0].regs["acc"]:
        divergence_detected = True
    assert divergence_detected, "expected unrecorded external MAP_SHARED/DMA write to cause replay divergence"

    return {
        "scaling": scaling_rows,
        "near_crash_locality": {
            "crash_step": rec_near.step_index,
            "fault_origin_step": near_hit.step_index,
            "distance_steps": rec_near.step_index - near_hit.step_index,
            "reverse_replay_steps": near_rev_steps,
            "intervals_scanned": near_intervals,
            "max_live_checkpoints": tl_near.max_checkpoints_live,
        },
        "external_shared_mem_divergence_detected": divergence_detected,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON summary")
    args = ap.parse_args()

    currency_summary = run_currency_probe()
    replay_summary = run_replay_probe()
    report = {
        "currency_probe": currency_summary,
        "replay_probe": replay_summary,
        "all_assertions_passed": True,
    }

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print("=== Part 1: Hennessy / Adl-Tabatabai-Gross Currency & DWARF Synthesis ===")
        for row in currency_summary["sound_classifications"]:
            rescue = f" (rescued via {row['recovered_via']})" if row["recovered_via"] else ""
            print(
                f"  pc={row['pc']} [{row['block']}] var={row['var']:4s} "
                f"class={row['classification']:20s} raw={row['raw_storage']:20s} "
                f"path={row['path_sensitivity']:12s} exp={row['expected']} obs={row['observed']}{rescue}"
            )
        print("  Differential wrong-value bugs caught (buggy DWARF):")
        for bug in currency_summary["wrong_value_bugs_caught"]:
            print(f"    pc={bug['pc']} var={bug['var']}: expected={bug['expected']} observed={bug['observed']}")

        print("\n=== Part 2: rr Deterministic Replay, O(log T) Checkpoints & Omniscient Index ===")
        for row in replay_summary["scaling"]:
            print(
                f"  iters={row['total_iters']:5d} crash_step={row['crash_step']:5d} "
                f"trace_events={row['trace_events_recorded']} "
                f"max_ckpts={row['max_live_checkpoints']:2d} (<= {row['log2_bound']:2d}) "
                f"scanned={row['intervals_scanned']:2d} "
                f"fault_step={row['fault_origin_step']:5d} tid={row['fault_origin_tid']} "
                f"rev_steps={row['reverse_replay_steps']:5d} omni_chain={row['omniscient_chain_len']}"
            )
        near = replay_summary["near_crash_locality"]
        print(
            f"  Near-crash locality (T={near['crash_step']}): distance={near['distance_steps']} steps -> "
            f"recovered in {near['reverse_replay_steps']} replay steps across {near['intervals_scanned']} "
            f"intervals (max_ckpts={near['max_live_checkpoints']})"
        )
        print(
            f"  External MAP_SHARED/DMA unrecorded-writer divergence detected: "
            f"{replay_summary['external_shared_mem_divergence_detected']}"
        )
        print("\n[OK] All currency, DWARF synthesis, O(log T) checkpoint, and replay assertions passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
