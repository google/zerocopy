#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import random
from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations, product
from typing import Dict, List, Optional, Set, Tuple

RLX, REL, ACQ, ACQ_REL, SC = "rlx", "rel", "acq", "acq_rel", "sc"

def has_acq(o: str) -> bool:
    return o in (ACQ, ACQ_REL, SC)

def has_rel(o: str) -> bool:
    return o in (REL, ACQ_REL, SC)

@dataclass(frozen=True)
class Instr:
    kind: str  # "load", "store", "fad", "fence"
    loc: Optional[str] = None
    val: int = 0
    ord: str = RLX
    reg: Optional[str] = None

LitmusProgram = List[List[Instr]]

@dataclass(frozen=True)
class Event:
    eid: int
    tid: int
    idx: int
    kind: str   # "init", "R", "W", "RMW", "F"
    loc: Optional[str]
    ord: str
    rval: Optional[int] = None
    wval: Optional[int] = None
    reg: Optional[str] = None

def is_read(e: Event) -> bool:
    return e.kind in ("R", "RMW")

def is_write(e: Event) -> bool:
    return e.kind in ("init", "W", "RMW")

def tc(edges: Set[Tuple[int, int]]) -> Set[Tuple[int, int]]:
    adj: Dict[int, Set[int]] = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
    res: Set[Tuple[int, int]] = set()
    for start in list(adj.keys()):
        stack = list(adj.get(start, ()))
        seen = set(stack)
        while stack:
            cur = stack.pop()
            res.add((start, cur))
            for nxt in adj.get(cur, ()):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
    return res

def compose(r1: Set[Tuple[int, int]], r2: Set[Tuple[int, int]]) -> Set[Tuple[int, int]]:
    by_mid: Dict[int, List[int]] = {}
    for b, c in r2:
        by_mid.setdefault(b, []).append(c)
    out: Set[Tuple[int, int]] = set()
    for a, b in r1:
        for c in by_mid.get(b, ()):
            out.add((a, c))
    return out

def is_irreflexive(r: Set[Tuple[int, int]]) -> bool:
    return all(a != b for a, b in r)

def is_acyclic(r: Set[Tuple[int, int]]) -> bool:
    return is_irreflexive(tc(r))

def enumerate_axiomatic_outcomes(
    prog: LitmusProgram,
    locs: List[str],
    variant: str,
    include_final_mo: bool = False,
) -> Set[Tuple]:
    possible_vals: Dict[str, Set[int]] = {l: {0} for l in locs}
    for _ in range(len(prog) + 3):
        for th in prog:
            for ins in th:
                if ins.kind == "store":
                    possible_vals[ins.loc].add(ins.val)
                elif ins.kind == "fad":
                    for v in list(possible_vals[ins.loc]):
                        possible_vals[ins.loc].add(v + ins.val)

    read_slots: List[Tuple[int, int, str]] = []
    for tid, th in enumerate(prog):
        for idx, ins in enumerate(th):
            if ins.kind in ("load", "fad"):
                read_slots.append((tid, idx, ins.loc))

    outcomes: Set[Tuple] = set()
    value_choices = [sorted(possible_vals[loc]) for (_, _, loc) in read_slots]

    for choice in product(*value_choices):
        rmap = {(read_slots[i][0], read_slots[i][1]): choice[i] for i in range(len(read_slots))}
        events: List[Event] = []
        init_ids: Dict[str, int] = {}
        for l in locs:
            eid = len(events)
            init_ids[l] = eid
            events.append(Event(eid, -1, 0, "init", l, RLX, None, 0, None))
        sb_edges: Set[Tuple[int, int]] = set()
        reg_out: Dict[str, int] = {}
        for tid, th in enumerate(prog):
            prev_eids: List[int] = []
            for idx, ins in enumerate(th):
                eid = len(events)
                if ins.kind == "load":
                    rv = rmap[(tid, idx)]
                    if ins.reg:
                        reg_out[ins.reg] = rv
                    ev = Event(eid, tid, idx, "R", ins.loc, ins.ord, rv, None, ins.reg)
                elif ins.kind == "store":
                    ev = Event(eid, tid, idx, "W", ins.loc, ins.ord, None, ins.val, None)
                elif ins.kind == "fad":
                    rv = rmap[(tid, idx)]
                    if ins.reg:
                        reg_out[ins.reg] = rv
                    ev = Event(eid, tid, idx, "RMW", ins.loc, ins.ord, rv, rv + ins.val, ins.reg)
                elif ins.kind == "fence":
                    ev = Event(eid, tid, idx, "F", None, ins.ord, None, None, None)
                else:
                    raise ValueError(ins.kind)
                for pe in prev_eids:
                    sb_edges.add((pe, eid))
                prev_eids.append(eid)
                events.append(ev)

        sb = tc(sb_edges)
        reads = [e for e in events if is_read(e)]
        writes_by_loc = {l: [e for e in events if is_write(e) and e.loc == l] for l in locs}

        rf_options = []
        possible = True
        for r in reads:
            cands = [w.eid for w in writes_by_loc[r.loc] if w.wval == r.rval and w.eid != r.eid]
            if not cands:
                possible = False
                break
            rf_options.append(cands)
        if not possible:
            continue

        mo_options_per_loc = []
        for l in locs:
            non_init = [w.eid for w in writes_by_loc[l] if w.kind != "init"]
            mo_options_per_loc.append([(init_ids[l],) + perm for perm in permutations(non_init)])

        for rf_tuple in product(*rf_options):
            rf = {(rf_tuple[i], reads[i].eid) for i in range(len(reads))}
            if variant not in ("cpp20_allow_lb", "armv8_0_mca", "armv8_3_rcpc"):
                if not is_acyclic(sb | rf):
                    continue

            for mo_tuple in product(*mo_options_per_loc):
                mo: Set[Tuple[int, int]] = set()
                final_mo_vals: Dict[str, int] = {}
                for li, seq in enumerate(mo_tuple):
                    final_mo_vals[locs[li]] = events[seq[-1]].wval
                    for i in range(len(seq)):
                        for j in range(i + 1, len(seq)):
                            mo.add((seq[i], seq[j]))

                rf_inv = {(r, w) for (w, r) in rf}
                fr = {(a, b) for (a, b) in compose(rf_inv, mo) if a != b}
                eco = tc(rf | mo | fr)

                rmw_ok = True
                for (w, r) in rf:
                    if events[r].kind == "RMW":
                        if (w, r) not in mo:
                            rmw_ok = False
                            break
                        for l_seq in mo_tuple:
                            if w in l_seq and r in l_seq:
                                if l_seq.index(r) != l_seq.index(w) + 1:
                                    rmw_ok = False
                                break
                if not rmw_ok:
                    continue

                if variant in ("armv8_0_mca", "armv8_3_rcpc"):
                    sb_loc = {(a, b) for (a, b) in sb if events[a].loc is not None and events[a].loc == events[b].loc}
                    if not is_acyclic(sb_loc | rf | mo | fr):
                        continue
                    ext = {(a, b) for a in range(len(events)) for b in range(len(events))
                           if events[a].tid != events[b].tid and events[a].tid >= 0 and events[b].tid >= 0}
                    obs = ((rf | mo | fr) & ext) | {(a, b) for (a, b) in (rf | mo | fr) if events[a].kind == "init"}

                    def is_L(e: Event) -> bool:
                        return e.kind in ("W", "RMW") and e.ord in (REL, ACQ_REL, SC)
                    def is_A(e: Event) -> bool:
                        if e.kind in ("R", "RMW"):
                            if e.ord == SC:
                                return True
                            if variant == "armv8_0_mca" and has_acq(e.ord):
                                return True
                        return False
                    def is_Q(e: Event) -> bool:
                        return variant == "armv8_3_rcpc" and e.kind in ("R", "RMW") and e.ord in (ACQ, ACQ_REL)
                    def is_M(e: Event) -> bool:
                        return e.kind in ("R", "W", "RMW")
                    def is_dmb_full(e: Event) -> bool:
                        return e.kind == "F" and e.ord in (ACQ_REL, SC)
                    def is_dmb_ld(e: Event) -> bool:
                        return e.kind == "F" and e.ord == ACQ
                    def is_dmb_st(e: Event) -> bool:
                        return e.kind == "F" and e.ord == REL

                    bob: Set[Tuple[int, int]] = set()
                    lmws: Set[Tuple[int, int]] = set()
                    for (a, b) in sb:
                        ea, eb = events[a], events[b]
                        if is_M(ea) and ea.loc == eb.loc and eb.kind in ("W", "RMW"):
                            lmws.add((a, b))
                        if is_L(ea) and is_A(eb):
                            bob.add((a, b))
                        if (is_A(ea) or is_Q(ea)) and is_M(eb):
                            bob.add((a, b))
                        if is_M(ea) and is_L(eb):
                            bob.add((a, b))
                        if is_A(ea) and is_L(ea) and ea.kind == "RMW" and is_M(eb):
                            bob.add((a, b))
                    for f in events:
                        if f.kind == "F":
                            for a in events:
                                for b in events:
                                    if (a.eid, f.eid) in sb and (f.eid, b.eid) in sb and is_M(a) and is_M(b):
                                        if is_dmb_full(f):
                                            bob.add((a.eid, b.eid))
                                        elif is_dmb_ld(f) and is_read(a):
                                            bob.add((a.eid, b.eid))
                                        elif is_dmb_st(f) and is_write(a) and is_write(b):
                                            bob.add((a.eid, b.eid))
                    lob = tc(lmws | bob)
                    if not is_acyclic(obs | lob):
                        continue
                else:
                    id_w = {(e.eid, e.eid) for e in events if e.kind in ("W", "RMW")}
                    if variant == "rc11_cat_c11_rs":
                        sb_loc_w = {(a, b) for (a, b) in sb
                                    if events[a].kind in ("W", "RMW") and events[b].kind in ("W", "RMW")
                                    and events[a].loc == events[b].loc}
                        rs_head = id_w | compose(id_w, sb_loc_w)
                    else:
                        rs_head = id_w

                    if variant == "cpp20_broken_no_rmw_rs":
                        rmw_chain = id_w
                    else:
                        rf_rmw = {(w, r) for (w, r) in rf if events[r].kind == "RMW"}
                        rmw_chain = id_w | tc(rf_rmw)
                    rs = compose(rs_head, rmw_chain)

                    rel_starts: Set[Tuple[int, int]] = set()
                    for e in events:
                        if has_rel(e.ord):
                            if e.kind in ("W", "RMW"):
                                rel_starts.add((e.eid, e.eid))
                            elif e.kind == "F":
                                for w in events:
                                    if w.kind in ("W", "RMW") and (e.eid, w.eid) in sb:
                                        rel_starts.add((e.eid, w.eid))
                    acq_ends: Set[Tuple[int, int]] = set()
                    for r in events:
                        if is_read(r):
                            if has_acq(r.ord):
                                acq_ends.add((r.eid, r.eid))
                            for f in events:
                                if f.kind == "F" and has_acq(f.ord) and (r.eid, f.eid) in sb:
                                    acq_ends.add((r.eid, f.eid))

                    sw = {
                        (a, b)
                        for (a, b) in compose(compose(compose(rel_starts, rs), rf), acq_ends)
                        if events[a].tid != events[b].tid
                    }
                    hb = tc(sb | sw)

                    if not is_irreflexive(hb | compose(hb, eco)):
                        continue

                    sc_acc = {e.eid for e in events if e.kind in ("R", "W", "RMW") and e.ord == SC}
                    sc_f = {e.eid for e in events if e.kind == "F" and e.ord == SC}
                    sc_all = sc_acc | sc_f

                    if variant == "cpp11_naive_sc_hb":
                        s_rel = {(a, b) for (a, b) in (hb | eco) if a in sc_all and b in sc_all}
                        hb_refl = hb | {(e.eid, e.eid) for e in events}
                        sbl = {(a, b) for (a, b) in sb if events[a].loc != events[b].loc}
                        hbl = {(a, b) for (a, b) in hb if events[a].loc is not None and events[a].loc == events[b].loc}
                        scb = sb | compose(compose(sbl, hb), sbl) | hbl | mo | fr
                        left_f = {(a, a) for a in sc_acc} | {(f, x) for f in sc_f for (f2, x) in hb_refl if f == f2}
                        right_f = {(a, a) for a in sc_acc} | {(x, f) for f in sc_f for (x, f2) in hb_refl if f == f2}
                        pscf = {(f1, f2) for (f1, f2) in (hb | compose(compose(hb, eco), hb)) if f1 in sc_f and f2 in sc_f}
                        psc = s_rel | compose(compose(left_f, scb), right_f) | pscf
                        if not is_acyclic(psc):
                            continue
                    elif variant in ("rc11_cat_p0982", "rc11_cat_c11_rs"):
                        hb_refl = hb | {(e.eid, e.eid) for e in events}
                        sbl = {(a, b) for (a, b) in sb if events[a].loc != events[b].loc}
                        hbl = {(a, b) for (a, b) in hb if events[a].loc is not None and events[a].loc == events[b].loc}
                        scb = sb | compose(compose(sbl, hb), sbl) | hbl | mo | fr
                        left = {(a, a) for a in sc_acc} | {(f, x) for f in sc_f for (f2, x) in hb_refl if f == f2}
                        right = {(a, a) for a in sc_acc} | {(x, f) for f in sc_f for (x, f2) in hb_refl if f == f2}
                        pscb = compose(compose(left, scb), right)
                        pscf = {(f1, f2) for (f1, f2) in (hb | compose(compose(hb, eco), hb)) if f1 in sc_f and f2 in sc_f}
                        if not is_acyclic(pscb | pscf):
                            continue
                    else:
                        sc_sw_sc = {(a, b) for (a, b) in sw if a in sc_acc and b in sc_acc}
                        shb = tc(sb | sc_sw_sc | compose(compose(sb, hb), sb))
                        s_edges: Set[Tuple[int, int]] = set()
                        for (a, b) in shb:
                            if a in sc_all and b in sc_all:
                                s_edges.add((a, b))
                        for (a, b) in eco:
                            if a in sc_acc and b in sc_acc:
                                s_edges.add((a, b))
                        for (a, y) in compose(eco, hb):
                            if a in sc_acc and y in sc_f:
                                s_edges.add((a, y))
                        for (x, b) in compose(hb, eco):
                            if x in sc_f and b in sc_acc:
                                s_edges.add((x, b))
                        for (x, y) in compose(compose(hb, eco), hb):
                            if x in sc_f and y in sc_f:
                                s_edges.add((x, y))
                        if not is_acyclic(s_edges):
                            continue

                regs_sorted = tuple((k, reg_out[k]) for k in sorted(reg_out.keys()))
                if include_final_mo:
                    mo_sorted = tuple((k, final_mo_vals[k]) for k in sorted(locs))
                    outcomes.add((regs_sorted, mo_sorted))
                else:
                    outcomes.add(regs_sorted)

    return outcomes


INF = Fraction(10**9, 1)
NEG_ONE = Fraction(-1, 1)

@dataclass
class ThreadView:
    cur: Dict[str, Fraction]
    acq: Dict[str, Fraction]
    rel: Dict[str, Fraction]
    obs_cur: Dict[str, Fraction]
    obs_acq: Dict[str, Fraction]
    obs_rel: Dict[str, Fraction]
    obs_is_read_cur: Dict[str, bool]
    obs_is_read_acq: Dict[str, bool]
    obs_is_read_rel: Dict[str, bool]
    s_last_sc: Fraction = Fraction(0, 1)
    s_left_hb_cur: Fraction = Fraction(0, 1)
    s_left_hb_acq: Fraction = Fraction(0, 1)
    s_left_hb_rel: Fraction = Fraction(0, 1)
    s_f_cur: Fraction = Fraction(0, 1)
    s_f_acq: Fraction = Fraction(0, 1)
    s_f_rel: Fraction = Fraction(0, 1)

@dataclass
class OpMsgDense:
    mo_ts: Fraction
    val: int
    msg_view: Dict[str, Fraction]
    obs_view: Dict[str, Fraction]
    obs_is_read_view: Dict[str, bool]
    is_rmw_after_prev: bool = False
    s_self_sc: Fraction = Fraction(0, 1)
    s_f_hb_w: Fraction = Fraction(0, 1)
    s_read_sc_lb: Fraction = Fraction(0, 1)
    s_read_f_lb: Fraction = Fraction(0, 1)
    s_ub: Fraction = INF
    s_left_msg: Fraction = Fraction(0, 1)
    s_f_msg: Fraction = Fraction(0, 1)

def vmax(v1: Dict[str, Fraction], v2: Dict[str, Fraction]) -> Dict[str, Fraction]:
    return {k: (v1[k] if v1[k] >= v2[k] else v2[k]) for k in v1}

def obs_join(
    o1: Dict[str, Fraction], r1: Dict[str, bool],
    o2: Dict[str, Fraction], r2: Dict[str, bool],
) -> Tuple[Dict[str, Fraction], Dict[str, bool]]:
    no, nr = {}, {}
    for k in o1:
        if o1[k] > o2[k]:
            no[k], nr[k] = o1[k], r1[k]
        elif o2[k] > o1[k]:
            no[k], nr[k] = o2[k], r2[k]
        else:
            no[k] = o1[k]
            nr[k] = r1[k] or r2[k]
    return no, nr

def copy_tv(tv: ThreadView) -> ThreadView:
    return ThreadView(
        dict(tv.cur), dict(tv.acq), dict(tv.rel),
        dict(tv.obs_cur), dict(tv.obs_acq), dict(tv.obs_rel),
        dict(tv.obs_is_read_cur), dict(tv.obs_is_read_acq), dict(tv.obs_is_read_rel),
        tv.s_last_sc, tv.s_left_hb_cur, tv.s_left_hb_acq, tv.s_left_hb_rel,
        tv.s_f_cur, tv.s_f_acq, tv.s_f_rel,
    )

def copy_mem(mem: Dict[str, List[OpMsgDense]]) -> Dict[str, List[OpMsgDense]]:
    return {
        k: [
            OpMsgDense(
                m.mo_ts, m.val, dict(m.msg_view), dict(m.obs_view), dict(m.obs_is_read_view),
                m.is_rmw_after_prev, m.s_self_sc, m.s_f_hb_w, m.s_read_sc_lb, m.s_read_f_lb,
                m.s_ub, m.s_left_msg, m.s_f_msg,
            )
            for m in lst
        ]
        for k, lst in mem.items()
    }

def live_eco_before_hb_lb(
    mem: Dict[str, List[OpMsgDense]],
    obs: Dict[str, Fraction],
    obs_is_read: Dict[str, bool],
) -> Fraction:
    lb = Fraction(0, 1)
    for l, mlist in mem.items():
        ots = obs[l]
        if ots < 0:
            continue
        for m in mlist:
            if m.mo_ts < ots:
                lb = max(lb, m.s_self_sc, m.s_f_hb_w, m.s_read_sc_lb, m.s_read_f_lb)
            elif m.mo_ts == ots and obs_is_read[l]:
                lb = max(lb, m.s_self_sc, m.s_f_hb_w)
    return lb

def enumerate_operational_outcomes(
    prog: LitmusProgram,
    locs: List[str],
    sc_mode: str,
    include_final_mo: bool = False,
) -> Set[Tuple]:
    zero = Fraction(0, 1)
    bot = {l: zero for l in locs}
    unobs = {l: NEG_ONE for l in locs}
    false_map = {l: False for l in locs}
    init_mem = {l: [OpMsgDense(zero, 0, dict(bot), dict(unobs), dict(false_map), False)] for l in locs}
    init_tvs = [
        ThreadView(
            dict(bot), dict(bot), dict(bot),
            dict(unobs), dict(unobs), dict(unobs),
            dict(false_map), dict(false_map), dict(false_map),
        )
        for _ in prog
    ]
    init_sc_view = dict(bot)
    outcomes: Set[Tuple] = set()
    visited_states: Set[Tuple] = set()

    def freeze_state(pcs, tvs, mem, sc_view, used_s, regs):
        ftvs = tuple(
            (
                tuple(sorted(t.cur.items())), tuple(sorted(t.acq.items())), tuple(sorted(t.rel.items())),
                tuple(sorted(t.obs_cur.items())), tuple(sorted(t.obs_acq.items())), tuple(sorted(t.obs_rel.items())),
                tuple(sorted(t.obs_is_read_cur.items())), tuple(sorted(t.obs_is_read_acq.items())), tuple(sorted(t.obs_is_read_rel.items())),
                t.s_last_sc, t.s_left_hb_cur, t.s_left_hb_acq, t.s_left_hb_rel, t.s_f_cur, t.s_f_acq, t.s_f_rel,
            )
            for t in tvs
        )
        fmem = tuple(
            (
                k,
                tuple(
                    (
                        m.mo_ts, m.val, tuple(sorted(m.msg_view.items())), tuple(sorted(m.obs_view.items())),
                        tuple(sorted(m.obs_is_read_view.items())), m.is_rmw_after_prev,
                        m.s_self_sc, m.s_f_hb_w, m.s_read_sc_lb, m.s_read_f_lb, m.s_ub, m.s_left_msg, m.s_f_msg,
                    )
                    for m in mem[k]
                ),
            )
            for k in locs
        )
        return (pcs, ftvs, fmem, tuple(sorted(sc_view.items())), used_s, tuple(sorted(regs.items())))

    def candidate_s_placements(used_s: Tuple[Fraction, ...], lb: Fraction, ub: Fraction) -> List[Fraction]:
        if lb >= ub:
            return []
        pts = [lb] + [x for x in used_s if lb < x < ub] + [ub]
        return [(pts[i] + pts[i + 1]) / 2 for i in range(len(pts) - 1)]

    def step_dfs(pcs, tvs, mem, sc_view, used_s, regs):
        skey = freeze_state(pcs, tvs, mem, sc_view, used_s, regs)
        if skey in visited_states:
            return
        visited_states.add(skey)
        if all(pcs[t] >= len(prog[t]) for t in range(len(prog))):
            regs_sorted = tuple((k, regs[k]) for k in sorted(regs.keys()))
            if include_final_mo:
                mo_sorted = tuple((k, mem[k][-1].val) for k in sorted(locs))
                outcomes.add((regs_sorted, mo_sorted))
            else:
                outcomes.add(regs_sorted)
            return

        for tid in range(len(prog)):
            pc = pcs[tid]
            if pc >= len(prog[tid]):
                continue
            ins = prog[tid][pc]
            next_pcs = pcs[:tid] + (pc + 1,) + pcs[tid + 1:]
            tv0 = tvs[tid]
            pre_sc = tv0.s_last_sc
            pre_left_hb = tv0.s_left_hb_cur
            left_sb_entering = max(pre_sc, pre_left_hb)

            if ins.kind == "fence":
                tv = copy_tv(tv0)
                nmem = copy_mem(mem)
                nsc = dict(sc_view)
                if has_acq(ins.ord):
                    tv.cur = vmax(tv.cur, tv.acq)
                    tv.obs_cur, tv.obs_is_read_cur = obs_join(
                        tv.obs_cur, tv.obs_is_read_cur, tv.obs_acq, tv.obs_is_read_acq
                    )
                    tv.s_left_hb_cur = max(tv.s_left_hb_cur, tv.s_left_hb_acq)
                    tv.s_f_cur = max(tv.s_f_cur, tv.s_f_acq)

                if ins.ord == SC and sc_mode in ("op_sc1a_global_all", "op_sc1b_perloc_acc_global_fence", "op_sc1c_fence_only"):
                    joined = vmax(tv.cur, nsc)
                    tv.cur = dict(joined)
                    tv.acq = vmax(tv.acq, joined)
                    nsc = dict(joined)
                    tv.rel = dict(tv.cur)
                    step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, nsc, used_s, regs)
                elif ins.ord == SC and sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug"):
                    live_eco_lb = live_eco_before_hb_lb(nmem, tv.obs_cur, tv.obs_is_read_cur)
                    lb = max(pre_sc, pre_left_hb, tv.s_f_cur, live_eco_lb)
                    for s_val in candidate_s_placements(used_s, lb, INF):
                        tv_b = copy_tv(tv)
                        mem_b = copy_mem(nmem)
                        tv_b.s_last_sc = max(tv_b.s_last_sc, s_val)
                        tv_b.s_f_cur = max(tv_b.s_f_cur, s_val)
                        tv_b.s_f_acq = max(tv_b.s_f_acq, s_val)
                        tv_b.rel = dict(tv_b.cur)
                        tv_b.obs_rel = dict(tv_b.obs_cur)
                        tv_b.obs_is_read_rel = dict(tv_b.obs_is_read_cur)
                        tv_b.s_left_hb_rel = max(left_sb_entering, tv_b.s_left_hb_cur)
                        tv_b.s_f_rel = tv_b.s_f_cur
                        for l in locs:
                            ots = tv_b.obs_cur[l]
                            if ots >= 0:
                                for m in mem_b[l]:
                                    if m.mo_ts <= ots and s_val < m.s_ub:
                                        m.s_ub = s_val
                        step_dfs(next_pcs, tvs[:tid] + [tv_b] + tvs[tid + 1:], mem_b, nsc, tuple(sorted(used_s + (s_val,))), regs)
                else:
                    if has_rel(ins.ord):
                        tv.rel = dict(tv.cur)
                        tv.obs_rel = dict(tv.obs_cur)
                        tv.obs_is_read_rel = dict(tv.obs_is_read_cur)
                        tv.s_left_hb_rel = left_sb_entering if sc_mode == "op_sc2_unpatched_bug" else max(left_sb_entering, tv.s_left_hb_cur)
                        tv.s_f_rel = tv.s_f_cur
                    step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, nsc, used_s, regs)

            elif ins.kind == "load":
                loc = ins.loc
                mlist = mem[loc]
                min_ts = tv0.cur[loc]
                if ins.ord == SC and sc_mode in ("op_sc1a_global_all", "op_sc1b_perloc_acc_global_fence"):
                    min_ts = max(min_ts, sc_view[loc])

                for idx, m in enumerate(mlist):
                    if m.mo_ts < min_ts:
                        continue
                    eco_in_lb = zero
                    for j in range(idx + 1):
                        mj = mlist[j]
                        eco_in_lb = max(eco_in_lb, mj.s_self_sc, mj.s_f_hb_w)
                        if j < idx:
                            eco_in_lb = max(eco_in_lb, mj.s_read_sc_lb, mj.s_read_f_lb)
                    eco_out_ub = INF
                    for k in range(idx + 1, len(mlist)):
                        eco_out_ub = min(eco_out_ub, mlist[k].s_ub)

                    if sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug") and tv0.s_f_cur >= eco_out_ub:
                        continue

                    if ins.ord == SC and sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug"):
                        lb = max(pre_sc, pre_left_hb, eco_in_lb)
                        for s_val in candidate_s_placements(used_s, lb, eco_out_ub):
                            tv = copy_tv(tv0)
                            nmem = copy_mem(mem)
                            rm = nmem[loc][idx]
                            rm.s_read_sc_lb = max(rm.s_read_sc_lb, s_val)
                            rm.s_read_f_lb = max(rm.s_read_f_lb, tv.s_f_cur)
                            rm.s_ub = min(rm.s_ub, s_val)
                            tv.cur[loc] = max(tv.cur[loc], rm.mo_ts)
                            tv.acq[loc] = max(tv.acq[loc], rm.mo_ts)
                            tv.cur = vmax(tv.cur, rm.msg_view)
                            tv.acq = vmax(tv.acq, rm.msg_view)
                            read_obs = dict(unobs); read_obs[loc] = rm.mo_ts
                            read_isr = dict(false_map); read_isr[loc] = True
                            tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, read_obs, read_isr)
                            tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, rm.obs_view, rm.obs_is_read_view)
                            tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, tv.obs_cur, tv.obs_is_read_cur)
                            tv.s_last_sc = max(tv.s_last_sc, s_val)
                            tv.s_left_hb_cur = max(left_sb_entering, rm.s_left_msg)
                            tv.s_left_hb_acq = max(tv.s_left_hb_acq, tv.s_left_hb_cur)
                            tv.s_f_cur = max(tv.s_f_cur, rm.s_f_msg)
                            tv.s_f_acq = max(tv.s_f_acq, tv.s_f_cur)
                            nregs = dict(regs)
                            if ins.reg: nregs[ins.reg] = rm.val
                            step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, dict(sc_view), tuple(sorted(used_s + (s_val,))), nregs)
                    else:
                        tv = copy_tv(tv0)
                        nmem = copy_mem(mem)
                        nsc = dict(sc_view)
                        rm = nmem[loc][idx]
                        if sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug"):
                            rm.s_read_f_lb = max(rm.s_read_f_lb, tv.s_f_cur)
                        tv.cur[loc] = max(tv.cur[loc], rm.mo_ts)
                        tv.acq[loc] = max(tv.acq[loc], rm.mo_ts)
                        tv.acq = vmax(tv.acq, rm.msg_view)
                        read_obs = dict(unobs); read_obs[loc] = rm.mo_ts
                        read_isr = dict(false_map); read_isr[loc] = True
                        tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, read_obs, read_isr)
                        tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, read_obs, read_isr)
                        tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, rm.obs_view, rm.obs_is_read_view)
                        tv.s_left_hb_acq = max(tv.s_left_hb_acq, left_sb_entering, rm.s_left_msg)
                        tv.s_f_acq = max(tv.s_f_acq, tv.s_f_cur, rm.s_f_msg)
                        if has_acq(ins.ord):
                            tv.cur = vmax(tv.cur, rm.msg_view)
                            tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, rm.obs_view, rm.obs_is_read_view)
                            tv.s_left_hb_cur = max(left_sb_entering, rm.s_left_msg)
                            tv.s_f_cur = max(tv.s_f_cur, rm.s_f_msg)
                        else:
                            tv.s_left_hb_cur = max(tv.s_left_hb_cur, left_sb_entering)
                        if ins.ord == SC:
                            if sc_mode == "op_sc1a_global_all":
                                nsc[loc] = max(nsc[loc], rm.mo_ts)
                                joined = vmax(tv.cur, nsc)
                                tv.cur = dict(joined); tv.acq = vmax(tv.acq, joined); nsc = dict(joined)
                            elif sc_mode == "op_sc1b_perloc_acc_global_fence":
                                nsc[loc] = max(nsc[loc], rm.mo_ts)
                        nregs = dict(regs)
                        if ins.reg: nregs[ins.reg] = rm.val
                        step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, nsc, used_s, nregs)

            elif ins.kind in ("store", "fad"):
                loc = ins.loc
                mlist = mem[loc]
                min_ts = tv0.cur[loc]
                if ins.ord == SC and sc_mode in ("op_sc1a_global_all", "op_sc1b_perloc_acc_global_fence"):
                    min_ts = max(min_ts, sc_view[loc])

                for after_idx in range(len(mlist)):
                    if after_idx + 1 < len(mlist) and mlist[after_idx + 1].is_rmw_after_prev:
                        continue
                    if ins.kind == "fad":
                        if mlist[after_idx].mo_ts < min_ts:
                            continue
                    else:
                        if after_idx + 1 < len(mlist) and mlist[after_idx + 1].mo_ts <= min_ts:
                            continue

                    lo_mo = max(mlist[after_idx].mo_ts, min_ts) if ins.kind == "store" else mlist[after_idx].mo_ts
                    new_mo_ts = (lo_mo + mlist[after_idx + 1].mo_ts) / 2 if after_idx + 1 < len(mlist) else lo_mo + Fraction(1, 1)

                    eco_in_lb = zero
                    for j in range(after_idx + 1):
                        mj = mlist[j]
                        eco_in_lb = max(eco_in_lb, mj.s_self_sc, mj.s_f_hb_w, mj.s_read_sc_lb, mj.s_read_f_lb)
                    eco_out_ub = INF
                    for k in range(after_idx + 1, len(mlist)):
                        eco_out_ub = min(eco_out_ub, mlist[k].s_ub)

                    if sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug") and tv0.s_f_cur >= eco_out_ub:
                        continue

                    wval = (mlist[after_idx].val + ins.val) if ins.kind == "fad" else ins.val
                    write_obs = dict(unobs); write_obs[loc] = new_mo_ts
                    write_isr = dict(false_map); write_isr[loc] = False

                    if ins.ord == SC and sc_mode in ("op_sc2_p0668_stime", "op_sc2_unpatched_bug"):
                        lb = max(pre_sc, pre_left_hb, eco_in_lb)
                        for s_val in candidate_s_placements(used_s, lb, eco_out_ub):
                            tv = copy_tv(tv0)
                            nmem = copy_mem(mem)
                            base_m = nmem[loc][after_idx]
                            tv.cur[loc] = new_mo_ts
                            tv.acq[loc] = max(tv.acq[loc], new_mo_ts)
                            tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, write_obs, write_isr)
                            if ins.kind == "fad":
                                tv.cur = vmax(tv.cur, base_m.msg_view)
                                tv.acq = vmax(tv.acq, base_m.msg_view)
                                tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, base_m.obs_view, base_m.obs_is_read_view)
                                s_left_out = max(left_sb_entering, base_m.s_left_msg)
                                s_f_out = max(tv.s_f_cur, base_m.s_f_msg)
                            else:
                                s_left_out = left_sb_entering
                                s_f_out = tv.s_f_cur
                            tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, tv.obs_cur, tv.obs_is_read_cur)
                            tv.s_last_sc = max(tv.s_last_sc, s_val)
                            tv.s_left_hb_cur = s_left_out; tv.s_left_hb_acq = max(tv.s_left_hb_acq, s_left_out)
                            tv.s_f_cur = s_f_out; tv.s_f_acq = max(tv.s_f_acq, s_f_out)

                            new_msg = OpMsgDense(
                                mo_ts=new_mo_ts, val=wval, msg_view=dict(tv.cur),
                                obs_view=dict(tv.obs_cur), obs_is_read_view=dict(tv.obs_is_read_cur),
                                is_rmw_after_prev=(ins.kind == "fad"),
                                s_self_sc=s_val, s_f_hb_w=s_f_out,
                                s_read_sc_lb=s_val if ins.kind == "fad" else zero,
                                s_read_f_lb=s_f_out if ins.kind == "fad" else zero,
                                s_ub=min(eco_out_ub, s_val), s_left_msg=s_left_out, s_f_msg=s_f_out,
                            )
                            nmem[loc].insert(after_idx + 1, new_msg)
                            nregs = dict(regs)
                            if ins.kind == "fad" and ins.reg: nregs[ins.reg] = base_m.val
                            step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, dict(sc_view), tuple(sorted(used_s + (s_val,))), nregs)
                    else:
                        tv = copy_tv(tv0)
                        nmem = copy_mem(mem)
                        nsc = dict(sc_view)
                        base_m = nmem[loc][after_idx]
                        tv.cur[loc] = new_mo_ts
                        tv.acq[loc] = max(tv.acq[loc], new_mo_ts)
                        tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, write_obs, write_isr)
                        tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, write_obs, write_isr)

                        if ins.kind == "fad":
                            tv.acq = vmax(tv.acq, base_m.msg_view)
                            tv.obs_acq, tv.obs_is_read_acq = obs_join(tv.obs_acq, tv.obs_is_read_acq, base_m.obs_view, base_m.obs_is_read_view)
                            tv.s_left_hb_acq = max(tv.s_left_hb_acq, left_sb_entering, base_m.s_left_msg)
                            tv.s_f_acq = max(tv.s_f_acq, tv.s_f_cur, base_m.s_f_msg)
                            if has_acq(ins.ord):
                                tv.cur = vmax(tv.cur, base_m.msg_view)
                                tv.obs_cur, tv.obs_is_read_cur = obs_join(tv.obs_cur, tv.obs_is_read_cur, base_m.obs_view, base_m.obs_is_read_view)
                                tv.s_left_hb_cur = max(left_sb_entering, base_m.s_left_msg)
                                tv.s_f_cur = max(tv.s_f_cur, base_m.s_f_msg)
                            else:
                                tv.s_left_hb_cur = max(tv.s_left_hb_cur, left_sb_entering)
                        else:
                            tv.s_left_hb_cur = max(tv.s_left_hb_cur, left_sb_entering)
                            tv.s_left_hb_acq = max(tv.s_left_hb_acq, left_sb_entering)

                        if ins.ord == SC:
                            if sc_mode == "op_sc1a_global_all":
                                nsc[loc] = new_mo_ts
                                joined = vmax(tv.cur, nsc)
                                tv.cur = dict(joined); tv.acq = vmax(tv.acq, joined); nsc = dict(joined)
                            elif sc_mode == "op_sc1b_perloc_acc_global_fence":
                                nsc[loc] = new_mo_ts

                        # P0982R1 Release-Sequence View Rule (including Release-only RMWs!):
                        if ins.kind == "fad" and has_rel(ins.ord):
                            m_view = vmax(base_m.msg_view, tv.cur)
                            m_obs, m_isr = obs_join(base_m.obs_view, base_m.obs_is_read_view, tv.obs_cur, tv.obs_is_read_cur)
                            m_s_left = max(base_m.s_left_msg, tv.s_left_hb_cur)
                            m_s_f = max(base_m.s_f_msg, tv.s_f_cur)
                        elif has_rel(ins.ord):
                            m_view = dict(tv.cur); m_obs = dict(tv.obs_cur); m_isr = dict(tv.obs_is_read_cur)
                            m_s_left = tv.s_left_hb_cur; m_s_f = tv.s_f_cur
                        elif ins.kind == "fad":
                            m_view = vmax(base_m.msg_view, tv.rel)
                            m_obs, m_isr = obs_join(base_m.obs_view, base_m.obs_is_read_view, tv.obs_rel, tv.obs_is_read_rel)
                            m_s_left = max(base_m.s_left_msg, tv.s_left_hb_rel)
                            m_s_f = max(base_m.s_f_msg, tv.s_f_rel)
                        else:
                            m_view = dict(tv.rel); m_obs = dict(tv.obs_rel); m_isr = dict(tv.obs_is_read_rel)
                            m_s_left = tv.s_left_hb_rel; m_s_f = tv.s_f_rel

                        new_msg = OpMsgDense(
                            mo_ts=new_mo_ts, val=wval, msg_view=m_view,
                            obs_view=m_obs, obs_is_read_view=m_isr,
                            is_rmw_after_prev=(ins.kind == "fad"),
                            s_self_sc=zero, s_f_hb_w=tv.s_f_cur,
                            s_read_sc_lb=zero, s_read_f_lb=tv.s_f_cur if ins.kind == "fad" else zero,
                            s_ub=eco_out_ub, s_left_msg=m_s_left, s_f_msg=m_s_f,
                        )
                        nmem[loc].insert(after_idx + 1, new_msg)
                        nregs = dict(regs)
                        if ins.kind == "fad" and ins.reg: nregs[ins.reg] = base_m.val
                        step_dfs(next_pcs, tvs[:tid] + [tv] + tvs[tid + 1:], nmem, nsc, used_s, nregs)

    step_dfs(tuple(0 for _ in prog), init_tvs, init_mem, init_sc_view, (), {})
    return outcomes


def run_verification():

    # 0. Canonical 15 2-3T litmus suite (comparing C++20 P0668R5, ARMv8.0, ARMv8.3 +rcpc, SC-1a, SC-1b, SC-1c, and Op-SC2')
    litmus15 = [
        ("MP+rel+rmw_rlx+acq", [
            [Instr("store", "x", 1, RLX), Instr("store", "y", 1, REL)],
            [Instr("fad", "y", 1, RLX, "r0")],
            [Instr("load", "y", 0, ACQ, "r1"), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r0", 1), ("r1", 2), ("r2", 0))),
        ("MP+rel+rmw_rel+acq", [
            [Instr("store", "x", 1, RLX), Instr("store", "y", 1, REL)],
            [Instr("fad", "y", 1, REL, "r0")],
            [Instr("load", "y", 0, ACQ, "r1"), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r0", 1), ("r1", 2), ("r2", 0))),
        ("MP+rel+write_rlx+acq", [
            [Instr("store", "x", 1, RLX), Instr("store", "y", 1, REL), Instr("store", "y", 2, RLX)],
            [Instr("load", "y", 0, ACQ, "r1"), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r1", 2), ("r2", 0))),
        ("SB+rlx", [
            [Instr("store", "x", 1, RLX), Instr("load", "y", 0, RLX, "r1")],
            [Instr("store", "y", 1, RLX), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r1", 0), ("r2", 0))),
        ("SB+sc_accesses", [
            [Instr("store", "x", 1, SC), Instr("load", "y", 0, SC, "r1")],
            [Instr("store", "y", 1, SC), Instr("load", "x", 0, SC, "r2")],
        ], ["x", "y"], (("r1", 0), ("r2", 0))),
        ("SB+sc_fences", [
            [Instr("store", "x", 1, RLX), Instr("fence", None, 0, SC), Instr("load", "y", 0, RLX, "r1")],
            [Instr("store", "y", 1, RLX), Instr("fence", None, 0, SC), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r1", 0), ("r2", 0))),
        ("SB+mixed_sc_fence_access", [
            [Instr("store", "x", 1, SC), Instr("load", "y", 0, SC, "r1")],
            [Instr("store", "y", 1, RLX), Instr("fence", None, 0, SC), Instr("load", "x", 0, RLX, "r2")],
        ], ["x", "y"], (("r1", 0), ("r2", 0))),
        ("SB+sc_acq", [
            [Instr("store", "x", 1, SC), Instr("load", "y", 0, ACQ, "r1")],
            [Instr("store", "y", 1, SC), Instr("load", "x", 0, SC, "r2")],
        ], ["x", "y"], (("r1", 0), ("r2", 0))),
        ("RWC+sc+acq", [
            [Instr("store", "x", 1, SC)],
            [Instr("load", "x", 0, ACQ, "r1"), Instr("load", "y", 0, SC, "r2")],
            [Instr("store", "y", 1, SC), Instr("load", "x", 0, SC, "r3")],
        ], ["x", "y"], (("r1", 1), ("r2", 0), ("r3", 0))),
        ("Z6.U", [
            [Instr("store", "x", 1, SC), Instr("store", "y", 1, REL)],
            [Instr("fad", "y", 1, SC, "r1"), Instr("load", "y", 0, RLX, "r2")],
            [Instr("store", "y", 3, SC), Instr("load", "x", 0, SC, "r3")],
        ], ["x", "y"], (("r1", 1), ("r2", 3), ("r3", 0))),
        ("IRIW+sc", [
            [Instr("store", "x", 1, SC)],
            [Instr("load", "x", 0, SC, "r1"), Instr("load", "y", 0, SC, "r2")],
            [Instr("store", "y", 1, SC)],
            [Instr("load", "y", 0, SC, "r3"), Instr("load", "x", 0, SC, "r4")],
        ], ["x", "y"], (("r1", 1), ("r2", 0), ("r3", 1), ("r4", 0))),
        ("IRIW+acq", [
            [Instr("store", "x", 1, REL)],
            [Instr("load", "x", 0, ACQ, "r1"), Instr("load", "y", 0, ACQ, "r2")],
            [Instr("store", "y", 1, REL)],
            [Instr("load", "y", 0, ACQ, "r3"), Instr("load", "x", 0, ACQ, "r4")],
        ], ["x", "y"], (("r1", 1), ("r2", 0), ("r3", 1), ("r4", 0))),
        ("2+2W+rlx", [
            [Instr("store", "x", 1, RLX), Instr("store", "y", 2, RLX)],
            [Instr("store", "y", 1, RLX), Instr("store", "x", 2, RLX)],
        ], ["x", "y"], None),
        ("2+2W+sc", [
            [Instr("store", "x", 1, SC), Instr("store", "y", 2, SC)],
            [Instr("store", "y", 1, SC), Instr("store", "x", 2, SC)],
        ], ["x", "y"], None),
        ("LB+rlx", [
            [Instr("load", "x", 0, RLX, "r1"), Instr("store", "y", 1, RLX)],
            [Instr("load", "y", 0, RLX, "r2"), Instr("store", "x", 1, RLX)],
        ], ["x", "y"], (("r1", 1), ("r2", 1))),
    ]
    print("=== 15 CANONICAL LITMUS TESTS (C++20 vs ARMv8.3 +rcpc vs SC-1a/1b vs Op-SC2') ===", flush=True)
    for name, prg, lcs, target in litmus15:
        ax = enumerate_axiomatic_outcomes(prg, lcs, "cpp20_p0668", include_final_mo=True)
        op = enumerate_operational_outcomes(prg, lcs, "op_sc2_p0668_stime", include_final_mo=True)
        assert op == ax, f"Mismatch on {name}: {op ^ ax}"
        if name == "SB+sc_acq":
            v83 = {r for (r, _) in enumerate_axiomatic_outcomes(prg, lcs, "armv8_3_rcpc", include_final_mo=True)}
            sc1a = {r for (r, _) in enumerate_operational_outcomes(prg, lcs, "op_sc1a_global_all", include_final_mo=True)}
            sc1b = {r for (r, _) in enumerate_operational_outcomes(prg, lcs, "op_sc1b_perloc_acc_global_fence", include_final_mo=True)}
            assert target in v83 and target not in sc1a and target in sc1b
        if name in ("RWC+sc+acq", "Z6.U"):
            sc1b = {r for (r, _) in enumerate_operational_outcomes(prg, lcs, "op_sc1b_perloc_acc_global_fence", include_final_mo=True)}
            ax_regs = {r for (r, _) in ax}
            assert target in ax_regs and target not in sc1b
        print(f"Litmus {name:26s}: EXACT=True (outcomes={len(ax)})", flush=True)

    p4_acqrel = [
        [Instr("store", "x", 1, SC), Instr("store", "y", 1, REL)],
        [Instr("load", "y", 0, RLX, "r1"), Instr("fence", None, 0, ACQ_REL), Instr("store", "z", 1, RLX)],
        [Instr("load", "z", 0, ACQ, "r2"), Instr("load", "w", 0, SC, "r3")],
        [Instr("store", "w", 1, SC), Instr("load", "x", 0, SC, "r4")],
    ]
    locs4 = ["x", "y", "z", "w"]
    bad_outcome = (("r1", 1), ("r2", 1), ("r3", 0), ("r4", 0))

    ax_p4 = enumerate_axiomatic_outcomes(p4_acqrel, locs4, "cpp20_p0668", include_final_mo=True)
    ax_p4_regs = {r for (r, _) in ax_p4}
    op_unpatched_p4 = enumerate_operational_outcomes(p4_acqrel, locs4, "op_sc2_unpatched_bug", include_final_mo=True)
    op_unpatched_regs = {r for (r, _) in op_unpatched_p4}
    op_fixed_p4 = enumerate_operational_outcomes(p4_acqrel, locs4, "op_sc2_p0668_stime", include_final_mo=True)
    op_fixed_regs = {r for (r, _) in op_fixed_p4}

    print("=== 4-THREAD FENCE(ACQREL) COUNTER-WITNESS & FIX VERIFICATION ===", flush=True)
    print(f"C++20 P0668R5 allows (1,1,0,0):          {bad_outcome in ax_p4_regs} (total (regs,mo)={len(ax_p4)})", flush=True)
    print(f"Unpatched Op-SC2 allows (1,1,0,0) [BUG]: {bad_outcome in op_unpatched_regs} (total (regs,mo)={len(op_unpatched_p4)})", flush=True)
    print(f"Patched Op-SC2' allows (1,1,0,0):        {bad_outcome in op_fixed_regs} (total (regs,mo)={len(op_fixed_p4)})", flush=True)
    print(f"Patched Op-SC2' == C++20 on P_4_acqrel:  {op_fixed_p4 == ax_p4}", flush=True)
    assert bad_outcome not in ax_p4_regs
    assert bad_outcome in op_unpatched_regs
    assert op_fixed_p4 == ax_p4

    extra_4t = [
        ("4T_IRIW+sc_fences", [
            [Instr("store", "x", 1, RLX)],
            [Instr("load", "x", 0, ACQ, "r1"), Instr("fence", None, 0, SC), Instr("load", "y", 0, RLX, "r2")],
            [Instr("store", "y", 1, RLX)],
            [Instr("load", "y", 0, ACQ, "r3"), Instr("fence", None, 0, SC), Instr("load", "x", 0, RLX, "r4")],
        ], ["x", "y"]),
        ("4T_AcqRelChain+RMW+SC", [
            [Instr("store", "x", 1, SC), Instr("fad", "y", 1, REL, "r0")],
            [Instr("fad", "y", 1, RLX, "r1"), Instr("fence", None, 0, ACQ_REL), Instr("store", "z", 1, RLX)],
            [Instr("load", "z", 0, RLX, "r2"), Instr("fence", None, 0, ACQ), Instr("load", "w", 0, SC, "r3")],
            [Instr("store", "w", 1, SC), Instr("load", "x", 0, SC, "r4")],
        ], ["x", "y", "z", "w"]),
        ("4T_WRC+Fsc+AcqRel", [
            [Instr("store", "x", 1, SC)],
            [Instr("load", "x", 0, RLX, "r1"), Instr("fence", None, 0, ACQ_REL), Instr("store", "y", 1, RLX)],
            [Instr("load", "y", 0, ACQ, "r2"), Instr("fence", None, 0, SC), Instr("load", "z", 0, RLX, "r3")],
            [Instr("store", "z", 1, RLX), Instr("fence", None, 0, SC), Instr("load", "x", 0, SC, "r4")],
        ], ["x", "y", "z"]),
    ]
    for name, prg, lcs in extra_4t:
        ax = enumerate_axiomatic_outcomes(prg, lcs, "cpp20_p0668", include_final_mo=True)
        op = enumerate_operational_outcomes(prg, lcs, "op_sc2_p0668_stime", include_final_mo=True)
        print(f"Litmus {name:24s}: EXACT={op == ax} (outcomes={len(ax)})", flush=True)
        assert op == ax, f"Mismatch on {name}: only_op={op - ax}, only_ax={ax - op}"

    rng = random.Random(20261122)
    ords = [RLX, REL, ACQ, ACQ_REL, SC]
    total_checked = 0
    for n_threads, n_trials, max_ins in [(2, 40, 3), (3, 50, 2), (4, 60, 2)]:
        locs_pool = ["x", "y", "z"] if n_threads <= 3 else ["x", "y", "z", "w"]
        for t_i in range(n_trials):
            prog = []
            reg_id = 0
            val_id = 1
            for th in range(n_threads):
                k_len = 2 if n_threads == 4 else rng.randint(1, max_ins)
                t_ins = []
                for _ in range(k_len):
                    kind = rng.choice(["load", "store", "fad", "fence"])
                    if kind == "fence":
                        o = rng.choice([ACQ, REL, ACQ_REL, SC])
                        t_ins.append(Instr("fence", None, 0, o, None))
                    elif kind == "load":
                        o = rng.choice([RLX, ACQ, SC])
                        reg_id += 1
                        t_ins.append(Instr("load", rng.choice(locs_pool), 0, o, f"r{reg_id}"))
                    elif kind == "store":
                        o = rng.choice([RLX, REL, SC])
                        val_id += 1
                        t_ins.append(Instr("store", rng.choice(locs_pool), val_id, o, None))
                    else:
                        o = rng.choice(ords)
                        reg_id += 1
                        t_ins.append(Instr("fad", rng.choice(locs_pool), 1, o, f"r{reg_id}"))
                prog.append(t_ins)
            used_locs = sorted({ins.loc for th in prog for ins in th if ins.loc is not None})
            if not used_locs:
                used_locs = ["x"]
            ax = enumerate_axiomatic_outcomes(prog, used_locs, "cpp20_p0668", include_final_mo=True)
            op = enumerate_operational_outcomes(prog, used_locs, "op_sc2_p0668_stime", include_final_mo=True)
            if op != ax:
                print(f"MISMATCH on {n_threads}T trial {t_i}: prog={prog}", flush=True)
                print("only_op:", op - ax, flush=True)
                print("only_ax:", ax - op, flush=True)
                sys.exit(1)
            total_checked += 1
        print(f"Completed {n_threads}T batch ({n_trials} programs): 100% exact!", flush=True)
    print(f"RANDOM DIFFERENTIAL FUZZING (2T=40, 3T=50, 4T=60 => {total_checked} programs): 100% EXACT (regs, final_mo) MATCH!", flush=True)

if __name__ == "__main__":
    run_verification()
