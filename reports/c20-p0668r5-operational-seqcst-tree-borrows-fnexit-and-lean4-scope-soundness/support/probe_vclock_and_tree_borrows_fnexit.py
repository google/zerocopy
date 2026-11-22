#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

@dataclass
class Skeleton04GlobalMem:
    na_val: Dict[int, Optional[int]] = field(default_factory=dict)
    na_write_ts: Dict[int, int] = field(default_factory=dict)
    na_read_ts: Dict[int, int] = field(default_factory=dict)

    def init_loc(self, loc: int, val: int, ts: int = 0) -> None:
        self.na_val[loc] = val
        self.na_write_ts[loc] = ts
        self.na_read_ts[loc] = ts

    def read_na(self, cur_view: Dict[int, int], loc: int) -> Optional[int]:
        w_ts = self.na_write_ts.get(loc, 0)
        c_ts = cur_view.get(loc, 0)
        if w_ts <= c_ts:
            if loc not in self.na_val or self.na_val[loc] is None:
                return None
            r_ts = self.na_read_ts.get(loc, 0)
            self.na_read_ts[loc] = max(r_ts, c_ts)
            return self.na_val[loc]
        return None

    def write_na(self, cur_view: Dict[int, int], loc: int, val: int) -> bool:
        w_ts = self.na_write_ts.get(loc, 0)
        r_ts = self.na_read_ts.get(loc, 0)
        c_ts = cur_view.get(loc, 0)
        if w_ts <= c_ts and r_ts <= c_ts:
            next_ts = c_ts + 1
            cur_view[loc] = max(c_ts, next_ts)
            self.na_val[loc] = val
            self.na_write_ts[loc] = max(w_ts, next_ts)
            self.na_read_ts[loc] = max(r_ts, next_ts)
            return True
        return False


VClock = Dict[int, int]

def vc_le(c1: VClock, c2: VClock) -> bool:
    return all(v <= c2.get(t, 0) for t, v in c1.items())

def vc_join(c1: VClock, c2: VClock) -> VClock:
    out = dict(c1)
    for t, v in c2.items():
        if v > out.get(t, 0):
            out[t] = v
    return out

@dataclass
class LocRaceState:
    na_write: Optional[Tuple[int, int]] = None
    na_reads: Dict[int, int] = field(default_factory=dict)
    at_write: VClock = field(default_factory=dict)
    at_read: VClock = field(default_factory=dict)

class VClockRaceMachine:
    def __init__(self, n_threads: int):
        self.clocks: Dict[int, VClock] = {t: {t: 1} for t in range(n_threads)}
        self.locs: Dict[int, LocRaceState] = {}
        self.rel_views: Dict[Tuple[int, int], VClock] = {}
        self.loc_val: Dict[int, int] = {}
        self.loc_seq: Dict[int, int] = {}

    def _loc(self, loc: int) -> LocRaceState:
        return self.locs.setdefault(loc, LocRaceState())

    def tick(self, tid: int) -> None:
        self.clocks[tid][tid] = self.clocks[tid].get(tid, 0) + 1

    def fork_from(self, parent: int, child: int) -> None:
        self.clocks[child] = vc_join(self.clocks[child], self.clocks[parent])
        self.tick(parent)

    def check_and_record_na_read(self, tid: int, loc: int) -> Tuple[bool, str]:
        st = self._loc(loc)
        tc = self.clocks[tid]
        if st.na_write is not None:
            wt, we = st.na_write
            if we > tc.get(wt, 0):
                return False, f"UB DataRace(NaWrite T{wt}@{we} vs NaRead T{tid}@{tc})"
        if not vc_le(st.at_write, tc):
            return False, f"UB DataRace(AtomicWrite {st.at_write} vs NaRead T{tid}@{tc})"
        st.na_reads[tid] = tc[tid]
        return True, "ok"

    def check_and_record_na_write(self, tid: int, loc: int, cause: str = "NaWrite") -> Tuple[bool, str]:
        st = self._loc(loc)
        tc = self.clocks[tid]
        if st.na_write is not None:
            wt, we = st.na_write
            if we > tc.get(wt, 0):
                return False, f"UB DataRace(NaWrite T{wt}@{we} vs {cause} T{tid}@{tc})"
        for rt, re in st.na_reads.items():
            if re > tc.get(rt, 0):
                return False, f"UB DataRace(NaRead T{rt}@{re} vs {cause} T{tid}@{tc})"
        if not vc_le(st.at_write, tc):
            return False, f"UB DataRace(AtomicWrite {st.at_write} vs {cause} T{tid}@{tc})"
        if not vc_le(st.at_read, tc):
            return False, f"UB DataRace(AtomicRead {st.at_read} vs {cause} T{tid}@{tc})"
        st.na_write = (tid, tc[tid])
        st.na_reads = {}
        return True, "ok"

    def check_and_record_atomic_store(self, tid: int, loc: int, val: int, ord_kind: str) -> Tuple[bool, str]:
        st = self._loc(loc)
        tc = self.clocks[tid]
        if st.na_write is not None:
            wt, we = st.na_write
            if we > tc.get(wt, 0):
                return False, f"UB DataRace(NaWrite T{wt}@{we} vs AtomicStore({ord_kind}) T{tid}@{tc})"
        for rt, re in st.na_reads.items():
            if re > tc.get(rt, 0):
                return False, f"UB DataRace(NaRead T{rt}@{re} vs AtomicStore({ord_kind}) T{tid}@{tc})"
        st.at_write[tid] = max(st.at_write.get(tid, 0), tc[tid])
        seq = self.loc_seq.get(loc, 0) + 1
        self.loc_seq[loc] = seq
        self.loc_val[loc] = val
        self.rel_views[(loc, seq)] = dict(tc) if ord_kind in ("Release", "AcqRel", "SeqCst") else {}
        self.tick(tid)
        return True, "ok"

    def check_and_record_atomic_load(self, tid: int, loc: int, ord_kind: str) -> Tuple[bool, str, int]:
        st = self._loc(loc)
        tc = self.clocks[tid]
        if st.na_write is not None:
            wt, we = st.na_write
            if we > tc.get(wt, 0):
                return False, f"UB DataRace(NaWrite T{wt}@{we} vs AtomicLoad({ord_kind}) T{tid}@{tc})", -1
        seq = self.loc_seq.get(loc, 0)
        val = self.loc_val.get(loc, 0)
        if ord_kind in ("Acquire", "AcqRel", "SeqCst"):
            self.clocks[tid] = vc_join(self.clocks[tid], self.rel_views.get((loc, seq), {}))
            tc = self.clocks[tid]
        st.at_read[tid] = max(st.at_read.get(tid, 0), tc[tid])
        self.tick(tid)
        return True, "ok", val


CELL, RES_IM, RES_FRZ_CLEAN, RES_FRZ_CONFL, UNIQUE, FROZEN, DISABLED = (
    "Cell", "ReservedIM", "ReservedFrz(clean)", "ReservedFrz(conflicted)", "Unique", "Frozen", "Disabled"
)

def tb_associated_access(perm: str) -> Optional[str]:
    if perm == CELL: return None
    if perm == UNIQUE: return "Write"
    return "Read"

def tb_transition(kind: str, is_foreign: bool, state: str, protected: bool) -> Optional[str]:
    if not is_foreign:
        if kind == "Read":
            return None if state == DISABLED else state
        if state in (DISABLED, FROZEN) or (state == RES_FRZ_CONFL and protected):
            return None
        return CELL if state == CELL else UNIQUE
    else:
        if kind == "Read":
            if state in (CELL, RES_IM, FROZEN, DISABLED): return state
            if state in (RES_FRZ_CLEAN, RES_FRZ_CONFL):
                return RES_FRZ_CONFL if protected else RES_FRZ_CLEAN
            if state == UNIQUE:
                return None if protected else FROZEN
        else:
            if state == CELL: return CELL
            if state == RES_IM:
                assert not protected
                return RES_IM
            return None if protected else DISABLED
    return None

@dataclass
class TBNode:
    tag: int
    parent: Optional[int]
    children: List[int] = field(default_factory=list)
    perm: str = UNIQUE
    accessed: bool = False
    protected: bool = False

class TreeBorrowsWithVClock:
    def __init__(self, n_threads: int, emit_vclock_on_fn_exit: bool):
        self.emit_vclock_on_fn_exit = emit_vclock_on_fn_exit
        self.race = VClockRaceMachine(n_threads)
        self.trees: Dict[int, Dict[int, TBNode]] = {}
        self.next_tag = 0

    def alloc_root(self, init_tid: int, loc: int, val: int = 0) -> int:
        tag = self.next_tag; self.next_tag += 1
        self.trees[loc] = {tag: TBNode(tag=tag, parent=None, perm=UNIQUE, accessed=True, protected=False)}
        self.race.loc_val[loc] = val; self.race.loc_seq[loc] = 0; self.race.tick(init_tid)
        return tag

    def is_ancestor_or_self(self, loc: int, anc: int, desc: int) -> bool:
        tree = self.trees[loc]
        cur: Optional[int] = desc
        while cur is not None:
            if cur == anc: return True
            cur = tree[cur].parent
        return False

    def perform_tb_access(self, loc: int, source_tag: int, kind: str, skip_children: bool = False) -> Tuple[bool, str]:
        tree = self.trees[loc]
        for t, node in list(tree.items()):
            if skip_children and t != source_tag and self.is_ancestor_or_self(loc, source_tag, t):
                continue
            is_foreign = not self.is_ancestor_or_self(loc, t, source_tag)
            nxt = tb_transition(kind, is_foreign, node.perm, node.protected)
            if nxt is None:
                return False, f"UB TreeBorrows({kind} by tag={source_tag} invalidated tag={t})"
            node.perm = nxt
            if t == source_tag:
                node.accessed = True
        return True, "ok"

    def retag(self, tid: int, loc: int, parent_tag: int, new_perm: str, fn_entry_protected: bool) -> Tuple[bool, str, int]:
        tree = self.trees[loc]
        assoc = tb_associated_access(new_perm)
        if assoc is not None:
            ok, msg = self.perform_tb_access(loc, parent_tag, assoc, skip_children=False)
            if not ok: return False, msg, -1
            ok, msg = (self.race.check_and_record_na_read(tid, loc) if assoc == "Read"
                       else self.race.check_and_record_na_write(tid, loc, "NaWrite::Retag"))
            if not ok: return False, msg, -1
        child_tag = self.next_tag; self.next_tag += 1
        tree[child_tag] = TBNode(tag=child_tag, parent=parent_tag, perm=new_perm,
                                 accessed=(assoc is not None and new_perm == UNIQUE), protected=fn_entry_protected)
        tree[parent_tag].children.append(child_tag)
        return True, "ok", child_tag

    def atomic_store(self, tid: int, loc: int, tag: int, val: int, ord_kind: str) -> Tuple[bool, str]:
        ok, msg = self.perform_tb_access(loc, tag, "Write", skip_children=False)
        return (False, msg) if not ok else self.race.check_and_record_atomic_store(tid, loc, val, ord_kind)

    def atomic_load(self, tid: int, loc: int, tag: int, ord_kind: str) -> Tuple[bool, str, int]:
        ok, msg = self.perform_tb_access(loc, tag, "Read", skip_children=False)
        return (False, msg, -1) if not ok else self.race.check_and_record_atomic_load(tid, loc, ord_kind)

    def non_atomic_write(self, tid: int, loc: int, tag: int, val: int) -> Tuple[bool, str]:
        ok, msg = self.perform_tb_access(loc, tag, "Write", skip_children=False)
        if not ok: return False, msg
        ok, msg = self.race.check_and_record_na_write(tid, loc, "NaWrite::Explicit")
        if ok: self.race.loc_val[loc] = val
        return ok, msg

    def release_protector_fn_exit(self, tid: int, loc: int, tag: int) -> Tuple[bool, str]:
        node = self.trees[loc][tag]
        assoc = tb_associated_access(node.perm)
        if assoc is not None and node.accessed:
            ok, msg = self.perform_tb_access(loc, tag, assoc, skip_children=True)
            if not ok: return False, msg
            if self.emit_vclock_on_fn_exit:
                ok, msg = (self.race.check_and_record_na_write(tid, loc, "NaWrite::ProtectorEnd") if assoc == "Write"
                           else self.race.check_and_record_na_read(tid, loc))
                if not ok: return False, msg
        node.protected = False
        return True, "ok"

def run_probe2():
    # Part 2A: scalar naWriteTs/naReadTs vs VClock
    m0 = Skeleton04GlobalMem()
    m0.init_loc(1, 42, ts=0)
    assert m0.read_na({1: 0}, 1) == 42
    assert m0.write_na({1: 0}, 1, 99) is True  # Scalar bug: misses unsynchronized race at ts=0!

    m5 = Skeleton04GlobalMem()
    m5.init_loc(1, 42, ts=5)
    assert m5.read_na({1: 5}, 1) == 42
    assert m5.write_na({1: 5}, 1, 99) is True  # Scalar bug: misses unsynchronized race at ts=5!

    vc0 = VClockRaceMachine(2)
    assert vc0.check_and_record_na_read(0, 1)[0] is True
    assert vc0.check_and_record_na_write(1, 1)[0] is False  # VClock catches unsynchronized race!

    vc_sync = VClockRaceMachine(2)
    assert vc_sync.check_and_record_na_read(0, 1)[0] is True
    assert vc_sync.check_and_record_atomic_store(0, 2, 1, "Release")[0] is True
    ok, _, val = vc_sync.check_and_record_atomic_load(1, 2, "Acquire")
    assert ok and val == 1
    assert vc_sync.check_and_record_na_write(1, 1)[0] is True  # Positive control: Rel->Acq handoff ok!

    # Part 2B: TreeBorrows FnExit ProtectorEnd VClock soundness
    def run_foo_scenario(emit_fn_exit: bool, raw_is_cell: bool, llvm_end_writeback: bool, sync_rel_acq: bool, write_inside_foo: bool) -> bool:
        tb = TreeBorrowsWithVClock(2, emit_vclock_on_fn_exit=emit_fn_exit)
        root_a = tb.alloc_root(0, 10, 0)
        root_f = tb.alloc_root(0, 20, 0)
        if raw_is_cell:
            ok, _, raw_p = tb.retag(0, 10, root_a, CELL, False)
            assert ok
        else:
            raw_p = root_a
        tb.race.fork_from(0, 1)
        # Enter foo(x: &mut AtomicUsize): default implicit_writes=false => protected ReservedFrz
        ok, _, x_tag = tb.retag(0, 10, root_a, RES_FRZ_CLEAN, True)
        assert ok
        if write_inside_foo:
            ok, _, cell_x = tb.retag(0, 10, x_tag, CELL, False)
            assert ok
            ok, _ = tb.atomic_store(0, 10, cell_x, 1, "Relaxed")
            assert ok
            assert tb.trees[10][x_tag].perm == UNIQUE
            tb.trees[10][x_tag].accessed = True
        if llvm_end_writeback:
            ok, _ = tb.non_atomic_write(0, 10, x_tag, 1)
            if not ok:
                return False
        ok, _ = tb.release_protector_fn_exit(0, 10, x_tag)
        if not ok:
            return False
        ok, _ = tb.atomic_store(0, 20, root_f, 1, "Release" if sync_rel_acq else "Relaxed")
        assert ok
        ok, _, fv = tb.atomic_load(1, 20, root_f, "Acquire" if sync_rel_acq else "Relaxed")
        assert ok and fv == 1
        ok, _, _ = tb.atomic_load(1, 10, raw_p, "Relaxed")
        return ok

    assert run_foo_scenario(False, True, False, False, True) is True    # Unpatched Miri misses UB (Cell)
    assert run_foo_scenario(True,  True, False, False, True) is False   # Patched FnExit catches UB (Cell)
    assert run_foo_scenario(False, False, False, False, True) is True   # Unpatched Miri misses UB (Unique)
    assert run_foo_scenario(True,  False, False, False, True) is False  # Patched FnExit catches UB (Unique)
    assert run_foo_scenario(False, True, True, False, True) is False    # LLVM noalias writeback is UB in unpatched Miri!
    assert run_foo_scenario(True,  True, False, True, True) is True     # Positive control: Rel->Acq ok
    assert run_foo_scenario(True,  True, False, False, False) is True   # Positive control: unwritten &mut AtomicUsize ok
    print("ALL PROBE 2A (VClock) & 2B (TreeBorrows FnExit ProtectorEnd) ASSERTIONS PASSED!")

if __name__ == "__main__":
    run_probe2()
