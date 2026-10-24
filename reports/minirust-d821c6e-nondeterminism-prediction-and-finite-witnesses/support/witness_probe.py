"""Small, owned byte-machine probe; neither Rust execution nor a proof assistant.

All state and transitions below are defined here. HistoryFree and AliasSensitive
are different semantic policies. The latter is deliberately not Tree Borrows.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
import json
import resource
import time

# Darwin rejects lowering this process's RLIMIT_AS. The exhaustive domains
# below are tiny; actual peak RSS is checked and reported after the run.
resource.setrlimit(resource.RLIMIT_CPU, (10, resource.getrlimit(resource.RLIMIT_CPU)[1]))


class UB(Exception):
    pass


@dataclass(frozen=True)
class Ptr:
    allocation: int | None
    offset: int
    tag: str


class ByteMachine:
    def __init__(self, history_sensitive):
        self.history_sensitive = history_sensitive
        self.allocations = {}
        self.permissions = {}
        self.next_id = 0
        self.events = []

    def alloc(self, cells, tag):
        aid = self.next_id
        self.next_id += 1
        self.allocations[aid] = [True, list(cells)]
        self.permissions[aid] = {tag: [[True, True] for _ in cells]}
        self.events.append(("alloc", aid))
        return Ptr(aid, 0, tag)

    def alias(self, p, tag):
        # A raw pointer alias, not an extra logical exclusive ownership token.
        self.permissions[p.allocation][tag] = [x[:] for x in self.permissions[p.allocation][p.tag]]
        self.events.append(("alias", tag))
        return Ptr(p.allocation, p.offset, tag)

    def at(self, p, delta):
        # This probe's fixed machine offset range is 0..15. Pointer arithmetic
        # is represented and checked rather than silently using Python's range.
        q = Ptr(p.allocation, p.offset + delta, p.tag)
        if not 0 <= q.offset <= 15:
            raise UB("pointer-arithmetic")
        if q.allocation is None or q.allocation not in self.allocations:
            raise UB("provenance")
        live, cells = self.allocations[q.allocation]
        if not live or q.offset > len(cells):
            raise UB("pointer-arithmetic")
        self.events.append(("offset", q.offset))
        return q

    def access(self, p, write):
        if p.allocation is None or p.allocation not in self.allocations:
            raise UB("provenance")
        live, cells = self.allocations[p.allocation]
        if not live:
            raise UB("dead-allocation")
        if not 0 <= p.offset < len(cells):
            raise UB("bounds")
        rights = self.permissions[p.allocation].get(p.tag)
        if rights is None or not rights[p.offset][int(write)]:
            raise UB("authority")
        if self.history_sensitive:
            # Accesses consult and update the same concrete alias state as the
            # byte operation. A read can disable a later sibling write.
            for tag, other in self.permissions[p.allocation].items():
                if tag != p.tag:
                    other[p.offset][1] = False
                    if write:
                        other[p.offset][0] = False
        self.events.append(("write-access" if write else "read-access", p.offset))
        return cells

    def read_u8(self, p):
        cells = self.access(p, False)
        v = cells[p.offset]
        if v is None:
            raise UB("uninitialized")
        return v

    def read_bool(self, p):
        v = self.read_u8(p)
        if v not in (0, 1):
            raise UB("invalid-bool")
        return bool(v)

    def write_u8(self, p, v):
        if not isinstance(v, int) or not 0 <= v <= 255:
            raise UB("invalid-u8")
        cells = self.access(p, True)
        cells[p.offset] = v

    def free(self, p):
        self.access(p, True)
        if p.offset != 0:
            raise UB("free-interior")
        self.allocations[p.allocation][0] = False
        self.events.append(("free", p.allocation))


def copy_loop(m, src, dst, n):
    # The prospective Rust implementation is a bytewise loop around add,
    # read::<u8>, write::<u8>. This is its owned semantic program only.
    i = 0
    while i < n:
        v = m.read_u8(m.at(src, i))
        m.write_u8(m.at(dst, i), v)
        i += 1


def rejected(f):
    try:
        f()
        return None
    except UB as e:
        return str(e)


def main():
    started = time.monotonic()
    cases = 0
    prefix_events = 0
    alphabet = (0, 1, 2, 255)
    destinations = (None, 0, 255)
    controls = {}
    separations = {}
    overlap_controls = {}
    for history in (False, True):
        name = "AliasSensitive" if history else "HistoryFree"
        # Enumerate lengths 0..3, source and destination contents, and three
        # disjoint arrangements: separate allocations, one allocation/same tag,
        # one allocation/distinct alias tags.
        for n in range(4):
            for source in product(alphabet, repeat=n):
                for old in product(destinations, repeat=n):
                    for arrangement in ("separate", "same-tag", "distinct-tags"):
                        m = ByteMachine(history)
                        same_allocation = arrangement != "separate"
                        if same_allocation:
                            base = m.alloc([19, *source, 77, *old, 23], "owner")
                            src = Ptr(base.allocation, 1, "owner")
                            dst_base = m.alias(base, "destination") if arrangement == "distinct-tags" else base
                            dst = Ptr(base.allocation, n + 2, dst_base.tag)
                            before = list(m.allocations[base.allocation][1])
                        else:
                            src_base = m.alloc([19, *source, 77], "s")
                            dst_base = m.alloc([31, *old, 23], "d")
                            src = Ptr(src_base.allocation, 1, "s")
                            dst = Ptr(dst_base.allocation, 1, "d")
                            before = list(m.allocations[src.allocation][1])
                        frame = m.alloc([211, 212], "frame")
                        copy_loop(m, src, dst, n)
                        got = m.allocations[dst.allocation][1][dst.offset:dst.offset+n]
                        assert got == list(source)
                        assert m.allocations[frame.allocation][1] == [211, 212]
                        if same_allocation:
                            cells = m.allocations[src.allocation][1]
                            expected = before[:]
                            expected[dst.offset:dst.offset+n] = list(source)
                            assert cells == expected
                        else:
                            assert m.allocations[src.allocation][1] == before
                            assert m.allocations[dst.allocation][1][0] == 31
                            assert m.allocations[dst.allocation][1][-1] == 23
                        cases += 1
                        prefix_events += len(m.events)

        checks = {}
        m = ByteMachine(history)
        src, dst = m.alloc([None], "s"), m.alloc([0], "d")
        checks["uninitialized-source"] = rejected(lambda: copy_loop(m, src, dst, 1))
        m = ByteMachine(history)
        src, dst = m.alloc([2], "s"), m.alloc([0], "d")
        checks["invalid-bool-at-production"] = rejected(lambda: m.read_bool(src))
        checks["out-of-bounds-source"] = rejected(lambda: copy_loop(m, src, dst, 2))
        m = ByteMachine(history)
        src, dst = m.alloc([1], "s"), m.alloc([0], "d")
        m.free(src)
        checks["stale-provenance"] = rejected(lambda: copy_loop(m, src, dst, 1))
        checks["absent-provenance"] = rejected(lambda: m.read_u8(Ptr(None, 0, "s")))
        m = ByteMachine(history)
        src, dst = m.alloc([1], "s"), m.alloc([0], "d")
        m.permissions[dst.allocation]["d"][0][1] = False
        checks["missing-destination-authority"] = rejected(lambda: copy_loop(m, src, dst, 1))
        assert all(checks.values()), checks
        controls[name] = checks

        # Model distinction has an observable safety consequence, not just a
        # renamed state: read through a sibling raw alias then write original.
        m = ByteMachine(history)
        p = m.alloc([3], "original")
        sibling = m.alias(p, "sibling")
        assert m.read_u8(sibling) == 3
        separations[name] = rejected(lambda: m.write_u8(p, 4)) or "success"

        # An empty input does not manufacture dereferences or require a live
        # pointer; this is a property of this loop, not all raw-copy primitives.
        m = ByteMachine(history)
        copy_loop(m, Ptr(None, 0, "x"), Ptr(None, 0, "y"), 0)
        assert not m.events

        # Nonoverlap is needed by this functional contract. Forward bytewise
        # copying of overlapping regions need not itself be UB; it can simply
        # produce the wrong snapshot-copy answer.
        m = ByteMachine(history)
        p = m.alloc([1, 2, 3], "owner")
        copy_loop(m, p, Ptr(p.allocation, 1, p.tag), 2)
        cells = m.allocations[p.allocation][1]
        assert cells == [1, 1, 1] and cells != [1, 1, 2]
        overlap_controls[name] = cells

    assert separations == {"HistoryFree": "success", "AliasSensitive": "authority"}
    peak_rss_bytes = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert peak_rss_bytes < 256 * 1024 * 1024
    assert time.monotonic() - started < 10
    print(json.dumps({
        "subject": "owned finite byte-machine witness probe",
        "not_established": ["Lean theorem", "Rust frontend adequacy", "MiniRust correspondence", "Rust alias validity", "full law-class inhabitation theorem"],
        "positive_copy_cases": cases,
        "executed_primitive_events": prefix_events,
        "source_byte_alphabet": alphabet,
        "destination_cell_alphabet": destinations,
        "lengths": [0, 1, 2, 3],
        "controls": controls,
        "distinct_model_witness": separations,
        "overlap_functional_counterexample": overlap_controls,
        "zero_length_absent_provenance": "success with zero events, both models",
        "elapsed_seconds": time.monotonic() - started,
        "peak_rss_bytes_darwin": peak_rss_bytes,
    }, indent=2))


if __name__ == "__main__":
    main()
